{-# LANGUAGE DeriveDataTypeable, AutoDeriveTypeable, BangPatterns #-}
{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances #-}

-- |
-- Module       : Language.ManyDice.Tokenizer
-- Copyright    : (c) 2015 Paul Drees
-- Maintainer   : zemyla@gmail.com
-- Stability    : experimental
-- Portability  : GHC
--
-- A tokenizer for the ManyDice language. The language's EBNF is similar to
-- that at <http://anydice.com/ebnf.txt>, except for the @legacy@ special form,
-- which uses the syntax from
-- <http://web.archive.org/web/20100218153735/http://catlikecoding.com/anydice/wiki/Documentation/Documentation the old AnyDice>,
-- except that the form @[N]@, which in normal AnyDice interpolates a value as
-- best as it can into a string, here is extended to include a variable,
-- expression, or function call into a @legacy@ evaluation.

module Language.ManyDice.Tokenizer (
-- * Updating a 'Text.Parsec.Pos.SourcePos'
    Delta(..),
    updatePosDelta,
    deltaAddChars,
    deltaAddChar,
    deltaAddTabs,
    deltaAddTab,
    deltaAddNewlines,
    deltaAddNewline,
    textDelta,
-- * Tokens
    Comparison(..),
    TakeClosest(..),
    Token(..),
    VarType(..),
    tpretty,
    DeltaToken(..),
    TStream,
    nextToken,
    toTStream,
    toTokens,
    tokenP,
    reserved,
    comp,
    takeClosest,
    tchar,
    tstring,
    varName,
    funName,
    number,
    varType,
    liftParsec
    ) where

import Prelude hiding (foldl, foldr, sequence, mapM, mapM_)
import Control.Applicative
import Control.Monad
import qualified Data.Text as T
import Data.Text (Text)
import Data.Hashable
import Data.Functor.Identity
import qualified Text.Parsec as P
import Text.Parsec (Parsec, ParsecT, unexpected, (<?>), Stream(..), tokenPrim)
import qualified Text.Parsec.Pos as P
import Text.Parsec.Pos (SourcePos, sourceLine, sourceColumn, setSourceLine, setSourceColumn)
import Data.Data
import Data.Monoid
import Data.Foldable
import Data.Traversable
import Data.Char
import Data.Bits
import Data.Ix
import Data.Coerce
import Data.List (unfoldr)

-- | The type @Delta@ represents a change in a 'Text.Parsec.Pos.SoucePos' by
-- inputting a token. It is here so that the stream doesn't have to track its
-- position manually; instead, each token knows its 'Delta', and updates the
-- position in the 'Text.Parsec.Prim.tokenPrim' function.
data Delta
    -- | One or more linefeeds, followed by zero or more normal characters.
    = LineFeeds {-# UNPACK #-} !Int {-# UNPACK #-} !Int
    -- | Zero or more characters, followed by zero or more tabs, followed by
    -- zero or more characters.
    | Tabbed {-# UNPACK #-} !Int {-# UNPACK #-} !Int {-# UNPACK #-} !Int
    deriving (Eq, Ord, Read, Show, Typeable, Data)

-- @addTabs col t@ gives the result of adding @t@ tabs to column @col@.
addTabs :: Int -> Int -> Int
addTabs col t = if t <= 0 then col else col + t * 8 + ((col - 1) .&. 7)
{-# INLINE addTabs #-}

instance Monoid Delta where
    mempty = Tabbed 0 0 0

-- When adding two linefeed sets together, ignore any characters between the
-- first set of linefeeds and the second.
    mappend (LineFeeds lfa _) (LineFeeds lfb cb) = LineFeeds (lfa + lfb) cb
-- Add the characters and tabs to the end of the linefeeds (since the column
-- always starts at 1 after a linefeed).
    mappend (LineFeeds lfa ca) (Tabbed pcb tb cb) = LineFeeds lfa $ cb - 1 + addTabs (ca + pcb + 1) tb
-- Normal characters before a linefeed are ignored.
    mappend (Tabbed {}) d@(LineFeeds {}) = d
-- Add the two together. If there are any characters between two sets of tabs,
-- then eight characters is equivalent to one tab.
    mappend (Tabbed pca ta ca) (Tabbed pcb tb cb)
        | tb <= 0 = Tabbed pca ta (ca + pcb + cb)
        | ta <= 0 = Tabbed (pca + ca + pcb) tb cb
        | otherwise = Tabbed pca (ta + tb + unsafeShiftR (ca + pcb) 3) cb

    mconcat = foldl' mappend mempty
    {-# INLINE mconcat #-}

-- | Add a 'Delta' to a 'Text.Parsec.Pos.SourcePos', as if it were being done
-- by 'Text.Parsec.Pos.updatePosString'.
updatePosDelta :: SourcePos -> Delta -> SourcePos
updatePosDelta !p (LineFeeds lf c) = let
    !p' = setSourceLine p (lf + sourceLine p)
    !col = c + 1
    in setSourceColumn p' col
updatePosDelta !p (Tabbed pc t c) = let
    !ncol = c + addTabs (pc + sourceColumn p) t
    in setSourceColumn p ncol

-- | Add a given number of normal characters to the 'Delta'.
deltaAddChars :: Delta -> Int -> Delta
deltaAddChars d nc | nc <= 0 = d
deltaAddChars (LineFeeds lf c) nc = LineFeeds lf (c + nc)
deltaAddChars (Tabbed pc t c) nc = Tabbed pc t (c + nc)

-- | Add a single character to the 'Delta'. This method is given for brevity.
deltaAddChar :: Delta -> Delta
deltaAddChar d = deltaAddChars d 1
{-# INLINE deltaAddChar #-}

-- | Add a given number of tabs to the 'Delta'.
deltaAddTabs :: Delta -> Int -> Delta
deltaAddTabs d nt | nt <= 0 = d
deltaAddTabs (LineFeeds lf c) nt = LineFeeds lf (c + nt * 8 + (c .&. 7))
deltaAddTabs (Tabbed pc t c) nt
    | t <= 0 = Tabbed (pc + c) nt 0
    | otherwise = Tabbed pc (t + nt + unsafeShiftR c 3) 0

-- | Add a single tab to the 'Delta'. This method is given for brevity.
deltaAddTab :: Delta -> Delta
deltaAddTab d = deltaAddTabs d 1
{-# INLINE deltaAddTab #-}

-- | Add a given number of newlines to the 'Delta'.
deltaAddNewlines :: Delta -> Int -> Delta
deltaAddNewlines d nlf | nlf <= 0 = d
deltaAddNewlines (LineFeeds lf _) nlf = LineFeeds (lf + nlf) 0
deltaAddNewlines (Tabbed {}) nlf = LineFeeds nlf 0

-- | Add a single newline to the 'Delta'. This method is given for brevity.
deltaAddNewline :: Delta -> Delta
deltaAddNewline d = deltaAddNewlines d 1
{-# INLINE deltaAddNewline #-}

-- | Convert a 'Data.Text.Text' value into a 'Delta'.
--
-- @'Text.Parsec.Pos.updatePosString' p ('Data.Text.unpack' t) =
-- 'updatePosDelta' p ('textDelta' t)@
textDelta :: Text -> Delta
textDelta = T.foldl' go mempty where
    go d _ | d `seq` False = undefined
    go d c
        | c == '\n' = deltaAddNewline d
        | c == '\t' = deltaAddTab d
        | otherwise = deltaAddChar d

-- -----------------------------------------------------------------------------
-- * Tokens

-- | The type for comparisons. They are separate from other tokens because they
-- are used in different ways in the normal and legacy parsers. The order here
-- is important: They are arranged so that, if @cmp@ is a comparison and
-- @c = 1 + 'Prelude.fromEnum' cmp@, then @'Data.Bits.bit' c 0@ is whether this
-- comparison includes less-than, @'Data.Bits.bit' c 1@ is whether it includes
-- equals, and @'Data.Bits.bit' c 2@ is whether it includes greater-than.
data Comparison
    = CLT
    | CEQ
    | CLE
    | CGT
    | CNE
    | CGE
    deriving (Eq, Ord, Read, Show, Typeable, Data, Enum, Bounded, Ix)

-- | The type for the various forms of the
-- <http://web.archive.org/web/20100218153745/http://catlikecoding.com/anydice/wiki/Documentation/Filters "Take Closest">
-- operation. This is only generated in the @legacy@ form.
data TakeClosest
    = CLowest
    | CMatch
    | CHighest
    | CWeighted
    | CTies
    deriving (Eq, Ord, Read, Show, Typeable, Data, Enum, Bounded, Ix)

-- | The type of a token.
data Token
    -- | A single character that doesn't fall under any of the other categories.
    = TChar {-# UNPACK #-} !Char
    -- | A number, @[0-9]+@
    | TNum !Integer
    -- | A variable name, @[A-Z]+@
    | TVarName !Text
    -- | A function word or reserved word, @[a-z]+@
    | TFunName !Text
    -- | The inside of a string, @[^\"]*@. The quotes are emitted separately.
    | TString !Text
    -- | A comparison, @=|!=|\<=?|>=?@
    | TComparison !Comparison
    -- | A take-closest modifier, @\@[\<>=%#]@
    | TClosest !TakeClosest
    -- | An ellipsis, @\\.\\.\\.?|&hellip;@
    | TEllipsis
    -- | One or more end-of-line characters, @
    | TEOL
    -- | An unterminated comment, returned so it can be handled in the parser.
    -- Terminated comments are swallowed.
    | TBadComment
    deriving (Eq, Ord, Read, Show, Typeable, Data)

-- | Pretty-print a token.
tpretty :: Token -> String
tpretty (TChar c) = show c
tpretty (TNum n) = "number " ++ show n
tpretty (TVarName t) = "word " ++ show t
tpretty (TFunName t) = "word " ++ show t
tpretty (TString t) = "string " ++ show t
tpretty (TComparison c) = case c of
    CLT -> "'<'"
    CEQ -> "'='"
    CLE -> "'<='"
    CGT -> "'>'"
    CNE -> "'!='"
    CGE -> "'>='"
tpretty (TClosest c) = case c of
    CLowest -> "'@<'"
    CMatch -> "'@='"
    CHighest -> "'@>'"
    CWeighted -> "'@%'"
    CTies -> "'@#'"
tpretty TEllipsis = "'..'"
tpretty TEOL = "end of line"
tpretty TBadComment = "unterminated comment"

-- | A variable type annotation in a function declaration. This can either be
-- @?@ (any type), @n@ (a number), @s@ (a sequence), or @d@ (a die).
data VarType
    = AnyType
    | NumType
    | SeqType
    | DieType
    deriving (Eq, Ord, Read, Show, Typeable, Data, Enum, Bounded, Ix)

-- | A 'Token' with its associated 'Delta'.
data DeltaToken = DeltaToken !Token !Delta
    deriving (Eq, Ord, Read, Show, Typeable, Data)

-- | The current state of the 'TStream'. The actual stream state is a stack of
-- these.
data StreamState
    -- | Inside a pair of brackets.
    = InBracket
    -- | Inside a @legacy@ construct.
    | InLegacy
    -- | Inside a string.
    | InString
    -- | Just read the word @"legacy"@.
    | InLStart
    deriving (Eq, Ord, Read, Show, Typeable, Data, Enum, Bounded, Ix)

-- | A stream reading from a 'Data.Text.Text'.
data TStream = TStream !Text ![StreamState]
    deriving (Eq, Ord, Read, Show, Typeable, Data)

-- A 'TStream' with adjoined 'Delta' to keep track of how many characters it
-- has processed.
data DTStream = DTStream !Text ![StreamState] !Delta
    deriving (Eq, Ord, Read, Show, Typeable, Data)

dtUncons :: DTStream -> Maybe (Char, DTStream)
dtUncons (DTStream t ss d) = case T.uncons t of
    Nothing -> Nothing
    Just (c, t') -> Just (c, DTStream t' ss d') where
        !d' = case c of
            '\n' -> deltaAddNewline d
            '\t' -> deltaAddTab d
            _ -> deltaAddChar d
{-# INLINE dtUncons #-}

dtState :: DTStream -> StreamState
dtState (DTStream _ ss _) = case ss of
    [] -> InBracket
    s:_ -> s
{-# INLINE dtState #-}

dtPushState :: StreamState -> DTStream -> DTStream
dtPushState s (DTStream t ss d) = DTStream t (s:ss) d
{-# INLINE dtPushState #-}

dtPopState :: DTStream -> DTStream
dtPopState ds@(DTStream t ss d) = case ss of
    [] -> ds
    _:ss' -> DTStream t ss' d
{-# INLINE dtPopState #-}

dtSpan :: (Char -> Bool) -> DTStream -> (Text, DTStream)
dtSpan f (DTStream t ss d) = case T.span f t of
    (tl, tr) -> (tl, dst) where
        !dst = DTStream tr ss (d <> textDelta tl)
{-# INLINE dtSpan #-}

dtToken :: Token -> DTStream -> Maybe (DeltaToken, TStream)
dtToken tok (DTStream t ss d) = Just (dtok, st) where
    !dtok = DeltaToken tok d
    !st = TStream t ss
{-# INLINE dtToken #-}

-- | Try to read a 'DeltaToken' from a 'TStream'.
nextToken :: TStream -> Maybe (DeltaToken, TStream)
nextToken = go where
    rmBracket :: DTStream -> DTStream
    rmBracket ds@(DTStream t ss d) = case ss of
        InBracket:ss' -> DTStream t ss' d
        _ -> ds

    lstr :: Text
    lstr = T.pack "legacy"

    isLineSpace :: Char -> Bool
    isLineSpace c = isSpace c && c /= '\n'
    {-# INLINE isLineSpace #-}

    isStringChar :: Char -> Bool
    isStringChar c = c /= '"' && c /= '\n'
    {-# INLINE isStringChar #-}

    addDigit :: Integer -> Char -> Integer
    addDigit i _ | i `seq` False = undefined
    addDigit i c = 10 * i + toInteger (ord c - ord '0')
    {-# INLINE addDigit #-}

    go (TStream t ss) = dgo (DTStream t ss mempty)
    {-# INLINE go #-}

    stripState :: DTStream -> DTStream
    stripState (DTStream t _ d) = DTStream t [] d
    {-# INLINE stripState #-}

    toClosest :: Char -> Maybe TakeClosest
    toClosest '<' = Just CLowest
    toClosest '>' = Just CHighest
    toClosest '=' = Just CMatch
    toClosest '%' = Just CWeighted
    toClosest '#' = Just CTies
    toClosest  _  = Nothing

    -- We're going to output a TEOL. Grab as much whitespace and comments as
    -- possible.
    stripWS :: DTStream -> Maybe (DeltaToken, TStream)
    stripWS ds = case dtUncons ds of
        Just (c, ds')
            | isSpace c -> case dtSpan isSpace ds of
                (_, ds') -> stripWS ds'
            | c == '\\' -> case dtSpan ('\\' /=) ds' of
                (_, dsr) -> case dtUncons dsr of
                    Just ('\\', dsr') -> stripWS dsr'
                    _ -> dtToken TBadComment dsr
        _ -> dtToken TEOL ds

    dgo :: DTStream -> Maybe (DeltaToken, TStream)
    dgo ds = case dtUncons ds of
        Nothing -> Nothing
        Just (c, ds') -> case c of
            '\n' -> stripWS (stripState ds')
            _ | dtState ds' == InString -> case c of
                '"' -> dtToken (TChar '"') ds'
                _ -> case dtSpan isStringChar ds of
                    (ts, dss) -> dtToken (TString ts) dss
            _ | isSpace c -> dgo $ snd $ dtSpan isLineSpace ds'
            '\\' -> case dtSpan ('\\' /=) ds' of
                (tc, dsc) -> case dtUncons dsc of
                    Just ('\\', dsc') -> case T.find ('\n' ==) tc of
                        Just _ -> stripWS (stripState dsc')
                        _ -> dgo dsc'
                    _ -> dtToken TBadComment dsc
            _ | InLStart <- dtState ds' -> case c of
                '"' -> dtToken (TChar '"') $ dtPushState InLegacy (dtPopState ds')
                _ -> dgo (dtPopState ds)
            _ | isDigit c -> case dtSpan isDigit ds of
                (tn, dsn) -> dtToken (TNum n) dsn where
                    !n = T.foldl' addDigit 0 tn
            _ | isUpper c -> case dtState ds' of
                InLegacy -> dtToken (TFunName $ T.singleton $ toLower c) ds'
                _ -> case dtSpan isUpper ds of
                    (tn, dsn) -> dtToken (TVarName tn) dsn
            _ | isLower c -> case dtState ds' of
                InLegacy -> dtToken (TFunName $ T.singleton c) ds'
                _ -> case dtSpan isLower ds of
                    (tn, dsn) -> dtToken (TFunName tn) dsn' where
                        !dsn' = if (c, tn) == ('l', lstr) then dtPushState InLStart dsn else dsn
            '[' -> dtToken (TChar '[') (dtPushState InBracket ds')
            ']' -> dtToken (TChar ']') (rmBracket ds')
            '"' -> case dtState ds' of
                InLegacy -> dtToken (TChar '"') (dtPopState ds')
                _ -> dtToken (TChar '"') (dtPushState InString ds')
            '\8230' -> dtToken TEllipsis ds'
            '.' -> case dtUncons ds' of
                Just ('.', ds'') -> case dtUncons ds'' of
                    Just ('.', ds''') -> dtToken TEllipsis ds'''
                    _ -> dtToken TEllipsis ds''
                _ -> dtToken (TChar '.') ds'
            '=' -> dtToken (TComparison CEQ) ds'
            '<' -> case dtUncons ds' of
                Just ('=', ds'') -> dtToken (TComparison CLE) ds''
                _ -> dtToken (TComparison CLT) ds'
            '>' -> case dtUncons ds' of
                Just ('=', ds'') -> dtToken (TComparison CGE) ds''
                _ -> dtToken (TComparison CGT) ds'
            '!' -> case dtUncons ds' of
                Just ('=', ds'') -> dtToken (TComparison CNE) ds''
                _ -> dtToken (TChar '!') ds'
            '@'
                | InLegacy <- dtState ds'
                , Just (c', ds'') <- dtUncons ds'
                , Just cl <- toClosest c' -> dtToken (TClosest cl) ds''
            _ -> dtToken (TChar c) ds'
{-# INLINE nextToken #-}

instance (Monad m) => Stream TStream m DeltaToken where
    uncons = return . nextToken
    {-# INLINE uncons #-}

-- | Turn a 'Data.Text.Text' into a 'TStream' with an empty context.
toTStream :: Text -> TStream
toTStream t = TStream t []
{-# INLINE toTStream #-}

-- | Turn a 'Data.Text.Text' into a list of 'DeltaToken's.
toTokens :: Text -> [DeltaToken]
toTokens = unfoldr nextToken . toTStream
{-# INLINE toTokens #-}

-- | @tokenP fn@ accepts a token @tok@ when @fn tok@ returns
-- @'Prelude.Just' x@. It eats 'TBadComment' tokens and produces an error.
tokenP :: (Token -> Maybe a) -> Parsec TStream u a
tokenP fn = tokenPrim dpretty gpos dfn >>= badComment where
    dpretty (DeltaToken t _) = tpretty t
    {-# INLINE dpretty #-}

    gpos p (DeltaToken _ d) _ = updatePosDelta p d
    {-# INLINE gpos #-}

    dfn (DeltaToken t _) = case t of
        TBadComment -> Just Nothing
        _ -> case fn t of
            Nothing -> Nothing
            p -> Just p
    
    badComment = maybe (unexpected "Unterminated comment") return
    {-# INLINE badComment #-}
{-# INLINE tokenP #-}

-- | Lift a 'Text.Parsec.Parsec' parser on the 'Data.Functor.Identity' monad
-- to one on an arbitrary monad.
liftParsec :: (Monad m) => Parsec TStream u a -> ParsecT TStream u m a
liftParsec p = let
    pf = P.runParsecT p
    pf' s = return $ fmap ((coerce :: (a -> m a) -> (Identity a -> m a)) return) $ runIdentity $ pf s
    in P.mkPT pf'

-- | @reserved s@ accepts only lowercase words identical to @s@.
reserved :: String -> Parsec TStream u ()
reserved s = tokenP fn <?> s where
    t = T.pack s
    fn (TFunName tf) = if tf == t then Just () else Nothing
    fn _ = Nothing

-- | Accepts a comparison (@=|!=|[\<>]=?@).
comp :: Parsec TStream u Comparison
comp = tokenP fn <?> "comparison" where
    fn (TComparison c) = Just c
    fn _ = Nothing

-- | Accepts a take-closest filter (@\@[\<=>%#]@). These are only produced in
-- a @legacy@ construct.
takeClosest :: Parsec TStream u TakeClosest
takeClosest = tokenP fn <?> "take-closest" where
    fn (TClosest c) = Just c
    fn _ = Nothing

-- | Accepts a single character. It works properly when used to match letters,
-- '\n', and the ellipsis.
tchar :: Char -> Parsec TStream u Char
tchar '\8230' = tokenP fn <?> "'..'" where
    fn TEllipsis = Just '\8230'
    fn _ = Nothing
tchar '\n' = tokenP fn <?> "end of line" where
    fn TEOL = Just '\n'
    fn _ = Nothing
tchar c | isLower c = tokenP fn <?> show c where
    fn (TFunName t) = case T.compareLength t 1 of
        EQ -> if T.head t == c then Just c else Nothing
        _ -> Nothing
    fn _ = Nothing
tchar c | isUpper c = tokenP fn <?> show c where
    fn (TVarName t) = case T.compareLength t 1 of
        EQ -> if T.head t == c then Just c else Nothing
        _ -> Nothing
    fn _ = Nothing
tchar c = tokenP fn <?> show c where
    fn (TChar c') = if c == c' then Just c else Nothing
    fn _ = Nothing

-- | Accepts a quote-delimited string.
tstring :: Parsec TStream u Text
tstring = tchar '"' *> tokenP fn <* tchar '"' <?> "string" where
    fn (TString t) = Just t
    fn _ = Nothing

-- | Accepts an uppercase variable name.
varName :: Parsec TStream u Text
varName = tokenP fn <?> "variable name" where
    fn (TVarName t) = Just t
    fn _ = Nothing

-- | Accepts a lowercase function word. Does not accept \"d\", though.
funName :: Parsec TStream u Text
funName = tokenP fn <?> "function word" where
    fn (TFunName t) = case T.compareLength t 1 of
        EQ -> if T.head t == 'd' then Nothing else Just t
        _ -> Just t
    fn _ = Nothing

-- | Accepts a number.
number :: Parsec TStream u Integer
number = tokenP fn <?> "number" where
    fn (TNum n) = Just n
    fn _ = Nothing

-- | Accepts a variable type annotation.
varType :: Parsec TStream u VarType
varType = tokenP fn <?> "variable type" where
    fn (TChar c) = if c == '?' then Just AnyType else Nothing
    fn (TFunName t) = case T.compareLength t 1 of
        EQ -> case T.head t of
            'd' -> Just DieType
            'n' -> Just NumType
            's' -> Just SeqType
            _ -> Nothing
        _ -> Nothing
    fn _ = Nothing
