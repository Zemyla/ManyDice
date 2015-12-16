{-# LANGUAGE DeriveDataTypeable, AutoDeriveTypeable, BangPatterns #-}
{-# LANGUAGE FlexibleInstances, GADTs, PolyKinds, DataKinds #-}
{-# LANGUAGE StandaloneDeriving, ScopedTypeVariables #-}
{-# OPTIONS -Wall #-}

-- |
-- Module       : Language.ManyDice.Parser
-- Copyright    : (c) 2015 Paul Drees
-- Maintainer   : zemyla@gmail.com
-- Stability    : experimental
-- Portability  : GHC
--
-- A parser for the ManyDice language. It takes a string of tokens from the
-- 'Language.ManyDice.Tokenizer', and turns them into an abstract syntax tree.

module Language.ManyDice.Parser (
    Expr(..),
    SeqPart(..),
    CountType(..),
    Modifier(..),
    exprP,
    FunParam(..),
    FunName(..),
    StmtType(..),
    StmtEq(..),
    StmtT(..),
    Block,
    Statement(..),
    statement,
    block,
    program,
    parseT) where

import Language.ManyDice.Tokenizer
import Prelude hiding (foldl, foldr, sequence, mapM, mapM_)
import Control.Applicative
import qualified Data.Text as T
import Data.Text (Text)
import qualified Data.Text.Lazy as TL
import qualified Data.Text.Internal.Builder as TB
import qualified Data.Vector as V
import Data.Vector (Vector)
import qualified Text.Parsec as P
import Text.Parsec (Parsec, try, unexpected, (<?>), eof, ParseError)
import Text.Parsec.Combinator (sepBy, optionMaybe, chainl1, sepEndBy1, chainr1)
import qualified Data.Sequence as Q
import Data.Sequence (Seq)
import Data.Data
import Data.Monoid
import Data.Foldable
import Data.Ix

infixr 1 :**
infix  2 :^^
infixl 3 :&, :|
infixl 4 :<<, :>>, :<=, :>=, :==, :/=
infixl 6 :+, :-
infixl 7 :*, :/
infixr 8 :^
infixl 9 :@

-- | An expression in ManyDice.
data Expr
    = ENum !Integer
    | EVar !Text
    | ESequence !(Seq SeqPart)
    | EAbs !Expr
    | ELength !Expr
    | ESignum !Expr
    | ENegate !Expr
    | ENot !Expr
    | !Expr :& !Expr
    | !Expr :| !Expr
    | !Expr :<< !Expr
    | !Expr :>> !Expr
    | !Expr :<= !Expr
    | !Expr :>= !Expr
    | !Expr :== !Expr
    | !Expr :/= !Expr
    | !Expr :+ !Expr
    | !Expr :- !Expr
    | !Expr :* !Expr
    | !Expr :/ !Expr
    | !Expr :^ !Expr
    | !Expr :@ !Expr
    -- | The @x@ operator in a @legacy@ construct.
    | !Expr :** !Expr
    -- | The @^@ operator in a @legacy@ construct.
    | !Expr :^^ !Expr
    | Die !Expr !Expr !Modifier
    | Funcall !Text !(Seq Expr)
    deriving (Eq, Ord, Read, Show, Typeable, Data)

-- | A part of a sequence in an expression.
data SeqPart
    = Single !Expr
    | Range !Expr !Expr
    | Count !Expr !Expr
    | RangeCount !Expr !Expr !Expr
    deriving (Eq, Ord, Read, Show, Typeable, Data)

-- | The target of a
-- <http://web.archive.org/web/20100218153755/http://catlikecoding.com/anydice/wiki/Documentation/Modifiers count or explosion modifier>.
data CountType
    = CountH
    | CountL
    | CountComp !Comparison !Expr
    | CountSeq !(Seq SeqPart)
    deriving (Eq, Ord, Read, Show, Typeable, Data)

-- | A filter or modifier on a die roll.
data Modifier
    = ModNone
    | ModHighest !Expr
    | ModLowest !Expr
    | ModMedian !Expr
    | ModCompare !Comparison !Expr
    | ModClosest !TakeClosest !Expr
    | ModCount !CountType
    | ModExplode !Expr !CountType
    deriving (Eq, Ord, Read, Show, Typeable, Data)

instance Num Expr where
    fromInteger = ENum
    {-# INLINE fromInteger #-}

    negate (ENum n) = ENum (negate n)
    negate (ENegate e) = e
    negate (ESignum a) = signum (negate a)
    negate (ENum n :+ a) = ENum (negate n) :- a
    negate (ENum n :- a) = ENum (negate n) :+ a
    negate (ENum n :* a) = ENum (negate n) :* a
    negate (Die a b m) = Die (negate a) b m
    negate e = ENegate e

    signum (ENum n) = ENum (signum n)
    signum e@(ESignum _) = e
    signum e@(ENot _) = e
    signum e@(_ :& _) = e
    signum e@(_ :| _) = e
    signum e@(_ :<< _) = e
    signum e@(_ :>> _) = e
    signum e@(_ :<= _) = e
    signum e@(_ :>= _) = e
    signum e@(_ :== _) = e
    signum e@(_ :/= _) = e
    signum (ENum n :* a) = ENum (signum n) * signum a
    signum e = ESignum e

    abs (ENum n) = ENum (abs n)
    abs (ENegate a) = abs a
    abs e@(ELength _) = e
    abs e@(EAbs _) = e
    abs e@(ENot _) = e
    abs e@(_ :& _) = e
    abs e@(_ :| _) = e
    abs e@(_ :<< _) = e
    abs e@(_ :>> _) = e
    abs e@(_ :<= _) = e
    abs e@(_ :>= _) = e
    abs e@(_ :== _) = e
    abs e@(_ :/= _) = e
    abs (ESignum a) = signum (abs a)
    abs (ENum n :- a) = abs (ENum (negate n) :+ a)
    abs (ENum n :* a) = ENum (abs n) :* abs a
    abs (a :/ ENum n) = abs a :/ ENum (abs n)
    abs (ENum n :/ a) = ENum (abs n) :/ abs a
    abs a = EAbs a

    ea + (ENegate eb) = ea - eb
    (ENegate ea) + eb = eb - ea
    ea@(ENum n) + eb
        | n == 0 = eb
        | otherwise = case eb of
            ENum nb -> ENum (n + nb)
            ENum nb :+ eb' -> ENum (n + nb) + eb'
            ENum nb :- eb' -> ENum (n + nb) - eb'
            ENum nb :* eb'
                | (dn, 0) <- divMod n nb -> ENum nb * (ENum dn + eb')
            _ -> ea :+ eb
    ea + eb@(ENum _) = eb + ea
    (al :+ ar) + eb
        | ENum na <- al = case eb of
            ENum nb :+ br -> ENum (na + nb) + (ar + br)
            ENum nb :- br -> ENum (na + nb) + (ar - br)
            _ -> al :+ (ar + eb)
        | otherwise = case eb of
            bl@(ENum _) :+ br -> bl :+ (al + (ar + br))
            bl@(ENum _) :- br -> bl :+ (al + (ar - br))
            _ -> al :+ (ar + eb)
    (al :- ar) + eb
        | ENum na <- al = case eb of
            ENum nb :+ br -> ENum (na + nb) + (br - ar)
            ENum nb :- br -> ENum (na + nb) - (ar + br)
            _ -> al :+ (ar + eb)
        | otherwise = case eb of
            bl@(ENum _) :+ br -> bl :+ (al + (br - ar))
            bl@(ENum _) :- br -> bl :+ (al - (br + ar))
            _ -> al :+ (ar + eb)
    ea + eb@(_ :+ _) = eb + ea
    ea + eb@(_ :- _) = eb + ea
    (ENum na :* ar) + (ENum nb :* br)
        | na == nb = ENum na * (ar + br)
        | na == negate nb = ENum na * (ar - br)
    ea + eb = ea :+ eb

    ea - (ENegate eb) = ea + eb
    (ENegate ea) - eb = negate (ea + eb)
    ea@(ENum na) - eb
        | na == 0 = negate eb
        | otherwise = case eb of
            ENum nb -> ENum (na - nb)
            ENum nb :+ eb' -> ENum (na - nb) - eb'
            ENum nb :- eb' -> ENum (na - nb) + eb'
            ENum nb :* eb'
                | (dn, 0) <- divMod na nb -> ENum nb * (ENum dn - eb')
            _ -> ea :- eb
    ea - (ENum n) = ea + ENum (negate n)
    (al :+ ar) - eb
        | ENum na <- al = case eb of
            ENum nb :+ br -> ENum (na - nb) + (ar - br)
            ENum nb :- br -> ENum (na - nb) + (ar + br)
            _ -> al :+ (ar - eb)
        | otherwise = case eb of
            ENum nb :+ br -> ENum (negate nb) + (al + (ar - br))
            ENum nb :- br -> ENum (negate nb) + (al + (ar + br))
            _ -> al :+ (ar - eb)
    (al :- ar) - eb
        | ENum na <- al = case eb of
            ENum nb :+ br -> ENum (na - nb) - (ar + br)
            ENum nb :- br -> ENum (na - nb) + (br - ar)
            _ -> al :- (ar + eb)
        | otherwise = case eb of
            ENum nb :+ br -> ENum (negate nb) + (al - (ar + br))
            ENum nb :- br -> ENum (negate nb) + (al + (br - ar))
            _ -> al :- (ar + eb)
    ea - (ENum nb :+ eb) = ENum (negate nb) + (ea - eb)
    ea - (ENum nb :- eb) = ENum (negate nb) + (ea + eb)
    ea - (ENum nb :* eb) = ea + (ENum (negate nb) :* eb)
    ea - eb = ea :- eb

    ea@(ENum na) * eb
        | na == 0 = ENum 0
        | na == 1 = eb
        | na == -1 = negate eb
        | otherwise = case eb of
            ENum nb -> ENum (na * nb)
            ENum nb :* eb' -> ENum (na * nb) * eb'
            _ -> ea :* eb
    ea * eb@(ENum _) = eb * ea
    (al :* ar) * eb
        | ENum na <- al = case eb of
            ENum nb :* br -> ENum (na * nb) :* (ar * br)
            _ -> al :* (ar * eb)
        | otherwise = case eb of
            bl@(ENum _) :* br -> bl :* (al * (ar * br))
            _ -> al :* (ar * eb)
    ea * eb@(_ :* _) = eb * ea
    ea * eb = ea :* eb

unop :: Parsec TStream () (Expr -> Expr)
unop = tokenP fn <?> "'+', '-', '!', '#', or 'd'" where
    enot (ENum n) = if n == 0 then ENum 1 else ENum 0
    enot e = ENot e

    edie e = Die (ENum 1) e ModNone

    fn (TFunName t) = case T.compareLength t 1 of
        EQ -> if T.head t == 'd' then Just edie else Nothing
        _ -> Nothing
    fn (TChar c) = case c of
        '+' -> Just id
        '-' -> Just negate
        '!' -> Just enot
        '#' -> Just ELength
        _   -> Nothing
    fn _ = Nothing

type BEither a = Either a a

binopV :: Vector (BEither (Parsec TStream () (Expr -> Expr -> Expr)))
binopV = V.fromListN 7 [Left (tokenP diefn <?> "'d'"), Left (tokenP atfn <?> "'@'"), Right (tokenP powfn <?> "'^'"), Left (tokenP mulfn <?> "'*' or '/'"), Left (tokenP addfn <?> "'+' or '-'"), Left (tokenP cmpfn <?> "comparison operator"), Left (tokenP bitfn <?> "'&' or '|'")] where
    eand (ENum na) _ | na == 0 = ENum 0
    eand _ (ENum nb) | nb == 0 = ENum 0
    eand (ENum _) (ENum _) = ENum 1
    eand ea eb = ea :& eb

    eor (ENum na) _ | na /= 0 = ENum 1
    eor _ (ENum nb) | nb /= 0 = ENum 1
    eor (ENum _) (ENum _) = ENum 0
    eor ea eb = ea :| eb

    ediv ea eb@(ENum 0) = ea :/ eb
    ediv ea (ENum 1) = ea
    ediv ea (ENum (-1)) = negate ea
    ediv (ENum na) _ | na == 0 = ENum 0
    ediv (ENum na) (ENum nb) = ENum (quot na nb)
    ediv (ENum na :* ea) (ENum nb)
        | (da, 0) <- quotRem na nb = ENum da * ea
    ediv ea eb = ea :/ eb

    edie ea eb = Die ea eb ModNone

    bitfn (TChar c) = case c of
        '&' -> Just eand
        '|' -> Just eor
        _ -> Nothing
    bitfn _ = Nothing

    cmpfn (TComparison c) = Just $ case c of
        CLT -> (:<<)
        CEQ -> (:==)
        CLE -> (:<=)
        CGT -> (:>>)
        CNE -> (:/=)
        CGE -> (:>=)
    cmpfn _ = Nothing

    addfn (TChar c) = case c of
        '+' -> Just (+)
        '-' -> Just (-)
        _ -> Nothing
    addfn _ = Nothing

    mulfn (TChar c) = case c of
        '*' -> Just (*)
        '/' -> Just ediv
        _ -> Nothing
    mulfn _ = Nothing

    powfn (TChar '^') = Just (:^)
    powfn _ = Nothing

    atfn (TChar '@') = Just (:@)
    atfn _ = Nothing

    diefn (TFunName t) = case T.compareLength t 1 of
        EQ -> if T.head t == 'd' then Just edie else Nothing
        _ -> Nothing
    diefn _ = Nothing

exprV :: Vector (Parsec TStream () Expr)
exprV = V.constructN 8 go where
    go :: Vector (Parsec TStream () Expr) -> Parsec TStream () Expr
    go v = case V.length v of
        0 -> let
            unval = unop <*> unval <|> baseValue
            in unval
        n -> case (V.!) binopV (n - 1) of
            Left op -> chainl1 (V.last v) op
            Right op -> chainr1 (V.last v) op

exprP :: Parsec TStream () Expr
exprP = V.last exprV

baseValue :: Parsec TStream () Expr
baseValue = (tokenP vfn <?> "value") <|> tchar '(' *> exprP <* tchar ')' <|> tchar '{' *> seqList <* tchar '}' <|> (bracket >>= verify) <|> try (reserved "legacy" *> tchar '"') *> exprL <* tchar '"' where
    vfn (TVarName t) = Just $ EVar t
    vfn (TNum n) = Just $ ENum n
    vfn _ = Nothing

    verify (t, st, sv)
        | Q.null st = unexpected "Expecting at least one function word"
        | otherwise = return $! Funcall t sv

seqVal :: Parsec TStream () SeqPart
seqVal = select <$> exprP <*> optionMaybe (tchar '\8230' *> exprP) <*> optionMaybe (tchar ':' *> exprP) where
    select s Nothing Nothing = Single s
    select s Nothing (Just c) = Count s c
    select s (Just r) Nothing = Range s r
    select s (Just r) (Just c) = RangeCount s r c

seqList :: Parsec TStream () Expr
seqList = toExpr <$> (sepBy seqVal (tchar ',') <|> pure []) where
    toExpr ls = ESequence $ Q.fromList ls

funVal :: Parsec TStream () (Either Text Expr)
funVal = Right <$> exprP <|> (tokenP fn <?> "function word") where
    fn (TFunName t) = case T.compareLength t 1 of
        EQ -> if T.head t == 'd' then Nothing else Just (Left t)
        _ -> Just (Left t)
    fn _ = Nothing

bracket :: Parsec TStream () (Text, Seq Text, Seq Expr)
bracket = tchar '[' *> (tchar ']' *> failbrac <|> go <$> funVal <*> many funVal) <* tchar ']' where
    failbrac = unexpected "Empty brackets"

    append (b, st, sv) _ | b `seq` st `seq` sv `seq` False = undefined
    append (b, st, sv) (Left t) = (b', st', sv) where
        !b' = b <> TB.singleton ' ' <> TB.fromText t
        !st' = (Q.|>) st t
    append (b, st, sv) (Right v) = (b', st, sv') where
        !b' = b <> TB.fromString " ?"
        !sv' = (Q.|>) sv v

    go tv ls = let
        !iv = case tv of
            Left t -> (TB.fromText t, Q.singleton t, mempty)
            Right v -> (TB.singleton '?', mempty, Q.singleton v)
        in case foldl' append iv ls of
            (b, st, sv) -> (t, st, sv) where
                !t = TL.toStrict $ TB.toLazyText b

-- EBNF for Legacy dice
-- ldie : valuelist
-- valuelist : pval (\'x\' valuelist)?
-- pval : value (\'^\' value)?
-- value : value (4)
-- value (4) : value (3) { (\'+\' | \'-\') value (3) }
-- value (3) : value (2) { \'*\' value (2) }
-- value (2) : value (1) dieval?
-- value (1) : (\'+\' | \'-\') value (1) | dieval | value (0)
-- value (0) : number | \'(\' value \')\' | \'|\' value \'|\' | \'[\' (regular value | funcall) \']\'
-- dieval : 'd' seqval modifier?
-- seqval : value (1) | seq
-- seq : \'{\' (seqitem { ',' seqitem })? \'}\'
-- seqitem : value (\'..\' value)? (\'=\' value)?
-- modifier : (\'h\' | \'l\' | \'m\') value (0)? | cmptake value(1) | \'c\' cval | \'e\' value (0)? cval
-- cmptake : comparison | take
-- cval : \'h\' | \'l\' | comparison value | seq

exprL :: Parsec TStream () Expr
exprL = chainr1 pexprL (tokenP xfn <?> "'x'") <?> "legacy expression" where
    xfn (TFunName t) = case T.compareLength t 1 of
        EQ -> if T.head t == 'x' then Just (:**) else Nothing
        _ -> Nothing
    xfn _ = Nothing

pexprL :: Parsec TStream () Expr
pexprL = flip id <$> rexprL <*> ((tokenP pfn <?> "'^'") <*> rexprL <|> pure id) where
    pfn (TChar '^') = Just (:^^)
    pfn _ = Nothing

rexprL :: Parsec TStream () Expr
rexprL = chainl1 mexprL (tokenP pmfn <?> "'+' or '-'") where
    pmfn (TChar c) = case c of
        '+' -> Just (+)
        '-' -> Just (-)
        _ -> Nothing
    pmfn _ = Nothing

mexprL :: Parsec TStream () Expr
mexprL = chainl1 dexprL (tokenP mfn <?> "'*'") where
    mfn (TChar '*') = Just (*)
    mfn _ = Nothing

dexprL :: Parsec TStream () Expr
dexprL = flip id <$> uexprL <*> (dieValL <|> pure id)

uexprL :: Parsec TStream () Expr
uexprL = pmtok <*> uexprL <|> ($ ENum 1) <$> dieValL <|> sexprL where
    pmtok = tokenP pmfn <?> "'+' or '-'"
    pmfn (TChar c) = case c of
        '+' -> Just id
        '-' -> Just negate
        _ -> Nothing
    pmfn _ = Nothing

sexprL :: Parsec TStream () Expr
sexprL = numtok <|> tchar '(' *> rexprL <* tchar ')' <|> tchar '|' *> (abs <$> rexprL) <* tchar '|' <|> (bracket >>= verify) where
    numtok = tokenP numfn <?> "number"
    numfn (TNum n) = Just (ENum n)
    numfn _ = Nothing

    verify (t, st, sv)
        | Q.null st = case Q.viewl sv of
            Q.EmptyL -> unexpected "Empty brackets"
            (Q.:<) e sv' | Q.null sv' -> return e
            _ -> unexpected "Too many expressions in brackets"
        | otherwise = return $! Funcall t sv

dieValL :: Parsec TStream () (Expr -> Expr)
dieValL = dtok <*> (uexprL <|> ESequence <$> seqListL) <*> modifierL where
    dtok = tokenP dfn <?> "'d'"
    dfn (TFunName t) = case T.compareLength t 1 of
        EQ -> if T.head t == 'd' then Just (\ds m dc -> Die dc ds m) else Nothing
        _ -> Nothing
    dfn _ = Nothing

seqValL :: Parsec TStream () SeqPart
seqValL = select <$> rexprL <*> optionMaybe (tchar '\8230' *> rexprL) <*> optionMaybe (tchar '=' *> rexprL) where
    select s Nothing Nothing = Single s
    select s Nothing (Just c) = Count s c
    select s (Just r) Nothing = Range s r
    select s (Just r) (Just c) = RangeCount s r c

seqListL :: Parsec TStream () (Seq SeqPart)
seqListL = tchar '{' *> (Q.fromList <$> (sepBy seqValL (tchar ',') <|> pure [])) <* tchar '}'

modifierL :: Parsec TStream () Modifier
modifierL = hmlTok <*> (sexprL <|> pure (ENum 1)) <|> ctTok <*> uexprL <|> countExpL <*> countTypeL where
    hmlTok = tokenP hmlfn <?> "'h', 'm', or 'l'"
    hmlfn (TFunName t) = case T.compareLength t 1 of
        EQ -> case T.head t of
            'h' -> Just ModHighest
            'l' -> Just ModLowest
            'm' -> Just ModMedian
            _ -> Nothing
        _ -> Nothing
    hmlfn _ = Nothing

    ctTok = tokenP ctfn <?> "comparison or take-closest"
    ctfn (TComparison c) = Just (ModCompare c)
    ctfn (TClosest c) = Just (ModClosest c)
    ctfn _ = Nothing

countExpL :: Parsec TStream () (CountType -> Modifier)
countExpL = ModCount <$ tchar 'c' <|> (ModExplode <$ tchar 'e') <*> (uexprL <|> pure (ENum 1))

countTypeL :: Parsec TStream () CountType
countTypeL = hlTok <|> compTok <*> uexprL <|> CountSeq <$> seqListL where
    hlTok = tokenP hlfn <?> "'h' or 'l'"
    hlfn (TFunName t) = case T.compareLength t 1 of
        EQ -> case T.head t of
            'h' -> Just CountH
            'l' -> Just CountL
            _ -> Nothing
        _ -> Nothing
    hlfn _ = Nothing

    compTok = tokenP compfn <?> "comparison"
    compfn (TComparison c) = Just (CountComp c)
    compfn _ = Nothing

data FunParam = FunParam !Text !VarType
    deriving (Eq, Ord, Read, Show, Typeable, Data)

data FunName = FunName !Text !(Seq FunParam)
    deriving (Eq, Ord, Read, Show, Typeable, Data)

data StmtType
    = In
    | Out
    deriving (Eq, Ord, Read, Show, Typeable, Data, Enum, Bounded, Ix)

data StmtEq t where
    IsIn :: StmtEq 'In
    IsOut :: StmtEq 'Out

class StmtT t where
    stmtT :: p t -> StmtEq t

instance StmtT 'In where
    stmtT _ = IsIn

instance StmtT 'Out where
    stmtT _ = IsOut

type Block t = Seq (Statement t)

data Statement (t :: StmtType) where
    VarDef :: !Text -> !Expr -> Statement t
    IfStmt :: !Expr -> !(Block t) -> !(Block t) -> Statement t
    LoopStmt :: !Text -> !Expr -> !(Block t) -> Statement t
    Result :: !Expr -> Statement 'In
    FunDef :: !FunName -> !(Block 'In) -> Statement 'Out
    Output :: !Expr -> !(Maybe Text) -> Statement 'Out
    Setting :: !Text -> !(Either Text Expr) -> Statement 'Out

deriving instance Eq (Statement t)
deriving instance Ord (Statement t)
deriving instance Show (Statement t)
deriving instance (Typeable t) => Typeable (Statement t)

funSigP :: Parsec TStream () (Either Text FunParam)
funSigP = (tokenP wordfn <?> "variable or word") >>= rest where
    wordfn (TFunName t) = case T.compareLength t 1 of
        EQ -> if T.head t == 'd' then Nothing else Just (Left t)
        _ -> Just (Left t)
    wordfn (TVarName t) = Just (Right t)
    wordfn _ = Nothing

    rest (Left t) = return $ Left t
    rest (Right t) = (Right . FunParam t) <$> (tchar ':' *> varType <|> pure AnyType)

funSig :: Parsec TStream () FunName
funSig = ((,) <$> funSigP <*> many funSigP) >>= uncurry verify where
    append (b, st, sv) _ | b `seq` st `seq` sv `seq` False = undefined
    append (b, _, sv) (Left t) = (b', True, sv) where
        !b' = b <> TB.singleton ' ' <> TB.fromText t
    append (b, st, sv) (Right v) = (b', st, sv') where
        !b' = b <> TB.fromString " ?"
        !sv' = (Q.|>) sv v

    verify pf pr = let
        !i = case pf of
            Left t -> (TB.fromText t, True, mempty)
            Right v -> (TB.singleton '?', False, Q.singleton v)
        in case foldl' append i pr of
            (b, st, sv)
                | st -> return $! FunName t sv where
                    !t = TL.toStrict $ TB.toLazyText b
            _ -> unexpected "Require at least one word in function name"

varDef :: Parsec TStream () (Statement t)
varDef = VarDef <$> varName <*> (tchar ':' *> exprP)

resultDef :: Parsec TStream () (Statement 'In)
resultDef = (Result <$ (reserved "result" *> tchar ':')) <*> exprP

baseStmt :: (StmtT t) => Parsec TStream () (Statement t)
baseStmt = varDef <|> ifStmt <|> loopStmt

statement :: forall t. (StmtT t) => Parsec TStream () (Statement t)
statement = (*>) optRet $ baseStmt <|> case stmtT (Proxy :: Proxy t) of
    IsIn -> resultDef
    IsOut -> setStmt <|> outputStmt <|> funDef

{-# SPECIALIZE statement :: Parsec TStream () (Statement 'In) #-}
{-# SPECIALIZE statement :: Parsec TStream () (Statement 'Out) #-}

optRet :: Parsec TStream () ()
optRet = () <$ (tchar '\n' <|> pure ' ')

block :: (StmtT t) => Parsec TStream () (Block t)
block = blockStart *> (Q.fromList <$> sepEndBy1 statement (tchar '\n') <|> pure mempty) <* tchar '}' where
    blockStart = try (optRet *> tchar '{') *> optRet

{-# SPECIALIZE block :: Parsec TStream () (Block 'In) #-}
{-# SPECIALIZE block :: Parsec TStream () (Block 'Out) #-}

optBlock :: (StmtT t) => Parsec TStream () (Block t)
optBlock = optRet *> (block <|> Q.singleton <$> statement)

{-# SPECIALIZE optBlock :: Parsec TStream () (Block 'In) #-}
{-# SPECIALIZE optBlock :: Parsec TStream () (Block 'Out) #-}

ifStmt :: (StmtT t) => Parsec TStream () (Statement t)
ifStmt = (IfStmt <$ reserved "if") <*> exprP <*> optBlock <*> (try (optRet *> reserved "else") *> (Q.singleton <$> ifStmt <|> block) <|> pure mempty)

{-# SPECIALIZE ifStmt :: Parsec TStream () (Statement 'In) #-}
{-# SPECIALIZE ifStmt :: Parsec TStream () (Statement 'Out) #-}

loopStmt :: (StmtT t) => Parsec TStream () (Statement t)
loopStmt = (LoopStmt <$ reserved "loop") <*> varName <*> (reserved "over" *> exprP) <*> block

{-# SPECIALIZE loopStmt :: Parsec TStream () (Statement 'In) #-}
{-# SPECIALIZE loopStmt :: Parsec TStream () (Statement 'Out) #-}

setStmt :: Parsec TStream () (Statement 'Out)
setStmt = (Setting <$ reserved "set") <*> tstring <*> (reserved "to" *> (Left <$> tstring <|> Right <$> exprP))

outputStmt :: Parsec TStream () (Statement 'Out)
outputStmt = (Output <$ reserved "output") <*> exprP <*> optionMaybe (reserved "named" *> tstring)

funDef :: Parsec TStream () (Statement 'Out)
funDef = (FunDef <$ (reserved "function" *> tchar ':')) <*> funSig <*> block

program :: Parsec TStream () (Block 'Out)
program = optRet *> (Q.fromList <$> sepEndBy1 statement (tchar '\n')) <* (optRet *> eof)

parseT :: Parsec TStream () a -> Text -> Either ParseError a
parseT p t = P.runParser p () "" (toTStream t)
