{-# LANGUAGE DeriveDataTypeable, AutoDeriveTypeable, BangPatterns #-}
{-# LANGUAGE FlexibleInstances #-}

-- |
-- Module       : Language.ManyDice.Parser
-- Copyright    : (c) 2015 Paul Drees
-- Maintainer   : zemyla@gmail.com
-- Stability    : experimental
-- Portability  : GHC
--
-- A parser for the ManyDice language. It takes a string of tokens from the
-- 'Language.ManyDice.Tokenizer', and turns them into an abstract syntax tree.

module Language.ManyDice.Parser where

import Language.ManyDice.Tokenizer
import Prelude hiding (foldl, foldr, sequence, mapM, mapM_)
import Control.Applicative
import Control.Monad
import qualified Data.Text as T
import Data.Text (Text)
import qualified Data.Text.Lazy as TL
import qualified Data.Text.Internal.Builder as TB
import Data.Text.Internal.Builder (Builder)
import qualified Data.Vector as V
import Data.Vector (Vector)
import Data.Hashable
import qualified Text.Parsec as P
import Text.Parsec (Parsec, ParsecT, unexpected, (<?>))
import qualified Text.Parsec.Combinator as P
import Text.Parsec.Combinator (sepBy, optionMaybe, chainl1, sepEndBy1, chainr1)
import qualified Data.Map.Strict as M
import Data.Map.Strict (Map)
import qualified Data.Sequence as Q
import Data.Sequence (Seq)
import Data.Data
import Data.Monoid
import Data.Foldable
import Data.Traversable
import Data.Bits
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
    signum e@(ESignum a) = e
    signum e@(ENot a) = e
    signum e@(a :& b) = e
    signum e@(a :| b) = e
    signum e@(a :<< b) = e
    signum e@(a :>> b) = e
    signum e@(a :<= b) = e
    signum e@(a :>= b) = e
    signum e@(a :== b) = e
    signum e@(a :/= b) = e
    signum (ENum n :* a) = ENum (signum n) * signum a
    signum e = ESignum e

    abs (ENum n) = ENum (abs n)
    abs (ENegate a) = abs a
    abs e@(ELength a) = e
    abs e@(EAbs a) = e
    abs e@(ENot a) = e
    abs e@(a :& b) = e
    abs e@(a :| b) = e
    abs e@(a :<< b) = e
    abs e@(a :>> b) = e
    abs e@(a :<= b) = e
    abs e@(a :>= b) = e
    abs e@(a :== b) = e
    abs e@(a :/= b) = e
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
            _ -> ENum n :+ eb
    ea + eb@(ENum n) = eb + ea
    ea@(al :+ ar) + eb
        | ENum na <- al = case eb of
            ENum nb :+ br -> ENum (na + nb) + (ar + br)
            ENum nb :- br -> ENum (na + nb) + (ar - br)
            _ -> al :+ (ar + eb)
        | otherwise = case eb of
            bl@(ENum nb) :+ br -> bl :+ (al + (ar + br))
            bl@(ENum nb) :- br -> bl :+ (al + (ar - br))
            _ -> al :+ (ar + eb)
    ea@(al :- ar) + eb
        | ENum na <- al = case eb of
            ENum nb :+ br -> ENum (na + nb) + (br - ar)
            ENum nb :- br -> ENum (na + nb) - (ar + br)
            _ -> al :+ (ar + eb)
        | otherwise = case eb of
            bl@(ENum nb) :+ br -> bl :+ (al + (br - ar))
            bl@(ENum nb) :- br -> bl :+ (al - (br + ar))
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
    ea - eb@(ENum n) = ea + ENum (negate n)
    ea@(al :+ ar) - eb
        | ENum na <- al = case eb of
            ENum nb :+ br -> ENum (na - nb) + (ar - br)
            ENum nb :- br -> ENum (na - nb) + (ar + br)
            _ -> al :+ (ar - eb)
        | otherwise = case eb of
            ENum nb :+ br -> ENum (negate nb) + (al + (ar - br))
            ENum nb :- br -> ENum (negate nb) + (al + (ar + br))
            _ -> al :+ (ar - eb)
    ea@(al :- ar) - eb
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
    ea * eb@(ENum nb) = eb * ea
    (al :* ar) * eb
        | ENum na <- al = case eb of
            ENum nb :* br -> ENum (na * nb) :* (ar * br)
            _ -> al :* (ar * eb)
        | otherwise = case eb of
            bl@(ENum nb) :* br -> bl :* (al * (ar * br))
            _ -> al :* (ar * eb)
    ea * eb@(_ :* _) = eb * ea
    ea * eb = ea :* eb

unop :: Parsec TStream () (Expr -> Expr)
unop = (tokenP fn <?> "unary operator") <|> pure id where
    enot (ENum n) = if n == 0 then ENum 1 else ENum 0
    enot e = ENot e

    edie e = Die (ENum 1) e ModNone

    fn (TFunName t) = case T.compareLength t 1 of
        EQ -> if T.head t == 'd' then Just edie else Nothing
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
    eand (ENum na) (ENum nb) = ENum 1
    eand ea eb = ea :& eb

    eor (ENum na) _ | na /= 0 = ENum 1
    eor _ (ENum nb) | nb /= 0 = ENum 1
    eor (ENum na) (ENum nb) = ENum 0
    eor ea eb = ea :| eb

    ediv ea eb@(ENum 0) = ea :/ eb
    ediv ea eb@(ENum 1) = ea
    ediv ea eb@(ENum (-1)) = negate ea
    ediv (ENum na) _ | na == 0 = ENum 0
    ediv (ENum na) (ENum nb) = ENum (div na nb)
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
        0 -> unop <*> baseValue
        n -> case (V.!) binopV (n - 1) of
            Left op -> chainl1 (V.last v) op
            Right op -> chainr1 (V.last v) op

exprP :: Parsec TStream () Expr
exprP = V.last exprV

baseValue :: Parsec TStream () Expr
baseValue = (tokenP vfn <?> "value") <|> tchar '(' *> exprP <* tchar ')' <|> tchar '{' *> seqList <* tchar '}' <|> (bracket >>= verify) {- <|> reserved "legacy" *> tchar '"' *> exprL <* tchar '"' -} where
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
seqList = toExpr <$> sepBy seqVal (tchar ',') where
    toExpr ls = ESequence $ Q.fromList ls

funVal :: Parsec TStream () (Either Text Expr)
funVal = Right <$> exprP <|> (tokenP fn <?> "function word") where
    fn (TFunName t) = case T.compareLength t 1 of
        EQ -> if T.head t == 'd' then Nothing else Just (Left t)
        _ -> Just (Left t)
    fn _ = Nothing

bracket :: Parsec TStream () (Text, Seq Text, Seq Expr)
bracket = tchar '[' *> (go <$> funVal <*> many funVal) <* tchar ']' where
    append (b, st, sv) _ | b `seq` st `seq` sv `seq` False = undefined
    append (b, st, sv) (Left t) = (b', st', sv) where
        !b' = b <> TB.singleton ' ' <> TB.fromText t
        !st' = (Q.|>) st t
    append (b, st, sv) (Right v) = (b', st, sv') where
        !b' = b <> TB.fromString (' ':show (Q.length sv))
        !sv' = (Q.|>) sv v

    go tv ls = let
        !iv = case tv of
            Left t -> (TB.fromText t, Q.singleton t, mempty)
            Right v -> (TB.singleton '0', mempty, Q.singleton v)
        in case foldl' append iv ls of
            (b, st, sv) -> (t, st, sv) where
                !t = TL.toStrict $ TB.toLazyText b
