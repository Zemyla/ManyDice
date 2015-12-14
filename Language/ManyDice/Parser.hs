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
import qualified Data.Vector as V
import Data.Vector (Vector)
import Data.Hashable
import qualified Text.Parsec as P
import Text.Parsec (ParsecT, unexpected, (<?>))
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
    -- | A part of a sequence converted to a number.
    | ESeqPart !SeqPart
    | EAbs !Expr
    | ELength !Expr
    | ESignum !Expr
    | ENegate !Expr
    | ENot !Expr
    | ELength !Expr
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
                | (dn, 0) <- div n nb -> ENum nb * (ENum dn + eb')
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
                | (dn, 0) <- div n nb -> ENum nb * (ENum dn - eb')
            _ -> ea :- eb
    ea - eb@(ENum n) = ea + ENum (negate n)
    ea@(al :+ ar) + eb
        | ENum na <- al = case eb of
            ENum nb :+ br -> ENum (na - nb) + (ar - br)
            ENum nb :- br -> ENum (na - nb) + (ar + br)
            _ -> al :+ (ar - eb)
        | otherwise = case eb of
            ENum nb :+ br -> ENum (negate nb) + (al + (ar - br))
            ENum nb :- br -> ENum (negate nb) + (al + (ar + br))
            _ -> al :+ (ar - eb)
    ea@(al :- ar) + eb
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

unop :: Parsec TStream u (Expr -> Expr)
unop = tokenP fn where
    enot (ENum n) = if n == 0 then ENum 1 else ENum 0
    enot e = ENot e

    edie e = Die (ENum 1) e ModNone

    fn (TFunWord t) = case T.compareLength t 1 of
        EQ -> if T.head t == 'd' then Just edie else Nothing
    fn (TChar c) = case c of
        '+' -> Just id
        '-' -> Just negate
        '!' -> Just enot
        '#' -> Just ELength
        _   -> Nothing
    fn _ = Nothing

