{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE LambdaCase #-}

module TypeSystem where

import Prelude hiding ( (<>), (^), Word, (*) )
import Control.Monad ( join, liftM2 )
import Data.Function ( fix )
import Data.Functor ( (<&>) )
import Data.List ( isPrefixOf, stripPrefix )
import Memo

type Denot = String

eval :: Denot -> Denot  -- Evaluation of an expression of denotations, amounts to a certain form of reductions.
eval = show

print :: Show m => m -> IO String
print x = return $ show x

infixl 8 %    -- Infix Application of Denotations
(%) = (++)

infixr :->
data Ty
  = E | T -- Base Types are provided here. A typer should be provided to help with denotations.
  | Unit -- Unit should never be used, but is here to provide ccc structure
  | Ty :-> Ty
  | Eff Effect Ty
  | Pair Ty Ty -- could be written as a function but heh
  deriving (Eq, Show, Ord)

data Effect
  = U     -- Identity
  | S     -- Set
  | F     -- Id x Set (Emphasis)
  | M     -- Maybe
  | C Ty  -- Predicate Application
  | G Ty  -- Read
  | W Ty  -- Write
  | D Ty  -- State Expresser
  deriving (Show, Ord)

instance Eq Effect where
  U  == _ = True
  _  == U = True
  S == S = True
  F == F = True
  M == M = True
  C u == C v = u == v
  G u == G v = u == v
  W u == W v = u == v
  D u == D v = u == v

-- convenience constructors
effU   = Eff U
effS   = Eff S
effF   = Eff F
effM   = Eff M
effC t = Eff (C t)
effG r = Eff (G r)
effW t = Eff (W t)
effD s = Eff (D s)

-- FIXME: replace with actual definitions when we have a functor to denot encoder
functor, appl, monad :: Effect -> Bool
functor _ = True
appl f@(W w) = functor f && monoid w
appl f = functor f && True
monad f = appl f && True

monoid :: Ty -> Bool
monoid T = True
monoid _ = False

adjunction :: Effect -> Effect -> Bool
adjunction (W i) (G j) = i == j
adjunction _ _ = False

class Commute f where
  commutative :: f -> Bool

instance Commute Ty where     -- Monoidic commutativity
  commutative = monoid

instance Commute Effect where -- Monadic commutativity
  commutative = \case
    S   -> True
    M   -> True
    F   -> True
    G _ -> True
    W w -> commutative w
    D _ -> False
    U   -> False

-- This is written here for simplicity during compilation as it should realistically be insinde the Parser.
type Mode = [Op] -- left currified
data Op
  = FA | BA | PM | FC     -- Base        > < & .
  | MR Effect | ML Effect -- Functor     fmap
  | UR Effect | UL Effect -- Applicative pure
  | A Effect              -- Applicative <*>
  | J Effect              -- Monad       join
  | Eps                   -- Adjoint     counit
  | DN                    -- Cont        lower
  | XL Effect Op          -- Comonad     extend
  deriving (Eq)

instance Show Op where
  show = \case
    FA     -> ">"
    BA     -> "<"
    PM     -> "&"
    FC     -> "."
    MR _   -> "R"
    ML _   -> "L"
    UL _   -> "UL"
    UR _   -> "UR"
    A  _   -> "A"
    J  _   -> "J"
    Eps    -> "Eps"
    DN     -> "D"
    XL f o -> "XL " ++ show o

denotOP :: Op -> Denot
denotOP = show

baseTypeCombinations :: Ty -> Ty -> [(Mode, Denot, Ty)]
baseTypeCombinations = curry \case
 (,) (a :-> b) r         | r == a -> [([FA], denotOP FA, b)]
 (,) l         (a :-> b) | l == a -> [([BA], denotOP BA, b)]
 (,) (a :-> T) (b :-> T) | a == b -> [([PM], denotOP PM, a :-> T)]  -- FIXME: handle necessity of type for truth values
 (,) _         _                  -> []

combineEffects :: Effect -> Effect -> [Effect]
combineEffects = curry \case
  (,) M       M                  -> [M]
  (,) F       F                  -> [F]
  (,) S       S                  -> [S]
  (,) (G i)   (G j)    | i == j  -> [G i]
  (,) (W i)   (W j)    | i == j  -> [W i]
  (,) (C i)   (C j)    | i == j  -> [C i]
  (,) (D i)   (D j)    | i == j  -> [D i]
  (,) _        _                 -> []
