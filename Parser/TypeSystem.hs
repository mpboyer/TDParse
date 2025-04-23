{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TupleSections #-}

module TypeSystem where

import Prelude hiding ( (<>), (^), Word, (*) )
import Control.Monad ( join, liftM2 )
import Data.Function ( fix )
import Data.Functor ( (<&>) )
import Data.List ( isPrefixOf, stripPrefix )
import Memo

type Denot = String

infixr :->
data Ty
  = E | T -- Base Types are provided here. A typer should be provided to help with denotations.
  | Unit -- Unit should never be used, but is here to provide ccc structure
  | Ty :-> Ty
  | Eff Effect Ty
  | Pair Ty Ty -- could be written as a function but heh
  deriving (Eq, Show, Ord)

data Effect
  = U
  | S    -- Set
  | F    -- Id x Set (Emphasis)
  | M    -- Maybe
  | C Ty -- Predicate Application
  | G Ty -- Read
  | W Ty -- Write
  | D Ty -- State Expresser
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
  L u v == L t r = u == t && v == r

invertible :: Effect -> Bool
invertible (W _) = False
invertible _     = True

canInvert op =
  \case
    MR f -> not ([ML f] `isPrefixOf` op) || invertible f
    _ -> True

-- convenience constructors
effS     = Eff S
effF     = Eff F
effM     = Eff M
effC t   = Eff (C t)
effG r   = Eff (G r)
effW t   = Eff (W t)
effU     = Eff U
effL s e = Eff (L s e)

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
instance Commute Ty where
  commutative = monoid
instance Commute Effect where
  commutative = \case
    S -> True
    M -> True
    F -> True
    G _ -> True
    W w -> commutative w
    L _ _ -> False
    U     -> False


type Mode = [Op] -- left currified
data Op
  = FA | BA | PM | FC     -- Base        > < & .
  | MR Effect | ML Effect -- Functor     fmap
  | UR Effect | UL Effect -- Applicative pure
  | A Effect              -- Applicative <*>
  | J Effect              -- Monad       join
  | Eps                   -- Adjoint     counit
  | D                     -- Cont        lower
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
    D      -> "D"
    XL f o -> "XL " ++ show o


modes :: Ty -> Ty -> [(Mode, Denot, Ty)]
modes = curry \case
  (,) (a :-> b) r         | a == r -> [([FA], show FA, b)]
  (,) l         (a :-> b) | l == a -> [([BA], show BA, b)]
  (,) (a :-> T) (b :-> T) | a == b -> [([PM], show PM, a :-> T)]
  (,) _         _                  -> []

-- data Effect = U | S | F | M | C Ty | G Ty | W Ty | L Ty Ty
combineEffects :: Effect -> Effect -> [Effect]
combineEffects = curry \case
  (,) U       U                  -> [U]
  (,) S       S                  -> [S]
  (,) F       F                  -> [F]
  (,) M       M                  -> [M]
  (,) (G i)   (G j)    | i == j  -> [G i]
  (,) (W i)   (W j)    | i == j  -> [W i]
  (,) (C i)   (C j)    | i == j  -> [C i]
  (,) (L i j) (L j' k) | j == j' -> [L i k]
  (,) _        _                 -> []

combineWith tag handler =
  curry $ fix $ memoizeTag tag . ((handler <$>) .) . combineTypes

combineTypes ::
  Monad m
  => ((Ty, Ty) -> m [(Mode, Denot, Ty)])
  ->  (Ty, Ty) -> m [(Mode, Denot, Ty)]
combineTypes combine (l, r) = map (\(m,d,t) -> (m, d, t)) . concat <$>

  -- for starters, try the basic modes of combination
  return (modes l r)

  -- then if the left daughter is Functorial, try to find a mode
  -- `op` that would combine its underlying type with the right daughter
  <+> case l of
    Eff f a | functor f ->
      combine (a,r) <&>
      map \(op,d,c) -> (ML f:op, show (ML f) ++ d, Eff f c)
    _ -> return []

  -- vice versa if the right daughter is Functorial
  <+> case r of
    Eff f a | functor f ->
      combine (l,a) <&>
      concatMap \(op,d,c) -> let m = MR f
                              in [(m:op, show m ++ d, Eff f c) | canInvert op m]
    _ -> return []

  -- if the left daughter requests something Functorial, try to find an
  -- `op` that would combine it with a `pure`ified right daughter
  <+> case l of
    Eff f a :-> b | appl f ->
      combine (a :-> b,r) <&>
      concatMap \(op,d,c) -> let m = UR f
                              in [(m:op, show m ++ d, c) | norm op m]
    _ -> return []

  -- vice versa if the right daughter requests something Functorial
  <+> case r of
    Eff f a :-> b | appl f ->
      combine (l,a :-> b) <&>
      concatMap \(op,d,c) -> let m = UL f
                              in [(m:op, show m ++ d, c) | norm op m]
    _ -> return []

  -- additionally, if both daughters are Applicative, then see if there's
  -- some mode `op` that would combine their underlying types
  <+> case (l,r) of
    (Eff f a, Eff g b) | appl f ->
      combine (a, b) <&>
      liftM2 (\h (op,d,c) -> let m = A h
                              in (m:op, show m ++ d, Eff h c)) (combineEffects f g)
    _ -> return []

  -- if the left daughter is left adjoint to the right daughter, cancel them out
  -- and fina a mode `op` that will combine their underlying types
  -- note that the asymmetry of adjunction rules out xover
  -- there remains some derivational ambiguity:
  -- W,W,R,R has 3 all-cancelling derivations not 2 due to local WR/RW ambig
  -- also the left arg of Eps is guaranteed to be comonadic, so extend it
  <+> case (l,r) of
    (Eff f a, Eff g b) | adjunction f g ->
      combine (a, b) <&>
      concatMap \(op,d,c) -> do (m,eff) <- [(Eps, id), (XL f Eps, Eff f)]
                                return (m:op, show m ++ d, eff c)
    _ -> return []

  -- finally see if the resulting types can additionally be lowered/joined
  <**> return [addD, addJ, return]

  where
    infixr 6 <+>
    (<+>) = liftM2 (++)
    infixl 5 <**>
    (<**>) = liftM2 (flip (<*>))


norm op = \case
  UR f -> not $ (op `startsWith`) `anyOf` [[MR f], [D, MR f]]
  UL f -> not $ (op `startsWith`) `anyOf` [[ML f], [D, ML f]]
  D    -> not $ (op `startsWith`) `anyOf`
       [ [m U, D, m U] | m <- [MR, ML] ]
    ++ [ [ML U, D, MR U]
       , [A U, D, MR U]
       , [ML U, D, A U]
       , [Eps]
       ]
  J f  -> not $ (op `startsWith`) `anyOf`
       [ [m f]  ++ k ++ [m f]  | k <- [[J f], []], m <- [MR, ML] ]
    ++ [ [ML f] ++ k ++ [MR f] | k <- [[J f], []] ]
    ++ [ [A f]  ++ k ++ [MR f] | k <- [[J f], []] ]
    ++ [ [ML f] ++ k ++ [A f]  | k <- [[J f], []] ]
    ++ [           k ++ [Eps]  | k <- [[A f], []] ] -- safe if no lexical FRFs
    -- and all (non-split) inverse scope for commutative effects
    ++ [ [MR f   ,     A  f]   | commutative f ]
    ++ [ [A f    ,     ML f]   | commutative f ]
    ++ [ [MR f] ++ k ++ [ML f] | commutative f, k <- [[J f], []] ]
    ++ [ [A f]  ++ k ++ [A f]  | commutative f, k <- [[J f], []] ]

  _ -> True

  where
    infixl 4 `anyOf`
    anyOf = any
    startsWith = flip isPrefixOf

addJ :: (Mode, Denot, Ty) -> [(Mode, Denot, Ty)]
addJ = \case
  (op, d, Eff f (Eff g a)) | monad f, norm op (J f) ->
    [(J h:op, show (J h) ++ d, Eff h a) | h <- combineEffects f g]
  _ -> []

addD :: (Mode, Denot, Ty) -> [(Mode, Denot, Ty)]
addD = \case
  (op, d, Eff (L i a) a') | a == a', norm op D ->
    [(D:op, show D ++ d, i)]
  _ -> []
