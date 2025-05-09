{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE LambdaCase #-}

module Parser where

import Prelude hiding ( (<>), (^), Word, (*) )
import Control.Monad ( join, liftM2 )
import Data.Function ( fix )
import Data.Functor ( (<&>) )
import Data.List ( isPrefixOf, stripPrefix )
import Memo
import TypeSystem (Denot, Ty (..), Mode, Op (..), Effect (..), baseTypeCombinations, combineEffects, functor, adjunction, appl, monad, monoid, commutative, (%), denotOP, eval) -- here are the current requirements
import Lang


data SynTree
  = Leaf String Denot Ty
  | Branch SynTree SynTree
  | Island SynTree SynTree
  deriving ( Show, Eq )


-- Returns all syntactically valid parse trees
coreParser ::
  Monad m
  => CFG
  -> ((Int, Int, Phrase) -> m [(Cat, SynTree)])
  ->  (Int, Int, Phrase) -> m [(Cat, SynTree)]
coreParser _ _ (_, _, [(s, sign)]) = return [(c, Leaf s d t) | (d, c, t) <- sign]
coreParser cfg parse phrase = concat <$> mapM help (bisect phrase)
  where
    bisect (lo, hi, u) = do
      i <- [1 .. length u - 1]
      let (ls, rs) = splitAt i u
      let break = lo + i
      return ((lo, break - 1, ls), (break, hi, rs))

    help (ls, rs) = do
      parsesL <- parse ls
      parsesR <- parse rs
      return $
        [ (cat, mkIsland cat lsyn rsyn)
        | (lcat, lsyn) <- parsesL
        , (rcat, rsyn) <- parsesR
        , cat <- cfg lcat rcat
        ]

    mkIsland CP = Island
    mkIsland _  = Branch


parse :: Lang -> String -> Maybe [SynTree]
parse lang input = do
  let lexes = filter (/= "") $ words input >>= stripClitics
  ws <- mapM (\s -> (s,) <$> lookup s (lexicon lang)) lexes
  return $ snd <$> memo (coreParser $ grammar lang) (0, length ws - 1, ws)
  where
    stripClitics s = clitics >>= \c -> maybe [s] ((:[c]) . reverse) $ stripPrefix (reverse c) (reverse s)
    clitics = ["'s"]


-- Now for the semantics deriving
-- Use of a monad m is for easing memoization.
-- Returns a wrapped list of all possible combinations with their resulting type, given a pair of types.
-- This amounts to describing the rules of creation of the typing rules that propagate effects up.
-- The limitation on the number of effects should be done during parsing, according to some confluent rewriting system.
typeCombinations :: Monad m => ((Ty, Ty) -> m [(Mode, Denot, Ty)]) -> (Ty, Ty) -> m [(Mode, Denot, Ty)]
typeCombinations combine (l, r) =
  return (baseTypeCombinations l r)
  <+> case l of
    Eff f a | functor f ->
      combine (a, r) <&>
      map \(op, d, t) -> (ML f:op, denotOP (ML f) % d, Eff f t)
    _ -> return []

  <+> case r of
    Eff f b | functor f ->
      combine (l, b) <&>
      map \(op, d, t) -> (MR f:op, denotOP (MR f) % d, Eff f t)
    _ -> return []

  <+> case l of
    Eff f a | appl f ->
      combine (a, r) <&>
      map \(op, d, t) -> (UR f:op, denotOP (UR f) % d, Eff f t)
    _ -> return []

  <+> case r of
    Eff f b | appl f ->
      combine (l, b) <&>
      map \(op, d, t) -> (UL f:op, denotOP (UL f) % d, Eff f t)

  <+> case (l, r) of
    (Eff f a, Eff g b) | appl f ->
      combine (a, b) <&>
      liftM2 (\h (op, d, c) -> let m = A h
                                in (m:op, denotOP m % d, Eff h c)) (combineEffects f g)
    _ -> return []

  <+> case (l, r) of
    (Eff f a, Eff g b) | adjunction f g ->
      combine (a, b) <&>
      concatMap \(op, d, c) -> do (m, eff) <- [(Eps, id), (XL f Eps, Eff f)]
                                  return (m:op, denotOP m % d, eff c)
    _ -> return []

  where
    infixr 6 <+>
    (<+>) = liftM2 (++)

combineWith tag handler =
  curry $ fix $ memoizeTag tag . ((handler <$>) .) . typeCombinations

data SemObj
  = Lex Denot
  | Comb Mode Denot
  deriving (Eq, Show)

getDenote :: SemObj -> Denot
getDenote (Lex w)    = w
getDenote (Comb m d) = d

data Derivation = Derivation String SemObj Ty [Derivation]
  deriving (Show, Eq)

hasType :: Ty -> Derivation -> Bool
hasType t (Derivation _ _ t' _) = t == t'

derive :: SynTree -> [Derivation]
derive = execute . go
  where
    go = \case
      Leaf   s d t -> return [Derivation s (Lex d) t []] -- Amount to Axioms
      Branch l r   -> goWith False id l r
      Island l r   -> goWith True (filter $ \(_,_,t) -> True) l r

    goWith tag handler l r = do
      lefts  <- go l
      rights <- go r
      concat <$> sequence do
        lp@(Derivation lstr lval lty _) <- lefts
        rp@(Derivation rstr rval rty _) <- rights
        return do
          combos <- combineWith tag handler lty rty
          return do
            (op, d, ty) <- combos
            let cval = Comb op (eval $ d % getDenote lval % getDenote rval)
            return $ Derivation (lstr ++ " " ++ rstr) cval ty [lp, rp]
