{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE LambdaCase #-}

module Lang where

import Control.Monad (join, liftM2)
import Data.Function (fix)
import Data.Functor ((<&>))
import Data.List (isPrefixOf, stripPrefix)
import Memo
import TypeSystem -- Note that the Type System here, is seen as the base
-- TypeSystem is to be seen as part of the language, but is not as it also includes denotations.
import Prelude hiding (Word, (*), (<>), (^))

data Cat
  = CP
  | Cmp
  | CBar
  | DBar
  | Cor
  | DP
  | Det
  | Gen
  | GenD
  | Dmp
  | NP
  | TN
  | VP
  | TV
  | DV
  | AV
  | AdjP
  | TAdj
  | Deg
  | AdvP
  | TAdv
  deriving (Eq, Show, Ord)

type CFG = Cat -> Cat -> [Cat]

demoCFG :: CFG
demoCFG = curry \case
  (DP, VP) -> [CP]
  (Cmp, CP) -> [CP]
  (Cor, CP) -> [CBar]
  (Cor, DP) -> [DBar]
  (DP, DBar) -> [DP]
  (Dmp, DP) -> [DP]
  (CP, CBar) -> [CP]
  (Det, NP) -> [DP]
  (Gen, TN) -> [DP]
  (DP, GenD) -> [Gen]
  (AdjP, NP) -> [NP]
  (NP, AdjP) -> [NP]
  (TAdj, DP) -> [AdjP]
  (Deg, AdjP) -> [AdjP]
  (TV, DP) -> [VP]
  (AV, CP) -> [VP]
  (DV, DP) -> [TV]
  (VP, AdvP) -> [VP]
  (TAdv, DP) -> [AdvP]
  (_, _) -> []

type Sense = (Denot, Cat, Ty)
type Word = (String, [Sense])
type Phrase = [Word]
type Lexicon = [Word]

data Lang = Lang {lexicon :: Lexicon, grammar :: CFG}
