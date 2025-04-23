module Denotation1 where

type Denot = String

data BTy = E | T deriving (Eq, Show, Ord)

monoid :: BTy -> Bool
monoid T = True
monoid _ = False
