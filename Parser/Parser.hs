{-# LANGUAGE LambdaCase #-}

module Parser where

import Prelude hiding (Word)
import Memo
import Lang
import TypeSystem



data SynTree
  = Leaf String Sense
  | Branch SynTree SynTree
  | Island SynTree SynTree
