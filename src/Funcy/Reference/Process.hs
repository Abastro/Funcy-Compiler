module Funcy.Reference.Process (
  ReferSugar(..), procRearrange
) where

import Data.Coerce ( coerce )

import Funcy.Base.Util
import Funcy.Base.AST
import Funcy.Reference.Refers

-- TODO transition to next form
class Traversable t => ReferSugar t where
  -- |Index each part
  tagPart :: t a -> t (SyntaxIndex [], a)

  -- |Desugar process
  desugar :: t a -> Desugar t

instance WithProperty Traversing ReferSugar where
  property _ = Traversing traverse


procRearrange :: ASTProcOn ReferSugar Rearrange Referred
procRearrange = mkProcess (TypeClassOf @ReferSugar)
  $ internalProcRearr (Indexing tagPart) (Specific desugar)


{-------------------------------------------------------------------
                          Basic instance
--------------------------------------------------------------------}


-- |Reference case
instance ReferSugar Reference where
  tagPart = coerce
  desugar ref = Desugar {
    _expandPart = defaultExpandPart, -- Placeholder
    _foldInto = Refers $ getReference ref
  }
