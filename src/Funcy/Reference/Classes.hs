module Funcy.Reference.Classes (
  ReferSugar(..)
) where

import Funcy.Base.AST

class Traversable t => ReferSugar t where
  -- |Index each part
  --tagPart :: t a -> t (SIndexed [] a)

  -- |Desugar process
  --desugar :: t a -> Desugar t c

instance Collection ReferSugar where
  asTraversed _ = traverse
