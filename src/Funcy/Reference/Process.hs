module Funcy.Reference.Process (
  ReferSugar(..), procRearrange
) where

import Data.Coerce ( coerce )

import Funcy.Base.Util
import Funcy.Base.Recursive
import Funcy.Base.AST
import Funcy.Reference.Refers

-- TODO transition to next form
class Traversable t => ReferSugar t where
  -- |Index each part
  tagIndex :: t a -> t (SIndex [], a)

  -- |Desugar process
  desugar :: t a -> Desugar t

procRearrange :: ASTProc ReferSugar Rearrange Loc Loc
procRearrange = genProcOver $ intProcRearr
  (getMetadata . unfix) (Indexing tagIndex) (Specific desugar)


{-------------------------------------------------------------------
                          Basic instance
--------------------------------------------------------------------}


-- |Reference case
instance ReferSugar Reference where
  tagIndex = coerce
  desugar ref = Desugar {
    _expandPart = defaultExpandPart, -- Placeholder
    _foldInto = Refers $ getReference ref
  }
