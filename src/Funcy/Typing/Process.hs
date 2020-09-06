module Funcy.Typing.Process (
  InferType(..), 
) where

import Control.Monad.Except (MonadError(..))

import Data.Coerce ( coerce )

import Funcy.Base.Util
import Funcy.Base.Message
import Funcy.Base.AST
import Funcy.Typing.Infers


class Traversable t => InferType t where
  -- |Tag the part
  tagTPart :: Stacking InferType p -> t a -> t (TypingIndex p, a)
  -- |Combine input types to form a type
  combine :: Stacking InferType p -> t p -> Infer p p

instance WithProperty Traversing InferType where
  property _ = Traversing traverse


procInfer :: ASTProcOn InferType (Infer (ASTOn InferType))
  (TypedTerm (ASTOn InferType))
procInfer = mkProcess (TypeClassOf @InferType)
  (internalProcInfer (Indexing $ tagTPart astStacking) (TypeCombine $ combine astStacking))


{-------------------------------------------------------------------
                          Basic instance
--------------------------------------------------------------------}


-- |Reference case
instance InferType Reference where
  tagTPart st = coerce
  combine st (Reference ref) = do
    -- Extracts from context (Recursive ones are desugar-ed with fix operator)
    tp <- boundOf ref >>= maybe (throwError $ referError ref) pure
    pure tp
