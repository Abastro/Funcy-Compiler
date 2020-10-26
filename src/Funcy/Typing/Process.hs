module Funcy.Typing.Process (
  InferType(..), procInfer,
) where

import Control.Monad.Except (MonadError(..))

import Data.Coerce ( coerce )

import Funcy.Base.Util
import Funcy.Base.Message
import Funcy.Base.Recursive
import Funcy.Base.AST
import Funcy.Typing.Infers


class Traversable t => InferType t where
  -- |Tag the part
  tagTPart :: StOn InferType Loc p ->
    t a -> t (TypeBinder p, a)
  -- |Combine input types to form a type
  combine :: StOn InferType Loc p ->
    t p -> Infer p p

procInfer :: ASTProc InferType (Infer (AST InferType Loc)) Loc Loc
procInfer = genProcOver $ intProcInfer
  (getMetadata . unfix) astStack
  (Indexing $ tagTPart astStack)
  (TypeCombine $ combine astStack)

{-------------------------------------------------------------------
                          Basic instance
--------------------------------------------------------------------}

-- |Reference case
instance InferType Reference where
  tagTPart _ = coerce
  combine _ (Reference ref) = do
    -- Extracts from context (Recursive ones are desugar-ed with fix operator)
    tp <- boundOf ref >>= maybe (throwError $ referError ref) pure
    pure tp
