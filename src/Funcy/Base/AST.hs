{-------------------------------------------------------------------
                      Abstract Syntax Tree
--------------------------------------------------------------------}

{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE ExistentialQuantification #-}
module Funcy.Base.AST (
  Binding, Loc(..), Reference(..),
  Nodal, Node(..), getMetadata,
  AST, StOn(..), astStack,
  mapHover, stateHover, stateInvHover, stTravHover,
  indexHover, travHover, itravHover,
  ASTProcIn, ASTProc, genProcOver,
) where

import Data.Tuple

import Control.Monad.State ( StateT(..) )

import Control.Lens.Type ( LensLike, Traversal, Iso )
import qualified Control.Lens.Combinators as Lens

import Funcy.Base.Util
import Funcy.Base.Recursive

-- |Binding reference name
type Binding = String

data Loc = Loc {
  beginOffset :: Int,
  endOffset :: Int
}

newtype Reference a = Reference {
  getReference :: Binding
} deriving (Functor, Foldable, Traversable)


type Nodal t k a = (k, t a)
data Node (c :: TypeClass) k a = forall t. (c t) => Node (Nodal t k a)
type AST c k = Fix (Node c k)
newtype StOn c k a = StOn {
  stack :: forall t. (c t) => k -> t a -> a
}

astStack :: StOn c k (AST c k)
astStack = StOn $ fmap (Fix . Node) . (,)

getMetadata :: Node c k a -> k
getMetadata (Node (m, _)) = m

-- |Mapping Hover
mapHover :: (Traversable t) => Traversal (Nodal t k a) (Nodal t k b) (t a) (t b)
mapHover = content

-- |Stateful Hover
stateHover :: (Functor m) =>
  (k -> StateT (t a) m l) -> Nodal t k a -> m (Nodal t l a)
stateHover = uncurry . fmap runStateT

-- |Stateful inverse hover, where metadata is the state
stateInvHover :: (Functor m) =>
  (t a -> StateT k m (t b)) -> Nodal t k a -> m (Nodal t k b)
stateInvHover = uncurry . flip . fmap (fmap (fmap swap) . runStateT)

-- |Stateful inverse traversing hover
stTravHover :: (Monad m, Traversable t) =>
  (a -> StateT k m b) -> Nodal t k a -> m (Nodal t k b)
stTravHover = stateInvHover . Lens.traversed

-- |Indexed Hover
indexHover :: (Traversable t) => Iso (t a) (t b) (t (i, a)) (t (j, b)) ->
  Traversal (Nodal t k a) (Nodal t k b) (Nodal t k (i, a)) (Nodal t k (j, b))
indexHover indexing = Lens.alongside id indexing

-- |Traversing Hover, usually for subcall
travHover :: (Traversable t) => Traversal (Nodal t k a) (Nodal t k b) a b
travHover = content . Lens.traversed

-- |Traversing Hover with Index, usually for subcall
itravHover :: (Traversable t) => Iso (t a) (t b) (t (i, a)) (t (i, b)) ->
  Traversal (Nodal t k a) (Nodal t k b) (i, a) (i, b)
itravHover indexing = content . indexing . Lens.traversed


-- |Internal AST Process
type ASTProcIn t m k l a b = LensLike m (Nodal t k a) (Nodal t l b) a b

-- |Typeclassed AST Process
type ASTProcOn c m k l a b =
  LensLike m (Node c k a) (Node c l b) a b

-- |Exposed AST Process
type ASTProc c m k l = ASTProcOn c m k l (AST c k) (AST c l)

-- |Generalize process over a typeclass
genProcOver :: (Monad m) => (forall t. (c t) => ASTProcIn t m k l a b) ->
  ASTProcOn c m k l a b
genProcOver l f (Node nodal) = Node <$> l f nodal

