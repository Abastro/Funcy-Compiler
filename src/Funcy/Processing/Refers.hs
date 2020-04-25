{-# LANGUAGE TypeFamilies #-}

module Funcy.Processing.Refers where

import Control.Monad.Reader
import Control.Monad.Writer

import Data.Functor.Identity
import Data.Foldable

import qualified Data.Set as Set
import qualified Data.Graph as Graph
import qualified Data.Map.Strict as MapS
import qualified Data.Map.Lazy as MapL

import Funcy.Processing.AST

{-----------------------------------------------------------------------------------------------------------------------------------
                                                        Reference Tracking
------------------------------------------------------------------------------------------------------------------------------------}

data Multi t = Bi (Binary t) | Multi [(Binding, t)]

class MultiSugar p where
    type Desugar p
    -- Extract the Binding involved.
    binding :: p -> Maybe Binding

    -- Interpret the flag, possibly with ID. Multiple one happens with cyclic references.
    interpret :: [Binding] -> p -> Desugar p


-- Map from references
newtype Refer t = MkRefs { runRef :: MapS.Map Binding t }


singleRef :: Binding -> t -> Refer t
singleRef ident = MkRefs . MapS.singleton ident

removeRef :: Binding -> Refer t -> Refer t
removeRef ident  = MkRefs . MapS.delete ident . runRef

removeRefs :: [Binding] -> Refer t -> Refer t
removeRefs idents = MkRefs . (`MapS.withoutKeys` Set.fromList idents) . runRef

allRefs :: Refer t -> [Binding]
allRefs = MapS.keys . runRef

instance Semigroup t => Semigroup (Refer t) where
    x <> y = MkRefs $ MapS.unionWith (<>) (runRef x) (runRef y)
instance Semigroup t => Monoid (Refer t) where
    mempty = MkRefs MapS.empty


type Location = [Binding]

type RWT r w m a = ReaderT r (WriterT w m) a

type Organize a = RWT Location (Refer Location) Identity a

{-----------------------------------------------------------------------------------------------------------------------------------
                                                        Reference Organizing
------------------------------------------------------------------------------------------------------------------------------------}

-- Finds unbound references and Sorts referencs by referential order.
-- Also converts multiple branch into binaries
organizeRefs :: MultiSugar p => AST Multi p -> Organize (AST Binary (Desugar p))
organizeRefs (Leaf (InRef ref)) = do
    location <- ask
    writer (Leaf (InRef ref),
        singleRef ref location) -- Tracks head only

organizeRefs (Leaf ref) = pure $ Leaf ref

organizeRefs (Branch flag (Bi br)) = pass $ do
    br' <- traverse organizeRefs br -- Traverse over the branch, tracking references
    pure (Branch (interpret [] flag) br', -- (Re-)attach flag
        maybe id removeRef (binding flag)) -- Remove references to current binding

organizeRefs (Branch flag (Multi brs)) = pass $ do
    brs' <- traverse subCall brs -- Traverse over the branch, tracking references
    let sorted = Graph.stronglyConnComp brs' -- Topological sort
    brs'' <- traverse foldComp sorted -- Traverse over components, folding it into individual branch
    pure (foldl' step initial brs'', -- Accumulates the result
        removeRefs $ fmap fst brs) -- Remove references to current binding
    where
        subCall (id, br) = do
            br' <- listen $ local (id :) $ organizeRefs br -- Call with updated location
            pure ((id, fst br'), id, allRefs $ snd br')

        foldComp (Graph.AcyclicSCC br) = pure $ singular br
        foldComp (Graph.CyclicSCC brs) = pure (fmap fst brs,
            foldl' step initial $ fmap singular brs) -- Accumulates cyclic references separately

        initial = Leaf (Internal "Chain") -- Placeholder
        step other (idents, cont) = Branch (interpret idents flag) $ Binary cont other
        singular (ident, t) = ([ident], t)

