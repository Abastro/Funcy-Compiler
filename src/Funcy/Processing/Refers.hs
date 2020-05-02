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


-- Reference-specific branch structure
data Multi t = Bi (Binary t) | Multi [(Binding, t)]

refChain = Internal ["Chain"]

{-----------------------------------------------------------------------------------------------------------------------------------
                                                        Reference Tracking
------------------------------------------------------------------------------------------------------------------------------------}

-- TODO Syntactic sugar handling
-- TODO Load required module first (Need elaborate module system)
-- Dot-overloading (foo.bar) - As a class constraint, resolved right away when trivial

class MultiSugar p where
    type Desugar p
    -- Extract the Binding involved.
    binding :: p -> Maybe Binding

    -- Interpret the flag, possibly with ID. Multiple one happens with cyclic references.
    interpret :: [Binding] -> p -> Desugar p


-- Map from references
type Refer t = MapS.Map Binding t

removeRefs :: [Binding] -> Refer t -> Refer t
removeRefs idents = (`MapS.withoutKeys` Set.fromList idents)

{-
instance Semigroup t => Semigroup (Refer t) where
    x <> y = MkRefs $ MapS.unionWith (<>) (runRef x) (runRef y)
instance Semigroup t => Monoid (Refer t) where
    mempty = MkRefs MapS.empty
-}

type Location = [Binding]

type Organize a = ReaderT Location (WriterT (Refer Location) Identity) a

{-----------------------------------------------------------------------------------------------------------------------------------
                                                        Reference Organizing
------------------------------------------------------------------------------------------------------------------------------------}

-- Finds unbound references and Sorts referencs by referential order.
-- Also converts multiple branch into binaries
organizeRefs :: MultiSugar p => AST Multi p -> Organize (AST Binary (Desugar p))
organizeRefs (Leaf (InRef ref)) = do
    location <- ask
    writer (Leaf (InRef ref),
        MapS.singleton ref location) -- Tracks head only

organizeRefs (Leaf ref) = pure $ Leaf ref

organizeRefs (Branch flag (Bi br)) = pass $ do
    -- TODO: Localize location
    br' <- traverse organizeRefs br -- Traverse over the branch, tracking references
    pure (Branch (interpret [] flag) br', -- (Re-)attach flag
        maybe id MapS.delete (binding flag)) -- Remove references to current binding

organizeRefs (Branch flag (Multi brs)) = pass $ do
    brs' <- traverse subCall brs -- Traverse over the branch, tracking references
    let sorted = Graph.stronglyConnComp brs' -- Topological sort
    brs'' <- traverse foldComp sorted -- Traverse over components, folding it into individual branch
    pure (foldl' step initial brs'', -- Accumulates the result
        removeRefs $ fmap fst brs) -- Remove references to current binding
    where
        subCall (id, br) = do
            br' <- listen $ local (id :) $ organizeRefs br -- Call with updated location
            pure ((id, fst br'), id, MapS.keys $ snd br')

        foldComp (Graph.AcyclicSCC br) = pure $ singular br
        foldComp (Graph.CyclicSCC brs) = pure (fmap fst brs,
            foldl' step initial $ fmap singular brs) -- Accumulates cyclic references separately

        initial = Leaf refChain -- Placeholder
        step other (idents, cont) = Branch (interpret idents flag) $ Binary cont other
        singular (ident, t) = ([ident], t)

