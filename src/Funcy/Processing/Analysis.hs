{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeFamilies #-}

module Funcy.Processing.Analysis where

import Control.Applicative
import Control.Monad.Reader
import Control.Monad.Writer
import Control.Monad.Except
import Control.Monad.State

import Data.List
import Data.Function
import Data.Functor
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

data MultiBranch t = NormBranch (BiBranch t) | MultiBranch [(Binding, t)]

class MultiSugar p where
    type Desugar p
    interpret :: p -> Desugar p
    binding :: p -> Maybe Binding
    withId :: p -> Binding -> Desugar p


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
type Detail = Location

type RWT r w m a = ReaderT r (WriterT w m) a

type Organize a = RWT Location (Refer Detail) Identity a

{-----------------------------------------------------------------------------------------------------------------------------------
                                                        Reference Organizing
------------------------------------------------------------------------------------------------------------------------------------}

-- Log the error for later
asErr :: Graph.SCC (Binding, a) -> Location -> Refer Detail
asErr (Graph.AcyclicSCC _) _ = mempty
asErr (Graph.CyclicSCC vertices) loc = let refs = fmap fst vertices
    in singleRef (":cyclic:" <> mconcat (intersperse "," refs)) $ loc <> (":" : refs) -- Need to elaborate error

-- Finds unbound references and Sorts referencs by referential order, while converting multiple branch into binaries
organizeRefs :: MultiSugar p => AST MultiBranch p -> Organize (AST BiBranch (Desugar p))
organizeRefs (Leaf (InRef ref)) = do
    location <- ask
    writer (Leaf (InRef ref),
        singleRef (head ref) location) -- Tracks head only

organizeRefs (Leaf ref) = pure $ Leaf ref

organizeRefs (Branch flag (NormBranch br)) = pass $ do
    br' <- traverse organizeRefs br -- Traverse over the branch, tracking references
    pure (Branch (interpret flag) br', -- (Re-)attach flag
        maybe id removeRef (binding flag)) -- Remove references to current binding

organizeRefs (Branch flag (MultiBranch brs)) = pass $ do
    brs' <- traverse preSort brs -- Traverse over the branch, tracking references
    let sorted = Graph.stronglyConnComp brs' -- Topological sort
    brs'' <- traverse postSort sorted -- Traverse over components, flattening it
    pure (foldl' step initial $ mconcat brs'', -- Accumulates the result
        removeRefs $ fmap fst brs) -- Remove references to current binding
    where
        preSort (id, br) = do
            br' <- listen $ local (id :) $ organizeRefs br
            pure ((id, fst br'), id, allRefs $ snd br')        
        postSort :: Graph.SCC (Binding, a) -> Organize [(Binding, a)]
        postSort comp = do
            location <- ask
            writer (Graph.flattenSCC comp, asErr comp location)
        initial = Leaf (Internal "Chain") -- Placeholder
        step other (ident, cont) = Branch (withId flag ident) $ BiBranch cont other


{-----------------------------------------------------------------------------------------------------------------------------------
                                                Typing & Reference Validity Checking
------------------------------------------------------------------------------------------------------------------------------------}

{-
t1 ~ t2, (term) unification (System of equation solving)
Full equality / inference with implementation detals hidden
_ : tp, proof search
Rules of Constructions
-}

-- Typeclass for typed terms
class Typer p where
    findType :: p -> BiBranch (Infer (Term p) a) -> Infer (Term p) a
    unify :: Constraint (Term p) -> Solve (Term p) a
    unifyMany :: [Constraint (Term p)] -> Solve (Term p) a


-- Type analysis uses bibranch exclusively
type Term = AST BiBranch


-- Constaint t a b means a should unify with b under type t
data Constraint t = Constraint t t t

-- Known terms
type Known t = MapL.Map String t

-- Unified terms
type Unified t = (Known t, [Constraint t])


-- Denotes inference procedure
type Infer t a = RWT (Known t) [Constraint t] Identity a

-- Denotes solving procedure
type Solve t a = StateT (Unified t) Identity a


infer :: Typer p => Term p -> Infer (Term p) (Term p)
infer (Leaf ref) = case ref of
    InRef (x : xs) -> do
        _
    Internal _ -> _
infer (Branch flag branch) = _