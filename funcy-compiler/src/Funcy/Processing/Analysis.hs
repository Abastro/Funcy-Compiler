{-# LANGUAGE TypeFamilies #-}

module Funcy.Processing.Analysis where

import Control.Applicative
import Control.Monad.Reader
import Control.Monad.Writer
import Control.Monad.Except
import Control.Monad.State

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

class MultiSugar p where
    type Desugar p
    interpret :: p -> Desugar p
    binding :: p -> Maybe Binding
    withId :: p -> Binding -> Desugar p

{-----------------------------------------------------------------------------------------------------------------------------------
                                                        References
------------------------------------------------------------------------------------------------------------------------------------}
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


type Location = [String]
type Detail = [String]

{-----------------------------------------------------------------------------------------------------------------------------------
                                                        Reference Organizing
------------------------------------------------------------------------------------------------------------------------------------}

asErr :: Graph.SCC (String, Writer (Refer Detail) a) -> Refer Detail
asErr (Graph.AcyclicSCC _) = mempty
asErr (Graph.CyclicSCC vertices) = let refs = fmap fst vertices in singleRef ("_cyclic" <> mconcat refs) refs -- Need to elaborate error

-- Finds unbound references and Sorts referencs by referential order, while converting multiple branch into binaries
organizeRefs :: MultiSugar p => Location -> AST MultiBranch p -> Writer (Refer Detail) (AST BiBranch (Desugar p))
organizeRefs loc (Leaf ref) = writer (Leaf ref, case ref of
    InRef (h:_) -> singleRef h loc -- What to do here?
    _ -> mempty)
organizeRefs loc (Branch flag branch) = case branch of
    NormBranch bi ->
        bi
        & traverse (organizeRefs loc)                                    -- Traverse over the branch, tracking references
        <&> Branch (interpret flag)                            -- (Re-)attach flag
        & (maybe id $ censor . removeRef) (binding flag)       -- Remove references to current binding
    MultiBranch comps ->
        comps
        <&> uncurry (\id -> (,) id . organizeRefs (id : loc))
        <&> preSort                                             -- Construct reference graph (refering -> refered)
        & Graph.stronglyConnComp                                -- Perform topological sort (term which never get refered comes to head)
        <&> postSort                                            -- Deconstruct sorted components and place in error
        & fmap mconcat . sequenceA                              -- Merge references
        & (censor . removeRefs) (fst <$> comps)                 -- Remove bound references
        <&> foldl' step initial                                 -- Fold multiple branches into binaries. The most-refered root comes out to head
        where
            preSort (ident, res) = ((ident, res), ident, allRefs $ execWriter res)
            postSort component = writer ([], asErr component) *> traverse sequenceA (Graph.flattenSCC component)
            initial = Leaf (Internal "Chain") -- Placeholder
            step other (ident, cont) = Branch (withId flag ident) $ BiBranch cont other


{-----------------------------------------------------------------------------------------------------------------------------------
                                                        Typing
------------------------------------------------------------------------------------------------------------------------------------}

{-
t1 ~ t2, (term) unification (System of equation solving)
Full equality / inference with implementation detals hidden
_ : tp, proof search
Rules of Constructions
-}

-- Type analysis uses bibranch exclusively
type Term = AST BiBranch


-- Constaint t a b means a should unify with b under type t
data Constraint t = Constraint t t t

-- Known terms?
type Known t = MapL.Map String t

-- Unified terms
type Unified t = (Known t, [Constraint t])

type RWT r w m a = ReaderT r (WriterT w m) a

-- Denotes inference procedure
type Infer t a = RWT (Known t) [Constraint t] Identity a

-- Denotes solving procedure
type Solve t a = StateT (Unified t) Identity a

-- Typeclass for typed terms
class Typer p where
    findType :: p -> BiBranch (Infer (Term p) a) -> Infer (Term p) a
    unify :: Constraint (Term p) -> Solve (Term p) a
    unifyMany :: [Constraint (Term p)] -> Solve (Term p) a

infer :: Typer p => Term p -> Infer (Term p) (Term p)
infer (Leaf ref) = _
infer (Branch flag branch) = _