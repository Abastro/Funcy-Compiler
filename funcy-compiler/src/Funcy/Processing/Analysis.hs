{-# LANGUAGE TypeFamilies #-}

module Funcy.Processing.Analysis where

import Control.Applicative
import Control.Monad.Reader
import Control.Monad.Writer
import Control.Monad.Except

import Data.Function
import Data.Functor
import Data.Functor.Identity
import Data.Foldable

import qualified Data.Set as Set
import qualified Data.Graph as Graph
import qualified Data.Map.Strict as MapS

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
asErr (Graph.CyclicSCC vertices) = let refs = fmap fst vertices in singleRef ("_cyclic" <> mconcat refs) refs -- Need elaborate error

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
            initial = Leaf (Internal "Block") -- Placeholder
            step other (ident, cont) = Branch (withId flag ident) $ BiBranch cont other