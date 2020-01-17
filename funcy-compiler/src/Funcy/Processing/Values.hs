{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}

module Funcy.Processing.Values where

import Control.Applicative
import Control.Monad
import Control.Arrow

import Data.Tuple
import Data.Function
import Data.Functor
import Data.Foldable

import Data.Graph as Graph
import qualified Data.Map.Lazy as MapL
import qualified Data.Map.Strict as MapS
import qualified Data.Set as Set

import Funcy.Processing.Modules


{-----------------------------------------------------------------------------------------------------------------------------------
                                                    Abstract Syntx Tree
------------------------------------------------------------------------------------------------------------------------------------}

type Idented a = (String, a)

data AST m p = AST p (m (AST m p))
data BiBranch t = Leaf | Branch t t deriving (Functor, Foldable, Traversable)
data MultiBranch t = NormBranch (BiBranch t) | MultiBranch [Idented t]

instance Functor m => Functor (AST m) where
    fmap f (AST flag branch) = AST (f flag) $ (fmap . fmap) f branch

class MultiSugar p where
    type Desugar p
    intrpret :: p -> Desugar p
    binding :: p -> Maybe String
    refer :: p -> Maybe String
    withId :: p -> String -> Desugar p

{-----------------------------------------------------------------------------------------------------------------------------------
                                                        References
------------------------------------------------------------------------------------------------------------------------------------}
-- Map from reference to destination names
newtype Refs = Refs { refMap :: MapS.Map String [String] }

type Referred a = (Refs, a)
type IdRefed a = Idented (Referred a)

referred :: Maybe String -> Referred a -> Referred a
referred (Just ident) = first $ Refs . MapS.insert ident [ident] . refMap
referred Nothing = id

found :: Maybe String -> Referred a -> Referred a
found (Just ident) = first $ Refs . MapS.delete ident . refMap
found Nothing = id

foundMany :: [String] -> Referred a -> Referred a
foundMany keys = first $ Refs . (`MapS.withoutKeys` Set.fromList keys) . refMap


instance Semigroup Refs where
    x <> y = Refs $ MapS.unionWith (++) (refMap x) (refMap y)
instance Monoid Refs where
    mempty = Refs MapS.empty

{-----------------------------------------------------------------------------------------------------------------------------------
                                                        Reference Tracking
------------------------------------------------------------------------------------------------------------------------------------}

asErr :: SCC (IdRefed a) -> Refs
asErr (AcyclicSCC vertex) = Refs MapS.empty
asErr (CyclicSCC vertices) = Refs $ let refs = fst <$> vertices
    in MapS.singleton ("_cyclic" <> concat refs) refs

-- Tracks unbound references and sorts them by referential order, while converting multiple branch into binaries
-- TODO: Deal with modules?
trackRefs :: MultiSugar p => AST MultiBranch p -> Referred (AST BiBranch (Desugar p))
trackRefs (AST flag branch) = case branch of
    NormBranch bi -> bi
            & traverse trackRefs                                    -- Traverse over the branch, tracking references
            <&> AST (intrpret flag)                                 -- (Re-)attach flag
            & found (binding flag)                                  -- Remove references to current binding
            & referred (refer flag)                                 -- Add current reference
    MultiBranch comps -> comps
            <&> preSort . fmap trackRefs                            -- Construct reference graph (refering -> refered)
            & Graph.stronglyConnComp                                -- Perform topological sort (term which never get refered comes to head)
            <&> postSort                                            -- Deconstruct sorted components and place in error
            & foundMany (fst <$> comps) . mconcat                   -- Merge unbound references and remove bound references
            <&> foldl' step initial                                 -- Fold multiple branches into binaries. The most-refered root comes out to head
        where
            preSort node = let (ident, (refs, _)) = node in (node, ident, MapS.keys $ refMap refs)
            postSort component = (asErr component, []) <> traverse sequenceA (flattenSCC component)
            initial = AST (intrpret flag) Leaf
            step other (ident, cont) = AST (withId flag ident) $ Branch cont other


{-----------------------------------------------------------------------------------------------------------------------------------
                                                        Inference
------------------------------------------------------------------------------------------------------------------------------------}

{-
t1 ~ t2, (term) unification (System of equation solving)
Full equality / inference with implementation detals hidden
_ : tp, proof search
Rules of Constructions
-}

data Term
data ConstraintKind = Equality | Typed

data Constraint = Constraint ConstraintKind Term Term

