{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}

module Funcy.Processing.Values where

import Control.Applicative
import Control.Monad

import Control.Monad.Reader
import Control.Monad.Writer
import Control.Monad.State

import Data.Function
import Data.Functor
import Data.Functor.Identity
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
newtype Refs = MkRefs { runRef :: MapS.Map String [String] }

type Referred = WriterT Refs Identity
type IdRefed a = Idented (Referred a)

referred :: Maybe String -> Referred a -> Referred a
referred = maybe id $ \ident -> censor $ MkRefs . MapS.insert ident [ident] . runRef

found :: Maybe String -> Referred a -> Referred a
found = maybe id $ \ident -> censor $ MkRefs . MapS.delete ident . runRef

foundMany :: [String] -> Referred a -> Referred a
foundMany keys = censor $ MkRefs . (`MapS.withoutKeys` Set.fromList keys) . runRef


instance Semigroup Refs where
    x <> y = MkRefs $ MapS.unionWith (++) (runRef x) (runRef y)
instance Monoid Refs where
    mempty = MkRefs MapS.empty

{-----------------------------------------------------------------------------------------------------------------------------------
                                                        Reference Tracking
------------------------------------------------------------------------------------------------------------------------------------}

asErr :: SCC (IdRefed a) -> Refs
asErr (AcyclicSCC vertex) = MkRefs MapS.empty
asErr (CyclicSCC vertices) = MkRefs $ let refs = fst <$> vertices
      in MapS.singleton ("_cyclic" <> concat refs) refs

-- Finds unbound references and Sorts referencs by referential order, while converting multiple branch into binaries
-- TODO: Deal with modules?
sortRefs :: MultiSugar p => AST MultiBranch p -> Referred (AST BiBranch (Desugar p))
sortRefs (AST flag branch) = case branch of
    NormBranch bi -> bi
            & traverse sortRefs                                    -- Traverse over the branch, tracking references
            <&> AST (intrpret flag)                                 -- (Re-)attach flag
            & found (binding flag)                                  -- Remove references to current binding
            & referred (refer flag)                                 -- Add current reference
    MultiBranch comps -> comps
            <&> preSort . fmap sortRefs                            -- Construct reference graph (refering -> refered)
            & Graph.stronglyConnComp                                -- Perform topological sort (term which never get refered comes to head)
            <&> postSort                                            -- Deconstruct sorted components and place in error
            & foundMany (fst <$> comps) . fmap concat . sequenceA   -- Merge unbound references and remove bound references
            <&> foldl' step initial                                 -- Fold multiple branches into binaries. The most-refered root comes out to head
        where
            preSort (ident, res) = ((ident, res), ident, MapS.keys $ runRef $ execWriter res)
            postSort component = writer ([], asErr component) *> traverse sequenceA (flattenSCC component)
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


-- Constaint t a b means a should unify with b under type t
data Constraint t = Constraint t t t

-- Known terms
type Known t = MapL.Map String t

-- Unified terms
type Unified t = (Known t, [Constraint t])

type RWT r w m a = ReaderT r (WriterT w m) a

-- Denotes terms getting inferred
type Infer t a = RWT (Known t) [Constraint t] Identity a

-- Denotes solving process of constraints
type Solve t a = StateT (Unified t) Identity a

-- Typeclass for typed terms
class TypedTerm t where
    findType :: t -> BiBranch (Infer t a) -> Infer t a
    unify :: Constraint t -> Solve t a
    unifyMany :: [Constraint t] -> Solve t a


-- I'm too lazy to write more now -.-