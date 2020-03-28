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

import Funcy.Processing.AST

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