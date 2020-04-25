{-# LANGUAGE TypeFamilies #-}

module Funcy.Processing.Typing where

import Control.Applicative
import Control.Monad.Reader
import Control.Monad.Writer
import Control.Monad.Except
import Control.Monad.State
import Control.Monad.RWS

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

-- TODO Syntactic sugar handling

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
    internal :: String -> Term p

    -- Check type of left side
    checkLeft :: NameGen n => p -> Term p
        -> Infer n p (Bound (Term p))
    -- Check type of right side
    checkRight :: NameGen n => p -> Term p
        -> Infer n p (Term p)
    -- Combine
    combine :: p -> Term p -> Term p -> Infer n p (Term p)


-- Type analysis uses bibranch exclusively
type Term = AST Binary

-- Constaint t a b means a should unify with b under type t
data Constraint t = Constraint {
    ttype :: t,
    termA :: t,
    termB :: t
}

-- Known types of bindings
type Known t = MapL.Map Binding t

type Bound t = Writer (Known t) t

-- Unified terms
type Unified t = (Known t, [Constraint t])

class NameGen n where
    generateName :: Binding -> n -> Binding
    updateName :: n -> n

-- Denotes inference procedure
type Infer s p a = RWST (Known (Term p)) [Constraint (Term p)] s Identity a

-- Denotes solving procedure
type Solve p a = StateT (Unified (Term p)) Identity a

-- Infers type of each term
infer :: (Typer p, NameGen n) => Term p -> Infer n p (Term p)
infer (Leaf l) = case l of
    InRef ref -> do
        refed <- asks $ MapL.lookup ref
        pure $ case refed of
            Just t -> t
            Nothing -> Leaf $ Internal "RefError" -- TODO: More detailed error / fresh name supply?
    Internal name -> pure $ internal name

infer (Branch flag (Binary l r)) = do
    bnder <- infer l >>= checkLeft flag     -- Infer type of left term
    let (ltype, bound) = runWriter bnder
    let updated = local (MapL.union bound)  -- Localize for obtained bounds
    rtype <- updated (infer r) >>= checkRight flag -- Infer type of right term
    modify updateName
    combine flag ltype rtype                -- Combine left and right type to obtain the whole type
