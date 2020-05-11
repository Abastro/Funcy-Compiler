{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Funcy.Processing.Typing where

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
import Data.Maybe

import qualified Data.Set as Set
import qualified Data.Graph as Graph
import qualified Data.Map.Strict as MapS
import qualified Data.Map.Lazy as MapL

import Funcy.Processing.AST
import Funcy.Processing.Modules

{-----------------------------------------------------------------------------------------------------------------------------------
                                                        Type-related Terms
------------------------------------------------------------------------------------------------------------------------------------}

data Typing c p = Typing {
    -- Binding from the left side - first parameter is term, second is type
    bindType :: Term p -> Term p -> Infer c p [(Binding, Term p)],

    -- Combine two 'types'
    combine :: Term p -> Term p -> Infer c p (Term p)
}

newtype TypingWith c q p = TypingWith { runTyper :: (p -> q) -> Typing c q } deriving Functor

instance Expansive (TypingWith c q) where
    expand inc = fmap $ wrap inc


newtype TypingIntern p = TypingIntern { runIntern :: [String] -> Either [String] (Term p) } deriving Functor

instance Expansive TypingIntern where
    expand inc = fmap $ wrap inc

-- Type analysis uses bibranch exclusively
type Term = AST Binary

{-----------------------------------------------------------------------------------------------------------------------------------
                                                        Typing & Inference
------------------------------------------------------------------------------------------------------------------------------------}

{-
t1 ~ t2, (term) unification (System of equation solving)
Full equality / inference with implementation detals hidden
-}


-- Constaint t a b means a should unify with b under type t
data Constraint t = Constraint {
    termA :: t,
    termB :: t
}

data Side = LeftSide | RightSide

class Context c where
    -- get (fresh) name from name supply within given context
    getVar :: Binding -> c t -> Binding

    -- inspect type for certain name
    inspect :: Binding -> c t -> Maybe t

    -- apply certain bounds
    applyBnd :: [(Binding, t)] -> c t -> c t

    -- get sub-context
    subContext :: Side -> c t -> c t


-- Denotes inference procedure
type Infer c p a =
    ExceptT String (
        ReaderT (c (Term p)) (
            WriterT [Constraint (Term p)]
            Identity)) a


var :: (Context c) => Binding -> Infer c p Binding
var ident = asks (getVar ident)

recall :: (Context c) => Binding -> Infer c p (Maybe (Term p))
recall ref = asks (inspect ref)

-- Strict recall - causes error if not detected
recallS :: (Context c) => Binding -> Infer c p (Term p)
recallS ref = asks (inspect ref) >>= maybe (throwError "Internal Error") pure

-- TODO: Formalize possible operations

-- Infers type of each term
infer :: (Context c, DomainedFeature TypingIntern p, ElementFeature (TypingWith c p) p) => Term p -> Infer c p (Term p)
infer (Leaf r) = let referError = Leaf . Internal "ReferError" in
    case r of
        InRef ref -> do
            refed <- asks $ inspect ref
            pure $ fromMaybe (referError ["Binding", ref]) refed -- TODO: More detailed error
        Internal key other -> do
            let res = maybe (Left . (:) key) runIntern (findFeature key) other
            pure $ either referError id res

infer (Branch flag (Binary l r)) = do
    let subInfer side t = local (subContext side) $ infer t
    let typer = runTyper (featureOf flag) id
    ltype <- subInfer LeftSide l  -- Infer type of left term
    bound <- bindType typer l ltype
    let updated = local (applyBnd bound)  -- Localize for obtained bounds
    rtype <- updated (subInfer RightSide r) -- Infer type of right term
    updated $ combine typer ltype rtype -- Combine left and right type to obtain the whole type


-- Unified terms
--type Unified t = (Known t, [Constraint t])
-- Denotes solving procedure
--type Solve p a = StateT (Unified (Term p)) Identity a