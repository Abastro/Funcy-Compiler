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

data Typing p = Typing {
    -- Binding from the left side - first parameter is term, second is type
    bindType :: Term p -> Term p -> Infer CtxProxy p [(Binding, Term p)],

    -- Combine two 'types'
    combine :: Term p -> Term p -> Infer CtxProxy p (Term p)
}

newtype TypingWith q p = TypingWith { runTyper :: (p -> q) -> Typing q } deriving Functor

instance Expansive (TypingWith q) where
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
    getVar :: c t -> Binding -> Binding

    -- inspect type for certain name
    inspect :: c t -> Binding -> Maybe t

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


asProxy :: (Context c) => c t -> CtxProxy t
asProxy ctx = CtxProxy (getVar ctx) (inspect ctx)


data CtxProxy t = CtxProxy (Binding -> Binding) (Binding -> Maybe t)

var :: Binding -> CtxProxy t -> Binding
var bnd (CtxProxy v _) = v bnd

recall :: Binding -> CtxProxy t -> Maybe t
recall bnd (CtxProxy _ r) = r bnd

recallS :: Binding -> CtxProxy t -> Infer c p t
recallS bnd = maybe (throwError "Internal Error") pure . recall bnd

-- TODO: Formalize possible operations

-- Infers type of each term
infer :: (Context c, DomainedFeature TypingIntern p, ElementFeature (TypingWith p) p) => Term p -> Infer c p (Term p)
infer (Leaf r) = let referError = Leaf . Internal "ReferError" in
    case r of
        InRef ref -> do
            refed <- asks inspect <&> ($ ref)
            pure $ fromMaybe (referError ["Binding", ref]) refed -- TODO: More detailed error
        Internal key other -> do
            let res = maybe (Left . (:) key) runIntern (findFeature key) other
            pure $ either referError id res

infer (Branch flag (Binary l r)) = do
    let subInfer side t = local (subContext side) $ infer t
    let withProxy = mapExceptT $ withReaderT asProxy
    let typer = runTyper (featureOf flag) id
    ltype <- subInfer LeftSide l  -- Infer type of left term
    bound <- withProxy $ bindType typer l ltype
    let updated = local (applyBnd bound)  -- Localize for obtained bounds
    rtype <- updated (subInfer RightSide r) -- Infer type of right term
    updated $ withProxy $ combine typer ltype rtype -- Combine left and right type to obtain the whole type

-- TODO Constraint solving

-- Unified terms
--type Unified t = (Known t, [Constraint t])
-- Denotes solving procedure
--type Solve p a = StateT (Unified (Term p)) Identity a