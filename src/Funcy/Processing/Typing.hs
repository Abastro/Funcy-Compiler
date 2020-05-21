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
    -- Check if this term forms closure
    ckEnclose :: Bool
    ,
    -- Binding from the left side - first parameter is term, second is type
    bindType :: Term p -> Term p -> Infer CtxProxy [] p [(Binding, Term p)]
    ,
    -- Combine two 'types'
    combine :: Term p -> Term p -> Infer CtxProxy [] p (Term p)
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

class Context c where
    -- get (fresh) name from name supply within given context
    getVar :: c t -> Binding -> Binding

    -- inspect type for certain name
    inspect :: c t -> Binding -> Maybe t

    -- apply certain bounds
    applyBnd :: [(Binding, t)] -> c t -> c t

    -- get sub-context
    subContext :: Side -> c t -> c t

data CtxProxy t = CtxProxy (Binding -> Binding) (Binding -> Maybe t)

asProxy :: (Context c) => c t -> CtxProxy t
asProxy ctx = CtxProxy (getVar ctx) (inspect ctx)

var :: Binding -> CtxProxy t -> Binding
var bnd (CtxProxy v _) = v bnd

recall :: Binding -> CtxProxy t -> Maybe t
recall bnd (CtxProxy _ r) = r bnd

recallS :: Binding -> CtxProxy t -> Infer c [] p t
recallS bnd = maybe (throwError "Internal Error") pure . recall bnd


-- TODO Construction of closures
data Closure a = Singular a | Closure [Closure a]

toClosure :: [a] -> Closure a
toClosure = Closure . fmap Singular


instance Semigroup (Closure a) where
    (Closure m) <> (Closure n) = Closure (m ++ n)
    m <> Closure n = Closure (m : n)
    m <> n = m <> Closure [n]

instance Monoid (Closure a) where
    mempty = Closure []


-- Denotes inference procedure
type Infer c w p a =
    ExceptT String (
        ReaderT (c (Term p)) (
            WriterT (w (Constraint (Term p)))
            Identity)) a


-- Infers type of each term
infer :: (Context c,
    DomainedFeature TypingIntern p,
    ElementFeature (TypingWith p) p)
    => Term p -> Infer c Closure p (Term p)
infer (Leaf r) = let referError = Leaf . Internal "ReferError" in
    case r of -- This is problematic in case it's introduced later
        InRef ref -> do
            refed <- asks inspect <&> ($ ref)
            pure $ fromMaybe (referError ["Binding", ref]) refed -- TODO: More detailed error
        Internal key other -> do
            let res = maybe (Left . (:) key) runIntern (findFeature key) other
            pure $ either referError id res

infer (Branch flag (Binary l r)) = pass $ do
    let subInfer side t = local (subContext side) $ infer t
    let withProxy = mapExceptT . withReaderT $ asProxy
    let fromListing = mapExceptT . mapReaderT . mapWriter . fmap $ toClosure
    let applyLocal = fromListing . withProxy
    let typer = runTyper (featureOf flag) id
    let close = if ckEnclose typer then Closure . (: []) else id

    -- Infer type of left term, and obtain bindings
    ltype <- subInfer LeftSide l
    bound <- applyLocal $ bindType typer l ltype
    let updated = local (applyBnd bound)  -- Localization for obtained bounds

    -- Infer type of right term
    rtype <- updated $ subInfer RightSide r
    tp <- updated $ applyLocal $ combine typer ltype rtype -- Combine left and right type to obtain the whole type
    return (tp, close)

{-----------------------------------------------------------------------------------------------------------------------------------
                                                        Constraint Solving
------------------------------------------------------------------------------------------------------------------------------------}

type Known t = MapL.Map Binding t

-- TODO Constraint solving
type Subst t = MapL.Map Binding t

type UnifyState t = [Constraint t]

-- Denotes solving procedure
type Solve p a =
    ExceptT String (
        ReaderT (Known (Term p)) (
            StateT (UnifyState (Term p))
            Identity)) a

solve :: Solve p (Subst (Term p))
solve = do
    cs <- get
    case cs of
        [] -> ask
        (con : cs0) -> do
            (su1, cs1) <- _unify con
            put (cs1 ++ (_apply su1 cs0))
            local (_compose su1) solve
