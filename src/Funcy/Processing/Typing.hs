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

{-----------------------------------------------------------------------------------------------------------------------------------
                                                        Type-related Terms
------------------------------------------------------------------------------------------------------------------------------------}

-- Typeclass for typed terms
class Typer p where

    -- Errors when it's invalid
    internalType :: String -> [String] -> Term p

    typing :: Context c => p -> Typing c p

data Typing c p = Typing {
    -- Infer type of left side
    inferLeft :: Term p -> Infer c p (Binder (Term p)),

    -- Infer type of right side
    inferRight :: Term p -> Infer c p (Term p),

    -- Combine two 'types'
    combine :: Term p -> Term p -> Infer c p (Term p)
}

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
    ttype :: t,
    termA :: t,
    termB :: t
}

type Binder t = Writer [(Binding, t)] t

class Context c where
    -- get (fresh) name from name supply within given context
    var :: Binding -> c t -> Binding

    -- inspect type for certain name
    inspect :: Binding -> c t -> Maybe t

    -- apply certain bounds
    applyBnd :: [(Binding, t)] -> c t -> c t

    -- get sub-context
    subContext :: String -> c t -> c t


-- Denotes inference procedure
type Infer c p a =
    ExceptT String (
        ReaderT (c (Term p)) (
            WriterT [Constraint (Term p)]
            Identity)) a

recall :: (Context c, Typer p) => Binding -> Infer c p (Maybe (Term p))
recall ref = asks (inspect ref)

-- Strict recall - causes error if not detected
recallS :: (Context c, Typer p) => Binding -> Infer c p (Term p)
recallS ref = asks (inspect ref) >>= maybe (throwError "Internal Error") pure

-- Infer certain part
inferFor :: (Context c, Typer p) => String -> Term p -> Infer c p (Term p)
inferFor part = local (subContext part) . infer

-- Infers type of each term
infer :: (Context c, Typer p) => Term p -> Infer c p (Term p)
infer (Leaf l) = case l of
    InRef ref -> do
        refed <- asks $ inspect ref
        pure $ fromMaybe (Leaf $ Internal "RefError" []) refed -- TODO: More detailed error
    Internal key other -> pure $ internalType key other

infer (Branch flag (Binary l r)) = do
    let typer = typing flag
    bnder <- infer l >>= inferLeft typer     -- Infer type of left term
    let (ltype, bound) = runWriter bnder
    let updated = local (applyBnd bound)  -- Localize for obtained bounds
    rtype <- updated (infer r) >>= inferRight typer -- Infer type of right term
    combine typer ltype rtype               -- Combine left and right type to obtain the whole type



-- Unified terms
--type Unified t = (Known t, [Constraint t])
-- Denotes solving procedure
--type Solve p a = StateT (Unified (Term p)) Identity a