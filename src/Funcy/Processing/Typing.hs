{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Funcy.Processing.Typing where

import           Control.Applicative
import           Control.Monad.Reader
import           Control.Monad.Writer
import           Control.Monad.Except
import           Control.Monad.State

import           Data.List
import           Data.Function
import           Data.Functor
import           Data.Functor.Identity
import           Data.Foldable
import           Data.Maybe

import           Data.Set (Set)
import qualified Data.Set as Set
import           Data.Graph (Graph)
import qualified Data.Graph as Graph
import           Data.Map (Map)
import qualified Data.Map as Map

import           Funcy.Processing.AST
import           Funcy.Processing.Modules
import           Funcy.Processing.Message

{-----------------------------------------------------------------------------------------------------------------------------------
                                                        Type-related Data
------------------------------------------------------------------------------------------------------------------------------------}

data Typing p = Typing {
  -- |Check if this term forms closure
  ckEnclose :: Bool
  ,
  -- |Binding from the left side - first parameter is term, second is type
  bindType :: Term p -> Term p -> Infer CtxProxy p [(Binding, Term p)]
  ,
  -- |Combine two 'types'
  combine :: Term p -> Term p -> Infer CtxProxy p (Term p)
}

-- |Typing of certain term
newtype TypingWith q p = TypingWith {
  runTyper :: (p -> q) -> Typing q
} deriving Functor

instance Expansive (TypingWith q) where
  expand inc = fmap $ wrap inc


-- |Internal Typing
newtype TypingIntern q p = TypingIntern {
  runIntern :: (p -> q) -> [Binding] -> Infer CtxProxy q (Term q)
} deriving Functor

instance Expansive (TypingIntern q) where
  expand inc = fmap $ wrap inc

-- |Type analysis uses bibranch exclusively
type Term p = AST (Binary p)


{-----------------------------------------------------------------------------------------------------------------------------------
                                                        Typing & Inference
------------------------------------------------------------------------------------------------------------------------------------}

{-
t1 ~ t2, (term) unification (System of equation solving)
Full equality / inference with implementation detals hidden
-}


-- |Constaint for unification
data Constraint t = Constraint {
  termA :: t,
  termB :: t
}

class Context c where
  -- |get (fresh) name from name supply within given context
  getVar :: c t -> Binding -> Binding

  -- |inspect type for certain name
  inspect :: c t -> Binding -> Maybe t

  -- |apply certain bounds
  applyBnd :: [(Binding, t)] -> c t -> c t

  -- |get sub-context
  subContext :: Side -> c t -> c t


data CtxProxy t = CtxProxy (Binding -> Binding) (Binding -> Maybe t)

asProxy :: (Context c) => c t -> CtxProxy t
asProxy ctx = CtxProxy (getVar ctx) (inspect ctx)

var :: Binding -> CtxProxy t -> Binding
var bnd (CtxProxy v _) = v bnd

recall :: Binding -> CtxProxy t -> Maybe t
recall bnd (CtxProxy _ r) = r bnd

recallS :: Binding -> CtxProxy t -> Infer c p t
recallS bnd = maybe (throwError internal) pure . recall bnd



-- |Environment
type Env t = Map Binding t
type Env' = ()

listToEnv :: [(Binding, Term p)] -> Env'
listToEnv = error "formEnvironment"


-- |Denotes inference procedure
type Infer c p
  = ExceptT ErrorMsg
    (ReaderT (c (Term p))
    (WriterT [Constraint (Term p)]
    Identity))


-- TODO Consider the case where flag is ignored
-- TODO Why look for bound variables in inference process?
-- |Infers type of each term
infer :: ( Context c
     , DomainedFeature (TypingIntern p) p
     , ElementFeature (TypingWith p) p )
  => Term p
  -> Infer c p (Term p)
infer term = case term of
  Leaf (InRef ref)          -> do
    refed <- asks inspect <&> ($ ref) -- TODO: Consider cross reference
    pure $ fromMaybe (referError ["Binding", ref]) refed -- TODO: More detailed error

  Leaf (Internal key other) -> do
    let tp = maybe (throwError . (:) key) (($ id) . runIntern) (findFeature key) other
    catchError (applyLocal tp) (pure . referError) -- Catch error into AST

  Branch (Binary flag l r)  -> do
    let subInfer side t = local (subContext side) $ infer t
    let typer           = runTyper (featureOf flag) id

    -- Infer type of left term, and obtain bindings
    ltype <- subInfer LeftSide l
    bound <- applyLocal $ bindType typer l ltype
    let updated = local (applyBnd bound) -- Localization for obtained bounds

    -- Infer type of right term
    rtype <- updated $ subInfer RightSide r -- TODO need to give binding info for child closures
    tp    <- updated $ applyLocal $ combine typer ltype rtype -- Combine left and right type to obtain the whole type
    pure tp
  where
    referError  = Leaf . Internal "ReferError"
    withProxy   = mapExceptT . withReaderT $ asProxy
    applyLocal  = withProxy


{-----------------------------------------------------------------------------------------------------------------------------------
                                                        Constraint Solving
------------------------------------------------------------------------------------------------------------------------------------}

-- |Substitutions
type Subst t = Map Binding t


type UnifyState t = (Subst t, [Constraint t])

-- |Denotes solving procedure
type Solve p a
  = ExceptT
      String
      (StateT (UnifyState (Term p)) Identity)
      a

{-

-- TODO Unification search space (Proof Dictionary) - Accumulative 
-- TODO Consider binding specific to closure
-- |Solve
solve :: Solve p (Subst (Term p))
solve = do
  (su, cs) <- get
  case cs of
    Singular con -> do
        -- Unify and solve the constraint
      (su', cs') <- unify con
      put (compose su su', cs')
      solve
    Closure _ []          -> return su
    Closure _ (cs0 : css) -> do
      -- Solve for head constraints
      put (su, cs0)
      su' <- solve
      -- Apply the constraints and substitutions
      put (compose su su', applySubst su' css)
      solve

unify :: Constraint (Term p) -> Solve p (UnifyState (Term p))
unify = error "unify"

compose :: Subst (Term p) -> Subst (Term p) -> Subst (Term p)
compose = error "compose"

applySubst
  :: Subst (Term p)
  -> [Closure e (Constraint (Term p))]
  -> Closure e (Constraint (Term p))
applySubst = error "applySubst"

-}