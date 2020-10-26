{-# LANGUAGE TemplateHaskell #-}
module Funcy.Typing.Infers (
  Constraint(..), TypedTerm(..), theType, theTerm,
  TypeBinder(..), defaultBinder, TypeCombine(..),
  Infer, mkVar, boundOf, sBoundOf,
  intProcInfer,
) where

import Control.Monad ( (>=>) )
import Control.Monad.Reader
    ( MonadTrans(..), ReaderT, MonadReader(..) )
import Control.Monad.Writer ( WriterT, listen )
import Control.Monad.Except ( ExceptT, throwError )

import Control.Lens.TH ( makeLenses )
import Control.Lens.Operators ( (^.), (<>=) )
import qualified Control.Lens.Combinators as Lens

import Funcy.Base.Util
import Funcy.Base.AST
import Funcy.Base.Message


-- |Constaint for unification
data Constraint t = Constraint {
  -- |Internal inferred term
  inTerm :: t,
  -- |External specified term
  outTerm :: t
}

-- TODO How would disambiguation go with
-- forall a. a -> (forall a. a -> a)
data TpRepr t = TpRepr {
  tpVar :: [Binding],
  constraint :: [Constraint t],
  conType :: t
}

instance Semigroup (TpRepr t) where
  -- Takes latter type
  TpRepr v c _ <> TpRepr v' c' t' = TpRepr (v <> v') (c <> c') t'

instance Monoid (TpRepr t) where
  mempty = TpRepr [] [] undefined


data TypedTerm p a = TypedTerm {
  _theTerm :: a,
  _theType :: p
} deriving Functor
$(makeLenses ''TypedTerm)


data InferCtx a = InferCtx {
  _getVar :: String -> Binding,
  _getBound :: Binding -> Maybe a,
  _addBound :: [(Binding, a)] -> InferCtx a
}
$(makeLenses ''InferCtx)

-- |Creates a fresh variable.
mkVar :: String -> Infer a Binding
mkVar name = Lens.view (getVar . Lens.to ($ name))

-- |Looks for type of certain bound.
boundOf :: Binding -> Infer a (Maybe a)
boundOf bnd = Lens.view (getBound . Lens.to ($ bnd))

-- |Looks for type of certain bound. Errors out if it doesn't exist
sBoundOf :: Binding -> Infer a a
sBoundOf bnd = boundOf bnd >>= maybe (throwError internal) pure

-- |Denotes inference procedure
type Infer t
  = ExceptT ErrorMsg
    (ReaderT (InferCtx t)
    (WriterT (TpRepr t)
    Id))


newtype TypeBinder p = TypeBinder {
  -- |Bind vars with inferred type
  bindType :: TypedTerm p p -> Infer p [(Binding, p)]
}

newtype TypeCombine p t = TypeCombine {
  -- |Combines type
  combineType :: t p -> Infer p p
}

-- |Binder which does not bind anything
defaultBinder :: TypeBinder p
defaultBinder = TypeBinder $ const $ pure []


data InState p = InState {
  _location :: Loc,
  _bounds :: [(Binding, p)]
}
$(makeLenses ''InState)

intProcInfer :: (Traversable term) =>
  (a -> Loc) -> StOn t k a -> Indexing (TypeBinder a) term -> TypeCombine a term ->
  ASTProcIn term (Infer a) Loc Loc a b
intProcInfer getLoc stack indexing combine subProc =
  stateHover (\l -> do
    return InState { _location = l, _bounds = [] }
  ) >=> indexHover (indexIso indexing) (stTravHover $ \(binder, br) -> do
    bnds <- Lens.use bounds
    (res, tpRepr) <- lift $ listen $ local (applyBnd bnds) $ subProc br
    extBnds <- lift $ bindType binder $ undefined -- TODO Disambiguate binding?
    bounds <>= extBnds
    return (binder, res)
  ) >=> stateHover (\st -> do
    let bnds = st ^. bounds
    tp <- lift $ local (applyBnd bnds) $ combineType combine undefined
    return st
  ) >=> stateHover (return . Lens.view location)
  where
    applyBnd bnds = Lens.foldMapOf addBound ($ bnds)


{-------------------------------------------------------------------
                          Constraint Solving
--------------------------------------------------------------------}

{-

-- |Substitutions
type Subst t = Map Binding t


type UnifyState t = (Subst t, [Constraint t])

-- |Denotes solving procedure
type Solve p a
  = ExceptT
      String
      (StateT (UnifyState (Term p)) Identity)
      a



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