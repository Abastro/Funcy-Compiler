{-# LANGUAGE TemplateHaskell #-}
module Funcy.Typing.Infers (
  Constraint(..), TypedTerm(..), theType, theTerm,
  TypingIndex(..), TypeBinder(..), defaultBinder, TypeCombine(..),
  Infer, mkVar, boundOf, sBoundOf,
  internalProcInfer
) where

import Control.Monad.Identity ( Identity )
import Control.Monad.Reader
    ( MonadTrans(..), ReaderT, MonadReader(..) )
import Control.Monad.Writer ( WriterT )
import Control.Monad.Except ( ExceptT, throwError )

import Control.Lens.TH ( makeLenses )
import Control.Lens.Operators ( (^.), (<>=) )
import qualified Control.Lens.Combinators as Lens

import Data.Coerce ( coerce )

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

data TypedTerm p a = TypedTerm {
  _theTerm :: a,
  _theType :: p
} deriving Functor
$(makeLenses ''TypedTerm)


data InferCtx a = InferCtx {
  _getVar :: String -> Binding,
  _getBound :: Binding -> Maybe a,
  _subCtx :: Binding -> InferCtx a,
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
type Infer a
  = ExceptT ErrorMsg
    (ReaderT (InferCtx a)
    (WriterT [Constraint a]
    Identity))


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

data TypingIndex p = TypingIndex {
  _partName :: String,
  _binder :: TypeBinder p
}
$(makeLenses ''TypingIndex)


data InState p = InState {
  _bounds :: [(Binding, p)]
}
$(makeLenses ''InState)

internalProcInfer :: (Traversable term) =>
  Indexing (TypingIndex p) term -> TypeCombine p term ->
  (ASTProcIn term (Infer p) (TypedTerm p)) (TypingIndex p) (InState p) p
internalProcInfer dex comb = ASTProcIn {
  mkState = const $ InState [],
  tagBranch = indexing dex,
  onState = \part sub -> do
    bnds <- Lens.use bounds
    res <- lift $ local (childCtx (part ^. partName) . applyBnd bnds) sub
    extBnds <- lift $ bindType (part ^. binder) res
    bounds <>= extBnds
    pure (part, res),
  mergeBranch = \state br -> do
    let tps = Lens.view (content . theType) <$> br
    let term = Lens.view (content . theTerm) <$> br
    tp <- local (applyBnd $ state ^. bounds) $ combineType comb tps
    pure $ TypedTerm term tp
} where
  childCtx name = Lens.foldMapOf subCtx ($ name)
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