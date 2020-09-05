{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module Funcy.Processing.Typing (
  Constraint(..), TypedTerm(..), theType, theTerm,
  TypingIndex(..), InferType(..), TypeBinder(..), defaultBinder,
  Infer, mkVar, boundOf, procInfer,
) where

import Control.Monad.Identity ( Identity )
import Control.Monad.Reader
    ( MonadTrans(..), ReaderT, MonadReader(..) )
import Control.Monad.Writer ( WriterT )
import Control.Monad.Except ( ExceptT )

import Control.Lens.TH ( makeLenses )
import Control.Lens.Operators ( (^.), (<>=) )
import qualified Control.Lens.Combinators as Lens

import Data.Coerce ( coerce )

import Funcy.Processing.Util
import Funcy.Processing.AST
import Funcy.Processing.Message ( ErrorMsg )


{-------------------------------------------------------------------
                          Typing & Inference
--------------------------------------------------------------------}

{-
t1 ~ t2, (term) unification (System of equation solving)
Full equality / inference with implementation detals hidden
-}

-- |Constaint for unification
data Constraint t = Constraint {
  termA :: t,
  termB :: t
}

data TypedTerm p a = TypedTerm {
  _theTerm :: a,
  _theType :: p
} deriving Functor
$(makeLenses ''TypedTerm)


data InferCtx a = InferCtx {
  _getVar :: String -> Binding,
  _getBound :: Binding -> a,
  _subCtx :: Binding -> InferCtx a,
  _addBound :: [(Binding, a)] -> InferCtx a
}
$(makeLenses ''InferCtx)

mkVar :: String -> Infer a Binding
mkVar name = Lens.view (getVar . Lens.to ($ name))

boundOf :: Binding -> Infer a a
boundOf bnd = Lens.view (getBound . Lens.to ($ bnd))


-- |Denotes inference procedure
type Infer a
  = ExceptT ErrorMsg
    (ReaderT (InferCtx a)
    (WriterT [Constraint a]
    Identity))


newtype TypeBinder p = TypeBinder {
  -- |Bind vars with inferred type
  bindType :: forall a. TypedTerm p p -> Infer p [(Binding, p)]
}

-- |Binder which does not bind anything
defaultBinder :: TypeBinder p
defaultBinder = TypeBinder $ const $ pure []

data TypingIndex p = TypingIndex {
  _partName :: String,
  _binder :: TypeBinder p
}
$(makeLenses ''TypingIndex)

class Traversable t => InferType t where
  -- |Tag the part
  tagPart :: Stackable InferType p -> t a -> t (TypingIndex p, a)
  -- |Combine input types to form a type
  combine :: Stackable InferType p -> t p -> Infer p p

instance Collection InferType where
  asTraversed _ = traverse


data InState p = InState {
  _bounds :: [(Binding, p)]
}
$(makeLenses ''InState)


procInfer :: ASTProcOn InferType (Infer (ASTOn InferType)) (TypedTerm (ASTOn InferType))
procInfer = mkProcess (TypeClassOf @InferType) (theProcess astStackable)

theProcess :: (InferType term) => Stackable InferType p ->
  (ASTProcIn term (Infer p) (TypedTerm p)) (TypingIndex p) (InState p) p
theProcess stack = ASTProcIn {
  mkState = const $ InState [],
  tagBranch = tagPart stack,
  onState = \part sub -> do
    bnds <- Lens.use bounds
    res <- lift $ local (childCtx (part ^. partName) . applyBnd bnds) sub
    extBnds <- lift $ bindType (part ^. binder) res
    bounds <>= extBnds
    pure (part, res),
  mergeBranch = \state br -> do
    let tps = Lens.view (content . theType) <$> br
    let term = Lens.view (content . theTerm) <$> br
    tp <- local (applyBnd $ state ^. bounds) $ combine stack tps
    pure $ TypedTerm term tp
} where
  childCtx name = Lens.foldMapOf subCtx ($ name)
  applyBnd bnds = Lens.foldMapOf addBound ($ bnds)


instance InferType Reference where
  tagPart stack = coerce
  combine stack (Reference ref) = do
    -- Lookup type dict? Or no?
    undefined

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