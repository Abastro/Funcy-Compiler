{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TemplateHaskell #-}
module Funcy.Base.AST (
  Binding, Location, (//), Reference(..),
  ASTOn, Stacking(..), astStacking,
  ASTProcOn, ASTProcIn(..), mkProcess, processAST,
  Conversion(..), convertAST
) where

import Control.Monad.State ( StateT(..) )
import Control.Lens.Type ( LensLike', Traversal )
import qualified Control.Lens.Combinators as Lens

import Data.Functor.Compose ( Compose(..) )

import Funcy.Base.Util

{-------------------------------------------------------------------
                      Abstract Syntax Tree
--------------------------------------------------------------------}

-- |Binding reference name
type Binding = String

-- |Location
newtype Location = Location [String] deriving (Eq)

(//) :: Location -> String -> Location
(Location loc) // name = Location (name : loc)
infixr 5 //


newtype Reference a = Reference {
  getReference :: Binding
} deriving (Functor, Foldable, Traversable)



data ASTOn (c :: TypeClass) =
  forall t. (c t) => ASTOn (t (ASTOn c))

newtype Stacking (c :: TypeClass) p = Stacking {
  stack :: forall t. (c t) => t p -> p
}

astStacking :: Stacking c (ASTOn c)
astStacking = Stacking ASTOn

{-------------------------------------------------------------------
                          AST Processes
--------------------------------------------------------------------}


type ASTProcOn (c :: TypeClass) m r =
  forall t. (c t) => LensLike' (Compose m r) (t (ASTOn c)) (ASTOn c)

data ASTProcIn t m r i s b = ASTProcIn {
  -- |Create state
  mkState :: forall a. t a -> s,
  -- |Tag branches before local processing
  tagBranch :: forall a. t a -> t (i, a),
  -- |Handle local process on state (parameter is the subcall)
  onState :: i -> m (r b) -> StateT s m (i, r b),
  -- |Merge branches after local processing
  mergeBranch :: forall a. s -> t (i, r a) -> m (r (t a))
}

mkProcess :: (Monad m, Functor r, WithProperty Traversing c, c t) =>
  TypeClassOf c -> ASTProcIn t m r i s a -> LensLike' (Compose m r) (t a) a
mkProcess cl ASTProcIn {
  mkState = mkState,
  tagBranch = tagBranch,
  onState = onState,
  mergeBranch = mergeBranch
} subProc br = Compose $ do
  let localA i = onState i . getCompose . subProc
  let proced = (cl |. traversing) (uncurry localA) (tagBranch br)
  runStateT proced (mkState br) >>= uncurry (flip mergeBranch)


-- |Processing of AST (Depth-first traversal)
processAST :: (Monad m, Functor r) =>
  ASTProcOn c m r -> ASTOn c -> (Compose m r) (ASTOn c)
processAST process (ASTOn br) =
  ASTOn <$> process (processAST process) br


newtype Conversion (d :: TypeClass) t = Conversion {
  conversion :: forall a p. TypeClassOf d -> Stacking d p -> t a -> p
}

convertAST :: (WithProperty (Conversion d) c) => ASTOn c -> ASTOn d
convertAST inp = let
  clc = classOf inp
  cld = classOf outp
  outp = case inp of
    ASTOn br -> (clc |. conversion) cld astStacking br
  in outp

