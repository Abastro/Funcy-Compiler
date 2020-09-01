{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE DeriveTraversable #-}
module Funcy.Processing.AST where

import Control.Monad.State
import Control.Lens
import Data.Kind
import Data.Functor.Compose

import Funcy.Processing.Util

{-----------------------------------------------------------------------------------------------------------------------------------
                                                    Abstract Syntax Tree
------------------------------------------------------------------------------------------------------------------------------------}

-- |Binding reference name
type Binding = String

data Reference =
  EmptyRef                    -- Empty reference - to be used for one-sided branches
  | InRef Binding
  | Internal String [String]
  deriving (Eq, Ord)
$(makePrisms ''Reference)

data AST t = Leaf Reference | Branch (t (AST t))

data Binary p a = Binary p a a deriving (Functor, Foldable, Traversable)
data Side = LeftSide | RightSide deriving (Eq, Ord, Enum, Show)

-- |Location
newtype Location = Location [String] deriving (Eq)

(//) :: Location -> String -> Location
(Location loc) // name = Location (name : loc)
infixr 5 //



data ASTOn (c :: TypeClass) =
  LeafOn Reference |
  forall t. (Traversable t, c t) => BranchOn (t (ASTOn c))


{-----------------------------------------------------------------------------------------------------------------------------------
                                                    AST Processes
------------------------------------------------------------------------------------------------------------------------------------}

type LeafProc m r = Reference -> (Compose m r) Reference

type BranchProc (c :: TypeClass) m r =
  forall a t. (Traversable t, c t) => LensLike' (Compose m r) (t a) a

data ASTProcOn (c :: TypeClass) m r = ASTProcOn {
  procLeaf :: LeafProc m r,
  procBranch :: BranchProc c m r
}

data BranchProcess t m r u s = BranchProcess {
  -- |Create state
  mkState :: forall a. t a -> s,
  -- |Tag branches before local processing
  tagBranch :: forall a. t a -> t (StateT s m a),
  -- |Handle local process on state (parameter is the subcall)
  onState :: forall a. m (r a) -> StateT s m (u a),
  -- |Merge branch after local processing
  mergeBranch :: forall a. s -> t (u a) -> m (r (t a))
}

mkBrProcess :: (Monad m, Functor r, Traversable t) =>
  BranchProcess t m r u s -> LensLike' (Compose m r) (t a) a
mkBrProcess BranchProcess {
  mkState = mkState,
  tagBranch = tagBranch,
  onState = onState,
  mergeBranch = mergeBranch
} subProc br = Compose $ do
  let tagBr = tagBranch br
  let localA = (>>= onState . getCompose . subProc)
  (procBr, state) <- runStateT (traverse localA tagBr) (mkState br)
  mergeBranch state procBr


-- |Processing of AST (Depth-first traversal)
processAST :: (Monad m, Functor r) =>
  ASTProcOn c m r -> ASTOn c -> (Compose m r) (ASTOn c)
processAST process (LeafOn ref) =
  LeafOn <$> procLeaf process ref
processAST process (BranchOn br) =
  BranchOn <$> (procBranch process) (processAST process) br

