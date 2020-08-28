{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE DeriveTraversable #-}
module Funcy.Processing.AST where

import Control.Monad.State
import Control.Lens

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
type Location = [Binding]

{-
instance Functor m => Functor (AST m) where
  fmap f (Leaf ref) = Leaf ref
  fmap f (Branch flag branch) = Branch (f flag) $ (fmap . fmap) f branch
-}


{-----------------------------------------------------------------------------------------------------------------------------------
                                                    AST Processes
------------------------------------------------------------------------------------------------------------------------------------}

-- |AST Process on monad m with result r over AST t.
-- s is the intermediate state.
data ASTProcess m r t s = ASTProcess {
  -- |Handle reference
  handleRef :: Reference -> m (r Reference),
  -- |Create state
  mkState :: forall a. t a -> s,
  -- |Tag branches before local processing
  tagBranch :: forall a. t a -> t (StateT s m a),
  -- |Handle local process on state
  onState :: forall a. m (r a) -> StateT s m (r a),
  -- |Merge branch after local processing
  mergeBranch :: forall a. s -> t (r a) -> m (r (t a))
}

-- |Processing of AST (Depth-first traversal)
processAST :: (Monad m, Functor r, Traversable t) =>
  ASTProcess m r t s -> AST t -> m (r (AST t))
processAST process (Leaf ref) = fmap Leaf <$> handleRef process ref
processAST process (Branch br) = do
  -- Tagged branches
  let tagBr = tagBranch process br
  -- Locally process tagged AST
  let localA tagAST = tagAST >>= onState process . processAST process
  -- Traverse local processes
  (procBr, state) <- runStateT (traverse localA tagBr) (mkState process br)
  -- Handle the whole branch aftermath
  fmap Branch <$> mergeBranch process state procBr
