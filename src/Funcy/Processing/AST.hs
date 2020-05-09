{-# LANGUAGE DeriveTraversable #-}
module Funcy.Processing.AST where

{-----------------------------------------------------------------------------------------------------------------------------------
                                                    Abstract Syntx Tree
------------------------------------------------------------------------------------------------------------------------------------}

data Reference = InRef Binding | Internal String [String] deriving (Eq, Ord)

data AST m p = Leaf Reference | Branch p (m (AST m p))
data Binary t = Binary t t deriving (Functor, Foldable, Traversable)

instance Functor m => Functor (AST m) where
    fmap f (Leaf ref) = Leaf ref
    fmap f (Branch flag branch) = Branch (f flag) $ (fmap . fmap) f branch


-- Binding reference name
type Binding = String



