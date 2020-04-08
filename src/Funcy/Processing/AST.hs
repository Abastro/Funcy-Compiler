{-# LANGUAGE DeriveTraversable #-}
module Funcy.Processing.AST where

{-----------------------------------------------------------------------------------------------------------------------------------
                                                    Abstract Syntx Tree
------------------------------------------------------------------------------------------------------------------------------------}

data Reference = RefError String | InRef [Binding] | Internal String deriving (Eq, Ord)

data AST m p = Leaf Reference | Branch p (m (AST m p))
data BiBranch t = BiBranch t t deriving (Functor, Foldable, Traversable)
data MultiBranch t = NormBranch (BiBranch t) | MultiBranch [(Binding, t)]

instance Functor m => Functor (AST m) where
    fmap f (Leaf ref) = Leaf ref
    fmap f (Branch flag branch) = Branch (f flag) $ (fmap . fmap) f branch


-- Binding reference name
type Binding = String

data CoreFlag =
    IntroFunc Binding | ElimFunc
    | IntroPair Binding | ElimPair Binding Binding