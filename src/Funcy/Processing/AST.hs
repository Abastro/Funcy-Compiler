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

data Side = LeftSide | RightSide deriving Show


-- |Binding reference name
type Binding = String


{-----------------------------------------------------------------------------------------------------------------------------------
                                                    Closures
------------------------------------------------------------------------------------------------------------------------------------}

-- |Closure with given environment
data Closure e a = Singular a | Closure e [Closure e a]

-- |Create closure from a list of terms
listToClosure :: Monoid e => [a] -> Closure e a
listToClosure = Closure mempty . fmap Singular

enclose :: Monoid e => Closure e a -> Closure e a
enclose = Closure mempty . (: [])

-- |Combines the two closure along with environment
instance Monoid e => Semigroup (Closure e a) where
  (Closure e m) <> (Closure e' n) = Closure (e <> e') (m <> n)
  m             <> (Closure e n)  = Closure e (m : n)
  m             <> n              = Closure mempty [m] <> n

instance Monoid e => Monoid (Closure e a) where
  mempty = Closure mempty []


{-----------------------------------------------------------------------------------------------------------------------------------
                                                    AST Processes
------------------------------------------------------------------------------------------------------------------------------------}

data ASTProcess f m t p a = ASTProcess {
  handleRef :: Reference -> f Reference,
  handleBranch :: (p, m a) -> f (p, m a),
  tagBranch :: p -> m a -> m (a, t),
  localize :: t -> f a -> f a
}

processAST :: (Monad f, Traversable m) => ASTProcess f m t p (AST m p) -> AST m p -> f (AST m p)
processAST process (Leaf ref) = Leaf <$> handleRef process ref
processAST process (Branch flag br) = do
  let subProcess (br, tag) = localize process tag $ processAST process br
  br' <- traverse subProcess (tagBranch process flag br)
  (flag', br'') <- handleBranch process (flag, br')
  pure $ Branch flag' br''
