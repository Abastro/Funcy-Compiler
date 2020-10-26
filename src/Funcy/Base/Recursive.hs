{-------------------------------------------------------------------
                          Recursive Type
                  [* Borrowed from data-fix *]
--------------------------------------------------------------------}
{-# LANGUAGE RankNTypes #-}
module Funcy.Base.Recursive where

import Control.Lens.Type ( LensLike, Lens )
import qualified Control.Lens.Combinators as Lens

newtype Fix f = Fix {
  unfix :: f (Fix f)
}

hoistFix :: Functor f => (forall a. f a -> g a) -> Fix f -> Fix g
hoistFix nt = Fix . nt . fmap (hoistFix nt) . unfix

foldFix :: Functor f => (f a -> a) -> Fix f -> a
foldFix g = g . fmap (foldFix g) . unfix

unfoldFix :: Functor f => (a -> f a) -> a -> Fix f
unfoldFix g = Fix . fmap (unfoldFix g) . g

foldFixM :: (Monad m, Traversable t) => (t a -> m a) -> Fix t -> m a
foldFixM g = (g =<<) . traverse (foldFixM g) . unfix

unfoldFixM :: (Monad m, Traversable t) => (a -> m (t a)) -> a -> m (Fix t)
unfoldFixM g = fmap Fix . (traverse (unfoldFixM g) =<<) . g

foldLens :: Functor m => Lens a b (s a) (t b) ->
  LensLike m (s a) (t b) a b -> a -> m b
foldLens cv l = cv . l  $ foldLens cv l

fixLens :: Functor m => LensLike m (f (Fix f)) (g (Fix g)) (Fix f) (Fix g) ->
  Fix f -> m (Fix g)
fixLens = foldLens $ Lens.iso unfix Fix
