{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}

module Funcy.Processing.Util where

import Control.Monad.Identity ( Identity )

import Control.Lens.Type ( Lens, Iso, Getter )
import qualified Control.Lens.Combinators as Lens

import Data.Kind ( Constraint )

import Data.Graph ( Graph, SCC )
import Data.IntMap ( IntMap )
import Data.Map ( Map )
import qualified Data.IntMap as IntMap
import qualified Data.Map as Map


{-----------------------------------------------------------------------------------------------------------------------------------
                                                        Miscellaneous
------------------------------------------------------------------------------------------------------------------------------------}

type TypeClass = (* -> *) -> Constraint

-- Type representing certain typeclass
data TypeClassOf (c :: TypeClass) = TypeClassOf

classOf :: p c -> TypeClassOf c
classOf = const $ TypeClassOf

type Id = Identity

invfmap :: Functor f => f (a -> b) -> a -> f b
invfmap f x = ($ x) <$> f

{-----------------------------------------------------------------------------------------------------------------------------------
                                                        Lens Utilities
------------------------------------------------------------------------------------------------------------------------------------}

mapGetter :: Functor f => Getter s a -> Getter (f s) (f a)
mapGetter = Lens.to . fmap . Lens.view

map2Getter :: (Functor f, Functor g) => Getter s a -> Getter (f (g s)) (f (g a))
map2Getter = Lens.to . fmap . fmap . Lens.view

map3Getter :: (Functor f, Functor g, Functor h) => Getter s a -> Getter (f (g (h s))) (f (g (h a)))
map3Getter = Lens.to . fmap . fmap . fmap . Lens.view

attached :: Lens (i, a) (j, a) i j
attached = Lens._1

content :: Lens (i, a) (i, b) a b
content = Lens._2

{-----------------------------------------------------------------------------------------------------------------------------------
                                                        Data Structure Wrapping
------------------------------------------------------------------------------------------------------------------------------------}

-- | Dictionary, i.e. map. Used alike a multiset.
class (Foldable f) => Dictionary f where
  type Key f
  cempty :: f a
  singleton :: Key f -> a -> f a
  keyList :: f a -> [Key f]
  pairList :: f a -> [(Key f, a)]
  merge :: Semigroup a => f a -> f a -> f a
  search :: Key f -> f a -> Maybe a
  insertWithKey :: Key f -> a -> f a -> f a
  removeWithKey :: Key f -> f a -> f a

instance (Ord k) => Dictionary (Map k) where
  type Key (Map k) = k
  cempty = Map.empty
  singleton = Map.singleton
  keyList = Map.keys
  pairList = Map.assocs
  merge = Map.unionWith (<>)
  search = Map.lookup
  insertWithKey = Map.insert
  removeWithKey = Map.delete

instance Dictionary IntMap where
  type Key (IntMap) = Int
  cempty = IntMap.empty
  singleton = IntMap.singleton
  keyList = IntMap.keys
  pairList = IntMap.assocs
  merge = IntMap.unionWith (<>)
  search = IntMap.lookup
  insertWithKey = IntMap.insert
  removeWithKey = IntMap.delete

newtype Union f a = Union {runUnion :: f a}

isoUnion :: Iso (Union f a) (Union g b) (f a) (g b)
isoUnion = Lens.coerced

instance (Foldable f) => Foldable (Union f) where
  foldMap f = foldMap f . runUnion

instance (Dictionary f) => Dictionary (Union f) where
  type Key (Union f) = Key f
  cempty = Union cempty
  singleton = fmap Union . singleton
  keyList = keyList . runUnion
  pairList = pairList . runUnion
  merge (Union c) (Union c') = Union $ merge c c'
  search key = search key . runUnion
  insertWithKey key value = Lens.over isoUnion $ insertWithKey key value
  removeWithKey key = Lens.over isoUnion $ removeWithKey key

instance (Dictionary f, Semigroup a) => Semigroup (Union f a) where
  (<>) = merge

instance (Dictionary f, Semigroup a) => Monoid (Union f a) where
  mempty = Union cempty

$(Lens.makePrisms ''SCC)
