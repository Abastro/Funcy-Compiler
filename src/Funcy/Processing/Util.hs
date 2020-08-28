{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
module Funcy.Processing.Util where

import           Control.Lens

import           Data.Set (Set)
import qualified Data.Set as Set
import           Data.Map (Map)
import qualified Data.Map as Map
import           Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap

import           Data.Graph (Graph, SCC)
import qualified Data.Graph as Graph


mapGetter :: Functor f => Getter s a -> Getter (f s) (f a)
mapGetter = to . fmap . view

-- |Dictionary, in other words map. Used alike a multiset.
class (Foldable f) => Dictionary f where
  type Key f
  cempty :: f a
  merge :: Semigroup a => f a -> f a -> f a
  search :: Key f -> f a -> Maybe a
  insertWithKey :: Key f -> a -> f a -> f a
  removeWithKey :: Key f -> f a -> f a

instance (Ord k) => Dictionary (Map k) where
  type Key (Map k) = k
  cempty = Map.empty
  merge = Map.unionWith (<>)
  search = Map.lookup
  insertWithKey = Map.insert
  removeWithKey = Map.delete

instance Dictionary IntMap where
  type Key (IntMap) = Int
  cempty = IntMap.empty
  merge = IntMap.unionWith (<>)
  search = IntMap.lookup
  insertWithKey = IntMap.insert
  removeWithKey = IntMap.delete

newtype Union f a = Union { runUnion :: f a }

isoUnion :: Iso' (Union f a) (f a)
isoUnion = iso runUnion Union


instance (Foldable f) => Foldable (Union f) where
  foldMap f = foldMap f . runUnion

instance (Dictionary f) => Dictionary (Union f) where
  type Key (Union f) = Key f
  cempty = Union cempty
  merge (Union c) (Union c') = Union $ merge c c'
  search key = search key . runUnion
  insertWithKey key value = over isoUnion $ insertWithKey key value
  removeWithKey key = over isoUnion $ removeWithKey key

instance (Dictionary f, Semigroup a) => Semigroup (Union f a) where
  (<>) = merge

instance (Dictionary f, Semigroup a) => Monoid (Union f a) where
  mempty = Union cempty


$(makePrisms ''SCC)
