-- Module System for Funcy (Most of this is just to simulate duck typing)

{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeOperators #-}

module Funcy.Processing.Modules where

import Control.Applicative
import Control.Monad

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set

import Data.Void

import Text.Printf


-- A type which can represent all types a module requires
-- Type dep consists of the direct dependency module types
newtype ModuleType loc dep = WrapModule { containerType :: Either loc dep }


-- Domain which specifies the module
type Domain = String

-- Set of direct dependencies
type DirectDeps = Set.Set Domain

-- Mapping which maps each indirect dependency module to specific direct dependency module which is dependent to the indirect module.
type DepDistrib = Map.Map Domain Domain

-- Dependencies for moduloid m. Here m represents the sum type of supported types.
data Dependencies dep = DepInfo DirectDeps DepDistrib
instance Show (Dependencies dep) where
    show (DepInfo deps _) = printf "Depends on %s" $ show $ Set.toList deps


-- Group of modules with dependencies
class ModuleGroup g where
    dependencies :: Dependencies g

-- Combines dependencies.
combineDeps :: Dependencies l -> Dependencies r -> Dependencies (Either l r)
combineDeps (DepInfo dir1 distrib1) (DepInfo dir2 distrib2) = DepInfo combDir combDistrib
    where
        combDir = Set.union dir1 dir2
        combDistrib = Map.union distrib1 distrib2

instance (ModuleGroup l, ModuleGroup r) => ModuleGroup (Either l r) where
    dependencies = combineDeps dependencies dependencies

instance ModuleGroup Void where
    dependencies = DepInfo Set.empty Map.empty


-- Representation of domain for local type for each module
newtype ModuleDomain loc = MInstance Domain deriving Show
class DomainedLocal loc where
    mInstance :: ModuleDomain loc


createDep :: Dependencies dep -> ModuleDomain loc -> Dependencies (ModuleType loc dep)
createDep (DepInfo _ depDist) (MInstance domain) = DepInfo (Set.singleton domain)
    $ foldr Map.union Map.empty $ fmap (`Map.singleton` domain) depDist

instance (DomainedLocal loc, ModuleGroup dep) => ModuleGroup (ModuleType loc dep) where
    dependencies = createDep dependencies mInstance


-- Element-specific feature
class (Functor f, ModuleGroup g) => ElementFeature f g where
    featureOf :: g -> f g

-- Actual implementation of feature for individual module.
-- This should be implemented to search feature using domain.
class (Functor f, DomainedLocal loc) => FeatureImpl f loc dep where
    featureImpl :: f (ModuleType loc dep)

-- Feature extraction from certain domain, using feature implementation.
class (Functor f, ModuleGroup g) => DomainedFeature f g where
    findFeature :: Domain -> Maybe (f g)


instance (Functor f) => ElementFeature f Void where
    featureOf _ = error "impossible"

instance (Functor f) => DomainedFeature f Void where
    findFeature _ = Nothing



instance (ElementFeature f l, ElementFeature f r) => ElementFeature f (Either l r) where
    featureOf = either (fmap Left . featureOf) (fmap Right . featureOf)


-- Domained feature of Union
instance (DomainedFeature f l, DomainedFeature f r) => DomainedFeature f (Either l r) where
    findFeature domain = do
        dirDomain <- directDep dependencies domain
        expand dirDomain Left <|> expand dirDomain Right
        where
            directDep :: Dependencies dep -> Domain -> Maybe (ModuleDomain dep)
            directDep (DepInfo _ distrib) domain = MInstance <$> Map.lookup domain distrib

            expand :: DomainedFeature f g => ModuleDomain h -> (g -> h) -> Maybe (f h)
            expand (MInstance domain) trans = fmap trans <$> findIn dependencies domain

            findIn :: DomainedFeature f dep => Dependencies dep -> Domain -> Maybe (f dep)
            findIn (DepInfo dirs _) domain = if Set.member domain dirs then findFeature domain else Nothing


instance (DomainedLocal loc, ElementFeature f loc, ElementFeature f dep) => ElementFeature f (ModuleType loc dep) where
    featureOf elem = case containerType elem of
        Left el -> WrapModule . Left <$> featureOf el
        Right el -> WrapModule . Right <$> featureOf el

instance (FeatureImpl f loc dep, DomainedFeature f dep) => DomainedFeature f (ModuleType loc dep) where
    findFeature domain = featureInModule domain mInstance
        <|> (fmap . fmap) (WrapModule . Right) (findFeature domain)
        where
            featureInModule :: FeatureImpl f loc dep => Domain -> ModuleDomain loc -> Maybe (f (ModuleType loc dep))
            featureInModule domain (MInstance domM) = if domain == domM then Just featureImpl else Nothing
