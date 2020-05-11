-- Module System for Funcy (Most of this is just to simulate duck typing)

{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE LambdaCase #-}

module Funcy.Processing.Modules where

import Control.Applicative
import Control.Monad

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set

import Data.Void

import GHC.Generics

import Text.Printf

-- Inclusion type, to represent inclusion relationship
data Include p c = Inclusion {
    wrap :: c -> p,
    unwrap :: p -> Maybe c
}

type p :>: c = Include p c

idIn :: a :>: a
idIn = Inclusion id Just

composeIn :: b :>: c -> a :>: b -> a :>: c
composeIn i j = Inclusion {
    wrap = wrap j . wrap i,
    unwrap = unwrap j >=> unwrap i
}

(>.>) = composeIn

bijection :: (a -> b) -> (b -> a) -> b :>: a
bijection w u = Inclusion w (Just . u)

leftIn :: (f :+: g) p :>: f p
leftIn = Inclusion {
    wrap = L1,
    unwrap = \case L1 p -> Just p; R1 _ -> Nothing
}
rightIn :: (f :+: g) p :>: g p
rightIn = Inclusion {
    wrap = R1,
    unwrap = \case L1 _ -> Nothing; R1 p -> Just p
}


-- Expansive features which can applied to parents
class Expansive f where
    expand :: Include p c -> f c -> f p


-- A type which can represent all types a module requires
-- Type dep consists of the direct dependency module types
data ModuleType loc dep = Dep dep | Local loc

depIn :: ModuleType loc dep :>: dep
depIn = Inclusion {
    wrap = Dep,
    unwrap = \case Dep d -> Just d; _ -> Nothing
}

localIn :: ModuleType loc dep :>: loc
localIn = Inclusion {
    wrap = Local,
    unwrap = \case Local l -> Just l; _ -> Nothing
}

-- Domain which specifies the module
type Domain = String

-- Set of direct dependencies
type DirectDeps = Set.Set Domain

-- Mapping which maps each indirect dependency module to specific direct dependency module which is dependent to the indirect module.
type DepDistrib = Map.Map Domain Domain

-- Dependencies for moduloid m. Here m represents the sum type of supported types.
data Dependencies dep = DepInfo DirectDeps DepDistrib deriving Functor
instance Show (Dependencies dep) where
    show (DepInfo deps _) = printf "Depends on %s" $ show $ Set.toList deps


-- Group of modules with dependencies
class ModuleGroup t where
    dependencies :: Dependencies t

    default dependencies :: (Generic t, ModuleGroup' (Rep t)) => Dependencies t
    dependencies = fmap to dependencies'

class ModuleGroup' f where
    dependencies' :: Dependencies (f p)

instance ModuleGroup' V1 where
    dependencies' = DepInfo Set.empty Map.empty

instance ModuleGroup c => ModuleGroup' (K1 i c) where
    dependencies' = fmap K1 dependencies

instance (ModuleGroup' f) => ModuleGroup' (M1 i t f) where
    dependencies' = fmap M1 dependencies'

instance (ModuleGroup' f, ModuleGroup' g) => ModuleGroup' (f :+: g) where
    dependencies' = combineDeps dependencies' dependencies' where
        combineDeps :: Dependencies (l p) -> Dependencies (r p) -> Dependencies ((l :+: r) p)
        combineDeps (DepInfo dir1 distrib1) (DepInfo dir2 distrib2) = do
            let combDir = Set.union dir1 dir2
            let combDistrib = Map.union distrib1 distrib2
            DepInfo combDir combDistrib


instance ModuleGroup Void

-- Representation of domain for local type for each module
newtype ModuleDomain loc = MInstance Domain deriving Show
class DomainedLocal loc where
    mInstance :: ModuleDomain loc

-- Module group for single module
instance (DomainedLocal loc, ModuleGroup dep) => ModuleGroup (ModuleType loc dep) where
    dependencies = createDep dependencies mInstance where
        createDep :: Dependencies dep -> ModuleDomain loc -> Dependencies (ModuleType loc dep)
        createDep (DepInfo _ depDist) (MInstance domain) = DepInfo (Set.singleton domain)
            $ Map.unions $ flip Map.singleton domain <$> depDist -- each element into the domain


-- Element-specific feature - Use generic deriving
class (Expansive f) => ElementFeature f t where
    featureOf :: t -> f t

    default featureOf :: (Generic t, ElementFeature' f (Rep t)) => t -> f t
    featureOf = expand (bijection to from) . featureOf' . from

class (Expansive f) => ElementFeature' f g where
    featureOf' :: g p -> f (g p)

instance (Expansive f) => ElementFeature' f V1 where
    featureOf' = undefined

instance (ElementFeature f c) => ElementFeature' f (K1 i c) where
    featureOf' (K1 x) = expand (bijection K1 unK1) $ featureOf x

instance (ElementFeature' f g) => ElementFeature' f (M1 i t g) where
    featureOf' (M1 x) = expand (bijection M1 unM1) $ featureOf' x

instance (ElementFeature' i f, ElementFeature' i g) => ElementFeature' i (f :+: g) where
    featureOf' (L1 x) = expand leftIn $ featureOf' x
    featureOf' (R1 x) = expand rightIn $ featureOf' x

instance (Expansive f) => ElementFeature f Void


-- Feature extraction from certain domain - Use generic deriving
-- Searches more efficiently via immediately calculating which route to go for
class (Expansive f, ModuleGroup t) => DomainedFeature f t where
    findFeature :: Domain -> Maybe (f t)

    default findFeature :: (Generic t, DomainedFeature' f (Rep t)) => Domain -> Maybe (f t)
    findFeature = fmap (expand $ bijection to from) . findFeature'

class (Expansive f, ModuleGroup' g) => DomainedFeature' f g where
    findFeature' :: Domain -> Maybe (f (g p))


instance (Expansive f) => DomainedFeature' f V1 where
    findFeature' _ = Nothing

instance (DomainedFeature f c) => DomainedFeature' f (K1 i c) where
    findFeature' = fmap (expand $ bijection K1 unK1) . findFeature

instance (DomainedFeature' f g) => DomainedFeature' f (M1 i t g) where
    findFeature' = fmap (expand $ bijection M1 unM1) . findFeature'

instance (DomainedFeature' i f, DomainedFeature' i g) => DomainedFeature' i (f :+: g) where
    findFeature' domain = do
        dirDomain <- directDep dependencies' domain
        expandUsing dirDomain leftIn <|> expandUsing dirDomain rightIn
        where
            directDep :: Dependencies dep -> Domain -> Maybe (ModuleDomain dep)
            directDep (DepInfo _ distrib) domain = MInstance <$> Map.lookup domain distrib

            expandUsing :: DomainedFeature' f g => ModuleDomain h -> (h :>: g p) -> Maybe (f h)
            expandUsing (MInstance domain) trans = expand trans <$> findIn dependencies' domain

            findIn :: DomainedFeature' f g => Dependencies (g p) -> Domain -> Maybe (f (g p))
            findIn (DepInfo dirs _) domain = if Set.member domain dirs then findFeature' domain else Nothing

instance (Expansive f) => DomainedFeature f Void


-- Actual implementation of element-specific feature for individual module
class (Expansive f, DomainedLocal loc) => FeatureElImpl f loc dep where
    featureImplEl :: loc -> f (ModuleType loc dep)

instance (DomainedLocal loc, FeatureElImpl f loc dep, ElementFeature f dep) => ElementFeature f (ModuleType loc dep) where
    featureOf elem = case elem of
        Dep el -> expand depIn $ featureOf el
        Local el -> featureImplEl el

-- Actual implementation of global feature for individual module.
-- This should be implemented to search feature using domain.
class (Expansive f, DomainedLocal loc) => FeatureGlImpl f loc dep where
    featureImplGl :: f (ModuleType loc dep)

instance (FeatureGlImpl f loc dep, DomainedFeature f dep) => DomainedFeature f (ModuleType loc dep) where
    findFeature domain = featureInModule domain mInstance
        <|> expand depIn <$> findFeature domain -- Not here
        where
            featureInModule :: FeatureGlImpl f loc dep => Domain -> ModuleDomain loc -> Maybe (f (ModuleType loc dep))
            featureInModule domain (MInstance domM) = if domain == domM then Just featureImplGl else Nothing
