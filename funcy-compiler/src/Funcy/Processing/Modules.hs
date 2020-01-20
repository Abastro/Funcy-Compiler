-- Module System for Funcy (Most of this is just to simulate duck typing)

{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}

module Funcy.Processing.Modules where

import Control.Applicative
import Control.Monad

import qualified Data.Map.Lazy as Map
import qualified Data.Set as Set
import           Text.Printf                    ( printf )

data Containment c t = Containment {
    wrap :: t -> c,
    unwrap :: c -> Maybe t
}

idCont :: Containment a a
idCont = Containment {
    wrap = id,
    unwrap = Just
}

chainCont :: Containment b a -> Containment c b -> Containment c a
chainCont con2 con1 = Containment {
    wrap = wrap con1 . wrap con2,
    unwrap = unwrap con1 >=> unwrap con2
}

containLeft :: Containment (Either a b) a
containLeft = Containment {
    wrap = Left,
    unwrap = either Just (const Nothing)
}

containRight :: Containment (Either a b) b
containRight = Containment {
    wrap = Right,
    unwrap = either (const Nothing) Just
}


class Expansive f where
    expandWith :: Containment b a -> f a -> f b

newtype Broad f c a = Broad { deBroad :: Containment c a -> f c }
instance Expansive (Broad f c) where
    expandWith cont toFeature = Broad (deBroad toFeature . chainCont cont)


-- A type which can represent all types a module requires
-- Type dep consists of the direct dependency module types
newtype ModuleType loc dep = FormModule { containerType :: Either loc dep }

moduleWraps :: Containment (ModuleType loc dep) (Either loc dep)
moduleWraps = Containment {
    wrap = FormModule,
    unwrap = Just . containerType
}

type Domain = String

-- Set of direct dependencies
type DirectDeps = Set.Set Domain

-- Mapping which maps each indirect dependency module to specific direct dependency module which is dependent to the indirect module.
type DepDistrib = Map.Map Domain Domain

-- Dependencies for moduloid m. Here m represents the sum type of supported types.
data Dependencies dep = DepInfo DirectDeps DepDistrib
instance Show (Dependencies dep) where
    show (DepInfo deps _) = printf "Depends on %s" $ show $ Set.toList deps


-- Domained group with dependencies
class DomainedGroup g where
    dependencies :: Dependencies g

-- Combines dependencies.
-- TODO : More efficient approach
combineDeps :: Dependencies l -> Dependencies r -> Dependencies (Either l r)
combineDeps (DepInfo dir1 distrib1) (DepInfo dir2 distrib2) = DepInfo (Set.union dir1 dir2) (Map.union distrib1 distrib2)

instance (DomainedGroup l, DomainedGroup r) => DomainedGroup (Either l r) where
    dependencies = combineDeps dependencies dependencies

data Void

instance DomainedGroup Void where
    dependencies = DepInfo Set.empty Map.empty


-- Representation of Module Domain
newtype ModuleDomain loc = MInstance Domain deriving Show

-- DomainedLocal class, which represents the local type with given domain name
class DomainedLocal loc where
    mInstance :: ModuleDomain loc


createDependency :: Dependencies dep -> ModuleDomain loc -> Dependencies (ModuleType loc dep)
createDependency (DepInfo _ depDist) (MInstance domain) = DepInfo (Set.singleton domain)
    $ foldr Map.union Map.empty $ fmap (`Map.singleton` domain) depDist

instance (DomainedLocal loc, DomainedGroup dep) => DomainedGroup (ModuleType loc dep) where
    dependencies = createDependency dependencies mInstance


-- Element-specific Feature
class (Expansive f, DomainedGroup g) => ElementFeature f g where
    featureOf :: g -> f g

-- Feature for certain local module, implemented by individual module
class (Functor f, DomainedLocal loc) => LocalFeature f loc dep where
    getFeature :: f (ModuleType loc dep)

-- Feature extraction from certain domain
class (Functor f, DomainedGroup g) => DomainedFeature f g where
    findFeature :: Domain -> Maybe (f g)


instance (Expansive f) => ElementFeature f Void where
    featureOf _ = error "impossible"

instance (Functor f) => DomainedFeature f Void where
    findFeature _ = Nothing



instance (ElementFeature f l, ElementFeature f r) => ElementFeature f (Either l r) where
    featureOf = either
        (expandWith containLeft . featureOf)
        (expandWith containRight . featureOf)


getDirectDep :: Dependencies dep -> Domain -> Maybe (ModuleDomain dep)
getDirectDep (DepInfo _ distrib) domain = MInstance <$> Map.lookup domain distrib

findFeatureDep :: DomainedFeature f dep => Dependencies dep -> Domain -> Maybe (f dep)
findFeatureDep (DepInfo dirs _) domain = if Set.member domain dirs then findFeature domain else Nothing

expandFeature :: DomainedFeature f g => ModuleDomain h -> (g -> h) -> Maybe (f h)
expandFeature (MInstance domain) trans = (fmap $ fmap trans) (findFeatureDep dependencies domain)

-- Domained feature of Union
instance (DomainedFeature f l, DomainedFeature f r) => DomainedFeature f (Either l r) where
    findFeature domain = do
        dirDomain <- getDirectDep dependencies domain
        expandFeature dirDomain Left <|> expandFeature dirDomain Right


instance (DomainedLocal loc, ElementFeature f loc, ElementFeature f dep) => ElementFeature f (ModuleType loc dep) where
    featureOf elem = case containerType elem of
        Left el -> expandWith moduleWraps $ expandWith containLeft $ featureOf el
        Right el -> expandWith moduleWraps $ expandWith containRight $ featureOf el

instance (LocalFeature f loc dep, DomainedFeature f dep) => DomainedFeature f (ModuleType loc dep) where
    findFeature domain = featureInModule domain mInstance <|> ( fmap $ fmap (FormModule . Right) ) (findFeature domain)

featureInModule :: LocalFeature f loc dep => Domain -> ModuleDomain loc -> Maybe (f (ModuleType loc dep))
featureInModule domain (MInstance domM) = if domain == domM then Just getFeature else Nothing


