{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Funcy.Processing.Values where

import Control.Applicative
import Data.Graph
import Data.List
import qualified Data.Map.Lazy as Map
import qualified Data.Set as Set
import Funcy.Processing.Modules

type Name = String


-- Description for interpretation error handling
class (Monad d) => Description d where
    describeError :: String -> d a

newtype Desc a = Desc (Maybe a) deriving (Functor, Applicative, Monad)

instance Description Desc where
    describeError msg = Desc Nothing


{-
class Parameterized expr where
    type Param expr
    type Target expr
    rawExpr :: expr -> IpExpr (Param expr) (Target expr)

class Functional fn where
    type Input fn
    type Output fn
    rawFn :: fn -> Maybe (IpFunction (Input fn) (Output fn))

class Paired pr where
    type Prior pr
    type Posterior pr
    rawPr :: pr -> IpPair (Prior pr) (Posterior pr)
-}



data EValue ext = External ext | Composite Graph (Table (EValue ext)) deriving Functor


-- Translator to certain expression
newtype Translator expr = Translator { translateToExpr :: Name -> expr }

instance Functor Translator where
    fmap func trans = Translator (func . translateToExpr trans)

translateLocal :: DomainedFeature Translator expr => (Domain, Name) -> Maybe expr
translateLocal (domain, name) = do
    translator <- findFeature domain
    return $ translateToExpr translator name
{-
translateAST :: DomainedFeature Translator expr => EValue (Domain, Name) -> Maybe (EValue expr)
translateAST = extractMaybe . fmap translateLocal


-- Or use Alternative?
extractMaybe :: EValue (Maybe ext) -> Maybe (EValue ext)
extractMaybe (External extern) = fmap External extern
extractMaybe (Composite egraph vals) = fmap Composite egraph (fmap extractMaybe vals)
-}


--evaluate :: ElementFeature (Processor ext) ext => EValue ext -> EValue ext
--evaluate (External extern) = External extern
--evaluate (Composite egraph vals) = 

{-
[ 0 ]
\a. [ floor a ]
\a. \b. [ (+) a b ]
[ ext [things] ]
-}

-- Modules related with interpreters
newtype InterModule m = Intermodule m


