module Funcy.Processing.Values where

import Control.Applicative
import Control.Monad

import Control.Monad.Reader
import Control.Monad.Writer
import Control.Monad.State

import Data.Function
import Data.Functor
import Data.Functor.Identity
import Data.Foldable

import Data.Graph as Graph
import qualified Data.Map.Lazy as MapL
import qualified Data.Map.Strict as MapS
import qualified Data.Set as Set

import Funcy.Processing.AST

