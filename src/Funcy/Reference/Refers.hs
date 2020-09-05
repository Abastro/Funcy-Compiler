{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TemplateHaskell #-}
module Funcy.Reference.Refers (
  SyntaxIndex(..), partName, bindings,
  DesugarFold(..), _Refers, _Simple, _Sort, _Cyclic,
  Desugar(..), expandPart, foldInto, defaultExpandPart,
  ReferSugar(..),
  RefError(..), ReferInfo(..), Refers, Referred,
  Rearrange,
) where

import Control.Monad ( when, unless, guard )
import Control.Monad.Reader ( ReaderT )
import Control.Monad.Writer ( WriterT )
import qualified Control.Monad.Reader as Reader
import qualified Control.Monad.Writer as Writer

import Control.Lens.TH ( makePrisms, makeLenses )
import Control.Lens.Type ( Lens' )
import Control.Lens.Operators ( (^.), (.~), (.>), (<.), (+=), (<>=) )
import qualified Control.Lens.Combinators as Lens

import Data.Coerce ( coerce )
import Data.Foldable ( Foldable(fold, toList) )
import Data.Maybe ( isJust )
import Data.Monoid ( Endo(..) )

import Data.Set ( Set )
import Data.Graph ( Graph, SCC )
import qualified Data.Graph as Graph
import Data.Map ( Map )

import Funcy.Base.Util
import Funcy.Base.AST


{-------------------------------------------------------------------
                          Reference Handling
--------------------------------------------------------------------}

-- TODO Load required module first -> Needs be addressed by main process


-- |Syntax indexing with bindings involved.
-- Part name should be unique in the specific syntax.
data SyntaxIndex f = SyntaxIndex {
  _partName :: String,
  _bindings :: f Binding
}
$(Lens.makeLenses ''SyntaxIndex)

type SIndexed f = (,) (SyntaxIndex f)


data DesugarFold t a =
  -- |Reference (Leaf). Never branch.
  Refers (Binding)
  -- |Simple fold. Any kind of unfolding/folding is strictly discouraged.
  | Simple (Endo (t a))
  -- |Sorting fold
  | Sort ([SIndexed Id a] -> t a)
  -- |Sorting fold allowing cyclic references
  | Cyclic ([SCC (SIndexed Id a)] -> t a)
$(makePrisms ''DesugarFold)

-- |Desugar type, should be generic over type a
data Desugar t a = Desugar {
  _expandPart :: SIndexed [] a -> [SIndexed Id a],
  _foldInto :: DesugarFold t a
}
$(makeLenses ''Desugar)

defaultExpandPart :: SIndexed [] a -> [SIndexed Id a]
defaultExpandPart (SyntaxIndex n bs, a) = (, a) . SyntaxIndex n . coerce <$> bs


class Traversable t => ReferSugar t where
  -- |Index each part
  tagPart :: t a -> t (SIndexed [] a)

  -- |Desugar process
  desugar :: t a -> Desugar t c

instance Collection ReferSugar where
  asTraversed _ = traverse


data RefError =
  -- Conflicts among same level declarations
  Conflict Binding [Location]
  -- Illegal early references
  | EarlyRef ReferInfo
  -- Illegal recursive references
  | Recursive [ReferInfo]

data ReferInfo = ReferInfo Binding Location [Location]

type Refers = Union (Map Binding)
type Referred = WriterT (Refers [Location]) Id

type Rearrange
  = ReaderT Location
    (WriterT [RefError]
    Id)


{-------------------------------------------------------------------
                          Basic instance
--------------------------------------------------------------------}

-- |Reference case
instance ReferSugar Reference where
  tagPart = coerce
  desugar ref = Desugar {
    _expandPart = defaultExpandPart, -- Placeholder
    _foldInto = Refers $ getReference ref
  }
