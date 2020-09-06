{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TemplateHaskell #-}
module Funcy.Reference.Refers (
  SyntaxIndex(..), partName, bindings,
  DesugarFold(..), _Refers, _Simple, _Sort, _Cyclic,
  Desugar(..), expandPart, foldInto, defaultExpandPart,
  RefError(..), ReferInfo(..), Refers, Referred,
  Rearrange, internalProcRearr
) where

import Control.Monad ( when, unless, guard )
import Control.Monad.Trans ( MonadTrans(..) )
import Control.Monad.Reader ( ReaderT, MonadReader(..) )
import Control.Monad.Writer ( WriterT, MonadWriter(..) )
import qualified Control.Monad.Reader as Reader
import qualified Control.Monad.Writer as Writer

import Control.Lens.TH ( makePrisms, makeLenses )
import Control.Lens.Type ( Lens' )
import Control.Lens.Operators
    ( (^.), (.>), (<.), (+=), (.~), (<>=) )
import qualified Control.Lens.Combinators as Lens

import Data.Coerce ( coerce )
import Data.Foldable ( Foldable(fold, toList) )
import Data.Maybe ( isJust )
import Data.Monoid ( Endo(..) )

import Data.Map ( Map )
import Data.Graph ( Graph, SCC )
import qualified Data.Graph as Graph

import Funcy.Base.Util
import Funcy.Base.AST

-- TODO Load required module first -> Needs be addressed by main process


-- |Syntax indexing with bindings involved.
-- Part name should be unique in the specific syntax.
data SyntaxIndex f = SyntaxIndex {
  _partName :: String,
  _bindings :: f Binding
}
$(makeLenses ''SyntaxIndex)

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
data Desugar t = Desugar {
  _expandPart :: forall a. SIndexed [] a -> [SIndexed Id a],
  _foldInto :: forall a. DesugarFold t a
}
$(makeLenses ''Desugar)

defaultExpandPart :: SIndexed [] a -> [SIndexed Id a]
defaultExpandPart (SyntaxIndex n bs, a) = (, a) . SyntaxIndex n . coerce <$> bs


type Refers = Union (Map Binding)
type Referred = WriterT (Refers [Location]) Id


data BrIndex f = BrIndex {
  _iIndex :: Int,
  _sIndex :: SyntaxIndex f
}
$(makeLenses ''BrIndex)

data InState t = InState {
  _desugaring :: Desugar t,
  _curIndex :: Int,
  -- All declarations
  _decls :: Refers [String],
  -- First declarations with its position
  _fdecls :: Map Binding (Int, String)
}
$(makeLenses ''InState)


data RefError =
  -- Conflicts among same level declarations
  Conflict Binding [Location]
  -- Illegal early references
  | EarlyRef ReferInfo
  -- Illegal recursive references
  | Recursive [ReferInfo]

data ReferInfo = ReferInfo Binding Location [Location]

type Rearrange
  = ReaderT Location
    (WriterT [RefError]
    Id)


theBinding :: Lens' (SyntaxIndex Id) Binding
theBinding = bindings . Lens.coerced

-- TODO Maybe error out on problematic ones?

-- |Internal, do not use (Too complex to use anyway)
internalProcRearr :: Traversable syntax =>
  Indexing (SyntaxIndex []) syntax -> Specific Desugar syntax ->
  (ASTProcIn syntax Rearrange Referred) (BrIndex []) (InState syntax) a
internalProcRearr tag desugar = ASTProcIn {
  tagBranch = Lens.over (Lens.mapped . attached) (BrIndex 0) . indexing tag
  ,
  mkState = \br -> InState {
    _desugaring = specific desugar br,
    _curIndex = 0,
    _decls = cempty,
    _fdecls = cempty
  },
  onState = \index sub -> do
    dsf <- Lens.use $ desugaring . foldInto
    let pName = index ^. sIndex . partName
    let bnds = index ^. sIndex . bindings
    iindex <- Lens.use curIndex

    decls <>= foldMap singleton bnds [pName]            -- Gather declarations (using union)
    when (Lens.has _Simple dsf) $ do
      fdecls <>= foldMap singleton bnds (iindex, pName) -- Gather first declarations
      curIndex += 1

    ast <- lift $ local (// pName) sub
    pure (iIndex .~ iindex $ index , ast),
  mergeBranch = \st br -> do
    loc <- ask
    let dsf = st ^. desugaring . foldInto

    -- Topological sort
    let expand = (Lens.alongside sIndex id) (st ^. desugaring . expandPart)
    let formNode referred = (sequenceA referred,
          referred ^. attached . sIndex . theBinding,
          referred ^. content . Lens.to (keyList . Writer.execWriter))
    let comp = map sequenceA . Graph.stronglyConnComp . map formNode $ foldMap expand br

    -- Conflict check
    -- Binding with > 1 declarations on same level -> Error
    unless (Lens.has _Refers dsf) $ do
      Lens.itraverseOf_ (ifolded <. Lens.filtered (isJust . Lens.preview (Lens.ix 1)))
        (fmap tell . conflictError loc) (runUnion $ st ^. decls)

    -- Cycle check - cyclic SCCs are not allowed unless cyclic
    unless (Lens.has _Cyclic dsf || Lens.has _Refers dsf) $ do
      let unpack = Lens.to Writer.runWriter . Lens.alongside (mapGetter $ attached . sIndex) id
      Lens.itraverseOf_
        (traversed . Lens.below _CyclicSCC . unpack .> ifolded)
        (fmap tell . flip (recursiveError loc)) comp

    -- Early reference check (Simple case only)
    when (Lens.has _Simple dsf) $ do
      let unpack = Lens.to Writer.runWriter . Lens.alongside (attached . iIndex) id
      Lens.itraverseOf_
        (traversed . Lens.below _AcyclicSCC . unpack .> ifolded)
        (fmap tell . earlyRefError loc (st ^. fdecls)) comp

    -- Folding into a branch
    let rmDecl = (flip . foldr $ removeWithKey @Refers) (keyList $ st ^. decls)
    let br' = Writer.censor rmDecl $ sequenceA (br ^. mapGetter content)
    let comp' = sequenceA comp ^. Lens.to (Writer.censor rmDecl)
          . map3Getter (Lens.alongside sIndex id)
    case dsf of
      Refers bnd -> do
        -- Reference is handled here - No work is actually done above since collection is empty
        pure $ tell (singleton bnd [loc]) >> br'
      Simple tr ->
        pure $ appEndo tr <$> br'
      Sort folder ->
        pure $ folder . foldMap Graph.flattenSCC <$> comp'
      Cyclic cycFolder ->
        pure $ cycFolder <$> comp'
} where
  conflictError loc bnd names =
    (: []) . Conflict bnd $ map (loc //) names

  -- |Early Reference Error
  earlyRefError loc decls refInd refers = EarlyRef <$> do
    (bnd, refloc) <- pairList @Refers refers
    (declInd, name) <- toList $ search @(Map Binding) bnd decls
    -- Error only when reference earlier than declaration
    guard (refInd < declInd)
    pure $ ReferInfo bnd (loc // name) refloc

  -- |Recursive Error
  recursiveError loc refers parts = (: []) . Recursive $ do
    part <- parts
    let bnd = part ^. theBinding
    let name = part ^. partName
    pure $ ReferInfo bnd (loc // name) (fold $ search @Refers bnd refers)

