{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TemplateHaskell #-}
module Funcy.Processing.Refers (
  SyntaxIndex, Desugar, DesugarFold, ReferSugar,
  RefError, ReferInfo, Refers, Referred, Rearrange,
  procRearrange
) where

import           Control.Applicative
import           Control.Monad.Reader
import           Control.Monad.Writer
import           Control.Monad.State
import           Control.Lens

import           Data.Coerce
import           Data.Tuple (swap)
import           Data.Functor.Identity
import           Data.Functor.Compose
import           Data.Foldable
import           Data.Maybe
import           Data.Function
import           Data.Semigroup

import           Data.Set               (Set)
import           Data.Graph             (Graph, SCC)
import qualified Data.Graph as Graph
import           Data.Map               (Map, assocs)

import           Funcy.Processing.Util
import           Funcy.Processing.AST

{-----------------------------------------------------------------------------------------------------------------------------------
                                                        Reference Handling
------------------------------------------------------------------------------------------------------------------------------------}

-- TODO Load required module first -> Needs be addressed by main process

-- |Syntax indexing with bindings involved.
-- Part name should be unique in the specific syntax.
data SyntaxIndex f = SyntaxIndex {
  _partName :: String,
  _bindings :: f Binding
}
$(makeLenses ''SyntaxIndex)

type SIndexed f = Attach (SyntaxIndex f)

theBinding :: Lens' (SyntaxIndex Id) Binding
theBinding = bindings . coerced


data DesugarFold t a =
  -- |Simple fold. Any kind of unfolding/folding is strictly discouraged.
  Simple (Endo (t a))
  | Sort ([SIndexed Id a] -> t a)
  | Cyclic ([SCC (SIndexed Id a)] -> t a)
$(makePrisms ''DesugarFold)

-- |Desugar type, should be generic over type a
-- TODO This does not work as things are given only for certain case..
data Desugar t a = Desugar {
  _expandPart :: SIndexed [] a -> [SIndexed Id a],
  _foldInto :: DesugarFold t a
}
$(makeLenses ''Desugar)


class Traversable t => ReferSugar t where
  -- |Index each part
  tagPart :: t a -> t (SIndexed [] a)

  -- |Desugar process
  desugar :: t a -> Desugar t c


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
    Identity)

data BrIndex f = BrIndex {
  _iIndex :: Int,
  _sIndex :: SyntaxIndex f
}
$(makeLenses ''BrIndex)

oversIndex :: Lens
  (Attach (BrIndex f) i) (Attach (BrIndex g) j)
  (Attach (SyntaxIndex f) i) (Attach (SyntaxIndex g) j)
oversIndex = asPair . alongside sIndex id . from asPair

data InState t = InState {
  _desugaring :: forall a. Desugar t a,
  _curIndex :: BrIndex [],
  _decls :: Union (Map String) [String],
  _fdecls :: Map String (Int, String)
}
$(makeLenses ''InState)


newtype InResult f a = InResult {
  getResult :: Referred (Attach (BrIndex f) a)
}


procRearrange :: ASTProcOn ReferSugar Rearrange Referred
procRearrange = ASTProcOn {
  procLeaf = traverseOf _InRef $
    \bnd -> Compose $ do
      loc <- ask
      pure $ writer (bnd, singleton bnd [loc]),
  procBranch = mkBrProcess branchProcess
}

-- TODO Maybe error out?
branchProcess :: (ReferSugar syntax) =>
  (BranchProcess syntax Rearrange Referred) (InResult []) (InState syntax)
branchProcess = BranchProcess {
  mergeBranch = \st br -> do
    loc <- ask
    let dsf = st ^. desugaring . foldInto

    -- Topological sort
    let expand = traverseOf oversIndex $ st ^. desugaring . expandPart
    let expanded = concat $ sequenceA . fmap expand . getResult <$> br
    let formNode referred = (referred,
          referred ^. folded . attached . sIndex . theBinding,
          keyList . execWriter $ referred)
    let comp = sequenceA <$> (Graph.stronglyConnComp $ formNode <$> expanded)

    -- Conflict check
    -- Binding with > 1 declarations on same level -> Error
    itraverseOf_ ( ifolded <. filtered (isJust . preview (ix 1)) )
      (fmap tell . conflictError loc) (runUnion $ st ^. decls)

    -- Cycle check
    unless (has _Cyclic dsf) $ do
      let unpackCc = alongside (mapGetter $ attached . sIndex) (to (flip search) . mapGetter (to fold))
      itraverseOf_
        (traversed . below _CyclicSCC . to runWriter . unpackCc . swapped .> ifolded)
        (fmap tell . recursiveError loc) comp

    -- Early reference check (Simple case only)
    when (has _Simple dsf) $ do
      let getDecl = st ^. fdecls . to (flip search) . mapGetter (to toList)
      let unpackErc = alongside (attached . iIndex) (to runUnion . to assocs) . to (transposeOf _2)
      itraverseOf_
        (traversed . below _AcyclicSCC . to runWriter . unpackErc . folded .> ifolded)
        (fmap tell . (uncurry <$> earlyRefError loc getDecl)) comp

    -- Folding into a branch
    let rmDecl = (flip . foldr $ removeWithKey @Refers) (keyList $ st ^. decls)
    let comp' = censor rmDecl $ sequenceA comp
    case dsf of
      Simple tr ->
        let stripBr = view (mapGetter content) . getResult <$> br in
        pure $ censor rmDecl $ appEndo tr <$> sequenceA stripBr
      Sort folder -> do
        comp' ^. mapGetter (
          mapGetter (mapGetter oversIndex . to Graph.flattenSCC) . to concat . to folder) . to pure
      Cyclic cycFolder ->
        comp' ^. mapGetter (mapGetter (mapGetter oversIndex) . to cycFolder) . to pure
  ,
  tagBranch = (. tagPart) $ fmap $ (curIndex . sIndex %%=) . const . swap . (^. asPair)
  ,
  mkState = \br -> InState {
    _desugaring = desugar br,
    _curIndex = BrIndex 0 undefined,
    _decls = cempty,
    _fdecls = cempty
  },
  onState = \sub -> do
    dsf <- use $ desugaring . foldInto
    index <- use $ curIndex
    let pName = index ^. sIndex . partName
    let bnds = index ^. sIndex . bindings

    decls <>= foldMap singleton bnds [pName]            -- Gather declarations (using union)
    when (has _Simple dsf) $ do
      let iindex = index ^. iIndex
      fdecls <>= foldMap singleton bnds (iindex, pName) -- Gather first declarations
      curIndex . iIndex += 1

    ast <- lift $ local (// pName) sub
    pure $ InResult $ Attach index <$> ast
} where
  conflictError loc bnd =
    (: []) . Conflict bnd . map (loc //)

  earlyRefError loc getDecl refInd bnd = invfmap $ do
    (declInd, name) <- getDecl bnd
    -- Error only when reference earlier than declaration
    guard (refInd < declInd)
    pure $ EarlyRef . ReferInfo bnd (loc // name)

  recursiveError loc getRef =
    (: []) . Recursive . map ( liftA3 ReferInfo
    (^. theBinding) (^. partName . to (loc //)) (^. theBinding . to getRef) )
