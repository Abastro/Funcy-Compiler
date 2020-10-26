{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TemplateHaskell #-}

{-------------------------------------------------------------------
                        Reference Tracking
--------------------------------------------------------------------}

module Funcy.Reference.Refers (
  SIndex, SIndexed,
  DesugarFold(..), _Refers, _Simple, _Sort, _Cyclic,
  Desugar(..), expandPart, foldInto, defaultExpandPart,
  RefError(..), ReferInfo(..), Refers, Referred,
  Rearrange, intProcRearr
) where

import Control.Monad ( (>=>) )
import Control.Monad.Trans ( MonadTrans(..) )
import Control.Monad.Writer ( WriterT, MonadWriter(..) )
import qualified Control.Monad.Writer as Writer

import Control.Lens.TH ( makePrisms, makeLenses )
import Control.Lens.Type ( Lens' )
import Control.Lens.Operators
    ( (<.), (^.), (<>=) )
import qualified Control.Lens.Combinators as Lens

import Data.Coerce ( coerce )
import Data.Foldable ( Foldable(..) )
import Data.Maybe ( isJust )

import Data.Map ( Map )
import Data.Graph ( SCC )
import qualified Data.Graph as Graph

import Funcy.Base.Report
import Funcy.Base.Util
import Funcy.Base.AST

-- TODO Load required module first -> Needs be addressed by main process


-- |Syntax indexing with bindings involved.
type SIndex f = f Binding
type SIndexed f = (,) (SIndex f)

data DesugarFold t a =
  -- |Reference (Leaf). Never branch.
  Refers (Binding)
  -- |Simple fold. Any kind of unfolding/folding is strictly discouraged.
  | Simple (t a -> t a)
  -- |Sorting fold without cyclic references
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
defaultExpandPart (bs, a) = (, a) . coerce <$> bs


type Refers = Union (Map Binding)
type Referred = WriterT (Refers [Loc]) Id

data InState t = InState {
  _location :: Loc,
  _desugaring :: Desugar t,
  -- |Gathered declarations
  _decls :: Refers [Loc]
}
$(makeLenses ''InState)


data RefError =
  -- |Conflicts among same level declarations
  Conflict Binding [Loc]
  -- |Illegal recursive references
  | Recursive [ReferInfo]

data ReferInfo = ReferInfo Binding Loc [Loc]

type Rearrange = ReportT RefError (
  WriterT (Refers [Loc]) Id)


theBinding :: Lens' (SIndex Id) Binding
theBinding = Lens.coerced


intProcRearr :: (Traversable syntax) =>
  (a -> Loc) -> Indexing (SIndex []) syntax -> Specific Desugar syntax ->
    ASTProcIn syntax Rearrange Loc Loc a a
intProcRearr getLoc tagging desugar subProc =
  indexHover (indexIso tagging) $
    stateHover (\l -> do
      ds <- Lens.use $ Lens.to (getSpecific desugar)
      return InState {
        _location = l,
        _desugaring = ds,
        _decls = cempty
      })
    >=> stTravHover (\(bnds, br) -> do
      dsf <- Lens.use $ desugaring . foldInto
      rmEarlyDecl <- if Lens.has _Simple dsf then rmDecl else return id
      decls <>= foldMap singleton bnds [getLoc br]
      br' <- lift . listen . Writer.censor rmEarlyDecl $ subProc br -- Subprocess
      pure (bnds, br')
    ) >=> stateInvHover (\br -> fmap placeIndex . pass $ do
      dsf <- Lens.use $ desugaring . foldInto
      case dsf of
        Refers bnd -> do
          loc <- Lens.use location
          tell $ singleton bnd [loc]  -- Writes reference.
          return (stripIndex br, id)
        Simple tr -> do
          checkConflict
          return (tr $ stripIndex br, id)
        Sort folder -> do
          checkConflict
          exBr <- expandSort br
          checkCycle exBr             -- Sort does not allow recursive reference.
          rmDecl >>= return . (folder $ foldMap Graph.flattenSCC $ stripExRef exBr,)
        Cyclic cycFolder -> do
          checkConflict
          exBr <- expandSort br
          rmDecl >>= return . (cycFolder $ stripExRef exBr,)
    ) >=> stateHover (return . Lens.view location)
  where
    -- |Remove declarations
    rmDecl = do
      decl <- Lens.use $ decls . Lens.to keyList
      return $ flip (foldr removeWithKey) decl

    stripIndex = fmap $ fst . snd   -- Strips index
    stripExRef = fmap . fmap $ fst  -- Strips reference
    placeIndex = fmap $ ([],)       -- Placeholder index

    -- |Topological sort with bindings separation
    expandSort br = do
      exPart <- Lens.use $ desugaring . expandPart 
      let formNode (index, (node, refs)) = (((index, node), refs),
            index ^. theBinding, keyList @Refers refs)
      return $ Graph.stronglyConnComp . map formNode $ foldMap exPart br

    -- |Conflict check, Binding with > 1 declarations = Error.
    checkConflict = do
      decl <- Lens.use decls
      Lens.itraverseOf_ (Lens.ifolded <. Lens.filtered (isJust . Lens.preview (Lens.ix 1)))
        (fmap reportError . Conflict) (runUnion decl)

    -- |Cycle check, cycles are reported as error.
    checkCycle exBr = do
      Lens.traverseOf_ (Lens.traversed . _CyclicSCC)
        (reportError . Recursive . fmap refInfo) exBr where
      refInfo ((bnd', node), refs) = let bnd = coerce bnd'
        in ReferInfo bnd (getLoc node) (fold $ search @Refers bnd refs)
