{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TemplateHaskell #-}
module Funcy.Processing.Refers (
  SyntaxIndex, SIndexed, CycIndexed, Desugar, DesugarFold, SyntaxSugar,
  RefError, ReferInfo, Refers, procRearrange
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
import qualified Data.Set as Set
import           Data.Graph             (Graph, SCC)
import qualified Data.Graph as Graph
import           Data.Map               (Map)
import qualified Data.Map as Map        (keys, singleton, lookup)

import           Funcy.Processing.Util
import           Funcy.Processing.AST

{-----------------------------------------------------------------------------------------------------------------------------------
                                                        Reference Handling
------------------------------------------------------------------------------------------------------------------------------------}

-- TODO How to sort?
-- TODO Syntactic sugar handling
-- TODO Load required module first (Need elaborate module system)
-- Dot-overloading (foo.bar) - As a class constraint, resolved right away when trivial

-- |Syntax indexing with bindings involved
data SyntaxIndex f = SyntaxIndex {
  _partName :: String,
  _bindings :: f Binding
}
$(makeLenses ''SyntaxIndex)

type Id = Identity
type SIndexed f = (,) (SyntaxIndex f)
type CycIndexed = (,) [SyntaxIndex Id]

data DesugarFold t a =
  Simple (Endo (t a))
  | Sort ([SIndexed Id a] -> t a)
  | Cyclic ([SCC (SIndexed Id a)] -> t a)
$(makePrisms ''DesugarFold)

-- |Desugar type, should be generic over type a
data Desugar t a = Desugar {
  expandPart :: SIndexed [] a -> [SIndexed Id a],
  _foldInto :: DesugarFold t a
}
$(makeLenses ''Desugar)


class Traversable t => SyntaxSugar t where
  -- |Index each part
  tagPart :: t a -> t (SIndexed [] a)

  -- |Desugar process
  desugar :: t a -> Desugar t c


synIndex :: Lens' (SIndexed f a) (SyntaxIndex f)
synIndex = _1

theBinding :: Lens' (SyntaxIndex Id) Binding
theBinding = bindings . coerced

data RefError =
  Conflict Binding [Location]                   -- Conflicts among same level declarations
  | EarlyRef ReferInfo                          -- Illegal early references
  | Recursive [ReferInfo]                       -- Illegal recursive references
data ReferInfo = ReferInfo Binding Location [Location]

type Refers = Union (Map Binding)


type Rearrange
  = ReaderT Location
    (WriterT [RefError]
    Identity)

type Referred = Writer (Refers [Location])


-- TODO Maybe error out?

procRearrange :: SyntaxSugar t => ASTProcess Rearrange Referred t (SyntaxIndex [])
procRearrange = ASTProcess {
  handleRef = fmap getCompose . traverseOf _InRef $
    \bnd -> Compose $ do
      loc <- ask
      pure $ writer (bnd, Union $ Map.singleton bnd [loc])
  ,
  mergeBranch = let
    report (SyntaxIndex name bnds) =
      foldMap (fmap Union . Map.singleton) bnds [name]

    conflictError loc bnd =
      Conflict bnd . map (: loc)
    recursiveError loc getRef =
      Recursive . map ( liftA3 ReferInfo
      (view theBinding) ((: loc) . view partName) (getRef . view theBinding) )
    in \st br -> do
      loc <- ask

      -- AST along with gathered occurring references
      let tagAST = sequenceA <$> tagPart br

      -- Gathered declarations
      let decls = runUnion $ foldMapOf (folded . folded . synIndex) report $ tagAST

      -- Conflict check
      -- Binding with > 1 declarations on same level -> Error
      itraverseOf_ ( ifolded <. filtered (isJust . preview (ix 1)) )
        (fmap tell . fmap (: []) . conflictError loc) decls

      -- Topological sort
      let expanded = concat $ traverse (expandPart $ desugar br) <$> tagAST
      let formNode referred = (referred,
            view (folded . synIndex . theBinding) referred,
            Map.keys . runUnion . execWriter $ referred)
      let comp = sequenceA <$> (Graph.stronglyConnComp $ formNode <$> expanded)

      -- Cycle check
      let allowCycle = has (foldInto . _Cyclic) $ desugar br
      let unpack = alongside (mapGetter synIndex) (to (flip search) . to (fmap fold))
      unless allowCycle $ itraverseOf_
        (folded . below _CyclicSCC . to runWriter . unpack . swapped .> ifolded)
        (fmap tell . fmap (: []) . recursiveError loc) comp

      -- TODO early references check for simple case

      -- Folding into a branch
      let rmDecl = (flip . foldr $ removeWithKey @Refers) (Map.keys decls)
      let comp' = censor rmDecl $ sequenceA comp
      case view foldInto $ desugar br of
        Simple tr ->
          pure $ censor rmDecl $ appEndo tr <$> sequenceA br
        Sort folder ->
          pure $ folder <$> concat . fmap Graph.flattenSCC <$> comp'
        Cyclic cycFolder -> do
          -- TODO Better way to handle cycles
          pure $ cycFolder <$> comp'

  ,
  tagBranch = fmap (state . const . swap) . tagPart
  ,
  mkState = const undefined -- Never used
  ,
  onState = \sub -> do
    pName <- use partName
    lift $ local (pName :) sub
}


-- |Finds unbound references and Sorts references by referential order.
-- Also converts multiple branch into binaries.
{-
organizeRefs :: BlockSugar p => AST Multiple p -> Organize (AST (Binary p))
organizeRefs (Leaf ref)                 = do
  case ref of
    InRef bnd -> ask >>= tell . MapS.singleton bnd
    _ -> pure ()
  pure $ Leaf ref -- Tracks head only

organizeRefs (Branch flag (Bi br))      = pass $ do
  br' <- traverse subCall $ tag br -- Traverse over the branch, tracking references
  pure
    ( Branch (interpret [] flag) br', -- (Re-)attach flag
      removeRefs $ binding flag) -- Remove references to current binding
  where
    subCall (side, br) = local (sideName flag side :) $ organizeRefs br
    tag (Binary l r) = Binary (LeftSide, l) (RightSide, r)

organizeRefs (Branch flag (Multi brs))  = pass $ do
  brs' <- traverse subCall brs                      -- Traverse over the branch, tracking references
  let sorted = Graph.stronglyConnComp brs'
  brs'' <- traverse foldComp sorted                 -- Traverse over components, folding it into individual branch
  pure ( foldl' step initial brs'', removeRefs $ fmap fst brs ) -- Accumulate/Remove references to current binding
  where
    subCall (ident, br) = do
      br' <- listen $ local (ident :) $ organizeRefs br -- Call with updated location
      pure ((ident, fst br'), ident, MapS.keys $ snd br')

    foldComp (Graph.AcyclicSCC br) = pure $ singular br
    foldComp (Graph.CyclicSCC brs) =
      pure ( fmap fst brs, foldl' step initial $ fmap singular brs ) -- Accumulates cyclic references separately

    initial = Leaf refChain
    step other (idents, cont) = Branch (interpret idents flag) $ Binary cont other
    singular (ident, t) = ([ident], t)
-}
