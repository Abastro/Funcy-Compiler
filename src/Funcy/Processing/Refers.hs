{-# LANGUAGE TypeFamilies #-}

module Funcy.Processing.Refers where

import           Control.Monad.Reader
import           Control.Monad.Writer

import           Data.Functor.Identity
import           Data.Foldable

import qualified Data.Set                      as Set
import qualified Data.Graph                    as Graph
import qualified Data.Map.Strict               as MapS
import qualified Data.Map.Lazy                 as MapL

import           Funcy.Processing.AST


-- |Reference-specific branch structure
data Multiple t = Bi (Binary t) | Multi [(Binding, t)]

-- |Placeholder for chain
refChain :: Reference
refChain = Internal "Chain" []

{-----------------------------------------------------------------------------------------------------------------------------------
                                                        Reference Tracking
------------------------------------------------------------------------------------------------------------------------------------}

-- TODO Syntactic sugar handling
-- TODO Load required module first (Need elaborate module system)
-- Dot-overloading (foo.bar) - As a class constraint, resolved right away when trivial

class BlockSugar p where
  -- |Extract the Bindings involved.
  binding :: p -> [Binding]

  -- |Interpret the flag, possibly with externally given ID.
  -- Multiple one happens with cyclic references.
  interpret :: [Binding] -> p -> p

  -- |Name of certain side - for logging
  sideName :: p -> Side -> Binding


-- |Map from references - contains some logging
type Refer i = MapS.Map Binding i

removeRefs :: [Binding] -> Refer i -> Refer i
removeRefs idents = flip MapS.withoutKeys $ Set.fromList idents

type Organize
  = ReaderT [Binding]
    (WriterT (Refer [Binding])
    Identity)


{-----------------------------------------------------------------------------------------------------------------------------------
                                                        Reference Organizing
------------------------------------------------------------------------------------------------------------------------------------}

-- TODO How would I organize this properly
-- TODO Maybe accumulate declarations inward? How to error out?
procOrganize :: BlockSugar p => ASTProcess Organize Multiple Binding p a
procOrganize = ASTProcess {
  handleRef = \ref -> do
    case ref of
      InRef bnd -> ask >>= tell . MapS.singleton bnd
      _ -> pure ()
    pure ref -- Tracks head only
  ,
  handleBranch = error ""
  ,
  tagBranch = \flag branch ->
    let nameOf = sideName flag in
    case branch of
      Bi (Binary l r) -> Bi (Binary (l, nameOf LeftSide) (r, nameOf RightSide))
      Multi brs -> Multi $ listen <$> brs
  ,
  localize = \ident -> local (ident :)
}

-- |Finds unbound references and Sorts references by referential order.
-- Also converts multiple branch into binaries.
organizeRefs :: BlockSugar p => AST Multiple p -> Organize (AST Binary p)
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

