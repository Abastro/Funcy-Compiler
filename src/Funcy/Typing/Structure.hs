module Funcy.Typing.Structure where

import Control.Monad.Writer ( MonadWriter(..) )
import Control.Lens.Operators ( (^.) )

import Funcy.Base.AST
import Funcy.Typing.Infers

data TypeUni a =
  TypeUni Int
  | Typed a a -- Typed t1 t2 ~ t2 : t1 (t2 has type t1)
  deriving (Functor, Foldable, Traversable)

vForceT :: Infer a Binding
vForceT = mkVar "force'"

bindTyped :: TypeBinder p
bindTyped = TypeBinder $ \r -> do
  tpName <- vForceT
  pure [(tpName, r ^. theTerm)]

instance InferType TypeUni where
  tagPart stack (TypeUni n) = TypeUni n
  tagPart stack (Typed tp term) = Typed
    (TypingIndex "#type" $ bindTyped, tp)
    (TypingIndex "#term" defaultBinder, term)

  combine stack (TypeUni n) = pure $ stack $ TypeUni (n+1)
  combine stack (Typed inferTp _) = do
    tpName <- vForceT
    specTp <- boundOf tpName
    tell [Constraint inferTp specTp]
    pure specTp -- Gives explicit type


data Side = Dep | Rest

data BasicTerm a =
  FuncType Binding a a            -- Pi (x : t1) t2
  | PairType Binding a a          -- Sigma (x : t1) t2
  | IntroFunc Binding a a         -- \x : t1. t2
  | ElimFunc a a                  -- t1 (t2)
  | IntroPair Binding a a         -- (x = t1, t2)
  | ElimPair Side a               -- t.(0|1)
  deriving (Functor, Foldable, Traversable)

-- TODO 2-type and case-specific r's into (2->r)

bindIntroFunc :: Binding -> TypeBinder p
bindIntroFunc bnd = TypeBinder $ \r -> do
  pure [(bnd, r ^. theTerm)]

bindIntroPair :: Binding -> TypeBinder p
bindIntroPair bnd = TypeBinder $ \r -> do
  pure [(bnd, r ^. theType)]

instance InferType BasicTerm where
  tagPart stack (IntroFunc bnd tp term) = IntroFunc bnd
    (TypingIndex "#tparam" $ bindIntroFunc bnd, tp)
    (TypingIndex "#ret" $ defaultBinder, term)

  tagPart stack (ElimFunc fun par) = ElimFunc
    (TypingIndex "#func" defaultBinder, fun)
    (TypingIndex "#param" defaultBinder, par)

  tagPart stack (IntroPair bnd dep rest) = IntroPair bnd
    (TypingIndex "#dep" $ bindIntroPair bnd, dep)
    (TypingIndex "#rest" defaultBinder, rest)

  tagPart stack (ElimPair side pair) = ElimPair side
    (TypingIndex "#pair" defaultBinder, pair)

  combine stack (IntroFunc bnd _ tp) = do
    parTp <- boundOf bnd -- No good way to infer the parameter type. How would I impl this?
    pure $ stack $ FuncType bnd parTp tp

  combine stack (ElimFunc funTp parTp) = do
    bnd <- mkVar "param"
    resT <- stack . Reference <$> mkVar "tres"
    let funTp' = stack $ FuncType bnd parTp resT
    tell [Constraint funTp funTp']
    pure resT

  combine stack (IntroPair bnd depTp restTp) = do
    pure $ stack $ PairType bnd depTp restTp

  combine stack (ElimPair side pairTp) = do
    bnd <- mkVar "dep"
    depT <- stack . Reference <$> mkVar "tdep"
    resT <- stack . Reference <$> mkVar "tres"
    let pairTp' = stack $ PairType bnd depT resT
    tell [Constraint pairTp pairTp']
    case side of
      Dep -> pure depT
      Rest -> pure resT

