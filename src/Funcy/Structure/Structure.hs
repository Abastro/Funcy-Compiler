module Funcy.Structure.Structure where

import Control.Monad.Writer ( MonadWriter(..) )
import Control.Lens.Operators ( (^.) )

import Data.Monoid (Endo(..))

import Funcy.Base.AST
import Funcy.Reference.Refers
import Funcy.Reference.Process
import Funcy.Typing.Infers
import Funcy.Typing.Process

data TypeUni a =
  TypeUni Int
  | Typed a a -- Typed t1 t2 ~ t2 : t1 (t2 has type t1)
  deriving (Functor, Foldable, Traversable)

instance ReferSugar TypeUni where
  tagIndex (TypeUni n) = TypeUni n
  tagIndex (Typed tp term) = Typed
    (SyntaxIndex "#type" [], tp)
    (SyntaxIndex "#term" [], term)

  desugar _ = Desugar {
    _expandPart = defaultExpandPart,
    _foldInto = Simple $ Endo id
  }

vForceT :: Infer a Binding
vForceT = mkVar "force'"

bindTyped :: TypeBinder p
bindTyped = TypeBinder $ \r -> do
  tpName <- vForceT
  pure [(tpName, r ^. theTerm)]

instance InferType TypeUni where
  tagTPart st (TypeUni n) = TypeUni n
  tagTPart st (Typed tp term) = Typed
    (TypingIndex "#type" $ bindTyped, tp)
    (TypingIndex "#term" defaultBinder, term)

  combine st (TypeUni n) = pure $ stack st $ TypeUni (n+1)
  combine st (Typed inferTp _) = do
    tpName <- vForceT
    specTp <- sBoundOf tpName -- Specified, should not error
    tell [Constraint {inTerm = inferTp, outTerm = specTp}]
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

instance ReferSugar BasicTerm where
  tagIndex (IntroFunc bnd tp term) = IntroFunc bnd
    (SyntaxIndex "#tparam" [bnd], tp)
    (SyntaxIndex "#ret" [], term)

  tagIndex (ElimFunc fun par) = ElimFunc
    (SyntaxIndex "#func" [], fun)
    (SyntaxIndex "#param" [], par)

  tagIndex (IntroPair bnd dep rest) = IntroPair bnd
    (SyntaxIndex "#dep" [bnd], dep)
    (SyntaxIndex "#rest" [], rest)

  tagIndex (ElimPair side pair) = ElimPair side
    (SyntaxIndex "#pair" [], pair)

  desugar _ = Desugar {
    _expandPart = defaultExpandPart,
    _foldInto = Simple $ Endo id
  }


bindIntroFunc :: Binding -> TypeBinder p
bindIntroFunc bnd = TypeBinder $ \r -> do
  pure [(bnd, r ^. theTerm)]

bindIntroPair :: Binding -> TypeBinder p
bindIntroPair bnd = TypeBinder $ \r -> do
  pure [(bnd, r ^. theType)]

instance InferType BasicTerm where
  tagTPart st (IntroFunc bnd tp term) = IntroFunc bnd
    (TypingIndex "#tparam" $ bindIntroFunc bnd, tp)
    (TypingIndex "#ret" $ defaultBinder, term)

  tagTPart st (ElimFunc fun par) = ElimFunc
    (TypingIndex "#func" defaultBinder, fun)
    (TypingIndex "#param" defaultBinder, par)

  tagTPart st (IntroPair bnd dep rest) = IntroPair bnd
    (TypingIndex "#dep" $ bindIntroPair bnd, dep)
    (TypingIndex "#rest" defaultBinder, rest)

  tagTPart st (ElimPair side pair) = ElimPair side
    (TypingIndex "#pair" defaultBinder, pair)

  combine st (IntroFunc bnd _ tp) = do
    parTp <- sBoundOf bnd -- Specified, should not error
    pure $ stack st $ FuncType bnd parTp tp

  combine st (ElimFunc funTp parTp) = do
    bnd <- mkVar "param"
    resT <- stack st . Reference <$> mkVar "tres"
    let funTp' = stack st $ FuncType bnd parTp resT
    tell [Constraint {inTerm = funTp, outTerm = funTp'}]
    pure resT

  combine st (IntroPair bnd depTp restTp) = do
    pure $ stack st $ PairType bnd depTp restTp

  combine st (ElimPair side pairTp) = do
    bnd <- mkVar "dep"
    depT <- stack st . Reference <$> mkVar "tdep"
    resT <- stack st . Reference <$> mkVar "tres"
    let pairTp' = stack st $ PairType bnd depT resT
    tell [Constraint {inTerm = pairTp, outTerm = pairTp'}]
    case side of
      Dep -> pure depT
      Rest -> pure resT

