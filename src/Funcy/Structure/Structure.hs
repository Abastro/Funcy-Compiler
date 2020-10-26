module Funcy.Structure.Structure where

import Control.Monad.Writer ( MonadWriter(..) )
import Control.Lens.Operators ( (^.) )

import Data.Monoid (Endo(..))

import Funcy.Base.Util
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
  tagIndex (Typed tp term) = Typed ([], tp) ([], term)

  desugar _ = Desugar {
    _expandPart = defaultExpandPart,
    _foldInto = Simple id
  }

vForceT :: Infer a Binding
vForceT = mkVar "force'"

bindTyped :: TypeBinder p
bindTyped = TypeBinder $ \r -> do
  tpName <- vForceT
  pure [(tpName, r ^. theTerm)]

instance InferType TypeUni where
  tagTPart _ (TypeUni n) = TypeUni n
  tagTPart _ (Typed tp term) = Typed
    (bindTyped, tp) (defaultBinder, term)

  combine st (TypeUni n) = pure $ stack st undefined $ TypeUni (n+1)
  combine _ (Typed inferTp _) = do
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
  | IntroBool a                   -- 0|1 (as Bool)
  | ElimBool a a a                -- if t1 then t2 else t3
  deriving (Functor, Foldable, Traversable)


instance ReferSugar BasicTerm where
  tagIndex (IntroFunc bnd tp term) = IntroFunc bnd
    ([bnd], tp) ([], term)

  tagIndex (ElimFunc fun par) = ElimFunc
    ([], fun) ([], par)

  tagIndex (IntroPair bnd dep rest) = IntroPair bnd
    ([bnd], dep) ([], rest)

  tagIndex (ElimPair side pair) = ElimPair side
    ([], pair)

  desugar _ = Desugar {
    _expandPart = defaultExpandPart,
    _foldInto = Simple id
  }


bindIntroFunc :: Binding -> TypeBinder p
bindIntroFunc bnd = TypeBinder $ \r -> do
  pure [(bnd, r ^. theTerm)]

bindIntroPair :: Binding -> TypeBinder p
bindIntroPair bnd = TypeBinder $ \r -> do
  pure [(bnd, r ^. theType)]

instance InferType BasicTerm where
  tagTPart _ (IntroFunc bnd tp term) = IntroFunc bnd
    (bindIntroFunc bnd, tp)
    (defaultBinder, term)

  tagTPart _ (ElimFunc fun par) = ElimFunc
    (defaultBinder, fun)
    (defaultBinder, par)

  tagTPart _ (IntroPair bnd dep rest) = IntroPair bnd
    (bindIntroPair bnd, dep)
    (defaultBinder, rest)

  tagTPart _ (ElimPair side pair) = ElimPair side
    (defaultBinder, pair)

  combine st (IntroFunc bnd _ tp) = do
    parTp <- sBoundOf bnd -- Specified, should not error
    pure $ stack st undefined $ FuncType bnd parTp tp

  combine st (ElimFunc funTp parTp) = do
    bnd <- mkVar "param"
    resT <- stack st undefined . Reference <$> mkVar "tres"
    let funTp' = stack st undefined $ FuncType bnd parTp resT
    tell [Constraint {inTerm = funTp, outTerm = funTp'}]
    pure resT

  combine st (IntroPair bnd depTp restTp) = do
    pure $ stack st undefined $ PairType bnd depTp restTp

  combine st (ElimPair side pairTp) = do
    bnd <- mkVar "dep"
    depT <- stack st undefined . Reference <$> mkVar "tdep"
    resT <- stack st undefined . Reference <$> mkVar "tres"
    let pairTp' = stack st undefined $ PairType bnd depT resT
    tell [Constraint {inTerm = pairTp, outTerm = pairTp'}]
    case side of
      Dep -> pure depT
      Rest -> pure resT

