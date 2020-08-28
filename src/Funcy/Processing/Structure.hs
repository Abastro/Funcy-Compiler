{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module Funcy.Processing.Structure where

import           Control.Monad.Reader
import           Control.Monad.Writer
import           Control.Monad.Except

import           Data.Void
import           Data.Functor

import           Text.Read

import           Funcy.Processing.AST
import           Funcy.Processing.Modules
import           Funcy.Processing.Typing
import           Funcy.Processing.Message


data TypeFlag =
  Typed -- t2 : t1 (t2 has type t1)


mkUni :: Int -> Reference
mkUni num = Internal "UType" [show num]

tpPrefix = "force_"

-- |Module for universe type
type UniType = ModuleType TypeFlag Void

instance DomainedLocal TypeFlag where
  mInstance = MInstance "UType"

instance FeatureGlImpl (TypingIntern q) TypeFlag Void where
  featureImplGl = TypingIntern $ const typeOf where
    typeOf = fmap (Leaf . mkUni) . runArg (argParser pNumber)

instance FeatureElImpl (TypingWith q) TypeFlag Void where
  featureImplEl Typed = TypingWith $ pure $ Typing
    { ckEnclose = True
    , bindType  = \tp _ -> do
                    tpName <- asks $ var tpPrefix
                    pure [(tpName, tp)]
    , combine   = \_ tp' -> do
                    tpName <- asks $ var tpPrefix
                    tp     <- ask >>= recallS tpName
                    tell [Constraint tp tp'] -- Unify type
                    pure tp -- Gives explicit type
    }


data BasicFlag =
  IntroFunc Binding           -- \x. t
  | ElimFunc                  -- t1 (t2)
  | IntroPair Binding         -- (x = t1, t2)
  | ElimPair Side             -- t.(0|1)

-- TODO 2-type and case-specific r's into (2->r)

type Basics = ModuleType BasicFlag Void

-- TODO Type is not going to be specified
lambda :: (BasicFlag -> p) -> (Binding, Term p) -> Term p -> Term p
lambda inc (x, t) y = Branch $ Binary (inc $ IntroFunc x) t y

apply :: (BasicFlag -> p) -> Term p -> Term p -> Term p
apply inc f x = Branch $ Binary (inc ElimFunc) f x

funcTFormer = Leaf $ Internal "Basics" ["TypeFunc"]
pairTFormer = Leaf $ Internal "Basics" ["TypePair"]

-- |Basic function type
fnType :: (BasicFlag -> p) -> Term p -> Term p -> Term p
fnType inc a b = apply inc funcTFormer $ lambda inc ("#unused", a) b

instance DomainedLocal BasicFlag where
  mInstance = MInstance "Basics"

instance FeatureGlImpl (TypingIntern q) BasicFlag Void where
  featureImplGl = TypingIntern $ do
    inc <- asks (. Local)
    let (>-->) = fnType inc
    let tpFormer = ( do
        na <- asks $ var "a"
        nu <- asks $ var "u"
        let a = Leaf $ InRef na
        let u = Leaf $ InRef nu
        pure $ (a >--> u) >--> u )
    pure $ check >=> const tpFormer
    where
      check = fmap (const ()) . runArg
        (argParser $ pName "TypeFunc" <|||> pName "TypePair")

instance FeatureElImpl (TypingWith q) BasicFlag Void where
  featureImplEl (IntroFunc param) = TypingWith $ do
    inc <- asks (. Local)
    pure $ Typing
      { ckEnclose = True
      , bindType  = \_ _ -> pure [(param, error "TODO: Make new")]
      , combine   = \_ tpRet -> do
        tpPar <- ask >>= recallS param
        pure $ apply inc funcTFormer $ lambda inc (param, tpPar) tpRet
      }

  featureImplEl (IntroPair dep) = TypingWith $ do
    inc <- asks (. Local)
    pure $ Typing
      {
        -- TODO May not enclose in some cases
        ckEnclose = True
      , bindType  = \_ tpDep -> pure [(dep, tpDep)]
      , combine   = \tpDep tpRest ->
        pure $ apply inc pairTFormer $ lambda inc (dep, tpDep) tpRest
      }

  featureImplEl ElimFunc = TypingWith $ do
    inc <- asks (. Local)
    pure $ Typing
      { ckEnclose = True
      , bindType  = const . const $ pure []
      , combine   = \tpf tpx -> do
        par <- asks $ var "p"
        blk <- asks $ var "r"
        let tpRet = Leaf $ InRef blk
        let tpf' = apply inc funcTFormer $ lambda inc (par, tpx) tpRet
        tell [Constraint tpf tpf']
        pure tpRet
      }

  featureImplEl (ElimPair side) = TypingWith $ do
    inc <- asks (. Local)
    pure $ Typing
      { ckEnclose = True
      , bindType  = const . const $ pure []
      , combine   = \_ tp -> do
        par <- asks $ var "x"
        tpDep  <- Leaf . InRef <$> asks (var "a")
        tpRest <- Leaf . InRef <$> asks (var "b")
        let tp' = apply inc pairTFormer $ lambda inc (par, tpDep) tpRest

        tell [Constraint tp tp']
        pure $ case side of
          LeftSide -> tpDep
          RightSide -> tpRest
      }
