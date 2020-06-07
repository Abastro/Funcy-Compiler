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

data TypeFlag =
  Typed -- t2 : t1 (t2 has type t1)


mkUni :: Int -> Reference
mkUni num = Internal "UType" [show num]

tpPrefix = "force_"

type UniType = ModuleType BasicFlag Void

instance DomainedLocal TypeFlag where
  mInstance = MInstance "UType"

instance FeatureGlImpl (TypingIntern q) TypeFlag Void where
  featureImplGl = TypingIntern $ const typeOf   where
    illegalArguments = Left ["IllegalArguments", "[number]"]
    typeOf [num] =
      pure . Leaf . mkUni . (1 +) <$> maybe illegalArguments Right (readMaybe num)
    typeOf _ = illegalArguments

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
    IntroFunc Binding           -- \x : t1. t2
    | ElimFunc                  -- t1 t2
    | IntroPair Binding         -- (x = t1, t2)
    | ElimPair Binding Binding  -- (p, q) = t1 in t2

-- TODO 2-type and case-specific r's into (2->r)

type Basics = ModuleType BasicFlag Void

lambda :: (BasicFlag -> p) -> (Binding, Term p) -> Term p -> Term p
lambda inc (x, t) y = Branch (inc $ IntroFunc x) $ Binary t y

apply :: (BasicFlag -> p) -> Term p -> Term p -> Term p
apply inc f x = Branch (inc ElimFunc) $ Binary f x

funcTFormer = Leaf $ Internal "Basics" ["TypeFunc"]
pairTFormer = Leaf $ Internal "Basics" ["TypePair"]

-- Basic function type
fnType :: (BasicFlag -> p) -> Term p -> Term p -> Term p
fnType inc a b = apply inc funcTFormer $ lambda inc ("#unused", a) b

instance DomainedLocal BasicFlag where
  mInstance = MInstance "Basics"

instance FeatureGlImpl (TypingIntern q) BasicFlag Void where
  featureImplGl = TypingIntern $ do
    inc <- asks (. Local)
    let (>==>) a b = fnType inc a b
    let tpFormer = ( do
        na <- asks $ var "a"
        nu <- asks $ var "u"
        let a = Leaf $ InRef na
        let u = Leaf $ InRef nu -- TODO a should be lower than uni type u, constraint
        pure $ (a >==> u) >==> u )
    pure $ (fmap . fmap) (const tpFormer) typeOf
    where
      fitsIn x = x == "TypeFunc" || x == "TypePair"
      typeOf [x] | fitsIn x = Right ()
      typeOf _              = Left ["IllegalArguments", "TypeFunc|TypePair"]

instance FeatureElImpl (TypingWith q) BasicFlag Void where
  featureImplEl (IntroFunc param) = TypingWith $ do
    inc <- asks (. Local)
    pure $ Typing
      { ckEnclose = True
      , bindType  = \tpPar _ -> pure [(param, tpPar)]
      , combine   = \_ tpRet -> do
                      tpPar <- ask >>= recallS param
                      pure $ apply inc funcTFormer $ lambda inc
                                                            (param, tpPar)
                                                            tpRet
      }

  featureImplEl (IntroPair dep) = TypingWith $ do
    inc <- asks (. Local)
    pure $ Typing
      {
        -- May not enclose in some cases
        ckEnclose = True
      , bindType  = \_ tpDep -> pure [(dep, tpDep)]
      , combine   = \tpDep tpRest ->
        pure $ apply inc pairTFormer $ lambda inc (dep, tpDep) tpRest
      }

  featureImplEl ElimFunc = TypingWith $ do
    inc <- asks (. Local)
    pure $ Typing
      { ckEnclose = True
      , bindType  = \_ _ -> pure []
      , combine   = \tpf tpx -> do
        par <- asks $ var "p"
        blk <- asks $ var "r"
        let tpRet = Leaf $ InRef blk
        let tpf' = apply inc funcTFormer $ lambda inc (par, tpx) tpRet
        tell [Constraint tpf tpf']
        pure tpRet
      }

  featureImplEl (ElimPair p1 p2) = TypingWith $ do
    inc <- asks (. Local)
    pure $ Typing
      { ckEnclose = True
      , bindType  = \pair tpp -> do
        tDep  <- asks $ var "a"
        tRest <- asks $ var "b"
        let tpDep  = Leaf $ InRef tDep
        let tpRest = Leaf $ InRef tRest
        let tpp' = apply inc pairTFormer $ lambda inc (p1, tpDep) tpRest

        tell [Constraint tpp tpp']
        pure [(p1, tpDep), (p2, tpRest)]
      , combine   = \_ tpe -> pure tpe
      }
