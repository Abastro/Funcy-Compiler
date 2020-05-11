{-# LANGUAGE MultiParamTypeClasses #-}
module Funcy.Processing.Structure where

import Control.Monad.Reader
import Control.Monad.Writer
import Control.Monad.Except

import Data.Void

import Text.Read

import Funcy.Processing.AST
import Funcy.Processing.Modules
import Funcy.Processing.Typing

data TypeFlag =
    Typed -- t2 : t1 (t2 has type t1)


mkUni :: Int -> Reference
mkUni num = Internal "UType" [show num]

tpPrefix = "force_"

type UniType = ModuleType BasicFlag Void

instance DomainedLocal TypeFlag where
    mInstance = MInstance "UType"

instance FeatureGlImpl TypingIntern TypeFlag Void where
    featureImplGl = TypingIntern typeOf where
        illegalArguments = Left ["IllegalArguments", "[number]"]
        typeOf [num] = Leaf . mkUni . (1+) <$>
            maybe illegalArguments Right (readMaybe num)
        typeOf _ = illegalArguments

instance (Context c) => FeatureElImpl (TypingWith c q) TypeFlag Void where
    featureImplEl Typed = TypingWith $
        pure $ Typing {
            bindType = \tp _ -> do
                tpName <- var tpPrefix
                pure [(tpName, tp)]
            ,
            combine = \_ tp' -> do
                tpName <- var tpPrefix
                tp <- recallS tpName
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

funcTFormer = Leaf $ Internal "TypeFunc" []
pairTFormer = Leaf $ Internal "TypePair" []

instance DomainedLocal BasicFlag where
    mInstance  = MInstance "Basics"

instance FeatureGlImpl TypingIntern BasicFlag Void where
    featureImplGl = TypingIntern $ \_ -> Left ["Unsupported"]

instance (Context c) => FeatureElImpl (TypingWith c q) BasicFlag Void where
    featureImplEl (IntroFunc param) = TypingWith $ do
        inc <- asks (. Local)
        pure $ Typing {
            bindType = \tpPar _ -> pure [(param, tpPar)]
            ,
            combine = \_ tpRet -> do
                tpPar <- recallS param
                pure $ apply inc funcTFormer $ lambda inc (param, tpPar) tpRet
        }

    featureImplEl (IntroPair dep) = TypingWith $ do
        inc <- asks (. Local)
        pure $ Typing {
            bindType = \_ tpDep -> pure [(dep, tpDep)]
            ,
            combine = \tpDep tpRest ->
                pure $ apply inc pairTFormer $ lambda inc (dep, tpDep) tpRest
        }

    featureImplEl ElimFunc = TypingWith $ do
        inc <- asks (. Local)
        pure $ Typing {
            bindType = \_ _ -> pure []
            ,
            combine = \tpf tpx -> do
                par <- var "p"
                blk <- var "r"
                let tpRet = Leaf $ InRef blk
                let tpf' = apply inc funcTFormer $ lambda inc (par, tpx) tpRet
                tell [Constraint tpf tpf']
                pure tpRet
        }

    featureImplEl (ElimPair p1 p2) = TypingWith $ do
        inc <- asks (. Local)
        pure $ Typing {
            bindType = \pair tpp -> do
                tDep <- var "a"
                tRest <- var "b"
                let tpDep = Leaf $ InRef tDep
                let tpRest = Leaf $ InRef tRest
                let tpp' = apply inc pairTFormer $ lambda inc (p1, tpDep) tpRest

                tell [Constraint tpp tpp']
                pure [(p1, tpDep), (p2, tpRest)]
            ,
            combine = \_ tpe -> pure tpe
        }