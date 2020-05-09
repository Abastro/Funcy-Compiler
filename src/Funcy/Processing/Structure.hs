module Funcy.Processing.Structure where

import Control.Monad.Reader
import Control.Monad.Writer
import Control.Monad.Except

import Funcy.Processing.AST
import Funcy.Processing.Typing


data TypeFlag =
    Typed -- t2 : t1 (t2 has type t1)


mkUni :: Int -> Reference
mkUni num = Internal "TypeUni" [show num]

tpPrefix = "force_"

instance Typer TypeFlag where
    internalType "TypeUni" [num] = Leaf $ mkUni $ read num + 1

    typing Typed = Typing {
        inferLeft = \tp -> do
            tpName <- asks $ var tpPrefix
            hightp <- inferFor "#type" tp
            pure $ writer (hightp, [(tpName, tp)])
        ,
        inferRight = inferFor "#term"
        ,
        combine = \ht tp -> do
            tpName <- asks $ var tpPrefix
            tp' <- recallS tpName
            tell [Constraint ht tp tp']
            pure tp' -- Uses explicit type
    }


data BasicFlag =
    IntroFunc Binding           -- \x : t1. t2
    | ElimFunc                  -- t1 t2
    | IntroPair Binding         -- (x = t1, t2)
    | ElimPair Binding Binding  -- (p, q) = t1 in t2

-- TODO 2-type and case-specific r's into (2->r)

lambda :: (Binding, Term BasicFlag) -> Term BasicFlag -> Term BasicFlag
lambda (x, t) y = Branch (IntroFunc x) $ Binary t y

apply :: Term BasicFlag -> Term BasicFlag -> Term BasicFlag
apply f x = Branch ElimFunc $ Binary f x

funcTFormer = Leaf $ Internal "TypeFunc" []
pairTFormer = Leaf $ Internal "TypePair" []

instance Typer BasicFlag where
    internalType = error "Not supported"

    typing (IntroFunc param) = Typing {
        inferLeft = \tpPar -> do
            hightp <- inferFor param tpPar
            pure $ writer (hightp, [(param, tpPar)])
        ,
        inferRight = inferFor "#return"
        ,
        combine = \_ tpRet -> do
            tpPar <- recallS param
            pure $ apply funcTFormer $ lambda (param, tpPar) tpRet
    }

    typing (IntroPair dep) = Typing {
        inferLeft = \termDep -> do
            tpDep <- inferFor dep termDep
            pure $ writer (tpDep, [(dep, tpDep)])
        ,
        inferRight = inferFor "#rest"
        ,
        combine = \tpDep tpRest ->
            pure $ apply pairTFormer $ lambda (dep, tpDep) tpRest
    }

    typing ElimFunc = Typing {
        inferLeft = fmap pure . inferFor "#func"
        ,
        inferRight = inferFor "#param"
        ,
        combine = \tpf tpx -> do
            ht <- inferFor "#high" tpf
            par <- asks $ var "p"
            blk <- asks $ var "r"
            let tpRet = Leaf $ InRef blk
            let tpf' = apply funcTFormer $ lambda (par, tpx) tpRet
            tell [Constraint ht tpf tpf']
            pure tpRet
    }

    typing (ElimPair p1 p2) = Typing {
        inferLeft = \pair -> do
            tDep <- asks $ var "a"
            tRest <- asks $ var "b" -- refers local variables whose type is known obviously
            let tpDep = Leaf $ InRef tDep
            let tpRest = Leaf $ InRef tRest

            tpp <- inferFor "#pair" pair
            let tpp' = apply pairTFormer $ lambda (p1, tpDep) tpRest

            ht <- inferFor "#high" tpp
            tell [Constraint ht tpp tpp']
            pure $ writer (pair, [(p1, tpDep), (p2, tpRest), (tDep, ht), (tRest, ht)])
        ,
        inferRight = inferFor "#expr"
        ,
        combine = \_ tpe -> pure tpe
    }