module Funcy.Processing.TypeSystem where

import Control.Monad.Reader
import Control.Monad.Writer
import Control.Monad.Except

import Funcy.Processing.AST
import Funcy.Processing.Typing

data TypeFlag = Typed -- t2 : t1 (t2 has type t1)

mkUni :: Int -> Reference
mkUni num = Internal ["TypeUni", show num]

tpPrefix = "force_"

instance Typer TypeFlag where
    internal ["TypeUni", num] = Leaf $ mkUni $ read num + 1

    inferLeft Typed tp = do
        tpName <- asks $ var tpPrefix
        hightp <- inferFor "#type" tp
        pure $ writer (hightp, [(tpName, tp)])

    inferRight Typed = inferFor "#term"

    combine Typed ht tp = do
        tpName <- asks $ var tpPrefix
        tp' <- recallS tpName
        tell [Constraint ht tp tp']
        pure tp' -- Uses explicit type