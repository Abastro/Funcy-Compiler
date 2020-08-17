module Funcy.Processing.Message where

type ProcError = Either [String]

illegalArg :: String -> ProcError a
illegalArg format = Left ["IllegalArg", format]


