module Funcy.Base.Message where

type ErrorMsg = [String]

internal :: ErrorMsg
internal = ["InternalError"]

referError :: String -> ErrorMsg
referError content = ["ReferError", content]
