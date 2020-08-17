module Funcy.Processing.Message where

import Control.Monad.Except
import Control.Monad.State
import Control.Monad.Identity

import Text.ParserCombinators.ReadP hiding (get)

import Data.List


type ErrorMsg = [String]


internal :: ErrorMsg
internal = ["InternalError"]

illegalArg :: Int -> String -> ErrorMsg
illegalArg index format = ["IllegalArg", show index, format]


-- Simple parser

data Format =
  FName String |
  FNumber |
  FChoice [Format]

instance Show Format where
  show (FName x) = x
  show FNumber = "{number}"
  show (FChoice f) = concat . intersperse "|" $ fmap show f

type Parser a = (ReadP a, Format)

parseWith :: Monad m => Parser a -> String -> ExceptT String m a
parseWith (parser, format) content =
  case readP_to_S parser content of
    ((x, "") : _) -> pure x
    _ -> throwError $ show format


pName :: String -> Parser String
pName x = (string x, FName x)

pNumber :: Parser Int
pNumber = (readS_to_P reads, FNumber)

pChoice :: [Parser a] -> Parser a
pChoice parsers = (choice $ map fst parsers, FChoice $ map snd parsers)

(<|||>) :: Parser a -> Parser a -> Parser a
a <|||> b = pChoice [a, b]

-- Parse arguments

type PArg m a = StateT (Int, [String]) m a

argParser :: Monad m => Parser a -> PArg (ExceptT [String] m) a
argParser parser = do
  (index, args) <- get
  case args of
    (c:cs) -> do
      put (index + 1, cs)
      lift . withExceptT (illegalArg index) $ parseWith parser c
    [] -> throwError $ illegalArg index "Missing"

runArg :: Monad m => PArg (ExceptT [String] m) a -> [String] -> ExceptT ErrorMsg m a
runArg parg content = do
  (x, (index, args)) <- runStateT parg (0, content)
  if null args then pure ()
  else throwError $ illegalArg index "Unexpected"
  pure x
