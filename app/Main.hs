{-# LANGUAGE DeriveDataTypeable #-}
{-# OPTIONS_GHC -fno-cse #-}

module Main where

import           Binding                (bind)
import           Parser                 (parseFile)
import           PrettyPrint            ()
import           System.Console.CmdArgs
import           System.Environment
import           System.IO
import           TypeGraph              (checkCycles, getGraph)
import           Typecheck              (typecheck)

import qualified TypeUtil as TypeUtil

data Args = Args
  { input      :: FilePath
  , debug_flag :: Bool
  , repl_mode  :: Bool
  , expansion  :: Bool
  }
  deriving (Show, Data, Typeable)

wyv_args =
  Args { input      = def &= typFile &= argPos 0
       , debug_flag = def &= name "d" &= help "Enable debug tracing"
       , repl_mode  = def &= name "r"
       , expansion  = def &= name "e" &= help "Enable expansion extension"
       }
    &= help ""
    &= program "wyvern typechecker"

main = do
  arg <- cmdArgs wyv_args
  let infile   = input arg
  let is_repl  = repl_mode arg

  prelude <- readFile "lib/Prelude.wyv"
  input   <- readFile infile

  if is_repl then return () else runFile arg (prelude ++ input)

runFile :: Args -> String -> IO ()
runFile arg input = do
  let raw_ast = case parseFile input of
        Left  err -> error (show err)
        Right x   -> x
  --putStrLn $ "Raw AST:\n" ++ show raw_ast
  let bound_ast = getRight "bind" $ bind raw_ast
  putStrLn $ "Bound AST:\n" ++ show bound_ast

  let type_graph = getRight "type-graph construction" $ getGraph bound_ast
  putStrLn "Type graph:" >> mapM_ (putStrLn . show) type_graph
  let nocycles = getRight "material/shape separation" $ checkCycles type_graph
  nocycles `seq` putStrLn $ "Type graph looks good"
  let ty = getRight "typechecking" $ typecheck bound_ast (tcContextOfArgs arg)
  putStrLn $ "Type: " ++ (show ty)

getRight :: String -> Either String b -> b
getRight stage e = case e of
  Left  err -> error ("\n  *** error during " ++ stage ++ " ***\n" ++ err)
  Right x   -> x

tcContextOfArgs arg =
  TypeUtil.emptyCtx {
    TypeUtil.extensions = TypeUtil.Extensions {
      TypeUtil.doExpansion = expansion arg,
      TypeUtil.doTrace = debug_flag arg
    }
  }