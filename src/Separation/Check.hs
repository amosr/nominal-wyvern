-- Material/shape graph checks
-- This checks that the only cycles go through shapes.
{-# LANGUAGE FlexibleContexts, ConstraintKinds #-}
module Separation.Check where

import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.Writer
import qualified Data.Map.Strict as Map
import Data.List (union)
import Text.Printf
import Syntax
import PrettyPrint()
import TypeUtil
import Debug.Trace
import Typecheck.Lookup (typecheckPathSingleton)
import Typecheck.Check (typecheckExpr)

import Separation.Acyclic
import Separation.Base

checkTop :: Context -> Program -> Either String [Edge]
checkTop ctx p = do
  edges <- checkGraph ctx p
  checkTypes ctx p
  return edges

checkGraph :: Context -> Program -> Either String [Edge]
checkGraph ctx p = do
  edges <- runTG ctx p (buildGraph p)
  checkCycles edges
  return edges

checkTypes :: Context -> Program -> Either String ()
checkTypes ctx p@(Program _ e) = do
  _ <- runTG ctx p (checkExpr e)
  return ()


checkExpr :: Expr -> TGMonad ()
checkExpr e = case e of
  PathExpr _ -> return ()
  Call _ _ _ -> return ()
  New ty z defns -> do
    checkTy ty
    local (appendGamma [(z,ty)]) $ mapM_ checkDefns defns
  Let x annot e1 e2 -> do
    checkExpr e1
    xTy <- case annot of
      Just ty -> return ty
      Nothing -> local turnSubtypingOff $ typecheckExpr e1
    checkTy xTy
    local (appendGamma [(x,xTy)]) $ checkExpr e2
  TopLit -> return ()
  UndefLit -> return ()
  Assert _ t1 t2 -> do
    checkTy t1
    checkTy t2

checkDefns :: MemberDefinition -> TGMonad ()
checkDefns d = case d of
  TypeMemDefn _ ty -> checkTy ty
  ValDefn _ ty _ -> checkTy ty
  DefDefn _ args ty expr -> local (appendGamma (map argToTup args)) $ do
    mapM_ checkTy (map argType args)
    checkTy ty
    checkExpr expr
