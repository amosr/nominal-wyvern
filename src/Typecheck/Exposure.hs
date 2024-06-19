-- Exposure and membership
-- Exposure, upcasting, downcasting: Figure 8, page 18
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
-- {-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Typecheck.Exposure where

import Control.Monad.Except
import Control.Monad.Extra
import Control.Monad.Reader
import Data.Maybe
import Debug.Trace
import PrettyPrint ()
import Syntax
import Text.Printf
import TypeUtil

import qualified Data.Set as Set

import qualified Typecheck.Lookup as Lookup

bounds'EQQ :: Set.Set Bound
bounds'EQQ = Set.singleton EQQ

bounds'LE :: Set.Set Bound
bounds'LE = Set.fromList [LEQ, EQQ]

bounds'GE :: Set.Set Bound
bounds'GE = Set.fromList [EQQ, GEQ]

exposure :: TC m => Type -> m Type
exposure tau@(Type base rs) = case base of
  -- Rule Exp-Top
  TopType     -> return tau
  -- Rule Exp-Bot
  BotType     -> return tau
  -- Rule Exp-Name
  NamedType _ -> return tau
  -- Rules Exp-Upper, Exp-Otherwise
  PathType p t -> do
    tau' <- exposePath1 bounds'LE rs p t
    case tau' of
      Just tau' -> exposure tau'
      Nothing -> return tau

exposePath1 :: TC m => Set.Set Bound -> [Refinement] -> Path -> Name -> m (Maybe Type)
exposePath1 checkBounds rs p t = withTrace ("exposePath1: " ++ show (rs,p,t)) $ do
  taup  <- Lookup.typecheckPathSingleton p
  taup' <- exposure taup
  -- XXX TODO avoid catch here as it might silence real errors
  catchError (do
    TypeMemDecl _ _ b taut <- Lookup.lookupTypeMemDecl t taup' p
    assert ("expose: " ++ show (b,taut)) (Set.member b checkBounds)
    return (Just (merge taut rs)))
    (\e -> return Nothing)


-- Change from paper: we encode upcast and downcast as partial functions here.
-- The paper version is a total function, but upcast is non-deterministically
-- applied. Making it partial lets the subtyping algorithm control backtracking.
upcast :: TC m => Type -> m (Maybe Type)
upcast tau@(Type base rs) = case base of
  -- Rules Uc-Upper, Uc-Otherwise(1)
  PathType p t ->
    exposePath1 bounds'LE rs p t
  -- Rule Uc-Otherwise(2)
  _ -> return Nothing

downcast :: TC m => Type -> m (Maybe Type)
downcast tau@(Type base rs) = case base of
  -- Rules Dc-Upper, Dc-Otherwise(1)
  PathType p t ->
    exposePath1 bounds'GE rs p t
  -- Rule Dc-Otherwise(2)
  _ -> return Nothing

-----------------------------
-- Avoidance

avoid :: TC m => Bound -> Binding -> Type -> m (Maybe Type)
avoid checkBounds x t = do
  fuel <- reader avoidFuel
  avoidType checkBounds x t fuel

-- `avoid` from Jonathan email discussion 2024/05/26
-- simplify type to avoid given self binding
-- TODO: parameterise by bound-set {EQQ}, {LEQ,EQQ} or {EQQ,GEQ}
avoidType :: TC m => Bound -> Binding -> Type -> Int -> m (Maybe Type)
avoidType b x (Type t r) 0 = return Nothing
avoidType b x (Type t r) fuel = withErrorContext ("avoid:" ++ show (b,x,t,r)) $ do
  t' <- avoidBase b x t fuel
  -- XXX WRONG: the returned bound b' does not reflect whether refinements are subtypes
  -- Should restrict refinement unfolding according to b' as in paper
  r' <- mapM (\r -> avoidRefinement b x r fuel) r
  return (do
    t' <- t'
    r'' <- sequence r'
    Just (merge t' r''))

avoidBase :: TC m => Bound -> Binding -> BaseType -> Int -> m (Maybe Type)
avoidBase _ x TopType _ = return $ Just (Type TopType [])
avoidBase _ x BotType _ = return $ Just (Type BotType [])
avoidBase _ x (NamedType n) _ = return $ Just (Type (NamedType n) [])
avoidBase bReq x (PathType p t) fuel
  -- XXX: need catch here? if type has no such member, is it a top-level error?
  -- implement with catch for now, as it gives a better error message
  | p == Var x = catch $ do
    taup  <- Lookup.typecheckPathSingleton p
    -- CHANGE: different from Jonathan's: perform exposure here
    taup' <- exposure taup
    TypeMemDecl _ _ b taut <- Lookup.lookupTypeMemDecl t taup' p
    t' <- avoidType bReq x taut (fuel - 1)
    return (do
      _ <- joinBound bReq b
      t')
  | otherwise
  = return $ Just (Type (PathType p t) [])
 where
  catch act = catchError act (\e -> withErrorContext ("avoid:fallback:" ++ show e) $ return Nothing)

avoidRefinement :: TC m => Bound -> Binding -> Refinement -> Int -> m (Maybe Refinement)
avoidRefinement b x (RefineDecl n br tau) fuel = do
  t' <- avoidType (productBound b br) x tau fuel
  return (do
    t' <- t'
    Just (RefineDecl n br t'))
