-- Exposure and membership
-- Exposure, upcasting, downcasting: Figure 8, page 18
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
-- {-# LANGUAGE LambdaCase #-}
-- {-# LANGUAGE ScopedTypeVariables #-}

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

-- `avoid` from Jonathan email discussion 2024/05/26
-- simplify type to avoid given self binding
-- TODO: parameterise by bound-set {EQQ}, {LEQ,EQQ} or {EQQ,GEQ}
avoid :: TC m => Set.Set Bound -> Binding -> Type -> m (Maybe Type)
avoid checkBounds x (Type t r) = withErrorContext ("avoid:" ++ show (x,t,r)) $ do
  t' <- avoidBase checkBounds x t
  r' <- mapM (avoidRefinement checkBounds x) r
  return (merge <$> t' <*> sequence r')

avoidBase :: TC m => Set.Set Bound -> Binding -> BaseType -> m (Maybe Type)
avoidBase _ x TopType = return $ Just $ Type TopType []
avoidBase _ x BotType = return $ Just $ Type BotType []
avoidBase _ x (NamedType n) = return $ Just $ Type (NamedType n) []
avoidBase checkBounds x (PathType p t)
  -- XXX: need catch here? if type has no such member, is it a top-level error?
  -- implement with catch for now, as it gives a better error message
  | p == Var x = catch $ do
    taup  <- Lookup.typecheckPathSingleton p
    -- CHANGE: different from Jonathan's: perform exposure here
    taup' <- exposure taup
    TypeMemDecl _ _ b taut <- Lookup.lookupTypeMemDecl t taup' p
    if Set.member b checkBounds
    then avoid checkBounds x taut
    -- then return (Just taut)
    else return Nothing
  | otherwise
  = return $ Just $ Type (PathType p t) []
 where
  catch act = catchError act (\e -> withErrorContext ("avoid:fallback:" ++ show e) $ return Nothing)

avoidRefinement :: TC m => Set.Set Bound -> Binding -> Refinement -> m (Maybe Refinement)
avoidRefinement checkBounds x (RefineDecl n b tau) = do
  t' <- avoid checkBounds x tau
  return (RefineDecl n b <$> t')
