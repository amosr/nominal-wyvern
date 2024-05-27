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
-- import Data.Kind (Type)
import Data.List (find, partition)
import Data.Maybe
import Debug.Trace
import PrettyPrint ()
import Syntax
import Text.Printf
import TypeUtil

import qualified Typecheck.Lookup as Lookup

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
    tau' <- exposePath1 (\b -> b == LEQ || b == EQQ) rs p t
    case tau' of
      Just tau' -> exposure tau'
      Nothing -> return tau

exposePath1 :: TC m => (Bound -> Bool) -> [Refinement] -> Path -> Name -> m (Maybe Type)
exposePath1 checkBounds rs p t = withTrace ("exposePath1: " ++ show (rs,p,t)) $ do
  taup  <- Lookup.typecheckPathSingleton p
  taup' <- exposure taup
  -- XXX TODO avoid catch here as it might silence real errors
  catchError (do
    TypeMemDecl _ _ b taut <- Lookup.lookupTypeMemDecl t taup' p
    assert ("expose: " ++ show (b,taut)) (checkBounds b)
    return (Just (merge taut rs)))
    (\e -> return Nothing)


-- Change from paper: we encode upcast and downcast as partial functions here.
-- The paper version is a total function, but upcast is non-deterministically
-- applied. Making it partial lets the subtyping algorithm control backtracking.
upcast :: TC m => Type -> m (Maybe Type)
upcast tau@(Type base rs) = case base of
  -- Rules Uc-Upper, Uc-Otherwise(1)
  PathType p t ->
    exposePath1 (\b -> b == LEQ || b == EQQ) rs p t
  -- Rule Uc-Otherwise(2)
  _ -> return Nothing

downcast :: TC m => Type -> m (Maybe Type)
downcast tau@(Type base rs) = case base of
  -- Rules Dc-Upper, Dc-Otherwise(1)
  PathType p t ->
    exposePath1 (\b -> b == GEQ || b == EQQ) rs p t
  -- Rule Dc-Otherwise(2)
  _ -> return Nothing

-- `avoid` from Jonathan email discussion 2024/05/26
-- simplify type to avoid given self binding
-- TODO: parameterise by bound-set {EQQ}, {LEQ,EQQ} or {EQQ,GEQ}
avoid :: TC m => Binding -> Type -> m (Maybe Type)
avoid x (Type t r) = do
  t' <- avoidBase x t
  r' <- mapM (avoidRefinement x) r
  return (merge <$> t' <*> sequence r')

avoidBase :: TC m => Binding -> BaseType -> m (Maybe Type)
avoidBase x TopType = return $ Just $ Type TopType []
avoidBase x BotType = return $ Just $ Type BotType []
avoidBase x (NamedType n) = return $ Just $ Type (NamedType n) []
avoidBase x (PathType p t)
  -- XXX: need catch here? if type has no such member, is it a top-level error?
  -- implement with catch for now, as it gives a better error message
  | p == Var x = catch $ do
    taup  <- Lookup.typecheckPathSingleton p
    TypeMemDecl _ _ b taut <- Lookup.lookupTypeMemDecl t taup p
    case b of
      EQQ -> return $ Just taut
      _   -> return Nothing
  | otherwise
  = return $ Just $ Type (PathType p t) []
 where
  catch act = catchError act (\_ -> return Nothing)

avoidRefinement :: TC m => Binding -> Refinement -> m (Maybe Refinement)
avoidRefinement x (RefineDecl n b tau) = do
  t' <- avoid x tau
  return (RefineDecl n b <$> t')
