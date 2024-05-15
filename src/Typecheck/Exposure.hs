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
  PathType p@(Var b) t ->
    exposePath1 (\b -> b == LEQ || b == EQQ) rs b t

  PathType p t ->
    throwError "exposure: multi-length paths not supported"

exposePath1 :: TC m => (Bound -> Bool) -> [Refinement] -> Binding -> Name -> m Type
exposePath1 checkBounds rs b t = do
  taup  <- Lookup.typecheckPathSingleton (Var b)
  taup' <- exposure taup
  -- XXX TODO avoid catch here as it might silence real errors
  catchError (do
    TypeMemDecl _ _ b taut <- Lookup.lookupTypeMemDecl t taup' b
    assert "" (checkBounds b)
    tau' <- exposure taut
    return (merge tau' rs))
    (\e -> return (Type (PathType (Var b) t) rs))


upcast :: TC m => Type -> m Type
upcast tau@(Type base rs) = case base of
  -- Rules Uc-Upper, Uc-Otherwise(1)
  PathType p@(Var b) t ->
    exposePath1 (\b -> b == LEQ || b == EQQ) rs b t
  -- Rule Uc-Otherwise(2)
  _ -> return tau

downcast :: TC m => Type -> m Type
downcast tau@(Type base rs) = case base of
  -- Rules Dc-Upper, Dc-Otherwise(1)
  PathType p@(Var b) t ->
    exposePath1 (\b -> b == GEQ || b == EQQ) rs b t
  -- Rule Dc-Otherwise(2)
  _ -> return tau


-- unfold :: TC m => Type -> m (Binding, [MemberDeclaration])
-- unfold t0 = do
--   t1 <- typeExpand t0
--   normaliseMembers t1

-- typeExpand :: TC m => Type -> m Type
-- typeExpand tau@(Type base rs) = case base of
--   PathType p t -> withErrorContext (printf "in type expand (path %s)" (show tau)) $ do
--     tau_p <- typecheckPath p
--     (z, decls) <- unfold tau_p
--     TypeMemDecl _ _ bound ty <- Lookup.lookupTypeMemDecl t tau_p
--     case bound of
--       GEQ -> return tau
--       _ -> typeExpand (subst p z (merge ty rs))
--   _ -> return tau

-- typeExpand :: TC m => Type -> m Type
-- typeExpand tau@(Type base rs) = case base of
--   PathType p t -> withErrorContext (printf "in type expand (path %s)" (show tau)) $ do
--     tau_p <- typecheckPath p
--     (z, decls) <- unfold tau_p
--     TypeMemDecl _ _ bound ty <- Lookup.lookupTypeMemDecl t tau_p
--     case bound of
--       GEQ -> return tau
--       _ -> typeExpand (subst p z (merge ty rs))
--   _ -> return tau


-- -- Figure 7, type-member lookup
-- lookupMemberDecls :: TC m => (MemberDeclaration -> Bool) -> Type -> Binding -> m MemberDeclaration
-- lookupMemberDecls pred ty self =
--   let _

-- lookupRefinements :: TC m => (MemberDeclaration -> Bool) -> [Refinement] -> m (Maybe MemberDeclaration)
-- lookupRefinements pred ty self =

-- refinementOfMemberDeclaration :: Refinement -> MemberDeclaration
-- refinementOfMemberDeclaration (Refinement n b t) = TypeMemDecl Material n b t

