-- Member lookup: Figure 7, page 17
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
-- {-# LANGUAGE LambdaCase #-}
-- {-# LANGUAGE ScopedTypeVariables #-}

module Typecheck.Lookup where

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

-- | Figure 7, Declaration Lookup
lookupMemberDecl :: TC m => (MemberDeclaration -> Bool) -> String -> Type -> Binding -> m MemberDeclaration
lookupMemberDecl pred err (Type base rs) self_new
 -- Rule Look-Refine
 | Just r <- find pred (map refToDecl rs) =
   return r
 -- Rule Look-Name
 | NamedType n <- base = do
  NameDecl _ _ self_old decls <- lookupNameDecl n
  case find pred decls of
    Just d -> return $ subst (Var self_new) self_old d
    Nothing -> throwError err
 -- Fail
 | otherwise =
  throwError err

lookupValDecl :: (MonadReader Context m, MonadError String m, MonadFail m) => Name -> Type -> Binding -> m MemberDeclaration
lookupValDecl field ty = lookupMemberDecl pred msg ty
 where
  pred (ValDecl field' _) = field == field'
  pred _ = False

  msg = printf "couldn't find field named %s in type %s" (show field) (show ty)

lookupTypeMemDecl :: (MonadReader Context m, MonadError String m, MonadFail m) => Name -> Type -> Binding -> m MemberDeclaration
lookupTypeMemDecl field ty = lookupMemberDecl pred msg ty
 where
  pred (TypeMemDecl _ field' _ _) = field == field'
  pred _ = False

  msg = printf "couldn't find type member named %s in type %s" (show field) (show ty)

lookupDefDecl :: (MonadReader Context m, MonadError String m, MonadFail m) => Name -> Type -> Binding -> m MemberDeclaration
lookupDefDecl field ty = lookupMemberDecl pred msg ty
 where
  pred (DefDecl field' _ _) = field == field'
  pred _ = False

  msg = printf "couldn't find method named %s in type %s" (show field) (show ty)

-- Get type of a path, restricted to single-variable paths
-- The paper uses the `\Delta | \Sigma | \Gamma | S \vdash p : \tau` for this
typecheckPathSingleton :: TC m => Path -> m Type
typecheckPathSingleton p = case p of
  -- Rule T-Var
  Var b -> lookupGamma b
  -- Field (Var b) v -> do
  --   tau <- typecheckPath p
  --   ValDecl _ tauv <- lookupValDecl v tau b
  --   return tauv
  -- Rule T-Loc is not implemented; it only exists for type safety proof
  Field p v ->
    throwError "typecheckPathSingleton: multi-length paths not supported"
