{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Typecheck.Check where

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

import qualified Typecheck.Exposure as Exposure
import qualified Typecheck.Lookup as Lookup
import qualified Typecheck.Subtyping as Subtyping

-- Figure 6, expression typing
typecheckExpr :: TC m => Expr -> m Type
-- Rule T-Var
typecheckExpr (PathExpr (Var p)) = Lookup.typecheckPathSingleton (Var p)
-- Rule T-Let
typecheckExpr (Let x ta ex e) = do
  taux <- withErrorContext (printf "in let-expression %s" (show x)) $
    typecheckExpr ex
  taux <- case ta of
    Just taux' -> do
      ok <- Subtyping.isSubtype taux taux'
      assertSub (msg taux taux') ok
      return taux'
    Nothing -> return taux
  local (appendGamma [(x, taux)]) $ typecheckExpr e
 where
  msg t1 t2 = printf "type annotation on let: %s not a subtype of %s\nlet-expression %s = %s" (show t1) (show t2) (show x) (show ex)
-- Rule T-Sel
typecheckExpr (PathExpr (Field (Var p) t)) = do
  tau  <- Lookup.typecheckPathSingleton (Var p)
  tau' <- Exposure.exposure tau
  -- Slight change from paper: tau' doesn't actually need to be a name 'n'
  ValDecl _ tauv <- Lookup.lookupValDecl t tau' p
  return tauv
-- Multi-length paths not allowed
typecheckExpr e@(PathExpr (Field _ _)) = throwError ("not supported: multi-length paths: " ++ show e)

-- Rule T-App
typecheckExpr (Call (Var p) f args) =
  withErrorContext (printf "in method call %s.%s" (show p) f) $ do
    tau  <- Lookup.typecheckPathSingleton (Var p)
    tau' <- Exposure.exposure tau
    DefDecl _ params taur <- Lookup.lookupDefDecl f tau' p
    assert (printf "Wrong number of arguments: got %d, expected %d" (length args) (length params))
      (length args == length params)
    mapM_ checkArg (args `zip` params)
    let taur' = substParams (args `zip` params) taur
    -- traceM (printf "tau: %s\ntau': %s\ntaur: %s\ntaur': %s\nsubst: %s\nself: %s" (show tau) (show tau') (show taur) (show taur') (show (args `zip` params)) (show p))
    return taur'
  where
    checkArg (arg,param) = do
      taua <- Lookup.typecheckPathSingleton arg
      -- TODO: expressivity: we should substitute into param types before checking. this isn't required for paper as paper only supports single-argument methods
      ok <- Subtyping.isSubtype taua (argType param)
      assertSub
        (printf "Parameter %s instantiated to %s\n  Expected type %s; got %s" (show (argName param)) (show arg) (show (argType param)) (show taua))
        ok

    substParams [] taur = taur
    substParams ((arg,param) : ps) taur =
        substParams ps (subst arg (argName param) taur)
typecheckExpr e@(Call pp f args) =
  -- We can't do method calls with long paths in general...
  throwError ("not supported: target for method call must be variable (A-normal form): " ++ show e)

-- Rule T-New
typecheckExpr (New tau self defs) = withErrorContext ("in new expression of type " ++ show tau) $ do
  assertTypeValid tau
  typecheckNew tau self defs
  return tau

-- Extensions
typecheckExpr TopLit = return theTop
typecheckExpr UndefLit = return theBot
typecheckExpr (Assert b tau1 tau2) = do
  ok <- Subtyping.isSubtype tau1 tau2
  let msg = printf "assertion failed: %s %s %s"
        (show tau1)
        (if b then "<:" else "</:")
        (show tau2)
  assertSub msg (ok == b)
  return theTop

typecheckNew :: TC m => Type -> Binding -> [MemberDefinition] -> m ()
typecheckNew tau self defs = do
  let refs = ref (sig defs)
  let taux = merge tau refs
  local (appendGamma [(self, taux)]) $ do
    ok <- Subtyping.isSubtype taux tau
    assertSub (printf "new object is not subtype of declared type.\nobject type: %s" (show taux)) ok
    mapM_ checkDef defs
 where
  checkDef TypeMemDefn{} =
    -- TODO: check against type member in tau
    return ()
  checkDef (ValDefn v tauv ev) = do
    -- TODO: must check against field in tau

    -- Change from paper: the paper uses the typecheck relation in check-mode;
    -- instead, we use typecheck in infer-mode and check subtype.
    -- This is simply to avoid implementing both check and infer modes, rather
    -- than any fundamental reason.
    tauv' <- typecheckExpr ev
    ok <- Subtyping.isSubtype tauv' tauv
    assertSub (printf "field definition `%s` is not subtype of declared type\nexpression: %s\nhas type: %s\nexpected type: %s" v (show ev) (show tauv') (show tauv)) ok
  checkDef (DefDefn f args taur er) = do
    -- TODO: where do we check wellformedness of arg types?
    let binds = map (\a -> (argName a, argType a)) args
    local (appendGamma binds) $ do
      -- Change from paper: as in value check above, use infer-mode
      taur' <- typecheckExpr er
      ok <- Subtyping.isSubtype taur' taur
      assertSub (printf "method definition `%s` result is not subtype of declared type\nexpression: %s\nhas type: %s\nexpected type: %s" f (show er) (show taur') (show taur)) ok

-- Figure 6, type validity
-- \Gamma \vdash \tau valid
assertTypeValid :: TC m => Type -> m ()
-- Unnamed rule "Top valid"
assertTypeValid (Type TopType []) = return ()
assertTypeValid tau@(Type TopType r) =
  throwError (printf "top type cannot be refined: %s" (show tau))

-- Unnamed rule "Bot valid"
assertTypeValid (Type BotType []) = return ()
assertTypeValid tau@(Type BotType r) =
  throwError (printf "bottom type cannot be refined: %s" (show tau))

-- Unnamed rule "beta r_b valid"
assertTypeValid tau0@(Type b rb) =
  withErrorContext ("in type validity " ++ show tau0) $
  locallyFresh tau0 (\self -> do
    tauu <- Exposure.exposure (Type b [])
    mapM_ (check self tauu) rb)
  where
    check self tauu r@(RefineDecl t b tau) = do
      mem@(TypeMemDecl _ _ b' tau') <- Lookup.lookupTypeMemDecl t tauu self
      ok <- Subtyping.isSubtypeRefinementMember r (RefineDecl t b' tau')
      assertSub (printf "type refinement not subtype\n  refinement: %s\n  class member: %s" (show r) (show mem)) ok
