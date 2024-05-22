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
import qualified Typecheck.Expansion as Expansion

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
      ok <- Expansion.expandCheckSubtype taux taux'
      assertSub (msg taux taux') ok
      return taux'
    Nothing -> return taux
  taux' <- local (appendGamma [(x, taux)]) $ typecheckExpr e
  let ok = not (freeInType x taux')
  assert (msgFree taux') ok
  return taux'
 where
  msg t1 t2 = printf "type annotation on let: %s not a subtype of %s\nlet-expression %s = %s" (show t1) (show t2) (show x) (show ex)
  msgFree t = printf "let-expression %s escapes-check:\nthe let-expression has type %s, which refers to the local binding\n" (show x) (show t)
-- Rule T-Sel
typecheckExpr (PathExpr (Field p t)) = do
  tau  <- Lookup.typecheckPathSingleton p
  tau' <- Exposure.exposure tau
  ValDecl _ tauv <- Lookup.lookupValDecl t tau' p
  return tauv

-- Rule T-App
typecheckExpr (Call p f args) =
  withErrorContext (printf "in method call %s.%s" (show p) f) $ do
    tau  <- Lookup.typecheckPathSingleton p
    tau' <- Exposure.exposure tau
    DefDecl _ params taur <- Lookup.lookupDefDecl f tau' p
    assert (printf "Wrong number of arguments: got %d, expected %d" (length args) (length params))
      (length args == length params)
    -- TODO: EXTENSION: check p: p must be var unless p is not mentioned in type
    let aps = args `zip` params
    goArgs aps taur
    -- mapM_ checkArg (args `zip` params)
    -- let taur' = substParams (args `zip` params) taur
    -- return taur'
  where
    goArgs [] taur = return taur
    goArgs ((arg,param) : rest) taur = do
      taua <- Lookup.typecheckPathSingleton arg
      ok <- Expansion.expandCheckSubtype taua (argType param)
      assertSub
        (printf "Parameter %s instantiated to %s\n  Expected type %s; got %s" (show (argName param)) (show arg) (show (argType param)) (show taua))
        ok
      -- EXTENSION
      -- Change from paper: parameter types can refer to the types of previous
      -- parameters, so we substitute this argument into the remaining
      -- parameter types.
      -- This isn't required in the paper, as the paper only supports methods
      -- with a single parameter.
      let rest' = substParams arg (argName param) rest
      let taur' = subst arg (argName param) taur
      goArgs rest' taur'

    substParams _ _ [] = []
    substParams arg nm ((argx,paramx) : rest) =
      (argx, Arg (argName paramx) (subst arg nm (argType paramx))) : substParams arg nm rest

-- Rule T-New
typecheckExpr (New tau self defs) = withErrorContext ("in new expression of type " ++ show tau) $ do
  assertTypeValid tau
  typecheckNew tau self defs
  return tau

-- Extensions
typecheckExpr TopLit = return theTop
typecheckExpr UndefLit = return theBot
typecheckExpr (Assert b tau1 tau2) = do
  ok <- Expansion.expandCheckSubtype tau1 tau2
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
    ok <- Expansion.expandCheckSubtype taux tau
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
    ok <- Expansion.expandCheckSubtype tauv' tauv
    assertSub (printf "field definition `%s` is not subtype of declared type\nexpression: %s\nhas type: %s\nexpected type: %s" v (show ev) (show tauv') (show tauv)) ok
  checkDef (DefDefn f args taur er) = do
    -- TODO: where do we check wellformedness of arg types?
    let binds = map (\a -> (argName a, argType a)) args
    local (appendGamma binds) $ do
      -- Change from paper: as in value check above, use infer-mode
      taur' <- typecheckExpr er
      ok <- Expansion.expandCheckSubtype taur' taur
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
    mapM_ (check (Var self) tauu) rb)
  where
    check self tauu r@(RefineDecl t b tau) = do
      mem@(TypeMemDecl _ _ b' tau') <- Lookup.lookupTypeMemDecl t tauu self
      -- TODO: is this expansion correct even for >= members?
      tauX <- Expansion.tryExpandLhs tau tau'
      ok <- Subtyping.isSubtypeRefinementMember (RefineDecl t b tauX) (RefineDecl t b' tau')
      assertSub (printf "type refinement not subtype\n  refinement: %s\n  class member: %s" (show r) (show mem)) ok
