-- Subtyping
-- Figure 10
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PatternGuards #-}
-- {-# LANGUAGE ScopedTypeVariables #-}

module Typecheck.Subtyping where

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
import qualified Typecheck.Exposure as Exposure

-- Figure 10, subtyping on types
isSubtype :: TC m => Type -> Type -> m Bool
-- Rule S-Top
isSubtype _ (Type TopType []) = return True
-- Rule S-Bot
isSubtype (Type BotType []) _ = return True
-- Rule S-Refine
isSubtype (Type b1 r1) (Type b2 r2)
  | b1 == b2
  = withTrace ("S-Refine: " ++ show (b1,r1,r2)) $
    isSubtypeRefines r1 r2
-- Rule S-NameUp
isSubtype (Type (NamedType n) r) (Type (NamedType n') r') = withTrace ("S-NameUp: " ++ show (n,r,n',r')) $
  -- Try all declared subtypes; success if any succeed
  searchTLDecls
    (\case
      SubtypeDecl (Type (NamedType nn) rS) nS
        | nn == n ->
        isSubtypeRefines r rS &&^
        isSubtype (Type nS r) (Type (NamedType n') r')
      _ -> return False
    )
  -- Find all supertypes
-- Non-deterministic S-Lower/S-Upper:
-- The rules in the paper are not algorithmic. In fact, it's not trivial to implement them with a reasonable complexity.
-- The problem here occurs when we have `p.T <: q.U`.
-- We want to unfold one of the type members. But we don't want to unfold them too far....
-- Example: in context
-- a: X { type T <= Top }
-- b: X { type T <= a.T }
-- c: X { type T >= a.T }
-- Now, suppose we want to check `b.T <: c.T`. This is true.
-- We can't greedily unfold all the way. We'd end up with `Top <: a.T`, which isn't necessarily true.
-- So, instead, we only want to unfold each side one step.
-- In general, we don't know how far to unfold each one, so we try all alternatives.
-- This is not good. Is there a better way?
isSubtype tau0@(Type (PathType _ _) _) tau0'@(Type (PathType _ _) _)= withTrace ("S-Lower&S-Upper: " ++ show (tau0, tau0')) $ do
  tau  <- Exposure.upcast tau0
  tau' <- Exposure.upcast tau0'
  case (tau, tau') of
    (Just tau, Just tau') ->
      isSubtype tau tau' ||^ isSubtype tau0 tau' ||^ isSubtype tau0 tau0'
    (Just tau, Nothing) -> isSubtype tau tau0'
    (Nothing, Just tau') -> isSubtype tau0 tau'
    (Nothing, Nothing) -> return False
-- Rule S-Lower
isSubtype tau0@(Type (PathType _ _) _) tau' = withTrace ("S-Lower: " ++ show (tau0, tau')) $ do
  tau <- Exposure.upcast tau0
  case tau of
    Just tau -> isSubtype tau tau'
    Nothing -> return False
-- Rule S-Upper
isSubtype tau tau0'@(Type (PathType _ _) _) = withTrace ("S-Upper: " ++ show (tau, tau0')) $ do
  tau' <- Exposure.downcast tau0'
  case tau' of
    Just tau' -> isSubtype tau tau'
    Nothing -> return False

-- Otherwise, Top <: _ or _ <: Bot
isSubtype tau tau' =
  return False
  -- throwError ("isSubtype unhandled: " ++ show (tau,tau'))

-- Figure 10, subtyping relation `type t B \tau <: type t B \tau`
-- This is subtyping on type members in the paper
isSubtypeRefinementMember :: TC m => Refinement -> Refinement -> m Bool
-- Rule S-T-Eq
isSubtypeRefinementMember (RefineDecl t EQQ tau) (RefineDecl t' EQQ tau') =
  isSubtype tau tau' &&^ isSubtype tau' tau
-- Rule S-T-Le(1)
isSubtypeRefinementMember (RefineDecl t LEQ tau) (RefineDecl t' LEQ tau') =
  isSubtype tau tau'
--      S-T-Le(2)
isSubtypeRefinementMember (RefineDecl t EQQ tau) (RefineDecl t' LEQ tau') =
  isSubtype tau tau'
-- Rule S-T-Ge(1)
isSubtypeRefinementMember (RefineDecl t EQQ tau) (RefineDecl t' GEQ tau') =
  isSubtype tau' tau
--      S-T-Ge(2)
isSubtypeRefinementMember (RefineDecl t GEQ tau) (RefineDecl t' GEQ tau') =
  isSubtype tau' tau
-- Otherwise
isSubtypeRefinementMember _ _ = return False

-- Figure 10, subtyping on refinements
isSubtypeRefines :: TC m => [Refinement] -> [Refinement] -> m Bool
-- Rule S-R-Nil
isSubtypeRefines _ [] =
  return True
-- Rule S-R-Cons
isSubtypeRefines lhs (r : rhs) =
  case find (matchRef r) lhs of
    Just l -> isSubtypeRefinementMember l r &&^ isSubtypeRefines lhs rhs
    Nothing -> return False

-- Figure 11, top-level member declaration
-- isSubtypeMemberDeclaration :: TC m => MemberDeclaration -> MemberDeclaration

-- Figure 11, top-level member declaration
isSubtypeMemDecls :: TC m => [MemberDeclaration] -> [MemberDeclaration] -> m Bool
-- Rule S-Top-Nil
isSubtypeMemDecls _ [] = return True
-- Rule S-Top-Type
isSubtypeMemDecls s1 (TypeMemDecl _ t b2 tau2 : s2) =
  case find (matchTypeMemDecl t) s1 of
    Just (TypeMemDecl _ _ b1 tau1) ->
      isSubtypeRefinementMember (RefineDecl t b1 tau1) (RefineDecl t b2 tau2) &&^
      isSubtypeMemDecls s1 s2
    _ -> return False
-- Rule S-Top-Field
isSubtypeMemDecls s1 (ValDecl v tau2 : s2) =
  case find (matchValDecl v) s1 of
    Just (ValDecl _ tau1) ->
      isSubtype tau1 tau2 &&^
      isSubtypeMemDecls s1 s2
    _ -> return False
-- Rule S-Top-Method
isSubtypeMemDecls s1 (DefDecl f arg2 ret2 : s2) =
  case find (matchDefDecl f) s1 of
    Just (DefDecl _ arg1 ret1) ->
      isSubtype ret1 ret2 &&^
      allM (\(a1,a2) -> isSubtype (argType a2) (argType a1)) (arg1 `zip` arg2) &&^
      isSubtypeMemDecls s1 s2
    _ -> return False

