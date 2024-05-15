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
  = isSubtypeRefines r1 r2
-- Rule S-NameUp
isSubtype (Type (NamedType n) r) (Type (NamedType n') r') =
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
-- Rule S-Lower
isSubtype tau0@(Type (PathType _ _) _) tau' = do
  tau <- Exposure.upcast tau0
  isSubtype tau tau'
-- Rule S-Upper
isSubtype tau tau0'@(Type (PathType _ _) _) = do
  tau' <- Exposure.downcast tau0'
  isSubtype tau tau'

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