-- Expansion (extension)
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
-- {-# LANGUAGE LambdaCase #-}
-- {-# LANGUAGE ScopedTypeVariables #-}

module Typecheck.Expansion where

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
import qualified Typecheck.Subtyping as Subtyping

depth :: Type -> Int
depth (Type b []) = 0
depth (Type b r) = 1 + maximum (map depthRefinement r)

depthRefinement :: Refinement -> Int
depthRefinement (RefineDecl _ _ tau) = depth tau

expandCheckSubtype :: TC m => Type -> Type -> m Bool
expandCheckSubtype t1 t2 = do
  (t1', t2') <- tryExpandPair t1 t2
  Subtyping.isSubtype t1' t2'

tryExpandPair :: TC m => Type -> Type -> m (Type, Type)
tryExpandPair t1 t2 = do
  let d = depth t1 `max` depth t2
  t1' <- tryExpand d t1
  t2' <- tryExpand d t2
  return (t1', t2')

tryExpand :: TC m => Int -> Type -> m Type
tryExpand d t = do
  e <- reader (doExpansion . extensions)
  if e then expand d t else return t

expand :: TC m => Int -> Type -> m Type
expand 0 t = return t
expand d t = withTrace ("expand" ++ show (d,t)) $ do
  Type b' r' <- unfold1 t
  r'' <- mapM (expandR (d - 1)) r'
  return (Type b' r'')

expandR :: TC m => Int -> Refinement -> m Refinement
expandR d (RefineDecl n b tau) = do
  tau' <- expand d tau
  return $ RefineDecl n b tau


unfold1 :: TC m => Type -> m Type
unfold1 (Type (NamedType n) r) = do
  NameDecl _ _ self fields <- lookupNameDecl n
  r' <- concatMapM (takeField self) fields
  return (Type (NamedType n) (mergeRefs r r'))
 where
  takeField self tt@(TypeMemDecl _ t b tau) = do
    tau' <- Exposure.avoid self tau
    case tau' of
      Just tau' -> return [RefineDecl t b tau']
      Nothing -> return []
  takeField _ _ = return []

unfold1 tau@(Type (PathType p t) r) = do
  tau' <- Exposure.exposure tau
  case tau' of
    Type (NamedType n) r -> do
      Type _ r' <- unfold1 tau'
      -- It's tempting to return the above unfolding as-is, but for a subtyping judgment
      --   p.t <: p.t
      -- we do not want to unfold p.t on the left-hand-side -- it might make
      -- the judgment un-derivable.
      -- Instead, apply the refinements we find to the original path
      return (Type (PathType p t) r')

    _ -> return tau

-- Top / Bot
unfold1 tau = return tau
