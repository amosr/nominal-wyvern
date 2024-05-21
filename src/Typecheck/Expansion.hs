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

expandCheckSubtype :: TC m => Type -> Type -> m Bool
expandCheckSubtype t1 t2 = do
  t1' <- tryExpandLhs t1 t2
  Subtyping.isSubtype t1' t2

tryExpandLhs :: TC m => Type -> Type -> m Type
tryExpandLhs t1 t2 = do
  e <- reader (doExpansion . extensions)
  v <- if e then expandLhs t1 t2 else return t1
  traceM ("expand: " ++ show (t1, t2, v))
  return v

expandLhs :: TC m => Type -> Type -> m Type
expandLhs t1@(Type b1 r1) t2@(Type b2 r2) = withTrace ("expandLhs" ++ show (t1,t2)) $ do
  Type b' r' <- unfold1 t1 r2
  r'' <- mapM (\r -> expandLhsR r r2) r'
  return (Type b' r'')

expandLhsR :: TC m => Refinement -> [Refinement] -> m Refinement
expandLhsR r@(RefineDecl n b tau) rs = do
  case find (matchRef r) rs of
   Just (RefineDecl _ _ tau') -> do
    tau'' <- expandLhs tau tau'
    return (RefineDecl n b tau'')
   Nothing ->
    return r


unfold1 :: TC m => Type -> [Refinement] -> m Type
unfold1 (Type (NamedType n) r) rs = do
  -- traceM ("unfold1: " ++ show (n,r,rs))
  NameDecl _ _ self fields <- lookupNameDecl n
  let r' = concatMap (takeField self) fields
  return (Type (NamedType n) (mergeRefs r r'))
 where
  takeField self tt@(TypeMemDecl _ t b tau) =
    [RefineDecl t b tau | not (self `freeInType` tau) && any (matchRef (RefineDecl t b tau)) rs]
  takeField _ _ = []

unfold1 tau@(Type (PathType p t) r) rs = do
  tau' <- Exposure.exposure tau
  case tau' of
    Type (NamedType n) r -> do
      Type _ r' <- unfold1 tau' rs
      -- It's tempting to return the above unfolding as-is, but for a subtyping judgment
      -- p.t <: p.t { }
      -- we do not want to unfold p.t on the left-hand-side, as it might get stuck
      -- traceM ("unfold1-rebox: " ++ show (p,t,r,r',rs))
      return (Type (PathType p t) r')

    _ -> return tau

-- Top / Bot
unfold1 tau _ = return tau


-- Free variable membership
freeInType :: Binding -> Type -> Bool
freeInType b (Type t rs) = freeInBase b t || any (freeInRef b) rs

freeInBase b (PathType p _) = freeInPath b p
freeInBase b _ = False

freeInPath b (Var b') = b == b'
freeInPath b (Field p _) = freeInPath b p

freeInRef b (RefineDecl _ _ tau) = freeInType b tau
