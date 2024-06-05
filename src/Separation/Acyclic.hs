-- Material/shape graph checks
-- This checks that the only cycles go through shapes.
{-# LANGUAGE FlexibleContexts, ConstraintKinds #-}
module Separation.Acyclic where

import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.Writer
import qualified Data.Map.Strict as Map
import Data.List (union)
import Text.Printf
import Syntax
import PrettyPrint()
import TypeUtil
import Debug.Trace
import Typecheck.Lookup (typecheckPathSingleton)

import Separation.Base

buildGraph :: Program -> TGMonad ()
buildGraph (Program decls expr) = do
  mapM_ buildGraphDecl decls

buildGraphDecl :: TopLevelDeclaration -> TGMonad ()
buildGraphDecl d = case d of
  NameDecl ta n z decls ->
    local (appendGamma [(z,makeNomType n)]) $ mapM_ (buildGraphMemDecl (PVar n)) decls
  SubtypeDecl t1@(Type n1 r1) n2 -> do
    checkTy t1
    (n1',n1TA) <- getPType n1
    (n2',n2TA) <- getPType n2
    tell [Edge n2' [] n1']
    mapM_ (recRefs n2') r1
    --If n1 is a shape, n2 must be a shape
    case (n1TA,n2TA) of
      (Shape,Material) -> throwError $ invalidShapeSubtype n1 n2
      _ -> return ()
    where recRefs n2' (RefineDecl _ _ (Type nr rr)) = do
            (nr',_) <- getPType nr
            tell [Edge n2' [] nr']
            mapM_ (recRefs n2') rr
          invalidShapeSubtype n1 n2 = printf "invalid shape usage: %s can only subtype named shapes, but %s is not a shape" (show n1) (show n2)

buildGraphMemDecl :: PType -> MemberDeclaration -> TGMonad ()
buildGraphMemDecl n d = case d of
  TypeMemDecl ta t bound t2@(Type bt rt) -> do
    checkTy t2
    let nt = PPath n t
    (bt',btTA) <- getPType bt
    genEdges (bt',btTA) rt nt []
    --check if shape is used as lower bound
    case (bound,btTA) of
      (EQQ,Shape) -> throwError $ invalidLB bt
      (GEQ,Shape) -> throwError $ invalidLB bt
      _           -> return ()
    --If the type member is a shape, check that upper bound is a shape
    case (ta,bound,btTA) of
      (Shape,LEQ,Material) -> throwError $ invalidShapeUB t
      _ -> return ()
    where invalidLB bt = printf "invalid shape usage: %s used as lower bound" (show bt)
          invalidShapeUB t = printf "invalid shape usage: %s must be upper bounded by a shape" (show t)
  ValDecl v ty -> checkTy ty
  DefDecl f args ty -> local (appendGamma (map argToTup args)) $ do
    mapM_ checkTy (map argType args)
    checkTy ty

---------------------------------------
genEdges :: (PType,TypeAnnot) -> [Refinement] -> PType -> [(PType,TypeAnnot)] -> TGMonad ()
genEdges (b,_) [] br ba = tell [Edge br ba b]
genEdges (b,bTA) (RefineDecl _ _ (Type bt rt):rest) br ba = do
  bt' <- getPType bt
  genEdges (b,bTA) rest br ba
  genEdges bt' rt br ((b,bTA):ba)

--------------------------------------
--naive cycle checking
checkCycles :: [Edge] -> Either String ()
checkCycles es = runExcept $ mapM_ (dfs es' []) vertices
  where vertices = foldr (\(Edge from _ to) vs -> [from,to] `union` vs) [] es
        es' = filter noshape es
        noshape (Edge _ ls _) = and (map (isMat.snd) ls)
        isMat Material = True
        isMat Shape    = False

dfs :: [Edge] -> [PType] -> PType -> Except String ()
dfs es stack v =
  if v `elem` stack then
    throwError $ printf "Cycle found: %s" (show stack)
    else do
      let es' = filter (\(Edge from _ _) -> from == v) es
      mapM_ (\(Edge _ _ to) -> dfs es (v:stack) to) es'
