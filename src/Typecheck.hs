{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Typecheck where

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
import qualified Typecheck.Check as Check

typecheck prog = runExcept (runReaderT (fullTypecheck prog) emptyCtx)

-- Top-level typechecking
-- Figure 5 judgment `P : \tau`
fullTypecheck :: TC m => Program -> m Type
fullTypecheck (Program decls expr) = do
  let (names, subs) = partition split decls
  mapM_ checkTLDecl names
  local (appendTopLevel decls) $ do
    mapM_ checkTLDecl subs
    withErrorContext "checking program expression" $ Check.typecheckExpr expr
  where
    split NameDecl {} = True
    split SubtypeDecl{} = False

checkTLDecl :: TC m => TopLevelDeclaration -> m ()
-- Check named class: fields cannot be mentioned in types
-- Is this formalised in the paper?
checkTLDecl (NameDecl _ n z decls) = withErrorContext ("checking top-level named type " ++ show n) $ do
  let fields = getFields decls
      paths = map (Field (Var z)) fields
      types = getTypes decls
  mapM_ (noReference paths) types
  where
    getFields [] = []
    getFields ((ValDecl v _) : xs) = v : getFields xs
    getFields (_ : xs) = getFields xs
    getTypes [] = []
    getTypes (TypeMemDecl _ _ _ ty : xs) = ty : getTypes xs
    getTypes (_ : xs) = getTypes xs
    noReference paths ty = mapM_ (notInType ty) paths
    notInType (Type base rs) path = do
      case base of
        PathType p t -> notInPath p path
        _ -> return ()
      mapM_ (notInRefine path) rs
    notInRefine path (RefineDecl _ _ ty) = notInType ty path
    notInPath p path
      | p == path = throwError (printf "error when checking name well-formedness: sibling field %s in declaration of named type %s" (show path) (show n))
      | otherwise = case p of
        Var _ -> return ()
        Field p' _ -> notInPath p' path

-- Check subtyping declaration, Figure 5
checkTLDecl s@(SubtypeDecl tau@(Type (NamedType n1) r1) (NamedType n2)) = withErrorContext ("checking subtyping declaration: " ++ show s) $ do
  NameDecl _ _ x1 sigma1 <- lookupNameDecl n1
  NameDecl _ _ x2 sigma2 <- lookupNameDecl n2
  local (appendGamma [(x1, tau)]) $ do
    let sigma1' = mergeDecls (map refToDecl r1) sigma1
    let sigma2' = subst (Var x1) x2 sigma2
    ok <- Subtyping.isSubtypeMemDecls sigma1' sigma2'
    assertSub (msg sigma1' sigma2') ok
  where
    msg sigma1 sigma2 = printf "invalid subtype decl: %s not a subtype of %s\n%s <:\n%s" (show tau) (show n2) (show sigma1) (show sigma2)
checkTLDecl s@(SubtypeDecl (Type _ r1) _) =
  throwError ("invalid subtyping declaration: " ++ show s)


-- TODO check WF
-- checkTypeWF :: forall m. TC m => Type -> m ()
-- checkTypeWF (Type TopType []) = return ()
-- checkTypeWF (Type BotType []) = return ()
-- checkTypeWF (Type base rs) = do
--   Type n rn <- typeExpand (Type base rs)
--   (x_n, decls_n) <- unfoldExpanded (Type n [])
--   let typeMembers = rs ++ ref decls_n
--       findMatchingRefinement :: Refinement -> [(Refinement, Refinement)]
--       findMatchingRefinement l = (\r -> (l, r)) <$> filter (matchRef l) typeMembers
--       matchingRefinements :: [(Refinement, Refinement)]
--       matchingRefinements = concatMap findMatchingRefinement rn
--       checkRefinementInvalidSubtype :: (Refinement, Refinement) -> m Bool
--       checkRefinementInvalidSubtype (l, r) = local (appendGamma [(x_n, (Type base rs))]) $ not <$> isSubtypeRef l r

--   maybeViolatingRefinements <- findM checkRefinementInvalidSubtype matchingRefinements
--   case maybeViolatingRefinements of
--     Nothing -> return ()
--     Just (l, r) -> throwError (printf "Invalid refinement when checking wellformedness of type %s: %s is not a subtype of %s" (show (Type base rs)) (show l) (show r))

-- equalType :: TC m => Type -> Type -> m Bool
-- equalType (Type b1 r1) (Type b2 r2) =
--   equalBaseType b1 b2 &&^ checkPermDual equalRefinement r1 r2
