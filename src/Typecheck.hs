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

typecheck prog = runExcept (runReaderT (fullTypecheck prog) emptyCtx)

fullTypecheck :: TC m => Program -> m Type
fullTypecheck (Program decls expr) = do
  let (names, subs) = partition split decls
  mapM_ checkTLDecl names
  local (appendTopLevel decls) $ do
    ctx <- ask
    --traceM ("ctx: " ++ (show $ toplevel ctx))
    mapM_ checkTLDecl subs
    final_p <- preprocess (Program decls expr)
    typecheckProgram final_p
  where
    split NameDecl {} = True
    split (SubtypeDecl _ _) = False

typecheckProgram :: TC m => Program -> m Type
typecheckProgram (Program decls expr) = do
  -- let (names, subs) = partition split decls
  -- mapM_ checkTLDecl names
  -- local (appendTopLevel decls) $ do
  --   ctx <- ask
  --   --traceM ("ctx: " ++ (show $ toplevel ctx))
  --   mapM_ checkTLDecl subs
  typecheckExpr expr

-- where
--   split NameDecl {} = True
--   split (SubtypeDecl _ _) = False

checkTLDecl :: TC m => TopLevelDeclaration -> m ()
checkTLDecl (NameDecl _ n z decls) = do
  let fields = getFields decls
      paths = map (Field (Var z)) fields
      types = getTypes decls
  --traceM ("fields = " ++ show fields)
  --traceM ("paths = " ++ show paths)
  --traceM ("types = " ++ show types)
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
checkTLDecl (SubtypeDecl t1 n2) = do
  (x1, decls1) <- unfold t1
  (x2, decls2) <- unfold (Type n2 [])
  local (appendGamma [(x1, t1)]) $
    isStructSubtype decls1 (subst (Var x1) x2 decls2) >>= assertSub (msg decls1 (subst (Var x1) x2 decls2))
  where
    msg decls1 decls2 = printf "invalid subtype decl: %s not a subtype of %s\n%s <:\n%s" (show t1) (show n2) (show decls1) (show decls2)

checkTypeWF :: forall m. TC m => Type -> m ()
checkTypeWF (Type TopType []) = return ()
checkTypeWF (Type BotType []) = return ()
checkTypeWF (Type base rs) = do
  Type n rn <- typeExpand (Type base rs)
  (x_n, decls_n) <- unfoldExpanded (Type n [])
  let typeMembers = rs ++ ref decls_n
      findMatchingRefinement :: Refinement -> [(Refinement, Refinement)]
      findMatchingRefinement l = (\r -> (l, r)) <$> filter (matchRef l) typeMembers
      matchingRefinements :: [(Refinement, Refinement)]
      matchingRefinements = concatMap findMatchingRefinement rn
      checkRefinementInvalidSubtype :: (Refinement, Refinement) -> m Bool
      checkRefinementInvalidSubtype (l, r) = local (appendGamma [(x_n, (Type base rs))]) $ not <$> isSubtypeRef l r

  maybeViolatingRefinements <- findM checkRefinementInvalidSubtype matchingRefinements
  case maybeViolatingRefinements of
    Nothing -> return ()
    Just (l, r) -> throwError (printf "Invalid refinement when checking wellformedness of type %s: %s is not a subtype of %s" (show (Type base rs)) (show l) (show r))

-- T-New
newTypeWF :: TC m => Type -> Binding -> [MemberDefinition] -> m ()
newTypeWF ty x defns = do
  checkTypeWF ty
  Type n rs <- typeExpand ty
  (x_n, decls_n) <- unfoldExpanded (Type n [])
  let tau_x = Type n (ref . sig $ defns)
      self = (x, tau_x)
      ap_self = local (appendGamma [self])
      new_decls = sig defns
      old_decls = subst (Var x) x_n (map refToDecl rs ++ decls_n)
  ap_self $
    isStructSubtype new_decls old_decls
      >>= assertSub (printf "new expr not struct subtype:\n%s <:\n%s" (show new_decls) (show old_decls))
  let checkDefn (TypeMemDefn _ _) = return ()
      checkDefn d@(DefDefn f args tau_r expr) = ap_self $ do
        let args' = map argToTup args
        local (appendGamma args') $ do
          tau_r' <- typecheckExpr expr
          isSubtype tau_r' tau_r >>= assertSub (printf "defn %s: %s is not a subtype of return type %s" (show f) (show tau_r') (show tau_r))
      checkDefn (ValDefn v tau_v expr) = do
        tau_v' <- typecheckExpr expr
        ap_self $ isSubtype tau_v' tau_v >>= assertSub (printf "val %s: %s is not a subtype of annotation %s" v (show tau_v') (show tau_v))
  mapM_ checkDefn defns

unfold :: TC m => Type -> m (Binding, [MemberDeclaration])
unfold t0 = do
  t1 <- typeExpand t0
  unfoldExpanded t1

unfoldExpanded :: TC m => Type -> m (Binding, [MemberDeclaration])
unfoldExpanded (Type base rs) =
  case base of
    NamedType n -> do
      NameDecl _ _ z decls <- lookupTLDecls pred msg
      -- Shadowing: only take the declarations from type that are not
      -- overwritten by the refinement.
      let decls' = filter noshadow decls
      return (z, map refToDecl rs ++ decls')
      where
        pred (NameDecl _ n' _ _) = n == n'
        pred _ = False

        noshadow (TypeMemDecl _ t _ _) =
          all (notnamed t) rs
        noshadow _ = True

        notnamed t (RefineDecl t' _ _) =
          t /= t'


        msg = printf "couldn't find name %s" (show n)
    _ -> return (Binding "z" (-1), map refToDecl rs)

typeExpand :: TC m => Type -> m Type
typeExpand tau@(Type base rs) = case base of
  PathType p t -> do
    tau_p <- typecheckPath p
    (z, decls) <- unfold tau_p
    TypeMemDecl _ _ bound ty <- lookupMemberDecls pred errMsg decls
    case bound of
      GEQ -> return tau
      _ -> typeExpand (subst p z (merge ty rs))
    where
      pred (TypeMemDecl _ t' _ _) = t == t'
      pred _ = False
      errMsg = printf "type expand: couldn't find type member %s in path %s" t (show p)
  _ -> return tau

typecheckExpr :: TC m => Expr -> m Type
typecheckExpr e = case e of
  PathExpr p -> typecheckPath p
  New ty z rs ->
    newTypeWF ty z rs
      >> return ty
  Call p meth es -> do
    pty <- typecheckPath p
    (z, decls) <- unfold pty
    let pred (DefDecl b _ _) = b == meth
        pred _ = False
    DefDecl m args retTy <- lookupMemberDecls pred cantFindDef decls
    --subfunc creates the correct type by subbing in the arguments and path p
    let subfunc ty = foldr (\(Arg x _, exp) -> subst exp x) (subst p z ty) (zip args es)
    let argsTypeSubbed = map (subfunc . (\(Arg _ ty) -> ty)) args --correct arg types
    esTys <- mapM typecheckPath es --these are the calling types
    --subtype check
    assert wrongLength (length esTys == length argsTypeSubbed)
    es_expanded <- zipWithM expand esTys argsTypeSubbed
    checkPairwise isSubtype esTys argsTypeSubbed >>= assertSub (callNotSubtype esTys argsTypeSubbed)
    return $ subfunc retTy --subbed return type
    where
      cantFindDef = "failed to find method name " ++ meth
      wrongLength = printf "calling %s: wrong # of arguments" meth
      callNotSubtype esTys argsTypeSubbed = printf "calling %s: subtype check failed when calling method, %s not subtypes of %s" meth (show esTys) (show argsTypeSubbed)
  Let x annot e1 e2 -> do
    t1 <- typecheckExpr e1
    xTy <- case annot of
      Just ty -> do
        isSubtype t1 ty >>= assertSub (letmsg t1 ty)
        return ty
      Nothing -> return t1
    local (appendGamma [(x, xTy)]) $ typecheckExpr e2
    where
      letmsg t1 ty = printf "let expr: var %s has type %s, but annotation has type %s" (show x) (show t1) (show ty)
  TopLit -> return theTop
  UndefLit -> return theBot
  Assert True t1 t2 -> do
    isSubtype t1 t2
      >>= assertSub (printf "assertion '%s <: %s' failed" (show t1) (show t2))
    return theTop
  Assert False t1 t2 -> do
    liftM not (isSubtype t1 t2)
      >>= assertSub (printf "assertion: '%s </: %s' failed" (show t1) (show t2))
    return theTop

typecheckPath :: TC m => Path -> m Type
typecheckPath p = case p of
  Var b -> lookupGamma b
  Field p v -> do
    tau <- typecheckPath p
    (z, decls) <- unfold tau
    ValDecl _ tauv <- lookupMemberDecls pred errMsg decls
    return $ subst p z tauv
    where
      pred (ValDecl b _) = b == v
      pred _ = False
      errMsg = ("failed to find field " ++ v)

--type equality
equalBaseType :: TC m => BaseType -> BaseType -> m Bool
equalBaseType a b =
  {-trace ("eq base type " ++ show a ++ " " ++ show b) $-} case (a, b) of
    (TopType, TopType) -> return True
    (BotType, BotType) -> return True
    (NamedType n1, NamedType n2) -> return $ n1 == n2
    (PathType p1 n1, PathType p2 n2)
      | p1 == p2 -> return $ n1 == n2
    {-
    | otherwise -> do
        tau1 <- typecheckPath p1
        tau2 <- typecheckPath p2
        eqTy <- equalType tau1 tau2
        return $ eqTy && (n1 == n2)
    -}
    _ -> return False

equalType :: TC m => Type -> Type -> m Bool
equalType (Type b1 r1) (Type b2 r2) =
  equalBaseType b1 b2 &&^ checkPermDual equalRefinement r1 r2

--traceM $ (show (Type b1 r1)) ++ " = " ++ (show (Type b2 r2))

equalRefinement :: TC m => Refinement -> Refinement -> m Bool
equalRefinement (RefineDecl t1 bound1 ty1) (RefineDecl t2 bound2 ty2) =
  (return $ t1 == t2 && bound1 == bound2) &&^ equalType ty1 ty2

isSubtype :: TC m => Type -> Type -> m Bool
isSubtype t1@(Type b1 r1) t2@(Type b2 r2) = do
  --traceM (show t1 ++ " <: " ++ show t2)
  eqBase <- equalBaseType b1 b2
  if eqBase
    then checkPerm isSubtypeRef r1 r2
    else s_Top ||^ s_Bot ||^ s_Name ||^ s_Upper ||^ s_Lower
  where
    pred t' (TypeMemDecl _ t _ _) = t == t'
    pred t' _ = False
    lookupMsg t = "failed to find type member " ++ t
    s_Top = equalType t2 theTop
    s_Bot = equalType t1 theBot
    s_Name =
      ( isSubtypeBase t1 b2 &&^ do
          checkPerm isSubtypeRef r1 r2
      )
    --this (above) is the old rule, the next two lines is the new rule
    --(z,r1') <- unfold t1
    --local (appendGamma [(z,t1)]) $ checkPerm isSubtypeMemDecl r1' (map refToDecl r2))
    s_Upper = case b1 of
      PathType p t -> do
        tau_p <- typecheckPath p
        (z, decls) <- unfold tau_p
        TypeMemDecl _ _ bound ty <- lookupMemberDecls (pred t) (lookupMsg t) decls
        case bound of
          GEQ -> return False
          _ ->
            let t1' = subst p z (merge ty r1)
             in isSubtype t1' t2
      _ -> return False
    s_Lower = case b2 of
      PathType p t -> do
        tau_p <- typecheckPath p
        (z, decls) <- unfold tau_p
        TypeMemDecl _ _ bound ty <- lookupMemberDecls (pred t) (lookupMsg t) decls
        --traceM (printf "got here %s %s" (show bound) (show ty))
        case bound of
          LEQ -> return False
          _ ->
            let t2' = subst p z (merge ty r2)
             in isSubtype t1 t2'
      _ -> return False

isSubtypeBase :: TC m => Type -> BaseType -> m Bool
isSubtypeBase (Type b1 r1) b2 = do
  --traceM ("isb: " ++ show (Type b1 r1) ++ " <: " ++ show b2)
  equalBaseType b1 b2 ||^ searchTLDecls pred
  where
    pred (SubtypeDecl (Type baseL rsL) baseR) =
      equalBaseType b1 baseL
        &&^ checkPerm isSubtypeRef r1 rsL
        &&^ isSubtypeBase (Type baseR r1) b2
    pred _ = return False

isSubtypeRef :: TC m => Refinement -> Refinement -> m Bool
isSubtypeRef a b = isSubtypeMemDecl (refToDecl a) (refToDecl b)

isStructSubtype :: TC m => [MemberDeclaration] -> [MemberDeclaration] -> m Bool
isStructSubtype as bs = checkPerm isSubtypeMemDecl as bs

{-trace (show a ++ " <: " ++ show b) $-}
isSubtypeMemDecl :: TC m => MemberDeclaration -> MemberDeclaration -> m Bool
isSubtypeMemDecl a b = case (a, b) of
  (TypeMemDecl _ t1 bound1 ty1, TypeMemDecl _ t2 bound2 ty2)
    | t1 == t2 -> case (bound1, bound2) of
      (EQQ, EQQ) -> checkCov &&^ checkContra --checkEq?
      (LEQ, LEQ) -> checkCov
      (EQQ, LEQ) -> checkCov
      (GEQ, GEQ) -> checkContra
      (EQQ, GEQ) -> checkContra
      _ -> return False
    | otherwise -> return False
    where
      checkCov = do
        -- AMOS: disable expansion inside subtyping rules
        -- Expansion should not occur inside subtyping, as it introduces divergence.
        -- Instead, only perform expansion before calling subtyping rules
        -- expanded_ty1 <- expand ty1 ty2
        isSubtype ty1 ty2
      checkContra = do
        -- expanded_ty2 <- expand ty2 ty1
        isSubtype ty2 ty1
  (ValDecl v1 t1, ValDecl v2 t2) ->
    (return $ v1 == v2) &&^ isSubtype t1 t2
  (DefDecl f1 args1 ty1, DefDecl f2 args2 ty2) -> do
    let types1 = map argType args1
        types2 = map argType args2
        names1 = map argName args1
        names2 = map argName args2
        subfunc ty = foldr (\(x1, x2) -> subst (Var x1) x2) ty (zip names1 names2)
        vs1 = map argToTup args1
        types2' = map subfunc types2
        ty2' = subfunc ty2
    local (appendGamma vs1) $ do
      argsSubtype <- checkPerm isSubtype types2' types1 --contra
      retSubtype <- isSubtype ty1 ty2' --cov
      return $ (f1 == f2) && argsSubtype && retSubtype
  _ -> return False

expand :: TC m => Type -> Type -> m Type
expand ty@(Type t1 _) (Type t2 refs2) = do
  (_, memberDecls) <- unfold ty
  let refs1 =
        mapMaybe
          ( \case
              TypeMemDecl _ n b t -> Just (RefineDecl n b t)
              _ -> Nothing
          )
          memberDecls
  final_refs <-
    mapM
      ( \r@(RefineDecl n2 _ t2') ->
          case find (\(RefineDecl n1 _ _) -> n1 == n2) refs1 of
            Just (RefineDecl n1 b1 t1') -> do
              res <- expand t1' t2'
              return [RefineDecl n1 b1 res]
            -- XXX: why is this a failure? `Bot <: n { t = tau }` should succeed, but failing here?
            Nothing -> return []
            -- Nothing -> fail ("expand: this program doesn't type: unknown type " ++ show (n2, memberDecls) ++ "\nty: " ++ (show ty) ++ "\nty2: " ++ (show (Type t2 refs2)))
      )
      refs2
  let refs2' = concat final_refs
  -- Keep any refinements from refs1 that aren't overwritten by refs2
  let refs1' = filter (\r1@(RefineDecl n1 _ _) -> all (\r2@(RefineDecl n2 _ _) -> n1 /= n2) refs2') refs1
  let r = Type t1 (refs1' ++ refs2')
  traceM ("expand: " ++ show ty)
  traceM ("===>    " ++ show r)
  return (Type t1 (refs1' ++ refs2'))

preprocess :: TC m => Program -> m Program
preprocess (Program decls expr) = do
  p_expr <- preprocessExpr expr
  return (Program decls p_expr)

preprocessExpr :: TC m => Expr -> m Expr
preprocessExpr expr = case expr of
  PathExpr pa -> return expr
  Call pa method es -> return expr
  -- pa is path, s is method name, pas is arguments

  New ty bind mds -> return expr
  Let bind m_ty ex ex' -> do
    left_ex <- preprocessExpr ex
    right_ex <- preprocessExpr ex'
    return (Let bind m_ty left_ex right_ex)
  TopLit -> return expr
  UndefLit -> return expr
  Assert b ty ty' -> do
    expanded_ty <- expand ty ty'
    return (Assert b expanded_ty ty')
