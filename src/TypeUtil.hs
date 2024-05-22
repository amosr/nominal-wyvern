{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}

module TypeUtil where

import Control.Monad.Except
import Control.Monad.Extra
import Control.Monad.Reader
import Data.Functor.Identity
import Data.List (find)
import Data.Maybe (isNothing)
import Debug.Trace
import PrettyPrint
import Syntax
import Text.Printf

instance MonadFail Data.Functor.Identity.Identity where
  fail x = error ("monad pattern match fail: " ++ x)

data CheckSubtype = On | Off

data Extensions = Extensions {
  -- allowMultiPath :: Bool,
  doExpansion :: Bool,
  doTrace :: Bool
}

data Context = Context
  { toplevel :: [TopLevelDeclaration],
    gamma :: [(Binding, Type)],
    locallyFreshSupply :: Int,
    isCheck :: CheckSubtype,
    extensions :: Extensions
  }

emptyCtx = Context [] [] 0 On (Extensions False False)

appendTopLevel :: [TopLevelDeclaration] -> Context -> Context
appendTopLevel ds (Context t g f c e) = Context (ds ++ t) g f c e

appendGamma :: [(Binding, Type)] -> Context -> Context
appendGamma ds (Context t g f c e) = Context t (ds ++ g) f c e

locallyFresh' :: Type -> Context -> (Context, Binding)
locallyFresh' tau (Context t g f c e) =
  -- XXX: does this need to be globally unique?
  let b = Binding "^fresh" f in
  (Context t ((b,tau) : g) (f + 1) c e, b)

locallyFresh :: TC m => Type -> (Binding -> m a) -> m a
locallyFresh tau act = do
  c <- ask
  let (c',b) = locallyFresh' tau c
  local (const c') (act b)

turnSubtypingOff :: Context -> Context
turnSubtypingOff (Context t g f _ e) = Context t g f Off e

type TC m = (MonadReader Context m, MonadError String m, MonadFail m)

assert :: TC m => String -> Bool -> m ()
assert err True = do
  ctx <- ask
  when (doTrace (extensions ctx)) $ traceM ("(trace) assertion ok: " ++ err)
assert err False = throwError err

assertSub :: TC m => String -> Bool -> m ()
assertSub err b = do
  ctx <- ask
  case (isCheck ctx) of
    On -> assert err b
    Off ->
      when (doTrace (extensions ctx)) $ traceM ("(trace) ignoring subtype assertion: " ++ err)

withTrace :: TC m => String -> m a -> m a
withTrace ctx act = do
  c <- ask
  when (doTrace (extensions c)) $ traceM ("(trace) " ++ ctx ++ "{")
  r <- act
  when (doTrace (extensions c)) $ traceM "(trace) }"
  return r

withErrorContext :: TC m => String -> m a -> m a
withErrorContext ctx act =
  catchError act' (\err -> throwError ("    " ++ ctx ++ "\n" ++ err))
 where
  act' = withTrace ctx act

lookupGamma :: TC m => Binding -> m Type
lookupGamma v = do
  g <- reader gamma
  case lookup v g of
    Just x -> return x
    Nothing ->
      let err = printf "no such variable: %s\ncontext: %s" (show v) (show g) in
      throwError err

lookupTLDecls :: TC m => (TopLevelDeclaration -> Bool) -> String -> m TopLevelDeclaration
lookupTLDecls pred msg = do
  ctx <- ask
  -- traceM ("toplevel" ++ show (toplevel ctx))
  search <- reader (find pred . toplevel)
  case search of
    Just x -> return x
    Nothing -> throwError msg

lookupNameDecl :: TC m => Binding -> m TopLevelDeclaration
lookupNameDecl n =
  lookupTLDecls find_name msg
 where
  find_name (NameDecl _ n' _ _) = n == n'
  find_name _ = False
  msg = printf "no such top-level named type: `%s`" (show n)

searchTLDecls :: TC m => (TopLevelDeclaration -> m Bool) -> m Bool
searchTLDecls pred = do
  tldecls <- reader toplevel
  anyM pred tldecls

----------------------------------
theTop = Type TopType []

theBot = Type BotType []

makeNomType s = Type (NamedType s) []

sameName :: Binding -> Binding -> Bool
sameName b1 b2 = name b1 == name b2

argToTup :: Arg -> (Binding, Type)
argToTup (Arg v ty) = (v, ty)

refToDecl :: Refinement -> MemberDeclaration
refToDecl (RefineDecl t bound ty) = TypeMemDecl Material t bound ty

matchTypeMemDecl :: Name -> MemberDeclaration -> Bool
matchTypeMemDecl t1 (TypeMemDecl _ t2 _ _) = t1 == t2
matchTypeMemDecl t1 _ = False

matchValDecl :: Name -> MemberDeclaration -> Bool
matchValDecl t1 (ValDecl t2 _) = t1 == t2
matchValDecl t1 _ = False

matchDefDecl :: Name -> MemberDeclaration -> Bool
matchDefDecl t1 (DefDecl t2 _ _) = t1 == t2
matchDefDecl t1 _ = False



matchRef :: Refinement -> Refinement -> Bool
matchRef (RefineDecl t1 _ _) (RefineDecl t2 _ _) = t1 == t2

mergeRefs :: [Refinement] -> [Refinement] -> [Refinement]
mergeRefs new old = new ++ old'
  where
    old' = filter search old
    search x = isNothing $ find (matchRef x) new

merge :: Type -> [Refinement] -> Type
merge (Type base rs) rs' = Type base (mergeRefs rs' rs)

mergeDecls :: [MemberDeclaration] -> [MemberDeclaration] -> [MemberDeclaration]
mergeDecls new old = new ++ old'
  where
    old' = filter search old
    search (TypeMemDecl _ t _ _) = isNothing $ find (matchTypeMemDecl t) new
    search _ = True

--turn definitions into member declarations
sig :: [MemberDefinition] -> [MemberDeclaration]
sig = map f
  where
    f (TypeMemDefn t ty) = TypeMemDecl Material t EQQ ty
    f (ValDefn v ty _) = ValDecl v ty
    f (DefDefn meth args ty _) = DefDecl meth args ty

--filter for only the type members and turn them into refinements
ref :: [MemberDeclaration] -> [Refinement]
ref [] = []
ref (TypeMemDecl _ t b ty : xs) = RefineDecl t b ty : ref xs
ref (_ : xs) = ref xs

--check that f is true for all zipped pairs
checkPairwise :: Monad m => (a -> a -> m Bool) -> [a] -> [a] -> m Bool
checkPairwise f as bs = allM (uncurry f) (zip as bs)

--check that for all b in bs, there exists an a such that (f a b) is true
checkPerm :: Monad m => (a -> a -> m Bool) -> [a] -> [a] -> m Bool
checkPerm f as bs = allM (\b -> anyM (flip f b) as) bs

checkPermDual :: Monad m => (a -> a -> m Bool) -> [a] -> [a] -> m Bool
checkPermDual f as bs = checkPerm f as bs &&^ checkPerm f bs as

--substitution
--substitute PATH for BINDING (p/x) in [path/type/member decl]
class Substitute a where
  subst :: Path -> Binding -> a -> a

instance Substitute Path where
  subst p x e = case e of
    Var b -> if b == x then p else Var b
    Field fp fn -> Field (subst p x fp) fn

instance Substitute Type where
  subst p x (Type b rs) = Type (subst p x b) (map (subst p x) rs)

instance Substitute BaseType where
  subst p x base = case base of
    PathType p' t -> PathType (subst p x p') t
    _ -> base

instance Substitute MemberDeclaration where
  subst p x d = case d of
    TypeMemDecl ta b bound ty -> TypeMemDecl ta b bound (subst p x ty)
    ValDecl b ty -> ValDecl b (subst p x ty)
    DefDecl b args retTy -> DefDecl b (map (\(Arg bi t) -> Arg bi (subst p x t)) args) (subst p x retTy)

instance Substitute MemberDefinition where
  subst p x d = case d of
    TypeMemDefn n t -> TypeMemDefn n (subst p x t)
    ValDefn n t e -> ValDefn n (subst p x t) (subst p x e)
    DefDefn n as t e -> DefDefn n as (subst p x t) (subst p x e)

instance Substitute Refinement where
  subst p x (RefineDecl t bound ty) = RefineDecl t bound (subst p x ty)

instance Substitute Expr where
  subst p x e = case e of
    PathExpr p' -> PathExpr $ subst p x p'
    Call p1 f args -> Call (subst p x p1) f (subst p x args)
    New t b ds -> New (subst p x t) b (subst p x ds)
    Let b t e1 e2 -> Let b (subst p x t) (subst p x e1) (subst p x e2)
    TopLit -> e
    UndefLit -> e
    Assert b t1 t2 -> Assert b (subst p x t1) (subst p x t2)


instance (Substitute a) => Substitute [a] where
  subst p x list = map (subst p x) list

instance (Substitute a) => Substitute (Maybe a) where
  subst p x list = fmap (subst p x) list

-- Free variable membership
freeInType :: Binding -> Type -> Bool
freeInType b (Type t rs) = freeInBase b t || any (freeInRef b) rs

freeInBase b (PathType p _) = freeInPath b p
freeInBase b _ = False

freeInPath b (Var b') = b == b'
freeInPath b (Field p _) = freeInPath b p

freeInRef b (RefineDecl _ _ tau) = freeInType b tau