{-# LANGUAGE FlexibleContexts, ConstraintKinds #-}
module TypeUtil where

import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.Extra
import Data.List (find)
import Data.Maybe (isNothing)
import Syntax
import PrettyPrint
import Text.Printf
import Data.Functor.Identity

instance MonadFail Data.Functor.Identity.Identity where
  fail = error "monad pattern match fail"

data CheckSubtype = On | Off
data Context = Context
  { toplevel :: [TopLevelDeclaration]
  , gamma    :: [(Binding,Type)]
  , isCheck  :: CheckSubtype
  }
emptyCtx = Context [] [] On
appendTopLevel :: [TopLevelDeclaration] -> Context -> Context
appendTopLevel ds (Context t g c) = Context (ds++t) g c
appendGamma :: [(Binding,Type)] -> Context -> Context
appendGamma ds (Context t g c) = Context t (ds++g) c
turnSubtypingOff :: Context -> Context
turnSubtypingOff (Context t g _) = Context t g Off
type TC m = (MonadReader Context m, MonadError String m, MonadFail m)

assert :: TC m => String -> Bool -> m ()
assert _   True  = return ()
assert err False = throwError err

assertSub :: TC m => String -> Bool -> m ()
assertSub err b = do
  ctx <- ask
  case (isCheck ctx) of
    On -> assert err b
    Off -> return ()

lookupMemberDecls :: TC m => (MemberDeclaration -> Bool) -> String -> [MemberDeclaration] -> m MemberDeclaration
lookupMemberDecls pred msg list =
  case find pred list of
    Just x  -> return x
    Nothing -> throwError msg

lookupGamma' :: TC m => Binding -> m Type
lookupGamma' v = do
  search <- reader (lookup v . gamma)
  case search of
    Just x  -> return x
    Nothing -> throwError (printf "failed to lookup variable %s" (show v))

lookupGamma :: TC m => Binding -> m Type
lookupGamma v = do
  search <- reader (lookup v . gamma) 
  case search of
    Just x  -> return x
    Nothing -> throwError (printf "failed to lookup variable %s" (show v))
lookupTLDecls :: TC m => (TopLevelDeclaration -> Bool) -> String -> m TopLevelDeclaration
lookupTLDecls pred msg = do
  search <- reader (find pred . toplevel)
  case search of
    Just x  -> return x
    Nothing -> throwError msg

searchTLDecls :: TC m => (TopLevelDeclaration -> m Bool) -> m Bool
searchTLDecls pred = do
  tldecls <- reader toplevel
  anyM pred tldecls
----------------------------------
theTop = Type TopType []
theBot = Type BotType  []
makeNomType s = Type (NamedType s) []

sameName :: Binding -> Binding -> Bool
sameName b1 b2 = name b1 == name b2

argToTup :: Arg -> (Binding,Type)
argToTup (Arg v ty) = (v,ty)

refToDecl :: Refinement -> MemberDeclaration
refToDecl (RefineDecl t bound ty) = TypeMemDecl Material t bound ty

matchRef :: Refinement -> Refinement -> Bool
matchRef (RefineDecl t1 _ _) (RefineDecl t2 _ _) = t1 == t2

mergeRefs :: [Refinement] -> [Refinement] -> [Refinement]
mergeRefs new old = new ++ old'
  where old'     = filter search old
        search x = isNothing $ find (matchRef x) new

merge :: Type -> [Refinement] -> Type
merge (Type base rs) rs' = Type base (mergeRefs rs' rs)

--turn definitions into member declarations
sig :: [MemberDefinition] -> [MemberDeclaration]
sig = map f
  where f (TypeMemDefn t ty) = TypeMemDecl Material t EQQ ty
        f (ValDefn v ty _) = ValDecl v ty
        f (DefDefn meth args ty _) = DefDecl meth args ty
--filter for only the type members and turn them into refinements
ref :: [MemberDeclaration] -> [Refinement]
ref [] = []
ref (TypeMemDecl _ t b ty:xs) = RefineDecl t b ty:ref xs
ref (_:xs) = ref xs

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
    _             -> base

instance Substitute MemberDeclaration where
  subst p x d = case d of
    TypeMemDecl ta b bound ty -> TypeMemDecl ta b bound (subst p x ty)
    ValDecl b ty          -> ValDecl b (subst p x ty)
    DefDecl b args retTy  -> DefDecl b (map (\(Arg bi t) -> Arg bi (subst p x t)) args) (subst p x retTy)

instance Substitute Refinement where
  subst p x (RefineDecl t bound ty) = RefineDecl t bound (subst p x ty)

instance (Substitute a) => Substitute [a] where
  subst p x list = map (subst p x) list 
