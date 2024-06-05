-- Material/shape separation datatypes
{-# LANGUAGE FlexibleContexts, ConstraintKinds #-}
module Separation.Base where

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

--For clarity, PTypes are the nodes in the type graph
--They are like base types, but all path types/type members are given "absolute paths",
--such as A.S or A.B.T rather than z.S or z.b.T
data PType
  = PTop
  | PBot
  | PVar Binding
  | PPath PType Name
  deriving (Eq, Ord)

instance Show PType where
  show PTop        = "Top"
  show PBot        = "Bot"
  show (PVar b)    = show b
  show (PPath p n) = printf "%s::%s" (show p) n

type PCtx = Map.Map PType TypeAnnot

type TGMonad = WriterT [Edge] (ReaderT Context (ReaderT PCtx (Except String)))

mapTAs :: [TopLevelDeclaration] -> Writer [(PType,TypeAnnot)] ()
mapTAs = mapM_ f
  where f (NameDecl ta n _ decls) = do
          tell [(PVar n,ta)]
          mapM_ (g n) decls
        f (SubtypeDecl _ _) = return ()
        g n (TypeMemDecl ta t _ _) = tell [(PPath (PVar n) t,ta)]
        g n _ = return ()

runTG :: Context -> Program -> TGMonad () -> Either String [Edge]
runTG ctx (Program decls _) m = runExcept (
                  runReaderT (
                    runReaderT (
                      execWriterT m
                    ) (turnSubtypingOff $ appendTopLevel decls ctx)
                  ) (Map.fromList (execWriter (mapTAs decls)))
                )

data Edge = Edge {
              from  :: PType
            , label :: [(PType,TypeAnnot)]
            , to    :: PType
            }
  deriving (Show)

getPType :: BaseType -> TGMonad (PType,TypeAnnot)
getPType b = do
  pt <- convert b
  ta <- lookupPType pt
  return (pt,ta)
  where convert :: BaseType -> TGMonad PType
        convert b = case b of
          TopType      -> return PTop
          BotType      -> return PBot
          NamedType n  -> return (PVar n)
          PathType p t -> do
            Type b' _ <- typecheckPathSingleton p
            pt <- convert b'
            return (PPath pt t)

lookupPType :: PType -> TGMonad TypeAnnot
lookupPType pt = do
  pctx <- (lift.lift) ask
  case Map.lookup pt pctx of
    Just x  -> return x
    Nothing -> return Material

-- Material shape separation:
-- (1) A shape is never used as part of a lower bound syntactically (i.e. after ≥ or =).
-- (2) The upper bound of a shape is always a shape, and named shapes can only subtype named shapes.
-- (3) Shapes cannot be refined in refinements.

--check condition (3), that no shapes appear in the refinements of any type
checkTy :: Type -> TGMonad ()
checkTy (Type _ rs) = mapM_ check rs
  where check (RefineDecl _ _ (Type bt rt)) = do
          (bt',btTA) <- getPType bt
          -- XXX: CHANGE FROM PAPER: this disallows shapes altogether, even if they are not refined (rt = []). Bug or intentional?
          case btTA of
            Shape    -> invalidShape bt
            Material -> return ()
          mapM_ check rt
        invalidShape shape = throwError $ printf "invalid shape usage: shape type %s used in refinement" (show shape)
