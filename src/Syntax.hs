module Syntax where

type Name = String

data Binding = Binding
  { name :: Name
  , idx  :: Int
  }
  deriving (Eq, Ord)

data Arg = Arg
  { argName :: Binding
  , argType :: Type
  }
  deriving (Eq, Ord)

data TypeAnnot = Shape | Material
  deriving (Eq, Ord)

data Program = Program [TopLevelDeclaration] Expr
  deriving (Eq, Ord)

data TopLevelDeclaration
  = NameDecl TypeAnnot Binding Binding [MemberDeclaration]
  | SubtypeDecl Type BaseType
  deriving (Eq, Ord)

data MemberDeclaration
  = TypeMemDecl TypeAnnot Name Bound Type
  | ValDecl Name Type
  | DefDecl Name [Arg] Type
  deriving (Eq, Ord)

data MemberDefinition
  = TypeMemDefn Name Type
  | ValDefn Name Type Expr
  | DefDefn Name [Arg] Type Expr
  deriving (Eq, Ord)

data Refinement = RefineDecl Name Bound Type
  deriving (Eq, Ord)

data Type = Type BaseType [Refinement]
  deriving (Eq, Ord)

data BaseType
  = TopType
  | BotType
  | NamedType Binding
  | PathType Path Name
  deriving (Eq, Ord)

data Path
  = Var Binding
  | Field Path Name
  deriving (Eq, Ord)

data Expr
  = PathExpr Path
  | Call Path Name [Path]
  | New Type Binding [MemberDefinition]
  | Let Binding (Maybe Type) Expr Expr
  | TopLit
  | UndefLit
  | Assert Bool Type Type
  deriving (Eq, Ord)

data Bound = LEQ | EQQ | GEQ
  deriving (Eq, Ord)
