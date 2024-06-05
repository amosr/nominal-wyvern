module Parser where

import Text.ParserCombinators.Parsec
import Text.ParserCombinators.Parsec.Language
import qualified Text.ParserCombinators.Parsec.Token as Token
import RawSyntax

languageDef =
    emptyDef { Token.commentStart   = "/*"
             , Token.commentEnd     = "*/"
             , Token.commentLine    = "//"
             , Token.identStart     = letter
             , Token.identLetter    = alphaNum <|> char '_'
             , Token.reservedNames  = [ "name", "val", "def", "type", "new", "subtype", "let", "in", "Top", "Bot", "undefined", "@shape", "assert", "assertNot"]
            , Token.reservedOpNames = [ "=", "<=", "=", ">=", "+", ".", ":", ",", "{", "}", "=>", "<:"]
    }
              
lexer = Token.makeTokenParser languageDef

identifier = Token.identifier lexer <?> "identifier"
reserved   = Token.reserved lexer
resOp      = Token.reservedOp lexer
parens     = Token.parens lexer
braces     = Token.braces lexer
integer    = Token.integer lexer
whiteSpace = Token.whiteSpace lexer
dot        = Token.reservedOp lexer "."
colon      = Token.reservedOp lexer ":"
comma      = Token.reservedOp lexer ","

--parser definition
parseFile = parse parseProgram ""
parseProgram :: Parser Program
parseProgram = whiteSpace >> parseProgram' <* eof
    where parseProgram' = Program <$> many tlDecl <*> expr

annot (Just _) = Shape
annot Nothing  = Material
typeAnnot = annot <$> optionMaybe (reserved "@shape")
--top-level declarations
tlDecl = (nameDecl <|> subtypeDecl) <?> "top-level declaration"
  where nameDecl = NameDecl <$> typeAnnot
                            <*  reserved "name"
                            <*> identifier
                            <*  resOp "{" 
                            <*> identifier <* resOp "=>"
                            <*> many memberDecl
                            <*  resOp "}"
        subtypeDecl = SubtypeDecl <$  reserved "subtype"
                                  <*> ty
                                  <*  resOp "<:"
                                  <*> basetype
--member declarations
memberDecl = (typeMemDecl <|> valDecl <|> defDecl) <?> "member declaration"
  where typeMemDecl = TypeMemDecl <$> typeAnnot
                                  <*  reserved "type"
                                  <*> identifier
                                  <*> bound
                                  <*> ty
        valDecl = ValDecl <$  reserved "val"
                          <*> identifier
                          <*  colon
                          <*> ty
        defDecl = DefDecl <$  reserved "def"
                          <*> identifier
                          <*> parens (((,) <$> identifier <* colon <*> ty) `sepBy` comma)
                          <*  colon
                          <*> ty

--definitions
defn :: Parser MemberDefinition
defn = (fieldDefn <|> defDefn <|> typeDefn) <?> "member definition"
  where fieldDefn = ValDefn <$  reserved "val"
                            <*> identifier
                            <*  colon
                            <*> ty
                            <*  resOp "="
                            <*> expr
        defDefn = DefDefn <$  reserved "def"
                          <*> identifier
                          <*> parens (((,) <$> identifier <* colon <*> ty) `sepBy` comma)
                          <*  colon
                          <*> ty
                          <*> braces expr
        typeDefn = TypeMemDefn <$  reserved "type"
                               <*> identifier
                               <*  resOp "="
                               <*> ty

--refinements
refine = RefineDecl <$  reserved "type"
                    <*> identifier
                    <*> bound
                    <*> ty

--expressions
path :: Parser Path
path = chainl1 (Var <$> identifier) ((\p (Var f) -> Field p f) <$ dot)

expr = (callOrPath
   <|> primaryNonPath
   <|> letexpr
   <|> assert
   <|> assertNot) <?> "expression"

callOrPath = do
  p <- path <?> "variable or dot-separated path"
  c <- optionMaybe (parens (path `sepBy` comma) <?> "method call")
  case (p, c) of
    (Field p t, Just args) -> return (Call p t args)
    (Var x, Just _) -> error ("cannot call non-method variable " ++ show x)
    (_, Nothing) -> return (PathExpr p)

primaryNonPath =
          TopLit <$ reserved "Top"
      <|> UndefLit <$ reserved "undefined"
      <|> (IntLit . fromIntegral) <$> integer
      <|> new
      <|> parens expr
  where new = New <$  reserved "new" 
                  <*> ty
                  <*  resOp "{"
                  <*> identifier <* resOp "=>"
                  <*> many defn
                  <*  resOp "}"
letexpr = Let <$  reserved "let"
              <*> identifier
              <*> optTyAnnot
              <*  resOp "="
              <*> expr
              <*  reserved "in"
              <*> expr
optTyAnnot = optionMaybe (colon *> ty)

assert = Assert True <$  reserved "assert"
                     <*> ty
                     <*  resOp "<:"
                     <*> ty

assertNot = Assert False <$  reserved "assertNot"
                         <*> ty
                         <*  resOp "<:"
                         <*> ty

--types
ty = do
  bt <- basetype
  -- XXX: try: try produces bad error messages, but the braces here create ambiguity with the `new T { this => defs }` syntax
  rs <- optionMaybe (try (braces ((refine `sepBy` comma) <?> "comma-separated type definitions") <?> "type refinement"))
  case rs of
    Nothing -> return (Type bt [])
    Just rs' -> return (Type bt rs')

basetype = TopType    <$ reserved "Top"
       <|> BotType    <$ reserved "Bot"
       <|> nameOrPath <$> path
  where nameOrPath (Var n) = NamedType n
        nameOrPath (Field p t) = PathType p t

bound :: Parser Bound
bound = LEQ <$ resOp "<="
    <|> EQQ <$ resOp "="
    <|> GEQ <$ resOp ">="
