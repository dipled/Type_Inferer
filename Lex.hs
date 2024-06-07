{- 

  DIFERENCIAR MAÍUSCULA DE MINÚSCULA CONSTRUTOR VARIÁVEL ETC em 3 lugares diferentes
  Construtor e Tupla na gramática da linguagem da Expr e Pat
 -}

module Lex where
import Text.Parsec
import Text.Parsec.Language (emptyDef)
import Text.Parsec.Token qualified as L
import Type


-- -------- Lexical ---------------

lingDef =
  emptyDef
    { L.commentStart = "{-",
      L.commentEnd = "-}",
      L.commentLine = "--",
      L.identStart = letter,
      L.identLetter = letter,
      L.reservedOpNames = ["(,)", "=", "->", "{", "}", ";"],
      L.reservedNames = ["True", "False", "if", "then", "else", "case", "let", "in", "of"]
    }

lexical = L.makeTokenParser lingDef

reserved = L.reserved lexical

literalInt = L.integer lexical

symbol = L.symbol lexical

parens = L.parens lexical

op = L.reservedOp lexical

identifier = L.identifier lexical


-- --------- Parser -----------------
parseExpr = runParser expr [] "lambda-calculus"


patVar :: Parsec String u Pat
patVar = identifier >>= \id -> return $ PVar id

patLit :: Parsec String u Pat
patLit =
  do i <- literalInt; return $ PLit $ LitInt i
  <|> do reserved "True"; return $ PLit $ LitBool True
  <|> do reserved "False"; return $ PLit $ LitBool False

manyPat :: Parsec String u [Pat]
manyPat = 
  try (do p <- pat; ps <- manyPat; return $ p : ps)
  <|> return [] -- Caso de construtor vazio E caso de parada da recursão at the same focking time!!!

patCon :: Parsec String u Pat
patCon = 
  do
    i <- identifier
    pats <- manyPat
    return $ PCon i pats

pat :: Parsec String u Pat
pat =
  do patVar
  <|> patCon -- DIFERENCIAR MAÍUSCULA DE MINÚSCULA CONSTRUTOR VARIÁVEL ETC
  <|> patLit
  

manyPatArrow :: Parsec String u [(Pat, Expr)]
manyPatArrow =
  try (do p <- patArrow; op ";"; ps <- manyPatArrow; return $ p : ps)
  <|> do p <- patArrow; return [p]

patArrow :: Parsec String u (Pat, Expr)
patArrow = 
  do
    p <- pat
    op "->"
    e <- expr
    return (p, e)


expr :: Parsec String u Expr
expr = chainl1 parseNonApp $ return $ App -- Já trata a aplicação de expressões
-- expr :: Parsec String u Expr
-- expr = chainl1 (between spaces spaces parseNonApp) $ return $ App



constr :: Parsec String u Expr
constr = do id <- identifier; return $ Const id

var :: Parsec String u Expr
var = do is <- identifier; return $ Var is

-- var :: Parsec String u Expr
-- var = do is <- lower; i <- identifier; return $ Var $ is : i


literal :: Parsec String u Expr
literal = 
    do i <- literalInt; return $ Lit $ LitInt i
    <|> do reserved "True"; return $ Lit $ LitBool True
    <|> do reserved "False"; return $ Lit $ LitBool False

ifExpr :: Parsec String u Expr
ifExpr = 
  do
    reserved "if"
    e1 <- expr
    reserved "then"
    e2 <- expr
    reserved "else"
    e3 <- expr
    return $ If e1 e2 e3

letExpr :: Parsec String u Expr
letExpr = 
  do
    reserved "let"
    id <- identifier
    op "="
    e1 <- expr
    reserved "in"
    e2 <- expr
    return $ Let (id, e1) e2

caseExpr :: Parsec String u Expr
caseExpr =
  do
    reserved "case"
    e <- expr
    reserved "of"
    op "{"
    p <- manyPatArrow
    op "}"
    return $ Case e p

lamAbs :: Parsec String u Expr
lamAbs = 
  do
    symbol "\\"
    i <- identifier
    symbol "."
    e <- expr
    return $ Lam i e

parseNonApp :: Parsec String u Expr
parseNonApp =
    parens expr     -- (E)
    <|> ifExpr      -- if b then e1 else e2
    <|> lamAbs      -- \x.E
    <|> literal     -- True
    <|> letExpr     -- let id = e1 in e2
    <|> caseExpr    -- case e1 of {p -> e2}
    <|> var         -- x
    <|> constr

----------------------------------------
-- parseLambda s = case parseExpr s of
--                      Left er -> print er
--                      Right e -> (print e >> print (infer e))
parseLambda = print . parseExpr

main = do
  e <- readFile "test.txt"
  parseLambda e

-- unexpected emite mensagem de erro