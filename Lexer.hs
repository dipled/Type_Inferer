module Lexer where
import Text.Parsec
import Text.Parsec.Language (emptyDef)
import Text.Parsec.Token qualified as L
import Type
import Data.Char


-- -------- Lexical ---------------

lingDef =
  emptyDef
    { L.commentStart = "{-",
      L.commentEnd = "-}",
      L.commentLine = "--",
      L.identStart = letter,
      L.identLetter = letter,
      L.reservedOpNames = ["(,)", "=", "->", "{", "}", ";", "(", ")", ","],
      L.reservedNames = ["True", "False", "if", "then", "else", "case", "let", "in", "of"]
    }

lexical = L.makeTokenParser lingDef

reserved = L.reserved lexical

literalInt = L.integer lexical

symbol = L.symbol lexical

parens = L.parens lexical

op = L.reservedOp lexical

identifier = L.identifier lexical

spacesAndComments = L.whiteSpace lexical
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

patTup :: Parsec String u Pat
patTup = 
  do
    op "("
    e1 <- pat
    op ","
    e2 <- pat
    op ")"
    return $ PCon "(,)" [e1, e2]

patVarCon :: Parsec String u Pat
patVarCon = 
  do
    id@(i : is) <- identifier
    if isLower i then return $ PVar id else do pats <- manyPat; return $ PCon id pats

pat :: Parsec String u Pat
pat =
  do patVarCon
  <|> patLit
  <|> patTup
  

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


-- expr :: Parsec String u Expr
-- expr = chainl1 parseNonApp $ return $ App -- Já trata a aplicação de expressões
expr :: Parsec String u Expr
expr = chainl1 (between spacesAndComments spacesAndComments parseNonApp) $ return App



varConstr :: Parsec String u Expr
varConstr = 
  do
    id@(i : is) <- identifier
    if isLower i then return $ Var id else return $ Const id

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
    
-- leftRec :: (Stream s m t)
        -- => ParsecT s u m a -> ParsecT s u m (a -> a) -> ParsecT s u m a


lamAbs :: Parsec String u Expr
lamAbs = 
  do
    symbol "\\"
    i <- identifier
    symbol "."
    e <- expr
    return $ Lam i e

tup :: Parsec String u Expr
tup = 
  do
    op "("
    e1 <- expr
    op ","
    e2 <- expr
    op ")"
    return $ App (App (Const "(,)") e1) e2 


parseNonApp :: Parsec String u Expr
parseNonApp =
    try tup
    <|> parens expr     -- (E)
    <|> ifExpr      -- if b then e1 else e2
    <|> lamAbs      -- \x.E
    <|> literal     -- True
    <|> letExpr     -- let id = e1 in e2
    <|> caseExpr    -- case e1 of {p -> e2}
    <|> varConstr




-- unexpected emite mensagem de erro