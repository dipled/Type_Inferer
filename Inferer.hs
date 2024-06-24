import Lexer
import Type
import Distribution.Utils.Generic (fstOf3, sndOf3)
import Debug.Trace

tiContext g i = if l /= [] then instantiate t else error ("Undefined Term: " ++ i ++ "\n")
  where
    l = dropWhile (\(i' :>: _) -> i /= i') g
    (_ :>: t) = head l
    unqt = instantiate t

tiExpr :: [Assump] -> Expr -> TI (SimpleType, Subst)
tiExpr g (Lit (LitBool a)) = return (TCon "Bool", []) 
tiExpr g (Lit (LitInt a)) = return (TCon "Int", [])
tiExpr g (Var i) = do t <- tiContext g i; return (t, []) -- Busca "i" no contexto
tiExpr g (App e e') = do
  (t, s1) <- tiExpr g e 
  (t', s2) <- tiExpr (apply s1 g) e'
  b <- freshVar
  let s3 = unify (apply s2 t) (t' --> b)
  return (apply s3 b, s3 @@ s2 @@ s1)
tiExpr g (Lam i e) = do
  b <- freshVar
  (t, s) <- tiExpr (g /+/ [i :>: b]) e
  nt <- instantiate (apply s (b --> t))
  return (apply s nt, s)
tiExpr g (Const i) = do t <- tiContext g i; return (t, [])
tiExpr g (If e1 e2 e3) =
  do
    (t1, s1) <- tiExpr g e1
    (t2, s2) <- tiExpr (apply s1 g) e2
    (t3, s3) <- tiExpr (apply (s2 @@ s1) g) e3
    let s4 = unify t1 $ TCon "Bool"
        s5 = unify (apply s4 t2) (apply s4 t3)
    return (apply s5 t3, s5 @@ s4 @@ s3 @@ s2 @@ s1)
tiExpr g (Let (i, e1) e2) =
  do
    (t, s1) <- tiExpr g e1
    (t', s2) <- tiExpr (apply s1 (g /+/ [i :>: generalize (apply s1 g) t])) e2
    return (t', s2 @@ s1)
tiExpr g (Case e p) = 
  do
    (t, s) <- tiExpr g e
    (t1, g', s1) <- unifyExprPat (apply s g) t (map fst p)
    (t2, s2) <- caseExprs ((apply $ s1 @@ s) g) (map (apply $ s1 @@ s) g') (map snd p)
    return (t2, s2 @@ s1 @@ s)


tiExprGen :: [Assump] -> Expr -> TI (SimpleType, Subst)
tiExprGen g e = tiExpr g e >>= \(t, s) -> return (generalize g (apply s t), s)

getN :: SimpleType -> SimpleType
getN (TArr l r) = getN r
getN t = t 


pats :: [Assump] -> [Pat] -> TI[(SimpleType, [Assump], [(Id, SimpleType)])]
pats g [] = return []
pats g (x : xs) = 
  do
    t <- tiPat g x
    let t' = fstOf3 t
    fmap (t :) (pats g xs)

                      
arrow :: [SimpleType] -> SimpleType -> SimpleType
arrow [] t = t  
arrow (x : xs) (TArr l r) = TArr x $ arrow xs r
arrow (x : xs) t = TArr x $ arrow xs t


tiPat :: [Assump] -> Pat -> TI (SimpleType, [Assump], [(Id, SimpleType)])
tiPat g (PVar i) = 
  do 
    b <- freshVar
    return (b, g /+/ [i :>: b], [])
tiPat g (PLit l) = case l of LitBool b -> return (TCon "Bool", g, []); LitInt i -> return (TCon "Int", g, [])
tiPat g pp@(PCon i p) = 
  do

    t  <- tiContext g i
    t' <- instantiate t
    ts <- pats g p 
    let ts'  = map fstOf3 ts
        ts'' = arrow ts' t
        g'   = concat (map sndOf3 ts)
        s    = unify t' ts''
        t''  = getN t'
    return (apply s t'', g', s)

tiExprs :: [Assump] -> [[Assump]] -> SimpleType -> [Expr] -> TI (SimpleType, [(Id, SimpleType)])
tiExprs g l t [] = return (t, [])
tiExprs g l@(a : as) t (x : xs) = 
  do
    (t', s1) <- tiExpr (g /+/ a) x
    let s = unify t' t
    (t'', s2) <- tiExprs (apply (s1 @@ s) g) as (apply (s1 @@ s) t) xs
    return (t'', s2 @@ s1 @@ s)

caseExprs :: [Assump] -> [[Assump]] -> [Expr] -> TI (SimpleType, Subst)
caseExprs g l@(a : as) (x : xs) = 
  do
    (t, s) <- tiExpr (g /+/ a) x
    (t', s1) <- tiExprs (apply s g) as t xs
    return (t, s1 @@ s) 

unifyExprPat :: [Assump] -> SimpleType -> [Pat] -> TI (SimpleType, [[Assump]], Subst)
unifyExprPat g t [] = return (t, [], [])
unifyExprPat g t (x : xs) = 
  do 
    (t', g', s1) <- tiPat g x
    let s = unify t' t
    (t'', g'', s2) <- unifyExprPat (apply (s @@ s1) g) (apply (s @@ s1) t) xs
    return (apply s2 t, g': g'', s2 @@ s1 @@ s)

--- Examples ---
ex1 = App (Lam "f" $ Lam "x" $ App (Var "f") $ Var "x") (Lam "a" $ Lam "b" $ Var "a")

ex2 = Lam "x" (App (Var "x") (Var "x"))

ex3 = Lam "g" (Lam "f" (Lam "x" (App (Var "g") (App (Var "f") (Var "x")))))

ex4 = Lam "x" (Var "x")

ex5 = Lam "w" (Lam "y" (Lam "x" (App (Var "y") (App (App (Var "w") (Var "y")) (Var "x")))))

ex6 = Lam "x" (Lam "y" (Lam "w" (Lam "u" (App (App (Var "x") (Var "w")) (App (App (Var "y") (Var "w")) (Var "u"))))))

ex7 = Lam "p" (Lam "q" (App (App (Var "p") (Var "q")) (Lam "a" (Lam "b" (Var "b")))))

ex8 = Lam "x" (App (Var "x") (Var "x"))



infer e = runTI (tiExprGen iniCont e)

parseLambda s = case parseExpr s of
                     Left er -> print er
                     Right e -> putStrLn ("\n\nExpression:\n" ++ show e ++ "\n\n") 
                                >> putStrLn ("Type:\n" ++ (show $ infer e))
main = do
  e <- readFile "test.txt"
  parseLambda e
