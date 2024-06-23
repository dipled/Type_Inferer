import Data.List (intersect, nub, union)
import Lexer
import Type
import Debug.Trace
{-TODO
  Fazer o case
-}



tiContext g i = if l /= [] then instantiate t else error ("Undefined: " ++ i ++ "\n")
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
  t <- instantiate t
  return (apply s (b --> t), s)
tiExpr g (Const i) = do t <- tiContext g i; return (t, [])
tiExpr g (If e1 e2 e3) =
  do
    (t1, s1) <- tiExpr g e1
    (t2, s2) <- tiExpr (apply s1 g) e2
    (t3, s3) <- tiExpr (apply (s1 @@ s2) g) e3
    let s4 = unify t1 $ TCon "Bool"
        s5 = unify t2 t3
    return (apply s5 t3, s5 @@ s4 @@ s3 @@ s2 @@ s1)
tiExpr g (Let (i, e1) e2) =
  do
    (t, s1) <- tiExpr g e1
    (t', s2) <- tiExpr (apply s1 (g /+/ [i :>: generalize (apply s1 g) t])) e2
    return (t', s2 @@ s1)
-- tiExpr g (Case e pats) =
--   do
--     (t1, s1) <- tiExpr g e



--- Examples ---
ex1 = App (Lam "f" $ Lam "x" $ App (Var "f") $ Var "x") (Lam "a" $ Lam "b" $ Var "a")

ex2 = Lam "x" (App (Var "x") (Var "x"))

ex3 = Lam "g" (Lam "f" (Lam "x" (App (Var "g") (App (Var "f") (Var "x")))))

ex4 = Lam "x" (Var "x")

ex5 = Lam "w" (Lam "y" (Lam "x" (App (Var "y") (App (App (Var "w") (Var "y")) (Var "x")))))

ex6 = Lam "x" (Lam "y" (Lam "w" (Lam "u" (App (App (Var "x") (Var "w")) (App (App (Var "y") (Var "w")) (Var "u"))))))

ex7 = Lam "p" (Lam "q" (App (App (Var "p") (Var "q")) (Lam "a" (Lam "b" (Var "b")))))

ex8 = Lam "x" (App (Var "x") (Var "x"))



infer e = runTI (tiExpr iniCont e)

parseLambda s = case parseExpr s of
                     Left er -> print er
                     Right e -> (print e >> print (infer e))
main = do
  e <- readFile "test.txt"
  parseLambda e
