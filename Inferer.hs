import Data.List (intersect, nub, union)
import Lex
import Type

closure :: [Assump] -> SimpleType -> SimpleType
closure g t =
  let newG = [gl | gl <- tv t, not $ elem gl $ concat $ map tv g]
      --newG -> variáveis em t que não ocorrem livres
      s = zip newG $ map TGen [0 ..]
      --aplica as substituições para tipos genéricos
   in apply s t

tiContext g i = if l /= [] then t else error ("Undefined: " ++ i ++ "\n")
  where
    l = dropWhile (\(i' :>: _) -> i /= i') g
    (_ :>: t) = head l

tiExpr :: [Assump] -> Expr -> TI (SimpleType, Subst)
tiExpr g (Lit (LitBool a)) = return (TCon "Bool", [])
tiExpr g (Lit (LitInt a)) = return (TCon "Int", [])
tiExpr g (Var i) = return (tiContext g i, [])
tiExpr g (App e e') = do
  (t, s1) <- tiExpr g e
  (t', s2) <- tiExpr (apply s1 g) e'
  b <- freshVar
  let s3 = unify (apply s2 t) (t' --> b)
  return (apply s3 b, s3 @@ s2 @@ s1)
tiExpr g (Lam i e) = do
  b <- freshVar
  (t, s) <- tiExpr (g /+/ [i :>: b]) e
  return (apply s (b --> t), s)
tiExpr g (Const i) = return (tiContext g i, [])
tiExpr g (If e1 e2 e3) =
  do
    (t1, s1) <- tiExpr g e1
    (t2, s2) <- tiExpr (apply s1 g) e2
    (t3, s3) <- tiExpr (apply (s1 @@ s2) g) e3
    let s4 = unify t1 $ TCon "Bool"
        s5 = unify t2 t3
    return (apply s5 t3, s4 @@ s1 @@ s2 @@ s3 @@ s5)
tiExpr g (Let (i, e1) e2) =
  do
    (t, s1) <- tiExpr g e1
    (t', s2) <- tiExpr (apply s1 (g /+/ [i :>: closure (apply s1 g) t])) e2
    return (t', s1 @@ s2)


--- Examples ---
ex1 = App (Lam "f" $ Lam "x" $ App (Var "f") $ Var "x") (Lam "a" $ Lam "b" $ Var "a")

ex2 = Lam "x" (App (Var "x") (Var "x"))

ex3 = Lam "g" (Lam "f" (Lam "x" (App (Var "g") (App (Var "f") (Var "x")))))

ex4 = Lam "x" (Lam "x" (Var "x"))

ex5 = Lam "w" (Lam "y" (Lam "x" (App (Var "y") (App (App (Var "w") (Var "y")) (Var "x")))))

ex6 = Lam "x" (Lam "y" (Lam "w" (Lam "u" (App (App (Var "x") (Var "w")) (App (App (Var "y") (Var "w")) (Var "u"))))))

infer e = runTI (tiExpr iniCont e)
