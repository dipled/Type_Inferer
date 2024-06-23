module Type where
import Debug.Trace
import Data.List (intersect, nub, union)

type Index = Int

type Id = String

data TI a = TI (Index -> (a, Index))

type Subst = [(Id, SimpleType)]

data Pat
  = PVar Id
  | PLit Literal
  | PCon Id [Pat]
  deriving (Eq, Show)

data Literal = LitInt Integer | LitBool Bool
  deriving (Show, Eq)

data Expr
  = Var Id
  | Const Id
  | App Expr Expr
  | Lam Id Expr
  | Lit Literal
  | If Expr Expr Expr
  | Case Expr [(Pat, Expr)]
  | Let (Id, Expr) Expr
  deriving (Eq, Show)

data SimpleType
  = TVar Id
  | TArr SimpleType SimpleType
  | TCon String
  | TApp SimpleType SimpleType
  | TGen Int
  deriving (Eq)

data Assump = Id :>: SimpleType deriving (Eq, Show)

iniCont = ["(,)" :>: (TArr (TGen 0) (TArr (TGen 1) (TApp (TApp (TCon "(,)") (TGen 0)) (TGen 1)))), "True" :>: (TCon "Bool"), "False" :>: (TCon "Bool")]

instance Show SimpleType where
  show (TApp (TApp (TCon "(,)") a) b) = "(" ++ show a ++ ", " ++ show b ++ ")"
  show (TApp a b) = show a ++ " " ++ show b
  show (TVar i) = i
  show (TArr (TVar i) t) = i ++ " -> " ++ show t
  show (TArr (TCon i) t) = i ++ " -> " ++ show t
  show (TArr t t') = "(" ++ show t ++ ")" ++ "->" ++ show t'
  show (TCon a) = a
  show (TGen a) = "a" ++ show a

--------------------------
instance Functor TI where
  fmap f (TI m) = TI (\e -> let (a, e') = m e in (f a, e'))

instance Applicative TI where
  pure a = TI (\e -> (a, e))
  TI fs <*> TI vs = TI (\e -> let (f, e') = fs e; (a, e'') = vs e' in (f a, e''))

instance Monad TI where
  --   return x = TI (\e -> (x, e))
  TI m >>= f = TI (\e -> let (a, e') = m e; TI fa = f a in fa e')

freshVar :: TI SimpleType
freshVar = TI (\e -> let v = "t" ++ show e in (TVar v, e + 1))

freshVarList :: Int -> TI [SimpleType]
freshVarList m = if m < 0 then return [] else  freshVar >>= \t -> freshVarList (m - 1) >>= \ts -> return (t : ts)

maxT :: Int -> SimpleType -> Int
maxT n (TArr t1 t2) = maxT (maxT n t1) t2
maxT n (TApp t1 t2) = maxT (maxT n t1) t2
maxT n (TGen i)     = max n i
maxT n _            = n

instantiate t = 
  do 
    let m = maxT (-1) t
    ts <- freshVarList m
    return (go ts t)
    where 
      go :: [SimpleType] -> SimpleType -> SimpleType
      go ts (TArr l r) = TArr (go ts l) (go ts r)
      go ts (TApp l r) = TApp (go ts l) (go ts r)
      go ts (TGen i)  = go' ts i
        where 
          go' :: [SimpleType] -> Int -> SimpleType
          go' (h : t) 0 = h
          go' (h : t) n = go' t $ n - 1
          go' [] 0 = error "Index too large"
      go ts t         = t  
    

runTI (TI m) = let (t, _) = m 0 in t

----------------------------
t --> t' = TArr t t'

infixr 4 @@

(@@) :: Subst -> Subst -> Subst
s1 @@ s2 = [(u, apply s1 t) | (u, t) <- s2] ++ s1

dom = map (\(i :>: _) -> i)

as /+/ as' = as' ++ filter (compl) as
  where
    is = dom as' -- ids
    compl (i :>: _) = notElem i is

----------------------------
genVariables :: SimpleType -> [String]

genVariables (TGen i) = ["a" ++ show i]
genVariables (TApp l r) = union (genVariables l) (genVariables r)
genVariables (TArr l r) = union (genVariables l) (genVariables r)
genVariables (TVar i) = []
genVariables (TCon i) = []



class Subs t where
  apply :: Subst -> t -> t
  ftv :: t -> [Id] -- free type variables EU ACHO (foi o cristiano que fez isso e tava "tv" antes, mas pelo código parece ser free type variables)

instance Subs SimpleType where
  apply s (TVar u) =
    case lookup u s of
      Just t -> t
      Nothing -> TVar u
  apply s (TArr l r) = (TArr (apply s l) (apply s r))
  apply s (TApp l r) = (TApp (apply s l) (apply s r))
  apply s (TCon u) =
    case lookup u s of
      Just t -> t
      Nothing -> TCon u
  apply s (TGen g) =
    case lookup ("a" ++ show g) s of
      Just t -> t
      Nothing -> TGen g

  ftv (TVar u) = [u]
  ftv (TArr l r) = ftv l `union` ftv r
  ftv (TApp l r) = ftv l `union` ftv r
  ftv (TCon u) = [u]
  ftv (TGen i) = []

instance (Subs a) => Subs [a] where
  apply s = map $ apply s
  ftv = nub . concat . map ftv

instance Subs Assump where
  apply s (i :>: t) = i :>: apply s t
  ftv (i :>: t) = ftv t

------------------------------------
varBind :: Id -> SimpleType -> Maybe Subst
varBind u t
  | t == TVar u = Just []
  | t == TCon u = Just []
  | u `elem` ftv t = Nothing
  | otherwise = Just [(u, t)]

mgu :: (SimpleType, SimpleType) -> Maybe Subst

-- mgu (TGen i, t) = if ("a" ++ show i) `notElem` (genVariables t) then Just [("a" ++ show i, t)] else Nothing
-- mgu (t, TGen i) = if ("a" ++ show i) `notElem` (genVariables t) then Just [("a" ++ show i, t)] else Nothing
mgu (TApp l r, TApp l' r') =
  do
    s1 <- mgu (l, l')
    s2 <- mgu ((apply s1 r), (apply s1 r'))
    return (s2 @@ s1) 
mgu (TGen i, TGen i') = Just [("a" ++ show i, TGen i')]
mgu (TGen i, t) = Just [] --if ("a" ++ show i) `notElem` (genVariables t) then Just [("a" ++ show i, t)] else Nothing
mgu (t, TGen i) = Just [] --if ("a" ++ show i) `notElem` (genVariables t) then Just [("a" ++ show i, t)] else Nothing
mgu (TArr l r, TArr l' r') =
  do
    s1 <- mgu (l, l')
    s2 <- mgu ((apply s1 r), (apply s1 r'))
    return (s2 @@ s1)
mgu (t, TVar u) = varBind u t
mgu (TVar u, t) = varBind u t
mgu (TCon a, TCon b)
  | a == b = Just []
  | otherwise = Nothing
mgu (t, TCon u) = Nothing
mgu (TCon u, t) = Nothing

unify :: SimpleType -> SimpleType -> Subst
unify t t' = case mgu (t, t') of
  Nothing ->
    error
      ( "\ntrying to unify:\n"
          ++ (show t)
          ++ "\nand\n"
          ++ (show t')
          ++ "\n"
      )
  Just s -> s
