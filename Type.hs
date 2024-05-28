module Type where
import Data.List(nub, intersect, union)


type Index  = Int
type Id     = String
data TI a   = TI (Index -> (a, Index))
type Subst  = [(Id, SimpleType)]



data Pat = PVar Id
    | PLit Literal
    | PCon Id [Pat]
    deriving (Eq, Show)

data Literal = LitInt Integer | LitBool Bool 
    deriving (Show, Eq)

data Expr = Var Id
    | Const Id
    | App Expr Expr
    | Lam Id Expr
    | Lit Literal
    | If Expr Expr Expr
    | Case Expr [(Pat, Expr)]
    | Let (Id, Expr) Expr
    deriving (Eq, Show)

data SimpleType = TVar Id
    | TArr SimpleType SimpleType
    | TCon String
    | TApp SimpleType SimpleType
    | TGen Int
    deriving (Eq, Show)

data Assump = Id :>: SimpleType deriving (Eq, Show)


iniCont = ["(,)" :>: (TArr (TGen 0) (TArr (TGen 1) (TApp (TApp (TCon "(,)") (TGen 0)) (TGen 1)))), "True" :>: (TCon "Bool"), "False" :>: (TCon "Bool")]