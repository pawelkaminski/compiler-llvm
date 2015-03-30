module AbsLatte where

-- Haskell module generated by the BNF converter


newtype Ident = Ident String deriving (Eq,Ord,Show)
data Program =
   Program [TopDef]
  deriving (Eq,Ord,Show)

data TopDef =
   FnDef Type Ident [Arg] Block
 | ClassDefPure Ident ClassBlock
 | ClassDefChild Ident Ident ClassBlock
  deriving (Eq,Ord,Show)

data Arg =
   Arg Type Ident
  deriving (Eq,Ord,Show)

data Block =
   Block [Stmt]
  deriving (Eq,Ord,Show)

data Stmt =
   Empty
 | BStmt Block
 | Decl Type [Item]
 | AssPure [Ident] Expr
 | Incr [Ident]
 | Decr [Ident]
 | Ret Expr
 | VRet
 | Cond Expr Stmt
 | CondElse Expr Stmt Stmt
 | While Expr Stmt
 | SExp Expr
  deriving (Eq,Ord,Show)

data Item =
   NoInit Ident
 | Init Ident Expr
  deriving (Eq,Ord,Show)

data ClassBlock =
   ClassBlock [ClassStmt]
  deriving (Eq,Ord,Show)

data ClassStmt =
   ClassEmpty
 | MethodDef Type Ident [Arg] Block
 | ClassDecl Type [ClassItem]
  deriving (Eq,Ord,Show)

data ClassItem =
   ClassVarInit Ident
  deriving (Eq,Ord,Show)

data Type =
   PureType PureType
 | Fun Type [Type]
  deriving (Eq,Ord,Show)

data PureType =
   Int
 | Str
 | Bool
 | Void
 | Class Ident
  deriving (Eq,Ord,Show)

data Expr =
   EVar Expr [Ident]
 | EVarPure [Ident]
 | ELitInt Integer
 | EString String
 | ELitTrue
 | ELitFalse
 | ELitCall
 | ENewObj PureType
 | EApp Expr Ident [Expr]
 | EAppObj Expr Ident [Expr] Expr
 | EAppPure [Ident] [Expr]
 | EAppPureObj [Ident] [Expr] Expr
 | Ecast Expr Expr
 | Neg Expr
 | Not Expr
 | EMul Expr MulOp Expr
 | EAdd Expr AddOp Expr
 | ERel Expr RelOp Expr
 | EAnd Expr Expr
 | EOr Expr Expr
  deriving (Eq,Ord,Show)

data AddOp =
   Plus
 | Minus
  deriving (Eq,Ord,Show)

data MulOp =
   Times
 | Div
 | Mod
  deriving (Eq,Ord,Show)

data RelOp =
   LTH
 | LE
 | GTH
 | GE
 | EQU
 | NE
  deriving (Eq,Ord,Show)

