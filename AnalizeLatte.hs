module AnalizeLatte where
import System.IO
import System.Environment
import qualified Data.Map as M
import qualified Data.Set as S
import Control.Monad.Error
import Control.Monad.Reader
import Control.Monad.State
import Data.List
import Data.Maybe
import LexLatte
import ParLatte
import AbsLatte
import ErrM
import CommonLatte

{-
First get all function and clases definitons at (stored in state monad)
then gets all functions and clases from state. Adds embeded functions
and check types inside functions and classes blocks, remove emeded functions.
Check if main function exists, changes it llvm identifier and check its type
Returns analize state: clases data, functions data and last used label
-}
analize::[TopDef] -> Execution(Class, Functions, Integer)
analize definitions = do
	getDefinitions definitions
	classes <- gets$getAllClasses
	func <- gets$getAllFunctions
	setEmbededFunctions
	typeAnalizeClasses classes
	typeAnalizeFunctions func
	removeEmbededFunctions
	checkIfMainExists
	(c, f, l) <- gets$getAllClassesFunctionsAndLabel
	return ((c, f, l))

{-
Checks if ident main function exists and is int type, changes its llvm identifier
to main.
-}
checkIfMainExists :: Execution()
checkIfMainExists = do
	v <- gets$getFunction (Ident "main")
	case v of
		Nothing -> runErrorEmptyExec ("main function does not exists.")
		Just (TypeInteger, [], block, _) -> setMainName block
		Just (_) -> runErrorEmptyExec ("main function must be int type and has no parameters.")

{-
Change main fuction llvm identifier
-}
setMainName :: Block -> Execution()
setMainName block = do
	v <- modify$memorySetFunction (Ident "main") TypeInteger [] block "@main"
	return ()

-- ################################ --
-- ##### get Function Helpers ##### --
-- ################################ --

{-
Check if arguments of function passed as list of arguments
repeats and has non void type. Returns list of arguments state
(ident, type, llvm identifier) and list of latte identifiers
-}
getArguments::[Arg] -> Execution([(Ident, AllTypes, Integer)], [Ident])
getArguments [] = return([], [])
getArguments ((Arg types id):r) = do
	typeName <- getType types
	label <- freshLabel
	(v, l) <- getArguments r
	h <- ask
	case find (==id) l of
		Just _ -> do
				liftIO$hPutStr h ("ERROR\n " ++ show(id) ++ " argument is duplicated.\n")
				error("")
		Nothing ->  case typeName of
			TypeVoid -> do
				liftIO$hPutStr h ("ERROR\n Arguments couldn't have void type.\n")
				error("")
			_ -> return((id, typeName, label):v, id:l)

-- #################################### --
-- ##### end get Function Helpers ##### --
-- #################################### --

-- ############################# --
-- ##### get Class Helpers ##### --
-- ############################# --

{-
Gets list attributes (from one line declaration). Checks if variables doesn't repeat.
Returns map of class attributes ~ key latte Ident, value llvm list number, and last used llvm numer (attributes size)
-}
getAtributesMap :: [ClassItem] -> Integer -> Execution((M.Map Ident Integer), Integer)
getAtributesMap [] it = return(M.empty, it)
getAtributesMap ((ClassVarInit name):r) it = do
	(list, newIt) <- getAtributesMap r (it+1)
	case (M.member name list) of
		True -> do
			h <- ask
			liftIO$hPutStr h ("ERROR\n Multiple assign to one attribute name.")
			error("")
		False -> return ((M.insert name it list), newIt)

{-
Gets list attributes (latte Ident, value llvm list number) its types and current class attributes map (Memory).
Checks if variables doesn't repeat. Returns map of attributes (Memory).
-}
checkAndSetAttributes :: [(Ident, Integer)] -> AllTypes -> Memory -> Execution(Memory)
checkAndSetAttributes  [] t m = return(m)

checkAndSetAttributes ((name, it):r) t m = do
	mem <- checkAndSetAttributes r t m
	case M.lookup name mem of
		Just _ -> do
			h <- ask
			liftIO$hPutStr h ("ERROR\n Multiple assign to " ++ show(name) ++ " attribute name.")
			error("")
		Nothing -> return(M.insert name (t, it) mem)


{-
Gets list of class statements.
For each attribute check if it repeats, gives them llvm class identifier, puts them inside attributes Map (Memory).
For each method check if it repeats, check its parameters, give them llvm identifier
and put it inside methods Map(Functions).
Returns map of class methods and attributes.
-}
getAttributesAndMethods::[ClassStmt] -> Integer -> Execution((Functions, Memory))
getAttributesAndMethods [] _ = return (M.empty, M.empty)

getAttributesAndMethods (ClassEmpty:r) iter= do
	v <- getAttributesAndMethods r iter
	return v

-- class methods declarations
getAttributesAndMethods ((MethodDef types name arguments block):r) iter = do
	typeName <- getType types
	(argumentsList, _) <- getArguments arguments
	newBlock <- optimalizeBlock block
	(meth, attr) <- getAttributesAndMethods r iter
	label <- freshLabel
	case M.lookup name meth of
		Just _ -> do
			h <- ask
			liftIO$hPutStr h ("ERROR\n Method " ++ show(name) ++ " duplicates.")
			error("")
		Nothing -> return ((M.insert name (typeName, argumentsList, newBlock, ("@meth"++show(label))) meth), attr)

-- class attribiute declarations
getAttributesAndMethods ((ClassDecl types names):r) iter = do
	typeName <- getType types
	(atributesList, newIter)<- getAtributesMap names iter
	(meth, attr) <- getAttributesAndMethods r newIter
	newattr <- checkAndSetAttributes (M.toList atributesList) typeName attr
	return (meth, newattr)

-- ################################# --
-- ##### end get Class Helpers ##### --
-- ################################# --

-- ################################################################### --
-- ##### optimalization simply variables - functions and methods ##### --
-- ################################################################### --

{-
Gets initial block value and returns modified block.
Modifications at this stage are necessary to pass tests.
-}
optimalizeBlock :: (Block) -> Execution(Block)
optimalizeBlock (Block block) = do
	newBlock <- simplyfyStatement block
	return(Block newBlock)

simplyfyStatement:: [Stmt] -> Execution([Stmt])
simplyfyStatement [] = return([])

simplyfyStatement ((BStmt b):r) = do
	newStmt <- optimalizeBlock b
	rest <- simplyfyStatement r
	return ((BStmt newStmt):rest)

simplyfyStatement ((Ret e):r) = do
	(newExp, _) <- simplyfyExpression e
	rest <- simplyfyStatement r
	return ((Ret newExp):rest)

simplyfyStatement ((Decl t items):r) = do
	newItems <- simplyfyItems items
	rest <- simplyfyStatement r
	return ((Decl t newItems):rest)

simplyfyStatement ((AssPure id e):r) = do
	(newExp, _) <- simplyfyExpression e
	rest <- simplyfyStatement r
	return ((AssPure id newExp):rest)

simplyfyStatement ((SExp e):r) = do
	(newExp, v) <- simplyfyExpression e
	rest <- simplyfyStatement r
	case v of
		Nothing -> return ((SExp newExp):rest)
		Just _ -> return (rest)

{-
remove empty (false) cond statement and (true) parenthes
-}
simplyfyStatement ((Cond e s):r) = do
	(statement:_) <- simplyfyStatement [s]
	(newExp, v) <- simplyfyExpression e
	rest <- simplyfyStatement r
	case v of
		Just (TypeBoolean False) -> return (rest)
		Just (TypeBoolean True) -> return (statement:rest)
		_ -> return ((Cond newExp statement):rest)

{-
remove death condition
-}
simplyfyStatement ((CondElse e s1 s2):r) = do
	(statement1:_) <- simplyfyStatement [s1]
	(statement2:_) <- simplyfyStatement [s2]
	(newExp, v) <- simplyfyExpression e
	rest <- simplyfyStatement r
	case v of
		Just (TypeBoolean False) -> return (statement2:rest)
		Just (TypeBoolean True) -> return (statement1:rest)
		_ -> return ((CondElse newExp statement1 statement2):rest)

{-
remove always falsy while
-}
simplyfyStatement ((While e s):r) = do
	(statement:_) <- simplyfyStatement [s]
	(newExp, v) <- simplyfyExpression e
	rest <- simplyfyStatement r
	case v of
		Just (TypeBoolean False) -> return (rest)
		_ -> return ((While newExp statement):rest)


simplyfyStatement (x:r) = do
	var <- simplyfyStatement r
	return (x:var)

{-
Translate grammar relation operators into haskell one
-}
simplifyRelFunc :: RelOp -> BasicTypesValue -> BasicTypesValue -> Execution( BasicTypesValue)
simplifyRelFunc LTH (TypeInt a) (TypeInt b) = return(TypeBoolean (a<b))
simplifyRelFunc LTH (TypeBoolean a) (TypeBoolean b) = return(TypeBoolean (a<b))
simplifyRelFunc LE (TypeInt a) (TypeInt b) = return(TypeBoolean (a<=b))
simplifyRelFunc LE (TypeBoolean a) (TypeBoolean b) = return(TypeBoolean (a<=b))
simplifyRelFunc GTH (TypeInt a) (TypeInt b) = return(TypeBoolean (a>b))
simplifyRelFunc GTH (TypeBoolean a) (TypeBoolean b) = return(TypeBoolean (a>b))
simplifyRelFunc GE (TypeInt a) (TypeInt b) = return(TypeBoolean (a>=b))
simplifyRelFunc GE (TypeBoolean a) (TypeBoolean b) = return(TypeBoolean (a>=b))
simplifyRelFunc EQU (TypeInt a) (TypeInt b) = return(TypeBoolean (a==b))
simplifyRelFunc EQU (TypeBoolean a) (TypeBoolean b) = return(TypeBoolean (a==b))
simplifyRelFunc NE (TypeInt a) (TypeInt b) = return(TypeBoolean (a/=b))
simplifyRelFunc NE (TypeBoolean a) (TypeBoolean b) = return(TypeBoolean (a/=b))


{-
Translate grammar mul operators into haskell one
-}
simplifyMulFunc :: MulOp -> BasicTypesValue -> BasicTypesValue -> Execution( BasicTypesValue)
simplifyMulFunc Times (TypeInt a) (TypeInt b) = return(TypeInt (a*b))
simplifyMulFunc Div (TypeInt a) (TypeInt b) = return(TypeInt (quot a b))
simplifyMulFunc Mod (TypeInt a) (TypeInt b) = return(TypeInt (a `mod` b))

{-
Translate grammar add operators into haskell one
-}
simplifyAddFunc :: AddOp -> BasicTypesValue -> BasicTypesValue -> Execution( BasicTypesValue)
simplifyAddFunc Plus (TypeInt a) (TypeInt b) = return(TypeInt (a+b))
simplifyAddFunc Minus (TypeInt a) (TypeInt b) = return(TypeInt (a-b))


simplyfyExpressionList :: [Expr] -> Execution([Expr])
simplyfyExpressionList [] = return([])
simplyfyExpressionList (e:r) = do
	(newE, _) <- simplyfyExpression e
	newR <- simplyfyExpressionList r
	return(newE:newR)


{-
Simplifies expressions counts trivial values
-}
simplyfyExpression :: Expr -> Execution((Expr, Maybe BasicTypesValue))

simplyfyExpression (ELitInt v) = return ((ELitInt v), (Just (TypeInt v)))

simplyfyExpression (Neg e) = do
	(newExp, v) <- simplyfyExpression e
	case v of
		Nothing -> return((Neg newExp), Nothing)
		Just (TypeInt x) -> case (x < 0) of
			True -> return ((ELitInt x), (Just (TypeInt x)))
			False -> return ((Neg (ELitInt x)), (Just (TypeInt x)))
		_ -> runErrorSimply ("ERROR\n Couldn't negate non integer value")


simplyfyExpression ELitTrue = return (ELitTrue, (Just (TypeBoolean True)))

simplyfyExpression ELitFalse = return (ELitFalse, (Just (TypeBoolean False)))

simplyfyExpression (Not e) = do
	(newExp, v) <- simplyfyExpression e
	case v of
		Nothing -> return((Not newExp), Nothing)
		Just (TypeBoolean False) -> return (ELitTrue, Just (TypeBoolean True))
		Just (TypeBoolean True) -> return (ELitFalse, Just (TypeBoolean False))
		_ -> runErrorSimply ("ERROR\n Couldn't negate non bool value")

simplyfyExpression (EAnd e1 e2) = do
	(newExp1, v1) <- simplyfyExpression e1
	(newExp2, v2) <- simplyfyExpression e2
	case (v1,v2) of
		(Nothing, Just (TypeBoolean True)) -> return(newExp1, Nothing)
		(Nothing, Just (TypeBoolean False)) -> return (ELitFalse, Just (TypeBoolean False))
		(Just (TypeBoolean True), Nothing) -> return(newExp2, Nothing)
		(Just (TypeBoolean False), Nothing) -> return (ELitFalse, Just (TypeBoolean False))
		(Nothing, Nothing) -> return((EAnd newExp1 newExp2), Nothing)
		((Just (TypeBoolean True)), (Just (TypeBoolean True))) -> return (ELitTrue, Just (TypeBoolean True))
		((Just (TypeBoolean _)), (Just (TypeBoolean _))) -> return (ELitFalse, Just (TypeBoolean False))
		_ -> runErrorSimply ("ERROR\n Couldn't and non bool values")

simplyfyExpression (EOr e1 e2) = do
	(newExp1, v1) <- simplyfyExpression e1
	(newExp2, v2) <- simplyfyExpression e2
	case (v1,v2) of
		(Nothing, Just (TypeBoolean True)) -> return(ELitTrue, Just (TypeBoolean True))
		(Nothing, Just (TypeBoolean False)) -> return(newExp1, Nothing)
		(Just (TypeBoolean True), Nothing) -> return(ELitTrue, Just (TypeBoolean True))
		(Just (TypeBoolean False), Nothing) -> return(newExp2, Nothing)
		(Nothing, Nothing) -> return((EOr newExp1 newExp2), Nothing)
		((Just (TypeBoolean False)), (Just (TypeBoolean False))) -> return (ELitFalse, Just (TypeBoolean False))
		((Just (TypeBoolean _)), (Just (TypeBoolean _))) -> return (ELitTrue, Just (TypeBoolean True))
		_ -> runErrorSimply ("ERROR\n Couldn't or non bool values")


simplyfyExpression (ERel e1 op e2) = do
	(newExp1, v1) <- simplyfyExpression e1
	(newExp2, v2) <- simplyfyExpression e2
	case (v1,v2) of
		(Just (TypeBoolean x), Just (TypeBoolean y)) -> do
			ret <- simplifyRelFunc op (TypeBoolean x) (TypeBoolean y)
			case ret of
				(TypeBoolean True) -> return(ELitTrue, Just (TypeBoolean True))
				(TypeBoolean False) -> return(ELitFalse, Just (TypeBoolean False))
		(Just (TypeInt x), Just (TypeInt y)) -> do
			ret <- simplifyRelFunc op (TypeInt x) (TypeInt y)
			case ret of
				(TypeBoolean True) -> return(ELitTrue, Just (TypeBoolean True))
				(TypeBoolean False) -> return(ELitFalse, Just (TypeBoolean False))
		_ -> return((ERel e1 op e2),Nothing)

simplyfyExpression (EMul e1 op e2) = do
	(newExp1, v1) <- simplyfyExpression e1
	(newExp2, v2) <- simplyfyExpression e2
	case (v1,v2) of
		(Just (TypeInt x), Just (TypeInt y)) -> do
			(TypeInt ret) <- simplifyMulFunc op (TypeInt x) (TypeInt y)
			case (ret < 0) of
				True -> return((Neg(ELitInt ret)), Just (TypeInt ret))
				False -> return((ELitInt ret), Just (TypeInt ret))
		_ -> return((EMul e1 op e2),Nothing)

simplyfyExpression (EAdd e1 op e2) = do
	(newExp1, v1) <- simplyfyExpression e1
	(newExp2, v2) <- simplyfyExpression e2
	case (v1,v2) of
		(Just (TypeInt x), Just (TypeInt y)) -> do
			(TypeInt ret) <- simplifyAddFunc op (TypeInt x) (TypeInt y)
			case (ret < 0) of
				True -> return((Neg(ELitInt ret)), Just (TypeInt ret))
				False -> return((ELitInt ret), Just (TypeInt ret))
		_ -> return ((EAdd e1 op e2),Nothing)

simplyfyExpression (EAppPure idList exprList) = do
	newExprList <- simplyfyExpressionList exprList
	return((EAppPure idList newExprList), Nothing)

{-
guard, couldn't simplify other expressions
-}
simplyfyExpression e = return (e, Nothing)

{-
simplify multiple initialization
-}
simplyfyItems :: [Item] -> Execution([Item])
simplyfyItems [] = return ([])
simplyfyItems ((NoInit x):r) = do
	rest <- simplyfyItems r
	return((NoInit x):rest)

simplyfyItems ((Init x e):r) = do
	(newExp, _) <- simplyfyExpression e
	rest <- simplyfyItems r
	return((Init x newExp):rest)

-- ####################################################################### --
-- ##### end optimalization simply variables - functions and methods ##### --
-- ####################################################################### --

-- ################################## --
-- ##### get definition helpers ##### --
-- ################################## --

{-
check if parrent of class exists and if there is no cycle in inheritance
-}

checkCycleInheritance :: Ident -> S.Set Ident -> Execution()
checkCycleInheritance name visited = do
	v <- gets$getClass name
	case v of
		Nothing -> runErrorEmptyExec("Class " ++ show(name) ++ " parrent doesn't exist" )
		Just (Nothing, _, _) -> return()
		Just (Just parName, _, _) -> case S.member name visited of
			True -> runErrorEmptyExec("Inheritance cycle in class" ++ show(name))
			False -> checkCycleInheritance parName (S.insert name visited)

-- ###################################### --
-- ##### end get definition helpers ##### --
-- ###################################### --

-- ########################### --
-- ##### get definitions ##### --
-- ########################### --

getDefinitions::[TopDef] -> Execution()
--empty
getDefinitions [] = return()

--functions
-- get all data and checks if function with name already exists
getDefinitions ((FnDef types name arguments block):r) = do
	typeName <- getType types
	(argumentsList, _) <- getArguments arguments
	newBlock <- optimalizeBlock block
	v <- gets$getFunction name
	label <- freshLabel
	modify$memorySetFunction name typeName argumentsList newBlock ("@.fn"++show(label))
	case v of
		Nothing -> getDefinitions r
		Just _ -> runErrorEmptyExec("Function " ++ show(name) ++ " duplicates.")


--class
getDefinitions ((ClassDefPure name (ClassBlock block)):r) = do
	(meth, attr) <- getAttributesAndMethods block 0
	v <- gets$getClass name
	modify$memorySetClass name Nothing meth attr
	checkCycleInheritance name S.empty
	case v of
		Nothing -> getDefinitions r
		Just _ -> runErrorEmptyExec("Function " ++ show(name) ++ " duplicates.")

--child Class
getDefinitions ((ClassDefChild name parrentName (ClassBlock block)):r) =  do
	-- first argument is always parrent class
	(meth, attr) <- getAttributesAndMethods block 1
	v <- gets$getClass name
	modify$memorySetClass name (Just parrentName) meth attr
	checkCycleInheritance name S.empty
	case v of
		Nothing -> getDefinitions r
		Just _ -> runErrorEmptyExec("Function " ++ show(name) ++ " duplicates.")

-- ############################### --
-- ##### end get definitions ##### --
-- ############################### --

-- ################################ --
-- ##### type analize helpers ##### --
-- ################################ --

addArgumentsToMemory :: [(Ident, AllTypes, Integer)] -> Execution ()
addArgumentsToMemory [] = return ()
addArgumentsToMemory ((name, types, _):rest) = do
	--already checked repeated
	modify$memoryAddVariable name types 0
	addArgumentsToMemory rest

-- it only returns type and if exists
memoryGetVariableFromIdList :: [Ident] -> StateInfo -> Maybe (AllTypes, Integer)
memoryGetVariableFromIdList [] _ = Nothing
memoryGetVariableFromIdList (id:[]) (c,f, mem, n, cla, ls) = memoryGetVariable id (c,f, mem, n, cla, ls)
memoryGetVariableFromIdList (id:l) (c,f, mem, n, cla, ls) = case (memoryGetVariable id (c,f, mem, n, cla, ls)) of
	Just ((TypeClass cl), _) -> memoryFindClassAttr l cl c
	_ -> Nothing

{-
finds Variable inside memory, class and its ancestors
-}
memoryFindClassAttr :: [Ident] -> Ident -> Class -> Maybe (AllTypes, Integer)
memoryFindClassAttr [] _ _ = Nothing
memoryFindClassAttr (id:[]) clName classes = case (M.lookup clName classes) of
	Just (Nothing, _, mem) -> M.lookup id mem
	Just (Just parId, _, mem) -> case (M.lookup id mem) of
		Just x -> Just x
		Nothing -> memoryFindClassAttr [id] parId classes

memoryFindClassAttr (id:l) clName classes = case (M.lookup clName classes) of
	Just (Nothing, _, mem) -> case (M.lookup id mem) of
		Just ((TypeClass ncl), _) -> memoryFindClassAttr l ncl classes
		_ -> Nothing

	Just (Just parId, _, mem) -> case (M.lookup id mem) of
		Just ((TypeClass ncl), _) -> memoryFindClassAttr l ncl classes
		Just (_) -> Nothing
		Nothing -> memoryFindClassAttr [id] parId classes

{-
finds method inside memory, class and its ancestors
-}
memoryGetFunctionFromIdList :: [Ident] -> StateInfo -> Maybe (AllTypes, [(Ident, AllTypes, Integer)], Block, String)
memoryGetFunctionFromIdList [] _ = Nothing
memoryGetFunctionFromIdList (id:[]) (c,f, mem, n, cla, ls) = getFunction id (c,f, mem, n, cla, ls)
memoryGetFunctionFromIdList ((Ident "self"):l) (c,f, mem, n, cla, ls) = case cla of
	Just id -> memoryFindClassMeth l id c
	_-> Nothing

memoryGetFunctionFromIdList (id:l) (c,f, mem, n, cla, ls) = case (memoryGetVariable id (c,f, mem, n, cla, ls)) of
	Just ((TypeClass cl), _) -> memoryFindClassMeth l cl c
	_ -> Nothing

memoryFindClassMeth :: [Ident] -> Ident -> Class -> Maybe (AllTypes, [(Ident, AllTypes, Integer)], Block, String)
memoryFindClassMeth [] _ _ = Nothing

memoryFindClassMeth (id:[]) clName classes = case (M.lookup clName classes) of
	Just (Nothing, func, _) -> M.lookup id func
	Just (Just parId, func, _) -> case (M.lookup id func) of
		Just x -> Just x
		Nothing -> memoryFindClassMeth [id] parId classes

memoryFindClassMeth (id:l) clName classes = case (M.lookup clName classes) of
	Just (Nothing, _, mem) -> case (M.lookup id mem) of
		Just ((TypeClass ncl), _) -> memoryFindClassMeth l ncl classes
		_ -> Nothing

	Just (Just parId, _, mem) -> case (M.lookup id mem) of
		Just ((TypeClass ncl), _) -> memoryFindClassMeth l ncl classes
		Just (_) -> Nothing
		Nothing -> memoryFindClassMeth [id] parId classes

{-
Checks arguments number.
-}
checkArguments :: [Expr] -> [(Ident, AllTypes, Integer)] -> Execution ([Expr])
checkArguments [] [] = return([])
checkArguments exprList [] = runErrorExprListExec("More parameters than arguments.")
checkArguments [] argsList = runErrorExprListExec("More arguments than parameters.")
checkArguments (expr:el) ((_, types, _):al) = do
	typeExp <- analizeExpression expr
	case (typeExp == types) of
		True -> do
			exprL <- checkArguments el al
			return (expr:exprL)
		False -> case (typeExp, types) of
			(TypeClass from, TypeClass to) -> do
				checkParenthes from to
				exprL <- checkArguments el al
				return ((Ecast (EVarPure [to]) expr):exprL)
			_ -> runErrorExprListExec("Wrong parameter type " ++ show(types) ++ ", " ++ show(typeExp))
storeMem :: [(Ident, (AllTypes, Integer))] -> Execution()
storeMem [] = return ()
storeMem ((id, (types, int)):r) = do
	modify$memoryAddVariable id types int
	storeMem r

{-
set function arguments as local variables
-}
setAttributesMemory :: Ident -> Execution ()
setAttributesMemory id = do
	Just (par, meth, mem) <- gets$getClass id
	case par of
		Nothing -> storeMem (M.toList mem)
		Just x -> do
			setAttributesMemory x
			storeMem (M.toList mem)

{-
update class methods
-}
updateMethods:: Functions -> [(Ident, (AllTypes, [(Ident, AllTypes, Integer)], Block, String))] -> Functions
updateMethods meth [] = meth
updateMethods meth ((id,x):list) = updateMethods (M.insert id x meth) list

-- #################################### --
-- ##### end type analize helpers ##### --
-- #################################### --

-- ######################### --
-- ##### type analize  ##### --
-- ######################### --

{-
checks attributes and methods, keeps attributes as local variables of class methods
-}
typeAnalizeClasses :: [(Ident, (Maybe Ident, Functions, Memory))] -> Execution ()
typeAnalizeClasses [] = return ()
typeAnalizeClasses ((id, (par, meth, mem)):rest)  = do
	modify$memoryAddLevel True
	modify$memorySetCurrentClass id
	setAttributesMemory id
	newmeth <- typeAnalizeMethods (M.toList meth)
	modify$memorySetClass id par (updateMethods meth (M.toList newmeth)) mem
	modify$memoryRemoveCurrentClass
	modify$memoryRemoveLevel
	typeAnalizeClasses rest


{-
checks methods similar to functions, but uses class attributes as variables
-}
typeAnalizeMethods :: [(Ident, (AllTypes, [(Ident, AllTypes, Integer)], Block, String))] -> Execution (Functions)
typeAnalizeMethods [] = return(M.empty)
typeAnalizeMethods ((id, (types, args, (Block block), llvmid)):rest) = do
	modify$memoryAddLevel False
	addArgumentsToMemory args
	(newBlock, _) <- analizeBlock block types True
	-- updates function definition
	modify$memoryRemoveLevel
	methMap <- typeAnalizeMethods rest
	return (M.insert id (types, args, (Block newBlock), llvmid) methMap)


typeAnalizeFunctions :: [(Ident, (AllTypes, [(Ident, AllTypes, Integer)], Block, String))] -> Execution ()
typeAnalizeFunctions [] = return()
typeAnalizeFunctions ((id, (types, args, (Block block), llvmid)):rest) = do
	modify$memoryAddLevel True
	addArgumentsToMemory args
	(newBlock, _) <- analizeBlock block types True
	-- updates function definition
	modify$memorySetFunction id types args (Block newBlock) llvmid
	modify$memoryRemoveLevel
	typeAnalizeFunctions rest

{-
checks if class inherits by signed class.
-}
checkParenthes :: Ident -> Ident -> Execution()
checkParenthes (Ident "null") par = do
	v <- gets$getClass par
	return()

checkParenthes child par = do
	v <- gets$getClass child
	case v of
		Nothing -> runErrorEmptyExec("Casted class does not exists.")
		Just (Nothing, _, _) -> case (child == par) of
			True -> return()
			False -> runErrorEmptyExec("Cast type runError")
		Just (Just parName, _, _) -> case (or [(parName == par), (child == par)]) of
			False -> checkParenthes parName par
			True -> return()

--- list of statements, return type and if return statement is necessary, return statements and if returned
analizeBlock :: [Stmt] -> AllTypes -> Bool-> Execution([Stmt], Bool)
analizeBlock [] TypeVoid True = return([VRet], True)
analizeBlock [] _ False = return([], False)
analizeBlock [] _ True = runErrorBlock("Function needs return statement.")

analizeBlock (Empty:r) types retN = do
	analizeRet <- analizeBlock r types retN
	return(analizeRet)

analizeBlock ((BStmt (Block block)):r) types retN = do
	modify$memoryAddLevel False
	(newBlock1, ret1)  <- analizeBlock block types False
	modify$memoryRemoveLevel
	case ret1 of
		True -> return([BStmt (Block newBlock1)], True)
		False -> do
			(newBlock2, ret2) <- analizeBlock r types retN
			return(((BStmt (Block newBlock1)):newBlock2), ret2)

analizeBlock ((Decl typesV items):r) types retN = do
	varType <- getType typesV
	newItems <- analizeItems items varType
	(newStmt, ret) <- analizeBlock r types retN
	return((((Decl typesV newItems)):newStmt), ret)

{-
Adds cast to statement if is necessary
-}
analizeBlock ((AssPure idList expr):r) types retN = do
	variable <- gets$memoryGetVariableFromIdList idList
	typeExp <- analizeExpression expr
	case variable of
		Nothing -> runErrorBlock("Variable " ++ show(idList) ++ "not declared")
		Just ((TypeClass classParentName) ,_) -> do
			case (typeExp) of
				(TypeClass classChildName) ->  case (classChildName == classParentName) of
					True -> do
						(newStmt, ret) <- analizeBlock r types retN
						return((((AssPure idList expr)):newStmt), ret)
					False -> do
						checkParenthes classChildName classParentName
						(newStmt, ret) <- analizeBlock r types retN
						return(((AssPure idList (Ecast (EVarPure [classParentName]) expr)):newStmt), ret)
				_ -> runErrorBlock("Variable " ++ show(idList) ++ " expression type doesn't match.")
		Just (typesVar ,_) -> do
			case (typeExp == typesVar) of
				False -> runErrorBlock("Variable " ++ show(idList) ++ " expression type doesn't match.")
				True -> do
					(newStmt, ret) <- analizeBlock r types retN
					return((((AssPure idList expr)):newStmt), ret)

analizeBlock ((Incr idList):r) types retN = do
	variable <- gets$memoryGetVariableFromIdList idList
	case variable of
		Nothing -> runErrorBlock("Variable " ++ show(idList) ++ "not declared")
		Just (typesVar ,_) -> do
			case (TypeInteger == typesVar) of
				False -> runErrorBlock("Variable " ++ show(idList) ++ " expression type doesn't match.")
				True -> do
					(newStmt, ret) <- analizeBlock r types retN
					return((((Incr idList)):newStmt), ret)

analizeBlock ((Decr idList):r) types retN = do
	variable <- gets$memoryGetVariableFromIdList idList
	case variable of
		Nothing -> runErrorBlock("Variable " ++ show(idList) ++ "not declared")
		Just (typesVar ,_) -> do
			case (TypeInteger == typesVar) of
				False -> runErrorBlock("Variable " ++ show(idList) ++ " expression type doesn't match.")
				True -> do
					(newStmt, ret) <- analizeBlock r types retN
					return((((Decr idList)):newStmt), ret)

analizeBlock (VRet:r) TypeVoid retN = return([VRet], True)
analizeBlock (VRet:r) _ retN = runErrorBlock("Couldn't return void")

analizeBlock ((Ret e):r) types retN = do
	typeExp <- analizeExpression e
	case (typeExp == types) of
		True -> return([(Ret e)], True)
		False -> case (typeExp, types) of
			((TypeClass from), (TypeClass to)) -> do
				checkParenthes from to
				return([(Ret (Ecast (EVarPure [to]) e))], True)
			_ -> runErrorBlock("Wrong return Type")

analizeBlock ((SExp e):r) types retN = do
	analizeExpression e
	(newStmt, ret) <- analizeBlock r types retN
	return((SExp e):newStmt, ret)

analizeBlock ((Cond e stmt):r) types retN = do
	typeExp <- analizeExpression e
	case (typeExp == TypeBool) of
		False -> runErrorBlock("Non bool expression at if condition")
		True -> do
			modify$memoryAddLevel False
			([newStmt], _) <- analizeBlock [stmt] types False
			modify$memoryRemoveLevel
			(newStmtList, ret) <- analizeBlock r types retN
			return((Cond e newStmt):newStmtList, ret)

analizeBlock ((CondElse e stmt1 stmt2):r) types retN = do
	typeExp <- analizeExpression e
	case (typeExp == TypeBool) of
		False -> runErrorBlock("Non bool expression at if condition")
		True -> do
			modify$memoryAddLevel False
			([newStmt1], ret1) <- analizeBlock [stmt1] types False
			modify$memoryRemoveLevel
			modify$memoryAddLevel False
			([newStmt2], ret2) <- analizeBlock [stmt2] types False
			modify$memoryRemoveLevel
			case ((ret1 == True) && (ret2 == True)) of
				True -> return([(CondElse e newStmt1 newStmt2)], True)
				False -> do
					modify$memoryAddLevel False
					(newStmtList, ret) <- analizeBlock r types retN
					modify$memoryRemoveLevel
					return((CondElse e newStmt1 newStmt2):newStmtList, ret)

analizeBlock ((While e stmt):r) types retN = do
	typeExp <- analizeExpression e
	case (typeExp == TypeBool) of
		False -> runErrorBlock("Non bool expression at while condition")
		True -> do
			modify$memoryAddLevel False
			([newStmt], _) <- analizeBlock [stmt] types False
			modify$memoryRemoveLevel
			(newStmtList, ret) <- analizeBlock r types retN
			return((While e newStmt):newStmtList, ret)

analizeItems :: [Item] -> AllTypes -> Execution([Item])
analizeItems [] _= return([])
analizeItems ((NoInit id):r) types = do
	variable <- gets$memoryGetVariableOneLevel id
	case variable of
		Just _ -> runErrorItemExec("Variable " ++ show(id) ++ "duplicates")
		Nothing -> do
			modify$memoryAddVariable id types 0
			retItems <- analizeItems r types
			return((NoInit id):retItems)

{-
Adds cast to expression if is necessary
-}
analizeItems ((Init id e):r) (TypeClass className) = do
	variable <- gets$memoryGetVariableOneLevel id
	case variable of
		Just _ -> runErrorItemExec("Variable " ++ show(id) ++ "duplicates")
		Nothing -> do
			typeExp <- analizeExpression e
			case typeExp of
				(TypeClass classChildName) ->  case (classChildName == className) of
					True -> do
						modify$memoryAddVariable id (TypeClass className) 0
						retItems <- analizeItems r (TypeClass className)
						return ((Init id e):retItems)
					False -> do
						checkParenthes classChildName className
						modify$memoryAddVariable id (TypeClass className) 0
						retItems <- analizeItems r (TypeClass className)
						return ((Init id (Ecast (EVarPure [className]) e)):retItems)
				_ -> runErrorItemExec("Variable " ++ show(id) ++ "expression has type.")

analizeItems ((Init id e):r) types = do
	variable <- gets$memoryGetVariableOneLevel id
	case variable of
		Just _ -> runErrorItemExec("Variable " ++ show(id) ++ "duplicates")
		Nothing -> do
			typeExp <- analizeExpression e
			case (typeExp == types) of
				False -> runErrorItemExec("Variable " ++ show(id) ++ "expression has type.")
				True -> do
					modify$memoryAddVariable id types 0
					retItems <- analizeItems r types
					return((Init id e):retItems)

analizeExpression:: Expr -> Execution(AllTypes)
analizeExpression (ELitInt _) = return(TypeInteger)
analizeExpression (EString _) = return(TypeString)
analizeExpression (ELitTrue) = return(TypeBool)
analizeExpression (ELitFalse) = return(TypeBool)
analizeExpression (ELitCall) = return(TypeClass (Ident "null"))

analizeExpression (EVarPure idList) = do
	variable <- gets$memoryGetVariableFromIdList idList
	case variable of
		Nothing -> runErrorExpr("Variable " ++ show(idList) ++ "not declared")
		Just (types ,_) -> return(types)


analizeExpression (ENewObj types ) = do
	realType <- getType (PureType types)
	case realType of
		(TypeClass id) -> do
			v <- gets$getClass id
			case v of
				Nothing -> runErrorExpr("class " ++ show(id) ++ "does not exist")
				Just _ -> return realType
		_ -> runErrorExpr("new statement can be run only for class.")

analizeExpression (EAppPure idList exprList ) = do
	meth <- gets$memoryGetFunctionFromIdList idList
	case meth of
		Nothing -> runErrorExpr("method " ++ show(idList) ++ " not found.")
		Just (types, argsList, _, _) -> do
			checkArguments exprList argsList
			return (types)

analizeExpression (EAppPureObj idList exprList exprt) = do
--TODO run exprt
	meth <- gets$memoryGetFunctionFromIdList idList
	case meth of
		Nothing -> runErrorExpr("method " ++ show(idList) ++ " not found.")
		Just (types, argsList, _, _) -> do
			checkArguments exprList argsList
			return (types)


{-
it can be cast only to class id
-}
analizeExpression (Ecast (EVarPure (id:_)) expr) = do
	gets$getClass id
	types <- analizeExpression expr

	case types of
		TypeClass (Ident "null") -> return (TypeClass id)
		TypeClass idc -> do
			case (idc == id) of
				True -> return (TypeClass id)
				False -> do
					checkParenthes idc id
					return (TypeClass id)
		_ -> runErrorExpr("Cast type error.")


analizeExpression (ERel e1 op e2) = do
	t1 <- analizeExpression e1
	t2 <- analizeExpression e2
	case (t1 == t2) of
		False -> runErrorExpr("Relation operation arguments must have the same type")
		True -> case ((op /= EQU) && (op /= NE)) of
			False -> return(TypeBool)
			True -> case (t1 == TypeInteger) of
				False -> runErrorExpr("Relation less/greater operation arguments must have integer type")
				True -> return(TypeBool)

analizeExpression (Neg e ) = do
	t<- analizeExpression e
	case (t == TypeInteger) of
		False -> runErrorExpr("Negation operation argument must have integer value")
		True -> return(TypeInteger)

analizeExpression (Not e ) = do
	t<- analizeExpression e
	case (t == TypeBool) of
		False -> runErrorExpr("Not operation argument must have bool value")
		True -> return(TypeBool)

analizeExpression (EAdd e1  op e2 ) = do
	t1<- analizeExpression e1
	t2<- analizeExpression e2
	case (((t2 == TypeInteger) && (t1 == TypeInteger)) ||  ((t2 == TypeString) && (t1 == TypeString) && (op == Plus))) of
		False -> runErrorExpr("Add operation arguments must have integer or string values")
		True -> return(t1)

analizeExpression (EMul e1 _ e2 ) = do
	t1<- analizeExpression e1
	t2<- analizeExpression e2
	case ((t2 == TypeInteger) && (t1 == TypeInteger)) of
		False -> runErrorExpr("Mul operation arguments must have integer values")
		True -> return(TypeInteger)


analizeExpression (EAnd e1 e2 ) = do
	t1<- analizeExpression e1
	t2<- analizeExpression e2
	case ((t2 == TypeBool) && (t1 == TypeBool)) of
		False -> runErrorExpr("And operation arguments must have bool values")
		True -> return(TypeBool)

analizeExpression (EOr e1 e2 ) = do
	t1<- analizeExpression e1
	t2<- analizeExpression e2
	case ((t2 == TypeBool) && (t1 == TypeBool)) of
		False -> runErrorExpr("Or operation arguments must have bool values")
		True -> return(TypeBool)

analizeExpression _ = runErrorExpr("Wrong expression")

-- ############################# --
-- ##### end type analize  ##### --
-- ############################# --

-- ############################# --
-- ##### run error helpers ##### --
-- ############################# --
{-
Run errors for different type functions. Function error() brakes haskell program evaluation.
-}
runErrorExpr :: String -> Execution(AllTypes)
runErrorExpr str = do
	h <- ask
	liftIO$hPutStr h ("ERROR\n" ++ str ++ "\n")
	error("")

runErrorBlock :: String -> Execution([Stmt], Bool)
runErrorBlock str = do
	h <- ask
	liftIO$hPutStr h ("ERROR\n" ++ str ++ "\n")
	error("")

runErrorEmptyExec :: String -> Execution()
runErrorEmptyExec str = do
	h <- ask
	liftIO$hPutStr h ("ERROR\n" ++ str ++ "\n")
	error("")

runErrorItemExec :: String -> Execution([Item])
runErrorItemExec str = do
	h <- ask
	liftIO$hPutStr h ("ERROR\n" ++ str ++ "\n")
	error("")

runErrorExprListExec :: String -> Execution(b)
runErrorExprListExec str = do
	h <- ask
	liftIO$hPutStr h ("ERROR\n" ++ str ++ "\n")
	error("")

runErrorSimply :: String -> Execution((Expr, Maybe BasicTypesValue))
runErrorSimply str = do
	h <- ask
	liftIO$hPutStr h ("ERROR\n" ++ str ++ "\n")
	error("")

-- ################################# --
-- ##### end run error helpers ##### --
-- ################################# --
