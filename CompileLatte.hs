module CompileLatte where
import System.IO
import System.Environment
import qualified Data.Map as M
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
Adds embeded functions and compile stored functions and classes.
-}
compile:: Execution()
compile = do
	--compile clases
	cl <- gets$getAllClasses
	--compile functions
	fn <- gets$getAllFunctions
	setEmbededFunctions
	compileClasses cl
	compileFunctions fn
	return ()


-- #################################### --
-- ##### compile classes helpers  ##### --
-- #################################### --

strFromIdent :: Ident -> String
strFromIdent id = reverse$drop 1 (reverse$drop 7 (show(id)))

sortByInteger (a1, (b1, c1)) (a2, (b2, c2))
	| c1 < c2 = LT
	| c1 > c2 = GT
	| c1 == c2 = compare a1 a2


showAttributes :: [(Ident, (AllTypes, Integer))] -> Execution (String)
showAttributes [] = return (" ")
showAttributes ((_, (t, _)):[]) = getllvmType t
showAttributes ((_, (t, _)):r) = do
	attr <- showAttributes r
	types <- getllvmType t
	return (types ++ ", " ++ attr)


showClassInit :: Maybe Ident -> Memory -> Execution (String)
showClassInit Nothing m =  showAttributes$ sortBy sortByInteger (M.toList m)
showClassInit (Just id) m = case (M.null m) of
	True -> return ("%class." ++ strFromIdent(id))
	_ -> do
		attr <- showAttributes$ sortBy sortByInteger (M.toList m)
		return ("%class." ++ strFromIdent(id) ++ ", " ++ attr)


-- ######################################## --
-- ##### end compile classes helpers  ##### --
-- ######################################## --



-- ############################ --
-- ##### compile classes  ##### --
-- ############################ --

compileClasses::[(Ident, (Maybe Ident, Functions, Memory) )] -> Execution()
compileClasses [] = return()

compileClasses ((id, (par, methods, attributes)):rest) = do
	h <- ask
	classInit <- showClassInit par attributes
	liftIO$hPutStrLn h ("%class." ++ strFromIdent(id) ++ " = type { " ++ classInit ++ " }")
	modify$memorySetCurrentClass id
	compileFunctions (M.toList methods)
	modify$memoryRemoveCurrentClass
	compileClasses rest

-- ################################ --
-- ##### end compile classes  ##### --
-- ################################ --

-- ##################################### --
-- ##### compile function helpers  ##### --
-- ##################################### --


{-
Transform AllTypes into llvm type
-}
getllvmType::AllTypes -> Execution(String)
getllvmType TypeInteger = return("i32")
getllvmType TypeString = return("i8*")
getllvmType TypeBool = return("i1")
getllvmType TypeVoid = return("void")
getllvmType (TypeClass id) = return("%class." ++ strFromIdent(id) ++ "*")

{-
Compile arguments list into llvm arguments list code.
-}
getllvmArgsString::[(Ident, AllTypes, Integer)] -> Execution(String)
getllvmArgsString [] = return ("")
getllvmArgsString ((name, types, id):[]) = do
	typesV <- getllvmType types
	return (" " ++ typesV ++ " %var" ++ show(id))
getllvmArgsString ((name, types, id):r) = do
	rest <- getllvmArgsString r
	typesV <- getllvmType types
	return (" " ++ typesV ++ " %var" ++ show(id) ++ "," ++ rest)

{-
Compile arguments values as local variables of fuction block
(as it was mentioned in task description).
-}
setArgumentsAsVariables::[(Ident, AllTypes, Integer)] -> Execution()
setArgumentsAsVariables[] = return ()
setArgumentsAsVariables ((name, types, id):r) = do
	h <- ask
	t <- getllvmType types
	labelalloc <- callLlvmAlloca t
	liftIO$hPutStrLn h ("\tstore " ++ t ++ " %var" ++ show(id) ++ ", " ++ t ++ "* %var" ++ show(labelalloc))
	modify$memoryAddVariable name types labelalloc
	setArgumentsAsVariables r

{-
Compile constant string outside of function.
-}
compileStrings :: [(String, String)] -> Execution()
compileStrings [] = return()
compileStrings ((_, str):r) = do
	h <- ask
	liftIO$hPutStrLn h (str)
	compileStrings r

-- ######################################### --
-- ##### end compile function helpers  ##### --
-- ######################################### --

-- ############################## --
-- ##### compile functions  ##### --
-- ############################## --

{-
Gets function type, name, arguments and block. First compile function header (type, name, arguments).
Then sets new memory level (last level bool = True), compile start label, compile arguments as variables.
Compile function block, remove memory level close function, and compile string constants
-}
compileFunctions::[(Ident, (AllTypes, [(Ident, AllTypes, Integer)], Block, String))] -> Execution()
compileFunctions [] = return()
compileFunctions ((id, (types, arguments, (Block block), name)):rest) = do
	h <- ask
	t <- getllvmType types
	funcStartLabel <- freshLabel
	argsList <- getllvmArgsString arguments
	curClass <- gets$memoryGetCurrentClass
	modify$memoryAddLevel True
	case curClass of
		Nothing -> do
			liftIO$hPutStrLn h ("define "++ t ++" " ++ name ++ "( " ++ argsList ++ " ) {")
			callLlvmStartLabel ("l"++show(funcStartLabel))
			setArgumentsAsVariables arguments
			stringsList <- compileBlock block
			liftIO$hPutStrLn h ("}\n")
			modify$memoryRemoveLevel
			compileStrings stringsList
			compileFunctions rest
		(Just cls) -> case (null argsList) of
			False -> do
				typesClass <- getllvmType (TypeClass cls)
				liftIO$hPutStrLn h ("define "++ t ++" " ++ name ++ "( "++typesClass++" %this, " ++ argsList ++ " ) {")
				callLlvmStartLabel ("l"++show(funcStartLabel))
				liftIO$hPutStrLn h ("\t%varthis = alloca "++ typesClass)
				liftIO$hPutStrLn h ("\tstore " ++ typesClass ++ " %this, " ++ typesClass ++ "* %varthis")
				setArgumentsAsVariables arguments
				stringsList <- compileBlock block
				liftIO$hPutStrLn h ("}\n")
				modify$memoryRemoveLevel
				compileStrings stringsList
				compileFunctions rest
			True -> do
				typesClass <- getllvmType (TypeClass cls)
				liftIO$hPutStrLn h ("define "++ t ++" " ++ name ++ "( "++typesClass++" %this ) {")
				callLlvmStartLabel ("l"++show(funcStartLabel))
				liftIO$hPutStrLn h ("\t%varthis = alloca "++ typesClass)
				liftIO$hPutStrLn h ("\tstore " ++ typesClass ++ " %this, " ++ typesClass ++ "* %varthis")
				setArgumentsAsVariables arguments
				stringsList <- compileBlock block
				liftIO$hPutStrLn h ("}\n")
				modify$memoryRemoveLevel
				compileStrings stringsList
				compileFunctions rest

-- ################################## --
-- ##### end compile functions  ##### --
-- ################################## --

-- ################################## --
-- ##### compile block helpers  ##### --
-- ################################## --

{-
Initalize pure many varilables
-}
compileItems :: [Item] -> AllTypes -> Execution([(String, String)])
compileItems [] _= return([])
compileItems ((NoInit id):r) allType = do
	h <- ask
	types <- getllvmType allType
	labelalloc <- callInitialLlvmAlloca types
	modify$memoryAddVariable id allType labelalloc
	compileItems r allType

{-
Initalize many varilables with initial value.
-}
compileItems ((Init id e):r) allType = do
	h <- ask
	types <- getllvmType allType
	(_, Just identif, strl1) <- compileExpr e
	labelalloc <- callLlvmAlloca types
	modify$memoryAddVariable id allType labelalloc
	liftIO$hPutStrLn h ("\tstore "++ types ++ " "++identif ++", "++ types ++ "*" ++ " %var" ++ show(labelalloc))
	-- TODO add class
	strl2 <- compileItems r allType
	return (concat [strl1, strl2])


-- it only returns type and identifier
memoryGetVariableFromIdList :: [Ident] -> Execution (AllTypes, Integer)
memoryGetVariableFromIdList (id:[])  = do
	memVar <- gets$memoryGetVariable id
	case memVar of
		Just (typeVar, intVar) -> return (typeVar, intVar)
		Nothing -> do
			(Just cl) <- gets$memoryGetCurrentClass
			memoryFindClassAttr [id] cl "this" Nothing

memoryGetVariableFromIdList (id:l) = do
	memVar <- gets$ memoryGetVariable id
	case memVar of
		Just ((TypeClass cl), intVar) -> memoryFindClassAttr l cl (show(intVar)) Nothing
		--we are in class method and are getting our attribute
		Nothing -> do
			(Just cl) <- gets$memoryGetCurrentClass
			memoryFindClassAttr (id:l) cl "this" Nothing

{-
finds Variable inside memory, class and its ancestors
-}
memoryFindClassAttr :: [Ident] -> Ident -> String -> Maybe Ident-> Execution (AllTypes, Integer)
memoryFindClassAttr (id:[]) clName llvmId initialClass = do
	Just (parId, _, mem) <- gets$getClass clName
	case (M.lookup id mem) of
		Just (typesVar, attrId) -> do
			retIdetif <- callLlvmLoadClassAttr clName llvmId attrId initialClass
			return (typesVar, retIdetif)
		Nothing -> case initialClass of
			Nothing -> memoryFindClassAttr [id] (fromJust parId) llvmId (Just clName)
			(Just x) -> memoryFindClassAttr [id] (fromJust parId) llvmId initialClass


memoryFindClassAttr (id:l) clName llvmId initialClass = do
	Just (parId, _, mem) <- gets$getClass clName
	case (M.lookup id mem) of
		Just ((TypeClass typesVar), attrId) -> do
			retIdetif <- callLlvmLoadClassAttr clName llvmId attrId initialClass
			memoryFindClassAttr l typesVar (show(retIdetif)) Nothing
		Nothing -> case initialClass of
				Nothing -> memoryFindClassAttr (id:l) (fromJust parId) llvmId (Just clName)
				(Just x) -> memoryFindClassAttr (id:l) (fromJust parId) llvmId initialClass


{-
loads objects from pointer and gets it's attribute
-}
callLlvmLoadClassAttr :: Ident -> String -> Integer -> Maybe Ident -> Execution (Integer)
callLlvmLoadClassAttr clTypeId ident1 ident2 Nothing = do
	h <- ask
	identif1 <- freshLabel
	identif2 <- freshLabel
	types <- getllvmType (TypeClass clTypeId)
	liftIO$hPutStrLn h ("\t%var"++show(identif1) ++" = load "++ types ++"* %var" ++ ident1)
	liftIO$hPutStrLn h ("\t%var"++show(identif2) ++" = getelementptr inbounds "++types++" %var" ++ show(identif1) ++", i32 0, i32 "++show(ident2))
	return (identif2)

callLlvmLoadClassAttr clTypeId ident1 ident2 (Just firstId) = do
	h <- ask
	identif1 <- freshLabel
	identif2 <- freshLabel
	identif3 <- freshLabel
	types <- getllvmType (TypeClass clTypeId)
	typesFirst <- getllvmType (TypeClass firstId)
	liftIO$hPutStrLn h ("\t%var"++show(identif1) ++" = load "++ types ++"* %var" ++ ident1)
	liftIO$hPutStrLn h ("\t%var"++show(identif2) ++" = bitcast "++ typesFirst ++" %var" ++ ident1 ++ " to " ++ types)
	liftIO$hPutStrLn h ("\t%var"++show(identif3) ++" = getelementptr inbounds "++types++" %var" ++ show(identif2) ++", i32 0, i32 "++show(ident2))
	return (identif3)


-- ###################################### --
-- ##### end compile block helpers  ##### --
-- ###################################### --


-- ########################## --
-- ##### compile block  ##### --
-- ########################## --

-- return string identifier and string value
{-
Gets function list of statements, compile it and returns constant strings used inside function
-}
compileBlock :: [Stmt] -> Execution([(String, String)])
compileBlock [] = return ([])
compileBlock (Empty :r) = do
	compileBlock r


compileBlock (VRet :r) = do
	h <- ask
	liftIO$hPutStrLn h ("\tret void")
	compileBlock r

compileBlock ((Ret e):r) = do
	h <- ask
	(types, Just val, strl1)<- compileExpr e

	--liftIO$hPutStr h ("ERROR\n" ++ show(types) ++ "\n")

	t <- getllvmType types
	liftIO$hPutStrLn h ("\tret "++ t ++ " " ++ val)
	strl2 <- compileBlock r
	return (concat [strl1, strl2])


compileBlock ((SExp e):r) = do
	(_, _, strl1)<- compileExpr e
	strl2 <- compileBlock r
	return (concat [strl1, strl2])

{-
Block inside block changes only memory level
-}
compileBlock ((BStmt (Block bl)):r) = do
	modify$memoryAddLevel False
	strl1 <- compileBlock bl
	modify$memoryRemoveLevel
	strl2 <- compileBlock r
	return (concat [strl1, strl2])

{-
Declare variable
-}
compileBlock ((Decl typesV items):r)  = do
	allType <- getType typesV
	strl1 <- compileItems items allType
	strl2 <- compileBlock r
	return (concat [strl1, strl2])

-- TODO add class call
{-
Assign compiled value to variable
-}
compileBlock ((AssPure idList exp):r)  = do
	(_, labelalloc)<- memoryGetVariableFromIdList idList
	(allType, Just identif, strl1) <- compileExpr exp
	types <- getllvmType allType
	h <- ask
	liftIO$hPutStrLn h ("\tstore "++ types ++ " "++identif ++", "++ types ++ "*" ++ " %var" ++ show(labelalloc))
	strl2 <- compileBlock r
	return (concat [strl1, strl2])

{-
Increment variable
-}
compileBlock ((Incr idList ):r)  = do
	(_, labelalloc)<- memoryGetVariableFromIdList idList
	h <- ask
	identif1 <- freshLabel
	identif2 <- freshLabel
	liftIO$hPutStrLn h ("\t%var"++show(identif1) ++" = load i32* %var" ++ show(labelalloc))
	liftIO$hPutStrLn h ("\t%var"++show(identif2) ++" = add i32 %var" ++ show(identif1)  ++", 1")
	liftIO$hPutStrLn h ("\tstore i32 %var"++show(identif2) ++", i32* %var" ++ show(labelalloc))
	compileBlock r


{-
Decrement variable
-}
compileBlock ((Decr idList ):r)  = do
	(_, labelalloc)<- memoryGetVariableFromIdList idList
	h <- ask
	identif1 <- freshLabel
	identif2 <- freshLabel
	liftIO$hPutStrLn h ("\t%var"++show(identif1) ++" = load i32* %var" ++ show(labelalloc))
	liftIO$hPutStrLn h ("\t%var"++show(identif2) ++" = sub i32 %var" ++ show(identif1)  ++", 1")
	liftIO$hPutStrLn h ("\tstore i32 %var"++show(identif2) ++", i32* %var" ++ show(labelalloc))
	compileBlock r


{-
Condition block always consist of two labels block one if expression is correct and another after if - statement
-}
compileBlock ((Cond exp stmt):r) = do
	(allType, Just identif, strl1) <- compileExpr exp
	h <- ask
	label1 <- freshLabel
	label2 <- freshLabel
	liftIO$hPutStrLn h ("\tbr i1 "++identif ++", label %l" ++ show(label1) ++ ", label %l" ++ show(label2))
	callLlvmStartLabel ("l"++show(label1))
	modify$memoryAddLevel False
	strl2 <- compileBlock [stmt]
	modify$memoryRemoveLevel
	liftIO$hPutStrLn h ("\tbr label %l"++show(label2))
	callLlvmStartLabel ("l"++show(label2))
	strl3 <- compileBlock r
	return (concat [strl1, strl2, strl3])


{-
Condition else block always consist of three labels block one if expression is correct, two if incorrect
and another after if - else statement.
-}
compileBlock ((CondElse exp stmt1 stmt2):r) = do
	(allType, Just identif, strl1) <- compileExpr exp
	h <- ask
	label1 <- freshLabel
	label2 <- freshLabel
	labelend <- freshLabel
	liftIO$hPutStrLn h ("\tbr i1 "++identif ++", label %l" ++ show(label1) ++ ", label %l" ++ show(label2))
	callLlvmStartLabel ("l"++show(label1))
	modify$memoryAddLevel False
	strl2 <- compileBlock [stmt1]
	modify$memoryRemoveLevel
	-- after if else condition function may finish
	case r of
		[] -> do
			callLlvmStartLabel ("l"++show(label2))
			modify$memoryAddLevel False
			strl3 <- compileBlock [stmt2]
			modify$memoryRemoveLevel
			return (concat [strl1, strl2, strl3])
		_ -> do
			liftIO$hPutStrLn h ("\tbr label %l"++show(labelend))
			callLlvmStartLabel ("l"++show(label2))
			modify$memoryAddLevel False
			strl3 <- compileBlock [stmt2]
			modify$memoryRemoveLevel
			liftIO$hPutStrLn h ("\tbr label %l"++show(labelend))
			callLlvmStartLabel ("l"++show(labelend))
			strl4 <- compileBlock r
			return (concat [strl1, strl2, strl3, strl4])


{-
Condition else block always consist of three labels block one checks expression, two run while body
and another after statement.
-}
compileBlock ((While exp stmt):r) = do
	h <- ask
	label1 <- freshLabel
	label2 <- freshLabel
	labelend <- freshLabel
	liftIO$hPutStrLn h ("\tbr label %l"++show(label1))
	callLlvmStartLabel ("l"++show(label1))
	(allType, Just identif, strl1) <- compileExpr exp
	liftIO$hPutStrLn h ("\tbr i1 "++identif ++", label %l" ++ show(label2) ++ ", label %l" ++ show(labelend))
	callLlvmStartLabel ("l"++show(label2))
	modify$memoryAddLevel False
	strl2 <- compileBlock [stmt]
	modify$memoryRemoveLevel
	liftIO$hPutStrLn h ("\tbr label %l"++show(label1))
	callLlvmStartLabel ("l"++show(labelend))
	strl3 <- compileBlock r
	return (concat [strl1, strl2, strl3])

-- ############################## --
-- ##### end compile block  ##### --
-- ############################## --


-- ################################# --
-- ##### compile expr helpers  ##### --
-- ################################# --

{-
transforms grammar operators into llvm operators
-}
compileRelOperators :: RelOp -> Execution(String)
compileRelOperators LTH = return("icmp slt")
compileRelOperators LE = return("icmp sle")
compileRelOperators GTH = return("icmp sgt")
compileRelOperators GE = return("icmp sge")
compileRelOperators EQU = return("icmp eq")
compileRelOperators NE = return("icmp ne")

compileMulOperators :: MulOp -> Execution(String)
compileMulOperators Times = return("mul")
compileMulOperators Div = return("udiv")
compileMulOperators Mod = return("srem")

compileAddOperators :: AddOp -> Execution(String)
compileAddOperators Plus = return("add")
compileAddOperators Minus = return("sub")

{-
Compile expression list into llvm arguments of called function.
-}
getArgumentsCallString:: [Expr] -> Execution(String, [(String, String)])
getArgumentsCallString [] = return ("", [])
getArgumentsCallString (expr:[]) = do
	(types, Just id, strList) <-compileExpr expr
	typesV <- getllvmType types
	return ((" " ++ typesV ++ " " ++ id ), strList)
getArgumentsCallString (expr:r) = do
	(types, Just id, strList) <-compileExpr expr
	typesV <- getllvmType types
	(restStr, restList) <- getArgumentsCallString r
	return ((" " ++ typesV ++ " " ++ id ++ "," ++ restStr), (concat [strList, restList]))


{-
Gives function (with Nothing), or method with class identifier (first parameter of method)
-}

getFunctionFromIdList :: [Ident] -> Execution ((AllTypes, [(Ident, AllTypes, Integer)], Block, String), Maybe String)
getFunctionFromIdList (id:[]) = do
	(Just funcDef) <- gets$getFunction id
	return (funcDef, Nothing)

getFunctionFromIdList ((Ident "self"):(l:[])) = do
	(Just clsId) <- gets$memoryGetCurrentClass
	h <- ask
	types <- getllvmType (TypeClass clsId)
	newLabel <- freshLabel
	liftIO$hPutStrLn h ("\t%var"++ show(newLabel) ++" = load "++types++"* %varthis")
	getMethod l clsId (show(newLabel)) Nothing


getFunctionFromIdList (id:l) = do
	(TypeClass clsId, identif) <- memoryGetVariableFromIdList (tail (reverse (id:l)))
	h <- ask
	types <- getllvmType (TypeClass clsId)
	newLabel <- freshLabel
	liftIO$hPutStrLn h ("\t%var"++ show(newLabel) ++" = load "++types++"* %var"++show(identif))
	getMethod (head (reverse (id:l))) clsId (show(newLabel)) Nothing

{-
get method having class initialClass with llvm identifier llvmId and from clName level
-}
getMethod :: Ident -> Ident -> String -> Maybe Ident-> Execution ((AllTypes, [(Ident, AllTypes, Integer)], Block, String), Maybe String)
getMethod identif clName llvmId initialClass = do
	Just (parId, meth, _) <- gets$getClass clName
	case (M.lookup identif meth) of
		(Just methDef) -> case initialClass of
			Nothing -> do
				types <- getllvmType (TypeClass clName)
				return (methDef, (Just (types ++" %var" ++llvmId++" ")))
			(Just from) -> do
				h <- ask
				identif1 <- freshLabel
				types <- getllvmType (TypeClass clName)
				typesFirst <- getllvmType (TypeClass from)
				liftIO$hPutStrLn h ("\t%var"++show(identif1) ++" = bitcast "++ typesFirst ++" %var" ++ llvmId ++ " to " ++ types)
				return (methDef, (Just (types ++ " %var"++show(identif1)++" ")))
		Nothing -> case initialClass of
			Nothing -> getMethod identif (fromJust parId) llvmId (Just clName)
			(Just x) -> getMethod identif (fromJust parId) llvmId initialClass


-- ##################################### --
-- ##### end compile expr helpers  ##### --
-- ##################################### --

-- ############################### --
-- ##### Compile Expression  ##### --
-- ############################### --

{-
Gets expression and compile it, returns expression type, expression label
and list of used const strings inside evaluation (id, llvm code).
-}
compileExpr :: Expr -> Execution(AllTypes, Maybe String, [(String, String)])

compileExpr (ELitInt int) = return(TypeInteger, Just (show(int)), [])
{-
bool is stored as i1 value
-}
compileExpr (ELitTrue) = return(TypeBool, Just "0", [])
compileExpr (ELitFalse) = return(TypeBool, Just  "1", [])
compileExpr (ELitCall) = return(TypeClass (Ident "null"), Just  "null", [])

{-
returns const strings
-}
compileExpr (EString str) = do
	h <- ask
	labelalloc <- callLlvmAlloca "i8*"
	labelstr <- freshLabel
	labelret <- freshLabel
	liftIO$hPutStrLn h ("\tstore i8* getelementptr inbounds (["++ show(length(str)+1)++" x i8]* @."++show(labelstr)++", i32 0, i32 0), i8** %var"++show(labelalloc)++"\n")
	liftIO$hPutStrLn h ("\t%var"++ show(labelret) ++" = load i8** %var"++show(labelalloc)++"\n")
	return(TypeString, Just ("%var"++show(labelret)), [("%var"++show(labelalloc), "@."++show(labelstr) ++" = private unnamed_addr constant ["++show(length(str)+1)++" x i8] c\""++ str ++"\00\" \n")])

compileExpr (EVarPure idList) = do
	(allType, labelalloc) <- memoryGetVariableFromIdList idList
	types <- getllvmType allType
	h <- ask
	newLabel <- freshLabel
	liftIO$hPutStrLn h ("\t%var"++ show(newLabel) ++" = load "++types++"* %var"++show(labelalloc))
	return(allType, Just ("%var"++ show(newLabel)), [])

compileExpr (ENewObj (Class classId)) = do
	h <- ask
	znwmLabel <- freshLabel
	newLabel <- freshLabel
	memLabel <- freshLabel
	len <- gets$getClassLength classId
	llvmType <- getllvmType (TypeClass classId)
	liftIO$hPutStrLn h ("\t%var"++ show(znwmLabel) ++" = call noalias i8* @_Znwm(i64 "++ show(len) ++")")
	liftIO$hPutStrLn h ("\t%var"++ show(newLabel) ++" = bitcast i8* %var" ++ show(znwmLabel) ++" to " ++ llvmType)
	liftIO$hPutStrLn h ("\t%var"++ show(memLabel) ++" = bitcast "++ llvmType ++" %var" ++ show(newLabel) ++" to i8*")
	liftIO$hPutStrLn h ("\tcall void @llvm.memset.p0i8.i64(i8*  %var"++ show(memLabel) ++", i8 0, i64 "++ show(len) ++", i32 8, i1 false)")
	return(TypeClass classId, Just ("%var"++ show(newLabel)), [])


{-
If function is non void then it is needed to store it value. Adds class identif
to method call.
-}
compileExpr (EAppPure idList exprList) = do
	((allType, args, _, identif), classIdentif) <- getFunctionFromIdList idList
	types <- getllvmType allType
	h <- ask
	(argsStr, strList)<- getArgumentsCallString exprList
	case classIdentif of
		Nothing -> case types of
			"void" -> do
				liftIO$hPutStrLn h ("\tcall "++types++" "++identif++"( "++ argsStr++" )\n")
				return(allType, Nothing , strList)
			_ -> do
				newLabel <- freshLabel
				liftIO$hPutStrLn h ("\t%var"++ show(newLabel) ++" = call "++types++" "++identif++"( "++ argsStr++" )")
				return(allType, Just ("%var"++ show(newLabel)), strList)
		(Just classLlvmIdent) -> case types of
			"void" -> case (null argsStr) of
				False -> do
					liftIO$hPutStrLn h ("\tcall "++types++" "++identif++"( "++classLlvmIdent ++", "++ argsStr++" )\n")
					return(allType, Nothing , strList)
				True -> do
					liftIO$hPutStrLn h ("\tcall "++types++" "++identif++"( "++classLlvmIdent ++" )\n")
					return(allType, Nothing , strList)
			_ -> case (null argsStr) of
				False -> do
					newLabel <- freshLabel
					liftIO$hPutStrLn h ("\t%var"++ show(newLabel) ++" = call "++types++" "++identif++"( "++classLlvmIdent ++ ", " ++ argsStr++" )")
					return(allType, Just ("%var"++ show(newLabel)), strList)
				True -> do
					newLabel <- freshLabel
					liftIO$hPutStrLn h ("\t%var"++ show(newLabel) ++" = call "++types++" "++identif++"( "++classLlvmIdent ++ " )")
					return(allType, Just ("%var"++ show(newLabel)), strList)


compileExpr (Ecast (EVarPure (id:_)) expr) = do
	(allType1, Just identif1, strl1) <- compileExpr expr
	case allType1 of
		(TypeClass (Ident "null")) -> return ((TypeClass id), Just identif1, strl1)
		(TypeClass classId) -> case (classId == id) of
			True-> return (allType1, Just identif1, strl1)
			False-> do
				returnLabel <- callLlvmCast classId id identif1
				return ((TypeClass id), returnLabel, strl1)


compileExpr (ERel e1 op e2) = do
	(allType1, Just identif1, strl1) <- compileExpr e1
	(allType2, Just identif2, strl2) <- compileExpr e2
	types <- getllvmType allType1
	oper <- compileRelOperators op
	h <- ask
	newLabel <- freshLabel
	liftIO$hPutStrLn h ("\t%var"++ show(newLabel) ++" = " ++ oper ++ " "++types++" "++identif1++", "++identif2)
	return (TypeBool, Just ("%var"++ show(newLabel)), (concat [strl1, strl2]))

compileExpr (Neg e ) = do
	(allType, Just identif, strl) <- compileExpr e
	types <- getllvmType allType
	h <- ask
	newLabel <- freshLabel
	liftIO$hPutStrLn h ("\t%var"++ show(newLabel) ++" = sub "++types++" 0, "++identif)
	return (allType, Just ("%var"++ show(newLabel)), strl)

compileExpr (Not e ) = do
	(allType, Just identif, strl) <- compileExpr e
	types <- getllvmType allType
	h <- ask
	newLabel <- freshLabel
	liftIO$hPutStrLn h ("\t%var"++ show(newLabel) ++" = xor "++types++" "++identif++", true")
	return (allType, Just ("%var"++ show(newLabel)), strl)

compileExpr (EMul e1 op e2 ) = do
	(allType1, Just identif1, strl1) <- compileExpr e1
	(allType2, Just identif2, strl2) <- compileExpr e2
	types <- getllvmType allType1
	oper <- compileMulOperators op
	h <- ask
	newLabel <- freshLabel
	liftIO$hPutStrLn h ("\t%var"++ show(newLabel) ++" = " ++ oper ++ " "++types++" "++identif1++", "++identif2)
	return (allType1, Just ("%var"++ show(newLabel)), (concat [strl1, strl2]))

{-
Inside add operator is defined string concatenation
-}
compileExpr (EAdd e1  op e2 ) = do
	(allType1, Just identif1, strl1) <- compileExpr e1
	(allType2, Just identif2, strl2) <- compileExpr e2
	types <- getllvmType allType1
	h <- ask
	newLabel <- freshLabel
	case (allType1, op) of
		(TypeString, Plus) -> do
			liftIO$hPutStrLn h ("\t%var"++ show(newLabel) ++" = call i8* @concat (i8* "++identif1++", i8*"++identif2++")")
			return (allType1, Just ("%var"++ show(newLabel)), (concat [strl1, strl2]))
		_ -> do
			oper <- compileAddOperators op
			liftIO$hPutStrLn h ("\t%var"++ show(newLabel) ++" = " ++ oper ++ " "++types++" "++identif1++", "++identif2)
			return (allType1, Just ("%var"++ show(newLabel)), (concat [strl1, strl2]))


{-
And expressions always uses 3 labels and uses phi expressions
-}
compileExpr (EAnd e1 e2 ) = do
	(allType1, Just identif1, strl1) <- compileExpr e1
	types <- getllvmType allType1
	h <- ask
	label1 <- freshLabel
	label2 <- freshLabel
	newLabel <- freshLabel
	startLabel <- gets$getCurrentLabelLlvm
	liftIO$hPutStrLn h ("\tbr i1 "++identif1 ++", label %l" ++ show(label1) ++ ", label %l" ++ show(label2))
	callLlvmStartLabel ("l"++show(label1))
	(allType2, Just identif2, strl2) <- compileExpr e2
	lastLabel <- gets$getCurrentLabelLlvm
	liftIO$hPutStrLn h ("\tbr label %l"++show(label2))
	callLlvmStartLabel ("l"++show(label2))
	liftIO$hPutStrLn h ("\t%var"++ show(newLabel) ++" = phi i1 [ 0, %" ++startLabel++" ] , [ "++identif2++", %"++lastLabel++ "]")
	return (allType1, Just ("%var"++ show(newLabel)), (concat [strl1, strl2]))

{-
Or expressions always uses 3 labels and uses phi expressions
-}
compileExpr (EOr e1 e2 ) = do
	(allType1, Just identif1, strl1) <- compileExpr e1
	types <- getllvmType allType1
	h <- ask
	label1 <- freshLabel
	label2 <- freshLabel
	newLabel <- freshLabel
	startLabel <- gets$getCurrentLabelLlvm
	liftIO$hPutStrLn h ("\tbr i1 "++identif1 ++", label %l" ++ show(label2) ++ ", label %l" ++ show(label1) )
	callLlvmStartLabel ("l"++show(label1))
	(allType2, Just identif2, strl2) <- compileExpr e2
	lastLabel <- gets$getCurrentLabelLlvm
	liftIO$hPutStrLn h ("\tbr label %l"++show(label2))
	callLlvmStartLabel ("l"++show(label2))
	liftIO$hPutStrLn h ("\t%var"++ show(newLabel) ++" = phi i1 [ 1, %" ++startLabel++" ] , [ "++identif2++", %"++lastLabel++ "]")
	return (allType1, Just ("%var"++ show(newLabel)), (concat [strl1, strl2]))

-- ################################### --
-- ##### End Compile Expression  ##### --
-- ################################### --


-- #################################### --
-- ##### Call llvm Sring helpers  ##### --
-- #################################### --

{-
Gets allocated variable type and returns of identifier of it.
According to test core022.lat sets initial alloca value.
-}
callLlvmAlloca :: String -> Execution(Integer)
callLlvmAlloca types = do
	h <- ask
	labelalloc <- freshLabel
	liftIO$hPutStrLn h ("\t%var"++ show(labelalloc) ++" = alloca "++ types)
	return labelalloc


callInitialLlvmAlloca :: String -> Execution(Integer)
callInitialLlvmAlloca types = do
	h <- ask
	labelalloc <- freshLabel
	liftIO$hPutStrLn h ("\t%var"++ show(labelalloc) ++" = alloca "++ types)
	case types of
		"i32" -> do
			liftIO$hPutStrLn h ("\tstore i32 0, i32* %var" ++ show(labelalloc))
			return labelalloc
		"i1" -> do
			liftIO$hPutStrLn h ("\tstore i1 0, i1* %var" ++ show(labelalloc))
			return labelalloc
		"i8*" -> return labelalloc
		n -> do
			liftIO$hPutStrLn h ("\tstore "++ n ++" null, "++ n ++"* %var" ++ show(labelalloc))
			return labelalloc


{-
Calls new llvm label.
-}
callLlvmStartLabel :: String -> Execution()
callLlvmStartLabel label = do
	h <- ask
	modify$setCurrentLabelLlvm (label)
	liftIO$hPutStrLn h (label++ ":")
	return()

{-
LLvm cast object
-}
callLlvmCast :: Ident -> Ident -> String -> Execution(Maybe String)
callLlvmCast from to identif = do
	h <- ask
	castLabel <- freshLabel
	llvmTypeFrom <- getllvmType (TypeClass from)
	llvmTypeTo <- getllvmType (TypeClass to)
	liftIO$hPutStrLn h ("\t%var"++ show(castLabel) ++" = bitcast "++llvmTypeFrom++" "++identif++" to "++ llvmTypeTo)
	return (Just ("%var"++ show(castLabel)))
-- ######################################## --
-- ##### End Call llvm Sring helpers  ##### --
-- ######################################## --
