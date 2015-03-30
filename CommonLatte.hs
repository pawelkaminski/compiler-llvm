module CommonLatte where
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

{-
All basic variable type
-}
data AllTypes = TypeInteger | TypeBool | TypeString | TypeClass Ident | TypeVoid

{-
Basic types for trivial values optimalization
-}
data BasicTypesValue = TypeInt Integer | TypeBoolean Bool


instance Show AllTypes where
	show(TypeInteger) = "integer"
	show(TypeBool) = "bool"
	show(TypeString) = "string"
	show(TypeClass a) = "class " ++ (show a)
	show(TypeVoid) = "void"


instance Eq AllTypes where
    TypeInteger == TypeInteger = True
    TypeBool == TypeBool = True
    TypeString == TypeString = True
    TypeClass a == TypeClass b = a == b
    TypeVoid == TypeVoid = True
    _==_ = False


-- single block memory ~ map: key - variable ident, values - types
type Memory = M.Map Ident (AllTypes, Integer)
-- functions ~ map: key - function ident, values - type, arguments list (program name, type, llvm name), instructions
type Functions = M.Map Ident (AllTypes, [(Ident, AllTypes, Integer)], Block, String)
-- functions ~ map: key - function ident, values -  map, attributes map
type Class = M.Map Ident (Maybe Ident, Functions, Memory)
-- Integer is label counter, ident is build class name, String is current build label
type StateInfo = (Class, Functions, [(Memory, Bool)], Integer, Maybe Ident, String)
--type Procedures = M.Map Ident String --store output file descriptor at monad reader
--type Execution = ReaderT (Procedures,Handle) (StateT ([Memory], Integer) IO)
type Execution = ReaderT (Handle) (StateT (StateInfo) IO)


-- ####################################################### --
-- ##### llvm identifier counter and function label  ##### --
-- ####################################################### --

freshLabel :: Execution Integer
freshLabel = do
	v <- gets$getActualLabel
	modify$updateLabel
	return (v)

updateLabel :: StateInfo -> StateInfo
updateLabel (c,f, m, l, cl, ls) = (c,f, m,l+1, cl, ls)

getActualLabel :: StateInfo -> Integer
getActualLabel (c,f, m, l, cl, ls) = l

setCurrentLabelLlvm :: String -> StateInfo -> StateInfo
setCurrentLabelLlvm newls (c,f, m, l, cla, ls) = (c, f, m, l, cla, newls)

getCurrentLabelLlvm :: StateInfo -> String
getCurrentLabelLlvm (_, _, _, _, _, ls) = ls

-- ########################################################### --
-- ##### end llvm identifier counter and function label  ##### --
-- ########################################################### --


-- ############################################################## --
-- ##### memory, functions, class, variables modifications  ##### --
-- ############################################################## --

memoryAddLevel :: Bool -> StateInfo -> StateInfo
memoryAddLevel bool (c,f, ms, l, cla, ls) = (c,f, ((M.empty, bool) :ms), l, cla, ls)

memoryRemoveLevel :: StateInfo -> StateInfo
memoryRemoveLevel (c,f, m:ms, l, cla, ls) = (c,f, ms, l, cla, ls)

memoryAddVariable :: Ident -> AllTypes -> Integer -> StateInfo -> StateInfo
memoryAddVariable id t int (c,f, (m, bool):ms, l, cla, ls) =  (c,f, ((M.insert id (t, int) m),bool):ms, l, cla, ls)

memorySetFunction :: Ident -> AllTypes-> [(Ident, AllTypes, Integer)] ->  Block -> String-> StateInfo -> StateInfo
memorySetFunction id t arg b label (c, f, m, i, cla, ls) = (c, (M.insert id (t, arg, b, label) f), m, i, cla, ls)

memoryGetVariableOneLevel :: Ident -> StateInfo -> Maybe (AllTypes, Integer)
memoryGetVariableOneLevel id (c,f, ((m,bool):mem), l, cla, ls) = M.lookup id m

memoryGetVariable :: Ident -> StateInfo -> Maybe (AllTypes, Integer)
memoryGetVariable id (c,f, mem, l, cla, ls) = memoryGetVariableFromMemory id mem

{-
Gets variable form every possible memory level (bool == True - last level)
-}
memoryGetVariableFromMemory :: Ident -> [(Memory, Bool)] -> Maybe (AllTypes, Integer)
memoryGetVariableFromMemory id [] = Nothing
memoryGetVariableFromMemory id ((m, bool):ms) = case M.lookup id m of
	Just x -> Just x
	Nothing -> case bool of
		True -> Nothing
		False -> memoryGetVariableFromMemory id ms

memoryRemoveFunction :: Ident -> StateInfo -> StateInfo
memoryRemoveFunction id (c,f, m, l, cla, ls) = (c, (M.delete id f), m, l, cla, ls)

memorySetClass :: Ident -> Maybe Ident -> Functions-> Memory -> StateInfo -> StateInfo
memorySetClass id parent meth attr (c, f, m, i, cla, ls) = ((M.insert id (parent, meth, attr) c), f, m, i, cla, ls)

memorySetCurrentClass :: Ident -> StateInfo -> StateInfo
memorySetCurrentClass id (c, f, m, i, _, ls) = (c, f, m, i, (Just id), ls)

memoryGetCurrentClass :: StateInfo -> Maybe Ident
memoryGetCurrentClass (_, _, _, _, Nothing , _) = Nothing
memoryGetCurrentClass (_, _, _, _, (Just cls), _) = (Just cls)

memoryRemoveCurrentClass ::  StateInfo -> StateInfo
memoryRemoveCurrentClass (c, f, m, i, cla, ls) = (c, f, m, i, Nothing, ls)
-- ################################################################## --
-- ##### end memory, functions, class, variables modifications  ##### --
-- ################################################################## --

-- ##################################### --
-- ##### embeded functions helpers ##### --
-- ##################################### --

setEmbededFunctions :: Execution()
setEmbededFunctions = do
	modify$memorySetFunction (Ident "printInt") TypeVoid [((Ident "x"), TypeInteger, 0)] (Block [Empty]) ("@printInt")
	modify$memorySetFunction (Ident "printString") TypeVoid [((Ident "x"), TypeString, 0)] (Block [Empty]) ("@printString")
	modify$memorySetFunction (Ident "error") TypeVoid [] (Block [Empty]) ("@error")
	modify$memorySetFunction (Ident "readInt") TypeInteger [] (Block [Empty]) ("@readInt")
	modify$memorySetFunction (Ident "readString") TypeString [] (Block [Empty]) ("@readString")
	return ()

removeEmbededFunctions :: Execution()
removeEmbededFunctions = do
	modify$memoryRemoveFunction (Ident "printInt")
	modify$memoryRemoveFunction (Ident "printString")
	modify$memoryRemoveFunction (Ident "error")
	modify$memoryRemoveFunction (Ident "readInt")
	modify$memoryRemoveFunction (Ident "readString")
	return ()

-- ######################################### --
-- ##### end embeded functions helpers ##### --
-- ######################################### --


-- ################################################## --
-- ##### geting functions and classes functions ##### --
-- ################################################## --

getAllClasses::StateInfo -> [(Ident, (Maybe Ident, Functions, Memory))]
getAllClasses (c, _, _ , _, _, _)=  M.toList c

getAllFunctions::StateInfo -> [(Ident, (AllTypes, [(Ident, AllTypes, Integer)], Block, String))]
getAllFunctions (_, f, _ , _, _, _)=  M.toList f

getAllClassesFunctionsAndLabel::StateInfo -> (Class, Functions, Integer)
getAllClassesFunctionsAndLabel (c, f, _ , l, _, _)=  (c, f, l)

getFunction :: Ident -> StateInfo -> Maybe (AllTypes, [(Ident, AllTypes, Integer)], Block, String)
getFunction id (c, f, m, i, _, _) = M.lookup id f

getClass :: Ident -> StateInfo -> Maybe (Maybe Ident, Functions, Memory)
getClass id (c, _, _, _, _, _) = M.lookup id c

{-
 necessary to create new object
-}
getMemLength :: Maybe (Maybe Ident, Functions, Memory) -> Int
getMemLength Nothing = 0
getMemLength (Just (_, _, m)) = (M.size m)*8

getClassLength :: Ident -> StateInfo -> Int
getClassLength id (c, _, _, _, _, _) = getMemLength$ M.lookup id c

-- ###################################################### --
-- ##### end geting functions and classes functions ##### --
-- ###################################################### --

{-
transforms grammar type to compiler AllTypes
-}
getType::Type -> Execution(AllTypes)
getType (PureType Int) = return(TypeInteger)
getType (PureType Str) = return(TypeString)
getType (PureType Bool) = return(TypeBool)
getType (PureType Void) = return(TypeVoid)
getType (PureType (Class id)) = return(TypeClass id)

