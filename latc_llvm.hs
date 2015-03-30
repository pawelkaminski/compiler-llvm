module Main where
import System.IO
import System.Environment
import System.Process
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
import AnalizeLatte
import CompileLatte

main::IO()
main = do
    programName<-getProgName
    arguments<- getArgs
    case arguments of
        [] -> getContents >>= preprocess
        [n] -> readFile n >>= preprocess
        _ -> putStrLn$"Error Program Call:"++unwords(programName:arguments)

preprocess::String -> IO ()
preprocess s =
    case pProgram$ myLexer s of
        -- grammar error
        Bad a -> do
            hPutStr stderr ("ERROR\n" ++ a)
            error ("")
        Ok(Program t)-> do
            [n]<-getArgs
            --Works only on linux!
            -- program stops when error is evaluated
            -- tricky identifier form 100, assumption that none of class will have more than 100 atributes
            (cl, fn, label) <- evalStateT  (runReaderT(analize t) (stderr)) (M.empty, M.empty, [], 1, Nothing, "")
            hPutStr stderr ("OK")
            withFile ((pureName n) ++ "ll") WriteMode $ \output -> do
                hPutStrLn output initialStringLlvm
                evalStateT  (runReaderT(compile) (output)) (cl, fn, [], label, Nothing, "")
            runCommand ("llvm-as " ++ (pureName n) ++ "ll")
            --uncomment to create linked library binary file
            --runCommand ("llvm-link lib/runtime.bc " ++ (pureName n) ++ "bc -o prog.bc")
            return ()



{-
declare void @printInt(i32)
declare void @printString(i8*)
declare i32 @readInt()
declare i8* @readString()
declare i8* @concat(i8*, i8*)
+ new cast operators
-}

initialStringLlvm::String
initialStringLlvm = "declare void @printInt(i32)\n\
\declare void @printString(i8*)\n\
\declare i32 @readInt()\n\
\declare i8* @readString()\n\
\declare i8* @concat(i8*, i8*)\n\
\declare noalias i8* @_Znwm(i64)\n\
\declare void @llvm.memset.p0i8.i64(i8* nocapture, i8, i64, i32, i1)\n\n"

--base on words from prelude, splits string into pices using function Char -> Bool
wordsWhen:: (Char -> Bool) -> String -> [String]
wordsWhen p s =  case dropWhile p s of
                      "" -> []
                      s' -> w : wordsWhen p s''
                            where (w, s'') = break p s'

pureName::String->String
pureName n = case head n of
                --absolut path
                '/' -> "/" ++ (pureName' (wordsWhen (=='/') n))
                --relative path
                _   -> pureName' (wordsWhen (=='/') n)

pureName'::[String]->String
pureName' v = ((foldr (++) "" ((map (++"/") (reverse$tail$reverse v)))) ++ (splitLastName$reverse $wordsWhen (=='.') (last v)))

splitLastName::[String]->String
splitLastName x = case tail x of
                    [] -> ((head x) ++ ".")
                    x' -> (foldr (++) "" (map (++".") (reverse x')))
