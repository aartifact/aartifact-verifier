----------------------------------------------------------------
--
-- | aartifact
--   http://www.aartifact.org/
--
-- @src\/Main.hs@
--
--   Main module. Parses command-line arguments, calls
--   appropriate routines, and tracks time spent.
--

----------------------------------------------------------------
-- 

module Main (main) where

import System.IO
import System.Environment (getArgs)
import System.Time (getClockTime,diffClockTimes,tdSec,tdPicosec)
import Directory (getDirectoryContents, doesFileExist)

import IOParser (parseP, program, stdAloneExp)
import IOSource
import IOPrintFormat
import ExpSQL (expSql)
import Validation (rawCxt, validate, validateBasic)
import ValidationPropositional (validatePropositional)
import ValidationSyntaxVars (validateSyntaxVars)
import Context (shStats)
import ContextRaw (compiledSysList, rawsys)

----------------------------------------------------------------
-- | The target of the output, as specified by the command-line
--   arguments.

data OutputTarget = CmdLine | File String

----------------------------------------------------------------
-- | The logical system of the validation procedure to deploy.

type System = String
type Procedure = String

----------------------------------------------------------------
-- | Takes a file path in the form of a string, try to parse the
--   file into an abstract syntax, and run it.

rmvEnt = let r l = case l of '%':' ':'1':xs->r xs; x:xs->x:r xs; []->[] in r
commaSep l = foldr (\x y -> x++", "++y) (last l) (init l)

showTD td = "(completed in "++
  (show$floor(((toRational$tdSec td)*(toRational$10^12)+
    (toRational$tdPicosec td))/10^9))++"ms)\n"

readFiles :: [String] -> IO [[Stmt]]
readFiles [] = do { return [] }
readFiles (f:fs) =
  do { syss <- readFiles fs
     ; sysStr <- readFile $ "systems/" ++ f
     ; sys <- parseP program f sysStr  
     ; return $ sys:syss
     }

processSql :: String -> IO ()
processSql str =
  do { r <- parseP stdAloneExp "" $ "\\vbeg"++str++"\\vend"
     ; putStr $ case r of
         [ExpStmt _ (e,_)] -> expSql e
         _ -> "Error: SQL conversion failed."
     }

processRawCx :: IO ()
processRawCx =
  do { fs <- getDirectoryContents "./systems"
     ; fs <- return $ filter (\f -> not $ (f==".") || (f=="..")) fs     
     ; syss <- readFiles fs
     ; syssStrs <- return $ map (rmvEnt.show.rawCxt) syss
     ; fSyssStrs <- return $ map (\(f,s)->"\nrawsys \""++f++"\" = "++s) $ zip fs syssStrs
     ; allStr <- return $ foldr (++) [] fSyssStrs
     ; writeFile "ContextRaw.hs" $ 
       "module ContextRaw where\nimport ExpConst\nimport Exp\nimport ExpPredicate\nimport Context\nimport ContextAux\nimport MapUsingRBTree\n"
       ++ "compiledSysList = [" ++ commaSep ["\""++f++"\"" | f<-fs] ++ "]\n"
       ++ allStr
       ++ "\nrawsys _ = stateEmpty"
     }

clearRawCx :: IO ()
clearRawCx =
  do { writeFile "ContextRaw.hs" $ 
       "module ContextRaw where\nimport ExpConst\nimport Exp\nimport Context\nimport ContextAux\nimport MapUsingRBTree\n"
       ++ "compiledSysList = []\n"
       ++ "rawsys _ = stateEmpty"
     }

processSys :: System -> Procedure -> OutputFormat -> OutputTarget -> Bool -> String -> String -> IO ()
processSys sys proc oFmt out stat fname txt =
  let (cr,wr) = case out of
        CmdLine -> (putStr "", putStr)
        File outf -> (writeFile outf "", appendFile outf)
  in
  do { sysCxt <- getSysCxt sys
     ; t0 <- getClockTime
     ; stmts <- parseP program fname txt
     ; cr
     ; (ss',stadat) <- return $ (getValidate proc) sysCxt stmts
     ; wr $ fmt oFmt "output" $ showStmts oFmt $ ss'
     ; t1 <- getClockTime
     ; if stat then 
         writeFile "stat.dat" $ --fmt oFmt "output" $ fmt oFmt "ignore" $ 
         (("\n"++showTD (diffClockTimes t1 t0))++("\n"++shStats stadat))
       else
         return ()
     }

getValidate proc = case proc of
  "syntaxvars" -> validateSyntaxVars
  "propositional" -> validatePropositional
  "basic" -> validateBasic
  "full" -> validate
  _ -> validate

getSysCxt sys =
  if sys `elem` compiledSysList then return $ rawsys sys
  else
    do { ex <- doesFileExist $ sys
       ; syStr <- if ex then readFile $ sys else return ""
       ; syStmts <- parseP program sys syStr
       ; return $ rawCxt syStmts
       }

cmd :: System -> Procedure -> OutputFormat -> [Bool] -> OutputTarget -> [String] -> IO ()
cmd _  _  _    _           out ["-sqlexp", expStr] = processSql expStr
cmd sy pr oFmt [_,stat,cx] out ("-lit":args)   = cmd sy pr oFmt [True,stat,cx] out args
cmd sy pr oFmt [lit,_,cx]  out ("-stat":args)  = cmd sy pr oFmt [lit,True,cx] out args
cmd _  _  _    _   out ("-compilesystems":_)   = processRawCx
cmd _  _  _    _   out ("-compilenosystems":_) = clearRawCx
cmd sy pr _    fls out ("-o":f       :args)    = cmd sy pr htmlOutFmt fls (File f) args
cmd sy pr _    fls out ("-html"      :args)    = cmd sy pr htmlOutFmt fls out args
cmd sy pr _    fls out ("-cmdhtml"   :args)    = cmd sy pr cmdHtmlOutFmt fls out args
cmd sy pr _    fls out ("-ansi"      :args)    = cmd sy pr ansiOutFmt fls out args
cmd _  pr oFmt fls out ("-system"    :sy:args) = cmd sy pr oFmt fls out args
cmd sy _  oFmt fls out ("-procedure" :pr:args) = cmd sy pr oFmt fls out args
cmd sy pr  oFmt [lit,stat,_] out [s] =
  if lit then processSys sy pr oFmt out stat "" s
  else do {t<-readFile s; processSys sy pr oFmt out stat s t}
cmd _ _ _ _ _ _ = putStr $ showStmt noneOutFmt $ SystemError 
                "usage:\taa [-html|-ansi] \"path/file.ext\"\n\n"

----------------------------------------------------------------
-- | The main function, useful if the interpreter is compiled.

main :: IO ()
main =
  do{ args <- getArgs
    ; cmd "fullcontext" "full" noneOutFmt [False,False,False] CmdLine args
    }

--eof