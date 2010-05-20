----------------------------------------------------------------
--
-- aartifact
-- http://www.aartifact.org/src/
-- Copyright (C) 2008-2010
-- A. Lapets
--
-- This software is made available under the GNU GPLv3.
-- 
-- Main.hs
--   Main module. Parses command-line arguments, calls
--   appropriate routines, and tracks time spent.

----------------------------------------------------------------
-- 

module Main (main) where

import System.IO
import System.Environment (getArgs)
import System.Time (getClockTime,diffClockTimes,tdSec,tdPicosec)

import IOParser (parseP, program, stdAloneExp)
import IOSource
import IOPrintFormat
import ExpSQL (expSql)
import Validation (rawcxt, validate)
import ValidationPropositional (validatePropositional, propOnt)
import ValidationSyntaxVars (validateSyntaxVars)
import Context (shStats)
import ContextOntology (ont)
import ContextRaw (cxtraw)

----------------------------------------------------------------
-- The target of the output, as specified by the command-line
-- arguments.

data OutputTarget = CmdLine | File String

----------------------------------------------------------------
-- The logical system of the validation procedure to deploy.

data LogicalSystem = 
    FullContext
  | Propositional
  | SyntaxVars

----------------------------------------------------------------
-- Takes a file path in the form of a string, try to parse the
-- file into an abstract syntax, and run it.

showTD td = "(completed in "++
  (show$floor(((toRational$tdSec td)*(toRational$10^12)+
    (toRational$tdPicosec td))/10^9))++"ms)\n"

processSql :: String -> IO ()
processSql str =
  do { r <- parseP stdAloneExp "" $ "\\vbeg"++str++"\\vend"
     ; putStr $ case r of
         [ExpStmt _ (e,_)] -> expSql e
         _ -> "Error: SQL conversion failed."
     }

processRawCx :: IO ()
processRawCx =
  do { ont <- readFile "ontology"
     ; ont <- parseP program "<ontology>" ont
     ; writeFile "ContextRaw.hs" $ 
       "module ContextRaw where\nimport ExpConst\nimport Exp\nimport ContextAux\nimport MapUsingRBTree\ncxtraw="
       ++((let r l = case l of '%':' ':'1':xs->r xs; x:xs->x:r xs; []->[] in r) $ show (rawcxt ont))
     }

process :: OutputFormat -> OutputTarget -> Bool -> String -> String -> IO ()
process oFmt out stat fname txt =
  let (cr,wr) = case out of
        CmdLine -> (putStr "", putStr)
        File outf -> (writeFile outf "", appendFile outf)
  in
  do { --ont <- readFile "ontology"
     --; ont <- parseP program "<ontology>" ont
     ; t0 <- getClockTime
     ; stmts <- parseP program fname txt
     ; cr
     ; (ss',stadat) <- return $ validate cxtraw stmts
     ; wr $ fmt oFmt "output" $ showStmts oFmt $ ss'
     ; t1 <- getClockTime
     ; if stat then 
         writeFile "stat.dat" $ 
         --fmt oFmt "output" $ 
         --fmt oFmt "ignore" $ 
         (("\n"++showTD (diffClockTimes t1 t0))++("\n"++shStats stadat))
       else
         return ()
     }

processSyntaxVars :: OutputFormat -> OutputTarget -> Bool -> String -> String -> IO ()
processSyntaxVars oFmt out stat fname txt =
  let (cr,wr) = case out of
        CmdLine -> (putStr "", putStr)
        File outf -> (writeFile outf "", appendFile outf)
  in
  do { t0 <- getClockTime
     ; stmts <- parseP program fname txt
     ; cr
     ; (ss',stadat) <- return $ validateSyntaxVars stmts
     ; wr $ fmt oFmt "output" $ showStmts oFmt $ ss'
     ; t1 <- getClockTime
     ; if stat then 
         writeFile "stat.dat" $ 
         --fmt oFmt "output" $ 
         --fmt oFmt "ignore" $ 
         (("\n"++showTD (diffClockTimes t1 t0))++("\n"++shStats stadat))
       else
         return ()
     }

processPropositional :: OutputFormat -> OutputTarget -> Bool -> String -> String -> IO ()
processPropositional oFmt out stat fname txt =
  let (cr,wr) = case out of
        CmdLine -> (putStr "", putStr)
        File outf -> (writeFile outf "", appendFile outf)
  in
  do { ont <- parseP program "<ontology>" propOnt
     ; t0 <- getClockTime
     ; stmts <- parseP program fname txt
     ; cr
     ; (ss',stadat) <- return $ validatePropositional ont stmts
     ; wr $ fmt oFmt "output" $ showStmts oFmt $ ss'
     ; t1 <- getClockTime
     ; if stat then 
         writeFile "stat.dat" $ 
         --fmt oFmt "output" $ 
         --fmt oFmt "ignore" $ 
         (("\n"++showTD (diffClockTimes t1 t0))++("\n"++shStats stadat))
       else
         return ()
     }

cmd :: LogicalSystem -> OutputFormat -> [Bool] -> OutputTarget -> [String] -> IO ()
cmd lgsy _    _   out ["-sqlexp", expStr] = processSql expStr
cmd lgsy oFmt [_,stat,cx]  out ("-lit":args) = cmd lgsy oFmt [True,stat,cx] out args
cmd lgsy oFmt [lit,_,cx]   out ("-stat":args) = cmd lgsy oFmt [lit,True,cx] out args
cmd lgsy oFmt [lit,stat,_] out ("-rawcxt":args) = processRawCx
cmd lgsy _    fls out ("-o":f          :args) = cmd lgsy htmlOutFmt fls (File f) args
cmd lgsy _    fls out ("-html"         :args) = cmd lgsy htmlOutFmt fls out args
cmd lgsy _    fls out ("-cmdhtml"      :args) = cmd lgsy cmdHtmlOutFmt fls out args
cmd lgsy _    fls out ("-ansi"         :args) = cmd lgsy ansiOutFmt fls out args
cmd lgsy _    fls out ("-propositional":args) = cmd Propositional ansiOutFmt fls out args
cmd lgsy _    fls out ("-fullcontext"  :args) = cmd FullContext ansiOutFmt fls out args
cmd lgsy _    fls out ("-syntaxvars"  :args)  = cmd SyntaxVars ansiOutFmt fls out args
cmd lgsy oFmt [lit,stat,_] out [s] =
  if lit then process oFmt out stat "" s
  else case lgsy of
    FullContext -> do {t<-readFile s; process oFmt out stat s t}
    Propositional -> do {t<-readFile s; processPropositional oFmt out stat s t}
    SyntaxVars -> do {t<-readFile s; processSyntaxVars oFmt out stat s t}
 
cmd _ _ _ _ _ = putStr $ showStmt noneOutFmt $ SystemError 
                "usage:\taa [-html|-ansi] \"path/file.ext\"\n\n"

----------------------------------------------------------------
-- The main function, useful if the interpreter is compiled.

main :: IO ()
main =
  do{ args <- getArgs
    ; cmd FullContext noneOutFmt [False,False,False] CmdLine args
    }

--eof
