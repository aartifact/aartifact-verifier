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
import Validation (validate, rawcxt, validate')
import Context (shStats)
import ContextOntology (ont)
import ContextRaw (cxtraw)

----------------------------------------------------------------
-- The target of the output, as specified by the command-line
-- arguments.

data OutputTarget = CmdLine | File String

----------------------------------------------------------------
-- Takes a file path in the form of a string, try to parse the
-- file into an abstract syntax, and run it.

showTD td = "(completed in "++
  (show$floor(((toRational$tdSec td)*(toRational$10^12)+
    (toRational$tdPicosec td))/10^9))++"ms)\n"

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
     ; (ss',stadat) <- return $ validate' cxtraw stmts
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

processSql :: String -> IO ()
processSql str =
  do { r <- parseP stdAloneExp "" $ "\\vbeg"++str++"\\vend"
     ; putStr $ case r of
         [ExpStmt _ (e,_)] -> expSql e
         _ -> "Error: SQL conversion failed."
     }

cmd :: OutputFormat -> [Bool] -> OutputTarget -> [String] -> IO ()
cmd _    _   out ["-sqlexp", expStr] = processSql expStr
cmd oFmt [_,stat,cx] out ("-lit":args) = cmd oFmt [True,stat,cx] out args
cmd oFmt [lit,_,cx] out ("-stat":args) = cmd oFmt [lit,True,cx] out args
cmd oFmt [lit,stat,_] out ("-rawcxt":args) = processRawCx
cmd _    fls out ("-o":f    :args) = cmd htmlOutFmt fls (File f) args
cmd _    fls out ("-html"   :args) = cmd htmlOutFmt fls out args
cmd _    fls out ("-cmdhtml":args) = cmd cmdHtmlOutFmt fls out args
cmd _    fls out ("-ansi"   :args) = cmd ansiOutFmt fls out args
cmd oFmt [lit,stat,_] out [s] =
  if lit then process oFmt out stat "" s
  else do {t<-readFile s; process oFmt out stat s t}
cmd _ _ _ _ = putStr $ showStmt noneOutFmt $ SystemError 
                "usage:\taa [-html|-ansi] \"path/file.ext\"\n\n"

----------------------------------------------------------------
-- The main function, useful if the interpreter is compiled.

main :: IO ()
main =
  do{ args <- getArgs
    ; cmd noneOutFmt [False,False,False] CmdLine args
    }

--eof
