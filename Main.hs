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
import Validation (validate)
import ContextOntology (ont)

----------------------------------------------------------------
-- Takes a file path in the form of a string, try to parse the
-- file into an abstract syntax, and run it.

showTD td = "(completed in "++
  (show$floor(((toRational$tdSec td)*(toRational$10^12)+
    (toRational$tdPicosec td))/10^9))++"ms)\n"

process :: OutputFormat -> String -> String -> IO ()
process oFmt fname txt =
  do { --ont <- readFile "ontology"
     ; ont <- parseP program "<ontology>" ont
     ; t0 <- getClockTime
     ; stmts <- parseP program fname txt
     ; putStr $ showStmts oFmt $ validate ont stmts
     ; t1 <- getClockTime
     ; putStr $ fmt oFmt "ignore" $ "\n"++showTD (diffClockTimes t1 t0)
     }

processSql :: String -> IO ()
processSql str =
  do { r <- parseP stdAloneExp "" $ "\\vbeg"++str++"\\vend"
     ; putStr $ case r of
         [ExpStmt _ (e,_)] -> expSql e
         _ -> "Error: SQL conversion failed."
     }

procCmd :: OutputFormat -> Bool -> [String] -> IO ()
procCmd _ _ ["-sqlexp", expStr] = processSql expStr
procCmd oFmt lit ("-lit":args) = procCmd oFmt True args
procCmd _ lit ("-html":args) = procCmd htmlOutFmt lit args
procCmd _ lit ("-ansi":args) = procCmd ansiOutFmt lit args
procCmd oFmt lit [s] = if lit then process oFmt "" s
                       else do { t<-readFile s; process oFmt s t}
procCmd _ _ _ = putStr $ showStmt noneOutFmt $ SystemError 
                "usage:\taa [-html|-ansi] \"path/file.ext\"\n\n"

----------------------------------------------------------------
-- The main function, useful if the interpreter is compiled.

main :: IO ()
main =
  do{ args <- getArgs
    ; procCmd noneOutFmt False args
    }

--eof
