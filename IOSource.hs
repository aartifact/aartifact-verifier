----------------------------------------------------------------
--
-- aartifact
-- http://www.aartifact.org/src/
-- Copyright (C) 2008-2011
-- A. Lapets
--
-- This software is made available under the GNU GPLv3.
--
-- IOSource.hs
--   Functions for manipulating the source text of a formal
--   argument. Uses parser structures from the Parsec library.

----------------------------------------------------------------
-- 

module IOSource where

import Text.ParserCombinators.Parsec

import IOPrintFormat
import Exp
import Context

----------------------------------------------------------------
-- Helper functions for manipulating source text strings.

-- Normalize the input and output text. We actually want to
-- parse the "commented" text (see comment definition at bottom
-- of "Parse.hs") so we "invert" comments by adding "\\vend" and
-- "\\vbeg" to the ends of the document.

normOut :: String -> String
normOut s = unlines(init (tail (lines s)))

normIn :: String -> String
normIn s = "\\vend\n"++pr s++"\n\\vbeg" where
  pr s = case s of
    "" -> ""
    ':':cs -> ' ':pr cs
    '\\':'&':cs -> '\\':'&':pr cs
    '&':cs -> ' ':pr cs
    c:cs -> c:pr cs

-- These functions return the input source text based on the
-- source position (as represented by the "SourcePos" type from
-- the "Parsec" library).

srcTxtFrom s p1 = (init.unlines) $ drop (sourceLine p1-1) (lines s)
srcTxt s p1 p2 = 
  let getLines i j ls = take (j-i) $ drop i ls
      ls = getLines (sourceLine p1-1) (sourceLine p2) (lines s)
  in (init.unlines) $ case ls of
    [] -> []
    [l] -> [take (sourceColumn p2 - sourceColumn p1) 
                                   (drop (sourceColumn p1-1) l)]
    ls -> [f]++ms++[l]
      where f = drop (sourceColumn p1 - 1) $ head ls
            ms = init (tail ls)
            l = take (sourceColumn p2 - 1) (last ls)

----------------------------------------------------------------
-- Concrete syntax of source for expressions, with accommodation
-- for tags and annotations that can correspond to errors or
-- verification results.

data Err = ErrUnbound [String] | ErrVer String | ErrContra
data Src =
    Src String
  | SrcStat Stat Src
  | SrcReport Report Src
  | SrcOk Src
  | SrcErr Src Err
  | SrcL [String] [Src]
  | SrcIg [Src]

showWithErr oFmt err s = case err of
  ErrUnbound _ -> fmt oFmt "invalid" s
  ErrVer es -> fmt oFmt "invalid" s
  ErrContra -> fmt oFmt "contradiction" s

showSrc oFmt src = case src of
  Src s -> fmt oFmt "string" s
  SrcStat _ s -> showSrc oFmt s
  SrcReport _ s -> showSrc oFmt s
  SrcOk s -> fmt oFmt "valid" $ showSrc oFmt s
  SrcErr s err -> showWithErr oFmt err $ showSrc oFmt s
  SrcL ts ss -> sht ts ss where
    sht (t:ts) ss = fmt oFmt "string" t ++ shs ts ss
    sht [] [] = ""
    sht [] ss = shs [] ss
    shs ts (s:ss) = showSrc oFmt s ++ sht ts ss
    shs [] [] = ""
    shs ts [] = sht ts []
  SrcIg ss -> concat $ map (showSrc oFmt) ss

isErr :: Src -> Bool
isErr s = case s of
  Src _ -> False
  SrcStat _ s -> isErr s
  SrcReport _ s -> isErr s
  SrcOk _ -> False
  SrcErr _ _ -> True
  SrcL _ srcs -> or $ map isErr srcs
  SrcIg srcs -> or $ map isErr srcs

statSrc s = case s of
  Src _ -> [[], []]
  SrcStat s _ -> s
  SrcReport s _ -> [[], []]
  SrcOk s -> statSrc s
  SrcErr s _ -> statSrc s
  SrcL _ ss -> statSrc $ last ss
  SrcIg ss -> statSrc $ last ss

----------------------------------------------------------------
-- Abstract syntax for a full source document (consisting of a
-- list of statements).

data IntroTyp = Variable | Constant | RelOp | SetOp | ArithOp
data ExpTyp = Assume | Assert | Consider
data Stmt =
    Text String
  | Intro Src IntroTyp [Name]
  | ExpStmt ExpTyp (Exp, Src)
  | Include String [Stmt]
  | IncludeWrap String Stmt
  | SyntaxError String
  | SystemError String

mkIncludeWrap :: String -> Stmt -> Stmt
mkIncludeWrap n (IncludeWrap n' r) = (IncludeWrap n' r)
mkIncludeWrap n r = IncludeWrap n r

showStmt :: OutputFormat -> Stmt -> String
showStmt oFmt r = case r of
  Text srcStr -> fmt oFmt "string" srcStr
  Intro src _ _ -> showSrc oFmt src
  ExpStmt _ (_,src) -> showSrc oFmt src
  IncludeWrap n r  -> "Included dependency processed."     --fmt html "green" $ "In [["++n++"]]: "
  SystemError s -> "\n *** System error *** : " ++ s
  SyntaxError s -> fmt oFmt "invalidsyntax" $ s --"\n\n *** Syntax error in statement immediately below *** : \n\n" ++

showStmts :: OutputFormat -> [Stmt] -> String
showStmts oFmt rs = case getReportStmts rs of
  Nothing -> fmtIgnore oFmt $ normOut $ foldr (++) "" $ map (showStmt oFmt) rs
  Just r -> r

fmtIgnore oFmt str = fmt oFmt "ignore" $ pr str where
  pr str = case str of 
    ('\\':'v':'b':'e':'g':cs) -> fmt oFmt "ignore-right" "\\vbeg" ++ pr cs
    ('\\':'v':'e':'n':'d':cs) -> fmt oFmt "ignore-left" "\\vend" ++ pr cs
    (c:cs) -> c:pr cs
    [] -> []

----------------------------------------------------------------
-- Collects the state report from the results, if there is one.

type Report = String

getReportStmts :: [Stmt] -> Maybe Report
getReportStmts ss = case concat (map getReportStmt ss) of
  [] -> Nothing
  r:_ -> Just r

getReportStmt :: Stmt -> [Report]
getReportStmt (ExpStmt _ (_,src)) = getReportSrc src
getReportStmt _ = []

getReportSrc src = case src of
  Src _ -> []
  SrcStat _ s -> []
  SrcReport r s -> [r]
  SrcOk _ -> []
  SrcErr _ _ -> []
  SrcL _ srcs -> concat $ map getReportSrc srcs
  SrcIg srcs -> concat $ map getReportSrc srcs

--eof
