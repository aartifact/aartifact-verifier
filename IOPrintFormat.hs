----------------------------------------------------------------
--
-- Aartifact
-- http://www.aartifact.org/src/
-- Copyright (C) 2008-2010
-- A. Lapets
--
-- This software is made available under the GNU GPLv3.
--
-- IOPrintFormat.hs
--   Functions for formatting text output (HTML entities and
--   ANSI escape sequences currently supported).

----------------------------------------------------------------
-- 

module IOPrintFormat where

----------------------------------------------------------------
-- The output format consists of a list of string functions
-- representing transformations to be applied to source text
-- based on the status of that text (valid, invalid, and so on).

type OutputFormat = [String -> String]

noneOutFmt :: OutputFormat
noneOutFmt = [id,id,id,id,id]

ansiOutFmt :: OutputFormat
ansiOutFmt =
  [ id
  , \s-> "\ESC[32m"++s
  , \s-> s++"\ESC[0m"
  , \s-> "\ESC[36m"++s++"\ESC[0m"
  , \s-> "\ESC[31m"++s++"\ESC[0m"
  ]

htmlOutFmt :: OutputFormat
htmlOutFmt =
  [ (let pr s = case s of
          ('\n':' ':cs) -> "\n&nbsp;"++pr cs
          (' ':' ':cs) -> "&nbsp; "++pr cs
          (c:cs) -> c:pr cs
          [] -> []
     in pr -- Fix &nbsp; entities.
    )
  , \s-> "<font color=\"lightsteelblue\">"++s
  , \s-> s++"</font>"
  , \s-> "<font color=\"cornflowerblue\">"++s++"</font>"
  , \s-> "<font color=\"firebrick\"><b>"++s++"</b></font>" -- #C82626
  ]

fmt [sp,_,_,_,_] "string" s = sp s
fmt [_,li,_,_,_] "ignore-left" s = li s
fmt [_,_,ri,_,_] "ignore-right" s = ri s
fmt [_,li,ri,_,_] "ignore" s = li (ri s)
fmt [_,_,_,va,_] "valid" s = va s
fmt [_,_,_,_,inv] "invalid" s = inv s

--eof
