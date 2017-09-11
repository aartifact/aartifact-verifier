----------------------------------------------------------------
--
-- | aartifact
--   http://www.aartifact.org/
--
-- @src\/IOPrintFormat.hs@
--
--   Functions for formatting text output (HTML entities and
--   ANSI escape sequences currently supported).
--

----------------------------------------------------------------
--

module IOPrintFormat where

----------------------------------------------------------------
-- | The output format consists of a list of string functions
--   representing transformations to be applied to source text
--   based on that text's status (valid, invalid, and so on).

type OutputFormat = [String -> String]

noneOutFmt :: OutputFormat
noneOutFmt = [id,id,id,id,id,id,id,id]

ansiOutFmt :: OutputFormat
ansiOutFmt =
  [ id
  , id
  , \s-> "\ESC[32m"++s
  , \s-> s++"\ESC[0m"
  , \s-> "\ESC[32m"++s++"\ESC[0m" --valid
  , \s-> "\ESC[36m"++s++"\ESC[0m" --invalid
  , \s-> "\ESC[36m"++s++"\ESC[0m" --contradiction
  , \s-> "\ESC[31m"++s++"\ESC[0m" --syntax
  ]

asciiOutFmt :: OutputFormat
asciiOutFmt =
  [ id
  , id
  , \s-> ""++s
  , \s-> s++""
  , \s-> "!!>"++s++"<!!" --valid
  , \s-> "<<<"++s++">>>" --invalid
  , \s-> ">>>"++s++"<<<" --contradiction
  , \s-> "??>"++s++"<??" --syntax
  ]

cmdHtmlOutFmt :: OutputFormat
cmdHtmlOutFmt =
  let (ou:fs) = htmlOutFmt
      ou' = 
       (let pr s = case s of
                    ('\n':cs) -> "\n"++pr cs
                    (c:cs) -> c:pr cs
                    [] -> []
        in pr)
  in (ou':fs)

htmlOutFmt :: OutputFormat
htmlOutFmt =
  [ (let pr s = case s of
          ('\n':cs) -> "\n<br />"++pr cs
          (c:cs) -> c:pr cs
          [] -> []
     in (\s -> "<code>"++pr s++"</code>")
    ),
    (let pr s = case s of
          ('\n':' ':cs) -> "\n&nbsp;"++pr cs
          (' ':' ':cs) -> "&nbsp; "++pr cs
          (c:cs) -> c:pr cs
          [] -> []
     in pr -- Fix &nbsp; entities.
    )
  , \s-> "<font color=\"#B0C4DE\">"++s --lightsteelblue
  , \s-> s++"</font>"
  , \s-> "<font color=\"#6495ED\">"++s++"</font>" --cornflowerblue
  , \s-> "<font color=\"#EAC100\"><b>"++s++"</b></font>" -- invalid (firebrick,#C82626)
  , \s-> "<font color=\"#B22222\"><b>"++s++"</b></font>" -- contradiction
  , \s-> "<font color=\"#E46D00\"><b><i>"++s++"</i></b></font>"
  ]

fmt [ou,_,_,_,_,_,_,_] "output" s = ou s
fmt [_,sp,_,_,_,_,_,_] "string" s = sp s
fmt [_,_,li,_,_,_,_,_] "ignore-left" s = li s
fmt [_,_,_,ri,_,_,_,_] "ignore-right" s = ri s
fmt [_,_,li,ri,_,_,_,_] "ignore" s = li (ri s)
fmt [_,_,_,_,va,_,_,_] "valid" s = va s
fmt [_,_,_,_,_,inv,_,_] "invalid" s = inv s
fmt [_,_,_,_,_,_,cntr,_] "contradiction" s = cntr s
fmt [_,_,_,_,_,_,_,syn] "invalidsyntax" s = syn s

--eof