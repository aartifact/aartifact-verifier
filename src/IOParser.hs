----------------------------------------------------------------
--
-- | aartifact
--   http://www.aartifact.org/
--
-- @src\/IOParse.hs@
--
--   Parser implementation using the Parsec library.
--

----------------------------------------------------------------
--

module IOParser (parseP, program, stdAloneExp) where

import Text.ParserCombinators.Parsec
import qualified Text.ParserCombinators.Parsec.Token as P
import Text.ParserCombinators.Parsec.Expr
import Text.ParserCombinators.Parsec.Language
import Data.List (partition, sort, isPrefixOf)
import Data.Maybe (catMaybes, listToMaybe)
import Data.Ratio

import IOParserOps
import IOSource
import ExpConst
import Exp
import Validation

----------------------------------------------------------------
-- | Exported parse function.

parseP :: Parse [Stmt] -> String -> String -> IO [Stmt]
parseP p fname tx =
  do{ tx' <- return $ normIn tx
    ; r <- return $ runParser p (PS tx' [fname] opsState0 [True]) "" tx'
    ; return $ case r of
       Right ss -> ss
       Left e -> [SyntaxError $ srcTxtFrom tx' (errorPos e)]
    }

----------------------------------------------------------------
-- | Parser state representation.
--   The parser state maintains a stack of inclusions
--   (filenames) to detect recursive inclusion dependencies.

type FileSysPath = String
type Flag = Bool
data ParseState = PS String [FileSysPath] OpsState [Flag]
type Parse a = GenParser Char ParseState a

getSrc :: Parse String
getSrc = do{ PS txt _ _ _ <- getState; return txt }
getPos = getPosition

----------------------------------------------------------------
-- Parser definitions ------------------------------------------
----------------------------------------------------------------

----------------------------------------------------------------
-- | Top-level parsers.

stdAloneExp :: Parse [Stmt]
stdAloneExp = do{ whiteSpace; (e,s,_) <- phraseP; eof
                ; return $ [ExpStmt Consider (e,s)] }

program :: Parse [Stmt]
program =
  do{ s <- getSrc
    ; pos1 <- getPos 
    ; whiteSpace
    ; pos2 <- getPos
    ; ss <- many stmtOrErrP
    ; eof
    ; return $ [Text (srcTxt s pos1 pos2)]++concat ss
    }

----------------------------------------------------------------
-- | Statements.

introKeys = ["Introduce"]
assumpKeys = ["Assume", "Assume that"]
assertKeys = ["Assert", "Assert that"]
considerKeys = ["Consider"]

stmtOrErrP = stmtP <?|> 
  do{ src <- getSrc
    ; pos <- getPos
    ; anyChar
    ; pos2 <- getPos
    ; ss <- many stmtOrErrP
    ; errTxt <- return $ srcTxt src pos pos2
    ; return $ 
      case concat ss of
        (SyntaxError t):ss -> [SyntaxError $ errTxt++t] ++ ss
        ss -> [SyntaxError $ errTxt] ++ ss
    }

stmtP :: Parse [Stmt]
stmtP = introP 
    <|> (expStmtP assumpKeys Assume <?> "assumption")
    <|> (expStmtP considerKeys Consider <?> "consideration") 
    <|> (expStmtP assertKeys Assert <?> "assertion")
    <|> includeP

introP :: Parse [Stmt]
introP =
  do{ src <- getSrc
    ; p0 <- getPos
    ; keysP introKeys
    ; words <- many wordP
    ; p1 <- getPos
    ; xs <- mathdelims $ sepBy1 nameP commaSep
    ; p2 <- getPos
    ; periodManyP
    ; p3 <- getPos
    ; PS txt b ops flags <- getState
    ; setState $ PS txt b (addOps (map fst xs) ops (introTyp words)) flags
    ; return $ [Text (srcTxt src p0 p1), 
                Intro (Src (srcTxt src p1 p2)) (introTyp words) xs, 
                Text (srcTxt src p2 p3)]
    }
  <?> "variable or operator introduction"

expStmtP ks stmt =
  do{ src <- getSrc
    ; p1 <- getPos
    ; keysP ks
    ; _ <- many uuidP
    ; (e,s,(p2,p3)) <- phraseP
    ; periodManyP
    ; p4 <- getPos
    ; return $ [Text$ srcTxt src p1 p2, 
                ExpStmt stmt (e,s), 
                Text$ srcTxt src p3 p4]
    }

includeP :: Parse [Stmt]
includeP =
  do{ reserved "\\vdepend"
    ; ws <- many1 wordP
    ; reserved "\\vdependbeg"
    ; n <- return $ foldr (\s1-> \s2-> s1++" "++s2) (last ws) (init ws)
    ; ss <- ((try $ many stmtP) <?> "ERROR IN INCLUSION [["++n++"]]")
    ; reserved "\\vdependend"
    ; return $ [Include n (concat ss)]
    }
  <?> "inclusion block"

----------------------------------------------------------------
-- | Arithmetic expressions.

expP :: Parse Exp
expP =
  (listSepApp commaSep mkTup)
  $ expNoCommaP

expNoCommaP :: Parse Exp
expNoCommaP =
  (opsP opsLogic).
  (opsRelP)
  $ expNoRelP

expNoRelP :: Parse Exp
expNoRelP =
  do{ PS _ _ (_:opsSet:opsArith:_, _) _ <- getState
    ; e <- (opsP opsSet).
           (listSepApp (reservedOp "\\times") mkProd).
           (opsP opsArith)
           $ expAppP
    ; return e
    } 

expAppP :: Parse Exp
expAppP =
  do { es <- many1 expNoAppP
     ; return $ foldl App (head es) (tail es)
     }
  <?> "expression with functional application"

expNoAppP :: Parse Exp
expNoAppP =
  opsP opsSubscript
   ( iterP
 <|> ifThenElseP
 <|> (rootP <?|> rootP')
 <|> expAtom
 <|> quantP "\\forall" (mkQ Forall Imp)
 <|> quantP "\\exists" (mkQ Exists And)
   )
   <?> "simple expression"

expAtom :: Parse Exp
expAtom =
     try (expVectorIterP ("+", Plus))
 <|> try (expVectorIterP ("*", Times))
 <|> try (expVectorIterP ("\\cdot", Times))
 <|> try (bracks "||" "||" VectorNorm expP)
 <|> try (bracks "|" "|" (Brack Bar Bar) expP)
 <|> expFracP
 <|> (try expProbP <|> expProbWithCondP)
 <|> expIntervalP
 <|> bracks "\\lceil" "\\rceil" Ceil expP
 <|> bracks "\\lfloor" "\\rfloor" Floor expP
 <|> angles "\\langle" "\\rangle" (Brack Round Round) expP
 <|> braces expP
 <|> parens expP
 <|> expNumP
 -- <|> (try $ phrasePred "\\p" NLPredC)
 -- <|> (try $ phrasePred "\\l" NLPredLC)
 <|> (try varOrConstP)
 <|> (try $ mathbraces setEnumP)
 <|> (try $ mathbraces setCompP)
 <|> (try $ mathbraces setP)
 <?> "atomic expression"

expIntervalP =
  do{ reserved "\\interval"
    ; e <- expAtom
    ; return $ mkInterval e
    }

expVectorIterP (opStr,con) =
  do{ e1 <- varP
    ; reservedOp "_"
    ; e1' <- expAtom
    ; reservedOp opStr
    ; reservedOp "\\ldots" <|> reservedOp "..."
    ; reservedOp opStr
    ; e2 <- varP
    ; reservedOp "_"
    ; e2' <- expAtom
    ; return $ App (C (IterVect con)) (T[e1,e1',e2,e2'])
    }

quantP :: String -> ([(Name, Maybe Exp)] -> Exp -> Exp) -> Parse Exp
quantP str cnstrct =
  do{ reserved str
    ; qvs <- quantVarsList
    ; symb "."
    ; e <- expP
    ; return $ cnstrct (addLimits qvs) e
    }
    <?> "quantifier: "++str

-- If no domain is provided for a variable, look further 
-- down the list and try to find one.
addLimits [] = []
addLimits ((i, Just e):vts) = (i, Just e):(addLimits vts)
addLimits ((i, Nothing):vts) = (i, nxt vts):(addLimits vts)
  where nxt = \qvs->listToMaybe $ catMaybes (map snd qvs)

quantVarsList = sepBy1 (quantVarWithIn <?|> quantVarNoIn) commaSep
      <?> "quantifier variable"

quantVarNoIn = do{x <- nameP; return (x, Nothing)}
quantVarWithIn =
  do{ x <- nameP
    ; reservedOp "\\in"
    ; e <- expNoCommaP
    ; return (x, Just e)
    }

iterP :: Parse Exp
iterP = iter1P <?|> iter2P <?|> iter0P

iter0P :: Parse Exp
iter0P =
  do{ op <- iterOps
    ; e2 <- expNoRelP <|> expAtom
    ; return $ App (C $ Aggregate op) e2
    }
    <?> "iterated operator application"

iter1P :: Parse Exp
iter1P =
  do{ op <- iterOps
    ; reservedOp "_"
    ; reservedOp "{"
    ; x <- nameP
    ; reservedOp "\\in"
    ; e1 <- expP
    ; reservedOp "}"
    ; e2 <- expNoRelP <|> expAtom
    ; return $ Bind op [x] $ T[bOp In (Var x) e1,e2]
    }
    <?> "iterated operator application"

iter2P :: Parse Exp
iter2P =
  do{ op <- iterOps
    ; reservedOp "_"; reservedOp "{"
    ; x <- nameP
    ; reservedOp "="
    ; e1 <- expP
    ; reservedOp "}"
    ; reservedOp "^"; reservedOp "{"
    ; e1' <- expP
    ; reservedOp "}"
    ; e2 <- expNoRelP <|> expAtom
    ; return $ Bind op [x] $ T[bOp In (Var x) (bOp SetEnum e1 e1'),e2]
    }
    <?> "iterated operator application"

iterOps :: Parse Const
iterOps = (foldr (<|>) (last l) (init l))<?>"iterated operator"
  where l = map (\((o,s),_)->do{reserved s; return o}) opsIter

setEnumP :: Parse Exp
setEnumP =
  do{ e1 <- expNoCommaP
    ; commaSep
    ; reservedOp "\\ldots" <|> reservedOp "..."
    ; commaSep
    ; e2 <- expNoCommaP
    ; return $ bOp SetEnum e1 e2
    }
    <?> "set (enumeration)"

expProbWithCondP :: Parse Exp
expProbWithCondP =
  do{ reserved "\\Pr"
    ; (reservedOp "(" <|> reservedOp "[")
    ; e1 <- expP
    ; reservedOp "|"
    ; e2 <- expP
    ; (reservedOp ")" <|> reservedOp "]")
    ; return $ App (C Probability) (T [e1,e2])
    }
    <?> "probability expression (with conditions)"

expProbP :: Parse Exp
expProbP =
  do{ reserved "\\Pr"
    ; (reservedOp "(" <|> reservedOp "[")
    ; e <- expP
    ; (reservedOp ")" <|> reservedOp "]")
    ; return $ App (C Probability) e
    }
    <?> "probability expression (without conditions)"

setCompP :: Parse Exp
setCompP =
  do{ e1 <- expP
    ; reservedOp "|"
    ; e2 <- listSepApp commaSep listAnd expNoCommaP
    ; return $ mkSetComp e1 e2
    }
    <?> "set (comprehension)"

setP :: Parse Exp
setP = listSepApp commaSep ((App (C SetExplicit)).(T).sort) expNoCommaP
    <?> "set (explicit)"

ifThenElseP :: Parse Exp
ifThenElseP =
  do{ reserved "\\if"   ; e1 <- expP
    ; reserved "\\then" ; e2 <- expP
    ; reserved "\\else" ; e3 <- expP
    ; return $ App (C IfThenElse) (T[e1,e2,e3])
    }

expFracP :: Parse Exp
expFracP =
  do{ reserved "\\frac"
    ; e1 <- between (symb "{") (symb "}") expP
    ; e2 <- between (symb "{") (symb "}") expP
    ; return $ App (C Div) (T[e1,e2])
    }

rootP :: Parse Exp
rootP =
  do{ reserved "\\sqrt"
    ; e1 <- between (symb "[") (symb "]") expP
    ; e2 <- between (symb "{") (symb "}") expP
    ; return $ mkRoot e1 e2
    }
    
rootP' :: Parse Exp
rootP' =
  do{ reserved "\\sqrt"
    ; e2 <- between (symb "{") (symb "}") expP
    ; return $ mkRoot (C (N 2)) e2
    }

opsRelP :: Parse Exp -> Parse Exp
opsRelP p =
  do{ e <- p
    ; PS _ _ (opsRel:_, _)_ <- getState
    ; opLL' <- return $ opLL opsRel
    ; rest <- many$do{ o<-foldr (<|>) (last opLL') (init opLL'); e<-p; return (o,e)}
    ; return $ if rest==[] then e else listAnd $ mkRelExp e rest
    }
  where
    mkRelExp e [(o,e')] = [bOp o e e']
    mkRelExp e ((o,e'):oes) = (bOp o e e'):mkRelExp e' oes
    opLL opsRel = map (\((o,s),_) -> do{reservedOp s; return o}) (head opsRel)

opsP :: OpTable -> Parse Exp -> Parse Exp
opsP t = buildExpressionParser $ map (map o) t
 where
  o ((op, s), Pre) = prefix s $ App (C op)
  o ((op, s), None) = prefix s $ App (C op)
  o ((op, s), a) = binary s (bOp op) (assoc a)
  assoc InL = AssocLeft
  assoc InR = AssocRight

expNumP :: Parse Exp
expNumP =
  do{ n <- naturalOrFloat
    ; return $ case n of
        Left  n -> C$N$ toRational n
        Right d -> C$N$ toRational d
    }
    <?> "numeric literal"

constP ((op,str),_) = do{reserved str; return $ C op}<?>str
opP ((op,str),_) = do{reserved "\\nofix"; braces (reservedOp str); return $ C op}
varOrConstP = 
  do{ PS _ _ (_,[uCs]) _ <- getState
    ; foldr (<?|>) varP (map opP opsAll ++ map constP (constAll++uCs))
    } <?> "constant or variable"

varP =
  do{ x <- nameP;
    ; PS _ _ ops _ <- getState
    ; if (fst x) `elem` (opsStrTbl ops) then pzero else return $ Var x
    } <?> "variable"

----------------------------------------------------------------
-- | English logical expression phrases.

forallKeys = ["for all", "for any" ]
existsKeys = ["there exists", "there exist"]
iffKeys = ["iff", "if and only if"]
impliesKeys = ["implies", "implies that", "if", "then"]
suchThatKeys = ["such that", "s.t."]

phraseOp f txt (e,s,(p1,p2)) (e',s',(p1',p2')) = 
  (f e e', SrcL ["", srcTxt txt p2 p1'] [s,s'], (p1,p2'))

phraseOps s =
  [ [ binary "or" (phraseOp (bOp Or) s) AssocLeft ]
  , [ binary "iff" (phraseOp (bOp Iff) s) AssocLeft
    , binary "if and only if" (phraseOp (bOp Iff) s) AssocLeft
    , binary "implies that" (phraseOp (bOp Imp) s) AssocLeft
    , binary "implies" (phraseOp (bOp Imp) s) AssocLeft
    ]
  ]

phraseP :: Parse (Exp, Src, (SourcePos, SourcePos))
phraseP =
  do{ PS txt _ _ _ <- getState
    ; buildExpressionParser (phraseOps txt) phraseAndP
    }
  <?> "logical expression (English)" 

phraseAndP :: Parse (Exp, Src, (SourcePos, SourcePos))
phraseAndP =
  do{ src <- getSrc
    ; es <- sepBy1 phraseNoAndP ((try $ do{reserved ","; reserved "and"}) <|> reserved "," <|> reserved "and")
    ; return $ foldr (phraseOp (bOp And) src) (last es) (init es)  
    }

phraseNoAndP :: Parse (Exp, Src, (SourcePos, SourcePos))
phraseNoAndP =
     phraseForall
 <|> phraseExists
 <|> phraseConsidering
 <|> phraseInContextForall
 <|> phraseIfThen
 <|> phraseNot
 <|> phraseContradiction
 <|> bracksIgnP "{" "}" (phraseP)  --(phraseIsP <?|> phraseP)
 <|> bracksIgnP "(" ")" (phraseP)  -- (wStr $ parens phraseP)
 <|> phrasePreds
 <|> (try phrasePredBare')
 <|> phraseMathP
 <|> phraseMakeReport

phrasePreds = 
     phrasePred "\\p" NLPredC
 <|> phrasePred "\\l" NLPredLC
 <|> phrasePredBrack NLPredLC

phraseForall = phraseQ (keysP forallKeys) (do{commaP;return ""}) Forall Imp
  <?> "universal quantification (English)"

phraseExists = phraseQ (keysP existsKeys) (keysP suchThatKeys) Exists And
  <?> "existential quantification (English)"

withPos p = do{ p1<-getPos; p; p2<-getPos; return (p,(p1,p2)) }

phraseQ qP sepP q o =
  do{ s <- getSrc
    ; p1 <- getPos
    ; qP
    ; p2 <- getPos
    ; vs <- mathdelims quantVarsList
    ; p3 <- getPos
    ; sepP
    ; (e,src,(p4,p5)) <- phraseP
    ; return $ ((mkQ q o) (addLimits vs) e,
                SrcL [srcTxt s p1 p2, srcTxt s p3 p4] [Src (srcTxt s p2 p3), src], 
                (p1,p5))
    } <?> "quantified formula (English)"

phraseConsidering =
  do{ s <- getSrc
    ; p1 <- getPos
    ; keysP ["considering"]
    ; (e1,src1,(p2,p3)) <- phraseMathP <|> (braces phraseP)
    ; commaP
    ; (e2,src2,(p4,p5)) <- phraseP
    ; return $ (Bind Considering (fv [] e1) (T[e1,e2]), 
                SrcL [srcTxt s p1 p2,srcTxt s p3 p4] [src1, src2], 
                (p1,p5))
    } <?> "\'considering\' phrase (English)"

phraseInContextForall =
  do{ s <- getSrc
    ; p1 <- getPos
    ; keysP ["in context for all"]
    ; commaP
    ; (e,src,(p2,p3)) <- phraseP
    ; return $ (Bind InContextForall (fv [] e) e, 
                SrcL [srcTxt s p1 p2] [src], 
                (p1,p3))
    } <?> "\'in context for all\' phrase (English)"

phraseIfThen =
  do{ s <- getSrc
    ; p1 <- getPos
    ; keysP ["if"]
    ; (e1,s1,(p2,p3)) <- phraseP
    ; keysP ["then"]
    ; (e2,s2,(p4,p5)) <- phraseP
    ; return (bOp Imp e1 e2, SrcL [srcTxt s p1 p2, srcTxt s p3 p4] [s1,s2],(p1,p5))
    }
    <?> "\"if ... then ... \" clause (English)"

phraseNot =
  do{ s <- getSrc
    ; p1 <- getPos
    ; keysP ["it is not the case that", "not"]
    ; (e,src,(p2,p3)) <- phraseP
    ; return (App (C Not) e, SrcL [srcTxt s p1 p2] [src], (p1,p3))
    }
    <?> "logical negation (English)"

phraseContradiction =
  do{ s <- getSrc
    ; p1 <- getPos
    ; keysP ["contradiction"]
    ; p2 <- getPos
    ; return $ (C Contradiction, Src $ srcTxt s p1 p2, (p1,p2))
    } <?> "contradiction"

phraseMathP :: Parse (Exp, Src, (SourcePos, SourcePos))
phraseMathP =
  do{ s <- getSrc
    ; pos1 <- getPos
    ; e <- mathdelims expP <|> mathbrackets expP
    ; pos2 <- getPos  
    ; return $ (e, Src $ srcTxt s pos1 pos2, (pos1,pos2))
    }

phrasePred flagStr con =
  do{ s <- getSrc
    ; p1 <- getPos
    ; reserved flagStr
    ; ews <- braces (many1 (phrasePredSubExp <|> phrasePredWord'' <|> phrasePredWordIs <|> phrasePredSubPred))
    ; p2 <- getPos
    ; return $ (mkNLPred con ews, Src $ srcTxt s p1 p2, (p1,p2))
    }
    <?> "predicate expression (English)"

phrasePredBrack con =
  do{ s <- getSrc
    ; p1 <- getPos
    ; ews <- brackets (many1 (phrasePredSubExp <|> phrasePredWord'' <|> phrasePredWordIs <|> phrasePredSubPred))
    ; p2 <- getPos
    ; return $ (mkNLPred con ews, Src $ srcTxt s p1 p2, (p1,p2))
    }
    <?> "predicate expression (English)"

phrasePredSubExp = do{(e,_,_) <- phraseMathP; return $ Left e}
phrasePredWord'' = do{w <- wordP''; return $ Right w} where
  wordP'' = reservedAsWordP "and" <|> wordP
  reservedAsWordP r = do{_ <- reserved r; return r}
phrasePredWordIs = do{ reserved "is"; return $ Right "is"}

phrasePredSubPred = do{ (e,_,_) <- phrasePreds; return $ Left e}

phrasePredBare' =
  do{ s <- getSrc
    ; p1 <- getPos
    ; e <- phrasePredBare
    ; p2 <- getPos
    ; return $ (e, Src $ srcTxt s p1 p2, (p1,p2))
    }
    <?> "non-delimited predicate expression (English)"

phrasePredBare = phrasePredBare2 <|> phrasePredBare1
phrasePredBare1 =
  do{ --ews <- many1 (phrasePredSubExp <|> phrasePredWord <|> phrasePredWordIs)
      e1 <- (phrasePredSubExp <|> phrasePredWord <|> phrasePredWordIs)
    ; ews <- many1 (phrasePredWordIs <|> phrasePredWord)
    ; if hasRight (e1:ews) then return $ mkNLPred NLPredLC (e1:ews) else pzero
    }
    <?> "predicate expression (English)"

phrasePredBare2 =
  do{ ews <- many1 (phrasePredWordIs <|> phrasePredWord)
    ; if hasRight ews then return $ mkNLPred NLPredLC ews else pzero
    }
    <?> "predicate expression (English)"

phraseMakeReport =
  do{ s <- getSrc
    ; pos1 <- getPos
    ; symb "?"
    ; es <- sepBy expNoCommaP commaSep
    ; symb "?"
    ; pos2 <- getPos
    ; many1 anyChar
    ; return $ (App (C MakeReport) (T es), Src $ srcTxt s pos1 pos2, (pos1,pos2))
    }

hasRight (Right x:xs) = True
hasRight (_:xs) = hasRight xs
hasRight [] = False

-- NOTE: Reserved words must be allowed to occur here.
phrasePredWord = do{w <- wordP; return $ Right w} 

----------------------------------------------------------------
-- | Punctuation

punctAny = symb "," <|> symb "." <|> symb ";" <|> symb ":"
punctP = many punctAny <?> "punctuation mark(s): .,:;"
periodP = symb "." <?> "punctuation mark: \".\""
periodManyP = (many $ symb ".") <?> "punctuation mark: \".\""
commaP = many (symb ",") <?> "comma"
commaSep = do {skipMany1 $ space <|> char ','; return ()}
doubleSlashSep = skipMany1 (reserved " " <|> reserved "\\\\")

----------------------------------------------------------------
-- | Brackets.

bracksIgnP lstr rstr p =
  do{ s <- getSrc
    ; p1 <- getPos
    ; symb lstr
    ; (e,src,(p2,p3)) <- p
    ; symb rstr
    ; p4 <- getPos
    ; return (e, SrcIg [Src (srcTxt s p1 p2), src, Src (srcTxt s p3 p4)], (p1,p4))
    }

parens :: Parse Exp -> Parse Exp
parens p =
  do{ b1 <- (brackP "(" Round <|> brackP "[" Square )
    ; e <- p
    ; b2 <- (brackP ")" Round <|> brackP "]" Square )
    ; return $ mkBrack b1 b2 e
    }
    <?> "bracketed/parenthesized expression"

angles :: String -> String -> Const -> Parse Exp -> Parse Exp
angles l r c p =
  do{ reservedOp l
    ; e <- p
    ; reservedOp r
    ; return $ mkVect e
    } <?> "bracketed expression: "++l++"..."++r

bracks :: String -> String -> Const -> Parse Exp -> Parse Exp
bracks l r c p =
  do{ reservedOp l
    ; e <- p
    ; reservedOp r
    ; return $ App (C c) e
    } <?> "bracketed expression: "++l++"..."++r

brackP str ret = do{symb str; return ret}<?> "bracket"
braces p       = between (symb "{") (symb "}") p
brackets p       = between (symb "[") (symb "]") p
parens0 p      = between (symb "(") (symb ")") p
dollarsigns p  = between (symb "$") (symb "$") p
mathpounds p  = between (symb "#") (symb "#") p
mathdelims p = dollarsigns p <|> mathpounds p
mathbrackets p = between (reservedOp "\\[") (reservedOp "\\]") p
mathbraces p   = between (reservedOp "\\{") (reservedOp "\\}") p

----------------------------------------------------------------
-- | Other basic parsers.

nameP :: Parse Name
nameP = do{i <- idP; if i == "\\" then pzero else return (i,-1)}

keyP :: String -> Parse String
keyP s = do{reserved s; return s;}

keysP :: [String] -> Parse String
keysP l = foldl (<|>) (head l') (tail l') where l' = map keyP l

wordP = do{w <- symb "-"; return "-"} <|> wordP'
wordP' :: Parse String
wordP' = do{w <- idP; if w!!0 == '\\' then pzero else return w}

uuidP :: Parse String
uuidP = do{symb "~"; uuid <- many1 (alphaNum <|> (char '-')); symb "~"; return uuid}

{- wordP'' = 
  do{ c0 <- letter <|> oneOf "\\"
    ; cs <- many (alphaNum <|> oneOf "'")
    ; return $ c0:cs
    } -}

listSepApp :: Parse b -> ([a] -> a) -> Parse a -> Parse a
listSepApp sepP f p = do{es <- sepBy1 p sepP; return $ f es}

----------------------------------------------------------------
-- | Parsec definitions.

lang = P.makeTokenParser langDef
langDef
  = emptyDef
  { commentStart    = "\\vend"
  , commentEnd      = "\\vbeg"
  , commentLine     = "%--"
  , nestedComments  = True
  , identStart      = letter <|> oneOf "\\"
  , identLetter     = alphaNum <|> oneOf "'"
  , opStart         = opLetter langDef
  , opLetter        = oneOf ""
  , reservedOpNames = constStr
  , reservedNames   =
      constStr ++ opsStr ++
      introKeys ++ assumpKeys ++ considerKeys ++ assertKeys ++
      forallKeys ++ existsKeys ++
      iffKeys ++ impliesKeys ++ suchThatKeys ++
      ["and", ", and", "or"] ++
      ["\\not"]++
      ["\\interval"]++
      ["\\forall", "\\exists", "\\if", "\\then", "\\else", "\\sqrt",
       "\\frac",
       "\\Pr",
       "\\nofix", "\\p", "\\l", "\\q",
       ".", "\\\\", "|", "\\[", "\\]", 
       "\\{", "\\}", "\\langle", "\\rangle",
       "\\lfloor", "\\rfloor", "\\lceil", "\\rceil",
       "\\vdepend", "\\vdependbeg", "\\vdependend"]

    , caseSensitive = True
    }

whiteSpace      = P.whiteSpace lang
reserved        = P.reserved lang
reservedOp      = P.reservedOp lang
symb            = P.symbol lang
idP             = P.identifier lang
natural         = P.natural lang
naturalOrFloat  = P.naturalOrFloat lang

binary  str f assoc = Infix (do{ reservedOp str; return f }) assoc
prefix  str f = Prefix (do{ reservedOp str; return f })
postfix str f = Postfix (do{ reservedOp str; return f })

(<?|>) :: Parse a -> Parse a -> Parse a
(<?|>) p q = (try p) <|> q

--eof