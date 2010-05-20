----------------------------------------------------------------
--
-- aartifact
-- http://www.aartifact.org/src/
-- Copyright (C) 2008-2010
-- A. Lapets
--
-- This software is made available under the GNU GPLv3.
--
-- ExpPrint.hs
--   Legible string output of expressions.

----------------------------------------------------------------
-- 

module ExpPrint where

import Data.Maybe (catMaybes)
import Data.List (partition, sort, sortBy)
import Ratio

import Set
import ExpConst
import Exp

----------------------------------------------------------------
-- 

expPrintT es = concatDelim ", " $ map expPrint es

expPrint e = let p = expPrint in case e of
  Var (n,_) -> n
  C SetN -> "\\N"
  C SetZ -> "\\Z"
  C SetQ -> "\\Q"
  C SetR -> "\\R"
  C Ast -> "\\ast"
  C EulerE -> "\\eulere"
  C (Set []) -> "\\emptyset"
  C Infinity -> "\\infty"
  C (N r) -> if denominator r == 1 then show (numerator r) else "{"++(show $ numerator r)++"/"++(show $ denominator r)++"}"
  App (C Plus) (T [e1,e2]) -> p e1 ++ " + " ++ p e2
  App (C Minus) (T [e1,e2]) -> p e1 ++ " - " ++ p e2
  App (C Times) (T [e1,e2]) -> p e1 ++ " * " ++ p e2
  App (C Pow) (T [e1,e2]) -> p e1 ++ "^" ++ p e2
  App (C Div) (T [e1,e2]) -> p e1 ++ " / " ++ p e2
  App (C Min) e -> "\\min " ++ p e
  App (C Max) e -> "\\max " ++ p e
  App (C LCM) e -> "\\lcm " ++ p e
  App (C GCF) e -> "\\gcf " ++ p e
  App (C PowerSet) e -> "\\powerset " ++ p e
  App (C SetExplicit) (T es) -> "\\{" ++ expPrintT es ++ "\\}"
  App (C Neg) e -> "-" ++ p e
  App (C Circ) (T [e1,e2]) -> p e1 ++ " \\circ " ++ p e2
  App (C Union) (T [e1,e2]) -> p e1 ++ " \\cup " ++ p e2
  App (C Isect) (T [e1,e2]) -> p e1 ++ " \\cap " ++ p e2
  App (C Cart) (T [e1,e2]) -> p e1 ++ " \\times " ++ p e2
  App (C Arrow) (T [e1,e2]) -> p e1 ++ " \\rightarrow " ++ p e2
  App (C Lt) (T [e1,e2]) -> p e1 ++ " < " ++ p e2
  App (C Lte) (T [e1,e2]) -> p e1 ++ " \\leq " ++ p e2
  App (C Gt) (T [e1,e2]) -> p e1 ++ " > " ++ p e2
  App (C Gte) (T [e1,e2]) -> p e1 ++ " \\geq " ++ p e2
  App (C Neq) (T [e1,e2]) -> p e1 ++ " \\neq " ++ p e2
  App (C Eql) (T [e1,e2]) -> p e1 ++ " = " ++ p e2
  App (C In) (T [e1,e2]) -> p e1 ++ " \\in " ++ p e2
  App (C Subset) (T [e1,e2]) -> p e1 ++ " \\subset " ++ p e2
  App (C Subseteq) (T [e1,e2]) -> p e1 ++ " \\subseteq " ++ p e2
  App (C (NotC Lt)) (T [e1,e2]) -> p e1 ++ " \\not< " ++ p e2
  App (C (NotC Lte)) (T [e1,e2]) -> p e1 ++ " \\not\\leq " ++ p e2
  App (C (NotC Gt)) (T [e1,e2]) -> p e1 ++ " \\not> " ++ p e2
  App (C (NotC Gte)) (T [e1,e2]) -> p e1 ++ " \\not\\geq " ++ p e2
  App (C (NotC Neq)) (T [e1,e2]) -> p e1 ++ " \\not\\neq " ++ p e2
  App (C (NotC Eql)) (T [e1,e2]) -> p e1 ++ " \\not= " ++ p e2
  App (C (NotC In)) (T [e1,e2]) -> p e1 ++ " \\not\\in " ++ p e2
  App (C (NotC Subset)) (T [e1,e2]) -> p e1 ++ " \\not\\subset " ++ p e2
  App (C (NotC Subseteq)) (T [e1,e2]) -> p e1 ++ " \\not\\subseteq " ++ p e2
  App (C Subscript) (T [e1,e2]) -> p e1 ++ "_" ++ p e2
  App (C Log) e -> "\\log(" ++ p e ++ ")"
  App (C Ln) e -> "\\ln(" ++ p e ++ ")"
  App (C Dom) e -> "\\dom(" ++ p e ++ ")"
  App (C Ran) e -> "\\ran(" ++ p e ++ ")"
  App (C (NLPredLC ws)) (T es) -> concatDelim " " $ map prNLPredLCW (pairUp ws es)
  T es -> "(" ++ expPrintT es ++ ")"
  _ -> show e

concatDelim delim l = foldr (\x y -> x ++ delim ++ y) (last l) (init l)

prNLPredLCW :: Either String Exp -> String
prNLPredLCW (Left w) = w
prNLPredLCW (Right e) = "$" ++ expPrint e ++ "$"

pairUp :: [Maybe String] -> [Exp] -> [Either String Exp]
pairUp (Nothing:ws) (e:es) = Right e:pairUp ws es
pairUp (Just w:ws) es = Left w:pairUp ws es
pairUp [] [] = [] 

--eof
