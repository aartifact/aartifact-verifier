----------------------------------------------------------------
--
-- aartifact
-- http://www.aartifact.org/src/
-- Copyright (C) 2008-2010
-- A. Lapets
--
-- This software is made available under the GNU GPLv3.

-- ExpSQL.hs
--   Routines for generating SQL versions of expression
--   instances.

----------------------------------------------------------------
-- 

module ExpSQL (expSql)
  where

import Data.List (sortBy)
import Ratio (numerator, denominator)

import Set
import ExpConst
import Exp

----------------------------------------------------------------
-- 

type Ix = Integer
data Node = Syn String | SynData String String | Exp Exp | ExpMath Exp

expSql e = showSep "\n" $ ((\(x,y,z) -> x) $ cnvAll 0 (-1) 0 0 [] es)
  where es = if isLogical e then [Exp e] else [Syn "$", Exp e, Syn "$"]

commaSepNode [e] = [e]
commaSepNode (e:es) = e:(Syn ","):(commaSepNode es)

dof e p o l r s d t vs = 
  (vs++["(" ++ (showSep "," [
    "'$entid'",
    show e, if p == -1 then "null" else show p,
    show o, show l, show r,
    "'"++s++"'", "'"++d++"'", t
  ]) ++ ")"], e+1, r+1)

cnvAll :: Ix -> Ix -> Ix -> Ix -> [String] -> [Node]  -> ([String], Ix, Ix)
cnvAll e p o l vs [] = (vs, e, l)
cnvAll e p o l vs (n:ns) = cnvAll e' p (o+1) min1 vs1 ns
  where (vs1, e',  min1) = cnv (e+1) p o (l+1) vs n

cnv :: Ix -> Ix -> Ix -> Ix -> [String] -> Node -> ([String], Ix, Ix)
cnv e p o l vs (Syn s)           = dof e p o l l s     "null" "true"  vs
cnv e p o l vs (SynData s dat)   = dof e p o l l s     dat   "true"  vs
cnv e p o l vs (ExpMath exp)     = cnvAll e p o l vs $ if isLogical exp then [Exp exp] else [Syn "$", Exp exp, Syn "$"]
cnv e p o l vs (Exp (Var (x,_))) = dof e p o l l "Var" x      "false" vs
cnv e p o l vs (Exp (C (N r))) = dof e p o l l "N" ((show $ numerator r)++"/"++(show $ denominator r)) "false" vs

cnv eix pix oix min0 vs (Exp (Bind Considering _ (T[e1,e2]))) =
  let l = [ExpMath e1, Syn ", ", ExpMath e2]
      (vs3, eix3, min3) = cnvAll (eix+1) eix 0 (min0+1) vs l
      (vs'', _, min3') = dof eix pix oix min0 min3 "Considering" "null" "false" vs3
  in (vs'', eix3+1, min3')

cnv eix pix oix min0 vs (Exp (Bind InContextForall _ e)) =
  let l = [ExpMath e]
      (vs3, eix3, min3) = cnvAll (eix+1) eix 0 (min0+1) vs l
      (vs'', _, min3') = dof eix pix oix min0 min3 "InContextForall" "null" "false" vs3
  in (vs'', eix3+1, min3')

cnv eix pix oix min0 vs (Exp (Bind Plus _ (T[e1,e2]))) =
  let l = [Syn "{", Syn "\\sum_{", Exp e1, Syn "\\rbrace", Syn "{", Exp e2, Syn "}", Syn "}"]
      (vs3, eix3, min3) = cnvAll (eix+1) eix 0 (min0+1) vs l
      (vs'', _, min3') = dof eix pix oix min0 min3 "Summation" "null" "false" vs3
  in (vs'', eix3+1, min3')

cnv eix pix oix min0 vs (Exp (Bind Times _ (T[e1,e2]))) =
  let l = [Syn "{", Syn "\\prod_{", Exp e1, Syn "\\rbrace", Syn "{", Exp e2, Syn "}", Syn "}"]
      (vs3, eix3, min3) = cnvAll (eix+1) eix 0 (min0+1) vs l
      (vs'', _, min3') = dof eix pix oix min0 min3 "Product" "null" "false" vs3
  in (vs'', eix3+1, min3')

cnv eix pix oix min0 vs (Exp (Bind SetComp _ (T [e1,e2]))) =
  let q [] = []
      q [e] = [Exp e]
      q (e:es) = [Exp e, Syn ","] ++ q es
      l = [Syn "\\{", Exp e1, Syn "|", Exp e2, Syn "\\}"]
      (vs3, eix3, min3) = cnvAll (eix+1) eix 0 (min0+1) vs l
      (vs'', _, min3') = dof eix pix oix min0 min3 "SetComp" "null" "false" vs3
  in (vs'', eix3+1, min3')

cnv eix pix oix min0 vs (Exp (App (C SetEnum) (T[e1,e2]))) =
  let l = [Syn "\\{", Exp e1, Syn ", ", Syn "...", Syn ", ", Exp e2, Syn "\\}"]
      (vs3, eix3, min3) = cnvAll (eix+1) eix 0 (min0+1) vs l
      (vs'', _, min3') = dof eix pix oix min0 min3 "SetEnum" "null" "false" vs3
  in (vs'', eix3+1, min3')

cnv eix pix oix min0 vs (Exp (C (NLPredLC ws))) = cnv eix pix oix min0 vs (Exp (App (C (NLPredLC ws)) (T [])))

cnv eix pix oix min0 vs (Exp (T es)) =
  let q [] = []
      q [e] = [Exp e]
      q (e:es) = [Exp e, Syn ","] ++ q es
      l = [Syn "("] ++ q es ++ [Syn ")"]
      (vs3, eix3, min3) = cnvAll (eix+1) eix 0 (min0+1) vs l
      (vs'', _, min3') = dof eix pix oix min0 min3 "Tuple" "" "false" vs3
  in (vs'', eix3+1, min3')

cnv eix pix oix min0 vs (Exp (App (C SetExplicit) (T es))) =
  let q [] = []
      q [e] = [Exp e]
      q (e:es) = [Exp e, Syn ","] ++ q es
      l = [Syn "\\{"] ++ q es ++ [Syn "\\}"]
      (vs3, eix3, min3) = cnvAll (eix+1) eix 0 (min0+1) vs l
      (vs'', _, min3') = dof eix pix oix min0 min3 "SetExplicit" "" "false" vs3
  in (vs'', eix3+1, min3')

cnv eix pix oix min0 vs (Exp (App (C (NLPredLC ws)) (T es))) =
  let q ((Just w):ws) es = [SynData "NLPredLCWord" w] ++ q ws es
      q (Nothing:ws)  (e:es) = [Syn " $", Exp e, Syn "$"] ++ q ws es
      q [] _ = []
      
      dt (Just w) = w
      dt (Nothing) = "."

      dat [] = ""
      dat [w] = dt w
      dat (w:ws) = dt w ++ "_" ++ dat ws

      l = [Syn "\\l{"] ++ q ws es ++ [Syn " }"]
      (vs3, eix3, min3) = cnvAll (eix+1) eix 0 (min0+1) vs l
      (vs'', _, min3') = dof eix pix oix min0 min3 "NLPredLC" (dat ws) "false" vs3
  in (vs'', eix3+1, min3')


cnv eix pix oix min0 vs (Exp (App (C Subscript) (T [e1,e2]))) =
  let (vs3, eix3, min3) = cnvAll (eix+1) eix 0 (min0+1) vs [Syn "{", Syn "{", Exp e1, Syn "}", Syn "_", Syn "{", Exp e2, Syn "}", Syn "}"]
      (vs'', _, min3') = dof eix pix oix min0 min3 "Subscript" "null" "false" vs3
  in (vs'', eix3+1, min3')

cnv eix pix oix min0 vs (Exp (App (C (Brack Bar Bar)) e)) =
  let (vs3, eix3, min3) = cnvAll (eix+1) eix 0 (min0+1) vs [Syn "|", Exp e, Syn "|"]
      (vs'', _, min3') = dof eix pix oix min0 min3 "Brack Bar Bar" "null" "false" vs3
  in (vs'', eix3+1, min3')

------
{- cnv eix pix oix min0 vs (Exp (App (C (Brack b1 b2)) e)) =
  let (vs3, eix3, min3) = cnvAll (eix+1) eix 0 (min0+1) vs [Syn (fst $ showBr b1), Exp e, Syn (snd $ showBr b2)]
      (vs'', _, min3') = dof eix pix oix min0 min3 ("Brack"++" "++showBr b1++" "++show b2) "null" "false" vs3
  in (vs'', eix3+1, min3') -}
------

cnv eix pix oix min0 vs (Exp (App (C IntervalOO) (T[e1,e2]))) =
  let (vs3, eix3, min3) = cnvAll (eix+1) eix 0 (min0+1) vs [Syn "(", Exp e1, Syn ", ", Exp e2, Syn ")"]
      (vs'', _, min3') = dof eix pix oix min0 min3 "IntervalOO" "\\interval" "false" vs3
  in (vs'', eix3+1, min3')

cnv eix pix oix min0 vs (Exp (App (C IntervalOC) (T[e1,e2]))) =
  let (vs3, eix3, min3) = cnvAll (eix+1) eix 0 (min0+1) vs [Syn "(", Exp e1, Syn ", ", Exp e2, Syn "]"]
      (vs'', _, min3') = dof eix pix oix min0 min3 "IntervalOC" "\\interval" "false" vs3
  in (vs'', eix3+1, min3')
  
cnv eix pix oix min0 vs (Exp (App (C IntervalCO) (T[e1,e2]))) =
  let (vs3, eix3, min3) = cnvAll (eix+1) eix 0 (min0+1) vs [Syn "[", Exp e1, Syn ", ", Exp e2, Syn ")"]
      (vs'', _, min3') = dof eix pix oix min0 min3 "IntervalCO" "\\interval" "false" vs3
  in (vs'', eix3+1, min3')
  
cnv eix pix oix min0 vs (Exp (App (C IntervalCC) (T[e1,e2]))) =
  let (vs3, eix3, min3) = cnvAll (eix+1) eix 0 (min0+1) vs [Syn "[", Exp e1, Syn ", ", Exp e2, Syn "]"]
      (vs'', _, min3') = dof eix pix oix min0 min3 "IntervalCC" "\\interval" "false" vs3
  in (vs'', eix3+1, min3')

cnv eix pix oix min0 vs (Exp (App (C Neg) e)) =
  let (vs3, eix3, min3) = cnvAll (eix+1) eix 0 (min0+1) vs [Syn "-", Exp e]
      (vs'', _, min3') = dof eix pix oix min0 min3 "Neg" "null" "false" vs3
  in (vs'', eix3+1, min3')

cnv eix pix oix min0 vs (Exp (App (C (IterVect op)) (T[e1,e1',e2,e2']))) =
  let (vs3, eix3, min3) = cnvAll (eix+1) eix 0 (min0+1) vs $ 
            [Exp e1, Syn "_", Exp e1', Syn (showC' op), Syn "...", Syn (showC' op), Exp e2, Syn "_", Exp e2']
      (vs'', _, min3') = dof eix pix oix min0 min3 ("IterVect"++show op) "null" "false" vs3
  in (vs'', eix3+1, min3')

cnv eix pix oix min0 vs (Exp (App (e1@(C (Aggregate _))) e2)) =
    let (vs3, eix3, min3) = cnvAll (eix+1) eix 0 (min0+1) vs [Syn "{", Exp e1, Exp e2, Syn "}"]
        (vs'', _, min3') = dof eix pix oix min0 min3 (show Apply) "null" "false" vs3
    in (vs'', eix3+1, min3')

cnv eix pix oix min0 vs (Exp (App (e1@(C PowerSet)) e2)) =
    let (vs3, eix3, min3) = cnvAll (eix+1) eix 0 (min0+1) vs [Syn "{", Exp e1, Syn "(", Exp e2, Syn ")", Syn "}"]
        (vs'', _, min3') = dof eix pix oix min0 min3 (show Apply) "null" "false" vs3
    in (vs'', eix3+1, min3')

cnv eix pix oix min0 vs (Exp (App (e1@(C GCF)) e2)) =
    let (vs3, eix3, min3) = cnvAll (eix+1) eix 0 (min0+1) vs [Syn "{", Exp e1, Exp e2, Syn "}"]
        (vs'', _, min3') = dof eix pix oix min0 min3 (show Apply) "null" "false" vs3
    in (vs'', eix3+1, min3')
  
cnv eix pix oix min0 vs (Exp (App (e1@(C LCM)) e2)) =
    let (vs3, eix3, min3) = cnvAll (eix+1) eix 0 (min0+1) vs [Syn "{", Exp e1, Exp e2, Syn "}"]
        (vs'', _, min3') = dof eix pix oix min0 min3 (show Apply) "null" "false" vs3
    in (vs'', eix3+1, min3')

cnv eix pix oix min0 vs (Exp (App (C Ceil) e)) =
  let (vs3, eix3, min3) = cnvAll (eix+1) eix 0 (min0+1) vs [Syn "\\lceil", Exp e, Syn "\\rceil"]
      (vs'', _, min3') = dof eix pix oix min0 min3 "Ceil" "null" "false" vs3
  in (vs'', eix3+1, min3')

cnv eix pix oix min0 vs (Exp (App (C Floor) e)) =
  let (vs3, eix3, min3) = cnvAll (eix+1) eix 0 (min0+1) vs [Syn "\\lfloor", Exp e, Syn "\\rfloor"]
      (vs'', _, min3') = dof eix pix oix min0 min3 "Floor" "null" "false" vs3
  in (vs'', eix3+1, min3')

cnv eix pix oix min0 vs (Exp (App (C c) (T es))) =
  case es of
    [e1,e2] ->
      if c `elem` [And, Or, Imp, Iff] then
        let e1l = if isLogical e1 then mkExpBraced e1 [Exp e1] else [Syn "$", Exp e1, Syn "$"]
            e2l = if isLogical e2 then mkExpBraced e2 [Exp e2] else [Syn "$", Exp e2, Syn "$"]
            (vs3, eix3, min3) = cnvAll (eix+1) eix 0 (min0+1) vs $ [Syn "{"]++e1l++[Syn $ showC' c]++e2l++[Syn "}"]
            (vs'', _, min3') = dof eix pix oix min0 min3 (show c) "null" "false" vs3
        in (vs'', eix3+1, min3')
      else if c `elem` bins then
        let (vs3, eix3, min3) = cnvAll (eix+1) eix 0 (min0+1) vs $
                      [Syn "{"] ++ mkBr c e1 [Exp e1] ++ [Syn $ (showC' c)]++ mkBr c e2 [Exp e2] ++ [Syn "}"]
            (vs'', _, min3') = dof eix pix oix min0 min3 (show c) "null" "false" vs3
        in (vs'', eix3+1, min3')
      else
       ([],-1,-1)
    es -> ([],-1,-1)

cnv eix pix oix min0 vs (Exp (App e1 e2)) =
    let (vs3, eix3, min3) = cnvAll (eix+1) eix 0 (min0+1) vs [Syn "{", Exp e1, Syn "(", Exp e2, Syn ")", Syn "}"]
        (vs'', _, min3') = dof eix pix oix min0 min3 (show Apply) "null" "false" vs3
    in (vs'', eix3+1, min3')

cnv eix pix oix min0 vs (Exp (Forall (v:vars) (App (C Imp) (T[_,e])))) =
  let q (v:vars) = [Syn ", ", Exp (Var v)] ++ q vars
      q [] = []
      l = [Syn "$", Exp (Var v)] ++ q vars ++ [Syn "$"] ++ [Syn ", "] ++ [ExpMath e]
      (vs3, eix3, min3) = cnvAll (eix+1) eix 0 (min0+1) vs l
      (vs'', _, min3') = dof eix pix oix min0 min3 "Forall" "null" "false" vs3
  in (vs'', eix3+1, min3')

cnv eix pix oix min0 vs (Exp (Exists (v:vars) (App (C And) (T[_,e])))) =
  let q (v:vars) = [Syn ", ", Exp (Var v)] ++ q vars
      q [] = []
      l = [Syn "$", Exp (Var v)] ++ q vars ++ [Syn "$"] ++ [Syn " s.t. "] ++ [ExpMath e]
      (vs3, eix3, min3) = cnvAll (eix+1) eix 0 (min0+1) vs l
      (vs'', _, min3') = dof eix pix oix min0 min3 "Exists" "null" "false" vs3
  in (vs'', eix3+1, min3')

cnv eix pix oix min0 vs (Exp (Exists (v:vars) e)) =
  let q (v:vars) = [Syn ", ", Exp (Var v)] ++ q vars
      q [] = []
      l = [Syn "$", Exp (Var v)] ++ q vars ++ [Syn "$"] ++ [Syn " s.t. "] ++ [ExpMath e]
      (vs3, eix3, min3) = cnvAll (eix+1) eix 0 (min0+1) vs l
      (vs'', _, min3') = dof eix pix oix min0 min3 "Exists" "null" "false" vs3
  in (vs'', eix3+1, min3')

cnv e p o l vs (Exp (C c)) = ggg c f ([],-1,-1)
  where f s s' = dof e p o l l s s' "false" vs

cnv eix pix oix min _ _ = ([],-1,-1)

ggg c f ow = case c of
  Log -> f "Log" "\\log"
  Ln -> f "Ln" "\\ln"
  EulerE -> f "EulerE" "\\eulere"
  Max -> f "Max" "\\max"
  Min -> f "Min" "\\min"
  LCM -> f "LCM" "\\lcm"
  GCF -> f "GCF" "\\gcf"
  Set [] -> f "Emptyset" "\\emptyset"
  SetN -> f "SetN" "\\N"
  SetZ -> f "SetZ" "\\Z"
  SetQ -> f "SetQ" "\\Q"
  SetR -> f "SetR" "\\R"
  PowerSet -> f "PowerSet" "\\powerset"
  Ast -> f "Ast" "\\ast"
  Infinity -> f "Infinity" "\\infty"
  Dom -> f "Dom" "\\dom"
  Ran -> f "Ran" "\\ran"
  Plus -> f "Plus" "\\nofix{+}"
  Minus -> f "Minus" "\\nofix{-}"
  Times -> f "Times" "\\nofix{*}"
  Div -> f "Div" "\\nofix{/}"
  
  Aggregate Plus -> f "AggregatePlus" "\\sum"
  Aggregate Times -> f "AggregateTimes" "\\prod"
  Aggregate Circ -> f "AggregateCirc" "\\bigcirc"
  Aggregate Union -> f "AggregateUnion" "\\bigcup"
  Aggregate Isect -> f "AggregateIsect" "\\bigcap"

  Eql -> f "Eql" "\\nofix{=}"
  Lt -> f "Lt" "\\nofix{<}"
  Lte -> f "Lte" "\\nofix{\\leq}"
  Gt -> f "Gt" "\\nofix{>}"
  Gte -> f "Gte" "\\nofix{\\geq}"
  Neq -> f "Neq" "\\nofix{\\neq}"
  _ -> ow

isLogical (App (C (NLPredLC _)) _) = True
isLogical (C (NLPredLC _)) = True
isLogical (App (C c) (T [e1,e2])) = c `elem` [And, Or, Imp, Iff]
isLogical (Forall _ _) = True
isLogical (Exists _ _) = True
isLogical (Bind Considering _ _) = True
isLogical (Bind InContextForall _ _) = True
isLogical _ = False

bins = [Plus,Minus,Times,Div,Mod,Union,Isect,Cart,Arrow,
        Eql,Neq,Lt,Lte,Gt,Gte,Subset,Subseteq,In,Pow,Circ,
        NotC Lt, NotC Lte, NotC Gt, NotC Gte, NotC In, NotC Subset, NotC Subseteq]

binsOps = [Plus,Minus,Times,Div,Mod,Union,Isect,Cart,Arrow,Pow,Circ]

mkExpBraced (Forall _ _) l = [Syn "\\lbrace"]++l++[Syn "\\rbrace"]
mkExpBraced (Exists _ _) l = [Syn "\\lbrace"]++l++[Syn "\\rbrace"]
mkExpBraced (App (C c) (T [e1,e2]))  l = if c `elem` [Imp, Iff] then [Syn "\\lbrace"]++l++[Syn "\\rbrace"] else l
mkExpBraced _ l = l

mkBr c0 (App (C c) (T[e1,e2])) l =
  if c `elem` binsOps && c0 `elem` binsOps then [Syn "("]++l++[Syn ")"] else l
mkBr _ _ l = l

showC' c = case c of
  And -> "and"
  Or -> "or"
  Imp -> "implies that"
  Iff -> "if and only if"
  Plus -> "+"
  Minus -> "-"
  Times -> "\\cdot"
  Div -> "/"
  Mod -> "\\mod"
  Pow -> "^"
  Circ -> "\\circ"
  PowerSet -> "\\powerset"
  Union -> "\\cup"
  Isect -> "\\cap"
  Cart -> "\\times"
  Arrow -> "\\rightarrow"
  Eql -> "="
  Neq -> "\\neq"
  Gt -> ">"
  Gte -> "\\geq"
  Lt -> "<"
  Lte -> "\\leq"
  In -> "\\in"
  Subset -> "\\subset"
  Subseteq -> "\\subseteq"
  Subsetneq -> "\\subsetneq"

  NotC c -> "\\not" ++ showC' c
  _ -> ""

showSep :: String -> [String] -> String
showSep s xs = foldr (\x y -> x ++ s ++ y) (last xs) (init xs)

----------------------------------------------------------------
-- 

--eof
