----------------------------------------------------------------
--
-- aartifact
-- http://www.aartifact.org/src/
-- Copyright (C) 2008-2010
-- A. Lapets
--
-- This software is made available under the GNU GPLv3.
-- 
-- ContextNorm.hs
--   Common normal forms for arithmetic expressions.

----------------------------------------------------------------
-- 

module ContextNorm where

import Ratio
import Data.List (sortBy)

import Set
import ExpConst
import Exp
import ContextRelations

----------------------------------------------------------------
-- Context contribution: normalize an equations and add it to
-- the corresponding expression's equivalence class.

considNorm e0 (rs@(aux,eqs,hg)) = 
  let es = allNorms rs e0
      each [] rs = rs
      each (e:es) rs = each es $ updRelsEq rs e0 e
  in each es rs

----------------------------------------------------------------
-- Context contribution: evaluate an expression and add it to
-- the context.

normsToCheck :: [Exp -> Exp]
normsToCheck =
 [ norm plusNorm Plus Times
 , norm multNorm0 Times Pow
 , normRec multNorm1 (normNoP plusNorm Plus Times)
 ]

allNorms rs (e@(App (C Eql) (T[e1,e2]))) = allNorms' e
  --if (chkRels rs (bOp In e1 (C SetR)) && chkRels rs (bOp In e2 (C SetR))) then allNorms' e else allNorms' e
allNorms rs (e@(Forall ns (App (C Eql) (T[e1,e2])))) = [(Forall ns  (App (C Eql) (T[e2,e1])))]
allNorms rs (Forall ns (App (C Imp) (T[e0, (App (C Eql) (T[e1,e2]))]))) = [(Forall ns (App (C Imp) (T[e0, (App (C Eql) (T[e2,e1]))])))]
allNorms rs _ = []

allNorms' (e@(App (C Eql) (T[e1,e2]))) = [n e | n <- normsToCheck] ++ (if simpPlusEqnChk e then [C(B True)] else [])
allNorms' _ = []

simpPlusEqnChk (App (C Eql) (T [e1,e2])) =
  let (App (C Eql) (T [e1',e2'])) = norm plusNorm Plus Times (App (C Eql) (T [e1,e2]))
  in e1' == e2'
simpPlusEqnChk _ = False

srt :: [(Exp,b)] -> [(Exp,b)]
srt = sortBy $ \p p' -> if fst p < fst p' then LT else GT

norm n op1 op2 (App (C op) (T [el,er])) = 
  let (esl, esr) = p $ ((filter (\p->snd p/=0)) $ srt $ n el 1, (filter (\p->snd p/=0)) $srt $ n er 1) --(filter (\p->snd p/=0)) $works for plus,others?
      (esle, lvs) = unzip esl
      (esre, rvs) = unzip esr
      cv = map (\x -> C $ N x)
      bld = bOp (RatioMultiSet op1 op2)
  in bOp op (bld (T esle) (T $ cv lvs)) (bld (T esre) (T $ cv rvs))
norm n op1 op2 e = e

normRec n nnp (App (C Eql) (T [el,er])) =
  let ((el'',vl''), (er'',vr'')) = (unzip $ mknnp $ srt $ n el 1, unzip $ mknnp $ srt $ n er 1)
      mknnp = map (\(e,v) -> (e, nnp v))
      bld = bOp (RatioMultiSet Times Pow)
  in bOp Eql (bld (T el'') (T vl'')) (bld (T er'') (T vr''))
normRec n nnp e = e

normNoP n op1 op2 e = 
  let (es,vs) = unzip $ srt $ n e 1
      cv = map (\x -> C $ N x)
  in bOp (RatioMultiSet op1 op2) (T es) (T $ cv vs)

join op omit = foldr add where
  add (e',i') ((e,i):eis) =
    if e /= e' then (e,i):(add (e',i') eis)
    else if omit $ op i i' then eis
    else (e, op i i'):eis 
  add p [] = [p]

plusNorm (App (C Plus)  (T [e1,e2]))     fac = (join (+) ((==) 0)) (plusNorm e1 fac) (plusNorm e2 fac)
plusNorm (App (C Minus) (T [e1,e2]))     fac = (join (+) ((==) 0)) (plusNorm e1 fac) (plusNorm e2 (-1 * fac))
plusNorm (App (C Times) (T [e,C (N i)])) fac = plusNorm e (i * fac)
plusNorm (App (C Times) (T [C (N i),e])) fac = plusNorm e (i * fac)
plusNorm (App (C Div)   (T [e,C (N i)])) fac = if i /= 0 then plusNorm e (fac / i) else [(bOp Div e $ C $ N i, fac)]
plusNorm (App (C Neg)   e)               fac = plusNorm e (-1 * fac)
plusNorm (C (N i))                       fac = [(C $ N 1, i * fac)]
plusNorm e                               fac = [(e, fac)]

multNorm0 (App (C Times) (T [e1,e2]))        exp = (join (+) ((==) 0)) (multNorm0 e1 exp) (multNorm0 e2 exp)
multNorm0 (App (C Pow)   (T [(C (N 1)),e2])) exp = [(C $ N 1, 1)]
multNorm0 (App (C Pow)   (T [e1,(C (N 0))])) exp = [(C $ N 1, 1)]
multNorm0 (App (C Pow)   (T [e1,(C (N i))])) exp = multNorm0 e1 (exp * i)
multNorm0 (C (N 1))                          exp = [(C $ N 1, 1)]
multNorm0 e                                  exp = [(e,exp)]

multNorm1 (App (C Times) (T [e1,e2])) i = join (bOp Plus) (\_->False) (multNorm1 e1 i) (multNorm1 e2 i)
multNorm1 (App (C Pow)   (T [e1,e2])) i = [(e1, if i == -1 then (App (C Neg)) e2 else e2)]
multNorm1 e                           i = [(e, C $ N i)]

-- Factor a list of frequencies by first finding the LCD, then
-- dividing out the GCD of the numerators.
p (efs0l, efs0r) = (conv efs0l, conv efs0r) where
  efs = (filter (\p->snd p/=0)) (efs0l++efs0r)
  gcdL ns = foldr gcd (foldr (*) 1 ns) ns
  lcmL ns = foldr lcm (foldr (*) 1 ns) ns
  mlcm = lcmL (map denominator (map snd efs))
  efs' = map (\(e,f) -> (e,((fromInteger $ numerator f) * (mlcm % (denominator f))))) efs
  mgcd = gcdL (map numerator (map snd efs'))
  conv = map (\(e,f) -> (e, f / (fromInteger mgcd)))

--eof
