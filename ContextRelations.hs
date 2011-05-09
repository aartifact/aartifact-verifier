----------------------------------------------------------------
--
-- aartifact
-- http://www.aartifact.org/src/
-- Copyright (C) 2008-2011
-- A. Lapets
--
-- This software is made available under the GNU GPLv3.
--
-- ContextRelations.hs
--   Representation of context of expressions equivalence
--   classes and relations over these classes. Additional
--   components of the simulated natural context are built on
--   top of this base representation.

----------------------------------------------------------------
-- 

module ContextRelations (considRels, addRelLaw, updRels, updRels'',
                         updRelsTrue, updRelsEq, chkRels, chkRels', eqChkZ, 
                         closureRels, ixsEqv, reportRels) where

import Set
import MatchingIndex
import ExpConst (Const(..))
import Exp (Exp(..), splitAnd, fv, eqOpen, subs, consts, bOp)
import ExpPredicate (PredWrap(..))
import ExpSubst (resetVar)
import ContextEquiv
import ContextHypergraph

----------------------------------------------------------------
-- External interface and support functions.

-- This wrapper is needed in case the expression contains
-- local variables.
ixsEqv :: [Exp] -> Equivalence Exp Index -> ([Index], Equivalence Exp Index)
ixsEqv es eqs = getIxsWithPut (map resetVar es) eqs
ixsEqv' es eqs = getIxsWithPut es eqs

type Relations a = (a, Equivalence Exp Index, Hypergraph PredWrap Index)

updRels'' :: Relations a -> Exp -> Relations a
updRels'' rs (e@(App (C _) _)) = updRels rs e
updRels'' rs e = updRelsTrue rs (resetVar e)

updRels :: Relations a -> Exp -> Relations a
updRels rs (App (C Eql) (T[e1,e2])) = updRelsEq rs e1 e2
updRels rs e = upd ixsEqv' (upd ixsEqv rs e) e
upd ixsEqv (aux,eqs,hg) (App (C c) (T es)) = [(PW c,is)] |=>* (aux,eqs',hg)
  where (is,eqs') = ixsEqv es eqs
upd _ rs _ = rs

updRelsTrue :: Relations a -> Exp -> Relations a
updRelsTrue rs e = rs''
  where rs'' = updRels rs' (bOp Eql (resetVar e) (C(B True)))
        rs' = updRels rs (bOp Eql e (C(B True)))

updRelsEq :: Relations a -> Exp -> Exp -> Relations a
updRelsEq (aux,eqs,hg) e0 e = [(PW Eql,[i,i'])] |=>* (aux,mergeEC i i' eqs',relabelHG hg i i')
  where ([i,i'],eqs') = ixsEqv' [e0',e'] eqs
        (e0',e') = (resetVar e0, resetVar e)

-- This checks the structure for a particular relation instance.
-- This currently takes linear time, this should be much faster.
chkRels :: Relations a -> Exp -> Bool
chkRels _ (C (B True)) = True
chkRels (aux,eqs,_ ) (App (C Eql) (T [e1,e2])) = eqChkZ 1 eqs (resetVar e1) (resetVar e2)
chkRels (aux,eqs,rs) (App (C c) (T es)) = (PW c,is) `edgeHG` rs
  where (is,_) = ixsEqv es eqs
chkRels (aux,eqs,rs) (App (C c) e) = (PW c,is) `edgeHG` rs
  where (is,_) = ixsEqv [e] eqs
chkRels _ _ = False

chkRels' :: Relations a -> Exp -> Bool
chkRels' _ (C (B True)) = True
chkRels' (aux,eqs,_ ) (App (C Eql) (T [e1,e2])) = eqChkZ 1 eqs (resetVar e1) (resetVar e2)
chkRels' (aux,eqs,rs) (App (C c) (T es)) = (PW c,is) `edgeHG` rs
  where (is,_) = ixsEqv es eqs
chkRels' (_,eqs,_rs) e = i == j
  where ([i,j],_) = ixsEqv [e,C(B True)] eqs

-- Recursive equality check.
eqChk :: (Exp -> Exp -> Bool) ->  Exp -> Exp -> Bool
eqChk eq e e' = eqOpen (eqChk eq) e e' || eq e e'

eqChkZ :: Int -> Equivalence Exp Index -> Exp -> Exp -> Bool
eqChkZ 0 er e1 e2 = eqChk (\e1-> \e2-> (chkEquality er e1 e2) || (e1==e2)) e1 e2
eqChkZ n er e1 e2 = eqChk (\e1-> \e2-> (eqChkZ (n-1) er e1 e2)) e1 e2

-- Reporting on expressions.
reportRels :: [Exp] -> Relations a -> [Exp]
reportRels es (_,eqs,rs) = [(App (C p) (T (map (conv eis) is))) | (PW p,is) <- l'']
  where l'' = reportHG (\is' -> is' `subset` is) rs
        (is,_) = ixsEqv es eqs
        eis = zip es is
        conv ((e,i):eis) i' = if i==i' then e else conv eis i'
        conv _ _ = C C_None

closureRels :: Relations a -> Relations a
closureRels (aux,eqs,hg) = (aux,eqs',hg') where (eqs',hg') = closureHG' (PW Eql) (eqs,hg)

----------------------------------------------------------------
-- Internal support functions.

(|=>) :: (Eq b, Ord a) => [Edge a b] -> (c,Equivalence Exp b,Hypergraph a b) -> (c,Equivalence Exp b,Hypergraph a b)
(|=>) nrs (a,e,r) = (a, e, putsHG r nrs)

(|=>*) :: [Edge PredWrap Index] -> (a,Equivalence Exp Index,Hypergraph PredWrap Index) -> (a,Equivalence Exp Index,Hypergraph PredWrap Index)
(|=>*) (nrs@[(PW Eql,[i,j])]) (a,e,r) = 
  closureRels $ nrs |=> (a, mergeEC i j e, resetMarksHG r)
(|=>*) nrs (a,e,r) = closureRels $ nrs |=> (a, e, resetMarksHG r)

-- Closure operation on the relation graph (with semantic
-- support for the "Eql" relation: equivalent nodes are
-- relabelled so that they have the same label).
closureHG' :: (Eq a, Ord a, Eq b, Ord b) => b -> (Equivalence a Index, Hypergraph b Index) -> (Equivalence a Index, Hypergraph b Index)
closureHG' eqC (eqs, (hg@(ls,_))) =
   let ls' = [l | (mrk,l)<-ls, mrk]
       newEdges = concat [matchIxs sr l o | ((fr,sr),o)<-ls', l<-getsHG hg fr]
       hg' = putsHG (resetMarksHG hg) newEdges
       eqM [i1,i2] (eqs,hg) = (mergeEC i1 i2 eqs, relabelHG hg i1 i2) 
       (eqs'',g'') = foldr eqM (eqs,hg') (map snd $ getHG hg' eqC) 

       r_sz = hgSize g''
       (e_sz, q_sz) = eqvSize eqs''
       sz_ok = (r_sz < e_sz)

   in (if True && hasMarkedHG g'' then closureHG' eqC else id) (eqs'',g'')

----------------------------------------------------------------
-- Consideration with respect to relation context.

considRels (e0@(App (C (NLPredLC _)) (T es))) (aux,eqs,rs) =
  let (is, eqs') = ixsEqv es eqs
  in foldr considRels' (aux,eqs',rs) es

considRels (e0@(App (C c) (T es))) (aux,eqs,rs) =
  if c `elem` [Or,Pow,Plus,Minus,Times,Div,Mod,Otimes,Oplus,Union,Isect,Cart,Arrow,SetExplicit,GCF,LCM] then
    let (i1:is, eqs') = ixsEqv ([e0]++es) eqs
        ls = if c==SetExplicit then [(PW In, [j,i1]) | j <- is] else []
        rs' = (ls++[(PW $ SLC Eql c, i1:is)]) |=> (aux,eqs', rs)
    in rs'
  else
    (aux,eqs,rs)

considRels (e0@(App (C c) e)) (aux,eqs,rs) =
  if c `elem` [Neg,Ran,Dom,Max,Min,Ln,Log] then
    let ([i1,i2], eqs') = ixsEqv [e0,e] eqs
    in [(PW $ SLC Eql c, [i1,i2])] |=> (aux,eqs', rs)
  else
    (aux,eqs,rs)

considRels (e0@(App e1 e2)) (aux,eqs,rs) =
  let ([i0,i1,i2], eqs') = ixsEqv [e0,e1,e2] eqs
  in [(PW $ SLC Eql Apply, [i0,i1,i2])] |=> (aux,eqs', rs)

considRels (e0@(T es)) (aux,eqs,rs) =
  let (i:js, eqs') = ixsEqv ((T es):es) eqs
  in ([(PW $ SLC Eql Tuple, i:js)]) |=> (aux,eqs',rs)

considRels _ rs = rs

considRels' (T es) (aux,eqs,rs) =
  let (i:js, eqs') = ixsEqv ((T es):es) eqs
      ls = [(PW $ NLPredLC [Nothing, Just "is", Just "a", Just "component", Just "of", Nothing], [j,i]) | j <- js]
  in (ls++[(PW $ SLC Eql Tuple, i:js)]) |=> (aux,eqs',rs)
considRels' _ rs = rs

----------------------------------------------------------------
-- Loading and initialization of relation ontology.

addRelLaw (aux,eqs,rs) e = 
  let cs = map C $ getAxCs e
      (is,eqs') = ixsEqv cs eqs
  in (aux, eqs', foldl addLawHG rs (convertPW (zip cs is) e))

getAxCs :: Exp -> [Const]
getAxCs (Forall ns (App (C Imp) (T[_,(App (C cl) (T [e1,e2]))]))) =
  if cl `elem` [Imp,Iff] then concat $ map consts (splitAnd e1 ++ splitAnd e2) else []
getAxCs (Forall ns (App (C Imp) (T[_,e]))) = concat $ map consts (splitAnd e)
getAxCs _ = []

convArgs ixs n js nes ((App (C c) e):es) =
  case convArgs ixs (n-1) [] [] (case e of T es->es; _->[e]) of
    Just (n',as',nes') -> convArgs ixs n' (n:js) (((SLC Eql c,n:as'):nes') ++ nes) es
    Nothing -> Nothing
convArgs ixs n js nes ((App e1 e2):es) =
  case convArgs ixs (n-1) [] [] [e1,e2] of
    Just (n',as',nes') -> convArgs ixs n' (n:js) (((SLC Eql Apply,n:as'):nes') ++ nes) es
    Nothing -> Nothing
convArgs ixs n js nes ((T es0):es) =
  case convArgs ixs (n-1) [] [] es0 of
    Just (n',as',nes') -> convArgs ixs n' (n:js) (((SLC Eql Tuple,n:as'):nes') ++ nes) es
    Nothing -> Nothing
convArgs ixs n js nes  (e:es) = case lookup e ixs of
  Just 0 -> Nothing
  Just j -> convArgs ixs n (j:js) nes es
  _ -> Nothing
convArgs ixs n js nes  [] = Just (n,reverse js, nes)

convExp ixs n (e0@(App (C c) (T es))) = case convArgs ixs n [] [] es of
  Nothing -> Nothing
  Just (n,js, nes) -> Just (n,(c,js), nes)
convExp _ _ _ = Nothing

convExps ixs n old new (e:es) = case (convExp ixs n e) of
  Nothing -> Nothing
  Just (n',eo,ens) -> convExps ixs n' (eo:old) (ens++new) es
convExps ixs n old new [] = Just (n,reverse old,reverse new)

convertPW :: [(Exp, Index)] -> Exp -> [([(PredWrap, [Index])], [(PredWrap, [Index])])]
convertPW cns e = map f l
  where l = convert cns e
        f = (\(x,y) -> (map g x,map g y))
        g = (\(x,y) -> (PW x, y))

convert :: [(Exp, Index)] -> Exp -> [([(Const, [Index])], [(Const, [Index])])]
convert cns (Forall ns (App (C Imp) (T[e00,(App (C c) (T [e1,e2]))]))) =
  if c == Iff then
       convert cns (Forall ns (App (C Imp) (T[e00,(App (C Imp) (T [e1,e2]))]))) 
    ++ convert cns (Forall ns (App (C Imp) (T[e00,(App (C Imp) (T [e2,e1]))])))
  else 
  let es1 = splitAnd e1
      es2 = splitAnd e2
      vns = zip (map Var ns) [toInteger $ -1 * i | i <- [1..length ns]]
      n0 = toInteger $ -1 * (length ns + 1)
      ixs = vns++cns
  in case (convExps ixs n0 [] [] es1) of
       Just (n1, es1',es1x') -> case (convExps ixs n1 [] [] es2) of
         Just (_, es2',es2x') -> [(es1'++es2x'++es1x', es2')]; _ -> []
       _ -> []

convert cns (Forall ns (App (C Imp) (T[_,e2]))) =
  let es1 = []
      es2 = splitAnd e2
      vns = zip (map Var ns) [toInteger $ -1 * i | i <- [1..length ns]]
      n0 = toInteger $ -1 * (length ns + 1)
      ixs = vns++cns
  in case (convExps ixs n0 [] [] es2) of
       Just (_,_,[]) -> []
       Just (_, es2',es2x') -> [(es2x', es2')]
       _ -> []

convert cns _ = []

--eof
