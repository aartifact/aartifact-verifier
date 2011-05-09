----------------------------------------------------------------
--
-- aartifact
-- http://www.aartifact.org/src/
-- Copyright (C) 2008-2011
-- A. Lapets
--
-- This software is made available under the GNU GPLv3.
--
-- ContextAux.hs
--   Auxiliary context component: syntax-directed propositions.

----------------------------------------------------------------
-- 

module ContextAux --(addAuxLaw, Aux, considAux1, considAux2, aux0)
  where

import ExpConst (Const(..))
import Exp (Exp(..), splitAnd, fv)
import ExpSubst (match, exmch, subst, resetVar)
import ContextRelations

----------------------------------------------------------------
-- Auxiliary structure for storing lists of expressions drawn
-- from the ontology.

data Aux = Aux1 [(Exp,Exp,Exp)] | Aux2 [(Const,Exp,Exp)]
  deriving Show

aux0 = [Aux1 [], Aux2 []]

----------------------------------------------------------------
-- Consideration with respect to auxiliary context.

considAux1 e (rs@((aux@(Aux1 as:_)),_,_)) = pr rs e as
  where pr r e as = case as of (a:as)->pr (pr1 r a e) e as;_->r
        pr1 r (e1,e2,e3) e = case match (fv [] e1) e1 e of
          Nothing -> r
          Just sub -> let e2's = splitAnd $ subst sub e2 in
            if and (map (chkRels' r) e2's) then
              let e3s = splitAnd $ subst sub e3
              in foldr (\y x -> updRels'' x y) r e3s 
            else r

considAux2 e (rs@((aux@(_:Aux2 as:_)),_,_)) = pr rs e as
  where pr r e as = case as of (a:as)->pr (pr1 r a e) e as;_->r
        pr1 r (Imp,e1,e2) e = case exmch (fv [] e1) e1 e of
          Nothing -> r
          Just sub -> 
            let e2s = splitAnd $ subst sub e2
            in foldr (\y x -> updRels'' x y) r e2s
        pr1 r _ _ = r

----------------------------------------------------------------
-- Converting expressions to ontology laws.

add2 x ((Aux2 xs):as) = Aux2 (x:xs):as
add2 x (a:as) = a:add2 x as
add2 _ [] = []

add1 x ((Aux1 xs):as) = Aux1 (x:xs):as
add1 x (a:as) = a:add1 x as
add1 _ [] = []

addAuxLaw (rs@(aux,eqs,hg)) e = case e of
  Bind Considering vs (T[e1,App (C Imp) (T[e2,e3])]) ->
    (add1 (e1,e2,e3) aux, eqs, hg)
  Bind Considering vs (T[e1,e3]) ->
    (add1 (e1,C (B True),e3) aux, eqs, hg)
  Bind InContextForall _ (App (C Imp) (T[e1,e2])) ->
    (add2 (Imp,e1,e2) aux, eqs, hg)
  Bind InContextForall _ (App (C Iff) (T[e1,e2])) ->
    (add2 (Imp,e2,e1) (add2 (Imp,e1,e2) aux), eqs, hg)
  _ -> rs

--eof
