----------------------------------------------------------------
--
-- aartifact
-- http://www.aartifact.org/src/
-- Copyright (C) 2008-2010
-- A. Lapets
--
-- This software is made available under the GNU GPLv3.
--
-- ContextAux.hs
--   Auxiliary context component: syntax-directed propositions.

----------------------------------------------------------------
-- 

module ContextAux where

import ExpConst (Const(..))
import Exp (Exp(..), splitAnd, fv)
import ExpSubst
import ContextRelations

----------------------------------------------------------------
-- Consideration with respect to auxiliary context.

considAux1 e (rs@((aux@[Aux1 as]),_,_)) = pr rs e as
  where pr r e as = case as of (a:as)->pr (pr1 r a e) e as;_->r
        pr1 r (e1,e2,e3) e = case match (fv [] e1) e1 e of
          Nothing -> r
          Just sub -> let e2's = splitAnd $ subst sub e2 in
            if and (map (chkRels r) e2's) then
              let e3s = splitAnd $ subst sub e3
              in foldr (\y x -> updRels x y) r e3s 
            else r

----------------------------------------------------------------
-- Auxiliary structure for a list of various types.

data Aux = Aux1 [(Exp,Exp,Exp)] | Aux2

----------------------------------------------------------------
-- Converting expressions to ontology laws.

add1 x ((Aux1 xs):as) = Aux1 (x:xs):as
add1 x (a:as) = a:add1 x as
add1 _ [] = []

addAuxLaw (rs@(aux,eqs,hg)) e = case e of
  Bind Considering vs (T[e1,App (C Imp) (T[e2,e3])]) ->
    (add1 (e1,e2,e3) aux, eqs, hg)
  Bind Considering vs (T[e1,e3]) ->
    (add1 (e1,C (B True),e3) aux, eqs, hg)
  _ -> rs

--eof
