----------------------------------------------------------------
--
-- aartifact
-- http://www.aartifact.org/src/
-- Copyright (C) 2008-2010
-- A. Lapets
--
-- This software is made available under the GNU GPLv3.
--
-- Context.hs
--   Representation of state for verifier.

----------------------------------------------------------------
-- 

module Context where

import Set
import MatchingIndex
import ExpConst
import Exp
import ContextEquiv
import ContextHypergraph
import ContextRelations
import ContextAux
import ContextEval
import ContextNorm
import ContextLit

----------------------------------------------------------------
-- Representation of simulated natural context.

type Context = (VC,Relations)

state0 :: [Exp] -> Context
state0 ontology = (([],(0,[])), empRels ontology)

----------------------------------------------------------------
-- The "VC" component represents the variables and constants
-- within a context.

type VC = ([Name], (Integer,[Name]))

varsCxt :: Context -> [Name]
varsCxt ((b,_),_) = b

-- Make expression variables unique.
freshExpVars :: Exp -> Context -> (Exp, Context)
freshExpVars e ((b,(c,gs)),rs) = (e',((b,(c',gs)),rs))
  where (e',c') = uv [] c e

-- For "hiding" propositions that no longer apply because
-- bound variables have been hidden by a new quantifier.
updVars :: [Name] -> Context -> Context
updVars vs ((b,c),rs) = ((b \/ vs,c), clearVars f rs)
  where f e = (fv (b `diff` vs) e) /\ vs == []

updConsts :: [Name] -> Context -> Context
updConsts vs ((b,c),rs) = ((b,c), clearVars f rs)
  where f e = (fv (b `diff` vs) e) /\ vs == []

clearVars :: (Exp -> Bool) -> Relations -> Relations
clearVars f (aux,eqs,rs) = (aux,filtEq eqs f,rs)

----------------------------------------------------------------
-- The "Relations" component represents the known and derived
-- facts about all expressions within the context.

type Relations = ([Aux], Equivalence Exp Index, Hypergraph Const Index)

empRels :: [Exp] -> Relations
empRels laws = foldl updRels (foldl addLaw init laws) laws
  where init = ([Aux1 []], snd $ ixsEqv [C$B True] empEquiv, empHG)

trueExpsCxt :: Context -> [Exp]
trueExpsCxt (_,(_,eqs,_)) =  getByIx i eqs
  where ([i],_) = ixsEqv [C (B True)] eqs

eqCxt :: Context -> Exp -> Exp -> Bool
eqCxt (_,(_,eqs,_)) e1 e2 = eqChkZ 0 eqs e1 e2

assertCxt :: Context -> Exp -> Bool
assertCxt (_,rs) e = chkRels rs e

assumeCxt :: Exp -> Context -> Context
assumeCxt e s = foldl each s $ splitAnd e where
  each s e = (vcs', updRelsTrue (updRels rs' e) e)
    where (vcs',rs') = considerCxt e s

considerCxt :: Exp -> Context -> Context
considerCxt e (vcs,(aux0,eqs0,hg0)) =
  let (_,eqs0') = ixsEqv (subs e) eqs0
      rs = (aux0,eqs0',resetMarksHG hg0) --addLaw (aux0,eqs0',resetMarksHG hg0) e
      pr f rs = foldr f rs (subs e) --Subexps. occur later in list.
      rs' = foldr pr rs [considRels,considAux1,considNorm,considEval,considLit]
  in (vcs,closureRels rs')

addLaw :: Relations -> Exp -> Relations
addLaw rs e = foldr (\add rs-> add rs e) rs [addAuxLaw,addRelLaw]

--getR (_,(_,eqs,(ls,x))) = (eqs,"^%",(ls,"^%",x))

--eof
