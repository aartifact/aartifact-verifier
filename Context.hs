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
import ExpPrint
import ContextEquiv
import ContextHypergraph
import ContextRelations
import ContextAux
import ContextEval
import ContextNorm
import ContextLit

----------------------------------------------------------------
-- Representation of simulated natural context.

type Context = (VC,Relations,Stat)

state0 :: [Exp] -> Context
state0 ontology = (([],(0,[])), empRels ontology, stat0)

----------------------------------------------------------------
-- The "Stat" component represents statistics accumulated during
-- the simulation process.

type Stat = [[Integer]]

statCxt :: Context -> Stat
statCxt (_,_,s) = s

stat0 :: Stat
stat0 = [[],[],[],[],[]]

updStat ::  Stat -> Context -> Context
updStat s' (v,r,s) = (v,r,s')

updRelStat :: Exp -> Relations -> Stat -> Stat
updRelStat e (_,eqs',hg') [is,js,ks,es,es'] =
  let (eqDomSz, eqRanSz) = eqvSize eqs' in
  [hgSize hg':is, eqDomSz:js, eqRanSz:ks, expStat e:es, expStat' e:es']

shStats :: Stat -> String
shStats [is,js,ks,es,es'] = shStats' [is,js,ks,es,es'] where
  shStats' [i:is,j:js,k:ks,e:es,e':es'] = shStats' [is,js,ks,es,es']
           ++ "\n" ++ show i ++ "\t" ++ show j ++ "\t" ++ show k ++ "\t" ++ show e ++ "\t" ++ show e'
  shStats' _ = ""

expStat e = case e of
  C _ -> 0
  Var _ -> 0
  App (C c) e -> if c `elem` [And,Imp,Iff,Or] then 0 else 1 + expStat e
  App e1 e2 -> expStat e1 + expStat e2 + 1
  T es -> 1 + (foldr (+) 0 $ map expStat es)
  Forall _ e -> 0 --expStat e + 1
  Exists _ e -> 0 --expStat e + 1
  Bind _ _ e -> expStat e + 1
  
expStat' e = toInteger $ foldr max 0 $ map f cs where
  cOnly (C c) = [c]
  cOnly _ = []
  f c = length (filter ((==) c) cs)
  cs = concat (map cOnly $ subs e)

----------------------------------------------------------------
-- The "VC" component represents the variables and constants
-- within a context.

type VC = ([Name], (Integer,[Name]))

varsCxt :: Context -> [Name]
varsCxt ((b,_),_,_) = b

-- Make expression variables unique.
freshExpVars :: Exp -> Context -> (Exp, Context)
freshExpVars e ((b,(c,gs)),rs,stat) = (e',((b,(c',gs)),rs,stat))
  where (e',c') = uv [] c e

-- For "hiding" propositions that no longer apply because
-- bound variables have been hidden by a new quantifier.
updVars :: [Name] -> Context -> Context
updVars vs ((b,c),rs,stat) = ((b \/ vs,c), clearVars f rs,stat)
  where f e = (fv (b `diff` vs) e) /\ vs == []

updConsts :: [Name] -> Context -> Context
updConsts vs ((b,c),rs,stat) = ((b,c), clearVars f rs,stat)
  where f e = (fv (b `diff` vs) e) /\ vs == []

clearVars :: (Exp -> Bool) -> Relations -> Relations
clearVars f (aux,eqs,rs) = (aux,filtEq eqs f,rs)

----------------------------------------------------------------
-- The "Relations" component represents the known and derived
-- facts about all expressions within the context.

type Relations = ([Aux], Equivalence Exp Index, Hypergraph Const Index)

empRels :: [Exp] -> Relations
empRels laws = foldl updRels (foldl addLaw init laws) laws
  where init = (aux0, snd $ ixsEqv [C$B True] empEquiv, empHG)

trueExpsCxt :: Context -> [Exp]
trueExpsCxt (_,(_,eqs,_),_) =  getByIx i eqs
  where ([i],_) = ixsEqv [C (B True)] eqs

eqCxt :: Context -> Exp -> Exp -> Bool
eqCxt (_,(_,eqs,_),_) e1 e2 = eqChkZ 0 eqs e1 e2

assertCxt :: Context -> Exp -> Bool
assertCxt (_,rs,_) e = chkRels rs e

assumeCxt :: Exp -> Context -> Context
assumeCxt e s = foldl each s $ splitAnd e where
  each s e = (vcs'', updRelsTrue (updRels rs'' e) e, stat'')
    where (vcs'',rs'',stat'') = considerCxt1 e (vcs',rs',stat')
          (vcs',rs',stat') = considerCxt e s

considerCxt :: Exp -> Context -> Context
considerCxt e (vcs,(aux0,eqs0,hg0),stat) =
  let (_,eqs0') = ixsEqv (subs e) eqs0
      rs = (aux0,eqs0',resetMarksHG hg0) --addLaw (aux0,eqs0',resetMarksHG hg0) e
      pr f rs = foldr f rs (subs e) --Subexps. occur later in list.
      rs' = foldr pr rs [considRels,considNorm,considAux1,considEval,considLit]
  in (vcs,closureRels rs',updRelStat e rs' stat)

considerCxt1 :: Exp -> Context -> Context
considerCxt1 e (vcs,(aux0,eqs0,hg0),stat) =
  let rs' = considAux2 e (aux0,eqs0,resetMarksHG hg0)
  in (vcs,closureRels rs',stat)

reportCxt :: [Exp] -> Context -> String
reportCxt es (_,rels,_) = "~@"++str++"@~"
  where str = foldr (\x y -> x++"|"++y) (last l) (init l)
        l = map expPrint $ reportRels es rels

addLaw :: Relations -> Exp -> Relations
addLaw rs e = foldr (\add rs-> add rs e) rs [addAuxLaw,addRelLaw]

--getR (_,(_,eqs,(ls,x))) = (eqs,"^%",(ls,"^%",x))

--eof
