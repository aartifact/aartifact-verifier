----------------------------------------------------------------
--
-- aartifact
-- http://www.aartifact.org/src/
-- Copyright (C) 2008-2010
-- A. Lapets
--
-- This software is made available under the GNU GPLv3.
--
-- ValidatePropositional.hs
--   Functions for turning a list of statements (a source
--   document) into an output representing its validation
--   status with respect to propositional logic.

----------------------------------------------------------------
-- 

module ValidationPropositional (validatePropositional, propOnt) where

import Data.Maybe (catMaybes)

import Set
import IOPrintFormat
import IOSource
import ExpConst (Const(..))
import Exp
import ExpSubst
import Context
import ContextEval
import ValidationComp

----------------------------------------------------------------
-- Ontology for propositional logic.

propOnt =
   "\\vbeg"
 ++"Assume considering $P \\Rightarrow Q$, \\l{$P \\Rightarrow Q$ is the implication from $P$ to $Q$}."
 ++"Assume for any $P,Q,R$, \\l{$R$ is the implication from $P$ to $Q$} and \\l{$R$ is true} implies that \\l{$P$ does imply $Q$}."
 ++"Assume for any $P,Q,R$, \\l{$P$ does imply $Q$} and \\l{$Q$ does imply $R$} implies that \\l{$P$ does imply $R$}."
 ++"Assume for any $P,Q,R$, \\l{$R$ is the implication from $P$ to $Q$} and \\l{$P$ does imply $Q$} implies that \\l{$R$ is true}."
 ++"Assume for any $P,Q$, \\l{$P$ does imply $Q$} and \\l{$P$ is true} implies that \\l{$Q$ is true}."
  
 ++"Assume considering $P \\wedge Q$, \\l{$P \\wedge Q$ is the conjunction of $P$ and $Q$}."
 ++"Assume for any $P,Q,R$, \\l{$R$ is the conjunction of $P$ and $Q$}, \\l{$P$ is true}, and \\l{$Q$ is true} implies that \\l{$R$ is true}."
 ++"Assume for any $P,Q,R$, \\l{$R$ is the conjunction of $P$ and $Q$} and \\l{$R$ is true} implies that \\l{$P$ is true} and \\l{$Q$ is true}."
  
 ++"Assume considering $P \\vee Q$, \\l{$P \\vee Q$ is the disjunction of $P$ and $Q$}."
 ++"Assume for any $P,Q,R$, \\l{$R$ is the disjunction of $P$ and $Q$} and \\l{$P$ is true} implies that \\l{$R$ is true}."
 ++"Assume for any $P,Q,R$, \\l{$R$ is the disjunction of $P$ and $Q$} and \\l{$Q$ is true} implies that \\l{$R$ is true}."

 ++"Assume for any $P,Q$, if \\l{$P$ is false} and \\l{$Q$ is the negation of $P$} then \\l{$Q$ is true}."
 ++"Assume for any $P,Q$, if \\l{$P$ is true} and \\l{$Q$ is the negation of $P$} then \\l{$Q$ is false}."
 ++"Assume for any $P,Q$, if \\l{$Q$ is the negation of $P$} then \\l{$P$ is the negation of $Q$}."
 ++"Assume considering $\\neg P$, \\l{$\\neg P$ is the negation of $P$}."

 ++"Assume for any $P,Q,R$, \\l{$P$ does imply $Q$}, \\l{$P$ does imply $R$}, \\l{$R$ is the negation of $Q$} implies \\l{$P$ is false}."

 ++"Assume for any $P,Q,R,S$, \\l{$P$ does imply $S$}, \\l{$Q$ does imply $S$}, \\l{$R$ is the disjunction of $P$ and $Q$} implies \\l{$R$ does imply $S$}."
 ++"\\vend"

assertCxt' s e = assertCxt s e || assertCxt s (App (C (NLPredLC [Nothing,Just "is",Just "true"])) (T[e]))
assumeCxt' e s = assumeCxt (App (C (NLPredLC [Nothing,Just "is",Just "true"])) (T[e])) s --(assumeCxt e s) 

----------------------------------------------------------------
-- Process a list of statements while maintaining a context,
-- and validate expressions with respect to this context.

validatePropositional :: [Stmt] -> [Stmt] -> ([Stmt], Stat)
validatePropositional ont ss = (\(ss,(_,_,st))->(ss,st)) $ execs (state0 ont') ss
  where ont' = concat $ map (\x->case x of ExpStmt _ (e,_)->[e];_->[]) ont

validatePropositional' cxtraw ss = (\(ss,(_,_,st))->(ss,st)) $ execs (state0 []) ss
rawcxt ont = state0 $ concat $ map (\x->case x of ExpStmt _ (e,_)->[e];_->[]) ont

exec :: Context -> Stmt -> ([Stmt], Context)
exec state (s@(Text _)) = ([s], state)
exec state (s@(SyntaxError _)) = ([s], state)
exec state (s@(Intro src ty vs)) = ([Intro (SrcErr src (ErrVer "")) ty vs], state)
exec state (ExpStmt Assert (e,src)) = 
    if isErr srcChk then ([ExpStmt Assert (e,srcChk)], state')
    else ([ExpStmt Assert (e,src')], state'')
  where state'' = updStat stat' $ if isErr src' then state' else assumeCxt' e state'
        stat' = statSrc src'
        src' = vArt state' e src
        srcChk = vAsu state' e src
        state' = considerCxt e state
exec state (ExpStmt si (e,src)) = ([ExpStmt si (e,src')], state')
  where state' = if isErr src' then considerCxt e state else 
                   assumeCxt' e state
        src' = vAsu state e src

exec state (Include n ss) = (map (mkIncludeWrap n) rs, state')
  where (rs, state') = execs state ss
exec state stmt = ([stmt],state)

execs :: Context -> [Stmt] -> ([Stmt], Context)
execs state []     = ([], state)
execs state (s:ss) = (vs++vs', state'') where
  (vs , state' ) = exec  state  s
  (vs', state'') = execs state' ss

----------------------------------------------------------------
-- Analysis and verification of expressions with feedback in the
-- form of source annotations/tags.

vAsu :: Context -> Exp -> Src -> Src
vAsu s e (SrcIg [l,src,r]) = SrcIg [l,vAsu s e src,r]
vAsu s (App (C (NLPredC _)) (T [])) src = SrcOk src
vAsu s (App (C Imp) (T[e1,e2])) (SrcL ts [s1,s2]) = SrcL ts [vAsu s e1 s1, vAsu s e2 s2]
vAsu s (App (C Iff) (T[e1,e2])) (SrcL ts [s1,s2]) = SrcL ts [vAsu s e1 s1, vAsu s e2 s2]
vAsu s (App (C Not) e)          (SrcL ts [src]) = SrcL ts [vAsu s e src]
vAsu s (App (C And) (T[e1,e2])) (SrcL ts [s1,s2]) = SrcL ts [vAsu s e1 s1, vAsu s e2 s2]
vAsu s (App (C Or)  (T[e1,e2])) (SrcL ts [s1,s2]) = SrcL ts [vAsu s e1 s1, vAsu s e2 s2]
vAsu s e src = SrcErr src (ErrVer "")

vArt :: Context -> Exp -> Src -> Src
vArt s e (SrcIg [l,src,r]) = SrcIg [l,vArt s e src,r]

vArt s (e@(App (C Imp) (T[e1,e2]))) (SrcL ts [s1,s2]) =
  if assertCxt' s e then SrcOk (SrcL ts [s1,s2])
  else SrcL ts [vAsu s e1 s1, vArt (assumeCxt' e1 s) e2 s2]

vArt s (e@(App (C Or) (T[e1,e2]))) (SrcL ts [s1,s2]) =
  if assertCxt' s e then SrcOk (SrcL ts [s1,s2])
  else SrcL ts [vAsu s e1 s1, vArt s e2 s2]

vArt s (App (C Iff) (T[e1,e2])) (SrcL ts [s1,s2]) =  SrcL ts [vArt (assumeCxt' e2 s) e1 s1, vArt (assumeCxt' e1 s) e2 s2]
vArt s (App (C And) (T[e1,e2])) (SrcL ts [s1,s2]) = SrcL ts [vArt s e1 s1, vArt (assumeCxt' e1 s) e2 s2]

vArt s e src =
  if assertCxt' s e then SrcStat (statCxt s) $ SrcOk src
  else SrcStat (statCxt s) $ SrcErr src (ErrVer "") 

-- eof
