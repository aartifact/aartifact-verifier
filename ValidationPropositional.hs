----------------------------------------------------------------
--
-- aartifact
-- http://www.aartifact.org/src/
-- Copyright (C) 2008-2011
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

module ValidationPropositional (validatePropositional) where

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
-- Process a list of statements while maintaining a context,
-- and validate expressions with respect to this context.

validatePropositional :: Context -> [Stmt] -> ([Stmt], Stat)
validatePropositional ont ss = (\(ss,(_,_,_,st))->(ss,st)) $ execs ont ss

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

assertCxt' s e = assertCxt s e || assertCxt s (App (C (NLPredLC [Nothing,Just "is",Just "true"])) (T[e]))
assumeCxt' e s = assumeCxt (App (C (NLPredLC [Nothing,Just "is",Just "true"])) (T[e])) s --(assumeCxt e s) 

vAsu :: Context -> Exp -> Src -> Src
vAsu s e (SrcIg [l,src,r]) = SrcIg [l,vAsu s e src,r]
vAsu s (App (C (NLPredC _)) (T [])) src = SrcOk src
vAsu s (App (C (NLPredLC _)) (T [])) src = SrcOk src
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
