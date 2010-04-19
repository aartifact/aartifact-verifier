----------------------------------------------------------------
--
-- aartifact
-- http://www.aartifact.org/src/
-- Copyright (C) 2008-2010
-- A. Lapets
--
-- This software is made available under the GNU GPLv3.
--
-- ValidationSyntaxVars.hs
--   Functions for turning a list of statements (a source
--   document) into an output representing its validation
--   status in terms of syntax and bound variables.

----------------------------------------------------------------
-- 

module ValidationSyntaxVars (validateSyntaxVars) where

import IOPrintFormat
import IOSource
import ExpConst (Const(..))
import Exp
import Context
import ValidationComp (Verification(..))

----------------------------------------------------------------
-- Process a list of statements while maintaining a context,
-- and validate expressions with respect to this context.

validateSyntaxVars :: [Stmt] -> ([Stmt], Stat)
validateSyntaxVars ss = (\(ss,(_,_,st))->(ss,st)) $ execs (state0 []) ss

exec :: Context -> Stmt -> ([Stmt], Context)
exec state (s@(Text _)) = ([s], state)
exec state (s@(SyntaxError _)) = ([s], state)
exec state (s@(Intro _ Variable vs)) = ([s], updVars vs state)
exec state (s@(Intro srcStr _ vs)) = ([s], updConsts vs state)
exec state (ExpStmt Assert (e,src)) = ([ExpStmt Assert (e',src')], state'')
  where state'' = updStat stat' state'
        stat' = statSrc src'
        src' = vArt state' e' src
        (e',state') = freshExpVars (normOps e) state
exec state (ExpStmt si (e,src)) = ([ExpStmt si (e',src')], state'')
  where state'' = state'
        src' = vAsu state' e' src
        (e',state') = freshExpVars (normOps e) state
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
vAsu s (Forall vs (App (C Imp) (T[e1,e2]))) (SrcL ts [s1,s2]) = SrcL ts [vAsu (updVars vs s) e1 s1, vAsu (updVars vs s) e2 s2]
vAsu s (Exists vs (App (C And) (T[e1,e2]))) (SrcL ts [s1,s2]) = SrcL ts [vAsu (updVars vs s) e1 s1, vAsu (updVars vs s) e2 s2]
vAsu s (Bind Considering vs (T[e1,e2])) (SrcL ts [s1,s2]) = SrcL ts [vAsu (updVars vs s) e1 s1, vAsu (updVars vs s) e2 s2]
vAsu s (App (C Not) e) (SrcL ts [src]) = SrcL ts [vAsu s e src]
vAsu s (App (C And) (T[e1,e2])) (SrcL ts [s1,s2]) = SrcL ts [vAsu s e1 s1, vAsu s e2 s2]
vAsu s (App (C Or)  (T[e1,e2])) (SrcL ts [s1,s2]) = SrcL ts [vAsu s e1 s1, vAsu s e2 s2]
vAsu s (App (C Imp) (T[e1,e2])) (SrcL ts [s1,s2]) = SrcL ts [vAsu s e1 s1, vAsu s e2 s2]
vAsu s (App (C Iff) (T[e1,e2])) (SrcL ts [s1,s2]) = SrcL ts [vAsu s e1 s1, vAsu s e2 s2]
vAsu s e src = if length fvs == 0 then SrcOk src else SrcErr src (ErrUnbound (map fst fvs))
  where fvs = fv (varsCxt s) e

vArt :: Context -> Exp -> Src -> Src
vArt s e (SrcIg [l,src,r]) = SrcIg [l,vArt s e src,r]
vArt s (Forall vs (App (C Imp) (T[e1,e2]))) (SrcL ts [s1,s2]) = SrcL ts [vAsu (updVars vs s) e1 s1, vArt (updVars vs s) e2 s2]
vArt s (Exists vs (App (C And) (T[e1,e2]))) (SrcL ts [s1,s2]) = SrcL ts [vArt (updVars vs s) e1 s1, vArt (updVars vs s) e2 s2]
vArt s (App (C And) (T[e1,e2])) (SrcL ts [s1,s2]) = SrcL ts [vArt s e1 s1, vArt s e2 s2]
vArt s (App (C Or)  (T[e1,e2])) (SrcL ts [s1,s2]) = SrcL ts [vArt s e1 s1, vArt s e2 s2]
vArt s (App (C Imp) (T[e1,e2])) (SrcL ts [s1,s2]) = SrcL ts [vAsu s e1 s1, vArt s e2 s2]
vArt s (App (C Iff) (T[e1,e2])) (SrcL ts [s1,s2]) = SrcL ts [vArt s e1 s1, vArt s e2 s2]
vArt s (App (C Not) e) (SrcL ts [src]) = SrcL ts [vArt s e src]
vArt s e src = 
  let fvs = fv (varsCxt s) e
  in if length fvs > 0 then SrcErr src (ErrUnbound (map fst fvs)) else SrcStat (statCxt s) $ SrcOk src 

-- eof
