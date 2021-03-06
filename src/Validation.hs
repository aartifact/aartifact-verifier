----------------------------------------------------------------
--
-- | aartifact
--   http://www.aartifact.org/
--
-- @src\/Validate.hs@
--
--   Functions for turning a list of statements (a source
--   document) into an output representing its validation
--   status.
--

----------------------------------------------------------------
--

module Validation (rawCxt, validate, validateBasic) where

import IOPrintFormat
import IOSource
import ExpConst (Const(..))
import Exp
import Context
import ValidationComp (Verification(..))
import ValidationSearch (verify)

----------------------------------------------------------------
-- | Process a list of statements while maintaining a context,
--   and validate expressions with respect to this context.

validate :: Context -> [Stmt] -> ([Stmt], Stat)
validate cxtraw ss = (\(ss,(_,_,_,st))->(ss,st)) $ execs cxtraw ss
validateBasic cxtraw ss = (\(ss,(_,_,_,st))->(ss,st)) $ execs (setBasic cxtraw) ss
rawCxt stmts = state0 $ concat $ map (\x->case x of ExpStmt _ (e,_)->[e];_->[]) stmts

exec :: Context -> Stmt -> ([Stmt], Context)
exec state (s@(Text _)) = ([s], state)
exec state (s@(SyntaxError _)) = ([s], state)
exec state (Intro src Variable vs) = ([Intro (SrcOk src) Variable vs], updVars vs state)
exec state (Intro src ty vs) = ([Intro (SrcOk src) ty vs], updConsts vs state)
exec state (ExpStmt Assert (e,src)) = ([ExpStmt Assert (e',src')], state'')
  where state'' = updStat stat' $ if isErr src' then considerCxt e' state' else assumeCxt e' state'
        stat' = statSrc src'
        src' = vArt state' e' src
        (e',state') = freshExpVars (normOps e) state
exec state (ExpStmt Assume (e,src)) = ([ExpStmt Assume (e',src')], state'')
  where state'' = if isErr src' then considerCxt e' state' else assumeCxt e' state'
        src' = vAsu state' e' src
        (e',state') = freshExpVars (normOps e) state
exec state (ExpStmt Consider (e,src)) = ([ExpStmt Consider (e',src')], state'')
  where state'' = if isErr src' then state' else addLawCxt state' e
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
-- | Analysis and verification of expressions with feedback in
--   the form of source annotations/tags.

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
vArt s (Forall vs (App (C Imp) (T[e1,e2]))) (SrcL ts [s1,s2]) =
  SrcL ts [vAsu (updVars vs s) e1 s1, vArt (assumeCxt e1 (updVars vs s)) e2 s2]
--vArt s (Exists vs (App (C And) (T[e1,e2]))) (SrcL ts [s1,s2]) = 
--  SrcL ts [vArt (updVars vs s) e1 s1, vArt (assumeCxt e1 (updVars vs s)) e2 s2]
vArt s (App (C And) (T[e1,e2])) (SrcL ts [s1,s2]) = SrcL ts [vArt s e1 s1, vArt (assumeCxt e1 s) e2 s2]
--vArt s (App (C Or)  (T[e1,e2])) (SrcL ts [s1,s2]) = SrcL ts [vArt s e1 s1, vArt s e2 s2]
vArt s (App (C Imp) (T[e1,e2])) (SrcL ts [s1,s2]) = SrcL ts [vAsu s e1 s1, vArt (assumeCxt e1 s) e2 s2]
vArt s (App (C Iff) (T[e1,e2])) (SrcL ts [s1,s2]) = SrcL ts [vArt (assumeCxt e2 s) e1 s1, vArt (assumeCxt e1 s) e2 s2]
vArt s (App (C Not) e) (SrcL ts [src]) = SrcL ts [vArt s e src]
vArt s (App (C MakeReport) (T es)) src = SrcReport (reportCxt es (considerCxt (T es) s)) src
vArt s e src = 
  let fvs = fv (varsCxt s) e
  in if length fvs > 0 then SrcErr src (ErrUnbound (map fst fvs)) else
     case verify_or_contra s e of
       Verifiable Contradiction -> SrcStat (statCxt s) $ SrcErr src (ErrContra)
       Verifiable (B True)      -> SrcStat (statCxt s) $ SrcOk src --([R str $ Verifiable s (B True)], assumeCxt e state')
       r                        -> SrcStat (statCxt s) $ SrcErr src (ErrVer "") --([R (str) r], state')

verify_or_contra s e =
  case verify (assumeCxt e s) (C Contradiction) of
    Verifiable (B True) -> Verifiable Contradiction
    _                   -> verify s e

-- ++":"++(show (evalExp state e)) -- ++ show (getR state)
-- eof