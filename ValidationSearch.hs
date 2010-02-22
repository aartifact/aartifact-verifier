----------------------------------------------------------------
--
-- aartifact
-- http://www.aartifact.org/src/
-- Copyright (C) 2008-2010
-- A. Lapets
--
-- This software is made available under the GNU GPLv3.

-- ValidationSearch.hs
--   Functions for making and verifiyig logical inferences
--   using the logical syntax defined in the module "Exp".

----------------------------------------------------------------
-- 

module ValidationSearch (verify) where

import Data.Maybe (catMaybes)

import Set
import ExpConst (Const(..))
import Exp
import ExpSubst
import Context
import ContextEval
import ValidationComp

----------------------------------------------------------------
-- Top-level verification based on basic inference rules that
-- govern the two quantifiers and five logical operators.

verify s e = r$r$r$vfy s e where
  r (Potential vf) = vf ()
  r v = v

vfy :: Context -> Exp -> Verification
vfy s e =
 let srch0 ow = case ow of Unknown->chkC s e $ srchv s e; _->ow
     chkC s e ow = case srchContext s e ||| srchNot s e ||| srchContra s e of
       Verifiable (B b) -> Verifiable (B b)
       _ -> ow
 in case e of
  App (C And) (T[e1,e2]) -> vfy s e1 &&& vfy (assumeCxt e1 s) e2
  App (C Or)  (T[e1,e2]) -> srch0 $ vfy s e1 ||| vfy s e2
  App (C Imp) (T[e1,e2]) -> srch0 $ notV (vfy s e1) ||| vfy (assumeCxt e1 s) e2
  App (C Iff) (T[e1,e2]) -> srch0 $ vfy (assumeCxt e1 s) e2 &&& vfy (assumeCxt e2 s) e1
  App (C Not) e0         -> srch0 $ notV (vfy s e0)

  App (C FalToUnknown) e -> isVTrue' $ vfy s e
  App (C SearchIff) (T[e',e]) -> if isVTrue $ vfy s e then vfy s e' else Unknown

  Forall ns e0 -> srch0 $ vfy (updVars ns s) e0         --vfyQ s e0 andV |||
  Exists ns e0 -> 
    if (resetVar e) `elem` trueExpsCxt s then Verifiable (B True) else srch0 $ (srchv s e ||| vfyExists s e) --vfyQ s e0 orV' |||
  
  -- ??
  
  _ ->
   let s' = considerCxt e s
       fff Unknown = if eqCxt s' e (C(B False)) then Verifiable (B False) else Unknown
       fff ow = ow
   in    if eqCxt s' e (C(B True)) then Verifiable (B True)
    else 
     fff $ (
         (chkC s' e) $
         srchv s' e
     ||| boolToV (assertCxt s' e)
     ||| boolToV (or [eqCxt s' a e | a<-trueExpsCxt s'])
     )



----------------------------------------------------------------
-- Take a list of expressions sharing free variables, and tries to
-- find a collection of assumptions (and corresponding substitution)
-- that form an instantiation of these expressions. Only uses portions
-- of an expression not of the form "e1 \in e2"; checks these last,
-- but only if all variables within them have already been resolved.

vfyExists s (Exists ns e) =
  let (ins, es) = splitInExps e
      as = trueExpsCxt (updVars ns s)
      inst s (e:es) = try es $ catMaybes $ map (unify s) $ catMaybes $ map (match ns e) as
      inst s [] = Just s -- all expressions matched
      orMaybe x x' = maybe x' Just x
      try es (s:matches) = inst s (map (subst s) es) `orMaybe` try es matches 
      try es [] = Nothing
  in case inst emptySubst es of
    Nothing -> Unknown
    Just sub ->
      case ins of
        [] -> Verifiable (B True)
        _ -> let e' = listAnd $ map (subst sub) ins
             in (boolToV $ fv (varsCxt s) e' == []) &&& vfy s e'

----------------------------------------------------------------
-- 

srchContext s e = boolToV $ e `elem` trueExpsCxt s

srchNot s e = Potential $ \() -> orV $ concat [map (vfy s) $ chk e a | a<-as] where
  as = trueExpsCxt s
  chk e (App (C Not) e') = map (App (C Not)) $ chk e e'
  chk e e'               = if e==e' then [C$B$True] else []

srchContra s e = Potential $ \() -> orV $ concat [map (vfy s) $ contraPair e a a' | a<-as, a'<-as] where
  as = trueExpsCxt s
  contraPair e (App (C Imp) (T[e1,e2])) (App (C Imp) (T[e1', App (C Not) e2'])) = 
    if e==e1 && e1==e1' && e2==e2' then [C$B$False] else []
  contraPair _ _ _ = []

-- Check whether some combination of assumptions implies the formula in
-- question. It is capable of handling assumptions that contain an
-- arbitrarily long sequence of alternating "for all"/"implies" expressions.

srchv s e = Potential 
  (\()-> orV $ map (vfy s) $ concat [search [] [] e a | a<-trueExpsCxt s])

-- Check that substitution actually captures all variables?

search :: [Name] -> [(Exp,Subst->Subst)] -> Exp -> Exp -> [Exp]
search ns gs e (App (C And) (T[e1,e2])) = search ns gs e e1 ++ search ns gs e e2
search [] gs e (App (C Or)  (T[e1,e2])) = 
    map (App (C FalToUnknown)) $ 
      [bOp And (listAnd [e | (e,_)<-gs]) (bOp And (bOp Imp e1 e) (bOp Imp e2 e))]
search ns gs (e@(Exists _ _)) (e'@(App (C Iff) (T[e1,e2]))) = 
    search ns gs e (bOp Imp e1 e2) ++ search ns gs e (bOp Imp e2 e1)
search ns gs e (App (C Iff) (T[e1,e2])) =
  let l1 = (case match ns e2 e of
               Nothing -> []
               Just sub -> 
                 if not $ ns `subset` boundInSubst sub then [] else 
                   [bOp SearchIff (subst sub e1) (listAnd [subst (subf sub) e | (e,subf)<-gs])])
        ++
           (case match ns e1 e of
               Nothing -> []
               Just sub -> 
                 if not $ ns `subset` boundInSubst sub then [] else 
                   [bOp SearchIff (subst sub e2) (listAnd [subst (subf sub) e | (e,subf)<-gs])])
  in if length l1 > 0 then l1 else search ns gs e (bOp Imp e1 e2) ++ search ns gs e (bOp Imp e2 e1)

search ns gs e (App (C Imp) (T[e1,e2])) = search ns ((e1,\s->s):gs) e e2
search ns gs e (Forall ns' e') = search (ns \/ ns') (map (\(e,s) -> (e,(limitSubst ns).s)) gs) e e'
search ns gs e e' = map (App (C FalToUnknown)) $ searchBase ns gs e e'

searchBase ns gs (Exists ns'' e'') (Exists ns' e') =
 if ns == [] then
   if length ns' /= length ns'' then [] else
     let e00'' = Forall ns'' $ bOp Imp (subst (zip ns' (map Var ns'')) e') e''
     in [bOp And e00'' (listAnd [subst (subf []) e | (e,subf)<-gs])]
 else
  if length ns' /= length ns'' then [] else
   let es' = splitAnd (subst (zip ns' (map Var ns'')) e')
       es'' = splitAnd e''
       (e0',e0'') = unzip (zip es' es'')
   in case match ns (Exists ns'' (listAnd e0')) (Exists ns'' (listAnd e0'')) of
       Nothing -> []
       Just sub -> 
         if not $ ns `subset` boundInSubst sub then [] else
           let contextEs = listAnd [subst (subf sub) e | (e,subf)<-gs]
           in 
            if length es'' <= length es' then
              [contextEs]
            else
              [bOp And (Forall ns'' (bOp Imp (listAnd e0'') (listAnd (drop (length es') es'')))) contextEs]

searchBase ns gs e e' = case match ns e' e of
  Nothing -> []
  Just s ->
    if not $ ns `subset` boundInSubst s then
      [Exists (ns `diff` boundInSubst s) $ listAnd [subst (subf s) e | (e,subf)<-gs]] 
    else
      [listAnd [subst (subf s) e | (e,subf)<-gs]]

--eof
