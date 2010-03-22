----------------------------------------------------------------
--
-- aartifact
-- http://www.aartifact.org/src/
-- Copyright (C) 2008-2010
-- A. Lapets
--
-- This software is made available under the GNU GPLv3.
--
-- ExpSubst.hs
--   Capture-avoiding substitution on expressions.

----------------------------------------------------------------
-- 

module ExpSubst (Subst, emptySubst, match, exmch, subst, unify,
                   boundInSubst, limitSubst, resetVar) where

import Set
import ExpConst
import Exp

type Subst = [(Name, Exp)]

emptySubst :: Subst
emptySubst = []

boundInSubst :: Subst -> [Name]
boundInSubst s = map fst s

limitSubst :: [Name] -> Subst -> Subst
limitSubst ns = filter $ \(n,_) -> n `elem` ns

----------------------------------------------------------------
-- Capture-avoiding substitution.
--
-- The maximum variable index of the replacement expressions 
-- is computed, and the target expression's variable indices
-- are incremented so that all variables are unique with
-- respect to each other. This update takes linear time in the
-- size of all the expressions involved in a substitution.

subst :: Subst -> Exp -> Exp
subst  s  e = subst' s (incVar [] (foldr max 0 (map (maxVar.snd) s)) e)
subst' [] e = e
subst' s  e = case e of
  C op        -> C op
  Var x       -> maybe (Var x) id $ lookup x s
  Forall ns e -> Forall ns $ subst' [(n,e) | (n,e)<-s, not $ n `elem` ns] e
  Exists ns e -> Exists ns $ subst' [(n,e) | (n,e)<-s, not $ n `elem` ns] e
  Bind c ns e -> Bind c ns $ subst' [(n,e) | (n,e)<-s, not $ n `elem` ns] e
  App e1 e2   -> App (subst' s e1) (subst' s e2)
  T es        -> T $ map (subst' s) es

maxVar :: Exp -> Integer
maxVar e = case e of
  C _         -> -1
  Var (_,i)   -> i
  Forall ns e -> foldr max (maxVar e) (map snd ns)
  Exists ns e -> foldr max (maxVar e) (map snd ns)
  Bind c ns e -> foldr max (maxVar e) (map snd ns)
  App e1 e2   -> max (maxVar e1) (maxVar e2)
  T es        -> foldr max (-1) (map maxVar es)

incVar :: [String] -> Integer -> Exp -> Exp
incVar vs j e = 
  let incVars c vs j ns e = c (map (\(v,i)->(v,i+j)) ns) (incVar (vs \/ map fst ns) j e)
  in case e of
  C op        -> C op
  Var (n,i)   -> Var $ if n `elem` vs then (n,i+j) else (n,i)
  Forall ns e -> incVars Forall vs j ns e
  Exists ns e -> incVars Exists vs j ns e
  Bind c ns e -> incVars (Bind c) vs j ns e
  App e1 e2   -> App (incVar vs j e1) (incVar vs j e2)
  T es        -> T $ map (incVar vs j) es

resetVar :: Exp -> Exp
resetVar e = pr [] 0 e where
 prns ns j = [("#",toInteger $ j)|j<-[j..j+length ns-1]]
 pre ns vs j e =  pr ((zip ns [j..j+length ns-1])++vs) (j+length ns) e
 pr vs j e = case e of
  C op        -> C op
  Var (n,i)   -> maybe e (\j->Var ("#",toInteger $ j)) $ lookup (n,i) vs
  Forall ns e -> Forall (prns ns j) $ pre ns vs j e
  Exists ns e -> Exists (prns ns j) $ pre ns vs j e
  Bind c ns e -> Bind c (prns ns j) $ pre ns vs j e
  App e1 e2   -> App (pr vs j e1) (pr vs j e2)
  T es        -> T $ map (pr vs j) es

unify :: Subst -> Subst -> Maybe Subst
unify (ne:s1) s2 = case unify s1 s2 of
  Nothing  -> Nothing
  Just s2' -> if consistent s2 ne then Just (ne:s2') else Nothing
unify [] s2 = Just s2

unifyMaybe (Just s1) (Just s2) = unify s1 s2
unifyMaybe _         _         = Nothing

consistent :: Subst -> (Name, Exp) -> Bool
consistent s (n,e) = and [e==e' | (n',e')<-s, n'==n]

----------------------------------------------------------------
-- Basic matching algorithm.

match :: [Name] -> Exp -> Exp -> Maybe Subst
match ns e1 e2 = match' [] ns e1 e2
match' ps ns (C op)        (C op')          = if op == op' then Just emptySubst else Nothing
match' ps ns (Forall xs e) (Forall xs' e')  = matchq' ps ns xs e xs' e'
match' ps ns (Exists xs e) (Exists xs' e')  = matchq' ps ns xs e xs' e'
match' ps ns (Bind c xs e) (Bind c' xs' e') = if c==c' then matchq' ps ns xs e xs' e' else Nothing
match' ps ns (App e1 e2)   (App e1' e2')    = matchs' ps ns [e1,e2] [e1',e2']
match' ps ns (T es)        (T es')          = matchs' ps ns es es'
match' ps ns (T es)        (C (TC cs))      = matchs' ps ns es (map C cs)
match' ps ns (Var x)       (Var x')         = if (x==x' && not (x `elem` ns)) || ((x,x') `elem` ps) then Just emptySubst
                                              else if (x `elem` ns) then Just [(x, Var x')] else Nothing
match' ps ns (Var x)       e2               = if Var x == e2 && not (x `elem` ns) then Just emptySubst
                                              else if (x `elem` ns) then Just [(x, e2)] else Nothing
match' ps ns _             _                = Nothing

matchq' ps ns xs e xs' e' =
  let ps' = [(x,x') | (x,x')<-ps, not (x `elem` xs || x' `elem` xs')]
  in if xs `eql` xs' then
       match' ps' (ns `diff` xs) e e'
     else if length xs == length xs' then 
       match' (ps'++(zip xs xs')) ((ns `diff` xs) `diff` xs') e e'
     else Nothing

matchs' ps ns es es' =
  if length es == length es' then
    foldl unifyMaybe (Just []) (map (uncurry $ match' ps ns) (zip es es'))
  else
    Nothing

----------------------------------------------------------------
-- Extended matching algorithm (matches last entries of a
-- conjunction, variations on quantifiers.

exmch :: [Name] -> Exp -> Exp -> Maybe Subst
exmch ns e1 e2 = exmch' [] ns e1 e2
exmch' ps ns (C op)        (C op')          = if op == op' then Just emptySubst else Nothing

exmch' ps ns (Forall xs (App (C Imp) (T[C (B True), e]))) (Forall xs' (App (C Imp) (T[C (B True), e'])))  = exmchq' ps ns xs e xs' e'
exmch' ps ns (Forall xs (e00@(App (C Imp) (T[e0, e])))) (Forall xs' (App (C Imp) (T[C (B True), e'])))  = exmch' ps ns (Forall xs e00) (Forall xs' e')
exmch' ps ns (Forall xs (App (C Imp) (T[C (B True), e]))) (Forall xs' (e00'@(App (C Imp) (T[e0', e']))))  = exmch' ps ns (Forall xs e) (Forall xs' e00')

exmch' ps ns (Forall xs e) (Forall xs' e')  = exmchq' ps ns xs e xs' e'

exmch' ps ns (Exists xs (App (C And) (T[C (B True), e]))) (Exists xs' (App (C And) (T[C (B True), e'])))  = exmchq' ps ns xs e xs' e'
exmch' ps ns (Exists xs (e00@(App (C And) (T[e0, e])))) (Exists xs' (App (C And) (T[C (B True), e'])))  = exmch' ps ns (Exists xs e00) (Exists xs' e')
exmch' ps ns (Exists xs (App (C And) (T[C (B True), e]))) (Exists xs' (e00'@(App (C And) (T[e0', e']))))  = exmch' ps ns (Exists xs e) (Exists xs' e00')

exmch' ps ns (Exists xs e) (Exists xs' e')  = exmchq' ps ns xs e xs' e'
exmch' ps ns (Bind c xs e) (Bind c' xs' e') = if c==c' then exmchq' ps ns xs e xs' e' else Nothing

--exmch' ps ns (App AppVar _) _  = Nothing
--exmch' ps ns _ (App AppVar _)  = Nothing
exmch' ps ns (App e1 e2)   (App e1' e2')    = exmchs' ps ns [e1,e2] [e1',e2']
exmch' ps ns (T es)        (T es')          = exmchs' ps ns es es'
exmch' ps ns (T es)        (C (TC cs))      = exmchs' ps ns es (map C cs)
exmch' ps ns (Var x)       (Var x')         = if (x==x' && not (x `elem` ns)) || ((x,x') `elem` ps) then Just emptySubst
                                              else if (x `elem` ns) then Just [(x, Var x')] else Nothing
exmch' ps ns (Var x)       e2               = if Var x == e2 && not (x `elem` ns) then Just emptySubst
                                              else if (x `elem` ns) then Just [(x, e2)] else Nothing
exmch' ps ns _             _                = Nothing

exmchq' ps ns xs e xs' e' =
  let ps' = [(x,x') | (x,x')<-ps, not (x `elem` xs || x' `elem` xs')]
  in if xs `eql` xs' then
       exmch' ps' (ns `diff` xs) e e'
     else if length xs == length xs' then
       exmch' (ps'++(zip xs xs')) ((ns `diff` xs) `diff` xs') e e'
     else Nothing

exmchs' ps ns es es' =
  if length es == length es' then
    foldl unifyMaybe (Just []) (map (uncurry $ exmch' ps ns) (zip es es'))
  else
    Nothing

--eof
