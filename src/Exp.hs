----------------------------------------------------------------
--
-- | aartifact
--   http://www.aartifact.org/
--
-- @src\/Exp.hs@
--
--   Representation of arithmetic and logical expressions.
--

----------------------------------------------------------------
--

module Exp where

import Data.Maybe (catMaybes)
import Data.List (partition, sort, sortBy)

import Set
import ExpConst

----------------------------------------------------------------
-- | Variable names consist of the user-defined string, and an
--   integer identifier unique to each binding.

type Name = (String, Integer)
data Exp =
    C Const
  | Var Name
  | App Exp Exp
  | T [Exp]
  | Forall [Name] Exp
  | Exists [Name] Exp
  | Bind Const [Name] Exp
    deriving (Show, Eq, Ord)

----------------------------------------------------------------
-- | Convenient constructors to be used in parsers and
--   elsewhere.

bOp op e1 e2 =  App (C op) (T [e1,e2])
listAnd es = if es==[] then C$B True else foldr (bOp And) (last es) (init es)

mkRoot e1 e2 = bOp Pow e2 (bOp Div (C (N 1)) e1)
mkTup es = if length es == 1 then head es else T es
mkVect e = case e of T es -> T es; _ -> T [e]
mkProd es = if length es == 1 then head es else App (C Cart) (T es)
mkNLPred pc ews = App (C $ pc $ map str ews) (T args)
 where str = either (\_->Nothing) Just
       exp = either Just (\_->Nothing)
       args = catMaybes $ map exp ews

mkSetComp e1 e2 = Bind SetComp (catMaybes $ map getVS ins) $ T[e1,e2]
  where (ins, rest) = splitInExps e2
        getVS (App (C In) (T[Var n, e2])) = Just n
        getVS _ = Nothing

mkBrack0 b1 b2 e = App (C $ Brack b1 b2) e
mkBrack Round Round e = e
mkBrack b1 b2 e = App (C $ Brack b1 b2) e

mkInterval (App (C (Brack Square Square)) e) = App (C IntervalCC) e
mkInterval (App (C (Brack Round Square)) e) = App (C IntervalOC) e
mkInterval (App (C (Brack Square Round)) e) = App (C IntervalCO) e
mkInterval e = App (C IntervalOO) e

----------------------------------------------------------------
-- | Map and specialized search functions on expressions.

mapExp :: (Exp -> Exp) -> Exp -> Exp
mapExp f e = f (mpe f e)

mapExpPre :: (Exp -> Exp) -> Exp -> Exp
mapExpPre f e = mpe f (f e)

mpe :: (Exp -> Exp) -> Exp -> Exp
mpe f e = case e of
  C op -> C op
  Var n -> Var n
  App e1 e2 -> App (mapExp f e1) (mapExp f e2)
  T es -> T (map (mapExp f) es)
  Forall ns e -> Forall ns (mapExp f e)
  Exists ns e -> Exists ns (mapExp f e)
  Bind c ns e -> Bind c ns (mapExp f e)

----------------------------------------------------------------
-- | Aggregation of all distinct subexpressions. Subexpressions
--   occur after expressions that contain them. Subexpressions
--   under quantifiers or variable bind points are not included.

subs :: Exp -> [Exp]
subs e = case e of
  App e1 e2 -> e:(subs e1 ++ subs e2)
  T es -> e:(concat $ map subs es)
  Forall _ e0 -> [e] --e:(subs e0)
  Exists _ e0 -> [e] --e:(subs e0)
  Bind _ _ e0 -> [e] --e:(subs e0)
  _ -> [e] --var or const

consts :: Exp -> [Const]
consts e = let cs = consts in case e of
  App e1 e2 -> cs e1++cs e2
  T es -> concat $ map cs es
  Forall _ e0 -> cs e0
  Exists _ e0 -> cs e0
  Bind c _ e0 -> c:cs e0
  C c -> [c]
  _ -> [] --var

----------------------------------------------------------------
-- | Equality on expressions, open form (non-recursive).

eqOpen :: (Exp -> Exp -> Bool) -> Exp -> Exp -> Bool
eqOpen eq (C c)         (C c')           = c == c'
eqOpen eq (Var n)       (Var n')         = n == n'
eqOpen eq (App e1 e2)   (App e1' e2')    = eqOpens eq [e1,e2] [e1',e2']
eqOpen eq (T es)        (T es')          = eqOpens eq es es'
eqOpen eq (Forall ns e) (Forall ns' e')  = (ns `eql` ns') && (e `eq` e')
eqOpen eq (Exists ns e) (Exists ns' e')  = (ns `eql` ns') && (e `eq` e')
eqOpen eq (Bind c ns e) (Bind c' ns' e') = c == c' && (ns `eql` ns') && eq e e'
eqOpen eq _             _                = False

eqOpens :: (Exp -> Exp -> Bool) -> [Exp] -> [Exp] -> Bool
eqOpens eq (e:es) (e':es') = e `eq` e' && eqOpens eq es es'
eqOpens eq []     []       = True
eqOpens eq _      _        = False

----------------------------------------------------------------
-- | Free variable determination.

fv :: [Name] -> Exp -> [Name]
fv bound e = case e of
  C op -> []
  Var n -> [n] `diff` bound
  App e1 e2 -> foldl (\/) [] $ map (fv bound) [e1,e2]
  T es -> foldl (\/) [] $ map (fv bound) es
  Forall ns e -> fv (bound \/ ns) e
  Exists ns e -> fv (bound \/ ns) e
  Bind c ns e -> fv (bound \/ ns) e

----------------------------------------------------------------
-- | Generation of unique variable names.

updName :: Name -> Integer -> Name
updName (s,i) i' = (s,i')

uv :: [(Name,Integer)] -> Integer -> Exp -> (Exp, Integer)
uv fvs c (C op)  = (C op, c)
uv fvs c (Var n) = case lookup n fvs of
  Nothing -> (Var n, c)
  Just i' -> (Var $ updName n i', c)
uv fvs c (App e1 e2) = (App e1' e2', c')
  where ([e1',e2'], c') = uvs fvs c [e1,e2]
uv fvs c (T es) = (T es', c') where (es', c') = uvs fvs c es
uv fvs c (Forall ns e) = uvq fvs c Forall ns e
uv fvs c (Exists ns e) = uvq fvs c Exists ns e
uv fvs c (Bind o ns e) = uvq fvs c (Bind o) ns e

uvs fvs c [] = ([],c)
uvs fvs c (e:es) = (e':es',c'') where
  (e',c') = uv fvs c e
  (es',c'') = uvs fvs c' es

uvq fvs c q ns e = (q ns' e', c'') where
  c' = c + (toInteger $ length ns)
  fvs' = zip ns [c..c']
  (e',c'') = uv (fvs'++fvs) c' e
  ns' = map (\(v,n) -> updName v n) fvs'

----------------------------------------------------------------
-- | Common decomposition operations for expressions.

splitAnd :: Exp -> [Exp]
splitAnd (App (C And) (T [e1,e2])) = splitAnd e1 ++ splitAnd e2
splitAnd e                         = [e]

splitInExps :: Exp -> ([Exp], [Exp])
splitInExps (e@(App (C Imp) (T [e1,e2]))) =
  let (es,rest) = partition expIn $ splitAnd e1
  in if length rest > 0 then (es, [App (C Imp) (T [listAnd rest,e2])])
     else (es, [e2])
splitInExps e = partition expIn $ splitAnd e

splitInExps' (e@(App (C Imp) (T [e1,e2]))) =
  let (es,rest) = partition expIn $ splitAnd e1
  in if length rest > 0 then (es, [App (C Imp) (T [listAnd rest,e2])])
     else (es, [e2])
splitInExps' e = partition expIn $ splitAnd e

expIn (App (C In) e) = True
expIn _              = False

isTrue (C (B True)) = True
isTrue _ = False
isFalse (C (B False)) = True
isFalse _ = False

cLTEeSort :: [Exp] -> [Exp]
cLTEeSort = sortBy f where
  f (C c) _ = LT
  f _ _ = GT

normOps = mapExp (\e->e)

mkQ q o vs e = q (map fst vs) $ bOp o (listAnd $ concat $ map each vs) e
  where each (n, Just t) = [bOp In (Var n) t]
        each (n, Nothing) = []

--eof