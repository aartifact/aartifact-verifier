----------------------------------------------------------------
--
-- | aartifact
--   http://www.aartifact.org/
--
-- @src\/ContextEval.hs@
--
--   Simple evaluation rules (i.e. a calculator) for simple
--   expressions consisting mostly of constants.
--   Meta-propositions about the literal structure of
--   expressions.
--

----------------------------------------------------------------
--

module ContextEval (considEval, considLit) where

import Ratio
import Data.Maybe (catMaybes)

import Set
import ExpConst (Const (..), Bracket (..))
import Exp
import ExpSubst
import ContextRelations

----------------------------------------------------------------
-- | Context contribution: evaluate an expression and add it to
--   the context.

considEval e rs = maybe rs (updRelsEq rs e) $ evalConst e

----------------------------------------------------------------
-- | Predicates that automatically apply to constants.

considLit e rs = case e of
  C (N i) ->
    if denominator i == 1 && numerator i >= 0 then
      updRels rs (bOp In e (C (SetN)))
    else if denominator i == 1 then
      updRels rs (bOp In e (C (SetZ)))
    else 
      updRels rs (bOp In e (C (SetQ)))
  _ -> rs

----------------------------------------------------------------
-- | Synonyms for functions to manipulate rationals.

dnom = denominator
nume = numerator

rat :: Num a => Integer -> a
rat n = fromInteger n

int :: Rational -> Bool
int r = dnom r == 1

----------------------------------------------------------------
-- | Defined evaluation of constants.

evalConst :: Exp -> Maybe Exp
evalConst e = case mapExp evC e of C c-> Just (C c); _ -> Nothing
  where
    evC (e@(App (C c1) (C c2))) = eC e c1 c2
    evC (e@(T es)) = maybe e (\cs -> C $ TC cs) $ valueList es
    evC e = e

eC _ Neg   (N i) = C$N$ -1 * i
eC _ Floor (N x) = C$N$ rat $ nume x `div` dnom x
eC _ Ceil  (N x) = C$N$ rat $ 1 + (nume x `div` dnom x)
eC e Pow   (TC[N x,N y]) = if int y then C$N$ x^nume y else e
eC _ Mod   (TC[N x,N y]) = C$N$ rat ((nume x*dnom y) `mod` (nume y*dnom x)) / rat (dnom x*dnom y)
eC _ Times (TC[N x,N y]) = C$N$ x * y
eC e Div   (TC[N x,N y]) = if y==0 then e else C$N$ x / y
eC _ Plus  (TC[N x,N y]) = C$N$ x + y
eC _ Minus (TC[N x,N y]) = C$N$ x - y
eC _ Min   (TC[N x,N y]) = C$N$ min x y
eC _ Max   (TC[N x,N y]) = C$N$ max x y
eC _ Eql   (TC[N x,N y]) = C$B$ x == y
eC _ Eql   (TC[B x,B y]) = C$B$ x == y
eC _ Neq   (TC[N x,N y]) = C$B$ x /= y
eC _ Lt    (TC[N x,N y]) = C$B$ x < y
eC _ Lte   (TC[N x,N y]) = C$B$ x <= y
eC _ Gt    (TC[N x,N y]) = C$B$ x > y
eC _ Gte   (TC[N x,N y]) = C$B$ x >= y
eC _ Not   (B b)         = C$B$ not b
eC _ And   (TC[B x,B y]) = C$B$ x && y
eC _ Or    (TC[B x,B y]) = C$B$ x || y
eC e Not   (N n)         = if n `elem` [0,1] then C$N$ 1-n else e
eC e And   (TC[N x,N y]) = if [x,y] `subset` [0,1] then C$B$ (x,y) == (1,1) else e
eC e Or    (TC[N x,N y]) = if [x,y] `subset` [0,1] then C$B$ (x,y) /= (0,0) else e
eC _ Imp   (TC[B x,B y]) = C$B$ (not x) || y
eC _ Iff   (TC[B x,B y]) = C$B$ ((not x) || y) && ((not y) || x)
eC _ IfThenElse (TC [B b,c1,c2]) = if b then C c1 else C c2
eC _ (Brack Bar Bar) (N x) = C$ N$ abs x
eC _ (Brack Bar Bar) (Set s) = C$N$ toRational $ length s
eC _ (Brack Bar Bar) (TC cs) = C$N$ toRational $ length cs
eC e Min (Set cs) = if and (map isN cs) && length cs > 0 then let ns = getNs cs in C$N$foldr min (last ns) (init ns) else e
eC e Max (Set cs) = if and (map isN cs) && length cs > 0 then let ns = getNs cs in C$N$foldr max (last ns) (init ns) else e
eC _ In (TC[N x,SetN]) = C$B$ int x && x >= 0
eC _ In (TC[N x,SetZ]) = C$B$ int x
eC _ In (TC[N x,SetQ]) = C$B True
eC _ In (TC[N x,SetR]) = C$B True
eC _ In (TC[TC cs, Kleene as]) = C$B$ and [c `elt` as | c <- cs]
eC _ In (TC[c, Set s2]) = C$B$ c `elt` s2
eC _ Pow   (TC[Set s1,Ast]) = C$ Kleene s1
eC e Pow   (TC[Set s,N i]) =
  if not $ int i then e
  else if i == 0 then C$Set$[]
  else if i == 1 then C$Set$s
  else eC e Cart (TC (map Set $ take (fromInteger $ nume i) $ repeat s))
eC _ Union (TC[Set s1,Set s2]) = C$Set$ s1 \/ s2
eC _ Isect (TC[Set s1,Set s2]) = C$Set$ s1 /\ s2
eC _ Minus (TC[Set s1,Set s2]) = C$Set$ s1 `diff` s2
eC _ Subset   (TC[Set s1, Set s2]) = C$B$ s1 `subsetV` s2
eC _ Subseteq (TC[Set s1, Set s2]) = C$B$ s1 `subsetV` s2
eC _ Eql     (TC[Set s1,Set s2]) = C$B$ s1 `eql` s2
eC _ Eql     (TC[TC c1,TC c2]) = C$B$ c1 == c2
eC e SetEnum (TC[N n1,N n2]) = if int n1 && int n2 then C $ Set (map ((N).rat) [nume n1..nume n2]) else e
eC _ SetExplicit (TC cs) = C$Set$ set cs
eC _ Circ      (TC[TC s1,TC s2]) = C$TC$ s1++s2
eC e Subscript (TC[TC cs,N i]) = if int i && (i < toRational (length cs)) then C $ cs!!(rat $ nume i) else e
eC _ Cart  (TC [Set s1, Set s2]) = C$Set$ map (\(c1,c2)->TC[c1,c2]) $ s1 >< s2
eC e Cart  (TC cs) =
  let uwrap (Set c) = Just c
      uwrap _ = Nothing
      ss = catMaybes $ map uwrap cs
      mkProd [cs] = [[c] | c<-cs]
      mkProd (cs:css) = [[c]++cs' | c<-cs, cs'<-mkProd css]
  in if length ss /= length cs then e else C$Set$ case ss of
      [] -> []
      [s] -> s
      _ -> map TC $ mkProd ss
eC e _ _ = e 

eqV (Set cs) (Set cs') = cs `eql` cs'
eqV v v' = v == v'

elt c' cs = or [eqV c c' | c<-cs]
subsetV cs cs' = and [elt c cs' | c<-cs]

value :: Exp -> Maybe Const
value (T es) = maybe Nothing (\cs -> Just $ TC cs) $ valueList es
value (C c) = case c of
  N n -> Just c
  B b -> Just c
  Set s -> Just c
  TC cs -> Just c
  Kleene cs -> Just c
  c -> if c `elem` [SetN,SetZ,SetQ,SetR,Ast,Min,Max,Infinity] then Just c else Nothing
value _ = Nothing

valueList :: [Exp] -> Maybe [Const]
valueList es = if length cs == length es then Just cs else Nothing
  where cs = catMaybes $ map value es

isN c = case c of N _-> True; _ -> False
getN c = case c of N x->Just x;_ -> Nothing
getNs = catMaybes.(map getN)

identity c = case c of
  Plus -> N 0
  Times -> N 1
  Union -> Set []
  Isect -> Set []
  And -> B True
  Or -> B False

----------------------------------------------------------------
-- | Turn quantified variables into substitution collections;
--   fail if not all sets are evaluated or there are no sets.

convIns :: [Exp] -> Maybe [Subst]
convIns [(App (C In) (T [Var n, C (Set cs)]))] = Just $ [[(n,C c)] | c<-cs]
convIns ((App (C In) (T [Var n, C (Set cs)])):ins) = maybe Nothing (\r->Just$ [sub++[(n,C c)] | c<-cs, sub<-r]) $ convIns ins
convIns _ = Nothing

--eof