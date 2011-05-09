----------------------------------------------------------------
--
-- aartifact
-- http://www.aartifact.org/src/
-- Copyright (C) 2008-2011
-- A. Lapets
--
-- This software is made available under the GNU GPLv3.
--
-- Contributors to this module:
--    David House
--    Andrei Lapets
--
-- MapUsingRBTree.hs
--   Red-black tree implementation of data structure for
--   no-removal finite maps.

----------------------------------------------------------------
--

module MapUsingRBTree where
--(Map, emp, app, ran, preImg, set, domSize,ranSize, def, mapRan, appInDom, inDom)

import Set ((\/))

----------------------------------------------------------------
-- Implementation.

type Map a b = Tree a b

-- Define the red-black tree.

data Color = R | Bl deriving Show
data Tree a b = NULL | Bran Color (Tree a b) (a,b) (Tree a b)
  deriving Show

emp :: Tree a b
emp =  NULL

domSize :: Tree a b -> Integer
domSize t = sz t where
  sz (Bran _ t _ t') = 1 + sz t + sz t'
  sz NULL = 0

ranSize :: Eq b => Tree a b -> Integer
ranSize t = toInteger $ length $ u t where
  u (Bran _ t (_,y) t') = [y] \/ u t \/ u t'
  u NULL = []

inDom :: (Eq a, Ord a) => Tree a b -> a -> Bool
inDom t x = isIndex x t
  where
    isIndex e NULL = False
    isIndex e (Bran _ a (e1,_) b)
      | e < e1 = isIndex e a
      | e == e1 = True
      | e > e1 = isIndex e b

appInDom :: (Eq a, Ord a) => a -> Tree a b -> b
appInDom x (Bran _ t (x',y) t')
 | x <  x' = appInDom x t
 | x == x' = y
 | x >  x' = appInDom x t'

app :: (Eq a, Ord a) => a -> Tree a b -> Maybe b
app x t = lookup x (getIndex' x t)
  where
    -- findIndexB helper function                   
    getIndex' :: Ord a => a -> Tree a b -> [(a,b)]
    getIndex' e NULL = []
    getIndex' e (Bran _ a (e1,i) b)
      | e < e1 = getIndex' e a
      | e == e1 = [(e,i)]
      | e > e1 = getIndex' e b

ran :: (Eq a, Ord a) => Tree a b -> [b]
ran t = acc [] t where
  acc l NULL = l
  acc l (Bran _ t (_,y) t') = y:acc (acc l t) t'

mapRan :: (Eq a, Ord a) => (a -> b -> b) -> Tree a b -> Tree a b
mapRan f t = mp t where
  mp (Bran c t (x,y) t') = Bran c (mp t) (x,f x y) (mp t')
  mp _ = NULL

preImg :: (Eq a, Eq b, Ord a) => b -> Tree a b -> [a]
preImg y t = acc [] t where
  acc l NULL = l
  acc l (Bran _ t (x,y') t') = if y==y' then x:acc (acc l t) t' else acc (acc l t) t'

list :: (Eq a, Eq b, Ord a) => Tree a b -> [(a,b)]
list t = case t of
  NULL -> []
  Bran _ t1 xy t2 -> xy:(list t1 ++ list t2)

set :: (Eq a, Ord a) => a -> b -> Map a b -> Map a b
set x y m = def x y (\_ _->y) m

-- Balanced by a-inequalities.
def :: (Eq a, Ord a) => a -> b -> (a -> b -> b) -> Tree a b -> Tree a b
def e i f s = blackify (ins s) where 
  ins NULL = Bran R NULL (e,i) NULL
  ins (Bran color a (e1,y) b)
    | e < e1 = bal color (ins a) (e1,y) b
    | e == e1 = Bran color a (e1,f e1 y) b
    | e > e1 = bal color a (e1,y) (ins b)
  blackify(Bran _ a (e2,y) b) = Bran Bl a (e2,y) b

  -- Balancing function.
  bal Bl (Bran R (Bran R a x b) y c) z d = Bran R (Bran Bl a x b) y (Bran Bl c z d)
  bal Bl (Bran R a x (Bran R b y c)) z d = Bran R (Bran Bl a x b) y (Bran Bl c z d)
  bal Bl a x (Bran R (Bran R b y c) z d) = Bran R (Bran Bl a x b) y (Bran Bl c z d)
  bal Bl a x (Bran R b y (Bran R c z d)) = Bran R (Bran Bl a x b) y (Bran Bl c z d)
  bal color a x b = Bran color a x b

--eof
