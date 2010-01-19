----------------------------------------------------------------
--
-- aartifact
-- http://www.aartifact.org/src/
-- Copyright (C) 2008-2010
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

module MapUsingRBTree (Map, emp, app, ran, preImg, set, 
                         def, mapRan, appInDom, inDom) where

----------------------------------------------------------------
-- Implementation.

type Map a b = Tree a b

-- Define the red-black tree.

data Color = R | B
data Tree a b = NULL | Bran Color (Tree a b) (a,b) (Tree a b)

emp :: Tree a b
emp =  NULL

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

set :: (Eq a, Ord a) => a -> b -> Map a b -> Map a b
set x y (m) = def x y (\_ _->y) m

-- Balanced by a-inequalities.
def :: (Eq a, Ord a) => a -> b -> (a -> b -> b) -> Tree a b -> Tree a b
def e i f s = blackify (ins s) where 
  ins NULL = Bran R NULL (e,i) NULL
  ins (Bran color a (e1,y) b)
    | e < e1 = bal color (ins a) (e1,y) b
    | e == e1 = Bran color a (e1,f e1 y) b
    | e > e1 = bal color a (e1,y) (ins b)
  blackify(Bran _ a (e2,y) b) = Bran B a (e2,y) b

  -- Balancing function.
  bal B (Bran R (Bran R a x b) y c) z d = Bran R (Bran B a x b) y (Bran B c z d)
  bal B (Bran R a x (Bran R b y c)) z d = Bran R (Bran B a x b) y (Bran B c z d)
  bal B a x (Bran R (Bran R b y c) z d) = Bran R (Bran B a x b) y (Bran B c z d)
  bal B a x (Bran R b y (Bran R c z d)) = Bran R (Bran B a x b) y (Bran B c z d)
  bal color a x b = Bran color a x b

--eof
