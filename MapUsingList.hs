----------------------------------------------------------------
--
-- aartifact
-- http://www.aartifact.org/src/
-- Copyright (C) 2008-2011
-- A. Lapets
--
-- This software is made available under the GNU GPLv3.
--
-- MapUsingList.hs
--   List implementation of data structure for no-removal finite
--   maps.

----------------------------------------------------------------
--

module MapUsingList (Map, emp, app, ran, set, def, mapRan) where

----------------------------------------------------------------
-- Implementation.

data Map a b = M [(a,b)]

emp :: Map a b
emp =  M []

app :: Eq a => a -> Map a b -> Maybe b
app x (M m) = lookup x m

ran :: Map a b -> [b]
ran (M m) = map snd m

set :: Eq a => a -> b -> Map a b -> Map a b
set x y (m) = def x y (\_ _->y) m

def :: Eq a => a -> b -> (a -> b -> b) -> Map a b -> Map a b
def x' y' f (M m) = M $ df m
  where df ((x,y):xys) = if x/=x' then (x,y):df xys else (x,f x y):xys
        df [] = [(x',y')]

mapRan :: (a -> b -> b) -> Map a b -> Map a b
mapRan f (M m) = M [(x, f x y) | (x,y) <- m]

mapRanSpec :: Eq a => a -> (b -> b) -> Map a b -> Map a b
mapRanSpec x' f (M m) = M [(x, if x'==x then f y else y) | (x,y) <- m]

--eof
