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
--    Andrei Lapets
--    David House
--
-- ContextEquiv.hs
--   Data structure for representing and efficiently 
--   manipulating a collection of equivalence classes over a
--   type with a defined order relation.

----------------------------------------------------------------
--

module ContextEquiv where

import MapUsingRBTree

----------------------------------------------------------------
-- Equivalence class data structure interface.

-- This is the data structure used for maintaining a collection
-- of equivalence classes of expressions.

type Equivalence a b = (Map a b, b)

empEquiv :: Num b => Equivalence a b
empEquiv = (emp, 1)

eqvSize :: Eq b => Equivalence a b -> (Integer, Integer)
eqvSize (m,_) = (domSize m, ranSize m)

-- This determines if two expressions are equal according
-- to the data structure.
chkEquality :: (Eq a, Ord a, Num b) => Equivalence a b -> a -> a -> Bool
chkEquality eqs x y = case getIxs [x,y] eqs of Just [i,j] -> i==j; _ -> False

getIx :: (Eq a, Ord a, Num b) => Equivalence a b -> a -> Maybe b
getIx (m,ni) x = case app x m of Just 0 -> Nothing; r -> r

getIxWithPutLbld :: (Eq a, Ord a, Num b) => Equivalence a b -> a -> (Either b b, Equivalence a b)
getIxWithPutLbld (eqs@(l,ni)) x = case getIx eqs x of
  Nothing -> (Left ni, (set x ni l,ni+1))
  Just i -> (Right i, eqs)

-- This function takes a list of expressions and determines
-- the corresponding list of equivalence class indices.
getIxs :: (Eq a, Ord a, Num b) => [a] -> Equivalence a b -> Maybe [b]
getIxs [] eqs = Just []
getIxs (x:xs) eqs = case getIxs xs eqs of
  Nothing -> Nothing
  Just is -> case getIx eqs x of
    Nothing -> Nothing
    Just i -> Just (i:is)

-- This takes a list of expressions and returns the list of
-- indices, but adds any new expressions and generates fresh
-- indices for them.
getIxsWithPut :: (Eq a, Ord a, Num b) => [a] -> Equivalence a b -> ([b], Equivalence a b)
getIxsWithPut [] eqs = ([],eqs)
getIxsWithPut (x:xs) eqs =
  let (is, (eqs'@(l,ni'))) = getIxsWithPut xs eqs
  in case getIx eqs' x of
    Just i -> (i:is, eqs')
    Nothing -> (ni':is, (set x ni' l,ni'+1))

getByIx :: (Eq a, Ord a, Num b) => b -> Equivalence a b -> [a]
getByIx y (m,_) = preImg y m

mergeEC :: (Eq a, Ord a, Num b) => b -> b -> Equivalence a b -> Equivalence a b
mergeEC j j' (m,ni) = (mapRan (\_ i->if i==j then j' else i) m,ni)

filtEq :: (Eq a, Ord a, Num b) => Equivalence a b -> (a -> Bool) -> Equivalence a b
filtEq (m,ni) f = (mapRan (\e i -> if f e then i else 0) m, ni)

-- This adds a new equality relationship to the structure.
putEquivExps :: (Eq a, Ord a, Num b) => a -> a -> Equivalence a b -> Equivalence a b
putEquivExps x y (eqs@(l,ni)) =
  case (getIx eqs x, getIx eqs y) of
    (Just i,  Just j)  -> mergeEC i j eqs
    (Just i,  Nothing) -> (set y i l,ni)
    (Nothing, Just i)  -> (set x i l,ni)
    (Nothing, Nothing) -> (set x ni (set y ni l),ni+1)

--eof
