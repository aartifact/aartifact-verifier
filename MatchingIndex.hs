----------------------------------------------------------------
--
-- aartifact
-- http://www.aartifact.org/src/
-- Copyright (C) 2008-2010
-- A. Lapets
--
-- This software is made available under the GNU GPLv3.
--
-- MatchingIndex.hs
--   Index data type that supports matching (i.e. unification)
--   over index lists; for use as a label for equivalence
--   relations.

----------------------------------------------------------------
-- 

module MatchingIndex where

----------------------------------------------------------------
-- For positive integers, matching corresponds to equality.
-- Negative integers are used as "wildcards" that can match any
-- positive integer. In order for two index lists to match, each
-- negative integer instance must match the same positive value.

type Index = Integer

matchIxs :: (Ord b, Num b) => [[b]] -> [[b]] -> [(a, [b])] -> [(a, [b])]
matchIxs e1 e2 concs = (case matchEach e1 e2 [] of
  Just su -> concat [let ls = lookups conc su in if 0 `elem` ls then [] else [(c, ls)] | (c, conc) <- concs]
  _ -> [])
  where
    lookups xs l = [if x<0 then lkup x l else x | x<-xs]

    lkup x' ((x,y):xys) = if x==x' then y else lkup x' xys
    lkup x' [] = 0

    matchEach (cl1:cls1) (cl2:cls2) ps = case mch cl1 cl2 ps of
      Nothing -> Nothing
      Just ps' -> matchEach cls1 cls2 ps'
    matchEach [] [] ps = Just ps
    matchEach _  _  _  = Nothing

    mch (x:xs) (y:ys) ps =
      if x > 0 then (if x==y then mch xs ys ps else Nothing)
      else if x == 0 then Nothing
      else case lookup x ps of
        Nothing -> mch xs ys $ (x,y):ps
        Just y' -> if y==y' then mch xs ys ps else Nothing
    mch [] [] ps = Just ps
    mch _  _  _  = Nothing

--eof
