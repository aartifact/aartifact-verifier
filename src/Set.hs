----------------------------------------------------------------
--
-- | aartifact
--   http://www.aartifact.org/
--
-- @src\/Set.hs@
--
--   Set representation and common operations.
--

----------------------------------------------------------------
--

module Set where

import Data.List

----------------------------------------------------------------
-- | Sets are represented as lists; because this is a standard
--   practice, this module exposes this fact, and exists solely
--   to provide concise synonyms for common operations.

type Set a = [a]

add :: Eq a => a -> Set a -> Set a
add x set = if x `elem` set then set else x:set

subset :: Eq a => Set a -> Set a -> Bool
subset s1 s2 = and $ map (\x -> elem x s2) s1

eql :: Eq a => Set a -> Set a -> Bool
eql s1 s2 = (s1 `subset` s2) && (s2 `subset` s1)

set :: Eq a => [a] -> Set a
set = nub

(\/) :: Eq a => Set a -> Set a -> Set a
(\/) = Data.List.union

(/\) :: Eq a => Set a -> Set a -> Set a
(/\) = Data.List.intersect

diff :: Eq a => Set a -> Set a -> Set a
diff = (\\)

(><) :: (Eq a, Eq b) => Set a -> Set b -> Set (a,b)
(><) s s' = [(x,y) | x<-s, y<-s']

rgt :: (a -> a -> Bool) -> Set (a,b) -> a -> Set b
rgt eq r x = [y | (x',y) <- r, x' `eq` x]

lft :: (b -> b -> Bool) -> Set (a,b) -> b -> Set a
lft eq r y = [x | (x,y') <- r, y' `eq` y]

--eof