----------------------------------------------------------------
--
-- | aartifact
--   http://www.aartifact.org/
--
-- Contributors to this module:
--    Andrei Lapets
--    David House
--
-- @src\/ContextHypergraph.hs@
--
--   Data structure for a hypergraph with a defined closure
--   function.
--

----------------------------------------------------------------
--

module ContextHypergraph where

import MapUsingRBTree

----------------------------------------------------------------
-- | Marks (representing processed/unprocessed state).

type Mark = Bool

unmarked :: Mark
unmarked = False

marked :: Mark
marked = True

oneMarked :: [(Mark,a)] -> Bool
oneMarked = or.(map fst)

----------------------------------------------------------------
-- | Hypergraph interface.
--   Edges are labelled by a value of type "a", and nodes in the
--   graph are labelled by a value of type "b".
--   All edges having the same label are all stored under a
--   single entry designated by the label.

type Edge a b = (a, [b])
type EdgeList a b = ([a], [[b]])
type Law a b = (EdgeList a b, [Edge a b])
type Hypergraph a b = ([(Mark,Law a b)], Map a (Mark, [(Mark,[b])]))

empHG :: (Eq a, Ord a, Eq b) => Hypergraph a b
empHG = ([], emp)

hgSize :: Ord a => Hypergraph a b -> Integer
hgSize (ls,g) =  toInteger $ length $ concat (map snd $ ran g)

addLawHG :: (Eq a, Ord a) => Hypergraph a b -> ([Edge a b], [Edge a b]) -> Hypergraph a b
addLawHG (ls,g) (r,o) = ((marked,((map fst r, map snd r),o)):ls,g')
  where g' = foldr (\x g -> def x (unmarked,[]) (\_ y ->y) g) g (map fst r)

edgeHG :: (Eq a, Ord a, Eq b) => Edge a b -> Hypergraph a b -> Bool
edgeHG (e,ns) (_,g) = ns `elem` [ns | (_,ns) <- maybe [] snd $ app e g]

reportHG :: (Eq a, Ord a, Show a, Eq b) => ([b] -> Bool) -> Hypergraph a b -> [(a,[b])]
reportHG f (_,g) =
  let l = list g
      l' =  concat [map (\y -> (x,y)) ys | (x,ys) <- [ (x, map snd ys) | (x,(_,ys)) <- l]]
  in [(x,y) | (x,y) <- l', f y]

relabelHG :: (Eq a, Ord a, Eq b) => Hypergraph a b -> b -> b -> Hypergraph a b
relabelHG (ls,g) j j' = (ls, mapRan (\_ (mrk,es) -> (mrk, map relbl es)) g)
  where relbl (m,is) = (m, [if i==j then j' else i | i<-is])

isEMarked :: (Eq a, Ord a, Eq b) => Hypergraph a b -> a -> Bool
isEMarked (_,g) c = maybe False fst $ app c g

hasMarkedHG :: (Eq a, Ord a, Eq b) => Hypergraph a b -> Bool
hasMarkedHG (_,g) = oneMarked $ ran g

resetMarksHG :: (Eq a, Ord a, Eq b) => Hypergraph a b -> Hypergraph a b
resetMarksHG (ls,g) = 
  ([(unmarked,l) | (_,l)<-ls], 
   mapRan (\_ (_,es) -> (unmarked, map (\(_,is) -> (unmarked, is)) es)) g)

getHG :: (Eq a, Ord a, Eq b) => Hypergraph a b -> a -> [Edge a b]
getHG (_,g) e = [(e, snd ens) | ens <- maybe [] snd (app e g), fst ens]

----------------------------------------------------------------
-- | We optimize for the common cases by handling them
--   explicitly. This optimization improves performance by a
--   significant constant factor (between 2 and 20).

getsHG :: (Eq a, Ord a, Eq b) => Hypergraph a b -> [a] -> [[[b]]]
getsHG _ [] = []
getsHG (hg@(_,g)) es = if or $ map (isEMarked hg) es then (case es of
  [e1]       -> [[y1] | (m,y1)<-p e1, m]
  [e1,e2]    -> [[y1,y2] | (m1,y1)<-p e1, y2<-if m1 then map snd (p e2) else [y2|(m2,y2)<-p e2,m2]]
  [e1,e2,e3] -> 
    [y1:ys | 
     (m1,y1)<-p e1, 
     ys<-if m1 then 
          [[y2,y3] | (_,y2)<-p e2,(_,y3)<-p e3]
         else 
          [[y2,y3] | (m2,y2)<-p e2,
            y3<-if m2 then map snd (p e3) else [y3 | (m3,y3)<-p e3,m3]]]

  [e1,e2,e3,e4] ->
    [y1:ys |
     (m1,y1)<-p e1, 
     ys <- if m1 then
            [[y2,y3,y4] | (_,y2)<-p e2,(_,y3)<-p e3,(_,y4)<-p e4]
           else [y2:ys | 
            (m2,y2)<-p e2, 
            ys<-if m2 then 
                 [[y3,y4] | (_,y3)<-p e3,(_,y4)<-p e4]
                else 
                 [[y3,y4] | (m3,y3)<-p e3, 
                            y4 <- if m2 then map snd $ p e4 else [y4 | (m4,y4)<-p e4, m4]]]]

  [e1,e2,e3,e4,e5] -> 
    [y1:ys | 
      (m1,y1)<-p e1, 
      ys <- if m1 then
             [[y2,y3,y4,y5] | (_,y2)<-p e2,(_,y3)<-p e3,(_,y4)<-p e4,(_,y5)<-p e5]
            else [y2:ys | 
             (m2,y2)<-p e2, 
             ys<-if m2 then 
                  [[y3,y4,y5] | (_,y3)<-p e3,(_,y4)<-p e4,(_,y5)<-p e5]
                 else 
                  [y3:ys |
                    (m3,y3)<-p e3, 
                    ys <- if m2 then  [[y4,y5] | (_,y4)<-p e4,(_,y5)<-p e5]
                          else [[y4,y5] | (m4,y4)<-p e4, 
                               y5<-if m4 then map snd (p e5) else [y5 | (m5,y5)<-p e5,m5]]]]]
  es -> get es
  ) else [] where
    p c = snd $ appInDom c g
    get0 [c] =  [[y] | (_,y)<-p c]
    get0 (c:cs) = [y:ys | (_,y)<-p c, ys<-get0 cs]
    get [c] =  [[y] | (m,y)<-p c,m]
    get (c:cs) = [y:ys | (m,y)<-p c, ys<-if m then get0 cs else get cs]

putHG :: (Eq a, Ord a, Eq b) => Hypergraph a b -> Edge a b -> Hypergraph a b
putHG (ls,g) (e,ns) = (ls', def e (marked,[(marked,ns)]) add g)
  where add _ (mrk,l) = if (ns `elem` map snd l) then (mrk,l) else (marked,(marked,ns):l)
        ls' = [(mrk || (e `elem` fst r), (r,o)) | (mrk,(r,o)) <- ls]

putsHG :: (Eq a, Ord a, Eq b) => Hypergraph a b -> [Edge a b] -> Hypergraph a b
putsHG hg es = foldl putHG hg es

--eof