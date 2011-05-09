----------------------------------------------------------------
--
-- aartifact
-- http://www.aartifact.org/src/
-- Copyright (C) 2008-2011
-- A. Lapets
--
-- This software is made available under the GNU GPLv3.
--
-- ExpPredicate.hs
--   Representation of arithmetic and logical expressions in
--   the form of an encapsulated predicate object that can
--   be used as, for example, an edge label in relation graphs.

----------------------------------------------------------------
-- 

module ExpPredicate where

import Data.Maybe (catMaybes)
import Data.List (partition, sort, sortBy)

import Set
import ExpConst
import Exp

----------------------------------------------------------------
--

data PredWrap =
    PW Const
  | PE Exp
  deriving (Show,Eq,Ord)

----------------------------------------------------------------
--

--eof
