----------------------------------------------------------------
--
-- aartifact
-- http://www.aartifact.org/src/
-- Copyright (C) 2008-2010
-- A. Lapets
--
-- This software is made available under the GNU GPLv3.
--
-- ExpConst.hs
--   Representation of built-in mathematical constants.

----------------------------------------------------------------
-- 

module ExpConst where

import Ratio

import Set

----------------------------------------------------------------
-- 

data Bracket = Round | Square | Curly | Angle | Oxford | Bar
  deriving (Show, Eq, Ord)

data Const =
    Apply | Tuple | Considering
  | FalToUnknown | SearchIff
  | SLC Const Const
  | RatioMultiSet Const Const
  | UserOp String

  | Pow | Log | Ln | EulerE
  | Neg | Times | Div | Plus | Minus 
  | Mod | GCF | LCM
  | Max | Min | Floor | Ceil
  | Subscript | Circ
  | Eql | Neq | Lt | Lte | Gt | Gte | Cong
  | In | Union | Isect | Cart | Arrow | Ran | Dom
  | Subset | Subseteq
  | And | Or | Not | Imp | Iff | IfThenElse
  | B Bool | N Rational | SetZ | SetN | SetQ | SetR | Ast
  | SetComp | SetExplicit | SetEnum | Set [Const] | PowerSet
  | TC [Const] | Kleene [Const]
  | NLPredC [Maybe String] | NLPredLC [Maybe String]
  | Brack Bracket Bracket
  | Infinity
  deriving (Show,Eq,Ord)

----------------------------------------------------------------
-- Concrete representations (e.g. for parsing) of constants.

data OpFixity = InL | InR | Pre | Post | Circum | None
type OpTable = [[((Const, String), OpFixity)]]

constStr = (map (snd.fst) constAll)++["\\times"]
opsStr = map (snd.fst) opsAll
constAll = constStrPairs++opsIter
opsAll = concat$opsArith++opsSet++opsRel++opsLogic++opsSubscript

constStrPairs = map (\p->(p,None))
  [ (EulerE, "\\eulere")
  , (Set [], "\\emptyset")
  , (Ast,  "\\ast")
  , (PowerSet, "\\powerset")
  , (Min,  "\\min")
  , (Max,  "\\max")
  , (SetZ, "\\Z")
  , (SetN, "\\N")
  , (SetQ, "\\Q")
  , (SetR, "\\R")
  , (Dom, "\\dom")
  , (Ran, "\\ran")
  , (Infinity, "\\infty")
  , (Log, "\\log")
  , (GCF, "\\gcf")
  , (LCM, "\\lcm")
  ]
opsIter = map (\p->(p,None))
  [ (Plus,  "\\sum")
  , (Times, "\\prod")
  , (Union, "\\bigcup")
  , (Isect, "\\bigcap")
  , (And, "\\bigwedge")
  , (Or, "\\bigvee")
  ]
opsSubscript = [ [ ((Subscript, "_"), InL) ] ]
opsArith  =
  [ [ ((Pow,   "^"), InL) ]
  , [ ((Neg,   "-"), Pre) ]
  , [ ((Not,   "\\neg"), Pre) ]
  , [ ((Times, "\\cdot"), InL)
    , ((Times, "*"), InL)
    , ((Div,   "/"), InL)
    ]
  , [ ((Plus,  "+"), InL)
    , ((Minus, "-"), InL)
    ]
  , [ ((Mod,   "\\mod"), InL) ]
  , [ ((Circ,  "\\circ"), InL)
    ]
  ]
opsSet  =
  --[[((Cart,  "\\times"), InL)]] --implemented in parser
  [ [ ((Isect, "\\cap"), InL)
    , ((Union, "\\cup"), InL)
    ]
  , [ ((Arrow, "\\rightarrow"), InR)
    ]
  ]
opsRel =
  [ [ ((Eql,  "="), InL)
    , ((Neq,  "\\neq"), InL)
    , ((Cong, "\\equiv"), InL)
    , ((Gt,   ">"), InL)
    , ((Gte,  "\\geq"), InL)
    , ((Lt,   "<"), InL)
    , ((Lte,  "\\leq"), InL)
    , ((In,   "\\in"), InL)
    , ((Subseteq, "\\subseteq"), InL)
    , ((Subset, "\\subset"), InL) ]
  ]
opsLogic =
  [ [ ((And, "\\wedge"), InL)
    , ((Or,  "\\vee"), InL)
    ]
  , [ ((Imp, "\\Rightarrow"), InR)
    , ((Iff, "\\Leftrightarrow"), InL)
    ]
  ]

--eof
