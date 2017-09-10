----------------------------------------------------------------
--
-- | aartifact
--   http://www.aartifact.org/
--
-- @src\/IOParserOps.hs@
--
--   Representation of built-in and user-defined operators, as
--   used by the parser state.
--

----------------------------------------------------------------
--

module IOParserOps where

import IOSource
import ExpConst

----------------------------------------------------------------
-- | Operator table for parser.

type OpsState = ([OpTable], OpTable)

opsState0 :: OpsState
opsState0 = ([opsRel, opsSet, opsArith], [[]])

addOps :: [String] -> OpsState -> IntroTyp -> OpsState
addOps os0 ([rs, ss, as], [cs]) ty = 
 let mk fx = [((UserOp o, o), fx) | o<-os0]
     os = mk InL
     os' = mk None
 in case ty of
   RelOp -> ([rs++[os], ss, as], [cs])
   SetOp -> ([rs, ss++[os], as], [cs])
   ArithOp -> ([rs, ss, as++[os]], [cs])
   Constant -> ([rs, ss, as], [cs++os'])
   _ -> ([rs, ss, as], [cs])

opsStrTbl :: OpsState -> [String]
opsStrTbl (ts,nFOs) = concat$concat$[[ map (snd.fst) l | l<-t] | t<-ts++[nFOs]]

introTyp ws = case ws of
  ("set":_) -> SetOp 
  ("relation":_) -> RelOp
  ("arithmetic":_) -> ArithOp
  ("constant":_) -> Constant
  ("constants":_) -> Constant
  _ -> Variable

--eof