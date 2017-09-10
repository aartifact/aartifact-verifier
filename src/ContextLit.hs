----------------------------------------------------------------
--
-- | aartifact
--   http://www.aartifact.org/
--
-- @src\/ContextLit.hs@
--
--   Auxiliary context component: meta-propositions about the
--   literal structure of expressions.
--

----------------------------------------------------------------
--

module ContextLit where

import Ratio

import ExpConst (Const(..))
import Exp (Exp(..), bOp)
import ContextRelations

----------------------------------------------------------------
-- | Consideration with respect to auxiliary context.

considLit e rs = case e of
  C (N i) ->
    if denominator i == 1 && numerator i >= 0 then
      updRels rs (bOp In e (C (SetN)))
    else if denominator i == 1 then
      updRels rs (bOp In e (C (SetZ)))
    else 
      updRels rs (bOp In e (C (SetQ)))
  _ -> rs

--eof