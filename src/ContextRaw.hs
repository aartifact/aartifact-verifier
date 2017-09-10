----------------------------------------------------------------
--
-- | aartifact
--   http://www.aartifact.org/
--
-- @src\/ContextOntology.hs@
--
--   Concrete syntax of the propositions that constitute the
--   built-in ontology.
--

----------------------------------------------------------------
--

module ContextRaw where
import ExpConst
import Exp
import ExpPredicate
import Context
import ContextAux
import MapUsingRBTree
compiledSysList = []

rawsys _ = stateEmpty

--eof