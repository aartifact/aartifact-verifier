----------------------------------------------------------------
--
-- | aartifact
--   http://www.aartifact.org/
--
-- @src\/ValidationComp.hs@
--
--   Representation of partially or completely computedresult
--   of a validation attempt.
--

----------------------------------------------------------------
--

module ValidationComp where

import ExpConst
import Exp

data Verification = 
    Verifiable Const 
  | Unknown
  | Potential (() -> Verification)

----------------------------------------------------------------
-- | Functions for values of type Verification Bool.

(&&&) v1 v2 = case v1 of
  Verifiable (B True) -> case v2 of
    Verifiable (B True) -> Verifiable (B True)
    Verifiable (B False) -> Verifiable (B False)
    _ -> v2
  Verifiable (B False) -> Verifiable (B False)
  Unknown -> case v2 of
    Verifiable (B False) -> Verifiable (B False)
    _ -> Unknown
  Potential vf -> case v2 of
    Verifiable (B True) -> v1
    Potential vf' -> Potential (\() -> vf () &&& vf' ())
    falOrUnv -> falOrUnv
  _ -> Unknown

(|||) v1 v2 = case v1 of
  Verifiable (B True) -> v1
  Verifiable (B False) -> case v2 of
    Verifiable (B False) -> Verifiable (B False)
    Verifiable (B True) -> v2
    Potential vf -> Potential $ \() -> v1 ||| vf ()
    Unknown -> v1
  Potential vf -> case v2 of
    Verifiable (B True) -> v2
    Verifiable (B False) -> Potential $ \() -> vf () ||| v2
    Potential vf' -> Potential (\() -> vf () ||| vf' ())
    Unknown -> v1
    _ -> Unknown
  Unknown -> v2
  _ -> Unknown

(|/|) v1 v2 = case v1 of
  Verifiable (B True) -> v1
  Verifiable (B False) -> case v2 of
    Verifiable (B b) -> v2
    Potential vf -> Potential $ \() -> v1 |/| vf ()
    Unknown -> Unknown
  Potential vf -> case v2 of
    Verifiable (B True) -> v2
    Verifiable (B False) -> Potential $ \() -> vf () |/| v2
    Potential vf' -> Potential (\() -> vf () |/| vf' ())
    Unknown -> Unknown
  Unknown -> Unknown
  _ -> Unknown

notV r = case r of
  Verifiable (B b) -> Verifiable (B $ not b)
  _ -> Unknown

orV :: [Verification] -> Verification
orV = foldl (|||) Unknown

orV' :: [Verification] -> Verification
orV' = foldl (|/|) (Verifiable (B False))

andV :: [Verification] -> Verification
andV = foldl (&&&) (Verifiable (B True))

boolToV b = if b then Verifiable (B True) else Unknown
isVTrue v = case v of Verifiable (B True)->True;_->False
isVTrue' v = case v of
  Verifiable (B True) -> v
  Potential vf -> Potential $ \() -> isVTrue' $ vf ()
  _ -> Unknown

--eof