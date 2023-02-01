{-# OPTIONS --safe --without-K #-}
module KL.DecEq where

open import Relation.Binary.Definitions using (DecidableEquality)

open import KL.Prelude

record DecEq {ℓ} (A : Type ℓ) : Type ℓ where
  field _≟_ : DecidableEquality A

-- open DecEq ⦃ ... ⦄ public
-- ^ it is unique if exists but do we want to use only instance search for this?
