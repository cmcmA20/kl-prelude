{-# OPTIONS --safe --without-K #-}
module KL.Propositional where

open import Relation.Binary.PropositionalEquality using (isPropositional)

open import KL.Prelude

record IsProp {ℓ} (A : Type ℓ) : Type ℓ where
  field isProp : isPropositional A
