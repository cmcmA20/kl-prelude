{-# OPTIONS --safe --without-K #-}
module KL.Prelude where

open import Agda.Primitive using (Level; lsuc; _⊔_)
  renaming (Set to Type; lzero to 0ℓ)
  public

module Levels where
  variable
    ℓ  ℓ′ ℓ″ ℓ‴ ℓ⁗ : Level
    ℓ₀ ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level
open Levels

-- fire up instance search
it : {A : Type ℓ} ⦃ x : A ⦄ → A
it ⦃ x ⦄ = x

open import Data.Product using (Σ; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
Σ-≡ : {A : Type ℓ} {B : A → Type ℓ′} {P Q : Σ A B} →
      (basePath : proj₁ P ≡ proj₁ Q) → (liftedPath : subst B basePath (proj₂ P) ≡ proj₂ Q) →
      P ≡ Q
Σ-≡ refl refl = refl

Σ-elim-fst : {A : Type ℓ} {B : A → Type ℓ′} {P Q : Σ A B} →
         P ≡ Q →
         proj₁ P ≡ proj₁ Q
Σ-elim-fst refl = refl
