{-# OPTIONS --safe --without-K #-}
module KL.Show where

open import Data.String.Base using (String)

open import KL.Prelude

-- not for pretty-printing but for debug purposes
record Show (A : Type ℓ) : Type ℓ where
  field show : A → String
