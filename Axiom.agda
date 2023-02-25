{-# OPTIONS --cubical #-}

module Axiom where

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude

-- what's the difference between `hcomp and `merge?
postulate
  merge  : ∀ {ℓ} {A : Type ℓ} (p : I → A) (q : I → A) → (p i1 ≡ q i0) → (p i0 ≡ q i1)
  mergeT : ∀ {ℓ} (P : I → Type ℓ) (Q : I → Type ℓ) → (P i1 ≡ Q i0) → (P i0 ≡ Q i1)


{--
merge' : ∀ {ℓ} {A : Type ℓ} (p : I → A) (q : I → A) → (p i1 ≡ q i0) → (p i0 ≡ q i1)
merge' {ℓ}{A} p q r = p ∙∙ r ∙∙ q
--}
