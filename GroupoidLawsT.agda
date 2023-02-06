{-# OPTIONS --cubical #-}

module GroupoidLawsT where

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism renaming (Iso to _≅_)



rUnitT : ∀ {ℓ} {A B : Type ℓ} {p : A ≡ B} → p ≡ p ∙ refl
rUnitT {ℓ}{A}{B}{p} j i = hfill walls (inS (p i)) j
  where
    walls : ∀ j → Partial (~ i ∨ i) (Type ℓ)
    walls j (i = i0) = A
    walls j (i = i1) = B


-- need re-prove
lUnitT-filler : ∀ {ℓ} {A B : Type ℓ} (p : A ≡ B) → I → I → I → Type ℓ
lUnitT-filler {ℓ}{A}{B} p j k i =
  hfill (λ j → λ { (i = i0) → A
                 ; (i = i1) → p (~ k ∨ j )
                 ; (k = i0) → p i
                 })
        (inS (p (~ k ∧ i)))
        j

lUnitT : ∀ {ℓ} {A B : Type ℓ} {p : A ≡ B} → p ≡ refl ∙ p
lUnitT {ℓ}{A}{B}{p} j i = lUnitT-filler p i1 j i

-- need re-prove
rCancelT-filler : ∀ {ℓ} {A B : Type ℓ} (p : A ≡ B) → (k j i : I) → Type ℓ
rCancelT-filler {ℓ}{A}{B} p k j i =
  hfill (λ k → λ { (i = i0) → A
                 ; (i = i1) → p (~ k ∧ ~ j)
                 ; (j = i1) → A
                 })
        (inS (p (i ∧ ~ j)))
        k

rCancelT : ∀ {ℓ} {A B : Type ℓ} (p : A ≡ B) → p ∙ sym p ≡ refl
rCancelT {ℓ}{A}{B} p j i = rCancelT-filler p i1 j i

lCancelT : ∀ {ℓ} {A B : Type ℓ} (p : A ≡ B) → sym p ∙ p ≡ refl
lCancelT {ℓ}{A}{B} p = rCancelT (sym p)
