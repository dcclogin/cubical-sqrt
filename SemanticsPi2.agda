{-# OPTIONS --cubical --allow-unsolved-metas #-}

module SemanticsPi2 where

open import SyntaxPi2
open import GroupoidLawsT
open import Data.Bool hiding  (_∨_ ; _∧_)
open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism renaming (Iso to _≅_)


⟦_⟧ : Π₂ → Type
⟦ 𝔹 ⟧ = Bool

id-path : {T : Type} → T ≡ T
id-path = refl

not-path : Bool ≡ Bool
not-path = isoToPath (iso not not rem rem)
  where
    rem : (b : Bool) → not (not b) ≡ b
    rem false = refl
    rem true  = refl


!notp=notp : sym not-path ≡ not-path
!notp=notp = {!!}


_⟦_⟧₁ : {A B : Π₂} (i : I) (c : A ↔ B) → ⟦ A ⟧ ≡ ⟦ B ⟧
i ⟦ id₁ ⟧₁    = id-path
i ⟦ not₁ ⟧₁   = not-path
i ⟦ !₁ c ⟧₁   = sym (i ⟦ c ⟧₁)
i ⟦ p ⊙ q ⟧₁  = (i ⟦ p ⟧₁) ∙ (i ⟦ q ⟧₁)
i ⟦ sqrt c ⟧₁ = {!!}


_⟦_⟧₂ : {A B : Π₂} (i : I) {p q : A ↔ B}
      → (p ⇔ q) → (i ⟦ p ⟧₁) ≡ (i ⟦ q ⟧₁)
i ⟦ id₂ ⟧₂      = refl
i ⟦ !₂ t ⟧₂     = sym (i ⟦ t ⟧₂)
i ⟦ t₁ ⊙₂ t₂ ⟧₂ = (i ⟦ t₁ ⟧₂) ∙ (i ⟦ t₂ ⟧₂)
i ⟦ sqd ⟧₂      = {!!}
i ⟦ sqf ⟧₂      = {!!}
i ⟦ sqi t ⟧₂    = {!!}
i ⟦ sqc ⟧₂      = {!!}
i ⟦ idl⊙l ⟧₂    = sym lUnitT           -- refl ∙ p ≡ p
i ⟦ idr⊙l ⟧₂    = sym rUnitT           -- p ∙ refl ≡ p
i ⟦ !r p ⟧₂     = rCancelT (i ⟦ p ⟧₁)  -- p ∙ (sym p) ≡ refl
i ⟦ !l p ⟧₂     = lCancelT (i ⟦ p ⟧₁)  -- (sym p) ∙ p ≡ refl
i ⟦ assoc⊙l ⟧₂  = {!!}
i ⟦ assoc⊙r ⟧₂  = {!!}
i ⟦ t₁ ▣ t₂ ⟧₂  = {!!}
i ⟦ !id₁ ⟧₂     = refl
i ⟦ !not₁ ⟧₂    = !notp=notp           -- (sym not-path) ≡ not-path
i ⟦ !! ⟧₂       = refl
i ⟦ `! t ⟧₂     = cong sym (i ⟦ t ⟧₂)
