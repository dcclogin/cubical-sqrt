{-# OPTIONS --cubical --allow-unsolved-metas #-}

module SemanticsPi2 where

open import SyntaxPi2
open import GroupoidLawsT
open import Cubical.Data.Bool
open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism renaming (Iso to _≅_)


⟦_⟧ : Π₂ → Type
⟦ 𝟚 ⟧ = Bool

id-path : ∀ {ℓ} {T : Type ℓ} → T ≡ T
id-path = refl

not-path : Bool ≡ Bool
not-path = isoToPath (iso not not rem rem)
  where
    rem : (b : Bool) → not (not b) ≡ b
    rem false = refl
    rem true  = refl

-- funExt?
!notp=notp : sym not-path ≡ not-path
!notp=notp = {!!}

module _ where private
  ptws : (b : Bool) → transport (sym not-path) b ≡ not b
  ptws = λ _ → refl

  _ : transport (sym not-path) ≡ not
  _ = funExt ptws



-- _to_⟦_⟧₁ ?
_⟦_⟧₁ : {A B : Π₂} (i : I) (c : A ↔ B) → ⟦ A ⟧ ≡ ⟦ B ⟧
i ⟦ `id₁ ⟧₁   = id-path
i ⟦ `not ⟧₁   = not-path
i ⟦ !₁ c ⟧₁   = sym (i ⟦ c ⟧₁)
i ⟦ p ⊙ q ⟧₁  = (i ⟦ p ⟧₁) ∙ (i ⟦ q ⟧₁)
i ⟦ sqrt c ⟧₁ = {!!} -- need a semantics model


_⟦_⟧₂ : {A B : Π₂} (i : I) {p q : A ↔ B}
      → (p ⇔ q) → (i ⟦ p ⟧₁) ≡ (i ⟦ q ⟧₁)
i ⟦ `id₂ ⟧₂     = refl
i ⟦ !₂ t ⟧₂     = sym (i ⟦ t ⟧₂)
i ⟦ t₁ ⊙₂ t₂ ⟧₂ = (i ⟦ t₁ ⟧₂) ∙ (i ⟦ t₂ ⟧₂)
i ⟦ sqd ⟧₂      = {!!}
i ⟦ sqf ⟧₂      = {!!}
i ⟦ sqi t ⟧₂    = {!!}
i ⟦ sqc ⟧₂      = {!!}
i ⟦ sq! ⟧₂      = {!!}
i ⟦ idl⊙l ⟧₂    = sym lUnitT           -- refl ∙ p ≡ p
i ⟦ idr⊙l ⟧₂    = sym rUnitT           -- p ∙ refl ≡ p
i ⟦ !r p ⟧₂     = rCancelT (i ⟦ p ⟧₁)  -- p ∙ (sym p) ≡ refl
i ⟦ !l p ⟧₂     = lCancelT (i ⟦ p ⟧₁)  -- (sym p) ∙ p ≡ refl
i ⟦ assoc⊙l ⟧₂  = assocT
i ⟦ assoc⊙r ⟧₂  = sym assocT
i ⟦ t₁ ▣ t₂ ⟧₂  = (i ⟦ t₁ ⟧₂) ◾ (i ⟦ t₂ ⟧₂) -- p ≡ q → r ≡ s → p ∙ r ≡ q ∙ s
i ⟦ !id₁ ⟧₂     = refl
i ⟦ !not ⟧₂     = !notp=notp           -- (sym not-path) ≡ not-path
i ⟦ !! ⟧₂       = refl
i ⟦ `! t ⟧₂     = cong sym (i ⟦ t ⟧₂)
