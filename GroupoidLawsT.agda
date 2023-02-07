{-# OPTIONS --cubical #-}

module GroupoidLawsT where

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism renaming (Iso to _≅_)


∙-fillerT : ∀ {ℓ} {A B C : Type ℓ} (p : A ≡ B) (q : B ≡ C)
          → Square refl q p (p ∙ q)
∙-fillerT {ℓ}{A}{B}{C} p q i j = hfill walls (inS (p i)) j
  where
    walls : ∀ j → Partial (~ i ∨ i) (Type ℓ)
    walls j (i = i0) = A
    walls j (i = i1) = q j



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
                 ; (i = i1) → p (~ k ∨ j)
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


-- p ∙ r ≡ q ∙ r
-- q ∙ r ≡ q ∙ s
_◾_ : ∀ {ℓ} {A B C : Type ℓ} {p q : A ≡ B} {r s : B ≡ C}
   → p ≡ q → r ≡ s → p ∙ r ≡ q ∙ s
_◾_ {ℓ}{A}{B}{C}{p}{q}{r}{s} α β = x ∙ y
  where
    x : p ∙ r ≡ q ∙ r
    x = λ i → α i ∙ r

    y : q ∙ r ≡ q ∙ s
    y = λ i → q ∙ β i


-- associativity
-- need two fillers : α-filler and β-filler
-- β-filler depends on ∙-fillerT
α-filler : ∀ {ℓ} {A B C D : Type ℓ} (p : A ≡ B) (q : B ≡ C) (r : C ≡ D)
         → Square refl (q ∙ r) p (p ∙ (q ∙ r))
α-filler {ℓ}{A}{B}{C}{D} p q r i j = hfill walls (inS (p i)) j
  where
    walls : ∀ j → Partial (~ i ∨ i) (Type ℓ)
    walls j (i = i0) = A
    walls j (i = i1) = (q ∙ r) j


β-filler : ∀ {ℓ} {A B C D : Type ℓ} (p : A ≡ B) (q : B ≡ C) (r : C ≡ D)
         → Square refl (q ∙ r) p ((p ∙ q) ∙ r)
β-filler {ℓ}{A}{B}{C}{D} p q r i j = hcomp walls (∙-fillerT p q i j)
  where
    walls : ∀ k → Partial (~ j ∨ j ∨ ~ i ∨ i) (Type ℓ)
    walls k (i = i0) = A
    walls k (i = i1) = ∙-fillerT q r j k
    walls k (j = i0) = p i
    walls k (j = i1) = ∙-fillerT (p ∙ q) r i k


assocT :  ∀ {ℓ} {A B C D : Type ℓ} {p : A ≡ B} {q : B ≡ C} {r : C ≡ D}
       → (p ∙ q) ∙ r ≡ p ∙ (q ∙ r)
assocT {ℓ}{A}{B}{C}{D}{p}{q}{r} j i = hcomp walls (p i)
  where
    walls : ∀ k → Partial (~ j ∨ j ∨ ~ i ∨ i) (Type ℓ)
    walls k (i = i0) = A
    walls k (i = i1) = (q ∙ r) k
    walls k (j = i0) = β-filler p q r i k
    walls k (j = i1) = α-filler p q r i k
