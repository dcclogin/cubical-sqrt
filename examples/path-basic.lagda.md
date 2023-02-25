```agda
{-# OPTIONS --cubical #-}

open import Cubical.Core.Everything
```

```agda
∂ : I → I
∂ i = ~ i ∨ i
```

## Reflexive

```agda
refl : ∀ {ℓ} {A : Type ℓ} {a : A} → a ≡ a
refl {ℓ}{A}{a} i = hcomp walls a
  where
    walls : ∀ j → Partial (∂ i) A
    walls j (i = i0) = a
    walls j (i = i1) = a
```

## Symmetric

```agda
symm₁ symm₂ symm₃ : ∀ {ℓ} {A : Type ℓ} {a b : A} → a ≡ b → b ≡ a
symm₁ {ℓ}{A}{a}{b} p i = hcomp walls a
  where
    walls : ∀ j → Partial (∂ i) A
    walls j (i = i0) = p j
    walls j (i = i1) = a

symm₂ {ℓ}{A}{a}{b} p i = hcomp walls (p i)
  where
    walls : ∀ j → Partial (∂ i) A
    walls j (i = i0) = p j
    walls j (i = i1) = p (~ j)

symm₃ {ℓ}{A}{a}{b} p i = hcomp walls b
  where
    walls : ∀ j → Partial (∂ i) A
    walls j (i = i0) = b
    walls j (i = i1) = p (~ j)
```

## Transitive

```agda
_∙∙_∙∙_ : ∀ {ℓ} {A : Type ℓ} {a b c d : A} → a ≡ b → b ≡ c → c ≡ d → a ≡ d
_∙∙_∙∙_ {ℓ}{A}{a}{b}{c}{d} p q r i = hcomp walls (q i)
  where
    walls : ∀ j → Partial (∂ i) A
    walls j (i = i0) = p (~ j)
    walls j (i = i1) = r j


trans₁ trans₂ trans₃ : ∀ {ℓ} {A : Type ℓ} {a b c : A} → a ≡ b → b ≡ c → a ≡ c
trans₁ {ℓ}{A}{a}{b}{c} p q = refl ∙∙ p ∙∙ q
trans₂ {ℓ}{A}{a}{b}{c} p q = p ∙∙ refl ∙∙ q
trans₃ {ℓ}{A}{a}{b}{c} p q = p ∙∙ q ∙∙ refl
```
