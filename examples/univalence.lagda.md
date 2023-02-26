```agda
{-# OPTIONS --cubical #-}

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Isomorphism renaming (Iso to _≅_)
```

```agda
private
  variable
    ℓ : Level
    A B C : Type ℓ
```



```agda
open _≅_

≅-trans : A ≅ B → B ≅ C → A ≅ C
≅-trans {A = A}{C = C} c₁ c₂ = iso f g sec rtr
  where
    f : A → C
    g : C → A
    f a = (fun c₂ ∘ fun c₁) a
    g c = (inv c₁ ∘ inv c₂) c

    sec : ∀ c → f (g c) ≡ c
    sec c = cong (fun c₂) (rightInv c₁ (inv c₂ c)) ∙ (rightInv c₂ c)

    rtr : ∀ a → g (f a) ≡ a
    rtr a = cong (inv c₁) (leftInv c₂ (fun c₁ a)) ∙ (leftInv c₁ a)
```


```agda
≃-trans : A ≃ B → B ≃ C → A ≃ C
≃-trans e₁ e₂ = {!!}
```


```agda
≡-trans : A ≡ B → B ≡ C → A ≡ C
≡-trans {A = A} p q i = hcomp walls (p i)
  where
    walls : ∀ j → Partial (~ i ∨ i) _
    walls j (i = i0) = A
    walls j (i = i1) = q j
```


```agda
module iso-to-path where private
  way1 : ∀ {ℓ} {A B C : Type ℓ} → A ≅ B → B ≅ C → A ≡ C
  way2 : ∀ {ℓ} {A B C : Type ℓ} → A ≅ B → B ≅ C → A ≡ C

  way1 c₁ c₂ = isoToPath (≅-trans c₁ c₂)
  way2 c₁ c₂ = ≡-trans (isoToPath c₁) (isoToPath c₂)

  coherence : (c₁ : A ≅ B) (c₂ : B ≅ C) → way1 c₁ c₂ ≡ way2 c₁ c₂
  coherence c₁ c₂ = {!!}
```
