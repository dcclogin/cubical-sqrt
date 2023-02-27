```agda
{-# OPTIONS --cubical #-}

open import Cubical.Data.Bool
open import Cubical.Core.Everything
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism

private
  variable
    ℓ : Level
    A B C : Type ℓ

```

> What's the difference between `Iso` and `_≃_`? Why choose `_≃_` for univalence?


### Derive `ua` from `Glue`

```agda
ua : A ≃ B → A ≡ B
ua {A = A}{B = B} e i = Glue B walls
  where
    walls : Partial (~ i ∨ i) (Σ[ T ∈ _ ] T ≃ B)
    walls (i = i0) = A , e
    walls (i = i1) = B , idEquiv B
```


### Generalized version

```agda
ua-g : A ≃ B → C ≃ B → A ≡ C
ua-g {A = A}{B = B}{C = C} ea ec i = Glue B walls
  where
    walls : Partial (~ i ∨ i) (Σ[ T ∈ _ ] T ≃ B)
    walls (i = i0) = A , ea
    walls (i = i1) = C , ec
```

It looks like transitivity of `_≃_` but one of two equivalences is inverted.
See [Cubical.Foundations.Equiv](https://github.com/agda/cubical/blob/master/Cubical/Foundations/Equiv.agda).


### Curious ones

```agda
ua-t12 : A ≃ A → A ≃ A → A ≡ A
ua-t12 {A = A} e₁ e₂ i = Glue A walls
  where
    walls : Partial (~ i ∨ i) _
    walls (i = i0) = A , e₁
    walls (i = i1) = A , e₂

ua-t21 : A ≃ A → A ≃ A → A ≡ A
ua-t21 {A = A} e₁ e₂ i = Glue A walls
  where
    walls : Partial (~ i ∨ i) _
    walls (i = i0) = A , e₂
    walls (i = i1) = A , e₁
```

Define `notPath` and then use `ua-t12`, `ua-t21` to get the roof path:

```agda
notPath : Bool ≡ Bool
notPath = isoToPath (iso not not rem rem)
  where
    rem : ∀ b → not (not b) ≡ b
    rem true  = λ _ → true
    rem false = λ _ → false
```
