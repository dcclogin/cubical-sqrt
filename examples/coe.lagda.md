# Coercion


```agda
{-# OPTIONS --cubical #-}

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude


private
  variable
    ℓ ℓ' : Level
    A B : Type ℓ
    x y : A
    C : A → Type ℓ
```


```text
transport : A ≡ B → A → B
transport P a = transp (λ i → P i) i0 a
```

```text
subst : x ≡ y → C x → C y
subst {C = C} p a = transp (λ i → C (p i)) i0 a
```


```agda
coe0→1 : (P : I → Type ℓ) → P i0 → P i1
coe0→1 P a = transp P i0 a

coe1→0 : (P : I → Type ℓ) → P i1 → P i0
coe1→0 P b = transp (λ i → P (~ i)) i0 b
```


```agda
cancel-coe : (P : I → Type ℓ) → ∀ a → (coe1→0 P (coe0→1 P a)) ≡ a
cancel-coe P a = {!!}
```
