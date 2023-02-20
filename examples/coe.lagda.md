## Coercions, transport


```agda
{-# OPTIONS --cubical #-}

module coe where

open import Cubical.Core.Everything


private
  variable
    ℓ ℓ' : Level
    A B : Type ℓ
    x y : A
    C : A → Type ℓ
```


```agda
transport : A ≡ B → A → B
transport P a = transp (λ i → P i) i0 a
```

```agda
subst : x ≡ y → C x → C y
subst {C = C} p a = transp (λ i → C (p i)) i0 a
```


```agda
coe0→1 : (P : I → Type ℓ) → P i0 → P i1
coe0→1 P a = transp P i0 a

coe1→0 : (P : I → Type ℓ) → P i1 → P i0
coe1→0 P b = transp (λ i → P (~ i)) i0 b
```
