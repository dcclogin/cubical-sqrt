```agda
{-# OPTIONS --cubical #-}

open import Cubical.Core.Everything
open import Cubical.Foundations.CartesianKanOps
```


## Syntax of the core language

```text
exp := ...
    | coe r⇝r' A a
```


## Scratch


UIP:

```text
A ∈ Type ℓ
a b ∈ A
p q ∈ a ≡ b
------------
UIP₁ ∈ p ≡ q
```

2DTT:

```text
A ∈ Type ℓ
a b ∈ A
p q ∈ a ≡ b
u v ∈ p ≡ q
------------
UIP₂ ∈ u ≡ v
```
