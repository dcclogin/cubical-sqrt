```agda
{-# OPTIONS --cubical #-}

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
```


## Syntax of the core language


### Syntax of `𝕀` elements

```text
r, s := 0 | 1 | i | 1 − r | r ∧ s | r ∨ s
```


### Syntax of terms and types

```text
t,u,A,B := x | λx : A. t | t u | (x : A) → B       Π-types
        | (t, u) | t.1 | t.2 | (x : A) × B          Σ-types
        | 0 | s u | natrec t u | ℕ                  Natural numbers
        | <i> t | t r | Path A t u                  Path types
        | [φ₁ t₁, φ₂ t₂, ..., φₙ tₙ]                Systems
        | compⁱ A [φ ↦ u] a₀                       Compositions
        | Glue [φ ↦ (T,f)] A                       Glue types
        | glue [φ ↦ t] u                           Glue term
        | unglue [φ ↦ f] u                         unglue term
```

### Syntax of contexts

```text
Γ, Δ := ()
     | Γ, x : A
     | Γ, i : 𝕀
     | Γ, φ              Restrictions
```

### Syntax of face formula

```text
φ, ψ := 0𝔽 | 1𝔽
     | (i = 0)
     | (i = 1)
     | φ ∧ ψ
     | φ ∨ ψ
```

Some operations can be defined with `comp` in the language:

- `transp`
- `fill`


## Composition

If `Γ, φ ⊢ u : A`, then `Γ ⊢ a : A[φ ↦ u]` means `Γ ⊢ a : A` **AND** `Γ, φ ⊢ a = u : A`.

It can be read as "in the restricted context `φ`, `a` agrees with `u`".
In other words, `a` is a evidence that `u` (defined on `φ`) is *extensible*.

Composition says extensibility of partial elements is preserved along paths.

```text
Γ ⊢ φ : 𝔽
Γ, (i : 𝕀) ⊢ A
Γ, φ, (i : 𝕀) ⊢ u : A
Γ ⊢ a₀ : A(i0) [φ ↦ u(i0)]
---------------------------------------------
Γ ⊢ compⁱ A [φ ↦ u] a₀ : A(i1) [φ ↦ u(i1)]
```

Here `u` is a **partial path**, while `u(i0)` and `u(i1)` are **partial elements**.

It can be easily translated into Cubical Agda code:

```agda
postulate
  comp' : ∀ {ℓ}
        → (A : ∀ i → Type ℓ)
        → (φ : I)
        → (u : ∀ i → Partial φ (A i))
        → A i0 [ φ ↦ u i0 ]
        -------------------------
        → A i1 [ φ ↦ u i1 ]
```

### Two special cases

1. When `φ = 1𝔽`, `u(i1)` becomes a "total element" (no context restrictions):
```text
Γ ⊢ compⁱ A [1𝔽 ↦ u] a₀ = u(i1) : A(i1)
```

2. When `φ = 0𝔽`, composition corresponds to transport:
```text
Γ ⊢ transpⁱ A a = compⁱ A [] a : A(i1)
```

In Cubical Agda, `transp` is primitive. Can we define our own `transp` with `comp`?


### Kan filling operation


```text
Γ, i : 𝕀 ⊢ fillⁱ A [φ ↦ u] a₀ = compʲ A(i/i∧j) [φ ↦ u(i/i∧j), (i=0) ↦ a₀] a₀ : A
```
Let

```text
Γ, i : 𝕀 ⊢ v = fillⁱ A [φ ↦ u] a₀ : A
```

`v` satisfies:

1. when `i=0`, it's just identity function.
```text
Γ ⊢ v(i0) = a₀ : A
```

2. when `i=1`, it's the "full composition".
```text
Γ ⊢ v(i1) = compⁱ A [φ ↦ u] a₀ : A(i1)
```


```agda
fill' : ∀ {ℓ}
      → (A : ∀ i → Type ℓ)
      → (φ : I)
      → (u : ∀ i → Partial φ (A i))
      → A i0 [ φ ↦ u i0 ]
      -------------------------------
      → (i : I) → A i
fill' A φ u a₀ i = outS (comp' A* (φ ∨ ~ i) u* (inS (outS a₀)))
  where
    A* : _
    A* = λ j → A (i ∧ j)

    u* : ∀ j → Partial (φ ∨ ~ i) _
    u* j (φ = i1) = u (i ∧ j) 1=1
    u* j (i = i0) = outS a₀

```



### Contractible types


Definition:

```text
isContr A = (x : A) × ((y : A) → Path A x y)
```

It can be interpreted as : there is an `x : A`, so that for every `y : A`, there is a path from `x` to `y`.


### Equivalence

Definition:

```text
isEquiv T A f = (y : A) → isContr ((x : T) × Path A y (f x))
Equiv T A = (f : T → A) × isEquiv T A f
```

### Glueing


Inference rules (`unglue b` for `unglue [φ ↦ f] b`):

```text
Γ ⊢ A
Γ, φ ⊢ T
Γ, φ ⊢ f : Equiv T A
------------------------
Γ ⊢ Glue [φ ↦ (T, f)] A
```


```text
Γ ⊢ b : Glue [φ ↦ (T, f)] A
----------------------------
Γ ⊢ unglue b : A [φ ↦ f b]
```


```text
Γ, φ ⊢ f : Equiv T A
Γ, φ ⊢ t : T
Γ ⊢ a : A [φ ↦ f t]
------------------------------------------
Γ ⊢ glue [φ ↦ t] a : Glue [φ ↦ (T, f)] A
```


```text
Γ ⊢ b : Glue [φ ↦ (T, f)] A
-------------------------------------------------------
Γ ‌⊢ b = glue [φ ↦ b] (unglue b) : Glue [φ ↦ (T, f)] A
```


```text
Γ, φ ⊢ f : Equiv T A
Γ, φ ⊢ t : T
Γ ⊢ a : A [φ ↦ f t]
------------------------------------------
Γ ⊢ unglue (glue [φ ↦ t] a) = a : A
```


Two special cases (when `φ = 1𝔽`, no restrictions):

```text
Γ ⊢ A
Γ ⊢ T
Γ ⊢ f : Equiv T A
-----------------------------
Γ ⊢ Glue [1𝔽 ↦ (T, f)] A = T
```

```text
Γ ⊢ f : Equiv T A
Γ ⊢ t : T
Γ ⊢ a = f t : A
-----------------------------
Γ ⊢ glue [1𝔽 ↦ t] a = t : T
```


Example:

```text
Γ, ⊢ B
Γ, (i=i0) ⊢ A
Γ, (i=i1) ⊢ B
Γ, (i=i0) ⊢ f : Equiv A B
Γ, (i=i1) ⊢ id : Equiv B B
------------------------------------------------
Γ ⊢ Glue [(i=i0) ↦ (A, f), (i=i1) ↦ (B, id)] B
```

Agda code.



## Examples


Let's prove `≡-trans` with the postulated `comp'`:

```agda
≡-trans : ∀ {ℓ} {A : Type ℓ} {a b c : A} → a ≡ b → b ≡ c → a ≡ c
≡-trans {ℓ}{A}{a}{b}{c} p q i = outS (comp' (λ _ → A) φ u (inS (p i)))
  where
    φ : I
    φ = ~ i ∨ i

    u : ∀ j → Partial φ _
    u j (i = i0) = a
    u j (i = i1) = q j
```

Let's prove `∙-filler` with `fill'`:

```agda
∙-filler : ∀ {ℓ} {A : Type ℓ} {a b c : A}
         → (p : a ≡ b)
         → (q : b ≡ c)
         --------------
         → Square refl q p (≡-trans p q)
∙-filler {ℓ}{A}{a}{b}{c} p q i j = fill' (λ _ → A) φ u (inS (p i)) j
  where
    φ : I
    φ = ~ i ∨ i

    u : ∀ j → Partial φ _
    u j (i = i0) = a
    u j (i = i1) = q j
```

All good!
