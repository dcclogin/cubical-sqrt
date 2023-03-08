```agda
{-# OPTIONS --cubical #-}

open import Cubical.Core.Everything
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
