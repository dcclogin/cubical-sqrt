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



Operations that can be defined in the language

- `transp`
- `fill`



```agda

```


## Composition

If `Γ, φ ⊢ u : A`, then `Γ ⊢ a : A[φ ↦ u]` means `Γ ⊢ a : A` **AND** `Γ, φ ⊢ a ≡ u : A`.

Composition says extensibility of partial elements is preserved along paths. But What does it mean for a partial element to be "extensible"?


```text
Γ ⊢ φ : 𝔽
Γ, (i : 𝕀) ⊢ A
Γ, φ, (i : 𝕀) ⊢ u : A
Γ ⊢ a₀ : A(i0) [φ ↦ u(i0)]
---------------------------------------------
Γ ⊢ compⁱ A [φ ↦ u] a₀ : A(i1) [φ ↦ u(i1)]
```

Here `u` is a *partial path*, while `u(i0)` and `u(i1)` are *partial elements*.

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

When `φ = 1𝔽`, u(i1) becomes a "total element" (no context restrictions):

```text
Γ ⊢ compⁱ A [1𝔽 ↦ u] a₀ = u(i1) : A(i1)
```

When `φ = 0𝔽`, composition corresponds to transport:

```text
Γ ⊢ transpⁱ A a = compⁱ A [] a : A(i1)
```

In Cubical Agda, `transp` is primitive. Can we define our own `transp` with `comp`?
