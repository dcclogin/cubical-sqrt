```agda
{-# OPTIONS --cubical #-}
```


Syntax of terms and types

```text
t,u,A,B := x | λx : A. t | t u | (x : A) → B        Π-types
         | (t, u) | t.1 | t.2 | (x : A) × B          Σ-types
         | 0 | s u | natrec t u | ℕ                  Natural numbers
         | <i> t | t r | Path A t u                  Path types
         | [φ₁ t₁, φ₂ t₂, ..., φₙ tₙ]                Systems
         | compⁱ A [φ ↦ u] a₀                       Compositions
```

Syntax of contexts

```text
Γ, Δ := () | Γ, x : A | Γ, i : 𝕀 | Γ, φ
```

Syntax of face formula

```text
φ, ψ := 0𝔽 | 1𝔽 | (i = 0) | (i = 1) | φ ∧ ψ | φ ∨ ψ
```



Derived operations

- `transp`
- `fill`
