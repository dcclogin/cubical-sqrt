## Examples from Naive Cubical Type Theory


```agda
{-# OPTIONS --cubical #-}

module hcomp-hfill where

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude


private
  variable
    ℓ ℓ' : Level
    A B : Type ℓ
    X : A → Type ℓ
    a b : A

```


### Lemma 2.3.1

For every type A and every a : A, there exists a path `(Path A a a)` called the reflexivity path of `a` and denoted `reflₐ`

```agda
refl' : (a : A) → Path A a a
refl' a = λ _ → a
```

### Lemma 2.3.2

Given a function `f : A → B` and terms `a, b : A`, we have an operation `ap(f) : (Path A a b) → (Path B (f a) (f b))`

```agda
ap : (f : A → B) → (Path A a b) → (Path B (f a) (f b))
ap f p = λ i → f (p i)
```

```agda
refl-pres : (f : A → B) → ap f (refl' a) ≡ refl' (f a)
refl-pres {a = a} f = λ i → (λ _ → f a)
```


### Theorem 2.3.3 (Function extensionality)

```agda
funext : (f g : A → B) → ((a : A) → f a ≡ g a) → f ≡ g
funext f g H = λ i → (λ a → H a i)


funextP : (f g : (a : A) → X a) → ((a : A) → f a ≡ g a) → f ≡ g
funextP f g H = λ i → (λ a → H a i)
```




### Lemma 3.2.1 (Inverse)

For every type `A` and every `a, b : A`, there is a inverse function `(Path A a b) → (Path A b a)`.

```agda
!_ : ∀ {ℓ} {A : Type ℓ} {a b : A} → a ≡ b → b ≡ a
!_ {ℓ}{A}{a}{b} p i = hcomp walls a
  where
    walls : ∀ (j : I) → Partial (~ i ∨ i) A
    walls j (i = i0) = p j
    walls j (i = i1) = a
```

An alternative (and simpler) way to define inverse:
```agda
!'_ : ∀ {ℓ} {A : Type ℓ} {a b : A} → a ≡ b → b ≡ a
!'_ {ℓ}{A}{a}{b} p = λ i → p (~ i)
```

Another alternative way (using coercion, described in Evan's Thesis Page 50):

```agda
coe0→1 : ∀ {ℓ} (A : I → Type ℓ) → A i0 → A i1
coe0→1 A a = transp (λ i → A i) i0 a

!''_ : ∀ {ℓ} {A : Type ℓ} {a b : A} → a ≡ b → b ≡ a
!''_ {ℓ}{A}{a}{b} p = coe0→1 (λ i → p i ≡ a) refl
```


> Question : Are these ways equivalent? In what sense?






### Lemma 3.2.2 (Homogeneous composition)

For every type `A` and every `a, b, c : A`, there is a function `(Path A a b)` → `(Path A b c)` → `(Path A a c)`.

```agda
compPath : ∀ {ℓ} {A : Type ℓ} {a b c : A} → a ≡ b → b ≡ c → a ≡ c
compPath {ℓ}{A}{a}{b}{c} p q i = hcomp walls (p i)
  where
    walls : ∀ (j : I) → Partial (~ i ∨ i) A
    walls j (i = i0) = a
    walls j (i = i1) = q j
```

There are at least one alternative ways to define homogeneous composition. To do that we first define a "double composition" operation:

```text
_∙∙_∙∙_ : ∀ {ℓ} {A : Type ℓ} {x y z w : A} → x ≡ y → y ≡ z → z ≡ w → x ≡ w
_∙∙_∙∙_ {ℓ}{A}{x}{y}{z}{w} p q r i = hcomp walls (q i)
  where
    walls : ∀ (j : I) → Partial (~ i ∨ i) A
    walls j (i = i0) = (! p) j  -- or p (~ j)
    walls j (i = i1) = r j
```

And then set one of `p`, `q`, and `r` to `refl`:

```agda

compPath1 : ∀ {ℓ} {A : Type ℓ} {a b c : A} → a ≡ b → b ≡ c → a ≡ c
compPath1 {ℓ}{A}{a}{b}{c} p q = refl ∙∙ p ∙∙ q

compPath2 : ∀ {ℓ} {A : Type ℓ} {a b c : A} → a ≡ b → b ≡ c → a ≡ c
compPath2 {ℓ}{A}{a}{b}{c} p q = p ∙∙ refl ∙∙ q

compPath3 : ∀ {ℓ} {A : Type ℓ} {a b c : A} → a ≡ b → b ≡ c → a ≡ c
compPath3 {ℓ}{A}{a}{b}{c} p q = p ∙∙ q ∙∙ refl
```






## Weak connections

### Lemma 4.1.1 (Meet)

For every type `A` and `a, b : A`, there is an operation `_[_∧_] : (Path A a b) → I → I → A`.

```agda
_[_∧*_] : ∀ {ℓ} {A : Type ℓ} {a b : A} → (p : a ≡ b) → I → I → A
_[_∧*_] {ℓ}{A}{a}{b} p i j = hfill walls (inS a) j
  where
    walls : ∀ (j : I) → Partial (~ i ∨ i) A
    walls j (i = i0) = a
    walls j (i = i1) = p j
```

```agda
_[_∧_] : ∀ {ℓ} {A : Type ℓ} {a b : A} → (p : a ≡ b) → I → I → A
_[_∧_] {ℓ}{A}{a}{b} p i j = hcomp walls a
  where
    walls : ∀ (k : I) → Partial (~ i ∨ i ∨ ~ j ∨ j) A
    walls k (i = i0) = a
    walls k (i = i1) = p [ j ∧* k ]
    walls k (j = i0) = a
    walls k (j = i1) = p [ i ∧* k ]
```
