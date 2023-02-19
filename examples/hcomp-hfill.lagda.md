```agda
{-# OPTIONS --cubical #-}

module hcomp-hfill where

open import Cubical.Core.Everything


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

Given a function `f : A → B` and terms `a, b : A`, we have an operation `ap(f) : (Path A a b) → (Path B (f a) (f b))``

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
