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
    p : a ≡ b

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

A third way (using coercion, described in Evan's Thesis Page 50):

```agda
coe0→1 : ∀ {ℓ} (A : I → Type ℓ) → A i0 → A i1
coe0→1 A a = transp (λ i → A i) i0 a

!''_ : ∀ {ℓ} {A : Type ℓ} {a b : A} → a ≡ b → b ≡ a
!''_ {ℓ}{A}{a}{b} p = coe0→1 (λ i → p i ≡ a) refl
```


> Question 1 : Are these ways equivalent? In what sense?

> Question 2 : What's the relation between `coe0→1` and weak connections?






### Lemma 3.2.2 (Homogeneous composition)

For every type `A` and every `a, b, c : A`, there is a function `(Path A a b) → (Path A b c) → (Path A a c)`.

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

`compPath1` is definitionally equal to `compPath`:

```agda
_ : ∀ {ℓ} {A : Type ℓ} {a b c : A} {p : a ≡ b} {q : b ≡ c} → compPath1 p q ≡ compPath p q
_ = refl
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


### Lemma 4.1.2 (Join)

For every type `A` and `a, b : A`, there is an operation `_[_∨_] : (Path A a b) → I → I → A`.

```agda
_[_∨*_] : ∀ {ℓ} {A : Type ℓ} {a b : A} → (p : a ≡ b) → I → I → A
_[_∨*_] {ℓ}{A}{a}{b} p i j = hfill walls (inS (p i)) j
  where
    walls : ∀ (j : I) → Partial (~ i ∨ i) A
    walls j (i = i0) = p j
    walls j (i = i1) = b
```

```agda
_[_∨_] : ∀ {ℓ} {A : Type ℓ} {a b : A} → (p : a ≡ b) → I → I → A
_[_∨_] {ℓ}{A}{a}{b} p i j = hcomp walls a
  where
    walls : ∀ (k : I) → Partial (~ i ∨ ~ j) A
    walls k (i = i0) = p [ k ∧* j ]
    walls k (j = i0) = p [ k ∧* i ]
```


An alternative (and simpler) way to define connections (from 1lab.dev):

```agda
∧-conn : ∀ {ℓ} {A : Type ℓ} {a b : A} (p : a ≡ b) → PathP (λ i → a ≡ p i) refl p
∧-conn {ℓ}{A}{a}{b} p i j = p (i ∧ j)

∨-conn : ∀ {ℓ} {A : Type ℓ} {a b : A} (p : a ≡ b) → PathP (λ i → p i ≡ b) p refl
∨-conn {ℓ}{A}{a}{b} p i j = p (i ∨ j)
```

Or we can use `Square` instead of "path of paths":

```agda
-- Square [left] [right] [bottom] [top]
∧-conn' : ∀ {ℓ} {A : Type ℓ} {a b : A} (p : a ≡ b) → Square refl p refl p
∧-conn' {ℓ}{A}{a}{b} p i j = p (i ∧ j)

∨-conn' : ∀ {ℓ} {A : Type ℓ} {a b : A} (p : a ≡ b) → Square p refl p refl
∨-conn' {ℓ}{A}{a}{b} p i j = p (i ∨ j)
```


They can also be viewed as constructed from the diagonal `(p : a ≡ b)`. It's definitionally equal to two egdes:

```agda
_ : ∀ {ℓ} {A : Type ℓ} {a b : A} {p : a ≡ b} → (λ i → ∧-conn p i i) ≡ p
_ = refl

_ : ∀ {ℓ} {A : Type ℓ} {a b : A} {p : a ≡ b} → (λ i → ∨-conn p i i) ≡ p
_ = refl
```

But it's not definitionally equal in the first method:

```text
_ : ∀ {ℓ} {A : Type ℓ} {a b : A} {p : a ≡ b} → (λ i → p [ i ∧ i ]) ≡ p
_ = {!!}
```



## The groupoid laws

First, it's better to define fillers for `_∙∙_∙∙_` and `_∙_`:

```agda
∙∙-filler : ∀ {ℓ} {A : Type ℓ} {a b c d : A} (p : a ≡ b) (q : b ≡ c) (r : c ≡ d)
         → Square (sym p) r q (p ∙∙ q ∙∙ r)
∙∙-filler {ℓ}{A}{a}{b}{c} p q r i j = hfill walls (inS (q i)) j
  where
    walls : ∀ (j : I) → Partial (~ i ∨ i) A
    walls j (i = i0) = p (~ j)
    walls j (i = i1) = r j
```

```agda
∙-filler : ∀ {ℓ} {A : Type ℓ} {a b c : A} (p : a ≡ b) (q : b ≡ c)
         → Square refl q p (p ∙ q)
∙-filler {ℓ}{A}{a}{b}{c} p q i j = hfill walls (inS (p i)) j
  where
    walls : ∀ (j : I) → Partial (~ i ∨ i) A
    walls j (i = i0) = a
    walls j (i = i1) = q j
```

### Lemma 4.2.1 (Right unit)

For every `A` and every `a, b : A` we have a path `p ≡ p ∙ refl` where `p : a ≡ b`.

```agda
ru : ∀ {ℓ} {A : Type ℓ} {a b : A} {p : a ≡ b}
   → p ≡ p ∙ refl
ru {ℓ}{A}{a}{b}{p} j i = ∙-filler p refl i j
```

### Lemma 4.2.2 (Left unit)

For every `A` and every `a, b : A` we have a path `p ≡ refl ∙ p` where `p : a ≡ b`.

```agda
lu : ∀ {ℓ} {A : Type ℓ} {a b : A} {p : a ≡ b}
   → p ≡ refl ∙ p
lu {ℓ}{A}{a}{b}{p} j i = hcomp walls (p (~ j ∧ i))
  where
    walls : ∀ (k : I) → Partial (~ i ∨ i ∨ ~ j) A
    walls k (i = i0) = a
    walls k (i = i1) = p (~ j ∨ k)
    walls k (j = i0) = p i
```

### Lemma 4.2.3 (Right inverse w.r.t. concatenation)

For every `A` and every `a, b : A` we have a path `p ∙ (sym p) ≡ refl` where `p : a ≡ b`.

```agda
rc : ∀ {ℓ} {A : Type ℓ} {a b : A} {p : a ≡ b}
   → p ∙ (sym p) ≡ refl
rc {ℓ}{A}{a}{b}{p} j i = hcomp walls (p i)
  where
    walls : ∀ (k : I) → Partial (~ i ∨ i ∨ j) A
    walls k (i = i0) = a
    walls k (i = i1) = p (~ k)
    walls k (j = i1) = p (i ∧ ~ k)
```

### Lemma 4.2.4 (Left inverse w.r.t. concatenation)

For every `A` and every `a, b : A` we have a path `(sym p) ∙ p ≡ refl` where `p : a ≡ b`.

```agda
lc : ∀ {ℓ} {A : Type ℓ} {a b : A} {p : a ≡ b}
   → (sym p) ∙ p ≡ refl
lc {ℓ}{A}{a}{b}{p} j i = hcomp walls (p (~ i))
  where
    walls : ∀ (k : I) → Partial (~ i ∨ i ∨ j) A
    walls k (i = i0) = b
    walls k (i = i1) = p k
    walls k (j = i1) = p (~ i ∨ k)
```

### Lemma 4.2.5 (Path inversion is involutive)

For every `A` and every `a, b : A` we have a path `(sym (sym p) ≡ p` where `p : a ≡ b`.

```agda
inv : ∀ {ℓ} {A : Type ℓ} {a b : A} {p : a ≡ b}
    → (sym (sym p)) ≡ p
inv {ℓ}{A}{a}{b}{p} = refl
```

Using `hcomp`:

```text
-- has some error but I cannot figure out why
inv : ∀ {ℓ} {A : Type ℓ} {a b : A} {p : a ≡ b}
    → (sym (sym p)) ≡ p
inv {ℓ}{A}{a}{b}{p} j i = hcomp walls (p (~ j))
  where
    walls : ∀ (k : I) → Partial (~ i ∨ i ∨ j) A
    walls k (i = i0) = p (~ j ∧ ~ k)
    walls k (i = i1) = p (~ j ∨ k)
    walls k (j = i1) = p (i ∧ k)
```



### Lemma 4.2.6 (Associativity)

For every `A` and every `a, b, c, d : A`, we have a path `(p ∙ q) ∙ r ≡ p ∙ (q ∙ r)` where `p : a ≡ b` `q : b ≡ c` `r : c ≡ d`.

```agda
α-filler : ∀ {ℓ} {A : Type ℓ} {a b c d : A} (p : a ≡ b) (q : b ≡ c) (r : c ≡ d)
         → Square refl (q ∙ r) p (p ∙ (q ∙ r))
α-filler {ℓ}{A}{a}{b}{c}{d} p q r i j = hfill walls (inS (p i)) j
  where
    walls : ∀ j → Partial (~ i ∨ i) A
    walls j (i = i0) = a
    walls j (i = i1) = (q ∙ r) j
```

```agda
β-filler : ∀ {ℓ} {A : Type ℓ} {a b c d : A} (p : a ≡ b) (q : b ≡ c) (r : c ≡ d)
         → Square refl (q ∙ r) p ((p ∙ q) ∙ r)
β-filler {ℓ}{A}{a}{b}{c}{d} p q r i j = hcomp walls (∙-filler p q i j)
  where
    walls : ∀ k → Partial (~ j ∨ j ∨ ~ i ∨ i) A
    walls k (i = i0) = a
    walls k (i = i1) = ∙-filler q r j k
    walls k (j = i0) = p i
    walls k (j = i1) = ∙-filler (p ∙ q) r i k

```

```agda
assoc :  ∀ {ℓ} {A : Type ℓ} {a b c d : A} {p : a ≡ b} {q : b ≡ c} {r : c ≡ d}
       → (p ∙ q) ∙ r ≡ p ∙ (q ∙ r)
assoc {ℓ}{A}{a}{b}{c}{d}{p}{q}{r} j i = hcomp walls (p i)
  where
    walls : ∀ k → Partial (~ j ∨ j ∨ ~ i ∨ i) A
    walls k (i = i0) = a
    walls k (i = i1) = (q ∙ r) k
    walls k (j = i0) = β-filler p q r i k
    walls k (j = i1) = α-filler p q r i k
```


## The groupoid laws for **paths of types**

See [GroupoidLawsT.agda](https://github.com/dcclogin/cubical-sqrt/blob/main/GroupoidLawsT.agda).
