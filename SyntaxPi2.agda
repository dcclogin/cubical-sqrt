{-# OPTIONS --cubical #-}

module SyntaxPi2 where

open import Cubical.Core.Everything

infix  19 _⇔_
infix  18 _↔_
infixr 25 _⊙_
infixr 21 _▣_
infix 100 !₁_


data Π₂ : Type where
  𝟚 : Π₂


data _↔_ : (A B : Π₂) → Type where

  `id₁   : {A : Π₂} → (A ↔ A)
  `not   : 𝟚 ↔ 𝟚
  !₁_    : {A B : Π₂} → (A ↔ B) → (B ↔ A)
  _⊙_    : {A B C : Π₂} → (A ↔ B) → (B ↔ C) → (A ↔ C)
  sqrt   : {A : Π₂} → (c : A ↔ A) → (A ↔ A)



data _⇔_ : {A B : Π₂} (p q : A ↔ B) → Type where

  `id₂  : {A B : Π₂} {c : A ↔ B} → c ⇔ c
  !₂_   : {A B : Π₂} {p q : A ↔ B} → (p ⇔ q) → (q ⇔ p)
  _⊙₂_  : {A B : Π₂} {p q r : A ↔ B} → (p ⇔ q) → (q ⇔ r) → (p ⇔ r)

  !id₁  : {A : Π₂} → !₁ `id₁{A} ⇔ `id₁{A}
  !not  : !₁ `not ⇔ `not

  sqd   : {A : Π₂} {c : A ↔ A} → sqrt c ⊙ sqrt c ⇔ c
  sqf   : {A : Π₂} {c : A ↔ A} → sqrt (c ⊙ c) ⇔ sqrt c ⊙ sqrt c
  sqi   : {A : Π₂} {p q : A ↔ A} → (p ⇔ q) → sqrt p ⇔ sqrt q
  sqc   : {A : Π₂} {c : A ↔ A} → sqrt c ⊙ c ⇔ c ⊙ sqrt c -- derivable from assoc and sqd
  sq!   : {A : Π₂} {c : A ↔ A} → sqrt (!₁ c) ⇔ !₁ (sqrt c)

  idl⊙l : {A B : Π₂} {c : A ↔ B} → (`id₁ ⊙ c) ⇔ c
  idr⊙l : {A B : Π₂} {c : A ↔ B} → (c ⊙ `id₁) ⇔ c

  !r    : {A B : Π₂} (p : A ↔ B) → p ⊙ !₁ p ⇔ `id₁
  !l    : {A B : Π₂} (p : A ↔ B) → !₁ p ⊙ p ⇔ `id₁

  !!    : {A B : Π₂} {p : A ↔ B} → !₁ (!₁ p) ⇔ p
  `!    : {A B : Π₂} {p q : A ↔ B} → (p ⇔ q) → (!₁ p ⇔ !₁ q)

  assoc⊙l : {A B C D : Π₂} {p : A ↔ B} {q : B ↔ C} {r : C ↔ D}
          → (p ⊙ q) ⊙ r ⇔ p ⊙ (q ⊙ r)
  assoc⊙r : {A B C D : Π₂} {p : A ↔ B} {q : B ↔ C} {r : C ↔ D}
          → p ⊙ (q ⊙ r) ⇔ (p ⊙ q) ⊙ r

  _▣_   : {A B C : Π₂} {c₁ c₃ : A ↔ B} {c₂ c₄ : B ↔ C}
        → (c₁ ⇔ c₃) → (c₂ ⇔ c₄)
        -----------------------
        → (c₁ ⊙ c₂) ⇔ (c₃ ⊙ c₄)




-- equational reasoning of ⇔

_∎₂ : {A B : Π₂} → (c : A ↔ B) → c ⇔ c
c ∎₂ = `id₂

_⇔⟨_⟩_ : {A B : Π₂} → (c₁ : A ↔ B) → {c₂ c₃ : A ↔ B}
       → (c₁ ⇔ c₂) → (c₂ ⇔ c₃) → (c₁ ⇔ c₃)
c₁ ⇔⟨ p ⟩ q = p ⊙₂ q

_⇔⟨⟩_ : {A B : Π₂} → (c₁ : A ↔ B) → {c₂ : A ↔ B}
      → (c₁ ⇔ c₂) → (c₁ ⇔ c₂)
c₁ ⇔⟨⟩ q = c₁ ⇔⟨ `id₂ ⟩ q

infix 3 _∎₂
infixr 2 _⇔⟨_⟩_
infixr 2 _⇔⟨⟩_

-- example

cancel-not : `not ⊙ `not ⇔ `id₁
cancel-not =
  `not ⊙ `not      ⇔⟨ `id₂ ▣ (!₂ !not) ⟩
  `not ⊙ (!₁ `not) ⇔⟨ !r `not ⟩
  `id₁ ∎₂
