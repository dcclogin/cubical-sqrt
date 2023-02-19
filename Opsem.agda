{-# OPTIONS --cubical #-}

{--

Operational semantics of sqrt{Pi}

Can we compile to circuits?

Sums of roots; connections to QFT; connections to HoTT


--}

module Opsem where

open import Cubical.Core.Everything
open import Cubical.Data.Bool
open import Cubical.Data.Prod

-- Baby Pi with sqrt

data U : SSet where
  𝟚 : U

⟦_⟧ : U → Type
⟦ 𝟚 ⟧ = Bool

data _⟷_ : U → U → SSet where
  `id      : 𝟚 ⟷ 𝟚 
  `not     : 𝟚 ⟷ 𝟚 
  _⊙_      : ∀ {A B C} → (A ⟷ B) → (B ⟷ C) → (A ⟷ C)
  sqrt     : ∀ {A} → (A ⟷ A) → (A ⟷ A)
  `sqrtNot  : ∀ {A} → (A ⟷ A)
  
-- sqrt c ◎ sqrt c = c

  
{--
evalF : ∀ {A B} → (A ⟷ B) → ⟦ A ⟧ → ⟦ B ⟧
evalF `id v = v
evalF `not b = not b
evalF (c₁ ⊙ c₂) v = evalF c₂ (evalF c₁ v)
evalF (sqrt c) v = ?

-----

partialBool : ∀ i → Bool → Bool → Partial (i ∨ ~ i) Bool
partialBool i b1 b2 (i = i0) = b1
partialBool i b1 b2 (i = i1) = b2

-- sqrt : ∀ {A} → (⟦ A ⟧ → ⟦ A ⟧) → Σ (λ i → Partial i ⟦ A ⟧)
-- sqrt = ?

evalP : ∀ {A B} → (i : I) → (A ⟷ B) → ⟦ A ⟧ → Partial (i ∨ ~ i) ⟦ B ⟧ 
evalP i `id b = partialBool i b b 
evalP i `not b =  partialBool i (not b) (not b)
evalP i `sqrtNot b = partialBool i b (not b)
evalP i (c₁ ⊙ c₂) b = {!!}
--}
