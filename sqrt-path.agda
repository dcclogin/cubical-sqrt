{-# OPTIONS --cubical #-}

module sqrt-path where

open import Cubical.Core.Everything
open import Cubical.Foundations.Function
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Transport
open import Data.Product hiding (Σ-syntax)
open import Cubical.Foundations.Isomorphism renaming (Iso to _≅_)

postulate
  magic : ∀ {ℓ : Level} {X : Type ℓ} → X

private
  variable
    ℓ ℓ' ℓ'' : Level
    A B C D : Type ℓ
    a x y z w : A
    b : B
    φ : I


refl : {x : A} → x ≡ x
refl {x = x} = λ i → x

_∙_ : {x y z : A} → x ≡ y → y ≡ z → x ≡ z
_∙_ {A = A} {x = x} p q j = hcomp (λ i → λ { (j = i0) → x ; (j = i1) → q i }) (p j)
infixr 80 _∙_

!_ : {x y : A} → x ≡ y → y ≡ x
!_ p i = p (~ i)
infixr 100 !_




transport : ∀ {ℓ} {A B : Type ℓ} → A ≡ B → A → B
transport p a = transp (λ i → p i) i0 a
-- f = (λ x → f x)

transport-refl : ∀ {ℓ} {A : Type ℓ} (x : A) → transport refl x ≡ x
transport-refl {A = A} x i = transp (λ _ → A) i x
-- transp (λ i → A) i0 x ≡ transp (λ i → A) i1 x

transport-fill : ∀ {ℓ} {A B : Type ℓ} (p : A ≡ B) (a : A) → PathP (λ i → p i) a (transport p a)
transport-fill p a i = transp (λ j → p (i ∧ j)) (~ i) a
-- i ? 0 --> 0
-- i ? 1 --> i



-- maybe bad names
pull : ∀ {ℓ} (A : I → Type ℓ) (i : I) → A i → A i1
pull A i a = transp (λ j → A (i ∨ j)) i a
-- i ? 0 --> i
-- i ? 1 --> 1

pull' : ∀ {ℓ} (A : I → Type ℓ) (i : I) → A i1 → A i
pull' A i a = transp (λ j → A (i ∨ ~ j)) i a
-- i ? 1 --> 1
-- i ? 0 --> i

push : ∀ {ℓ} (A : I → Type ℓ) (i : I) → A i0 → A i
push A i a = transp (λ j → A (i ∧ j)) (~ i) a
-- i ? 0 --> 0
-- i ? 1 --> i

push' : ∀ {ℓ} (A : I → Type ℓ) (i : I) → A i → A i0
push' A i a = transp (λ j → A (i ∧ ~ j)) (~ i) a
-- i ? 1 --> i
-- i ? 0 --> 0

tripA→ : ∀ {ℓ} (A : I → Type ℓ) (i : I) → A i0 → A i1
tripA→ A i = pull A i ∘ push A i

tripA← : ∀ {ℓ} (A : I → Type ℓ) (i : I) → A i1 → A i0
tripA← A i = push' A i ∘ pull' A i



sqrt→ : ∀ {ℓ} {A B : Type ℓ} (p : A ≡ B) (i : I)
      → (p i0 → p i) × (p i → p i1)
sqrt→ p i = (λ a → transp (λ j → p (i ∧ j)) (~ i) a)
          , (λ a → transp (λ j → p (i ∨ j)) i a)

sqrt← : ∀ {ℓ} {A B : Type ℓ} (p : A ≡ B) (i : I)
      → (p i1 → p i) × (p i → p i0)
sqrt← p i = (λ b → transp (λ j → p (i ∨ ~ j)) i b)
          , (λ b → transp (λ j → p (i ∧ ~ j)) (~ i) b)


trip→ : ∀ {ℓ} {A B : Type ℓ} (p : A ≡ B) (i : I) → A → B
trip→ p i = snd (sqrt→ p i) ∘ fst (sqrt→ p i)

trip← : ∀ {ℓ} {A B : Type ℓ} (p : A ≡ B) (i : I) → B → A
trip← p i = snd (sqrt← p i) ∘ fst (sqrt← p i)



-- see Cubical.Foundations.CartesianKanOps
-- need heterogeneous fill
seg : ∀ {ℓ} {A B : Type ℓ} (p : A ≡ B) (i j : I) → (p i → p j)
seg p i j = {!!}

seg≡ : ∀ {ℓ} {A B : Type ℓ} (p : A ≡ B) (i j : I) → (p i ≡ p j)
seg≡ p i j = {!!}




-- rename transpEquiv from Cubical.Foundations.Transport
pulle : ∀ {ℓ} {A B : Type ℓ} (p : A ≡ B) (i : I) → p i ≃ p i1
pulle P i .fst = transp (λ j → P (i ∨ j)) i
pulle P i .snd
  = transp (λ k → isEquiv (transp (λ j → P (i ∨ (j ∧ k))) (i ∨ ~ k)))
      i (idIsEquiv (P i))

-- similar but for isomorphism ≅
pulli : ∀ {ℓ} {A B : Type ℓ} (p : A ≡ B) (i : I) → p i ≅ p i1
pulli P i = iso f g sec rtr
  where
    f : P i → P i1
    f x = transp (λ j → P (i ∨ j)) i x

    g : P i1 → P i
    g x = transp (λ j → P (i ∨ ~ j)) i x

    sec : ∀ x → f (g x) ≡ x
    sec x = magic

    rtr : ∀ x → g (f x) ≡ x
    rtr x = magic
    

pushe : ∀ {ℓ} {A B : Type ℓ} (p : A ≡ B) (i : I) → p i0 ≃ p i
pushe P i .fst = transp (λ j → P (i ∧ j)) (~ i)
pushe P i .snd = magic

pushi : ∀ {ℓ} {A B : Type ℓ} (p : A ≡ B) (i : I) → p i0 ≅ p i
pushi P i = magic



-- proof with ua
pullp : ∀ {ℓ} {A B : Type ℓ} (p : A ≡ B) (i : I)
      → p i ≡ p i1
pullp p i = ua (pulle p i)

pushp : ∀ {ℓ} {A B : Type ℓ} (p : A ≡ B) (i : I)
      → p i0 ≡ p i
pushp p i = ua (pushe p i)

sqrt≡ : ∀ {ℓ} {A B : Type ℓ} (p : A ≡ B) (i : I)
      → (p i0 ≡ p i) × (p i ≡ p i1)
sqrt≡ p i = pushp p i , pullp p i


trip≡ : ∀ {ℓ} {A B : Type ℓ} (p : A ≡ B) (i : I) → A ≡ B
trip≡ p i = fst (sqrt≡ p i) ∙ snd (sqrt≡ p i)


