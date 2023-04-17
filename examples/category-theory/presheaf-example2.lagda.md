```agda
open import Level renaming (suc to ℓ-suc)
open import Categories.Category
open import Categories.Category.Instance.Sets
open import Categories.Functor
open import Categories.Functor.Presheaf
open import Relation.Binary.Core
open import Relation.Binary.Structures
open import Relation.Binary.Definitions
open import Relation.Binary.PropositionalEquality
open import Data.Empty
open import Data.Unit
open import Data.Nat.Base
open import Data.Fin.Base
```

Example category □ - category of cubes

collection of objects
```agda
□-Obj = ℕ
```

collection of morphisms
```agda
infix 4 _⇒□_
infixr 9 _⊙_

data _⇒□_ : ℕ → ℕ → Set 0ℓ where
  id□ : ∀ {n} → n ⇒□ n
  δ    : ∀ {n} → (i : Fin (suc (suc n))) → n ⇒□ (suc n)
  σ    : ∀ {n} → (i : Fin (suc n)) → (suc n) ⇒□ n
  _⊙_  : ∀ {l m n} → m ⇒□ n → l ⇒□ m → l ⇒□ n
```


```agda
--- ???
face : ∀ {n} → (i : Fin (suc (suc n))) → Fin n → Fin (suc n)
face i = {!!}

degen : ∀ {n} → (i : Fin (suc n)) → Fin (suc n) → Fin n
degen {0} i j = {!!}
degen {suc n} i j = {!!}
```


```agda
⟦_⟧ : ∀ {m n} → m ⇒□ n → (Fin m → Fin n)
⟦ id□ ⟧ x = x
⟦ δ i ⟧ x = face i x
⟦ σ i ⟧ x = degen i x
⟦ f ⊙ g ⟧ x = ⟦ f ⟧ (⟦ g ⟧ x)
```

```agda
record _≈□_ {m n} (f g : m ⇒□ n) : Set where
  constructor □-eq
  field
    □-pointwise : ∀ {x} → ⟦ f ⟧ x ≡ ⟦ g ⟧ x

open _≈□_ public
```

```agda
□ : Category 0ℓ 0ℓ 0ℓ
□ = record
      { Obj = □-Obj
      ; _⇒_ = _⇒□_
      ; _≈_ = _≈□_
      ; id = id□
      ; _∘_ = _⊙_
      ; assoc = □-eq refl
      ; sym-assoc = □-eq refl
      ; identityˡ = □-eq refl
      ; identityʳ = □-eq refl
      ; identity² = □-eq refl
      ; equiv = record
        { refl = □-eq refl
        ; sym = λ eq → □-eq (sym (□-pointwise eq))
        ; trans = λ eq₁ eq₂ → □-eq (trans (□-pointwise eq₁) (□-pointwise eq₂)) }
      ; ∘-resp-≈ = λ {_ _ _ f g h i} eq₁ eq₂
                   → □-eq (trans (cong ⟦ f ⟧ (□-pointwise eq₂)) (□-pointwise eq₁))
      }
```


```agda
□₁-F₀ : Category.Obj (Category.op □) → Category.Obj (Sets 0ℓ)
□₁-F₀ n = n ⇒□ 1

□₁-F₁ : {A B : Category.Obj (Category.op □)}
      → Category.op □ [ A , B ]
      → Sets 0ℓ [ □₁-F₀ A , □₁-F₀ B ]
□₁-F₁ {0} {0} id□ x₁ = {!!}
□₁-F₁ {0} {0} (x ⊙ x₂) x₁ = {!!}
□₁-F₁ {0} {suc B} x x₁ = {!!}
□₁-F₁ {suc A} {B} x x₁ = {!!}
```

```agda
□₁ : Presheaf □ (Sets 0ℓ)
□₁ = record
       { F₀ = □₁-F₀
       ; F₁ = {!!}
       ; identity = {!!}
       ; homomorphism = {!!}
       ; F-resp-≈ = {!!}
       }
```
