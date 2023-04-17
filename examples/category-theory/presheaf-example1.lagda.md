```agda
open import Level
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
```

Example category ■ - category of cubes (2 dimensions only)

collection of objects
```agda
data ■-Obj : Set 0ℓ where
  [0] [1] : _
```

collection of morphisms
```agda
data [0]to[0] : Set 0ℓ where
  id[0] : _

data [0]to[1] : Set 0ℓ where
  f₀ f₁ : _

data [1]to[0] : Set 0ℓ where
  d : _

data [1]to[1] : Set 0ℓ where
  id[1] : _

_⇒■_ : Rel ■-Obj 0ℓ
[0] ⇒■ [0] = [0]to[0]
[0] ⇒■ [1] = [0]to[1]
[1] ⇒■ [0] = [1]to[0]
[1] ⇒■ [1] = [1]to[1]
```


```agda
_≈■_ : ∀ {A B} → Rel (A ⇒■ B) 0ℓ
_≈■_ {A}{B} x y = (x ≡ y)

≈■-refl : ∀ {A B} → Reflexive (_≈■_ {A}{B})
≈■-refl = refl

≈■-symm : ∀ {A B} → Symmetric (_≈■_ {A}{B})
≈■-symm {A} {B} refl = refl

≈■-trans : ∀ {A B} → Transitive (_≈■_ {A}{B})
≈■-trans {A} {B} refl refl = refl
```



```agda
■-id : ∀ {A} → (A ⇒■ A)
■-id {[0]} = id[0]
■-id {[1]} = id[1]

■-comp : ∀ {A B C} → (B ⇒■ C) → (A ⇒■ B) → (A ⇒■ C)
■-comp {[0]} {[0]} {[0]} id[0] id[0] = id[0]
■-comp {[0]} {[0]} {[1]} f id[0] = f
■-comp {[0]} {[1]} {[0]} d f₀ = {!!}
■-comp {[0]} {[1]} {[0]} d f₁ = {!!}
■-comp {[0]} {[1]} {[1]} id[1] f = f
■-comp {[1]} {[0]} {[0]} id[0] d = d
■-comp {[1]} {[0]} {[1]} f₀ d = {!!}
■-comp {[1]} {[0]} {[1]} f₁ d = {!!}
■-comp {[1]} {[1]} {[0]} d id[1] = d
■-comp {[1]} {[1]} {[1]} id[1] id[1] = id[1]
```

seems imposible to define this category in this way...
