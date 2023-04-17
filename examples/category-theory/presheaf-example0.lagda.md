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


Example category G - vertex and edge


collection of objects
```agda
data GObj : Set 0ℓ where
  V E : _
```

collections of morphisms
```agda
data EtoV : Set 0ℓ where

data VtoE : Set 0ℓ where
  s t : _

data VtoV : Set 0ℓ where
  idV : _

data EtoE : Set 0ℓ where
  idE : _


_⇒G_ : Rel GObj 0ℓ
V ⇒G V = VtoV
V ⇒G E = VtoE
E ⇒G V = EtoV
E ⇒G E = EtoE
```

```agda
_≈G_ : {A B : GObj} → Rel (A ⇒G B) 0ℓ
_≈G_ {V} {V} idV idV = ⊤
_≈G_ {V} {E} s s = ⊤
_≈G_ {V} {E} s t = ⊥
_≈G_ {V} {E} t s = ⊥
_≈G_ {V} {E} t t = ⊤
_≈G_ {E} {E} idE idE = ⊤

≈G-refl : {A B : GObj} → Reflexive (_≈G_ {A}{B})
≈G-refl {V} {V} {idV} = tt
≈G-refl {V} {E} {s} = tt
≈G-refl {V} {E} {t} = tt
≈G-refl {E} {E} {idE} = tt

≈G-symm : {A B : GObj} → Symmetric (_≈G_ {A}{B})
≈G-symm {V} {V} {x = idV} {y = idV} a = tt
≈G-symm {V} {E} {x = s} {y = s} a = tt
≈G-symm {V} {E} {x = t} {y = t} a = tt
≈G-symm {E} {E} {x = idE} {y = idE} a = tt

≈G-trans : {A B : GObj} → Transitive (_≈G_ {A}{B})
≈G-trans {V} {V} {idV} {idV} {idV} x y = tt
≈G-trans {V} {E} {s} {s} {s} x y = tt
≈G-trans {V} {E} {t} {t} {t} x y = tt
≈G-trans {E} {E} {idE} {idE} {idE} x y = tt
```


```agda
Gid : {A : GObj} → A ⇒G A
Gid {V} = idV
Gid {E} = idE
```

```agda
-- ???
Gcomp : {A B C : GObj} → (B ⇒G C) → (A ⇒G B) → (A ⇒G C)
Gcomp {V} {V} {V} idV idV = idV
Gcomp {V} {V} {E} f idV = f
Gcomp {V} {E} {E} idE g = g
Gcomp {E} {E} {E} idE idE = idE
```


```agda
assoc-G : {A B C D : GObj} {f : A ⇒G B} {g : B ⇒G C} {h : C ⇒G D}
        → Gcomp (Gcomp h g) f ≈G Gcomp h (Gcomp g f)
assoc-G {V} {V} {V} {V} {idV} {idV} {idV} = tt
assoc-G {V} {V} {V} {E} {idV} {idV} {s} = tt
assoc-G {V} {V} {V} {E} {idV} {idV} {t} = tt
assoc-G {V} {V} {E} {E} {idV} {s} {idE} = tt
assoc-G {V} {V} {E} {E} {idV} {t} {idE} = tt
assoc-G {V} {E} {E} {E} {s} {idE} {idE} = tt
assoc-G {V} {E} {E} {E} {t} {idE} {idE} = tt
assoc-G {E} {E} {E} {E} {idE} {idE} {idE} = tt

sym-assoc-G : {A B C D : GObj} {f : A ⇒G B} {g : B ⇒G C} {h : C ⇒G D}
            → Gcomp h (Gcomp g f) ≈G Gcomp (Gcomp h g) f
sym-assoc-G {V} {V} {V} {V} {idV} {idV} {idV} = tt
sym-assoc-G {V} {V} {V} {E} {idV} {idV} {s} = tt
sym-assoc-G {V} {V} {V} {E} {idV} {idV} {t} = tt
sym-assoc-G {V} {V} {E} {E} {idV} {s} {idE} = tt
sym-assoc-G {V} {V} {E} {E} {idV} {t} {idE} = tt
sym-assoc-G {V} {E} {E} {E} {s} {idE} {idE} = tt
sym-assoc-G {V} {E} {E} {E} {t} {idE} {idE} = tt
sym-assoc-G {E} {E} {E} {E} {idE} {idE} {idE} = tt
```


```agda
identity¹-G : {A B : GObj} {f : A ⇒G B} → Gcomp Gid f ≈G f
identity¹-G {V} {V} {idV} = tt
identity¹-G {V} {E} {s} = tt
identity¹-G {V} {E} {t} = tt
identity¹-G {E} {E} {idE} = tt

identityʳ-G : {A B : GObj} {f : A ⇒G B} → Gcomp f Gid ≈G f
identityʳ-G {V} {V} {idV} = tt
identityʳ-G {V} {E} {s} = tt
identityʳ-G {V} {E} {t} = tt
identityʳ-G {E} {E} {idE} = tt

identity²-G : {A : GObj} → Gcomp (Gid {A}) (Gid {A}) ≈G Gid {A}
identity²-G {V} = tt
identity²-G {E} = tt
```



```agda
G : Category 0ℓ 0ℓ 0ℓ
G = record
      { Obj = GObj
      ; _⇒_ = _⇒G_
      ; _≈_ = _≈G_
      ; id = Gid
      ; _∘_ = Gcomp
      ; assoc = assoc-G
      ; sym-assoc = sym-assoc-G
      ; identityˡ = identity¹-G
      ; identityʳ = identityʳ-G
      ; identity² = identity²-G
      ; equiv = record
        { refl = ≈G-refl
        ; sym = ≈G-symm
        ; trans = ≈G-trans }
      ; ∘-resp-≈ = resp1
      }
      where
        resp1 : {A B C : GObj} {f h : B ⇒G C} {g i : A ⇒G B}
             → f ≈G h → g ≈G i → Gcomp f g ≈G Gcomp h i
        resp1 {V} {V} {V} {idV} {idV} {idV} {idV} a b = tt
        resp1 {V} {V} {E} {s} {s} {idV} {idV} a b = tt
        resp1 {V} {V} {E} {t} {t} {idV} {idV} a b = tt
        resp1 {V} {E} {E} {idE} {idE} {s} {s} a b = tt
        resp1 {V} {E} {E} {idE} {idE} {t} {t} a b = tt
        resp1 {E} {E} {E} {idE} {idE} {idE} {idE} a b = tt

```




```agda
data Vertices : Set 0ℓ where
  a b c d : _

data Edges : Set 0ℓ where
  𝟏 𝟐 𝟑 𝟒 : _


source : Edges → Vertices
source 𝟏 = a
source 𝟐 = b
source 𝟑 = b
source 𝟒 = d

target : Edges → Vertices
target 𝟏 = b
target 𝟐 = c
target 𝟑 = c
target 𝟒 = d
```



```agda
G-F₀ : Category.Obj (Category.op G) → Category.Obj (Sets 0ℓ)
G-F₀ V = Vertices
G-F₀ E = Edges

G-F₁ : {A B : Category.Obj (Category.op G)}
     → Category.op G [ A , B ]
     → Sets 0ℓ [ G-F₀ A , G-F₀ B ]
G-F₁ {V} {V} idV y = y
G-F₁ {E} {V} s = source
G-F₁ {E} {V} t = target
G-F₁ {E} {E} idE y = y
```


```agda
identity-F : {A : Category.Obj (Category.op G)}
          → Sets 0ℓ [ G-F₁ ((Category.id (Category.op G)) {A}) ≈ Category.id (Sets 0ℓ) ]
identity-F {V} {x} = refl
identity-F {E} {x} = refl


homomorphism-F : {X Y Z : Category.Obj (Category.op G)} {f : Category.op G [ X , Y ]} {g : Category.op G [ Y , Z ]}
              → Sets 0ℓ [ G-F₁ (Category.op G [ g ∘ f ]) ≈ Sets 0ℓ [ G-F₁ g ∘ G-F₁ f ] ]
homomorphism-F {V} {V} {V} {idV} {idV} {x} = refl
homomorphism-F {E} {V} {V} {f} {idV} {x} = refl
homomorphism-F {E} {E} {V} {idE} {g} {x} = refl
homomorphism-F {E} {E} {E} {idE} {idE} {x} = refl

```

```agda
F : Presheaf G (Sets 0ℓ)  -- Functor G.op (Sets 0ℓ)
F = record
      { F₀ = G-F₀
      ; F₁ = G-F₁
      ; identity = identity-F
      ; homomorphism = λ { {V}{V}{V}{idV}{idV}{x} → refl
                         ; {E}{V}{V}{f}{idV}{x} → refl
                         ; {E}{E}{V}{idE}{g}{x} → refl
                         ; {E}{E}{E}{idE}{idE}{x} → refl }
                     -- why cannot just put homomorphism-F here ???
      ; F-resp-≈ = resp2
      }
      where
        resp2 : {A B : Category.Obj (Category.op G)}
              → {f g : Category.op G [ A , B ]}
              → Category.op G [ f ≈ g ]
              → Sets 0ℓ [ G-F₁ f ≈ G-F₁ g ]
        resp2 {V} {V} {idV} {idV} x = refl
        resp2 {E} {V} {s} {s} x = refl
        resp2 {E} {V} {t} {t} x = refl
        resp2 {E} {E} {idE} {idE} x = refl

```
