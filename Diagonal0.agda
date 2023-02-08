{-# OPTIONS --cubical --allow-unsolved-metas #-}

module Diagonal0 where

open import Data.Bool hiding  (_∨_ ; _∧_)
open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism renaming (Iso to _≅_)

idp : {T : Type} → T ≡ T
idp = refl

rem : (b : Bool) → not (not b) ≡ b
rem false = refl
rem true  = refl

notp : Bool ≡ Bool
notp = isoToPath (iso not not rem rem)

not-equiv : Bool ≃ Bool
not-equiv = isoToEquiv (iso not not rem rem)

-- It's relatively easier to get the diagonal from a well-defined square
-- Square [left] [right] [bottom] [top]
diag-from-sq : (p : Bool ≡ Bool)
             → Square p p p p → Bool ≡ Bool
diag-from-sq p sq = λ i → sq i i

-- example
-- might need Glue and Glue-fill

{--
sq0 : Square notp idp idp notp
sq0 i j = hfill (λ j → λ { (i = i0) → notp j
                         ; (i = i1) → idp{Bool} j })
                (inS (idp{Bool} i)) j
--}

notp' : Bool ≡ Bool
notp' i = Glue Bool walls
  where
    walls : Partial (~ i ∨ i) (Σ[ T ∈ Type ] (T ≃ Bool))
    walls (i = i0) = Bool , not-equiv
    walls (i = i1) = Bool , idEquiv Bool


_ : ∀ x → transport notp' x ≡ not x
_ = λ _ → refl

_ : notp' ≡ notp
_ = refl



-- hcomp
-- extensibility is preserved by paths
hcomp' : ∀ {ℓ} {A : Type ℓ} {φ}
       → (walls : I → Partial φ A)  -- partial path or tube (j ?)
       → A [ φ ↦ walls i0 ]         -- the bottom
       → A [ φ ↦ walls i1 ]         -- the top
hcomp' walls bot = inS (hcomp walls (outS bot))


hfill' :  ∀ {ℓ} {A : Type ℓ} {φ}
        → (walls : I → Partial φ A)     -- partial path/tube
        → A [ φ ↦ walls i0 ]            -- the bottom
        → I                             -- another direction/dimention
        → A
hfill' {A = A} {φ = φ} walls bot k = hcomp new-walls (outS bot)
  where
    new-walls : ∀ j → Partial (φ ∨ ~ k) A
    new-walls j (φ = i1) = walls (k ∧ j) 1=1   -- k=i1 then (walls j 1=1)
    new-walls j (k = i0) = outS bot            -- k=i0 then bottom


-- see 1lab.Univalence
glue-hfill' : ∀ {ℓ} {φ}
            → (walls : I → Partial φ (Type ℓ))
            → Type ℓ [ φ ↦ walls i0 ]
            → I
            → Type ℓ
glue-hfill' = {!!}
