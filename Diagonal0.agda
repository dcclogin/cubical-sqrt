{-# OPTIONS --cubical --allow-unsolved-metas #-}

module Diagonal0 where

open import Data.Bool hiding  (_∨_ ; _∧_)
open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism renaming (Iso to _≅_)

idp : ∀ {ℓ} {T : Type ℓ} → T ≡ T
idp = refl

notp : Bool ≡ Bool
notp = isoToPath (iso not not rem rem)
  where
    rem : (b : Bool) → not (not b) ≡ b
    rem false = refl
    rem true  = refl






-- It's relatively easy to get the diagonal from a well-defined square
-- Square [left] [right] [bottom] [top]
diag-from-sq : (p q : Bool ≡ Bool) → Square p q q p → Bool ≡ Bool
diag-from-sq p q sq = λ i → sq i i

-- example
-- might need Glue
sq0 : Square notp notp notp notp
sq0 i j = hfill walls (inS (notp i)) j
  where
    walls : ∀ j → Partial (~ i ∨ i) Type
    walls j (i = i0) = notp j
    walls j (i = i1) = notp j
