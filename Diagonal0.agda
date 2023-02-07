{-# OPTIONS --cubical --allow-unsolved-metas #-}

module Diagonal0 where

open import Data.Bool hiding  (_∨_ ; _∧_)
open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism renaming (Iso to _≅_)

idp : {T : Type} → T ≡ T
idp = refl

notp : Bool ≡ Bool
notp = isoToPath (iso not not rem rem)
  where
    rem : (b : Bool) → not (not b) ≡ b
    rem false = refl
    rem true  = refl






-- It's relatively easier to get the diagonal from a well-defined square
-- Square [left] [right] [bottom] [top]
diag-from-sq : (p : Bool ≡ Bool)
             → Square p p p p → Bool ≡ Bool
diag-from-sq p sq = λ i → sq i i

-- example
-- might need Glue

{--
sq0 : Square notp idp idp notp
sq0 i j = hfill (λ j → λ { (i = i0) → notp j
                         ; (i = i1) → idp{Bool} j })
                (inS (idp{Bool} i)) j
--}
