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
  š : U

ā¦_ā§ : U ā Type
ā¦ š ā§ = Bool

data _ā·_ : U ā U ā SSet where
  `id      : š ā· š 
  `not     : š ā· š 
  _ā_      : ā {A B C} ā (A ā· B) ā (B ā· C) ā (A ā· C)
  sqrt     : ā {A} ā (A ā· A) ā (A ā· A)
  `sqrtNot  : ā {A} ā (A ā· A)
  
-- sqrt c ā sqrt c = c

  
{--
evalF : ā {A B} ā (A ā· B) ā ā¦ A ā§ ā ā¦ B ā§
evalF `id v = v
evalF `not b = not b
evalF (cā ā cā) v = evalF cā (evalF cā v)
evalF (sqrt c) v = ?

-----

partialBool : ā i ā Bool ā Bool ā Partial (i āØ ~ i) Bool
partialBool i b1 b2 (i = i0) = b1
partialBool i b1 b2 (i = i1) = b2

-- sqrt : ā {A} ā (ā¦ A ā§ ā ā¦ A ā§) ā Ī£ (Ī» i ā Partial i ā¦ A ā§)
-- sqrt = ?

evalP : ā {A B} ā (i : I) ā (A ā· B) ā ā¦ A ā§ ā Partial (i āØ ~ i) ā¦ B ā§ 
evalP i `id b = partialBool i b b 
evalP i `not b =  partialBool i (not b) (not b)
evalP i `sqrtNot b = partialBool i b (not b)
evalP i (cā ā cā) b = {!!}
--}
