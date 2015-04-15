
{-# OPTIONS --copatterns #-}

data _==_ {A : Set} (a : A) : A → Set where
  idp : a == a

-- Coinductive equivalences
record CoEq (A B : Set) : Set where
  coinductive
  constructor coEq
  field
    to   : A → B
    from : B → A
    eq   : (a : A) (b : B) → CoEq (a == from b) (to a == b)
open CoEq public

-- {-# TERMINATING #-}
id-CoEq : (A : Set) → CoEq A A
to   (id-CoEq A) a = a
from (id-CoEq A) b = b
eq   (id-CoEq A) a b = id-CoEq _
-- eq   (id-CoEq A) a b = id-CoEq {!(a == b)!}
