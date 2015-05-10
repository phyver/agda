{-# OPTIONS --hyvernat-termination-check #-}

data Nat : Set where
  Z : Nat
  S : Nat -> Nat

bad : Nat -> Nat
bad n = bad (S n)
