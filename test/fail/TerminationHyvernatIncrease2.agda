{-# OPTIONS --hyvernat-termination-check #-}

data Nat : Set where
  Z : Nat
  S : Nat -> Nat

bad : Nat -> Nat
bad Z = Z
bad (S n) = bad (S (S n))
