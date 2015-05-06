{-# OPTIONS --hyvernat-termination-check #-}

module TerminationHyvernatIncrease2 where

  data Nat : Set where
    Z : Nat
    S : Nat -> Nat

  bad : Nat -> Nat
  bad Z = Z
  bad (S n) = bad (S (S n))
