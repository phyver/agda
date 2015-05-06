{-# OPTIONS --hyvernat-termination-check #-}

module TerminationHyvernatIncrease where

  data Nat : Set where
    Z : Nat
    S : Nat -> Nat

  bad : Nat -> Nat
  bad n = bad (S n)
