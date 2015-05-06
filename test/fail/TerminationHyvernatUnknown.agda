{-# OPTIONS --hyvernat-termination-check #-}

module TerminationHyvernatUnknown where

  data Nat : Set where
    Z : Nat
    S : Nat -> Nat


  bad : Nat -> Nat
  bad Z = S Z
  bad (S n) = bad (bad n)
