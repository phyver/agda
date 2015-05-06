{-# OPTIONS --hyvernat-termination-check #-}

module TerminationHyvernatCycle where

  data Bool : Set where
    True False : Bool

  bad : Bool -> Bool
  bad True = bad False
  bad False = bad True
