{-# OPTIONS --hyvernat-termination-check #-}

data Bin : Set where
  Eps : Bin
  Zer : Bin → Bin
  One : Bin → Bin

-- check that the order is right
bad : Bin -> Bin
bad (Zer (One b)) = bad (Zer (One b))
bad _ = Eps
