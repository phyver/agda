{-# OPTIONS --hyvernat-termination-check #-}
{-# OPTIONS -v term:40  #-}

data Bin : Set where
  Eps : Bin
  Zer : Bin → Bin
  One : Bin → Bin

-- TODO: This loops the termination checker:
-- bla : Bin → Set
-- bla Eps = Bin
-- bla (Zer b) = bla b
-- bla (One b) = bla (Zer b)
