{-# OPTIONS --hyvernat-termination-check #-}
{-# OPTIONS --allow-unsolved-metas #-}
{-# OPTIONS -v term:2  #-}

data Nat : Set where
  Z : Nat
  S : Nat -> Nat

data Bool : Set where
  True False : Bool

data List (X : Set) : Set where
  Nil : List X
  Cons : X -> List X -> List X

data Tree (X : Set) : Set where
  Leaf : Tree X
  Node : Tree X -> X -> Tree X -> Tree X

data Bin : Set where
  Eps : Bin
  Zer : Bin → Bin
  One : Bin → Bin

id : Nat -> Nat
id Z = Z
id (S n) = S (id n)


last : List Nat -> Nat
--last Nil = ?
last Nil = Z
last (Cons n Nil) = n
last (Cons _ l) = last l

length : List Nat -> Nat
length Nil = Z
length (Cons _ l) = S (length l)

append : List Nat -> List Nat -> List Nat
append Nil l = l
append (Cons a as) l = Cons a (append as l)

rev_append : List Nat -> List Nat -> List Nat
rev_append Nil l = l
rev_append (Cons a as) l = rev_append as (Cons a l)

-- should pass when I deal with metavariables
meta1 : Nat -> Nat
meta1 n = meta1 ?

meta2 : Nat -> Nat -> Nat
meta2 Z Z = Z
meta2 (S n) m = meta2 m ?
meta2 m (S n) = meta2 n ?


f1 : Bin → Set
f1 Eps = Bin
f1 (Zer b) = f1 b
f1 (One b) = f1 (Zer b)

-- should pass when I add the calling context of calls
--f2 : Bin -> Bin
--f2 (One x) = f2 (Zer (f2 x))
--f2 _ = Eps

-- check that the order is right
h : Bin -> Bin
h (Zer (One b)) = h (One (Zer b))
h _ = Eps
