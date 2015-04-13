-- 2014-04-13
-- Examples that should check with Pierre Hyvernat's termination checker

data Unit : Set where
  unit : Unit

data Either (A B : Set) : Set where
  left  : A → Either A B
  right : B → Either A B

record _×_ (A B : Set) : Set where
  constructor _,_
  field
    fst : A
    snd : B

data ℕ : Set where
  zero : ℕ
  suc  : (n : ℕ) → ℕ

data Bool : Set where
  true false : Bool

data BT : Set where
  leaf : BT
  bin  : BT → BT → BT

data T : Set where
  leaf : T
  un   : T → T
  bin  : T → T → T

data List (A : Set) : Set where
  [] : List A
  _∷_ : (x : A) (xs : List A) → List A

infixr 13 _∷_

-- comb n t  terminates on the lex. product  (n, right-depth t)
comb : ℕ → BT → BT
comb _ leaf = leaf
comb zero _ = leaf
comb (suc n) (bin t leaf) = bin (comb n t) leaf
comb n (bin t1 (bin t2 t3)) = comb n (bin (bin t1 t2) t3)


-- Should work if termination is checked on case trees.
merge : T → T → T
merge leaf        u           = u
merge (un t)      u           = un (merge t u)
merge (bin t1 t2) (bin u1 u2) = bin (merge t1 u1) (merge t2 u2)
merge (bin t1 t2) u           = merge u (bin t1 t2)

sum : List ℕ → ℕ
sum [] = zero
sum (n ∷ []) = n
sum (n ∷ (zero  ∷ l)) = sum (n ∷ l)
sum (n ∷ (suc m ∷ l)) = sum (suc n ∷ m ∷ l)

sum-works : List ℕ → ℕ
sum-works [] = zero
sum-works (n ∷ []) = n
sum-works (n ∷ (zero  ∷ l)) = sum-works (n ∷ l)
sum-works (n ∷ (suc m ∷ l)) = suc (sum-works (n ∷ m ∷ l))

-- Version of test0 with dummy variable
test-3 : Either Unit Unit → Unit
test-3 (left  x) = test-3 (right x)
test-3 (right x) = x

neq : Bool → Bool → Bool
neq false y     = y
neq true  true  = false
neq true  false = neq false true

-- swap-1 : ℕ → ℕ → ℕ
-- swap-1  zero   n = n
-- swap-1 (suc m) n = suc (swap-1 n m)

works-1 : ℕ → ℕ → ℕ
works-1  zero   n = n
works-1 (suc m) n = works-1 m (suc n)

test-1 : ℕ × ℕ → ℕ
test-1 (zero  , n) = n
test-1 (suc m , n) = test-1 (m , suc n)

test0 : Bool → Bool
test0 true  = test0 false  -- F T-1
test0 false = true
