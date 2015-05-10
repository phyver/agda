{-# OPTIONS --hyvernat-termination-check #-}
{-# OPTIONS --termination-depth 6 #-}

data Tree : Set where
  Leaf : Tree
  Node : Tree -> Tree -> Tree

comb : Tree -> Tree
comb Leaf = Leaf
comb (Node t Leaf) = Node (comb t) Leaf
comb (Node t1 (Node t2 t3)) = comb (Node (Node t1 t2) t3)
