import Calls

-- ack Z     m     = S m
-- ack (S n) Z     = ack0 n (S Z)
-- ack (S n) (S m) = ack2 n (ack1 (S n) m)

-- 0=n 1=m
ack1 :: Call
ack1 = Call
  [ (0 , Const "S" (Exact [Case "S"] 0))  -- n := S (S- n)
  , (1 , Exact [Case "S"] 1)              -- m := S- m
  ]

ack2 = Call
  [ (0 , Exact [Case "S"] 0)           -- n := S- n
  , (1 , Approx [ Branch Infty [] 0    -- m := ∞
                , Branch Infty [] 1])  --    = <∞>n + <∞>m
  ]

f1 = Call [ (0 , Const "B" (Const "C" (Exact [(Case "A")] 0) ) )]
f2 = Call [ (0 , Exact [(Case "B")] 0)]
f3 = Call [ (0 , Exact [(Case "C")] 0)]

g = Call [ (0 , Approx
  [ Branch (Number 0) [] 1
  , Branch Infty [] 1
  , Branch (Number 10) [] 1
  ] ) ]

main = do
  print_call ack1
  print_call ack2
  print_call f1
  print_call f2
  print_call f3
  print_call $ collapse_call 0 100 g
