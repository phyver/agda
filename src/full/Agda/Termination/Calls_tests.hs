import Calls

ack1 = [ (0 , Const "S" (Exact [(Case "S")] 0) ) , (1 , Exact [(Case "S")] 1)]

ack2 = [ (0 , Exact [(Case "S")] 0) , (1 , Approx [(Infty, [], 0) , (Infty, [], 1)])]

f1 = [ (0 , Const "B" (Const "C" (Exact [(Case "A")] 0) ) )]
f2 = [ (0 , Exact [(Case "B")] 0)]
f3 = [ (0 , Exact [(Case "C")] 0)]

g = [ (0 , Approx [ (Number 0, [], 1), (Infty, [], 1), (Number 10, [], 1) ]) ]

main = do
  print_call ack1
  print_call ack2
  print_call f1
  print_call f2
  print_call f3
  print_call $ collapse_call 0 100 g
