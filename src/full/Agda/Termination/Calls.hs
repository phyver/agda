module Calls where

import Data.List
import Data.Monoid



-- type for depth differences
data Z_infty =
    Number Int
  | Infty
  deriving Eq
instance Ord Z_infty where
  compare Infty Infty = EQ
  compare Infty _ = GT
  compare _ Infty = LT
  compare (Number n) (Number m) = compare n m
instance Show Z_infty where
  show Infty = "∞"
  show (Number n) = show n
instance Monoid Z_infty where
  mempty = Number 0
  mappend Infty _ = Infty
  mappend _ Infty = Infty
  mappend (Number n) (Number m) = Number (n+m)

-- the two kinds of destructors: projections (on a label) and case (on a
-- constructors)
data Destructor =
    Proj String
  | Case String
  deriving Eq
instance Show Destructor where
  show (Proj l) = "π_" ++ l
  show (Case c) = c ++ "-"

-- term language for for approximations
data Term =
    Const String Term                           -- constructor
  | Record [(String , Term)]                    -- record
  | Exact [Destructor]  Int                     -- "exact" branch of destructors, with argument
  | Approx [ (Z_infty , [Destructor] , Int) ]   -- sum of approximations
instance Show Term where
  show (Const c t) = c ++ (show t)
  show (Record l) = "{" ++ (intercalate " ; " (map (\(l,t) -> show l ++ "=" ++ show t) l)) ++ "}"
  show (Exact ds i) = (intercalate "" (map show ds)) ++ "x_" ++ (show i)
  show (Approx l) = intercalate " + " (map (\(w,ds,i) -> "<" ++ (show w) ++ ">" ++ (intercalate "" (map show ds)) ++ "x_" ++ (show i)) l)

-- a call is a substitution of the arguments by terms. The arguments are
-- numbered consecutively, so that a call is just a list.
type Call = [(Int , Term)]
print_call :: Call -> IO()
print_call [] = putStr ""
print_call ((i,t):c) = putStr "x_" >> (putStr $ show i) >> putStr " := " >> print t >> putStrLn ""

-- collapse the weight of an approximation
collapse_infty :: Int -> Z_infty -> Z_infty
collapse_infty b Infty = Infty
collapse_infty b (Number n)
  | n < -b    = Number (-b)
  | n > b-1   = Infty
  | otherwise = Number n

-- Longest common suffix of l1 and l2; returns a triple containing the suffix,
-- and the remainining elements in l1 and l2 in reverse order:
--    l1 l2  -->  s r1 r2 s.t. l1 = rev_append r1 s
--                             l2 = rev_append r2 s
suffix :: (Eq a) => [a] -> [a] -> ([a],[a],[a])
suffix l1 l2 = rev_prefix (reverse l1) (reverse l2) []
  where rev_prefix (a:l1) (b:l2) s
          | a == b    = rev_prefix l1 l2 (a:s)
          | otherwise = (s, l1, l2)
        rev_prefix l1 l2 s = (s, l1, l2)

type Branch = (Z_infty, [Destructor], Int)

-- approximates b1 b2 == True when b1 is an approximation of b2
approximates_destructors :: Branch -> Branch -> Bool
approximates_destructors (w1, ds1, x1) (w2, ds2, x2)
  | x1 == x2  = case suffix ds1 ds2 of
                       (_, [], ds2') -> w2 <= w1 <> (Number $ length ds2')
                       otherwise -> False
  | otherwise = False

-- nub_max : keeps only maximal branches
nub_max :: [Branch] -> [Branch]
nub_max [] = []
nub_max (b:bs) = aux b (nub_max bs)
  where aux b [] = [b]
        aux b (b1:bs)
          | approximates_destructors b b1  = aux b bs
          | approximates_destructors b1 b  = aux b1 bs
          | otherwise                      = b1:(aux b bs)

-- computes the normal form of <w>v
reduce_approx :: Z_infty -> Term -> [Branch]
reduce_approx w (Const _ v) = reduce_approx (w <> (Number 1)) v
reduce_approx w (Record l) = nub_max $ concat $ map (reduce_approx (w <> (Number 1))) $ map snd l
reduce_approx w (Approx bs) = nub_max $ map (\(w',ds,i) -> (w <> w', ds, i)) bs
reduce_approx w (Exact ds i) = [ (w,ds,i) ]


approximates :: Term -> Term -> Bool
approximates (Exact ds1 i1) (Exact ds2 i2)
  | ds1 == ds2 && i1 == i2 = True
  | otherwise              = False
approximates (Const c1 u1) (Const c2 u2)
  | c1 == c2  = approximates u1 u2
  | otherwise = False
approximates (Record l1) (Record l2) =
  let p = unzip l1 in
  let labels1 = fst p in
  let terms1 = snd p in
  let p = unzip l2 in
  let labels2 = fst p in
  let terms2 = snd p in
  (labels1 == labels2) && (all (\(x,y) -> approximates x y) $ zip terms1 terms2)
approximates (Approx b1s) (Approx b2s) = all (\x -> any (\y -> approximates_destructors y x) b1s) b2s
approximates (Approx b1s) u2 = approximates (Approx b1s) (Approx $ reduce_approx (Number 0) u2)
approximates _ _ = False



compatible :: Term -> Term -> Bool
compatible (Exact ds1 i1) (Exact ds2 i2) = ds1 == ds2 && i1 == i2
compatible (Const c1 u1) (Const c2 u2)
  | c1 == c2  = compatible u1 u2
  | otherwise = False
compatible (Record l1) (Record l2) =
  let p = unzip l1 in
  let labels1 = fst p in
  let terms1 = snd p in
  let p = unzip l2 in
  let labels2 = fst p in
  let terms2 = snd p in
  (labels1 == labels2) && (all (\(x,y) -> compatible x y) $ zip terms1 terms2)
compatible (Approx bs) u = compatible (Approx $ reduce_approx (Number 0) u) (Approx bs)
compatible u (Approx bs) = compatible (Approx $ reduce_approx (Number 0) u) (Approx bs)
compatible _ _ = False



-- calls
get_term :: Call -> Int -> Term
get_term tau i = case lookup i tau of
                   (Just t) -> t
                   Nothing -> Approx []

-- approximation order for calls
approximates_call :: Call -> Call -> Bool
approximates_call tau sigma =
  let indices = map fst tau in
  -- let indices2 = map fst sigma in
  -- if indices /= indices2 then error "PROBLEM..." else
  all (\i -> approximates (get_term tau i) (get_term sigma i)) indices


-- compatibility for calls
compatible_call :: Call -> Call -> Bool
compatible_call tau sigma =
  let indices = map fst tau in
  -- let indices2 = map fst sigma in
  -- if indices /= indices2 then error "PROBLEM..." else
  all (\i -> compatible (get_term tau i) (get_term sigma i)) indices

-- get_subtree is inside the Maybe monad to deal with impossible cases
get_subtree :: [Destructor] -> Term -> Maybe Term
get_subtree [] v = Just v
get_subtree ds (Approx bs) = Just $ Approx $ map (\(w,d,i) -> (w <> (Number (-(length ds))),d,i)) bs
get_subtree ds (Exact ds' i) = Just $ Exact ((reverse ds) ++ ds') i
get_subtree ((Case c1):ds) (Const c2 v)
  | c1 == c2  = get_subtree ds v
  | otherwise = Nothing     -- IMPOSSIBLE CASE
get_subtree ((Proj l):ds) (Record r) =
  case lookup l r of
    Just v -> get_subtree ds v
    Nothing -> error "TYPING PROBLEM"
get_subtree _ _ = error "TYPING PROBLEM"



substitute :: Term -> Call -> Maybe Term
substitute (Const c u) tau = substitute u tau >>= \t -> Just $ Const c t
substitute (Record r) tau =
  let p = unzip r in
  let labels = fst p in
  let terms = snd p in
  sequence (map (\t -> substitute t tau) terms)  >>= \l ->
  Just $ Record $ zip labels l
substitute (Exact ds i) tau = get_subtree (reverse ds) (get_term tau i)
substitute (Approx bs) tau =
  sequence (map (\(w,ds,i) ->
                    get_subtree (reverse ds)
                                (get_term tau i)   >>= \t ->
                    Just $ reduce_approx w t)
                bs)                 >>= \l ->
  Just $ Approx $ nub_max $ concat l


-- collapsing the weights
collapse1 :: Int -> Term -> Term
collapse1 b (Const c u) = Const c (collapse1 b u)
collapse1 b (Record r) =
  let p = unzip r in
  let labels = fst p in
  let args = snd p in
  Record (zip labels (map (collapse1 b) args))
collapse1 b (Exact ds i) = Exact ds i
collapse1 b (Approx bs) = Approx $ nub_max $ map (\(w,ds,i) -> (collapse_infty b w, ds, i)) bs

-- collapsing the destructors
collapse2 :: Int -> Term -> Term
collapse2 d (Const c u) = Const c (collapse2 d u)
collapse2 d (Record r) =
  let p = unzip r in
  let labels = fst p in
  let args = snd p in
  Record (zip labels (map (collapse2 d) args))
collapse2 d (Exact ds i) =
  let n = length ds in
  if n > d
  then Approx [(Number (d-n), drop (n-d) ds, i)]
  else (Exact ds i)
collapse2 d (Approx bs) = Approx $ nub_max $ map (\(w,ds,i) -> let n=length ds in if n>d then (w <> (Number (d-n)),drop (n-d) ds,i) else (w,ds,i)) bs

-- collapsing constructors
collapse3 :: Int -> Term -> Term
collapse3 0 (Exact ds i) = Exact ds i
collapse3 0 u = Approx $ reduce_approx (Number 0) u
collapse3 d (Const c u) = Const c (collapse3 (d-1) u)
collapse3 d (Record r) = 
  let p = unzip r in
  let labels = fst p in
  let args = snd p in
  Record (zip labels (map (collapse3 (d-1)) args))
collapse3 d u = u


collapse :: Int -> Int -> Term -> Term
collapse d b u = collapse1 b $ collapse2 d $ collapse3 d u

collapse_call :: Int -> Int -> Call -> Call
collapse_call d b tau = map (\(i,t) -> (i, collapse d b t)) tau

compose :: Int -> Int -> Call -> Call -> Maybe Call
compose d b tau sigma =
  sequence (map (\(i,t) -> substitute t tau >>= \u -> Just(i,u)) sigma) >>= \c ->
  Just $ collapse_call d b c

is_decreasing :: Call -> Bool
is_decreasing tau = any decr tau
  where
  isOK ds t i = approximates (Approx [(Number (-1), ds, i)]) t
  decr (i,t) = aux [] t
    where aux ds (Const c u) = isOK ds t i || aux ((Case c):ds) u
          aux ds (Record r) = isOK ds t i || any (\(n,u) -> aux ((Proj n):ds) u) r
          aux ds t = isOK ds t i



