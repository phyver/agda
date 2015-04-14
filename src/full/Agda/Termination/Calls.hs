{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE TupleSections #-}

module Calls where

import Control.Arrow (first, second)

import Data.List
import Data.Monoid
import Data.Functor
import Data.Traversable (forM)

-- | Type for depth differences.
data Z_infty
  = Number Int
  | Infty
  deriving Eq

instance Ord Z_infty where
  compare Infty Infty = EQ
  compare Infty _ = GT
  compare _ Infty = LT
  compare (Number n) (Number m) = compare n m

-- TODO: Define Pretty instance instead  (Agda.Utils.Pretty).
instance Show Z_infty where
  show Infty = "∞"
  show (Number n) = show n

instance Monoid Z_infty where
  mempty = Number 0
  mappend Infty _ = Infty
  mappend _ Infty = Infty
  mappend (Number n) (Number m) = Number (n+m)

-- | The two kinds of destructors:
--   projections (on a label) and case (on a constructors)
data Destructor
  = Proj String
  | Case String
  deriving Eq

instance Show Destructor where
  show (Proj l) = "π_" ++ l
  show (Case c) = c ++ "-"

-- | The arguments of the caller are de Bruijn indices.
type Var = Int
type Weight = Z_infty

data Branch = Branch
  { brWeight :: Weight
  , brDests  :: [Destructor]
  , brVar    :: Var
  }

-- | Semantic editor for @Weight@.
mapWeight :: (Weight -> Weight) -> Branch -> Branch
mapWeight f br = br { brWeight = f (brWeight br) }

-- | Term language for approximations.
data Term
  = Const String Term           -- ^ constructor
  | Record [(String , Term)]    -- ^ record
  | Exact [Destructor]  Var     -- ^ "exact" branch of destructors, with argument
  | Approx [Branch]             -- ^ sum of approximations

instance Show Term where
  show (Const c t) = c ++ (show t)
  show (Record l) = "{" ++ (intercalate " ; " (map (\(l,t) -> show l ++ "=" ++ show t) l)) ++ "}"
  show (Exact ds i) = (intercalate "" (map show ds)) ++ "x_" ++ (show i)
  show (Approx l) = intercalate " + " (map (\(Branch w ds i) -> "<" ++ (show w) ++ ">" ++ (intercalate "" (map show ds)) ++ "x_" ++ (show i)) l)

-- | A call is a substitution of the arguments by terms.

newtype Call = Call { theCall :: [(Var , Term)] }
    -- NOTE: could be also just [Term]

print_call :: Call -> IO ()
print_call (Call []) = putStr ""
print_call (Call ((i,t):c)) = putStr "x_" >> (putStr $ show i) >> putStr " := " >> print t >> putStrLn "" >> print_call (Call c)

-- | Collapse the weight of an approximation.

collapse_infty :: Int -> Z_infty -> Z_infty
collapse_infty b Infty = Infty
collapse_infty b (Number n)
  | n < -b    = Number (-b)
  | n > b-1   = Infty
  | otherwise = Number n

-- | Longest common suffix of @l1@ and @l2@;
--   returns a triple containing the suffix,
--   and the remainining elements in @l1@ and @l2@ in reverse order:
--   @
--     l1 l2  -->  s r1 r2 s.t. l1 = rev_append r1 s
--                              l2 = rev_append r2 s
--   @
suffix :: (Eq a) => [a] -> [a] -> ([a],[a],[a])
suffix l1 l2 = rev_prefix (reverse l1) (reverse l2) []
  where rev_prefix (a:l1) (b:l2) s
          | a == b    = rev_prefix l1 l2 (a:s)
          | otherwise = (s, l1, l2)
        rev_prefix l1 l2 s = (s, l1, l2)
  -- TODO: Maybe move to Agda.Utils.List

-- | Approximates b1 b2 == True when b1 is an approximation of b2.
--   Written @b2 <= b1@ (@b2@ is more informative than @b1@).
approximates_destructors :: Branch -> Branch -> Bool
approximates_destructors (Branch w1 ds1 x1) (Branch w2 ds2 x2)
  | x1 == x2  = case suffix ds1 ds2 of
                       (_, [], ds2') -> w2 <= w1 <> (Number $ length ds2')
                       otherwise -> False
  | otherwise = False

  -- TODO: instantiate Agda.Utils.PartialOrd

-- | @nub_max@ keeps only maximal branches.
--   The output is a list of incomparable branches.
nub_max :: [Branch] -> [Branch]
nub_max [] = []
nub_max (b:bs) = aux b (nub_max bs)
  where aux b [] = [b]
        aux b (b1:bs)
          | approximates_destructors b b1  = aux b bs
          | approximates_destructors b1 b  = aux b1 bs
          | otherwise                      = b1:(aux b bs)

  -- TODO: reuse Agda.Utils.Favorites

-- | Computes the normal form of @<w>v@.
reduce_approx :: Z_infty -> Term -> [Branch]
reduce_approx w (Const _ v) = reduce_approx (w <> (Number 1)) v
reduce_approx w (Record l) = nub_max $ concat $ map (reduce_approx (w <> (Number 1))) $ map snd l
reduce_approx w (Approx bs) = nub_max $ map (\(Branch w' ds i) -> (Branch (w <> w') ds i)) bs
reduce_approx w (Exact ds i) = [ Branch w ds i ]

-- | Partial order @approximates t1 t2@ iff @t2 <= t1@.
approximates :: Term -> Term -> Bool
approximates (Exact ds1 i1) (Exact ds2 i2)
  | ds1 == ds2 && i1 == i2 = True
  | otherwise              = False
approximates (Const c1 u1) (Const c2 u2)
  | c1 == c2  = approximates u1 u2
  | otherwise = False
approximates (Record l1) (Record l2)
  | let (labels1, terms1) = unzip l1
  , let (labels2, terms2) = unzip l2 =
  labels1 == labels2 && and (zipWith approximates terms1 terms2)
approximates (Approx b1s) (Approx b2s) = all (\x -> any (\y -> approximates_destructors y x) b1s) b2s
approximates (Approx b1s) u2 = approximates (Approx b1s) (Approx $ reduce_approx (Number 0) u2)
approximates _ _ = False


-- | @compatible t1 t2@ if exists @t0@ such that @t0 <= t1@ and @t0 <= t2@
compatible :: Term -> Term -> Bool
compatible (Exact ds1 i1) (Exact ds2 i2) = ds1 == ds2 && i1 == i2
compatible (Const c1 u1) (Const c2 u2)
  | c1 == c2  = compatible u1 u2
  | otherwise = False
compatible (Record l1) (Record l2)
  | let (labels1, terms1) = unzip l1
  , let (labels2, terms2) = unzip l2 =
  labels1 == labels2 && and (zipWith compatible terms1 terms2)
compatible (Approx bs) u = compatible (Approx $ reduce_approx (Number 0) u) (Approx bs)
compatible u (Approx bs) = compatible (Approx $ reduce_approx (Number 0) u) (Approx bs)
compatible _ _ = False



-- | Lookup in a substitution (call).  Partial because of partial application.
get_term :: Call -> Var -> Term
get_term (Call tau) i =
  case lookup i tau of
    Just t  -> t
    Nothing -> Approx []  -- TODO: correct?

-- | Pointwise approximation order for calls.
approximates_call :: Call -> Call -> Bool
approximates_call tau sigma =
  let indices = map fst $ theCall tau in
  -- let indices2 = map fst sigma in
  -- if indices /= indices2 then error "PROBLEM..." else
  all (\i -> approximates (get_term tau i) (get_term sigma i)) indices

-- TODO: Isolate common pattern of these functions.

-- | Pointwise compatibility for calls.
compatible_call :: Call -> Call -> Bool
compatible_call tau sigma =
  let indices = map fst $ theCall tau in
  -- let indices2 = map fst sigma in
  -- if indices /= indices2 then error "PROBLEM..." else
  all (\i -> compatible (get_term tau i) (get_term sigma i)) indices

-- | @get_subtree@ is inside the @Maybe@ monad to deal with impossible cases.
get_subtree :: [Destructor] -> Term -> Maybe Term
get_subtree [] v = return v
get_subtree ds (Approx bs) = return $ Approx $
  map (mapWeight (Number (- length ds) <>)) bs
get_subtree ds (Exact ds' i) = return $ Exact (reverse ds ++ ds') i
get_subtree (Case c1 : ds) (Const c2 v)
  | c1 == c2  = get_subtree ds v
  | otherwise = Nothing     -- IMPOSSIBLE CASE
get_subtree (Proj l : ds) (Record r) =
  case lookup l r of
    Just v  -> get_subtree ds v
    Nothing -> error "TYPING PROBLEM"
get_subtree _ _ = error "TYPING PROBLEM"
  -- TODO: use __IMPOSSIBLE__

-- | Given a term and a substitution (call), apply the substitution.

substitute :: Term -> Call -> Maybe Term
substitute (Const c u) tau = Const c <$> substitute u tau
substitute (Record r) tau | let (labels, terms) = unzip r =
  Record . zip labels <$> mapM (`substitute` tau) terms
substitute (Exact ds i) tau = get_subtree (reverse ds) (get_term tau i)
substitute (Approx bs) tau = Approx . nub_max . concat <$> do
  forM bs $ \ (Branch w ds i) -> do
    reduce_approx w <$> get_subtree (reverse ds) (get_term tau i)

-- | Collapsing the weights.

collapse1 :: Int -> Term -> Term
collapse1 b (Const c u) = Const c (collapse1 b u)
collapse1 b (Record r) | let (labels, args) = unzip r =
  Record (zip labels (map (collapse1 b) args))
collapse1 b (Exact ds i) = Exact ds i
collapse1 b (Approx bs) = Approx $ nub_max $ map (mapWeight (collapse_infty b)) bs

-- | Collapsing the destructors.

collapse2 :: Int -> Term -> Term
collapse2 d (Const c u) = Const c (collapse2 d u)
collapse2 d (Record r) | let (labels, args) = unzip r =
  Record (zip labels (map (collapse2 d) args))
collapse2 d (Exact ds i) =
  let n = length ds in
  if n > d
  then Approx [Branch (Number (d-n)) (drop (n-d) ds) i]
  else (Exact ds i)
collapse2 d (Approx bs) = Approx $ nub_max $
  map (\ (Branch w ds i) -> let n=length ds in
         if n>d then Branch (w <> (Number (d-n))) (drop (n-d) ds) i
         else Branch w ds i)
      bs

-- | Collapsing constructors.

collapse3 :: Int -> Term -> Term
collapse3 0 (Exact ds i) = Exact ds i
collapse3 0 u = Approx $ reduce_approx (Number 0) u
collapse3 d (Const c u) = Const c (collapse3 (d-1) u)
collapse3 d (Record r) | let (labels, args) = unzip r =
  Record (zip labels (map (collapse3 (d-1)) args))
collapse3 d u = u

-- | Collapsing a term.

collapse :: Int -> Int -> Term -> Term
collapse d b u = collapse1 b $ collapse2 d $ collapse3 d u

-- | Collapsing a call.

collapse_call :: Int -> Int -> Call -> Call
collapse_call d b (Call tau) = Call $ map (second (collapse d b)) tau

-- | Call composition (partial).

compose :: Int -> Int -> Call -> Call -> Maybe Call
compose d b tau (Call sigma) = collapse_call d b . Call <$> do
  forM sigma $ \ (i,t) -> (i,) <$> substitute t tau

is_decreasing :: Call -> Bool
is_decreasing tau = any decr $ theCall tau
  where
  isOK ds t i = approximates (Approx [Branch (Number (-1)) ds i]) t
  decr (i,t) = aux [] t
    where aux ds (Const c u) = isOK ds t i || aux ((Case c):ds) u
          aux ds (Record r) = isOK ds t i || any (\(n,u) -> aux ((Proj n):ds) u) r
          aux ds t = isOK ds t i
