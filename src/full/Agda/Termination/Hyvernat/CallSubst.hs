{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE PatternGuards  #-}
{-# LANGUAGE TupleSections  #-}

-- | Pierre Hyvernat's refinement of size-change termination.
--   See
--
--      Pierre Hyvernat,
--      The Size-Change Termination Principle for Constructor Based Languages
--      LMCS 2013
--
--  TODO: give an introduction by a relevant example here.

module Agda.Termination.Hyvernat.CallSubst where

import Control.Arrow (first, second)

import Data.List
import Data.Monoid
import Data.Functor
import Data.Traversable (forM)

import Agda.Syntax.Abstract.Name (QName)

import Agda.Termination.CutOff
import Agda.Termination.CallDecoration

import Agda.Utils.PartialOrd
import Agda.Utils.Pretty (Pretty(..), prettyShow, text, align)




type Depth = Int  -- ^ cutoff for constructor/destructor depth
type Bound = Int  -- ^ cutoff for weight

-- | Type for depth differences.
data ZInfty
  = Least               -- FIXME: probably doesn't work...  meta2 (S n) m = meta2 m ? //  meta2 m (S n) = meta2 n ? is non terminating...
  | Number Int
  | Infty
  deriving Eq

instance Ord ZInfty where
  compare Infty Infty = EQ
  compare Infty _ = GT
  compare _ Infty = LT
  compare Least Least = EQ
  compare Least _ = LT
  compare _ Least = GT
  compare (Number n) (Number m) = compare n m

instance Pretty ZInfty where
  pretty Least = text "⊥"
  pretty Infty = text "∞"
  pretty (Number n) = pretty n


instance Monoid ZInfty where
  mempty = Number 0
  mappend Infty _ = Infty
  mappend _ Infty = Infty
  mappend Least _ = Least
  mappend _ Least = Least
  mappend (Number n) (Number m) = Number (n+m)

-- | The two kinds of destructors:
--   projections (on a label) and case (on a constructors)
data Destructor n
  = Proj String
  | Case n
  deriving Eq

instance Pretty n => Pretty (Destructor n) where
  pretty (Proj l) = text $ "π_" ++ l
  pretty (Case c) = text $ (prettyShow c) ++ "-"

-- | The arguments of the caller are de Bruijn indices.
type ArgNo = Int
type Weight = ZInfty

data Branch n = Branch
  { brWeight :: Weight
  , brDests  :: [Destructor n]
  , brArgNo  :: ArgNo
  }

-- | Semantic editor for @Weight@.
mapWeight :: (Weight -> Weight) -> Branch n -> Branch n
mapWeight f br = br { brWeight = f (brWeight br) }

-- | Term language for approximations.
data Term n
  = Const n (Term n)              -- ^ constructor
  | Record [(String , Term n)]    -- ^ record
  | Exact [Destructor n]  ArgNo   -- ^ "exact" branch of destructors, with argument
  | Approx [Branch n]             -- ^ sum of approximations

instance Pretty n => Pretty (Term n) where
  pretty (Const c t)  = text $ prettyShow c ++ " " ++ prettyShow t
  pretty (Record l)   = text $ "{" ++ (intercalate " ; " (map (\(l,t) -> prettyShow l ++ "=" ++ prettyShow t) l)) ++ "}"
  pretty (Exact ds i) = text $ (intercalate " " (map prettyShow ds)) ++ " x_" ++ (prettyShow i)
  pretty (Approx [])  = text "empty sum"
  pretty (Approx l)   = text $ intercalate " + " (map (\(Branch w ds i) -> "<" ++ (prettyShow w) ++ ">" ++ (intercalate " " (map prettyShow ds)) ++ " x_" ++ (prettyShow i)) l)

-- | A call is a substitution of the arguments by terms.

newtype CallSubst n = CallSubst { callSubst :: [(ArgNo , Term n)] }
    -- NOTE: could be also just [Term n]

instance Pretty n => Pretty (CallSubst n) where
  pretty (CallSubst []) = text "...empty..."
  pretty (CallSubst c) = align 10 $ map (\(a,t) -> ("x_" ++ (prettyShow a) ++  " = ", pretty t)) c

instance Pretty n => Show (CallSubst n) where
  show = prettyShow

-- | Collapse the weight of an approximation.

collapseZInfty :: Int -> ZInfty -> ZInfty
collapseZInfty b Infty = Infty
collapseZInfty b Least = Least
collapseZInfty b (Number n)
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
suffix l1 l2 = revPrefix (reverse l1) (reverse l2) []
  where revPrefix (a:l1) (b:l2) s
          | a == b    = revPrefix l1 l2 (a:s)
          | otherwise = (s, l1, l2)
        revPrefix l1 l2 s = (s, l1, l2)
  -- TODO: Maybe move to Agda.Utils.List

-- | Approximates b1 b2 == True when b1 is an approximation of b2.
--   Written @b1 <= b2@ (@b2@ is more informative than @b1@).
approximatesDestructors :: Eq n => Branch n -> Branch n -> Bool
approximatesDestructors (Branch w1 ds1 x1) (Branch w2 ds2 x2)
  | x1 == x2  = case suffix ds1 ds2 of
                       (_, [], ds2') -> w2 <= w1 <> (Number $ length ds2')
                       otherwise -> False
  | otherwise = False

  -- TODO: instantiate Agda.Utils.PartialOrd

-- | @nubMax@ keeps only maximal branches.
--   The output is a list of incomparable branches.
nubMax :: Eq n => [Branch n] -> [Branch n]
nubMax [] = []
nubMax (b:bs) = aux b (nubMax bs)
  where aux b [] = [b]
        aux b (b1:bs)
          | approximatesDestructors b b1  = aux b bs
          | approximatesDestructors b1 b  = aux b1 bs
          | otherwise                      = b1:(aux b bs)

  -- TODO: reuse Agda.Utils.Favorites

-- | Computes the normal form of @<w>v@.
reduceApprox :: Eq n => ZInfty -> Term n -> [Branch n]
reduceApprox w (Const _ v) = reduceApprox (w <> (Number 1)) v
reduceApprox w (Record l) = nubMax $ concat $ map (reduceApprox (w <> (Number 1))) $ map snd l
reduceApprox w (Approx bs) = nubMax $ map (\(Branch w' ds i) -> (Branch (w <> w') ds i)) bs
reduceApprox w (Exact ds i) = [ Branch w ds i ]

-- | Partial order @approximates t1 t2@ iff @t1 <= t2@.
approximates :: Eq n => Term n -> Term n -> Bool
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
approximates (Approx b1s) (Approx b2s) = all (\x -> any (\y -> approximatesDestructors y x) b1s) b2s
approximates (Approx b1s) u2 = approximates (Approx b1s) (Approx $ reduceApprox (Number 0) u2)
approximates _ _ = False

-- | The lesser term is the one with less information.
--   Call graph completion keeps the worst calls
--   (those that endanger termination),
--   which corresponds to terms with least information.

instance Eq n => PartialOrd (Term n) where
  comparable = fromLeq approximates

-- | @compatible t1 t2@ if exists @t0@ such that @t1 <= t0@ and @t2 <= t0@
compatible :: Eq n => Term n -> Term n -> Bool
compatible (Exact ds1 i1) (Exact ds2 i2) = ds1 == ds2 && i1 == i2
compatible (Const c1 u1) (Const c2 u2)
  | c1 == c2  = compatible u1 u2
  | otherwise = False
compatible (Record l1) (Record l2)
  | let (labels1, terms1) = unzip l1
  , let (labels2, terms2) = unzip l2 =
  labels1 == labels2 && and (zipWith compatible terms1 terms2)
compatible (Approx bs1) (Approx bs2) =
  any (\b1 ->
  any (\b2 -> (approximatesDestructors b1 b2) || (approximatesDestructors b2 b1)) bs2) bs1
compatible (Approx bs) u = compatible (Approx $ reduceApprox (Number 0) u) (Approx bs)
compatible u (Approx bs) = compatible (Approx $ reduceApprox (Number 0) u) (Approx bs)
compatible _ _ = False



-- | Lookup in a substitution (call).  Partial because of partial application.
getTerm :: CallSubst n -> ArgNo -> Term n
getTerm (CallSubst tau) i =
  case lookup i tau of
    Just t  -> t
    Nothing -> Approx []  -- TODO: correct?

-- | Pointwise approximation order for calls.
approximatesCall :: Eq n => CallSubst n -> CallSubst n -> Bool
approximatesCall tau sigma =
  let indices = map fst $ callSubst tau in
  -- let indices2 = map fst sigma in
  -- if indices /= indices2 then error "PROBLEM..." else
  all (\i -> approximates (getTerm tau i) (getTerm sigma i)) indices

-- TODO: Isolate common pattern of these functions.

-- | Pointwise compatibility for calls.
compatibleCall :: Eq n => CallSubst n -> CallSubst n -> Bool
compatibleCall tau sigma =
  let indices = map fst $ callSubst tau in
  -- let indices2 = map fst sigma in
  -- if indices /= indices2 then error "PROBLEM..." else
  all (\i -> compatible (getTerm tau i) (getTerm sigma i)) indices

-- | The lesser term is the one with less information.
--   Call graph completion keeps the worst calls
--   (those that endanger termination),
--   which corresponds to terms with least information.

instance Eq n => PartialOrd (CallSubst n) where
  comparable = fromLeq approximatesCall

-- | @getSubtree@ is inside the @Maybe@ monad to deal with impossible cases.
getSubtree :: Eq n => [Destructor n] -> Term n -> Maybe (Term n)
getSubtree [] v = return v
getSubtree ds (Approx bs) = return $ Approx $
  map (mapWeight (Number (- length ds) <>)) bs
getSubtree ds (Exact ds' i) = return $ Exact (reverse ds ++ ds') i
getSubtree (Case c1 : ds) (Const c2 v)
  | c1 == c2  = getSubtree ds v
  | otherwise = Nothing     -- IMPOSSIBLE CASE
getSubtree (Proj l : ds) (Record r) =
  case lookup l r of
    Just v  -> getSubtree ds v
    Nothing -> error "TYPING PROBLEM"
getSubtree _ _ = error "TYPING PROBLEM"
  -- TODO: use __IMPOSSIBLE__

-- | Given a term and a substitution (call), apply the substitution.

substitute :: Eq n => Term n -> CallSubst n -> Maybe (Term n)
substitute (Const c u) tau = Const c <$> substitute u tau
substitute (Record r) tau | let (labels, terms) = unzip r =
  Record . zip labels <$> mapM (`substitute` tau) terms
substitute (Exact ds i) tau = getSubtree (reverse ds) (getTerm tau i)
substitute (Approx bs) tau = Approx . nubMax . concat <$> do
  forM bs $ \ (Branch w ds i) -> do
    reduceApprox w <$> getSubtree (reverse ds) (getTerm tau i)

-- | Collapsing the weights.

collapse1 :: Eq n => Bound -> Term n -> Term n
collapse1 b (Const c u) = Const c (collapse1 b u)
collapse1 b (Record r) | let (labels, args) = unzip r =
  Record (zip labels (map (collapse1 b) args))
collapse1 b (Exact ds i) = Exact ds i
collapse1 b (Approx bs) = Approx $ nubMax $ map (mapWeight (collapseZInfty b)) bs

-- | Collapsing the destructors.

collapse2 :: Eq n => Depth -> Term n -> Term n
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

collapse3 :: Eq n => Depth -> Term n -> Term n
collapse3 d (Record r) | let (labels, args) = unzip r =
  Record (zip labels (map (collapse3 d) args))  -- do not decrease depth bound on records
collapse3 0 (Exact ds i) = Exact ds i
collapse3 0 u = Approx $ reduceApprox (Number 0) u
collapse3 d (Const c u) = Const c (collapse3 (d-1) u)
collapse3 d u = u

-- | Collapsing a term.

collapse :: Eq n => Depth -> Bound -> Term n -> Term n
collapse d b u = collapse1 b $ collapse2 d $ collapse3 d u

-- | Collapsing a call.

collapseCall :: Eq n => Depth -> Bound -> CallSubst n -> CallSubst n
collapseCall d b (CallSubst tau) = CallSubst $ map (second (collapse d b)) tau

-- | CallSubst composition (partial).

compose :: Eq n => Depth -> Bound -> CallSubst n -> CallSubst n -> Maybe (CallSubst n)
compose d b tau (CallSubst sigma) = (collapseCall d b . CallSubst <$> do
                                            forM sigma $ \ (i,t) -> (i,) <$> substitute t tau)

instance Eq n => CallComb (CallSubst n) where
  callComb tau sigma = compose d b tau sigma
    where CutOff c = ?cutoff
          b = c + 1
          d = 2*b -- *2 because of the layer of tuples FIXME

isDecreasing :: Eq n => CallSubst n -> Bool
isDecreasing tau = any decr $ callSubst tau
  where
  isOK ds t i = approximates (Approx [Branch (Number (-1)) ds i]) t
  decr (i,t) = aux [] t
    where aux ds (Const c u) = isOK ds t i || aux ((Case c):ds) u
          aux ds (Record r) = isOK ds t i || any (\(n,u) -> aux ((Proj n):ds) u) r
          aux ds t = isOK ds t i


instance Eq n => Idempotent (CallSubst n) where
  idempotent tau = maybe False (compatibleCall tau) (callComb tau tau)
  hasDecrease = isDecreasing
