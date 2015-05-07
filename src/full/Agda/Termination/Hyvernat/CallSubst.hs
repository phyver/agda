{-# LANGUAGE CPP #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE PatternGuards  #-}
{-# LANGUAGE TupleSections  #-}

-- | Pierre Hyvernat's refinement of size-change termination by Lee, Jones and
--   Ben-Amram.
--   The test is described in details in the paper
--
--      Pierre Hyvernat,
--      The Size-Change Termination Principle for Constructor Based Languages
--      LMCS 2013
--
--   To each recursive definition
--     f patterns = ... g args ...
--     ...
--     g patterns = ... f args ...
--     ...
--   I associate a call graph. Each "call site" gives an edge from the caller
--   to the called function. For example, "g args" gives an edge from "f" to
--   "g".
--
--   Those edge are labeled by substitutions representing how the arguments of
--   the called function are obtained from the arguments of the calling
--   function.
--   For example, in
--     f (Cons a l) (S n) = ... g l (T n) a
--   is represented by (arg1 := π1 Cons- arg1 , arg2 := T S- arg2 , arg3 := π2 Cons- arg1)
--   (Here, f has two arguments and g has three arguments...)
--     - π1 / π2 are used to identify the number of an argument to a
--       constructor: "a" is the first argument to a "Cons" and "l" is the
--       second argument to a "Cons"
--     - "Cons-" and "S-" are used to indicate pattern matching. They
--       litteraly mean "remove a Cons" or "remove an S".
--     - "T" is a usual constructor.
--   Thus, "arg3 := π2 Cons- arg1" means that the third argument at the call
--   site is obtained from the first argument of the caller by pattern
--   matching on "Cons" and taking the second argument.
--
--   ** NOTE: as per Andreas suggestion, we could replace this
--   ** representation as substitutions by a representation as "rewriting
--   ** rules". The label of the same edge would be
--   **   (Cons x1 x2),(S x3) => x2,(T x3),x1
--   ** This would actually simplify some parts of the implementation...
--
--   I then apply the size-change termination principle on this graph by
--   composing the substitutions. In order to keep the graph finite, I
--   collapse substitutions when they become to big: I only keep constructors
--   up to a given depth and approximate everything that was removed by a
--   "weight": "S S S n" collapsed at depth 1 gives "S <2> n" where the "<2>"
--   stands for "something with at most 2 constructors".
--   The weight themselves are bounded. When they reach a given bound, they
--   are replaced by "<∞>".
--

module Agda.Termination.Hyvernat.CallSubst where

import Data.List
import Data.Monoid
import Data.Functor
import Data.Traversable (forM)
import Control.Arrow (first, second)

import Agda.Utils.PartialOrd
import Agda.Utils.Pretty (Pretty(..), prettyShow, text, align)
#include "undefined.h"
import Agda.Utils.Impossible
import Agda.Auto.Syntax hiding (Const)
import Agda.Syntax.Abstract.Name (QName, qnameName)

import Agda.Termination.CutOff
import Agda.Termination.CallDecoration



-- | The test is parametrized by 2 bounds:
--     - a bound on the weight af approximations: b means approximations
--       belong to {-b, ..., 0, 1, ..., b-1, ∞}
--     - a bound on the depth of constructors we keep
--   The bigger the bounds, the more precise the test.
--   The bounds 1 (for approximations) and 0 (for depth) amounts roughly to
--   the original size-change termination principle.
type Depth = Int  -- ^ cutoff for constructor depth
type Bound = Int  -- ^ cutoff for weight of approximations

-- | Type for depth differences.
--   During an actual termination checking, the number appearing in labels
--   will all be in {-b, ..., 0, 1, ..., b-1, ∞}.
data ZInfty
  =  Number Int
   | Infty
  deriving Eq
instance Ord ZInfty where
  compare Infty Infty = EQ
  compare Infty _ = GT
  compare _ Infty = LT
  compare (Number n) (Number m) = compare n m
instance Pretty ZInfty where
  pretty Infty = text "<∞>"
  pretty (Number n) = text $ "<" ++ (show n) ++ ">"
instance Monoid ZInfty where
  mempty = Number 0
  mappend Infty _ = Infty
  mappend _ Infty = Infty
  mappend (Number n) (Number m) = Number (n+m)

-- | The two kinds of destructors:
--   projections (on a label) and case (on a constructors).
--   Projection are used to access the different arguments of a constructor.
data Destructor
  = Proj String
  | Case QName
  deriving Eq
instance Pretty Destructor where
  pretty (Proj l) = text $ "π_" ++ l
  pretty (Case c) = text $ (prettyShow $ qnameName c) ++ "-"

-- | The arguments of the caller are numbered from "1" to "arity".
type ArgNo = Int

-- | Variables appearing in terms representing argument of a called function
--   can either correspond to argument of the caller, or metavariables.
data Var = Arg ArgNo
         | MetaVar Nat
  deriving Eq
instance Pretty Var where
  pretty (Arg i) = text $ " x_" ++ (prettyShow i)
  pretty (MetaVar i) = text $ " ?_" ++ (prettyShow i)

-- | A "branch" identifies a variable in a pattern: starting from an argument
--   of the calling function, we follow a path given by constructors /
--   projections. The weight allows to approximate some constructor by their
--   number.
type Weight = ZInfty
data Branch = Branch
  { brWeight :: Weight
  , brDests  :: [Destructor]
  , brVar    :: Var
  }
instance Pretty Branch where
  pretty (Branch w ds x) = text $ (prettyShow w) ++ (intercalate " " (map prettyShow ds)) ++ (prettyShow x)

-- | Semantic editor for @Weight@.
mapWeight :: (Weight -> Weight) -> Branch -> Branch
mapWeight f br = br { brWeight = f (brWeight br) }

-- | Term language for approximations.
--   Arguments of the called function are terms constructed from
--     - constructors
--     - records (to allow constructors with several arguments)
--     - variables of patterns, aka branches
--   Those branch can either be "exact", ie correspond exactly to a pattern
--   variable, or "approximated". When they are approximated, we need to keep
--   a "non-deterministic sum" of variables: Node(x1,x2) at depth 0 is
--   approximated by "<1>x1 + <1>x2".
data Term
  = Const QName Term              -- ^ constructor
  | Record [(String , Term)]      -- ^ record
  | Exact [Destructor]  Var       -- ^ "exact" branch of destructors, with argument
  | Approx [Branch]               -- ^ sum of approximations
instance Pretty Term where
  pretty (Const c t)  = text $ prettyShow (qnameName c) ++ " " ++ prettyShow t
  pretty (Record [])   = text "empty record: SHOULDN'T HAPPEN"
  pretty (Record l)   = text $ "{" ++ (intercalate " ; " (map (\(l,t) -> prettyShow l ++ "=" ++ prettyShow t) l)) ++ "}"
  pretty (Exact ds x) = text $ (intercalate " " (map prettyShow ds)) ++ (prettyShow x)
  pretty (Approx [])  = text "empty sum"
  pretty (Approx l)   = text $ intercalate " + " (map (\(Branch w ds x) -> (prettyShow w) ++ (intercalate " " (map prettyShow ds)) ++ (prettyShow x)) l)

-- | A call is a substitution of the arguments (of the called function) by
--   terms (with variables corresponding to arguments of the calling function).
newtype CallSubst = CallSubst { callSubst :: [(ArgNo , Term)] }
    -- NOTE: could be also just [Term]
instance Pretty CallSubst where
  pretty (CallSubst []) = text "...empty substitution..."
  pretty (CallSubst c) = align 10 $ map (\(a,t) -> ("x_" ++ (prettyShow a) ++  " = ", pretty t)) c
instance Show CallSubst where
  show = prettyShow

-- | Collapse the weight of an approximation.
collapseZInfty :: Bound -> ZInfty -> ZInfty
collapseZInfty b Infty = Infty
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

-- | @approximates b1 b2@ is @True@ when b1 is an approximation of b2.
--   Written @b1 <= b2@ (@b2@ is more informative than @b1@).
approximatesDestructors :: Branch -> Branch -> Bool
approximatesDestructors (Branch w1 ds1 x1) (Branch w2 ds2 x2)
  | x1 == x2  = case suffix ds1 ds2 of
                       (_, [], ds2') -> w2 <= w1 <> (Number $ length ds2')
                       otherwise -> False
  | otherwise = False
  -- TODO: instantiate Agda.Utils.PartialOrd

-- | @nubMax@ keeps only maximal branches.
--   The output is a list of incomparable branches.
nubMax :: [Branch] -> [Branch]
nubMax [] = []
nubMax (b:bs) = aux b (nubMax bs)
  where aux b [] = [b]
        aux b (b1:bs)
          | approximatesDestructors b b1  = aux b bs
          | approximatesDestructors b1 b  = aux b1 bs
          | otherwise                      = b1:(aux b bs)
  -- TODO: reuse Agda.Utils.Favorites

-- | Computes the normal form of @<w>v@.
reduceApprox :: ZInfty -> Term -> [Branch]
reduceApprox w (Const _ v) = reduceApprox (w <> (Number 1)) v
reduceApprox w (Record []) = __IMPOSSIBLE__
reduceApprox w (Record l) = nubMax $ concat $ map (reduceApprox (w <> (Number 1))) $ map snd l
reduceApprox w (Approx bs) = nubMax $ map (\(Branch w' ds i) -> (Branch (w <> w') ds i)) bs
reduceApprox w (Exact ds i) = [ Branch w ds i ]

-- | Partial order @approximates t1 t2@ iff @t1 <= t2@.
approximates :: Term -> Term -> Bool
approximates (Exact ds1 i1) (Exact ds2 i2)
  | ds1 == ds2 && i1 == i2 = True
  | otherwise              = False
approximates (Const c1 u1) (Const c2 u2)
  | c1 == c2  = approximates u1 u2
  | otherwise = False
approximates (Record []) _ = __IMPOSSIBLE__
approximates _ (Record []) = __IMPOSSIBLE__
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
instance PartialOrd Term where
  comparable = fromLeq approximates

-- | @compatible t1 t2@ if exists @t0@ such that @t1 <= t0@ and @t2 <= t0@
compatible :: Term -> Term -> Bool
compatible (Exact ds1 i1) (Exact ds2 i2) = ds1 == ds2 && i1 == i2
compatible (Const c1 u1) (Const c2 u2)
  | c1 == c2  = compatible u1 u2
  | otherwise = False
compatible (Record []) _ = __IMPOSSIBLE__
compatible _ (Record []) = __IMPOSSIBLE__
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
getTerm :: CallSubst -> ArgNo -> Term
getTerm (CallSubst tau) i =
  case lookup i tau of
    Just t  -> t
    Nothing -> Approx []  -- TODO: correct?

-- | Pointwise approximation order for calls.
approximatesCall :: CallSubst -> CallSubst -> Bool
approximatesCall tau sigma =
  let indices = map fst $ callSubst tau in
  -- let indices2 = map fst sigma in
  -- if indices /= indices2 then error "PROBLEM..." else
  all (\i -> approximates (getTerm tau i) (getTerm sigma i)) indices

-- TODO: Isolate common pattern of these functions.

-- | Pointwise compatibility for calls.
compatibleCall :: CallSubst -> CallSubst -> Bool
compatibleCall tau sigma =
  let indices = map fst $ callSubst tau in
  -- let indices2 = map fst sigma in
  -- if indices /= indices2 then error "PROBLEM..." else
  all (\i -> compatible (getTerm tau i) (getTerm sigma i)) indices

-- | The lesser term is the one with less information.
--   Call graph completion keeps the worst calls
--   (those that endanger termination),
--   which corresponds to terms with least information.

instance PartialOrd CallSubst where
  comparable = fromLeq approximatesCall

-- | @getSubtree@ is inside the @Maybe@ monad to deal with impossible cases.
getSubtree :: [Destructor] -> Term -> Maybe Term
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
    Nothing -> __IMPOSSIBLE__   -- typing problem
getSubtree _ _ = __IMPOSSIBLE__ -- typing proble

-- | Given a term and a substitution (call), apply the substitution.
substituteVar :: Var -> CallSubst -> Term
substituteVar (Arg i) tau = getTerm tau i
substituteVar (MetaVar i) tau = Exact [] $ MetaVar i

substitute :: Term -> CallSubst -> Maybe Term
substitute (Const c u) tau = Const c <$> substitute u tau
substitute (Record []) _ = __IMPOSSIBLE__
substitute (Record r) tau | let (labels, terms) = unzip r =
  Record . zip labels <$> mapM (`substitute` tau) terms
substitute (Exact ds x) tau = getSubtree (reverse ds) $ substituteVar x tau
substitute (Approx bs) tau = Approx . nubMax . concat <$> do
  forM bs $ \ (Branch w ds x) -> do
    reduceApprox w <$> getSubtree (reverse ds) (substituteVar x tau)

-- | Collapsing the weights inside a term.
collapse1 :: Bound -> Term -> Term
collapse1 b (Const c u) = Const c (collapse1 b u)
collapse1 _ (Record []) = __IMPOSSIBLE__
collapse1 b (Record r) | let (labels, args) = unzip r =
  Record (zip labels (map (collapse1 b) args))
collapse1 b (Exact ds i) = Exact ds i
collapse1 b (Approx bs) = Approx $ nubMax $ map (mapWeight (collapseZInfty b)) bs

-- | check if a destructor is a Case
isCase :: Destructor -> Bool
isCase (Case _) = True
isCase (Proj _) = False

-- | number of Case destructors inside a list
weight :: [Destructor] -> Int
weight d = foldl (\n d -> if isCase d then n+1 else n) 0 d

-- | drop the beginning of a list of destructors so that the result has less
--   than d "Case" destructors
collapseDestructors :: Depth -> Branch -> Branch
collapseDestructors d (Branch wo ds i) =
    let (w,ds2) = aux d (reverse ds) in
    Branch (Number w <> wo) (reverse ds2) i
  where aux :: Depth -> [Destructor] => (Int, [Destructor])
        aux d [] = (0, [])
        aux d (Proj l : ds) = let (w,ds2) = aux d ds in (w, Proj l : ds2)
        aux 0 ds = (- (weight ds), [])
        aux d (Case c : ds) = let (w,ds2) = aux (d-1) ds in (w, Case c : ds2)

-- | Collapsing the destructors in a term.
collapse2 :: Depth -> Term -> Term
collapse2 d (Const c u) = Const c (collapse2 d u)
collapse2 _ (Record []) = __IMPOSSIBLE__
collapse2 d (Record r) | let (labels, args) = unzip r =
  Record (zip labels (map (collapse2 d) args))
collapse2 d (Exact ds i) = let n = weight ds in
  if n <= d
  then Exact ds i
  -- else Approx [Branch (Number (d-n)) (drop (n-d) ds) i]
  else Approx [collapseDestructors d (Branch (Number 0) ds i)]
collapse2 d (Approx bs) = Approx $ nubMax $
  map (collapseDestructors d) bs
  -- map (\ (Branch w ds i) -> let n=length ds in
  --        if n>d then Branch (w <> (Number (d-n))) (drop (n-d) ds) i
  --        else Branch w ds i)
  --     bs

-- | Collapsing constructors.
collapse3 :: Depth -> Term -> Term
collapse3 _ (Record []) = __IMPOSSIBLE__
collapse3 d (Record r) | let (labels, args) = unzip r =
  Record (zip labels (map (collapse3 d) args))  -- do not decrease depth bound on records
collapse3 0 (Exact ds i) = Exact ds i
collapse3 0 u = Approx $ reduceApprox (Number 0) u
collapse3 d (Const c u) = Const c (collapse3 (d-1) u)
collapse3 d u = u

-- | Collapsing a term.
collapse :: Depth -> Bound -> Term -> Term
collapse d b u = collapse1 b $ collapse2 d $ collapse3 d u

-- | Collapsing a call.
collapseCall :: Depth -> Bound -> CallSubst -> CallSubst
collapseCall d b (CallSubst tau) = CallSubst $ map (second (collapse d b)) tau

-- | CallSubst composition (partial).
compose :: Depth -> Bound -> CallSubst -> CallSubst -> Maybe CallSubst
compose d b tau (CallSubst sigma) = (collapseCall d b . CallSubst <$> do
                                            forM sigma $ \ (i,t) -> (i,) <$> substitute t tau)

instance CallComb CallSubst where
  callComb tau sigma = compose d b tau sigma
    where CutOff c = ?cutoff
          b = max 1 c  -- weight bound cannot be 0
          d = max 0 b  -- FIXME: need to be able to give both bounds independently

isDecreasing :: CallSubst -> Bool
isDecreasing (CallSubst tau) = any decr tau
  where
  decr (i,t) = aux [] t
    where aux ds (Const c u) = isOK ds t || aux ((Case c):ds) u
          aux _ (Record []) = __IMPOSSIBLE__
          aux ds (Record r) = isOK ds t || any (\(n,u) -> aux ((Proj n):ds) u) r
          aux ds t = isOK ds t
          isOK ds t = approximates (Approx [Branch (Number (-1)) ds $ Arg i]) $ removeMeta t
          removeMeta (Const n t) = Const n $ removeMeta t
          removeMeta (Record rs) = Record $ map (\(l,t) -> (l, removeMeta t)) rs
          removeMeta (Exact ds (Arg i)) = Exact ds (Arg i)
          removeMeta (Exact ds (MetaVar i)) = Approx []
          removeMeta (Approx s) = Approx [Branch w ds (Arg i) | Branch w ds (Arg i) <- s]

instance Idempotent CallSubst where
  idempotent tau = maybe False (compatibleCall tau) (callComb tau tau)
  hasDecrease = isDecreasing
