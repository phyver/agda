{-# LANGUAGE CPP #-} -- GHC 7.4.2 requires this indentation. See Issue 1460.
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ImplicitParams             #-}
{-# LANGUAGE NamedFieldPuns             #-}
{-# LANGUAGE PatternGuards              #-}
{-# LANGUAGE StandaloneDeriving         #-}
{-# LANGUAGE TupleSections              #-}

-- | Create call matrix for a call.

module Agda.Termination.CallToMatrix where

import Prelude hiding (null)

import Control.Applicative hiding (empty)
import Control.Monad.State

import Data.Foldable (toList)
import Data.List hiding (null)
import qualified Data.List as List
import Data.Maybe (mapMaybe, isJust, fromMaybe)
import Data.Monoid
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Traversable (traverse)

import Agda.Syntax.Abstract (IsProjP(..), AllNames(..))
import qualified Agda.Syntax.Abstract as A
import Agda.Syntax.Internal as I
import qualified Agda.Syntax.Info as Info
import Agda.Syntax.Position
import Agda.Syntax.Common as Common
import Agda.Syntax.Literal (Literal(LitString))

import Agda.Termination.CutOff
import Agda.Termination.Monad
import Agda.Termination.CallGraph hiding (toList)
import qualified Agda.Termination.CallGraph as CallGraph
import Agda.Termination.CallMatrix
import Agda.Termination.Order     as Order
import qualified Agda.Termination.SparseMatrix as Matrix
import Agda.Termination.Termination (endos, idempotent)
import qualified Agda.Termination.Termination  as Term
import Agda.Termination.RecCheck
import Agda.Termination.Inlining

import Agda.TypeChecking.Monad
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Reduce (reduce, normalise, instantiate, instantiateFull)
import Agda.TypeChecking.Records -- (isRecordConstructor, isInductiveRecord)
import Agda.TypeChecking.Telescope
import Agda.TypeChecking.EtaContract
import Agda.TypeChecking.Monad.Builtin
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.SizedTypes
import Agda.TypeChecking.Datatypes

import qualified Agda.TypeChecking.Monad.Base.Benchmark as Benchmark
import Agda.TypeChecking.Monad.Benchmark (billTo, billPureTo)

import Agda.Interaction.Options

import Agda.Utils.Either
import Agda.Utils.Function
import Agda.Utils.Functor (($>), (<.>))
import Agda.Utils.List
import Agda.Utils.Size
import Agda.Utils.Maybe
import Agda.Utils.Monad -- (mapM', forM', ifM, or2M, and2M)
import Agda.Utils.Null
import Agda.Utils.Permutation
import Agda.Utils.Pretty (render)
import Agda.Utils.Singleton
import Agda.Utils.VarSet (VarSet)
import qualified Agda.Utils.VarSet as VarSet

#include "undefined.h"
import Agda.Utils.Impossible

-- | Entry point.
--   Turn guardedness and arguments (eliminations) of a call into a call matrix.
class ElimsToCall a where
  elimsToCall :: Order -> [Elim] -> TerM a

instance ElimsToCall CallMatrix where
  elimsToCall g es = do
    cutoff <- terGetCutOff
    let ?cutoff = cutoff
    (nr, nc, m) <- compareArgs es
    return $ makeCM nr nc $ composeGuardedness g m

{- | @compareArgs es@

     Compare the list of de Bruijn patterns (=parameters) @pats@
     with a list of arguments @es@ and create a call maxtrix
     with |es| rows and |pats| columns.

     The guardedness is the number of projection patterns in @pats@
     minus the number of projections in @es@.
 -}
compareArgs :: (Integral n) => [Elim] -> TerM (n, n, [[Order]])
compareArgs es = do
  pats <- terGetPatterns
  -- apats <- annotatePatsWithUseSizeLt pats
  -- reportSDoc "term.compare" 20 $
  --   text "annotated patterns = " <+> sep (map prettyTCM apats)
  -- matrix <- forM es $ \ e -> forM apats $ \ (b, p) -> terSetUseSizeLt b $ compareElim e p
  matrix <- withUsableVars pats $ forM es $ \ e -> forM pats $ \ p -> compareElim e p

  -- Count the number of coinductive projection(pattern)s in caller and callee.
  -- Only recursive coinductive projections are eligible (Issue 1209).
  projsCaller <- genericLength <$> do
    filterM (isCoinductiveProjection True) $ mapMaybe (isProjP . getMasked) pats
  projsCallee <- genericLength <$> do
    filterM (isCoinductiveProjection True) $ mapMaybe isProjElim es
  cutoff <- terGetCutOff
  let ?cutoff = cutoff
  let guardedness = decr $ projsCaller - projsCallee
  liftTCM $ reportSLn "term.guardedness" 30 $
    "compareArgs: guardedness of call: " ++ show guardedness
  return $ addGuardedness guardedness (size es) (size pats) matrix

-- | Traverse patterns from left to right.
--   When we come to a projection pattern,
--   switch usage of SIZELT constraints:
--   on, if coinductive,
--   off, if inductive.
--
--   UNUSED
annotatePatsWithUseSizeLt :: [DeBruijnPat] -> TerM [(Bool,DeBruijnPat)]
annotatePatsWithUseSizeLt = loop where
  loop [] = return []
  loop (p@(ProjDBP q) : pats) = ((False,p) :) <$> do projUseSizeLt q $ loop pats
  loop (p : pats) = (\ b ps -> (b,p) : ps) <$> terGetUseSizeLt <*> loop pats


-- | @compareElim e dbpat@

compareElim :: Elim -> Masked DeBruijnPat -> TerM Order
compareElim e p = do
  liftTCM $ do
    reportSDoc "term.compare" 30 $ sep
      [ text "compareElim"
      , nest 2 $ text "e = " <+> prettyTCM e
      , nest 2 $ text "p = " <+> prettyTCM p
      ]
    reportSDoc "term.compare" 50 $ sep
      [ nest 2 $ text $ "e = " ++ show e
      , nest 2 $ text $ "p = " ++ show p
      ]
  case (e, getMasked p) of
    (Proj d, ProjDBP d')           -> compareProj d d'
    (Proj{}, _         )           -> return Order.unknown
    (Apply{}, ProjDBP{})           -> return Order.unknown
    (Apply arg, _)                 -> compareTerm (unArg arg) p

-- | In dependent records, the types of later fields may depend on the
--   values of earlier fields.  Thus when defining an inhabitant of a
--   dependent record type such as Σ by copattern matching,
--   a recursive call eliminated by an earlier projection (proj₁) might
--   occur in the definition at a later projection (proj₂).
--   Thus, earlier projections are considered "smaller" when
--   comparing copattern spines.  This is an ok approximation
--   of the actual dependency order.
--   See issues 906, 942.
compareProj :: MonadTCM tcm => QName -> QName -> tcm Order
compareProj d d'
  | d == d' = return Order.le
  | otherwise = liftTCM $ do
      -- different projections
      mr  <- getRecordOfField d
      mr' <- getRecordOfField d'
      case (mr, mr') of
        (Just r, Just r') | r == r' -> do
          -- of same record
          def <- theDef <$> getConstInfo r
          case def of
            Record{ recFields = fs } -> do
              fs <- return $ map unArg fs
              case (find (d==) fs, find (d'==) fs) of
                (Just i, Just i')
                  -- earlier field is smaller
                  | i < i'    -> return Order.lt
                  | i == i'   -> do
                     __IMPOSSIBLE__
                  | otherwise -> return Order.unknown
                _ -> __IMPOSSIBLE__
            _ -> __IMPOSSIBLE__
        _ -> return Order.unknown

-- | 'makeCM' turns the result of 'compareArgs' into a proper call matrix
makeCM :: Int -> Int -> [[Order]] -> CallMatrix
makeCM ncols nrows matrix = CallMatrix $
  Matrix.fromLists (Matrix.Size nrows ncols) matrix

{- To turn off guardedness, restore this code.
-- | 'addGuardedness' does nothing.
addGuardedness :: Integral n => Order -> n -> n -> [[Order]] -> (n, n, [[Order]])
addGuardedness g nrows ncols m = (nrows, ncols, m)
-}

-- | 'addGuardedness' adds guardedness flag in the upper left corner (0,0).
addGuardedness :: Integral n => Order -> n -> n -> [[Order]] -> (n, n, [[Order]])
addGuardedness o nrows ncols m =
  (nrows + 1, ncols + 1,
   (o : genericReplicate ncols Order.unknown) : map (Order.unknown :) m)

-- | Compose something with the upper-left corner of a call matrix
composeGuardedness :: (?cutoff :: CutOff) => Order -> [[Order]] -> [[Order]]
composeGuardedness o ((corner : row) : rows) = ((o .*. corner) : row) : rows
composeGuardedness _ _ = __IMPOSSIBLE__

-- | Stripping off a record constructor is not counted as decrease, in
--   contrast to a data constructor.
--   A record constructor increases/decreases by 0, a data constructor by 1.
offsetFromConstructor :: MonadTCM tcm => QName -> tcm Int
offsetFromConstructor c = maybe 1 (const 0) <$> do
  liftTCM $ isRecordConstructor c

-- | Compute the proper subpatterns of a 'DeBruijnPat'.
subPatterns :: DeBruijnPat -> [DeBruijnPat]
subPatterns p = case p of
  ConDBP c ps -> ps ++ concatMap subPatterns ps
  VarDBP _    -> []
  LitDBP _    -> []
  TermDBP _   -> []
  ProjDBP _   -> []

compareTerm :: Term -> Masked DeBruijnPat -> TerM Order
compareTerm t p = do
--   reportSDoc "term.compare" 25 $
--     text " comparing term " <+> prettyTCM t <+>
--     text " to pattern " <+> prettyTCM p
  t <- liftTCM $ stripAllProjections t
  o <- compareTerm' t p
  liftTCM $ reportSDoc "term.compare" 25 $
    text " comparing term " <+> prettyTCM t <+>
    text " to pattern " <+> prettyTCM p <+>
    text (" results in " ++ show o)
  return o
{-
compareTerm t p = Order.supremum $ compareTerm' t p : map cmp (subPatterns p)
  where
    cmp p' = (Order..*.) Order.lt (compareTerm' t p')
-}


-- | Remove all non-coinductive projections from an algebraic term
--   (not going under binders).
--   Also, remove 'DontCare's.
class StripAllProjections a where
  stripAllProjections :: a -> TCM a

instance StripAllProjections a => StripAllProjections (I.Arg a) where
  stripAllProjections = traverse stripAllProjections
  -- stripAllProjections (Arg info a) = Arg info <$> stripAllProjections a

{- DOES NOT WORK, since s.th. special is needed for Elims
instance StripAllProjections a => StripAllProjections [a] where
  stripAllProjections = traverse stripAllProjections

instance StripAllProjections a => StripAllProjections (Elim' a) where
-}

instance StripAllProjections Elims where
  stripAllProjections es =
    case es of
      []             -> return []
      (Apply a : es) -> do
        (:) <$> (Apply <$> stripAllProjections a) <*> stripAllProjections es
      (Proj p  : es) -> do
        isP <- isProjectionButNotCoinductive p
        applyUnless isP (Proj p :) <$> stripAllProjections es

instance StripAllProjections Args where
  stripAllProjections = mapM stripAllProjections

instance StripAllProjections Term where
  stripAllProjections t = do
    case ignoreSharing t of
      Var i es   -> Var i <$> stripAllProjections es
      Con c ts   -> Con c <$> stripAllProjections ts
      Def d es   -> Def d <$> stripAllProjections es
      DontCare t -> stripAllProjections t
      _ -> return t

-- | @compareTerm' t dbpat@
--
--   Precondition: top meta variable resolved

compareTerm' :: Term -> Masked DeBruijnPat -> TerM Order
compareTerm' v mp@(Masked m p) = do
  suc  <- terGetSizeSuc
  cutoff <- terGetCutOff
  let ?cutoff = cutoff
  v <- return $ ignoreSharing v
  case (v, p) of

    -- Andreas, 2013-11-20 do not drop projections,
    -- in any case not coinductive ones!:
    (Var i es, _) | Just{} <- allApplyElims es ->
      compareVar i mp

    (DontCare t, _) ->
      compareTerm' t mp

    -- Andreas, 2014-09-22, issue 1281:
    -- For metas, termination checking should be optimistic.
    -- If there is any instance of the meta making termination
    -- checking succeed, then we should not fail.
    -- Thus, we assume the meta will be instantiated with the
    -- deepest variable in @p@.
    -- For sized types, the depth is maximally
    -- the number of SIZELT hypotheses one can have in a context.
    (MetaV{}, p) -> Order.decr . max (if m then 0 else patternDepth p) . pred <$>
       terAsks _terSizeDepth

    -- Successor on both sides cancel each other.
    -- We ignore the mask for sizes.
    (Def s [Apply t], ConDBP s' [p]) | s == s' && Just s == suc ->
      compareTerm' (unArg t) (notMasked p)

    -- Register also size increase.
    (Def s [Apply t], p) | Just s == suc ->
      -- Andreas, 2012-10-19 do not cut off here
      increase 1 <$> compareTerm' (unArg t) mp

    -- In all cases that do not concern sizes,
    -- we cannot continue if pattern is masked.

    _ | m -> return Order.unknown

    (Lit l, LitDBP l')
      | l == l'     -> return Order.le
      | otherwise   -> return Order.unknown

    (Lit l, _) -> do
      v <- liftTCM $ constructorForm v
      case ignoreSharing v of
        Lit{}       -> return Order.unknown
        v           -> compareTerm' v mp

    -- Andreas, 2011-04-19 give subterm priority over matrix order

    (Con{}, ConDBP c ps) | any (isSubTerm v) ps ->
      decrease <$> offsetFromConstructor c <*> return Order.le

    (Con c ts, ConDBP c' ps) | conName c == c'->
      compareConArgs ts ps

    (Con c [], _) -> return Order.le

    -- new case for counting constructors / projections
    -- register also increase
    (Con c ts, _) -> do
      increase <$> offsetFromConstructor (conName c)
               <*> (infimum <$> mapM (\ t -> compareTerm' (unArg t) mp) ts)

    (t, p) -> return $ subTerm t p

-- | @subTerm@ computes a size difference (Order)
subTerm :: (?cutoff :: CutOff) => Term -> DeBruijnPat -> Order
subTerm t p = if equal t p then Order.le else properSubTerm t p
  where
    equal (Shared p) dbp = equal (derefPtr p) dbp
    equal (Con c ts) (ConDBP c' ps) =
      and $ (conName c == c')
          : (length ts == length ps)
          : zipWith equal (map unArg ts) ps
    equal (Var i []) (VarDBP i') = i == i'
    equal (Lit l)    (LitDBP l') = l == l'
    -- Terms.
    -- Checking for identity here is very fragile.
    -- However, we cannot do much more, as we are not allowed to normalize t.
    -- (It might diverge, and we are just in the process of termination checking.)
    equal t         (TermDBP t') = t == t'
    equal _ _ = False

    properSubTerm t (ConDBP _ ps) = decrease 1 $ supremum $ map (subTerm t) ps
    properSubTerm _ _ = Order.unknown

isSubTerm :: (?cutoff :: CutOff) => Term -> DeBruijnPat -> Bool
isSubTerm t p = nonIncreasing $ subTerm t p

compareConArgs :: Args -> [DeBruijnPat] -> TerM Order
compareConArgs ts ps = do
  cutoff <- terGetCutOff
  let ?cutoff = cutoff
  -- we may assume |ps| >= |ts|, otherwise c ps would be of functional type
  -- which is impossible
  case (length ts, length ps) of
    (0,0) -> return Order.le        -- c <= c
    (0,1) -> return Order.unknown   -- c not<= c x
    (1,0) -> __IMPOSSIBLE__
    (1,1) -> compareTerm' (unArg (head ts)) (notMasked (head ps))
    (_,_) -> foldl (Order..*.) Order.le <$>
               zipWithM compareTerm' (map unArg ts) (map notMasked ps)
       -- corresponds to taking the size, not the height
       -- allows examples like (x, y) < (Succ x, y)
{- version which does an "order matrix"
   -- Andreas, 2013-02-18 disabled because it is unclear
   -- how to scale idempotency test to matrix-shaped orders (need thinking/researcH)
   -- Trigges issue 787.
        (_,_) -> do -- build "call matrix"
          m <- mapM (\t -> mapM (compareTerm' suc (unArg t)) ps) ts
          let m2 = makeCM (genericLength ps) (genericLength ts) m
          return $ Order.orderMat (Order.mat m2)
-}
{- version which takes height
--    if null ts then Order.Le
--               else Order.infimum (zipWith compareTerm' (map unArg ts) ps)
-}

compareVar :: Nat -> Masked DeBruijnPat -> TerM Order
compareVar i (Masked m p) = do
  suc    <- terGetSizeSuc
  cutoff <- terGetCutOff
  let ?cutoff = cutoff
  let no = return Order.unknown
  case p of
    ProjDBP{}   -> no
    LitDBP{}    -> no
    TermDBP{}   -> no
    VarDBP j    -> compareVarVar i (Masked m j)
    ConDBP s [p] | Just s == suc -> decrease 1 <$> compareVar i (notMasked p)
    ConDBP c ps -> if m then no else do
      decrease <$> offsetFromConstructor c
               <*> (Order.supremum <$> mapM (compareVar i . notMasked) ps)

-- | Compare two variables.
--
--   The first variable comes from a term, the second from a pattern.
compareVarVar :: Nat -> Masked Nat -> TerM Order
compareVarVar i (Masked m j)
  | i == j    = if not m then return Order.le else liftTCM $
      -- If j is a size, we ignore the mask.
      ifM (isJust <$> do isSizeType =<< reduce =<< typeOfBV j)
        {- then -} (return Order.le)
        {- else -} (return Order.unknown)
  | otherwise = ifNotM ((i `VarSet.member`) <$> terGetUsableVars) (return Order.unknown) $ {- else -} do
      res <- isBounded i
      case res of
        BoundedNo  -> return Order.unknown
        BoundedLt v -> decrease 1 <$> compareTerm' v (Masked  m (VarDBP j))
