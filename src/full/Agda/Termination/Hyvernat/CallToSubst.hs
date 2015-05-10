{-# LANGUAGE CPP #-} -- GHC 7.4.2 requires this indentation. See Issue 1460.
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ImplicitParams             #-}
{-# LANGUAGE NamedFieldPuns             #-}
{-# LANGUAGE PatternGuards              #-}
{-# LANGUAGE StandaloneDeriving         #-}
{-# LANGUAGE TupleSections              #-}

{- | Create call substitution for a call.

For example,
@
  f (c x) (d y z) = ... g x (d x y) (zip x y) ...
@
Patterns become
@
  x := c- f1
  y := π₁ d- f2
  z := π₂ d- f2
@
Arguments become
@
  g1 := x     = c- f1
  g2 := d x y = d (c- f1 , π₁ d- f2)
  g3 := <∞> (f1 + f2)
@
-}
module Agda.Termination.Hyvernat.CallToSubst where

import Prelude hiding (null)

import Control.Monad.Trans

import Data.Foldable (toList)
import Data.List hiding (null)
import qualified Data.List as List
import Data.Maybe (mapMaybe, isJust, fromMaybe)
import Data.Monoid
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Traversable (forM, traverse)
import Control.Arrow (first, second)

import qualified Agda.Syntax.Internal as I
import Agda.Syntax.Common as Common
import Agda.Syntax.Abstract.Name

import Agda.Termination.CutOff
import Agda.Termination.Monad
import Agda.Termination.Order as Order
import Agda.Termination.CallDecoration
import Agda.Termination.CallToMatrix (ElimsToCall(..))

import Agda.Termination.Hyvernat.CallSubst as CallSubst

import Agda.TypeChecking.Monad hiding (Record)
import Agda.TypeChecking.Monad.Builtin
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Reduce

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

instance ElimsToCall CallSubst where
  elimsToCall g es = do
    cutoff <- terGetCutOff
    let ?cutoff = cutoff
    pats <- terGetPatterns
    let tau = invertPatterns pats
    sigma <- liftTCM $ callElims es
    return $ addInfty $ CallSubst tau >*< sigma

{- | Process patterns.

For example,
@
  f .e (c x) (d y z) = ... g x (d x y) (zip x y) ...
@
Patterns become
@
  x := c- f2
  y := π₁ d- f3
  z := π₂ d- f3
@
-}

-- | @addInfty@ replaces all empty approximations Approx [] by the "infinity
--   element". (<∞> x1 + <∞> x2 + ... + <∞> xn)
--   Those empty approximation (should) only arise from arguments with unknow
--   size:
--     - constants: which we cannot compare to any argument
--     - function calls
addInfty :: CallSubst -> CallSubst
addInfty (CallSubst tau) = CallSubst $ map (second $ addInftyTerm ((length tau)-1)) tau

addInftyTerm :: Int -> Term -> Term
addInftyTerm nbArgs (Const n t) = Const n $ addInftyTerm nbArgs t
addInftyTerm nbArgs (Record []) = Approx [Branch Infty [] $ CallSubst.Arg n | n <- [1..nbArgs]]
addInftyTerm nbArgs (Record r) = Record $ map (second $ addInftyTerm nbArgs) r
addInftyTerm nbArgs (Approx []) = Approx [Branch Infty [] $ CallSubst.Arg n | n <- [1..nbArgs]]
addInftyTerm _ t = t


-- NOTE: projection are at the end of the list of patterns
getCoPatterns:: MaskedDeBruijnPats -> [ Destructor ]
getCoPatterns ps = [ Case n | Masked False (ProjDBP n) <- ps ]



type DeBruijnIndex = Int

invertPatterns :: MaskedDeBruijnPats -> [ (DeBruijnIndex, Term) ]
invertPatterns ps = (-1, Exact (getCoPatterns ps) (CallSubst.Arg 0)) : (concat $ map aux (zip ps [1..]))
  where aux (Masked masked p, argNo) = if masked
                                       then []
                                       else map (second $ \ds -> Exact (reverse ds) $ CallSubst.Arg argNo) (invertPattern p)


-- | Beware, this function return the list of destructors in reverse order!
--   The calling function (invertPatterns) should thus reverse its result...
invertPattern :: DeBruijnPat -> [ (DeBruijnIndex, [Destructor]) ]
invertPattern p =
  case p of
    VarDBP i -> return (i, [])
    ConDBP c [] -> mzero
    ConDBP c [p] -> map (second (Case c :)) $ invertPattern p
    ConDBP c ps -> concat $ map (\(pat, pr) -> map (second (\ds -> Case c : Proj pr : ds)) $ invertPattern pat) $ zip ps $ map show [1..]
    LitDBP{}  -> mzero
    TermDBP{} -> mzero
    ProjDBP n -> mzero  -- projection on a argument. Can I use it?

{- | Process call arguments

For example,
@
  f (c x) (d y z) = ... g x (d x y) (zip x y) ...
@
Arguments become
@
  g1 := x
  g2 := d x y
  g3 := ∞
@
 -}

-- NOTE: projections are at the end of the list of elims.
callProjections :: [I.Elim] -> Term
callProjections [] = Exact [] $ CallSubst.Arg (-1)
callProjections (I.Proj n : cs) = Const n (callProjections cs)
callProjections (I.Apply _ : cs) = Exact  [] $ CallSubst.Arg (-1)


callElims :: [I.Elim] -> TCM CallSubst
callElims es = CallSubst <$> do
  el <- forM (zip es [1..]) $ \ (e, argNo) -> ((argNo,) <$> callElim e)
  return $ (0, callProjections $ reverse es) : el

callElim :: I.Elim -> TCM Term
callElim e =
  case e of
    I.Proj{}          -> return $ infty
    I.Apply (Common.Arg _ a) -> callArg a
  where
    infty = Approx []

callArg :: I.Term -> TCM Term
callArg v =
  case I.ignoreSharing v of
    I.Var i _    -> return $ Exact [] $ CallSubst.Arg i
    I.Con c []   -> return $ Const (I.conName c) infty  -- constant: we cannot compare it with anything
    I.Con c [v]  -> do
                       t <- callArg $ unArg v
                       return $ Const (I.conName c) t
    I.Con c vs   -> Const (I.conName c) . Record <$>
      zipWithM (\ v pr -> (show pr,) <$> callArg (unArg v)) vs [1..]
    I.Lit{} ->  do
      v <- liftTCM $ constructorForm v
      case I.ignoreSharing v of
        I.Lit{} -> return infty
        v       -> callArg v
    I.Def f es   -> return infty
    I.Lam{}      -> return infty -- not a first-order value
    I.Pi{}       -> return infty
    I.Sort{}     -> return infty
    I.Level{}    -> return infty
    I.MetaV x es -> return $ Exact [] $ CallSubst.MetaVar $ I.metaId x
    I.DontCare v -> callArg v
    I.Shared{}   -> __IMPOSSIBLE__
    I.ExtLam{}   -> __IMPOSSIBLE__
  where
    infty = Approx []