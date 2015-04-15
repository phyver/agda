{-# LANGUAGE CPP                        #-}
{-# LANGUAGE DeriveFoldable             #-}
{-# LANGUAGE DeriveFunctor              #-}
{-# LANGUAGE DeriveTraversable          #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ImplicitParams             #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE StandaloneDeriving         #-}

module Agda.Termination.CallMatrix where

-- module Agda.Termination.CallMatrix
--   ( CallMatrix'(..), CallMatrix
--   , callMatrix
--   , CallComb(..)
--   , tests
--   ) where

import Data.List as List hiding (union, insert)
import Data.Maybe
import Data.Monoid
import Data.Foldable (Foldable)
import qualified Data.Foldable as Fold
import Data.Traversable (Traversable)
import qualified Data.Traversable as Trav

import Agda.Termination.CutOff
import Agda.Termination.CallDecoration
import Agda.Termination.Order as Order hiding (tests)
import Agda.Termination.SparseMatrix as Matrix hiding (tests)
import Agda.Termination.Semiring (HasZero(..), Semiring)
import qualified Agda.Termination.Semiring as Semiring

import Agda.Utils.Favorites (Favorites)
import qualified Agda.Utils.Favorites as Fav
import Agda.Utils.Monad
import Agda.Utils.Null
import Agda.Utils.PartialOrd hiding (tests)
import Agda.Utils.Pretty hiding ((<>))
import Agda.Utils.QuickCheck
import Agda.Utils.Singleton
import Agda.Utils.TestHelpers

#include "undefined.h"
import Agda.Utils.Impossible

------------------------------------------------------------------------
--  * Call matrices
------------------------------------------------------------------------

-- | Call matrix indices = function argument indices.
--
--   Machine integer 'Int' is sufficient, since we cannot index more arguments
--   than we have addresses on our machine.

type ArgumentIndex = Int

-- | Call matrices.
--
--   A call matrix for a call @f --> g@ has dimensions @ar(g) × ar(f)@.
--
--   Each column corresponds to one formal argument of caller @f@.
--   Each row corresponds to one argument in the call to @g@.
--
--   In the presence of dot patterns, a call argument can be related
--   to /several/ different formal arguments of @f@.
--
--   See e.g. @test/succeed/DotPatternTermination.agda@:
--
--   @
--     data D : Nat -> Set where
--       cz : D zero
--       c1 : forall n -> D n -> D (suc n)
--       c2 : forall n -> D n -> D n
--
--     f : forall n -> D n -> Nat
--     f .zero    cz        = zero
--     f .(suc n) (c1  n d) = f n (c2 n d)
--     f n        (c2 .n d) = f n d
--   @
--
--   Call matrices (without guardedness) are
--
--   @
--           -1 -1   n < suc n  and       n <  c1 n d
--            ?  =                   c2 n d <= c1 n d
--
--            = -1   n <= n     and  n < c2 n d
--            ? -1                   d < c2 n d
--   @
--
--   Here is a part of the original documentation for call matrices
--   (kept for historical reasons):
--
--   This datatype encodes information about a single recursive
--   function application. The columns of the call matrix stand for
--   'source' function arguments (patterns). The rows of the matrix stand for
--   'target' function arguments. Element @(i, j)@ in the matrix should
--   be computed as follows:
--
--     * 'Order.lt' (less than) if the @j@-th argument to the 'target'
--       function is structurally strictly smaller than the @i@-th
--       pattern.
--
--     * 'Order.le' (less than or equal) if the @j@-th argument to the
--       'target' function is structurally smaller than the @i@-th
--       pattern.
--
--     * 'Order.unknown' otherwise.


newtype CallMatrix' a = CallMatrix { mat :: Matrix ArgumentIndex a }
  deriving (Eq, Ord, Show, Functor, Foldable, Traversable, CoArbitrary, PartialOrd, Pretty)

type CallMatrix = CallMatrix' Order

deriving instance NotWorse CallMatrix

instance HasZero a => Diagonal (CallMatrix' a) a where
  diagonal = diagonal . mat

-- | Call matrix multiplication.
--
--   @f --(m1)--> g --(m2)--> h@  is combined to @f --(m2 `mul` m1)--> h@
--
--   Note the reversed order of multiplication:
--   The matrix @c1@ of the second call @g-->h@ in the sequence
--   @f-->g-->h@ is multiplied with the matrix @c2@ of the first call.
--
--   Preconditions:
--   @m1@ has dimensions @ar(g) × ar(f)@.
--   @m2@ has dimensions @ar(h) × ar(g)@.
--
--   Postcondition:
--   @m1 >*< m2@ has dimensions @ar(h) × ar(f)@.

instance CallComb CallMatrix where
  callComb (CallMatrix m1) (CallMatrix m2) = Just $ CallMatrix $ mul orderSemiring m2 m1

{- UNUSED, BUT DON'T REMOVE!
-- | Call matrix addition = minimum = pick worst information.
addCallMatrices :: (?cutoff :: CutOff) => CallMatrix -> CallMatrix -> CallMatrix
addCallMatrices cm1 cm2 = CallMatrix $
  add (Semiring.add orderSemiring) (mat cm1) (mat cm2)
-}

------------------------------------------------------------------------
-- * Call matrix augmented with path information.
------------------------------------------------------------------------

-- | Call matrix augmented with path information.

type CallMatrixAug cinfo = CallDeco CallMatrix cinfo

instance Diagonal (CallMatrixAug cinfo) Order where
  diagonal = diagonal . augCallM


------------------------------------------------------------------------
-- * Printing
------------------------------------------------------------------------

-- instance Pretty CallMatrix where
--   pretty (CallMatrix m) = pretty m

------------------------------------------------------------------------
-- * Generators and tests
------------------------------------------------------------------------

-- ** CallMatrix

instance Arbitrary CallMatrix where
  arbitrary = callMatrix =<< arbitrary

-- | Generates a call matrix of the given size.

callMatrix :: Size ArgumentIndex -> Gen CallMatrix
callMatrix sz = CallMatrix <$> matrix sz

------------------------------------------------------------------------
-- * All tests
------------------------------------------------------------------------

tests :: IO Bool
tests = runTests "Agda.Termination.CallMatrix"
  [
  ]
  where ?cutoff = CutOff 2


-- RETIRED:  LONG OUTDATED call matrix invariant

-- -- | In a call matrix at most one element per row may be different
-- -- from 'unknown'.

-- callMatrixInvariant :: CallMatrix -> Bool
-- callMatrixInvariant (CallMatrix m) =
--   matrixInvariant m &&
--   all ((<= 1) . length . filter (/= unknown)) (toLists m)

-- prop_Arbitrary_CallMatrix = callMatrixInvariant

-- -- | Generates a call matrix of the given size.

-- callMatrix :: Size ArgumentIndex -> Gen CallMatrix
-- callMatrix sz = do
--   m <- matrixUsingRowGen sz rowGen
--   return $ CallMatrix { mat = m }
--   where
--   rowGen :: ArgumentIndex -> Gen [Order]
--   rowGen 0 = return []
--   rowGen n = do
--     x <- arbitrary
--     i <- choose (0, n - 1)
--     return $ genericReplicate i unknown ++ [x] ++
--              genericReplicate (n - 1 - i) unknown

-- prop_callMatrix sz =
--   forAll (callMatrix sz) $ \cm ->
--     callMatrixInvariant cm
--     &&
--     size (mat cm) == sz

-- prop_cmMul sz =
--   forAll natural $ \c2 ->
--   forAll (callMatrix sz) $ \cm1 ->
--   forAll (callMatrix $ Size { rows = cols sz, cols = c2 }) $ \cm2 ->
--     callMatrixInvariant (cm1 >*< cm2)

-- tests :: IO Bool
-- tests = runTests "Agda.Termination.CallMatrix"
--   [ quickCheck' callMatrixInvariant
--   , quickCheck' prop_Arbitrary_CallMatrix
--   , quickCheck' prop_callMatrix
--   , quickCheck' prop_cmMul
--   ]
--   where ?cutoff = DontCutOff -- CutOff 2  -- don't cut off in tests!
