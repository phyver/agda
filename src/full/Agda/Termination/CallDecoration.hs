{-# LANGUAGE CPP                        #-}
{-# LANGUAGE DeriveFoldable             #-}
{-# LANGUAGE DeriveFunctor              #-}
{-# LANGUAGE DeriveTraversable          #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ImplicitParams             #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE StandaloneDeriving         #-}

-- | Generic labels of the call graph, describing the size change
--   for a call.  Could be call matrices, for instance.

module Agda.Termination.CallDecoration where

import Data.List as List hiding (union, insert)
import Data.Maybe
import Data.Monoid
import Data.Foldable (Foldable)
import qualified Data.Foldable as Fold
import Data.Traversable (Traversable)
import qualified Data.Traversable as Trav

import Agda.Termination.CutOff
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


-- | Call combination.

class CallComb a where
  (>*<)    :: (?cutoff :: CutOff) => a -> a -> a
  callComb :: (?cutoff :: CutOff) => a -> a -> Maybe a

  callComb x y = Just $ x >*< y
  x >*< y = fromMaybe __IMPOSSIBLE__ $ callComb x y

------------------------------------------------------------------------
-- * Call decoration augmented with path information.
------------------------------------------------------------------------

-- | Call relation augmented with path information.

data CallDeco cm cinfo = CallDeco
  { augCallM    :: cm     -- ^ The size change of the (composed) call.
  , augCallInfo :: cinfo  -- ^ Meta info, like call path.
  }
  deriving (Eq, Show)

instance PartialOrd cm => PartialOrd (CallDeco cm cinfo) where
  comparable m m' = comparable (augCallM m) (augCallM m')

instance NotWorse cm => NotWorse (CallDeco cm cinfo) where
  c1 `notWorse` c2 = augCallM c1 `notWorse` augCallM c2

-- | Augmented call matrix multiplication.

instance (CallComb cm, Monoid cinfo) => CallComb (CallDeco cm cinfo) where
  callComb (CallDeco m1 p1) (CallDeco m2 p2) = do
    m <- callComb m1 m2
    return $ CallDeco m (mappend p1 p2)

-- | Non-augmented call matrix.

noAug :: Monoid cinfo => cm -> CallDeco cm cinfo
noAug m = CallDeco m mempty

------------------------------------------------------------------------
-- * Sets of incomparable call matrices augmented with path information.
------------------------------------------------------------------------

-- | Sets of incomparable call matrices augmented with path information.
--   Use overloaded 'null', 'empty', 'singleton', 'mappend'.
newtype CMSet cm cinfo = CMSet { cmSet :: Favorites (CallDeco cm cinfo) }
  deriving ( Show, Arbitrary, CoArbitrary
           , Monoid, Null, Singleton (CallDeco cm cinfo) )

-- | Call matrix set product is the Cartesian product.

instance (PartialOrd cm, CallComb cm, Monoid cinfo) => CallComb (CMSet cm cinfo) where
  CMSet as >*< CMSet bs = CMSet $ Fav.fromList $
    [ m | a <- Fav.toList as, b <- Fav.toList bs, m <- maybeToList (callComb a b) ]

-- | Insert into a call matrix set.

insert :: PartialOrd cm => CallDeco cm cinfo -> CMSet cm cinfo -> CMSet cm cinfo
insert a (CMSet as) = CMSet $ Fav.insert a as

-- | Union two call matrix sets.

union :: PartialOrd cm => CMSet cm cinfo -> CMSet cm cinfo -> CMSet cm cinfo
union = mappend

-- | Convert into a list of augmented call matrices.

toList :: CMSet cm cinfo -> [CallDeco cm cinfo]
toList (CMSet as) = Fav.toList as

------------------------------------------------------------------------
-- * Printing
------------------------------------------------------------------------

instance (Pretty cm, Pretty cinfo) => Pretty (CallDeco cm cinfo) where
  pretty (CallDeco m cinfo) = pretty cinfo $$ pretty m

instance (Pretty cm, Pretty cinfo) => Pretty (CMSet cm cinfo) where
  pretty = vcat . punctuate newLine . map pretty . toList
    where newLine = text "\n"

------------------------------------------------------------------------
-- * Generators
------------------------------------------------------------------------

instance (Arbitrary cm, Arbitrary cinfo) => Arbitrary (CallDeco cm cinfo) where
  arbitrary = CallDeco <$> arbitrary <*> arbitrary

instance (CoArbitrary cm, CoArbitrary cinfo) => CoArbitrary (CallDeco cm cinfo) where
  coarbitrary (CallDeco m info) = coarbitrary m . coarbitrary info
