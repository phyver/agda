{-# LANGUAGE CPP #-} -- GHC 7.4.2 requires this indentation. See Issue 1460.
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ImplicitParams             #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE StandaloneDeriving         #-}
{-# LANGUAGE TupleSections              #-}

-- | Call graphs and related concepts, more or less as defined in
--     \"A Predicative Analysis of Structural Recursion\" by
--     Andreas Abel and Thorsten Altenkirch.

-- Originally copied from Agda1 sources.

module Agda.Termination.CallGraph
  ( -- * Calls
    Node
  , Call, mkCall, mkCall', source, target, callMatrixSet
  , (>*<)
    -- * Call graphs
  , CallGraph(..)
  , targetNodes
  , fromList
  , toList
  , union
  , insert
  , complete, completionStep
  -- , prettyBehaviour
    -- * Tests
  , Agda.Termination.CallGraph.tests
  ) where

import Prelude hiding (null)

import Data.Foldable (Foldable)
import qualified Data.Foldable as Fold
import Data.Function
import qualified Data.List as List
import Data.Map (Map, (!))
import qualified Data.Map as Map
import Data.Maybe
import Data.Monoid
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Traversable (Traversable)
import qualified Data.Traversable as Trav

import Agda.Termination.CallMatrix (CallMatrix, callMatrix, CallMatrixAug(..), CMSet(..), CallComb(..))
import qualified Agda.Termination.CallMatrix as CMSet
import Agda.Termination.CutOff
import Agda.Termination.Order
import Agda.Termination.SparseMatrix as Matrix hiding (tests)
import Agda.Termination.Semiring (HasZero(..), Semiring)
import qualified Agda.Termination.Semiring as Semiring

import Agda.Utils.Favorites (Favorites(Favorites))
import qualified Agda.Utils.Favorites as Fav
import Agda.Utils.Graph.AdjacencyMap.Unidirectional (Edge(..),Graph(..))
import qualified Agda.Utils.Graph.AdjacencyMap.Unidirectional as Graph

import Agda.Utils.Function
import Agda.Utils.List hiding (tests)
import Agda.Utils.Map
import Agda.Utils.Maybe
import Agda.Utils.Monad
import Agda.Utils.Null
import Agda.Utils.PartialOrd
import Agda.Utils.Pretty
import Agda.Utils.QuickCheck hiding (label)
import Agda.Utils.Singleton
import Agda.Utils.TestHelpers
import Agda.Utils.Tuple

#include "undefined.h"
import Agda.Utils.Impossible

------------------------------------------------------------------------
-- Calls

-- | Call graph nodes.
--
--   Machine integer 'Int' is sufficient, since we cannot index more than
--   we have addresses on our machine.

type Node = Int

-- | Calls are edges in the call graph.
--   It can be labelled with several call matrices if there
--   are several pathes from one function to another.

type Call cinfo = Edge Node Node (CMSet cinfo)

callMatrixSet :: Call cinfo -> CMSet cinfo
callMatrixSet = label

-- | Make a call with a single matrix.
mkCall :: Node -> Node -> CallMatrix -> cinfo -> Call cinfo
mkCall s t m cinfo = Edge s t $ singleton $ CallMatrixAug m cinfo

-- | Make a call with empty @cinfo@.
mkCall' :: Monoid cinfo => Node -> Node -> CallMatrix -> Call cinfo
mkCall' s t m = mkCall s t m mempty

-- | 'Call' combination.
--
--   @f --(c1)--> g --(c2)--> h@  is combined to @f --(c1 >*< c2)--> h@
--
--   Precondition: @source c1 == target c2@

instance Monoid cinfo => CallComb (Call cinfo) where
  c1 >*< c2 | g == g' = Edge f h (label c1 >*< label c2)
    where f  = source c2
          g  = target c2
          g' = source c1
          h  = target c1
  c1 >*< c2 = __IMPOSSIBLE__

------------------------------------------------------------------------
-- Call graphs

-- | A call graph is a set of calls. Every call also has some
-- associated meta information, which should be 'Monoid'al so that the
-- meta information for different calls can be combined when the calls
-- are combined.

newtype CallGraph cinfo = CallGraph { theCallGraph :: Graph Node Node (CMSet cinfo) }
  deriving (Show)


-- | Returns all the nodes with incoming edges.  Somewhat expensive. @O(e)@.

targetNodes :: CallGraph cinfo -> Set Node
targetNodes = Graph.targetNodes . theCallGraph

-- | Converts a call graph to a list of calls with associated meta
--   information.

toList :: CallGraph cinfo -> [Call cinfo]
toList = Graph.edges . theCallGraph

-- | Converts a list of calls with associated meta information to a
--   call graph.

fromList :: Monoid cinfo => [Call cinfo] -> CallGraph cinfo
fromList = CallGraph . Graph.fromListWith CMSet.union

-- | 'null' checks whether the call graph is completely disconnected.
instance Null (CallGraph cinfo) where
  empty = CallGraph Graph.empty
  null  = List.all (null . label) . toList

-- | Takes the union of two call graphs.

union :: Monoid cinfo
      => CallGraph cinfo -> CallGraph cinfo -> CallGraph cinfo
union (CallGraph cs1) (CallGraph cs2) = CallGraph $
  Graph.unionWith CMSet.union cs1 cs2

-- | 'CallGraph' is a monoid under 'union'.

instance Monoid cinfo => Monoid (CallGraph cinfo) where
  mempty  = empty
  mappend = union

-- | Inserts a call into a call graph.

insert :: Monoid cinfo
       => Node -> Node -> CallMatrix -> cinfo
       -> CallGraph cinfo -> CallGraph cinfo
insert s t cm cinfo = CallGraph . Graph.insertEdgeWith CMSet.union e . theCallGraph
  where e = mkCall s t cm cinfo


-- * Combination of a new thing with an old thing
--   returning a really new things and updated old things.

type CombineNewOldT a = a -> a -> (a, a)

class CombineNewOld a where
  combineNewOld :: CombineNewOldT a

instance PartialOrd a => CombineNewOld (Favorites a) where
  combineNewOld new old = (new', Fav.unionCompared (new', old'))
    where (new', old') = Fav.compareFavorites new old

deriving instance CombineNewOld (CMSet cinfo)

instance (Monoid a, CombineNewOld a, Ord s, Ord t) => CombineNewOld (Graph s t a) where
  combineNewOld new old = Graph.unzip $ Graph.unionWith comb new' old'
    where
      new' = (,mempty) <$> new
      old' = (mempty,) <$> old
      comb (new1,old1) (new2,old2)  -- TODO: ensure old1 is null
        = mapFst (new2 `mappend`) $ combineNewOld new1 old2
        -- -- | old1 == mempty = mapFst (new2 `mappend`) $ combineNewOld new1 old2
        -- -- | otherwise      = __IMPOSSIBLE__

      -- Filter unlabelled edges from the resulting new graph.
      -- filt = Graph.filterEdges (not . null)

-- | Call graph combination.
--
--   Application of '>*<' to all pairs @(c1,c2)@
--   for which @'source' c1 = 'target' c2@.)

-- GHC supports implicit-parameter constraints in instance declarations
-- only from 7.4.  To maintain compatibility with 7.2, we skip this instance:
-- KEEP:
-- instance (Monoid cinfo, ?cutoff :: CutOff) => CombineNewOld (CallGraph cinfo) where
--   combineNewOld (CallGraph new) (CallGraph old) = CallGraph -*- CallGraph $ combineNewOld comb old
--     -- combined calls:
--     where comb = Graph.composeWith (>*<) CMSet.union new old

-- Non-overloaded version:
combineNewOldCallGraph :: (Monoid cinfo, ?cutoff :: CutOff) => CombineNewOldT (CallGraph cinfo)
combineNewOldCallGraph (CallGraph new) (CallGraph old) = CallGraph -*- CallGraph $ combineNewOld comb old
    -- combined calls:
    where comb = Graph.composeWith (>*<) CMSet.union new old

-- | Call graph comparison.
--   A graph @cs'@ is ``worse'' than @cs@ if it has a new edge (call)
--   or a call got worse, which means that one of its elements
--   that was better or equal to 'Le' moved a step towards 'Un'.
--
--   A call graph is complete if combining it with itself does not make it
--   any worse.  This is sound because of monotonicity:  By combining a graph
--   with itself, it can only get worse, but if it does not get worse after
--   one such step, it gets never any worse.

-- | @'complete' cs@ completes the call graph @cs@. A call graph is
-- complete if it contains all indirect calls; if @f -> g@ and @g ->
-- h@ are present in the graph, then @f -> h@ should also be present.

complete :: (?cutoff :: CutOff) => Monoid cinfo => CallGraph cinfo -> CallGraph cinfo
complete cs = repeatWhile (mapFst (not . null) . completionStep cs) cs

completionStep :: (?cutoff :: CutOff) => Monoid cinfo =>
  CallGraph cinfo -> CallGraph cinfo -> (CallGraph cinfo, CallGraph cinfo)
completionStep gOrig gThis = combineNewOldCallGraph gOrig gThis

-- prop_complete :: (?cutoff :: CutOff) => Property
-- prop_complete =
--   forAll (callGraph :: Gen (CallGraph [Integer])) $ \cs ->
--     isComplete (complete cs)

-- -- | Returns 'True' iff the call graph is complete.

-- isComplete :: (Ord cinfo, Monoid cinfo, ?cutoff :: CutOff) => CallGraph cinfo -> Bool
-- isComplete s = (s `union` (s `combine` s)) `notWorse` s

------------------------------------------------------------------------
-- * Printing
------------------------------------------------------------------------

-- | Displays the recursion behaviour corresponding to a call graph.

instance Pretty cinfo => Pretty (CallGraph cinfo) where
  pretty = vcat . map prettyCall . toList
    where
    prettyCall e = if null (callMatrixSet e) then empty else align 20 $
      [ ("Source:",    text $ show $ source e)
      , ("Target:",    text $ show $ target e)
      , ("Matrix:",    pretty $ callMatrixSet e)
      ]

-- -- | Displays the recursion behaviour corresponding to a call graph.

-- prettyBehaviour :: Show cinfo => CallGraph cinfo -> Doc
-- prettyBehaviour = vcat . map prettyCall . filter toSelf . toList
--   where
--   toSelf c = source c == target c

--   prettyCall e = vcat $ map text
--     [ "Function:  " ++ show (source e)
-- --    , "Behaviour: " ++ show (diagonal $ mat $ cm c)  -- TODO
-- --    , "Meta info: " ++ show cinfo
--     ]

------------------------------------------------------------------------
-- * Generators and properties
------------------------------------------------------------------------

-- | Generates a call graph.

callGraph :: (Monoid cinfo, Arbitrary cinfo) => Gen (CallGraph cinfo)
callGraph = do
  indices <- fmap List.nub arbitrary
  n <- natural
  let noMatrices | List.null indices = 0
                 | otherwise    = n `min` 3  -- Not too many.
  fromList <$> vectorOf noMatrices (matGen indices)
  where
  matGen indices = do
    [s, t] <- vectorOf 2 (elements indices)
    [c, r] <- vectorOf 2 (choose (0, 2))     -- Not too large.
    m <- callMatrix (Size { rows = r, cols = c })
    mkCall s t m <$> arbitrary

------------------------------------------------------------------------
-- All tests

tests :: IO Bool
tests = runTests "Agda.Termination.CallGraph" []
  -- [ quickCheck' prop_complete
  -- , quickCheck' prop_ensureCompletePrecondition
  -- ]
  where ?cutoff = CutOff 2
