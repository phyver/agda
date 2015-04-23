{-# LANGUAGE CPP #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE IncoherentInstances #-}  -- for Vars
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE UndecidableInstances #-} -- for Show from Pretty

{- | Call composition using unification of in-copatterns with out-eliminations

Example:

@
cycle 2 = delay (2 , delay (1 , delay (0 , cycle N)))

fst (force (cycle n    )) = n
snd (force (cycle 0    )) = snd (force (cycle (S N)))
snd (force (cycle (S n))) = cycle n
@

Calls cycle --> cycle

  1. 0  , force, snd --> S *, force, snd
  2. S n, force, snd --> n

with tail := ,force,snd

Calls cycle --> cycle

  1. 0  tail --> S* tail
  2. Sn tail --> n

Indirect calls

  1;1   no match
  1;2   12. 0   tail      --> *
  2;1   21. 1   tail tail --> S* tail
  2;2   22. SSn tail tail --> n

Cut-depth 1
-----------

   1. 0  tail --> S* tail
   2. Sn tail --> n
  12. 0  tail --> *
  21. Sn tail --> S* tail   (no decrease)
  22. equal to 2.


Cut-depth 2
-----------

Indirect calls ctd.

  1;12  no match
  1;21  121   0    tail tail      --> S* tail
  1;22  122   0    tail tail      --> * tail  (subsumed by 12)

  2;12  212   1    tail tail      --> *
  2;21  221   2    tail tail tail --> S* tail
  2;22  222   SSSn tail tail tail --> n

  12;1  121   0    tail tail      --> S* tail (subsumed by 122)
  21;1  no match
  22;1  2210  3    tail tail tail --> S* tail

  12;2  1220  0    tail tail      --> *   (subsumed by 12)
  21;2  212   1    tail tail      --> *
  22;2  222   SSSn tail tail tail --> n

Cutting at depth 2

  1.    0   tail      --> S* tail
  2.    Sn  tail      --> n

  12.   0   tail      --> *
  21.   1   tail tail --> S* tail   [idem]
  22.   SSn tail tail --> n         [idem]

  122.  0   tail tail --> * tail    [idem]
  221.  SSn tail tail --> S* tail   [idem]

  212.  1   tail tail --> *         [idem]
  222.  SSn tail tail --> n     (became equal to 22)

-}

module Agda.Termination.Unify.CallUnify where

import Prelude hiding (mapM, forM, mapM_, forM_)

import Control.Applicative hiding (Const, empty)
import Control.Monad.State hiding (mapM, forM, mapM_, forM_)
import Control.Monad.Writer hiding (mapM, forM, mapM_, forM_)

import Data.Foldable
import Data.Functor
import Data.Functor.Identity
import qualified Data.List as List
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Traversable

-- import Agda.Termination.CutOff
-- import Agda.Termination.CallDecoration

import Agda.Utils.Singleton
import Agda.Utils.Pretty as P

#include "undefined.h"
import Agda.Utils.Impossible

-- | A term language for call patterns and call arguments.
data Pat n a
  = Var a            -- ^ Variable.
  | Con n [Pat n a]  -- ^ Constructor.
  | Infty            -- ^ Unknown term, matches anything.
  deriving (Eq, Ord, Show, Functor, Foldable, Traversable)

-- | Copatterns and eliminations.
data Elim' n p
  = Apply p  -- ^ Application copattern/elimination.
  | Proj n   -- ^ Projection copattern/elimination.
  deriving (Eq, Ord, Show, Functor, Foldable, Traversable)

type Elim n a = Elim' n (Pat n a)

type Elims n a = [Elim n a]

-- | Call eliminations are truncated if exceeding the maximum depth.
--   Otherwise, they could grow indefinitely, e.g. @f --> tail f@.
data CallElims n a = CallElims
  { callElims :: Elims n a
  , truncated :: Bool  -- ^ Have we discarded eliminations already?
  } deriving (Eq, Ord, Functor, Foldable, Traversable)

type Var = Int

class Ord a => Variable a where

instance Variable Var where

-- | @vars(callArgs)@ contained in @vars(callPats)@
data CallUnify n = CallUnify
  { callVars :: Var              -- ^ Number of variables in 'callPat'.
  , callPats :: Elims     n Var  -- ^ No 'Infty' in here!
  , callArgs :: CallElims n Var  -- ^ Truncated to 'Infty'.
  } deriving (Eq, Ord)

-- | The variables of a pattern or elimination.
class Vars a p where
  vars :: (Monoid m, Singleton a m) => p -> m

-- instance Vars a (Pat n a) where
--   vars = foldMap singleton

instance Variable a => Vars a a where
  vars = singleton

instance (Foldable t, Vars a p) => Vars a (t p) where
  vars = foldMap vars

-- vars :: (Monoid m, Singleton a m, Traversable t) => t a -> m

applyElim :: Elim n a -> Maybe (Pat n a)
applyElim (Apply p) = Just p
applyElim Proj{}    = Nothing

applyElims :: Elims n a -> [Pat n a]
applyElims = catMaybes . map applyElim

mapCallElims :: (Elims n a -> Elims n a) -> CallElims n a -> CallElims n a
mapCallElims f (CallElims e t) = CallElims (f e) t

-- | If we are truncated already, we do not append eliminations.
appendElims :: CallElims n a -> Elims n a -> CallElims n a
appendElims ce@(CallElims e t) e' = if t then ce else CallElims (e ++ e') t

-- | If we have to drop arguments, we need to set 'truncated' to true.
takeElims :: Int -> CallElims n a -> CallElims n a
takeElims n ce@(CallElims e t) = CallElims e' $ t || not (null rest)
  where (e',rest) = splitAt n e

-- * Substitution

type Sol n a = Map a (Pat n a)

class Inst c where
  inst :: Variable a => Sol n a -> c n a -> c n a

instance Inst Pat where
  inst s p =
    case p of
      Var a    -> Map.findWithDefault (Var a) a s
      Con n ps -> Con n $ map (inst s) ps
      Infty    -> Infty

-- instance Inst p => Inst (Elim' n p) where
--   inst s e = inst s <$> e

    -- case e of
    --   Apply p -> Apply $ inst s p
    --   Proj{}  -> e

-- instance Inst Elims where
--   inst s = map (inst s)

instance Inst CallElims where
  inst s (CallElims e t) = CallElims (fmap (inst s) <$> e) t

instCall :: Sol n Int -> CallUnify n -> CallUnify n
instCall s (CallUnify n p e) = CallUnify n (fmap (inst s) <$> p) (inst s e)

-- * Unification

type Unify n a = StateT (Sol n a) Maybe

instantiate :: Variable a => Pat n a -> Unify n a (Pat n a)
instantiate p = do
  s <- get
  return $ inst s p

assign :: Variable a => a -> Pat n a -> Unify n a ()
assign x p = do
  s <- get
  put $ Map.insert x p s

unify :: (Eq n, Variable a) => Pat n a -> Pat n a -> Unify n a ()
unify p1 p2 = do
  p1 <- instantiate p1
  p2 <- instantiate p2
  case (p1, p2) of
    (Var x, Var y) | x == y -> return ()
    (Var x, _)     -> assign x p2
    (_, Var y)     -> assign y p1
    (Infty, Infty) -> return ()
    (Con c ps, Infty) -> zipWithM_ unify ps (repeat Infty)
    (Infty, Con c ps) -> zipWithM_ unify (repeat Infty) ps
    (Con c1 ps1, Con c2 ps2)
      | c1 == c2  -> zipWithM_ unify ps1 ps2
      | otherwise -> mzero

unifyE :: (Eq n, Variable a) => Elim n a -> Elim n a -> Unify n a ()
unifyE e1 e2 = do
  case (e1, e2) of
    (Apply p1, Apply p2) -> unify p1 p2
    (Apply{}, Proj{}) -> mzero
    (Proj{}, Apply{}) -> mzero
    (Proj q1, Proj q2)
      | q1 == q2  -> return ()
      | otherwise -> mzero

type Rest n a = Either (Elims n a) (Elims n a)

-- | Returns the rest of the longer elim chain, if the shorter ends in @More@.
unifyEs :: (Eq n, Variable a) => Elims n a -> Elims n a -> Unify n a (Rest n a)
unifyEs es1 es2 =
  case (es1, es2) of
    ([], _) -> return $ Right es2
    (_, []) -> return $ Left  es1
    (e1:es1, e2:es2) -> unifyE e1 e2 >> unifyEs es1 es2

-- -- | Returns the rest of the longer elim chain, if the shorter ends in @More@.
-- unifyEs :: Elims n a -> Elims n a -> Unify n a (Rest n a)
-- unifyEs es1 es2 =
--   case (es1, es2) of
--     ([], []) -> return $ Left []
--     ([More], _) -> return $ Right es2
--     (_, [More]) -> return $ Left  es1

-- -- | Returns the remaining eliminations of the call.
-- --   Patterns cannot be left over.
-- unifyCEs :: Elims n a -> CallElims n a -> Unify n a (Elims n a)
-- unifyCEs ps (CallElims es truncated) = do
--   r <- unifyEs ps es
--   case r of
--     Right es' -> return es'
--     Left []   -> return []
--     Left ps'  -> do
--       -- Unless the call has truncated arguments and projection,
--       -- unification fails.
--       guard truncated
--       -- Every variable in the remaining patterns is set to Infty.
--       zipWithM_ unify (applyElims ps') (repeat Infty)

-- | Returns the remaining eliminations of the call.
--   If the call was truncated, patterns are not left over,
--   but satisfied trivially.
unifyCEs :: (Eq n, Variable a) => Elims n a -> CallElims n a -> Unify n a (Rest n a)
unifyCEs ps (CallElims es truncated) = do
  r <- unifyEs ps es
  case r of
    Right es' -> return r
    Left ps'  -> if not truncated then return r else do
      -- Every variable in the remaining patterns is set to Infty.
      zipWithM_ unify (applyElims ps') (repeat Infty)
      return $ Left []

-- | Compose two calls.  The resulting call in non-canonical, i.e.
--   may not use all of its declared variables
compose :: Eq n => CallUnify n -> CallUnify n -> Maybe (CallUnify n)
compose (CallUnify n1 p1 e1) (CallUnify n2 p2' e2') = do
  -- Freshen variables in second call
  let p2 = map (fmap (fmap (n1 +))) p2'
      e2 = mapCallElims (map (fmap (fmap (n1 +)))) e2'
  -- Unify the patterns of the second call with the arguments of the first call.
  (r, s) <- unifyCEs p2 e1 `runStateT` Map.empty
  -- Instantiate the composed call.
  return $ instCall s $ case r of
    -- When patterns were left over, these have to be added to the
    -- patterns of the first call.
    Left ps -> CallUnify (n1 + n2) (p1 ++ ps) e2
    -- When call arguments were left over, these have to be added to the
    -- arguments of the second call.
    Right es -> CallUnify (n1 + n2) p1 (e2 `appendElims` es)

-- | Rename variables to use exactly the variables below @n@, for a minimal @n@.
canonicalize :: CallUnify a -> CallUnify a
canonicalize c = instCall s $ c{ callVars = length xs }
  where
    -- Get the free variables, in left to right order
    xs :: [Int]
    xs = List.nub $ vars $ callPats c
    -- Rename the variables in the call
    s  = Map.fromList $ zipWith (\ x i -> (x, Var i)) xs [0..]

-- * Truncation

type Depth   = Int   -- ^ Maximal depth of patterns
type Breadth = Int -- ^ Maximal number of copatterns

truncateAt :: Applicative m => Depth -> (Pat n a -> m (Pat n a)) -> Pat n a -> m (Pat n a)
truncateAt n trunc p
  | n <= 0    = trunc p
  | otherwise = do
    case p of
      Var x    -> pure $ Var x
      Infty    -> pure $ Infty
      Con c ps -> Con c <$> traverse (truncateAt (n - 1) trunc) ps

truncateToInfty :: Depth -> Pat n a -> Pat n a
truncateToInfty n = runIdentity . truncateAt n (const $ pure Infty)

type Truncate n a = StateT [a] (Writer (Sol n a))

next :: (Variable a) => Truncate n a a
next = do
  (x:xs) <- get
  put xs
  return x

-- trunc :: Pat n a -> Truncate n a (Pat n a)
-- trunc p = do
--      x <- next
--      tell (singleton x p)
--      return $ Var x

truncateToVar :: (Variable a) => Depth -> Pat n a -> Truncate n a (Pat n a)
truncateToVar n = truncateAt n $ \ p -> do
   x <- next
   tell $ singleton (x, p)
   return $ Var x

-- | Given a substitution @x1:=t1..xn:=tn@ from truncation
--   we construct a substitution mapping all variables of @ti@ to @xi@.
--   This might not be unique, if the @ti@ share variables.
--   For example, if we truncate caller @f (suc n) (cons n a as)@
--   to depth 0, we get truncation @f x1 x2@ and could map @n@ to either
--   @x1@ or @x2@.  As it is maller than both patterns, we can safely
--   chose any of @n:=x1@ or @n:=x2@.
carelessInvert :: forall a n. Variable a => Set a -> Sol n a -> Sol n a
carelessInvert ignore s = Map.fromList $ do
  (x,t) <- Map.toList s
  let ys :: Set a
      ys = vars (t :: Pat n a)
  map (,Var x) $ Set.toList $ ys Set.\\ ignore

truncateCall :: forall n. Depth -> Breadth -> CallUnify n -> CallUnify n
truncateCall d b (CallUnify n p e) = canonicalize $ CallUnify __IMPOSSIBLE__
  p' e'
  where
    -- Fresh variable supply.
    fresh = [n,n+1..]
    -- Truncate length of patterns and arguments.
    (p1, p2) = splitAt b p
    e1     = takeElims b e
    -- Truncate patterns, replacing subpatterns by fresh variables.
    p' :: Elims n Var
    (p',t) = runWriter $ mapM (mapM $ truncateToVar d) p1 `evalStateT` fresh
    -- Eliminated variables need to be replaced by the new ones
    -- in call arguments.
    -- We should restrict the replacements to variables that have actually
    -- disappeared.  We can keep the variables still bound in the patterns.
    keep :: Set Int
    keep   = vars p'
    s1     = carelessInvert keep t
    -- We delete p2, so we have to map its variables to infty
    s2     = Map.fromList $ zip (Set.toList $ vars p2 Set.\\ keep) $ repeat Infty
    s      = Map.union s1 s2
    e'     = inst s $ mapCallElims (map $ fmap $ truncateToInfty d) e1

composeCalls :: Eq n => Depth -> Breadth -> CallUnify n -> CallUnify n -> Maybe (CallUnify n)
composeCalls d b c1 c2 = truncateCall d b <$> compose c1 c2

-- For this call combination, the cutoff needs to be much higher
-- than for the ordinary foetus/SCT termination checker.
-- It needs to be at least the function arity and the pattern depth.

-- instance CallComb (CallUnify n) where
--   callComb c1 c2 = do
--     let Cutoff d = ?cutoff
--     truncateCall d <$> compose c1 c2

------------------------------------------------------------------------
-- * Pretty instances
------------------------------------------------------------------------

instance (Pretty n, Pretty a) => Pretty (Pat n a) where
  pretty (Var a)    = pretty a
  pretty Infty      = text ".."
  pretty (Con c []) = pretty c
  pretty (Con c ps) = parens $ fsep $ pretty c : map pretty ps

instance (Pretty n, Pretty p) => Pretty (Elim' n p) where
  pretty (Apply p) = pretty p
  pretty (Proj q)  = text "." P.<> pretty q

prettyElims :: (Pretty n, Pretty a) => Elims n a -> Doc
prettyElims es = fsep $ map pretty es

instance (Pretty n, Pretty a) => Pretty (CallElims n a) where
  pretty (CallElims e t) = if t then d <+> text "..." else d
    where d = prettyElims e

instance (Pretty n) => Pretty (CallUnify n) where
  pretty (CallUnify _ p e) = prettyElims p <+> text "-->" <+> pretty e

------------------------------------------------------------------------
-- * Unit tests
------------------------------------------------------------------------

instance Pretty a => Show a where
  show = prettyShow

cycle1 = CallUnify 0 p $ CallElims e False where
  p = [ Apply (Con "Z" []     ), Proj "tail" ]
  e = [ Apply (Con "S" [Infty]), Proj "tail" ]

cycle2 = CallUnify 1 p $ CallElims e False where
  p = [ Apply (Con "S" [Var 0]), Proj "tail" ]
  e = [ Apply (Var 0) ]

comb = composeCalls 3 3
combs cs ds = catMaybes [ comb c d | c <- cs, d <- ds ]
cs0 = [ cycle1, cycle2 ]
cs1 = combs cs0 cs0
cs10 = combs cs1 cs0
cs01 = combs cs0 cs1
cs11 = combs cs1 cs1

step s = Set.union s $ Set.fromList $ combs cs cs
  where cs = Set.toList s

css = List.iterate step $ Set.fromList cs0

final cs = fst . head . dropWhile (uncurry (/=)) $ zip cs (tail cs)

printIt css = forM_ (zip [(0 :: Int)..] css) $ \ (i, s) -> do
  putStrLn $ "iteration " ++ show i
  mapM_ print $ Set.toList s
  putStrLn ""


csfinal = mapM_ print $ Set.toList $ final css

run n = printIt $ take n css
