{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveTraversable #-}

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

import Control.Applicative hiding (Const, empty)
import Control.Monad.State
import Control.Monad.Writer

import Data.Foldable
import Data.Functor
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Traversable

import Agda.Utils.Singleton
import Agda.Utils.Empty

data Pat n a
  = Var a            -- ^ Variable.
  | Con n [Pat n a]  -- ^ Constructor.
  | Infty            -- ^ Unknown term, matches anything.
  deriving (Eq, Show, Functor, Foldable, Traversable)

data Elim n a
  = Apply (Pat n a) -- ^ Application copattern.
  | Proj n          -- ^ Projection copattern.
  | More            -- ^ Only at end of list of eliminations.
                    --   Stands for a truncated tail of eliminations.
  deriving (Eq, Show, Functor, Foldable, Traversable)

type Elims n a = [Elim n a]

type Var = Int

-- | Vars(callArg) contained in Vars(callPat)
data CallUnify a = CallUnify
  { callVars :: Var       -- ^ Number of variables in 'callPat'.
  , callPat :: Elims Var a  -- ^ No 'Infty' in here, no 'More'!
  , callArg :: Elims Var a  -- ^ Truncated to 'Infty' and 'More'.
  }

-- class Vars x p where
--   vars :: (Singleton x m, Monoid m) -> p -> m

-- | The variables of a pattern or elimination.
vars = foldMap singleton

type Sol n a = Map n (Pat n a)

inst :: Sol n a -> Pat n a -> Pat n a
inst s p =
  case p of
    Var a    -> Map.findWithDefault (Var a) a s
    Con n ps -> Con n $ map (inst s) ps
    Infty    -> Infty

type Unify n a c = StateT (Sol n a) (Maybe c)

instantiate :: Pat n a -> Unify n a (Pat n a)
instantiate p = do
  s <- get
  return $ inst s p

assign :: a -> Pat n a -> Unify n a ()
assign x p = do
  s <- get
  put $ Map.insert x p s

unify :: Pat n a -> Pat n a -> Unify n a ()
unify p1 p2 = do
  p1 <- instantiate p1
  p2 <- instantiate p2
  case (p1, p2) of
    (Var x, Var y) | x == y -> return ()
    (Var x, _)     -> assign (x, p2)
    (_, Var y)     -> assign (y, p1)
    (Infty, Infty) -> return ()
    (Con c ps, Infty) -> zipWithM_ unify ps (repeat Infty)
    (Infty, Con c ps) -> zipWithM_ unify (repeat Infty) ps
    (Con c1 ps1, Con c2 ps2)
      | c1 == c2  -> zipWithM_ unify ps1 ps2
      | otherwise -> mempty

unifyE :: Elim n a -> Elim n a -> Unify n a ()
unifyE e1 e2 = do
  case (e1, e2) of
    (Apply p1, Apply p2) -> unify p1 p2
    (Apply{}, Elim{}) -> mempty
    (Elim{}, Apply{}) -> mempty
    (Elim q1, Elim q2)
      | q1 == q2  -> return ()
      | otherwise -> mempty
    (More, _) -> return ()
    (_, More) -> return ()

type Rest n a = Either (Elims n a) (Elims n a)

-- | Returns the rest of the longer elim chain, if the shorter ends in @More@.
unifyEs :: Elims n a -> Elims n a -> Unify n a (Rest n a)
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

compose :: CallUnify a -> CallUnify a -> Maybe (CallUnify a)
compose (CallUnify n1 p1 e1) (CallUnify n2 p2' e2') = do
  -- Freshen variables in second call
  let p2 = map (n1 +) p2'
      e2 = map (n1 +) e2'
  (r, s) <- unifyEs p2 e1 `runStateT` empty
  case r of

type Depth = Int

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

type Truncate n a c = StateT [a] (Writer (Sol n a) c)

next :: Truncate n a a
next = do
  (x:xs) <- get
  put xs
  return x

-- trunc :: Pat n a -> Truncate n a (Pat n a)
-- trunc p = do
--      x <- next
--      tell (singleton x p)
--      return $ Var x

truncateToVar :: Depth -> Pat n a -> Truncate n a (Pat n a)
truncateToVar n = truncateAt n $ \ p -> do
   x <- next
   tell (singleton x p)
   return $ Var x
