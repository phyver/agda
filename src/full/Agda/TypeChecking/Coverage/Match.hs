{-# LANGUAGE CPP #-} -- GHC 7.4.2 requires this indentation. See Issue 1460.
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE PatternGuards #-}

module Agda.TypeChecking.Coverage.Match where

import Control.Applicative
import Control.Monad.State

import qualified Data.List as List
import Data.Maybe (mapMaybe)
import Data.Monoid
import Data.Traversable (traverse)

import Agda.Syntax.Abstract (IsProjP(..))
import Agda.Syntax.Common hiding (Arg, Dom, NamedArg)
import Agda.Syntax.Internal
import Agda.Syntax.Internal.Pattern ()
import Agda.Syntax.Literal

import Agda.Utils.Permutation
import Agda.Utils.Size
import Agda.Utils.List

#include "undefined.h"
import Agda.Utils.Impossible

{-| Given

    1. the function clauses @cs@
    2. the patterns @ps@ and permutation @perm@ of a split clause

we want to compute a variable index of the split clause to split on next.

First, we find the set @cs'@ of all the clauses that are
instances (via substitutions @rhos@) of the split clause.

In these substitutions, we look for a column that has only constructor patterns.
We try to split on this column first.
-}

-- | Match the given patterns against a list of clauses
match :: [Clause] -> [Arg Pattern] -> Permutation -> Match (Nat,[MPat])
match cs ps perm = foldr choice No $ zipWith matchIt [0..] cs
  where
    mps = buildMPatterns perm ps

    -- If liberal matching on literals fails or blocks we go with that.
    -- If it succeeds we use the result from conservative literal matching.
    -- This is to make sure that we split enough when literals are involved.
    -- For instance,
    --    f ('x' :: 'y' :: _) = ...
    --    f (c :: s) = ...
    -- would never split the tail of the list if we only used conservative
    -- literal matching.
    matchIt i c = matchClause yesMatchLit mps i c +++
                  matchClause noMatchLit  mps i c

    Yes _   +++ m = m
    No      +++ _ = No
    Block x +++ _ = Block x
    BlockP  +++ _ = BlockP

-- | We use a special representation of the patterns we're trying to match
--   against a clause. In particular we want to keep track of which variables
--   are blocking a match.
data MPat
  = VarMP Nat    -- ^ De Bruijn index (usually, rightmost variable in patterns is 0).
  | ConMP ConHead [Arg MPat]
  | LitMP Literal
  | DotMP MPat   -- ^ For keeping track of the original dot positions.
  | WildMP       -- ^ For dot patterns that cannot be turned into patterns.
  | ProjMP QName -- ^ Projection copattern.
  deriving (Show)

buildMPatterns :: Permutation -> [Arg Pattern] -> [Arg MPat]
buildMPatterns perm ps = evalState (mapM (traverse build) ps) xs
  where
    xs   = permute (invertP __IMPOSSIBLE__ perm) $ downFrom (size perm)
    tick = do x : xs <- get; put xs; return x

    build (VarP _)        = VarMP <$> tick
    build (ConP con _ ps) = ConMP con <$> mapM (traverse build . fmap namedThing) ps
    build (DotP t)        = DotMP <$> (tick *> buildT t)
    build (LitP l)        = return $ LitMP l
    build (ProjP dest)    = return $ ProjMP dest

    buildT (Con c args)   = ConMP c <$> mapM (traverse buildT) args
    buildT (Var i [])     = return (VarMP i)
    buildT (Shared p)     = buildT (derefPtr p)
    buildT _              = return WildMP

isTrivialMPattern :: MPat -> Bool
isTrivialMPattern VarMP{} = True
isTrivialMPattern ConMP{} = False
isTrivialMPattern LitMP{} = False
isTrivialMPattern DotMP{} = True
isTrivialMPattern WildMP{} = True
isTrivialMPattern ProjMP{} = False -- or True?

-- | If matching is inconclusive (@Block@) we want to know which
--   variables are blocking the match.
data Match a
  = Yes a                -- ^ Matches unconditionally.
  | No                   -- ^ Definitely does not match.
  | Block BlockingVars   -- ^ Could match if non-empty list of blocking variables
                         --   is instantiated properly.
  | BlockP               -- ^ Could match if split on possible projections is performed.
  deriving (Functor)

-- | Variable blocking a match.
data BlockingVar  = BlockingVar
  { blockingVarNo   :: Nat
    -- ^ De Bruijn index of variable blocking the match.
  , blockingVarCons :: Maybe [ConHead]
    -- ^ @Nothing@ means there is an overlapping match for this variable.
    --   This happens if one clause has a constructor pattern at this position,
    --   and another a variable.  It is also used for "just variable".
    --
    --   @Just cons@ means that it is an non-overlapping match and
    --   @cons@ are the encountered constructors.
  } deriving (Show)
type BlockingVars = [BlockingVar]

mapBlockingVarCons :: (Maybe [ConHead] -> Maybe [ConHead]) -> BlockingVar -> BlockingVar
mapBlockingVarCons f b = b { blockingVarCons = f (blockingVarCons b) }

clearBlockingVarCons :: BlockingVar -> BlockingVar
clearBlockingVarCons = mapBlockingVarCons $ const Nothing

overlapping :: BlockingVars -> BlockingVars
overlapping = map clearBlockingVarCons

-- | Left dominant merge of blocking vars.
zipBlockingVars :: BlockingVars -> BlockingVars -> BlockingVars
zipBlockingVars xs ys = map upd xs
  where
    upd (BlockingVar x (Just cons))
      | Just (BlockingVar _ (Just cons')) <- List.find ((x ==) . blockingVarNo) ys
                          = BlockingVar x (Just $ cons ++ cons')
    upd (BlockingVar x _) = BlockingVar x Nothing

-- | @choice m m'@ combines the match results @m@ of a function clause
--   with the (already combined) match results $m'$ of the later clauses.
--   It is for skipping clauses that definitely do not match ('No').
--   It is left-strict, to be used with @foldr@.
--   If one clause unconditionally matches ('Yes') we do not look further.
choice :: Match a -> Match a -> Match a
choice (Yes a)   _         = Yes a
choice (Block x) (Block y) = Block (zipBlockingVars x y)
choice (Block x) (Yes _)   = Block $ overlapping x
choice (Block x) _         = Block x
choice BlockP    m         = BlockP
choice No        m         = m

type MatchLit = Literal -> MPat -> Match [MPat]

noMatchLit :: MatchLit
noMatchLit _ _ = No

yesMatchLit :: MatchLit
yesMatchLit _ q@VarMP{}  = Yes [q]
yesMatchLit _ q@WildMP{} = Yes [q]
yesMatchLit _ _        = No

-- | Check if a clause could match given generously chosen literals
matchLits :: Clause -> [Arg Pattern] -> Permutation -> Bool
matchLits c ps perm =
  case matchClause yesMatchLit (buildMPatterns perm ps) 0 c of
    Yes _ -> True
    _     -> False

-- | @matchClause mlit qs i c@ checks whether clause @c@ number @i@
--   covers a split clause with patterns @qs@.
matchClause :: MatchLit -> [Arg MPat] -> Nat -> Clause -> Match (Nat,[MPat])
matchClause mlit qs i c = (\q -> (i,q)) <$> matchPats mlit (clausePats c) qs

-- | @matchPats mlit ps qs@ checks whether a function clause with patterns
--   @ps@ covers a split clause with patterns @qs@.
--
--   Issue 842: if in case of functions with varying arity,
--   the split clause has proper patterns left, we refuse to match,
--   because it would be troublesome to construct the split tree later.
--   We would have to move bindings from the rhs to the lhs.
--   For example, this is rejected:
--   @
--     F : Bool -> Set1
--     F true = Set
--     F      = \ x -> Set
--   @
matchPats :: MatchLit -> [Arg Pattern] -> [Arg MPat] -> Match [MPat]
matchPats mlit ps qs = mconcat $ properMatchesLeft :
    zipWith (matchPat mlit) (map unArg ps) (map unArg qs) ++
    [ projPatternsLeft ]
  where
    projPatternsLeft =
      let psrest = map unArg $ drop (length qs) ps
      in  if null $ mapMaybe isProjP psrest -- not $ any properlyMatching psrest
            then Yes []  -- no proj. patterns left
            else BlockP  -- proj. patterns left
    properMatchesLeft =
      if any (properMatch . unArg) $ drop (length ps) qs
      then No else Yes []
    properMatch ConMP{} = True
    properMatch LitMP{} = True
    properMatch _       = False

-- | Combine results of checking whether function clause patterns
--   covers split clause patterns.
--
--   'No' is dominant: if one function clause pattern is disjoint to
--   the corresponding split clause pattern, then
--   the whole clauses are disjoint.
--
--   'Yes' is neutral: for a match, all patterns have to match.
--
--   'Block' accumulates variables of the split clause
--   that have to be instantiated
--   to make the split clause an instance of the function clause.
--
--   'BlockP' yields to 'Block', since blocking vars can also
--   block the result type.
instance Monoid a => Monoid (Match a) where
  mempty                    = Yes mempty
  Yes a   `mappend` Yes b   = Yes $ mappend a b
  Yes _   `mappend` m       = m
  No      `mappend` _       = No
  Block x `mappend` No      = No
  Block x `mappend` Block y = Block $ mappend x y
  Block x `mappend` _       = Block x
  BlockP  `mappend` No      = No
  BlockP  `mappend` Block y = Block y
  BlockP  `mappend` _       = BlockP

-- | @matchPat mlit p q@ checks whether a function clause pattern @p@
--   covers a split clause pattern @q@.  There are three results:
--   @Yes ()@ means it covers, because @p@ is a variable
--   pattern or @q@ is a wildcard.
--   @No@ means it does not cover.
--   @Block [x]@ means @p@ is a proper instance of @q@ and could become
--   a cover if @q@ was split on variable @x@.
matchPat :: MatchLit -> Pattern -> MPat -> Match [MPat]
matchPat _    (VarP _) q = Yes [q]
matchPat _    (DotP _) q = Yes []
-- Jesper, 2014-11-04: putting 'Yes [q]' here triggers issue 1333.
-- Not checking for trivial MPats should be safe here, as dot patterns are
-- guaranteed to match if the rest of the pattern does, so some extra splitting
-- on them doesn't change the reduction behaviour.
matchPat mlit p (DotMP q) = matchPat mlit p q
matchPat mlit (LitP l) q = mlit l q
matchPat _    (ProjP d) (ProjMP d') = if d == d' then Yes [] else No
matchPat _    (ProjP d) _ = __IMPOSSIBLE__
-- matchPat mlit (ConP c (Just _) ps) q | recordPattern ps = Yes ()  -- Andreas, 2012-07-25 record patterns always match!
matchPat mlit (ConP c _ ps) q = case q of
  VarMP x -> Block [BlockingVar x (Just [c])]
  WildMP{} -> No -- Andreas, 2013-05-15 this was "Yes()" triggering issue 849
  ConMP c' qs
    | c == c'   -> matchPats mlit (map (fmap namedThing) ps) qs
    | otherwise -> No
  LitMP _  -> __IMPOSSIBLE__
  ProjMP _ -> __IMPOSSIBLE__
  DotMP _  -> __IMPOSSIBLE__

{- UNUSED
class RecordPattern a where
  recordPattern :: a -> Bool

instance RecordPattern Pattern where
  recordPattern VarP{} = True
  recordPattern DotP{} = False
  recordPattern LitP{} = False
  recordPattern (ConP _ Nothing _) = False
  recordPattern (ConP _ (Just _) ps) = recordPattern ps

instance RecordPattern a => RecordPattern [a] where
  recordPattern = all recordPattern

instance RecordPattern a => RecordPattern (Arg a) where
  recordPattern = recordPattern . unArg
-}
