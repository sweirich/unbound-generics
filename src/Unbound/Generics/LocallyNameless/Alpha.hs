{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeOperators #-}
{-# OPTIONS_GHC -fexpose-all-unfoldings #-}
{-# OPTIONS_HADDOCK show-extensions #-}

-- |
-- Module     : Unbound.Generics.LocallyNameless.Alpha
-- Copyright  : (c) 2014, Aleksey Kliger
-- License    : BSD3 (See LICENSE)
-- Maintainer : Aleksey Kliger
-- Stability  : experimental
--
-- Use the 'Alpha' typeclass to mark types that may contain 'Name's.
module Unbound.Generics.LocallyNameless.Alpha
  ( -- * Name-aware opertions
    Alpha (..),
    open,
    close,

    -- * Binder variables
    DisjointSet (..),
    inconsistentDisjointSet,
    singletonDisjointSet,
    isConsistentDisjointSet,
    isNullDisjointSet,

    -- * Implementation details
    NthPatFind (..),
    NamePatFind (..),
    AlphaCtx,
    initialCtx,
    patternCtx,
    termCtx,
    isTermCtx,
    incrLevelCtx,
    decrLevelCtx,
    isZeroLevelCtx,

    -- * Internal
    gaeq,
    gfvAny,
    gcloseMulti,
    gopenMulti,
    gisPat,
    gisTerm,
    gnthPatFind,
    gnamePatFind,
    gswaps,
    gfreshen,
    glfreshen,
    gacompare,

    -- ** Interal helpers for gfreshen
    FFM,
    liftFFM,
    retractFFM,
    ctxLevel,
    ctxMode,
  )
where

import Control.Applicative (Applicative (..), (<$>))
import Control.Arrow (first)
import Control.Monad (join)
import Data.Foldable (Foldable (..))
import Data.Function (on)
import Data.Functor.Contravariant (Contravariant (..))
import Data.List as List
import Data.Monoid (All (..), Monoid (..))
import Data.Ratio (Ratio)
import Data.Semigroup as Sem
import Data.Typeable (Typeable, gcast, typeOf)
import GHC.Generics
import Unbound.Generics.DisjointSet
import Unbound.Generics.FFM
import Unbound.Generics.LocallyNameless.Fresh
import Unbound.Generics.LocallyNameless.LFresh
import Unbound.Generics.LocallyNameless.Name
import Unbound.Generics.PermM

-- | Some 'Alpha' operations need to record information about their
-- progress.  Instances should just pass it through unchanged.
--
-- The context records whether we are currently operating on terms or patterns,
-- and how many binding levels we've descended.
data AlphaCtx = AlphaCtx {ctxMode :: !Mode, ctxLevel :: !Int}

data Mode = Term | Pat
  deriving (Eq)

-- | The starting context for alpha operations: we are expecting to
-- work on terms and we are under no binders.
initialCtx :: AlphaCtx
initialCtx = AlphaCtx {ctxMode = Term, ctxLevel = 0}
{-# INLINE initialCtx #-}

-- | Switches to a context where we expect to operate on patterns.
patternCtx :: AlphaCtx -> AlphaCtx
patternCtx ctx = ctx {ctxMode = Pat}
{-# INLINE patternCtx #-}

-- | Switches to a context where we expect to operate on terms.
termCtx :: AlphaCtx -> AlphaCtx
termCtx ctx = ctx {ctxMode = Term}
{-# INLINE termCtx #-}

-- | Returns 'True' iff we are in a context where we expect to see terms.
isTermCtx :: AlphaCtx -> Bool
isTermCtx AlphaCtx {ctxMode = Term} = True
isTermCtx _ = False
{-# INLINE isTermCtx #-}

-- | Increment the number of binders that we are operating under.
incrLevelCtx :: AlphaCtx -> AlphaCtx
incrLevelCtx ctx = ctx {ctxLevel = 1 + ctxLevel ctx}
{-# INLINE incrLevelCtx #-}

-- | Decrement the number of binders that we are operating under.
decrLevelCtx :: AlphaCtx -> AlphaCtx
decrLevelCtx ctx = ctx {ctxLevel = ctxLevel ctx - 1}
{-# INLINE decrLevelCtx #-}

-- | Are we operating under no binders?
isZeroLevelCtx :: AlphaCtx -> Bool
isZeroLevelCtx ctx = ctxLevel ctx == 0
{-# INLINE isZeroLevelCtx #-}

-- | Types that are instances of @Alpha@ may participate in name representation.
--
-- Minimal instance is entirely empty, provided that your type is an instance of
-- 'Generic'.
class (Show a) => Alpha a where
  -- | See 'Unbound.Generics.LocallyNameless.Operations.aeq'.
  aeq' :: AlphaCtx -> a -> a -> Bool
  default aeq' :: (Generic a, GAlpha (Rep a)) => AlphaCtx -> a -> a -> Bool
  aeq' c = gaeq c `on` from
  {-# INLINE aeq' #-}

  -- | See 'Unbound.Generics.LocallyNameless.Operations.fvAny'.
  --
  -- @
  --  fvAny' :: Fold a AnyName
  -- @
  fvAny' :: (Contravariant f, Applicative f) => AlphaCtx -> (AnyName -> f AnyName) -> a -> f a
  default fvAny' :: (Generic a, GAlpha (Rep a), Contravariant f, Applicative f) => AlphaCtx -> (AnyName -> f AnyName) -> a -> f a
  fvAny' c nfn = fmap to . gfvAny c nfn . from
  {-# INLINE fvAny' #-}

  -- | Replace free names by bound names.
  closeMulti :: AlphaCtx -> [NamePatFind] -> a -> a
  default closeMulti :: (Generic a, GAlpha (Rep a)) => AlphaCtx -> [NamePatFind] -> a -> a
  closeMulti c b = to . gcloseMulti c b . from
  {-# INLINE closeMulti #-}

  -- | Replace bound names by free names.
  -- Can open multiple indices at once
  openMulti :: AlphaCtx -> [NthPatFind] -> a -> a
  default openMulti :: (Generic a, GAlpha (Rep a)) => AlphaCtx -> [NthPatFind] -> a -> a
  openMulti c b = to . gopenMulti c b . from
  {-# INLINE openMulti #-}

  -- | @isPat x@ dynamically checks whether @x@ can be used as a valid pattern.
  isPat :: a -> DisjointSet AnyName
  default isPat :: (Generic a, GAlpha (Rep a)) => a -> DisjointSet AnyName
  isPat = gisPat . from
  {-# INLINE isPat #-}

  -- | @isPat x@ dynamically checks whether @x@ can be used as a valid term.
  isTerm :: a -> All
  default isTerm :: (Generic a, GAlpha (Rep a)) => a -> All
  isTerm = gisTerm . from
  {-# INLINE isTerm #-}

  -- | @isEmbed@ is needed internally for the implementation of
  --   'isPat'.  @isEmbed@ is true for terms wrapped in 'Embed' and zero
  --   or more occurrences of 'Shift'.  The default implementation
  --   simply returns @False@.
  isEmbed :: a -> Bool
  isEmbed _ = False
  {-# INLINE isEmbed #-}

  -- | If @a@ is a pattern, finds the @n@th name in the pattern
  -- (starting from zero), returning the number of names encountered
  -- if not found.
  nthPatFind :: a -> NthPatFind
  default nthPatFind :: (Generic a, GAlpha (Rep a)) => a -> NthPatFind
  nthPatFind = gnthPatFind . from
  {-# INLINE nthPatFind #-}

  -- | If @a@ is a pattern, find the index of the given name in the pattern.
  namePatFind :: a -> NamePatFind
  default namePatFind :: (Generic a, GAlpha (Rep a)) => a -> NamePatFind
  namePatFind = gnamePatFind . from
  {-# INLINE namePatFind #-}

  -- | See 'Unbound.Generics.LocallyNameless.Operations.swaps'. Apply
  -- the given permutation of variable names to the given pattern.
  swaps' :: AlphaCtx -> Perm AnyName -> a -> a
  default swaps' :: (Generic a, GAlpha (Rep a)) => AlphaCtx -> Perm AnyName -> a -> a
  swaps' ctx perm = to . gswaps ctx perm . from
  {-# INLINE swaps' #-}

  -- | See 'Unbound.Generics.LocallyNameless.Operations.freshen'.
  lfreshen' :: LFresh m => AlphaCtx -> a -> (a -> Perm AnyName -> m b) -> m b
  default lfreshen' ::
    (LFresh m, Generic a, GAlpha (Rep a)) =>
    AlphaCtx ->
    a ->
    (a -> Perm AnyName -> m b) ->
    m b
  lfreshen' ctx m cont = glfreshen ctx (from m) (cont . to)
  {-# INLINE lfreshen' #-}

  -- | See 'Unbound.Generics.LocallyNameless.Operations.freshen'.  Rename the free variables
  -- in the given term to be distinct from all other names seen in the monad @m@.
  freshen' :: Fresh m => AlphaCtx -> a -> m (a, Perm AnyName)
  default freshen' :: (Generic a, GAlpha (Rep a), Fresh m) => AlphaCtx -> a -> m (a, Perm AnyName)
  freshen' ctx = retractFFM . fmap (first to) . gfreshen ctx . from
  {-# INLINE freshen' #-}
  
  -- | See 'Unbound.Generics.LocallyNameless.Operations.acompare'. An alpha-respecting total order on terms involving binders.
  acompare' :: AlphaCtx -> a -> a -> Ordering
  default acompare' :: (Generic a, GAlpha (Rep a)) => AlphaCtx -> a -> a -> Ordering
  acompare' c = gacompare c `on` from
  {-# INLINE acompare' #-}
  
-- | The result of @'nthPatFind' a i@ is @Left k@ where @i-k@ is the
-- number of names in pattern @a@ (with @k < i@) or @Right x@ where @x@
-- is the @i@th name in @a@
newtype NthPatFind = NthPatFind {runNthPatFind :: Int -> Either Int AnyName}

-- | @since 0.3.2
instance Sem.Semigroup NthPatFind where
  (<>) = \(NthPatFind f) (NthPatFind g) ->
    NthPatFind $ \i -> case f i of
      Left i' -> g i'
      found@Right {} -> found

instance Monoid NthPatFind where
  mempty = NthPatFind Left
  mappend = (<>)

open :: Alpha a => AlphaCtx -> NthPatFind -> a -> a
open ctx p = openMulti ctx [p]
{-# INLINE open #-}

close :: Alpha a => AlphaCtx -> NamePatFind -> a -> a
close ctx p = closeMulti ctx [p]
{-# INLINE close #-}

-- | The result of @'namePatFind' a x@ is either @Left i@ if @a@ is a pattern that
-- contains @i@ free names none of which are @x@, or @Right j@ if @x@ is the @j@th name
-- in @a@
newtype NamePatFind = NamePatFind
  { runNamePatFind ::
      AnyName ->
      -- Left - names skipped over
      -- Right - index of the name we found
      Either Int Int
  }

-- | @since 0.3.2
instance Sem.Semigroup NamePatFind where
  (<>) = \(NamePatFind f) (NamePatFind g) ->
    NamePatFind $ \nm -> case f nm of
      ans@Right {} -> ans
      Left n -> case g nm of
        Left m -> Left $! n + m
        Right i -> Right $! n + i

instance Monoid NamePatFind where
  mempty = NamePatFind (\_ -> Left 0)
  mappend = (<>)

-- | The "Generic" representation version of 'Alpha'
class GAlpha f where
  gaeq :: AlphaCtx -> f a -> f a -> Bool

  gfvAny :: (Contravariant g, Applicative g) => AlphaCtx -> (AnyName -> g AnyName) -> f a -> g (f a)

  gcloseMulti :: AlphaCtx -> [NamePatFind] -> f a -> f a
  gopenMulti :: AlphaCtx -> [NthPatFind] -> f a -> f a

  gisPat :: f a -> DisjointSet AnyName
  gisTerm :: f a -> All

  gnthPatFind :: f a -> NthPatFind
  gnamePatFind :: f a -> NamePatFind

  gswaps :: AlphaCtx -> Perm AnyName -> f a -> f a
  gfreshen :: Fresh m => AlphaCtx -> f a -> FFM m (f a, Perm AnyName)

  glfreshen :: LFresh m => AlphaCtx -> f a -> (f a -> Perm AnyName -> m b) -> m b

  gacompare :: AlphaCtx -> f a -> f a -> Ordering

instance (Alpha c) => GAlpha (K1 i c) where
  gaeq ctx (K1 c1) (K1 c2) = aeq' ctx c1 c2
  {-# INLINE gaeq #-}

  gfvAny ctx nfn = fmap K1 . fvAny' ctx nfn . unK1
  {-# INLINE gfvAny #-}

  gcloseMulti ctx b = K1 . closeMulti ctx b . unK1
  {-# INLINE gcloseMulti #-}
  gopenMulti ctx b = K1 . openMulti ctx b . unK1
  {-# INLINE gopenMulti #-}

  gisPat = isPat . unK1
  {-# INLINE gisPat #-}
  gisTerm = isTerm . unK1
  {-# INLINE gisTerm #-}

  gnthPatFind = nthPatFind . unK1
  {-# INLINE gnthPatFind #-}
  gnamePatFind = namePatFind . unK1
  {-# INLINE gnamePatFind #-}

  gswaps ctx perm = K1 . swaps' ctx perm . unK1
  {-# INLINE gswaps #-}
  gfreshen ctx = fmap (first K1) . liftFFM . freshen' ctx . unK1
  {-# INLINE gfreshen #-}

  glfreshen ctx (K1 c) cont = lfreshen' ctx c (cont . K1)
  {-# INLINE glfreshen #-}

  gacompare ctx (K1 c1) (K1 c2) = acompare' ctx c1 c2
  {-# INLINE gacompare #-}
  
instance GAlpha f => GAlpha (M1 i c f) where
  gaeq ctx (M1 f1) (M1 f2) = gaeq ctx f1 f2
  {-# INLINE gaeq #-}

  gfvAny ctx nfn = fmap M1 . gfvAny ctx nfn . unM1
  {-# INLINE gfvAny #-}

  gcloseMulti ctx b = M1 . gcloseMulti ctx b . unM1
  {-# INLINE gcloseMulti #-}
  gopenMulti ctx b = M1 . gopenMulti ctx b . unM1
  {-# INLINE gopenMulti #-}

  gisPat = gisPat . unM1
  {-# INLINE gisPat #-}
  gisTerm = gisTerm . unM1
  {-# INLINE gisTerm #-}

  gnthPatFind = gnthPatFind . unM1
  {-# INLINE gnthPatFind #-}
  gnamePatFind = gnamePatFind . unM1
  {-# INLINE gnamePatFind #-}

  gswaps ctx perm = M1 . gswaps ctx perm . unM1
  {-# INLINE gswaps #-}
  gfreshen ctx = fmap (first M1) . gfreshen ctx . unM1
  {-# INLINE gfreshen #-}

  glfreshen ctx (M1 f) cont =
    glfreshen ctx f (cont . M1)
  {-# INLINE glfreshen #-}

  gacompare ctx (M1 f1) (M1 f2) = gacompare ctx f1 f2
  {-# INLINE gacompare #-}
  
instance GAlpha U1 where
  gaeq _ctx _ _ = True
  {-# INLINE gaeq #-}

  gfvAny _ctx _nfn _ = pure U1

  gcloseMulti _ctx _b _ = U1
  gopenMulti _ctx _b _ = U1

  gisPat _ = mempty
  gisTerm _ = mempty

  gnthPatFind _ = mempty
  gnamePatFind _ = mempty

  gswaps _ctx _perm _ = U1
  gfreshen _ctx _ = return (U1, mempty)
  {-# INLINE gfreshen #-}

  glfreshen _ctx _ cont = cont U1 mempty

  gacompare _ctx _ _ = EQ
  {-# INLINE gacompare #-}  

instance GAlpha V1 where
  gaeq _ctx _ _ = False
  {-# INLINE gaeq #-}

  gfvAny _ctx _nfn = pure

  gcloseMulti _ctx _b _ = undefined
  gopenMulti _ctx _b _ = undefined

  gisPat _ = mempty
  gisTerm _ = mempty

  gnthPatFind _ = mempty
  gnamePatFind _ = mempty

  gswaps _ctx _perm _ = undefined
  gfreshen _ctx _ = return (undefined, mempty)
  {-# INLINE gfreshen #-}

  glfreshen _ctx _ cont = cont undefined mempty

  gacompare _ctx _ _ = error "LocallyNameless.gacompare: undefined for empty data types"

instance (GAlpha f, GAlpha g) => GAlpha (f :*: g) where
  gaeq ctx (f1 :*: g1) (f2 :*: g2) =
    gaeq ctx f1 f2 && gaeq ctx g1 g2
  {-# INLINE gaeq #-}

  gfvAny ctx nfn (f :*: g) =
    (:*:) <$> gfvAny ctx nfn f
      <*> gfvAny ctx nfn g
  {-# INLINE gfvAny #-}

  gcloseMulti ctx b (f :*: g) = gcloseMulti ctx b f :*: gcloseMulti ctx b g
  {-# INLINE gcloseMulti #-}
  gopenMulti ctx b (f :*: g) = gopenMulti ctx b f :*: gopenMulti ctx b g
  {-# INLINE gopenMulti #-}

  gisPat (f :*: g) = gisPat f <> gisPat g
  {-# INLINE gisPat #-}
  gisTerm (f :*: g) = gisTerm f <> gisTerm g
  {-# INLINE gisTerm #-}

  gnthPatFind (f :*: g) = gnthPatFind f <> gnthPatFind g
  {-# INLINE gnthPatFind #-}
  gnamePatFind (f :*: g) = gnamePatFind f <> gnamePatFind g
  {-# INLINE gnamePatFind #-}

  gswaps ctx perm (f :*: g) =
    gswaps ctx perm f :*: gswaps ctx perm g
  {-# INLINE gswaps #-}

  gfreshen ctx (f :*: g) = do
    ~(g', perm2) <- gfreshen ctx g
    ~(f', perm1) <- gfreshen ctx (gswaps ctx perm2 f)
    return (f' :*: g', perm1 <> perm2)
  {-# INLINE gfreshen #-}

  glfreshen ctx (f :*: g) cont =
    glfreshen ctx g $ \g' perm2 ->
      glfreshen ctx (gswaps ctx perm2 f) $ \f' perm1 ->
        cont (f' :*: g') (perm1 <> perm2)
  {-# INLINE glfreshen #-}

  gacompare ctx (f1 :*: g1) (f2 :*: g2) =
    gacompare ctx f1 f2 <> gacompare ctx g1 g2
  {-# INLINE gacompare #-}

instance (GAlpha f, GAlpha g) => GAlpha (f :+: g) where
  gaeq ctx (L1 f1) (L1 f2) = gaeq ctx f1 f2
  gaeq ctx (R1 g1) (R1 g2) = gaeq ctx g1 g2
  gaeq _ctx _ _ = False
  {-# INLINE gaeq #-}

  gfvAny ctx nfn (L1 f) = fmap L1 (gfvAny ctx nfn f)
  gfvAny ctx nfn (R1 g) = fmap R1 (gfvAny ctx nfn g)
  {-# INLINE gfvAny #-}

  gcloseMulti ctx b (L1 f) = L1 (gcloseMulti ctx b f)
  gcloseMulti ctx b (R1 g) = R1 (gcloseMulti ctx b g)
  {-# INLINE gcloseMulti #-}
  gopenMulti ctx b (L1 f) = L1 (gopenMulti ctx b f)
  gopenMulti ctx b (R1 g) = R1 (gopenMulti ctx b g)
  {-# INLINE gopenMulti #-}

  gisPat (L1 f) = gisPat f
  gisPat (R1 g) = gisPat g
  {-# INLINE gisPat #-}

  gisTerm (L1 f) = gisTerm f
  gisTerm (R1 g) = gisTerm g
  {-# INLINE gisTerm #-}

  gnthPatFind (L1 f) = gnthPatFind f
  gnthPatFind (R1 g) = gnthPatFind g
  {-# INLINE gnthPatFind #-}

  gnamePatFind (L1 f) = gnamePatFind f
  gnamePatFind (R1 g) = gnamePatFind g
  {-# INLINE gnamePatFind #-}

  gswaps ctx perm (L1 f) = L1 (gswaps ctx perm f)
  gswaps ctx perm (R1 f) = R1 (gswaps ctx perm f)
  {-# INLINE gswaps #-}

  gfreshen ctx (L1 f) = fmap (first L1) (gfreshen ctx f)
  gfreshen ctx (R1 f) = fmap (first R1) (gfreshen ctx f)
  {-# INLINE gfreshen #-}

  glfreshen ctx (L1 f) cont =
    glfreshen ctx f (cont . L1)
  glfreshen ctx (R1 g) cont =
    glfreshen ctx g (cont . R1)
  {-# INLINE glfreshen #-}

  gacompare _ctx (L1 _) (R1 _) = LT
  gacompare _ctx (R1 _) (L1 _) = GT
  gacompare ctx (L1 f1) (L1 f2) = gacompare ctx f1 f2
  gacompare ctx (R1 g1) (R1 g2) = gacompare ctx g1 g2
  {-# INLINE gacompare #-}

-- ============================================================
-- Alpha instances for the usual types

newtype Closed a = Closed a
  deriving (Eq, Ord, Show)

instance (Show a, Eq a, Ord a) => Alpha (Closed a) where
  aeq' _ctx i j = i == j

  fvAny' _ctx _nfn i = pure i

  closeMulti _ctx _b i = i
  openMulti _ctx _b i = i

  isPat _ = mempty
  isTerm _ = mempty

  nthPatFind _ = mempty
  namePatFind _ = mempty

  swaps' _ctx _p i = i
  freshen' _ctx i = return (i, mempty)
  lfreshen' _ctx i cont = cont i mempty

  acompare' _ctx i j = compare i j


-- Unfortunately, we cannot use DerivingVia to use the above instance to create easy
-- instances for closed types

instance Alpha Int where
  aeq' _ctx i j = i == j

  fvAny' _ctx _nfn i = pure i

  closeMulti _ctx _b i = i
  openMulti _ctx _b i = i

  isPat _ = mempty
  isTerm _ = mempty

  nthPatFind _ = mempty
  namePatFind _ = mempty

  swaps' _ctx _p i = i
  freshen' _ctx i = return (i, mempty)
  lfreshen' _ctx i cont = cont i mempty

  acompare' _ctx i j = compare i j

instance Alpha Char where
  aeq' _ctx i j = i == j

  fvAny' _ctx _nfn i = pure i

  closeMulti _ctx _b i = i
  openMulti _ctx _b i = i

  isPat _ = mempty
  isTerm _ = mempty

  nthPatFind _ = mempty
  namePatFind _ = mempty

  swaps' _ctx _p i = i
  freshen' _ctx i = return (i, mempty)
  lfreshen' _ctx i cont = cont i mempty

  acompare' _ctx i j = compare i j

instance Alpha Integer where
  aeq' _ctx i j = i == j

  fvAny' _ctx _nfn i = pure i

  closeMulti _ctx _b i = i
  openMulti _ctx _b i = i

  isPat _ = mempty
  isTerm _ = mempty

  nthPatFind _ = mempty
  namePatFind _ = mempty

  swaps' _ctx _p i = i
  freshen' _ctx i = return (i, mempty)
  lfreshen' _ctx i cont = cont i mempty

  acompare' _ctx i j = compare i j

instance Alpha Float where
  aeq' _ctx i j = i == j

  fvAny' _ctx _nfn i = pure i

  closeMulti _ctx _b i = i
  openMulti _ctx _b i = i

  isPat _ = mempty
  isTerm _ = mempty

  nthPatFind _ = mempty
  namePatFind _ = mempty

  swaps' _ctx _p i = i
  freshen' _ctx i = return (i, mempty)
  lfreshen' _ctx i cont = cont i mempty

  acompare' _ctx i j = compare i j

instance Alpha Double where
  aeq' _ctx i j = i == j

  fvAny' _ctx _nfn i = pure i

  closeMulti _ctx _b i = i
  openMulti _ctx _b i = i

  isPat _ = mempty
  isTerm _ = mempty

  nthPatFind _ = mempty
  namePatFind _ = mempty

  swaps' _ctx _p i = i
  freshen' _ctx i = return (i, mempty)
  lfreshen' _ctx i cont = cont i mempty

  acompare' _ctx i j = compare i j

instance (Integral n, Alpha n) => Alpha (Ratio n) where
  aeq' _ctx i j = i == j

  fvAny' _ctx _nfn i = pure i

  closeMulti _ctx _b i = i
  openMulti _ctx _b i = i

  isPat _ = mempty
  isTerm _ = mempty

  nthPatFind _ = mempty
  namePatFind _ = mempty

  swaps' _ctx _p i = i
  freshen' _ctx i = return (i, mempty)
  lfreshen' _ctx i cont = cont i mempty

  acompare' _ctx i j = compare i j

instance Alpha Bool where
  aeq' _ctx i j = i == j

  fvAny' _ctx _nfn i = pure i

  closeMulti _ctx _b i = i
  openMulti _ctx _b i = i

  isPat _ = mempty
  isTerm _ = mempty

  nthPatFind _ = mempty
  namePatFind _ = mempty

  swaps' _ctx _p i = i
  freshen' _ctx i = return (i, mempty)
  lfreshen' _ctx i cont = cont i mempty

  acompare' _ctx i j = compare i j

instance Alpha () where
  aeq' _ctx i j = i == j

  fvAny' _ctx _nfn i = pure i

  closeMulti _ctx _b i = i
  openMulti _ctx _b i = i

  isPat _ = mempty
  isTerm _ = mempty

  nthPatFind _ = mempty
  namePatFind _ = mempty

  swaps' _ctx _p i = i
  freshen' _ctx i = return (i, mempty)
  lfreshen' _ctx i cont = cont i mempty

  acompare' _ctx i j = compare i j

instance Alpha a => Alpha (Maybe a)

instance Alpha a => Alpha [a]

instance (Alpha a, Alpha b) => Alpha (Either a b)

instance (Alpha a, Alpha b) => Alpha (a, b)

instance (Alpha a, Alpha b, Alpha c) => Alpha (a, b, c)

instance (Alpha a, Alpha b, Alpha c, Alpha d) => Alpha (a, b, c, d)

instance
  (Alpha a, Alpha b, Alpha c, Alpha d, Alpha e) =>
  Alpha (a, b, c, d, e)

-- ============================================================
-- Alpha instances for interesting types

runNamePatFinds :: Int -> [NamePatFind] -> AnyName -> Maybe (Int, Int)
runNamePatFinds _ [] _ = Nothing
runNamePatFinds n (npf : rest) a =
  case runNamePatFind npf a of
    Left _ -> runNamePatFinds (n+1) rest a
    Right j -> Just (n, j)

instance Typeable a => Alpha (Name a) where
  aeq' ctx n1 n2 =
    not (isTermCtx ctx) -- in terms, better be the same name
      || n1 == n2 -- in a pattern, names are always equivalent (since
      -- they're both bound, so they can vary).

  fvAny' ctx nfn nm =
    if isTermCtx ctx && isFreeName nm
      then contramap AnyName (nfn (AnyName nm))
      else pure nm

  openMulti ctx vn a@(Bn i j) =
    let k = ctxLevel ctx in
    if ctxMode ctx == Term && i >= k then
      (if length vn > (i - k)
      then case runNthPatFind (vn !! (i - k)) j of
        Right (AnyName nm) -> case gcast nm of
          Just nm' -> nm'
          Nothing -> error "LocallyNameless.open: inconsistent sorts"
        Left _ -> error "LocallyNameless.open : inconsistency - pattern had too few variables"
      else
        error ("LocallyNameless.open: length vn =" ++ show (length vn) ++ " i= " ++ show i ++ " ctxLevel=" ++ show (ctxLevel ctx)))
      else a
  openMulti _ctx _ a = a

  closeMulti ctx xs a@(Fn _ _) =
    if isTermCtx ctx
      then case runNamePatFinds 0 xs (AnyName a) of
             Nothing -> a
             Just (n, j) -> Bn (n + ctxLevel ctx) j
      else a
  closeMulti _ctx _ a = a

  isPat n =
    if isFreeName n
      then singletonDisjointSet (AnyName n)
      else inconsistentDisjointSet

  isTerm _ = mempty

  nthPatFind nm = NthPatFind $ \i ->
    if i == 0 then Right (AnyName nm) else Left $! i -1

  namePatFind nm1 = NamePatFind $ \(AnyName nm2) ->
    case gcast nm1 of
      Just nm1' -> if nm1' == nm2 then Right 0 else Left 1
      Nothing -> Left 1

  swaps' ctx perm nm =
    if isTermCtx ctx
      then case apply perm (AnyName nm) of
        AnyName nm' ->
          case gcast nm' of
            Just nm'' -> nm''
            Nothing -> error "Internal error swaps' on a Name returned permuted name of wrong sort"
      else nm

  freshen' ctx nm =
    if not (isTermCtx ctx)
      then do
        nm' <- fresh nm
        return (nm', single (AnyName nm) (AnyName nm'))
      else error "freshen' on a Name in term position"

  lfreshen' ctx nm cont =
    if not (isTermCtx ctx)
      then do
        nm' <- lfresh nm
        avoid [AnyName nm'] $ cont nm' $ single (AnyName nm) (AnyName nm')
      else error "lfreshen' on a Name in term position"

  acompare' ctx (Fn s1 i1) (Fn s2 i2)
    | isTermCtx ctx = compare s1 s2 <> compare i1 i2
  acompare' ctx n1@(Bn i1 j1) n2@(Bn i2 j2)
    | isTermCtx ctx =
      mconcat
        [ compare (typeOf n1) (typeOf n2),
          compare i1 i2,
          compare j1 j2
        ]
  acompare' ctx (Fn _ _) (Bn _ _) | isTermCtx ctx = LT
  acompare' ctx (Bn _ _) (Fn _ _) | isTermCtx ctx = GT
  acompare' _ _ _ = EQ

instance Alpha AnyName where
  aeq' ctx x y =
    x == y -- in a term unequal variables are unequal, in a pattern it's
      || not (isTermCtx ctx) -- ok

  fvAny' ctx nfn n@(AnyName nm) =
    if isTermCtx ctx && isFreeName nm
      then nfn n
      else pure n

  isTerm _ = mempty

  isPat n@(AnyName nm) =
    if isFreeName nm
      then singletonDisjointSet n
      else inconsistentDisjointSet

  swaps' ctx perm n =
    if isTermCtx ctx
      then apply perm n
      else n

  freshen' ctx (AnyName nm) =
    if isTermCtx ctx
      then error "LocallyNameless.freshen' on AnyName in Term mode"
      else do
        nm' <- fresh nm
        return (AnyName nm', single (AnyName nm) (AnyName nm'))

  lfreshen' ctx (AnyName nm) cont =
    if isTermCtx ctx
      then error "LocallyNameless.lfreshen' on AnyName in Term mode"
      else do
        nm' <- lfresh nm
        avoid [AnyName nm'] $ cont (AnyName nm') $ single (AnyName nm) (AnyName nm')

  openMulti ctx b (AnyName nm) = AnyName (openMulti ctx b nm)

  closeMulti ctx b (AnyName nm) = AnyName (closeMulti ctx b nm)

  nthPatFind nm = NthPatFind $ \i ->
    if i == 0 then Right nm else Left $! i - 1

  namePatFind nmHave = NamePatFind $ \nmWant ->
    if nmHave == nmWant then Right 0 else Left 1

  acompare' _ x y | x == y = EQ
  acompare' ctx (AnyName n1) (AnyName n2)
    | isTermCtx ctx =
      case compare (typeOf n1) (typeOf n2) of
        EQ -> case gcast n2 of
          Just n2' -> acompare' ctx n1 n2'
          Nothing -> error "LocallyNameless.acompare': Equal type representations, but gcast failed in comparing two AnyName values"
        ord -> ord
  acompare' _ _ _ = EQ
