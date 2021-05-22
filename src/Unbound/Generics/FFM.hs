{-# LANGUAGE RankNTypes #-}

module Unbound.Generics.FFM where

import Control.Monad (join)

-- Internal: the free monad over the Functor f.  Note that 'freshen''
-- has a monadic return type and moreover we have to thread the
-- permutation through the 'gfreshen' calls to crawl over the value
-- constructors.  Since we don't know anything about the monad @m@,
-- GHC can't help us.  But note that none of the code in the generic
-- 'gfreshen' instances actually makes use of the 'Fresh.fresh'
-- function; they just plumb the dictionary through to any 'K' nodes
-- that happen to contain a value of a type like 'Name' that does
-- actually freshen something.  So what we do is we actually make
-- gfreshen work not in the monad @m@, but in the monad @FFM m@ and
-- then use 'retractFFM' in the default 'Alpha' method to return back
-- down to @m@.  We don't really make use of the fact that 'FFM'
-- reassociates the binds of the underlying monad, but it doesn't hurt
-- anything.  Mostly what we care about is giving the inliner a chance
-- to eliminate most of the monadic plumbing.
newtype FFM f a = FFM {runFFM :: forall r. (a -> r) -> (f r -> r) -> r}

instance Functor (FFM f) where
  fmap f (FFM h) = FFM (\r j -> h (r . f) j)
  {-# INLINE fmap #-}

instance Applicative (FFM f) where
  pure x = FFM (\r _j -> r x)
  {-# INLINE pure #-}
  (FFM h) <*> (FFM k) = FFM (\r j -> h (\f -> k (r . f) j) j)
  {-# INLINE (<*>) #-}

instance Monad (FFM f) where
  return = pure
  {-# INLINE return #-}
  (FFM h) >>= f = FFM (\r j -> h (\x -> runFFM (f x) r j) j)
  {-# INLINE (>>=) #-}

liftFFM :: Monad m => m a -> FFM m a
liftFFM m = FFM (\r j -> j (fmap r m))
{-# INLINE liftFFM #-}

retractFFM :: Monad m => FFM m a -> m a
retractFFM (FFM h) = h return join
{-# INLINE retractFFM #-}