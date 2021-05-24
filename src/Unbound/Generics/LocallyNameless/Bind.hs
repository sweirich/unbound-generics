{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE GADTSyntax #-}
{-# OPTIONS_HADDOCK show-extensions #-}

-- |
-- Module     : Unbound.Generics.LocallyNameless.Bind
-- Copyright  : (c) 2014, Aleksey Kliger
-- License    : BSD3 (See LICENSE)
-- Maintainer : Aleksey Kliger
-- Stability  : experimental
--
-- The fundamental binding form.  The type @'Bind' p t@ allows you to
-- place a pattern @p@ in a term @t@ such that the names in the
-- pattern scope over the term.  Use 'Unbound.Generics.LocallyNameless.Operations.bind'
-- and 'Unbound.Generics.LocallyNameless.Operations.unbind' and 'Unbound.Generics.LocallyNameless.Operations.lunbind'
-- to work with @'Bind' p t@
module Unbound.Generics.LocallyNameless.Bind
  ( -- * Name binding
    Bind (..),
    forceBind,
  )
where

import Control.Applicative (Applicative (..), (<$>))
import Control.DeepSeq (NFData (..))
import Data.Monoid (All (..), (<>))
import GHC.Generics (Generic)
import Unbound.Generics.LocallyNameless.Alpha
import Unbound.Generics.LocallyNameless.Name

-- | A term of type @'Bind' p t@ is a term that binds the free
-- variable occurrences of the variables in pattern @p@ in the term
-- @t@.  In the overall term, those variables are now bound. See also
-- 'Unbound.Generics.LocallyNameless.Operations.bind' and
-- 'Unbound.Generics.LocallyNameless.Operations.unbind' and
-- 'Unbound.Generics.LocallyNameless.Operations.lunbind'
data Bind p t where
  B :: !p -> !t -> Bind p t
  BindOpen :: !AlphaCtx -> ![NthPatFind] -> !p -> !t -> Bind p t
  BindClose :: !AlphaCtx -> ![NamePatFind] -> !p -> !t -> Bind p t
  -- ^ A binding with a suspended use of the "open" operation.
  -- This suspended open is "outside" the binding, but can be used to
  -- aggregate multiple uses of open in series without traversing the
  -- entire term.
  deriving (Generic)

-- | This is an internal operation. If we use any other operation
-- besides open or close, we need to resolve the suspended operation first. 
forceBind :: (Alpha p, Alpha t) => Bind p t -> Bind p t
forceBind (B p t) = B p t
forceBind (BindOpen ctx bs p t) =
  B (openMulti (patternCtx ctx) bs p)
    (openMulti (incrLevelCtx ctx) bs t)
forceBind (BindClose ctx xs p t) =
   B (closeMulti (patternCtx ctx) xs p) (closeMulti (incrLevelCtx ctx) xs t)
{-# INLINE forceBind #-}

instance (Alpha p, Alpha t, NFData p, NFData t) => NFData (Bind p t) where
  rnf (B p t) = rnf p `seq` rnf t
  rnf b = rnf (forceBind b)

instance (Alpha p, Alpha t, Show p, Show t) => Show (Bind p t) where
  showsPrec prec (B p t) =
    showParen
      (prec > 0)
      ( showString "<"
          . showsPrec prec p
          . showString "> "
          . shows t
      )
  showsPrec prec b = showsPrec prec (forceBind b)

instance (Alpha p, Alpha t) => Alpha (Bind p t) where
  --aeq' ctx (B p1 t1) (B p2 t2) =
  --  aeq' (patternCtx ctx) p1 p2
  --    && aeq' (incrLevelCtx ctx) t1 t2
  aeq' ctx b1 b2 =
    case (forceBind b1, forceBind b2) of
      (B p1 t1, B p2 t2) ->
        aeq' (patternCtx ctx) p1 p2 && aeq' (incrLevelCtx ctx) t1 t2
  {-# INLINE aeq' #-}

  fvAny' ctx nfn (B p t) =
    B <$> fvAny' (patternCtx ctx) nfn p
      <*> fvAny' (incrLevelCtx ctx) nfn t
  fvAny' ctx nfn b = fvAny' ctx nfn (forceBind b)
  {-# INLINE fvAny' #-}

  isPat _ = inconsistentDisjointSet
  {-# INLINE isPat #-}

  isTerm (B p t) = All (isConsistentDisjointSet $ isPat p) <> isTerm t
  isTerm (BindOpen _ _ p t) = All (isConsistentDisjointSet $ isPat p) <> isTerm t
  isTerm (BindClose _ _ p t) = All (isConsistentDisjointSet $ isPat p) <> isTerm t
  {-# INLINE isTerm #-}

  closeMulti ctx xs (B p t) =
    BindClose ctx xs p t
--    B (close (patternCtx ctx) b p) (close (incrLevelCtx ctx) b t)
  closeMulti _ctx xs (BindClose ctx ys p t) =
    BindClose ctx (ys ++ xs) p t
--  closeMulti ctx a b = closeMulti ctx a (forceBind b)
  closeMulti ctx a (BindOpen ctx1 bs p t) =
    closeMulti ctx a (B (openMulti (patternCtx ctx1) bs p)
    (openMulti (incrLevelCtx ctx1) bs t))
  {-# INLINE closeMulti #-}

  openMulti ctx vn (B p t) =
    --  B (openMulti (patternCtx ctx) b p) (openMulti (incrLevelCtx ctx) b t)
    BindOpen ctx vn p t
  openMulti _ctx vn (BindOpen ctx vm p t) =
    BindOpen ctx (vm <> vn) p t
  --  openMulti ctx vn b = openMulti ctx vn (forceBind b)    
  openMulti ctx  vn (BindClose ctx1 xs p t) =
    openMulti ctx vn (B (closeMulti (patternCtx ctx1) xs p) (closeMulti (incrLevelCtx ctx1) xs t))
  {-# INLINE openMulti #-}

  nthPatFind b = error $ "Binding " ++ show b ++ " used as a pattern"
  namePatFind b = error $ "Binding " ++ show b ++ " used as a pattern"

  swaps' ctx perm (B p t) =
    B
      (swaps' (patternCtx ctx) perm p)
      (swaps' (incrLevelCtx ctx) perm t)
  swaps' ctx perm b = swaps' ctx perm (forceBind b)
  {-# INLINE swaps' #-}

  freshen' ctx (B p t) = do
    (p', perm1) <- freshen' (patternCtx ctx) p
    (t', perm2) <- freshen' (incrLevelCtx ctx) (swaps' (incrLevelCtx ctx) perm1 t)
    return (B p' t', perm1 <> perm2)
  freshen' ctx b = freshen' ctx (forceBind b)
  {-# INLINE freshen' #-}

  lfreshen' ctx (B p t) cont =
    lfreshen' (patternCtx ctx) p $ \p' pm1 ->
      lfreshen' (incrLevelCtx ctx) (swaps' (incrLevelCtx ctx) pm1 t) $ \t' pm2 ->
        cont (B p' t') (pm1 <> pm2)
  lfreshen' ctx b cont = lfreshen' ctx (forceBind b) cont
  {-# INLINE lfreshen' #-}

  acompare' ctx (B p1 t1) (B p2 t2) =
    acompare' (patternCtx ctx) p1 p2 <> acompare' (incrLevelCtx ctx) t1 t2
  acompare' ctx b1 b2 = acompare' ctx (forceBind b1) (forceBind b2)
  {-# INLINE acompare' #-}
