{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
{-# OPTIONS_GHC -fexpose-all-unfoldings #-}

-- |
-- Module     : Unbound.Generics.LocallyNameless.Subst
-- Copyright  : (c) 2014, Aleksey Kliger
-- License    : BSD3 (See LICENSE)
-- Maintainer : Aleksey Kliger
-- Stability  : experimental
--
-- A typeclass for types that may participate in capture-avoiding substitution
--
-- The minimal definition is empty, provided your type is an instance of 'GHC.Generics.Generic'
--
-- @
-- type Var = Name Factor
-- data Expr = SumOf [Summand]
--           deriving (Show, Generic)
-- data Summand = ProductOf [Factor]
--           deriving (Show, Generic)
-- instance Subst Var Expr
-- instance Subst Var Summand
-- @
--
-- The default instance just propagates the substitution into the constituent factors.
--
-- If you identify the variable occurrences by implementing the 'isvar' function, the derived 'subst' function
-- will be able to substitute a factor for a variable.
--
-- @
-- data Factor = V Var
--             | C Int
--             | Subexpr Expr
--           deriving (Show, Generic)
-- instance Subst Var Factor where
--   isvar (V v) = Just (SubstName v)
--   isvar _     = Nothing
-- @
module Unbound.Generics.LocallyNameless.Subst
  ( SubstName (..),
    SubstCoerce (..),
    Subst (..),
  )
where

import Data.List (find)
import Data.Maybe (fromMaybe)
import GHC.Generics
import Unbound.Generics.LocallyNameless.Alpha
import Unbound.Generics.LocallyNameless.Bind
import Unbound.Generics.LocallyNameless.Embed
import Unbound.Generics.LocallyNameless.Ignore
import Unbound.Generics.LocallyNameless.Name
import Unbound.Generics.LocallyNameless.Rebind
import Unbound.Generics.LocallyNameless.Rec
import Unbound.Generics.LocallyNameless.Shift

-- | See 'isVar'
data SubstName a b where
  SubstName :: (a ~ b) => Name a -> SubstName a b

-- | See 'isCoerceVar'
data SubstCoerce a b where
  SubstCoerce :: Name b -> (b -> Maybe a) -> SubstCoerce a b

-- | Instances of @'Subst' b a@ are terms of type @a@ that may contain
-- variables of type @b@ that may participate in capture-avoiding
-- substitution.
class Subst b a where
  -- | This is the only method that must be implemented
  isvar :: a -> Maybe (SubstName a b)
  isvar _ = Nothing
  {-# INLINE isvar #-}
  
  -- | This is an alternative version to 'isvar', useable in the case
  --   that the substituted argument doesn't have *exactly* the same type
  --   as the term it should be substituted into.
  --   The default implementation always returns 'Nothing'.
  isCoerceVar :: a -> Maybe (SubstCoerce a b)
  isCoerceVar _ = Nothing
  {-# INLINE isCoerceVar #-}

  -- | @'subst' nm e tm@ substitutes @e@ for @nm@ in @tm@.  It has
  -- a default generic implementation in terms of @isvar@
  subst :: Name b -> b -> a -> a
  default subst :: (Generic a, GSubst b (Rep a)) => Name b -> b -> a -> a
  subst n u x =
    if isFreeName n
      then case (isvar x :: Maybe (SubstName a b)) of
        Just (SubstName m) | m == n -> u
        _ -> case (isCoerceVar x :: Maybe (SubstCoerce a b)) of
          Just (SubstCoerce m f) | m == n -> fromMaybe x (f u)
          _ -> to $ gsubst n u (from x)
      else error $ "Cannot substitute for bound variable " ++ show n
  {-# INLINE subst #-}


  substs :: [(Name b, b)] -> a -> a
  default substs :: (Generic a, GSubst b (Rep a)) => [(Name b, b)] -> a -> a
  substs ss x
    | all (isFreeName . fst) ss =
      case (isvar x :: Maybe (SubstName a b)) of
        Just (SubstName m) | Just (_, u) <- find ((== m) . fst) ss -> u
        _ -> case isCoerceVar x :: Maybe (SubstCoerce a b) of
          Just (SubstCoerce m f) | Just (_, u) <- find ((== m) . fst) ss -> fromMaybe x (f u)
          _ -> to $ gsubsts ss (from x)
    | otherwise =
      error $ "Cannot substitute for bound variable in: " ++ show (map fst ss)
  {-# INLINE substs #-}

---- generic structural substitution.
class GSubst b f where
  gsubst :: Name b -> b -> f c -> f c
  gsubsts :: [(Name b, b)] -> f c -> f c

instance Subst b c => GSubst b (K1 i c) where
  gsubst nm val = K1 . subst nm val . unK1
  gsubsts ss = K1 . substs ss . unK1
  {-# INLINE gsubst #-}
  {-# INLINE gsubsts #-}

instance GSubst b f => GSubst b (M1 i c f) where
  gsubst nm val = M1 . gsubst nm val . unM1
  gsubsts ss = M1 . gsubsts ss . unM1
  {-# INLINE gsubst #-}
  {-# INLINE gsubsts #-}

instance GSubst b U1 where
  gsubst _nm _val _ = U1
  gsubsts _ss _ = U1
  {-# INLINE gsubst #-}
  {-# INLINE gsubsts #-}

instance GSubst b V1 where
  gsubst _nm _val = id
  gsubsts _ss = id
  {-# INLINE gsubst #-}
  {-# INLINE gsubsts #-}

instance (GSubst b f, GSubst b g) => GSubst b (f :*: g) where
  gsubst nm val (f :*: g) = gsubst nm val f :*: gsubst nm val g
  gsubsts ss (f :*: g) = gsubsts ss f :*: gsubsts ss g
  {-# INLINE gsubst #-}
  {-# INLINE gsubsts #-}

instance (GSubst b f, GSubst b g) => GSubst b (f :+: g) where
  gsubst nm val (L1 f) = L1 $ gsubst nm val f
  gsubst nm val (R1 g) = R1 $ gsubst nm val g

  gsubsts ss (L1 f) = L1 $ gsubsts ss f
  gsubsts ss (R1 g) = R1 $ gsubsts ss g
  {-# INLINE gsubst #-}
  {-# INLINE gsubsts #-}

-- these have a Generic instance, but
-- it's self-refential (ie: Rep Int = D1 (C1 (S1 (Rec0 Int))))
-- so our structural GSubst instances get stuck in an infinite loop.
instance Subst b Int where
  subst _ _ = id
  substs _ = id
  {-# INLINE subst #-}
  {-# INLINE substs #-}

instance Subst b Bool where
  subst _ _ = id
  substs _ = id
  {-# INLINE subst #-}
  {-# INLINE substs #-}

instance Subst b () where
  subst _ _ = id
  substs _ = id
  {-# INLINE subst #-}
  {-# INLINE substs #-}

instance Subst b Char where
  subst _ _ = id
  substs _ = id
  {-# INLINE subst #-}
  {-# INLINE substs #-}

instance Subst b Float where
  subst _ _ = id
  substs _ = id
  {-# INLINE subst #-}
  {-# INLINE substs #-}

instance Subst b Double where
  subst _ _ = id
  substs _ = id
  {-# INLINE subst #-}
  {-# INLINE substs #-}

-- huh, apparently there's no instance Generic Integer.
instance Subst b Integer where subst _ _ = id; substs _ = id

instance (Subst c a, Subst c b) => Subst c (a, b)

instance (Subst c a, Subst c b, Subst c d) => Subst c (a, b, d)

instance (Subst c a, Subst c b, Subst c d, Subst c e) => Subst c (a, b, d, e)

instance
  (Subst c a, Subst c b, Subst c d, Subst c e, Subst c f) =>
  Subst c (a, b, d, e, f)

instance (Subst c a) => Subst c [a]

instance (Subst c a) => Subst c (Maybe a)

instance (Subst c a, Subst c b) => Subst c (Either a b)

instance Subst b (Name a) where subst _ _ = id; substs _ = id

instance Subst b AnyName where subst _ _ = id; substs _ = id

instance (Subst c a) => Subst c (Embed a)

instance (Subst c e) => Subst c (Shift e) where
  subst x b (Shift e) = Shift (subst x b e)
  substs ss (Shift e) = Shift (substs ss e)
  {-# INLINE subst #-}
  {-# INLINE substs #-}


instance (Subst c b, Subst c a, Alpha a, Alpha b) => Subst c (Bind a b) where
  subst x b (B p t) = B (subst x b p) (subst x b t)
  subst x a b = subst x a (forceBind b)
  substs ss (B p t) = B (substs ss p) (substs ss t)
  substs ss b = substs ss (forceBind b)
  {-# INLINE subst #-}
  {-# INLINE substs #-}

instance (Subst c p1, Subst c p2) => Subst c (Rebind p1 p2)

instance (Subst c p) => Subst c (Rec p)

instance (Alpha p, Subst c p) => Subst c (TRec p)

instance Subst a (Ignore b) where
  subst _ _ = id
  substs _ = id
  {-# INLINE subst #-}
  {-# INLINE substs #-}
