{-# LANGUAGE DeriveGeneric #-}
{-# OPTIONS_HADDOCK show-extensions #-}

-- |
-- Module     : Unbound.Generics.LocallyNameless.Rec
-- Copyright  : (c) 2014, Aleksey Kliger
-- License    : BSD3 (See LICENSE)
-- Maintainer : Aleksey Kliger
-- Stability  : experimental
--
-- The pattern @'Rec' p@ binds the names in @p@ like @p@ itself would,
-- but additionally, the names in @p@ are scope over @p@.
--
-- The term @'TRec' p@ is shorthand for @'Bind' (Rec p) ()@
module Unbound.Generics.LocallyNameless.Rec
  ( Rec (..),
    rec,
    unrec,
    TRec (..),
  )
where

import Control.DeepSeq (NFData (..))
import Data.Monoid (All (..))
import GHC.Generics (Generic)
import Unbound.Generics.LocallyNameless.Alpha
import Unbound.Generics.LocallyNameless.Bind

-- | If @p@ is a pattern type, then @Rec p@ is also a pattern type,
-- which is /recursive/ in the sense that @p@ may bind names in terms
-- embedded within itself.  Useful for encoding e.g. lectrec and
-- Agda's dot notation.
newtype Rec p = Rec p
  deriving (Generic, Eq)

instance NFData p => NFData (Rec p) where
  rnf (Rec p) = rnf p `seq` ()

instance Show a => Show (Rec a) where
  showsPrec _ (Rec a) = showString "[" . shows a . showString "]"

-- | @TRec@ is a standalone variant of 'Rec': the only difference is
--   that whereas @'Rec' p@ is a pattern type, @TRec p@
--   is a /term type/.  It is isomorphic to @'Bind' ('Rec' p) ()@.
--
--   Note that @TRec@ corresponds to Pottier's /abstraction/ construct
--   from alpha-Caml.  In this context, @'Embed' t@ corresponds to
--   alpha-Caml's @inner t@, and @'Shift' ('Embed' t)@ corresponds to
--   alpha-Caml's @outer t@.
newtype TRec p = TRec (Bind (Rec p) ())
  deriving (Generic)

instance (Alpha a, Show a) => Show (TRec a) where
  showsPrec _ (TRec (B (Rec p) ())) = showString "[" . shows p . showString "]"
  showsPrec p (TRec b) = showsPrec p (TRec (forceBind b))

instance Alpha p => Alpha (Rec p) where
  isTerm _ = All False
  isPat (Rec p) = isPat p

  nthPatFind (Rec p) = nthPatFind p
  namePatFind (Rec p) = namePatFind p

  openMulti ctx b (Rec p) = Rec (openMulti (incrLevelCtx ctx) b p)
  closeMulti ctx b (Rec p) = Rec (closeMulti (incrLevelCtx ctx) b p)

instance Alpha p => Alpha (TRec p)

-- | Constructor for recursive patterns.
rec :: Alpha p => p -> Rec p
rec p = Rec (close (patternCtx initialCtx) (namePatFind p) p)

-- | Destructor for recursive patterns.
unrec :: Alpha p => Rec p -> p
unrec r@(Rec p) = open (patternCtx initialCtx) (nthPatFind r) p
