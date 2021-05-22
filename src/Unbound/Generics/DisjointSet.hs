-- | A @DisjointSet a@ is a 'Just' a list of distinct @a@s.  In addition to a monoidal
-- structure, a disjoint set also has an annihilator 'inconsistentDisjointSet'.
--
-- @
--   inconsistentDisjointSet \<> s == inconsistentDisjointSet
--   s \<> inconsistentDisjoinSet == inconsistentDisjointSet
-- @
module Unbound.Generics.DisjointSet where

import Data.List (intersect)
import Data.Semigroup as Sem

newtype DisjointSet a = DisjointSet (Maybe [a])

-- | @since 0.3.2
instance Eq a => Sem.Semigroup (DisjointSet a) where
  (<>) = \s1 s2 ->
    case (s1, s2) of
      (DisjointSet (Just xs), DisjointSet (Just ys)) | disjointLists xs ys -> DisjointSet (Just (xs <> ys))
      _ -> inconsistentDisjointSet

instance Eq a => Monoid (DisjointSet a) where
  mempty = DisjointSet (Just [])
  mappend = (<>)

instance Foldable DisjointSet where
  foldMap summarize (DisjointSet ms) = foldMap (foldMap summarize) ms

-- | Returns a @DisjointSet a@ that is the annihilator element for the 'Monoid' instance of 'DisjointSet'.
inconsistentDisjointSet :: DisjointSet a
inconsistentDisjointSet = DisjointSet Nothing

-- | @singletonDisjointSet x@ a @DisjointSet a@ that contains the single element @x@
singletonDisjointSet :: a -> DisjointSet a
singletonDisjointSet x = DisjointSet (Just [x])

disjointLists :: Eq a => [a] -> [a] -> Bool
disjointLists xs ys = null (xs `intersect` ys)

-- | @isConsistentDisjointSet@ returns @True@ iff the given disjoint set is not inconsistent.
isConsistentDisjointSet :: DisjointSet a -> Bool
isConsistentDisjointSet (DisjointSet Nothing) = False
isConsistentDisjointSet _ = True

-- | @isNullDisjointSet@ return @True@ iff the given disjoint set is 'mempty'.
isNullDisjointSet :: DisjointSet a -> Bool
isNullDisjointSet (DisjointSet (Just [])) = True
isNullDisjointSet _ = False