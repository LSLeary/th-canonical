
-- Should perhaps use ordered-containers:Data.Set.Ordered

{-# OPTIONS_GHC -Wno-unused-imports #-}

module Data.Ordered.Set (
  Set,
  member,
  singleton,
  toList,
  fromList,
  fromUnordered,
  (\\),
) where

-- base
import Data.Bifunctor (first)
import Data.List (foldl')

-- containers
import Data.Set qualified as S


data Set a = Set
  { order    ::        [a]
  , elements :: !(S.Set a)
  } deriving (Eq, Ord)

instance Foldable Set where
  foldMap f Set{order} = foldMap f order

-- | Left biased.
instance Ord a => Semigroup (Set a) where
  s1 <> s2 = Set
    { order    = order s1 <> filter (`S.notMember` elements s1) (order s2)
    , elements = elements s1 <> elements s2
    }

instance Ord a => Monoid (Set a) where
  mempty = Set mempty mempty

member :: Ord a => a -> Set a -> Bool
member x = S.member x . elements

singleton :: a -> Set a
singleton x = Set
  { order    = [x]
  , elements = S.singleton x
  }

toList :: Set a -> [a]
toList = order

fromList :: Ord a => [a] -> Set a
fromList xs = case foldl' extend mempty xs of
  (reversed, elements) -> Set{ order = reverse reversed, elements }
 where
  extend (ro, elems) x
    = first (\b -> if b then ro else x:ro)
    $ S.alterF (\b -> (b, True)) x elems

fromUnordered :: S.Set a -> Set a
fromUnordered elements = Set{ order = S.toList elements, elements }

(\\) :: Ord a => Set a -> Set a -> Set a
s1 \\ s2 = Set
  { order    = filter (`S.notMember` elements s2) (order s1)
  , elements = elements s1 S.\\ elements s2
  }
infixl 9 \\

