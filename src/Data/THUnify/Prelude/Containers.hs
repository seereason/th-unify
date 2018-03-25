module Data.THUnify.Prelude.Containers
    ( differences
    , adjacent
    , decreasing
    , increasing
    , prefixEq
    , preservePrefix
    , zipMaybes
    , partitions
    , partitionsM
    , setPartitionM
    , unsnoc
    , mapMaybe
    ) where

import Control.Monad.Extra (partitionM)
import Data.List (sort, (\\), partition)
import Data.ListLike as LL (cons, uncons, ListLike)
import Data.Set as Set (difference, fromList, null, Set, toList)

adjacent :: [a] -> [(a, a)]
adjacent (a : b : more) = (a, b) : adjacent (b : more)
adjacent _ = []

decreasing :: Ord a => [a] -> Bool
decreasing xs = increasing (reverse xs)

increasing :: Ord a => [a] -> Bool
increasing xs = sort xs == xs

prefixEq :: Eq a => [a] -> [a] -> Bool
prefixEq a b =
  take n a == take n b
  where n = min (length a) (length b)

preservePrefix :: Ord a => [a] -> [a] -> [a]
preservePrefix prefix added = prefix ++ (added \\ prefix)

-- | Properties of r = zipMaybes xs ys:
-- all isJust (fmap fst r) || all isJust (fmap snd r)
-- length r == max (length xs) (length ys)
zipMaybes :: [a] -> [b] -> [(Maybe a, Maybe b)]
zipMaybes [] ys = zip (repeat Nothing) (fmap Just ys)
zipMaybes xs [] = zip (fmap Just xs) (repeat Nothing)
zipMaybes (x : xs) (y : ys) = (Just x, Just y) : zipMaybes xs ys

-- | Given n predicates on a, partition a list of a into n+1 sub-lists, where
-- predicate n is the first predicate to satisfy each element of the nth sublist.
-- @@
-- > partitions [odd, (< 5)] [1,2,3,4,5,6,7,8,9] -> [[1,3,5,7,9],[2,4],[6,8]]
-- @@
partitions :: [a -> Bool] -> [a] -> [[a]]
partitions [] xs = [xs]
partitions (p : ps) xs =
    let (xs1, xs') = partition p xs in xs1 : partitions ps xs'

-- | Monadic version of partitions
partitionsM :: Monad m => [a -> m Bool] -> [a] -> m [[a]]
partitionsM [] xs = return [xs]
partitionsM (p : ps) xs =
    partitionM p xs >>= \(xs1, xs') -> (xs1 :) <$> partitionsM ps xs'

setPartitionM :: (Ord a, Monad m) => (a -> m Bool) -> Set a -> m (Set a, Set a)
setPartitionM p s = partitionM p (Set.toList s) >>= \(a, b) -> return (Set.fromList a, Set.fromList b)

-- | Given two sets, returns a pair: (extra, missing)
differences :: Ord a => Set a -> Set a -> Maybe (Set a, Set a)
differences s1 s2 =
    if Set.null extra && Set.null missing then Nothing else Just (extra, missing)
    where
      extra = Set.difference s1 s2
      missing = Set.difference s2 s1

unsnoc :: [a] -> Maybe ([a], a)
unsnoc xs = case uncons (reverse xs) of
              Nothing -> Nothing
              Just (x, xs') -> Just (reverse xs', x)

mapMaybe :: (ListLike l a, ListLike k b) => (a -> Maybe b) -> l -> k
mapMaybe f l =
  case uncons l of
    Nothing -> mempty
    Just (x, xs) ->
      let rs = mapMaybe f xs in
      case f x of
        Nothing -> rs
        Just r -> cons r rs
