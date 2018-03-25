-- | General purpose functions, not specifically related to this library.

{-# LANGUAGE CPP #-}
{-# LANGUAGE RankNTypes #-}
{-# OPTIONS -Wall #-}

module Data.THUnify.Prelude.Monad
    ( anyM'
    , everywhereM'
    ) where

import Data.Bool (bool)
import Data.Generics (GenericM, gmapM)

anyM' :: Monad m => (s -> Maybe (a, s)) -> (a -> m Bool) -> s -> m Bool
anyM' vw p s =
  maybe
    (return False)
    (\(x, s') -> p x >>= bool (anyM' vw p s') (return True))
    (vw s)

#if 0
anyM'' :: (Traversable t, Monad m) => (a -> m Bool) -> t a -> m Bool
anyM'' p = liftM or . mapM p
#endif

-- | Monadic variation on everywhere'
everywhereM' :: Monad m => GenericM m -> GenericM m
everywhereM' f x
  = do x' <- f x
       gmapM (everywhereM' f) x'
