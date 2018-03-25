{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}

module Data.THUnify.Prelude.SafeCopy
    ( Serialized(encode', decode')
    , safeCopyVersion
    ) where

import Data.Generics (Data)
import Data.Int (Int32)
import Data.SafeCopy (SafeCopy, Version, version)
import Data.SafeCopy.Internal (unVersion)

class (Data s, Eq s, Ord s, Show s) => Serialized a s where
  encode' :: a -> s
  decode' :: forall m. Monad m => s -> m a

safeCopyVersion :: forall a. SafeCopy a => a -> Int32
safeCopyVersion = unVersion . version'
    where
      version' :: forall a'. SafeCopy a' => a' -> Version a'
      version' _ = version
