{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Data.THUnify.TestData where

import Data.ByteString
import Data.Generics hiding (Generic)
import Data.Serialize (Serialize)
import Data.SafeCopy (base, deriveSafeCopy)
import GHC.Generics

data Hop key
    = FieldHop Int Int
    | IxHop key
    | AtHop key
    | ViewHop
    deriving (Show, Eq, Ord, Functor, Data, Typeable)

newtype SerializedIndex = SerializedIndex {unSerializedIndex :: ByteString} deriving (Data, Eq, Ord, Show, Generic, Serialize)

$(deriveSafeCopy 1 'base ''SerializedIndex)

data TypePath t s a = TypePath [Hop SerializedIndex] deriving (Show, Eq, Ord, Data, Typeable)
data TypeSPath t s = TypeSPath [Hop SerializedIndex] deriving (Show, Eq, Ord, Data, Typeable)
