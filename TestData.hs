{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TemplateHaskell #-}

module TestData where

import Data.ByteString
import Data.Generics hiding (Generic)
import Data.Serialize (Serialize)
import Data.Time (UTCTime)
import Data.Vector (Vector)
import Data.UserId (UserId)
import GHC.Generics

data Hop key
    = FieldHop Int Int
    | IxHop key
    | AtHop key
    | ViewHop
    deriving (Show, Eq, Ord, Functor, Data, Typeable)

newtype SerializedIndex = SerializedIndex {unSerializedIndex :: ByteString} deriving (Data, Eq, Ord, Show, Generic, Serialize)

-- $(deriveSafeCopy 1 'base ''SerializedIndex)

data EventTree t s
    = Current
      { _events :: [EventMono t s]
      -- ^ Most recent event first
      , _value :: s
      -- ^ Result of applying all the events to some initial value.
      }
    | Previous
      { _events :: [EventMono t s]
      -- ^ EventTree that occurred before some conflict caused the
      -- split that creating the branches.
      , _branches :: [EventTree t s]
      } deriving (Functor)

type EventMono = Event SerializedIndex SerializedIxValue SerializedValue

data Event k v a t s
    = Event
      { _user :: UserId
      -- ^ The event's creator
      , _when :: UTCTime
      -- ^ Time stamp assigned by the client as soon as possible after
      -- the user input that created the event.
      , _accession :: EventId
      -- ^ A sequence number assigned by the server when the event
      -- becomes part of a History.
      , _edit :: Edit k v a t s
      }

instance Functor (Event k v a t) where
    fmap f (Event u t a e) = Event u t a (fmap f e)

newtype EventId = EventId {unEventId :: Int}
    deriving (Eq, Ord, Read, Show, Data)

data Edit k v a t s
    = Updated {_oldV :: a, _newV :: a, _ePath :: TypeSPath t s}
    -- ^ Replace old with new
    | Reordered {_oldO :: Vector k, _newO :: Vector k, _ePath :: TypeSPath t s}
    -- ^ Update the order of the keys.
    | Inserted {_oldO :: Vector k, _newO :: Vector k, _eKey :: k, _insV :: v, _ePos :: Int, _ePath :: TypeSPath t s}
    -- ^ Insert an element at position n
    | Deleted {_oldO :: Vector k, _newO :: Vector k, _eKey :: k, _delV :: v, _ePos :: Int, _ePath :: TypeSPath t s}
    -- ^ Delete the element at position n

instance Functor (Edit k v a t) where
    fmap _ (Updated old new (TypeSPath hs)) = Updated old new (TypeSPath hs)
    fmap _ (Reordered old new (TypeSPath hs)) = Reordered old new (TypeSPath hs)
    fmap _ (Inserted old new k v pos (TypeSPath hs)) = Inserted old new k v pos (TypeSPath hs)
    fmap _ (Deleted old new k v pos (TypeSPath hs)) = Deleted old new k v pos (TypeSPath hs)

data TypePath t s a = TypePath [Hop SerializedIndex] deriving (Show, Eq, Ord, Data, Typeable)
data TypeSPath t s = TypeSPath [Hop SerializedIndex] deriving (Show, Eq, Ord, Data, Typeable)

newtype SerializedValue = SerializedValue {unSerializedValue :: ByteString} deriving (Data, Eq, Ord, Show)
newtype SerializedIxValue = SerializedIxValue {unSerializedIxValue :: ByteString} deriving (Data, Eq, Ord, Show)
