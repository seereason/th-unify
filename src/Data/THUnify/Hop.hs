{-# LANGUAGE CPP, ConstraintKinds #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS -Wall #-}

module Data.THUnify.Hop
    ( SerializedIndex(..)
    , Hop(..)
    , hopKey
    ) where

import Data.ByteString (ByteString)
import Data.Generics (Data, Typeable)
import Data.THUnify.Orphans ()
import Data.THUnify.Prelude (Serialized(decode', encode'))
import Data.SafeCopy (base)
import Data.THUnify.SafeCopy (deriveSafeCopy)
import Data.Serialize (Serialize(put, get), decode, encode, putWord8, getWord8)
import Language.Haskell.TH (Ppr(ppr))
import Language.Haskell.TH.Lift (deriveLift)
import Language.Haskell.TH.PprLib (ptext, hcat)
import Language.Haskell.TH.TypeGraph.Serialize (deriveSerialize)
import Language.Haskell.TH.TypeGraph.WebRoutesTH (derivePathInfo)
import Test.QuickCheck (Arbitrary(arbitrary), oneof)
import Text.ParserCombinators.Parsec.Prim (many)
import Web.Routes (PathInfo(..))

newtype SerializedIndex = SerializedIndex {unSerializedIndex :: ByteString} deriving (Data, Eq, Ord, Show)

$(deriveSerialize [t|SerializedIndex|])
$(derivePathInfo [t|SerializedIndex|])
$(deriveSafeCopy 1 'base [t|SerializedIndex|])

instance Serialize a => Serialized a SerializedIndex where
  decode' = either fail return . decode . unSerializedIndex
  encode' = SerializedIndex . encode

-- | The 'Hop' type represents the path from a type to one of the
-- subtypes it might contain.  This is either via a record field, or
-- via the type's Ixed instance (if it has one.)
data Hop key
    = FieldHop Int Int
      -- ^ Hop to one of the fields of a record - the constructor and
      -- field number are specified.  Also handles tuples, which are
      -- single constructor types.
    | IxHop key
    -- ^ Hop from an instance of 'Ixed', such as @[]@ or @Map@, via
    -- some key of the corresponding 'Index' type, to a value of the
    -- corresponding 'IxValue' type.  For serialization the
    -- 'Data.Serialize.encode' function is applied to the key to make
    -- this a monomorphic type @Hop SerializedIndex@.
    | AtHop key
    -- ^ Hop from an instance of At, which is a subclass of Ixed
    | ViewHop
    deriving (Show, Eq, Ord, Functor, Data, Typeable)

hopKey :: Hop key -> Maybe key
hopKey (IxHop key) = Just key
hopKey (AtHop key) = Just key
hopKey _ = Nothing

instance Arbitrary key => Arbitrary (Hop key) where
  arbitrary = oneof [ FieldHop <$> arbitrary <*> arbitrary
                    , IxHop <$> arbitrary
                    , AtHop <$> arbitrary
                    , pure ViewHop ]

instance PathInfo (Hop key) => PathInfo [Hop key] where
    toPathSegments = concat . fmap toPathSegments
    fromPathSegments = many fromPathSegments

instance Ppr typ => Ppr (Hop typ) where
    ppr (FieldHop c f) = ptext ("FieldHop " ++ show c ++ " " ++ show f)
    ppr (IxHop t) = hcat [ptext "IxHop ", ppr t]
    ppr (AtHop t) = hcat [ptext "AtHop ", ppr t]
    ppr ViewHop = ptext "ViewHop"

$(derivePathInfo [t|Hop|])
#if 1
instance Serialize (Hop SerializedIndex) where
    put (FieldHop c f) = putWord8 0 >> put c >> put f
    put (IxHop a) = putWord8 1 >> put (unSerializedIndex a)
    put (AtHop a) = putWord8 2 >> put (unSerializedIndex a)
    put ViewHop = putWord8 3
    get = getWord8 >>= \i ->
          case i of
            0 -> FieldHop <$> get <*> get
            1 -> (IxHop . SerializedIndex) <$> get
            2 -> (AtHop . SerializedIndex) <$> get
            3 -> pure ViewHop
            n -> error $ "decode - Unexpected tag for Hop SerializedIndex: " ++ show n
#else
$(deriveSerialize [t|Hop|])
#endif
$(deriveSafeCopy 3 'base [t|Hop|])

$(deriveLift ''Hop)
