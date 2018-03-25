{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE TemplateHaskell #-}

-- | Type expansion by th-desugar
module Data.THUnify.Prelude.Desugar
    ( E(E, unE), fakeE
    , expandType
    , expandTypeQ
    ) where

import Data.Data (Data)
import Language.Haskell.TH (Ppr(ppr), Type)
import Language.Haskell.TH.Desugar as DS (DsMonad, typeToTH, dsType, expand)
import Language.Haskell.TH.Lift (Lift(lift))

newtype E a = E {unE :: a} deriving (Eq, Ord, Functor, Show, Data)

-- | For places where we expected an expanded type and suspect we have one
-- but its E constructor has been lost.
fakeE  :: Type -> E Type
fakeE = E

instance Lift a => Lift (E a) where
  lift (E a) = [|E $(lift a)|]

instance Ppr t => Ppr (E t) where
  ppr = ppr . unE

-- | Use expand from th-desugar and mark result with the newtype E.
expandType :: DsMonad m  => Type -> m (E Type)
expandType typ = (E . DS.typeToTH) <$> (DS.dsType typ >>= DS.expand)

expandTypeQ :: DsMonad m  => m Type-> m (E Type)
expandTypeQ typ = typ >>= expandType

