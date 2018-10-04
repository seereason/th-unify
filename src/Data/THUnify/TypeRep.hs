-- | Correspondence between template haskell Type and syb TypeRep.

{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# OPTIONS -Wall #-}

module Data.THUnify.TypeRep
    ( Dispatcher
    , typeDispatcher
    , tySynDispatcher
    , typeFromTypeRep
    , typeRepFromType
    , expandedTypeFromTypeRep
    ) where

import Control.Lens (_1, over)
import Data.Either (partitionEithers)
import Data.Generics (Data, Proxy(Proxy), splitTyConApp, tyConName, TyCon, tyConModule, tyConPackage, tyConFingerprint, TypeRep, typeRep)
import Data.Map as Map (findWithDefault, fromList)
import Data.THUnify.Prelude (composeType, E, expandTypeQ)
import Language.Haskell.TH
import Language.Haskell.TH.Instances ()
import Language.Haskell.TH.Lift (Lift(lift))

-- Q monad is required due to use of 'lookupTypeName'.
typeFromTypeRep :: TypeRep -> Q (Either [String] Type)
typeFromTypeRep = goRep
    where
      goRep :: TypeRep -> Q (Either [String] Type)
      goRep rep = uncurry goTree (splitTyConApp rep)

      goTree :: TyCon -> [TypeRep] -> Q (Either [String] Type)
      goTree c rs = (compose . over _1 concat . partitionEithers) <$> ((:) <$> goTyCon c <*> mapM goRep rs)

      goTyCon :: TyCon -> Q (Either [String] Type)
      goTyCon c | tyConName c == "[]" = return (Right ListT)
      goTyCon c | tyConName c == "(,)" = return (Right (TupleT 2))
      goTyCon c | tyConName c == "(,,)" = return (Right (TupleT 3))
      goTyCon c | tyConName c == "(,,,)" = return (Right (TupleT 4))
      goTyCon c | tyConName c == "(,,,,)" = return (Right (TupleT 5))
      goTyCon c | tyConName c == "(,,,,,)" = return (Right (TupleT 6))
      goTyCon c | tyConName c == "(,,,,,,)" = return (Right (TupleT 7))
      goTyCon c | tyConName c == "(,,,,,,,)" = return (Right (TupleT 8))
      goTyCon c | tyConName c == "(,,,,,,,,)" = return (Right (TupleT 9))
      goTyCon c | tyConName c == "()" = return (Right (TupleT 0))
      goTyCon c =
          -- add location to message here
          maybe (Left ["Import required of type " ++ showTyCon c]) (Right . ConT)
            <$> lookupTypeName ({-tyConModule c ++ "." ++-} tyConName c)
      compose :: ([String], [Type]) -> Either [String] Type
      compose ([], ts) = Right (composeType ts)
      compose (es, _) = Left es

showTyCon :: TyCon -> String
showTyCon c =
        "TyCon {" ++
        "module=" ++ show (tyConModule c) ++
        " name=" ++ show (tyConName c) ++
        " package=" ++ show (tyConPackage c) ++
        " fingerprint=" ++ show (tyConFingerprint c) ++ "}"

instance Lift TypeRep where
  -- lift :: Lift t => t -> Q Exp
  -- lift (typeof 123) -> [|typeRep (Proxy :: Proxy Int)|]
  lift rep = [|typeRep (Proxy :: Proxy $(either (error . unlines) id <$> typeFromTypeRep rep))|]

-- | Convert a TypeRep to a Type
expandedTypeFromTypeRep :: TypeRep -> Q (Either [String] (E Type, TypeRep))
expandedTypeFromTypeRep rep =
    typeFromTypeRep rep >>=
    either (pure . Left) (\typ -> Right <$> ((,) <$> expandTypeQ (pure typ) <*> pure rep))

typeRepFromType :: TypeQ -> ExpQ -- :: TypeRep
typeRepFromType typ = [|typeRep (Proxy :: Proxy $typ)|]

type Dispatcher = (forall r. (forall d. Data d => Proxy d -> r) -> TypeRep -> r)

-- | Given a list of types, build a function that
-- takes a 'TypeRep' and passes the corresponding 'Proxy' argument
-- to a function of type @(forall d. Data d => Proxy d -> r)@.
typeDispatcher :: ExpQ -> [Type] -> ExpQ -- :: Dispatcher
typeDispatcher dflt types = tySynDispatcher dflt (fmap (\t -> (t, t)) types)

-- | Like 'typeDispatcher', but does an assoc on the type pair list.
-- Note that it is important for f to have a signature that allows it
-- to take @(forall d. Proxy d -> r)@ to avoid type errors.
tySynDispatcher :: ExpQ -> [(Type, Type)] -> ExpQ
tySynDispatcher dflt pairs =
    newName "r" >>= \r ->
    [| (\f t ->
            Map.findWithDefault
                ($dflt t)
                t
                (Map.fromList
                  $(listE
                     (fmap (\(typ1, typ2) ->
                                [|(typeRep (Proxy :: Proxy $(pure typ1)),
                                   f (Proxy :: Proxy $(pure typ2)))|]) pairs))))
          :: $(forallT [plainTV r] (pure []) [t|(forall d. Data d => Proxy d -> $(varT r)) -> TypeRep -> $(varT r)|]) |]
