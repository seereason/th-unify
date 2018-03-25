{-# LANGUAGE CPP #-}

module Data.THUnify.Reify
    ( typesFromClassName
    , typesFromClassName'
    , typesFromFamilyName
    , tySynInstPairs
    ) where

import Control.Monad (when)
import Control.Monad.RWS (ask, execRWS, get, local, modify, put, RWS)
import Control.Monad.State (execStateT, StateT)
import Data.Generics (Data, everywhere, mkT)
import Data.Map as Map ((!), fromList, insert, keys, lookup, Map, member)
import Data.Maybe (fromJust, fromMaybe, isJust)
import Data.Set as Set (fromList, insert, map, member, minView, null, Set, toList, union)
import Data.THUnify.Orphans ()
import Data.THUnify.Prelude (anyM', decomposeType, E(E, unE), expandTypeQ, toName)
import Data.THUnify.TestData
import Data.THUnify.TypeRep (typeRepFromType)
import Language.Haskell.TH
import Language.Haskell.TH.Instances ()
import Language.Haskell.TH.Syntax (qReify, Quasi)

-- | Find all the types that are currently instances of some class.
typesFromClassName :: Name -> Q (Set (E Type))
typesFromClassName cname = do
  (ClassI _ insts) <- reify cname
  Set.fromList <$> mapM (expandTypeQ . pure) (fmap go insts)
    where
      go :: Dec -> Type
#if MIN_VERSION_template_haskell(2,11,0)
      go (InstanceD _supers _ t _) =
#else
      go (InstanceD _supers t _) =
#endif
          let [_ixed, typ] = decomposeType t in
          typ
      go _ = error "expected InstanceD"

-- | Build a set of TypeRep
typesFromClassName' :: Name -> ExpQ
typesFromClassName' cname = do
  [|Set.fromList $(ListE <$> (typesFromClassName cname >>=
                              sequence . fmap (typeRepFromType . pure . unE) . Set.toList))|]

-- | Sounds the same as 'typeFunctionMap' - is it?
typesFromFamilyName :: Name -> Q (Map (E Type) (E Type))
typesFromFamilyName fname = do
  (FamilyI _ tySynInsts) <- reify fname
  let (pairs :: [(Type, Type)]) = fmap (\(TySynInstD _vt (TySynEqn [a] b)) -> (a, b)) tySynInsts
  pairs' <- mapM (\(a, b) -> (,) <$> expandTypeQ (pure a) <*> expandTypeQ (pure b)) pairs
  return $ Map.fromList pairs'

tySynInstPairs :: Name -> Q [(Type, Type)]
tySynInstPairs name = do
  FamilyI _ insts <- reify name
  return $ fmap (\(TySynInstD _name (TySynEqn [arg] syn)) -> (arg, syn)) insts
