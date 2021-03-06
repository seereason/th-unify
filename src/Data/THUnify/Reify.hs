{-# LANGUAGE CPP #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}

module Data.THUnify.Reify
    ( typesFromClassName
    , typesFromClassName'
    , typesFromFamilyName
    , tySynInstPairs
    ) where

import Data.List (intercalate)
import Data.Map as Map (fromList, Map)
import Data.Set as Set (fromList, Set, toList)
import Data.THUnify.Prelude (decomposeType, E(unE), expandTypeQ)
import Data.THUnify.TypeRep (typeRepFromType)
import Language.Haskell.TH
import Language.Haskell.TH.Desugar (DsMonad)
import Language.Haskell.TH.Instances ()
import Language.Haskell.TH.Syntax (Quasi)

-- | Find all the types that are currently instances of some class.
-- @@
-- λ> mapM_ (putStrLn . pprint) (Data.Set.toList $(typesFromClassName ''Enum >>= lift))
-- Data.Functor.Const.Const a_0 b_1
-- Data.Monoid.Alt f_0 a_1
-- ...
-- Data.UserId.UserId
-- ()
-- @@
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
typesFromFamilyName :: DsMonad m => Name -> m (Map (E Type) (E Type))
typesFromFamilyName fname = do
  (pairs :: [(Type, Type)]) <- tySynInstPairs fname
  pairs' <- mapM (\(a, b) -> (,) <$> expandTypeQ (pure a) <*> expandTypeQ (pure b)) pairs
  return $ Map.fromList pairs'

tySynInstPairs :: Quasi m => Name -> m [(Type, Type)]
tySynInstPairs name = do
  FamilyI _ insts <- runQ $ reify name
  return $ fmap (\(TySynInstD _name (TySynEqn [arg] syn)) -> (arg, syn)) insts
