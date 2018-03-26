{-# LANGUAGE CPP #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# OPTIONS -Wall #-}

-- | New View mechanism just uses Ixed/Index/IxValue instances.  For example
-- @@
--   instance View ReportStatus where
--     type ViewType ReportStatus = Text
--     _View = readShowIso Draft . iso pack unpack
-- @@
-- becomes
-- @@
--   instance Ixed ReportStatus where ix ViewIndex = readShowIso Draft . iso pack unpack
--   type instance IxValue ReportStatus = Text
--   type instance Index ReportStatus = ViewIndex
-- @@
module Data.THUnify.View
    ( View(ViewType, _View)
    , viewTypes
    , viewType
    , viewMap
    ) where

import Control.Lens hiding (Index, Strict)
import Data.Generics (Data)
import Data.Map (Map)
import Data.THUnify.Prelude (E, pprint1, unlifted)
import Data.THUnify.Reify (typesFromFamilyName)
import Data.THUnify.Unify (expandBindings, unify)
import Language.Haskell.TH
import Language.Haskell.TH.Desugar (DsMonad)
import Language.Haskell.TH.Instances ()
import Language.Haskell.TH.Syntax (Quasi)

-- | If there is an instance of View for a type @a@, then when @a@
-- appears in the data, the lens returned by '_View' is used to
-- compute the value of type @ViewType a@, and that value is used
-- instead.  For exmaple, a 'View' could be used to modify the value
-- obtained from a database so that it is more suitable to the user
-- interface that uses that value.  Then the @ViewType a@ value is
-- transformed back into an @a@ and stored in the database.
class (Data s, Data (ViewType s)) => View s where
    type ViewType s
    _View :: Iso' s (ViewType s)

-- | Retrieve every View instance known to the Q monad and return the
-- union of all of their a and b types.
viewTypes :: Quasi m => m [Type]
viewTypes = do
  FamilyI _ tySynInsts <- runQ $ reify ''ViewType
  return $ concatMap (\ (TySynInstD _vt (TySynEqn [a] b)) -> [a, b]) tySynInsts

-- | Attempt to implement viewInstanceType without the ExpandMap.
viewType :: Quasi m => Type -> m (Maybe Type)
viewType typ = do
  -- It is an error to ask an unlifted type whether it is an instance.
  primitive <- unlifted typ
  case primitive of
    True -> pure Nothing
    False -> do
      vInsts <- runQ $ reifyInstances ''ViewType [typ]
      case vInsts of
        -- tparam is the type parameter applied to ViewType.  This
        -- type is the class instance to which we are applying the
        -- ViewType function.
        [TySynInstD _ (TySynEqn [tparam] type2)] ->
            -- Unify the original type with type1, and apply
            -- the resulting bindings to type2.
            fmap (`expandBindings` type2) <$> unify (pure typ) (pure tparam)
        [] -> return Nothing
        _ -> error $ unlines (("Multiple instance ViewType " ++ pprint1 typ ++ ":") : fmap pprint1 vInsts)

viewMap :: DsMonad m => m (Map (E Type) (E Type))
viewMap = runQ $ typesFromFamilyName ''ViewType
