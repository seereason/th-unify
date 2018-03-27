-- | Compute which type parameters are phantom types.

{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# OPTIONS -Wall #-}

module Data.THUnify.Phantom
    ( phantom
    , nonPhantom
    ) where

import Control.Lens ((%=), makeLenses, over, use, view)
import Control.Monad.RWS (execRWST, local, RWST)
import Data.Set as Set (delete, difference, empty, insert, member, Set)
import Data.THUnify.Prelude (message, pprint1)
--import Data.THUnify.TestData
import Data.THUnify.Unify (findTypeVars, foldType, R(..), prefix)
import Language.Haskell.TH (Name, Type(VarT))
import Language.Haskell.TH.Desugar (DsMonad)

data S
    = S { _unused :: Set Name
        , _visited :: Set Type
        } deriving Show

$(makeLenses ''S)

-- | Return a Type's non-phantom type variables.
-- @@
-- λ> $([t|forall a b. TypeSPath a b|] >>= phantom >>= lift)
-- fromList [a, b]
-- λ> $([t|forall a b. (a, b)|] >>= phantom >>= lift)
-- fromList []
-- @@
phantom :: forall m. (DsMonad m) => Type -> m (Set Name)
phantom typ0 = do
  (view unused . fst) <$> execRWST (go typ0) (R 0 "" []) (S {_unused = findTypeVars typ0, _visited = Set.empty})
  where
    go :: Type -> RWST R () S m ()
    go typ = do
      types <- use visited
      case Set.member typ types of
        True -> return ()
        False -> do
          visited %= Set.insert typ
          message 1 ("phantom typ=" ++ pprint1 typ)
          local (over prefix (++ " ")) $
            foldType (const return) g typ mempty
    g typ () = do
      vars <- use unused
      message 1 ("phantom unused=" ++ pprint1 vars ++ ", typ=" ++ pprint1 typ)
      case typ of
        VarT s -> unused %= Set.delete s
        _ -> go typ

nonPhantom :: forall m. (DsMonad m) => Type -> m (Set Name)
nonPhantom typ = Set.difference (findTypeVars typ) <$> phantom typ
