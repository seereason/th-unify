-- | Compute which type parameters are phantom types.

{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
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
import Control.Monad.RWS (execRWST, local, RWST, when)
import Data.Set as Set (delete, difference, empty, member, null, Set)
import Extra.Debug (message, Verbosity)
import Extra.Pretty (pprint1)
import Data.THUnify.Unify (findTypeVars, foldType, HasVisited(visited), RT(..), prefix)
import Language.Haskell.TH (Name, Type(VarT))
import Language.Haskell.TH.Desugar (DsMonad)

data S
    = S { _unused :: Set Name -- ^ Type variables for which we have not yet encountered a binding
        , _visitedNames :: Set Name -- ^ Type names we have reified
        } deriving Show

$(makeLenses ''S)

instance HasVisited S where
  visited = visitedNames

-- | Return a Type's non-phantom type variables.
-- @@
-- λ> $([t|forall a b. TypeSPath a b|] >>= phantom >>= lift)
-- fromList [a, b]
-- λ> $([t|forall a b. (a, b)|] >>= phantom >>= lift)
-- fromList []
-- @@
phantom :: forall m. (DsMonad m, Verbosity RT (RWST RT () S m)) => Type -> m (Set Name)
phantom typ0 = do
  (view unused . fst) <$> execRWST (go typ0) (RT 0 "" []) (S {_unused = findTypeVars typ0, _visitedNames = Set.empty})
  where
    go :: Type -> RWST RT () S m ()
    go typ = do
      vars <- use unused
      if Set.null vars
      then return () -- All variables determined to be non-phantom
      else do
        --types <- use visited
        --case Set.member typ types of
        --  True -> return ()
        --  False -> do
        --    visited %= Set.insert typ
        --    message 1 ("phantom visiting " ++ pprint1 typ)
            local (over prefix (++ " ")) $
              foldType (const return) g typ mempty
    g typ () = do
      vars <- use unused
      case typ of
        VarT s -> do
          when (s `member` vars) (message 1 ("phantom found " ++ pprint1 s))
          unused %= Set.delete s
        _ -> go typ

nonPhantom :: forall m. (DsMonad m, Verbosity RT (RWST RT () S m)) => Type -> m (Set Name)
nonPhantom typ = Set.difference (findTypeVars typ) <$> phantom typ
