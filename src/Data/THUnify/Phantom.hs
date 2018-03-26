-- | Compute which type parameters are phantom types.

{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# OPTIONS -Wall #-}

module Data.THUnify.Phantom
    ( phantom
    , nonPhantom
    ) where

--import Control.Lens (over)
import Control.Monad.RWS (execRWST, {-local,-} modify, RWST)
import Data.Set as Set (difference, Set)
import Data.THUnify.Prelude ({-message, pprint1, prefix,-} R(..))
--import Data.THUnify.TestData
import Data.THUnify.Unify (findTypeVars, foldType)
import Language.Haskell.TH (Q, Type, Name)
import Language.Haskell.TH.Desugar (DsMonad)

-- | Return a Type's non-phantom type variables.
-- @@
-- λ> $([t|forall a b. TypeSPath a b|] >>= phantom >>= lift)
-- fromList [a, b]
-- λ> $([t|forall a b. (a, b)|] >>= phantom >>= lift)
-- fromList []
-- @@
phantom :: forall m. (m ~ Q, DsMonad m) => Type -> m (Set Name)
phantom typ = do
  fst <$> execRWST (do -- message 0 ("phantom typ=" ++ pprint1 typ)
                       -- local (over prefix (++ " ")) $
                         foldType (const return) g typ mempty)
    (R 0 "") (findTypeVars typ)
  where
    g :: Monad m => Type -> () -> RWST R () (Set Name) m ()
    g typ' () = do
      -- message 0 ("phantom typ'=" ++ pprint1 typ')
      modify (`Set.difference` (findTypeVars typ'))

nonPhantom :: forall m. (m ~ Q, DsMonad m) => Type -> m (Set Name)
nonPhantom typ = Set.difference (findTypeVars typ) <$> phantom typ
