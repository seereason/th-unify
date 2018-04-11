-- | General purpose functions, not specifically related to this library.

module Data.THUnify.Prelude
    ( module Data.THUnify.Prelude.Containers
    , module Data.THUnify.Prelude.Debug
    , module Data.THUnify.Prelude.Desugar
    , module Data.THUnify.Prelude.Monad
    , module Data.THUnify.Prelude.Ppr
    -- , module Data.THUnify.Prelude.Text
    , module Data.THUnify.Prelude.TH
    , gFind
    ) where

import Control.Monad (MonadPlus, msum)
import Data.Generics (Data, listify, Typeable)
import Data.THUnify.Prelude.Containers
import Data.THUnify.Prelude.Debug
import Data.THUnify.Prelude.Desugar
import Data.THUnify.Prelude.Monad
import Data.THUnify.Prelude.Orphans
import Data.THUnify.Prelude.Ppr
--import Data.THUnify.Prelude.Text
import Data.THUnify.Prelude.TH

gFind :: (MonadPlus m, Data a, Typeable b) => a -> m b
gFind = msum . map return . listify (const True)
