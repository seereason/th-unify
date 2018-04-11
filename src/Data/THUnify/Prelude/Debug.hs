{-# LANGUAGE CPP #-}
{-# LANGUAGE DeriveDataTypeable, StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}

module Data.THUnify.Prelude.Debug
    ( HasMessageInfo(..)
    -- , R(..), verbosity, prefix
    , message
    , indent
    , fixme
    ) where

import Control.Lens (Lens', view)
import Control.Monad (when)
import Control.Monad.Reader (MonadReader)
import Data.List (intercalate)
import Debug.Trace (trace)

class HasMessageInfo a where
    verbosity' :: Lens' a Int
    prefix' :: Lens' a String

#if 0
-- | A type with a HasMessageInfo instance to use in the Reader or RWS monad.
data R
    = R
      { _verbosity :: Int
      , _prefix :: String
      }

$(makeLenses ''R)

instance HasMessageInfo R where
    verbosity' = verbosity
    prefix' = prefix
#endif

-- | Output a verbosity controlled error message with the current
-- indentation.
message :: ({-Quasi m,-} MonadReader r m, HasMessageInfo r) =>
           Int -> String -> m ()
message minv s = do
    v <- view verbosity'
    p <- view prefix'
    when (v >= minv) $ trace (indent p s) (return ()) -- (runQ . runIO . putStr . indent p) s

-- | Indent the lines of a message.
indent :: String -> String -> String
indent p s = intercalate "\n" $ fmap (p ++) (lines s)

fixme :: String -> a
fixme = error
