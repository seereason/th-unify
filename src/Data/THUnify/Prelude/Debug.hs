{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses, UndecidableInstances #-}
{-# LANGUAGE DeriveDataTypeable, StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}

module Data.THUnify.Prelude.Debug
    ( HasMessageInfo(verbosity', prefix')
#if 0
    , hMessage
    , message
    , oMessage
    , eMessage
#else
    , Verbosity(message)
#endif
    , indent
    , fixme
    ) where

import Control.Lens (Lens', view)
import Control.Monad (when)
import Control.Monad.Identity (Identity)
import Control.Monad.Reader (MonadReader, ReaderT)
import Control.Monad.RWS
import Control.Monad.Trans (lift)
import Data.List (intercalate)
import Language.Haskell.TH.Syntax (Q, runIO)
import System.IO (hPutStrLn, stderr)
import System.IO.Unsafe (unsafePerformIO)

class HasMessageInfo a where
    verbosity' :: Lens' a Int
    prefix' :: Lens' a String

#if 0
hMessage :: (MonadReader r m, HasMessageInfo r) => Handle -> Int -> String -> m ()
hMessage h minv s = do
    v <- view verbosity'
    p <- view prefix'
    when (v >= minv) $ (return . unsafePerformIO . hPutStr stderr . indent p) s

oMessage :: (MonadReader r m, HasMessageInfo r) => Int -> String -> m ()
oMessage = hMessage stdout

message :: (MonadReader r m, HasMessageInfo r) => Int -> String -> m ()
message = oMessage

eMessage :: (MonadReader r m, HasMessageInfo r) => Int -> String -> m ()
eMessage = hMessage stderr
#else
-- | Class of monads with a verbosity level and a stored indentation string.
class (HasMessageInfo r, MonadReader r m) => Verbosity r m where
  message :: Int -> String -> m ()
  -- ^ If the monad's verbosity level exceeds the verbosity argument,
  -- prepend the current indentation string to the lines of a message
  -- and output it.

instance HasMessageInfo r => Verbosity r (ReaderT r Q) where
  message minv s = do
    v <- view verbosity'
    p <- view prefix'
    when (v >= minv) $ (lift . runIO . hPutStrLn stderr . indent p) s

instance (HasMessageInfo r, Monoid w) => Verbosity r (RWST r w s Q) where
  message minv s = do
    v <- view verbosity'
    p <- view prefix'
    when (v >= minv) $ (lift . runIO . hPutStrLn stderr . indent p) s

instance HasMessageInfo r => Verbosity r (ReaderT r IO) where
  message minv s = do
    v <- view verbosity'
    p <- view prefix'
    when (v >= minv) $ (lift . putStrLn . indent p) s

instance (HasMessageInfo r, Monoid w) => Verbosity r (RWST r w s IO) where
  message minv s = do
    v <- view verbosity'
    p <- view prefix'
    when (v >= minv) $ (lift . putStrLn . indent p) s

instance HasMessageInfo r => Verbosity r (ReaderT r Identity) where
  message minv s = do
    v <- view verbosity'
    p <- view prefix'
    when (v >= minv) $ (return . unsafePerformIO . putStrLn . indent p) s

instance (HasMessageInfo r, Monoid w) => Verbosity r (RWST r w s Identity) where
  message minv s = do
    v <- view verbosity'
    p <- view prefix'
    when (v >= minv) $ (return . unsafePerformIO . putStrLn . indent p) s

#if 0
instance (Quasi m, HasMessageInfo r, Monoid w) => Verbosity r (RWST r w s m) where
  message minv s = do
    v <- view verbosity'
    p <- view prefix'
    when (v >= minv) $ (lift . runQ . runIO . hPutStr stderr . indent p) s
#endif

#endif

-- | Indent the lines of a message.
indent :: String -> String -> String
indent p s = intercalate "\n" $ fmap (p ++) (lines s)

fixme :: String -> a
fixme = error
