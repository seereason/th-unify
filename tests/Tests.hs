{-# LANGUAGE CPP #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# OPTIONS -Wall -Wno-orphans #-}

import Data.Generics
import Data.Map
--import Data.SafeCopy
import Data.Set as Set (fromList)
import Data.THUnify.Monad
import qualified Data.THUnify.Phantom as Old (nonPhantom, phantom)
import Data.THUnify.Traverse (phantom)
import Language.Haskell.TH.Lift (lift)
import Language.Haskell.TH.Syntax (mkName, lift)
--import SafeCopy
import Test.HUnit hiding (Path)
import TestTypes

main :: IO ()
main = do
  counts <- runTestTT tests
  case counts of
    Counts {errors = 0, failures = 0} -> pure ()
    _ -> error (showCounts counts)

tests :: Test
tests =
    TestList
    [ TestCase (assertEqual "maxBound :: Int" "9223372036854775807" (show (maxBound :: Int)))
    , TestCase (assertEqual "phantom Proxy"
                  "Phantom {_phantom = fromList [t], _used = fromList []}"
                  $(phantom [t|Proxy|] >>= lift . show . friendlyNames))
    , TestCase (assertEqual "phantom Maybe"
                  "Phantom {_phantom = fromList [], _used = fromList [a]}"
                  $(phantom [t|Maybe|] >>= lift . show . friendlyNames))
    , TestCase (assertEqual "phantom Either"
                  "Phantom {_phantom = fromList [], _used = fromList [a,b]}"
                  $(phantom [t|Either|] >>= lift . show . friendlyNames))
    , TestCase (assertEqual "phantom TypeSPath"
                  "Phantom {_phantom = fromList [s1,t1], _used = fromList []}"
                  $(phantom [t|TypeSPath|] >>= lift . show . friendlyNames))
    -- Most tests moved to th-unify-clients
    ]
