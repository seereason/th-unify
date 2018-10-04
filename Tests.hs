{-# LANGUAGE LambdaCase, RankNTypes, ScopedTypeVariables, TemplateHaskell #-}

import Data.Set as Set (fromList)
import Data.THUnify.Prelude.Ppr (friendlyNames)
import Data.THUnify.Phantom (nonPhantom, phantom)
import Language.Haskell.TH.Syntax (mkName, lift)
import Test.HUnit
import TestData

main :: IO ()
main =
  f <$> runTestTT tests
  where
    f :: Counts -> ()
    f = \case
          Counts {errors = 0, failures = 0} -> ()
          x -> error (showCounts x)

tests :: Test
tests =
    TestList
    [ TestCase (assertEqual "maxBound :: Int" "9223372036854775807" (show (maxBound :: Int)))
    , TestCase (assertEqual "phantom 1"
                  (fromList [mkName "t"])
                  (friendlyNames $([t|forall t s. EventTree t s|] >>= phantom >>= lift)))
    , TestCase (assertEqual "phantom 2"
                  (fromList [mkName "s"])
                  (friendlyNames $([t|forall t s. EventTree t s|] >>= nonPhantom >>= lift)))
    ]
