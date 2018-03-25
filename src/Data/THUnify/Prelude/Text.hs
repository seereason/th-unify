{-# LANGUAGE RankNTypes #-}

module Data.THUnify.Prelude.Text
    ( diffText
    , camelWords
    , tests
    , capitalize
    , readShowIso
    , Describe(describe')
    , describe
    , trunc
    ) where

import Control.Lens (Iso', iso)
import Data.Algorithm.DiffContext (getContextDiff, prettyContextDiff)
import Data.Char (isUpper, toUpper)
import Data.ListLike (groupBy)
import Data.Text (split, Text, unpack)
import Test.HUnit (assertEqual, Test(TestCase, TestList))
import qualified Text.PrettyPrint as HPJ
import Text.Read (readMaybe)

-- | Output the difference between two string in the style of diff(1).  This
-- can be used with Test.HUnit.assertString:  assertString (diffText ("a", "1\n2\n3\n"), ("b", "1\n3\n"))
diffText :: (String, Text) -> (String, Text) -> String
diffText (nameA, textA) (nameB, textB) =
    show (prettyContextDiff
          (HPJ.text nameA)
          (HPJ.text nameB)
          (HPJ.text . unpack)
          (getContextDiff 2 (split (== '\n') textA) (split (== '\n') textB)))

-- | Convert a camel case string (no whitespace) into a natural
-- language looking phrase:
--   camelWords "aCamelCaseFOObar123" -> "A Camel Case FOObar123"
camelWords :: String -> String
camelWords s =
    case groupBy (\ a b -> isUpper a == isUpper b) (dropWhile (== '_') s) of -- "aCamelCaseFOObar123"
      (x : xs) -> concat $ capitalize x : map (\ (c : cs) -> if isUpper c then ' ' : c : cs else c : cs) xs
      [] -> ""

-- Most of these fail.
tests :: Test
tests =
    TestList
    [ TestCase (assertEqual "camel words 0" "A Camel Case FOO Bar 123" (camelWords "aCamelCaseFOOBar123"))
    , TestCase (assertEqual "camel words 1" "My Generator" (camelWords "myGenerator"))
    , TestCase (assertEqual "camel words 2" "PDF Generator" (camelWords "pDFGenerator"))
    , TestCase (assertEqual "camel words 3" "PDF Generator" (camelWords "PDFGenerator"))
    , TestCase (assertEqual "camel words 4" "Report PDF Generator" (camelWords "reportPDFGenerator")) ]

capitalize :: String -> String
capitalize [] = []
capitalize (c:cs) = (toUpper c) : cs

readShowIso :: (Show a, Read a) => a -> Iso' a String
readShowIso d = iso show (\v ->
                              case readMaybe v of
                                Nothing -> d
                                Just r' -> r')

-- | Override the default description associated with the type of @a@.
-- The first argument indicates the field of the parent record that
-- contains the @a@ value, if any.
class Describe a where
    describe' :: Maybe String -> a -> Maybe String

describe :: Describe a => a -> Maybe String
describe = describe' Nothing

-- | Truncate a string to avoid writing monster lines into the log.
trunc :: String -> String
trunc s = if length s > 1000 then take 1000 s ++ "..." else s
