{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# OPTIONS -Wall #-}

module Data.THUnify.Prelude.Ppr
    ( pprint1, pprint1', pprintW, pprintW'
    ) where

import Data.Generics (Data, everywhere, mkT)
import Instances.TH.Lift ()
import Language.Haskell.TH hiding (prim)
import Language.Haskell.TH.PprLib (to_HPJ_Doc)
import Language.Haskell.TH.Syntax as TH (Name(Name), NameFlavour(NameS))
import qualified Text.PrettyPrint as HPJ

-- | Pretty print a 'Ppr' value on a single line with each block of
-- white space (newlines, tabs, etc.) converted to a single space, and
-- all the module qualifiers removed from the names.  (If the data type
-- has no 'Name' values the friendlyNames function has no effect.)
pprint1 :: (Ppr a, Data a) => a -> [Char]
pprint1 = pprint1' . friendlyNames

pprint1' :: Ppr a => a -> [Char]
pprint1' = pprintStyle (HPJ.style {HPJ.mode = HPJ.OneLineMode})

-- | Pretty print with friendly names and wide lines
pprintW :: (Ppr a, Data a) => Int -> a -> [Char]
pprintW w = pprintW' w . friendlyNames

pprintW' :: Ppr a => Int -> a -> [Char]
pprintW' w = pprintStyle (HPJ.style {HPJ.lineLength = w})

-- | Helper function for pprint1 et. al.
pprintStyle :: Ppr a => HPJ.Style -> a -> String
pprintStyle style = HPJ.renderStyle style . to_HPJ_Doc . ppr

-- | Make a template haskell value more human reader friendly.  The
-- result almost certainly won't be compilable.  That's ok, though,
-- because the input is usually uncompilable - it imports hidden modules,
-- uses infix operators in invalid positions, puts module qualifiers in
-- places where they are not allowed, and maybe other things.
friendlyNames :: Data a => a -> a
friendlyNames =
    everywhere (mkT friendlyName)
    where
      friendlyName (Name x _) = Name x NameS -- Remove all module qualifiers
