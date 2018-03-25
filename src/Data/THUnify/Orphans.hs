{-# LANGUAGE CPP #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE PackageImports #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# OPTIONS -fno-warn-unused-imports -fno-warn-orphans #-}

module Data.THUnify.Orphans where

import Control.Lens (Index, IxValue)
import Data.Bifunctor (Bifunctor(bimap))
import Data.ByteString (ByteString)
import Data.Function.Memoize (deriveMemoizable)
import Data.Generics (Data, TyCon, TypeRep, tyConFingerprint, tyConModule, tyConName, tyConPackage, splitTyConApp)
import Data.Int (Int32)
import Data.List (intercalate)
import Data.ListLike as LL
import Data.Map as Map (Map, mapKeys, toList)
import Data.Order (fromMapVecKey, fromPairs, nextKey, Order, {-Order_0(..),-} OrderError(..), toKeys, toMap, toPairs)
import Data.OrderedMap (OrderedMap)
import Data.Proxy (Proxy(Proxy))
-- import Data.SafeCopy.Derive (deriveSafeCopy)
import Data.SafeCopy (base)
import Data.Serialize (Serialize(get, put))
import Data.Text (pack, unpack)
import Data.UserId (UserId)
import Data.Vector as Vector (fromList)
import Debug.Show (V(V))
import GHC.Fingerprint.Type (Fingerprint)
import Language.Haskell.TH
import Language.Haskell.TH.Lift (deriveLift, lift)
import Language.Haskell.TH.PprLib (Doc, hcat, ptext, vcat)
import Language.Haskell.TH.Syntax (ModName, NameFlavour, OccName, PkgName)
import Prelude hiding (concat, foldl1)
import System.Process (CmdSpec(..))
import Test.QuickCheck (Arbitrary(arbitrary), Gen, sized, vectorOf, shuffle)
import Text.Parsec (count, many)
--
import Web.Routes
--import Language.Haskell.TH.TypeGraph.WebRoutesTH (derivePathInfo)

-- The type parameter in Proxy t does not itself need to be an
-- instance of PathInfo, because there is no actual t value in the
-- Proxy value.  The derivePathInfo function does not realize this.
-- $(derivePathInfo ''Proxy)
instance {-PathInfo t =>-} PathInfo (Proxy t) where
    toPathSegments inp = case inp of Proxy -> [pack "proxy"]
    fromPathSegments = segment (pack "proxy") >> return Proxy

instance PathInfo ByteString where
    toPathSegments bs = [pack $ show bs]
    fromPathSegments = (read . unpack) <$> anySegment

#if 0
$(derivePathInfo ''Loc)
#else
instance PathInfo Loc where
    toPathSegments _ = []
    fromPathSegments = pure noLoc
        where
          noLoc = Loc "" "" "" (0, 0) (0, 0)
#endif
instance PathInfo (Int, Int) where
    toPathSegments (a, b) = toPathSegments [a, b]
    fromPathSegments = (\[a, b] -> (a, b)) <$> count 2 fromPathSegments
instance PathInfo [Loc] where
    toPathSegments = concat . fmap toPathSegments
    fromPathSegments = many fromPathSegments
instance PathInfo [Int] where
    toPathSegments = concat . fmap toPathSegments
    fromPathSegments = many fromPathSegments

#if 0
$(deriveLift ''G.Gr)
$(deriveLift ''G.NodeMap)
#endif

$(deriveMemoizable ''Type)
$(deriveMemoizable ''TyVarBndr)
$(deriveMemoizable ''Name)
$(deriveMemoizable ''NameFlavour)
$(deriveMemoizable ''TyLit)
$(deriveMemoizable ''OccName)
$(deriveMemoizable ''NameSpace)
$(deriveMemoizable ''PkgName)
$(deriveMemoizable ''ModName)

instance Ppr (Type, Int32) where
  ppr (t, n) = pprPair (t, n)

instance Ppr Int32 where ppr = ptext . show

instance Ppr (Name, [Type]) where
    ppr (name, params) = ppr (foldl1 AppT (ConT name : params))

pprPair :: (Ppr a, Ppr b) => (a, b) -> Doc
pprPair (a, b) = hcat [ptext "(", ppr a, ptext ",", ppr b, ptext ")"]

pprList :: [Doc] -> Doc
pprList xs = hcat [ptext "[", hcat (intersperse (ptext ",") xs), ptext "]"]

deriving instance Data CmdSpec

#if 0
instance Arbitrary ReportImageID where arbitrary = ReportImageID <$> arbitrary
instance Arbitrary ReportElemID where arbitrary = ReportElemID <$> arbitrary
instance (Arbitrary v, Enum k, Ord k) => Arbitrary (Order k v) where
    arbitrary = sized $ \n -> do
      vs <- vectorOf n (arbitrary :: Gen v)
      ks <- shuffle (take n [toEnum 0..] :: [k])
      fromPairs <$> shuffle (zip ks vs)
#endif

instance Ppr Char where ppr = ptext . show
instance Ppr Float where ppr = ptext . show
-- instance Ppr ReportElemID where ppr = ptext . show
-- instance Ppr ReportImageID where ppr = ptext . show
instance (Ppr k, Ord k, {-Enum k,-} Show k, Ppr v) => Ppr (Map k v) where ppr = pprList . fmap pprPair . Map.toList
instance (Ppr k, Ord k, Enum k, Show k, Ppr v) => Ppr (Order k v) where ppr = pprList . fmap pprPair . LL.toList . toPairs
instance Ppr (Int, Char) where ppr = ptext . show
instance Ppr ByteString where ppr = ptext . show
instance Arbitrary ByteString where arbitrary = pure mempty

instance Ppr Bool where
    ppr True = ptext "True"
    ppr False = ptext "False"

instance Show (V TyCon) where
    show (V c) =
        "TyCon {" ++
        "module=" ++ show (tyConModule c) ++
        " name=" ++ show (tyConName c) ++
        " package=" ++ show (tyConPackage c) ++
        " fingerprint=" ++ show (tyConFingerprint c) ++ "}"

instance Show (V TypeRep) where
    show (V r) =
        case splitTyConApp r of
          (c, rs) -> "[" ++ intercalate "," (show (V c) : fmap (show . V) rs) ++ "]"

instance Ppr TypeRep where
  ppr = ptext . show
