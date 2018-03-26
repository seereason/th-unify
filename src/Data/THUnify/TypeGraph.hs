{-# LANGUAGE CPP, ConstraintKinds #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# OPTIONS -Wall #-}

module Data.THUnify.TypeGraph
    ( TypeGraph(..)
    , typeGraphFmap
    , graph
    , keys
    , readTypeGraph
    , typeRepGraph
    ) where

import Control.Lens (makeLenses, view)
import Data.Bifunctor
import Data.Function (on)
import Data.Generics (TypeRep)
import qualified Data.Graph.Inductive as G
import Data.List (sortBy)
import Data.Map as Map (Map, singleton, toAscList, unionsWith)
import Data.THUnify.Graph (labNodes, labEdges, mkGraph)
import Data.THUnify.Hop (Hop(..))
import Data.THUnify.Orphans ()
import Data.THUnify.Prelude (pprint1')
import Data.Set as Set (fromList, Set, singleton, toAscList, union)
import Language.Haskell.TH (Ppr(ppr), pprint, Q, Type, TypeQ, ExpQ, listE)
import Language.Haskell.TH.Lift (deriveLift, lift)
import Language.Haskell.TH.PprLib (ptext, vcat)

-- | Represents a graph whose nodes are concrete data types, and whose
-- edges represent membership.  E.g. there would be an edge from
-- [Char] to Char (but not to []), or from Map Int String to String
-- (but not to Int, because the Int is part of the path.)
data TypeGraph typ
    = TypeGraph
      { _keys :: [typ]
      -- ^ Types that appear as Index keys.  This is a list rather
      -- than a Set for better control of the rendered expression.
      , _graph :: G.Gr typ (Hop typ) -- ^ The type graph
      }

instance (Ord typ, Show typ) => Show (TypeGraph typ) where
  show (TypeGraph ks gr) =
    "TypeGraph {_keys = " ++ show ks ++ ", _graph = Data.Path.Graph.mkGraph (" ++ show (labNodes gr) ++ ") (" ++ show (labEdges gr) ++ ")}"

typeGraphFmap :: (Ord a, Ord b) => (a -> b) -> TypeGraph a -> TypeGraph b
typeGraphFmap f (TypeGraph ks gr) = TypeGraph (fmap f ks) (bimap f (fmap f) gr)

$(makeLenses ''TypeGraph)

instance Ord (TypeGraph Type) where
    compare a b =
        case compare (_keys a) (_keys b) of
          EQ -> compareGraphs (_graph a) (_graph b)
          x -> x
        where
          compareGraphs a' b' =
              case compare (Set.fromList (labNodes a')) (Set.fromList (labNodes b')) of
                EQ -> compare (Set.fromList (labEdges a')) (Set.fromList (labEdges b'))
                x -> x

instance Eq (TypeGraph Type) where
    a == b = compare a b == EQ

readTypeGraph :: [TypeQ] -> [(TypeQ, TypeQ, Hop TypeQ)] -> [TypeQ] -> Q (TypeGraph Type)
readTypeGraph nodes edges keyTypes =
    TypeGraph <$> (sortBy (compare `on` pprint) <$> sequence keyTypes)
              <*> (readGraph nodes edges)

readGraph :: [TypeQ] -> [(TypeQ, TypeQ, Hop TypeQ)] -> Q (G.Gr Type (Hop Type))
readGraph nodes edges =
    mkGraph <$> sequence nodes
            <*> (mapM (\(n1,n2,e) -> ((,,) <$> n1 <*> n2 <*> e' e)) edges)
    where
      e' :: Hop TypeQ -> Q (Hop Type)
      e' (IxHop key) = IxHop <$> key
      e' (AtHop key) = AtHop <$> key
      -- No other constructors contain key values
      e' x = pure (fmap (undefined :: TypeQ -> Type) x)

-- | At runtime we need to characterize types and values by their
-- TypeRep value, this transforms a @TypeGraph Type@ into a @TypeGraph
-- TypeRep@.
typeRepGraph :: (Type -> ExpQ) -> TypeGraph Type -> ExpQ
typeRepGraph rep tg =
  [|TypeGraph $ks (mkGraph $ns $es)|]
    where
      ks :: ExpQ
      ks = listE (fmap rep (_keys tg))
      ns :: ExpQ
      ns = listE (fmap rep (labNodes (_graph tg)))
      es :: ExpQ
      es = listE (fmap (\(n1, n2, h) -> [|($(rep n1), $(rep n2), $(hop h))|]) (labEdges (_graph tg)))
      -- Turn the hop type parameter into a TypeRep
      hop :: Hop Type -> ExpQ
      hop (IxHop i) = [|IxHop $(rep i)|]
      hop (AtHop i) = [|AtHop $(rep i)|]
      hop (FieldHop c f) = [|FieldHop $(lift c) $(lift f)|]
      hop ViewHop = [|ViewHop|]

instance Ppr (TypeGraph Type) where
    ppr tg = vcat (fmap ppr1 (Map.toAscList mp))
        where
          gr = (view graph tg :: G.Gr Type (Hop Type))
          mp :: Map Type (Set ((Hop Type), Type))
          mp = Map.unionsWith Set.union (fmap (\(n1,n2,e) ->
                                                   let Just t1 = (G.lab gr n1)
                                                       Just t2 = (G.lab gr n2) in
                                                   Map.singleton t1 (Set.singleton (e, t2))) (G.labEdges gr))
          ppr1 (s, es) = vcat (ptext (pprint1' s) : fmap ppr2 (Set.toAscList es))
          ppr2 (hk, a) = ptext (" -> (" ++ pprint hk {-"hopExprString pprint1' hk"-} ++ ", " ++ pprint1' a ++ ")")

instance Ppr (TypeGraph TypeRep) where
    ppr tg = vcat (fmap ppr1 (Map.toAscList mp))
        where
          gr = (view graph tg :: G.Gr TypeRep (Hop TypeRep))
          mp :: Map TypeRep (Set ((Hop TypeRep), TypeRep))
          mp = Map.unionsWith Set.union (fmap (\(n1,n2,e) ->
                                                   let Just t1 = (G.lab gr n1)
                                                       Just t2 = (G.lab gr n2) in
                                                   Map.singleton t1 (Set.singleton (e, t2))) (G.labEdges gr))
          ppr1 (s, es) = vcat (ptext (pprint1' s) : fmap ppr2 (Set.toAscList es))
          ppr2 (hk, a) = ptext (" -> (" ++ pprint hk {-"hopExprString pprint1' hk"-} ++ ", " ++ pprint1' a ++ ")")

$(deriveLift ''TypeGraph)
