{-# LANGUAGE CPP, FlexibleContexts, RankNTypes, ScopedTypeVariables, TemplateHaskell, TypeFamilies #-}
{-# OPTIONS -Wall #-}

module Data.THUnify.TypeGraph.Paths
    ( PathsInfo(..)
    , makePaths
    ) where

import Control.Lens (_3, view)
import Control.Monad.Except (MonadError, throwError)
import Control.Monad.Writer (execWriterT, tell, WriterT)
import Data.Bool (bool)
import Data.Function (on)
import Data.Generics (Data, extQ, mkQ, Proxy(Proxy), typeOf, TypeRep, typeRep)
import qualified Data.Graph.Inductive as G
import Data.List (nub, sortBy)
import Data.Map as Map (fromList, keys, lookup, Map)
import Data.Maybe (fromJust, mapMaybe)
import Data.Order (Order)
import Data.THUnify.Graph (labEdges, labNodes, mkGraph)
import Data.THUnify.Hop (Hop(..), hopKey)
import Data.THUnify.Paths (IsPathError(fromPathError), PathError(..), showTypeRep, Paths(..), Value(..))
import Data.THUnify.Preface (pprint1)
import Data.THUnify.TypeGraph (graph, TypeGraph(..))
import Data.THUnify.TypeGraph.Edges (collectTypeInfo)
import Data.THUnify.TypeGraph.Nodes (TypeGraphNodes(_nodes))
import Data.THUnify.Unify (decomposeType, E(..))
import Data.THUnify.View (viewMap)
import Data.Set as Set (fromList, member, Set, toList)
import Data.Tuple (swap)
import Language.Haskell.TH (Dec(..), ExpQ, Q, runQ, Type(..), TypeQ)
import Language.Haskell.TH.Syntax (Lift(lift))

data PathsInfo
    = PathsInfo
      { _pathsDecs :: [Dec]
      , _pathsInst :: Type
      , _typeInfo :: TypeGraphNodes
      } deriving Show

instance Lift PathsInfo where
    lift (PathsInfo d i t) = [|PathsInfo $(lift d) $(lift i) $(lift t)|]

data S
    = S
      { _typegraph :: TypeGraph Type -- ^ Types that appear as index keys
      , _nodemap :: G.NodeMap Type
      , _visited :: Set (E Type)
      } deriving (Show)

#if 0
type EdgeT = RWST R [(Type, Type, Hop Type)] (Set Type)
#endif

makeQuery :: ExpQ -> [ExpQ] -> ExpQ
makeQuery q0 [] = [|const $q0|]
makeQuery q0 (q1 : qs) = foldl (\a b -> [|$a `extQ` $b|]) [|mkQ $q0 $q1|] qs

-- | Create a paths instance.  Also, create the type graph.  Obviously,
-- the Paths instance isn't available yet, so we need to do this using
-- the 'Type' values we are using to create that declaration.
makePaths ::
       Int
    -> TypeQ
    -> TypeGraphNodes
    -> Q PathsInfo
makePaths v0 paths nodes = do
  ({-primNodes, algNodes, ixNodes, atNodes, orderNodes,-} tg) <- collectTypeInfo v0 nodes
  let -- viewTypes = nub $ fmap (view _1) $ Prelude.filter (\e -> view _3 e == ViewHop) $ labEdges $ view graph tg
      g = view graph tg
  views <- viewMap
  let (nodeMap :: Map TypeRep (E Type)) = Map.fromList (fmap swap (_nodes nodes))
  let (keySet :: Set (E Type)) = Set.fromList (mapMaybe (\e -> maybe Nothing (\k -> Map.lookup k nodeMap) (hopKey (view _3 e))) (labEdges g))

  decs <- execWriterT $ do
    makeValueInstances nodeMap keySet views (view graph tg)
    runQ [d|instance Paths $paths where
              goValue _ = go
                where go :: forall s e m r. (Data s, IsPathError e, MonadError e m) => (forall v. Value v => v -> m r) -> s -> m r
                      go f s = $(makeQuery' [|f|] [t|m r|] [|throwError (fromPathError (BadValue (showTypeRep (Proxy :: Proxy s))) :: e) :: m r|] (sortBy (compare `on` (show . snd)) (_nodes nodes))) s
              hopRepGraph _ = TypeGraph {_keys = $(lift (_keys tg)),
                                         _graph = Data.THUnify.Graph.mkGraph
                                                    $(lift (sortBy (compare `on` show) (Data.THUnify.Graph.labNodes g)))
                                                    $(lift (sortBy compareHops (Data.THUnify.Graph.labEdges g)))} |] >>= tell
  paths' <- paths
  return $ PathsInfo {_pathsDecs = decs, _pathsInst = paths', _typeInfo = nodes}
      where
        compareHops :: (TypeRep, TypeRep, Hop TypeRep) -> (TypeRep, TypeRep, Hop TypeRep) -> Ordering
        compareHops (s1, e1, h1) (s2, e2, h2) =
            compare (show s1, fmap show h1, show e1) (show s2, fmap show h2, show e2)

-- | Build a generic query that takes a value in class Data and if possible applies it to
-- a function that takes an instance of Value.
makeQuery' :: ExpQ -> TypeQ -> ExpQ -> [(E Type, TypeRep)] -> ExpQ
makeQuery' fn result dflt types = makeQuery dflt (fmap (\t -> [|$fn :: $t -> $result|]) (fmap (pure . unE . fst) types))

trying :: [(a -> Bool, a -> r)] -> (a -> r) -> a -> r
trying ((p, f) : pairs) d x = bool (trying pairs d x) (f x) (p x)
trying [] d x = d x

makeValueInstances  :: Map TypeRep (E Type) -> Set (E Type) -> Map (E Type) (E Type) -> G.Gr TypeRep (Hop TypeRep) -> WriterT [Dec] Q ()
makeValueInstances nodeMap keySet views g = do
  mapM_ (trying
          [(isOrder, \t -> runQ (makeOrder keySet views t) >>= tell),
           (isAt, \t -> runQ (makeAt keySet views t) >>= tell),
           (isIx, \t -> runQ (makeIxed keySet views t) >>= tell),
           (isAlg, \t -> runQ (makeAlgebraic keySet views t) >>= tell)]
          (\t -> runQ (makePrimitive keySet views t) >>= tell))
        (sortBy (compare `on` (pprint1 . unE)) (nub (nodes ++ Set.toList keySet)))
  where
    nodes :: [E Type]
    nodes = fmap f (Map.keys nodeMap)
    edges :: [(E Type, E Type, Hop (E Type))]
    edges = fmap (\(s, a, h) -> (f s, f a, fmap f h)) (labEdges g)
    isOrder :: E Type -> Bool
    isOrder = isOrderType
    isAt :: E Type -> Bool
    isAt typ = any (isAtEdge typ) edges
    isIx :: E Type -> Bool
    isIx typ = any (isIxEdge typ) edges
    isAlg :: E Type -> Bool
    isAlg typ = any (isFieldEdge typ) edges

    isAtEdge :: E Type -> (E Type, E Type, Hop (E Type)) -> Bool
    isAtEdge typ (s, _, AtHop _) = typ == s
    isAtEdge _ _ = False
    isIxEdge typ (s, _, IxHop _) = typ == s
    isIxEdge _ _ = False
    isFieldEdge typ (s, _, FieldHop _ _) = typ == s
    isFieldEdge _ _ = False
    f :: TypeRep -> E Type
    f = fromJust . (`Map.lookup` nodeMap)

isOrderType :: E Type -> Bool
isOrderType typ =
    case decomposeType (unE typ) of
      (ConT order : _) | order == ''Order -> True
      _ -> False

makePrimitive :: Set (E Type) -> Map (E Type) (E Type) -> E Type -> Q [Dec]
makePrimitive ks v s' =
    let s = pure (unE s') in
    [d|instance Value $s where
          goAlg _ _ = throwError (fromPathError (BadValue (show (typeRep (Proxy :: Proxy $s)))))
          goView _go x = $(makeView (Map.lookup s' v) [|x|] [|_go|])
          goKey _go k = $(makeKey (Set.member s' ks) [|k|] [|_go|])
          goIx _ _ = throwError (fromPathError (BadIxed (show (typeRep (Proxy :: Proxy $s)))))
          goAt _ _ = throwError (fromPathError (BadAt (show (typeRep (Proxy :: Proxy $s)))))
          goOrder _ _ = throwError (fromPathError (BadOrder (show (typeRep (Proxy :: Proxy $s)))))|]

makeAlgebraic :: Set (E Type) -> Map (E Type) (E Type) -> E Type -> Q [Dec]
makeAlgebraic ks v s' =
    let s = pure (unE s') in
    [d|instance Value $s where
          goAlg go x = go x
          goView _go x = $(makeView (Map.lookup s' v) [|x|] [|_go|])
          goKey _go x = $(makeKey (Set.member s' ks) [|x|] [|_go|])
          goIx _ _ = throwError (fromPathError (BadIxed (show (typeRep (Proxy :: Proxy $s)))))
          goAt _ _ = throwError (fromPathError (BadAt (show (typeRep (Proxy :: Proxy $s)))))
          goOrder _ _ = throwError (fromPathError (BadOrder (show (typeRep (Proxy :: Proxy $s)))))|]

makeIxed :: Set (E Type) -> Map (E Type) (E Type) -> E Type -> Q [Dec]
makeIxed ks v s' =
    let s = pure (unE s') in
    [d|instance Value $s where
          goAlg _ _ = throwError (fromPathError (BadValue (show (typeRep (Proxy :: Proxy $s)))))
          goView _go x = $(makeView (Map.lookup s' v) [|x|] [|_go|])
          goKey _go x = $(makeKey (Set.member s' ks) [|x|] [|_go|])
          goIx go x = go x
          goAt _ _ = throwError (fromPathError (BadAt (show (typeRep (Proxy :: Proxy $s)))))
          goOrder _ _ = throwError (fromPathError (BadOrder (show (typeRep (Proxy :: Proxy $s)))))|]

makeAt :: Set (E Type) -> Map (E Type) (E Type) -> (E Type) -> Q [Dec]
makeAt ks v s' =
    let s = pure (unE s') in
    [d|instance Value $s where
          goAlg _ _ = throwError (fromPathError (BadValue (show (typeRep (Proxy :: Proxy $s)))))
          goView _go x = $(makeView (Map.lookup s' v) [|x|] [|_go|])
          goKey _go x = $(makeKey (Set.member s' ks) [|x|] [|_go|])
          goIx go x = go x
          goAt go x = go x
          goOrder _ _ = throwError (fromPathError (BadOrder (show (typeRep (Proxy :: Proxy $s)))))|]

makeOrder :: Set (E Type) -> Map (E Type) (E Type) -> E Type -> Q [Dec]
makeOrder ks v s' =
    let s = pure (unE s') in
    [d|instance Value $s where
          goAlg _ _ = throwError (fromPathError (BadValue (show (typeRep (Proxy :: Proxy $s)))))
          goView _go x = $(makeView (Map.lookup s' v) [|x|] [|_go|])
          goKey _go x = $(makeKey (Set.member s' ks) [|x|] [|_go|])
          goIx go x = go x
          goAt _ _ = throwError (fromPathError (BadAt (show (typeRep (Proxy :: Proxy $s)))))
          goOrder go x = go x|]

makeView :: Maybe (E Type) -> ExpQ -> ExpQ -> ExpQ
makeView Nothing x _go = [|throwError (fromPathError (BadView (show (typeOf $x))))|]
makeView (Just (E _v)) x go = [|$go $x|]

makeKey :: Bool -> ExpQ -> ExpQ -> ExpQ
makeKey False x _go = [|throwError (fromPathError (BadKey (show (typeOf $x))))|]
makeKey True x go = [|$go $x|]
