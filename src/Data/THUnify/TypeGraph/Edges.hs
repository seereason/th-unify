{-# LANGUAGE CPP, RankNTypes, ScopedTypeVariables, TemplateHaskell, TypeFamilies #-}
{-# OPTIONS -Wall #-}

module Data.THUnify.TypeGraph.Edges
    ( collectTypeInfo
    , makeHopGraph
    ) where

import Control.Lens ((.=), (%=), _1, _2, At, Index, Ixed, IxValue, makeLenses, over, use, zoom)
import Control.Lens ()
import Control.Monad (when)
import Control.Monad.RWS (execRWST, RWST, local)
import Control.Monad.State (evalState)
import Data.Function (on)
import Data.Generics (constrs, Data, dataTypeOf, gmapQ, gmapQi, isAlgType, Proxy, typeOf, TypeRep)
import qualified Data.Graph.Inductive as G
import Data.List as List (sortBy)
import Data.Map as Map (fromList, Map, lookup, toList)
import Data.Maybe (fromJust, fromMaybe, mapMaybe)
import Data.Monoid ((<>))
import Data.Order (Order)
import Data.THUnify.Graph (insNode, insEdge, mkNode, reachable)
import Data.THUnify.Hop (Hop(..))
import Data.THUnify.Preface (decomposeType, message, partitionsM, prefix', pprint1, R(..), setPartitionM, unsnoc)
import Data.THUnify.TypeGraph (graph, keys, TypeGraph(..))
import Data.THUnify.TypeGraph.Nodes (TypeGraphNodes(..))
import Data.THUnify.Unify (applyTypeFunction, Dispatcher, E(..), typesFromClassName, typesFromFamilyName, unifies, unify')
import Data.THUnify.View (viewMap)
import Data.SafeCopy (MigrateFrom)
import Data.Set as Set (empty, fromList, insert, map, member, notMember, Set, toList, unions)
import Language.Haskell.TH

data S typ
    = S
      { _typegraph :: TypeGraph typ -- ^ Types that appear as index keys
      , _nodemap :: G.NodeMap typ
      , _visited :: Set typ
      , _starts :: Set typ
      } deriving (Show)

$(makeLenses ''S)

type PathT typ = RWST R () (S typ)

-- | Collect the information required by 'makePaths' to build a
-- 'Paths' instance.
collectTypeInfo ::
       Int
    -> TypeGraphNodes
    -> Q ({-Set (E Type, TypeRep),
          Set (E Type, TypeRep),
          Set (E Type, TypeRep),
          Set (E Type, TypeRep),
          Set (E Type, TypeRep),-}
          TypeGraph TypeRep)
collectTypeInfo v0 nodes = do
  let nodeMap' :: (Type -> String) -> E Type -> TypeRep
      nodeMap' msg t = fromMaybe (error (msg (unE t))) (nodeMap t)
      nodeMap :: E Type -> Maybe TypeRep
      nodeMap t = Map.lookup t (Map.fromList (_nodes nodes))

  -- Get the view edges and the primitive types from the environment
  views <- viewMap
  migrations <- runQ $ typesFromFamilyName ''MigrateFrom
  let (views' :: Map TypeRep TypeRep) =
          (Map.fromList . mapMaybe bothJust . fmap (over _1 nodeMap . over _2 nodeMap) . Map.toList) views
      (migrations' :: Map TypeRep TypeRep) =
          (Map.fromList . mapMaybe bothJust . fmap (over _1 nodeMap . over _2 nodeMap) . Map.toList) migrations
      bothJust (Just a, Just b) = Just (a, b)
      bothJust _ = Nothing

  -- Get all the instances of Value, Ixed, and At
  (ixedInsts :: Set (E Type)) <- typesFromClassName ''Ixed
  (atInsts :: Set (E Type)) <- typesFromClassName ''At -- presumably a subset of ixedInsts

  -- Which nodes already have Value instances?
  -- (valueInsts :: Set (E Type)) <- typesFromClassName ''Value
  -- let nodes2 :: [(E Type, TypeRep)]
  --     nodes2 = Prelude.filter (\(t, _) -> Set.notMember t valueInsts) (_nodes nodes)

  -- Which of those are not in the primitive list?
  [primNodes, tupleNodes, orderNodes, atNodes, ixNodes, algNodes] <-
    fmap Set.fromList <$>
      partitionsM [(unifies (_primitives nodes) . fst),
                   (return . isTupleType . fst),
                   (return . isOrderType . fst),
                   (unifies atInsts . fst),
                   (unifies ixedInsts . fst)] (_nodes nodes)
{-
  (primNodes, nodes2) <- setPartitionM (unifies (_primitives nodes) . fst) (Set.fromList (_nodes nodes))
  -- There is an Ixed instance for tuples, but we treat them as
  -- algebraic types because the field types typically differ.
  let (tupleNodes, nodes3) = Set.partition (isTupleType . fst) nodes2
  -- Order nodes are ixNodes (atNodes?), but we give them special treatment for now
  let (orderNodes, nodes4) = Set.partition (isOrderType . fst) nodes3
  (atNodes, nodes5) <- setPartitionM (unifies atInsts . fst) nodes4
  (ixNodes, algNodes) <- setPartitionM (unifies ixedInsts . fst) nodes5
-}

  -- Partition out the Ixed nodes we can create hops for.  Due to the
  -- constraint 'TraversableWithIndex' in 'IxedValue', We need to
  -- filter any types that are not functors out of ixedNodes.  That
  -- means that the last element of the decomposed type must be the
  -- IxValue of that type.
  (atNodes', algNodes2) <- setPartitionM (isIxedValue . fst) atNodes
  (ixNodes', algNodes3) <- setPartitionM (isIxedValue . fst) ixNodes


  let ixedNodes :: Set (E Type, TypeRep)
      ixedNodes = ixNodes' <> atNodes' <> orderNodes
      ixedNodes' :: [(E Type, TypeRep)]
      ixedNodes' = sortBy (compare `on` (show . snd)) (Set.toList ixedNodes)

  -- Apply the IxValue and Index type functions to the Ixed instances
  (ixValueNodes :: [E Type]) <- fmap fromJust <$> mapM (applyTypeFunction ''IxValue) (fmap fst ixedNodes')
  (indexNodes :: [E Type]) <- fmap fromJust <$> mapM (applyTypeFunction ''Index) (fmap fst ixedNodes')

  -- Build maps representing the interesting portions of the IxValue and Index type functions
  let ixValueMap :: Map TypeRep TypeRep
      ixValueMap = Map.fromList (zip (fmap snd ixedNodes') (fmap (nodeMap' (\t -> error $ "Unexpected IxValue type: " <> pprint t)) ixValueNodes))
      indexMap :: Map TypeRep TypeRep
      indexMap = Map.fromList (zip (fmap snd ixedNodes') (fmap (nodeMap' (\t -> error $ "Unexpected Index type: " <> pprint t)) indexNodes))

  (g :: TypeGraph TypeRep) <-
      makeHopGraph v0 (_typeMap nodes) ixValueMap indexMap (fmap snd (_roots nodes)) views' migrations'
        (Set.map snd primNodes)
        (Set.map snd (algNodes <> tupleNodes <> algNodes2 <> algNodes3))
        (Set.map snd ixNodes')
        (Set.map snd atNodes')
        (Set.map snd orderNodes)

{-
  assertEqual (Set.map snd primNodes) (findPrimNodes g)
  assertEqual (Set.map snd (algNodes <> tupleNodes <> algNodes2 <> algNodes3)) (findAlgNodes g)
  assertEqual (Set.map snd ixNodes') (findIxNodes g)
  assertEqual (Set.map snd atNodes') (findAtNodes g)
  assertEqual (Set.map snd orderNodes) (findOrderNodes g)
-}

  return ({-primNodes, algNodes <> tupleNodes <> algNodes2 <> algNodes3, ixNodes', atNodes', orderNodes,-} g)

isOrderType :: E Type -> Bool
isOrderType typ =
    case decomposeType (unE typ) of
      (ConT order : _) | order == ''Order -> True
      _ -> False

isTupleType :: E Type -> Bool
isTupleType (E t) =
    case decomposeType t of
      (TupleT _ : _) -> True
      _ -> False

#if 0
assertEqual :: (Eq a, Monad m) => a -> a -> m ()
assertEqual a b | a == b = return ()
assertEqual _ _ = error $ "assertEqual failed"

-- | Nodes with no out edges
findPrimNodes :: TypeGraph TypeRep -> Set TypeRep
findPrimNodes tg =
  Set.fromList (filter (\n -> not (any (nonPrim n) (labEdges (view graph tg)))) (labNodes (view graph tg)))
    where
      nonPrim :: TypeRep -> (TypeRep, TypeRep, Hop TypeRep) -> Bool
      nonPrim a (b, _, _) | a /= b = False
      nonPrim _ (_, _, ViewHop) = False
      nonPrim _ _ = True

findAlgNodes :: TypeGraph TypeRep -> Set TypeRep
findAlgNodes tg =
  Set.fromList (filter (\n -> not (any (nonAlg n) (labEdges (view graph tg)))) (labNodes (view graph tg)))
    where
      nonAlg a (b, _, _) | a /= b = False
      nonAlg _ (_, _, IxHop _) = True
      nonAlg _ (_, _, AtHop _) = True
      nonAlg _ (_, _, ViewHop) = False
      nonAlg _ (_, _, FieldHop _ _) = False

findIxNodes :: TypeGraph TypeRep -> Set TypeRep
findIxNodes tg =
  Set.fromList (filter (\n -> not (any (nonIx n) (labEdges (view graph tg)))) (labNodes (view graph tg)))
    where
      nonIx a (b, _, _) | a /= b = False
      nonIx _ (_, _, ViewHop) = False
      nonIx _ (_, _, IxHop _) = False
      nonIx _ _ = True

findAtNodes :: TypeGraph TypeRep -> Set TypeRep
findAtNodes tg =
  Set.fromList (filter (\n -> not (any (nonAt n) (labEdges (view graph tg)))) (labNodes (view graph tg)))
    where
      nonAt a (b, _, _) | a /= b = False
      nonAt _ (_, _, ViewHop) = False
      nonAt _ _ = True

findOrderNodes :: TypeGraph TypeRep -> Set TypeRep
findOrderNodes tg =
  Set.fromList (filter (\n -> not (any (nonOrder n) (labEdges (view graph tg)))) (labNodes (view graph tg)))
    where
      nonOrder a (b, _, _) | a /= b = False
      nonOrder _ (b, _, _) = not (isOrderType b)
#endif

-- | Filter out any types that are not functors out of ixedNodes.
-- That means that the last element of the decomposed type must be the
-- IxValue of that type.
isIxedValue :: E Type -> Q Bool
isIxedValue t = do
  vtype <- applyTypeFunction ''IxValue t
  case vtype of
    Nothing -> return False
    Just (E vtype') ->
        case unsnoc (decomposeType (unE t)) of
          Just (_, a) -> maybe False (const True) <$> unify' vtype' a
          Nothing -> return False

runTypes ::
       (Monad m)
    => Int
    -> S typ
    -> (PathT typ m ())
    -> m (S typ)
runTypes v0 s0 action = fst <$> execRWST action r0 s0
    where r0 = (R {_verbosity = v0, _prefix = "  "})

-- | Build an expression for a TypeGraph.  The typ parameter must be TypeRep
-- because we use @gmapQ typeOf@ to get the field types in goAlgebraic.
makeHopGraph ::
    forall m. Monad m
    => Int
    -> Dispatcher
    -> Map TypeRep TypeRep -> Map TypeRep TypeRep
    -> [TypeRep]
    -> Map TypeRep TypeRep
    -> Map TypeRep TypeRep
    -> Set TypeRep -> Set TypeRep -> Set TypeRep -> Set TypeRep -> Set TypeRep
    -> m (TypeGraph TypeRep)
makeHopGraph v typeMap ixValueTypes indexTypes start views migrations primNodes algNodes ixNodes atNodes orderNodes = do
  -- Int is always a member of the key set, it is the default Index
  -- type for [a], Text, etc.  Int64 is the default Index type for
  -- Lazy Text, so that should probably be inserted too.  I'm not sure
  -- this is still necessary, Int should be discovered by expanding
  -- the Index type function.
  s <- runTypes v (S {_typegraph = TypeGraph {_graph = G.empty, _keys = Set.empty},
                      _nodemap = G.new,
                      _visited = mempty,
                      _starts = Set.fromList start}) $ do
    message 1 "\nCollecting typegraph edges:"

    -- Prune edges and nodes unreachable from the start type(s)
    mapM_ goNew start
    start' <- Set.toList <$> use starts
    gr <- use (typegraph . graph)
    let reachableTypeSet = evalState (mapM (reachable gr) start' >>= mapM mkNode . Set.toList . Set.unions) (G.fromGraph gr)
    (typegraph . graph) .= G.subgraph reachableTypeSet gr
    prunedTypeGraph <- use typegraph
    message 1 ("\nPruned type graph:\n" ++ pprint prunedTypeGraph)
  -- Return the graph
  return $ _typegraph s
    where
      goNew :: TypeRep -> PathT TypeRep m ()
      goNew t = do
        unvisited <- Set.notMember t <$> use visited
        case unvisited of
          False -> return ()
          True -> local (over prefix' (++ " ")) $ do
            message 1 $ "goType " ++ show t
            visited %= Set.insert t
            node t
            local (over prefix' (++ " ")) $ goMigration t
      goMigration :: TypeRep -> PathT TypeRep m ()
      goMigration t = do
        case Map.lookup t migrations of
          Nothing -> goView t
          Just t' -> do
             goNew t'
             -- There is no edge to the MigrateFrom type, but we need
             -- to prevent it from being pruned away.
             starts %= Set.insert t'
             goView t
      goView :: TypeRep -> PathT TypeRep m ()
      goView t = do
        case Map.lookup t views of
          Nothing -> goType t
          Just u -> do
             edge t u ViewHop
             goNew u
             goType t

      goType :: TypeRep -> PathT TypeRep m ()
      goType t | Set.member t primNodes = return ()
      goType t | Set.member t algNodes = do
        message 1 ("goAlgebraic " ++ show t)
        typeMap goAlg t
        where
          goAlg :: forall a. Data a => Proxy a -> PathT TypeRep m ()
          goAlg _ = when (isAlgType (dataTypeOf (undefined :: a)))
                       (mapM_ (uncurry goCon) (zip (constrs :: [a]) [1..]))
            where
              goCon :: a -> Int -> PathT TypeRep m ()
              goCon c cpos =
                let arity = length (gmapQ (const ()) c) in
                mapM_ (\fpos -> gmapQi (pred fpos) (goField cpos fpos) c) [1..arity]
              goField :: forall b. Data b => Int -> Int -> b -> PathT TypeRep m ()
              goField cpos fpos b =
                edge t (typeOf b) (FieldHop cpos fpos) >> goNew (typeOf b)
      goType t | Set.member t ixNodes = ixed IxHop t
      goType t | Set.member t atNodes = ixed AtHop t
      goType t | Set.member t orderNodes = order IxHop t
      goType t = error $ "makeHopGraph - unexpected type (no Data instance?): " ++ show t

      ixed :: (TypeRep -> Hop TypeRep) -> TypeRep -> PathT TypeRep m ()
      ixed mkHop t = do
        case (Map.lookup t indexTypes, Map.lookup t ixValueTypes) of
          (Nothing, _) -> error $ "Ixed type " ++ show t ++ " has no Index type"
          (_, Nothing) -> error $ "Ixed type " ++ show t ++ " has no IxValue type"
          (Just index, Just ixValue) -> do
            (typegraph . keys) %= Set.insert index
            edge t ixValue (mkHop index)
            goNew index
            goNew ixValue

      order :: (TypeRep -> Hop TypeRep) -> TypeRep -> PathT TypeRep m ()
      order mkHop t = do
        case (Map.lookup t indexTypes, Map.lookup t ixValueTypes) of
          (Nothing, _) -> error $ "Ixed type " ++ show t ++ " has no Index type"
          (_, Nothing) -> error $ "Ixed type " ++ show t ++ " has no IxValue type"
          (Just index, Just ixValue) -> do
            (typegraph . keys) %= Set.insert index
            edge t ixValue (mkHop index)
            goNew index
            goNew ixValue

      node :: Monad m => TypeRep -> PathT TypeRep m ()
      node typ = do
        gr <- use (typegraph . graph)
        gr' <- zoom nodemap (insNode typ gr)
        (typegraph . graph) .= gr'

      edge :: Monad m => TypeRep -> TypeRep -> Hop TypeRep -> PathT TypeRep m ()
      edge t1 t2 hop = do
        gr <- use (typegraph . graph)
        message 1 ("insEdge (" ++ show t1 ++ ") (" ++ show t2 ++ ") (" ++ pprint1 (fmap show hop) ++ ")")
        gr' <- zoom nodemap (insEdge (t1, t2, hop) gr)
        (typegraph . graph) .= gr'

    -- mapM_ (goType nodes' prims' viewMap ixedMap) nodes'
