{-# LANGUAGE CPP, FlexibleInstances, RankNTypes, RecordWildCards, ScopedTypeVariables, TemplateHaskell #-}
{-# OPTIONS -Wall #-}

module Data.THUnify.TypeGraph.Nodes
    ( TypeGraphNodes(..)
    , typeGraphNodes
    ) where

import Control.Lens ((%=), _2, _3, Index, Ixed, IxValue, makeLenses, over, use, view)
import Control.Monad (unless)
import Control.Monad.RWS as Monad (evalRWST, local, RWST)
import Data.Bool (bool)
import Data.Generics (Data, Proxy, TypeRep)
import Data.List (sort)
import Data.Map as Map (filter, fromList, insert, insertWith, keys, Map, member)
import Data.THUnify.Prelude (decomposeType, E(E, unE), expandTypeQ, HasMessageInfo(..), message, pprint1)
import Data.THUnify.Unify (applyTypeFunction',
                        expandBindings,
                        typeDispatcher,
                        typeFunctionMap,
                        typesFromClassName,
                        typesFromFamilyName,
                        typeRepFromType,
                        unifies)
import Data.THUnify.View (ViewType)
import Data.SafeCopy (MigrateFrom)
import Data.Set as Set hiding (empty, foldr, foldl)
import Data.Set.Extra as Set (partitionM)
import Language.Haskell.TH
import Language.Haskell.TH.Desugar (DsMonad)
import Language.Haskell.TH.Syntax (Lift(lift))

data R = R { _verbosity :: Int
           , _prefix :: String
           , _sinks :: Set (E Type)
           , _views :: Map (E Type) (E Type)
           , _migrations :: Map (E Type) (E Type)
           , _ixValues :: Map (E Type) (E Type)
           , _indexes :: Map (E Type) (E Type) }

$(makeLenses ''R)

data Ty = Ty | PrimTy deriving (Eq)

data S = S { _visited :: Map (E Type) Ty
           , _edges :: Map (E Type) (Set (E Type))
           }

$(makeLenses ''S)

instance HasMessageInfo R where
    verbosity' = verbosity
    prefix' = prefix

type NodeT = RWST R () S

typeReps :: Set (E Type) -> ExpQ -- :: [(E Type, TypeRep)]
typeReps types =
  listE (fmap (\t -> [|($(lift t), $(typeRepFromType (pure (unE t))))|]) (Set.toList types))

data TypeGraphNodes
    = TypeGraphNodes { _roots :: [(E Type, TypeRep)]
                     , _nodes :: [(E Type, TypeRep)]
                     , _primitives :: Set (E Type)
                     , _typeMap :: (forall r. (forall d. Data d => Proxy d -> r) -> TypeRep -> r)
                     }

instance Lift TypeGraphNodes where
    lift nodes@(TypeGraphNodes rs ns ps _) =
        [|TypeGraphNodes $(lift rs) $(lift ns) $(lift ps)
             $((typeDispatcher [|\t -> error $ "typeGraphNodes - unexpected type: " ++ show t|] . fmap (unE . fst)) (_nodes nodes))|]

instance Show TypeGraphNodes where
    show x = "TypeGraphNodes {_roots=" ++ show (_roots x) ++ ", _nodes=" ++ show (_nodes x) ++ ", _primitives=" ++ show (_primitives x) ++ ", _typeMap=<higher order function>}"

instance Eq TypeGraphNodes where
    n1 == n2 =
        sort (_roots n1) == sort (_roots n2) &&
        sort (_nodes n1) == sort (_nodes n2) &&
        _primitives n1 == _primitives n2

typeGraphNodes ::
       Int
    -> [TypeQ]
    -> [TypeQ]
    -> ExpQ -- :: TypeGraphNodes
typeGraphNodes v primTypes start = do
  nodes <- typeGraphNodes' v primTypes start
  [| TypeGraphNodes
       $(mapM expandTypeQ start >>= listE . fmap (\t -> [|(t, $(typeRepFromType (pure (unE t))))|]))
       $(typeReps nodes)
       $(mapM expandTypeQ primTypes >>= lift . Set.fromList)
       $((typeDispatcher [|\t -> error $ "typeGraphNodes - unexpected type: " ++ show t|] . fmap unE . Set.toList) nodes) |]

-- | Given a set of primitives and start types, explore the type
-- graph to collect the set of reachable types.
typeGraphNodes' ::
       Int
    -> [TypeQ]
    -> [TypeQ]
    -> Q (Set (E Type))
typeGraphNodes' v sinks' start = do
  (start' :: [E Type]) <- mapM expandTypeQ start
  dat <- typesFromClassName ''Data
  ixed <- typesFromClassName ''Ixed
  r0 <- R v "  "
          <$> (Set.fromList <$> sequence (fmap expandTypeQ sinks'))
          <*> typesFromFamilyName ''ViewType
          <*> typesFromFamilyName ''MigrateFrom
          <*> typeFunctionMap ''IxValue ixed
          <*> typeFunctionMap ''Index ixed
  fst <$> evalRWST (do message 1 "Collecting typegraph edges"
                       mapM_ doNew start'
                       nodes <- (Set.fromList . Map.keys) <$> use visited
                       prims'' <- (Set.fromList . Map.keys . Map.filter (== PrimTy)) <$> use visited
                       -- Any node that has a prim in its edge set is a sink - no out edges
                       -- will be generated from it, even to non-prim types.
                       sinks'' <- (Set.fromList . Map.keys . Map.filter (not . Set.null . Set.intersection prims'')) <$> use edges
                       redundantSinks <- Set.intersection sinks'' <$> view sinks
                       unless (Set.null redundantSinks) (message 1 ("Warning - redundant sinks: " ++ pprint1 (fmap unE (Set.toList redundantSinks))))
                       let primNodes = Set.intersection nodes prims''
                           nodes' = Set.difference nodes prims''
                       unless (Set.null primNodes) (message 1 ("Primitive nodes (omitted): " ++ pprint1 (fmap unE (Set.toList primNodes))))
                       -- Only instances of Data can be nodes
                       (nodes'', nondataNodes) <- runQ $ Set.partitionM (unifies dat) nodes'
                       unless (Set.null nondataNodes) (message 1 ("Non-Data types (omitted): " ++ pprint1 (fmap unE (Set.toList nondataNodes))))
                       return nodes'') r0 (S mempty mempty)
    where
      doNew :: DsMonad m => E Type -> NodeT m ()
      doNew t = do
        unvisited <- (not . Map.member t) <$> use visited
        case unvisited of
          False -> return ()
          True -> local (over prefix' (++ " ")) $ do
            message 1 $ pprint1 (unE t)
            visited %= Map.insert t Ty
            local (over prefix' (++ " ")) $ doMigration t
      doMigration :: DsMonad m => E Type -> NodeT m ()
      doMigration t =
          view migrations >>= \mp -> runQ (applyTypeFunction' mp t) >>= maybe (doView t) (\t' -> message 2 ("migrateFrom: " ++ pprint1 (unE t) ++ " -> " ++ pprint1 (unE t')) >> doView t >> doNew t')
      doView :: DsMonad m => E Type -> NodeT m ()
      doView t =
          view views >>= \mp -> runQ (applyTypeFunction' mp t) >>= maybe (doPrim t) (\t' -> message 2 ("view: " ++ pprint1 (unE t) ++ " -> " ++ pprint1 (unE t')) >> doPrim t >> doEdge t t')
      doPrim :: DsMonad m => E Type -> NodeT m ()
      doPrim t =
          view sinks >>= \s -> runQ (unifies s t) >>= bool (doTuple t) (message 2 ("primitive: " ++ pprint1 (unE t)) >> return ())
      -- lens considers a tuple to be an Ixed type.  We do not,
      -- because each field generally has a different type.  Therefore
      -- we handle that case before calling doIndex.
      doTuple :: DsMonad m => E Type -> NodeT m ()
      doTuple t = case decomposeType (unE t) of
                        (TupleT _ : ts) -> mapM_ (doEdge t . E) ts
                        _ -> doIndex t
      doIndex :: DsMonad m => E Type -> NodeT m ()
      doIndex t = view indexes >>= \mp -> runQ (applyTypeFunction' mp t) >>= maybe (doIxValue t) (\t' -> message 2 ("Index: " ++ pprint1 (unE t')) >> doIxValue t >> doEdge t t')
      doIxValue :: DsMonad m => E Type -> NodeT m ()
      doIxValue t = view ixValues >>= \mp -> runQ (applyTypeFunction' mp t) >>= maybe (doType t [] t) (\t' -> message 2 ("IxValue: " ++ pprint1 (unE t')) >> doEdge t t')
      doType :: DsMonad m => E Type -> [E Type] -> E Type -> NodeT m ()
      doType t stack (E (AppT t1 t2)) = doType t (E t2 : stack) (E t1)
      doType _ _ (E (TupleT _)) = error "We already handled this"
      doType t [a] (E ListT) = doEdge t a
      doType t stack (E (ConT tname)) = runQ (reify tname) >>= doInfo t stack
      doType _ _ typ = error $ "doType: " ++ show typ
      doInfo :: DsMonad m => E Type -> [E Type] -> Info -> NodeT m ()
#if MIN_VERSION_template_haskell(2,11,0)
      doInfo t stack (TyConI (NewtypeD _ _ tvs _ con _)) = doCon t (Map.fromList (zip (fmap tvtype tvs) (fmap unE stack))) con
      doInfo t stack (TyConI (DataD _cxt _ tvs _ cons _)) = mapM_ (doCon t (Map.fromList (zip (fmap tvtype tvs) (fmap unE stack)))) cons
#else
      doInfo t stack (TyConI (NewtypeD _ _ tvs con _)) = doCon t (Map.fromList (zip (fmap tvtype tvs) (fmap unE stack))) con
      doInfo t stack (TyConI (DataD _ _ tvs cons _)) = mapM_ (doCon t (Map.fromList (zip (fmap tvtype tvs) (fmap unE stack)))) cons
#endif
      doInfo t stack (TyConI (TySynD _name tvs syn))
        | length stack == length tvs = do
            let bindings = Map.fromList (zip (fmap tvtype tvs) (fmap unE stack))
            message 2 $ "type synonym " ++ pprint1 syn
            syn' <- expandTypeQ (pure syn)
            doEdge t (expandBindings bindings syn')
      doInfo _ _ (TyConI (TySynD _name _ _)) = error "doInfo - arity error"
      doInfo t _ (PrimTyConI _ _ _) = visited %= Map.insert t PrimTy
      doInfo _ _ info = error $ "Data.THUnify.Nodes.doInfo: " ++ show info
      doCon :: DsMonad m => E Type -> Map Type Type -> Con -> NodeT m ()
      doCon t bindings (NormalC _name fields) = mapM_ (doField t bindings . view _2) fields
      doCon t bindings (RecC _name fields) = mapM_ (doField t bindings . view _3) fields
      doCon t bindings (InfixC field1 _name field2) = mapM_ (doField t bindings . view _2) [field1, field2]
      doCon t bindings (ForallC _tvs _cxt con) = doCon t bindings con
#if MIN_VERSION_template_haskell(2,11,0)
      doCon _ _ (GadtC _ _ _) = error "GadtC"
      doCon _ _ (RecGadtC _ _ _) = error "RecGadtC"
#endif
      doField :: DsMonad m => E Type -> Map Type Type -> Type -> NodeT m ()
      doField t bindings ftype = message 2 ("field: " ++ pprint1 ftype) >> runQ (expandTypeQ (pure ftype)) >>= doEdge t . expandBindings bindings
      doEdge :: DsMonad m => E Type -> E Type -> NodeT m ()
      doEdge t1 t2 = edges %= Map.insertWith Set.union t1 (Set.singleton t2) >> doNew t2

tvtype :: TyVarBndr -> Type
tvtype (PlainTV name) = VarT name
tvtype (KindedTV name _) = VarT name

{-
λ> putStrLn $(typeGraphNodes' 0 [] [t|Type|] >>= Language.Haskell.TH.Syntax.lift . pprint . fmap unE . Set.toList)
[GHC.Types.Char]
[Language.Haskell.TH.Syntax.TyVarBndr]
[Language.Haskell.TH.Syntax.Type]
GHC.Types.Char
GHC.Types.Int
GHC.Integer.Type.Integer
Language.Haskell.TH.Syntax.ModName
Language.Haskell.TH.Syntax.Name
Language.Haskell.TH.Syntax.NameFlavour
Language.Haskell.TH.Syntax.NameSpace
Language.Haskell.TH.Syntax.OccName
Language.Haskell.TH.Syntax.PkgName
Language.Haskell.TH.Syntax.TyLit
Language.Haskell.TH.Syntax.TyVarBndr
Language.Haskell.TH.Syntax.Type
λ> putStrLn $(typeGraphNodes' 0 [[t|Name|]] [t|Type|] >>= Language.Haskell.TH.Syntax.lift . pprint . fmap unE . Set.toList)
[GHC.Types.Char]
[Language.Haskell.TH.Syntax.TyVarBndr]
[Language.Haskell.TH.Syntax.Type]
GHC.Types.Char
GHC.Types.Int
GHC.Integer.Type.Integer
Language.Haskell.TH.Syntax.Name
Language.Haskell.TH.Syntax.TyLit
Language.Haskell.TH.Syntax.TyVarBndr
Language.Haskell.TH.Syntax.Type
-}
