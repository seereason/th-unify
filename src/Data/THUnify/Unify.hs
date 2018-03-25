-- | Unification and binding expansion

{-# LANGUAGE CPP #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# OPTIONS -Wall #-}

module Data.THUnify.Unify
    ( unify
    , unify'
    , unifies
    , unifies'
    -- * Type Variable bindings
    , foldType, foldDec
    , expandBindings
    , withBindings
    , freeVariables
    , quantifyType
    -- * Type classes, type families, type functions
    , typesFromClassName
    , typesFromClassName'
    , applyTypeFunction
    , applyTypeFunction'
    , typeFunctionMap
    , typesFromFamilyName
    , tySynInstPairs
    -- * Syntax
    , mapCon, toNormalC
    ) where

import Control.Monad (when)
import Control.Monad.RWS (ask, execRWS, get, local, modify, put, RWS)
import Control.Monad.State (execStateT, StateT)
import Data.Generics (Data, everywhere, mkT)
import Data.Map as Map ((!), fromList, insert, keys, lookup, Map, member)
import Data.Maybe (fromJust, fromMaybe, isJust)
import Data.Set as Set (fromList, insert, map, member, minView, null, Set, toList, union)
import Data.THUnify.Orphans ()
import Data.THUnify.Prelude (anyM', decomposeType, E(E, unE), expandTypeQ, toName)
import Data.THUnify.Reify (tySynInstPairs, typesFromFamilyName)
import Data.THUnify.TestData
import Data.THUnify.TypeRep (typeRepFromType)
import Language.Haskell.TH
import Language.Haskell.TH.Instances ()
import Language.Haskell.TH.Syntax (qReify, Quasi)

-- | Unify two 'Type' and on success return the resulting variable bindings.
unify :: forall m. Quasi m => TypeQ -> TypeQ -> m (Maybe (Map Type Type))
unify aq bq = do
  a0 <- runQ aq
  b0 <- runQ bq
  unify' a0 b0

-- | This needs the Quasi monad because it uses qReify.
unify' :: forall m. Quasi m => Type -> Type -> m (Maybe (Map Type Type))
unify' a0 b0 =
    execStateT (go a0 b0) (Just mempty)
    where
      go :: Type -> Type -> StateT (Maybe (Map Type Type)) m ()
      -- ForallT brings new type variables into existance, hiding any
      -- same named variables we have already encountered.  So we must
      -- rename any of these variables already in the map to something
      -- different and unique (such as a newName.)  The names that
      -- must be changed are those not inside the ForallT - for the
      -- first clause that means those in b and those present in the
      -- State (Map Type Type).
      go (ForallT vs _cxt a) b = makeRenameMap (fmap tvname vs) >>= \mp -> modify (fmap (everywhere (mkT (rename mp)))) >> go a (rename mp b)
      go a (ForallT vs _cxt b) =  makeRenameMap (fmap tvname vs) >>= \mp -> modify (fmap (everywhere (mkT (rename mp)))) >> go (rename mp a) b
      go (AppT a b) (AppT c d) = go a c >> go b d
      go (ConT a) (ConT b) | a == b = return ()
      go a@(VarT _) b = do
        binding <- maybe Nothing (Map.lookup a) <$> get
        -- We ought to ensure that unexpended bindings don't appear in b
        maybe (modify (fmap (Map.insert a b))) (\a' -> go a' b) binding
      go a b@(VarT _) = go b a
      go a b | a == b = return ()
      go (ConT a) b = qReify a >>= goInfo b
      go a (ConT b) = qReify b >>= goInfo a
      go _ _ = {-trace ("Could not unify: " ++ pprint (AppT (AppT EqualityT a) b))-} (put Nothing)

      goInfo a (TyConI dec) = goDec a dec
      goInfo _a _b = {-trace ("Could not unify: " ++ pprint (AppT (AppT EqualityT a0) b0))-} (put Nothing)
      goDec a (TySynD tname [] b) = modify (fmap (Map.insert (ConT tname) b)) >> go a b
      goDec _a _b = {-trace ("Could not unify: " ++ pprint (AppT (AppT EqualityT a0) b0))-} (put Nothing)

makeRenameMap :: Quasi m => [Name] -> m (Map Type Type)
makeRenameMap tvars = runQ $ Map.fromList <$> (zip <$> mapM varT tvars <*> mapM (\n -> newName (nameBase n) >>= varT) tvars)

tvname :: TyVarBndr -> Name
tvname (PlainTV name) = name
tvname (KindedTV name _) = name

rename :: Map Type Type -> Type -> Type
rename mp typ = everywhere (mkT (\x -> (fromMaybe x (Map.lookup x mp)))) typ

-- | Given a set of types such as those returned by typesFromClassName, see if
-- a type unifies with any of them.  This indicates that the type is
-- an instances of that class.
unifies :: Set (E Type) -> E Type -> Q Bool
unifies insts t = anyM' Set.minView (\node -> isJust <$> unify' node (unE t)) (Set.map unE insts)

-- | Unify @t@ with any of the instance types @insts@ and return the
-- resulting type and bindings.
unifies' :: Set (E Type) -> E Type -> Q (Maybe (E Type, Map Type Type))
unifies' insts t = go insts
    where
      go :: Set (E Type) -> Q (Maybe (E Type, Map Type Type))
      go s = case Set.minView s of
               Nothing -> return Nothing
               Just (i, s') -> unify' (unE i) (unE t) >>= maybe (go s') (\mp -> return (Just (i, mp)))

-- | Expand a set of bindings such as those returned by unify.
expandBindings :: forall a. Data a => Map Pred Pred -> a -> a
expandBindings bindings typ = everywhere (mkT (expandBinding bindings)) typ

expandBinding :: Map Pred Pred -> Pred -> Pred
expandBinding mp x@(VarT _) = fromMaybe x (Map.lookup x mp)
expandBinding mp (ForallT tvs cx typ) =
  -- If we have an expansion for a type variable it no longer needs to
  -- be declared.
  case filter (not . (`Map.member` mp) . (VarT . tvname)) tvs of
    [] -> typ
    tvs' -> ForallT tvs' cx typ
expandBinding _ x = x

-- | Input is a list of type variable bindings (such as those
-- appearing in a Dec) and the current stack of type parameters
-- applied by AppT.  Builds a function that expands a type using those
-- bindings and pass it to an action.
withBindings :: forall m a r. Data a =>
                  [Type] -> [TyVarBndr] -> ((a -> a) -> m r) -> m r
withBindings ps binds _
    | (length ps < length binds) =
        error ("doInfo - arity mismatch:\n\tbinds=" ++ show binds ++
               "\n\tparams=" ++ show ps)
withBindings ps binds action =
  action subst
    where
      subst :: forall b. Data b => b -> b
      subst typ = everywhere (mkT subst1) typ

      ps' :: [Type]
      ps' = fmap subst ps

      bindings :: Map Name Type
      bindings = Map.fromList (zip (fmap toName binds) ps')

      subst1 :: Type -> Type
      subst1 t@(VarT name) = maybe t id (Map.lookup name bindings)
      subst1 t = t

-- | Bind the free variables in a type expression.
quantifyType :: E Type -> E Type
quantifyType typ =
  case freeVariables typ of
    vs | Set.null vs -> typ
    vs -> E (ForallT (fmap PlainTV (Set.toList vs)) [] (unE typ))

-- | Find the variables in a type expression that are free (used but
-- never declared.)
freeVariables :: E Type -> Set Name
freeVariables (E typ) =
  -- The reader value is the set of bound variables, the state value
  -- is the set of free variables.
  fst $ execRWS (go typ) mempty mempty
    where
      go :: Type -> RWS (Set Name) () (Set Name) ()
      go (ConT _) = return ()
      go (PromotedT _) = return () -- ??
      go (ForallT tvs _ typ') = let vs = Set.fromList (fmap tvname tvs) in local (Set.union vs) (go typ')
      go (VarT v) = do
        bound <- ask
        when (not (Set.member v bound)) (modify (Set.insert v))
      go (AppT a b) = go a >> go b
#if MIN_VERSION_template_haskell(2,11,0)
      go (InfixT a _ b) = go a >> go b
      go (UInfixT a _ b) = go a >> go b
      go (ParensT a) = go a
#endif
      go (SigT a _) = go a
      go (TupleT _) = return ()
      go (PromotedTupleT _) = return ()
      go (UnboxedTupleT _) = return ()
      go ArrowT = return ()
      go EqualityT = return ()
      go ListT = return ()
      go StarT = return ()
      go (LitT _) = return ()
      go PromotedNilT = return ()
      go PromotedConsT = return ()
      go ConstraintT = return ()
#if MIN_VERSION_template_haskell(2,11,0)
      go WildCardT = return ()
#endif

-- | Find all the types that are currently instances of some class.
typesFromClassName :: Name -> Q (Set (E Type))
typesFromClassName cname = do
  (ClassI _ insts) <- reify cname
  Set.fromList <$> mapM (expandTypeQ . pure) (fmap go insts)
    where
      go :: Dec -> Type
#if MIN_VERSION_template_haskell(2,11,0)
      go (InstanceD _supers _ t _) =
#else
      go (InstanceD _supers t _) =
#endif
          let [_ixed, typ] = decomposeType t in
          typ
      go _ = error "expected InstanceD"

-- | Build a set of TypeRep
typesFromClassName' :: Name -> ExpQ
typesFromClassName' cname = do
  [|Set.fromList $(ListE <$> (typesFromClassName cname >>=
                              sequence . fmap (typeRepFromType . pure . unE) . Set.toList))|]

-- | Given a type function name (e.g. ''Index) and a set of types
-- (e.g. all instances of Ixed), build a map from t to Index t.  Note
-- that type type variables in insts do not match those returned by
-- reifying name.
typeFunctionMap :: Name -> Set (E Type) -> Q (Map (E Type) (E Type))
typeFunctionMap name insts =
    Map.fromList <$> (mapM (\t -> (,) <$> pure t <*> (fromJust <$> applyTypeFunction name t))
                        (Set.toList insts))

-- Expand a type function, aka a type family instance.
-- @@
-- λ> putStrLn $([t|Map Int Char|] >>= applyTypeFunction ''Index >>= lift . show)
-- Just (ConT GHC.Types.Int)
-- @@
applyTypeFunction :: Name -> E Type -> Q (Maybe (E Type))
applyTypeFunction name (E arg) = do
  tySynInstPairs name >>= go
  where
    go :: [(Type, Type)] -> Q (Maybe (E Type))
    go [] = return Nothing
    go ((typ, syn) : more) = do
      r <- unify' typ arg
      case r of
        Nothing -> go more
        Just bindings -> Just <$> expandTypeQ (pure (expandBindings bindings syn))

-- | Apply the type function expressed by the Map, which can be
-- computed by 'typeFunctionMap' or 'typesFromFamilyName'.
applyTypeFunction' :: Map (E Type) (E Type) -> E Type -> Q (Maybe (E Type))
applyTypeFunction' typefn t = do
  -- Type variables in s will not match those in i
  mmp <- unifies' s t
  case mmp of
    Nothing -> return Nothing
    Just (i, bindings) -> return $ Just $ expandBindings bindings (typefn ! i)
  where
    s :: Set (E Type)
    s = Set.fromList (Map.keys typefn)

-- | Do a fold over the constructors of a type, after performing type
-- variable substitutions.
foldType :: ([Con] -> r -> Q r) -> Type -> r -> Q r
foldType f typ r0 =
    case decomposeType typ of
      [ForallT _tvs _cx typ'] -> foldType f typ' r0
      [ListT, typ'] -> foldType f typ' r0
      [VarT _name] -> return r0
      (ConT tname : tparams) -> qReify tname >>= goInfo tparams
      _ -> error $ "foldType - unexpected Type: " ++ show typ
    where
      goInfo tparams (TyConI dec) = foldDec f tparams dec r0
      goInfo _tparams info = error $ "foldType - unexpected info: " ++ show info

-- | Perform the substitutions implied by the type parameters and the
-- bindings on the declaration's constructors.  Then do a fold over
-- those constructors.  This is a helper function for foldType.
foldDec :: Monad m => ([Con] -> r -> m r) -> [Type] -> Dec -> r -> m r
#if MIN_VERSION_template_haskell(2,11,0)
foldDec f tparams (NewtypeD _cxt1 _tname binds _mk con _cxt2) r0 = foldDec f tparams (DataD _cxt1 _tname binds _mk [con] _cxt2) r0
foldDec f tparams (DataD _cxt1 _tname binds _mk cons _cxt2) r0 = withBindings tparams binds (\subst -> f (subst cons) r0)
#else
foldDec f tparams (NewtypeD _cxt1 _tname binds con _cxt2) r0 = foldDec f tparams (DataD _cxt1 _tname binds [con] _cxt2) r0
foldDec f tparams (DataD _cxt1 _tname binds cons _cxt2) r0 = withBindings tparams binds (\subst -> f (subst cons) r0)
#endif

mapCon :: Monad m => (Name -> m Name) -> (Name -> m Name) -> (Type -> m Type) -> Con -> m Con
mapCon cnamef fnamef ftypef con =
    case con of
      (NormalC cname btypes) -> NormalC <$> cnamef cname <*> mapM (overM2 ftypef) btypes
      (RecC cname vbtypes) -> RecC <$> cnamef cname <*> mapM (overM3 ftypef) vbtypes
      (InfixC btyp1 cname btyp2) -> InfixC <$> overM2 ftypef btyp1 <*> cnamef cname <*> overM2 ftypef btyp2
      (ForallC tvs cx con') -> ForallC tvs cx <$> mapCon cnamef fnamef ftypef con'
      _ -> error "mapCon"
    where
      overM2 :: Applicative m => (b -> m c) -> (a, b) -> m (a, c)
      overM2 f (a, b) = (,) <$> pure a <*> f b
      overM3 :: Applicative m => (c -> m d) -> (a, b, c) -> m (a, b, d)
      overM3 f (a, b, c) = (,,) <$> pure a <*> pure b <*> f c

toNormalC :: Con -> Con
toNormalC (ForallC tvs cx con) = ForallC tvs cx (toNormalC con)
toNormalC (InfixC btyp1 cname btyp2) = NormalC cname [btyp1, btyp2]
toNormalC (RecC cname vbtypes) = NormalC cname (fmap (\(_, a, b) -> (a, b)) vbtypes)
toNormalC (NormalC tvs btypes) = NormalC tvs btypes
toNormalC x = error $ "Unexpected Con: " ++ show x
