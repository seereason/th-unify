-- | Unification and binding expansion

{-# LANGUAGE CPP #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances, MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE LambdaCase #-}
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
    , HasVisited(visited)
    , foldType'
    , foldType
    , RT(..), prefix
    , expandBindings
    , freeVariables
    , quantifyType
    , typeFunctionMap
    , applyTypeFunction
    , applyTypeFunction'
    , applyTypeFunction''
    -- * Syntax
    , mapCon
    , toNormalC
    , findTypeVars
    ) where

import Control.Lens ((%=), _2, Lens', makeLenses, over, set, use, view)
import Control.Monad (when)
import Control.Monad.RWS (ask, execRWS, evalRWST, get, local, modify, put, RWS, RWST)
import Control.Monad.State (execStateT, StateT)
import Data.Default (Default(def))
import Data.Foldable (foldrM, toList)
import Data.Generics (Data, everywhere, mkT)
import Data.List (intersperse)
import Data.Map as Map ((!), fromList, insert, keys, lookup, Map, member)
import Data.Maybe (fromJust, fromMaybe, isJust, mapMaybe)
import Data.Set as Set (fromList, insert, map, member, minView, null, Set, union)
import Data.THUnify.Prelude (anyM', decomposeType, E(E, unE), expandTypeQ, gFind, pprint1, toName)
import Data.THUnify.Prelude.TH (withBindings)
import Data.THUnify.Reify (typesFromFamilyName, tySynInstPairs)
import Debug.Show (V(V))
import Extra.Debug (HasMessageInfo(..), message, Verbosity(..))
import Language.Haskell.TH
import Language.Haskell.TH.Desugar (DsMonad)
import Language.Haskell.TH.Instances ()
import Language.Haskell.TH.PprLib (Doc, hcat, text)
import Language.Haskell.TH.Syntax (qReify, Quasi)

-- | A type with a HasMessageInfo instance to use in the Reader or RWS monad.
data RT
    = RT
      { _verbosityR :: Int
      , _prefixR :: String
      , _tparamsR :: [Type]
      }

$(makeLenses ''RT)

instance HasMessageInfo RT where
    verbosity = verbosityR
    prefix = prefixR

class HasTypeParameters a where
    tparams :: Lens' a [Type]

instance HasTypeParameters RT where
    tparams = tparamsR

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
unifies' :: forall m. Quasi m => Set (E Type) -> E Type -> m (Maybe (E Type, Map Type Type))
unifies' insts t = go insts
    where
      go :: Set (E Type) -> m (Maybe (E Type, Map Type Type))
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

-- | Bind the free variables in a type expression.
-- @@
-- λ> quantifyType (E (AppT (AppT (ConT ''Map) (VarT (mkName "k"))) (VarT (mkName "v"))))
-- E {unE = ForallT [PlainTV k,PlainTV v] [] (AppT (AppT (ConT ''Map) (VarT k)) (VarT v))}
-- @@
quantifyType :: E Type -> E Type
quantifyType typ =
  case freeVariables typ of
    vs | Set.null vs -> typ
    vs -> E (ForallT (fmap PlainTV (toList vs)) [] (unE typ))

-- | Find the variables in a type expression that are free (used but
-- never declared.)
-- @@
-- λ> freeVariables (E (AppT (AppT (ConT ''Map) (VarT (mkName "k"))) (VarT (mkName "v"))))
-- fromList [k,v]
-- @@
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
      go _ = error "Data.THUnify.Unify.freeVariables - FIXME"

-- | Given a type function name (e.g. ''Index) and a set of types
-- (e.g. all instances of Ixed), build a map from t to Index t.  Note
-- that type variables in insts do not match those returned by
-- reifying name.
typeFunctionMap :: Name -> Set (E Type) -> Q (Map (E Type) (E Type))
typeFunctionMap name insts =
    Map.fromList <$> (mapM (\t -> (,) <$> pure t <*> (fromJust <$> applyTypeFunction name t))
                        (toList insts))

-- Expand a type function, aka a type family instance.
-- @@
-- λ> putStrLn $([t|Map Int Char|] >>= applyTypeFunction ''Index >>= lift . show)
-- Just (ConT GHC.Types.Int)
-- @@
applyTypeFunction :: forall m. DsMonad m => Name -> E Type -> m (Maybe (E Type))
applyTypeFunction tyfam (E arg) = do
  tySynInstPairs tyfam >>= go
  where
    go :: [(Type, Type)] -> m (Maybe (E Type))
    go [] = return Nothing
    go ((typ, syn) : more) = do
      r <- unify' typ arg
      case r of
        Nothing -> go more
        Just bindings -> Just <$> expandTypeQ (pure (expandBindings bindings syn))

-- | Apply the type function expressed by the Map, which can be
-- computed by 'typeFunctionMap' or 'Data.THUnion.Reify.typesFromFamilyName'.
applyTypeFunction' :: Quasi m => Map (E Type) (E Type) -> E Type -> m (Maybe (E Type))
applyTypeFunction' typefn t = do
  -- Type variables in s will not match those in i
  mmp <- unifies' s t
  case mmp of
    Nothing -> return Nothing
    Just (i, bindings) -> return $ Just $ expandBindings bindings (typefn ! i)
  where
    s :: Set (E Type)
    s = Set.fromList (Map.keys typefn)

instance Ppr (Set (E Type)) where
    ppr s = text "fromList [" <> hcat (intersperse (text ", ") (fmap ppr (toList s))) <> text "]"

instance Ppr a => Ppr (Maybe a) where
    ppr Nothing = text "-"
    ppr (Just a) = ppr a

instance Ppr (E Type, Map Type Type) where
    ppr (typ, bindings) = text "(type=" <> ppr typ <> text ", bindings:" <> ppr bindings <> text ")"

instance Semigroup Doc where
    a <> b = hcat [a, b]


-- | Expand the bindings in both types
applyTypeFunction'' :: (Quasi m, Verbosity r m) => Map (E Type) (E Type) -> E Type -> m (Maybe (E Type, E Type))
applyTypeFunction'' typefn t = do
  mmp <- unifies' s t
  case mmp of
    Nothing -> return Nothing
    Just (i, bindings) ->
      return $ Just $ (t, expandBindings bindings (typefn ! i))
  where
    s :: Set (E Type)
    s = Set.fromList (Map.keys typefn)

class HasVisited s where
  visited :: Lens' s (Set Name)

-- | Do a fold over the constructors of a type, after performing type
-- variable substitutions.
foldType' ::
    (Show r, Quasi m, Default s, HasVisited s, Verbosity RT (RWST RT () s m))
    => ([Con] -> r -> RWST RT () s m r)
    -> (Type -> r -> RWST RT () s m r)
    -> Type
    -> r -> m r
foldType' f g typ r0 =
    fst <$> evalRWST (foldType f g typ r0) (RT 0 "" []) def

foldType ::
    (Show r, Quasi m, HasVisited s, Verbosity RT (RWST RT () s m))
    => ([Con] -> r -> RWST RT () s m r)
    -> (Type -> r -> RWST RT () s m r)
    -> Type
    -> r
    -> RWST RT () s m r
foldType f g typ r0 =
    -- message 1 ("foldType typ=" ++ pprint1 typ) >>
    case decomposeType typ of
      [ForallT _tvs _cx typ'] -> foldType f g typ' r0
      [ListT, typ'] -> g typ' r0
      [VarT _name] -> return r0
      (TupleT _ : tparams) -> foldrM g r0 tparams
      (ConT tname : tps) ->
          local (over tparams (tps ++)) $ do
            names <- use visited
            if Set.member tname names
            then return r0
            else do
              visited %= Set.insert tname
              qReify tname >>= goInfo
      _ -> error $ "foldType - unexpected Type: " ++ show typ
    where
      goInfo (TyConI dec) =
          -- message 1 ("foldType tparams=" ++ show tparams) >>
          -- message 1 ("foldType dec=" ++ pprint1 dec) >>
          goDec f g dec r0
      goInfo (PrimTyConI {}) = return r0
      goInfo info = error $ "foldType - unexpected info: " ++ show info

-- | Perform the substitutions implied by the type parameters and the
-- bindings on the declaration's constructors.  Then do a fold over
-- those constructors.  This is a helper function for foldType.
goDec ::
    (Show r, Quasi m, HasVisited s, Verbosity RT (RWST RT () s m))
    => ([Con] -> r -> RWST RT () s m r)
    -> (Type -> r -> RWST RT () s m r)
    -> Dec
    -> r
    -> RWST RT () s m r
#if MIN_VERSION_template_haskell(2,11,0)
goDec f g (NewtypeD _cxt1 _tname binds _mk con _cxt2) r0 =
    goDec f g (DataD _cxt1 _tname binds _mk [con] _cxt2) r0
goDec f g (DataD _cxt1 _tname binds _mk cons _cxt2) r0 = do
#else
goDec f g (NewtypeD _cxt1 _tname binds con _cxt2) r0 =
    goDec f g (DataD _cxt1 _tname binds [con] _cxt2) r0
goDec f g (DataD _cxt1 _tname binds cons _cxt2) r0 = do
#endif
    tps <- view tparams
    message 2 ("goDec tparams=" ++ pprint1 (V tps))
    message 2 ("goDec binds=" ++ pprint1 binds)
    -- message 1 ("goDec cons=" ++ pprint1 cons)
    withBindings tps binds
      (\subst -> local (set tparams []) $ do
         let cons' = subst cons
         -- message 1 ("cons'=" ++ show cons')
         r1 <- f cons' r0
         -- message 1 ("goDec r1=" ++ show r1)
         foldrM (goCon g) r1 cons')
goDec f g (TySynD _tname _binds typ) r0 =
    foldType f g typ r0
goDec _f _g dec _r0 = error $ "goDec - unexpected Dec: " ++ pprint dec

goCon :: Quasi m => (Type -> r -> RWST RT () s m r) -> Con -> r -> RWST RT () s m r
goCon g (NormalC _tvs btypes) r = do
  -- message 1 ("goCon types=" ++ show (fmap (view _2) btypes))
  foldrM g r (fmap (view _2) btypes)
goCon g con r = goCon g (toNormalC con) r

-- | Apply monadic transformations to a constructor's cnames, fnames, and field types.
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

-- | Convert any (non-GADT) constructor to a similary NormalC.
toNormalC :: Con -> Con
toNormalC (ForallC tvs cx con) = ForallC tvs cx (toNormalC con)
toNormalC (InfixC btyp1 cname btyp2) = NormalC cname [btyp1, btyp2]
toNormalC (RecC cname vbtypes) = NormalC cname (fmap (\(_, a, b) -> (a, b)) vbtypes)
toNormalC (NormalC tvs btypes) = NormalC tvs btypes
toNormalC x = error $ "Unexpected Con: " ++ show x

findTypeVars :: Data a => a -> Set Name
findTypeVars x = Set.fromList $ mapMaybe (\case VarT name -> Just name; _ -> Nothing) (gFind x :: [Type])
