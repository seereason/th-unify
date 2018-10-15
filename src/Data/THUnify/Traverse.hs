{-# LANGUAGE CPP #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# OPTIONS -Wall #-}

module Data.THUnify.Traverse
    ( SubstFn, InfoFn
    , withTypeExpansions
    , withBindings
    , withFree
    , Phantom(..)
    , phantom
    ) where

import Control.Lens (_2, _3, (.=), (%=), over, use, view)
import Control.Monad.RWS (local, tell)
import Control.Monad.State
import Data.Generics (Data, everywhere, mkT)
import Data.List (intercalate)
import Data.Map as Map (insert, lookup, Map, null, toList)
import Data.Set as Set (difference, fromList, Set, singleton, union)
import Data.THUnify.Monad
import Language.Haskell.TH
import Language.Haskell.TH.Syntax

type SubstFn = forall d. Data d => d -> d

type InfoFn w =
       SubstFn          -- The current type variable bindings
    -> [TyVarBndr]      -- The type variables that SubstFn will expand
    -> Either Type Info -- The current type's info record or fully expanded type expression
    -> M w ()

-- | If a type has a kind of order higher than *, apply a suitable
-- number of type variables and call f.
withFree :: forall w. Monoid w => TypeQ -> (Type -> [TyVarBndr] -> M w ()) -> M w ()
withFree typeq f = do
  typ <- runQ typeq
  message 1 ("withFree " ++ pprint1 typ)
  indented 1 $ withTypeExpansions (g typ) typ
    where
      g :: Type -> InfoFn w
      g typ _subst _tvs _info = do
        freeTvs <- use tyvars -- type variables that didn't get bound by withTypeExpansions
        tyvars .= []
        message 1 ("withFree (" ++ pprint1 typ ++ ") -> (" ++ show freeTvs ++ ")")
        local (over expanding tail) $ indented 1 $ f typ freeTvs

-- | Traverse a 'Type' to collect the type variable bindings and
-- constraints.  When we arrive at an 'Info' record or some primitive
-- type like 'ListT' use withBindings to create a variable
-- substitution function and expand the Info record.
withTypeExpansions :: forall w. Monoid w => InfoFn w -> Type -> M w ()
withTypeExpansions f typ0 = indented 2 $ do
  r <- elem typ0 <$> view expanding
  case r of
    True -> do
      message 2 ("Revisited: " ++ pprint1 typ0)
    False -> do
      message 2 ("Type: " ++ pprint1 typ0 ++ " (show: " ++ take 20 (show typ0) ++ "...)")
      local (over expanding (typ0 :)) $ indented 2 $ doType typ0
    where
      doType :: Type -> M w ()
      doType (ForallT unb cx typ) = do
        unbound %= Set.union (Set.fromList unb)
        constraints %= (cx ++)
        doType typ
      doType (AppT typ param) = do
        applied %= (param :)
        doType typ
      doType ListT = do
        [typ] <- pop applied 1
        doType typ
      doType (TupleT n) = do
        types <- pop applied n
        mapM_ doType types
      doType typ@(VarT _name) = do
        f id mempty (Left typ)
      doType (ConT name) = do
        qReify name >>= doInfo
      doType typ = error ("withTypeExpansions - " ++ show typ ++ " support not implemented")

      doInfo :: Info -> M w ()
      doInfo info = do
        message 2 ("Info: " ++ pprint1 info ++ " (" ++ take 20 (show info) ++ "...)")
        case info of
          TyConI (TySynD _tname tvs' typ') -> do
            push tyvars tvs'
            params <- use applied
            unbound %= Set.union (Set.fromList (drop (length params) tvs'))
            withBindings g
              where g :: SubstFn -> [TyVarBndr] -> M w ()
                    g subst _tvs = do
                      let typ'' = subst typ'
                      doType typ''
          TyConI (NewtypeD cx' tname tvs' mk con deriv) -> do
            -- message 2 ("-> NewtypeD con=" ++ pprint1 con)
            constraints %= (cx' ++)
            tyvars %= (tvs' ++)
            withBindings g
              where g :: SubstFn -> [TyVarBndr] -> M w ()
                    g subst tvs = do
                      let info' = subst info
                          con' = subst con
                      -- typeMap %= Map.insert typ0 [con']
                      message 2 (pprint1 info')
                      -- message 2 ("doInfo NewtypeD con'=" ++ pprint1 (subst con))
                      f subst tvs (Right (TyConI (NewtypeD cx' tname tvs' mk con' deriv)))
          TyConI (DataD cx' tname tvs' mk cons deriv) -> do
            -- message 2 (intercalate "\n|  " ("-> DataD cons:" : fmap pprint1 cons))
            constraints %= (cx' ++)
            tyvars %= (tvs' ++)
            withBindings g
              where g :: SubstFn -> [TyVarBndr] -> M w ()
                    g subst tvs = do
                      let info' = subst info
                          cons' = subst cons
                      -- typeMap %= Map.insert typ0 cons'
                      message 2 (pprint1 info')
                      f subst tvs (Right (TyConI (DataD cx' tname tvs' mk cons' deriv)))
          PrimTyConI _ arity _ -> do
            message 2 (pprint1 info)
            -- Avoid further processing by discarding the appropriate
            -- number of type parameters?
            _ <- pop applied arity
            withBindings g
              where g :: SubstFn -> [TyVarBndr] -> M w ()
                    g subst tvs = indented 1 $ f subst tvs (Right info)
          FamilyI _dec _insts -> error "fixme - support type and data families"
          _ -> error (intercalate "\n|  "
                         ["withTypeExpansions - Unsupported Info:",
                          pprint1 info])

-- | Associate the type parameters on the 'applied' stack with the
-- type variables on the 'tyvars' stack.  Type parameters are obtained
-- from uses of type application by AppT, and type variables come from
-- the 'TyVarBndr' lists in a declaration.  This builds a 'SubstFn'
-- that expands all the bound type variables in a type expression,
-- along with a list of the bound type variables.  The action should
-- build its result using the writer monad of 'M'.
withBindings :: Monoid w => (SubstFn -> [TyVarBndr] -> M w ()) -> M w ()
withBindings action = indented 2 $ do
  np <- length <$> use applied
  nv <- length <$> use tyvars
  when (np > nv)
       (error ("withBindings - arity mismatch, not enough type variables"
               {- ++ ":\n\ttvs=" ++ show tvs ++ "\n\tparams=" ++ show params -}))
  params <- pop applied np
  -- Any excess type variables will be left in tyvars.
  bound <- pop tyvars np

  let bindings :: Map Name Type
      bindings = foldl addExpansion mempty (zip (fmap toName bound) params)

      addExpansion :: Map Name Type -> (Name, Type) -> Map Name Type
      addExpansion mp (name, expansion)
          | VarT name == expansion = mp
          | elem (VarT name) (filter (== (VarT name)) (gFind expansion :: [Type])) =
              error $ "Recursive type variable binding: " ++ show (name, expansion)
          | otherwise = Map.insert name (substMap mp expansion) mp

      substMap :: Map Name Type -> Type -> Type
      substMap mp typ = everywhere (mkT (substMap1 mp)) typ

      substMap1 :: Map Name Type -> Type -> Type
      substMap1 mp t@(VarT name) = maybe t id (Map.lookup name mp)
      substMap1 _ t = t

      subst :: forall b. Data b => b -> b
      subst typ = everywhere (mkT subst1) typ

      -- Apply the binding map expansions to one Type
      subst1 :: Type -> Type
      subst1 t@(VarT name) = maybe t id (Map.lookup name bindings)
      subst1 t = t

  when (not (Map.null bindings)) (message 2 (intercalate "\n  " ("withBindings:" : fmap (show . pprPair) (Map.toList bindings))))

  action subst bound

-- | A phantom type variable is one which is declared by the type but
-- is not used in any of the type's constructors.
data Phantom =
    Phantom
    { _phantom :: Set Name
    , _used :: Set Name
    } deriving (Data, Eq, Ord, Show)

instance Semigroup Phantom where
    -- a type variable is phantom until it shows up in either used set.
    Phantom p1 u1 <> Phantom p2 u2 =
        Phantom (Set.difference (Set.union p1 p2) u) u
        where u = Set.union u1 u2

instance Monoid Phantom where
    mempty = Phantom mempty mempty
    mappend = (<>)

-- | Return a list of unused type variables in a type expression.
-- This means using the Q monad to traverse down into the type
-- constructors to examine whether an actual field containing for the
-- variable is present.
phantom :: TypeQ -> Q Phantom
phantom typeq = runV 1 $ indented 1 $ do
  typ <- runQ typeq
  message 1 ("phantom1: " ++ pprint1 typ)
  withFree typeq (\typ' tvs -> do
                    tell (Phantom {_phantom = Set.fromList (fmap toName tvs), _used = mempty})
                    typeUsed (foldl AppT typ' (fmap (VarT . toName) tvs)))
     where
      -- Intersect all the phantom sets, union all the nonphantom sets
      typeUsed :: Type -> M Phantom ()
      typeUsed (VarT name) = tell (Phantom mempty (singleton name))
      typeUsed typ = do
        message 1 ("typeUsed " ++ pprint1 typ)
        indented 1 $ withTypeExpansions (\_subst _tvs info -> do
                                           message 1 ("expanded: " ++ either pprint1 pprint1 info)
                                           either typeUsed infoUsed info) typ

      infoUsed :: Info -> M Phantom ()
      infoUsed (TyConI dec) = decUsed dec
      infoUsed (PrimTyConI _ _ _) = pure ()
      -- infoUsed (FamilyI _dec insts)
      -- ClassI
      -- ClassOpI
      -- DataConI
      -- PatSynI
      -- VarI
      -- TyVarI
      infoUsed info = error ("phantom - unsupported Info: " ++ show info)

      decUsed (DataD _ _ _ _ cons _) = mapM_ conUsed cons
      decUsed (NewtypeD _ _ _ _ con _) = conUsed con
      decUsed (TySynD _name _tvs typ) = typeUsed typ
      decUsed dec = error ("phantom - unsupported Dec: " ++ pprint1 dec)

      conUsed :: Con -> M Phantom ()
      conUsed (NormalC _name types) = mapM_ (typeUsed . view _2) types
      conUsed (RecC _name types) = mapM_ (typeUsed . view _3) types
      conUsed (InfixC t1 _name t2) = typeUsed (view _2 t1) >> typeUsed (view _2 t2)
      conUsed (ForallC _tvs _cx con) = conUsed con
      conUsed (GadtC _names types typ) = mapM_ (typeUsed . view _2) types >> typeUsed typ
      conUsed (RecGadtC _names types typ) = mapM_ (typeUsed . view _3) types >> typeUsed typ
