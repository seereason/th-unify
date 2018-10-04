{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# OPTIONS -Wall #-}

module Data.THUnify.Prelude.TH
    ( decomposeType
    , composeType
    , unlifted
    , lookupTypeNameUnsafe
    , lookupValueNameUnsafe
    , lookupTypeUnsafe
    , lookupValueUnsafe
    , lookupConUnsafe
    , fieldType
    , FieldInfo(..)
    , fieldTypeConPos
    , tupleTypes
    , typeCons
    , conInfo
    , nameBasePlus
    , typeFromName
    , simpleClassInsts
    , liftType'
    , constructorName
    , declarationName
    , declarationType
    , unReify
    , ToName(toName)
    , typeConstructors
    , noLoc
    , tells
    , here
    , scrubLocs
    ) where

import Control.Lens (_1, view)
import Control.Monad.Writer (MonadWriter, tell)
import Data.Generics (Data, everywhere, mkT)
import Data.ListLike (findIndex)
import Data.Maybe (fromMaybe)
import Language.Haskell.TH.Instances ()
import Data.THUnify.Prelude.Ppr (pprint1)
import Language.Haskell.TH

import Language.Haskell.TH.Syntax

-- | Copied from haskell-src-meta
class ToName a where toName :: a -> Name

instance ToName TyVarBndr where
  toName (PlainTV n) = n
  toName (KindedTV n _) = n

instance ToName Con where
    toName (ForallC _ _ con) = toName con
    toName (NormalC cname _) = cname
    toName (RecC cname _) = cname
    toName (InfixC _ cname _) = cname
#if MIN_VERSION_template_haskell(2,11,0)
    toName (GadtC _ _ _) = error "toName - GADTs unsupported"
    toName (RecGadtC _ _ _) = error "toName - GADTs unsupported"
#endif

instance ToName VarStrictType where
  toName (n, _, _) = n

decomposeType :: Type -> [Type]
decomposeType t0 = (go t0 [])
          where go (AppT t1 t2) ts = go t1 (t2 : ts)
                go t ts = t : ts

-- | Turn a type parameter list into type applications
composeType :: [Type] -> Type
composeType ts = foldl1 AppT ts

unReify :: Data a => a -> a
unReify = everywhere (mkT unReifyName)

unReifyName :: Name -> Name
unReifyName = mkName . nameBase

#if 1
unlifted :: Quasi m => Type -> m Bool
unlifted typ =
    case decomposeType typ of
      ConT tname : tparams -> qReify tname >>= goInfo tparams
      [ListT, a] -> unlifted a
      (TupleT _ : tparams) -> or <$> mapM unlifted tparams
      [VarT _] -> return False
      _ -> error $ "unlifted - unexpected parameter: " ++ show typ
    where
      goInfo _ (PrimTyConI _ _ _) = return True
      goInfo tparams _ = or <$> mapM unlifted tparams
#else
class OverTypes t where
    overTypes :: Quasi m => (a -> Either Info Type -> m a) -> a -> t -> m a

-- | Perform a fold over the Type and Info values embedded in t
class OverTypes t where
    overTypes :: Quasi m => (a -> Either Info Type -> m a) -> a -> t -> m a

instance OverTypes Dec where
#if MIN_VERSION_template_haskell(2,11,0)
    overTypes f a (DataD _ _ _ _mk cons _) = foldM (overTypes f) a cons
    overTypes f a (NewtypeD _ _ _ _mk con _) = overTypes f a con
#else
    overTypes f a (DataD _ _ _ cons _) = foldM (overTypes f) a cons
    overTypes f a (NewtypeD _ _ _ con _) = overTypes f a con
#endif
    overTypes f a (TySynD _ _ typ) = overTypes f a typ
    overTypes _ a _ = return a

instance OverTypes StrictType where
    overTypes f a (_, t) = overTypes f a t

instance OverTypes VarStrictType where
    overTypes f a (_, _, t) = overTypes f a t

instance OverTypes Con where
    overTypes f a (ForallC _ _ con) = overTypes f a con
    overTypes f a (NormalC _ ts) = foldM (overTypes f) a ts
    overTypes f a (RecC _ ts) = foldM (overTypes f) a ts
    overTypes f a (InfixC t1 _ t2) = overTypes f a t1 >>= flip (overTypes f) t2

instance OverTypes Type where
    overTypes f a t@(AppT t1 t2) = f a (Right t) >>= flip (overTypes f) t1 >>= flip (overTypes f) t2
    overTypes f a (ConT name) = qReify name >>= overTypes f a
    overTypes f a t@(ForallT _ _ typ) = f a (Right t) >>= flip (overTypes f) typ
    overTypes f a t = f a (Right t)

instance OverTypes Info where
    overTypes f a x = f a (Left x)

-- | Does the type or the declaration to which it refers contain a
-- primitive (aka unlifted) type?  This will traverse down any 'Dec'
-- to the named types, and then check whether any of their 'Info'
-- records are 'PrimTyConI' values.
unlifted :: (OverTypes t, Quasi m) => t -> m Bool
unlifted x = overTypes f False x
    where
      f _ (Left (PrimTyConI _ _ _)) = return True
      f r _ = return r
#endif

lookupTypeNameUnsafe :: String -> Q Name
lookupTypeNameUnsafe name = fromMaybe (error ("Type name not in scope: " ++ show name)) <$> lookupTypeName name

lookupValueNameUnsafe :: String -> Q Name
lookupValueNameUnsafe name = fromMaybe (error ("Value name not in scope: " ++ show name)) <$> lookupValueName name

lookupTypeUnsafe :: String -> TypeQ
lookupTypeUnsafe name = lookupTypeNameUnsafe name >>= conT

lookupValueUnsafe :: String -> ExpQ
lookupValueUnsafe name = lookupValueNameUnsafe name >>= varE

lookupConUnsafe :: String -> ExpQ
lookupConUnsafe name = lookupValueNameUnsafe name >>= conE

-- | Return a field's type and parent type name.  This will not work
-- with type parameters.
fieldType :: Name -> Q (Maybe (Type, Name))
fieldType fname = reify fname >>= goInfo
    where
      goInfo :: Info -> Q (Maybe (Type, Name))
#if MIN_VERSION_template_haskell(2,11,0)
      goInfo (VarI _fname (AppT (AppT ArrowT (ConT tname)) ftype) _) = pure (Just (ftype, tname))
#else
      goInfo (VarI _fname (AppT (AppT ArrowT (ConT tname)) ftype) _ _) = pure (Just (ftype, tname))
#endif
      goInfo _info = pure Nothing -- error $ "fieldType - unexpected info: " ++ pprint1 info ++ "\n  " ++ show info

--                tname cct  cname  cpos  fct  ftype fpos
data FieldInfo = FieldInfo Name Int (Name, Int) Int (Type, Int) deriving Show

-- | Return a field's parent type name, constructor name, constructor arity, field position and type
fieldTypeConPos :: Name -> Q (Maybe FieldInfo)
fieldTypeConPos fname = fieldType fname >>= maybe (pure Nothing) (\(ftype, tname) -> reify tname >>= goInfo ftype tname)
    where
      goInfo :: Type -> Name -> Info -> Q (Maybe FieldInfo)
#if MIN_VERSION_template_haskell(2,11,0)
      goInfo ftype tname info@(TyConI (DataD _ _tname _ _ cons _)) = goCons ftype tname info (length cons) (zip [1..] cons)
      goInfo ftype tname info@(TyConI (NewtypeD _ _tname _ _ con _)) = goCons ftype tname info 1 (zip [1..] [con])
#else
      goInfo ftype tname info@(TyConI (DataD _ _tname _ cons _)) = goCons ftype tname info (length cons) (zip [1..] cons)
      goInfo ftype tname info@(TyConI (NewtypeD _ _tname _ con _)) = goCons ftype tname info 1 (zip [1..] [con])
#endif
      goInfo _ftype _tname info = error $ "fieldTypeConPos - unexpected Info: " ++ pprint info
      goCons :: Type -> Name -> Info -> Int -> [(Int, Con)] -> Q (Maybe FieldInfo)
      goCons ftype tname info cct ((cpos, ForallC _ _ con) : more) = goCons ftype tname info cct ((cpos, con) : more)
      goCons ftype tname _info cct ((cpos, RecC cname binds) : _)
          | any ((== fname) . view _1) binds =
              pure (Just (FieldInfo tname cct (cname, cpos) (length binds) (ftype, (fpos binds))))
      goCons ftype tname info cct (_ : more) = goCons ftype tname info cct more
      goCons _ftype _tname _cct _info [] = pure Nothing
      fpos :: [VarStrictType] -> Int
      fpos binds = length (takeWhile ((/= fname) . view _1) binds) + 1

tupleTypes :: Type -> Q [Type]
tupleTypes typ0 = goType typ0 []
    where
      goType (ForallT _binds _cxt typ) args = goType typ args
      goType (AppT a b) args = goType a (b : args)
      goType (TupleT n) args | n /= length args = error $ "tupleTypes - arity error: " ++ show typ0
      goType (TupleT _) args = pure args
      goType _ _ = error $ "tupleTypes - not a tuple: " ++ pprint1 typ0

typeCons :: Name -> Q [Con]
typeCons tname = reify tname >>= goInfo
    where
#if MIN_VERSION_template_haskell(2,11,0)
      goInfo (TyConI (DataD _ _ _ _ cons _)) = pure cons
      goInfo (TyConI (NewtypeD _ _ _ _ con _)) = pure [con]
#else
      goInfo (TyConI (DataD _ _ _ cons _)) = pure cons
      goInfo (TyConI (NewtypeD _ _ _ con _)) = pure [con]
#endif
      goInfo _ = error "typeCons - expected DataD or NewtypeD"

-- | Return the information about a constructor - the type name, its
-- position in the type's constructor list, and the types of its
-- fields.
conInfo :: Name -> Q (Maybe (Name, Int, Int, [Type]))
conInfo cname = reify cname >>= goInfo
    where
#if MIN_VERSION_template_haskell(2,11,0)
      goInfo (DataConI _cname fields tname) = goFields tname fields []
#else
      goInfo (DataConI _cname fields tname _fixity) = goFields tname fields []
#endif
      goInfo _info = pure Nothing
      -- Collect the field types
      goFields :: Name -> Type -> [Type] -> Q (Maybe (Name, Int, Int, [Type]))
      goFields tname (AppT (AppT ArrowT fld) more) flds = goFields tname more (fld : flds)
      goFields tname (ForallT _binds _ typ) flds = goFields tname typ flds
      goFields tname _returntype flds = reify tname >>= goType >>= \(cct, cpos) -> pure (Just (tname, cct, cpos, reverse flds))
#if MIN_VERSION_template_haskell(2,11,0)
      goType (TyConI (DataD _ tname _ _ cons _)) = pure (length cons, succ (e1 tname (findIndex ((== cname) . constructorName) cons)))
      goType (TyConI (NewtypeD _ _tname _ _ _con _)) = pure (1, 1)
#else
      goType (TyConI (DataD _ tname _ cons _)) = pure (length cons, succ (e1 tname (findIndex ((== cname) . constructorName) cons)))
      goType (TyConI (NewtypeD _ _tname _ _con _)) = pure (1, 1)
#endif
      goType info = error $ "conTypes - unexpected info: " ++ pprint1 info
      e1 _ (Just r) = r
      e1 tname Nothing = error $ "Type " ++ show tname ++ " has no constructor " ++ show cname

typeFromName :: Name -> Q Type
typeFromName tname = reify tname >>= goInfo
    where
#if MIN_VERSION_template_haskell(2,11,0)
      goInfo (TyConI (DataD _cxt _tname binds _ _cons _sups)) = foldl appT (conT tname) (map bindType binds)
      goInfo (TyConI (NewtypeD _cxt _tname binds _ _con _sups)) = foldl appT (conT tname) (map bindType binds)
#else
      goInfo (TyConI (DataD _cxt _tname binds _cons _sups)) = foldl appT (conT tname) (map bindType binds)
      goInfo (TyConI (NewtypeD _cxt _tname binds _con _sups)) = foldl appT (conT tname) (map bindType binds)
#endif
      goInfo (TyConI (TySynD _tname binds typ)) = foldl appT (pure typ) (map bindType binds)
      goInfo info = error $ "typeFromName - unexpected info: " ++ show info
      bindType :: TyVarBndr -> TypeQ
      bindType (PlainTV name) = varT name
      bindType (KindedTV name StarT) = varT name
      bindType tvb = error $ "typeFromName - unexpected type variable: " ++ show tvb

nameBasePlus :: Name -> String
nameBasePlus (Name (OccName name) NameS) = name
nameBasePlus (Name (OccName name) (NameU _)) = name
nameBasePlus (Name (OccName name) (NameL _)) = name
nameBasePlus (Name (OccName name) (NameQ (ModName modname))) = modname ++ "." ++ name
nameBasePlus (Name (OccName name) (NameG _ _ (ModName modname))) = modname ++ "." ++ name

-- | Retrieve every instance type of a class.  Assumes the class has
-- no type parameters.
simpleClassInsts :: Quasi m => Name -> m [Type]
simpleClassInsts clsName = do
  ClassI _ insts <- runQ $ reify clsName
#if MIN_VERSION_template_haskell(2,11,0)
  return $ fmap (\(InstanceD _ _ (AppT _ typ) _) -> typ) insts
#else
  return $ fmap (\(InstanceD _ (AppT _ typ) _) -> typ) insts
#endif

-- | Like lift, but names are obtained using lookupTypeUnsafe,
-- which uses lookupTypeName.  (Now I forget why this matters.)
liftType' :: Type -> ExpQ
liftType' (AppT a b) = [|appT $(liftType' a) $(liftType' b)|]
liftType' (ConT name) = [|lookupTypeUnsafe $(lift (nameBase name))|]
liftType' (TupleT n) = [|tupleT $(lift n)|]
liftType' ListT = [|listT|]
liftType' typ = error $ "liftType' - unexpected type: " ++ pprint1 typ ++ "\n  " ++ show typ

-- instance Lift Char where
--     lift c = litE (charL c)

constructorName :: Con -> Name
constructorName = toName

declarationName :: Dec -> Maybe Name
declarationName (FunD name _) = Just name
declarationName (ValD _pat _body _decs) = Nothing
#if MIN_VERSION_template_haskell(2,11,0)
declarationName (DataD _ name _ _ _ _) = Just name
declarationName (NewtypeD _ name _ _ _ _) = Just name
#else
declarationName (DataD _ name _ _ _) = Just name
declarationName (NewtypeD _ name _ _ _) = Just name
#endif
declarationName (TySynD name _ _) = Just name
declarationName (ClassD _ name _ _ _) = Just name
#if MIN_VERSION_template_haskell(2,11,0)
declarationName (InstanceD _ _ _ _) = Nothing
#else
declarationName (InstanceD _ _ _) = Nothing
#endif
declarationName (SigD name _) = Just name
declarationName (ForeignD _) = Nothing
declarationName (InfixD _ name) = Just name
declarationName (PragmaD _) = Nothing
#if MIN_VERSION_template_haskell(2,11,0)
declarationName (DataFamilyD _name _ _) = Nothing
declarationName (OpenTypeFamilyD _head) = Nothing
declarationName (DataInstD _ name _ _ _ _) = Just name
declarationName (NewtypeInstD _ name _ _ _ _) = Just name
declarationName (ClosedTypeFamilyD (TypeFamilyHead name _ _ _) _) = Just name
#else
declarationName (FamilyD _ _name _ _) = Nothing
declarationName (DataInstD _ name _ _ _) = Just name
declarationName (NewtypeInstD _ name _ _ _) = Just name
declarationName (ClosedTypeFamilyD name _ _ _) = Just name
#endif
declarationName (TySynInstD name _) = Just name
declarationName (RoleAnnotD name _) = Just name
#if MIN_VERSION_template_haskell(2,12,0)
declarationName (StandaloneDerivD _ _ _) = Nothing
#else
declarationName (StandaloneDerivD _ _) = Nothing
#endif
declarationName (DefaultSigD name _) = Just name

declarationType :: Dec -> Maybe Type
declarationType = fmap ConT . declarationName

typeConstructors :: Type -> Q [Con]
typeConstructors typ =
    doType typ
    where
      doType (AppT a _) = doType a
      doType (TupleT _) = pure []
      doType ListT = pure []
      doType (ConT tname) = reify tname >>= doInfo
      doType typ' = error $ "typeConstructors - unexpected Type: " ++ pprint1 typ' ++ "\n  " ++ show typ'
      doInfo (TyConI dec) = doDec dec
      doInfo info = error $ "typeConstructors - unexpected Info: " ++ pprint1 info ++ "\n  " ++ show info
#if MIN_VERSION_template_haskell(2,11,0)
      doDec (DataD _ _ _ _ cons _) = pure cons
      doDec (NewtypeD _ _ _ _ con _) = pure [con]
#else
      doDec (DataD _ _ _ cons _) = pure cons
      doDec (NewtypeD _ _ _ con _) = pure [con]
#endif
      doDec (TySynD _ _ typ') = doType typ'
      doDec dec = error $ "typeConstructors - unexpected Dec: " ++ pprint1 dec ++ "\n  " ++ show dec

noLoc :: Loc
noLoc = Loc "" "" "" (0, 0) (0, 0)

-- | Tell a list of DecQ to a [Dec] writer monad.
tells :: (Quasi m, MonadWriter [Dec] m) => [DecQ] -> m ()
tells decqs = runQ (sequence decqs) >>= tell

here :: ExpQ
here = location >>= lift

-- | Erase location information that changes constantly
scrubLocs :: forall a. Data a => a -> a
scrubLocs =
    everywhere (mkT scrub)
    where
      scrub :: Loc -> Loc
      scrub l = l {loc_filename = "", loc_module = "", loc_package = "", loc_start=(0,0), loc_end=(0,0)}
