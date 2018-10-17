{-# LANGUAGE CPP #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# OPTIONS -Wall #-}

module Data.THUnify.Traverse
    ( SubstFn, InfoFn
    , withTypeExpansions
    , withBindings
    , withFree
    , Phantom(..)
    , phantom, phantom'
    -- * M monad
    , M, runM, runV, execM, execV, evalM, evalV
    -- * M monad state lenses
    , applied, tyvars, unbound, constraints, visitedNames, visitedTypes
    -- * M monad messaging
    , message, quietly, noisily, indented, pprint1, friendlyNames
    -- * Template Haskell helper functions
    , findTypeVars, toName
    ) where

import Control.Lens (_2, _3, (.=), (%=), at, Lens', lens, makeLenses, non, over, Traversal', use, view)
import Control.Monad (MonadPlus, msum, when)
import Control.Monad.Reader (local, MonadReader, ReaderT)
import Control.Monad.RWS (evalRWST, listens, {-local,-} RWST, tell)
import Control.Monad.Trans (MonadIO(liftIO))
import Data.Char (isSpace)
import Data.Data (Data)
import Data.Generics ({-Data,-} everywhere, listify, mkT, Typeable)
import Data.List (dropWhileEnd, intercalate)
import Data.Map as Map (insert, lookup, Map, null, toList)
import Data.Set as Set (difference, fromList, Set, singleton, toList, union, unions)
import Instances.TH.Lift ()
import Language.Haskell.TH
import Language.Haskell.TH.Instances ()
import Language.Haskell.TH.PprLib (Doc, hcat, hsep, ptext, to_HPJ_Doc)
import Language.Haskell.TH.Syntax
import qualified Text.PrettyPrint as HPJ
import System.IO (hPutStrLn, stderr)

-- | Make a template haskell value more human reader friendly.  The
-- result may or may not be compilable.  That's ok, though, because
-- the input is usually uncompilable - it imports hidden modules, uses
-- infix operators in invalid positions, puts module qualifiers in
-- places where they are not allowed, and maybe other things.
friendlyNames :: Data a => a -> a
friendlyNames =
    everywhere (mkT friendlyName)
    where
      friendlyName (Name x _) = Name x NameS -- Remove all module qualifiers

-- | Render a 'Doc' on a single line.
render1 :: Doc -> String
render1 = HPJ.renderStyle (HPJ.style {HPJ.mode = HPJ.OneLineMode}) . to_HPJ_Doc

-- | Render a 'Doc' with the given width.
renderW :: Int -> Doc -> String
renderW w = HPJ.renderStyle (HPJ.style {HPJ.lineLength = w}) . to_HPJ_Doc

-- | Pretty print the result of 'render1'.
pprint1' :: Ppr a => a -> [Char]
pprint1' = render1 . ppr

-- | 'pprint1'' with friendlyNames.
pprint1 :: (Ppr a, Data a) => a -> [Char]
pprint1 = pprint1' . friendlyNames

-- | Pretty print the result of 'renderW'.
pprintW' :: Ppr a => Int -> a -> [Char]
pprintW' w = renderW w . ppr

-- | 'pprintW'' with friendly names.
pprintW :: (Ppr a, Data a) => Int -> a -> [Char]
pprintW w = pprintW' w . friendlyNames

pprPair :: (Ppr a, Ppr b) => (a, b) -> Doc
pprPair (a, b) = hcat [ptext "(", ppr a, ptext ", ", ppr b, ptext ")"]

pprSet :: Ppr a => Set a -> Doc
pprSet s = hcat [ptext "[", hsep (fmap ppr (Set.toList s)), ptext "]"]

class HasMessageInfo a where
    verbosity :: Lens' a Int
    prefix :: Lens' a String

-- | Class of monads with a verbosity level and a stored indentation string.
class (HasMessageInfo r, MonadReader r m) => Verbosity r m where
  message :: Int -> String -> m ()
  -- ^ If the monad's verbosity level exceeds the verbosity argument,
  -- prepend the current indentation string to the lines of a message
  -- and output it.

instance (MonadIO m, HasMessageInfo r, Monoid w) => Verbosity r (RWST r w s m) where
  message minv s = do
    v <- view verbosity
    p <- view prefix
    when (v >= minv) $ (liftIO . hPutStrLn stderr . indent p) s

instance (MonadIO m, HasMessageInfo r) => Verbosity r (ReaderT r m) where
  message minv s = do
    v <- view verbosity
    p <- view prefix
    liftIO $ putStrLn ("v=" ++ show v ++ " vmin=" ++ show minv)
    when (v >= minv) $ (liftIO . putStrLn . indent p) s

-- | Indent the lines of a message with a prefix
indent :: String -> String -> String
indent pre s = intercalate "\n" $ fmap (dropWhileEnd isSpace . (pre ++)) (lines s)

-- | If the current verbosity level is >= minv perform the action with
-- additional indentation.
indented :: (HasMessageInfo r, MonadReader r m) => Int -> m a -> m a
indented minv action = do
  (v :: Int) <- view verbosity
  if v >= minv then local (over prefix ("  " ++)) action else action

-- | Perform the action with reduced verbosity
quietly :: (HasMessageInfo r, MonadReader r m) => Int -> m a -> m a
quietly n = local (over verbosity (\i -> i - n))

-- | Perform the action with increased verbosity
noisily :: (HasMessageInfo r, MonadReader r m) => Int -> m a -> m a
noisily n = local (over verbosity (+ n))

gFind :: (MonadPlus m, Data a, Typeable b) => a -> m b
gFind = msum . fmap return . listify (const True)

-- | Find all the type variables in a type - i.e. 'Type' values of the
-- form @VarT name@.
findTypeVars :: Data a => a -> Set Name
findTypeVars a = unions (fmap (\case VarT name -> singleton name; _ -> mempty) (gFind a :: [Type]))

-- | Copied from haskell-src-meta
class ToName a where toName :: a -> Name

instance ToName TyVarBndr where
  toName (PlainTV n) = n
  toName (KindedTV n _) = n

instance ToName VarStrictType where
  toName (n, _, _) = n

-- | A type with a HasMessageInfo instance, for use in the Reader or
-- RWS monad.  Also includes a stack of 'Type' we need to limit
-- recursion.
data R = R Int String [Type]

instance HasMessageInfo R where
    verbosity = lens (\(R v _ _) -> v) (\(R _ s e) v' -> R v' s e)
    prefix = lens (\(R _ s _) -> s) (\(R v _ e) s' -> R v s' e)

-- | Access recursion limiting stack
expanding :: Lens' R [Type]
expanding = lens (\(R _ _ e) -> e) (\(R v s _) e' -> R v s e')

data S w =
    S
    { _applied :: [Type]
    -- ^ Type parameters from decomposed type applications (AppT)
    , _tyvars :: [TyVarBndr]
    -- ^ Type variables collected from the Info record
    , _unbound :: Set TyVarBndr
    -- ^ Type variables from ForallT types
    , _constraints :: Cxt
    -- ^ Collected Cxt
    , _visitedNames :: Map Name (Maybe w)
    , _visitedTypes :: Map Type (Maybe w)
    -- ^ Used to limit repeat visits to types
    } deriving Show

{-
instance Semigroup S where
    (S a1 b1 c1 d1) <> (S a2 b2 c2 d2) =
        S (a1 <> a2) (b1 <> b2) (c1 <> c2) (d1 <> d2)
instance Monoid S where
    mappend = (<>)
    mempty = S mempty mempty mempty mempty
-}

$(makeLenses ''S)

type M w a = RWST R w (S w) Q a

runM :: Monoid w => M w a -> Q (a, w)
runM action = evalRWST action r0 s0

execM :: Monoid w => M w a -> Q w
execM action = snd <$> runM action

evalM :: Monoid w => M w a -> Q a
evalM action = fst <$> runM action

runV :: Monoid w => Int -> M w a -> Q (a, w)
runV n action = runM (noisily n action)

execV :: Monoid w => Int -> M w a -> Q w
execV n action = execM (noisily n action)

evalV :: Monoid w => Int -> M w a -> Q a
evalV n action = evalM (noisily n action)

r0 :: R
r0 = R 0 "" []

s0 :: S w
s0 = S mempty mempty mempty mempty mempty mempty

-- | Pop and return n items off a list in the state
pop :: Monoid w => Traversal' (S w) [a] -> Int -> M w [a]
pop lns n = do
  (popped, keep) <- splitAt n <$> use lns
  lns .= keep
  return popped

push :: Monoid w => Traversal' (S w) [a] -> [a] -> M w ()
push lns xs = lns %= (xs ++)

-- Type traversal code

type SubstFn = forall d. Data d => d -> d

type InfoFn w =
       SubstFn          -- The current type variable bindings
    -> [TyVarBndr]      -- The type variables that SubstFn will expand
    -> Either Type Info -- The current type's info record or fully expanded type expression
    -> M w ()

-- | If a type has a kind of order higher than *, apply a suitable
-- number of type variables and call f.
withFree :: forall w. (Monoid w, Eq w) => TypeQ -> (Type -> [TyVarBndr] -> M w ()) -> M w ()
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
withTypeExpansions :: forall w. (Monoid w, Eq w) => InfoFn w -> Type -> M w ()
withTypeExpansions f typ0 = indented 2 $ do
  r <- elem typ0 <$> view expanding
  vis <- use (visitedTypes . at typ0 . non Nothing)
  case (r, vis) of
    (False, Nothing) -> do
      message 2 ("Type: " ++ pprint1 typ0 ++ " (show: " ++ take 20 (show typ0) ++ "...)")
      visitedTypes %= Map.insert typ0 Nothing
      (r, w) <- listens id $ local (over expanding (typ0 :)) $ indented 2 $ doType typ0
      visitedTypes %= Map.insert typ0 (Just w)
      return r
    _ ->
      message 2 ("revisited: (" ++ pprint1 typ0 ++ ")")
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
#if 1
        qReify name >>= doInfo
#else
        vis <- use (visitedNames . at name)
        case vis of
          Nothing -> do
            -- Prevent repeat visits by caching a bogus result
            visitedNames %= Map.insert name Nothing
            (r, w) <- listens id (qReify name >>= doInfo)
            -- Cache the actual result (not sure we really need this)
            visitedNames %= Map.insert name (Just w)
            return r
          Just w -> return ()
#endif
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
                      message 2 ("NewtypeD: " ++ pprint1 info')
                      -- message 2 ("doInfo NewtypeD con'=" ++ pprint1 (subst con))
                      f subst tvs (Right (TyConI (NewtypeD cx' tname tvs' mk con' deriv)))
          TyConI (DataD cx' tname tvs' mk cons deriv) -> do
            -- message 0 (intercalate "\n|  " ("DataD cons:" : fmap pprint1 cons))
            constraints %= (cx' ++)
            tyvars %= (tvs' ++)
            withBindings g
              where g :: SubstFn -> [TyVarBndr] -> M w ()
                    g subst tvs = do
                      let info' = subst info
                          cons' = subst cons
                      -- typeMap %= Map.insert typ0 cons'
                      message 2 ("DataD: " ++ pprint1 info')
                      f subst tvs (Right (TyConI (DataD cx' tname tvs' mk cons' deriv)))
          PrimTyConI _ arity _ -> do
            message 2 ("PrimTyConI: " ++ pprint1 info)
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
  -- Any excess type variables or parameters are left in the stack
  params <- pop applied (min np nv)
  bound <- pop tyvars (min np nv)
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
phantom typeq = execM $ indented 1 $ phantom' typeq

phantom' :: TypeQ -> M Phantom ()
phantom' typeq = do

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
