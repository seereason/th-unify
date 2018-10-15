{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeSynonymInstances #-}

module Data.THUnify.Monad
    ( -- * Template haskell pretty printing styles
      friendlyNames
    , render1
    , renderW
    , pprint1'
    , pprint1
    , pprintW'
    , pprintW
    , pprPair
    , pprSet
    -- * MonadReader support for debugging output
    , HasMessageInfo(..)
    , Verbosity(..)
    , indented
    , quietly
    , noisily
    -- * Template haskell helper function
    , ToName(toName)
    -- * Generic find
    , gFind
    , findTypeVars
    -- * The M monad, with its Reader and State types
    , R(..), expanding
    , S(..), applied, tyvars, unbound, constraints
    , M
    , runM, runV
    , push, pop
    ) where

import Control.Lens ((%=), (.=), Lens', lens, makeLenses, over, Traversal', use, view)
import Control.Monad (MonadPlus, msum, when)
import Control.Monad.Reader (local, MonadReader, ReaderT)
import Control.Monad.RWS (evalRWST, RWST)
import Control.Monad.Trans (MonadIO(liftIO))
import Data.Char (isSpace)
import Data.Data (Data)
import Data.Generics (everywhere, listify, mkT, Typeable)
import Data.List (dropWhileEnd, intercalate)
import Data.Set as Set (Set, singleton, toList, unions)
import Instances.TH.Lift ()
import Language.Haskell.TH
import Language.Haskell.TH.PprLib (Doc, hcat, hsep, ptext, to_HPJ_Doc)
import Language.Haskell.TH.Syntax as TH (Name(Name), NameFlavour(NameS))
import Prelude hiding ((<>))
import qualified Text.PrettyPrint as HPJ
import Prelude hiding ((<>))
import Language.Haskell.TH.Instances ()
import Language.Haskell.TH.Syntax
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

data S =
    S
    { _applied :: [Type]
    -- ^ Type parameters from decomposed type applications (AppT)
    , _tyvars :: [TyVarBndr]
    -- ^ Type variables collected from the Info record
    , _unbound :: Set TyVarBndr
    -- ^ Type variables from ForallT types
    , _constraints :: Cxt
    -- ^ Collected Cxt
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

type M w a = RWST R w S Q a

runM :: Monoid w => M w () -> Q w
runM action = snd <$> evalRWST action r0 s0

r0 :: R
r0 = R 0 "" []

s0 :: S
s0 = S mempty mempty mempty mempty

runV :: Monoid w => Int -> M w () -> Q w
runV n action = runM (noisily n action)

-- | Pop and return n items off a list in the state
pop :: Monoid w => Traversal' S [a] -> Int -> M w [a]
pop lns n = do
  (popped, keep) <- splitAt n <$> use lns
  lns .= keep
  return popped

push :: Monoid w => Traversal' S [a] -> [a] -> M w ()
push lns xs = lns %= (xs ++)
