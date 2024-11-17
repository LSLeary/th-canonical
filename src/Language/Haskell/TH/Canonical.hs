
-- --< Header >-- {{{

{-# LANGUAGE CPP, TemplateHaskell, QualifiedDo, RoleAnnotations
           , DerivingVia, DefaultSignatures, ViewPatterns
#-}

{- |

Description : Transform TH ASTs to canonical form.
Copyright   : (c) L. S. Leary, 2024

Transform TH ASTs to a canonical form suitable for comparison.

  * Rename internal variables consistently.
  * Strip exposed names of uniques.
  * Convert (pre-associated) infix to prefix.
  * Explicitly quantify tyvars wherever possible.
  * Disentangle GADT constructor tyvars.
  * Sort lists that are semantically sets.

-}

-- }}}

-- --< Exports & Imports >-- {{{

module Language.Haskell.TH.Canonical (

  -- * Canonising & Comparing TH ASTs
  canonical, (~),
  -- ** Equivalence
  Equivalence(..), (~~),
  -- *** Rendered
  Rendered, (<~>),
  raw, pretty,

  -- * Building Canonical TH ASTs
  Canon, runCanon,
  Canonical(..),

) where

-- base
import GHC.Generics hiding (SourceUnpackedness, SourceStrictness, Fixity)

import Foreign.ForeignPtr (ForeignPtr)
import Data.Word (Word8)
import Data.Char (ord, chr, isUpperCase, isLowerCase) --, isSymbol)
import Data.List (sort)
import Data.List.NonEmpty (NonEmpty)
import Data.Function (on)
import Data.Functor ((<&>))
import Data.Functor.Identity qualified
import Data.Foldable (fold)
import Numeric.Natural (Natural)

-- containers
import Data.Map.Strict qualified as M

-- transformers
import Control.Monad.Trans.Reader (Reader, ReaderT(..))

-- template-haskell
import Language.Haskell.TH
  ( Quote, Code, Ppr, pprint
  , Exp(..), Dec(..), Con(..), Pat(..), Type(..), Clause(..), Match(..), Body
  , Guard(PatG), Stmt(..), Lit, TyLit, TyVarBndr(..)
  , DerivStrategy, DerivClause, Overlap, Range, Role
  , SourceUnpackedness, SourceStrictness, Bang, Foreign, Callconv, Safety
  , Pragma, Inline, RuleMatch, Phases, RuleBndr, AnnTarget, FunDep
  , TypeFamilyHead(..), TySynEqn(..), FamilyResultSig(TyVarSig), InjectivityAnn
  , Fixity, FixityDirection, FieldExp, FieldPat
  , PatSynArgs(..), PatSynDir, Specificity(..)
#if MIN_VERSION_template_haskell(2,22,0)
  , NamespaceSpecifier
#endif
#if MIN_VERSION_template_haskell(2,21,0)
  , BndrVis
#endif
  )
import Language.Haskell.TH.Syntax
  (Lift, Name(..), mkName, nameBase, NameFlavour(..), ModName, Bytes)
import Language.Haskell.TH.CodeDo qualified as TH

-- th-canonical
import Data.Ordered.Set

-- }}}

-- --< Basic UI >-- {{{

-- | Take a TH AST to its canonical form.
canonical :: Canonical a => a -> a
canonical = runCanon . canon

-- | 'canonical' gives rise to an equivalence relation @~@ relating ASTs iff they share a canonical form.
(~) :: (Canonical a, Eq a) => a -> a -> Bool
(~) = (==) `on` canonical

-- | A less forgetful replacement for 'Bool'.
data Equivalence a = a :/= a | Equivalent a
  deriving (Lift, Show, Read, Eq, Ord, Functor, Foldable, Traversable)

-- | A variant of '~' that remembers the 'canonical' forms it computed.
(~~) :: (Canonical a, Eq a) => a -> a -> Equivalence a
(canonical -> x) ~~ (canonical -> y)
  | x == y    = Equivalent x
  | otherwise = x :/= y

type role Rendered nominal
data Rendered a = Rendered
  { raw_    :: String
  , pretty_ :: String
  } deriving (Lift, Eq, Ord)

render :: (Show a, Ppr a) => a -> Rendered a
render x = Rendered
  { raw_    = show x
  , pretty_ = pprint x
  }

-- | A variant of '~~' running at compile time.
(<~>)
  :: (Quote q, Canonical a, Eq a, Show a, Ppr a)
  => q a -> q a -> Code q (Equivalence (Rendered a))
qx <~> qy = TH.do
  x <- canonical <$> qx
  y <- canonical <$> qy
  let rx = render x
      ry = render y
  if x == y
    then [e|| Equivalent ry ||]
    else [e|| rx   :/=   ry ||]

raw    :: Rendered a -> String
raw    = raw_

pretty :: Rendered a -> String
pretty = pretty_

-- }}}

-- --< Canon >-- {{{

data Renaming = Renaming
  { renamed :: !(M.Map Name Name)
  , names   :: !Natural
  }

-- | A 'Monad' tracking the renaming state necessary for generating canonical TH ASTs.
newtype Canon a = Canon (Renaming -> a)
  deriving (Functor, Applicative, Monad)
    via CanonRep

type CanonRep = Reader Renaming

-- | Run 'Canon' with fresh renaming state.
runCanon :: Canon a -> a
runCanon (Canon s) = s Renaming{ renamed = M.empty, names = 0 }

asks :: (Renaming -> r) -> Canon r
asks = Canon

getRenamed :: Canon (Set Name)
getRenamed = asks (fromUnordered . M.keysSet . renamed)

toTVBs :: flag -> Set Name -> [TyVarBndr flag]
toTVBs s = fmap (flip PlainTV s) . toList

renamingAll :: Foldable f => f Name -> Canon a -> Canon a
renamingAll ns ca = foldr renaming ca ns

renaming :: Name -> Canon a -> Canon a
renaming n = local \rn@Renaming{renamed,names} -> if n `M.member` renamed
  then rn
  else Renaming
    { renamed = M.insert n (mkName (name names)) renamed
    , names   = names + 1
    }
 where
  local :: (Renaming -> Renaming) -> Canon a -> Canon a
  local f (Canon g) = Canon (g . f)

  -- Render naturals in lower-case alphabetic, shortest first.
  name :: Natural -> String
  name l = go [] (l - excess)
   where
    (ol, excess) = order l

    go ds 0 = reverse $ take ol (ds ++ repeat 'a')
    go ds k = case k `divMod` 26 of
      (q, r) -> go (char r:ds) q
     where
      char r = chr (fromIntegral r + ord 'a')

    order m = until (\(_, s) -> m < s) (\(o, s) -> (o+1, 26*(s + 1))) (1, 26)
      <&> \s -> (s `div` 26) - 1

-- }}}

-- --< Canonical >-- {{{

-- | Canonise a child node of a TH AST.
class Canonical a where
  canon :: a -> Canon a
  default canon :: (Generic a, Canonical' (Rep a)) => a -> Canon a
  canon = defCanon

-- --< Base >-- {{{

instance Canonical Word8          where canon = pure
instance Canonical Word           where canon = pure
instance Canonical (ForeignPtr a) where canon = pure
instance Canonical Char           where canon = pure
instance Canonical Int            where canon = pure
instance Canonical Integer        where canon = pure
instance Canonical Rational       where canon = pure

-- }}}

-- --< Tuples >-- {{{

instance Canonical ()
instance {-# OVERLAPPABLE #-} (Canonical a, Canonical b)
      => Canonical (a, b)
instance {-# OVERLAPPABLE #-} (Canonical a, Canonical b, Canonical c)
      => Canonical (a, b, c)

-- }}}

-- --< Traversables >-- {{{

instance Canonical a => Canonical (Maybe a) where
  canon = traverse canon

instance {-# OVERLAPPABLE #-} (Canonical a, Ord a) => Canonical [a] where
  canon = traverse canon
instance Canonical [Char] where canon = pure

instance (Canonical a, Ord a) => Canonical (NonEmpty a) where
  canon = traverse canon

-- }}}

-- --< Name >-- {{{

conid :: Name -> Bool
conid (nameBase -> c:_) = isUpperCase c || c == ':'
conid _                 = False

instance Canonical Name where
  canon n@(Name o nf) = case nf of
    NameG{}       -> pure n
    NameQ{}       -> pure n
    _ | conid n   -> pure (Name o NameS)
      | otherwise -> M.findWithDefault (Name o NameS) n <$> asks renamed

instance Canonical [Name] where
  canon = fmap sort . traverse canon

-- }}}

-- --< Dec >-- {{{

quantifyD :: Dec -> Dec
quantifyD = \case
  DataInstD    cxt mtvbs t mk cs dcs
    -> DataInstD    cxt (extend mtvbs ts) t mk cs dcs
   where ts = foldMap ftv cxt <> ftv t <> foldMap ftv mk
  NewtypeInstD cxt mtvbs t mk c  dcs
    -> NewtypeInstD cxt (extend mtvbs ts) t mk c  dcs
   where ts = foldMap ftv cxt <> ftv t <> foldMap ftv mk
  TySynInstD (TySynEqn mtvbs lhs rhs)
    -> TySynInstD (TySynEqn (extend mtvbs (ftv lhs)) lhs rhs)
  d -> d
 where
  extend mtvbs ts = if (not . null) tvbs then Just tvbs else Nothing
   where
    tvbs = fold mtvbs <> unbound
    unbound = toTVBs () (ts \\ foldMap bound (fold mtvbs))

instance Canonical Dec where
  canon d@(ValD _ _ ds) = bindingAll ds (defCanon d)
  canon d@(DataD cxt n tvbs mk cs dcs)
    | any gadt cs = do
      cs' <- canon (quantifyC <$> cs)
      bindingAll tvbs do
        DataD <$> canon cxt <*> canon n <*> canon tvbs
              <*> canon mk <*> pure cs' <*> canon dcs
    | otherwise   = defbndrs tvbs d
  canon d@(NewtypeD _ _ tvbs _ _ _) = defbndrs tvbs d
  canon d@(TypeDataD n tvbs mk cs)
    | any gadt cs = do
      cs' <- canon (quantifyC <$> cs)
      bindingAll tvbs do
        TypeDataD <$> canon n <*> canon tvbs <*> canon mk <*> pure cs'
    | otherwise   = defbndrs tvbs d
  canon d@(TySynD _   tvbs _  ) = defbndrs tvbs d
  canon d@(ClassD _ _ tvbs _ _) = defbndrs tvbs d
  canon d@(InstanceD _ _ t _  ) = defbndrs (ftv t) d
  canon   (SigD n t) = do
    t' <- quantify t
    defCanon (SigD n t')
  canon   (KiSigD n k) = do
    k' <- quantify k
    defCanon (KiSigD n k')
  canon   (DefaultD ts) = DefaultD <$> traverse canon ts
  canon d@(DataFamilyD _ tvbs _) = defbndrs tvbs d
  canon (quantifyD -> d@(DataInstD cxt mtvbs t mk cs dcs))
    | any gadt cs = do
      cs' <- canon (quantifyC <$> cs)
      bindingAll (fold mtvbs) do
        DataInstD <$> canon cxt <*> canon mtvbs <*> canon t
                  <*> canon mk <*> pure cs' <*> canon dcs
    | otherwise = defbndrs (fold mtvbs) d
  canon (quantifyD -> d@(NewtypeInstD _ mtvbs _ _ _ _))
    = defbndrs (fold mtvbs) d
  canon (quantifyD -> d@(TySynInstD _)) = defCanon d
  canon d@(OpenTypeFamilyD   tfh  ) = binding tfh (defCanon d)
  canon d@(ClosedTypeFamilyD tfh _) = binding tfh (defCanon d)
  canon d@(StandaloneDerivD _ cxt t)
    = defbndrs (ftv t <> foldMap ftv cxt) d
  canon   (PatSynD n args dir p) = do
    dir' <- canon dir
    let mkPS = PatSynD <$> canon n <*> canon args
                       <*> pure dir' <*> canon p
    case args of
      RecordPatSyn _ -> mkPS
      _              -> binding p mkPS
  canon   (PatSynSigD n uni@(ForallT u uc exi@(ForallT e ec t))) = do
    rn <- getRenamed
    let u_ = foldMap bound u <> ftv (resultT uni) \\ rn
        u' = toTVBs SpecifiedSpec u_
        e_ = foldMap bound e <> ftv exi \\ u_ \\ rn
        e' = toTVBs SpecifiedSpec e_
    bindingAll u_ do
      bindingAll e_ do
        defCanon (PatSynSigD n (ForallT u' uc (ForallT e' ec t)))
  canon d = defCanon d

resultT :: Type -> Type
resultT (   ArrowT              `AppT` _ `AppT` t) =   resultT t
resultT (MulArrowT `AppKindT` _ `AppT` _ `AppT` t) =   resultT t
resultT (ForallT    tvbs cxt t) = ForallT    tvbs cxt (resultT t)
resultT (ForallVisT tvbs     t) = ForallVisT tvbs     (resultT t)
resultT t                       =                              t

instance Canonical [Dec] where canon = fmap sort . traverse canon

instance Canonical  DerivStrategy
instance Canonical  DerivClause
instance Canonical [DerivClause] where canon = fmap sort . traverse canon

instance Canonical Overlap

-- }}}

-- --< Con >-- {{{

gadt :: Con -> Bool
gadt = \case
  GadtC{}       -> True
  RecGadtC{}    -> True
  ForallC _ _ c -> gadt c
  _             -> False

quantifyC :: Con -> Con
quantifyC = \case
  c@(GadtC    _  bts rt) | (not . null) unbound -> ForallC unbound [] c
   where
    unbound = toBind (snd <$> bts) rt
  c@(RecGadtC _ vbts rt) | (not . null) unbound -> ForallC unbound [] c
   where
    unbound = toBind (vbts <&> \(_, _, t) -> t) rt
  c -> c
 where
  toBind ts rt = toTVBs SpecifiedSpec (foldMap ftv ts <> ftv rt)

instance Canonical Con where
  canon   (ForallC tvbs1 cxt1 (ForallC tvbs2 cxt2 c))
    = canon (ForallC (tvbs1 <> tvbs2) (cxt1 <> cxt2) c)
  canon c@(ForallC tvbs _ _) = defbndrs tvbs c
  canon c = defCanon c

-- }}}

-- --< Clause, Source* & Foreign >-- {{{

instance Canonical Clause where
  canon c@(Clause ps _ ds) = bindingAll ps (bindingAll ds (defCanon c))

instance Canonical SourceUnpackedness
instance Canonical SourceStrictness
instance Canonical Bang

instance Canonical Foreign
instance Canonical Callconv
instance Canonical Safety

-- }}}

-- --< Pragmata >-- {{{

instance Canonical Pragma
instance Canonical Inline
instance Canonical RuleMatch
instance Canonical Phases
instance Canonical RuleBndr
instance Canonical AnnTarget

-- }}}

-- --< FunDeps & Type Families >-- {{{

instance Canonical  FunDep
instance Canonical [FunDep] where
  canon = fmap sort . traverse canon

instance Canonical TySynEqn where
  canon tse@(TySynEqn mtvbs lhs rhs) = bindingAll (fold mtvbs) do
    rn <- getRenamed
    let unbound = toTVBs () (ftv lhs \\ rn)
    if (not . null) unbound
      then bindingAll unbound do
        defCanon (TySynEqn (mtvbs <> Just unbound) lhs rhs)
      else do
        defCanon tse

instance Canonical TypeFamilyHead where
  canon tfh@(TypeFamilyHead _ _ _ _) = binding tfh (defCanon tfh)
instance Canonical FamilyResultSig
instance Canonical InjectivityAnn

-- }}}

-- --< Fixity & PatSyns >-- {{{

instance Canonical Fixity
instance Canonical FixityDirection

#if MIN_VERSION_template_haskell(2,22,0)
instance Canonical NamespaceSpecifier
#endif

instance Canonical PatSynDir
instance Canonical PatSynArgs where
  canon = \case
    PrefixPatSyn ns -> PrefixPatSyn <$> traverse canon ns
    RecordPatSyn ns -> RecordPatSyn <$> traverse canon ns
    i               -> defCanon i

-- }}}

-- --< Exp & co >-- {{{

instance Canonical Exp where
  canon (InfixE (Just l) op (Just r)) = do
    op' <- canon op
    l'  <- canon l
    r'  <- canon r
    pure (op' `AppE` l' `AppE` r')
  canon (InfixE (Just l) op Nothing) = do
    op' <- canon op
    l'  <- canon l
    pure (op' `AppE` l')
  canon e@(LamE ps _) = bindingAll ps (defCanon e)
  canon e@(LetE ds _) = bindingAll ds (defCanon e)
  canon e = defCanon e

instance Canonical Match where
  canon m@(Match p _ _) = binding p (defCanon m)

instance Canonical Body
instance Canonical Guard

instance {-# OVERLAPPING #-} Canonical (Guard, Exp) where
  canon t@(g, _) = binding g (defCanon t)

instance Canonical Stmt where
  canon (BindS p e) = do
    p' <- binding p (canon p)
    defCanon (BindS p' e)
  canon s = defCanon s
instance Canonical [Stmt] where
  canon [            ] = pure []
  canon (s@BindS{}:ss) = (:) <$> canon s <*> binding s (canon ss)
  canon (s        :ss) = binding s ((:) <$> defCanon s <*> canon ss)

instance Canonical Range
instance Canonical Lit
instance Canonical Bytes
instance Canonical ModName

-- }}}

-- --< Pat >-- {{{

instance Canonical Pat where
  canon (InfixP l op r) = ConP op [] <$> traverse canon [l, r]
  canon (ConP n ts ps)  = ConP <$> canon n <*> traverse canon ts <*> canon ps
  canon p = defCanon p

instance Canonical [FieldExp] where canon = fmap sort . traverse canon
instance Canonical [FieldPat] where canon = fmap sort . traverse canon

-- }}}

-- --< Type >-- {{{

quantify :: Type -> Canon Type
quantify t = do
  rn <- getRenamed
  let unbound = toTVBs SpecifiedSpec (ftv t \\ rn)
  pure $ if (not . null) unbound
    then ForallT unbound [] t
    else                    t

ftv :: Type -> Set Name
ftv = \case
  ForallT    tvbs cxt t -> (foldMap ftv cxt <> ftv t)
                        \\ foldMap bound tvbs
  ForallVisT tvbs     t -> ftv t \\ foldMap bound tvbs
  AppT f x              -> ftv f <> ftv x
  AppKindT t k          -> ftv t <> ftv k
  SigT t k              -> ftv t <> ftv k
  VarT n                -> singleton n
  InfixT  l n r         -> (if tyvarid n then singleton n else mempty)
                        <> ftv l <> ftv r
  UInfixT l n r         -> (if tyvarid n then singleton n else mempty)
                        <> ftv l <> ftv r
  PromotedInfixT  l _ r -> ftv l <> ftv r
  PromotedUInfixT l _ r -> ftv l <> ftv r
  ParensT t             -> ftv t
  ImplicitParamT _ t    -> ftv t
  _                     -> mempty

tyvarid :: Name -> Bool
tyvarid (Name _ NameG{})  = False
tyvarid (Name _ NameQ{})  = False
tyvarid (nameBase -> c:_) = isLowerCase c || c == '_'
tyvarid _                 = False

instance Canonical Type where
  canon f@(ForallT    tvbs _ _) = defbndrs tvbs f
  canon f@(ForallVisT tvbs _  ) = defbndrs tvbs f
  canon (InfixT l op r) = do
    op' <- canon op
    l'  <- canon l
    r'  <- canon r
    pure $ (if tyvarid op then VarT else ConT) op' `AppT` l' `AppT` r'
  canon (PromotedInfixT l op r) = do
    op' <- canon op
    l'  <- canon l
    r'  <- canon r
    pure $ PromotedT op' `AppT` l' `AppT` r'
  canon t = defCanon t

instance Canonical [Type] where canon = fmap sort . traverse canon

instance Canonical flag => Canonical (TyVarBndr flag)
instance Canonical TyLit
instance Canonical Role
instance Canonical Specificity
#if MIN_VERSION_template_haskell(2,21,0)
instance Canonical BndrVis
#endif

-- }}}

-- }}}

-- --< Binder >-- {{{

binding :: Binder b => b -> Canon a -> Canon a
binding = renamingAll . bound

bindingAll :: (Foldable f, Binder b) => f b -> Canon a -> Canon a
bindingAll = renamingAll . foldMap bound

defbndrs
  :: (Foldable f, Binder b, Generic a, Canonical' (Rep a))
  => f b -> a -> Canon a
defbndrs bs = bindingAll bs . defCanon

class Binder b where
  bound :: b -> Set Name

instance Binder Name where
  bound = singleton

instance Binder Dec where
  bound = \case
    FunD n _   -> singleton n
    ValD p _ _ -> bound p
    _          -> mempty

instance Binder Guard where
  bound = \case
    PatG ss -> foldMap bound ss
    _       -> mempty

instance Binder Stmt where
  bound = \case
    BindS p _ -> bound p
    LetS ds   -> foldMap bound ds
    ParS sss  -> (foldMap . foldMap) bound sss
    RecS ss   -> foldMap bound ss
    _         -> mempty

instance Binder Pat where
  bound = \case
    WildP             -> mempty
    LitP _            -> mempty
#if MIN_VERSION_template_haskell(2,22,0)
    TypeP  t          -> ftv t
    InvisP t          -> ftv t
#endif
    VarP n            -> singleton n
    UnboxedSumP p _ _ -> bound p
    ParensP     p     -> bound p
    TildeP      p     -> bound p
    BangP       p     -> bound p
    SigP        p t   -> bound p <> ftv t
    ViewP _     p     -> bound p
    AsP  n      p     -> singleton n <> bound p
    InfixP      l _ r -> bound l <> bound r
    UInfixP     l _ r -> bound l <> bound r
    TupP        ps    -> foldMap bound ps
    UnboxedTupP ps    -> foldMap bound ps
    ConP _ ts   ps    -> foldMap ftv ts <> foldMap bound ps
    ListP       ps    -> foldMap bound ps
    RecP _     fps    -> foldMap (bound . snd) fps

instance Binder (TyVarBndr flag) where
  bound = \case
    PlainTV  n _   ->           singleton n
    KindedTV n _ k -> ftv k <> singleton n

instance Binder TypeFamilyHead where
  bound = \case
    TypeFamilyHead _ tvbs frs _ -> foldMap bound tvbs <> bound frs

instance Binder FamilyResultSig where
  bound = \case
    TyVarSig tvb -> bound tvb
    _            -> mempty

-- }}}

-- --< Generics >-- {{{

defCanon :: (Generic a, Canonical' (Rep a)) => a -> Canon a
defCanon = fmap to . canon' . from

class Canonical' f where
  canon' :: f p -> Canon (f p)

instance Canonical' V1 where
  canon' = \case

instance Canonical' U1 where
  canon' = pure

instance (Canonical' f, Canonical' g) => Canonical' (f :+: g) where
  canon' = \case
    L1 fp -> L1 <$> canon' fp
    R1 gp -> R1 <$> canon' gp

instance (Canonical' f, Canonical' g) => Canonical' (f :*: g) where
  canon' (fp :*: gp) = (:*:) <$> canon' fp <*> canon' gp

instance Canonical c => Canonical' (K1 i c) where
  canon' (K1 c) = K1 <$> canon c

instance Canonical' f => Canonical' (M1 i t f) where
  canon' (M1 fp) = M1 <$> canon' fp

-- }}}

