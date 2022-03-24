{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE QualifiedDo #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}

{- | Module: Plutarch.Categories.Extra

Sourced from:
  https://gist.github.com/gnumonik/a9fde9fec6a0317e8dc1b99e6b0eaca1
See Sean Hunter:
  https://mlabs-corp.slack.com/archives/C02QQHLFB6Y/p1647023854211549
-}
module Plutarch.Categories.Extra (module Plutarch.Categories.Extra) where

import Data.Kind (Constraint)
import qualified GHC.Generics as GHC
import qualified Generics.SOP as SOP
import Plutarch (pcon', pmatch')
import Plutarch.Api.V1 (PMaybeData (..))
import Plutarch.Api.V1.AssocMap (PMap (PMap))
import Plutarch.DataRepr (PDataFields (..), PIsDataReprInstances (..))
import Plutarch.Lift (PUnsafeLiftDecl)
import Plutarch.Monadic as P

pidentity :: Term s (a :--> a)
pidentity = phoistAcyclic $ plam id

-- i was going to make PCategory and PProfunctor but that seemed like a bridge too far
(#.) :: Term s (b :--> c) -> Term s (a :--> b) -> Term s (a :--> c)
f #. g = goCompose # f # g
  where
    goCompose :: forall s a b c. Term s ((b :--> c) :--> (a :--> b) :--> (a :--> c))
    goCompose = phoistAcyclic $
      plam $ \bc ->
        plam $ \ab ->
          plam $ \a ->
            bc # (ab # a)
infixr 9 #.

{- PIDENTITY + PCONST  -}
newtype PIdentity (a :: PType) (s :: S) = PIdentity (Term s a)

prunIdentity :: Term s (PIdentity a :--> a)
prunIdentity = phoistAcyclic $
  plam $ \i -> pmatch i $ \case
    PIdentity x -> x

instance PlutusType (PIdentity a) where
  type PInner (PIdentity a) b = ((a :--> b) :--> b)
  pcon' (PIdentity x) = plam $ \f -> f # x

  pmatch' x f = x # plam (f . PIdentity)

-- PDIdentity; `Data` encoded identity

pdidentity :: PIsData a => (Term s (a :--> PDIdentity a))
pdidentity = phoistAcyclic $ plam $ \a -> pcon . PDIdentity $ pdcons # pdata a # pdnil

data PDIdentity (a :: PType) (s :: S)
  = PDIdentity (Term s (PDataRecord '["_0" ':= a]))
  deriving stock (GHC.Generic)
  deriving anyclass (SOP.Generic, PIsDataRepr)
  deriving (PlutusType, PIsData, PDataFields) via PIsDataReprInstances (PDIdentity a)

prunDIdentity :: PIsData a => (Term s (PDIdentity a :--> a))
prunDIdentity = phoistAcyclic $
  plam $ \i ->
    P.do
      PDIdentity r <- pmatch i
      pfield @"_0" # r

-- PConst

newtype PConst (a :: PType) (b :: PType) (s :: S) where
  PConst :: {getPConst :: Term s a} -> PConst a b s

pgetConst :: forall a s b. Term s (PConst a b :--> a)
pgetConst = phoistAcyclic $
  plam $ \cnst -> pmatch cnst $ \case
    PConst t -> t

instance Semigroup (Term s a) => Semigroup (Term s (PConst a b)) where
  a <> b = pcon $ PConst ((pgetConst # a) <> (pgetConst # b))

instance Monoid (Term s a) => Monoid (Term s (PConst a b)) where
  mempty = pcon $ PConst mempty

class (forall (s :: S). Monoid (Term s t)) => PMonoidal t
instance (forall (s :: S). Monoid (Term s t)) => PMonoidal t

instance PlutusType (PConst a b) where
  type PInner (PConst a _) c = ((a :--> c) :--> c)

  pcon' (PConst x) = plam $ \f -> f # x

  pmatch' x f = x # plam (f . PConst)

{-
    FUNCTOR
-}

type FunctorC :: (PType -> PType) -> PType -> Constraint
type FunctorC f t = (PFunctor f, FunctorConstraint f t)

type PFunctor :: (PType -> PType) -> Constraint
class PFunctor f where
  type FunctorConstraint f (a :: PType) :: Constraint

  pfmap :: (FunctorConstraint f a, FunctorConstraint f b) => Term s ((a :--> b) :--> f a :--> f b)

-- PIdentity
instance PFunctor PIdentity where
  type FunctorConstraint PIdentity _ = ()

  pfmap = phoistAcyclic $
    plam $ \f ia ->
      pmatch ia $ \case
        PIdentity x -> pcon $ PIdentity (f # x)

-- PDIdentity

instance PFunctor PDIdentity where
  type FunctorConstraint PDIdentity a = PIsData a

  pfmap = phoistAcyclic $
    plam $ \f ia -> P.do
      let a = prunDIdentity # ia
      pcon . PDIdentity $ pdcons # (pdata $ f # a) # pdnil

-- PConst
instance PFunctor (PConst a) where
  type FunctorConstraint (PConst a) _ = ()

  pfmap = phoistAcyclic $
    plam $ \_ cab -> pmatch cab $ \case
      PConst t -> pcon (PConst t)

-- PMaybe
instance PFunctor PMaybe where
  type FunctorConstraint PMaybe _ = ()

  pfmap = phoistAcyclic $
    plam $ \f ma ->
      pmatch ma $ \case
        PJust x -> pcon $ PJust (f # x)
        PNothing -> pcon PNothing

instance PFunctor PMaybeData where
  type FunctorConstraint PMaybeData a = (PIsData a)

  pfmap = phoistAcyclic $
    plam $ \f maybeA ->
      P.do
        pmatch maybeA $ \case
          PDNothing _ -> pcon . PDNothing $ pdnil
          PDJust a' -> P.do
            let a = pfield @"_0" # a'
            pcon . PDJust $ pdcons # pdata (f # a) # pdnil

-- PList
instance PFunctor PList where
  type FunctorConstraint PList a = PElemConstraint PList a
  pfmap = pmap

-- PBuiltinList
instance PFunctor PBuiltinList where
  type FunctorConstraint PBuiltinList a = PElemConstraint PBuiltinList a
  pfmap = pmap

-- PPair
instance PFunctor (PPair a) where
  type FunctorConstraint (PPair a) b = ()
  pfmap = phoistAcyclic $
    plam $ \f pair ->
      pmatch pair $ \case
        PPair a b -> pcon $ PPair a (f # b)

-- PEither
instance PFunctor (PEither l) where
  type FunctorConstraint (PEither l) _ = ()
  pfmap = phoistAcyclic $
    plam $ \f e -> pmatch e $ \case
      PLeft l -> pcon $ PLeft l
      PRight r -> pcon $ PRight (f # r)

{-
    APPLICATIVE
-}

type ApplicativeC :: (PType -> PType) -> PType -> Constraint
type ApplicativeC f a = (FunctorConstraint f a, ApplicativeConstraint f a)

type PApplicative :: (PType -> PType) -> Constraint
class PFunctor f => PApplicative f where
  type ApplicativeConstraint f (a :: PType) :: Constraint

  ppure :: ApplicativeC f a => Term s (a :--> f a)

  pliftA2 :: (ApplicativeC f x, ApplicativeC f y, ApplicativeC f z) => Term s ((x :--> y :--> z) :--> f x :--> f y :--> f z)

  (#<*>) :: (ApplicativeC f (a :--> b), ApplicativeC f a, ApplicativeC f b) => Term s (f (a :--> b)) -> Term s (f a) -> Term s (f b)
  fab #<*> fa = pliftA2 # pidentity # fab # fa

-- fixity?

instance PApplicative PIdentity where
  type ApplicativeConstraint PIdentity _ = ()

  ppure = phoistAcyclic $ plam $ \x -> pcon $ PIdentity x

  pliftA2 = phoistAcyclic $ plam $ \f a b -> pcon $ PIdentity (f # (prunIdentity # a) # (prunIdentity # b))

instance PApplicative PDIdentity where
  type ApplicativeConstraint PDIdentity a = PIsData a

  ppure = phoistAcyclic $ plam $ \x -> pcon . PDIdentity $ pdcons # pdata x # pdnil

  pliftA2 ::
    ( ApplicativeC PDIdentity x
    , ApplicativeC PDIdentity y
    , ApplicativeC PDIdentity z
    ) =>
    Term s ((x :--> y :--> z) :--> PDIdentity x :--> PDIdentity y :--> PDIdentity z)
  pliftA2 = phoistAcyclic $
    plam $ \f ia ib -> P.do
      let a = prunDIdentity # ia
          b = prunDIdentity # ib
      pcon . PDIdentity $ pdcons # pdata (f # a # b) # pdnil

instance PApplicative (PConst a) where
  type ApplicativeConstraint (PConst a) b = (PMonoidal a)

  ppure = phoistAcyclic $ plam $ \_ -> pcon $ PConst mempty

  pliftA2 = phoistAcyclic $ plam $ \_ a b -> pcon $ PConst (pgetConst # a <> pgetConst # b)

-- PMaybe
instance PApplicative PMaybe where
  type ApplicativeConstraint PMaybe _ = ()
  ppure = phoistAcyclic $ plam $ \x -> pcon (PJust x)

  pliftA2 = phoistAcyclic $
    plam $ \f ma mb ->
      pmatch ma $ \case
        PNothing -> pcon PNothing
        PJust x -> pmatch mb $ \case
          PJust y -> pcon $ PJust (f # x # y)
          PNothing -> pcon PNothing

instance PApplicative PMaybeData where
  type ApplicativeConstraint PMaybeData a = (PIsData a)
  ppure = phoistAcyclic $ plam $ \x -> pcon . PDJust $ pdcons # pdata x # pdnil

  pliftA2 = phoistAcyclic $
    plam $ \f ma mb ->
      pmatch ma $ \case
        PDNothing _ -> pcon $ PDNothing pdnil
        PDJust x -> pmatch mb $ \case
          PDJust y ->
            pcon . PDJust $
              pdcons
                # pdata
                  ( f
                      # (pfield @"_0" # x)
                      # (pfield @"_0" # y)
                  )
                # pdnil
          PDNothing _ -> pcon $ PDNothing pdnil

instance PApplicative PList where
  type ApplicativeConstraint PList _ = ()
  ppure = psingleton

  -- this might be really inefficient?
  pliftA2 = phoistAcyclic $
    plam $ \f ->
      pfix #$ plam $ \self xs ys ->
        pif
          (pnull # xs)
          pnil
          (pconcat # (pfmap # (f #$ phead # xs) # ys) # (self # (ptail # xs) # ys))

instance PApplicative PBuiltinList where
  type ApplicativeConstraint PBuiltinList _ = ()
  ppure = psingleton

  -- this might be really inefficient?
  pliftA2 = phoistAcyclic $
    plam $ \f ->
      pfix #$ plam $ \self xs ys ->
        pif
          (pnull # xs)
          pnil
          (pconcat # (pfmap # (f #$ phead # xs) # ys) # (self # (ptail # xs) # ys))

{-
    BIFUNCTOR
-}
type PBiFunctor :: (PType -> PType -> PType) -> Constraint
class PBiFunctor f where
  pbimap :: Term s ((x :--> a) :--> (y :--> b) :--> f x y :--> f a b)

-- PConst
instance PBiFunctor PConst where
  pbimap = phoistAcyclic $
    plam $ \f _ pc ->
      pmatch pc $ \case
        PConst t -> pcon $ PConst (f # t)

-- PPair
instance PBiFunctor PPair where
  pbimap = phoistAcyclic $
    plam $ \f g pair ->
      pmatch pair $ \case
        PPair a b -> pcon $ PPair (f # a) (g # b)

-- PEither
instance PBiFunctor PEither where
  pbimap = phoistAcyclic $
    plam $ \f g e ->
      pmatch e $ \case
        PLeft l -> pcon $ PLeft (f # l)
        PRight r -> pcon $ PRight (g # r)

pfirst :: (PBiFunctor f) => Term s ((x :--> a) :--> f x y :--> f a y)
pfirst = phoistAcyclic $ plam $ \f b -> pbimap # f # pidentity # b

psecond :: (PBiFunctor f) => Term s ((y :--> b) :--> f x y :--> f x b)
psecond = phoistAcyclic $ plam $ \f b -> pbimap # pidentity # f # b

{-
    FOLDABLE
-}
type PFoldable :: (PType -> PType) -> Constraint
class PFoldable f where
  type PFoldableConstraint f (a :: PType) :: Constraint
  pfoldL :: PFoldableConstraint f a => Term s ((b :--> a :--> b) :--> b :--> f a :--> b)

instance PFoldable PIdentity where
  type PFoldableConstraint PIdentity _ = ()

  pfoldL = phoistAcyclic $ plam $ \f b i -> f # b #$ prunIdentity # i

instance PFoldable PDIdentity where
  type PFoldableConstraint PDIdentity (a :: PType) = PIsData a
  pfoldL = phoistAcyclic $ plam $ \f b i -> f # b #$ prunDIdentity # i

instance PFoldable (PConst a) where
  type PFoldableConstraint (PConst a) _ = (PMonoidal a)
  pfoldL = phoistAcyclic $ plam $ \_ e _ -> e

instance PFoldable PList where
  type PFoldableConstraint PList a = PElemConstraint PList a
  pfoldL = pfoldl

instance PFoldable PBuiltinList where
  type PFoldableConstraint PBuiltinList a = PElemConstraint PBuiltinList a
  pfoldL = pfoldl

instance PFoldable (PMap k) where
  type PFoldableConstraint (PMap k) v = (PElemConstraint PBuiltinList (PBuiltinPair (PAsData k) (PAsData v)), PIsData v)
  pfoldL = phoistAcyclic $
    plam $ \f b m -> pmatch m $ \case
      PMap l -> pfoldl # (go #. f) # b # l
    where
      go :: PFoldableConstraint (PMap k) a => Term s ((a :--> b) :--> (PBuiltinPair (PAsData k) (PAsData a) :--> b))
      go = plam $ \g pair ->
        g # pfromData (psndBuiltin # pair)

instance PFoldable PMaybe where
  type PFoldableConstraint PMaybe _ = ()
  pfoldL = phoistAcyclic $
    plam $ \f b m -> pmatch m $ \case
      PJust a -> f # b # a
      PNothing -> b

instance PFoldable PMaybeData where
  type PFoldableConstraint PMaybeData a = (PIsData a)

  pfoldL = phoistAcyclic $
    plam $ \f b m ->
      P.do
        pmatch m $ \case
          PDNothing _ -> b
          PDJust a' -> P.do
            let a = pfield @"_0" # a'
            f # b # a

{-
    TRAVERSABLE
-}

type PTraverseC :: (PType -> PType) -> (PType -> PType) -> PType -> PType -> Constraint
type PTraverseC t f a b =
  ( PApplicative f
  , ApplicativeC f b
  , ApplicativeC f (t b)
  , PFoldableConstraint t a
  , PTraversableConstraint t f a b
  -- , PUnsafeLiftDecl a -- See note below.
  -- , PUnsafeLiftDecl b -- Note, Peter 2022-03-18; this constraint probably shouldn't be necessary
  -- I don't seem to be able to implement what I need for builtin list without it
  )

class (PFunctor t, PFoldable t) => PTraversable t where
  type PTraversableConstraint t (f :: PType -> PType) (a :: PType) (b :: PType) :: Constraint
  ptraverse :: PTraverseC t f a b => Term s ((a :--> f b) :--> t a :--> f (t b))

instance PTraversable PIdentity where
  type PTraversableConstraint PIdentity _ _ _ = ()
  ptraverse = phoistAcyclic $ plam $ \f i -> pfmap # ppure #$ f #$ prunIdentity # i

instance PTraversable PDIdentity where
  type PTraversableConstraint PDIdentity _ a b = (PIsData a, PIsData b)
  ptraverse = phoistAcyclic $ plam $ \f i -> pfmap # ppure #$ f #$ prunDIdentity # i

instance PTraversable (PConst a) where
  type PTraversableConstraint (PConst a) _ _ _ = ()
  ptraverse = phoistAcyclic $ plam $ \_ ta -> ppure #$ pcon $ PConst (pgetConst # ta)

instance PTraversable PMaybe where
  type PTraversableConstraint (PMaybe) _ _ _ = ()
  ptraverse = phoistAcyclic $
    plam $ \f ta -> pmatch ta $ \case
      PJust a -> pfmap # ppure #$ f # a
      PNothing -> ppure # pcon PNothing

instance PTraversable PMaybeData where
  type PTraversableConstraint PMaybeData f a b = (PIsData a, PIsData b)
  ptraverse = phoistAcyclic $
    plam $ \f ta -> pmatch ta $ \case
      PDJust recordA -> P.do
        let a = pfield @"_0" # recordA
        pfmap # ppure #$ f # a
      PDNothing _ -> ppure # pcon (PDNothing pdnil)

instance PTraversable PBuiltinList where
  type PTraversableConstraint PBuiltinList f a b = (PElemConstraint PBuiltinList b, PUnsafeLiftDecl b)
  ptraverse = phoistAcyclic $
    plam $ \f l -> P.do
      let pcons_f = plam $ \x ys -> pliftA2 # pcons # (f # x) # ys
      (pfoldr # pcons_f #$ ppure # pnil) # l

-- finish this tomorrow

pflip :: Term s ((a :--> b :--> c) :--> b :--> a :--> c)
pflip = phoistAcyclic $ plam $ \f b a -> f # a # b

{- Note, Peter 2022-03-18: Commenting these out to
turn off development builds.

-- type checking / inference "tests"
aList = pconstant ([1, 2, 3] :: [Integer])

aMaybe = pcon $ PJust (pconstant @PInteger 2)

add1 :: (FunctorC f PInteger) => Term s (f PInteger :--> f PInteger)
add1 = phoistAcyclic $ plam $ \fx -> pfmap # plam (+ 1) # fx

add2 :: (FunctorC f PInteger) => Term s (f PInteger :--> f PInteger)
add2 = phoistAcyclic $ plam $ \fx -> pfmap # plam (+ 2) # fx

add3 :: (FunctorC f PInteger) => Term s (f PInteger :--> f PInteger)
add3 = add1 #. add2

hm1 = add1 # aList

hm2 = add1 # aMaybe

notAnInt :: Term s (PConst PUnit PInteger)
notAnInt = pcon $ PConst (pcon PUnit)

notABool :: Term s (PConst PUnit PBool)
notABool = pcon $ PConst (pcon PUnit)

aFunction :: Term s (PInteger :--> PBool :--> PString)
aFunction = undefined

hm = pliftA2 # aFunction # notAnInt # notABool
-}
