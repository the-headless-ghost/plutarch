{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE PolyKinds    #-}
{-# OPTIONS_GHC -Wno-orphans #-}

{- |
Module     : Plutarch.SafeMoney.Tagged
Maintainer : emi@haskell.fyi
Description: On-chain Tagged equivalent.

On-chain Tagged equivalent. "Data.Tagged" has (something like):
@
data 'Tagged' t a = 'Tagged' a
@

In order for it to exist on-chain,
we can simply make it a 'PlutusType' by adding @s :: 'S'@:
@
data PTagged t a (s :: S) = PTagged (Term s a)
@

Following this, it's possible to rewrite a number of
the "Data.Tagged" utils in terms of Plutarch code.
-}
module Plutarch.SafeMoney.Tagged (
  module Data.Tagged,
  PTagged (..),
  pretag,
  puntag,
  ptag,
) where

import Control.Arrow (first)
import Data.Tagged
import Plutarch.Lift (PConstantDecl (PConstantRepr, PConstanted, pconstantFromRepr, pconstantToRepr), PUnsafeLiftDecl (..))
import Plutarch.Numeric
import Plutarch.Prelude
import Plutarch.Show (PShow (pshow'))
import Plutarch.TryFrom (PTryFrom (..))
import Plutarch.Unsafe (punsafeCoerce)
import PlutusTx qualified
import Prelude hiding (Fractional (..), Num (..), quot, rem)

--------------------------------------------------------------------------------
-- Data.Tagged orphans.
-- The only alternative way to solve this is to use our own version of 'Tagged'.
-- Even Tagged from "plutus-ledger-api" doesn't have ToData instances.

deriving newtype instance
  PlutusTx.ToData underlying =>
  PlutusTx.ToData (Tagged tag underlying)

deriving newtype instance
  PlutusTx.FromData underlying =>
  PlutusTx.FromData (Tagged tag underlying)

deriving newtype instance
  PlutusTx.UnsafeFromData underlying =>
  PlutusTx.UnsafeFromData (Tagged tag underlying)

--------------------------------------------------------------------------------

{- | A Plutarch-level 'Tagged'.

     @since 0.3
-}
newtype PTagged tag (underlying :: PType) (s :: S)
  = PTagged (Term s underlying)
  deriving
    ( -- | @since 0.3
      PlutusType
    , -- | @since 0.3
      PIsData
    , -- | @since 0.3
      PEq
    , -- | @since 0.3
      POrd
    )
    via (DerivePNewtype (PTagged tag underlying) underlying)

{- | No checks performed on this 'PTryFrom', since the structure is identical.
     This primarily allows types which want to implement 'PTryFrom' to work.

     @since 0.3
-}
deriving via
  DerivePNewtype (PTagged tagged underlying) underlying
  instance
    PTryFrom a underlying =>
    PTryFrom a (PTagged tagged underlying)

{- | No checks performed on this 'PTryFrom', since the structure is identical.
     This primarily allows types which want to implement 'PTryFrom' to work.

     @since 0.3
-}
instance
  PTryFrom PData (PAsData underlying) =>
  PTryFrom PData (PAsData (PTagged tag underlying))
  where
  -- The excess is just whatever the underlying excess would be.
  type
    PTryFromExcess PData (PAsData (PTagged tag underlying)) =
      PTryFromExcess PData (PAsData underlying)
  ptryFrom' d k =
    ptryFrom' @_ @(PAsData underlying) d $
      -- JUSTIFICATION:
      -- We are coercing from @PAsData underlying@ to @PAsData (PTagged tag underlying)@.
      -- Since 'PTagged' is a simple newtype, their shape is the same.
      k . first punsafeCoerce

instance PUnsafeLiftDecl a => PUnsafeLiftDecl (PTagged t a) where
  type PLifted (PTagged t a) = Tagged t (PLifted a)

instance PConstantDecl a => PConstantDecl (Tagged t a) where
  type PConstantRepr (Tagged t a) = PConstantRepr a
  type PConstanted (Tagged t a) = PTagged t (PConstanted a)
  pconstantToRepr (Tagged t) = pconstantToRepr t
  pconstantFromRepr = fmap Tagged . pconstantFromRepr

{- | PShow defers to underlying type. Behaves similarly to Show instance
     of 'Tagged'.
     @since 0.3
-}
instance PShow a => PShow (PTagged tag a) where
  pshow' True inner = "(" <> pshow' False inner <> ")"
  pshow' False inner = "PTagged" <> " " <> pshow' True (puntag inner)

{- | Change the tag on a 'PTagged'. Plutarch-level equivalent of 'retag'.

     @since 0.3
-}
pretag :: forall t' t a s. Term s (PTagged t a) -> Term s (PTagged t' a)
pretag = punsafeCoerce

{- | Strip the tag off a 'PTagged'. Plutarch-level equivalent of 'untag'.

     @since 0.3
-}
puntag :: Term s (PTagged t a) -> Term s a
puntag = punsafeCoerce

{- | Smart constructor for 'PTagged'.
     Plutarch-level equivalent of 'Tagged' constructor.
     The reason this exists is because @'pcon' ('PTagged' @tag x)@ is longer
     and less readable than @'ptag' @tag x@.

     @since 0.3
-}
ptag :: forall t a s. Term s a -> Term s (PTagged t a)
ptag = punsafeCoerce

--------------------------------------------------------------------------------
-- Safely lift any Tagged with a closed operation.

-- | Internal helper function for instances.
liftTagged0 ::
  Term s underlying ->
  Term s (PTagged tag underlying)
liftTagged0 a =
  pcon (PTagged a)

-- | Internal helper function for instances.
liftTagged1 ::
  (Term s underlying -> Term s underlying) ->
  Term s (PTagged tag underlying) ->
  Term s (PTagged tag underlying)
liftTagged1 f x =
  pmatch x $ \(PTagged x') -> pcon . PTagged . f $ x'

-- | Internal helper function for instances.
liftTagged2 ::
  (Term s underlying -> Term s underlying -> Term s underlying) ->
  Term s (PTagged tag underlying) ->
  Term s (PTagged tag underlying) ->
  Term s (PTagged tag underlying)
liftTagged2 f x y =
  pmatch x $ \(PTagged x') ->
    pmatch y $ \(PTagged y') ->
      pcon . PTagged $ x' `f` y'

instance
  forall tag (underlying :: PType) (s :: S).
  AdditiveSemigroup (Term s underlying) =>
  AdditiveSemigroup (Term s (PTagged tag underlying))
  where
  (+) = liftTagged2 (+)

instance
  forall tag (underlying :: PType) (s :: S).
  AdditiveMonoid (Term s underlying) =>
  AdditiveMonoid (Term s (PTagged tag underlying))
  where
  zero = liftTagged0 zero

instance
  forall tag (underlying :: PType) (s :: S).
  AdditiveGroup (Term s underlying) =>
  AdditiveGroup (Term s (PTagged tag underlying))
  where
  (-) = liftTagged2 (-)
  negate = liftTagged1 negate

instance
  forall tag (underlying :: PType) (s :: S).
  AdditiveCMM (Term s underlying) =>
  AdditiveCMM (Term s (PTagged tag underlying))
  where
  (^-) = liftTagged2 (^-)

instance
  forall tag (underlying :: PType) (s :: S).
  MultiplicativeSemigroup (Term s underlying) =>
  MultiplicativeSemigroup (Term s (PTagged tag underlying))
  where
  (*) = liftTagged2 (*)

instance
  forall tag (underlying :: PType) (s :: S).
  MultiplicativeMonoid (Term s underlying) =>
  MultiplicativeMonoid (Term s (PTagged tag underlying))
  where
  one = ptag one
  abs = ptag . abs . puntag
  signum = ptag . signum . puntag

instance
  forall tag (underlying :: PType) (s :: S).
  Distributive (Term s underlying) =>
  Distributive (Term s (PTagged tag underlying))
  where
  fromNZNatural = pcon . PTagged . fromNZNatural

instance
  forall tag (a :: PType) (nz :: PType) (s :: S).
  Euclidean (Term s a) (Term s nz) =>
  Euclidean (Term s (PTagged tag a)) (Term s (PTagged tag nz))
  where
  (puntag -> a) +^ (puntag -> nz) = ptag (a +^ nz)
  (puntag -> a) *^ (puntag -> nz) = ptag (a *^ nz)
  (puntag -> a) `quot` (puntag -> nz) = ptag (a `quot` nz)
  (puntag -> a) `rem` (puntag -> nz) = ptag (a `rem` nz)
  fromNatural = ptag . fromNatural

instance
  forall tag (a :: PType) (nz :: PType) (s :: S).
  Divisible (Term s a) (Term s nz) =>
  Divisible (Term s (PTagged tag a)) (Term s (PTagged tag nz))
  where
  reciprocal (puntag -> nz) = ptag (reciprocal nz)
  (puntag -> a) / (puntag -> nz) = ptag (a / nz)
