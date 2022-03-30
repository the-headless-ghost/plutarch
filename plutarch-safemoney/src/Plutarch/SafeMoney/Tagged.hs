{-# LANGUAGE ViewPatterns #-}
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

import Data.Tagged
import Plutarch.Numeric
import Plutarch.Prelude
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
    (PlutusType, PIsData, PEq, POrd)
    via (DerivePNewtype (PTagged tag underlying) underlying)

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
