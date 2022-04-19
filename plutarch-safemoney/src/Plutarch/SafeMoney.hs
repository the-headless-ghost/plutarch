{-# LANGUAGE PolyKinds #-}

{- |
Module     : Plutarch.SafeMoney
Maintainer : emi@haskell.fyi
Description: Phantom-type tagged types for handling assets in Plutus.

Phantom-type tagged types for handling assets in Plutus.
-}
module Plutarch.SafeMoney (
  -- * Tagged data types
  Tagged.PTagged,
  Tagged.ptag,
  Tagged.puntag,
  Tagged.pretag,

  -- * Reexports from "Data.Tagged"
  Tagged.Tagged (..),
  Tagged.untag,
  Tagged.retag,

  -- * Numeric type aliases
  PDiscrete,
  PDense,

  -- * Conversions
  pdiscreteValue,
  pdiscreteValue',
  pvalueDiscrete,
  pvalueDiscrete',
) where

import Prelude hiding (Num (..))

--------------------------------------------------------------------------------

import Plutus.V1.Ledger.Value (AssetClass (AssetClass))

import Plutarch.Api.V1 (PValue)
import Plutarch.Builtin ()
import Plutarch.Prelude

--------------------------------------------------------------------------------

import Plutarch.Api.V1.Extra (PAssetClass, passetClass, passetClassValue, passetClassValueOf, psingletonValue)

import Plutarch.SafeMoney.Tagged (PTagged, Tagged (Tagged))
import Plutarch.SafeMoney.Tagged qualified as Tagged

type PDiscrete tag = PTagged tag PInteger
type PDense tag = PTagged tag PRational

--------------------------------------------------------------------------------

{- | Downcast a 'PValue' to a 'PDiscrete' unit, providing a witness of the 'PAssetClass'.

     @since 0.3
-}
pvalueDiscrete ::
  forall (tag :: Type) (s :: S).
  Term s (PAssetClass :--> PValue :--> PDiscrete tag)
pvalueDiscrete = phoistAcyclic $
  plam $ \ac f ->
    Tagged.ptag $ passetClassValueOf # f # ac

{- | Downcast a 'PValue' to a 'PDiscrete' unit, providing a witness of the 'AssetClass', which gets inlined. If you use this 'AssetClass' twice, prefer 'pvalueDiscrete'.

     @since 0.3
-}
pvalueDiscrete' ::
  forall (tag :: Type) (s :: S).
  Tagged tag AssetClass ->
  Term s (PValue :--> PDiscrete tag)
pvalueDiscrete' (Tagged (AssetClass (cs, tn))) = phoistAcyclic $
  plam $ \f ->
    Tagged.ptag $ passetClassValueOf # f #$ passetClass # pconstant cs # pconstant tn

{- | Get a 'PValue' from a 'PDiscrete', providing a witness of the 'AssetClass'.
     __NOTE__: `pdiscreteValue` after `pvalueDiscrete` is not a round-trip.
     It filters for a particular tag.

     @since 0.3
-}
pdiscreteValue ::
  forall (tag :: Type) (s :: S).
  Term s (PAssetClass :--> PDiscrete tag :--> PValue)
pdiscreteValue = phoistAcyclic $
  plam $ \ac p ->
    passetClassValue
      # ac
      # Tagged.puntag p

{- | Get a 'PValue' from a 'PDiscrete', providing a witness of the 'AssetClass'.
     __NOTE__: `pdiscreteValue` after `pvalueDiscrete` is not a round-trip.
     It filters for a particular tag.

     If you use this 'AssetClass' twice, prefer 'pvalueDiscrete'.

     @since 0.3
-}
pdiscreteValue' ::
  forall (tag :: Type) (s :: S).
  Tagged tag AssetClass ->
  Term s (PDiscrete tag :--> PValue)
pdiscreteValue' (Tagged (AssetClass (cs, tn))) = phoistAcyclic $
  plam $ \p ->
    psingletonValue
      # pconstant cs
      # pconstant tn
      # Tagged.puntag p
