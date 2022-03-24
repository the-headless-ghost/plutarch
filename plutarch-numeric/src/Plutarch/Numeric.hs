{-# LANGUAGE Trustworthy #-}

{- | Module: Plutarch.Numeric
 Copyright: (C) MLabs 2022
 License: MIT
 Maintainer: Koz Ross <koz@mlabs.city>
 Portability: GHC only
 Stability: Experimental

 Improved numerical hierarchy.
-}
module Plutarch.Numeric (
  -- * Types

  -- ** Haskell
  Nat.Natural,
  NZN.NZNatural,
  NZI.NZInteger,
  Rat.Ratio,

  -- ** Plutarch
  Nat.PNatural,
  NZN.PNZNatural,
  NZI.PNZInteger,
  Rat.PRatio,

  -- ** Helpers
  Monoidal.Additive (..),
  Monoidal.Multiplicative (..),

  -- * Type classes

  -- ** Additive
  Additive.AdditiveSemigroup (..),
  Additive.AdditiveMonoid (..),
  Additive.AdditiveGroup (..),
  Additive.AdditiveCMM (..),

  -- ** Multiplicative
  Multiplicative.MultiplicativeSemigroup (..),
  Multiplicative.MultiplicativeMonoid (..),

  -- ** Combination
  Combination.Distributive (..),
  Combination.RemoveZero (..),
  Combination.PRemoveZero (..),
  Combination.Euclidean (..),
  Combination.Arithmetical (..),
  Combination.Divisible (..),

  -- ** Fraction-related

  -- *** Haskell
  Fractional.Fractionable (..),

  -- *** Plutarch
  Fractional.PFractionable (..),

  -- * Functions

  -- ** Reductions

  -- *** Haskell
  Monoidal.sum1,
  Monoidal.product1,
  Monoidal.sum,
  Monoidal.product,
  Monoidal.sumNZ,
  Monoidal.productNZ,

  -- *** Plutarch
  Monoidal.psum,
  Monoidal.pproduct,
  Monoidal.psumNZ,
  Monoidal.pproductNZ,

  -- ** Scaling
  Monoidal.scaleNZNatural,
  Monoidal.scaleNatural,
  Monoidal.scaleInteger,

  -- ** Exponentiation
  Monoidal.powNZNatural,
  Monoidal.powNatural,
  Monoidal.powInteger,
  Monoidal.powIntegerZero,

  -- ** Conversions

  -- *** Haskell
  Nat.toNatural,
  Nat.toAbsNatural,

  -- *** Plutarch
  Nat.ptoNatural,
  Nat.ptoAbsNatural,

  -- ** Fraction-related

  -- *** Haskell
  Rat.ratio,
  Rat.numerator,
  Rat.denominator,

  -- *** Plutarch
  Rat.pconRatio,
  Rat.pnumerator,
  Rat.pdenominator,
  Rat.pmatchRatio,
  Rat.pmatchRatios,
) where

import qualified Plutarch.Numeric.Additive as Additive
import qualified Plutarch.Numeric.Combination as Combination
import qualified Plutarch.Numeric.Fractional as Fractional
import qualified Plutarch.Numeric.Monoidal as Monoidal
import qualified Plutarch.Numeric.Multiplicative as Multiplicative
import qualified Plutarch.Numeric.NZInteger as NZI
import qualified Plutarch.Numeric.NZNatural as NZN
import qualified Plutarch.Numeric.Natural as Nat
import qualified Plutarch.Numeric.Ratio as Rat
