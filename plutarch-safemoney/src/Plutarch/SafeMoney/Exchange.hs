{-# LANGUAGE ScopedTypeVariables #-}

{- |
Module     : Plutarch.SafeMoney.Exchange
Maintainer : emi@haskell.fyi
Description: Phantom-type tagged types for handling assets in Plutus.

Phantom-type tagged types for handling assets in Plutus.
-}
module Plutarch.SafeMoney.Exchange (
  (:>),
  exchange,
  exchangeFrom,
) where

import Prelude hiding (Fractional (..), Num (..))

import Plutarch.Numeric
import Plutarch.Prelude
import Plutarch.SafeMoney.Tagged (PTagged (..), pretag, ptag, puntag)

{- | Represents an exchange from a to b.

     Let's say 1.00 ADA is worth 2.00 USD, then @ADA ':>' USD@ ought to be represented as 2.00.
-}
data (:>) a b

-- | Create an exchange given an example relation.
exchange :: Term s (PTagged a PInteger :--> PTagged b PNZNatural :--> PTagged (a :> b) (PRatio PInteger))
exchange =
  phoistAcyclic $
    plam $ \a b ->
      ptag $ pconRatio (puntag a) (puntag b)

-- | Exchange from 'a' to 'b' given the exchange rate.
exchangeFrom ::
  forall (s :: S) a b.
  Term
    s
    ( PTagged (a :> b) (PRatio PInteger)
        :--> PTagged a (PRatio PInteger)
        :--> PTagged b (PRatio PInteger)
    )
exchangeFrom =
  phoistAcyclic $
    plam $ \ex x -> pretag ex * pretag x
