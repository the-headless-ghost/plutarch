{-# LANGUAGE QualifiedDo #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Plutarch.Maybe.Extra (
  pfromMaybe,
  pfromMaybeData,
) where

import Plutarch.Api.V1 (PMaybeData (..))
import qualified Plutarch.Monadic as P

-- | Note, Peter 2022-02-23: Unsafe. Will error.
pfromMaybe :: Term s (PMaybe a :--> a)
pfromMaybe = phoistAcyclic $
  plam $ \maybe -> unTermCont $ do
    res <- tcont $ pmatch maybe
    pure $ case res of
      PNothing -> perror
      PJust a -> a

pfromMaybeData :: (PIsData a) => Term s (PMaybeData a :--> a)
pfromMaybeData = phoistAcyclic $
  plam $ \maybe -> P.do
    PDJust d <- pmatch maybe
    pfield @"_0" # d
