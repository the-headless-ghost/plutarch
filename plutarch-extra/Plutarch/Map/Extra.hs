{- | Note, Peter 2022-02-22:

 Helper function provided by Magnus Viernickel. They are not yet verified nor optimized.

 These are being upstreamed eventually (do not have a PR reference yet). Once they are, we
 should rely on the upstream versions).
-}
module Plutarch.Map.Extra (
  (#!?),
  (#!),
  plookup,
  plookupD,
  plookup',
  pkeys,
  pmapFromList,
  pmapFromList',
  pmapFromSet,
  pmapFromMap,
) where

import Data.Foldable (Foldable (foldl'))
import Plutarch.Api.V1 (PMaybeData (..), ptuple)
import Plutarch.Api.V1.AssocMap (PMap (PMap))
import Plutarch.Api.V1.Tuple (pbuiltinPairFromTuple)
import Plutarch.Lift (PLifted)
import Plutarch.Maybe.Extra (pfromMaybe)
import qualified PlutusTx.AssocMap as AssocMap
import PlutusTx.IsData.Class (FromData, ToData)

infixl 9 #!?, #!

(#!?) ::
  forall a b s.
  ( PIsData a
  , PIsData b
  , PEq a
  ) =>
  Term s (PMap a b) ->
  Term s a ->
  Term s (PMaybe b)
m #!? k = plookup # k # m

(#!) ::
  forall a b s.
  ( PIsData a
  , PIsData b
  , PEq a
  ) =>
  Term s (PMap a b) ->
  Term s a ->
  Term s b
m #! k = plookup' # k # m

-- | Safe: returns Maybe b
plookup ::
  forall a b s.
  ( PIsData a
  , PIsData b
  , PEq a
  ) =>
  Term s (a :--> PMap a b :--> PMaybe b)
plookup = phoistAcyclic $
  plam $ \key map -> unTermCont $ do
    let pred :: Term _ (PBuiltinPair (PAsData a) (PAsData b) :--> PBool)
        pred = plam $ \tup -> (pfromData $ pfstBuiltin # tup) #== key
        tup :: Term _ (PMaybe (PBuiltinPair (PAsData a) (PAsData b)))
        tup = pfind # pred # pto map
    res <- tcont $ pmatch tup
    pure $ case res of
      PNothing -> pcon PNothing
      PJust tup' -> pcon . PJust $ pfromData $ psndBuiltin # tup'

-- | Like plookup, but returns @PMaybeData b@
plookupD ::
  forall a b s.
  ( PIsData a
  , PIsData b
  , PEq a
  ) =>
  Term s (a :--> PMap a b :--> PMaybeData b)
plookupD = phoistAcyclic $
  plam $ \key map -> P.do
    let pred :: Term _ (PBuiltinPair (PAsData a) (PAsData b) :--> PBool)
        pred = plam $ \tup -> (pfromData $ pfstBuiltin # tup) #== key
        tup :: Term _ (PMaybe (PBuiltinPair (PAsData a) (PAsData b)))
        tup = pfind # pred # pto map
    pmatch tup $ \case
      PNothing -> pcon $ PDNothing pdnil
      PJust tup' -> pcon . PDJust $ pdcons # (psndBuiltin # tup') # pdnil

-- | Note, Peter 2022-02-23: Unsafe. Will error.
plookup' ::
  forall a b s.
  ( PIsData a
  , PIsData b
  , PEq a
  ) =>
  Term s (a :--> PMap a b :--> b)
plookup' = plam $ \key map -> pfromMaybe #$ plookup # key # map

{- | Return all keys of the map as a list. Ordering (of any type)
 is not guaranteed.
-}
pkeys ::
  forall (k :: PType) (v :: PType) (s :: S).
  Term s (PMap k v :--> PBuiltinList (PAsData k))
pkeys = phoistAcyclic $
  plam $ \map ->
    pmap
      # pfstBuiltin
      # (pto map :: Term _ (PBuiltinList (PBuiltinPair (PAsData k) (PAsData v))))

-- Somehwat ugly implementation, it might be possible to implement via `PUnsafeLiftDecl`, but I'm not sure...
pmapFromList ::
  forall (s :: S) (a :: PType) (b :: PType).
  (PIsData a, PIsData b) =>
  [(Term s a, Term s b)] ->
  Term s (PMap a b)
pmapFromList list = pcon $ PMap $ xs
  where
    xs :: Term s (PBuiltinList (PBuiltinPair (PAsData a) (PAsData b)))
    xs =
      foldl' (\xs x -> pcon $ PCons x xs) (pcon PNil) $
        fmap
          ( \(x, y) ->
              pfromData $
                pbuiltinPairFromTuple $
                  pdata $ ptuple # pdata x # pdata y
          )
          list

pmapFromList' ::
  forall (s :: S) (a :: PType) (b :: PType).
  ( Ord (PLifted a)
  , ToData (PLifted a)
  , ToData (PLifted b)
  , FromData (PLifted a)
  , FromData (PLifted b)
  , PLift a
  , PLift b
  , PIsData a
  , PIsData b
  ) =>
  [(PLifted a, PLifted b)] ->
  Term s (PMap a b)
pmapFromList' = pconstant . AssocMap.fromList

pmapFromSet :: forall (s :: S) (a :: PType). Term s a
pmapFromSet = undefined

pmapFromMap :: forall (s :: S) (a :: PType). Term s a
pmapFromMap = undefined
