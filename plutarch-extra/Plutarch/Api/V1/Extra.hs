{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Plutarch.Api.V1.Extra (
  pownTxOutRef,
  pownTxInfo,
  pownValue,
  pownInput,
  pownMintValue,
  psingletonValue,
  passetClassValue,
  padaOf,
  pvalueOf,
  passetClassValueOf,
  PAssetClass,
  passetClass,
  (:$),
) where

import qualified GHC.Generics as GHC
import qualified Generics.SOP as SOP
import Plutarch.Api.V1 (
  PScriptContext,
  PScriptPurpose (PSpending),
  PTxInInfo,
  PTxInfo,
  PTxOutRef,
 )
import Plutarch.Api.V1.AssocMap (PMap (PMap))
import Plutarch.Api.V1.Value (PCurrencySymbol, PTokenName, PValue (PValue))
import Plutarch.Builtin (ppairDataBuiltin)
import Plutarch.DataRepr (
  PDataFields,
  PIsDataReprInstances (PIsDataReprInstances),
 )
import Plutarch.Map.Extra ((#!?))
import Plutarch.Maybe.Extra (pfromMaybe)
import qualified Plutarch.Monadic as P

pownTxOutRef :: Term s :$ PScriptContext :--> PTxOutRef
pownTxOutRef = phoistAcyclic $
  plam $ \ctx -> P.do
    PSpending txoutRef <- pmatch $ pfield @"purpose" # ctx
    pfield @"_0" # txoutRef

pownTxInfo :: Term s :$ PScriptContext :--> PTxInfo
pownTxInfo = phoistAcyclic $
  plam $ \ctx -> pfield @"txInfo" # ctx

pownValue :: Term s :$ PScriptContext :--> PValue
pownValue = phoistAcyclic $
  plam $ \ctx ->
    let input = pownInput # ctx
     in pfield @"value" #$ pfield @"resolved" # input

pownMintValue :: Term s :$ PScriptContext :--> PValue
pownMintValue = phoistAcyclic $
  plam $ \ctx ->
    pfield @"mint" #$ pfield @"txInfo" # ctx

pownInput :: Term s :$ PScriptContext :--> PTxInInfo
pownInput = phoistAcyclic $
  plam $ \ctx ->
    let txInfo :: Term _ (PTxInfo)
        txInfo = pownTxInfo # ctx
        txOutRef :: Term _ (PTxOutRef)
        txOutRef = pownTxOutRef # ctx
        txInInfos :: Term _ (PBuiltinList (PAsData PTxInInfo))
        txInInfos = pfield @"inputs" # txInfo
        pred :: Term _ (PAsData PTxInInfo :--> PBool)
        pred = plam $ \actual' ->
          plet (pfield @"outRef" # pfromData actual') $ \actual ->
            txOutRef #== actual
     in pfromData $ pfromMaybe #$ pfind # pred # txInInfos

psingletonValue ::
  Term s :$ PCurrencySymbol :--> PTokenName :--> PInteger :--> PValue
psingletonValue = phoistAcyclic $
  plam $ \sym tok int ->
    let innerTup :: Term _ :$ PMap PTokenName PInteger
        innerTup =
          pcon $
            PMap $ psingleton #$ ppairDataBuiltin # pdata tok # pdata int
        outerTup :: Term _ :$ PMap PCurrencySymbol (PMap PTokenName PInteger)
        outerTup =
          pcon $
            PMap $ psingleton #$ ppairDataBuiltin # pdata sym # pdata innerTup
        res :: Term _ :$ PValue
        res = pcon $ PValue outerTup
     in res

passetClassValue :: Term s :$ PAssetClass :--> PInteger :--> PValue
passetClassValue = phoistAcyclic $
  plam $ \ass i -> P.do
    asset <- pletFields @["currencySymbol", "tokenName"] $ pto $ ass
    psingletonValue # asset.currencySymbol # asset.tokenName # i

pvalueOf :: Term s :$ PValue :--> PCurrencySymbol :--> PTokenName :--> PInteger
pvalueOf = phoistAcyclic $
  plam $ \val sym tok -> P.do
    let outerMap :: Term _ :$ PMaybe (PMap PTokenName PInteger)
        outerMap = pto val #!? sym
    res <- pmatch outerMap
    case res of
      PNothing -> 0
      PJust innerMap -> P.do
        innerRes <- pmatch $ innerMap #!? tok
        case innerRes of
          PNothing -> 0
          PJust val -> val

padaOf :: Term s :$ PValue :--> PInteger
padaOf = phoistAcyclic $
  plam $ \value -> pvalueOf # value # pconstant "" # pconstant ""

passetClassValueOf :: Term s :$ PValue :--> PAssetClass :--> PInteger
passetClassValueOf = plam $ \val asset -> P.do
  ac <- pletFields @["currencySymbol", "tokenName"] asset
  pvalueOf # val # ac.currencySymbol # ac.tokenName

data PAssetClass (s :: S)
  = PAssetClass
      ( Term
          s
          ( PDataRecord
              '[ "currencySymbol" ':= PCurrencySymbol
               , "tokenName" ':= PTokenName
               ]
          )
      )
  deriving stock (GHC.Generic)
  deriving anyclass (SOP.Generic, PIsDataRepr)
  deriving (PlutusType, PIsData, PDataFields) via PIsDataReprInstances PAssetClass

instance PEq PAssetClass where
  x #== y = P.do
    x' <- pletFields @["currencySymbol", "tokenName"] x
    y' <- pletFields @["currencySymbol", "tokenName"] y
    x'.currencySymbol #== y'.currencySymbol
      #&& x'.tokenName #== y'.tokenName

passetClass :: Term s :$ PCurrencySymbol :--> PTokenName :--> PAssetClass
passetClass = plam $ \sym tok ->
  pcon . PAssetClass $
    pdcons @"currencySymbol" # pdata sym
      #$ pdcons @"tokenName" # pdata tok # pdnil

-- and here the (:$)

type a :$ b = a b
infixr 0 :$
