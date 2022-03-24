module Plutarch.Integer.Extra (peven) where

-- Note, Jeff 2022-03-09:
-- Technically I could use `PIntegeral a` here but because it's not associated with
-- `Num`, so I have to hardcoded it to `PInteger`
peven :: Term s (PInteger :--> PBool)
peven = phoistAcyclic $ plam $ \n -> prem # n # 2 #== 0
