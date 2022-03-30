{-# LANGUAGE CPP #-}
{-# OPTIONS_GHC -Wno-unused-imports #-}

module Plutarch.Trace.Extra (ptraceIfNothing) where

import Plutarch.Internal.Other (Term, perror)
#ifdef Development
import Plutarch.Internal.Other (type (:-->), (#), phoistAcyclic, plet, pforce, pdelay)
#endif
#ifdef Development
import Plutarch.Bool (PBool, pif)
#else
import Plutarch.Bool (PBool)
#endif

import Plutarch.Lift (PLifted, PUnsafeLiftDecl)
import Plutarch.String (PString)
import Plutarch.Trace (ptraceError)

#ifdef Development
import Plutarch.Unsafe (punsafeBuiltin)
import qualified PlutusCore as PLC
#endif

ptraceIfNothing ::
  forall (s :: S) (a :: PType).
  Term s PString ->
  Term s (PMaybe a) ->
  Term s a
ptraceIfNothing s a' = plet a' $ \a -> pmatch a $ \case
  PJust x -> x
  PNothing -> ptraceError s
