{-# LANGUAGE UndecidableInstances #-}

module Plutarch.State.Extra (PState (PState), prunState) where

import Plutarch.Categories.Extra
import qualified Plutarch.Monadic as P

newtype PState (s :: PType) (a :: PType) (s' :: S) = PState (Term s' (s :--> PPair a s))
  deriving (PlutusType) via (DerivePNewtype (PState s a) (s :--> PPair a s))

prunState ::
  forall (s :: PType) (a :: PType) (s' :: S).
  Term s' (PState s a :--> (s :--> PPair a s))
prunState = phoistAcyclic $
  plam $ \state -> P.do
    PState runState <- pmatch state
    runState

instance PFunctor (PState (s :: PType)) where
  type FunctorConstraint (PState s) _ = ()
  pfmap = phoistAcyclic $
    plam $ \f fa -> pcon . PState $
      plam $ \s0 -> P.do
        PPair a s <- pmatch $ (prunState # fa) # s0
        pcon $ PPair (f # a) s

instance PApplicative (PState (s :: PType)) where
  type ApplicativeConstraint (PState s) _ = ()

  ppure = phoistAcyclic $
    plam $ \x -> pcon . PState $
      plam $ \s -> pcon $ PPair x s

  pliftA2 = phoistAcyclic $
    plam $ \x2y2z fx' fy' -> P.do
      fx :: Term _ (s :--> PPair x s) <- plet $ prunState # fx'
      fy :: Term _ (s :--> PPair y s) <- plet $ prunState # fy'
      pcon . PState $
        plam $ \s0 -> P.do
          PPair x s1 <- pmatch $ fx # s0
          PPair y s2 <- pmatch $ fy # s1
          pcon $ PPair (x2y2z # x #$ y) s2
