open import core

module focus-formation where
  -- every ε is an evaluation context -- trivially, here, since we don't
  -- include any of the premises in red brackets about finality
  focus-formation : ∀{d d' ε} → d == ε ⟦ d' ⟧ → ε evalctx
  focus-formation (FHPlus1 sub) = ECPlus1 (focus-formation sub)
  focus-formation (FHPlus2 sub) = ECPlus2 (focus-formation sub)
  focus-formation FHOuter = ECDot
  focus-formation (FHAp1 sub) = ECAp1 (focus-formation sub)
  focus-formation (FHAp2 sub) = ECAp2 (focus-formation sub)
  focus-formation (FHInl sub) = ECInl (focus-formation sub)
  focus-formation (FHInr sub) = ECInr (focus-formation sub)
  focus-formation (FHCase sub) = ECCase (focus-formation sub)
  focus-formation (FHFst sub) = ECFst
  focus-formation (FHSnd sub) = ECSnd
  focus-formation (FHPair1 sub) = ECPair1 (focus-formation sub)
  focus-formation (FHPair2 sub) = ECPair2 (focus-formation sub)
  focus-formation (FHNEHole sub) = ECNEHole (focus-formation sub)
  focus-formation (FHCast sub) = ECCast (focus-formation sub)
  focus-formation (FHFailedCast x) = ECFailedCast (focus-formation x)
