open import Prelude
open import dynamics-core

module lemmas-matching where
  -- arrow matching produces unique answers
  ▸arr-unicity : ∀{τ τ2 τ3} →
                 τ ▸arr τ2 →
                 τ ▸arr τ3 →
                 τ2 == τ3
  ▸arr-unicity MAHole MAHole = refl
  ▸arr-unicity MAArr MAArr   = refl

  -- only consistent types arrow match
  ▸arr-consist : ∀{τ1 τ2} →
                 τ1 ▸arr τ2 →
                 (τ1 ~ τ2)
  ▸arr-consist MAHole = TCHole2
  ▸arr-consist MAArr  = TCRefl
  
  -- if an arrow matches, then it's consistent with the 
  -- least restrictive function type
  ▸arr-consist-hole : ∀{t t'} →
                      t ▸arr t' →
                      t ~ (⦇-⦈ ==> ⦇-⦈)
  ▸arr-consist-hole MAHole = TCHole2
  ▸arr-consist-hole MAArr  = TCArr TCHole1 TCHole1

  -- sum matching produces unique answers
  ▸sum-unicity : ∀{τ τ2 τ3} →
                 τ ▸sum τ2 →
                 τ ▸sum τ3 →
                 τ2 == τ3
  ▸sum-unicity MSHole MSHole = refl
  ▸sum-unicity MSSum MSSum   = refl
  
  -- only consistent types sum match
  ▸sum-consist : ∀{τ1 τ2} →
                 τ1 ▸sum τ2 →
                 (τ1 ~ τ2)
  ▸sum-consist MSHole = TCHole2
  ▸sum-consist MSSum  = TCRefl

  -- if a sum matches, then it's consistent with the 
  -- least restrictive function type
  ▸sum-consist-hole : ∀{t t'} →
                      t ▸sum t' →
                      t ~ (⦇-⦈ ⊕ ⦇-⦈)
  ▸sum-consist-hole MSHole = TCHole2
  ▸sum-consist-hole MSSum  = TCSum TCHole1 TCHole1

  -- product matching produces unique answers
  ▸prod-unicity : ∀{τ τ2 τ3} →
                  τ ▸prod τ2 →
                  τ ▸prod τ3 →
                  τ2 == τ3
  ▸prod-unicity MPHole MPHole = refl
  ▸prod-unicity MPProd MPProd   = refl
  
  -- only consistent types product match
  ▸prod-consist : ∀{τ1 τ2} →
                  τ1 ▸prod τ2 →
                  (τ1 ~ τ2)
  ▸prod-consist MPHole = TCHole2
  ▸prod-consist MPProd = TCRefl
 
   -- if a sum matches, then it's consistent with the 
  -- least restrictive function type
  ▸prod-consist-hole : ∀{t t'} →
                       t ▸prod t' →
                       t ~ (⦇-⦈ ⊠ ⦇-⦈)
  ▸prod-consist-hole MPHole = TCHole2
  ▸prod-consist-hole MPProd = TCProd TCHole1 TCHole1
