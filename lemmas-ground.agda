open import Prelude
open import core

module lemmas-ground where
  -- not ground types aren't hole to hole
  ground-arr-not-hole : ∀{τ} →
                      (τ ground → ⊥) →
                      (τ ≠ (⦇-⦈ ==> ⦇-⦈))
  ground-arr-not-hole notg refl = notg GHole

  -- not ground types either have to be hole or an arrow
  notground : ∀{τ} → (τ ground → ⊥) → (τ == ⦇-⦈) + (Σ[ τ1 ∈ htyp ] Σ[ τ2 ∈ htyp ] (τ == (τ1 ==> τ2)))
  notground {num} gnd = abort (gnd GNum)
  notground {⦇-⦈} gnd = Inl refl
  notground {num ==> num} gnd = Inr (num , num , refl)
  notground {num ==> ⦇-⦈} gnd = Inr (num , ⦇-⦈ , refl)
  notground {num ==> τ2 ==> τ3} gnd = Inr (num , τ2 ==> τ3 , refl)
  notground {⦇-⦈ ==> num} gnd = Inr (⦇-⦈ , num , refl)
  notground {⦇-⦈ ==> ⦇-⦈} gnd = abort (gnd GHole)
  notground {⦇-⦈ ==> τ2 ==> τ3} gnd = Inr (⦇-⦈ , τ2 ==> τ3 , refl)
  notground {(τ1 ==> τ2) ==> num} gnd = Inr (τ1 ==> τ2 , num , refl)
  notground {(τ1 ==> τ2) ==> ⦇-⦈} gnd = Inr (τ1 ==> τ2 , ⦇-⦈ , refl)
  notground {(τ1 ==> τ2) ==> τ3 ==> τ4} gnd = Inr (τ1 ==> τ2 , τ3 ==> τ4 , refl)
