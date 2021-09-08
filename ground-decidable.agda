open import Prelude
open import core

module ground-decidable where
  ground-decidable : (τ : htyp) → (τ ground) + ((τ ground) → ⊥)
  ground-decidable num = Inl GNum
  ground-decidable ⦇-⦈ = Inr (λ ())
  ground-decidable (num ==> num) = Inr (λ ())
  ground-decidable (num ==> ⦇-⦈) = Inr (λ ())
  ground-decidable (num ==> τ' ==> τ'') = Inr (λ ())
  ground-decidable (⦇-⦈ ==> num) = Inr (λ ())
  ground-decidable (⦇-⦈ ==> ⦇-⦈) = Inl GHole
  ground-decidable (⦇-⦈ ==> τ' ==> τ'') = Inr (λ ())
  ground-decidable ((τ ==> τ₁) ==> num) = Inr (λ ())
  ground-decidable ((τ ==> τ₁) ==> ⦇-⦈) = Inr (λ ())
  ground-decidable ((τ ==> τ₁) ==> τ' ==> τ'') = Inr (λ ())

  ground-arr-lem : (τ : htyp) → ((τ ground) → ⊥) → (τ ≠  ⦇-⦈) → Σ[ τ1 ∈ htyp ] Σ[ τ2 ∈ htyp ] ((τ == (τ1 ==> τ2)) × ((τ1 ==> τ2) ≠ (⦇-⦈ ==> ⦇-⦈)))
  ground-arr-lem num ng nh = abort (ng GNum)
  ground-arr-lem ⦇-⦈ ng nh = abort (nh refl)
  ground-arr-lem (τ1 ==> τ2) ng nh = τ1 , τ2 , refl , (λ x → ng (lem' x))
    where
      lem' : ∀{τ1 τ2} → τ1 ==> τ2 == ⦇-⦈ ==> ⦇-⦈ → (τ1 ==> τ2) ground
      lem' refl = GHole
