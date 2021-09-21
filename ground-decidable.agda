open import Prelude
open import core

module ground-decidable where
  ground-decidable : (τ : htyp) → (τ ground) + ((τ ground) → ⊥)
  ground-decidable num = Inl GNum
  ground-decidable (⦇-⦈ ==> ⦇-⦈) = Inl GArrHole
  ground-decidable (⦇-⦈ ⊕ ⦇-⦈) = Inl GSumHole
  ground-decidable ⦇-⦈ = Inr (λ ())
  ground-decidable (num ==> τ₁) = Inr (λ ())
  ground-decidable (⦇-⦈ ==> num) = Inr (λ ())
  ground-decidable (⦇-⦈ ==> τ₁ ==> τ₂) = Inr (λ ())
  ground-decidable (⦇-⦈ ==> τ₁ ⊕ τ₂) = Inr (λ ())
  ground-decidable ((τ ==> τ₂) ==> τ₁) = Inr (λ ())
  ground-decidable ((τ ⊕ τ₂) ==> τ₁) = Inr (λ ())
  ground-decidable (num ⊕ τ₁) = Inr (λ ())
  ground-decidable (⦇-⦈ ⊕ num) = Inr (λ ())
  ground-decidable (⦇-⦈ ⊕ τ₁ ==> τ₂) = Inr (λ ())
  ground-decidable (⦇-⦈ ⊕ τ₁ ⊕ τ₂) = Inr (λ ())
  ground-decidable ((τ ==> τ₂) ⊕ τ₁) = Inr (λ ())
  ground-decidable ((τ ⊕ τ₂) ⊕ τ₁) = Inr (λ ())
