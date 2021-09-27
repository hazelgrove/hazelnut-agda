open import Prelude
open import core

module lemmas-ground where
  -- not ground types aren't just a type constructor filled with holes
  ground-not-holes : ∀{τ} →
                     (τ ground → ⊥) →
                     (τ ≠ (⦇-⦈ ==> ⦇-⦈)) × (τ ≠ (⦇-⦈ ⊕ ⦇-⦈)) × (τ ≠ (⦇-⦈ ⊠ ⦇-⦈))
  ground-not-holes notg = (λ{refl → notg GArrHole}) ,
                          (λ{refl → notg GSumHole}) ,
                          (λ{refl → notg GProdHole})

  -- not ground types either have to be hole, an arrow, or a sum
  not-ground : ∀{τ} →
              (τ ground → ⊥) →
              ((τ == ⦇-⦈) +
               (Σ[ τ1 ∈ htyp ] Σ[ τ2 ∈ htyp ] (τ == (τ1 ==> τ2))) + 
               (Σ[ τ1 ∈ htyp ] Σ[ τ2 ∈ htyp ] (τ == (τ1 ⊕ τ2))) +
               (Σ[ τ1 ∈ htyp ] Σ[ τ2 ∈ htyp ] (τ == (τ1 ⊠ τ2))))
  not-ground {num} gnd = abort (gnd GNum)
  not-ground {⦇-⦈} gnd = Inl refl
  not-ground {τ ==> τ₁} gnd = Inr (Inl (τ , τ₁ , refl))
  not-ground {τ ⊕ τ₁} gnd = Inr (Inr (Inl (τ , τ₁ , refl)))
  not-ground {τ ⊠ τ₁} gnd = Inr (Inr (Inr (τ , τ₁ , refl)))
