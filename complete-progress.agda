open import Nat
open import Prelude
open import core
open import contexts

open import progress
open import htype-decidable
open import lemmas-complete

module complete-progress where

  -- as in progress, we define a datatype for the possible outcomes of
  -- progress for readability.
  data okc : (d : ihexp) (Δ : hctx) → Set where
    V : ∀{d Δ} → d val → okc d Δ
    S : ∀{d Δ} → Σ[ d' ∈ ihexp ] (d ↦ d') → okc d Δ

  complete-progress : {Δ : hctx} {d : ihexp} {τ : htyp} →
                       Δ , ∅ ⊢ d :: τ →
                       d dcomplete →
                       okc d Δ
  complete-progress wt comp with progress wt
  complete-progress wt comp | I x = abort (lem-ind-comp comp x)
  complete-progress wt comp | S x = S x
  complete-progress wt comp | BV (BVVal x) = V x
  complete-progress wt (DCCast comp x₂ ()) | BV (BVHoleCast x x₁)
  complete-progress (TACast wt x) (DCCast comp x₃ x₄) | BV (BVArrCast x₁ x₂) = abort (x₁ (complete-consistency x x₃ x₄))
  complete-progress (TACast wt x) (DCCast comp x₃ x₄) | BV (BVSumCast x₁ x₂) = abort (x₁ (complete-consistency x x₃ x₄))
  complete-progress (TAInl wt) (DCInl x₁ comp) | BV (BVInl x)
    with complete-progress wt comp
  ... | V v = V (VInl v)
  ... | S (_ , Step x₂ x₃ x₄) = S (_ , Step (FHInl x₂) x₃ (FHInl x₄))
  complete-progress (TAInr wt) (DCInr x₁ comp) | BV (BVInr x)
    with complete-progress wt comp
  ... | V v = V (VInr v)
  ... | S (_ , Step x₂ x₃ x₄) = S (_ , Step (FHInr x₂) x₃ (FHInr x₄))

