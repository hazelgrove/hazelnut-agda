open import Nat
open import Prelude
open import contexts
open import dynamics-core

module canonical-value-forms where
  canonical-value-forms-num : ∀{Δ d} →
                              Δ , ∅ ⊢ d :: num →
                              d val →
                              Σ[ n ∈ Nat ] (d == N n)
  canonical-value-forms-num TANum VNum = _ , refl
  canonical-value-forms-num (TAVar x₁) ()
  canonical-value-forms-num (TAAp wt wt₁) ()
  canonical-value-forms-num (TAEHole x x₁) ()
  canonical-value-forms-num (TANEHole x wt x₁) ()
  canonical-value-forms-num (TACast wt x) ()
  canonical-value-forms-num (TAFailedCast wt x x₁ x₂) ()

  canonical-value-forms-arr : ∀{Δ d τ1 τ2} →
                              Δ , ∅ ⊢ d :: (τ1 ==> τ2) →
                              d val →
                              Σ[ x ∈ Nat ] Σ[ d' ∈ ihexp ]
                                ((d == (·λ x ·[ τ1 ] d')) ×
                                 (Δ , ■ (x , τ1) ⊢ d' :: τ2))
  canonical-value-forms-arr (TAVar x₁) ()
  canonical-value-forms-arr {Δ = Δ} {d = ·λ x ·[ τ1 ] d} {τ1 = τ1} {τ2 = τ2} (TALam _ wt) VLam
    = _ , _ , refl , tr (λ Γ → Δ , Γ ⊢ d :: τ2) (extend-empty x τ1) wt
  canonical-value-forms-arr (TAAp wt wt₁) ()
  canonical-value-forms-arr (TAEHole x x₁) ()
  canonical-value-forms-arr (TANEHole x wt x₁) ()
  canonical-value-forms-arr (TACast wt x) ()
  canonical-value-forms-arr (TAFailedCast x x₁ x₂ x₃) ()

  canonical-value-form-sum : ∀{Δ d τ1 τ2} →
                              Δ , ∅ ⊢ d :: (τ1 ⊕ τ2) →
                              d val →
                              (Σ[ d' ∈ ihexp ] ((d == (inl τ2 d')) × (Δ , ∅ ⊢ d' :: τ1))) +
                              (Σ[ d' ∈ ihexp ] ((d == (inr τ1 d')) × (Δ , ∅ ⊢ d' :: τ2)))
  canonical-value-form-sum (TAInl wt) (VInl v) = Inl (_ , refl , wt)
  canonical-value-form-sum (TAInr wt) (VInr v) = Inr (_ , refl , wt)

  canonical-value-form-prod : ∀{Δ d τ1 τ2} →
                              Δ , ∅ ⊢ d :: (τ1 ⊠ τ2) →
                              d val →
                              Σ[ d1 ∈ ihexp ] Σ[ d2 ∈ ihexp ]
                                ((d == ⟨ d1 , d2 ⟩) ×
                                 (Δ , ∅ ⊢ d1 :: τ1) ×
                                 (Δ , ∅ ⊢ d2 :: τ2))
  canonical-value-form-prod (TAVar x) ()
  canonical-value-form-prod (TAAp wt wt₁) ()
  canonical-value-form-prod (TACase wt x wt₁ x₁ wt₂) ()
  canonical-value-form-prod (TAPair wt wt₁) (VPair v v₁) = _ , _ , refl , wt , wt₁
  canonical-value-form-prod (TAFst wt) ()
  canonical-value-form-prod (TASnd wt) ()
  canonical-value-form-prod (TAEHole x x₁) ()
  canonical-value-form-prod (TANEHole x wt x₁) ()
  canonical-value-form-prod (TACast wt x) ()
  canonical-value-form-prod (TAFailedCast wt x x₁ x₂) ()
  
  -- this argues (somewhat informally, because you still have to inspect
  -- the types of the theorems above and manually verify this property)
  -- that we didn't miss any cases above; this intentionally will make this
  -- file fail to typecheck if we added more types, hopefully forcing us to
  -- remember to add canonical forms lemmas as appropriate
  canonical-value-forms-coverage1 : ∀{Δ d τ} →
                                   Δ , ∅ ⊢ d :: τ →
                                   d val →
                                   τ ≠ num →
                                   ((τ1 : htyp) (τ2 : htyp) → τ ≠ (τ1 ==> τ2)) →
                                   ((τ1 : htyp) (τ2 : htyp) → τ ≠ (τ1 ⊕ τ2)) →
                                   ((τ1 : htyp) (τ2 : htyp) → τ ≠ (τ1 ⊠ τ2)) →
                                   ⊥
  canonical-value-forms-coverage1 TANum val nn na ns np = nn refl
  canonical-value-forms-coverage1 (TALam x wt) val nn na ns np = na _ _ refl
  canonical-value-forms-coverage1 (TAInl wt) val nn na ns np = ns _ _ refl
  canonical-value-forms-coverage1 (TAInr wt) val nn na ns np = ns _ _ refl
  canonical-value-forms-coverage1 (TAPair wt wt₁) val nn na ns np = np _ _ refl

  canonical-value-forms-coverage2 : ∀{Δ d} →
                                   Δ , ∅ ⊢ d :: ⦇-⦈ →
                                   d val →
                                   ⊥
  canonical-value-forms-coverage2 (TAVar x₁) ()
  canonical-value-forms-coverage2 (TAAp wt wt₁) ()
  canonical-value-forms-coverage2 (TAEHole x x₁) ()
  canonical-value-forms-coverage2 (TANEHole x wt x₁) ()
  canonical-value-forms-coverage2 (TACast wt x) ()
  canonical-value-forms-coverage2 (TAFailedCast wt x x₁ x₂) ()
