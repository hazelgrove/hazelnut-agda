open import Nat
open import Prelude
open import contexts
open import dynamics-core

open import canonical-value-forms

module canonical-boxed-forms where
  canonical-boxed-forms-num : ∀{Δ d} →
                            Δ , ∅ ⊢ d :: num →
                            d boxedval →
                            Σ[ n ∈ Nat ] (d == N n)
  canonical-boxed-forms-num (TAVar _) (BVVal ())
  canonical-boxed-forms-num wt (BVVal v) = canonical-value-forms-num wt v

  -- this type gives somewhat nicer syntax for the output of the canonical
  -- forms lemma for boxed values at arrow type
  data cbf-arr : (Δ : hctx) (d : ihexp) (τ1 τ2 : htyp) → Set where
    CBFALam : ∀{Δ d τ1 τ2} →
      Σ[ x ∈ Nat ] Σ[ d' ∈ ihexp ]
        ((d == (·λ x ·[ τ1 ] d')) ×
         (Δ , ■ (x , τ1) ⊢ d' :: τ2)
        )
        → cbf-arr Δ d τ1 τ2
    CBFACastArr : ∀{Δ d τ1 τ2} →
      Σ[ d' ∈ ihexp ] Σ[ τ1' ∈ htyp ] Σ[ τ2' ∈ htyp ]
        ((d == (d' ⟨ τ1' ==> τ2' ⇒ τ1 ==> τ2 ⟩)) ×
         (τ1' ==> τ2' ≠ τ1 ==> τ2) ×
         (Δ , ∅ ⊢ d' :: τ1' ==> τ2') ×
         (d' boxedval)
        )
        → cbf-arr Δ d τ1 τ2

  canonical-boxed-forms-arr : ∀{Δ d τ1 τ2 } →
                              Δ , ∅ ⊢ d :: (τ1 ==> τ2)  →
                              d boxedval →
                              cbf-arr Δ d τ1 τ2
  canonical-boxed-forms-arr (TAVar x₁) (BVVal ())
  canonical-boxed-forms-arr (TALam f wt) (BVVal v) = CBFALam (canonical-value-forms-arr (TALam f wt) v)
  canonical-boxed-forms-arr (TAAp wt wt₁) (BVVal ())
  canonical-boxed-forms-arr (TAEHole x x₁) (BVVal ())
  canonical-boxed-forms-arr (TANEHole x wt x₁) (BVVal ())
  canonical-boxed-forms-arr (TACast wt x) (BVVal ())
  canonical-boxed-forms-arr (TACast wt x) (BVArrCast x₁ bv) = CBFACastArr (_ , _ , _ , refl , x₁ , wt , bv)
  canonical-boxed-forms-arr (TAFailedCast x x₁ x₂ x₃) (BVVal ())

  -- this type gives somewhat nicer syntax for the output of the canonical
  -- forms lemma for boxed values at sum type
  data cbf-sum : (Δ : hctx) (d : ihexp) (τ1 τ2 : htyp) → Set where
    CBFSInl : ∀{Δ d τ1 τ2} →
      Σ[ d' ∈ ihexp ]
        ((d == (inl τ2 d')) ×
         (Δ , ∅ ⊢ d' :: τ1) ×
         (d boxedval)
        )
        → cbf-sum Δ d τ1 τ2
    CBFSInr : ∀{Δ d τ1 τ2} →
      Σ[ d' ∈ ihexp ]
        ((d == (inr τ1 d')) ×
         (Δ , ∅ ⊢ d' :: τ2) ×
         (d boxedval)
        )
        → cbf-sum Δ d τ1 τ2
    CBFSCastSum : ∀{Δ d τ1 τ2} →
      Σ[ d' ∈ ihexp ] Σ[ τ1' ∈ htyp ] Σ[ τ2' ∈ htyp ]
        ((d == (d' ⟨ τ1' ⊕ τ2' ⇒ τ1 ⊕ τ2 ⟩)) ×
         (τ1' ⊕ τ2' ≠ τ1 ⊕ τ2) ×
         (Δ , ∅ ⊢ d' :: τ1' ⊕ τ2') ×
         (d' boxedval)
        )
        → cbf-sum Δ d τ1 τ2
      
  canonical-boxed-forms-sum : ∀{Δ d τ1 τ2 } →
                              Δ , ∅ ⊢ d :: (τ1 ⊕ τ2)  →
                              d boxedval →
                              cbf-sum Δ d τ1 τ2
  canonical-boxed-forms-sum (TAInl wt) x = CBFSInl (_ , refl , wt , x)
  canonical-boxed-forms-sum (TAInr wt) x = CBFSInr (_ , refl , wt , x)
  canonical-boxed-forms-sum (TACast wt x₁) (BVSumCast x bv) = CBFSCastSum (_ , _ , _ , refl , x , wt , bv)
  canonical-boxed-forms-sum (TAVar x₁) (BVVal ())
  canonical-boxed-forms-sum (TAAp wt wt₁) (BVVal ())
  canonical-boxed-forms-sum (TACase wt _ wt₁ _ wt₂) (BVVal ())
  canonical-boxed-forms-sum (TAFst wt) (BVVal ())
  canonical-boxed-forms-sum (TASnd wt) (BVVal ())
  canonical-boxed-forms-sum (TAEHole x₁ x₂) (BVVal ()) 
  canonical-boxed-forms-sum (TANEHole x₁ wt x₂) (BVVal ())
  canonical-boxed-forms-sum (TACast wt x₁) (BVVal ())
  canonical-boxed-forms-sum (TAFailedCast wt x₁ x₂ x₃) (BVVal ())

  -- this type gives somewhat nicer syntax for the output of the canonical
  -- forms lemma for boxed values at product type
  data cbf-prod : (Δ : hctx) (d : ihexp) (τ1 τ2 : htyp) → Set where
    CBFPPair : ∀{Δ d τ1 τ2} →
      Σ[ d1 ∈ ihexp ] Σ[ d2 ∈ ihexp ]
        ((d == ⟨ d1 , d2 ⟩) ×
         (Δ , ∅ ⊢ d1 :: τ1) ×
         (Δ , ∅ ⊢ d2 :: τ2) ×
         (d1 boxedval) ×
         (d2 boxedval)
        )
        → cbf-prod Δ d τ1 τ2
    CBFPCastProd : ∀{Δ d τ1 τ2} →
      Σ[ d' ∈ ihexp ] Σ[ τ1' ∈ htyp ] Σ[ τ2' ∈ htyp ]
        ((d == (d' ⟨ τ1' ⊠ τ2' ⇒ τ1 ⊠ τ2 ⟩)) ×
         (τ1' ⊠ τ2' ≠ τ1 ⊠ τ2) ×
         (Δ , ∅ ⊢ d' :: τ1' ⊠ τ2') ×
         (d' boxedval)
        )
        → cbf-prod Δ d τ1 τ2
  canonical-boxed-forms-prod : ∀{Δ d τ1 τ2 } →
                               Δ , ∅ ⊢ d :: (τ1 ⊠ τ2)  →
                               d boxedval →
                               cbf-prod Δ d τ1 τ2
  canonical-boxed-forms-prod (TAPair wt wt₁) (BVVal (VPair x x₁)) = CBFPPair (_ , _ , refl , wt , wt₁ , BVVal x , BVVal x₁)
  canonical-boxed-forms-prod (TAPair wt wt₁) (BVPair bv bv₁) = CBFPPair (_ , _ , refl , wt , wt₁ , bv , bv₁)
  canonical-boxed-forms-prod (TACast wt x) (BVProdCast x₁ bv) = CBFPCastProd (_ , _ , _ , refl , x₁ , wt , bv)
  
  canonical-boxed-forms-hole : ∀{Δ d} →
                               Δ , ∅ ⊢ d :: ⦇-⦈ →
                               d boxedval →
                               Σ[ d' ∈ ihexp ] Σ[ τ' ∈ htyp ]
                                 ((d == d' ⟨ τ' ⇒ ⦇-⦈ ⟩) ×
                                  (τ' ground) ×
                                  (Δ , ∅ ⊢ d' :: τ'))
  canonical-boxed-forms-hole (TAVar x₁) (BVVal ())
  canonical-boxed-forms-hole (TAAp wt wt₁) (BVVal ())
  canonical-boxed-forms-hole (TAEHole x x₁) (BVVal ())
  canonical-boxed-forms-hole (TANEHole x wt x₁) (BVVal ())
  canonical-boxed-forms-hole (TACast wt x) (BVVal ())
  canonical-boxed-forms-hole (TACast wt x) (BVHoleCast x₁ bv) = _ , _ , refl , x₁ , wt
  canonical-boxed-forms-hole (TAFailedCast x x₁ x₂ x₃) (BVVal ())

  canonical-boxed-forms-coverage : ∀{Δ d τ} →
                                   Δ , ∅ ⊢ d :: τ →
                                   d boxedval →
                                   τ ≠ num →
                                   ((τ1 : htyp) (τ2 : htyp) → τ ≠ (τ1 ==> τ2)) →
                                   ((τ1 : htyp) (τ2 : htyp) → τ ≠ (τ1 ⊕ τ2)) →
                                   ((τ1 : htyp) (τ2 : htyp) → τ ≠ (τ1 ⊠ τ2)) →
                                   τ ≠ ⦇-⦈ →
                                   ⊥
  canonical-boxed-forms-coverage TANum bv nn na ns np nh = nn refl
  canonical-boxed-forms-coverage (TAPlus wt wt₁) bv nn na ns np nh = nn refl
  canonical-boxed-forms-coverage (TALam x wt) bv nn na ns np nh = na _ _ refl
  canonical-boxed-forms-coverage (TAAp wt wt₁) (BVVal ()) nn na ns np nh
  canonical-boxed-forms-coverage (TAInl wt) bv nn na ns np nh = ns _ _ refl
  canonical-boxed-forms-coverage (TAInr wt) bv nn na ns np nh = ns _ _ refl
  canonical-boxed-forms-coverage (TACase wt _ wt₁ _ wt₂) (BVVal ()) nn na ns np nh
  canonical-boxed-forms-coverage (TAEHole x x₁) (BVVal ()) nn na ns np nh
  canonical-boxed-forms-coverage (TANEHole x wt x₁) (BVVal ()) nn na ns np nh
  canonical-boxed-forms-coverage (TACast wt x) (BVArrCast x₁ bv) nn na ns np nh = na _ _ refl
  canonical-boxed-forms-coverage (TACast wt x) (BVSumCast x₁ bv) nn na ns np nh = ns _ _ refl
  canonical-boxed-forms-coverage (TACast wt x) (BVProdCast x₁ bv) nn na ns np nh = np _ _ refl
  canonical-boxed-forms-coverage (TACast wt x) (BVHoleCast x₁ bv) nn na ns np nh = nh refl
  canonical-boxed-forms-coverage (TAFailedCast wt x x₁ x₂) (BVVal ()) nn na ns np nh
  canonical-boxed-forms-coverage (TAPair wt wt₁) bv nn na ns np nh = np _ _ refl
  canonical-boxed-forms-coverage (TAFst wt) (BVVal ()) nn na ns np nh
  canonical-boxed-forms-coverage (TASnd wt) (BVVal ()) nn na ns np nh
  
