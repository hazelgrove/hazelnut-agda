open import Nat
open import Prelude
open import contexts
open import dynamics-core
open import type-assignment-unicity

module canonical-indeterminate-forms where

  -- this type gives somewhat nicer syntax for the output of the canonical
  -- forms lemma for indeterminates at num type
  data cif-num : (Δ : hctx) (d : ihexp) → Set where
    CIFNPlus1 : ∀{Δ d} →
      Σ[ d1 ∈ ihexp ] Σ[ d2 ∈ ihexp ]
        ((d == d1 ·+ d2) ×
         (Δ , ∅ ⊢ d1 :: num) ×
         (Δ , ∅ ⊢ d2 :: num) ×
         (d1 indet) ×
         (d2 final)
        )
        → cif-num Δ d
    CIFNPlus2 : ∀{Δ d} →
      Σ[ d1 ∈ ihexp ] Σ[ d2 ∈ ihexp ]
        ((d == d1 ·+ d2) ×
         (Δ , ∅ ⊢ d1 :: num) ×
         (Δ , ∅ ⊢ d2 :: num) ×
         (d1 final) ×
         (d2 indet)
        )
        → cif-num Δ d
    CIFNAp : ∀{Δ d} →
      Σ[ d1 ∈ ihexp ] Σ[ d2 ∈ ihexp ] Σ[ τ2 ∈ htyp ]
        ((d == d1 ∘ d2) ×
         (Δ , ∅ ⊢ d1 :: τ2 ==> num) ×
         (Δ , ∅ ⊢ d2 :: τ2) ×
         (d1 indet) ×
         (d2 final) ×
         ((τ3 τ4 τ3' τ4' : htyp) (d1' : ihexp) → d1 ≠ (d1' ⟨ τ3 ==> τ4 ⇒ τ3' ==> τ4' ⟩))
        )
        → cif-num Δ d
    CIFNCase : ∀{Δ d} →
      Σ[ d1 ∈ ihexp ] Σ[ x ∈ Nat ] Σ[ d2 ∈ ihexp ] Σ[ y ∈ Nat ] Σ[ d3 ∈ ihexp ]
      Σ[ τ1 ∈ htyp ] Σ[ τ2 ∈ htyp ]
        ((d == case d1 x d2 y d3) ×
         (Δ , ∅ ⊢ d1 :: τ1 ⊕ τ2) ×
         (Δ , ■ (x , τ1) ⊢ d2 :: num) ×
         (Δ , ■ (y , τ2) ⊢ d3 :: num) ×
         (d1 indet) ×
         ((τ : htyp) (d' : ihexp) → d1 ≠ inl τ d') ×
         ((τ : htyp) (d' : ihexp) → d1 ≠ inr τ d') ×
         ((τ3 τ4 τ3' τ4' : htyp) (d' : ihexp) →
           d1 ≠ (d' ⟨(τ3 ⊕ τ4) ⇒ (τ3' ⊕ τ4')⟩))
        )
        → cif-num Δ d
    CIFNFst : ∀{Δ d} →
      Σ[ d' ∈ ihexp ] Σ[ τ' ∈ htyp ]
        ((d == fst d') ×
         (Δ , ∅ ⊢ d' :: num ⊠ τ') ×
         (d' indet) ×
         ((d1 d2 : ihexp) → d' ≠ ⟨ d1 , d2 ⟩) ×
         ((τ3 τ4 τ3' τ4' : htyp) (d'' : ihexp) →
           d' ≠ (d'' ⟨(τ3 ⊠ τ4) ⇒ (τ3' ⊠ τ4')⟩)) 
        )
        → cif-num Δ d
    CIFNSnd : ∀{Δ d} →
      Σ[ d' ∈ ihexp ] Σ[ τ' ∈ htyp ]
        ((d == snd d') ×
         (Δ , ∅ ⊢ d' :: τ' ⊠ num) ×
         (d' indet) ×
         ((d1 d2 : ihexp) → d' ≠ ⟨ d1 , d2 ⟩) ×
         ((τ3 τ4 τ3' τ4' : htyp) (d'' : ihexp) →
           d' ≠ (d'' ⟨(τ3 ⊠ τ4) ⇒ (τ3' ⊠ τ4')⟩)) 
        )
        → cif-num Δ d
    CIFNEHole : ∀{Δ d} →
      Σ[ u ∈ Nat ] Σ[ σ ∈ env ] Σ[ Γ ∈ tctx ]
        ((d == ⦇-⦈⟨ u , σ ⟩) ×
         ((u :: num [ Γ ]) ∈ Δ) ×
         (Δ , ∅ ⊢ σ :s: Γ)
        )
        → cif-num Δ d
    CIFNNEHole : ∀{Δ d} →
      Σ[ u ∈ Nat ] Σ[ σ ∈ env ] Σ[ Γ ∈ tctx ] Σ[ d' ∈ ihexp ] Σ[ τ' ∈ htyp ]
        ((d == ⦇⌜ d' ⌟⦈⟨ u , σ ⟩) ×
         (Δ , ∅ ⊢ d' :: τ') ×
         (d' final) ×
         ((u :: num [ Γ ]) ∈ Δ) ×
         (Δ , ∅ ⊢ σ :s: Γ)
        )
        → cif-num Δ d
    CIFNCast : ∀{Δ d} →
      Σ[ d' ∈ ihexp ]
        ((d == d' ⟨ ⦇-⦈ ⇒ num ⟩) ×
         (Δ , ∅ ⊢ d' :: ⦇-⦈) ×
         (d' indet) ×
         ((d'' : ihexp) (τ' : htyp) → d' ≠ (d'' ⟨ τ' ⇒ ⦇-⦈ ⟩))
        )
        → cif-num Δ d
    CIFNFailedCast : ∀{Δ d} →
      Σ[ d' ∈ ihexp ] Σ[ τ' ∈ htyp ]
        ((d == d' ⟨ τ' ⇒⦇-⦈⇏ num ⟩) ×
         (Δ , ∅ ⊢ d' :: τ') ×
         (τ' ground) ×
         (τ' ≠ num)
        )
        → cif-num Δ d

  canonical-indeterminate-forms-num : ∀{Δ d} →
                                      Δ , ∅ ⊢ d :: num →
                                      d indet →
                                      cif-num Δ d
  canonical-indeterminate-forms-num TANum ()
  canonical-indeterminate-forms-num (TAPlus wt wt₁) (IPlus1 x x₁) = CIFNPlus1 (_ , _ , refl , wt , wt₁ , x , x₁)
  canonical-indeterminate-forms-num (TAPlus wt wt₁) (IPlus2 x x₁) = CIFNPlus2 (_ , _  , refl , wt , wt₁ , x , x₁)
  canonical-indeterminate-forms-num (TAVar x₁) ()
  canonical-indeterminate-forms-num (TAAp wt wt₁) (IAp x ind x₁) = CIFNAp (_ , _ , _ , refl , wt , wt₁ , ind , x₁ , x)
  canonical-indeterminate-forms-num {Δ = Δ} (TACase {τ1 = τ1} {τ2 = τ2} {x = x} {d1 = d1} {y = y} {d2 = d2} wt _ wt₁ _ wt₂) (ICase ninl ninr ncast ind) = CIFNCase (_ , _ , _ , _ , _ , _ , _ , refl , wt , tr (λ Γ' → Δ , Γ' ⊢ d1 :: num) (extend-empty x τ1) wt₁ , tr (λ Γ' → Δ , Γ' ⊢ d2 :: num) (extend-empty y τ2) wt₂ , ind , ninl , ninr , ncast)
  canonical-indeterminate-forms-num (TAFst wt) (IFst x x₁ ind) = CIFNFst (_ , _ , refl , wt , ind , x , x₁)
  canonical-indeterminate-forms-num (TASnd wt) (ISnd x x₁ ind) = CIFNSnd (_ , _ , refl , wt , ind , x , x₁)
  canonical-indeterminate-forms-num (TAEHole x x₁) IEHole = CIFNEHole (_ , _ , _ , refl , x , x₁)
  canonical-indeterminate-forms-num (TANEHole x wt x₁) (INEHole x₂) = CIFNNEHole (_ , _ , _ , _ , _ , refl , wt , x₂ , x , x₁)
  canonical-indeterminate-forms-num (TACast wt x) (ICastHoleGround x₁ ind x₂) = CIFNCast (_ , refl , wt , ind , x₁)
  canonical-indeterminate-forms-num (TAFailedCast x x₁ x₂ x₃) (IFailedCast x₄ x₅ x₆ x₇) = CIFNFailedCast (_ , _ , refl , x , x₅ , x₇)
  
  -- this type gives somewhat nicer syntax for the output of the canonical
  -- forms lemma for indeterminates at arrow type
  data cif-arr : (Δ : hctx) (d : ihexp) (τ1 τ2 : htyp) → Set where
    CIFAEHole : ∀{d Δ τ1 τ2} →
      Σ[ u ∈ Nat ] Σ[ σ ∈ env ] Σ[ Γ ∈ tctx ]
        ((d == ⦇-⦈⟨ u , σ ⟩) ×
         ((u :: (τ1 ==> τ2) [ Γ ]) ∈ Δ) ×
         (Δ , ∅ ⊢ σ :s: Γ)
        )
      → cif-arr Δ d τ1 τ2
    CIFANEHole : ∀{d Δ τ1 τ2} →
      Σ[ u ∈ Nat ] Σ[ σ ∈ env ] Σ[ d' ∈ ihexp ] Σ[ τ' ∈ htyp ] Σ[ Γ ∈ tctx ]
        ((d == ⦇⌜ d' ⌟⦈⟨ u , σ ⟩) ×
         (Δ , ∅ ⊢ d' :: τ') ×
         (d' final) ×
         ((u :: (τ1 ==> τ2) [ Γ ]) ∈ Δ) ×
         (Δ , ∅ ⊢ σ :s: Γ)
        )
        → cif-arr Δ d τ1 τ2
    CIFAAp : ∀{d Δ τ1 τ2} →
      Σ[ d1 ∈ ihexp ] Σ[ d2 ∈ ihexp ] Σ[ τ2' ∈ htyp ] Σ[ τ1 ∈ htyp ] Σ[ τ2 ∈ htyp ]
        ((d == d1 ∘ d2) ×
         (Δ , ∅ ⊢ d1 :: τ2' ==> (τ1 ==> τ2)) ×
         (Δ , ∅ ⊢ d2 :: τ2') ×
         (d1 indet) ×
         (d2 final) ×
         ((τ3 τ4 τ3' τ4' : htyp) (d1' : ihexp) → d1 ≠ (d1' ⟨ τ3 ==> τ4 ⇒ τ3' ==> τ4' ⟩))
        )
        → cif-arr Δ d τ1 τ2
    CIFACase : ∀{Δ d τ1 τ2} →
      Σ[ d1 ∈ ihexp ] Σ[ x ∈ Nat ] Σ[ d2 ∈ ihexp ] Σ[ y ∈ Nat ] Σ[ d3 ∈ ihexp ]
      Σ[ τ3 ∈ htyp ] Σ[ τ4 ∈ htyp ]
        ((d == case d1 x d2 y d3) ×
         (Δ , ∅ ⊢ d1 :: τ3 ⊕ τ4) ×
         (Δ , ■ (x , τ3) ⊢ d2 :: τ1 ==> τ2) ×
         (Δ , ■ (y , τ4) ⊢ d3 :: τ1 ==> τ2) ×
         (d1 indet) ×
         ((τ : htyp) (d' : ihexp) → d1 ≠ inl τ d') ×
         ((τ : htyp) (d' : ihexp) → d1 ≠ inr τ d') ×
         ((τ5 τ6 τ5' τ6' : htyp) (d' : ihexp) →
           d1 ≠ (d' ⟨(τ5 ⊕ τ6) ⇒ (τ5' ⊕ τ6')⟩))
        )
        → cif-arr Δ d τ1 τ2
    CIFAFst : ∀{Δ d τ1 τ2} →
      Σ[ d' ∈ ihexp ] Σ[ τ' ∈ htyp ]
        ((d == fst d') ×
         (Δ , ∅ ⊢ d' :: (τ1 ==> τ2) ⊠ τ') ×
         (d' indet) ×
         ((d1 d2 : ihexp) → d' ≠ ⟨ d1 , d2 ⟩) ×
         ((τ3 τ4 τ3' τ4' : htyp) (d'' : ihexp) →
           d' ≠ (d'' ⟨(τ3 ⊠ τ4) ⇒ (τ3' ⊠ τ4')⟩))
        )
        → cif-arr Δ d τ1 τ2
    CIFASnd : ∀{Δ d τ1 τ2} →
      Σ[ d' ∈ ihexp ] Σ[ τ' ∈ htyp ]
        ((d == snd d') ×
         (Δ , ∅ ⊢ d' :: τ' ⊠ (τ1 ==> τ2)) ×
         (d' indet) ×
         ((d1 d2 : ihexp) → d' ≠ ⟨ d1 , d2 ⟩) ×
         ((τ3 τ4 τ3' τ4' : htyp) (d'' : ihexp) →
           d' ≠ (d'' ⟨(τ3 ⊠ τ4) ⇒ (τ3' ⊠ τ4')⟩)) 
        )
        → cif-arr Δ d τ1 τ2
    CIFACast : ∀{d Δ τ1 τ2} →
      Σ[ d' ∈ ihexp ] Σ[ τ1 ∈ htyp ] Σ[ τ2 ∈ htyp ] Σ[ τ1' ∈ htyp ] Σ[ τ2' ∈ htyp ]
        ((d == d' ⟨ (τ1' ==> τ2') ⇒ (τ1 ==> τ2) ⟩) ×
         (Δ , ∅ ⊢ d' :: τ1' ==> τ2') ×
         (d' indet) ×
         ((τ1' ==> τ2') ≠ (τ1 ==> τ2))
        )
       → cif-arr Δ d τ1 τ2
    CIFACastHole : ∀{d Δ τ1 τ2} →
      Σ[ d' ∈ ihexp ]
        ((d == (d' ⟨ ⦇-⦈ ⇒ ⦇-⦈ ==> ⦇-⦈ ⟩)) ×
         (τ1 == ⦇-⦈) ×
         (τ2 == ⦇-⦈) ×
         (Δ , ∅ ⊢ d' :: ⦇-⦈) ×
         (d' indet) ×
         ((d'' : ihexp) (τ' : htyp) → d' ≠ (d'' ⟨ τ' ⇒ ⦇-⦈ ⟩))
        )
        → cif-arr Δ d τ1 τ2
    CIFAFailedCast : ∀{d Δ τ1 τ2} →
      Σ[ d' ∈ ihexp ] Σ[ τ' ∈ htyp ]
        ((d == (d' ⟨ τ' ⇒⦇-⦈⇏ ⦇-⦈ ==> ⦇-⦈ ⟩) ) ×
         (τ1 == ⦇-⦈) ×
         (τ2 == ⦇-⦈) ×
         (Δ , ∅ ⊢ d' :: τ') ×
         (τ' ground) ×
         (τ' ≠ (⦇-⦈ ==> ⦇-⦈))
        )
        → cif-arr Δ d τ1 τ2

  canonical-indeterminate-forms-arr : ∀{Δ d τ1 τ2 } →
                                      Δ , ∅ ⊢ d :: (τ1 ==> τ2) →
                                      d indet →
                                      cif-arr Δ d τ1 τ2
  canonical-indeterminate-forms-arr (TAVar x₁) ()
  canonical-indeterminate-forms-arr (TALam _ wt) ()
  canonical-indeterminate-forms-arr (TAAp wt wt₁) (IAp x ind x₁) = CIFAAp (_ , _ , _ , _ , _ , refl , wt , wt₁ , ind , x₁ , x)
  canonical-indeterminate-forms-arr {Δ = Δ} (TACase {τ1 = τ1} {τ2 = τ2} {τ = τ3 ==> τ4} {x = x} {d1 = d1} {y = y} {d2 = d2} wt _ wt₁ _ wt₂) (ICase ninl ninr ncast ind) = CIFACase (_ , _ , _ , _ , _ , _ , _ , refl , wt , tr (λ Γ' → Δ , Γ' ⊢ d1 :: τ3 ==> τ4) (extend-empty x τ1) wt₁ , tr (λ Γ' → Δ , Γ' ⊢ d2 :: τ3 ==> τ4) (extend-empty y τ2) wt₂ , ind , ninl , ninr , ncast)
  canonical-indeterminate-forms-arr (TAFst wt) (IFst x x₁ ind) = CIFAFst (_ , _ , refl , wt , ind , x , x₁)
  canonical-indeterminate-forms-arr (TASnd wt) (ISnd x x₁ ind) = CIFASnd (_ , _ , refl , wt , ind , x , x₁)
  canonical-indeterminate-forms-arr (TAEHole x x₁) IEHole = CIFAEHole (_ , _ , _ , refl , x , x₁)
  canonical-indeterminate-forms-arr (TANEHole x wt x₁) (INEHole x₂) = CIFANEHole (_ , _ , _ , _ , _ , refl , wt , x₂ , x , x₁)
  canonical-indeterminate-forms-arr (TACast wt x) (ICastArr x₁ ind) = CIFACast (_ , _ , _ , _ , _ , refl , wt , ind , x₁)
  canonical-indeterminate-forms-arr (TACast wt TCHole2) (ICastHoleGround x₁ ind GArrHole) = CIFACastHole (_ , refl , refl , refl , wt , ind , x₁)
  canonical-indeterminate-forms-arr (TAFailedCast x x₁ GArrHole x₃) (IFailedCast x₄ x₅ GArrHole x₇) = CIFAFailedCast (_ , _ , refl , refl , refl , x , x₅ , x₇)
  
  -- this type gives somewhat nicer syntax for the output of the canonical
  -- forms lemma for indeterminates at sum type
  data cif-sum : (Δ : hctx) (d : ihexp) (τ1 τ2 : htyp) → Set where
    CIFSEHole : ∀{d Δ τ1 τ2} →
      Σ[ u ∈ Nat ] Σ[ σ ∈ env ] Σ[ Γ ∈ tctx ]
        ((d == ⦇-⦈⟨ u , σ ⟩) ×
         ((u :: (τ1 ⊕ τ2) [ Γ ]) ∈ Δ) ×
         (Δ , ∅ ⊢ σ :s: Γ)
        )
      → cif-sum Δ d τ1 τ2
    CIFSNEHole : ∀{d Δ τ1 τ2} →
      Σ[ u ∈ Nat ] Σ[ σ ∈ env ] Σ[ d' ∈ ihexp ] Σ[ τ' ∈ htyp ] Σ[ Γ ∈ tctx ]
        ((d == ⦇⌜ d' ⌟⦈⟨ u , σ ⟩) ×
         (Δ , ∅ ⊢ d' :: τ') ×
         (d' final) ×
         ((u :: (τ1 ⊕ τ2) [ Γ ]) ∈ Δ) ×
         (Δ , ∅ ⊢ σ :s: Γ)
        )
        → cif-sum Δ d τ1 τ2
    CIFSAp : ∀{d Δ τ1 τ2} →
      Σ[ d1 ∈ ihexp ] Σ[ d2 ∈ ihexp ] Σ[ τ2' ∈ htyp ] Σ[ τ1 ∈ htyp ] Σ[ τ2 ∈ htyp ]
        ((d == d1 ∘ d2) ×
         (Δ , ∅ ⊢ d1 :: τ2' ==> (τ1 ⊕ τ2)) ×
         (Δ , ∅ ⊢ d2 :: τ2') ×
         (d1 indet) ×
         (d2 final) ×
         ((τ3 τ4 τ3' τ4' : htyp) (d1' : ihexp) → d1 ≠ (d1' ⟨ τ3 ==> τ4 ⇒ τ3' ==> τ4' ⟩))
        )
        → cif-sum Δ d τ1 τ2
    CIFSInl : ∀{Δ d τ1 τ2} →
      Σ[ d' ∈ ihexp ]
        ((d == inl τ2 d') ×
         (Δ , ∅ ⊢ d' :: τ1) ×
         (d' indet)
        )
        → cif-sum Δ d τ1 τ2
    CIFSInr : ∀{Δ d τ1 τ2} →
      Σ[ d' ∈ ihexp ]
        ((d == inr τ1 d') ×
         (Δ , ∅ ⊢ d' :: τ2) ×
         (d' indet)
        )
        → cif-sum Δ d τ1 τ2
    CIFSCase : ∀{Δ d τ1 τ2} →
      Σ[ d1 ∈ ihexp ] Σ[ x ∈ Nat ] Σ[ d2 ∈ ihexp ] Σ[ y ∈ Nat ] Σ[ d3 ∈ ihexp ]
      Σ[ τ3 ∈ htyp ] Σ[ τ4 ∈ htyp ]
        ((d == case d1 x d2 y d3) ×
         (Δ , ∅ ⊢ d1 :: τ3 ⊕ τ4) ×
         (Δ , ■ (x , τ3) ⊢ d2 :: τ1 ⊕ τ2) ×
         (Δ , ■ (y , τ4) ⊢ d3 :: τ1 ⊕ τ2) ×
         (d1 indet) ×
         ((τ : htyp) (d' : ihexp) → d1 ≠ inl τ d') ×
         ((τ : htyp) (d' : ihexp) → d1 ≠ inr τ d') ×
         ((τ5 τ6 τ5' τ6' : htyp) (d' : ihexp) →
           d1 ≠ (d' ⟨(τ5 ⊕ τ6) ⇒ (τ5' ⊕ τ6')⟩))
        )
        → cif-sum Δ d τ1 τ2
    CIFSFst : ∀{Δ d τ1 τ2} →
      Σ[ d' ∈ ihexp ] Σ[ τ' ∈ htyp ]
        ((d == fst d') ×
         (Δ , ∅ ⊢ d' :: (τ1 ⊕ τ2) ⊠ τ') ×
         (d' indet) ×
         ((d1 d2 : ihexp) → d' ≠ ⟨ d1 , d2 ⟩) ×
         ((τ3 τ4 τ3' τ4' : htyp) (d'' : ihexp) →
           d' ≠ (d'' ⟨(τ3 ⊠ τ4) ⇒ (τ3' ⊠ τ4')⟩)) 
        )
        → cif-sum Δ d τ1 τ2
    CIFSSnd : ∀{Δ d τ1 τ2} →
      Σ[ d' ∈ ihexp ] Σ[ τ' ∈ htyp ]
        ((d == snd d') ×
         (Δ , ∅ ⊢ d' :: τ' ⊠ (τ1 ⊕ τ2)) ×
         (d' indet) ×
         ((d1 d2 : ihexp) → d' ≠ ⟨ d1 , d2 ⟩) ×
         ((τ3 τ4 τ3' τ4' : htyp) (d'' : ihexp) →
           d' ≠ (d'' ⟨(τ3 ⊠ τ4) ⇒ (τ3' ⊠ τ4')⟩)) 
        )
        → cif-sum Δ d τ1 τ2
    CIFSCast : ∀{d Δ τ1 τ2} →
      Σ[ d' ∈ ihexp ] Σ[ τ1 ∈ htyp ] Σ[ τ2 ∈ htyp ] Σ[ τ1' ∈ htyp ] Σ[ τ2' ∈ htyp ]
        ((d == d' ⟨ (τ1' ⊕ τ2') ⇒ (τ1 ⊕ τ2) ⟩) ×
         (Δ , ∅ ⊢ d' :: τ1' ⊕ τ2') ×
         (d' indet) ×
         ((τ1' ⊕ τ2') ≠ (τ1 ⊕ τ2))
        )
       → cif-sum Δ d τ1 τ2
    CIFSCastHole : ∀{d Δ τ1 τ2} →
      Σ[ d' ∈ ihexp ]
        ((d == (d' ⟨ ⦇-⦈ ⇒ ⦇-⦈ ⊕ ⦇-⦈ ⟩)) ×
         (τ1 == ⦇-⦈) ×
         (τ2 == ⦇-⦈) ×
         (Δ , ∅ ⊢ d' :: ⦇-⦈) ×
         (d' indet) ×
         ((d'' : ihexp) (τ' : htyp) → d' ≠ (d'' ⟨ τ' ⇒ ⦇-⦈ ⟩))
        )
        → cif-sum Δ d τ1 τ2
    CIFSFailedCast : ∀{d Δ τ1 τ2} →
      Σ[ d' ∈ ihexp ] Σ[ τ' ∈ htyp ]
        ((d == (d' ⟨ τ' ⇒⦇-⦈⇏ ⦇-⦈ ⊕ ⦇-⦈ ⟩) ) ×
         (τ1 == ⦇-⦈) ×
         (τ2 == ⦇-⦈) ×
         (Δ , ∅ ⊢ d' :: τ') ×
         (τ' ground) ×
         (τ' ≠ (⦇-⦈ ⊕ ⦇-⦈))
        )
        → cif-sum Δ d τ1 τ2

  canonical-indeterminate-forms-sum : ∀{Δ d τ1 τ2 } →
                                      Δ , ∅ ⊢ d :: (τ1 ⊕ τ2) →
                                      d indet →
                                      cif-sum Δ d τ1 τ2
  canonical-indeterminate-forms-sum (TAAp wt wt₁) (IAp x ind x₁) = CIFSAp (_ , _ , _ , _ , _ , refl , wt , wt₁ , ind , x₁ , x)
  canonical-indeterminate-forms-sum (TAInl wt) (IInl ind) = CIFSInl (_ , refl , wt , ind)
  canonical-indeterminate-forms-sum (TAInr wt) (IInr ind) = CIFSInr (_ , refl , wt , ind)
  canonical-indeterminate-forms-sum {Δ = Δ} (TACase {τ1 = τ1} {τ2 = τ2} {τ = τ3 ⊕ τ4} {x = x} {d1 = d1} {y = y} {d2 = d2} wt _ wt₁ _ wt₂) (ICase ninl ninr ncast ind) = CIFSCase (_ , _ , _ , _ , _ , _ , _ , refl , wt , tr (λ Γ' → Δ , Γ' ⊢ d1 :: (τ3 ⊕ τ4)) (extend-empty x τ1) wt₁ , tr (λ Γ' → Δ , Γ' ⊢ d2 :: (τ3 ⊕ τ4)) (extend-empty y τ2) wt₂ , ind , ninl , ninr , ncast)
  canonical-indeterminate-forms-sum (TAFst wt) (IFst x x₁ ind) = CIFSFst (_ , _ , refl , wt , ind , x , x₁)
  canonical-indeterminate-forms-sum (TASnd wt) (ISnd x x₁ ind) = CIFSSnd (_ , _ , refl , wt , ind , x , x₁)
  canonical-indeterminate-forms-sum (TAEHole x x₁) IEHole = CIFSEHole (_ , _ , _ , refl , x , x₁)
  canonical-indeterminate-forms-sum (TANEHole x wt x₁) (INEHole x₂) = CIFSNEHole (_ , _ , _ , _ , _ , refl , wt , x₂ , x , x₁)
  canonical-indeterminate-forms-sum (TACast wt x) (ICastSum x₁ ind) = CIFSCast (_ , _ , _ , _ , _ , refl , wt , ind , x₁)
  canonical-indeterminate-forms-sum (TACast wt x) (ICastHoleGround x₁ ind GSumHole) = CIFSCastHole (_ , refl , refl , refl , wt , ind , x₁)
  canonical-indeterminate-forms-sum (TAFailedCast wt x x₁ x₂) (IFailedCast x₃ x₄ GSumHole x₆) = CIFSFailedCast (_ , _ , refl , refl , refl , wt , x₄ , x₆)
  canonical-indeterminate-forms-sum (TAVar x) ()
  
  -- this type gives somewhat nicer syntax for the output of the canonical
  -- forms lemma for indeterminates at product type
  data cif-prod : (Δ : hctx) (d : ihexp) (τ1 τ2 : htyp) → Set where
    CIFPEHole : ∀{d Δ τ1 τ2} →
      Σ[ u ∈ Nat ] Σ[ σ ∈ env ] Σ[ Γ ∈ tctx ]
        ((d == ⦇-⦈⟨ u , σ ⟩) ×
         ((u :: (τ1 ⊠ τ2) [ Γ ]) ∈ Δ) ×
         (Δ , ∅ ⊢ σ :s: Γ)
        )
      → cif-prod Δ d τ1 τ2
    CIFPNEHole : ∀{d Δ τ1 τ2} →
      Σ[ u ∈ Nat ] Σ[ σ ∈ env ] Σ[ d' ∈ ihexp ] Σ[ τ' ∈ htyp ] Σ[ Γ ∈ tctx ]
        ((d == ⦇⌜ d' ⌟⦈⟨ u , σ ⟩) ×
         (Δ , ∅ ⊢ d' :: τ') ×
         (d' final) ×
         ((u :: (τ1 ⊠ τ2) [ Γ ]) ∈ Δ) ×
         (Δ , ∅ ⊢ σ :s: Γ)
        )
        → cif-prod Δ d τ1 τ2
    CIFPAp : ∀{d Δ τ1 τ2} →
      Σ[ d1 ∈ ihexp ] Σ[ d2 ∈ ihexp ] Σ[ τ2' ∈ htyp ] Σ[ τ1 ∈ htyp ] Σ[ τ2 ∈ htyp ]
        ((d == d1 ∘ d2) ×
         (Δ , ∅ ⊢ d1 :: τ2' ==> (τ1 ⊠ τ2)) ×
         (Δ , ∅ ⊢ d2 :: τ2') ×
         (d1 indet) ×
         (d2 final) ×
         ((τ3 τ4 τ3' τ4' : htyp) (d1' : ihexp) → d1 ≠ (d1' ⟨ τ3 ==> τ4 ⇒ τ3' ==> τ4' ⟩))
        )
        → cif-prod Δ d τ1 τ2
    CIFPCase : ∀{Δ d τ1 τ2} →
      Σ[ d1 ∈ ihexp ] Σ[ x ∈ Nat ] Σ[ d2 ∈ ihexp ] Σ[ y ∈ Nat ] Σ[ d3 ∈ ihexp ]
      Σ[ τ3 ∈ htyp ] Σ[ τ4 ∈ htyp ]
        ((d == case d1 x d2 y d3) ×
         (Δ , ∅ ⊢ d1 :: τ3 ⊕ τ4) ×
         (Δ , ■ (x , τ3) ⊢ d2 :: τ1 ⊠ τ2) ×
         (Δ , ■ (y , τ4) ⊢ d3 :: τ1 ⊠ τ2) ×
         (d1 indet) ×
         ((τ : htyp) (d' : ihexp) → d1 ≠ inl τ d') ×
         ((τ : htyp) (d' : ihexp) → d1 ≠ inr τ d') ×
         ((τ5 τ6 τ5' τ6' : htyp) (d' : ihexp) →
           d1 ≠ (d' ⟨(τ5 ⊕ τ6) ⇒ (τ5' ⊕ τ6')⟩))
        )
        → cif-prod Δ d τ1 τ2
    CIFPPair1 : ∀{Δ d τ1 τ2} →
      Σ[ d1 ∈ ihexp ] Σ[ d2 ∈ ihexp ]
        ((d == ⟨ d1 , d2 ⟩) ×
         (Δ , ∅ ⊢ d1 :: τ1) ×
         (Δ , ∅ ⊢ d2 :: τ2) ×
         d1 indet ×
         d2 final
        )
        → cif-prod Δ d τ1 τ2
    CIFPPair2 : ∀{Δ d τ1 τ2} →
      Σ[ d1 ∈ ihexp ] Σ[ d2 ∈ ihexp ]
        ((d == ⟨ d1 , d2 ⟩) ×
         (Δ , ∅ ⊢ d1 :: τ1) ×
         (Δ , ∅ ⊢ d2 :: τ2) ×
         d1 final ×
         d2 indet
        )
        → cif-prod Δ d τ1 τ2
    CIFPFst : ∀{Δ d τ1 τ2} →
      Σ[ d' ∈ ihexp ] Σ[ τ' ∈ htyp ]
        ((d == fst d') ×
         (Δ , ∅ ⊢ d' :: (τ1 ⊠ τ2) ⊠ τ') ×
         (d' indet) ×
         ((d1 d2 : ihexp) → d' ≠ ⟨ d1 , d2 ⟩) ×
         ((τ3 τ4 τ3' τ4' : htyp) (d'' : ihexp) →
           d' ≠ (d'' ⟨(τ3 ⊠ τ4) ⇒ (τ3' ⊠ τ4')⟩)) 
        )
        → cif-prod Δ d τ1 τ2
    CIFPSnd : ∀{Δ d τ1 τ2} →
      Σ[ d' ∈ ihexp ] Σ[ τ' ∈ htyp ]
        ((d == snd d') ×
         (Δ , ∅ ⊢ d' :: τ' ⊠ (τ1 ⊠ τ2)) ×
         (d' indet) ×
         ((d1 d2 : ihexp) → d' ≠ ⟨ d1 , d2 ⟩) ×
         ((τ3 τ4 τ3' τ4' : htyp) (d'' : ihexp) →
           d' ≠ (d'' ⟨(τ3 ⊠ τ4) ⇒ (τ3' ⊠ τ4')⟩)) 
        )
        → cif-prod Δ d τ1 τ2
    CIFPCast : ∀{d Δ τ1 τ2} →
      Σ[ d' ∈ ihexp ] Σ[ τ1 ∈ htyp ] Σ[ τ2 ∈ htyp ] Σ[ τ1' ∈ htyp ] Σ[ τ2' ∈ htyp ]
        ((d == d' ⟨ (τ1' ⊠ τ2') ⇒ (τ1 ⊠ τ2) ⟩) ×
         (Δ , ∅ ⊢ d' :: τ1' ⊠ τ2') ×
         (d' indet) ×
         ((τ1' ⊠ τ2') ≠ (τ1 ⊠ τ2))
        )
       → cif-prod Δ d τ1 τ2
    CIFPCastHole : ∀{d Δ τ1 τ2} →
      Σ[ d' ∈ ihexp ]
        ((d == (d' ⟨ ⦇-⦈ ⇒ ⦇-⦈ ⊠ ⦇-⦈ ⟩)) ×
         (τ1 == ⦇-⦈) ×
         (τ2 == ⦇-⦈) ×
         (Δ , ∅ ⊢ d' :: ⦇-⦈) ×
         (d' indet) ×
         ((d'' : ihexp) (τ' : htyp) → d' ≠ (d'' ⟨ τ' ⇒ ⦇-⦈ ⟩))
        )
        → cif-prod Δ d τ1 τ2
    CIFPFailedCast : ∀{d Δ τ1 τ2} →
      Σ[ d' ∈ ihexp ] Σ[ τ' ∈ htyp ]
        ((d == (d' ⟨ τ' ⇒⦇-⦈⇏ ⦇-⦈ ⊠ ⦇-⦈ ⟩) ) ×
         (τ1 == ⦇-⦈) ×
         (τ2 == ⦇-⦈) ×
         (Δ , ∅ ⊢ d' :: τ') ×
         (τ' ground) ×
         (τ' ≠ (⦇-⦈ ⊠ ⦇-⦈))
        )
        → cif-prod Δ d τ1 τ2

  canonical-indeterminate-forms-prod : ∀{Δ d τ1 τ2} →
                                       Δ , ∅ ⊢ d :: (τ1 ⊠ τ2) →
                                       d indet →
                                       cif-prod Δ d τ1 τ2
  canonical-indeterminate-forms-prod (TAVar x) ()
  canonical-indeterminate-forms-prod (TAAp wt wt₁) (IAp x ind x₁) = CIFPAp (_ , _ , _ , _ , _ , refl , wt , wt₁ , ind , x₁ , x)
  canonical-indeterminate-forms-prod {Δ = Δ} (TACase {τ1 = τ1} {τ2 = τ2} {τ = τ3 ⊠ τ4} {x = x} {d1 = d1} {y = y} {d2 = d2} wt _ wt₁ _ wt₂) (ICase ninl ninr ncast ind) = CIFPCase (_ , _ , _ , _ , _ , _ , _ , refl , wt , tr (λ Γ' → Δ , Γ' ⊢ d1 :: (τ3 ⊠ τ4)) (extend-empty x τ1) wt₁ , tr (λ Γ' → Δ , Γ' ⊢ d2 :: (τ3 ⊠ τ4)) (extend-empty y τ2) wt₂ , ind , ninl , ninr , ncast)
  canonical-indeterminate-forms-prod (TAPair wt wt₁) (IPair1 ind x) = CIFPPair1 (_ , _ , refl , wt , wt₁ , ind , x)
  canonical-indeterminate-forms-prod (TAPair wt wt₁) (IPair2 x ind) = CIFPPair2 (_ , _ , refl , wt , wt₁ , x , ind)
  canonical-indeterminate-forms-prod (TAFst wt) (IFst x x₁ ind) = CIFPFst (_ , _ , refl , wt , ind , x , x₁)
  canonical-indeterminate-forms-prod (TASnd wt) (ISnd x x₁ ind) = CIFPSnd (_ , _ , refl , wt , ind , x , x₁)
  canonical-indeterminate-forms-prod (TAEHole x x₁) IEHole = CIFPEHole (_ , _ , _ , refl , x , x₁)
  canonical-indeterminate-forms-prod (TANEHole x wt x₁) (INEHole x₂) = CIFPNEHole (_ , _ , _ , _ , _ , refl , wt , x₂ , x , x₁)
  canonical-indeterminate-forms-prod (TACast wt x) (ICastProd x₁ ind) = CIFPCast (_ , _ , _ , _ , _ , refl , wt , ind , x₁)
  canonical-indeterminate-forms-prod (TACast wt x) (ICastHoleGround x₁ ind GProdHole) = CIFPCastHole (_ , refl , refl , refl , wt , ind , x₁)
  canonical-indeterminate-forms-prod (TAFailedCast wt x GProdHole x₂) (IFailedCast x₃ x₄ GProdHole x₆) = CIFPFailedCast (_ , _ , refl , refl , refl , wt , x₄ , x₆)

  
  -- this type gives somewhat nicer syntax for the output of the canonical
  -- forms lemma for indeterminates at hole type
  data cif-hole : (Δ : hctx) (d : ihexp) → Set where
    CIFHEHole : ∀{Δ d} →
      Σ[ u ∈ Nat ] Σ[ σ ∈ env ] Σ[ Γ ∈ tctx ]
        ((d == ⦇-⦈⟨ u , σ ⟩) ×
         ((u :: ⦇-⦈ [ Γ ]) ∈ Δ) ×
         (Δ , ∅ ⊢ σ :s: Γ)
        )
      → cif-hole Δ d
    CIFHNEHole : ∀{Δ d} →
      Σ[ u ∈ Nat ] Σ[ σ ∈ env ] Σ[ d' ∈ ihexp ] Σ[ τ' ∈ htyp ] Σ[ Γ ∈ tctx ]
        ((d == ⦇⌜ d' ⌟⦈⟨ u , σ ⟩) ×
         (Δ , ∅ ⊢ d' :: τ') ×
         (d' final) ×
         ((u :: ⦇-⦈ [ Γ ]) ∈ Δ) ×
         (Δ , ∅ ⊢ σ :s: Γ)
        )
      → cif-hole Δ d
    CIFHAp : ∀{Δ d} →
      Σ[ d1 ∈ ihexp ] Σ[ d2 ∈ ihexp ] Σ[ τ2 ∈ htyp ]
        ((d == d1 ∘ d2) ×
         (Δ , ∅ ⊢ d1 :: (τ2 ==> ⦇-⦈)) ×
         (Δ , ∅ ⊢ d2 :: τ2) ×
         (d1 indet) ×
         (d2 final) ×
         ((τ3 τ4 τ3' τ4' : htyp) (d1' : ihexp) → d1 ≠ (d1' ⟨ τ3 ==> τ4 ⇒ τ3' ==> τ4' ⟩))
        )
      → cif-hole Δ d
    CIFHCase : ∀{Δ d} →
      Σ[ d1 ∈ ihexp ] Σ[ x ∈ Nat ] Σ[ d2 ∈ ihexp ] Σ[ y ∈ Nat ] Σ[ d3 ∈ ihexp ]
      Σ[ τ1 ∈ htyp ] Σ[ τ2 ∈ htyp ]
        ((d == case d1 x d2 y d3) ×
         (Δ , ∅ ⊢ d1 :: τ1 ⊕ τ2) ×
         (Δ , ■ (x , τ1) ⊢ d2 :: ⦇-⦈) ×
         (Δ , ■ (y , τ2) ⊢ d3 :: ⦇-⦈) ×
         (d1 indet) ×
         ((τ : htyp) (d' : ihexp) → d1 ≠ inl τ d') ×
         ((τ : htyp) (d' : ihexp) → d1 ≠ inr τ d') ×
         ((τ3 τ4 τ3' τ4' : htyp) (d' : ihexp) →
           d1 ≠ (d' ⟨(τ3 ⊕ τ4) ⇒ (τ3' ⊕ τ4')⟩))
        )
        → cif-hole Δ d
    CIFHFst : ∀{Δ d} →
      Σ[ d' ∈ ihexp ] Σ[ τ' ∈ htyp ]
        ((d == fst d') ×
         (Δ , ∅ ⊢ d' :: ⦇-⦈ ⊠ τ') ×
         (d' indet) ×
         ((d1 d2 : ihexp) → d' ≠ ⟨ d1 , d2 ⟩) ×
         ((τ3 τ4 τ3' τ4' : htyp) (d'' : ihexp) →
           d' ≠ (d'' ⟨(τ3 ⊠ τ4) ⇒ (τ3' ⊠ τ4')⟩)) 
        )
        → cif-hole Δ d
    CIFHSnd : ∀{Δ d} →
      Σ[ d' ∈ ihexp ] Σ[ τ' ∈ htyp ]
        ((d == snd d') ×
         (Δ , ∅ ⊢ d' :: τ' ⊠ ⦇-⦈) ×
         (d' indet) ×
         ((d1 d2 : ihexp) → d' ≠ ⟨ d1 , d2 ⟩) ×
         ((τ3 τ4 τ3' τ4' : htyp) (d'' : ihexp) →
           d' ≠ (d'' ⟨(τ3 ⊠ τ4) ⇒ (τ3' ⊠ τ4')⟩)) 
        )
        → cif-hole Δ d
    CIFHCast : ∀{Δ d} →
      Σ[ d' ∈ ihexp ] Σ[ τ' ∈ htyp ]
        ((d == d' ⟨ τ' ⇒ ⦇-⦈ ⟩) ×
         (Δ , ∅ ⊢ d' :: τ') ×
         (τ' ground) ×
         (d' indet)
        )
      → cif-hole Δ d

  canonical-indeterminate-forms-hole : ∀{Δ d} →
                                       Δ , ∅ ⊢ d :: ⦇-⦈ →
                                       d indet →
                                       cif-hole Δ d
  canonical-indeterminate-forms-hole (TAVar x₁) ()
  canonical-indeterminate-forms-hole (TAAp wt wt₁) (IAp x ind x₁) = CIFHAp (_ , _ , _ , refl , wt , wt₁ , ind , x₁ , x)
  canonical-indeterminate-forms-hole {Δ = Δ} (TACase {τ1 = τ1} {τ2 = τ2} {x = x} {d1 = d1} {y = y} {d2 = d2} wt _ wt₁ _ wt₂) (ICase ninl ninr ncast ind) = CIFHCase (_ , _ , _ , _ , _ , _ , _ , refl , wt , tr (λ Γ' → Δ , Γ' ⊢ d1 :: ⦇-⦈) (extend-empty x τ1) wt₁ , tr (λ Γ' → Δ , Γ' ⊢ d2 :: ⦇-⦈) (extend-empty y τ2) wt₂ , ind , ninl , ninr , ncast)
  canonical-indeterminate-forms-hole (TAFst wt) (IFst x x₁ ind) = CIFHFst (_ , _ , refl , wt , ind , x , x₁)
  canonical-indeterminate-forms-hole (TASnd wt) (ISnd x x₁ ind) = CIFHSnd (_ , _ , refl , wt , ind , x , x₁)
  canonical-indeterminate-forms-hole (TAEHole x x₁) IEHole = CIFHEHole (_ , _ , _ , refl , x , x₁)
  canonical-indeterminate-forms-hole (TANEHole x wt x₁) (INEHole x₂) = CIFHNEHole (_ , _ , _ , _ , _ , refl , wt , x₂ , x , x₁)
  canonical-indeterminate-forms-hole (TACast wt x) (ICastGroundHole x₁ ind) = CIFHCast (_ , _ , refl , wt , x₁ , ind)
  canonical-indeterminate-forms-hole (TACast wt x) (ICastHoleGround x₁ ind ())
  canonical-indeterminate-forms-hole (TAFailedCast x x₁ () x₃) (IFailedCast x₄ x₅ x₆ x₇)
  
  canonical-indeterminate-forms-coverage : ∀{Δ d τ} →
                                           Δ , ∅ ⊢ d :: τ →
                                           d indet →
                                           τ ≠ num →
                                           ((τ1 : htyp) (τ2 : htyp) → τ ≠ (τ1 ==> τ2)) →
                                           ((τ1 : htyp) (τ2 : htyp) → τ ≠ (τ1 ⊕ τ2)) →
                                           ((τ1 : htyp) (τ2 : htyp) → τ ≠ (τ1 ⊠ τ2)) →
                                           τ ≠ ⦇-⦈ →
                                           ⊥
  canonical-indeterminate-forms-coverage {τ = num} wt ind nn na ns np nh = nn refl
  canonical-indeterminate-forms-coverage {τ = ⦇-⦈} wt ind nn na ns np nh = nh refl
  canonical-indeterminate-forms-coverage {τ = τ ==> τ₁} wt ind nn na ns np nh = na τ τ₁ refl
  canonical-indeterminate-forms-coverage {τ = τ ⊕ τ₁} wt ind nn na ns np nh = ns τ τ₁ refl
  canonical-indeterminate-forms-coverage {τ = τ ⊠ τ₁} wt ind nn na ns np nh = np τ τ₁ refl
