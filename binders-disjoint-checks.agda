open import Prelude
open import Nat
open import dynamics-core


module binders-disjoint-checks where
  -- these are fairly mechanical lemmas that show that the
  -- judgementally-defined binders-disjoint is really a type-directed
  -- function

  -- numbers
  lem-bdσ-num : ∀{σ n} → binders-disjoint-σ σ (N n)
  lem-bdσ-num {σ = Id Γ} = BDσId
  lem-bdσ-num {σ = Subst d y σ} = BDσSubst BDNum lem-bdσ-num UBNum

  lem-bd-num : ∀{d n} → binders-disjoint d (N n)
  lem-bd-num {d = N x} = BDNum
  lem-bd-num {d = d ·+ d₁} = BDPlus lem-bd-num lem-bd-num
  lem-bd-num {d = X x} = BDVar
  lem-bd-num {d = ·λ x ·[ x₁ ] d} = BDLam lem-bd-num UBNum
  lem-bd-num {d = d ∘ d₁} = BDAp lem-bd-num lem-bd-num
  lem-bd-num {d = inl x d} = BDInl lem-bd-num
  lem-bd-num {d = inr x d} = BDInr lem-bd-num
  lem-bd-num {d = case d x d₁ x₁ d₂} = BDCase lem-bd-num UBNum lem-bd-num UBNum lem-bd-num
  lem-bd-num {d = ⟨ d , d₁ ⟩} = BDPair lem-bd-num lem-bd-num
  lem-bd-num {d = fst d} = BDFst lem-bd-num
  lem-bd-num {d = snd d} = BDSnd lem-bd-num
  lem-bd-num {d = ⦇-⦈⟨ u , σ ⟩} = BDHole lem-bdσ-num
  lem-bd-num {d = ⦇⌜ d ⌟⦈⟨ u , σ ⟩} = BDNEHole lem-bdσ-num lem-bd-num
  lem-bd-num {d = d ⟨ x ⇒ x₁ ⟩} = BDCast lem-bd-num
  lem-bd-num {d = d ⟨ x ⇒⦇-⦈⇏ x₁ ⟩} = BDFailedCast lem-bd-num
  
  -- plus
  lem-bdσ-into-plus : ∀{σ d1 d2} →
                      binders-disjoint-σ σ d1 →
                      binders-disjoint-σ σ d2 →
                      binders-disjoint-σ σ (d1 ·+ d2)
  lem-bdσ-into-plus BDσId BDσId = BDσId
  lem-bdσ-into-plus (BDσSubst x bd1 x₁) (BDσSubst x₂ bd2 x₃) =
    BDσSubst (BDPlus x x₂) (lem-bdσ-into-plus bd1 bd2) (UBPlus x₁ x₃)
        
  lem-bdσ-plus : ∀{σ d1 d2} →
                 binders-disjoint-σ σ (d1 ·+ d2) →
                 binders-disjoint-σ σ d1 × binders-disjoint-σ σ d2
  lem-bdσ-plus BDσId = BDσId , BDσId
  lem-bdσ-plus (BDσSubst (BDPlus x x₁) bd (UBPlus ub ub₁))
    with lem-bdσ-plus bd
  ... | dis1 , dis2 = BDσSubst x dis1 ub , BDσSubst x₁ dis2 ub₁
      
  lem-bd-plus : ∀{d d1 d2} →
                binders-disjoint d (d1 ·+ d2) →
                binders-disjoint d d1 × binders-disjoint d d2
  lem-bd-plus BDNum = BDNum , BDNum
  lem-bd-plus (BDPlus bd bd')
    with lem-bd-plus bd | lem-bd-plus bd'
  ... | bd₁ , bd₂ | bd₁' , bd₂' = BDPlus bd₁ bd₁' , BDPlus bd₂ bd₂'
  lem-bd-plus BDVar = BDVar , BDVar
  lem-bd-plus (BDLam bd (UBPlus x x₁))
    with lem-bd-plus bd
  ... | bd₁ , bd₂  = BDLam bd₁ x , BDLam bd₂ x₁
  lem-bd-plus (BDAp bd bd')
    with lem-bd-plus bd | lem-bd-plus bd'
  ... | bd₁ , bd₂ | bd₁' , bd₂' = BDAp bd₁ bd₁' , BDAp bd₂ bd₂'
  lem-bd-plus (BDInl bd)
    with lem-bd-plus bd
  ... | bd₁ , bd₂ = BDInl bd₁ , BDInl bd₂
  lem-bd-plus (BDInr bd)
    with lem-bd-plus bd
  ... | bd' , bdσ' = BDInr bd' , BDInr bdσ'
  lem-bd-plus (BDCase bd (UBPlus x x₂) bd₁ (UBPlus x₁ x₃) bd₂)
    with lem-bd-plus bd | lem-bd-plus bd₁ | lem-bd-plus bd₂
  ... | bd' , bd'' | bd₁' , bd₁'' | bd₂' , bd₂'' = BDCase bd' x bd₁' x₁ bd₂' , BDCase bd'' x₂ bd₁'' x₃ bd₂''
  lem-bd-plus (BDPair bd bd₁)
    with lem-bd-plus bd | lem-bd-plus bd₁ 
  ... | bd' , bd'' | bd₁' , bd₁''  = BDPair bd' bd₁' , BDPair bd'' bd₁''
  lem-bd-plus (BDFst bd)
    with lem-bd-plus bd
  ... | bd' , bdσ' = BDFst bd' , BDFst bdσ'
  lem-bd-plus (BDSnd bd)
    with lem-bd-plus bd
  ... | bd' , bdσ' = BDSnd bd' , BDSnd bdσ'
  lem-bd-plus (BDHole x)
    with lem-bdσ-plus x
  ... | bdσ₁ , bdσ₂ = BDHole bdσ₁ , BDHole bdσ₂
  lem-bd-plus (BDNEHole x bd)
    with lem-bdσ-plus x | lem-bd-plus bd
  ... | bdσ₁ , bdσ₂ | bd₁ , bd₂ = BDNEHole bdσ₁ bd₁ , BDNEHole bdσ₂ bd₂
  lem-bd-plus (BDCast bd)
    with lem-bd-plus bd
  ... | bd₁ , bd₂ = BDCast bd₁ , BDCast bd₂
  lem-bd-plus (BDFailedCast bd)
    with lem-bd-plus bd
  ... | bd₁ , bd₂ = BDFailedCast bd₁ , BDFailedCast bd₂

  -- var
  lem-bdσ-var : ∀{σ x} → binders-disjoint-σ σ (X x)
  lem-bdσ-var {σ = Id Γ} = BDσId
  lem-bdσ-var {σ = Subst d y σ} = BDσSubst BDVar lem-bdσ-var UBVar
  
  lem-bd-var : ∀{d x} → binders-disjoint d (X x)
  lem-bd-var {d = N x} = BDNum
  lem-bd-var {d = d ·+ d₁} = BDPlus lem-bd-var lem-bd-var
  lem-bd-var {d = X x} = BDVar
  lem-bd-var {d = ·λ x ·[ x₁ ] d} = BDLam lem-bd-var UBVar
  lem-bd-var {d = d ∘ d₁} = BDAp lem-bd-var lem-bd-var
  lem-bd-var {d = inl x d} = BDInl lem-bd-var
  lem-bd-var {d = inr x d} = BDInr lem-bd-var
  lem-bd-var {d = case d x d₁ x₁ d₂} = BDCase lem-bd-var UBVar lem-bd-var UBVar lem-bd-var
  lem-bd-var {d = ⟨ d , d₁ ⟩} = BDPair lem-bd-var lem-bd-var
  lem-bd-var {d = fst d} = BDFst lem-bd-var
  lem-bd-var {d = snd d} = BDSnd lem-bd-var
  lem-bd-var {d = ⦇-⦈⟨ u , σ ⟩} = BDHole lem-bdσ-var
  lem-bd-var {d = ⦇⌜ d ⌟⦈⟨ u , σ ⟩} = BDNEHole lem-bdσ-var lem-bd-var
  lem-bd-var {d = d ⟨ x ⇒ x₁ ⟩} = BDCast lem-bd-var
  lem-bd-var {d = d ⟨ x ⇒⦇-⦈⇏ x₁ ⟩} = BDFailedCast lem-bd-var
  
  -- lambda
  lem-bdσ-into-lam : ∀{x τ d σ} →
                     binders-disjoint-σ σ d →
                     unbound-in-σ x σ →
                     binders-disjoint-σ σ (·λ x ·[ τ ] d)
  lem-bdσ-into-lam BDσId UBσId = BDσId
  lem-bdσ-into-lam (BDσSubst x bd x₁) (UBσSubst x₂ ub x₃) =
    BDσSubst (BDLam x x₂) (lem-bdσ-into-lam bd ub) (UBLam2 (flip x₃) x₁)
  
  lem-bdσ-lam : ∀{σ x τ d} →
                binders-disjoint-σ σ (·λ x ·[ τ ] d) →
                binders-disjoint-σ σ d × unbound-in-σ x σ
  lem-bdσ-lam BDσId = BDσId , UBσId
  lem-bdσ-lam (BDσSubst (BDLam x₁ x) bd (UBLam2 x₂ ub))
    with lem-bdσ-lam bd
  ... | bdσ , ub' = (BDσSubst x₁ bdσ ub) , (UBσSubst x ub' (flip x₂))

  lem-bd-lam : ∀{d1 x τ1 d} →
               binders-disjoint d1 (·λ x ·[ τ1 ] d) →
               binders-disjoint d1 d × unbound-in x d1
  lem-bd-lam BDNum = BDNum , UBNum
  lem-bd-lam (BDPlus bd bd₁)
    with lem-bd-lam bd | lem-bd-lam bd₁
  ... | bd' , ub | bd₁' , ub₁ = BDPlus bd' bd₁' , UBPlus ub ub₁
  lem-bd-lam BDVar = BDVar , UBVar
  lem-bd-lam (BDLam bd (UBLam2 x x₁))
    with lem-bd-lam bd
  ... | bd' , ub = BDLam bd' x₁ , UBLam2 (flip x) ub
  lem-bd-lam (BDAp bd bd₁)
    with lem-bd-lam bd | lem-bd-lam bd₁
  ... | bd' , ub | bd₁' , ub₁ = BDAp bd' bd₁' , UBAp ub ub₁
  lem-bd-lam (BDInl bd)
    with lem-bd-lam bd
  ... | bd' , ub = BDInl bd' , UBInl ub
  lem-bd-lam (BDInr bd)
    with lem-bd-lam bd
  ... | bd' , ub = BDInr bd' , UBInr ub
  lem-bd-lam (BDCase bd (UBLam2 x x₁) bd₁ (UBLam2 x₂ x₃) bd₂)
    with lem-bd-lam bd | lem-bd-lam bd₁ | lem-bd-lam bd₂
  ... | bd' , ub | bd₁' , ub1 | bd₂' , ub2 = (BDCase bd' x₁ bd₁' x₃ bd₂') , (UBCase ub (flip x) ub1 (flip x₂) ub2)
  lem-bd-lam (BDPair bd bd₁)
    with lem-bd-lam bd | lem-bd-lam bd₁ 
  ... | bd' , ub | bd₁' , ub1 = BDPair bd' bd₁' , UBPair ub ub1
  lem-bd-lam (BDFst bd)
     with lem-bd-lam bd
  ... | bd' , ub = BDFst bd' , UBFst ub
  lem-bd-lam (BDSnd bd)
     with lem-bd-lam bd
  ... | bd' , ub = BDSnd bd' , UBSnd ub
  lem-bd-lam (BDHole x)
    with lem-bdσ-lam x
  ... | bdσ , ubσ = BDHole bdσ , UBHole ubσ
  lem-bd-lam (BDNEHole x bd)
    with lem-bd-lam bd | lem-bdσ-lam x
  ... | bd' , ub | bdσ , ubσ = BDNEHole bdσ bd' , UBNEHole ubσ ub
  lem-bd-lam (BDCast bd)
    with lem-bd-lam bd
  ... | bd' , ub = BDCast bd' , UBCast ub
  lem-bd-lam (BDFailedCast bd)
    with lem-bd-lam bd
  ... | bd' , ub = BDFailedCast bd' , UBFailedCast ub

  -- application
  lem-bdσ-into-ap : ∀{σ d1 d2} →
                    binders-disjoint-σ σ d1 →
                    binders-disjoint-σ σ d2 →
                    binders-disjoint-σ σ (d1 ∘ d2)
  lem-bdσ-into-ap BDσId BDσId = BDσId
  lem-bdσ-into-ap (BDσSubst x bd1 x₁) (BDσSubst x₂ bd2 x₃) =
    BDσSubst (BDAp x x₂) (lem-bdσ-into-ap bd1 bd2) (UBAp x₁ x₃)
  
  lem-bdσ-ap : ∀{σ d1 d2} →
               binders-disjoint-σ σ (d1 ∘ d2) →
               binders-disjoint-σ σ d1 × binders-disjoint-σ σ d2
  lem-bdσ-ap BDσId = BDσId , BDσId
  lem-bdσ-ap (BDσSubst (BDAp x x₁) bd (UBAp ub ub₁))
    with lem-bdσ-ap bd
  ... | dis1 , dis2 = BDσSubst x dis1 ub , BDσSubst x₁ dis2 ub₁


  lem-bd-ap : ∀{d d1 d2} →
              binders-disjoint d (d1 ∘ d2) →
              binders-disjoint d d1 × binders-disjoint d d2
  lem-bd-ap BDNum = BDNum , BDNum
  lem-bd-ap (BDPlus bd bd')
    with lem-bd-ap bd | lem-bd-ap bd'
  ... | bd₁ , bd₂ | bd₁' , bd₂' = BDPlus bd₁ bd₁' , BDPlus bd₂ bd₂'
  lem-bd-ap BDVar = BDVar , BDVar
  lem-bd-ap (BDLam bd (UBAp x x₁))
    with lem-bd-ap bd
  ... | bd₁ , bd₂  = BDLam bd₁ x , BDLam bd₂ x₁
  lem-bd-ap (BDAp bd bd')
    with lem-bd-ap bd | lem-bd-ap bd'
  ... | bd₁ , bd₂ | bd₁' , bd₂' = BDAp bd₁ bd₁' , BDAp bd₂ bd₂'
  lem-bd-ap (BDInl bd)
    with lem-bd-ap bd
  ... | bd₁ , bd₂ = BDInl bd₁ , BDInl bd₂
  lem-bd-ap (BDInr bd)
    with lem-bd-ap bd
  ... | bd' , bdσ' = BDInr bd' , BDInr bdσ'
  lem-bd-ap (BDCase bd (UBAp x x₂) bd₁ (UBAp x₁ x₃) bd₂)
    with lem-bd-ap bd | lem-bd-ap bd₁ | lem-bd-ap bd₂
  ... | bd' , bd'' | bd₁' , bd₁'' | bd₂' , bd₂'' = BDCase bd' x bd₁' x₁ bd₂' , BDCase bd'' x₂ bd₁'' x₃ bd₂''
  lem-bd-ap (BDPair bd bd₁)
    with lem-bd-ap bd | lem-bd-ap bd₁
  ... | bd' , bd'' | bd₁' , bd₁'' = BDPair bd' bd₁' , BDPair bd'' bd₁''
  lem-bd-ap (BDFst bd)
    with lem-bd-ap bd
  ... | bd' , bdσ' = BDFst bd' , BDFst bdσ'
  lem-bd-ap (BDSnd bd)
    with lem-bd-ap bd
  ... | bd' , bdσ' = BDSnd bd' , BDSnd bdσ'
  lem-bd-ap (BDHole x)
    with lem-bdσ-ap x
  ... | bdσ₁ , bdσ₂ = BDHole bdσ₁ , BDHole bdσ₂
  lem-bd-ap (BDNEHole x bd)
    with lem-bdσ-ap x | lem-bd-ap bd
  ... | bdσ₁ , bdσ₂ | bd₁ , bd₂ = BDNEHole bdσ₁ bd₁ , BDNEHole bdσ₂ bd₂
  lem-bd-ap (BDCast bd)
    with lem-bd-ap bd
  ... | bd₁ , bd₂ = BDCast bd₁ , BDCast bd₂
  lem-bd-ap (BDFailedCast bd)
    with lem-bd-ap bd
  ... | bd₁ , bd₂ = BDFailedCast bd₁ , BDFailedCast bd₂
  
  -- inl
  lem-bdσ-into-inl : ∀{σ d τ} →
                     binders-disjoint-σ σ d →
                     binders-disjoint-σ σ (inl τ d)
  lem-bdσ-into-inl BDσId = BDσId
  lem-bdσ-into-inl (BDσSubst x bd x₁) = BDσSubst (BDInl x) (lem-bdσ-into-inl bd) (UBInl x₁)
  
  lem-bdσ-inl : ∀{σ τ d} →
                binders-disjoint-σ σ (inl τ d) →
                binders-disjoint-σ σ d
  lem-bdσ-inl BDσId = BDσId
  lem-bdσ-inl (BDσSubst (BDInl x) bd (UBInl ub)) = BDσSubst x (lem-bdσ-inl bd) ub
                                                                               
  lem-bd-inl : ∀{d τ d1} →
               binders-disjoint d (inl τ d1) →
               binders-disjoint d d1
  lem-bd-inl BDNum = BDNum
  lem-bd-inl (BDPlus bd bd₁) = BDPlus (lem-bd-inl bd) (lem-bd-inl bd₁)
  lem-bd-inl BDVar = BDVar
  lem-bd-inl (BDLam bd (UBInl x)) = BDLam (lem-bd-inl bd) x
  lem-bd-inl (BDAp bd bd₁) = BDAp (lem-bd-inl bd) (lem-bd-inl bd₁)
  lem-bd-inl (BDInl bd) = BDInl (lem-bd-inl bd)
  lem-bd-inl (BDInr bd) = BDInr (lem-bd-inl bd)
  lem-bd-inl (BDCase bd (UBInl x) bd₁ (UBInl x₁) bd₂) = BDCase (lem-bd-inl bd) x (lem-bd-inl bd₁) x₁ (lem-bd-inl bd₂)
  lem-bd-inl (BDPair bd bd₁) = BDPair (lem-bd-inl bd) (lem-bd-inl bd₁)
  lem-bd-inl (BDFst bd) = BDFst (lem-bd-inl bd)
  lem-bd-inl (BDSnd bd) = BDSnd (lem-bd-inl bd)
  lem-bd-inl (BDHole x) = BDHole (lem-bdσ-inl x)
  lem-bd-inl (BDNEHole x bd) = BDNEHole (lem-bdσ-inl x) (lem-bd-inl bd)
  lem-bd-inl (BDCast bd) = BDCast (lem-bd-inl bd)
  lem-bd-inl (BDFailedCast bd) = BDFailedCast (lem-bd-inl bd)
  
  -- inr
  lem-bdσ-into-inr : ∀{σ d τ} →
                     binders-disjoint-σ σ d →
                     binders-disjoint-σ σ (inr τ d)
  lem-bdσ-into-inr BDσId = BDσId
  lem-bdσ-into-inr (BDσSubst x bd x₁) = BDσSubst (BDInr x) (lem-bdσ-into-inr bd) (UBInr x₁)
  
  lem-bdσ-inr : ∀{σ τ d} →
                binders-disjoint-σ σ (inr τ d) →
                binders-disjoint-σ σ d
  lem-bdσ-inr BDσId = BDσId
  lem-bdσ-inr (BDσSubst (BDInr x) bd (UBInr ub)) = BDσSubst x (lem-bdσ-inr bd) ub
                                                                               
  lem-bd-inr : ∀{d τ d1} →
               binders-disjoint d (inr τ d1) →
               binders-disjoint d d1
  lem-bd-inr BDNum = BDNum
  lem-bd-inr (BDPlus bd bd₁) = BDPlus (lem-bd-inr bd) (lem-bd-inr bd₁)
  lem-bd-inr BDVar = BDVar
  lem-bd-inr (BDLam bd (UBInr x)) = BDLam (lem-bd-inr bd) x
  lem-bd-inr (BDAp bd bd₁) = BDAp (lem-bd-inr bd) (lem-bd-inr bd₁)
  lem-bd-inr (BDInl bd) = BDInl (lem-bd-inr bd)
  lem-bd-inr (BDInr bd) = BDInr (lem-bd-inr bd)
  lem-bd-inr (BDCase bd (UBInr x) bd₁ (UBInr x₁) bd₂) = BDCase (lem-bd-inr bd) x (lem-bd-inr bd₁) x₁ (lem-bd-inr bd₂)
  lem-bd-inr (BDPair bd bd₁) = BDPair (lem-bd-inr bd) (lem-bd-inr bd₁)
  lem-bd-inr (BDFst bd) = BDFst (lem-bd-inr bd)
  lem-bd-inr (BDSnd bd) = BDSnd (lem-bd-inr bd)
  lem-bd-inr (BDHole x) = BDHole (lem-bdσ-inr x)
  lem-bd-inr (BDNEHole x bd) = BDNEHole (lem-bdσ-inr x) (lem-bd-inr bd)
  lem-bd-inr (BDCast bd) = BDCast (lem-bd-inr bd)
  lem-bd-inr (BDFailedCast bd) = BDFailedCast (lem-bd-inr bd)
  
  -- case
  lem-bdσ-into-case : ∀{σ d x d1 y d2} →
                      binders-disjoint-σ σ d →
                      unbound-in-σ x σ →
                      binders-disjoint-σ σ d1 →
                      unbound-in-σ y σ →
                      binders-disjoint-σ σ d2 →
                      binders-disjoint-σ σ (case d x d1 y d2)
  lem-bdσ-into-case BDσId ubx bdσ1 uby bdσ2 = BDσId
  lem-bdσ-into-case (BDσSubst x bdσ x₁) (UBσSubst x₂ ubx x₃) (BDσSubst x₆ bdσ1 x₇) (UBσSubst x₄ uby x₅) (BDσSubst x₈ bdσ2 x₉) =
    BDσSubst (BDCase x x₂ x₆ x₄ x₈) (lem-bdσ-into-case bdσ ubx bdσ1 uby bdσ2) (UBCase x₁ (flip x₃) x₇ (flip x₅) x₉)

  lem-bdσ-case : ∀{σ d x d1 y d2} →
                 binders-disjoint-σ σ (case d x d1 y d2) →
                 (binders-disjoint-σ σ d) ×
                 (unbound-in-σ x σ) ×
                 (binders-disjoint-σ σ d1) ×
                 (unbound-in-σ y σ) ×
                 (binders-disjoint-σ σ d2)
  lem-bdσ-case BDσId = BDσId , UBσId , BDσId , UBσId , BDσId
  lem-bdσ-case (BDσSubst (BDCase x x₁ x₂ x₃ x₄) bd (UBCase x₅ x₆ x₇ x₈ x₉))
    with lem-bdσ-case bd
  ... | bdd , ubx , bdd1 , uby , bdd2 = BDσSubst x bdd x₅ , UBσSubst x₁ ubx (flip x₆) , BDσSubst x₂ bdd1 x₇ , UBσSubst x₃ uby (flip x₈) , BDσSubst x₄ bdd2 x₉

  lem-bd-case : ∀{d x d1 y d2 d3} →
                binders-disjoint d3 (case d x d1 y d2) →
                (binders-disjoint d3 d) ×
                (unbound-in x d3) ×
                (binders-disjoint d3 d1) ×
                (unbound-in y d3) ×
                (binders-disjoint d3 d2)
  lem-bd-case BDNum = BDNum , UBNum , BDNum , UBNum , BDNum
  lem-bd-case (BDPlus bd bd₁)
    with lem-bd-case bd | lem-bd-case bd₁ 
  ... | bdd , ubx , bdd1 , uby , bdd2 | bdd' , ubx' , bdd1' , uby' , bdd2' = BDPlus bdd bdd' , UBPlus ubx ubx' , BDPlus bdd1 bdd1' , UBPlus uby uby' , BDPlus bdd2 bdd2'
  lem-bd-case BDVar = BDVar , UBVar , BDVar , UBVar , BDVar
  lem-bd-case (BDLam bd (UBCase x x₁ x₂ x₃ x₄))
    with lem-bd-case bd
  ... | bdd , ubx , bdd1 , uby , bdd2  = BDLam bdd x , UBLam2 (flip x₁) ubx , BDLam bdd1 x₂ , UBLam2 (flip x₃) uby , BDLam bdd2 x₄
  lem-bd-case (BDAp bd bd₁)
    with lem-bd-case bd | lem-bd-case bd₁ 
  ... | bdd , ubx , bdd1 , uby , bdd2 | bdd' , ubx' , bdd1' , uby' , bdd2' = BDAp bdd bdd' , UBAp ubx ubx' , BDAp bdd1 bdd1' , UBAp uby uby' , BDAp bdd2 bdd2'
  lem-bd-case (BDInl bd)
    with lem-bd-case bd
  ... | bdd , ubx , bdd1 , uby , bdd2 = BDInl bdd , UBInl ubx , BDInl bdd1 , UBInl uby , BDInl bdd2
  lem-bd-case (BDInr bd)
    with lem-bd-case bd
  ... | bdd , ubx , bdd1 , uby , bdd2 = BDInr bdd , UBInr ubx , BDInr bdd1 , UBInr uby , BDInr bdd2
  lem-bd-case (BDCase bd (UBCase x x₁ x₂ x₃ x₄) bd₁ (UBCase x₅ x₆ x₇ x₈ x₉) bd₂)
    with lem-bd-case bd | lem-bd-case bd₁ | lem-bd-case bd₂
  ... | bdd , ubx , bdd1 , uby , bdd2 | bdd' , ubx' , bdd1' , uby' , bdd2' | bdd'' , ubx'' , bdd1'' , uby'' , bdd2'' = BDCase bdd x bdd' x₅ bdd'' , UBCase ubx (flip x₁) ubx' (flip x₆) ubx'' , BDCase bdd1 x₂ bdd1' x₇ bdd1'' , UBCase uby (flip x₃) uby' (flip x₈) uby'' , BDCase bdd2 x₄ bdd2' x₉ bdd2''
  lem-bd-case (BDPair bd bd₁)
    with lem-bd-case bd | lem-bd-case bd₁ 
  ... | bdd , ubx , bdd1 , uby , bdd2 | bdd' , ubx' , bdd1' , uby' , bdd2' = BDPair bdd bdd' , UBPair ubx ubx' , BDPair bdd1 bdd1' , UBPair uby uby' , BDPair bdd2 bdd2'
  lem-bd-case (BDFst bd)
    with lem-bd-case bd
  ... | bdd , ubx , bdd1 , uby , bdd2 = BDFst bdd , UBFst ubx , BDFst bdd1 , UBFst uby , BDFst bdd2
  lem-bd-case (BDSnd bd)
    with lem-bd-case bd
  ... | bdd , ubx , bdd1 , uby , bdd2 = BDSnd bdd , UBSnd ubx , BDSnd bdd1 , UBSnd uby , BDSnd bdd2
  lem-bd-case (BDHole x)
    with lem-bdσ-case x
  ... | bdd , ubx , bdd1 , uby , bdd2 = BDHole bdd , UBHole ubx , BDHole bdd1 , UBHole uby , BDHole bdd2
  lem-bd-case (BDNEHole x bd)
    with lem-bd-case bd | lem-bdσ-case x
  ... | bdd , ubx , bdd1 , uby , bdd2 | bddσ , ubxσ , bdd1σ , ubyσ , bdd2σ = BDNEHole bddσ bdd , UBNEHole ubxσ ubx , BDNEHole bdd1σ bdd1 , UBNEHole ubyσ uby , BDNEHole bdd2σ bdd2
  lem-bd-case (BDCast bd)
    with lem-bd-case bd
  ... | bdd , ubx , bdd1 , uby , bdd2 = BDCast bdd , UBCast ubx , BDCast bdd1 , UBCast uby , BDCast bdd2
  lem-bd-case (BDFailedCast bd)
    with lem-bd-case bd
  ... | bdd , ubx , bdd1 , uby , bdd2 = BDFailedCast bdd , UBFailedCast ubx , BDFailedCast bdd1 , UBFailedCast uby , BDFailedCast bdd2

  -- pairs
  lem-bdσ-into-pair : ∀{σ d1 d2} →
                      binders-disjoint-σ σ d1 →
                      binders-disjoint-σ σ d2 →
                      binders-disjoint-σ σ ⟨ d1 , d2 ⟩
  lem-bdσ-into-pair BDσId BDσId = BDσId
  lem-bdσ-into-pair (BDσSubst x bdσ1 x₁) (BDσSubst x₂ bdσ2 x₃) = BDσSubst (BDPair x x₂) (lem-bdσ-into-pair bdσ1 bdσ2) (UBPair x₁ x₃)
  
  lem-bdσ-pair : ∀{σ d1 d2} →
                 binders-disjoint-σ σ ⟨ d1 , d2 ⟩ →
                 (binders-disjoint-σ σ d1) × (binders-disjoint-σ σ d2)
  lem-bdσ-pair BDσId = BDσId , BDσId
  lem-bdσ-pair (BDσSubst (BDPair x x₁) bdσ (UBPair x₂ x₃))
    with lem-bdσ-pair bdσ
  ... | bdσ1 , bdσ2 = BDσSubst x bdσ1 x₂ , BDσSubst x₁ bdσ2 x₃
  
  lem-bd-pair : ∀{d d1 d2} →
                binders-disjoint d ⟨ d1 , d2 ⟩ →
                (binders-disjoint d d1) × (binders-disjoint d d2)
  lem-bd-pair BDNum = BDNum , BDNum
  lem-bd-pair (BDPlus bd bd₁)
    with lem-bd-pair bd | lem-bd-pair bd₁
  ... | bd' , bd'' | bd₁' , bd₁'' = BDPlus bd' bd₁' , BDPlus bd'' bd₁''
  lem-bd-pair BDVar = BDVar , BDVar
  lem-bd-pair (BDLam bd (UBPair x x₁))
    with lem-bd-pair bd
  ... | bd' , bd'' = BDLam bd' x , BDLam bd'' x₁
  lem-bd-pair (BDAp bd bd₁)
    with lem-bd-pair bd | lem-bd-pair bd₁
  ... | bd' , bd'' | bd₁' , bd₁'' = BDAp bd' bd₁' , BDAp bd'' bd₁''
  lem-bd-pair (BDInl bd)
    with lem-bd-pair bd
  ... | bd' , bd'' = BDInl bd' , BDInl bd''
  lem-bd-pair (BDInr bd)
    with lem-bd-pair bd
  ... | bd' , bd'' = BDInr bd' , BDInr bd''
  lem-bd-pair (BDCase bd (UBPair x x₁) bd₁ (UBPair x₂ x₃) bd₂)
     with lem-bd-pair bd | lem-bd-pair bd₁ | lem-bd-pair bd₂
  ... | bd' , bd'' | bd₁' , bd₁'' | bd₂' , bd₂'' = BDCase bd' x bd₁' x₂ bd₂' , BDCase bd'' x₁ bd₁'' x₃ bd₂''
  lem-bd-pair (BDPair bd bd₁)
    with lem-bd-pair bd | lem-bd-pair bd₁
  ... | bd' , bd'' | bd₁' , bd₁'' = BDPair bd' bd₁' , BDPair bd'' bd₁''
  lem-bd-pair (BDFst bd)
    with lem-bd-pair bd
  ... | bd' , bd'' = BDFst bd' , BDFst bd''
  lem-bd-pair (BDSnd bd)
    with lem-bd-pair bd
  ... | bd' , bd'' = BDSnd bd' , BDSnd bd''
  lem-bd-pair (BDHole x)
    with lem-bdσ-pair x
  ... | bdσ' , bdσ'' = BDHole bdσ' , BDHole bdσ''
  lem-bd-pair (BDNEHole x bd)
    with lem-bdσ-pair x | lem-bd-pair bd
  ... | bdσ' , bdσ'' | bd' , bd'' = BDNEHole bdσ' bd' , BDNEHole bdσ'' bd''
  lem-bd-pair (BDCast bd)
    with lem-bd-pair bd
  ... | bd' , bd'' = BDCast bd' , BDCast bd''
  lem-bd-pair (BDFailedCast bd)
    with lem-bd-pair bd
  ... | bd' , bd'' = BDFailedCast bd' , BDFailedCast bd''

  -- fst
  lem-bdσ-into-fst : ∀{σ d} →
                     binders-disjoint-σ σ d →
                     binders-disjoint-σ σ (fst d)
  lem-bdσ-into-fst BDσId = BDσId
  lem-bdσ-into-fst (BDσSubst x bdσ x₁) = BDσSubst (BDFst x) (lem-bdσ-into-fst bdσ) (UBFst x₁)
  
  lem-bdσ-fst : ∀{σ d} →
                binders-disjoint-σ σ (fst d) →
                binders-disjoint-σ σ d
  lem-bdσ-fst BDσId = BDσId
  lem-bdσ-fst (BDσSubst (BDFst x) bdσ (UBFst x₁)) = BDσSubst x (lem-bdσ-fst bdσ) x₁
  
  lem-bd-fst : ∀{d d1} →
               binders-disjoint d (fst d1) →
               binders-disjoint d d1
  lem-bd-fst BDNum = BDNum
  lem-bd-fst (BDPlus bd bd₁) = BDPlus (lem-bd-fst bd) (lem-bd-fst bd₁)
  lem-bd-fst BDVar = BDVar
  lem-bd-fst (BDLam bd (UBFst x)) = BDLam (lem-bd-fst bd) x
  lem-bd-fst (BDAp bd bd₁) = BDAp (lem-bd-fst bd) (lem-bd-fst bd₁)
  lem-bd-fst (BDInl bd) = BDInl (lem-bd-fst bd)
  lem-bd-fst (BDInr bd) = BDInr (lem-bd-fst bd)
  lem-bd-fst (BDCase bd (UBFst x) bd₁ (UBFst x₁) bd₂) = BDCase (lem-bd-fst bd) x (lem-bd-fst bd₁) x₁ (lem-bd-fst bd₂)
  lem-bd-fst (BDPair bd bd₁) = BDPair (lem-bd-fst bd) (lem-bd-fst bd₁)
  lem-bd-fst (BDFst bd) = BDFst (lem-bd-fst bd)
  lem-bd-fst (BDSnd bd) = BDSnd (lem-bd-fst bd)
  lem-bd-fst (BDHole x) = BDHole (lem-bdσ-fst x)
  lem-bd-fst (BDNEHole x bd) = BDNEHole (lem-bdσ-fst x) (lem-bd-fst bd)
  lem-bd-fst (BDCast bd) = BDCast (lem-bd-fst bd)
  lem-bd-fst (BDFailedCast bd) = BDFailedCast (lem-bd-fst bd)

  -- snd
  lem-bdσ-into-snd : ∀{σ d} →
                     binders-disjoint-σ σ d →
                     binders-disjoint-σ σ (snd d)
  lem-bdσ-into-snd BDσId = BDσId
  lem-bdσ-into-snd (BDσSubst x bdσ x₁) = BDσSubst (BDSnd x) (lem-bdσ-into-snd bdσ) (UBSnd x₁)
  
  lem-bdσ-snd : ∀{σ d} →
                binders-disjoint-σ σ (snd d) →
                binders-disjoint-σ σ d           
  lem-bdσ-snd BDσId = BDσId
  lem-bdσ-snd (BDσSubst (BDSnd x) bdσ (UBSnd x₁)) = BDσSubst x (lem-bdσ-snd bdσ) x₁
  
  lem-bd-snd : ∀{d d1} →
               binders-disjoint d (snd d1) →
               binders-disjoint d d1
  lem-bd-snd BDNum = BDNum
  lem-bd-snd (BDPlus bd bd₁) = BDPlus (lem-bd-snd bd) (lem-bd-snd bd₁)
  lem-bd-snd BDVar = BDVar
  lem-bd-snd (BDLam bd (UBSnd x)) = BDLam (lem-bd-snd bd) x
  lem-bd-snd (BDAp bd bd₁) = BDAp (lem-bd-snd bd) (lem-bd-snd bd₁)
  lem-bd-snd (BDInl bd) = BDInl (lem-bd-snd bd)
  lem-bd-snd (BDInr bd) = BDInr (lem-bd-snd bd)
  lem-bd-snd (BDCase bd (UBSnd x) bd₁ (UBSnd x₁) bd₂) = BDCase (lem-bd-snd bd) x (lem-bd-snd bd₁) x₁ (lem-bd-snd bd₂)
  lem-bd-snd (BDPair bd bd₁) = BDPair (lem-bd-snd bd) (lem-bd-snd bd₁)
  lem-bd-snd (BDFst bd) = BDFst (lem-bd-snd bd)
  lem-bd-snd (BDSnd bd) = BDSnd (lem-bd-snd bd)
  lem-bd-snd (BDHole x) = BDHole (lem-bdσ-snd x)
  lem-bd-snd (BDNEHole x bd) = BDNEHole (lem-bdσ-snd x) (lem-bd-snd bd)
  lem-bd-snd (BDCast bd) = BDCast (lem-bd-snd bd)
  lem-bd-snd (BDFailedCast bd) = BDFailedCast (lem-bd-snd bd)
  
  -- cast
  lem-bdσ-into-cast : ∀{σ d τ1 τ2} →
                      binders-disjoint-σ σ d →
                      binders-disjoint-σ σ (d ⟨ τ1 ⇒ τ2 ⟩)
  lem-bdσ-into-cast BDσId = BDσId
  lem-bdσ-into-cast (BDσSubst x bd x₁) = BDσSubst (BDCast x) (lem-bdσ-into-cast bd) (UBCast x₁)
  
  lem-bdσ-cast : ∀{σ d τ1 τ2} →
                 binders-disjoint-σ σ (d ⟨ τ1 ⇒ τ2 ⟩) →
                 binders-disjoint-σ σ d
  lem-bdσ-cast BDσId = BDσId
  lem-bdσ-cast (BDσSubst (BDCast x) bd (UBCast ub)) = BDσSubst x (lem-bdσ-cast bd) ub

  lem-bd-cast : ∀{d1 d τ1 τ2} →
                binders-disjoint d1 (d ⟨ τ1 ⇒ τ2 ⟩) →
                binders-disjoint d1 d
  lem-bd-cast BDNum = BDNum
  lem-bd-cast (BDPlus bd bd₁) = BDPlus (lem-bd-cast bd) (lem-bd-cast bd₁)
  lem-bd-cast BDVar = BDVar
  lem-bd-cast (BDLam bd (UBCast x₁)) = BDLam (lem-bd-cast bd) x₁
  lem-bd-cast (BDHole x) = BDHole (lem-bdσ-cast x)
  lem-bd-cast (BDNEHole x bd) = BDNEHole (lem-bdσ-cast x) (lem-bd-cast bd)
  lem-bd-cast (BDAp bd bd₁) = BDAp (lem-bd-cast bd) (lem-bd-cast bd₁)
  lem-bd-cast (BDInl bd) = BDInl (lem-bd-cast bd)
  lem-bd-cast (BDInr bd) = BDInr (lem-bd-cast bd)
  lem-bd-cast (BDCase bd (UBCast x) bd₁ (UBCast x₁) bd₂) = BDCase (lem-bd-cast bd) x (lem-bd-cast bd₁) x₁ (lem-bd-cast bd₂)
  lem-bd-cast (BDPair bd bd₁) = BDPair (lem-bd-cast bd) (lem-bd-cast bd₁)
  lem-bd-cast (BDFst bd) = BDFst (lem-bd-cast bd)
  lem-bd-cast (BDSnd bd) = BDSnd (lem-bd-cast bd)
  lem-bd-cast (BDCast bd) = BDCast (lem-bd-cast bd)
  lem-bd-cast (BDFailedCast bd) = BDFailedCast (lem-bd-cast bd)

  -- failed cast
  lem-bdσ-into-failedcast : ∀{σ d τ1 τ2} →
                            binders-disjoint-σ σ d →
                            binders-disjoint-σ σ (d ⟨ τ1 ⇒⦇-⦈⇏ τ2 ⟩)
  lem-bdσ-into-failedcast BDσId = BDσId
  lem-bdσ-into-failedcast (BDσSubst x bd x₁) =
    BDσSubst (BDFailedCast x) (lem-bdσ-into-failedcast bd) (UBFailedCast x₁)
                           
                       
  lem-bdσ-failedcast : ∀{σ d τ1 τ2} →
                       binders-disjoint-σ σ (d ⟨ τ1 ⇒⦇-⦈⇏ τ2 ⟩) →
                       binders-disjoint-σ σ d
  lem-bdσ-failedcast BDσId = BDσId
  lem-bdσ-failedcast (BDσSubst (BDFailedCast x) bd (UBFailedCast ub)) = BDσSubst x (lem-bdσ-failedcast bd) ub

  lem-bd-failedcast : ∀{d1 d τ1 τ2} → binders-disjoint d1 (d ⟨ τ1 ⇒⦇-⦈⇏ τ2 ⟩) → binders-disjoint d1 d
  lem-bd-failedcast BDNum = BDNum
  lem-bd-failedcast (BDPlus bd bd₁) = BDPlus (lem-bd-failedcast bd) (lem-bd-failedcast bd₁)
  lem-bd-failedcast BDVar = BDVar
  lem-bd-failedcast (BDLam bd (UBFailedCast x₁)) = BDLam (lem-bd-failedcast bd) x₁
  lem-bd-failedcast (BDHole x) = BDHole (lem-bdσ-failedcast x)
  lem-bd-failedcast (BDNEHole x bd) = BDNEHole (lem-bdσ-failedcast x) (lem-bd-failedcast bd)
  lem-bd-failedcast (BDAp bd bd₁) = BDAp (lem-bd-failedcast bd) (lem-bd-failedcast bd₁)
  lem-bd-failedcast (BDInl bd) = BDInl (lem-bd-failedcast bd)
  lem-bd-failedcast (BDInr bd) = BDInr (lem-bd-failedcast bd)
  lem-bd-failedcast (BDCase bd (UBFailedCast x) bd₁ (UBFailedCast x₁) bd₂) =
    BDCase (lem-bd-failedcast bd) x (lem-bd-failedcast bd₁) x₁ (lem-bd-failedcast bd₂)
  lem-bd-failedcast (BDPair bd bd₁) = BDPair (lem-bd-failedcast bd) (lem-bd-failedcast bd₁)
  lem-bd-failedcast (BDFst bd) = BDFst (lem-bd-failedcast bd)
  lem-bd-failedcast (BDSnd bd) = BDSnd (lem-bd-failedcast bd)
  lem-bd-failedcast (BDCast bd) = BDCast (lem-bd-failedcast bd)
  lem-bd-failedcast (BDFailedCast bd) = BDFailedCast (lem-bd-failedcast bd)
  
  -- holes
  mutual
    -- For terms already holding an env, the equivalent lemms needs a judgement
    -- that two envs are disjoint
    data binders-disjoint-σs : env → env → Set where
      BDσsId    : ∀{Γ σ} → binders-disjoint-σs σ (Id Γ)
      BDσsSubst : ∀{d1 σ' y σ} →
                 binders-disjoint-σ σ' d1 →
                 binders-disjoint-σs σ σ' →
                 unbound-in-σ y σ' →
                 binders-disjoint-σs σ' (Subst d1 y σ) 

    lem-bdσs-sym : ∀{σ σ'} →
                   binders-disjoint-σs σ σ' →
                   binders-disjoint-σs σ' σ
    lem-bdσs-sym {σ = Id Γ} bd = BDσsId
    lem-bdσs-sym {σ = Subst d y σ} BDσsId = BDσsSubst BDσId BDσsId UBσId
    lem-bdσs-sym {σ = Subst d y σ} (BDσsSubst (BDσSubst x x₂ x₃) (BDσsSubst x₆ bd x₇) (UBσSubst x₁ x₄ x₅)) = BDσsSubst (BDσSubst (binders-disjoint-sym x) x₆ x₁) (BDσsSubst x₂ (lem-bdσs-sym bd) x₄) (UBσSubst x₃ x₇ (flip x₅))

    lem-bdσ-into-hole : ∀{σ σ' u} →
                        binders-disjoint-σs σ σ' →
                        binders-disjoint-σ σ (⦇-⦈⟨ u , σ' ⟩)
    lem-bdσ-into-hole {σ = Id Γ} bd = BDσId
    lem-bdσ-into-hole {σ = Subst d y σ} BDσsId = BDσSubst (BDHole BDσId) (lem-bdσ-into-hole BDσsId) (UBHole UBσId)
    lem-bdσ-into-hole {σ = Subst d y σ} (BDσsSubst (BDσSubst x x₁ x₂) (BDσsSubst x₆ bd x₇) (UBσSubst x₃ x₄ x₅)) = BDσSubst (BDHole (BDσSubst (binders-disjoint-sym x) x₆ x₃)) (lem-bdσ-into-hole (BDσsSubst x₁ (lem-bdσs-sym bd) x₄)) (UBHole (UBσSubst x₂ x₇ (flip x₅)))
                        
    lem-bdσ-hole : ∀{σ u σ'} →
                   binders-disjoint-σ σ (⦇-⦈⟨ u , σ' ⟩) →
                   binders-disjoint-σs σ σ'
    lem-bdσ-hole {σ = Id Γ} bd = lem-bdσs-sym BDσsId
    lem-bdσ-hole {σ = Subst d y σ} (BDσSubst (BDHole x) bd (UBHole x₁)) = lem-bdσs-sym (BDσsSubst x (lem-bdσ-hole bd) x₁)
    
    lem-bd-hole : ∀{d u σ} →
                  binders-disjoint d (⦇-⦈⟨ u , σ ⟩) →
                  binders-disjoint-σ σ d
    lem-bd-hole {σ = Id Γ} bd = BDσId
    lem-bd-hole {σ = Subst d y σ} BDNum = BDσSubst BDNum lem-bdσ-num UBNum
    lem-bd-hole {σ = Subst d y σ} (BDPlus bd bd₁)
      with lem-bd-hole bd | lem-bd-hole bd₁
    ... | BDσSubst x bdσ ub | BDσSubst x₁ bdσ₁ ub₁ = BDσSubst (BDPlus x x₁) (lem-bdσ-into-plus bdσ bdσ₁) (UBPlus ub ub₁)
        
    lem-bd-hole {σ = Subst d y σ} BDVar = BDσSubst BDVar lem-bdσ-var UBVar
    lem-bd-hole {σ = Subst d y σ} (BDLam bd (UBHole (UBσSubst x x₁ x₂)))
      with lem-bd-hole bd
    ... | BDσSubst x₃ bdσ x₄ = BDσSubst (BDLam x₃ x) (lem-bdσ-into-lam bdσ x₁) (UBLam2 (flip x₂) x₄)
    lem-bd-hole {σ = Subst d y σ} (BDAp bd bd₁)
      with lem-bd-hole bd | lem-bd-hole bd₁
    ... | BDσSubst x bdσ ub | BDσSubst x₁ bdσ₁ ub₁ = BDσSubst (BDAp x x₁) (lem-bdσ-into-ap bdσ bdσ₁) (UBAp ub ub₁)
    lem-bd-hole {σ = Subst d y σ} (BDInl bd)
      with lem-bd-hole bd
    ... | BDσSubst x bdσ ub = BDσSubst (BDInl x) (lem-bdσ-into-inl bdσ) (UBInl ub)
    lem-bd-hole {σ = Subst d y σ} (BDInr bd)
      with lem-bd-hole bd
    ... | BDσSubst x bdσ ub = BDσSubst (BDInr x) (lem-bdσ-into-inr bdσ) (UBInr ub)
    lem-bd-hole {σ = Subst d y σ} (BDCase bd (UBHole (UBσSubst x x₁ x₂)) bd₁ (UBHole (UBσSubst x₃ x₄ x₅)) bd₂)
      with lem-bd-hole bd | lem-bd-hole bd₁ | lem-bd-hole bd₂
    ... | BDσSubst y bdσ ub | BDσSubst y₁ bdσ₁ ub₁ | BDσSubst y₂ bdσ₂ ub₂ = BDσSubst (BDCase y x y₁ x₃ y₂) (lem-bdσ-into-case bdσ x₁ bdσ₁ x₄ bdσ₂) (UBCase ub (flip x₂) ub₁ (flip x₅) ub₂)
    lem-bd-hole {σ = Subst d y σ} (BDPair bd bd₁)
      with lem-bd-hole bd | lem-bd-hole bd₁
    ... | BDσSubst x bdσ ub | BDσSubst y₁ bdσ₁ ub₁ = BDσSubst (BDPair x y₁) (lem-bdσ-into-pair bdσ bdσ₁) (UBPair ub ub₁)
    lem-bd-hole {σ = Subst d y σ} (BDFst bd)
      with lem-bd-hole bd
    ... | BDσSubst x bdσ ub = BDσSubst (BDFst x) (lem-bdσ-into-fst bdσ) (UBFst ub)
    lem-bd-hole {σ = Subst d y σ} (BDSnd bd)
      with lem-bd-hole bd
    ... | BDσSubst x bdσ ub = BDσSubst (BDSnd x) (lem-bdσ-into-snd bdσ) (UBSnd ub)
    lem-bd-hole {u = u} {σ = Subst d y σ} (BDHole {u = u₁} {σ = Id Γ} BDσId) =
      BDσSubst (BDHole BDσId)
               (lem-bdσ-into-hole BDσsId) (UBHole UBσId)
    lem-bd-hole {u = u} {σ = Subst d y σ} (BDHole {u = u₁} {σ = Subst d₁ y₁ σ₁} (BDσSubst (BDHole (BDσSubst x x₂ x₃)) bd (UBHole (UBσSubst x₁ x₄ x₅))))
      with lem-bdσ-hole bd
    ... | BDσsSubst x₆ q x₇ = BDσSubst (BDHole (BDσSubst (binders-disjoint-sym x) x₆ x₁)) (lem-bdσ-into-hole (BDσsSubst x₂ (lem-bdσs-sym q) x₄)) (UBHole (UBσSubst x₃ x₇ (flip x₅)))
    lem-bd-hole {σ = Subst d y σ} (BDNEHole {σ = Id Γ} BDσId bd)
      with lem-bd-hole bd
    ... | BDσSubst x bdσ x₁ = BDσSubst (BDNEHole BDσId x) (lem-bdσ-into-nehole BDσsId bdσ) (UBNEHole UBσId x₁)
    lem-bd-hole {σ = Subst d y σ} (BDNEHole {σ = Subst d₁ y₁ σ'} (BDσSubst (BDHole (BDσSubst x x₃ x₄)) x₁ (UBHole (UBσSubst x₂ x₅ x₆))) bd)
      with lem-bd-hole bd | lem-bdσ-hole x₁
    ... | BDσSubst x₇ bdσ x₈ | BDσsSubst x₉ bdσs x₁₀ = BDσSubst (BDNEHole (BDσSubst (binders-disjoint-sym x) x₉ x₂) x₇) (lem-bdσ-into-nehole (BDσsSubst x₃ (lem-bdσs-sym bdσs) x₅) bdσ) (UBNEHole (UBσSubst x₄ x₁₀ (flip x₆)) x₈)
    lem-bd-hole {σ = Subst d y σ} (BDCast bd)
      with lem-bd-hole bd
    ... | BDσSubst y bdσ ub = BDσSubst (BDCast y) (lem-bdσ-into-cast bdσ) (UBCast ub)
    lem-bd-hole {σ = Subst d y σ} (BDFailedCast bd)
      with lem-bd-hole bd
    ... | BDσSubst y bdσ ub = BDσSubst (BDFailedCast y) (lem-bdσ-into-failedcast bdσ) (UBFailedCast ub)

    lem-bdσ-into-nehole : ∀{σ d u σ'} →
                          binders-disjoint-σs σ σ' →
                          binders-disjoint-σ σ d →
                          binders-disjoint-σ σ ⦇⌜ d ⌟⦈⟨ u , σ' ⟩
    lem-bdσ-into-nehole BDσsId BDσId = BDσId
    lem-bdσ-into-nehole BDσsId (BDσSubst x bd x₁) = BDσSubst (BDNEHole BDσId x) (lem-bdσ-into-nehole BDσsId bd) (UBNEHole UBσId x₁)
    lem-bdσ-into-nehole (BDσsSubst x bds x₁) BDσId = BDσId
    lem-bdσ-into-nehole (BDσsSubst (BDσSubst x x₈ x₉) (BDσsSubst x₄ bds x₅) (UBσSubst x₁ x₆ x₇)) (BDσSubst x₂ bd x₃) = BDσSubst (BDNEHole (BDσSubst (binders-disjoint-sym x) x₄ x₁) x₂) (lem-bdσ-into-nehole (BDσsSubst x₈ (lem-bdσs-sym bds) x₆) bd) (UBNEHole (UBσSubst x₉ x₅ (flip x₇)) x₃)
    
    lem-bdσ-nehole : ∀{d u σ σ'} →
                     binders-disjoint-σ σ ⦇⌜ d ⌟⦈⟨ u , σ' ⟩ →
                     binders-disjoint-σs σ σ' × binders-disjoint-σ σ d
    lem-bdσ-nehole BDσId = (lem-bdσs-sym BDσsId) , BDσId
    lem-bdσ-nehole (BDσSubst (BDNEHole x x₁) bd (UBNEHole x₂ ub))
      with lem-bdσ-nehole bd
    ... | bds' , bd' = (lem-bdσs-sym (BDσsSubst x bds' x₂)) , (BDσSubst x₁ bd' ub)

    lem-bd-nehole : ∀{d1 d u σ} →
                    binders-disjoint d1 ⦇⌜ d ⌟⦈⟨ u , σ ⟩ →
                    binders-disjoint-σ σ d1 × binders-disjoint d1 d
    lem-bd-nehole BDNum = lem-bdσ-num , BDNum
    lem-bd-nehole (BDPlus bd bd₁)
      with lem-bd-nehole bd | lem-bd-nehole bd₁
    ... | bdσ' , bd' | bd₁' , bdσ₁' = lem-bdσ-into-plus bdσ' bd₁' , BDPlus bd' bdσ₁'
    lem-bd-nehole BDVar = lem-bdσ-var , BDVar
    lem-bd-nehole (BDLam bd (UBNEHole x x₁))
      with lem-bd-nehole bd
    ... | bdσ' , bd' = lem-bdσ-into-lam bdσ' x , BDLam bd' x₁
    lem-bd-nehole (BDAp bd bd₁)
      with lem-bd-nehole bd | lem-bd-nehole bd₁
    ... | bdσ' , bd' | bd₁' , bdσ₁' = lem-bdσ-into-ap bdσ' bd₁' , BDAp bd' bdσ₁'
    lem-bd-nehole (BDInl bd)
      with lem-bd-nehole bd
    ... | bdσ' , bd' = lem-bdσ-into-inl bdσ' , BDInl bd'
    lem-bd-nehole (BDInr bd)
      with lem-bd-nehole bd
    ... | bdσ' , bd' = lem-bdσ-into-inr bdσ' , BDInr bd'
    lem-bd-nehole (BDCase bd (UBNEHole x x₁) bd₁ (UBNEHole x₂ x₃) bd₂)
      with lem-bd-nehole bd | lem-bd-nehole bd₁ | lem-bd-nehole bd₂
    ... | bdσ' , bd' | bdσ₁' , bd₁' | bdσ₂' , bd₂' = lem-bdσ-into-case bdσ' x bdσ₁' x₂ bdσ₂' , BDCase bd' x₁ bd₁' x₃ bd₂'
    lem-bd-nehole (BDPair bd bd₁)
       with lem-bd-nehole bd | lem-bd-nehole bd₁
    ... | bdσ' , bd' | bdσ₁' , bd₁' = lem-bdσ-into-pair bdσ' bdσ₁' , BDPair bd' bd₁'
    lem-bd-nehole (BDFst bd)
      with lem-bd-nehole bd
    ... | bdσ' , bd' = lem-bdσ-into-fst bdσ' , BDFst bd'
    lem-bd-nehole (BDSnd bd)
      with lem-bd-nehole bd
    ... | bdσ' , bd' = lem-bdσ-into-snd bdσ' , BDSnd bd'
    lem-bd-nehole (BDHole {u = u} {σ = Id Γ} BDσId) = lem-bdσ-into-hole BDσsId , BDHole BDσId
    lem-bd-nehole (BDHole {u = u} {σ = Subst d y σ'} (BDσSubst (BDNEHole x x₃) x₁ (UBNEHole x₂ x₄)))
      with lem-bdσ-nehole x₁
    ... | bdσ , bdσs = (lem-bdσ-into-hole (BDσsSubst x bdσ x₂)) , (BDHole (BDσSubst x₃ bdσs x₄))
    lem-bd-nehole (BDNEHole {σ = Id Γ} BDσId bd)
      with lem-bd-nehole bd
    ... | bdσ , bdσs = lem-bdσ-into-nehole BDσsId bdσ , BDNEHole BDσId bdσs
    lem-bd-nehole (BDNEHole {σ = Subst d y σ'} (BDσSubst (BDNEHole x x₃) x₁ (UBNEHole x₂ x₄)) bd)
      with lem-bd-nehole bd | lem-bdσ-nehole x₁
    ... | bdσ , bd' | bdσs , bdσ' = (lem-bdσ-into-nehole (BDσsSubst x bdσs x₂) bdσ) , BDNEHole (BDσSubst x₃ bdσ' x₄) bd'
    lem-bd-nehole (BDCast bd)
      with lem-bd-nehole bd
    ... | bdσ' , bd' = lem-bdσ-into-cast bdσ' , BDCast bd'
    lem-bd-nehole (BDFailedCast bd)
      with lem-bd-nehole bd
    ... | bdσ' , bd' = lem-bdσ-into-failedcast bdσ' , BDFailedCast bd'
    
                                               
    binders-disjoint-sym : ∀{d1 d2} → binders-disjoint d1 d2 → binders-disjoint d2 d1
    binders-disjoint-sym {d2 = N x} bd = BDNum
    binders-disjoint-sym {d2 = d2 ·+ d3} bd
      with lem-bd-plus bd
    ... | bd1 , bd2 = BDPlus (binders-disjoint-sym bd1) (binders-disjoint-sym bd2)
    binders-disjoint-sym {d2 = X x} bd = BDVar
    binders-disjoint-sym {d2 = ·λ x ·[ x₁ ] d2} bd
      with lem-bd-lam bd
    ... | bd' , ub = BDLam (binders-disjoint-sym bd') ub
    binders-disjoint-sym {d2 = d2 ∘ d3} bd
      with lem-bd-ap bd
    ... | bd1 , bd2 = BDAp (binders-disjoint-sym bd1) (binders-disjoint-sym bd2)
    binders-disjoint-sym {d2 = inl x d2} bd = BDInl (binders-disjoint-sym (lem-bd-inl bd))
    binders-disjoint-sym {d2 = inr x d2} bd = BDInr (binders-disjoint-sym (lem-bd-inr bd))
    binders-disjoint-sym {d2 = case d2 x d3 x₁ d4} bd
      with lem-bd-case bd
    ... | bdd , ubx , bdd1 , uby , bdd2 = BDCase (binders-disjoint-sym bdd) ubx (binders-disjoint-sym bdd1) uby (binders-disjoint-sym bdd2)
    binders-disjoint-sym {d2 = ⟨ d2 , d3 ⟩} bd
      with lem-bd-pair bd
    ... | bd1 , bd2 = BDPair (binders-disjoint-sym bd1) (binders-disjoint-sym bd2)
    binders-disjoint-sym {d2 = fst d2} bd = BDFst (binders-disjoint-sym (lem-bd-fst bd))
    binders-disjoint-sym {d2 = snd d2} bd = BDSnd (binders-disjoint-sym (lem-bd-snd bd))
    binders-disjoint-sym {d2 = ⦇-⦈⟨ u , σ ⟩} bd = BDHole (lem-bd-hole bd)
    binders-disjoint-sym {d2 = ⦇⌜ d2 ⌟⦈⟨ u , σ ⟩} bd
      with lem-bd-nehole bd
    ... | bdσ , bd' = BDNEHole bdσ (binders-disjoint-sym bd')
    binders-disjoint-sym {d2 = d2 ⟨ x ⇒ x₁ ⟩} bd = BDCast (binders-disjoint-sym (lem-bd-cast bd))
    binders-disjoint-sym {d2 = d2 ⟨ x ⇒⦇-⦈⇏ x₁ ⟩} bd = BDFailedCast (binders-disjoint-sym (lem-bd-failedcast bd))
  
