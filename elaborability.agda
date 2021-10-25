open import Nat
open import Prelude
open import dynamics-core
open import contexts
open import htype-decidable
open import lemmas-matching
open import lemmas-consistency
open import disjointness
open import typed-elaboration

module elaborability where
      
  mutual
    elaborability-synth : {Γ : tctx} {e : hexp} {τ : htyp} →
                          holes-unique e →
                          Γ ⊢ e => τ →
                          Σ[ d ∈ ihexp ] Σ[ Δ ∈ hctx ]
                            (Γ ⊢ e ⇒ τ ~> d ⊣ Δ)
    elaborability-synth HUNum SNum = _ , _ , ESNum
    elaborability-synth (HUPlus hu1 hu2 hd) (SPlus wt1 wt2)
      with elaborability-ana hu1 wt1 | elaborability-ana hu2 wt2
    ... | _ , _ , _ , D1 | _ , _ , _ , D2 =
      _ , _ , ESPlus hd (elab-ana-disjoint hd D1 D2) D1 D2
    elaborability-synth (HUAsc hu) (SAsc wt)
      with elaborability-ana hu wt
    ... | _ , _ , _ , D = _ , _ , ESAsc D
    elaborability-synth HUVar (SVar x) = _ , _ , ESVar x
    elaborability-synth (HULam2 hu) (SLam apt wt)
      with elaborability-synth hu wt
    ... | _ , _ , D = _ , _ , ESLam apt D
    elaborability-synth (HUAp hu1 hu2 hd) (SAp wt1 m wt2)
      with elaborability-ana hu1 (ASubsume wt1 (~sym (▸arr-consist m))) |
           elaborability-ana hu2 wt2
    ... | _ , _ , _ , D1 | _ , _ , _ , D2 =
      _ , _ , ESAp hd (elab-ana-disjoint hd D1 D2) wt1 m D1 D2
    elaborability-synth (HUPair hu1 hu2 hd) (SPair wt1 wt2)
      with elaborability-synth hu1 wt1 | elaborability-synth hu2 wt2
    ... | _ , _ , D1 | _ , _ ,  D2 = _ , _ , ESPair hd (elab-synth-disjoint hd D1 D2) D1 D2
    elaborability-synth (HUFst hu) (SFst wt m)
      with elaborability-ana hu (ASubsume wt (~sym (▸prod-consist m)))
    ... | _ , _ , _ , D = _ , _ , ESFst wt m D
    elaborability-synth (HUSnd hu) (SSnd wt m)
      with elaborability-ana hu (ASubsume wt (~sym (▸prod-consist m)))
    ... | _ , _ , _ , D = _ , _ , ESSnd wt m D
    elaborability-synth HUHole SEHole = _ , _ , ESEHole
    elaborability-synth (HUNEHole hu hnn) (SNEHole wt)
      with elaborability-synth hu wt
    ... | _ , _ , D = _ , _ , ESNEHole (elab-new-disjoint-synth hnn D) D
    
    elaborability-ana : {Γ : tctx} {e : hexp} {τ : htyp} →
                        holes-unique e →
                        Γ ⊢ e <= τ →
                        Σ[ d ∈ ihexp ] Σ[ Δ ∈ hctx ] Σ[ τ' ∈ htyp ]
                          (Γ ⊢ e ⇐ τ ~> d :: τ' ⊣ Δ)
    elaborability-ana {e = e} hu (ASubsume wt con)
      with elaborability-synth hu wt
    elaborability-ana {e = N x} hu (ASubsume wt con)
      | _ , _ , wt' = _ , _ , _ , EASubsume (λ _ ()) (λ _ _ ()) wt' con
    elaborability-ana {e = e ·+ e₁} hu (ASubsume wt con)
      | _ , _ , wt' = _ , _ , _ , EASubsume (λ _ ()) (λ _ _ ()) wt' con
    elaborability-ana {e = e ·: x} hu (ASubsume wt con)
      | _ , _ , wt' = _ , _ , _ , EASubsume (λ _ ()) (λ _ _ ()) wt' con
    elaborability-ana {e = X x} hu (ASubsume wt con)
      | _ , _ , wt' = _ , _ , _ , EASubsume (λ _ ()) (λ _ _ ()) wt' con
    elaborability-ana {e = ·λ x ·[ x₁ ] e} hu (ASubsume wt con)
      | _ , _ , wt' = _ , _ , _ , EASubsume (λ _ ()) (λ _ _ ()) wt' con
    elaborability-ana {e = e ∘ e₁} hu (ASubsume wt con)
      | _ , _ , wt' = _ , _ , _ , EASubsume (λ _ ()) (λ _ _ ()) wt' con
    elaborability-ana {e = ⟨ e , e₁ ⟩} hu (ASubsume wt con)
      | _ , _ , wt' = _ , _ , _ , EASubsume (λ _ ()) (λ _ _ ()) wt' con
    elaborability-ana {e = fst e} hu (ASubsume wt con)
      | _ , _ , wt' = _ , _ , _ , EASubsume (λ _ ()) (λ _ _ ()) wt' con
    elaborability-ana {e = snd e} hu (ASubsume wt con)
      | _ , _ , wt' = _ , _ , _ , EASubsume (λ _ ()) (λ _ _ ()) wt' con
    elaborability-ana {e = ⦇-⦈[ u ]} hu (ASubsume wt con)
      | _ , _ , wt' = _ , _ , _ , EAEHole
    elaborability-ana {e = ⦇⌜ e ⌟⦈[ u ]} (HUNEHole hu hnn) (ASubsume (SNEHole wt) con)
      | _ , _ , ESNEHole apt wt' with elaborability-synth hu wt
    ... | _ , _ , wt'' = _ , _ , _ , EANEHole (elab-new-disjoint-synth hnn wt'') wt''
    elaborability-ana (HULam1 hu) (ALam apt m wt)
      with elaborability-ana hu wt
    ... | _ , _ , _ , wt' = _ , _ , _ , EALam apt m wt'
    elaborability-ana (HUInl hu) (AInl m wt)
      with elaborability-ana hu wt
    ... | _ , _ , _ , wt' = _ , _ , _ , EAInl m wt'
    elaborability-ana (HUInr hu) (AInr m wt)
      with elaborability-ana hu wt
    ... | _ , _ , _ , wt' = _ , _ , _ , EAInr m wt'
    elaborability-ana (HUCase hu hu1 hu2 hd1 hd2 hd12) (ACase apt1 apt2 m wt wt1 wt2)
      with elaborability-synth hu wt | elaborability-ana hu1 wt1 | elaborability-ana hu2 wt2
    ... | _ , _ , wt' | _ , _ , _ , wt1' | _ , _ , _ , wt2' =
      _ , _ , _ , EACase hd1 hd2 hd12 (elab-synth-ana-disjoint hd1 wt' wt1')
                                      (elab-synth-ana-disjoint hd2 wt' wt2')
                                      (elab-ana-disjoint hd12 wt1' wt2')
                                      apt1 apt2 wt' m wt1' wt2'
