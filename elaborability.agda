open import Nat
open import Prelude
open import core
open import contexts
open import htype-decidable
open import lemmas-matching
open import lemmas-consistency
open import disjointness
open import typed-elaboration

module elaborability where
      
  mutual
    elaborability-synth : {Γ : tctx} {e : hexp} {τ : htyp} →
                          Γ ⊢ e => τ →
                          Σ[ d ∈ ihexp ] Σ[ Δ ∈ hctx ]
                            (Γ ⊢ e ⇒ τ ~> d ⊣ Δ)
    elaborability-synth SNum = _ , _ , ESNum
    elaborability-synth (SPlus dis wt1 wt2)
      with elaborability-ana wt1 | elaborability-ana wt2
    ... | _ , _ , _ , D1 | _ , _ , _ , D2 = _ , _ , ESPlus (elab-ana-disjoint dis D1 D2) dis D1 D2
    elaborability-synth (SAsc {τ = τ} wt)
      with elaborability-ana wt
    ... | _ , _ , τ' , D  = _ , _ , ESAsc D
    elaborability-synth (SVar x) = _ , _ , ESVar x
    elaborability-synth (SLam x₁ wt)
      with elaborability-synth wt
    ... | d' , Δ' , wt' = _ , _ , ESLam x₁ wt'
    elaborability-synth (SAp dis wt1 m wt2)
      with elaborability-ana (ASubsume wt1 (~sym (▸arr-consist m))) | elaborability-ana wt2
    ... | _ , _ , _ , D1 | _ , _ , _ , D2 = _ , _ , ESAp dis (elab-ana-disjoint dis D1 D2) wt1 m D1 D2
    elaborability-synth (SPair x wt wt₁)
      with elaborability-synth wt | elaborability-synth wt₁
    ... | _ , _ , D1 | _ , _ , D2 = _ , _ , ESPair x (elab-synth-disjoint x D1 D2) D1 D2
    elaborability-synth SEHole = _ , _ , ESEHole
    elaborability-synth (SNEHole new wt)
      with elaborability-synth wt
    ... | d' , Δ' , wt' = _ , _ , ESNEHole (elab-new-disjoint-synth new wt') wt'
  
    
    elaborability-ana : {Γ : tctx} {e : hexp} {τ : htyp} →
                         Γ ⊢ e <= τ →
                         Σ[ d ∈ ihexp ] Σ[ Δ ∈ hctx ] Σ[ τ' ∈ htyp ]
                            (Γ ⊢ e ⇐ τ ~> d :: τ' ⊣ Δ)
    elaborability-ana {e = e} (ASubsume D x₁)
      with elaborability-synth D
    -- these cases just pass through, but we need to pattern match so we can prove things aren't holes
    elaborability-ana {e = N n} (ASubsume D x₁)                  | _ , _ , D' = _ , _ , _ , EASubsume (λ _ ()) (λ _ _ ()) D' x₁
    elaborability-ana {e = e1 ·+ e2} (ASubsume D x₁)             | _ , _ , D' = _ , _ , _ , EASubsume (λ _ ()) (λ _ _ ()) D' x₁
    elaborability-ana {e = e ·: x} (ASubsume D x₁)               | _ , _ , D' = _ , _ , _ , EASubsume (λ _ ()) (λ _ _ ()) D' x₁
    elaborability-ana {e = X x} (ASubsume D x₁)                  | _ , _ , D' = _ , _ , _ , EASubsume (λ _ ()) (λ _ _ ()) D' x₁
    elaborability-ana {e = ·λ x e} (ASubsume D x₁)               | _ , _ , D' = _ , _ , _ , EASubsume (λ _ ()) (λ _ _ ()) D' x₁
    elaborability-ana {e = ·λ x [ x₁ ] e} (ASubsume D x₂)        | _ , _ , D' = _ , _ , _ , EASubsume (λ _ ()) (λ _ _ ()) D' x₂
    elaborability-ana {e = e1 ∘ e2} (ASubsume D x₁)              | _ , _ , D' = _ , _ , _ , EASubsume (λ _ ()) (λ _ _ ()) D' x₁
    elaborability-ana {e = ⟨ e1 , e2 ⟩} (ASubsume D x₁)          | _ , _ , D' = _ , _ , _ , EASubsume (λ _ ()) (λ _ _ ()) D' x₁
    elaborability-ana {e = fst e} (ASubsume D x₁)                | _ , _ , D' = _ , _ , _ , EASubsume (λ _ ()) (λ _ _ ()) D' x₁
    elaborability-ana {e = snd e} (ASubsume D x₁)                | _ , _ , D' = _ , _ , _ , EASubsume (λ _ ()) (λ _ _ ()) D' x₁
    -- the two holes are special-cased
    elaborability-ana {e = ⦇-⦈[ x ]} (ASubsume _ _ )                   | _ , _ , _  = _ , _ , _ , EAEHole
    elaborability-ana {Γ} {⦇⌜ e ⌟⦈[ x ]} (ASubsume (SNEHole new wt) x₂) | _ , _ , ESNEHole x₁ D' with elaborability-synth wt
    ... | w , y , z =  _ , _ , _ , EANEHole (elab-new-disjoint-synth new z) z
    -- the lambda cases
    elaborability-ana (ALam x₁ m wt)
      with elaborability-ana wt
    ... | _ , _ , _ , D' = _ , _ , _ , EALam x₁ m D'
    elaborability-ana (AInl x wt)
      with elaborability-ana wt
    ... | _ , _ , _ , D' = _ , _ , _ , EAInl x D'
    elaborability-ana (AInr x wt)
      with elaborability-ana wt
    ... | _ , _ , _ , D' = _ , _ , _ , EAInr x D'
    elaborability-ana (ACase dis dis₁ dis₂ x x₁ x₂ x₃ wt wt₁)
      with elaborability-synth x₃ | elaborability-ana wt | elaborability-ana wt₁
    ... | _ , _ , D | _ , _ , _ , D1 | _ , _ , _ , D2
      with typed-elaboration-ana D1 | typed-elaboration-ana D2
    ... | con1 , wtd1 | con2 , wtd2 = _ , _ , _ , EACase dis dis₁ dis₂ (elab-synth-ana-disjoint dis D D1) (elab-synth-ana-disjoint dis₁ D D2) (elab-ana-disjoint dis₂ D1 D2) x x₁ D x₂ D1 D2
  
