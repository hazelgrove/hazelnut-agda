open import Nat
open import Prelude
open import dynamics-core
open import contexts
open import lemmas-consistency
open import lemmas-disjointness
open import lemmas-matching
open import weakening

module typed-elaboration where
  mutual
    typed-elaboration-synth : {Γ : tctx} {e : hexp} {τ : htyp} {d : ihexp} {Δ : hctx} →
                            Γ ⊢ e ⇒ τ ~> d ⊣ Δ →
                            Δ , Γ ⊢ d :: τ
    typed-elaboration-synth ESNum = TANum
    typed-elaboration-synth (ESPlus dis apt x₁ x₂)
      with typed-elaboration-ana x₁ | typed-elaboration-ana x₂
    ... | con1 , ih1 | con2 , ih2 = TAPlus (TACast (weaken-ta-Δ1 apt ih1) con1) (TACast (weaken-ta-Δ2 apt ih2) con2)
    typed-elaboration-synth (ESVar x₁) = TAVar x₁
    typed-elaboration-synth (ESLam x₁ ex) = TALam x₁ (typed-elaboration-synth ex)
    typed-elaboration-synth (ESAp {Δ1 = Δ1} _ d x₁ x₂ x₃ x₄)
      with typed-elaboration-ana x₃ | typed-elaboration-ana x₄
    ... | con1 , ih1 | con2 , ih2  = TAAp (TACast (weaken-ta-Δ1 d ih1) con1) (TACast (weaken-ta-Δ2 {Δ1 = Δ1} d ih2) con2)
    typed-elaboration-synth (ESEHole {Γ = Γ} {u = u}) with natEQ u u
    ... | Inr u≠u = abort (u≠u refl)
    ... | Inl refl = TAEHole (x∈■ u (Γ , ⦇-⦈)) (STAId (λ x τ z → z))
    typed-elaboration-synth (ESNEHole {Γ = Γ} {τ = τ} {u = u} {Δ = Δ} (d1 , d2) ex)
                            with typed-elaboration-synth ex
    ... | ih1 = TANEHole {Δ = Δ ,, (u , Γ , ⦇-⦈)} (ctx-top Δ u (Γ , ⦇-⦈) (d2 u (lem-domsingle _ _))) (weaken-ta-Δ2 (d2 , d1) ih1) (STAId (λ x τ₁ z → z))
    typed-elaboration-synth (ESAsc x)
      with typed-elaboration-ana x
    ... | con , ih = TACast ih con
    typed-elaboration-synth (ESPair x x₁ x₂ x₃)
      with typed-elaboration-synth x₂ | typed-elaboration-synth x₃
    ... | ih1 | ih2 = TAPair (weaken-ta-Δ1 x₁ ih1) (weaken-ta-Δ2 x₁ ih2)
    typed-elaboration-synth (ESFst x x₁ x₂)
      with typed-elaboration-ana x₂
    ... | con , ih = TAFst (TACast ih con)
    typed-elaboration-synth (ESSnd x x₁ x₂)
      with typed-elaboration-ana x₂
    ... | con , ih = TASnd (TACast ih con)
    
    typed-elaboration-ana : {Γ : tctx} {e : hexp} {τ τ' : htyp} {d : ihexp} {Δ : hctx} →
                            Γ ⊢ e ⇐ τ ~> d :: τ' ⊣ Δ →
                            (τ' ~ τ) × (Δ , Γ ⊢ d :: τ')
    typed-elaboration-ana (EALam x₁ MAHole ex)
      with typed-elaboration-ana ex
    ... | con , D = TCHole1 , TALam x₁ D
    typed-elaboration-ana (EALam x₁ MAArr ex)
      with typed-elaboration-ana ex
    ... | con , D = TCArr TCRefl con , TALam x₁ D
    typed-elaboration-ana (EASubsume x x₁ x₂ x₃) = ~sym x₃ , typed-elaboration-synth x₂
    typed-elaboration-ana (EAEHole {Γ = Γ} {u = u}) = TCRefl , TAEHole (x∈■ u (Γ , _)) (STAId (λ x τ z → z))
    typed-elaboration-ana (EANEHole {Γ = Γ} {u = u} {τ = τ} {Δ = Δ} (d1 , d2) x)
      with typed-elaboration-synth x
    ... | ih1 = TCRefl , TANEHole {Δ = Δ ,, (u , Γ , τ)} (ctx-top Δ u (Γ , τ) (d2 u (lem-domsingle _ _)) ) (weaken-ta-Δ2 (d2 , d1) ih1) (STAId (λ x₁ τ₁ z → z))
    typed-elaboration-ana (EAInl MSHole x₁)
      with typed-elaboration-ana x₁
    ... | con , D = TCHole1 , TAInl D
    typed-elaboration-ana (EAInl MSSum x₁)
      with typed-elaboration-ana x₁
    ... | con , D = TCSum con TCRefl , TAInl D
    typed-elaboration-ana (EAInr MSHole x₁)
      with typed-elaboration-ana x₁
    ... | con , D = TCHole1 , TAInr D
    typed-elaboration-ana (EAInr MSSum x₁)
      with typed-elaboration-ana x₁
    ... | con , D = TCSum TCRefl con , TAInr D
    typed-elaboration-ana (EACase x x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ x₉ x₁₀ x₁₁)
      with typed-elaboration-synth x₈ |
           typed-elaboration-ana x₁₀ | typed-elaboration-ana x₁₁
    ... | D | con1 , D1 | con2 , D2 =
      let Δ##Δ1∪Δ2 = ##-comm (disjoint-parts (##-comm x₃) (##-comm x₄))
      in let wtd   = TACast (weaken-ta-Δ1 Δ##Δ1∪Δ2 D) (▸sum-consist x₉)
      in let wtd1  = TACast (weaken-ta-Δ2 Δ##Δ1∪Δ2 (weaken-ta-Δ1 x₅ D1)) con1
      in let wtd2  = TACast (weaken-ta-Δ2 Δ##Δ1∪Δ2 (weaken-ta-Δ2 x₅ D2)) con2
      in let wt    = TACase wtd x₆ wtd1 x₇ wtd2
      in TCRefl , wt
