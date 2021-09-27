open import Nat
open import Prelude
open import core
open import contexts
open import typed-elaboration
open import lemmas-gcomplete
open import lemmas-complete

module complete-elaboration where
  mutual
    complete-elaboration-synth : ∀{e τ Γ Δ d} →
                                 Γ gcomplete →
                                 e ecomplete →
                                 Γ ⊢ e ⇒ τ ~> d ⊣ Δ →
                                 (d dcomplete × τ tcomplete × Δ == ∅)
    complete-elaboration-synth gc ec ESNum = DCNum , TCNum , refl
    complete-elaboration-synth gc (ECPlus ec₁ ec₂) (ESPlus {Δ1 = Δ1} {Δ2 = Δ2} apt dis x₁ x₂)
      with complete-elaboration-ana gc ec₁ TCNum x₁ | complete-elaboration-ana gc ec₂ TCNum x₂
    ... | d1comp , t1comp , refl | d2comp , t2comp , refl =
      DCPlus (DCCast d1comp t1comp TCNum) (DCCast d2comp t2comp TCNum) , TCNum , refl
    complete-elaboration-synth gc ec (ESVar x₁) = DCVar , gc _ _ x₁ , refl
    complete-elaboration-synth gc (ECLam2 ec x₁) (ESLam x₂ exp)
      with complete-elaboration-synth (gcomp-extend gc x₁ x₂) ec exp
    ... | ih1 , ih2 , ih3 = DCLam ih1 x₁ , TCArr x₁ ih2 , ih3
    complete-elaboration-synth gc (ECAp ec ec₁) (ESAp _ _ x MAHole x₂ x₃)
      with comp-synth gc ec x
    ... | ()
    complete-elaboration-synth gc (ECAp ec ec₁) (ESAp {Δ1 = Δ1} {Δ2 = Δ2} _ _ x MAArr x₂ x₃)
      with comp-synth gc ec x
    ... | TCArr t1 t2
      with complete-elaboration-ana gc ec (TCArr t1 t2) x₂ | complete-elaboration-ana gc ec₁ t1 x₃
    ... | ih1 , _ ,  ih4 | ih2 , _ , ih3 = DCAp (DCCast ih1 (comp-ana gc x₂ ih1) (TCArr t1 t2)) (DCCast ih2 (comp-ana gc x₃ ih2) t1) ,
                                  t2 ,
                                  tr (λ qq → (qq ∪ Δ2) == ∅) (! ih4) (tr (λ qq → (∅ ∪ qq) == ∅) (! ih3) refl)
    complete-elaboration-synth gc () ESEHole
    complete-elaboration-synth gc () (ESNEHole _ exp)
    complete-elaboration-synth gc (ECAsc x ec) (ESAsc x₁)
      with complete-elaboration-ana gc ec x x₁
    ... | ih1 , _ , ih2 = DCCast ih1 (comp-ana gc x₁ ih1) x , x , ih2
    complete-elaboration-synth gc (ECPair ec ec₁) (ESPair {Δ1 = Δ1} {Δ2 = Δ2} x x₁ x₂ x₃)
      with complete-elaboration-synth gc ec x₂ | complete-elaboration-synth gc ec₁ x₃
    ... | ih1 , ih2 , ih3 | ih1' , ih2' , ih3' = DCPair ih1 ih1' , TCProd ih2 ih2' , tr (λ qq → (qq ∪ Δ2) == ∅) (! ih3) ih3'
    
    complete-elaboration-ana : ∀{e τ τ' Γ Δ d} →
                               Γ gcomplete →
                               e ecomplete →
                               τ tcomplete →
                               Γ ⊢ e ⇐ τ ~> d :: τ' ⊣ Δ →
                               (d dcomplete × τ' tcomplete × Δ == ∅)
    complete-elaboration-ana gc (ECLam1 ec) () (EALam x₁ MAHole exp)
    complete-elaboration-ana gc (ECLam1 ec) (TCArr t1 t2)  (EALam x₁ MAArr exp)
      with complete-elaboration-ana (gcomp-extend gc t1 x₁) ec t2 exp
    ... | ih , ih3 , ih2 = DCLam ih t1 , TCArr t1 ih3 , ih2
    complete-elaboration-ana gc ec tc (EASubsume x x₁ x₂ x₃)
      with complete-elaboration-synth gc ec x₂
    ... | ih1 , ih2 , ih3 = ih1 , ih2 , ih3
    complete-elaboration-ana gc (ECInl ec) (TCSum tc tc₁) (EAInl MSSum x₁)
      with complete-elaboration-ana gc ec tc x₁
    ... | ih1 , ih2 , ih3 = DCInl tc₁ ih1 , TCSum ih2 tc₁ , ih3
    complete-elaboration-ana gc (ECInr ec) (TCSum tc tc₁) (EAInr MSSum x₁)
      with complete-elaboration-ana gc ec tc₁ x₁
    ... | ih1 , ih2 , ih3 = DCInr tc ih1 , TCSum tc ih2 , ih3
    complete-elaboration-ana gc (ECCase ec ec₁ ec₂) tc (EACase x x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ MSHole x₁₀ x₁₁)
      with complete-elaboration-synth gc ec x₈ 
    ... | ih1 , () , ih3
    complete-elaboration-ana gc (ECCase ec ec₁ ec₂) tc (EACase {Δ = Δ} {Δ1 = Δ1} {Δ2 = Δ2} x x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ MSSum x₁₀ x₁₁)    
      with complete-elaboration-synth gc ec x₈ 
    ... | ih1 , TCSum ih2 ih4 , ih3  with complete-elaboration-ana (gcomp-extend gc ih2 x₆) ec₁ tc x₁₀
    ... | ih1' , ih2' , ih3' with complete-elaboration-ana (gcomp-extend gc ih4 x₇) ec₂ tc x₁₁
    ... | ih1'' , ih2'' , ih3'' = DCCase (DCCast ih1 (TCSum ih2 ih4) (TCSum ih2 ih4)) (DCCast ih1' ih2' tc) (DCCast ih1'' ih2'' tc) , tc , tr (λ qq → qq ∪ (Δ1 ∪ Δ2) == ∅) (! ih3) (tr (λ qq → ∅ ∪ (qq ∪ Δ2) == ∅) (! ih3') (tr (λ qq → ∅ ∪ (∅ ∪ qq) == ∅) (! ih3'') refl)) 
    
    -- this is just a convenience since it shows up a few times above
    comp-ana : ∀{Γ e τ d τ' Δ} →
               Γ gcomplete →
               Γ ⊢ e ⇐ τ ~> d :: τ' ⊣ Δ →
               d dcomplete →
               τ' tcomplete
    comp-ana gc ex dc = complete-ta gc (π2 (typed-elaboration-ana ex)) dc
