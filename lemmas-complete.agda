open import Nat
open import Prelude
open import core

open import lemmas-gcomplete

module lemmas-complete where
  -- no term is both complete and indeterminate
  lem-ind-comp : ∀{d} → d dcomplete → d indet → ⊥
  lem-ind-comp DCNum ()
  lem-ind-comp (DCPlus comp comp₁) (IPlus1 ind fin) = lem-ind-comp comp ind
  lem-ind-comp (DCPlus comp comp₁) (IPlus2 fin ind) = lem-ind-comp comp₁ ind
  lem-ind-comp DCVar ()
  lem-ind-comp (DCLam comp x₁) ()
  lem-ind-comp (DCAp comp comp₁) (IAp x ind x₁) = lem-ind-comp comp ind
  lem-ind-comp (DCCast comp x x₁) (ICastArr x₂ ind) = lem-ind-comp comp ind
  lem-ind-comp (DCCast comp x x₁) (ICastGroundHole x₂ ind) = lem-ind-comp comp ind
  lem-ind-comp (DCCast comp x x₁) (ICastHoleGround x₂ ind x₃) = lem-ind-comp comp ind
  lem-ind-comp (DCInl x comp) (IInl ind) = lem-ind-comp comp ind
  lem-ind-comp (DCInr x comp) (IInr ind) = lem-ind-comp comp ind
  lem-ind-comp (DCCase comp comp₁ comp₂) (ICase x x₁ x₂ ind) = lem-ind-comp comp ind
  lem-ind-comp (DCCast comp x x₁) (ICastSum x₂ ind) = lem-ind-comp comp ind
  lem-ind-comp (DCPair comp comp₁) (IPair1 ind x) = lem-ind-comp comp ind
  lem-ind-comp (DCPair comp comp₁) (IPair2 x ind) = lem-ind-comp comp₁ ind
  lem-ind-comp (DCFst comp) (IFst x x₁ ind) = lem-ind-comp comp ind
  lem-ind-comp (DCSnd comp) (ISnd x x₁ ind) = lem-ind-comp comp ind
  lem-ind-comp (DCCast comp x x₁) (ICastProd x₂ ind) = lem-ind-comp comp ind
  
  -- complete types that are consistent are equal
  complete-consistency : ∀{τ1 τ2} → τ1 ~ τ2 → τ1 tcomplete → τ2 tcomplete → τ1 == τ2
  complete-consistency TCRefl TCNum comp2 = refl
  complete-consistency TCRefl (TCArr comp1 comp2) comp3 = refl
  complete-consistency TCRefl (TCSum tc1 tc3) comp2 = refl
  complete-consistency TCHole1 comp1 ()
  complete-consistency (TCArr consis consis₁) (TCArr comp1 comp2) (TCArr comp3 comp4)
   with complete-consistency consis comp1 comp3 | complete-consistency consis₁ comp2 comp4
  ... | refl | refl = refl
  complete-consistency (TCSum consis consis₁) (TCSum comp1 comp2) (TCSum comp3 comp4)
    with complete-consistency consis comp1 comp3 | complete-consistency consis₁ comp2 comp4
  ... | refl | refl = refl
  complete-consistency TCRefl (TCProd comp comp₁) comp2 = refl
  complete-consistency TCHole2 () comp2
  complete-consistency (TCProd consis consis₁) (TCProd comp1 comp2) (TCProd comp3 comp4)
    with complete-consistency consis comp1 comp3 | complete-consistency consis₁ comp2 comp4
  ... | refl | refl = refl
  
  -- a well typed complete term is assigned a complete type
  complete-ta : ∀{Γ Δ d τ} → (Γ gcomplete) →
                             (Δ , Γ ⊢ d :: τ) →
                             d dcomplete →
                             τ tcomplete
  complete-ta gc TANum comp = TCNum
  complete-ta gc (TAPlus wt wt₁) comp = TCNum
  complete-ta gc (TAVar x₁) DCVar = gc _ _ x₁
  complete-ta gc (TALam a wt) (DCLam comp x₁) = TCArr x₁ (complete-ta (gcomp-extend gc x₁ a ) wt comp)
  complete-ta gc (TAAp wt wt₁) (DCAp comp comp₁)
    with complete-ta gc wt comp
  ... | TCArr qq qq₁ = qq₁
  complete-ta gc (TAEHole x x₁) ()
  complete-ta gc (TANEHole x wt x₁) ()
  complete-ta gc (TACast wt x) (DCCast comp x₁ x₂) = x₂
  complete-ta gc (TAFailedCast wt x x₁ x₂) ()
  complete-ta gc (TAInl wt) (DCInl x comp) = TCSum (complete-ta gc wt comp) x
  complete-ta gc (TAInr wt) (DCInr x comp) = TCSum x (complete-ta gc wt comp)
  complete-ta gc (TACase wt apt₁ wt₁ apt₂ wt₂) (DCCase comp comp₁ comp₂)
    with complete-ta gc wt comp
  ... | TCSum τc1 τc2 =  complete-ta (gcomp-extend gc τc1 apt₁) wt₁ comp₁ 
  complete-ta gc (TAPair wt wt₁) (DCPair comp comp₁) = TCProd (complete-ta gc wt comp) (complete-ta gc wt₁ comp₁)
  complete-ta gc (TAFst wt) (DCFst comp)
    with complete-ta gc wt comp
  ... | TCProd τc1 τc2 = τc1
  complete-ta gc (TASnd wt) (DCSnd comp)
    with complete-ta gc wt comp
  ... | TCProd τc1 τc2 = τc2
  
  -- a well typed term synthesizes a complete type
  comp-synth : ∀{Γ e τ} →
               Γ gcomplete →
               e ecomplete →
               Γ ⊢ e => τ →
               τ tcomplete
  comp-synth gc ec SNum = TCNum
  comp-synth gc ec (SPlus x x₁ x₂) = TCNum
  comp-synth gc (ECAsc x ec) (SAsc x₁) = x
  comp-synth gc ec (SVar x) = gc _ _ x
  comp-synth gc (ECAp ec ec₁) (SAp _ wt MAHole x₁) with comp-synth gc ec wt
  ... | ()
  comp-synth gc (ECAp ec ec₁) (SAp _ wt MAArr x₁) with comp-synth gc ec wt
  comp-synth gc (ECAp ec ec₁) (SAp _ wt MAArr x₁) | TCArr qq qq₁ = qq₁
  comp-synth gc () SEHole
  comp-synth gc () (SNEHole _ wt)
  comp-synth gc (ECLam2 ec x₁) (SLam x₂ wt) = TCArr x₁ (comp-synth (gcomp-extend gc x₁ x₂) ec wt)
  comp-synth gc (ECPair ec ec₁) (SPair x wt wt₁)
    with comp-synth gc ec wt | comp-synth gc ec₁ wt₁
  ... | τc1 | τc2 = TCProd τc1 τc2
