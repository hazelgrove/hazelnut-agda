open import Nat
open import Prelude
open import dynamics-core
open import contexts

open import binders-disjoint-checks
open import exchange
open import lemmas-consistency
open import lemmas-disjointness
open import lemmas-subst-ta
open import type-assignment-unicity
open import weakening

module preservation where
  -- if d and d' both result from filling the hole in ε with terms of the
  -- same type, they too have the same type.
  wt-different-fill : ∀{Δ Γ d ε d1 d2 d' τ τ1} →
                      d == ε ⟦ d1 ⟧ →
                      Δ , Γ ⊢ d :: τ →
                      Δ , Γ ⊢ d1 :: τ1 →
                      Δ , Γ ⊢ d2 :: τ1 →
                      d' == ε ⟦ d2 ⟧ →
                      Δ , Γ ⊢ d' :: τ
  wt-different-fill FHOuter D1 D2 D3 FHOuter
    with type-assignment-unicity D1 D2
  ... | refl = D3
  wt-different-fill (FHPlus1 eps1) (TAPlus D1 D2) D3 D4 (FHPlus1 eps2) = TAPlus (wt-different-fill eps1 D1 D3 D4 eps2) D2
  wt-different-fill (FHPlus2 eps1) (TAPlus D1 D2) D3 D4 (FHPlus2 eps2) = TAPlus D1 (wt-different-fill eps1 D2 D3 D4 eps2)
  wt-different-fill (FHAp1 eps) (TAAp D1 D2) D3 D4 (FHAp1 D5) = TAAp (wt-different-fill eps D1 D3 D4 D5) D2
  wt-different-fill (FHAp2 eps) (TAAp D1 D2) D3 D4 (FHAp2 D5) = TAAp D1 (wt-different-fill eps D2 D3 D4 D5)
  wt-different-fill (FHInl eps1) (TAInl D) D1 D2 (FHInl eps2) = TAInl (wt-different-fill eps1 D D1 D2 eps2)
  wt-different-fill (FHInr eps1) (TAInr D) D1 D2 (FHInr eps2) = TAInr (wt-different-fill eps1 D D1 D2 eps2)
  wt-different-fill (FHCase eps1) (TACase D x D₁ x₁ D₂) D1 D2 (FHCase eps2) = TACase (wt-different-fill eps1 D D1 D2 eps2) x D₁ x₁ D₂
  wt-different-fill (FHPair1 eps1) (TAPair D D₁) D1 D2 (FHPair1 eps2) = TAPair (wt-different-fill eps1 D D1 D2 eps2) D₁
  wt-different-fill (FHPair2 eps1) (TAPair D D₁) D1 D2 (FHPair2 eps2) = TAPair D (wt-different-fill eps1 D₁ D1 D2 eps2)
  wt-different-fill (FHFst eps1) (TAFst D) D1 D2 (FHFst eps2) = TAFst (wt-different-fill eps1 D D1 D2 eps2)
  wt-different-fill (FHSnd eps1) (TASnd D) D1 D2 (FHSnd eps2) = TASnd (wt-different-fill eps1 D D1 D2 eps2)
  wt-different-fill (FHNEHole eps) (TANEHole x D1 x₁) D2 D3 (FHNEHole D4) = TANEHole x (wt-different-fill eps D1 D2 D3 D4) x₁
  wt-different-fill (FHCast eps) (TACast D1 x) D2 D3 (FHCast D4) = TACast (wt-different-fill eps D1 D2 D3 D4) x
  wt-different-fill (FHFailedCast x) (TAFailedCast y x₁ x₂ x₃) D3 D4 (FHFailedCast eps) = TAFailedCast (wt-different-fill x y D3 D4 eps) x₁ x₂ x₃
  
  -- if a well typed term results from filling the hole in ε, then the term
  -- that filled the hole is also well typed
  wt-filling : ∀{ε Δ Γ d τ d'} →
               Δ , Γ ⊢ d :: τ →
               d == ε ⟦ d' ⟧ →
               Σ[ τ' ∈ htyp ] (Δ , Γ ⊢ d' :: τ')
  wt-filling TANum FHOuter = _ , TANum
  wt-filling (TAPlus ta ta₁) FHOuter = num , TAPlus ta ta₁
  wt-filling (TAPlus ta ta₁) (FHPlus1 eps) = wt-filling ta eps
  wt-filling (TAPlus ta ta₁) (FHPlus2 eps) = wt-filling ta₁ eps
  wt-filling (TAVar x₁) FHOuter = _ , TAVar x₁
  wt-filling (TALam f ta) FHOuter = _ , TALam f ta
  wt-filling (TAAp ta ta₁) FHOuter = _ , TAAp ta ta₁
  wt-filling (TAAp ta ta₁) (FHAp1 eps) = wt-filling ta eps
  wt-filling (TAAp ta ta₁) (FHAp2 eps) = wt-filling ta₁ eps
  wt-filling (TAInl ta) FHOuter = _ , TAInl ta
  wt-filling (TAInl ta) (FHInl eps) = wt-filling ta eps
  wt-filling (TAInr ta) FHOuter = _ , TAInr ta
  wt-filling (TAInr ta) (FHInr eps) = wt-filling ta eps
  wt-filling (TACase ta x ta₁ x₁ ta₂) FHOuter = _ , TACase ta x ta₁ x₁ ta₂
  wt-filling (TACase ta x ta₁ x₁ ta₂) (FHCase eps) = wt-filling ta eps
  wt-filling (TAPair ta ta₁) FHOuter = _ , TAPair ta ta₁
  wt-filling (TAPair ta ta₁) (FHPair1 eps) = wt-filling ta eps
  wt-filling (TAPair ta ta₁) (FHPair2 eps) = wt-filling ta₁ eps
  wt-filling (TAFst ta) FHOuter = _ , TAFst ta
  wt-filling (TAFst ta) (FHFst eps) = wt-filling ta eps
  wt-filling (TASnd ta) FHOuter = _ , TASnd ta
  wt-filling (TASnd ta) (FHSnd eps) = wt-filling ta eps
  wt-filling (TAEHole x x₁) FHOuter = _ , TAEHole x x₁
  wt-filling (TANEHole x ta x₁) FHOuter = _ , TANEHole x ta x₁
  wt-filling (TANEHole x ta x₁) (FHNEHole eps) = wt-filling ta eps
  wt-filling (TACast ta x) FHOuter = _ , TACast ta x
  wt-filling (TACast ta x) (FHCast eps) = wt-filling ta eps
  wt-filling (TAFailedCast x y z w) FHOuter = _ , TAFailedCast x y z w
  wt-filling (TAFailedCast x x₁ x₂ x₃) (FHFailedCast y) = wt-filling x y
  
  -- instruction transitions preserve type
  preserve-trans : ∀{Δ Γ d τ d'} →
                   binders-unique d →
                   Δ , Γ ⊢ d :: τ →
                   d →> d' →
                   Δ , Γ ⊢ d' :: τ
  preserve-trans bd TANum ()
  preserve-trans bd (TAPlus ta TANum) (ITPlus x) = TANum
  preserve-trans bd (TAVar x₁) ()
  preserve-trans bd (TALam _ ta) ()
  preserve-trans (BUAp (BULam bd x₁) bd₁ (BDLam x₂ x₃)) (TAAp (TALam apt ta) ta₁) ITLam = lem-subst apt x₂ bd₁ ta ta₁
  preserve-trans bd (TAAp (TACast ta TCRefl) ta₁) ITApCast = TACast (TAAp ta (TACast ta₁ TCRefl)) TCRefl
  preserve-trans bd (TAAp (TACast ta (TCArr x x₁)) ta₁) ITApCast = TACast (TAAp ta (TACast ta₁ (~sym x))) x₁
  preserve-trans bd (TAEHole x x₁) ()
  preserve-trans bd (TANEHole x ta x₁) ()
  preserve-trans bd (TACast ta x) (ITCastID) = ta
  preserve-trans bd (TACast (TACast ta x) x₁) (ITCastSucceed x₂) = ta
  preserve-trans bd (TACast ta x) (ITGround (MGArr x₁)) = TACast (TACast ta (TCArr TCHole1 TCHole1)) TCHole1
  preserve-trans bd (TACast ta TCHole2) (ITExpand (MGArr x₁)) = TACast (TACast ta TCHole2) (TCArr TCHole2 TCHole2)
  preserve-trans bd (TACast (TACast ta x) x₁) (ITCastFail w y z) = TAFailedCast ta w y z
  preserve-trans bd (TAFailedCast x y z q) ()
  preserve-trans bd (TAInl ta) ()
  preserve-trans bd (TAInr ta) ()
  preserve-trans (BUCase (BUInl bd) bd₁ bd₂ (BDInl x₂) x₃ x₄ x₅ x₆ x₇ x₈ x₉ x₁₀) (TACase (TAInl ta) x ta₁ x₁ ta₂) ITCaseInl = lem-subst x (binders-disjoint-sym x₂) bd ta₁ ta
  preserve-trans (BUCase (BUInr bd) bd₁ bd₂ (BDInr x₂) (BDInr x₃) x₄ x₅ x₆ x₇ x₈ x₉ x₁₀) (TACase (TAInr ta) x ta₁ x₁ ta₂) ITCaseInr = lem-subst x₁ (binders-disjoint-sym x₃) bd ta₂ ta
  preserve-trans (BUCase (BUCast bd) bd₁ bd₂ x₃ x₄ x₅ x₆ x₇ x₈ x₉ x₁₀ x₁₁) (TACase {Γ = Γ} (TACast ta x₂) x ta₁ x₁ ta₂) ITCaseCast
    with ~sum x₂
  ... | τ1~τ2 , τ3~τ4 = TACase ta x (lem-subst-cast-ta {Γ = Γ} x bd₁ τ1~τ2 ta₁) x₁ (lem-subst-cast-ta {Γ = Γ} x₁ bd₂ τ3~τ4 ta₂)
  preserve-trans bd (TAPair ta ta₁) ()
  preserve-trans bd (TAFst (TAPair ta ta₁)) ITFstPair = ta
  preserve-trans bd (TAFst (TACast ta x)) ITFstCast
    with ~prod x
  ... | τ1~τ2 , τ3~τ4 = TACast (TAFst ta) τ1~τ2
  preserve-trans bd (TASnd (TAPair ta ta₁)) ITSndPair = ta₁
  preserve-trans bd (TASnd (TACast ta x)) ITSndCast
    with ~prod x
  ... | τ1~τ2 , τ3~τ4 = TACast (TASnd ta) τ3~τ4
  preserve-trans bd (TACast ta TCRefl) (ITExpand ())
  preserve-trans bd (TACast ta TCHole1) (ITGround (MGSum x₁)) = TACast (TACast ta (TCSum TCHole1 TCHole1)) TCHole1
  preserve-trans bd (TACast ta TCHole1) (ITExpand ())
  preserve-trans bd (TACast ta TCHole2) (ITExpand (MGSum x₁)) = TACast (TACast ta TCHole2) (TCSum TCHole2 TCHole2)
  preserve-trans bd (TACast ta TCHole1) (ITGround (MGProd x₁)) = TACast (TACast ta (TCProd TCHole1 TCHole1)) TCHole1
  preserve-trans bd (TACast ta TCHole2) (ITExpand (MGProd x)) = TACast (TACast ta TCHole2) (TCProd TCHole2 TCHole2)


  
  lem-bd-ε1 : ∀{d ε d0} → d == ε ⟦ d0 ⟧ →
              binders-unique d →
              binders-unique d0
  lem-bd-ε1 FHOuter bd = bd
  lem-bd-ε1 (FHPlus1 eps) (BUPlus bd bd₁ x) = lem-bd-ε1 eps bd
  lem-bd-ε1 (FHPlus2 eps) (BUPlus bd bd₁ x) = lem-bd-ε1 eps bd₁
  lem-bd-ε1 (FHAp1 eps) (BUAp bd bd₁ x) = lem-bd-ε1 eps bd
  lem-bd-ε1 (FHAp2 eps) (BUAp bd bd₁ x) = lem-bd-ε1 eps bd₁
  lem-bd-ε1 (FHInl eps) (BUInl bd) = lem-bd-ε1 eps bd
  lem-bd-ε1 (FHInr eps) (BUInr bd) = lem-bd-ε1 eps bd
  lem-bd-ε1 (FHCase eps) (BUCase bd bd₁ bd₂ x x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈) = lem-bd-ε1 eps bd
  lem-bd-ε1 (FHPair1 eps) (BUPair bd bd₁ x) = lem-bd-ε1 eps bd
  lem-bd-ε1 (FHPair2 eps) (BUPair bd bd₁ x) = lem-bd-ε1 eps bd₁
  lem-bd-ε1 (FHFst eps) (BUFst bd) = lem-bd-ε1 eps bd
  lem-bd-ε1 (FHSnd eps) (BUSnd bd) = lem-bd-ε1 eps bd
  lem-bd-ε1 (FHNEHole eps) (BUNEHole bd x) = lem-bd-ε1 eps bd
  lem-bd-ε1 (FHCast eps) (BUCast bd) = lem-bd-ε1 eps bd
  lem-bd-ε1 (FHFailedCast eps) (BUFailedCast bd) = lem-bd-ε1 eps bd

  
  -- this is the main preservation theorem, gluing together the above
  preservation : {Δ : hctx} {d d' : ihexp} {τ : htyp} {Γ : tctx} →
                 binders-unique d →
                 Δ , Γ ⊢ d :: τ →
                 d ↦ d' →
                 Δ , Γ ⊢ d' :: τ
  preservation bd D (Step x x₁ x₂)
    with wt-filling D x
  ... | (_ , wt) = wt-different-fill x D wt (preserve-trans (lem-bd-ε1 x bd) wt x₁) x₂

  -- note that the exact statement of preservation in the paper, where Γ is
  -- empty indicating that the terms are closed, is an immediate corrolary
  -- of the slightly more general statement above.
  preservation' : {Δ : hctx} {d d' : ihexp} {τ : htyp} →
                  binders-unique d →
                  Δ , ∅ ⊢ d :: τ →
                  d ↦ d' →
                  Δ , ∅ ⊢ d' :: τ
  preservation' = preservation
