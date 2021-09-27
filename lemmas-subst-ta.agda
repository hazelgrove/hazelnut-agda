open import Prelude
open import Nat
open import core
open import contexts
open import contraction
open import weakening
open import exchange
open import lemmas-disjointness
open import binders-disjoint-checks

module lemmas-subst-ta where
  -- this is what makes the binders-unique assumption below good enough: it
  -- tells us that we can pick fresh variables
  mutual
    binders-envfresh : ∀{Δ Γ Γ' y σ} → Δ , Γ ⊢ σ :s: Γ' → y # Γ → unbound-in-σ y σ → binders-unique-σ σ → envfresh y σ
    binders-envfresh {Γ' = Γ'} {y = y} (STAId x) apt unbound unique with ctxindirect Γ' y
    binders-envfresh {Γ' = Γ'} {y = y} (STAId x₁) apt unbound unique | Inl x = abort (somenotnone (! (x₁ y (π1 x) (π2 x)) · apt))
    binders-envfresh (STAId x₁) apt unbound unique | Inr x = EFId x
    binders-envfresh {Γ = Γ} {y = y} (STASubst  {y = z} subst x₁) apt (UBσSubst x₂ unbound neq) (BUσSubst zz x₃ x₄) =
                                                                                    EFSubst (binders-fresh {y = y} x₁ zz x₂ apt)
                                                                                            (binders-envfresh subst (apart-extend1 Γ neq apt) unbound x₃)
                                                                                            neq

    binders-fresh : ∀{Δ Γ d2 τ y} →
                    Δ , Γ ⊢ d2 :: τ →
                    binders-unique d2 →
                    unbound-in y d2 →
                    Γ y == None →
                    fresh y d2
    binders-fresh TANum BUHole UBNum apt = FNum
    binders-fresh {y = y} (TAVar {x = x} x₁)  BUVar UBVar apt with natEQ y x
    binders-fresh (TAVar x₂) BUVar UBVar apt | Inl refl = abort (somenotnone (! x₂ · apt))
    binders-fresh (TAVar x₂) BUVar UBVar apt | Inr x₁ = FVar x₁
    binders-fresh {y = y} (TALam {x = x} x₁ wt) bu2 ub apt  with natEQ y x
    binders-fresh (TALam x₂ wt) bu2 (UBLam2 x₁ ub) apt | Inl refl = abort (x₁ refl)
    binders-fresh {Γ = Γ} (TALam {x = x} x₂ wt) (BULam bu2 x₃) (UBLam2 x₄ ub) apt | Inr x₁ =  FLam x₁ (binders-fresh wt bu2 ub (apart-extend1 Γ x₄ apt))
    binders-fresh (TAAp wt wt₁)  (BUAp bu2 bu3 x) (UBAp ub ub₁) apt = FAp (binders-fresh wt bu2 ub apt) (binders-fresh wt₁ bu3 ub₁ apt)
    binders-fresh (TAEHole x₁ x₂) (BUEHole x) (UBHole x₃) apt = FHole (binders-envfresh x₂ apt x₃ x )
    binders-fresh (TANEHole x₁ wt x₂) (BUNEHole bu2 x) (UBNEHole x₃ ub) apt = FNEHole (binders-envfresh x₂ apt x₃ x) (binders-fresh wt bu2  ub apt)
    binders-fresh (TACast wt x₁) (BUCast bu2) (UBCast ub) apt = FCast (binders-fresh wt  bu2  ub apt)
    binders-fresh (TAFailedCast wt x x₁ x₂) (BUFailedCast bu2) (UBFailedCast ub) apt = FFailedCast (binders-fresh wt  bu2  ub apt)
    binders-fresh (TAInl wt) (BUInl bu) (UBInl ub) apt = FInl (binders-fresh wt bu ub apt)
    binders-fresh (TAInr wt) (BUInr bu) (UBInr ub) apt = FInr (binders-fresh wt bu ub apt)
    binders-fresh {Γ = Γ} (TACase wt x wt₁ x₁ wt₂) (BUCase bu bu₁ bu₂ x₂ x₃ x₄ x₅ x₆ x₇ x₈ x₉ x₁₀) (UBCase ub x₁₁ ub₁ x₁₂ ub₂) apt = FCase (binders-fresh wt bu ub apt) x₁₁ (binders-fresh wt₁ bu₁ ub₁ (apart-extend1 Γ x₁₁ apt)) x₁₂ (binders-fresh wt₂ bu₂ ub₂ (apart-extend1 Γ x₁₂ apt))
    binders-fresh (TAPlus wt wt₁) () ub apt
    binders-fresh (TAPair wt wt₁) (BUPair bu bu₁ x) (UBPair ub ub₁) apt = FPair (binders-fresh wt bu ub apt) (binders-fresh wt₁ bu₁ ub₁ apt)
    binders-fresh (TAFst wt) (BUFst bu) (UBFst ub) apt = FFst (binders-fresh wt bu ub apt)
    binders-fresh (TASnd wt) (BUSnd bu) (UBSnd ub) apt = FSnd (binders-fresh wt bu ub apt)
    
  -- the substition lemma for preservation
  lem-subst : ∀{Δ Γ x τ1 d1 τ d2} →
              x # Γ →
              binders-disjoint d1 d2 →
              binders-unique d2 →
              Δ , Γ ,, (x , τ1) ⊢ d1 :: τ →
              Δ , Γ ⊢ d2 :: τ1 →
              Δ , Γ ⊢ [ d2 / x ] d1 :: τ
  lem-subst apt bd bu2 (TANum) wt = TANum
  lem-subst apt (BDPlus bd bd₁) bu2 (TAPlus wt1 wt2) wt3 = TAPlus (lem-subst apt bd bu2 wt1 wt3) (lem-subst apt bd₁ bu2 wt2 wt3)
  lem-subst {x = x} apt bd bu2 (TAVar {x = x'} x₂) wt2 with natEQ x' x
  ... | Inl refl with natEQ x x
  ... | Inr x≠x = abort (x≠x refl)
  ... | Inl refl with someinj x₂
  ... | refl = wt2
  lem-subst {x = x} apt bd bu2 (TAVar {x = x'} x₂) wt2 | Inr x'≠x with natEQ x x'
  ... | Inl refl = abort (x'≠x refl)
  ... | Inr x'≠x = TAVar x₂
  lem-subst {Δ = Δ} {Γ = Γ} {x = x} {d2 = d2} x#Γ (BDLam bd bd') bu2 (TALam {x = y} {τ1 = τ1} {d = d} {τ2 = τ2} x₂ wt1) wt2 with natEQ y x
  ... | Inl refl with natEQ x x
  ... | Inr x≠x = abort (x≠x refl)
  ... | Inl refl = abort (somenotnone x₂)
  lem-subst {Δ = Δ} {Γ = Γ} {x = x} {d2 = d2} x#Γ (BDLam bd bd') bu2 (TALam {x = y} {τ1 = τ1} {d = d} {τ2 = τ2} x₂ wt1) wt2 | Inr y≠x with natEQ x y
  ... | Inl refl = abort (y≠x refl)
  ... | Inr x≠y = TALam x₂ (lem-subst (apart-extend1 Γ x≠y x#Γ) bd bu2 (exchange-ta-Γ x≠y wt1) (weaken-ta (binders-fresh wt2 bu2 bd' x₂) wt2))
  lem-subst apt (BDAp bd bd₁) bu3 (TAAp wt1 wt2) wt3 = TAAp (lem-subst apt bd bu3 wt1 wt3) (lem-subst apt bd₁ bu3 wt2 wt3)
  lem-subst apt bd bu2 (TAEHole inΔ sub) wt2 = TAEHole inΔ (STASubst sub wt2)
  lem-subst apt (BDNEHole x₁ bd) bu2 (TANEHole x₃ wt1 x₄) wt2 = TANEHole x₃ (lem-subst apt bd bu2 wt1 wt2) (STASubst x₄ wt2)
  lem-subst apt (BDCast bd) bu2 (TACast wt1 x₁) wt2 = TACast (lem-subst apt bd bu2 wt1 wt2) x₁
  lem-subst apt (BDFailedCast bd) bu2 (TAFailedCast wt1 x₁ x₂ x₃) wt2 = TAFailedCast (lem-subst apt bd bu2 wt1 wt2) x₁ x₂ x₃
  lem-subst apt (BDInl bd) bu (TAInl wt1) wt2 = TAInl (lem-subst apt bd bu wt1 wt2)
  lem-subst apt (BDInr bd) bu (TAInr wt1) wt2 = TAInr (lem-subst apt bd bu wt1 wt2)
  lem-subst {Δ = Δ} {Γ = Γ} {x = x} {d1 = .(case _ _ _ _ _)} {d2 = d2} apt (BDCase bd x₁ bd₁ x₂ bd₂) bu (TACase {d = d} {τ1 = τ1} {τ2 = τ2} {x = y} {y = z} wt1 x₃ wt3 x₄ wt4) wt2
    with natEQ y x | natEQ z x
  ... | Inl refl | Inl refl with natEQ x x
  ... | Inr x≠x = abort (x≠x refl)
  ... | Inl refl = abort (somenotnone x₄)
  lem-subst {Δ = Δ} {Γ = Γ} {x = x} {d1 = .(case _ _ _ _ _)} {d2 = d2} apt (BDCase bd x₁ bd₁ x₂ bd₂) bu (TACase {d = d} {τ1 = τ1} {τ2 = τ2} {x = y} {y = z} wt1 x₃ wt3 x₄ wt4) wt2 | Inl refl | Inr z≠x with natEQ x x 
  ... | Inr x≠x = abort (x≠x refl)
  ... | Inl refl = abort (somenotnone x₃)
  lem-subst {Δ = Δ} {Γ = Γ} {x = x} {d1 = .(case _ _ _ _ _)} {d2 = d2} apt (BDCase bd x₁ bd₁ x₂ bd₂) bu (TACase {d = d} {τ1 = τ1} {τ2 = τ2} {x = y} {y = z} wt1 x₃ wt3 x₄ wt4) wt2 | Inr y≠x  | Inl refl with natEQ x x
  ... | Inr x≠x = abort (x≠x refl)
  ... | Inl refl = abort (somenotnone x₄)
  lem-subst {Δ = Δ} {Γ = Γ} {x = x} {d1 = .(case _ _ _ _ _)} {d2 = d2} apt (BDCase bd x₁ bd₁ x₂ bd₂) bu (TACase {d = d} {τ1 = τ1} {τ2 = τ2} {x = y} {y = z} wt1 x₃ wt3 x₄ wt4) wt2 | Inr y≠x  | Inr z≠x with natEQ x z
  ... | Inl refl = abort (z≠x refl)
  ... | Inr x≠z with natEQ x y
  ... | Inl refl = abort (y≠x refl)
  ... | Inr x≠y = TACase (lem-subst apt bd bu wt1 wt2) x₃ (lem-subst (apart-extend1 Γ x≠y apt) bd₁ bu (exchange-ta-Γ x≠y wt3) (weaken-ta (binders-fresh wt2 bu x₁ x₃) wt2)) x₄ (lem-subst (apart-extend1 Γ x≠z apt) bd₂ bu (exchange-ta-Γ x≠z wt4) (weaken-ta (binders-fresh wt2 bu x₂ x₄) wt2))
  lem-subst apt (BDPair bd bd₁) bu (TAPair wt1 wt3) wt2 = TAPair (lem-subst apt bd bu wt1 wt2) (lem-subst apt bd₁ bu wt3 wt2)
  lem-subst apt (BDFst bd) bu (TAFst wt1) wt2 = TAFst (lem-subst apt bd bu wt1 wt2)
  lem-subst apt (BDSnd bd) bu (TASnd wt1) wt2 = TASnd (lem-subst apt bd bu wt1 wt2)

  lem-subst-cast-sta : ∀{Δ Γ x τ1 τ2 σ Γ'} →
                       x # Γ →
                       τ1 ~ τ2 →
                       Δ , Γ ,, (x , τ2) ⊢ σ :s: Γ' →
                       Δ , Γ ,, (x , τ1) ⊢ Subst (X x ⟨ τ1 ⇒ τ2 ⟩) x σ :s: Γ'
  lem-subst-cast-sta {Γ = Γ} {x = x} {τ1 = τ1} {τ2 = τ2} {Γ' = Γ'} x#Γ con (STAId sub) = STASubst (STAId Γ'⊆) (TACast (TAVar (ctx-top Γ x τ1 x#Γ)) con)
      where
        Γ'⊆ : (y : Nat) (τ : htyp) → (y , τ) ∈ Γ' → (y , τ) ∈ (Γ ,, (x , τ1) ,, (x , τ2))
        Γ'⊆ y τ y∈Γ' with lem-dom-union {Δ1 = ■(x , τ2)} {Δ2 = Γ} (sub y τ y∈Γ')
        ... | Inl y∈x with natEQ x y
        ... | Inr x≠y = abort (somenotnone (! y∈x)) 
        ... | Inl refl = y∈x
        Γ'⊆ y τ y∈Γ' | Inr y∈Γ with natEQ x y
        ... | Inl refl = abort (somenotnone ((! y∈Γ) · x#Γ))
        ... | Inr x≠y with natEQ x y
        ... | Inl refl = abort (x≠y refl)
        ... | Inr x≠y' = y∈Γ
  lem-subst-cast-sta {Δ = Δ} {Γ = Γ} {x = x} {τ1 = τ1} {τ2 = τ2} {Γ' = Γ'} x#Γ con (STASubst {σ = σ} {y = y} {d = d} {τ = τ} wsta wt) = STASubst (STASubst (tr (λ c → Δ , c ,, (y , τ) ⊢ σ :s: Γ') (! (update Γ x τ1 τ2)) wsta) (tr (λ c → Δ , c ⊢ d :: τ) (! (update Γ x τ1 τ2)) wt)) (TACast (TAVar (ctx-top Γ x τ1 x#Γ)) con)
  
  lem-subst-cast-ta : ∀{Δ Γ d x τ1 τ2 τ} →
                   x # Γ →
                   binders-unique d →
                   τ1 ~ τ2 →
                   Δ , Γ ,, (x , τ2) ⊢ d :: τ →
                   Δ , Γ ,, (x , τ1) ⊢ [ (X x ⟨ τ1 ⇒ τ2 ⟩) / x ] d :: τ
  lem-subst-cast-ta apt bu con TANum = TANum
  lem-subst-cast-ta {Γ = Γ} {x = x} {τ1 = τ1} {τ2 = τ2} apt bu con (TAVar {x = x'} x₁)
      with natEQ x x'
  ... | Inl refl with natEQ x' x
  ... | Inr x'≠x = abort (x'≠x refl)
  ... | Inl refl with Γ x
  ... | None with natEQ x x
  ... | Inr x≠x = abort (x≠x refl)
  ... | Inl refl with someinj x₁
  ... | refl = TACast (TAVar (x∈∪l (■ (x , τ1)) Γ x τ1 (x∈■ x τ1))) con
  lem-subst-cast-ta {Γ = Γ} {x = x} {τ1 = τ1} {τ2 = τ2} apt bu con (TAVar {x = x} x₁) | Inl refl | Inl refl | Some t with someinj x₁
  ... | refl = abort (somenotnone apt)
  lem-subst-cast-ta {Γ = Γ} {x = x} {τ1 = τ1} {τ2 = τ2} {τ = τ} apt bu con (TAVar {x = x'} x₁) | Inr x≠x' with natEQ x' x
  ... | Inl refl = abort (x≠x' refl)
  ... | Inr x'≠x = TAVar (x∈∪r (■(x , τ1)) Γ x' τ x₁ (apart-singleton (λ refl → abort (x'≠x refl))))
  lem-subst-cast-ta {Δ = Δ} {Γ = Γ} {x = x} {τ = τ1 ==> τ3} apt (BULam bu x₁) con (TALam {x = y} x₂ wt)
    with natEQ x y
  ... | Inl refl = abort (somenotnone x₂)
  ... | Inr x≠y with natEQ y x
  ... | Inl refl = abort (x≠y refl)
  ... | Inr y≠x = TALam (apart-extend1 Γ y≠x x₂) (exchange-ta-Γ y≠x (lem-subst-cast-ta (apart-extend1 Γ x≠y apt) bu con (exchange-ta-Γ x≠y wt)))
  lem-subst-cast-ta {Γ = Γ} apt (BUAp bu bu₁ x) con (TAAp wt wt₁) = TAAp (lem-subst-cast-ta {Γ = Γ} apt bu con wt) (lem-subst-cast-ta {Γ = Γ} apt bu₁ con wt₁)
  lem-subst-cast-ta {Γ = Γ} apt (BUInl bu) con (TAInl wt) = TAInl (lem-subst-cast-ta {Γ = Γ} apt bu con wt)
  lem-subst-cast-ta {Γ = Γ} apt (BUInr bu) con (TAInr wt) = TAInr (lem-subst-cast-ta {Γ = Γ} apt bu con wt)
  lem-subst-cast-ta {x = x} apt (BUCase bu bu₁ bu₂ x₂ x₃ x₄ x₅ x₆ x₇ x₈ x₉ x₁₀) con (TACase {x = y} {y = z} wt apty wt₁ aptz wt₂) with natEQ y x | natEQ z x
  ... | Inl refl | Inl refl with natEQ x x
  ... | Inr x≠x = abort (x≠x refl)
  ... | Inl refl = abort (somenotnone aptz)
  lem-subst-cast-ta {x = x} apt (BUCase bu bu₁ bu₂ x₂ x₃ x₄ x₅ x₆ x₇ x₈ x₉ x₁₀) con (TACase {x = y} {y = z} wt apty wt₁ aptz wt₂) | Inl refl | Inr z≠x with natEQ x x
  ... | Inr x≠x = abort (x≠x refl)
  ... | Inl refl = abort (somenotnone apty)
  lem-subst-cast-ta {x = x} apt (BUCase bu bu₁ bu₂ x₂ x₃ x₄ x₅ x₆ x₇ x₈ x₉ x₁₀) con (TACase {x = y} {y = z} wt apty wt₁ aptz wt₂) | Inr y≠x  | Inl refl with natEQ x x
  ... | Inr x≠x = abort (x≠x refl)
  ... | Inl refl = abort (somenotnone aptz)
  lem-subst-cast-ta {Γ = Γ} {x = x} apt (BUCase bu bu₁ bu₂ x₂ x₃ x₄ x₅ x₆ x₇ x₈ x₉ x₁₀) con (TACase {x = y} {y = z} wt apty wt₁ aptz wt₂) | Inr y≠x  | Inr z≠x with natEQ x z
  ... | Inl refl = abort (z≠x refl)
  ... | Inr x≠z with natEQ x y
  ... | Inl refl = abort (y≠x refl)
  ... | Inr x≠y = TACase (lem-subst-cast-ta apt bu con wt) (apart-extend1 Γ y≠x apty) (exchange-ta-Γ y≠x (lem-subst-cast-ta (apart-extend1 Γ x≠y apt) bu₁ con (exchange-ta-Γ x≠y wt₁))) (apart-extend1 Γ z≠x aptz) (exchange-ta-Γ z≠x (lem-subst-cast-ta (apart-extend1 Γ x≠z apt) bu₂ con (exchange-ta-Γ x≠z wt₂)))
  lem-subst-cast-ta apt (BUEHole x₂) con (TAEHole x x₁) = TAEHole x (lem-subst-cast-sta apt con x₁)
  lem-subst-cast-ta apt (BUNEHole bu x₂) con (TANEHole x wt x₁) = TANEHole x (lem-subst-cast-ta apt bu con wt) (lem-subst-cast-sta apt con x₁)
  lem-subst-cast-ta apt (BUCast bu) con (TACast wt x) = TACast (lem-subst-cast-ta apt bu con wt) x
  lem-subst-cast-ta apt (BUFailedCast bu) con (TAFailedCast wt x x₁ x₂) = TAFailedCast (lem-subst-cast-ta apt bu con wt) x x₁ x₂
  lem-subst-cast-ta apt (BUPair bu bu₁ x) con (TAPair wt wt₁) = TAPair (lem-subst-cast-ta apt bu con wt) (lem-subst-cast-ta apt bu₁ con wt₁)
  lem-subst-cast-ta apt (BUFst bu) con (TAFst wt) = TAFst (lem-subst-cast-ta apt bu con wt)
  lem-subst-cast-ta apt (BUSnd bu) con (TASnd wt) = TASnd (lem-subst-cast-ta apt bu con wt)
