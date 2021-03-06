open import Nat
open import Prelude
open import dynamics-core
open import contexts
open import lemmas-disjointness
open import exchange

-- this module contains all the proofs of different weakening structural
-- properties that we use for the hypothetical judgements
module weakening where
  mutual
    weaken-subst-Δ : ∀{Δ1 Δ2 Γ σ Γ'} →
                     Δ1 ## Δ2 →
                     Δ1 , Γ ⊢ σ :s: Γ' →
                     (Δ1 ∪ Δ2) , Γ ⊢ σ :s: Γ'
    weaken-subst-Δ disj (STAId x) = STAId x
    weaken-subst-Δ disj (STASubst subst x) = STASubst (weaken-subst-Δ disj subst) (weaken-ta-Δ1 disj x)

    weaken-ta-Δ1 : ∀{Δ1 Δ2 Γ d τ} →
                   Δ1 ## Δ2 →
                   Δ1 , Γ ⊢ d :: τ →
                   (Δ1 ∪ Δ2) , Γ ⊢ d :: τ
    weaken-ta-Δ1 disj TANum = TANum
    weaken-ta-Δ1 disj (TAPlus wt wt₁) = TAPlus (weaken-ta-Δ1 disj wt) (weaken-ta-Δ1 disj wt₁)
    weaken-ta-Δ1 disj (TAVar x₁) = TAVar x₁
    weaken-ta-Δ1 disj (TALam x₁ wt) = TALam x₁ (weaken-ta-Δ1 disj wt)
    weaken-ta-Δ1 disj (TAAp wt wt₁) = TAAp (weaken-ta-Δ1 disj wt) (weaken-ta-Δ1 disj wt₁)
    weaken-ta-Δ1 disj (TAInl wt) = TAInl (weaken-ta-Δ1 disj wt)
    weaken-ta-Δ1 disj (TAInr wt) = TAInr (weaken-ta-Δ1 disj wt)
    weaken-ta-Δ1 disj (TACase wt x wt₁ x₁ wt₂) = TACase (weaken-ta-Δ1 disj wt) x (weaken-ta-Δ1 disj wt₁) x₁ (weaken-ta-Δ1 disj wt₂)
    weaken-ta-Δ1 {Δ1} {Δ2} {Γ} disj (TAEHole {u = u} {Γ' = Γ'} x x₁) = TAEHole (x∈∪l Δ1 Δ2 u _ x ) (weaken-subst-Δ disj x₁)
    weaken-ta-Δ1 {Δ1} {Δ2} {Γ} disj (TANEHole {Γ' = Γ'} {u = u} x wt x₁) = TANEHole (x∈∪l Δ1 Δ2 u _ x) (weaken-ta-Δ1 disj wt) (weaken-subst-Δ disj x₁)
    weaken-ta-Δ1 disj (TACast wt x) = TACast (weaken-ta-Δ1 disj wt) x
    weaken-ta-Δ1 disj (TAFailedCast wt x x₁ x₂) = TAFailedCast (weaken-ta-Δ1 disj wt) x x₁ x₂
    weaken-ta-Δ1 disj (TAPair wt wt₁) = TAPair (weaken-ta-Δ1 disj wt) (weaken-ta-Δ1 disj wt₁)
    weaken-ta-Δ1 disj (TAFst wt) = TAFst (weaken-ta-Δ1 disj wt)
    weaken-ta-Δ1 disj (TASnd wt) = TASnd (weaken-ta-Δ1 disj wt)
    
  -- this is a little bit of a time saver. since ∪ is commutative on
  -- disjoint contexts, and we need that premise anyway in both positions,
  -- there's no real reason to repeat the inductive argument above
  weaken-ta-Δ2 : ∀{Δ1 Δ2 Γ d τ} →
                 Δ1 ## Δ2 →
                 Δ2 , Γ ⊢ d :: τ →
                 (Δ1 ∪ Δ2) , Γ ⊢ d :: τ
  weaken-ta-Δ2 {Δ1} {Δ2} {Γ} {d} {τ} disj D = tr (λ q → q , Γ ⊢ d :: τ) (∪comm Δ2 Δ1 (##-comm disj)) (weaken-ta-Δ1 (##-comm disj) D)


  -- note that these statements are somewhat stronger than usual. this is
  -- because we don't have implcit α-conversion. this reifies the
  -- often-silent on paper assumption that if you collide with a bound
  -- variable you can just α-convert it away and not worry.
  mutual
    weaken-synth : ∀{x Γ e τ τ'} →
                   freshh x e →
                   Γ ⊢ e => τ →
                   (Γ ,, (x , τ')) ⊢ e => τ
    weaken-synth FRHNum SNum = SNum
    weaken-synth (FRHPlus frsh frsh₁) (SPlus x x₁) = SPlus (weaken-ana frsh x) (weaken-ana frsh₁ x₁)
    weaken-synth (FRHAsc frsh) (SAsc x₁) = SAsc (weaken-ana frsh x₁)
    weaken-synth {Γ = Γ} (FRHVar {x = x} x₁) (SVar {x = y} x₂) = SVar (x∈∪r (■ (x , _)) Γ y _ x₂ (apart-singleton (flip x₁)))
    weaken-synth {Γ = Γ} (FRHLam2 x₁ frsh) (SLam x₂ wt) =
                    SLam (apart-extend1 Γ (flip x₁) x₂)
                         (exchange-synth {Γ = Γ} (flip x₁) ((weaken-synth frsh wt)))
    weaken-synth FRHEHole SEHole = SEHole
    weaken-synth (FRHNEHole frsh) (SNEHole wt) = SNEHole (weaken-synth frsh wt)
    weaken-synth (FRHAp frsh frsh₁) (SAp wt x₂ x₃) = SAp (weaken-synth frsh wt) x₂ (weaken-ana frsh₁ x₃)
    weaken-synth (FRHPair frsh frsh₁) (SPair wt wt₁) = SPair (weaken-synth frsh wt) (weaken-synth frsh₁ wt₁)
    weaken-synth (FRHFst frsh) (SFst wt x) = SFst (weaken-synth frsh wt) x
    weaken-synth (FRHSnd frsh) (SSnd wt x) = SSnd (weaken-synth frsh wt) x

    weaken-ana : ∀{x Γ e τ τ'} →
                 freshh x e →
                 Γ ⊢ e <= τ →
                 (Γ ,, (x , τ')) ⊢ e <= τ
    weaken-ana frsh (ASubsume x₁ x₂) = ASubsume (weaken-synth frsh x₁) x₂
    weaken-ana {Γ = Γ} (FRHLam1 neq frsh) (ALam x₂ x₃ wt) =
                     ALam (apart-extend1 Γ (flip neq) x₂)
                          x₃
                          (exchange-ana {Γ = Γ} (flip neq) (weaken-ana frsh wt))
    weaken-ana (FRHInl frsh) (AInl x x₁) = AInl x (weaken-ana frsh x₁)
    weaken-ana (FRHInr frsh) (AInr x x₁) = AInr x (weaken-ana frsh x₁)
    weaken-ana {Γ = Γ} (FRHCase frshd newx≠y frshd₁ newx≠z frshd₂)
                       (ACase {Γ = .Γ} y#Γ z#Γ msum syn ana₁ ana₂) =
               ACase (apart-extend1 Γ (flip newx≠y) y#Γ)
                     (apart-extend1 Γ (flip newx≠z) z#Γ)
                     msum
                     (weaken-synth {Γ = Γ} frshd syn)
                     (exchange-ana {Γ = Γ} (flip newx≠y) (weaken-ana frshd₁ ana₁))
                     (exchange-ana {Γ = Γ} (flip newx≠z) (weaken-ana frshd₂ ana₂))
    
  mutual
    weaken-subst-Γ : ∀{x Γ Δ σ Γ' τ} →
                     envfresh x σ →
                     Δ , Γ ⊢ σ :s: Γ' →
                     Δ , (Γ ,, (x , τ)) ⊢ σ :s: Γ'
    weaken-subst-Γ {Γ = Γ} {τ = τ₁} (EFId {x = x₃} x₁) (STAId {Γ' = Γ'} x₂) = STAId (λ x τ x∈Γ' → x∈∪r (■ (x₃ , τ₁)) Γ x τ (x₂ x τ x∈Γ') (apart-singleton λ{refl → somenotnone ((! x∈Γ') · x₁)}))
    weaken-subst-Γ {x = x} {Γ = Γ} (EFSubst x₁ efrsh x₂) (STASubst {y = y} {τ = τ'} subst x₃) =
      STASubst (exchange-subst-Γ {Γ = Γ} (flip x₂) (weaken-subst-Γ {Γ = Γ ,, (y , τ')} efrsh subst))
               (weaken-ta x₁ x₃)

    weaken-ta : ∀{x Γ Δ d τ τ'} →
                fresh x d →
                Δ , Γ ⊢ d :: τ →
                Δ , Γ ,, (x , τ') ⊢ d :: τ
    weaken-ta FNum TANum = TANum
    weaken-ta (FPlus x₁ x₂) (TAPlus x x₃) = TAPlus (weaken-ta x₁ x) (weaken-ta x₂ x₃)
    weaken-ta {x} {Γ} {_} {_} {τ} {τ'} (FVar x₂) (TAVar x₃) = TAVar (x∈∪r (■(x , _)) Γ _ _ x₃ (apart-singleton (flip x₂)))
    weaken-ta {x = x} frsh (TALam {x = y} x₂ wt) with natEQ x y
    weaken-ta (FLam x₁ x₂) (TALam x₃ wt) | Inl refl = abort (x₁ refl)
    weaken-ta {Γ = Γ} {τ' = τ'} (FLam x₁ x₃) (TALam {x = y} x₄ wt) | Inr x₂ = TALam (apart-extend1 Γ (flip x₁) x₄) (exchange-ta-Γ {Γ = Γ} (flip x₁) (weaken-ta x₃ wt))
    weaken-ta (FAp frsh frsh₁) (TAAp wt wt₁) = TAAp (weaken-ta frsh wt) (weaken-ta frsh₁ wt₁)
    weaken-ta (FHole x₁) (TAEHole x₂ x₃) = TAEHole x₂ (weaken-subst-Γ x₁ x₃)
    weaken-ta (FNEHole x₁ frsh) (TANEHole x₂ wt x₃) = TANEHole x₂ (weaken-ta frsh wt) (weaken-subst-Γ x₁ x₃)
    weaken-ta (FCast frsh) (TACast wt x₁) = TACast (weaken-ta frsh wt) x₁
    weaken-ta (FFailedCast frsh) (TAFailedCast wt x₁ x₂ x₃) = TAFailedCast (weaken-ta frsh wt) x₁ x₂ x₃
    weaken-ta (FInl frsh) (TAInl wt) = TAInl (weaken-ta frsh wt)
    weaken-ta (FInr frsh) (TAInr wt) = TAInr (weaken-ta frsh wt)
    weaken-ta {Γ = Γ} (FCase frsh x frsh₁ x₁ frsh₂) (TACase wt x₂ wt₁ x₃ wt₂) =
      TACase (weaken-ta frsh wt)
      (apart-extend1 Γ (flip x) x₂)
      (exchange-ta-Γ {Γ = Γ} (flip x) (weaken-ta frsh₁ wt₁))
      (apart-extend1 Γ (flip x₁) x₃)
      (exchange-ta-Γ {Γ = Γ} (flip x₁) (weaken-ta frsh₂ wt₂))
    weaken-ta (FPair frsh frsh₁) (TAPair wt wt₁) = TAPair (weaken-ta frsh wt) (weaken-ta frsh₁ wt₁)
    weaken-ta (FFst frsh) (TAFst wt) = TAFst (weaken-ta frsh wt)
    weaken-ta (FSnd frsh) (TASnd wt) = TASnd (weaken-ta frsh wt)
