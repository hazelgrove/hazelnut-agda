open import Prelude
open import Nat
open import dynamics-core
open import contexts
open import lemmas-disjointness

module lemmas-freshness where
  -- if x is fresh in an hexp, it's fresh in its expansion
  mutual
    fresh-elab-synth1 : ∀{x e τ d Γ Δ} →
                         x # Γ →
                         freshh x e →
                         Γ ⊢ e ⇒ τ ~> d ⊣ Δ →
                         fresh x d
    fresh-elab-synth1 apt FHNum ESNum = FNum
    fresh-elab-synth1 apt (FRHPlus x x₄) (ESPlus gapt x₁ x₂ x₃) =
                          FPlus (FCast (fresh-elab-ana1 apt x x₂))
                                (FCast (fresh-elab-ana1 apt x₄ x₃))
    fresh-elab-synth1 apt (FRHAsc frsh) (ESAsc x₁) = FCast (fresh-elab-ana1 apt frsh x₁)
    fresh-elab-synth1 _ (FRHVar x₂) (ESVar x₃) = FVar x₂
    fresh-elab-synth1 {Γ = Γ} apt (FRHLam2 x₂ frsh) (ESLam x₃ exp) = FLam x₂ (fresh-elab-synth1 (apart-extend1 Γ x₂ apt) frsh exp)
    fresh-elab-synth1 apt (FRHAp frsh frsh₁) (ESAp x₁ x₂ x₃ x₄ x₅ x₆) = FAp (FCast (fresh-elab-ana1 apt frsh x₅)) (FCast (fresh-elab-ana1 apt frsh₁ x₆))
    fresh-elab-synth1 apt (FRHPair frsh frsh₁) (ESPair x x₁ x₂ x₃) = FPair (fresh-elab-synth1 apt frsh x₂) (fresh-elab-synth1 apt frsh₁ x₃)
    fresh-elab-synth1 apt (FRHFst frsh) (ESFst x x₁ x₂) = FFst (FCast (fresh-elab-ana1 apt frsh x₂))
    fresh-elab-synth1 apt (FRHSnd frsh) (ESSnd x x₁ x₂) = FSnd (FCast (fresh-elab-ana1 apt frsh x₂))
    fresh-elab-synth1 apt FRHEHole ESEHole = FHole (EFId apt)
    fresh-elab-synth1 apt (FRHNEHole frsh) (ESNEHole x₁ exp) = FNEHole (EFId apt) (fresh-elab-synth1 apt frsh exp)
    
    fresh-elab-ana1 : ∀{x e τ d τ' Γ Δ} →
                      x # Γ →
                      freshh x e →
                      Γ ⊢ e ⇐ τ ~> d :: τ' ⊣ Δ →
                      fresh x d
    fresh-elab-ana1 {Γ = Γ}  apt (FRHLam1 x₁ frsh) (EALam x₂ x₃ exp) = FLam x₁ (fresh-elab-ana1 (apart-extend1 Γ x₁ apt) frsh exp )
    fresh-elab-ana1 apt frsh (EASubsume x₁ x₂ x₃ x₄) = fresh-elab-synth1 apt frsh x₃
    fresh-elab-ana1 apt (FRHInl frsh) (EAInl x x₁) = FInl (fresh-elab-ana1 apt frsh x₁)
    fresh-elab-ana1 apt (FRHInr frsh) (EAInr x x₁) = FInr (fresh-elab-ana1 apt frsh x₁)
    fresh-elab-ana1 {Γ = Γ} apt (FRHCase frsh x₁ frsh₁ x₂ frsh₂) (EACase x x₃ x₄ x₅ x₆ x₇ x₈ x₉ x₁₀ x₁₁ x₁₂ x₁₃) = FCase (FCast (fresh-elab-synth1 apt frsh x₁₀)) x₁ (FCast (fresh-elab-ana1 (apart-extend1 Γ x₁ apt) frsh₁ x₁₂)) x₂ (FCast (fresh-elab-ana1 (apart-extend1 Γ x₂ apt) frsh₂ x₁₃))
    fresh-elab-ana1 apt FRHEHole EAEHole = FHole (EFId apt)
    fresh-elab-ana1 apt (FRHNEHole frsh) (EANEHole x₁ x₂) = FNEHole (EFId apt) (fresh-elab-synth1 apt frsh x₂)
    
  -- if x is fresh in the expansion of an hexp, it's fresh in that hexp
  mutual
    fresh-elab-synth2 : ∀{x e τ d Γ Δ} →
                         fresh x d →
                         Γ ⊢ e ⇒ τ ~> d ⊣ Δ →
                         freshh x e
    fresh-elab-synth2 FNum ESNum = FRHNum
    fresh-elab-synth2 (FPlus (FCast x) (FCast x₄)) (ESPlus apt x₁ x₂ x₃) =
      FRHPlus (fresh-elab-ana2 x x₂) (fresh-elab-ana2 x₄ x₃)
    fresh-elab-synth2 (FVar x₂) (ESVar x₃) = FRHVar x₂
    fresh-elab-synth2 (FLam x₂ frsh) (ESLam x₃ exp) = FRHLam2 x₂ (fresh-elab-synth2 frsh exp)
    fresh-elab-synth2 (FAp (FCast frsh) (FCast frsh₁)) (ESAp x₁ x₂ x₃ x₄ x₅ x₆) = FRHAp (fresh-elab-ana2 frsh x₅) (fresh-elab-ana2 frsh₁ x₆)
    fresh-elab-synth2 (FPair frsh frsh₁) (ESPair x x₁ x₂ x₃) = FRHPair (fresh-elab-synth2 frsh x₂) (fresh-elab-synth2 frsh₁ x₃)
    fresh-elab-synth2 (FFst (FCast frsh)) (ESFst x x₁ x₂) = FRHFst (fresh-elab-ana2 frsh x₂)
    fresh-elab-synth2 (FSnd (FCast frsh)) (ESSnd x x₁ x₂) = FRHSnd (fresh-elab-ana2 frsh x₂)
    fresh-elab-synth2 (FHole x₁) ESEHole = FRHEHole
    fresh-elab-synth2 (FNEHole x₁ frsh) (ESNEHole x₂ exp) = FRHNEHole (fresh-elab-synth2 frsh exp)
    fresh-elab-synth2 (FCast frsh) (ESAsc x₁) = FRHAsc (fresh-elab-ana2 frsh x₁)
    
    fresh-elab-ana2 : ∀{ x e τ d τ' Γ Δ} →
                      fresh x d →
                      Γ ⊢ e ⇐ τ ~> d :: τ' ⊣ Δ →
                      freshh x e
    fresh-elab-ana2 (FLam x₁ frsh) (EALam x₂ x₃ exp) = FRHLam1 x₁ (fresh-elab-ana2 frsh exp)
    fresh-elab-ana2 frsh (EASubsume x₁ x₂ x₃ x₄) = fresh-elab-synth2 frsh x₃
    fresh-elab-ana2 (FHole x₁) EAEHole = FRHEHole
    fresh-elab-ana2 (FNEHole x₁ frsh) (EANEHole x₂ x₃) = FRHNEHole (fresh-elab-synth2 frsh x₃)
    fresh-elab-ana2 (FInl frsh) (EAInl x x₁) = FRHInl (fresh-elab-ana2 frsh x₁)
    fresh-elab-ana2 (FInr frsh) (EAInr x x₁) = FRHInr (fresh-elab-ana2 frsh x₁)
    fresh-elab-ana2 (FCase (FCast frsh) x (FCast frsh₁) x₁ (FCast frsh₂)) (EACase x₂ x₃ x₄ x₅ x₆ x₇ x₈ x₉ x₁₀ x₁₁ x₁₂ x₁₃) = FRHCase (fresh-elab-synth2 frsh x₁₀) x (fresh-elab-ana2 frsh₁ x₁₂) x₁ (fresh-elab-ana2 frsh₂ x₁₃)
