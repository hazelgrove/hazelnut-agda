open import Prelude
open import core
open import contexts
open import lemmas-matching

module synth-unicity where
  -- synthesis only produces equal types. note that there is no need for an
  -- analagous theorem for analytic positions because we think of
  -- the type as an input
  synthunicity : {Γ : tctx} {e : hexp} {t t' : htyp} →
                 Γ ⊢ e => t →
                 Γ ⊢ e => t' →
                 t == t'
  synthunicity (SAsc _) (SAsc _) = refl
  synthunicity {Γ = G} (SVar in1) (SVar in2) = ctxunicity {Γ = G} in1 in2
  synthunicity (SAp  D1 MAHole _) (SAp D2 MAHole y) = refl
  synthunicity (SAp D1 MAHole _) (SAp D2 MAArr y) with synthunicity D1 D2
  ... | ()
  synthunicity (SAp D1 MAArr _) (SAp D2 MAHole y) with synthunicity D1 D2
  ... | ()
  synthunicity (SAp D1 MAArr _) (SAp D2 MAArr y) with synthunicity D1 D2
  ... | refl = refl
  synthunicity SEHole SEHole = refl
  synthunicity (SNEHole _) (SNEHole _) = refl
  synthunicity SNum SNum = refl
  synthunicity (SPlus _ _) (SPlus _ _) = refl
  synthunicity (SLam _ D1) (SLam _ D2) with synthunicity D1 D2
  synthunicity (SLam x₁ D1) (SLam x₂ D2) | refl = refl
  synthunicity (SPair D1 D2) (SPair D3 D4)
    with synthunicity D1 D3 | synthunicity D2 D4
  ... | refl | refl = refl
  synthunicity (SFst D1 x) (SFst D2 x₁) with synthunicity D1 D2
  ... | refl with ▸prod-unicity x x₁
  ... | refl = refl
  synthunicity (SSnd D1 x) (SSnd D2 x₁) with synthunicity D1 D2
  ... | refl with ▸prod-unicity x x₁
  ... | refl = refl
