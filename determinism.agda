open import Nat
open import Prelude
open import aasubsume-min
open import contexts
open import judgemental-erase
open import lemmas-matching
open import statics-core
open import synth-unicity

module determinism where
  -- since we do not specify the name of newly inserted hole names,
  -- we only have determinism up to renaming of holes. we don't
  -- need to consider alpha equivalence for binders, since the
  -- 
  -- the same action applied to the same type makes the same type
  actdet-type : {t t' t'' : ztyp} {α : action} →
                (t + α +> t') →
                (t + α +> t'') →
                (t' == t'')
  actdet-type TMArrChild1 TMArrChild1 = refl
  actdet-type TMArrChild2 TMArrChild2 = refl
  actdet-type TMArrParent1 TMArrParent1 = refl
  actdet-type TMArrParent1 (TMArrZip1 ())
  actdet-type TMArrParent2 TMArrParent2 = refl
  actdet-type TMArrParent2 (TMArrZip2 ())
  actdet-type TMDel TMDel = refl
  actdet-type TMConArrow TMConArrow = refl
  actdet-type TMConNum TMConNum = refl
  actdet-type (TMArrZip1 ()) TMArrParent1
  actdet-type (TMArrZip1 p1) (TMArrZip1 p2) with actdet-type p1 p2
  ... | refl = refl
  actdet-type (TMArrZip2 ()) TMArrParent2
  actdet-type (TMArrZip2 p1) (TMArrZip2 p2) with actdet-type p1 p2
  ... | refl = refl
  actdet-type TMPlusChild1 TMPlusChild1 = refl
  actdet-type TMPlusChild2 TMPlusChild2 = refl
  actdet-type TMPlusParent1 TMPlusParent1 = refl
  actdet-type (TMPlusZip1 ()) TMPlusParent1
  actdet-type TMPlusParent2 TMPlusParent2 = refl
  actdet-type (TMPlusZip2 ()) TMPlusParent2
  actdet-type TMConPlus TMConPlus = refl
  actdet-type TMPlusParent1 (TMPlusZip1 ())
  actdet-type (TMPlusZip1 x) (TMPlusZip1 y) with actdet-type x y
  ... | refl = refl
  actdet-type TMPlusParent2 (TMPlusZip2 ())
  actdet-type (TMPlusZip2 x) (TMPlusZip2 y) with actdet-type x y
  ... | refl = refl
  actdet-type TMProdChild1 TMProdChild1 = refl
  actdet-type TMProdChild2 TMProdChild2 = refl
  actdet-type TMProdParent1 TMProdParent1 = refl
  actdet-type TMProdParent1 (TMProdZip1 ())
  actdet-type TMProdParent2 TMProdParent2 = refl
  actdet-type TMProdParent2 (TMProdZip2 ())
  actdet-type TMConProd TMConProd = refl
  actdet-type (TMProdZip1 ()) TMProdParent1
  actdet-type (TMProdZip1 x) (TMProdZip1 y) with actdet-type x y
  ... | refl = refl
  actdet-type (TMProdZip2 ()) TMProdParent2
  actdet-type (TMProdZip2 x) (TMProdZip2 y) with actdet-type x y
  ... | refl = refl
  
  -- all expressions only move to one other expression
  movedet : {e e' e'' : zexp} {δ : direction} →
            (e + move δ +>e e') →
            (e + move δ +>e e'') →
            e' == e''
  movedet EMAscChild1 EMAscChild1 = refl
  movedet EMAscChild2 EMAscChild2 = refl
  movedet EMAscParent1 EMAscParent1 = refl
  movedet EMAscParent2 EMAscParent2 = refl
  movedet EMLamChild1 EMLamChild1 = refl
  movedet EMLamParent EMLamParent = refl
  movedet EMHalfLamChild1 EMHalfLamChild1 = refl
  movedet EMHalfLamChild2 EMHalfLamChild2 = refl
  movedet EMHalfLamParent1 EMHalfLamParent1 = refl
  movedet EMHalfLamParent2 EMHalfLamParent2 = refl
  movedet EMPlusChild1 EMPlusChild1 = refl
  movedet EMPlusChild2 EMPlusChild2 = refl
  movedet EMPlusParent1 EMPlusParent1 = refl
  movedet EMPlusParent2 EMPlusParent2 = refl
  movedet EMApChild1 EMApChild1 = refl
  movedet EMApChild2 EMApChild2 = refl
  movedet EMApParent1 EMApParent1 = refl
  movedet EMApParent2 EMApParent2 = refl
  movedet EMNEHoleChild1 EMNEHoleChild1 = refl
  movedet EMNEHoleParent EMNEHoleParent = refl
  movedet EMInlChild1 EMInlChild1 = refl
  movedet EMInlParent EMInlParent = refl
  movedet EMInrChild1 EMInrChild1 = refl
  movedet EMInrParent EMInrParent = refl
  movedet EMCaseParent1 EMCaseParent1 = refl
  movedet EMCaseParent2 EMCaseParent2 = refl
  movedet EMCaseParent3 EMCaseParent3 = refl
  movedet EMCaseChild1 EMCaseChild1 = refl
  movedet EMCaseChild2 EMCaseChild2 = refl
  movedet EMCaseChild3 EMCaseChild3 = refl
  movedet EMPairChild1 EMPairChild1 = refl
  movedet EMPairChild2 EMPairChild2 = refl
  movedet EMPairParent1 EMPairParent1 = refl
  movedet EMPairParent2 EMPairParent2 = refl
  movedet EMFstChild1 EMFstChild1 = refl
  movedet EMFstParent EMFstParent = refl
  movedet EMSndChild1 EMSndChild1 = refl
  movedet EMSndParent EMSndParent = refl
  
  -- non-movement lemmas; theses show up pervasively throughout and save a
  -- lot of pattern matching.
  lem-nomove-part : ∀ {t t'} → ▹ t ◃ + move parent +> t' → ⊥
  lem-nomove-part ()

  lem-nomove-pars : ∀{Γ e t e' t'} → Γ ⊢ ▹ e ◃ => t ~ move parent ~> e' => t' → ⊥
  lem-nomove-pars (SAMove ())

  lem-nomove-para : ∀{Γ e t e'} → Γ ⊢ ▹ e ◃ ~ move parent ~> e' ⇐ t → ⊥
  lem-nomove-para (AASubsume e x x₁ x₂) = lem-nomove-pars x₁
  lem-nomove-para (AAMove ())

  -- if a move action on a synthetic action makes a new form, it's unique
  synthmovedet : {Γ : tctx} {e e' e'' : zexp} {t' t'' : htyp} {δ : direction} →
                 Γ ⊢ e => t' ~ move δ ~> e'' => t'' →
                 e + move δ +>e e' →
                 e'' == e'
  synthmovedet (SAMove m1) m2 = movedet m1 m2
  -- all these cases lead to absurdities based on movement
  synthmovedet (SAZipAsc1 x) EMAscParent1 = abort (lem-nomove-para x)
  synthmovedet (SAZipAsc2 x _ _ _) EMAscParent2 = abort (lem-nomove-part x)
  synthmovedet (SAZipApArr _ _ _ x _) EMApParent1 = abort (lem-nomove-pars x)
  synthmovedet (SAZipApAna _ _ x) EMApParent2 = abort (lem-nomove-para x)
  synthmovedet (SAZipPlus1 x) EMPlusParent1 = abort (lem-nomove-para x)
  synthmovedet (SAZipPlus2 x) EMPlusParent2 = abort (lem-nomove-para x)
  synthmovedet (SAZipNEHole _ _ x) EMNEHoleParent = abort (lem-nomove-pars x)
  synthmovedet (SAZipPair1 _ _ x _) EMPairParent1 = abort (lem-nomove-pars x)
  synthmovedet (SAZipPair2 _ _ _ x) EMPairParent2 = abort (lem-nomove-pars x)
  synthmovedet (SAZipFst _ _ _ _ x) EMFstParent = abort (lem-nomove-pars x)
  synthmovedet (SAZipSnd _ _ _ _ x) EMSndParent = abort (lem-nomove-pars x)
  synthmovedet (SAZipLam1 _ _ _ x _ _) EMHalfLamParent1 = abort (lem-nomove-part x)
  synthmovedet (SAZipLam2 _ _ _ x) EMHalfLamParent2 = abort (lem-nomove-pars x)
  
  anamovedet : {Γ : tctx} {e e' e'' : zexp} {t : htyp} {δ : direction} →
               Γ ⊢ e ~ move δ ~> e'' ⇐ t →
               e + move δ +>e e' →
               e'' == e'
  anamovedet (AASubsume x₂ x x₃ x₁) m = synthmovedet x₃ m
  anamovedet (AAMove x) m = movedet x m
  anamovedet (AAZipLam x₁ x₂ d) EMLamParent = abort (lem-nomove-para d)
  anamovedet (AAZipInl x d) EMInlParent = abort (lem-nomove-para d)
  anamovedet (AAZipInr x d) EMInrParent = abort (lem-nomove-para d)
  anamovedet (AAZipCase1 x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈) EMCaseParent1 =
    abort (lem-nomove-pars x₅)
  anamovedet (AAZipCase2 x₁ x₂ x₃ x₄ d) EMCaseParent2 = abort (lem-nomove-para d)
  anamovedet (AAZipCase3 x₁ x₂ x₃ x₄ d) EMCaseParent3 = abort (lem-nomove-para d)

  lem-plusholematch : ∀ {t t1 t2} → t ~̸ (⦇-⦈ ⊕ ⦇-⦈) → t ~ ⦇-⦈ → t ▸sum (t1 ⊕ t2) → ⊥
  lem-plusholematch a TCRefl MSHole = a TCHole2
  lem-plusholematch a TCHole1 MSHole = a TCHole2
  lem-plusholematch a TCHole1 MSSum = a (TCSum TCHole1 TCHole1)
  lem-plusholematch a TCHole2 MSHole = a TCHole2

  lem-prodholematch : ∀ {t t1 t2} → t ~̸ (⦇-⦈ ⊠ ⦇-⦈) → t ~ ⦇-⦈ → t ▸prod (t1 ⊠ t2) → ⊥
  lem-prodholematch a TCRefl MPHole = a TCHole2
  lem-prodholematch a TCHole1 MPHole = a TCHole2
  lem-prodholematch a TCHole1 MPProd = a (TCProd TCHole1 TCHole1)
  lem-prodholematch a TCHole2 MPHole = a TCHole2
  
  mutual
    -- an action on an expression in a synthetic position produces one
    -- resultant expression and type.
    actdet-synth : {Γ : tctx} {e e' e'' : zexp} {e◆ : hexp} {t t' t'' : htyp} {α : action} →
                   (E : erase-e e e◆) →
                   (Γ ⊢ e◆ => t) →
                   (d1 : Γ ⊢ e => t ~ α ~> e'  => t') →
                   (d2 : Γ ⊢ e => t ~ α ~> e'' => t'') →
                   {p1 : aasubmin-synth d1} →
                   {p2 : aasubmin-synth d2} →
                   (e' == e'' × t' == t'')
    actdet-synth er wt (SAMove x₁) (SAMove x₂) = movedet x₁ x₂ , refl
    actdet-synth er wt SADel SADel = refl , refl
    actdet-synth er wt SAConAsc SAConAsc = refl , refl
    actdet-synth er wt (SAConPlus1 x₁) (SAConPlus1 x₂) = refl , refl
    actdet-synth er wt (SAConPlus1 x₁) (SAConPlus2 x₂) = abort (x₂ x₁)
    actdet-synth er wt (SAConPlus2 x₁) (SAConPlus1 x₂) = abort (x₁ x₂)
    actdet-synth er wt (SAConPlus2 x₁) (SAConPlus2 x₂) = refl , refl
    actdet-synth er wt (SAConApArr x₁) (SAConApArr x₂)
      with ▸arr-unicity x₁ x₂
    ... | refl = refl , refl
    actdet-synth er wt (SAConApArr x₁) (SAConApOtw x₂) = abort (x₂ (▸arr-consist-hole x₁))
    actdet-synth er wt (SAConApOtw x₁) (SAConApArr x₂) = abort (x₁ (▸arr-consist-hole x₂))
    actdet-synth er wt (SAConApOtw x₁) (SAConApOtw x₂) = refl , refl
    actdet-synth er wt SAConNEHole SAConNEHole = refl , refl
    
    actdet-synth (EEAscL E) (SAsc x) (SAMove EMAscParent1) (SAZipAsc1 x₂) =
      abort (lem-nomove-para x₂)
    actdet-synth (EEAscL E) (SAsc x) (SAZipAsc1 x₁) (SAMove EMAscParent1) =
      abort (lem-nomove-para x₁)
    actdet-synth (EEAscL E) (SAsc x) (SAZipAsc1 x₁) (SAZipAsc1 x₂) {p1} {p2}
     with actdet-ana E x x₁ x₂ {p1} {p2}
    ... | refl = refl , refl
   
    actdet-synth (EEAscR x) (SAsc x₁) (SAMove EMAscParent2) (SAZipAsc2 a _ _ _) =
      abort (lem-nomove-part a)
    actdet-synth (EEAscR x) (SAsc x₁) (SAZipAsc2 a _ _ _) (SAMove EMAscParent2) =
      abort (lem-nomove-part a)
    actdet-synth (EEAscR x) (SAsc x₂) (SAZipAsc2 a e1 _ _) (SAZipAsc2 b e2 _ _)
      with actdet-type a b
    ... | refl = refl , eraset-det e1 e2


    actdet-synth (EEHalfLamL x) (SLam x₁ wt) (SAMove EMHalfLamParent1)
                 (SAZipLam1 x₃ x₄ x₅ x₆ x₇ x₈) = abort (lem-nomove-part x₆)
    actdet-synth (EEHalfLamL x) (SLam x₁ wt) (SAZipLam1 x₂ x₃ x₄ x₅ x₆ x₇)
                 (SAMove EMHalfLamParent1) = abort (lem-nomove-part x₅)
    actdet-synth (EEHalfLamL x) (SLam x₁ wt) (SAZipLam1 x₂ x₃ x₄ x₅ x₆ x₇)
                 (SAZipLam1 x₈ x₉ x₁₀ x₁₁ x₁₂ x₁₃) with actdet-type x₅ x₁₁
    ... | refl with eraset-det x₄ x₁₀
    ... | refl with synthunicity x₇ x₁₃
    ... | refl = refl , refl

    actdet-synth (EEHalfLamR er) (SLam x wt) (SAMove EMHalfLamParent2)
                 (SAZipLam2 x₂ x₃ x₄ y) = abort (lem-nomove-pars y)
    actdet-synth (EEHalfLamR er) (SLam x wt) (SAZipLam2 x₁ x₂ x₃ x₄)
                 (SAMove EMHalfLamParent2) = abort (lem-nomove-pars x₄)
    actdet-synth (EEHalfLamR er) (SLam x wt) (SAZipLam2 x₁ x₂ x₃ d1)
                 (SAZipLam2 x₅ x₆ x₇ d2) {p1} {p2} with erasee-det x₂ x₆
    ... | refl with actdet-synth x₂ x₃ d1 d2 {p1} {p2}
    ... | refl , refl = refl , refl
    
    actdet-synth (EEApL E) (SAp m wt x) (SAMove EMApParent1) (SAZipApArr _ x₂ x₃ d2 x₄) =
      abort (lem-nomove-pars d2)
    actdet-synth (EEApL E) (SAp m wt x) (SAZipApArr _ x₁ x₂ d1 x₃) (SAMove EMApParent1) =
      abort (lem-nomove-pars d1)
    actdet-synth (EEApL E) (SAp m wt x) (SAZipApArr a x₁ x₂ d1 x₃)
                 (SAZipApArr b x₄ x₅ d2 x₆) {p1} {p2}
      with erasee-det x₁ x₄
    ... | refl with synthunicity x₂ x₅
    ... | refl with erasee-det E x₁
    ... | refl with actdet-synth E x₅ d1 d2 {p1} {p2}
    ... | refl , refl with ▸arr-unicity a b
    ... | refl = refl , refl

   
    actdet-synth (EEApR E) (SAp m wt x) (SAMove EMApParent2) (SAZipApAna x₂ x₃ x₄) =
      abort (lem-nomove-para x₄)
    actdet-synth (EEApR E) (SAp m wt x) (SAZipApAna x₁ x₂ x₃) (SAMove EMApParent2) =
      abort (lem-nomove-para x₃)
    actdet-synth (EEApR E) (SAp m wt x) (SAZipApAna x₁ x₂ d1) (SAZipApAna x₄ x₅ d2)  {p1} {p2}
     with synthunicity m x₂
    ... | refl with ▸arr-unicity x₁ wt
    ... | refl with synthunicity m x₅
    ... | refl with ▸arr-unicity x₄ wt
    ... | refl with actdet-ana E x d1 d2  {p1} {p2}
    ... | refl = refl , refl

   
    actdet-synth (EEPlusL E) (SPlus x x₁) (SAMove EMPlusParent1) (SAZipPlus1 d2) =
      abort (lem-nomove-para d2)
    actdet-synth (EEPlusL E) (SPlus x x₁) (SAZipPlus1 x₂) (SAMove EMPlusParent1) =
      abort (lem-nomove-para x₂)
    actdet-synth (EEPlusL E) (SPlus x x₁) (SAZipPlus1 x₂) (SAZipPlus1 x₃) {p1} {p2}
      = ap1 (λ x₄ → x₄ ·+₁ _) (actdet-ana E x x₂ x₃  {p1} {p2}) , refl

    actdet-synth (EEPlusR E) (SPlus x x₁) (SAMove EMPlusParent2) (SAZipPlus2 x₃) =
      abort (lem-nomove-para x₃)
    actdet-synth (EEPlusR E) (SPlus x x₁) (SAZipPlus2 x₂) (SAMove EMPlusParent2) =
      abort (lem-nomove-para x₂)
    actdet-synth (EEPlusR E) (SPlus x x₁) (SAZipPlus2 x₂) (SAZipPlus2 x₃) {p1} {p2}
      = ap1 (_·+₂_ _) (actdet-ana E x₁ x₂ x₃ {p1} {p2}) , refl

    
    actdet-synth EETop SEHole (SAConVar {Γ = G} p) (SAConVar p₁) =
      refl , (ctxunicity {Γ = G} p p₁)
    actdet-synth EETop SEHole (SAConLam x₁) (SAConLam x₂) = refl , refl
    actdet-synth EETop SEHole SAConNumlit SAConNumlit = refl , refl
    
    actdet-synth EETop (SNEHole wt) (SAFinish x) (SAFinish x₁) = refl , synthunicity x x₁

    actdet-synth (EENEHole E) (SNEHole wt) (SAMove EMNEHoleParent) (SAZipNEHole _ x₁ d2) =
      abort (lem-nomove-pars d2)
    actdet-synth (EENEHole E) (SNEHole wt) (SAZipNEHole _ x d1) (SAMove EMNEHoleParent) =
      abort (lem-nomove-pars d1)
    actdet-synth (EENEHole E) (SNEHole wt) (SAZipNEHole a x d1) (SAZipNEHole b x₁ d2) {p1} {p2}
      with erasee-det a b
    ... | refl with synthunicity x x₁
    ... | refl with actdet-synth a x d1 d2  {p1} {p2}
    ... | refl , refl = refl , refl

      -- new cases for sums
    actdet-synth EETop SEHole SAConInl SAConInl = refl , refl
    actdet-synth EETop SEHole SAConInr SAConInr = refl , refl
    actdet-synth er wt (SAConCase1 x₁ x₂ x₃) (SAConCase1 x₄ x₅ x₆) = refl , refl
    actdet-synth er wt (SAConCase1 x₁ x₂ MSHole) (SAConCase2 x₄ x₅ x₆) = abort (x₆ TCHole2)
    actdet-synth EETop wt (SAConCase1 x₁ x₂ MSSum) (SAConCase2 x₄ x₅ x₆) =
      abort (x₆ (TCSum TCHole1 TCHole1))
    actdet-synth EETop wt (SAConCase2 x₁ x₂ x₃) (SAConCase1 x₄ x₅ MSHole) = abort (x₃ TCHole2)
    actdet-synth EETop wt (SAConCase2 x₁ x₂ x₃) (SAConCase1 x₄ x₅ MSSum) =
      abort (x₃ (TCSum TCHole1 TCHole1))
    actdet-synth er wt (SAConCase2 x₁ x₂ x₃) (SAConCase2 x₄ x₅ x₆) = refl , refl
    
      -- new cases for products
    actdet-synth EETop wt (SAConFst1 x) (SAConFst1 x₁) with ▸prod-unicity x x₁
    ... | refl = refl , refl
    actdet-synth EETop wt (SAConFst1 x) (SAConFst2 x₁) = abort (x₁ (▸prod-consist-hole x))
    actdet-synth EETop wt (SAConFst2 x) (SAConFst1 x₁) = abort (x (▸prod-consist-hole x₁))
    actdet-synth EETop wt (SAConFst2 x) (SAConFst2 x₁) = refl , refl
    actdet-synth EETop wt (SAConSnd1 x) (SAConSnd1 x₁) with ▸prod-unicity x x₁
    ... | refl = refl , refl
    actdet-synth EETop wt (SAConSnd1 x) (SAConSnd2 x₁) = abort (x₁ (▸prod-consist-hole x))
    actdet-synth EETop wt (SAConSnd2 x) (SAConSnd1 x₁) = abort (x (▸prod-consist-hole x₁))
    actdet-synth EETop wt (SAConSnd2 x) (SAConSnd2 x₁) = refl , refl
    actdet-synth EETop SEHole SAConPair SAConPair = refl , refl
    actdet-synth (EEPairL er) (SPair wt wt₁) (SAMove EMPairParent1)
                 (SAZipPair1 er₁ wt₂ d wt₃) = abort (lem-nomove-pars d)
    actdet-synth (EEPairL er) (SPair wt wt₁) (SAZipPair1 er₁ wt₂ d wt₃)
                 (SAMove EMPairParent1) = abort (lem-nomove-pars d)
    actdet-synth (EEPairL er) (SPair wt wt₁) (SAZipPair1 er₁ wt₂ d₁ wt₃)
                 (SAZipPair1 er₂ wt₄ d₂ wt₅) {p1} {p2}
      with actdet-synth er₁ wt₂ d₁ d₂ {p1} {p2}
    ... | refl , refl = refl , refl
    actdet-synth (EEPairR er) (SPair wt wt₁) (SAMove EMPairParent2)
                 (SAZipPair2 wt₂ er₁ wt₃ d) = abort (lem-nomove-pars d)
    actdet-synth (EEPairR er) (SPair wt wt₁) (SAZipPair2 wt₂ er₁ wt₃ d)
                 (SAMove EMPairParent2) = abort (lem-nomove-pars d)
    actdet-synth (EEPairR er) (SPair wt wt₁) (SAZipPair2 wt₂ er₁ wt₃ d₁)
                 (SAZipPair2 wt₄ er₂ wt₅ d₂) {p1} {p2}
      with actdet-synth er₁ wt₃ d₁ d₂ {p1} {p2}
    ... | refl , refl = refl , refl
    actdet-synth (EEFst er) (SFst wt x₁) (SAMove EMFstParent)
                 (SAZipFst pr pr₁ er₁ wt₁ d) = abort (lem-nomove-pars d)
    actdet-synth (EEFst er) (SFst wt x₁) (SAZipFst pr pr₁ er₁ wt₁ d)
                 (SAMove EMFstParent) = abort (lem-nomove-pars d)
    actdet-synth (EEFst er) (SFst wt x₁) (SAZipFst pr pr₁ er₁ wt₁ d₁)
                 (SAZipFst pr₂ pr₃ er₂ wt₂ d₂) {p1} {p2}
      with erasee-det er₁ er₂
    ... | refl with synthunicity wt₁ wt₂
    ... | refl with actdet-synth er₁ wt₁ d₁ d₂ {p1} {p2}
    ... | refl , refl with ▸prod-unicity pr₁ pr₃
    ... | refl = refl , refl
    actdet-synth (EESnd er) (SSnd wt x₁) (SAMove EMSndParent) (SAZipSnd pr pr₁ er₁ wt₁ d) =
      abort (lem-nomove-pars d)
    actdet-synth (EESnd er) (SSnd wt x₁) (SAZipSnd pr pr₁ er₁ wt₁ d) (SAMove EMSndParent) =
      abort (lem-nomove-pars d)
    actdet-synth (EESnd er) (SSnd wt x₁) (SAZipSnd pr pr₁ er₁ wt₁ d₁)
                 (SAZipSnd pr₂ pr₃ er₂ wt₂ d₂) {p1} {p2}
      with erasee-det er₁ er₂
    ... | refl with synthunicity wt₁ wt₂
    ... | refl with actdet-synth er₁ wt₁ d₁ d₂ {p1} {p2}
    ... | refl , refl with ▸prod-unicity pr₁ pr₃
    ... | refl = refl , refl
    
    -- an action on an expression in an analytic position produces one
    -- resultant expression and type.
    actdet-ana : {Γ : tctx} {e e' e'' : zexp} {e◆ : hexp} {t : htyp} {α : action} →
                 erase-e e e◆ →
                 Γ ⊢ e◆ <= t →
                 (d1 : Γ ⊢ e ~ α ~> e' ⇐ t) →
                 (d2 : Γ ⊢ e ~ α ~> e'' ⇐ t) →
                 {p1 : aasubmin-ana d1} →
                 {p2 : aasubmin-ana d2} →
                 e' == e''
    -- lambda cases first
    -- an erased lambda can't be typechecked with subsume
    actdet-ana (EELam _) (ASubsume () _) _ _

    -- for things paired with movements, punt to the move determinism case
    actdet-ana _ _ D (AAMove y) = anamovedet D y
    actdet-ana _ _ (AAMove y) D =  ! (anamovedet D y)

    -- lambdas never match with subsumption actions, because it won't be well typed.
    actdet-ana EETop      (ALam x₁ x₂ wt) (AASubsume EETop () x₅ x₆) _
    actdet-ana (EELam _) (ALam x₁ x₂ wt) (AASubsume (EELam x₃) () x₅ x₆) _
    actdet-ana EETop      (ALam x₁ x₂ wt) _ (AASubsume EETop () x₅ x₆)
    actdet-ana (EELam _) (ALam x₁ x₂ wt) _ (AASubsume (EELam x₃) () x₅ x₆)

    -- with the cursor at the top, there are only two possible actions
    actdet-ana EETop (ALam x₁ x₂ wt) AADel AADel = refl
    actdet-ana EETop (ALam x₁ x₂ wt) AAConAsc AAConAsc = refl

    -- and for the remaining case, recurr on the smaller derivations
    actdet-ana (EELam er) (ALam x₁ x₂ wt) (AAZipLam x₃ x₄ d1) (AAZipLam x₅ x₆ d2) {p1} {p2}
       with ▸arr-unicity x₄ x₆
    ... | refl with ▸arr-unicity x₄ x₂
    ... | refl with actdet-ana er wt d1 d2  {p1} {p2}
    ... | refl = refl

    -- now the subsumption cases
    -- subsume / subsume, so pin things down then recurr
    actdet-ana er (ASubsume a b) (AASubsume x x₁ x₂ x₃) (AASubsume x₄ x₅ x₆ x₇) {p1} {p2}
      with erasee-det x₄ x
    ... | refl with erasee-det er x₄
    ... | refl with synthunicity x₅ x₁
    ... | refl = π1 (actdet-synth x x₅ x₂ x₆ {min-ana-lem x₂ p1} {min-ana-lem x₆ p2})

    -- (these are all repeated below, irritatingly.)
    actdet-ana EETop (ASubsume a b) (AASubsume EETop x SADel x₁) AADel = refl
    actdet-ana EETop (ASubsume a b) (AASubsume EETop x SAConAsc x₁) AAConAsc {p1} = abort p1
    actdet-ana EETop (ASubsume SEHole b) (AASubsume EETop SEHole (SAConVar {Γ = Γ} p) x₂)
               (AAConVar x₅ p₁)
      with ctxunicity {Γ = Γ} p p₁
    ... | refl = abort (x₅ x₂)
    actdet-ana EETop (ASubsume SEHole b) (AASubsume EETop SEHole (SAConLam x₄) x₂)
               (AAConLam1 x₅ m) {p1} = abort p1
    actdet-ana EETop (ASubsume a b) (AASubsume EETop x₁ (SAConLam x₃) x₂) (AAConLam2 x₅ x₆) =
      abort (x₆ x₂)
    actdet-ana EETop (ASubsume a b) (AASubsume EETop x₁ SAConNumlit x₂) (AAConNumlit x₄) =
      abort (x₄ x₂)
    actdet-ana EETop (ASubsume a b) (AASubsume EETop x (SAFinish x₂) x₁) (AAFinish x₄) = refl

    -- subsume / del
    actdet-ana er (ASubsume a b) AADel (AASubsume x x₁ SADel x₃) = refl
    actdet-ana er (ASubsume a b) AADel AADel = refl

    -- subsume / conasc
    actdet-ana EETop (ASubsume a b) AAConAsc (AASubsume EETop x₁ SAConAsc x₃) {p2 = p2} =
      abort p2
    actdet-ana er (ASubsume a b) AAConAsc AAConAsc = refl

    -- subsume / convar
    actdet-ana EETop (ASubsume SEHole b) (AAConVar x₁ p)
               (AASubsume EETop SEHole (SAConVar {Γ = Γ} p₁) x₅)
      with ctxunicity {Γ = Γ} p p₁
    ... | refl = abort (x₁ x₅)
    actdet-ana er (ASubsume a b) (AAConVar x₁ p) (AAConVar x₂ p₁) = refl

    -- subsume / conlam1
    actdet-ana EETop (ASubsume SEHole b) (AAConLam1 x₁ x₂)
               (AASubsume EETop SEHole (SAConLam x₃) x₆) {p2 = p2} = abort p2
    actdet-ana er (ASubsume a b) (AAConLam1 x₁ MAHole) (AAConLam2 x₃ x₄) =
      abort (x₄ TCHole2)
    actdet-ana er (ASubsume a b) (AAConLam1 x₁ MAArr) (AAConLam2 x₃ x₄) =
      abort (x₄ (TCArr TCHole1 TCHole1))
    actdet-ana er (ASubsume a b) (AAConLam1 x₁ x₂) (AAConLam1 x₃ x₄) = refl

    -- subsume / conlam2
    actdet-ana EETop (ASubsume SEHole TCRefl) (AAConLam2 x₁ x₂)
               (AASubsume EETop SEHole x₅ x₆) = abort (x₂ TCHole2)
    actdet-ana EETop (ASubsume SEHole TCHole1) (AAConLam2 x₁ x₂)
               (AASubsume EETop SEHole (SAConLam x₃) x₆) = abort (x₂ x₆)
    actdet-ana EETop (ASubsume SEHole TCHole2) (AAConLam2 x₁ x₂)
               (AASubsume EETop SEHole x₅ x₆) = abort (x₂ TCHole2)
    actdet-ana EETop (ASubsume a b) (AAConLam2 x₂ x₁) (AAConLam1 x₃ MAHole) = abort (x₁ TCHole2)
    actdet-ana EETop (ASubsume a b) (AAConLam2 x₂ x₁) (AAConLam1 x₃ MAArr) =
      abort (x₁ (TCArr TCHole1 TCHole1))
    actdet-ana er (ASubsume a b) (AAConLam2 x₂ x) (AAConLam2 x₃ x₄) = refl

    -- subsume / numlit
    actdet-ana er (ASubsume a b) (AAConNumlit x) (AASubsume x₁ x₂ SAConNumlit x₄) = abort (x x₄)
    actdet-ana er (ASubsume a b) (AAConNumlit x) (AAConNumlit x₁) = refl

    -- subsume / finish
    actdet-ana er (ASubsume a b) (AAFinish x) (AASubsume x₁ x₂ (SAFinish x₃) x₄) = refl
    actdet-ana er (ASubsume a b) (AAFinish x) (AAFinish x₁) = refl

    -- new cases for sums

    -- injections and cases, like lambdas, only check. so they can't be
    -- part of a subsume or a subsume action. so a lot of these cases
    -- just fall out immediately.
    actdet-ana (EEInl _) (ASubsume () _) _ _
    actdet-ana (EEInr _) (ASubsume () _) _ _
    actdet-ana (EECase1 _) (ASubsume () _) _ _
    actdet-ana (EECase2 _) (ASubsume () _) _ _
    actdet-ana (EECase3 _) (ASubsume () _) _ _

    actdet-ana EETop (AInl x wt) (AASubsume EETop () _ x₄) _
    actdet-ana EETop (AInl x wt) _ (AASubsume EETop () _ x₄)
    actdet-ana EETop (AInr x wt) (AASubsume EETop () _ x₄) _
    actdet-ana EETop (AInr x wt) _ (AASubsume EETop () _ x₄)
    actdet-ana EETop (ACase _ _ _ _ _ _) _ (AASubsume EETop () _ x₄)
    actdet-ana EETop (ACase _ _ _ _ _ _) (AASubsume EETop () _ x₄) _

    actdet-ana (EEInr er) (AInr x wt) (AASubsume (EEInr x₁) () x₃ x₄) _
    actdet-ana (EEInr er) (AInr x wt) _ (AASubsume (EEInr x₁) () x₃ x₄)
    actdet-ana (EEInl er) (AInl x wt) (AASubsume (EEInl x₁) () x₃ x₄) _
    actdet-ana (EEInl er) (AInl x wt) _ (AASubsume (EEInl x₁) () x₃ x₄)

    actdet-ana (EECase1 er) (ACase x₁ x₂ x₃ x₄ wt wt₁) _ (AASubsume (EECase1 x₉) () x₁₁ x₁₂)
    actdet-ana (EECase2 er) (ACase x₁ x₂ x₃ x₄ wt wt₁) _ (AASubsume (EECase2 x₉) () x₁₁ x₁₂)
    actdet-ana (EECase3 er) (ACase x₁ x₂ x₃ x₄ wt wt₁) _ (AASubsume (EECase3 x₉) () x₁₁ x₁₂)

    actdet-ana (EECase1 er) (ACase x₁ x₂ x₃ x₄ wt wt₁) (AASubsume (EECase1 x₉) () x₁₁ x₁₂) _
    actdet-ana (EECase2 er) (ACase x₁ x₂ x₃ x₄ wt wt₁) (AASubsume (EECase2 x₉) () x₁₁ x₁₂) _
    actdet-ana (EECase3 er) (ACase x₁ x₂ x₃ x₄ wt wt₁) (AASubsume (EECase3 x₉) () x₁₁ x₁₂) _

    actdet-ana EETop (ASubsume SEHole x₂) (AAConCase x₃ x₄)
               (AASubsume EETop SEHole (SAConCase1 x₁ x₅ MSHole) x₈) {p2 = p2} = abort p2
    actdet-ana EETop (ASubsume SEHole x₂) (AAConCase x₃ x₄)
               (AASubsume EETop SEHole (SAConCase2 x₁ x₅ x₆) x₈) = abort (x₆ TCHole2)
    actdet-ana EETop (ASubsume SEHole x₂) (AASubsume EETop SEHole (SAConCase1 x₁ x₃ MSHole) x₆)
               (AAConCase x₇ x₈) {p1} = abort p1
    actdet-ana EETop (ASubsume SEHole x₂) (AASubsume EETop SEHole (SAConCase2 x₁ x₃ x₄) x₆)
               (AAConCase x₇ x₈) = abort (x₄ TCHole2)

      -- the cases where the derivations match just go through
    actdet-ana er (ASubsume x x₁) (AAConInl1 x₂) (AAConInl1 x₃) = refl
    actdet-ana EETop (ASubsume SEHole x₁) (AAConInl2 x₂) (AAConInl2 x₃) = refl
    actdet-ana er (ASubsume x x₁) (AAConInr1 x₂) (AAConInr1 x₃) = refl
    actdet-ana er (ASubsume x x₁) (AAConInr2 x₂) (AAConInr2 x₃) = refl
    actdet-ana EETop (ASubsume SEHole x₂) (AAConCase x₃ x₄) (AAConCase x₅ x₆) = refl
    actdet-ana er (AInl x wt) AADel AADel = refl
    actdet-ana er (AInl x wt) AAConAsc AAConAsc = refl
    actdet-ana er (AInr x wt) AADel AADel = refl
    actdet-ana er (AInr x wt) AAConAsc AAConAsc = refl
    actdet-ana er (ACase x₁ x₂ x₃ x₄ wt wt₁) AADel AADel = refl
    actdet-ana er (ACase x₁ x₂ x₃ x₄ wt wt₁) AAConAsc AAConAsc = refl

    -- everything else we need to argue a little bit more carefully

    -- matching zipper cases; these cause us to recurr
    actdet-ana (EEInl er) (AInl x wt) (AAZipInl x₁ d1) (AAZipInl x₂ d2) {p1} {p2}
       with ▸sum-unicity x₂ x₁
    ... | refl with ▸sum-unicity x x₁
    ... | refl = ap1 inl (actdet-ana er wt d1 d2  {p1} {p2})

    actdet-ana (EEInr er) (AInr x wt) (AAZipInr x₁ d1) (AAZipInr x₂ d2) {p1} {p2}
       with ▸sum-unicity x₂ x₁
    ... | refl with ▸sum-unicity x x₁
    ... | refl = ap1 inr (actdet-ana er wt d1 d2  {p1} {p2})

    actdet-ana (EECase1 er) (ACase x₂ x₃ x₄ x₅ wt wt₁) (AAZipCase1 x₆ x₇ x₈ x₉ x₁₀ x₁₁ x₁₂ x₁₃)
               (AAZipCase1 x₁₄ x₁₅ x₁₆ x₁₇ x₁₈ x₁₉ x₂₀ x₂₁) {p1} {p2}
       with erasee-det x₈ x₁₆
    ... | refl with synthunicity x₁₇ x₉
    ... | refl with actdet-synth x₈ x₉ x₁₈ x₁₀ {p2} {p1}
    ... | refl , refl = refl

    actdet-ana (EECase2 er) (ACase x₂ x₃ x₄ x₅ wt wt₁) (AAZipCase2 x₆ x₇ x₈ x₉ d1)
               (AAZipCase2 x₁₁ x₁₂ x₁₃ x₁₄ d2) {p1} {p2}
       with synthunicity x₅ x₈
    ... | refl with synthunicity x₅ x₁₃
    ... | refl with ▸sum-unicity x₁₄ x₉
    ... | refl with ▸sum-unicity x₉ x₄
    ... | refl with actdet-ana er wt d1 d2 {p1} {p2}
    ... | refl = refl

    actdet-ana (EECase3 er) (ACase x₂ x₃ x₄ x₅ wt wt₁) (AAZipCase3 x₆ x₇ x₈ x₉ d1)
               (AAZipCase3 x₁₁ x₁₂ x₁₃ x₁₄ d2) {p1} {p2}
      with synthunicity x₈ x₁₃
    ... | refl with synthunicity x₈ x₅
    ... | refl with ▸sum-unicity x₄ x₉
    ... | refl with ▸sum-unicity x₄ x₁₄
    ... | refl with actdet-ana er wt₁ d1 d2 {p1} {p2}
    ... | refl = refl

    actdet-ana EETop (ASubsume SEHole x₁) (AASubsume EETop SEHole SAConInl x₅)
               (AAConInl1 x₆) {p1} = abort p1
    actdet-ana EETop (ASubsume SEHole x₁) (AASubsume EETop SEHole SAConInl x₅)
               (AAConInl2 x₆) = abort (x₆ x₅)
    actdet-ana EETop (ASubsume SEHole x₁) (AASubsume EETop SEHole SAConInr x₅)
               (AAConInr1 x₆) {p1} = abort p1
    actdet-ana EETop (ASubsume SEHole x₁) (AASubsume EETop SEHole SAConInr x₅)
               (AAConInr2 x₆) = abort (x₆ x₅)
    actdet-ana EETop (ASubsume SEHole x₁) (AAConInl1 x₂)
               (AASubsume EETop SEHole SAConInl x₆) {p2 = p2} = abort p2
    actdet-ana EETop (ASubsume SEHole x₁) (AAConInr1 x₂)
               (AASubsume EETop SEHole SAConInr c) {p2 = p2} = abort p2

    actdet-ana EETop (ASubsume SEHole x₁) (AAConInl1 q) (AAConInl2 x₃) =
      abort (lem-plusholematch x₃ x₁ q)
    actdet-ana EETop (ASubsume SEHole x₁) (AAConInl2 x₂) (AASubsume EETop SEHole SAConInl x₆) =
      abort (x₂ x₆)
    actdet-ana EETop (ASubsume SEHole x₁) (AAConInl2 x₂) (AAConInl1 q) =
      abort (lem-plusholematch x₂ x₁ q)
    actdet-ana EETop (ASubsume SEHole x₁) (AAConInr1 x₂) (AAConInr2 x₃) =
      abort (lem-plusholematch x₃ x₁ x₂)
    actdet-ana EETop (ASubsume SEHole x₁) (AAConInr2 x₂) (AASubsume EETop x₄ SAConInr x₆) =
      abort (x₂ x₆)
    actdet-ana EETop (ASubsume SEHole x₁) (AAConInr2 x₂) (AAConInr1 x₃) =
      abort (lem-plusholematch x₂ x₁ x₃)
