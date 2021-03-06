open import Nat
open import Prelude
open import dynamics-core
open import contexts
open import lemmas-consistency
open import type-assignment-unicity
open import lemmas-progress-checks

-- taken together, the theorems in this file argue that for any expression
-- d, at most one summand of the labeled sum that results from progress may
-- be true at any time: that boxed values, indeterminates, and expressions
-- that step are pairwise disjoint.
--
-- note that as a consequence of currying and comutativity of products,
-- this means that there are three theorems to prove. in addition to those,
-- we also prove several convenince forms that combine theorems about
-- indeterminate and boxed value forms into the same statement about final
-- forms, which mirrors the mutual definition of indeterminate and final
-- and saves some redundant argumentation.
module progress-checks where
  -- boxed values are not indeterminates
  boxedval-not-indet : ∀{d} → d boxedval → d indet → ⊥
  boxedval-not-indet (BVVal VNum) ()
  boxedval-not-indet (BVVal VLam) ()
  boxedval-not-indet (BVArrCast x bv) (ICastArr x₁ ind) = boxedval-not-indet bv ind
  boxedval-not-indet (BVHoleCast x bv) (ICastGroundHole x₁ ind) = boxedval-not-indet bv ind
  boxedval-not-indet (BVHoleCast x bv) (ICastHoleGround x₁ ind x₂) = boxedval-not-indet bv ind
  boxedval-not-indet (BVVal (VInl x)) (IInl ind) = boxedval-not-indet (BVVal x) ind
  boxedval-not-indet (BVVal (VInr x)) (IInr ind) = boxedval-not-indet (BVVal x) ind
  boxedval-not-indet (BVInl bv) (IInl ind) = boxedval-not-indet bv ind
  boxedval-not-indet (BVInr bv) (IInr ind) = boxedval-not-indet bv ind
  boxedval-not-indet (BVSumCast x bv) (ICastSum x₁ ind) = boxedval-not-indet bv ind
  boxedval-not-indet (BVVal (VPair x x₂)) (IPair1 ind x₁) = boxedval-not-indet (BVVal x) ind
  boxedval-not-indet (BVVal (VPair x x₂)) (IPair2 x₁ ind) = boxedval-not-indet (BVVal x₂) ind
  boxedval-not-indet (BVPair bv bv₁) (IPair1 ind x) = boxedval-not-indet bv ind
  boxedval-not-indet (BVPair bv bv₁) (IPair2 x ind) = boxedval-not-indet bv₁ ind
  boxedval-not-indet (BVProdCast x bv) (ICastProd x₁ ind) = boxedval-not-indet bv ind
  
  -- boxed values don't step
  boxedval-not-step : ∀{d} → d boxedval → (Σ[ d' ∈ ihexp ] (d ↦ d')) → ⊥
  boxedval-not-step (BVVal VNum) (d' , Step FHOuter () x₃)
  boxedval-not-step (BVVal VLam) (d' , Step FHOuter () x₃)
  boxedval-not-step (BVArrCast x bv) (d0' , Step FHOuter (ITCastID) FHOuter) = x refl
  boxedval-not-step (BVArrCast x bv) (_ , Step (FHCast x₁) x₂ (FHCast x₃)) = boxedval-not-step bv (_ , Step x₁ x₂ x₃)
  boxedval-not-step (BVHoleCast () bv) (d' , Step FHOuter (ITCastID) FHOuter)
  boxedval-not-step (BVHoleCast x bv) (d' , Step FHOuter (ITCastSucceed ()) FHOuter)
  boxedval-not-step (BVHoleCast GArrHole bv) (_ , Step FHOuter (ITGround (MGArr x)) FHOuter) = x refl
  boxedval-not-step (BVHoleCast x bv) (_ , Step (FHCast x₁) x₂ (FHCast x₃)) = boxedval-not-step bv (_ , Step x₁ x₂ x₃)
  boxedval-not-step (BVHoleCast x x₁) (_ , Step FHOuter (ITExpand ()) FHOuter)
  boxedval-not-step (BVHoleCast x x₁) (_ , Step FHOuter (ITCastFail x₂ () x₄) FHOuter)
  boxedval-not-step (BVVal (VInl x)) (_ , Step FHOuter () x₃)
  boxedval-not-step (BVVal (VInr x)) (_ , Step FHOuter () x₃)
  boxedval-not-step (BVInl bv) (_ , Step FHOuter () x₂)
  boxedval-not-step (BVInr bv) (_ , Step FHOuter () x₂)
  boxedval-not-step (BVSumCast x bv) (_ , Step FHOuter ITCastID FHOuter) = x refl
  boxedval-not-step (BVSumCast x bv) (_ , Step (FHCast x₁) x₂ (FHCast x₃)) = boxedval-not-step bv (_ , Step x₁ x₂ x₃)
  boxedval-not-step (BVHoleCast GNum bv) (_ , Step FHOuter (ITGround ()) FHOuter)
  boxedval-not-step (BVHoleCast GSumHole bv) (_ , Step FHOuter (ITGround (MGSum x)) FHOuter) = x refl
  boxedval-not-step (BVVal (VInl x)) (_ , Step (FHInl x₁) x₂ (FHInl x₃)) = boxedval-not-step (BVVal x) (_ , Step x₁ x₂ x₃)
  boxedval-not-step (BVVal (VInr x)) (_ , Step (FHInr x₁) x₂ (FHInr x₃)) = boxedval-not-step (BVVal x) (_ , Step x₁ x₂ x₃)
  boxedval-not-step (BVInl bv) (_ , Step (FHInl x) x₁ (FHInl x₂)) = boxedval-not-step bv (_ , Step x x₁ x₂)
  boxedval-not-step (BVInr bv) (_ , Step (FHInr x) x₁ (FHInr x₂)) = boxedval-not-step bv (_ , Step x x₁ x₂)
  boxedval-not-step (BVVal (VPair x x₁)) (_ , Step (FHPair1 x₂) x₃ (FHPair1 x₄)) = boxedval-not-step (BVVal x) (_ , Step x₂ x₃ x₄)
  boxedval-not-step (BVVal (VPair x x₁)) (_ , Step (FHPair2 x₂) x₃ (FHPair2 x₄)) = boxedval-not-step (BVVal x₁) (_ , (Step x₂ x₃ x₄))
  boxedval-not-step (BVPair bv bv₁) (_ , Step (FHPair1 x) x₁ (FHPair1 x₂)) = boxedval-not-step bv (_ , Step x x₁ x₂)
  boxedval-not-step (BVPair bv bv₁) (_ , Step (FHPair2 x) x₁ (FHPair2 x₂)) = boxedval-not-step bv₁ (_ , Step x x₁ x₂)
  boxedval-not-step (BVProdCast x bv) (_ , Step FHOuter ITCastID FHOuter) = x refl
  boxedval-not-step (BVProdCast x bv) (_ , Step (FHCast x₁) x₂ (FHCast x₃)) = boxedval-not-step bv (_ , Step x₁ x₂ x₃)
  boxedval-not-step (BVHoleCast GProdHole bv) (_ , Step FHOuter (ITGround (MGProd x)) FHOut\er) = x refl
  
  mutual
    -- indeterminates don't step
    indet-not-step : ∀{d} → d indet → (Σ[ d' ∈ ihexp ] (d ↦ d')) → ⊥
    indet-not-step IEHole (d' , Step FHOuter () FHOuter)
    indet-not-step (INEHole x) (d' , Step FHOuter () FHOuter)
    indet-not-step (INEHole x) (_ , Step (FHNEHole x₁) x₂ (FHNEHole x₃)) = final-sub-not-trans x x₁ x₂
    indet-not-step (IAp x₁ () x₂) (_ , Step FHOuter (ITLam) FHOuter)
    indet-not-step (IAp x (ICastArr x₁ ind) x₂) (_ , Step FHOuter (ITApCast) FHOuter) = x _ _ _ _ _  refl
    indet-not-step (IAp x ind _) (_ , Step (FHAp1 x₂) x₃ (FHAp1 x₄)) = indet-not-step ind (_ , Step x₂ x₃ x₄)
    indet-not-step (IAp x ind f) (_ , Step (FHAp2 x₃) x₄ (FHAp2 x₆)) = final-not-step f (_ , Step x₃ x₄ x₆)
    indet-not-step (ICastArr x ind) (d0' , Step FHOuter (ITCastID) FHOuter) = x refl
    indet-not-step (ICastArr x ind) (_ , Step (FHCast x₁) x₂ (FHCast x₃)) = indet-not-step ind (_ , Step x₁ x₂ x₃)
    indet-not-step (ICastGroundHole () ind) (d' , Step FHOuter (ITCastID) FHOuter)
    indet-not-step (ICastGroundHole x ind) (d' , Step FHOuter (ITCastSucceed ()) FHOuter)
    indet-not-step (ICastGroundHole GArrHole ind) (_ , Step FHOuter (ITGround (MGArr x₁)) FHOuter) = x₁ refl
    indet-not-step (ICastGroundHole x ind) (_ , Step (FHCast x₁) x₂ (FHCast x₃)) = indet-not-step ind (_ , Step x₁ x₂ x₃)
    indet-not-step (ICastHoleGround x ind ()) (d' , Step FHOuter (ITCastID ) FHOuter)
    indet-not-step (ICastHoleGround x ind g) (d' , Step FHOuter (ITCastSucceed  x₂) FHOuter) = x _ _ refl
    indet-not-step (ICastHoleGround x ind GArrHole) (_ , Step FHOuter (ITExpand (MGArr x₂)) FHOuter) = x₂ refl
    indet-not-step (ICastHoleGround x ind g) (_ , Step (FHCast x₁) x₂ (FHCast x₃)) = indet-not-step ind (_ , Step x₁ x₂ x₃)
    indet-not-step (ICastGroundHole x x₁) (_ , Step FHOuter (ITExpand ()) FHOuter)
    indet-not-step (ICastHoleGround x x₁ x₂) (_ , Step FHOuter (ITGround ()) FHOuter)
    indet-not-step (ICastGroundHole x x₁) (_ , Step FHOuter (ITCastFail x₂ () x₄) FHOuter)
    indet-not-step (ICastHoleGround x x₁ x₂) (_ , Step FHOuter (ITCastFail x₃ x₄ x₅) FHOuter) = x _ _ refl
    indet-not-step (IFailedCast x x₁ x₂ x₃) (d' , Step FHOuter () FHOuter)
    indet-not-step (IFailedCast x x₁ x₂ x₃) (_ , Step (FHFailedCast x₄) x₅ (FHFailedCast x₆)) = final-not-step x (_ , Step x₄ x₅ x₆)
    indet-not-step (IPlus1 () x₄) (_ , Step FHOuter (ITPlus x₁) FHOuter)
    indet-not-step (IPlus1 x x₄) (_ , Step (FHPlus1 x₁) x₂ (FHPlus1 x₃)) = indet-not-step x (_ , Step x₁ x₂ x₃)
    indet-not-step (IPlus1 x x₄) (.(_ ·+ _) , Step (FHPlus2 x₁) x₂ (FHPlus2 x₃)) = final-not-step x₄ (_ , Step x₁ x₂ x₃)
    indet-not-step (IPlus2 x ()) (_ , Step FHOuter (ITPlus x₁) FHOuter)
    indet-not-step (IPlus2 x x₄) (_ , Step (FHPlus1 x₁) x₂ (FHPlus1 x₃)) = final-not-step x (_ , Step x₁ x₂ x₃)
    indet-not-step (IPlus2 x x₄) (_ , Step (FHPlus2 x₁) x₂ (FHPlus2 x₃)) = indet-not-step x₄ (_ , Step x₁ x₂ x₃)
    indet-not-step (IInl ind) (_ , Step FHOuter () x₂)
    indet-not-step (IInl ind) (_ , Step (FHInl x) x₁ (FHInl x₂)) = indet-not-step ind (_ , Step x x₁ x₂)
    indet-not-step (IInr ind) (_ , Step FHOuter () x₂)
    indet-not-step (IInr ind) (_ , Step (FHInr x) x₁ (FHInr x₂)) = indet-not-step ind (_ , Step x x₁ x₂)
    indet-not-step (ICase x x₁ x₂ ind) (_ , Step FHOuter ITCaseInl x₅) = x _ _ refl
    indet-not-step (ICase x x₁ x₂ ind) (_ , Step FHOuter ITCaseInr x₅) = x₁ _ _ refl
    indet-not-step (ICase x x₁ x₂ ind) (_ , Step FHOuter ITCaseCast x₅) = x₂ _ _ _ _ _ refl
    indet-not-step (ICase x x₁ x₂ ind) (_ , Step (FHCase x₃) x₄ (FHCase x₅)) = indet-not-step ind (_ , Step x₃ x₄ x₅)
    indet-not-step (ICastSum x ind) (_ , Step FHOuter ITCastID FHOuter) = x refl
    indet-not-step (ICastSum x ind) (_ , Step (FHCast x₁) x₂ (FHCast x₃)) = indet-not-step ind (_ , Step x₁ x₂ x₃)
    indet-not-step (ICastGroundHole GNum ind) (_ , Step FHOuter (ITGround ()) FHOuter)
    indet-not-step (ICastGroundHole GSumHole ind) (_ , Step FHOuter (ITGround (MGSum x)) FHOuter) = x refl
    indet-not-step (ICastHoleGround x ind GNum) (_ , Step FHOuter (ITExpand ()) FHOuter)
    indet-not-step (ICastHoleGround x ind GSumHole) (_ , Step FHOuter (ITExpand (MGSum x₁)) FHOuter) = x₁ refl
    indet-not-step (IPair1 ind x) (_ , Step (FHPair1 x₁) x₂ (FHPair1 x₃)) = indet-not-step ind (_ , Step x₁ x₂ x₃)
    indet-not-step (IPair1 ind x) (_ , Step (FHPair2 x₁) x₂ (FHPair2 x₃)) = final-not-step x (_ , Step x₁ x₂ x₃)
    indet-not-step (IPair2 x ind) (_ , Step (FHPair1 x₁) x₂ (FHPair1 x₃)) = final-not-step x (_ , Step x₁ x₂ x₃)
    indet-not-step (IPair2 x ind) (_ , Step (FHPair2 x₁) x₂ (FHPair2 x₃)) = indet-not-step ind (_ , Step x₁ x₂ x₃)
    indet-not-step (IFst x x₁ ind) (_ , Step FHOuter ITFstPair FHOuter) = x _ _ refl
    indet-not-step (IFst x x₁ ind) (_ , Step (FHFst x₂) x₃ (FHFst x₄)) = indet-not-step ind (_ , Step x₂ x₃ x₄)
    indet-not-step (ISnd x x₁ ind) (_ , Step FHOuter ITSndPair FHOuter) = x _ _ refl
    indet-not-step (ISnd x x₁ ind) (_ , Step (FHSnd x₂) x₃ (FHSnd x₄)) = indet-not-step ind (_ , Step x₂ x₃ x₄)
    indet-not-step (ICastGroundHole GProdHole ind) (_ , Step FHOuter (ITGround (MGProd x)) FHOuter) = x refl
    indet-not-step (ICastHoleGround x ind GProdHole) (_ , Step FHOuter (ITExpand (MGProd x₁)) FHOuter) = x₁ refl
    indet-not-step (IPair1 ind x) (_ , Step FHOuter () FHOuter)
    indet-not-step (IPair2 x ind) (_ , Step FHOuter () FHOuter)
    indet-not-step (IFst x x₁ ind) (_ , Step FHOuter ITFstCast FHOuter) = x₁ _ _ _ _ _ refl
    indet-not-step (ISnd x x₁ ind) (_ , Step FHOuter ITSndCast FHOuter) = x₁ _ _ _ _ _ refl
    indet-not-step (ICastProd x ind) (_ , Step FHOuter ITCastID FHOuter) = x refl
    indet-not-step (ICastProd x ind) (_ , Step (FHCast x₁) x₂ (FHCast x₃)) = indet-not-step ind (_ , Step x₁ x₂ x₃)
    
    -- final expressions don't step
    final-not-step : ∀{d} → d final → Σ[ d' ∈ ihexp ] (d ↦ d') → ⊥
    final-not-step (FBoxedVal x) stp = boxedval-not-step x stp
    final-not-step (FIndet x) stp = indet-not-step x stp
 
