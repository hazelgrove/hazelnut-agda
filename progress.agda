open import Nat
open import Prelude
open import core
open import contexts
open import lemmas-consistency
open import lemmas-ground

open import progress-checks

open import canonical-boxed-forms
open import canonical-value-forms
open import canonical-indeterminate-forms

open import ground-decidable
open import htype-decidable

module progress where
  -- this is a little bit of syntactic sugar to avoid many layer nested Inl
  -- and Inrs that you would get from the more literal transcription of the
  -- consequent of progress
  data ok : (d : ihexp) (Δ : hctx) → Set where
    S  : ∀{d Δ} → Σ[ d' ∈ ihexp ] (d ↦ d') → ok d Δ
    I  : ∀{d Δ} → d indet → ok d Δ
    BV : ∀{d Δ} → d boxedval → ok d Δ

  progress : {Δ : hctx} {d : ihexp} {τ : htyp} →
             Δ , ∅ ⊢ d :: τ →
             ok d Δ
    -- constants
  progress TANum = BV (BVVal VNum)

    -- addition
  progress (TAPlus wt1 wt2) with progress wt1 | progress wt2
    -- if the left steps, the whole thing steps
  ... | S (_ , Step x y z) | _  = S (_ , Step (FHPlus1 x) y (FHPlus1 z))
  ... | I _ | S (_ , Step x y z) = S (_ , Step (FHPlus2 x) y (FHPlus2 z))
  ... | BV _ | S (_ , Step x y z) = S (_ , Step (FHPlus2 x) y (FHPlus2 z))
  ... | I x | I x₁ = I (IPlus1 x (FIndet x₁))
  ... | I x | BV x₁ = I (IPlus1 x (FBoxedVal x₁))
  ... | BV (BVVal VNum) | I x = I (IPlus2 (FBoxedVal (BVVal VNum)) x)
  ... | BV (BVVal VNum) | BV (BVVal VNum) = S (_ , Step FHOuter (ITPlus refl) FHOuter)
  
    -- variables
  progress (TAVar x₁) = abort (somenotnone (! x₁))

    -- lambdas
  progress (TALam _ wt) = BV (BVVal VLam)

    -- applications
  progress (TAAp wt1 wt2)
    with progress wt1 | progress wt2
    -- if the left steps, the whole thing steps
  ... | S (_ , Step x y z) | _ = S (_ , Step (FHAp1 x) y (FHAp1 z))
    -- if the left is indeterminate, step the right
  ... | I i | S (_ , Step x y z) = S (_ , Step (FHAp2 x) y (FHAp2  z))
    -- if they're both indeterminate, step when the cast steps and indet otherwise
  ... | I x | I y
    with canonical-indeterminate-forms-arr wt1 x
  ... | CIFACast (_ , _ , _ , _ , _ , refl , _ , _ ) = S (_ , Step FHOuter ITApCast FHOuter)
  ... | CIFAEHole (_ , _ , _ , refl , _)             = I (IAp (λ _ _ _ _ _ ()) x (FIndet y))
  ... | CIFANEHole (_ , _ , _ , _ , _ , refl , _)    = I (IAp (λ _ _ _ _ _ ()) x (FIndet y))
  ... | CIFAAp (_ , _ , _ , _ , _ , refl , _)        = I (IAp (λ _ _ _ _ _ ()) x (FIndet y))
  ... | CIFACastHole (_ , refl , refl , refl , _ )   = I (IAp (λ _ _ _ _ _ ()) x (FIndet y))
  ... | CIFAFailedCast (_ , _ , refl , _ )           = I (IAp (λ _ _ _ _ _ ()) x (FIndet y))
  ... | CIFACase (_ , _ , _ , _ , _ , _ , _ , refl , _ ) = I (IAp (λ _ _ _ _ _ ()) x (FIndet y))
  ... | CIFAFst (_ , _ , refl , _ , _ , _ , _) = I (IAp (λ _ _ _ _ _ ()) x (FIndet y))
  ... | CIFASnd (_ , _ , refl , _ , _ , _ , _) = I (IAp (λ _ _ _ _ _ ()) x (FIndet y))
  
    -- similar if the left is indeterminate but the right is a boxed val
  progress (TAAp wt1 wt2) | I x | BV y
    with canonical-indeterminate-forms-arr wt1 x
  ... | CIFACast (_ , _ , _ , _ , _ , refl , _ , _ ) = S (_ , Step FHOuter ITApCast FHOuter)
  ... | CIFAEHole (_ , _ , _ , refl , _)             = I (IAp (λ _ _ _ _ _ ()) x (FBoxedVal y))
  ... | CIFANEHole (_ , _ , _ , _ , _ , refl , _)    = I (IAp (λ _ _ _ _ _ ()) x (FBoxedVal y))
  ... | CIFAAp (_ , _ , _ , _ , _ , refl , _)        = I (IAp (λ _ _ _ _ _ ()) x (FBoxedVal y))
  ... | CIFACastHole (_ , refl , refl , refl , _ )   = I (IAp (λ _ _ _ _ _ ()) x (FBoxedVal y))
  ... | CIFAFailedCast (_ , _ , refl , _ )           = I (IAp (λ _ _ _ _ _ ()) x (FBoxedVal y))
  ... | CIFACase (_ , _ , _ , _ , _ , _ , _ , refl , _ ) = I (IAp (λ _ _ _ _ _ ()) x (FBoxedVal y))
  ... | CIFAFst (_ , _ , refl , _ , _ , _ , _) = I (IAp (λ _ _ _ _ _ ()) x (FBoxedVal y))
  ... | CIFASnd (_ , _ , refl , _ , _ , _ , _) = I (IAp (λ _ _ _ _ _ ()) x (FBoxedVal y))
  
    -- if the left is a boxed value, inspect the right
  progress (TAAp wt1 wt2) | BV v | S (_ , Step x y z) = S (_ , Step (FHAp2  x) y (FHAp2  z))
  progress (TAAp wt1 wt2) | BV v | I i
    with canonical-boxed-forms-arr wt1 v
  ... | CBFALam (_ , _ , refl , _)             = S (_ , Step FHOuter ITLam FHOuter)
  ... | CBFACastArr (_ , _ , _ , refl , _ , _) = S (_ , Step FHOuter ITApCast FHOuter)
  progress (TAAp wt1 wt2) | BV v | BV v₂
    with canonical-boxed-forms-arr wt1 v
  ... | CBFALam (_ , _ , refl , _)             = S (_ , Step FHOuter ITLam FHOuter)
  ... | CBFACastArr (_ , _ , _ , refl , _ , _) = S (_ , Step FHOuter ITApCast FHOuter)

    -- sum types
  progress (TAInl wt)
    with progress wt
  ... | S (_ , Step x y z) = S (_ , Step (FHInl x) y (FHInl z))
  ... | I x = I (IInl x)
  ... | BV x = BV (BVInl x)
  progress (TAInr wt)
    with progress wt
  ... | S (_ , Step x y z) = S (_ , Step (FHInr x) y (FHInr z))
  ... | I x = I (IInr x)
  ... | BV x = BV (BVInr x)
  progress (TACase wt _ wt₁ _ wt₂)
    with progress wt
  ... | S (_ , Step x y z)  = S (_ , Step (FHCase x) y (FHCase z))
  progress (TACase () _ wt₁ _ wt₂) | BV (BVVal VNum)
  progress (TACase () _ wt₁ _ wt₂) | BV (BVVal VLam)
  progress (TACase () _ wt₁ _ wt₂) | BV (BVVal (VPair x x₁))
  progress (TACase wt _ wt₁ _ wt₂) | BV (BVVal (VInl x)) = S (_ , Step FHOuter ITCaseInl FHOuter)
  ... | BV (BVVal (VInr x)) = S (_ , Step FHOuter ITCaseInr FHOuter)
  ... | BV (BVInl x)        = S (_ , Step FHOuter ITCaseInl FHOuter)
  ... | BV (BVInr x)        = S (_ , Step FHOuter ITCaseInr FHOuter)
  ... | BV (BVSumCast x x₁) = S (_ , Step FHOuter ITCaseCast FHOuter)
  ... | I (IAp x x₁ x₂) = I (ICase (λ _ _ ()) (λ _ _ ()) (λ _ _ _ _ _ ()) (IAp x x₁ x₂))
  ... | I (IInl x) = S (_ , Step FHOuter ITCaseInl FHOuter)
  ... | I (IInr x) = S (_ , Step FHOuter ITCaseInr FHOuter)
  ... | I (ICase x x₁ x₂ x₃) = I (ICase (λ _ _ ()) (λ _ _ ()) (λ _ _ _ _ _ ()) (ICase x x₁ x₂ x₃))
  ... | I (IFst x x₁ x₂) = I (ICase (λ _ _ ()) (λ _ _ ()) (λ _ _ _ _ _ ()) (IFst x x₁ x₂))
  ... | I (ISnd x x₁ x₂) = I (ICase (λ _ _ ()) (λ _ _ ()) (λ _ _ _ _ _ ()) (ISnd x x₁ x₂))
  ... | I IEHole = I (ICase (λ _ _ ()) (λ _ _ ()) (λ _ _ _ _ _ ()) IEHole)
  ... | I (INEHole x) = I (ICase (λ _ _ ()) (λ _ _ ()) (λ _ _ _ _ _ ()) (INEHole x))
  ... | I (ICastSum x x₁) = S (_ , Step FHOuter ITCaseCast FHOuter)
  ... | I (ICastHoleGround x x₁ x₂) = I (ICase (λ _ _ ()) (λ _ _ ()) (λ _ _ _ _ _ ()) (ICastHoleGround x x₁ x₂))
  ... | I (IFailedCast x x₁ x₂ x₃) = I (ICase (λ _ _ ()) (λ _ _ ()) (λ _ _ _ _ _ ()) (IFailedCast x x₁ x₂ x₃))

  
    --product types
  progress (TAPair wt₁ wt₂)
    with progress wt₁ | progress wt₂
  ... | S (_ , Step x y z) | _  = S (_ , Step (FHPair1 x) y (FHPair1 z))
  ... | I _ | S (_ , Step x y z) = S (_ , Step (FHPair2 x) y (FHPair2 z))
  ... | BV _ | S (_ , Step x y z) = S (_ , Step (FHPair2 x) y (FHPair2 z))
  ... | I x | I x₁ = I (IPair1 x (FIndet x₁))
  ... | I x | BV x₁ = I (IPair1 x (FBoxedVal x₁))
  ... | BV x | I x₁ = I (IPair2 (FBoxedVal x) x₁)
  ... | BV x | BV x₁ = BV (BVPair x x₁)
  progress (TAFst wt)
    with progress wt
  ... | S (_ , Step x y z) = S (_ , Step (FHFst x) y (FHFst z))
  ... | I (IAp x x₁ x₂) = I (IFst (λ _ _ ()) (λ _ _ _ _ _()) (IAp x x₁ x₂))
  ... | I (ICase x x₁ x₂ x₃) = I (IFst (λ _ _ ()) (λ _ _ _ _ _ ()) (ICase x x₁ x₂ x₃))
  ... | I (IPair1 x x₁) = S (_ , Step FHOuter ITFstPair FHOuter)
  ... | I (IPair2 x x₁) = S (_ , Step FHOuter ITFstPair FHOuter)
  ... | I (IFst x x₁ x₂) = I (IFst (λ _ _ ()) (λ _ _ _ _ _ ()) (IFst x x₁ x₂))
  ... | I (ISnd x x₁ x₂) = I (IFst (λ _ _ ()) (λ _ _ _ _ _ ()) (ISnd x x₁ x₂))
  ... | I IEHole = I (IFst (λ _ _ ()) (λ _ _ _ _ _ ()) IEHole)
  ... | I (INEHole x) = I (IFst (λ _ _ ()) (λ _ _ _ _ _ ()) (INEHole x))
  ... | I (ICastProd x x₁) = S (_ , Step FHOuter ITFstCast FHOuter)
  ... | I (ICastHoleGround x x₁ x₂) = I (IFst (λ _ _ ()) (λ _ _ _ _ _ ()) (ICastHoleGround x x₁ x₂))
  ... | I (IFailedCast x x₁ x₂ x₃) = I (IFst (λ _ _ ()) (λ _ _ _ _ _ ()) (IFailedCast x x₁ x₂ x₃))
  ... | BV (BVVal (VPair x x₁)) = S (_ , Step FHOuter ITFstPair FHOuter)
  ... | BV (BVPair x x₁) = S (_ , Step FHOuter ITFstPair FHOuter)
  ... | BV (BVProdCast x x₁) = S (_ , Step FHOuter ITFstCast FHOuter)
  progress (TASnd wt)
    with progress wt
  ... | S (_ , Step x y z) = S (_ , Step (FHSnd x) y (FHSnd z))
  ... | I (IAp x x₁ x₂) = I (ISnd (λ _ _ ()) (λ _ _ _ _ _ ()) (IAp x x₁ x₂))
  ... | I (ICase x x₁ x₂ x₃) = I (ISnd (λ _ _ ()) (λ _ _ _ _ _ ()) (ICase x x₁ x₂ x₃))
  ... | I (IPair1 x x₁) = S (_ , Step FHOuter ITSndPair FHOuter)
  ... | I (IPair2 x x₁) = S (_ , Step FHOuter ITSndPair FHOuter)
  ... | I (IFst x x₁ x₂) = I (ISnd (λ _ _ ()) (λ _ _ _ _ _ ()) (IFst x x₁ x₂))
  ... | I (ISnd x x₁ x₂) = I (ISnd (λ _ _ ()) (λ _ _ _ _ _ ()) (ISnd x x₁ x₂))
  ... | I IEHole = I (ISnd (λ _ _ ()) (λ _ _ _ _ _ ()) IEHole)
  ... | I (INEHole x) = I (ISnd (λ _ _ ()) (λ _ _ _ _ _ ()) (INEHole x))
  ... | I (ICastProd x x₁) = S (_ , Step FHOuter ITSndCast FHOuter)
  ... | I (ICastHoleGround x x₁ x₂) = I (ISnd (λ _ _ ()) (λ _ _ _ _ _ ()) (ICastHoleGround x x₁ x₂))
  ... | I (IFailedCast x x₁ x₂ x₃) = I (ISnd (λ _ _ ()) (λ _ _ _ _ _ ()) (IFailedCast x x₁ x₂ x₃))
  ... | BV (BVVal (VPair x x₁)) = S (_ , Step FHOuter ITSndPair FHOuter)
  ... | BV (BVPair x x₁) = S (_ , Step FHOuter ITSndPair FHOuter)
  ... | BV (BVProdCast x x₁) = S (_ , Step FHOuter ITSndCast FHOuter)
  
    -- empty holes are indeterminate
  progress (TAEHole _ _ ) = I IEHole

    -- nonempty holes step if the innards step, indet otherwise
  progress (TANEHole xin wt x₁)
    with progress wt
  ... | S (_ , Step x y z) = S (_ , Step (FHNEHole x) y (FHNEHole z))
  ... | I  x = I (INEHole (FIndet x))
  ... | BV x = I (INEHole (FBoxedVal x))

    -- casts
  progress (TACast wt con)
    with progress wt
    -- step if the innards step
  ... | S (_ , Step x y z) = S (_ , Step (FHCast x) y (FHCast z))
    -- if indet, inspect how the types in the cast are realted by consistency:
    -- if they're the same, step by ID
  progress (TACast wt TCRefl)  | I x = S (_ , Step FHOuter ITCastID FHOuter)
    -- if first type is hole
  progress (TACast {τ1 = τ1} wt TCHole1) | I x
    with τ1
  ... | num = I (ICastGroundHole GNum x)
  ... | ⦇-⦈ = S (_ , Step FHOuter ITCastID FHOuter)
  ... | τ11 ==> τ12
    with ground-decidable (τ11 ==> τ12)
  ... | Inl GArrHole = I (ICastGroundHole GArrHole x)
  ... | Inr y =  S (_ , Step FHOuter (ITGround (MGArr (π1 (ground-not-holes y)))) FHOuter)
  progress (TACast {τ1 = τ1} wt TCHole1) | I x | τ11 ⊕ τ12
    with ground-decidable (τ11 ⊕ τ12)
  ... | Inl GSumHole = I (ICastGroundHole GSumHole x)
  ... | Inr y =  S (_ , Step FHOuter (ITGround (MGSum (π1 (π2 (ground-not-holes y))))) FHOuter)
  progress (TACast {τ1 = τ1} wt TCHole1) | I x | τ11 ⊠ τ12
    with ground-decidable (τ11 ⊠ τ12)
  ... | Inl GProdHole = I (ICastGroundHole GProdHole x)
  ... | Inr y = S (_ , Step FHOuter (ITGround (MGProd (π2 (π2 (ground-not-holes y))))) FHOuter)
    -- if second type is hole
  progress (TACast wt (TCHole2 {num})) | I x
    with canonical-indeterminate-forms-hole wt x
  ... | CIFHEHole (_ , _ , _ , refl , f)           = I (ICastHoleGround (λ _ _ ()) x GNum)
  ... | CIFHNEHole (_ , _ , _ , _ , _ , refl , _ ) = I (ICastHoleGround (λ _ _ ()) x GNum)
  ... | CIFHAp (_ , _ , _ , refl , _ )             = I (ICastHoleGround (λ _ _ ()) x GNum)
  ... | CIFHCase (_ , _ , _ , _ , _ , _ , _ , refl , _ ) = I (ICastHoleGround (λ _ _ ()) x GNum)
  ... | CIFHFst (_ , _ , refl , _ , _ , _ , _)  = I (ICastHoleGround (λ _ _ ()) x GNum)
  ... | CIFHSnd (_ , _ , refl , _ , _ , _ , _)  = I (ICastHoleGround (λ _ _ ()) x GNum)
  ... | CIFHCast (_ , τ , refl , _ , grn , _)
    with htype-dec τ num
  ... | Inl refl = S (_ , Step FHOuter (ITCastSucceed grn ) FHOuter)
  ... | Inr y    = S (_ , Step FHOuter (ITCastFail grn GNum y) FHOuter)
  
  progress (TACast wt (TCHole2 {⦇-⦈}))| I x = S (_ , Step FHOuter ITCastID FHOuter)
  progress (TACast wt (TCHole2 {τ11 ==> τ12})) | I x
    with ground-decidable (τ11 ==> τ12)
  ... | Inr y = S (_ , Step FHOuter (ITExpand (MGArr (π1 (ground-not-holes y)))) FHOuter)
  ... | Inl GArrHole
    with canonical-indeterminate-forms-hole wt x
  ... | CIFHEHole (_ , _ , _ , refl , _)            = I (ICastHoleGround (λ _ _ ()) x GArrHole)
  ... | CIFHNEHole (_ , _ , _ , _ , _ , refl , _)   = I (ICastHoleGround (λ _ _ ()) x GArrHole)
  ... | CIFHAp (_ , _ , _ , refl , _ )              = I (ICastHoleGround (λ _ _ ()) x GArrHole)
  ... | CIFHCase (_ , _ , _ , _ , _ , _ , _ , refl , _ ) = I (ICastHoleGround (λ _ _ ()) x GArrHole)
  ... | CIFHFst (_ , _ , refl , _ , _ , _ , _) = I (ICastHoleGround (λ _ _ ()) x GArrHole)
  ... | CIFHSnd (_ , _ , refl , _ , _ , _ , _) = I (ICastHoleGround (λ _ _ ()) x GArrHole)
  ... | CIFHCast (_ , ._ , refl , _ , GNum , _)     = S (_ , Step FHOuter (ITCastFail GNum GArrHole (λ ())) FHOuter)
  ... | CIFHCast (_ , ._ , refl , _ , GArrHole , _) = S (_ , Step FHOuter (ITCastSucceed GArrHole) FHOuter)
  ... | CIFHCast (_ , _ , refl , _ , GSumHole , _)  = S (_ , Step FHOuter (ITCastFail GSumHole GArrHole (λ ())) FHOuter)
  ... | CIFHCast (_ , ._ , refl , _ , GProdHole , _) = S (_ , Step FHOuter (ITCastFail GProdHole GArrHole (λ ())) FHOuter)

  progress (TACast wt (TCHole2 {τ11 ⊕ τ12})) | I x
    with ground-decidable (τ11 ⊕ τ12)
  ... | Inr y = S (_ , Step FHOuter (ITExpand (MGSum (π1 (π2 (ground-not-holes y))))) FHOuter)
  ... | Inl GSumHole
    with canonical-indeterminate-forms-hole wt x
  ... | CIFHEHole (_ , _ , _ , refl , _)           = I (ICastHoleGround (λ _ _ ()) x GSumHole)
  ... | CIFHNEHole (_ , _ , _ , _ , _ , refl , _)  = I (ICastHoleGround (λ _ _ ()) x GSumHole)
  ... | CIFHAp (_ , _ , _ , refl , _ )             = I (ICastHoleGround (λ _ _ ()) x GSumHole)
  ... | CIFHCase (_ , _ , _ , _ , _ , _ , _ , refl , _ ) = I (ICastHoleGround (λ _ _ ()) x GSumHole)
  ... | CIFHFst (_ , _ , refl , _ , _ , _ , _) = I (ICastHoleGround (λ _ _ ()) x GSumHole)
  ... | CIFHSnd (_ , _ , refl , _ , _ , _ , _) = I (ICastHoleGround (λ _ _ ()) x GSumHole)
  ... | CIFHCast (_ , _ , refl , _ , GNum , _)     = S (_ , Step FHOuter (ITCastFail GNum GSumHole (λ ())) FHOuter)
  ... | CIFHCast (_ , _ , refl , _ , GArrHole , _) = S (_ , Step FHOuter (ITCastFail GArrHole GSumHole (λ ())) FHOuter)
  ... | CIFHCast (_ , _ , refl , _ , GSumHole , _) = S (_ , Step FHOuter (ITCastSucceed GSumHole) FHOuter)
  ... | CIFHCast (_ , _ , refl , _ , GProdHole , _) = S (_ , Step FHOuter (ITCastFail GProdHole GSumHole λ ()) FHOuter)
  progress (TACast wt (TCHole2 {τ11 ⊠ τ12})) | I x
    with ground-decidable (τ11 ⊠ τ12)
  ... | Inr y = S (_ , Step FHOuter (ITExpand (MGProd (π2 (π2 (ground-not-holes y))))) FHOuter)
  ... | Inl GProdHole
    with canonical-indeterminate-forms-hole wt x
  ... | CIFHEHole (_ , _ , _ , refl , _)           = I (ICastHoleGround (λ _ _ ()) x GProdHole)
  ... | CIFHNEHole (_ , _ , _ , _ , _ , refl , _)  = I (ICastHoleGround (λ _ _ ()) x GProdHole)
  ... | CIFHAp (_ , _ , _ , refl , _ )             = I (ICastHoleGround (λ _ _ ()) x GProdHole)
  ... | CIFHCase (_ , _ , _ , _ , _ , _ , _ , refl , _ ) = I (ICastHoleGround (λ _ _ ()) x GProdHole)
  ... | CIFHFst (_ , _ , refl , _ , _ , _ , _) = I (ICastHoleGround (λ _ _ ()) x GProdHole)
  ... | CIFHSnd (_ , _ , refl , _ , _ , _ , _) = I (ICastHoleGround (λ _ _ ()) x GProdHole)
  ... | CIFHCast (_ , _ , refl , _ , GNum , _)     = S (_ , Step FHOuter (ITCastFail GNum GProdHole (λ ())) FHOuter)
  ... | CIFHCast (_ , _ , refl , _ , GArrHole , _) = S (_ , Step FHOuter (ITCastFail GArrHole GProdHole (λ ())) FHOuter)
  ... | CIFHCast (_ , _ , refl , _ , GSumHole , _) = S (_ , Step FHOuter (ITCastFail GSumHole GProdHole λ ()) FHOuter)
  ... | CIFHCast (_ , _ , refl , _ , GProdHole , _) = S (_ , Step FHOuter (ITCastSucceed GProdHole) FHOuter)
  
    -- if both are arrows
  progress (TACast wt (TCArr {τ1} {τ2} {τ1'} {τ2'} c1 c2)) | I x
    with htype-dec (τ1 ==> τ2)  (τ1' ==> τ2')
  ... | Inl refl = S (_ , Step FHOuter ITCastID FHOuter)
  ... | Inr y    = I (ICastArr y x)

    -- if both are sums
  progress (TACast wt (TCSum {τ1} {τ2} {τ1'} {τ2'} c1 c2)) | I x
    with htype-dec (τ1 ⊕ τ2) (τ1' ⊕ τ2')
  ... | Inl refl = S (_ , Step FHOuter ITCastID FHOuter)
  ... | Inr y    = I (ICastSum y x)
  progress (TACast wt (TCProd {τ1} {τ2} {τ1'} {τ2'} c1 c2)) | I x
    with htype-dec (τ1 ⊠ τ2) (τ1' ⊠ τ2')
  ... | Inl refl = S (_ , Step FHOuter ITCastID FHOuter)
  ... | Inr y    = I (ICastProd y x)
    -- boxed value cases, inspect how the casts are related by consistency
    -- step by ID if the casts are the same
  progress (TACast wt TCRefl) | BV x = S (_ , Step FHOuter ITCastID FHOuter)
    -- if left is hole
  progress (TACast wt (TCHole1 {τ = τ})) | BV x
    with τ | ground-decidable τ
  ... | τ | Inl g = BV (BVHoleCast g x)
  ... | num | Inr y = abort (y GNum)
  ... | ⦇-⦈ | Inr y = S (_ , Step FHOuter ITCastID FHOuter)
  ... | τ1 ==> τ2 | Inr y
    with (htype-dec (τ1 ==> τ2) (⦇-⦈ ==> ⦇-⦈))
  ... | Inl refl = BV (BVHoleCast GArrHole x)
  ... | Inr y    = S (_ , Step FHOuter (ITGround (MGArr y)) FHOuter)
  progress (TACast wt (TCHole1 {τ = τ})) | BV x  | τ1 ⊕ τ2 | Inr y
    with (htype-dec (τ1 ⊕ τ2) (⦇-⦈ ⊕ ⦇-⦈))
  ... | Inl refl = BV (BVHoleCast GSumHole x)
  ... | Inr y    = S (_ , Step FHOuter (ITGround (MGSum y)) FHOuter)
  progress (TACast wt (TCHole1 {τ = τ})) | BV x  | τ1 ⊠ τ2 | Inr y
    with (htype-dec (τ1 ⊠ τ2) (⦇-⦈ ⊠ ⦇-⦈))
  ... | Inl refl = BV (BVHoleCast GProdHole x)
  ... | Inr y = S (_ , Step FHOuter (ITGround (MGProd y)) FHOuter)
    -- if right is hole
  progress {τ = τ} (TACast wt TCHole2) | BV x
    with canonical-boxed-forms-hole wt x
  ... | d' , τ' , refl , gnd , wt'
    with htype-dec τ τ'
  ... | Inl refl = S (_  , Step FHOuter (ITCastSucceed gnd) FHOuter)
  ... | Inr x₁
    with ground-decidable τ
  ... | Inl y = S (_ , Step FHOuter (ITCastFail gnd y (flip x₁)) FHOuter)
  ... | Inr y
    with not-ground y
  ... | Inl refl = S (_ , Step FHOuter ITCastID FHOuter)
  ... | Inr (Inl (τ1 , τ2 , refl)) = S (_ , Step FHOuter (ITExpand (MGArr (π1 (ground-not-holes y)))) FHOuter)
  ... | Inr (Inr (Inl (τ1 , τ2 , refl))) =  S (_ , Step FHOuter (ITExpand (MGSum (π1 (π2 (ground-not-holes y))))) FHOuter)
  ... | Inr (Inr (Inr (τ1 , τ2 , refl))) = S (_ , Step FHOuter (ITExpand (MGProd (π2 (π2 (ground-not-holes y))))) FHOuter)
    -- if both arrows
  progress (TACast wt (TCArr {τ1} {τ2} {τ1'} {τ2'} c1 c2)) | BV x
    with htype-dec (τ1 ==> τ2) (τ1' ==> τ2')
  ... | Inl refl = S (_ , Step FHOuter ITCastID FHOuter)
  ... | Inr y = BV (BVArrCast y x)
    -- if both sums
  progress (TACast wt (TCSum {τ1} {τ2} {τ1'} {τ2'} c1 c2)) | BV x
    with htype-dec (τ1 ⊕ τ2) (τ1' ⊕ τ2')
  ... | Inl refl = S (_ , Step FHOuter ITCastID FHOuter)
  ... | Inr y = BV (BVSumCast y x)
  progress (TACast wt (TCProd {τ1} {τ2} {τ1'} {τ2'} c1 c2)) | BV x
    with htype-dec (τ1 ⊠ τ2) (τ1' ⊠ τ2')
  ... | Inl refl = S (_ , Step FHOuter ITCastID FHOuter)
  ... | Inr y = BV (BVProdCast y x)
   -- failed casts
  progress (TAFailedCast wt y z w)
    with progress wt
  ... | S (d' , Step x a q) = S (_ , Step (FHFailedCast x) a (FHFailedCast q))
  ... | I x = I (IFailedCast (FIndet x) y z w)
  ... | BV x = I (IFailedCast (FBoxedVal x) y z w)
