open import Prelude
open import Nat
open import core
open import contexts
open import disjointness


-- this module contains lemmas and properties about the holes-disjoint
-- judgement that double check that it acts as we would expect

module holes-disjoint-checks where
  -- these lemmas are all structurally recursive and quite
  -- mechanical. morally, they establish the properties about reduction
  -- that would be obvious / baked into Agda if holes-disjoint was defined
  -- as a function rather than a judgement (datatype), or if we had defined
  -- all the O(n^2) cases rather than relying on a little indirection to
  -- only have O(n) cases. that work has to go somewhwere, and we prefer
  -- that it goes here.

  ds-lem-plus : ∀{e1 e2 e3} → holes-disjoint e3 e1 → holes-disjoint e3 e2 → holes-disjoint e3 (e1 ·+ e2)
  ds-lem-plus HDNum ν = HDNum
  ds-lem-plus (HDPlus hd hd₁) (HDPlus ν ν₁) = HDPlus (ds-lem-plus hd ν) (ds-lem-plus hd₁ ν₁)
  ds-lem-plus (HDAsc hd) (HDAsc ν) = HDAsc (ds-lem-plus hd ν)
  ds-lem-plus HDVar HDVar = HDVar
  ds-lem-plus (HDLam1 hd) (HDLam1 ν) = HDLam1 (ds-lem-plus hd ν)
  ds-lem-plus (HDLam2 hd) (HDLam2 ν) = HDLam2 (ds-lem-plus hd ν)
  ds-lem-plus (HDAp hd hd₁) (HDAp ν ν₁) = HDAp (ds-lem-plus hd ν) (ds-lem-plus hd₁ ν₁)
  ds-lem-plus (HDHole x) (HDHole x₁) = HDHole (HNPlus x x₁)
  ds-lem-plus (HDNEHole x hd) (HDNEHole x₁ ν) = HDNEHole (HNPlus x x₁) (ds-lem-plus hd ν)
  
  ds-lem-asc : ∀{e1 e2 τ} → holes-disjoint e2 e1 → holes-disjoint e2 (e1 ·: τ)
  ds-lem-asc HDNum = HDNum
  ds-lem-asc (HDPlus hd hd₁) = HDPlus (ds-lem-asc hd) (ds-lem-asc hd₁)
  ds-lem-asc (HDAsc hd) = HDAsc (ds-lem-asc hd)
  ds-lem-asc HDVar = HDVar
  ds-lem-asc (HDLam1 hd) = HDLam1 (ds-lem-asc hd)
  ds-lem-asc (HDLam2 hd) = HDLam2 (ds-lem-asc hd)
  ds-lem-asc (HDAp hd hd₁) = HDAp (ds-lem-asc hd) (ds-lem-asc hd₁)
  ds-lem-asc (HDHole x) = HDHole (HNAsc x)
  ds-lem-asc (HDNEHole x hd) = HDNEHole (HNAsc x) (ds-lem-asc hd)

  ds-lem-lam1 : ∀{e1 e2 x} → holes-disjoint e2 e1 → holes-disjoint e2 (·λ x e1)
  ds-lem-lam1 HDNum = HDNum
  ds-lem-lam1 (HDPlus hd hd₁) = HDPlus (ds-lem-lam1 hd) (ds-lem-lam1 hd₁)
  ds-lem-lam1 (HDAsc hd) = HDAsc (ds-lem-lam1 hd)
  ds-lem-lam1 HDVar = HDVar
  ds-lem-lam1 (HDLam1 hd) = HDLam1 (ds-lem-lam1 hd)
  ds-lem-lam1 (HDLam2 hd) = HDLam2 (ds-lem-lam1 hd)
  ds-lem-lam1 (HDAp hd hd₁) = HDAp (ds-lem-lam1 hd) (ds-lem-lam1 hd₁)
  ds-lem-lam1 (HDHole x₁) = HDHole (HNLam1 x₁)
  ds-lem-lam1 (HDNEHole x₁ hd) = HDNEHole (HNLam1 x₁) (ds-lem-lam1 hd) 

  ds-lem-lam2 : ∀{e1 e2 x τ} → holes-disjoint e2 e1 → holes-disjoint e2 (·λ x [ τ ] e1)
  ds-lem-lam2 HDNum = HDNum
  ds-lem-lam2 (HDPlus hd hd₁) = HDPlus (ds-lem-lam2 hd) (ds-lem-lam2 hd₁)
  ds-lem-lam2 (HDAsc hd) = HDAsc (ds-lem-lam2 hd)
  ds-lem-lam2 HDVar = HDVar
  ds-lem-lam2 (HDLam1 hd) = HDLam1 (ds-lem-lam2 hd)
  ds-lem-lam2 (HDLam2 hd) = HDLam2 (ds-lem-lam2 hd)
  ds-lem-lam2 (HDAp hd hd₁) = HDAp (ds-lem-lam2 hd) (ds-lem-lam2 hd₁)
  ds-lem-lam2 (HDHole x₁) = HDHole (HNLam2 x₁)
  ds-lem-lam2 (HDNEHole x₁ hd) = HDNEHole (HNLam2 x₁) (ds-lem-lam2 hd)

  ds-lem-nehole : ∀{e e1 u} → holes-disjoint e e1 → hole-name-new e u → holes-disjoint e ⦇⌜ e1 ⌟⦈[ u ]
  ds-lem-nehole HDNum ν = HDNum
  ds-lem-nehole (HDPlus hd hd₁) (HNPlus ν ν₁) = HDPlus (ds-lem-nehole hd ν) (ds-lem-nehole hd₁ ν₁)
  ds-lem-nehole (HDAsc hd) (HNAsc ν) = HDAsc (ds-lem-nehole hd ν)
  ds-lem-nehole HDVar ν = HDVar
  ds-lem-nehole (HDLam1 hd) (HNLam1 ν) = HDLam1 (ds-lem-nehole hd ν)
  ds-lem-nehole (HDLam2 hd) (HNLam2 ν) = HDLam2 (ds-lem-nehole hd ν)
  ds-lem-nehole (HDAp hd hd₁) (HNAp ν ν₁) = HDAp (ds-lem-nehole hd ν) (ds-lem-nehole hd₁ ν₁)
  ds-lem-nehole (HDHole x) (HNHole x₁) = HDHole (HNNEHole (flip x₁) x)
  ds-lem-nehole (HDNEHole x hd) (HNNEHole x₁ ν) = HDNEHole (HNNEHole (flip x₁) x) (ds-lem-nehole hd ν)

  ds-lem-ap : ∀{e1 e2 e3} → holes-disjoint e3 e1 → holes-disjoint e3 e2 → holes-disjoint e3 (e1 ∘ e2)
  ds-lem-ap HDNum hd2 = HDNum
  ds-lem-ap (HDPlus hd1 hd2) (HDPlus hd3 hd4) = HDPlus (ds-lem-ap hd1 hd3) (ds-lem-ap hd2 hd4)
  ds-lem-ap (HDAsc hd1) (HDAsc hd2) = HDAsc (ds-lem-ap hd1 hd2)
  ds-lem-ap HDVar hd2 = HDVar
  ds-lem-ap (HDLam1 hd1) (HDLam1 hd2) = HDLam1 (ds-lem-ap hd1 hd2)
  ds-lem-ap (HDLam2 hd1) (HDLam2 hd2) = HDLam2 (ds-lem-ap hd1 hd2)
  ds-lem-ap (HDAp hd1 hd2) (HDAp hd3 hd4) = HDAp (ds-lem-ap hd1 hd3) (ds-lem-ap hd2 hd4)
  ds-lem-ap (HDHole x) (HDHole x₁) = HDHole (HNAp x x₁)
  ds-lem-ap (HDNEHole x hd1) (HDNEHole x₁ hd2) = HDNEHole (HNAp x x₁) (ds-lem-ap hd1 hd2)

  -- holes-disjoint is symmetric
  disjoint-sym : (e1 e2 : hexp) → holes-disjoint e1 e2 → holes-disjoint e2 e1

  disjoint-sym _ (N n) HDNum = HDNum
  disjoint-sym _ (e2 ·+ e3) HDNum = HDPlus (disjoint-sym _ e2 HDNum) (disjoint-sym _ e3 HDNum)
  disjoint-sym _ (e2 ·: x) HDNum = HDAsc (disjoint-sym _ e2 HDNum)
  disjoint-sym _ (X x) HDNum = HDVar
  disjoint-sym _ (·λ x e2) HDNum = HDLam1 (disjoint-sym _ e2 HDNum)
  disjoint-sym _ (·λ x [ x₁ ] e2) HDNum = HDLam2 (disjoint-sym _ e2 HDNum)
  disjoint-sym _ (e2 ∘ e3) HDNum = HDAp (disjoint-sym _ e2 HDNum) (disjoint-sym _ e3 HDNum)
  disjoint-sym _ ⦇-⦈[ x ] HDNum = HDHole HNNum
  disjoint-sym _ ⦇⌜ e2 ⌟⦈[ x ] HDNum = HDNEHole HNNum (disjoint-sym _ e2 HDNum)
  
  disjoint-sym _ (N n) (HDPlus hd hd₁) = HDNum
  disjoint-sym _ (e2 ·+ e3) (HDPlus hd hd₁) with disjoint-sym _ _ hd | disjoint-sym _ _ hd₁
  ... | HDPlus ih ih₁ | HDPlus ih₂ ih₃ = HDPlus (ds-lem-plus ih ih₂) (ds-lem-plus ih₁ ih₃)
  disjoint-sym _ (e2 ·: x) (HDPlus hd hd₁) with disjoint-sym _ _ hd | disjoint-sym _ _ hd₁
  ... | HDAsc ih | HDAsc ih₁ = HDAsc (ds-lem-plus ih ih₁)
  disjoint-sym _ (X x) (HDPlus hd hd₁) = HDVar
  disjoint-sym _ (·λ x e2) (HDPlus hd hd₁) with disjoint-sym _ _ hd | disjoint-sym _ _ hd₁
  ... | HDLam1 ih | HDLam1 ih₁ = ds-lem-plus (HDLam1 ih) (HDLam1 ih₁)
  disjoint-sym _ (·λ x [ x₁ ] e2) (HDPlus hd hd₁) with disjoint-sym _ _ hd | disjoint-sym _ _ hd₁
  ... | HDLam2 ih | HDLam2 ih₁ = HDLam2 (ds-lem-plus ih ih₁)
  disjoint-sym _ (e2 ∘ e3) (HDPlus hd hd₁) with disjoint-sym _ _ hd | disjoint-sym _ _ hd₁
  ... | HDAp ih ih₁ | HDAp ih₂ ih₃ = HDAp (ds-lem-plus ih ih₂) (ds-lem-plus ih₁ ih₃)
  disjoint-sym _ ⦇-⦈[ x ] (HDPlus hd hd₁) with disjoint-sym _ _ hd | disjoint-sym _ _ hd₁
  ... | HDHole x₁ | HDHole x₂ = HDHole (HNPlus x₁ x₂)
  disjoint-sym _ ⦇⌜ e2 ⌟⦈[ x ] (HDPlus hd hd₁) with disjoint-sym _ _ hd | disjoint-sym _ _ hd₁
  ... | HDNEHole x₁ ih | HDNEHole x₂ ih₁ = HDNEHole (HNPlus x₁ x₂) (ds-lem-plus ih ih₁)
  
  disjoint-sym _ (N n) (HDAsc hd) = HDNum
  disjoint-sym _ (e2 ·+ e3) (HDAsc hd) with disjoint-sym _ _ hd
  ... | HDPlus x x₁ = HDPlus (ds-lem-asc x) (ds-lem-asc x₁)
  disjoint-sym _ (e2 ·: x) (HDAsc hd) with disjoint-sym _ _ hd
  disjoint-sym _ (e2 ·: x) (HDAsc hd) | HDAsc ih = HDAsc (ds-lem-asc ih)
  disjoint-sym _ (X x) (HDAsc hd) = HDVar
  disjoint-sym _ (·λ x e2) (HDAsc hd) with disjoint-sym _ _ hd
  disjoint-sym _ (·λ x e2) (HDAsc hd) | HDLam1 ih = HDLam1 (ds-lem-asc ih)
  disjoint-sym _ (·λ x [ x₁ ] e2) (HDAsc hd) with disjoint-sym _ _ hd
  disjoint-sym _ (·λ x [ x₁ ] e2) (HDAsc hd) | HDLam2 ih = HDLam2 (ds-lem-asc ih)
  disjoint-sym _ ⦇-⦈[ x ] (HDAsc hd) with disjoint-sym _ _ hd
  disjoint-sym _ ⦇-⦈[ x ] (HDAsc hd) | HDHole x₁ = HDHole (HNAsc x₁)
  disjoint-sym _ ⦇⌜ e2 ⌟⦈[ x ] (HDAsc hd) with disjoint-sym _ _ hd
  disjoint-sym _ ⦇⌜ e2 ⌟⦈[ x ] (HDAsc hd) | HDNEHole x₁ ih = HDNEHole (HNAsc x₁) (ds-lem-asc ih)
  disjoint-sym _ (e2 ∘ e3) (HDAsc hd) with disjoint-sym _ _ hd
  disjoint-sym _ (e2 ∘ e3) (HDAsc hd) | HDAp ih ih₁ = HDAp (ds-lem-asc ih) (ds-lem-asc ih₁)

  disjoint-sym _ (N n) HDVar = HDNum
  disjoint-sym _ (e2 ·+ e3) HDVar = HDPlus (disjoint-sym _ e2 HDVar) (disjoint-sym _ e3 HDVar)
  disjoint-sym _ (e2 ·: x₁) HDVar = HDAsc (disjoint-sym _ e2 HDVar)
  disjoint-sym _ (X x₁) HDVar = HDVar
  disjoint-sym _ (·λ x₁ e2) HDVar = HDLam1 (disjoint-sym _ e2 HDVar)
  disjoint-sym _ (·λ x₁ [ x₂ ] e2) HDVar = HDLam2 (disjoint-sym _ e2 HDVar)
  disjoint-sym _ ⦇-⦈[ x₁ ] HDVar = HDHole HNVar
  disjoint-sym _ ⦇⌜ e2 ⌟⦈[ x₁ ] HDVar = HDNEHole HNVar (disjoint-sym _ e2 HDVar)
  disjoint-sym _ (e2 ∘ e3) HDVar = HDAp (disjoint-sym _ e2 HDVar) (disjoint-sym _ e3 HDVar)

  disjoint-sym _ (N n) (HDLam1 hd) = HDNum
  disjoint-sym _ (e2 ·+ e3) (HDLam1 hd) with disjoint-sym _ _ hd
  ... | HDPlus x x₁ = HDPlus (ds-lem-lam1 x) (ds-lem-lam1 x₁)
  disjoint-sym _ (e2 ·: x₁) (HDLam1 hd) with disjoint-sym _ _ hd
  disjoint-sym _ (e2 ·: x₁) (HDLam1 hd) | HDAsc ih = HDAsc (ds-lem-lam1 ih)
  disjoint-sym _ (X x₁) (HDLam1 hd) = HDVar
  disjoint-sym _ (·λ x₁ e2) (HDLam1 hd) with disjoint-sym _ _ hd
  disjoint-sym _ (·λ x₁ e2) (HDLam1 hd) | HDLam1 ih = HDLam1 (ds-lem-lam1 ih)
  disjoint-sym _ (·λ x₁ [ x₂ ] e2) (HDLam1 hd) with disjoint-sym _ _ hd
  disjoint-sym _ (·λ x₁ [ x₂ ] e2) (HDLam1 hd) | HDLam2 ih = HDLam2 (ds-lem-lam1 ih)
  disjoint-sym _ ⦇-⦈[ x₁ ] (HDLam1 hd) with disjoint-sym _ _ hd
  disjoint-sym _ ⦇-⦈[ x₁ ] (HDLam1 hd) | HDHole x = HDHole (HNLam1 x)
  disjoint-sym _ ⦇⌜ e2 ⌟⦈[ x₁ ] (HDLam1 hd) with disjoint-sym _ _ hd
  disjoint-sym _ ⦇⌜ e2 ⌟⦈[ x₁ ] (HDLam1 hd) | HDNEHole x ih = HDNEHole (HNLam1 x) (ds-lem-lam1 ih)
  disjoint-sym _ (e2 ∘ e3) (HDLam1 hd) with disjoint-sym _ _ hd
  disjoint-sym _ (e2 ∘ e3) (HDLam1 hd) | HDAp ih ih₁ = HDAp (ds-lem-lam1 ih) (ds-lem-lam1 ih₁)

  disjoint-sym _ (N n) (HDLam2 hd) = HDNum
  disjoint-sym _ (e2 ·+ e3) (HDLam2 hd) with disjoint-sym _ _ hd
  ... | HDPlus x x₁ = HDPlus (ds-lem-lam2 x) (ds-lem-lam2 x₁)
  disjoint-sym _ (e2 ·: x₁) (HDLam2 hd) with disjoint-sym _ _ hd
  disjoint-sym _ (e2 ·: x₁) (HDLam2 hd) | HDAsc ih = HDAsc (ds-lem-lam2 ih)
  disjoint-sym _ (X x₁) (HDLam2 hd) = HDVar
  disjoint-sym _ (·λ x₁ e2) (HDLam2 hd) with disjoint-sym _ _ hd
  disjoint-sym _ (·λ x₁ e2) (HDLam2 hd) | HDLam1 ih = HDLam1 (ds-lem-lam2 ih)
  disjoint-sym _ (·λ x₁ [ x₂ ] e2) (HDLam2 hd) with disjoint-sym _ _ hd
  disjoint-sym _ (·λ x₁ [ x₂ ] e2) (HDLam2 hd) | HDLam2 ih = HDLam2 (ds-lem-lam2 ih)
  disjoint-sym _ ⦇-⦈[ x₁ ] (HDLam2 hd) with disjoint-sym _ _ hd
  disjoint-sym _ ⦇-⦈[ x₁ ] (HDLam2 hd) | HDHole x = HDHole (HNLam2 x)
  disjoint-sym _ ⦇⌜ e2 ⌟⦈[ x₁ ] (HDLam2 hd) with disjoint-sym _ _ hd
  disjoint-sym _ ⦇⌜ e2 ⌟⦈[ x₁ ] (HDLam2 hd) | HDNEHole x ih = HDNEHole (HNLam2 x) (ds-lem-lam2 ih)
  disjoint-sym _ (e2 ∘ e3) (HDLam2 hd) with disjoint-sym _ _ hd
  disjoint-sym _ (e2 ∘ e3) (HDLam2 hd) | HDAp ih ih₁ = HDAp (ds-lem-lam2 ih) (ds-lem-lam2 ih₁)

  disjoint-sym _ (N n) (HDAp hd hd₁) = HDNum
  disjoint-sym _ (e2 ·+ e3) (HDAp hd hd₁) with disjoint-sym _ _ hd | disjoint-sym _ _ hd₁
  ... | HDPlus x x₁ | HDPlus x₂ x₃ = HDPlus (ds-lem-ap x x₂) (ds-lem-ap x₁ x₃)
  disjoint-sym _ (e3 ·: x) (HDAp hd hd₁) with disjoint-sym _ _ hd | disjoint-sym _ _ hd₁
  disjoint-sym _ (e3 ·: x) (HDAp hd hd₁) | HDAsc ih | HDAsc ih1 = HDAsc (ds-lem-ap ih ih1)
  disjoint-sym _ (X x) (HDAp hd hd₁) = HDVar
  disjoint-sym _ (·λ x e3) (HDAp hd hd₁) with disjoint-sym _ _ hd | disjoint-sym _ _ hd₁
  disjoint-sym _ (·λ x e3) (HDAp hd hd₁) | HDLam1 ih | HDLam1 ih1 = HDLam1 (ds-lem-ap ih ih1)
  disjoint-sym _ (·λ x [ x₁ ] e3) (HDAp hd hd₁) with disjoint-sym _ _ hd | disjoint-sym _ _ hd₁
  disjoint-sym _ (·λ x [ x₁ ] e3) (HDAp hd hd₁) | HDLam2 ih | HDLam2 ih1 = HDLam2 (ds-lem-ap ih ih1)
  disjoint-sym _ ⦇-⦈[ x ] (HDAp hd hd₁) with disjoint-sym _ _ hd | disjoint-sym _ _ hd₁
  disjoint-sym _ ⦇-⦈[ x ] (HDAp hd hd₁) | HDHole x₁ | HDHole x₂ = HDHole (HNAp x₁ x₂)
  disjoint-sym _ ⦇⌜ e3 ⌟⦈[ x ] (HDAp hd hd₁) with disjoint-sym _ _ hd | disjoint-sym _ _ hd₁
  disjoint-sym _ ⦇⌜ e3 ⌟⦈[ x ] (HDAp hd hd₁) | HDNEHole x₁ ih | HDNEHole x₂ ih1 = HDNEHole (HNAp x₁ x₂) (ds-lem-ap ih ih1)
  disjoint-sym _ (e3 ∘ e4) (HDAp hd hd₁) with disjoint-sym _ _ hd | disjoint-sym _ _ hd₁
  disjoint-sym _ (e3 ∘ e4) (HDAp hd hd₁) | HDAp ih ih₁ | HDAp ih1 ih2 = HDAp (ds-lem-ap ih ih1) (ds-lem-ap ih₁ ih2)

  disjoint-sym _ (N n) (HDHole x) = HDNum
  disjoint-sym _ (e2 ·+ e3) (HDHole (HNPlus x x₁)) =
    HDPlus (disjoint-sym ⦇-⦈[ _ ] e2 (HDHole x)) (disjoint-sym ⦇-⦈[ _ ] e3 (HDHole x₁))
  disjoint-sym _ (e2 ·: x) (HDHole (HNAsc x₁)) = HDAsc (disjoint-sym ⦇-⦈[ _ ] e2 (HDHole x₁))
  disjoint-sym _ (X x) (HDHole x₁) = HDVar
  disjoint-sym _ (·λ x e2) (HDHole (HNLam1 x₁)) = HDLam1 (disjoint-sym ⦇-⦈[ _ ] e2 (HDHole x₁))
  disjoint-sym _ (·λ x [ x₁ ] e2) (HDHole (HNLam2 x₂)) = HDLam2 (disjoint-sym ⦇-⦈[ _ ] e2 (HDHole x₂))
  disjoint-sym _ ⦇-⦈[ x ] (HDHole (HNHole x₁)) =  HDHole (HNHole (flip x₁))
  disjoint-sym _ ⦇⌜ e2 ⌟⦈[ u' ] (HDHole (HNNEHole x x₁)) = HDNEHole (HNHole (flip x)) (disjoint-sym ⦇-⦈[ _ ] e2 (HDHole x₁))
  disjoint-sym _ (e2 ∘ e3) (HDHole (HNAp x x₁)) = HDAp (disjoint-sym ⦇-⦈[ _ ] e2 (HDHole x))
                                                       (disjoint-sym ⦇-⦈[ _ ] e3 (HDHole x₁))

  disjoint-sym _ (N n) (HDNEHole x₁ hd) = HDNum
  disjoint-sym _ (e2 ·+ e3) (HDNEHole (HNPlus x₁ x₂) hd) with disjoint-sym _ _ hd
  ... | HDPlus ih ih₁ = HDPlus (ds-lem-nehole ih x₁) (ds-lem-nehole ih₁ x₂)
  disjoint-sym _ (e2 ·: x) (HDNEHole x₁ hd) with disjoint-sym _ _ hd
  disjoint-sym _ (e ·: x) (HDNEHole (HNAsc x₁) hd) | HDAsc ih = HDAsc (ds-lem-nehole ih x₁)
  disjoint-sym _ (X x) (HDNEHole x₁ hd) = HDVar
  disjoint-sym _ (·λ x e2) (HDNEHole x₁ hd) with disjoint-sym _ _ hd
  disjoint-sym _ (·λ x e2) (HDNEHole (HNLam1 x₁) hd) | HDLam1 ih = HDLam1 (ds-lem-nehole ih x₁)
  disjoint-sym _ (·λ x [ x₁ ] e2) (HDNEHole x₂ hd) with disjoint-sym _ _ hd
  disjoint-sym _ (·λ x [ x₁ ] e2) (HDNEHole (HNLam2 x₂) hd) | HDLam2 ih = HDLam2 (ds-lem-nehole ih x₂)
  disjoint-sym _ ⦇-⦈[ x ] (HDNEHole x₁ hd) with disjoint-sym _ _ hd
  disjoint-sym _ ⦇-⦈[ x ] (HDNEHole (HNHole x₂) hd) | HDHole x₁ = HDHole (HNNEHole (flip x₂) x₁)
  disjoint-sym _ ⦇⌜ e2 ⌟⦈[ x ] (HDNEHole x₁ hd) with disjoint-sym _ _ hd
  disjoint-sym _ ⦇⌜ e2 ⌟⦈[ x ] (HDNEHole (HNNEHole x₂ x₃) hd) | HDNEHole x₁ ih = HDNEHole (HNNEHole (flip x₂) x₁) (ds-lem-nehole ih x₃)
  disjoint-sym _ (e2 ∘ e3) (HDNEHole x hd) with disjoint-sym _ _ hd
  disjoint-sym _ (e2 ∘ e3) (HDNEHole (HNAp x x₁) hd) | HDAp ih ih₁ = HDAp (ds-lem-nehole ih x) (ds-lem-nehole ih₁ x₁)

  -- note that this is false, so holes-disjoint isn't transitive
  -- disjoint-new : ∀{e1 e2 u} → holes-disjoint e1 e2 → hole-name-new e1 u → hole-name-new e2 u

  -- it's also not reflexive, because ⦇-⦈[ u ] isn't hole-disjoint with
  -- itself since refl : u == u; it's also not anti-reflexive, because the
  -- expression c *is* hole-disjoint with itself (albeit vacuously)
