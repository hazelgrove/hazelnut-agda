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
  ds-lem-num  : ∀{e n} → holes-disjoint e (N n)
  ds-lem-num {N x} = HDNum
  ds-lem-num {e ·+ e₁} = HDPlus ds-lem-num ds-lem-num
  ds-lem-num {e ·: x} = HDAsc ds-lem-num
  ds-lem-num {X x} = HDVar
  ds-lem-num {·λ x e} = HDLam1 ds-lem-num
  ds-lem-num {·λ x [ x₁ ] e} = HDLam2 ds-lem-num
  ds-lem-num {e ∘ e₁} = HDAp ds-lem-num ds-lem-num
  ds-lem-num {inl e} = HDInl ds-lem-num
  ds-lem-num {inr e} = HDInr ds-lem-num
  ds-lem-num {case e x e₁ x₁ e₂} = HDCase ds-lem-num ds-lem-num ds-lem-num
  ds-lem-num {⦇-⦈[ x ]} = HDHole HNNum
  ds-lem-num {⦇⌜ e ⌟⦈[ x ]} = HDNEHole HNNum ds-lem-num
  
  ds-lem-plus : ∀{e1 e2 e3} → holes-disjoint e3 e1 → holes-disjoint e3 e2 → holes-disjoint e3 (e1 ·+ e2)
  ds-lem-plus HDNum ν = HDNum
  ds-lem-plus (HDPlus hd hd₁) (HDPlus ν ν₁) = HDPlus (ds-lem-plus hd ν) (ds-lem-plus hd₁ ν₁)
  ds-lem-plus (HDAsc hd) (HDAsc ν) = HDAsc (ds-lem-plus hd ν)
  ds-lem-plus HDVar HDVar = HDVar
  ds-lem-plus (HDLam1 hd) (HDLam1 ν) = HDLam1 (ds-lem-plus hd ν)
  ds-lem-plus (HDLam2 hd) (HDLam2 ν) = HDLam2 (ds-lem-plus hd ν)
  ds-lem-plus (HDAp hd hd₁) (HDAp ν ν₁) = HDAp (ds-lem-plus hd ν) (ds-lem-plus hd₁ ν₁)
  ds-lem-plus (HDInl hd) (HDInl ν) = HDInl (ds-lem-plus hd ν)
  ds-lem-plus (HDInr hd) (HDInr ν) = HDInr (ds-lem-plus hd ν)
  ds-lem-plus (HDCase hd hd₁ hd₂) (HDCase ν ν₁ ν₂) = HDCase (ds-lem-plus hd ν) (ds-lem-plus hd₁ ν₁) (ds-lem-plus hd₂ ν₂)
  ds-lem-plus (HDHole x) (HDHole x₁) = HDHole (HNPlus x x₁)
  ds-lem-plus (HDNEHole x hd) (HDNEHole x₁ ν) = HDNEHole (HNPlus x x₁) (ds-lem-plus hd ν)

  ds-lem-var : ∀{e x} → holes-disjoint e (X x)
  ds-lem-var {N x} = HDNum
  ds-lem-var {e ·+ e₁} = HDPlus ds-lem-var ds-lem-var
  ds-lem-var {e ·: x} = HDAsc ds-lem-var
  ds-lem-var {X x} = HDVar
  ds-lem-var {·λ x e} = HDLam1 ds-lem-var
  ds-lem-var {·λ x [ x₁ ] e} = HDLam2 ds-lem-var
  ds-lem-var {e ∘ e₁} = HDAp ds-lem-var ds-lem-var
  ds-lem-var {inl e} = HDInl ds-lem-var
  ds-lem-var {inr e} = HDInr ds-lem-var
  ds-lem-var {case e x e₁ x₁ e₂} = HDCase ds-lem-var ds-lem-var ds-lem-var
  ds-lem-var {⦇-⦈[ x ]} = HDHole HNVar
  ds-lem-var {⦇⌜ e ⌟⦈[ x ]} = HDNEHole HNVar ds-lem-var
  
  ds-lem-asc : ∀{e1 e2 τ} → holes-disjoint e2 e1 → holes-disjoint e2 (e1 ·: τ)
  ds-lem-asc HDNum = HDNum
  ds-lem-asc (HDPlus hd hd₁) = HDPlus (ds-lem-asc hd) (ds-lem-asc hd₁)
  ds-lem-asc (HDAsc hd) = HDAsc (ds-lem-asc hd)
  ds-lem-asc HDVar = HDVar
  ds-lem-asc (HDLam1 hd) = HDLam1 (ds-lem-asc hd)
  ds-lem-asc (HDLam2 hd) = HDLam2 (ds-lem-asc hd)
  ds-lem-asc (HDAp hd hd₁) = HDAp (ds-lem-asc hd) (ds-lem-asc hd₁)
  ds-lem-asc (HDInl hd) = HDInl (ds-lem-asc hd)
  ds-lem-asc (HDInr hd) = HDInr (ds-lem-asc hd)
  ds-lem-asc (HDCase hd hd₁ hd₂) = HDCase (ds-lem-asc hd) (ds-lem-asc hd₁) (ds-lem-asc hd₂)
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
  ds-lem-lam1 (HDInl hd) = HDInl (ds-lem-lam1 hd)
  ds-lem-lam1 (HDInr hd) = HDInr (ds-lem-lam1 hd)
  ds-lem-lam1 (HDCase hd hd₁ hd₂) = HDCase (ds-lem-lam1 hd) (ds-lem-lam1 hd₁) (ds-lem-lam1 hd₂)
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
  ds-lem-lam2 (HDInl hd) = HDInl (ds-lem-lam2 hd)
  ds-lem-lam2 (HDInr hd) = HDInr (ds-lem-lam2 hd)
  ds-lem-lam2 (HDCase hd hd₁ hd₂) = HDCase (ds-lem-lam2 hd) (ds-lem-lam2 hd₁) (ds-lem-lam2 hd₂)
  ds-lem-lam2 (HDHole x₁) = HDHole (HNLam2 x₁)
  ds-lem-lam2 (HDNEHole x₁ hd) = HDNEHole (HNLam2 x₁) (ds-lem-lam2 hd)
  
  ds-lem-ap : ∀{e1 e2 e3} → holes-disjoint e3 e1 → holes-disjoint e3 e2 → holes-disjoint e3 (e1 ∘ e2)
  ds-lem-ap HDNum hd2 = HDNum
  ds-lem-ap (HDPlus hd1 hd2) (HDPlus hd3 hd4) = HDPlus (ds-lem-ap hd1 hd3) (ds-lem-ap hd2 hd4)
  ds-lem-ap (HDAsc hd1) (HDAsc hd2) = HDAsc (ds-lem-ap hd1 hd2)
  ds-lem-ap HDVar hd2 = HDVar
  ds-lem-ap (HDLam1 hd1) (HDLam1 hd2) = HDLam1 (ds-lem-ap hd1 hd2)
  ds-lem-ap (HDLam2 hd1) (HDLam2 hd2) = HDLam2 (ds-lem-ap hd1 hd2)
  ds-lem-ap (HDAp hd1 hd2) (HDAp hd3 hd4) = HDAp (ds-lem-ap hd1 hd3) (ds-lem-ap hd2 hd4)
  ds-lem-ap (HDInl hd) (HDInl ν) = HDInl (ds-lem-ap hd ν)
  ds-lem-ap (HDInr hd) (HDInr ν) = HDInr (ds-lem-ap hd ν)
  ds-lem-ap (HDCase hd hd₁ hd₂) (HDCase ν ν₁ ν₂) = HDCase (ds-lem-ap hd ν) (ds-lem-ap hd₁ ν₁) (ds-lem-ap hd₂ ν₂)
  ds-lem-ap (HDHole x) (HDHole x₁) = HDHole (HNAp x x₁)
  ds-lem-ap (HDNEHole x hd1) (HDNEHole x₁ hd2) = HDNEHole (HNAp x x₁) (ds-lem-ap hd1 hd2)

  ds-lem-inl : ∀{e1 e2} → holes-disjoint e2 e1 → holes-disjoint e2 (inl e1)
  ds-lem-inl HDNum = HDNum
  ds-lem-inl (HDPlus hd hd₁) = HDPlus (ds-lem-inl hd) (ds-lem-inl hd₁)
  ds-lem-inl (HDAsc hd) = HDAsc (ds-lem-inl hd)
  ds-lem-inl HDVar = HDVar
  ds-lem-inl (HDLam1 hd) = HDLam1 (ds-lem-inl hd)
  ds-lem-inl (HDLam2 hd) = HDLam2 (ds-lem-inl hd)
  ds-lem-inl (HDAp hd hd₁) = HDAp (ds-lem-inl hd) (ds-lem-inl hd₁)
  ds-lem-inl (HDInl hd) = HDInl (ds-lem-inl hd)
  ds-lem-inl (HDInr hd) = HDInr (ds-lem-inl hd)
  ds-lem-inl (HDCase hd hd₁ hd₂) = HDCase (ds-lem-inl hd) (ds-lem-inl hd₁) (ds-lem-inl hd₂)
  ds-lem-inl (HDHole x) = HDHole (HNInl x)
  ds-lem-inl (HDNEHole x hd) = HDNEHole (HNInl x) (ds-lem-inl hd)

  ds-lem-inr : ∀{e1 e2} → holes-disjoint e2 e1 → holes-disjoint e2 (inr e1)
  ds-lem-inr HDNum = HDNum
  ds-lem-inr (HDPlus hd hd₁) = HDPlus (ds-lem-inr hd) (ds-lem-inr hd₁)
  ds-lem-inr (HDAsc hd) = HDAsc (ds-lem-inr hd)
  ds-lem-inr HDVar = HDVar
  ds-lem-inr (HDLam1 hd) = HDLam1 (ds-lem-inr hd)
  ds-lem-inr (HDLam2 hd) = HDLam2 (ds-lem-inr hd)
  ds-lem-inr (HDAp hd hd₁) = HDAp (ds-lem-inr hd) (ds-lem-inr hd₁)
  ds-lem-inr (HDInl hd) = HDInl (ds-lem-inr hd)
  ds-lem-inr (HDInr hd) = HDInr (ds-lem-inr hd)
  ds-lem-inr (HDCase hd hd₁ hd₂) = HDCase (ds-lem-inr hd) (ds-lem-inr hd₁) (ds-lem-inr hd₂)
  ds-lem-inr (HDHole x) = HDHole (HNInr x)
  ds-lem-inr (HDNEHole x hd) = HDNEHole (HNInr x) (ds-lem-inr hd)

  ds-lem-case : ∀{e3 e x e1 y e2} → holes-disjoint e3 e → holes-disjoint e3 e1 → holes-disjoint e3 e2 → holes-disjoint e3 (case e x e1 y e2)
  ds-lem-case HDNum HDNum HDNum = HDNum
  ds-lem-case (HDPlus hd hd₁) (HDPlus ν ν₂) (HDPlus ν₁ ν₃) = HDPlus (ds-lem-case hd ν ν₁) (ds-lem-case hd₁ ν₂ ν₃)
  ds-lem-case (HDAsc hd) (HDAsc ν) (HDAsc ν₁) = HDAsc (ds-lem-case hd ν ν₁)
  ds-lem-case HDVar HDVar HDVar = HDVar
  ds-lem-case (HDLam1 hd) (HDLam1 ν) (HDLam1 ν₁) = HDLam1 (ds-lem-case hd ν ν₁)
  ds-lem-case (HDLam2 hd) (HDLam2 ν) (HDLam2 ν₁) = HDLam2 (ds-lem-case hd ν ν₁)
  ds-lem-case (HDAp hd hd₁) (HDAp ν ν₁) (HDAp ν₂ ν₃) = HDAp (ds-lem-case hd ν ν₂) (ds-lem-case hd₁ ν₁ ν₃)
  ds-lem-case (HDInl hd) (HDInl ν) (HDInl ν₁) = HDInl (ds-lem-case hd ν ν₁)
  ds-lem-case (HDInr hd) (HDInr ν) (HDInr ν₁) = HDInr (ds-lem-case hd ν ν₁)
  ds-lem-case (HDCase hd hd₁ hd₂) (HDCase ν ν₁ ν₂) (HDCase ν₃ ν₄ ν₅) = HDCase (ds-lem-case hd ν ν₃) (ds-lem-case hd₁ ν₁ ν₄)
                                                                         (ds-lem-case hd₂ ν₂ ν₅)
  ds-lem-case (HDHole x) (HDHole x₁) (HDHole x₂) = HDHole (HNCase x x₁ x₂)
  ds-lem-case (HDNEHole x hd) (HDNEHole x₁ ν) (HDNEHole x₂ ν₁) = HDNEHole (HNCase x x₁ x₂) (ds-lem-case hd ν ν₁)

  ds-lem-hole : ∀{e u} → hole-name-new e u → holes-disjoint e ⦇-⦈[ u ]
  ds-lem-hole HNNum = HDNum
  ds-lem-hole (HNPlus hnn hnn₁) = HDPlus (ds-lem-hole hnn) (ds-lem-hole hnn₁)
  ds-lem-hole (HNAsc hnn) = HDAsc (ds-lem-hole hnn)
  ds-lem-hole HNVar = HDVar
  ds-lem-hole (HNLam1 hnn) = HDLam1 (ds-lem-hole hnn)
  ds-lem-hole (HNLam2 hnn) = HDLam2 (ds-lem-hole hnn)
  ds-lem-hole (HNAp hnn hnn₁) = HDAp (ds-lem-hole hnn) (ds-lem-hole hnn₁)
  ds-lem-hole (HNInl hnn) = HDInl (ds-lem-hole hnn)
  ds-lem-hole (HNInr hnn) = HDInr (ds-lem-hole hnn)
  ds-lem-hole (HNCase hnn hnn₁ hnn₂) = HDCase (ds-lem-hole hnn) (ds-lem-hole hnn₁) (ds-lem-hole hnn₂)
  ds-lem-hole (HNHole x) = HDHole (HNHole (flip x))
  ds-lem-hole (HNNEHole x hnn) = HDNEHole (HNHole (flip x)) (ds-lem-hole hnn)
  
  ds-lem-nehole : ∀{e e1 u} → holes-disjoint e e1 → hole-name-new e u → holes-disjoint e ⦇⌜ e1 ⌟⦈[ u ]
  ds-lem-nehole HDNum ν = HDNum
  ds-lem-nehole (HDPlus hd hd₁) (HNPlus ν ν₁) = HDPlus (ds-lem-nehole hd ν) (ds-lem-nehole hd₁ ν₁)
  ds-lem-nehole (HDAsc hd) (HNAsc ν) = HDAsc (ds-lem-nehole hd ν)
  ds-lem-nehole HDVar ν = HDVar
  ds-lem-nehole (HDLam1 hd) (HNLam1 ν) = HDLam1 (ds-lem-nehole hd ν)
  ds-lem-nehole (HDLam2 hd) (HNLam2 ν) = HDLam2 (ds-lem-nehole hd ν)
  ds-lem-nehole (HDAp hd hd₁) (HNAp ν ν₁) = HDAp (ds-lem-nehole hd ν) (ds-lem-nehole hd₁ ν₁)
  ds-lem-nehole (HDInl hd) (HNInl ν) = HDInl (ds-lem-nehole hd ν)
  ds-lem-nehole (HDInr hd) (HNInr ν) = HDInr (ds-lem-nehole hd ν)
  ds-lem-nehole (HDCase hd hd₁ hd₂) (HNCase ν ν₁ ν₂) = HDCase (ds-lem-nehole hd ν) (ds-lem-nehole hd₁ ν₁)
                                                         (ds-lem-nehole hd₂ ν₂)
  ds-lem-nehole (HDHole x) (HNHole x₁) = HDHole (HNNEHole (flip x₁) x)
  ds-lem-nehole (HDNEHole x hd) (HNNEHole x₁ ν) = HDNEHole (HNNEHole (flip x₁) x) (ds-lem-nehole hd ν)
  
  -- holes-disjoint is symmetric
  disjoint-sym : ∀{e1 e2} → holes-disjoint e1 e2 → holes-disjoint e2 e1
  disjoint-sym HDNum = ds-lem-num
  disjoint-sym (HDPlus hd hd₁) = ds-lem-plus (disjoint-sym hd) (disjoint-sym hd₁)
  disjoint-sym (HDAsc hd) = ds-lem-asc (disjoint-sym hd)
  disjoint-sym HDVar = ds-lem-var
  disjoint-sym (HDLam1 hd) = ds-lem-lam1 (disjoint-sym hd)
  disjoint-sym (HDLam2 hd) = ds-lem-lam2 (disjoint-sym hd)
  disjoint-sym (HDAp hd hd₁) = ds-lem-ap (disjoint-sym hd) (disjoint-sym hd₁)
  disjoint-sym (HDInl hd) = ds-lem-inl (disjoint-sym hd)
  disjoint-sym (HDInr hd) = ds-lem-inr (disjoint-sym hd)
  disjoint-sym (HDCase hd hd₁ hd₂) = ds-lem-case (disjoint-sym hd) (disjoint-sym hd₁) (disjoint-sym hd₂)
  disjoint-sym (HDHole x) = ds-lem-hole x
  disjoint-sym (HDNEHole x hd) = ds-lem-nehole (disjoint-sym hd) x
  
  -- note that this is false, so holes-disjoint isn't transitive
  -- disjoint-new : ∀{e1 e2 u} → holes-disjoint e1 e2 → hole-name-new e1 u → hole-name-new e2 u

  -- it's also not reflexive, because ⦇-⦈[ u ] isn't hole-disjoint with
  -- itself since refl : u == u; it's also not anti-reflexive, because the
  -- expression c *is* hole-disjoint with itself (albeit vacuously)
