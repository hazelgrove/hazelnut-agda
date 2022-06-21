open import Prelude
open import Nat
open import dynamics-core

module lemmas-consistency where
  -- type consistency is symmetric
  ~sym : {t1 t2 : htyp} → t1 ~ t2 → t2 ~ t1
  ~sym TCRefl = TCRefl
  ~sym TCHole1 = TCHole2
  ~sym TCHole2 = TCHole1
  ~sym TCNEHole1 = TCNEHole2
  ~sym TCNEHole2 = TCNEHole1
  ~sym (TCArr p1 p2) = TCArr (~sym p1) (~sym p2)
  ~sym (TCSum p1 p2) = TCSum (~sym p1) (~sym p2)
  ~sym (TCProd p1 p2) = TCProd (~sym p1) (~sym p2)
  
  -- type consistency isn't transitive
  not-trans : ((t1 t2 t3 : htyp) → t1 ~ t2 → t2 ~ t3 → t1 ~ t3) → ⊥
  not-trans t with t (num ==> num) ⦇-⦈ num TCHole1 TCHole2
  ... | ()

  --  every pair of types is either consistent or not consistent
  ~dec : (t1 t2 : htyp) → ((t1 ~ t2) + (t1 ~̸ t2))
    -- this takes care of all hole cases, so we don't consider them below
  ~dec _ ⦇-⦈ = Inl TCHole1
  ~dec ⦇-⦈ _ = Inl TCHole2
  ~dec num num = Inl TCRefl
  ~dec num (t2 ==> t3) = Inr (λ ())
  ~dec num (t2 ⊕ t3) = Inr (λ ())
  ~dec num (α a) = Inr (λ ())
  ~dec num ⦇⌜ a ⌟⦈ = Inl TCNEHole2
  ~dec (t1 ==> t3) num = Inr (λ ())
  ~dec (t1 ==> t3) (t2 ==> t4)
    with ~dec t1 t2 | ~dec t3 t4
  ... | Inl x | Inl x₁ = Inl (TCArr x x₁)
  ... | Inl x | Inr x₁ = Inr λ{ TCRefl → x₁ TCRefl ; (TCArr x₂ x₃) → x₁ x₃}
  ... | Inr x | w = Inr λ{ TCRefl → x TCRefl ; (TCArr x₁ x₂) → x x₁}
  ~dec (t1 ==> t3) (t2 ⊕ t4) = Inr (λ ())
  ~dec (t1 ==> t3) (α a) = Inr (λ ())
  ~dec (t1 ==> t3) ⦇⌜ a ⌟⦈ = Inl TCNEHole2
  ~dec (t1 ⊕ t3) num = Inr (λ ())
  ~dec (t1 ⊕ t3) (t2 ==> t4) = Inr (λ ())
  ~dec (t1 ⊕ t3) (t2 ⊕ t4)
    with ~dec t1 t2 | ~dec t3 t4
  ... | Inl x | Inl x₁ = Inl (TCSum x x₁)
  ... | Inl x | Inr x₁ = Inr λ{ TCRefl → x₁ TCRefl ; (TCSum x₂ x₃) → x₁ x₃}
  ... | Inr x | w = Inr λ{ TCRefl → x TCRefl ; (TCSum x₁ x₂) → x x₁}
  ~dec (t1 ⊕ t3) (α a) = Inr (λ ())
  ~dec (t1 ⊕ t3) ⦇⌜ a ⌟⦈ = Inl TCNEHole2
  ~dec num (t2 ⊠ t4) = Inr (λ ())
  ~dec (t1 ==> t3) (t2 ⊠ t4) = Inr (λ ())
  ~dec (t1 ⊕ t3) (t2 ⊠ t4) = Inr (λ ())
  ~dec (t1 ⊠ t3) num = Inr (λ ())
  ~dec (t1 ⊠ t3) (t2 ==> t4) = Inr (λ ())
  ~dec (t1 ⊠ t3) (t2 ⊕ t4) = Inr (λ ())
  ~dec (t1 ⊠ t3) (t2 ⊠ t4)
    with ~dec t1 t2 | ~dec t3 t4
  ... | Inl x | Inl x₁ = Inl (TCProd x x₁)
  ... | Inl x | Inr x₁ = Inr λ{ TCRefl → x₁ TCRefl ; (TCProd x₂ x₃) → x₁ x₃}
  ... | Inr x | w = Inr λ{ TCRefl → x TCRefl ; (TCProd x₁ x₂) → x x₁}
  ~dec (t1 ⊠ t3) (α a) = Inr (λ ())
  ~dec (t1 ⊠ t3) ⦇⌜ a ⌟⦈ = Inl TCNEHole2
  ~dec (α a) num = Inr (λ ())
  ~dec (α a) (t2 ==> t4) = Inr (λ ())
  ~dec (α a) (t2 ⊕ t4) = Inr (λ ())
  ~dec (α a) (t2 ⊠ t4) = Inr (λ ())
  ~dec (α a) (α a')
    with natEQ a a'
  ... | Inl refl = Inl TCRefl
  ... | Inr a≢a' = Inr λ { TCRefl → a≢a' refl }
  ~dec (α a) ⦇⌜ a' ⌟⦈ = Inl TCNEHole2
  ~dec ⦇⌜ a ⌟⦈ _ = Inl TCNEHole1
  
  -- if arrows are consistent, their components are consistent
  ~arr : ∀{τ1 τ2 τ3 τ4} →
         (τ1 ==> τ2) ~ (τ3 ==> τ4) →
         (τ1 ~ τ3) × (τ2 ~ τ4)
  ~arr TCRefl = TCRefl , TCRefl
  ~arr (TCArr con con₁) = con , con₁
  
  -- if sums are consistent, their components are consistent
  ~sum : ∀{τ1 τ2 τ3 τ4} →
         (τ1 ⊕ τ2) ~ (τ3 ⊕ τ4) →
         (τ1 ~ τ3) × (τ2 ~ τ4)
  ~sum TCRefl = TCRefl , TCRefl
  ~sum (TCSum con con₁) = con , con₁

   -- if products are consistent, their components are consistent
  ~prod : ∀{τ1 τ2 τ3 τ4} →
          (τ1 ⊠ τ2) ~ (τ3 ⊠ τ4) →
          (τ1 ~ τ3) × (τ2 ~ τ4)
  ~prod TCRefl = TCRefl , TCRefl
  ~prod (TCProd con con₁) = con , con₁
