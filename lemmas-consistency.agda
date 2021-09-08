open import Prelude
open import core

module lemmas-consistency where
  -- type consistency is symmetric
  ~sym : {t1 t2 : htyp} → t1 ~ t2 → t2 ~ t1
  ~sym TCRefl = TCRefl
  ~sym TCHole1 = TCHole2
  ~sym TCHole2 = TCHole1
  ~sym (TCArr p1 p2) = TCArr (~sym p1) (~sym p2)

  -- type consistency isn't transitive
  not-trans : ((t1 t2 t3 : htyp) → t1 ~ t2 → t2 ~ t3 → t1 ~ t3) → ⊥
  not-trans t with t (num ==> num) ⦇-⦈ num TCHole1 TCHole2
  ... | ()

  --  every pair of types is either consistent or not consistent
  ~dec : (t1 t2 : htyp) → ((t1 ~ t2) + (t1 ~̸ t2))
    -- this takes care of all hole cases, so we don't consider them below
  ~dec _ ⦇-⦈ = Inl TCHole1
  ~dec ⦇-⦈ _ = Inl TCHole2
    -- num cases
  ~dec num num = Inl TCRefl
  ~dec num (t2 ==> t3) = Inr λ ()
    -- arrow cases
  ~dec (t1 ==> t2) num = Inr λ ()
  ~dec (t1 ==> t2) (t3 ==> t4) with ~dec t1 t3 | ~dec t2 t4
  ... | Inl x | Inl y = Inl (TCArr x y)
  ... | Inl _ | Inr y = Inr λ{ TCRefl → y TCRefl ; (TCArr x₁ x₂) → y x₂}
  ... | Inr x | _     = Inr λ{ TCRefl → x TCRefl ; (TCArr x₁ x₂) → x x₁}
