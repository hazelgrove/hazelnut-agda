open import Prelude
open import Nat
open import dynamics-core
open import contexts
open import lemmas-disjointness

module exchange where
  -- exchanging just two disequal elements produces the same context
  swap-little : {A : Set} {x y : Nat} {τ1 τ2 : A} → (x ≠ y) →
    ((■ (x , τ1)) ,, (y , τ2)) == ((■ (y , τ2)) ,, (x , τ1))
  swap-little {A} {x} {y} {τ1} {τ2} neq = ∪comm (■ (y , τ2))
                                                (■ (x , τ1))
                                                (disjoint-singles (flip neq))

  -- really the dynamics-core of all the exchange arguments: contexts with two
  -- disequal elements exchanged are the same. we reassociate the unions,
  -- swap as above, and then associate them back.
  --
  -- note that this is generic in the contents of the context. the proofs
  -- below show the exchange properties that we actually need in the
  -- various other proofs; the remaning exchange properties for both Δ and
  -- Γ positions for all the other hypothetical judgements are exactly in
  -- this pattern.
  swap : {A : Set} {x y : Nat} {τ1 τ2 : A} (Γ : A ctx) (x≠y : x == y → ⊥) →
         ((Γ ,, (x , τ1)) ,, (y , τ2)) == ((Γ ,, (y , τ2)) ,, (x , τ1))
  swap {A} {x} {y} {τ1} {τ2} Γ neq = funext eq
    where
      eq : (z : Nat) →  ((Γ ,, (x , τ1)) ,, (y , τ2)) z == ((Γ ,, (y , τ2)) ,, (x , τ1)) z
      eq z with natEQ y z
      ... | Inr y≠z with natEQ x z
      ... | Inl refl = refl
      ... | Inr x≠z with natEQ y z
      ... | Inl refl = abort (y≠z refl)
      ... | Inr y≠z' = refl
      eq z | Inl refl with natEQ x z
      ... | Inl refl = abort (neq refl)
      ... | Inr x≠z with natEQ z z
      ... | Inl refl = refl
      ... | Inr z≠z = abort (z≠z refl)

                       
                        
  -- (∪assoc Γ (■ (x , τ1)) (■ (y , τ2)) (disjoint-singles neq)) ·
  --                       (ap1 (λ qq → Γ ∪ qq) (swap-little neq) ·
  -- the above exchange principle used via transport in the judgements we needed
  exchange-subst-Γ : ∀{Δ Γ x y τ1 τ2 σ Γ'} →
                   x ≠ y →
                   Δ , (Γ ,, (x , τ1) ,, (y , τ2)) ⊢ σ :s: Γ' →
                   Δ , (Γ ,, (y , τ2) ,, (x , τ1)) ⊢ σ :s: Γ'
  exchange-subst-Γ {Δ} {Γ} {x} {y} {τ1} {τ2} {σ} {Γ'} x≠y =
    tr (λ qq → Δ , qq ⊢ σ :s: Γ') (swap Γ x≠y)

  exchange-synth : ∀{Γ x y τ τ1 τ2 e}
                       → x ≠ y
                       → (Γ ,, (x , τ1) ,, (y , τ2)) ⊢ e => τ
                       → (Γ ,, (y , τ2) ,, (x , τ1)) ⊢ e => τ
  exchange-synth {Γ} {x} {y} {τ} {τ1} {τ2} {e} neq  =
    tr (λ qq → qq ⊢ e => τ) (swap Γ neq)

  exchange-ana : ∀{Γ x y τ τ1 τ2 e}
                       → x ≠ y
                       → (Γ ,, (x , τ1) ,, (y , τ2)) ⊢ e <= τ
                       → (Γ ,, (y , τ2) ,, (x , τ1)) ⊢ e <= τ
  exchange-ana {Γ} {x} {y} {τ} {τ1} {τ2} {e} neq  =
    tr (λ qq → qq ⊢ e <= τ) (swap Γ neq)

  exchange-elab-synth : ∀{Γ x y τ1 τ2 e τ d Δ} →
                        x ≠ y →
                        (Γ ,, (x , τ1) ,, (y , τ2)) ⊢ e ⇒ τ ~> d ⊣ Δ →
                        (Γ ,, (y , τ2) ,, (x , τ1)) ⊢ e ⇒ τ ~> d ⊣ Δ
  exchange-elab-synth {Γ = Γ} {e = e} {τ = τ} {d = d } {Δ = Δ} neq =
    tr (λ qq → qq ⊢ e ⇒ τ ~> d ⊣ Δ) (swap Γ neq)

  exchange-elab-ana : ∀ {Γ x y τ1 τ2 τ τ' d e Δ} →
                      x ≠ y →
                      (Γ ,, (x , τ1) ,, (y , τ2)) ⊢ e ⇐ τ ~> d :: τ' ⊣ Δ →
                      (Γ ,, (y , τ2) ,, (x , τ1)) ⊢ e ⇐ τ ~> d :: τ' ⊣ Δ
  exchange-elab-ana {Γ = Γ} {τ = τ} {τ' = τ'} {d = d} {e = e} {Δ = Δ} neq =
    tr (λ qq → qq ⊢ e ⇐ τ ~> d :: τ' ⊣ Δ) (swap Γ neq)

  exchange-ta-Γ : ∀{Γ x y τ1 τ2 d τ Δ } →
                  x ≠ y →
                  Δ , (Γ ,, (x , τ1) ,, (y , τ2)) ⊢ d :: τ →
                  Δ , (Γ ,, (y , τ2) ,, (x , τ1)) ⊢ d :: τ
  exchange-ta-Γ {Γ = Γ} {d = d} {τ = τ} {Δ = Δ} neq =
    tr (λ qq → Δ , qq ⊢ d :: τ) (swap Γ neq)
