open import Nat
open import Prelude
open import contexts
open import core

module dynamics-core where
  open core public
  
  mutual
    -- identity substitution, substitition environments
    data env : Set where
      Id    : (Γ : tctx) → env
      Subst : (d : ihexp) → (y : Nat) → env → env

    -- internal expressions
    data ihexp : Set where
      N          : Nat → ihexp
      _·+_       : ihexp → ihexp → ihexp
      X          : Nat → ihexp
      ·λ_·[_]_   : Nat → htyp → ihexp → ihexp
      _∘_        : ihexp → ihexp → ihexp
      inl        : htyp → ihexp → ihexp
      inr        : htyp → ihexp → ihexp
      case       : ihexp → Nat → ihexp → Nat → ihexp → ihexp
      ⟨_,_⟩      : ihexp → ihexp → ihexp
      fst        : ihexp → ihexp
      snd        : ihexp → ihexp
      ⦇-⦈⟨_⟩     : (Nat × env) → ihexp
      ⦇⌜_⌟⦈⟨_⟩   : ihexp → (Nat × env) → ihexp
      _⟨_⇒_⟩     : ihexp → htyp → htyp → ihexp
      _⟨_⇒⦇-⦈⇏_⟩ : ihexp → htyp → htyp → ihexp

  -- convenient notation for chaining together two agreeable casts
  _⟨_⇒_⇒_⟩ : ihexp → htyp → htyp → htyp → ihexp
  d ⟨ t1 ⇒ t2 ⇒ t3 ⟩ = d ⟨ t1 ⇒ t2 ⟩ ⟨ t2 ⇒ t3 ⟩
  
  -- notation for a triple to match the CMTT syntax
  _::_[_] : Nat → htyp → tctx → (Nat × (tctx × htyp))
  u :: τ [ Γ ] = u , (Γ , τ)

    -- the hole name u does not appear in the term e
  data hole-name-new : hexp → Nat → Set where
    HNNum  : ∀{n u} → hole-name-new (N n) u
    HNPlus : ∀{e1 e2 u} →
             hole-name-new e1 u →
             hole-name-new e2 u →
             hole-name-new (e1 ·+ e2) u
    HNAsc  : ∀{e τ u} →
             hole-name-new e u →
             hole-name-new (e ·: τ) u
    HNVar  : ∀{x u} → hole-name-new (X x) u
    HNLam1 : ∀{x e u} →
             hole-name-new e u →
             hole-name-new (·λ x e) u
    HNLam2 : ∀{x e u τ} →
             hole-name-new e u →
             hole-name-new (·λ x ·[ τ ] e) u
    HNAp   : ∀{e1 e2 u} →
             hole-name-new e1 u →
             hole-name-new e2 u →
             hole-name-new (e1 ∘ e2) u
    HNInl  : ∀{e u} →
             hole-name-new e u →
             hole-name-new (inl e) u
    HNInr  : ∀{e u} →
             hole-name-new e u →
             hole-name-new (inr e) u
    HNCase : ∀{e x e1 y e2 u} →
             hole-name-new e u →
             hole-name-new e1 u →
             hole-name-new e2 u →
             hole-name-new (case e x e1 y e2) u
    HNPair : ∀{e1 e2 u} →
             hole-name-new e1 u →
             hole-name-new e2 u →
             hole-name-new ⟨ e1 , e2 ⟩ u       
    HNFst  : ∀{e u} →
             hole-name-new e u →
             hole-name-new (fst e) u
    HNSnd  : ∀{e u} →
             hole-name-new e u →
             hole-name-new (snd e) u
    HNHole : ∀{u u'} →
             u' ≠ u →
             hole-name-new (⦇-⦈[ u' ]) u
    HNNEHole : ∀{u u' e} →
               u' ≠ u →
               hole-name-new e u →
               hole-name-new (⦇⌜ e ⌟⦈[ u' ]) u

  -- two terms that do not share any hole names
  data holes-disjoint : hexp → hexp → Set where
    HDNum  : ∀{n e} → holes-disjoint (N n) e
    HDPlus : ∀{e1 e2 e3} →
             holes-disjoint e1 e3 →
             holes-disjoint e2 e3 →
             holes-disjoint (e1 ·+ e2) e3
    HDAsc  : ∀{e1 e2 τ} →
             holes-disjoint e1 e2 →
             holes-disjoint (e1 ·: τ) e2
    HDVar  : ∀{x e} → holes-disjoint (X x) e
    HDLam1 : ∀{x e1 e2} →
             holes-disjoint e1 e2 →
             holes-disjoint (·λ x e1) e2
    HDLam2 : ∀{x e1 e2 τ} →
             holes-disjoint e1 e2 →
             holes-disjoint (·λ x ·[ τ ] e1) e2
    HDAp   : ∀{e1 e2 e3} →
             holes-disjoint e1 e3 →
             holes-disjoint e2 e3 →
             holes-disjoint (e1 ∘ e2) e3
    HDInl  : ∀{e1 e2} →
             holes-disjoint e1 e2 →
             holes-disjoint (inl e1) e2
    HDInr  : ∀{e1 e2} →
             holes-disjoint e1 e2 →
             holes-disjoint (inr e1) e2
    HDCase : ∀{e x e1 y e2 e3} →
             holes-disjoint e e3 →
             holes-disjoint e1 e3 →
             holes-disjoint e2 e3 →
             holes-disjoint (case e x e1 y e2) e3
    HDPair : ∀{e1 e2 e3} →
             holes-disjoint e1 e3 →
             holes-disjoint e2 e3 →
             holes-disjoint ⟨ e1 , e2 ⟩ e3
    HDFst  : ∀{e1 e2} →
             holes-disjoint e1 e2 →
             holes-disjoint (fst e1) e2
    HDSnd  : ∀{e1 e2} →
             holes-disjoint e1 e2 →
             holes-disjoint (snd e1) e2
    HDHole : ∀{u e2} →
             hole-name-new e2 u →
             holes-disjoint (⦇-⦈[ u ]) e2
    HDNEHole : ∀{u e1 e2} →
               hole-name-new e2 u →
               holes-disjoint e1 e2 →
               holes-disjoint (⦇⌜ e1 ⌟⦈[ u ]) e2

  -- all hole names in the term are unique
  data holes-unique : hexp → Set where
    HUNum  : ∀{n} →
             holes-unique (N n)
    HUPlus : ∀{e1 e2} →
             holes-unique e1 →
             holes-unique e2 →
             holes-disjoint e1 e2 →
             holes-unique (e1 ·+ e2)
    HUAsc  : ∀{e τ} →
             holes-unique e →
             holes-unique (e ·: τ)
    HUVar  : ∀{x} →
             holes-unique (X x)
    HULam1 : ∀{x e} →
             holes-unique e →
             holes-unique (·λ x e)
    HULam2 : ∀{x e τ} →
             holes-unique e →
             holes-unique (·λ x ·[ τ ] e)
    HUAp   : ∀{e1 e2} →
             holes-unique e1 →
             holes-unique e2 →
             holes-disjoint e1 e2 →
             holes-unique (e1 ∘ e2)
    HUInl  : ∀{e} →
             holes-unique e →
             holes-unique (inl e)
    HUInr  : ∀{e} →
             holes-unique e →
             holes-unique (inr e)
    HUCase : ∀{e x e1 y e2} →
             holes-unique e →
             holes-unique e1 →
             holes-unique e2 →
             holes-disjoint e e1 →
             holes-disjoint e e2 →
             holes-disjoint e1 e2 →
             holes-unique (case e x e1 y e2)
    HUPair : ∀{e1 e2} →
             holes-unique e1 →
             holes-unique e2 →
             holes-disjoint e1 e2 →
             holes-unique ⟨ e1 , e2 ⟩
    HUFst  : ∀{e} →
             holes-unique e →
             holes-unique (fst e)
    HUSnd  : ∀{e} →
             holes-unique e →
             holes-unique (snd e)
    HUHole : ∀{u} →
             holes-unique (⦇-⦈[ u ])
    HUNEHole : ∀{u e} →
               holes-unique e →
               hole-name-new e u →
               holes-unique (⦇⌜ e ⌟⦈[ u ])
               
  -- freshness for external expressions
  data freshh : Nat → hexp → Set where
    FRHNum    : ∀{x n} →
                freshh x (N n)
    FRHPlus   : ∀{x d1 d2} →
                freshh x d1 →
                freshh x d2 →
                freshh x (d1 ·+ d2)
    FRHAsc    : ∀{x e τ} →
                freshh x e →
                freshh x (e ·: τ)
    FRHVar    : ∀{x y} →
                x ≠ y →
                freshh x (X y)
    FRHLam1   : ∀{x y e} →
                x ≠ y →
                freshh x e →
                freshh x (·λ y e)
    FRHLam2   : ∀{x τ e y} →
                x ≠ y →
                freshh x e →
                freshh x (·λ y ·[ τ ] e)
    FRHAp     : ∀{x e1 e2} →
                freshh x e1 →
                freshh x e2 →
                freshh x (e1 ∘ e2)
    FRHInl    : ∀{x d} →
                freshh x d →
                freshh x (inl d)
    FRHInr    : ∀{x d} →
                freshh x d →
                freshh x (inr d)
    FRHCase   : ∀{x d y d1 z d2} →
                freshh x d →
                x ≠ y →
                freshh x d1 →
                x ≠ z →
                freshh x d2 →
                freshh x (case d y d1 z d2)
    FRHPair   : ∀{x d1 d2} →
                freshh x d1 →
                freshh x d2 →
                freshh x ⟨ d1 , d2 ⟩
    FRHFst    : ∀{x d} →
                freshh x d →
                freshh x (fst d)
    FRHSnd    : ∀{x d} →
                freshh x d →
                freshh x (snd d)
    FRHEHole  : ∀{x u} →
                freshh x (⦇-⦈[ u ])
    FRHNEHole : ∀{x u e} →
                freshh x e →
                freshh x (⦇⌜ e ⌟⦈[ u ])
                
  -- those internal expressions without holes
  data _dcomplete : ihexp → Set where
    DCNum  : ∀{n} →
             (N n) dcomplete
    DCPlus : ∀{d1 d2} →
             d1 dcomplete →
             d2 dcomplete →
             (d1 ·+ d2) dcomplete
    DCVar  : ∀{x} →
             (X x) dcomplete
    DCLam  : ∀{x τ d} →
             d dcomplete →
             τ tcomplete →
             (·λ x ·[ τ ] d) dcomplete
    DCAp   : ∀{d1 d2} →
             d1 dcomplete →
             d2 dcomplete →
             (d1 ∘ d2) dcomplete
    DCInl  : ∀{τ d} →
             τ tcomplete →
             d dcomplete →
             (inl τ d) dcomplete
    DCInr  : ∀{τ d} →
             τ tcomplete →
             d dcomplete →
             (inr τ d) dcomplete
    DCCase : ∀{d x d1 y d2} →
             d dcomplete →
             d1 dcomplete →
             d2 dcomplete →
             (case d x d1 y d2) dcomplete
    DCPair : ∀{d1 d2} →
             d1 dcomplete →
             d2 dcomplete →
             ⟨ d1 , d2 ⟩ dcomplete
    DCFst  : ∀{d} →
             d dcomplete →
             (fst d) dcomplete
    DCSnd  : ∀{d} →
             d dcomplete →
             (snd d) dcomplete
    DCCast : ∀{d τ1 τ2} →
             d dcomplete →
             τ1 tcomplete →
             τ2 tcomplete →
             (d ⟨ τ1 ⇒ τ2 ⟩) dcomplete

  -- expansion
  mutual
    -- synthesis
    data _⊢_⇒_~>_⊣_ : (Γ : tctx) (e : hexp) (τ : htyp) (d : ihexp) (Δ : hctx) → Set where
      ESNum    : ∀{Γ n} →
                 Γ ⊢ (N n) ⇒ num ~> (N n) ⊣ ∅
      ESPlus   : ∀{Γ e1 e2 d1 d2 Δ1 Δ2 τ1 τ2} →
                 holes-disjoint e1 e2 →
                 Δ1 ## Δ2 →
                 Γ ⊢ e1 ⇐ num ~> d1 :: τ1 ⊣ Δ1 →
                 Γ ⊢ e2 ⇐ num ~> d2 :: τ2 ⊣ Δ2 →
                 Γ ⊢ e1 ·+ e2 ⇒ num ~> (d1 ⟨ τ1 ⇒ num ⟩) ·+ (d2 ⟨ τ2 ⇒ num ⟩) ⊣ (Δ1 ∪ Δ2)
      ESAsc    : ∀{Γ e τ d τ' Δ} →
                 Γ ⊢ e ⇐ τ ~> d :: τ' ⊣ Δ →
                 Γ ⊢ (e ·: τ) ⇒ τ ~> d ⟨ τ' ⇒ τ ⟩ ⊣ Δ
      ESVar    : ∀{Γ x τ} →
                 (x , τ) ∈ Γ →
                 Γ ⊢ X x ⇒ τ ~> X x ⊣ ∅
      ESLam    : ∀{Γ x τ1 τ2 e d Δ} →
                 x # Γ →
                 (Γ ,, (x , τ1)) ⊢ e ⇒ τ2 ~> d ⊣ Δ →
                 Γ ⊢ ·λ x ·[ τ1 ] e ⇒ (τ1 ==> τ2) ~> ·λ x ·[ τ1 ] d ⊣ Δ
      ESAp     : ∀{Γ e1 τ τ1 τ1' τ2 τ2' d1 Δ1 e2 d2 Δ2} →
                 holes-disjoint e1 e2 →
                 Δ1 ## Δ2 →
                 Γ ⊢ e1 => τ1 →
                 τ1 ▸arr τ2 ==> τ →
                 Γ ⊢ e1 ⇐ (τ2 ==> τ) ~> d1 :: τ1' ⊣ Δ1 →
                 Γ ⊢ e2 ⇐ τ2 ~> d2 :: τ2' ⊣ Δ2 →
                 Γ ⊢ e1 ∘ e2 ⇒ τ ~> (d1 ⟨ τ1' ⇒ τ2 ==> τ ⟩) ∘ (d2 ⟨ τ2' ⇒ τ2 ⟩) ⊣ (Δ1 ∪ Δ2)
      ESPair   : ∀{Γ e1 τ1 d1 Δ1 e2 τ2 d2 Δ2} →
                 holes-disjoint e1 e2 →
                 Δ1 ## Δ2 →
                 Γ ⊢ e1 ⇒ τ1 ~> d1 ⊣ Δ1 →
                 Γ ⊢ e2 ⇒ τ2 ~> d2 ⊣ Δ2 →
                 Γ ⊢ ⟨ e1 , e2 ⟩ ⇒ τ1 ⊠ τ2 ~> ⟨ d1 , d2 ⟩ ⊣ (Δ1 ∪ Δ2)
      ESFst    : ∀{Γ e τ τ' d τ1 τ2 Δ} →
                 Γ ⊢ e => τ →
                 τ ▸prod τ1 ⊠ τ2 →
                 Γ ⊢ e ⇐ τ1 ⊠ τ2 ~> d :: τ' ⊣ Δ →
                 Γ ⊢ fst e ⇒ τ1 ~> fst (d ⟨ τ' ⇒ τ1 ⊠ τ2 ⟩) ⊣ Δ
      ESSnd    : ∀{Γ e τ τ' d τ1 τ2 Δ} →
                 Γ ⊢ e => τ →
                 τ ▸prod τ1 ⊠ τ2 →
                 Γ ⊢ e ⇐ τ1 ⊠ τ2 ~> d :: τ' ⊣ Δ →
                 Γ ⊢ snd e ⇒ τ2 ~> snd (d ⟨ τ' ⇒ τ1 ⊠ τ2 ⟩) ⊣ Δ
      ESEHole  : ∀{Γ u} →
                 Γ ⊢ ⦇-⦈[ u ] ⇒ ⦇-⦈ ~> ⦇-⦈⟨ u , Id Γ ⟩ ⊣  ■ (u :: ⦇-⦈ [ Γ ])
      ESNEHole : ∀{Γ e τ d u Δ} →
                 Δ ## (■ (u , Γ , ⦇-⦈)) →
                 Γ ⊢ e ⇒ τ ~> d ⊣ Δ →
                 Γ ⊢ ⦇⌜ e ⌟⦈[ u ] ⇒ ⦇-⦈ ~> ⦇⌜ d ⌟⦈⟨ u , Id Γ  ⟩ ⊣ (Δ ,, u :: ⦇-⦈ [ Γ ])
      

    -- analysis
    data _⊢_⇐_~>_::_⊣_ : (Γ : tctx) (e : hexp) (τ : htyp)
                         (d : ihexp) (τ' : htyp) (Δ : hctx) → Set where
      EASubsume : ∀{e Γ τ' d Δ τ} →
                  ((u : Nat) → e ≠ ⦇-⦈[ u ]) →
                  ((e' : hexp) (u : Nat) → e ≠ ⦇⌜ e' ⌟⦈[ u ]) →
                  Γ ⊢ e ⇒ τ' ~> d ⊣ Δ →
                  τ ~ τ' →
                  Γ ⊢ e ⇐ τ ~> d :: τ' ⊣ Δ
      EALam     : ∀{Γ x τ τ1 τ2 e d τ2' Δ} →
                  x # Γ →
                  τ ▸arr τ1 ==> τ2 →
                  (Γ ,, (x , τ1)) ⊢ e ⇐ τ2 ~> d :: τ2' ⊣ Δ →
                  Γ ⊢ ·λ x e ⇐ τ ~> ·λ x ·[ τ1 ] d :: τ1 ==> τ2' ⊣ Δ
      EAInl     : ∀{Γ τ τ1 τ2 e d τ1' Δ} →
                  τ ▸sum τ1 ⊕ τ2 →
                  Γ ⊢ e ⇐ τ1 ~> d :: τ1' ⊣ Δ →
                  Γ ⊢ inl e ⇐ τ ~> inl τ2 d :: τ1' ⊕ τ2 ⊣ Δ
      EAInr     : ∀{Γ τ τ1 τ2 e d τ2' Δ} →
                  τ ▸sum τ1 ⊕ τ2 →
                  Γ ⊢ e ⇐ τ2 ~> d :: τ2' ⊣ Δ →
                  Γ ⊢ inr e ⇐ τ ~> inr τ1 d :: τ1 ⊕ τ2' ⊣ Δ
      EACase    : ∀{Γ e τ+ d Δ τ1 τ2 τ x e1 d1 τr1 Δ1 y e2 d2 τr2 Δ2} →
                  holes-disjoint e e1 →
                  holes-disjoint e e2 →
                  holes-disjoint e1 e2 →
                  Δ ## Δ1 →
                  Δ ## Δ2 →
                  Δ1 ## Δ2 →
                  x # Γ →
                  y # Γ →
                  Γ ⊢ e ⇒ τ+ ~> d ⊣ Δ →
                  τ+ ▸sum τ1 ⊕ τ2 →
                  (Γ ,, (x , τ1)) ⊢ e1 ⇐ τ ~> d1 :: τr1 ⊣ Δ1 →
                  (Γ ,, (y , τ2)) ⊢ e2 ⇐ τ ~> d2 :: τr2 ⊣ Δ2 →
                  Γ ⊢ case e x e1 y e2 ⇐ τ ~>
                    case (d ⟨ τ+ ⇒ τ1 ⊕ τ2 ⟩) x (d1 ⟨ τr1 ⇒ τ ⟩) y (d2 ⟨ τr2 ⇒ τ ⟩) :: τ
                      ⊣ (Δ ∪ (Δ1 ∪ Δ2))
      EAEHole   : ∀{Γ u τ} →
                  Γ ⊢ ⦇-⦈[ u ] ⇐ τ ~> ⦇-⦈⟨ u , Id Γ  ⟩ :: τ ⊣ ■ (u :: τ [ Γ ])
      EANEHole  : ∀{Γ e u τ d τ' Δ} →
                  Δ ## (■ (u , Γ , τ)) →
                  Γ ⊢ e ⇒ τ' ~> d ⊣ Δ →
                  Γ ⊢ ⦇⌜ e ⌟⦈[ u ] ⇐ τ ~> ⦇⌜ d ⌟⦈⟨ u , Id Γ  ⟩ :: τ ⊣ (Δ ,, u :: τ [ Γ ])

  mutual
    -- substitution typing
    data _,_⊢_:s:_ : hctx → tctx → env → tctx → Set where
      STAId    : ∀{Γ Γ' Δ} →
                 ((x : Nat) (τ : htyp) →
                 (x , τ) ∈ Γ' → (x , τ) ∈ Γ) →
                 Δ , Γ ⊢ Id Γ' :s: Γ'
      STASubst : ∀{Γ Δ σ y Γ' d τ} →
                 Δ , Γ ,, (y , τ) ⊢ σ :s: Γ' →
                 Δ , Γ ⊢ d :: τ →
                 Δ , Γ ⊢ Subst d y σ :s: Γ'

    -- type assignment
    data _,_⊢_::_ : (Δ : hctx) (Γ : tctx) (d : ihexp) (τ : htyp) → Set where
      TANum    : ∀{Δ Γ n} →
                 Δ , Γ ⊢ (N n) :: num
      TAPlus   : ∀{Δ Γ d1 d2} →
                 Δ , Γ ⊢ d1 :: num →
                 Δ , Γ ⊢ d2 :: num →
                 Δ , Γ ⊢ (d1 ·+ d2) :: num
      TAVar    : ∀{Δ Γ x τ} →
                 (x , τ) ∈ Γ →
                 Δ , Γ ⊢ X x :: τ
      TALam    : ∀{Δ Γ x τ1 d τ2} →
                 x # Γ →
                 Δ , (Γ ,, (x , τ1)) ⊢ d :: τ2 →
                 Δ , Γ ⊢ ·λ x ·[ τ1 ] d :: (τ1 ==> τ2)
      TAAp     : ∀{Δ Γ d1 d2 τ1 τ} →
                 Δ , Γ ⊢ d1 :: τ1 ==> τ →
                 Δ , Γ ⊢ d2 :: τ1 →
                 Δ , Γ ⊢ d1 ∘ d2 :: τ
      TAInl    : ∀{Δ Γ d τ1 τ2} →
                 Δ , Γ ⊢ d :: τ1 →
                 Δ , Γ ⊢ inl τ2 d :: τ1 ⊕ τ2
      TAInr    : ∀{Δ Γ d τ1 τ2} →
                 Δ , Γ ⊢ d :: τ2 →
                 Δ , Γ ⊢ inr τ1 d :: τ1 ⊕ τ2
      TACase   : ∀{Δ Γ d τ1 τ2 τ x d1 y d2} →
                 Δ , Γ ⊢ d :: τ1 ⊕ τ2 →
                 x # Γ →
                 Δ , (Γ ,, (x , τ1)) ⊢ d1 :: τ →
                 y # Γ →
                 Δ , (Γ ,, (y , τ2)) ⊢ d2 :: τ →
                 Δ , Γ ⊢ case d x d1 y d2 :: τ
      TAPair   : ∀{Δ Γ d1 d2 τ1 τ2} →
                 Δ , Γ ⊢ d1 :: τ1 →
                 Δ , Γ ⊢ d2 :: τ2 →
                 Δ , Γ ⊢ ⟨ d1 , d2 ⟩ :: τ1 ⊠ τ2
      TAFst    : ∀{Δ Γ d τ1 τ2} →
                 Δ , Γ ⊢ d :: τ1 ⊠ τ2 →
                 Δ , Γ ⊢ fst d :: τ1
      TASnd    : ∀{Δ Γ d τ1 τ2} →
                 Δ , Γ ⊢ d :: τ1 ⊠ τ2 →
                 Δ , Γ ⊢ snd d :: τ2
      TAEHole  : ∀{Δ Γ σ u Γ' τ} →
                 (u , (Γ' , τ)) ∈ Δ →
                 Δ , Γ ⊢ σ :s: Γ' →
                 Δ , Γ ⊢ ⦇-⦈⟨ u , σ ⟩ :: τ
      TANEHole : ∀{Δ Γ d τ' Γ' u σ τ} →
                 (u , (Γ' , τ)) ∈ Δ →
                 Δ , Γ ⊢ d :: τ' →
                 Δ , Γ ⊢ σ :s: Γ' →
                 Δ , Γ ⊢ ⦇⌜ d ⌟⦈⟨ u , σ ⟩ :: τ
      TACast   : ∀{Δ Γ d τ1 τ2} →
                 Δ , Γ ⊢ d :: τ1 →
                 τ1 ~ τ2 →
                 Δ , Γ ⊢ d ⟨ τ1 ⇒ τ2 ⟩ :: τ2
      TAFailedCast : ∀{Δ Γ d τ1 τ2} →
                     Δ , Γ ⊢ d :: τ1 →
                     τ1 ground →
                     τ2 ground →
                     τ1 ≠ τ2 →
                     Δ , Γ ⊢ d ⟨ τ1 ⇒⦇-⦈⇏ τ2 ⟩ :: τ2

  -- substitution
  [_/_]_ : ihexp → Nat → ihexp → ihexp
  [ d / y ] (N n) = N n
  [ d / y ] (d1 ·+ d2) = ([ d / y ] d1) ·+ ([ d / y ] d2)
  [ d / y ] X x
    with natEQ x y
  [ d / y ] X .y | Inl refl = d
  [ d / y ] X x  | Inr neq = X x
  [ d / y ] (·λ x ·[ x₁ ] d')
    with natEQ x y
  [ d / y ] (·λ .y ·[ τ ] d') | Inl refl = ·λ y ·[ τ ] d'
  [ d / y ] (·λ x ·[ τ ] d')  | Inr x₁ = ·λ x ·[ τ ] ( [ d / y ] d')
  [ d / y ] (d1 ∘ d2) = ([ d / y ] d1) ∘ ([ d / y ] d2)
  [ d / y ] (inl τ d') = inl τ ([ d / y ] d')
  [ d / y ] (inr τ d') = inr τ ([ d / y ] d')
  [ d / y ] (case d' x d1 z d2)
    with natEQ x y | natEQ z y
  ... | Inl refl | Inl refl = case ([ d / y ] d') x d1 z d2
  ... | Inl refl | Inr neq  = case ([ d / y ] d') x d1 z ([ d / y ] d2)
  ... | Inr neq  | Inl refl = case ([ d / y ] d') x ([ d / y ] d1) z d2
  ... | Inr neq1 | Inr neq2 = case ([ d / y ] d') x ([ d / y ] d1) z ([ d / y ] d2)
  [ d / y ] ⟨ d1 , d2 ⟩ = ⟨ [ d / y ] d1 , [ d / y ] d2 ⟩
  [ d / y ] (fst d') = fst ([ d / y ] d')
  [ d / y ] (snd d') = snd ([ d / y ] d')
  [ d / y ] ⦇-⦈⟨ u , σ ⟩ = ⦇-⦈⟨ u , Subst d y σ ⟩
  [ d / y ] ⦇⌜ d' ⌟⦈⟨ u , σ  ⟩ =  ⦇⌜ [ d / y ] d' ⌟⦈⟨ u , Subst d y σ ⟩
  [ d / y ] (d' ⟨ τ1 ⇒ τ2 ⟩ ) = ([ d / y ] d') ⟨ τ1 ⇒ τ2 ⟩
  [ d / y ] (d' ⟨ τ1 ⇒⦇-⦈⇏ τ2 ⟩ ) = ([ d / y ] d') ⟨ τ1 ⇒⦇-⦈⇏ τ2 ⟩

  -- applying an environment to an expression
  apply-env : env → ihexp → ihexp
  apply-env (Id Γ) d = d
  apply-env (Subst d y σ) d' = [ d / y ] ( apply-env σ d')

  -- values
  data _val : (d : ihexp) → Set where
    VNum  : ∀{n} → (N n) val
    VLam  : ∀{x τ d} → (·λ x ·[ τ ] d) val
    VInl  : ∀{d τ} → d val → (inl τ d) val
    VInr  : ∀{d τ} → d val → (inr τ d) val
    VPair : ∀{d1 d2} → d1 val → d2 val → ⟨ d1 , d2 ⟩ val

  -- boxed values
  data _boxedval : (d : ihexp) → Set where
    BVVal      : ∀{d} →
                 d val →
                 d boxedval
    BVInl      : ∀{d τ} →
                 d boxedval →
                 (inl τ d) boxedval
    BVInr      : ∀{d τ} →
                 d boxedval →
                 (inr τ d) boxedval
    BVPair     : ∀{d1 d2} →
                 d1 boxedval →
                 d2 boxedval →
                 ⟨ d1 , d2 ⟩ boxedval
    BVArrCast  : ∀{d τ1 τ2 τ3 τ4} →
                 τ1 ==> τ2 ≠ τ3 ==> τ4 →
                 d boxedval →
                 d ⟨ (τ1 ==> τ2) ⇒ (τ3 ==> τ4) ⟩ boxedval
    BVSumCast  : ∀{d τ1 τ2 τ3 τ4} →
                 τ1 ⊕ τ2 ≠ τ3 ⊕ τ4 →
                 d boxedval →
                 d ⟨ (τ1 ⊕ τ2) ⇒ (τ3 ⊕ τ4) ⟩ boxedval
    BVProdCast : ∀{d τ1 τ2 τ3 τ4} →
                 τ1 ⊠ τ2 ≠ τ3 ⊠ τ4 →
                 d boxedval →
                 d ⟨ (τ1 ⊠ τ2) ⇒ (τ3 ⊠ τ4) ⟩ boxedval
    BVHoleCast : ∀{τ d} →
                 τ ground →
                 d boxedval →
                 d ⟨ τ ⇒ ⦇-⦈ ⟩ boxedval
    
  mutual
    -- indeterminate forms
    data _indet : (d : ihexp) → Set where
      IPlus1    : ∀{d1 d2} →
                  d1 indet →
                  d2 final →
                  (d1 ·+ d2) indet
      IPlus2    : ∀{d1 d2} →
                  d1 final →
                  d2 indet →
                  (d1 ·+ d2) indet
      IAp       : ∀{d1 d2} →
                  ((τ1 τ2 τ3 τ4 : htyp) (d1' : ihexp) →
                    d1 ≠ (d1' ⟨(τ1 ==> τ2) ⇒ (τ3 ==> τ4)⟩)) →
                  d1 indet →
                  d2 final →
                  (d1 ∘ d2) indet
      IInl      : ∀{d τ} →
                  d indet →
                  (inl τ d) indet
      IInr      : ∀{d τ} →
                  d indet →
                  (inr τ d) indet
      ICase     : ∀{d x d1 y d2} →
                  ((τ : htyp) (d' : ihexp) →
                    d ≠ inl τ d') →
                  ((τ : htyp) (d' : ihexp) →
                    d ≠ inr τ d') →
                  ((τ1 τ2 τ1' τ2' : htyp) (d' : ihexp) →
                    d ≠ (d' ⟨(τ1 ⊕ τ2) ⇒ (τ1' ⊕ τ2')⟩)) →
                  d indet →
                  (case d x d1 y d2) indet
      IPair1    : ∀{d1 d2} →
                  d1 indet →
                  d2 final →
                  ⟨ d1 , d2 ⟩ indet
      IPair2    : ∀{d1 d2} →
                  d1 final →
                  d2 indet →
                  ⟨ d1 , d2 ⟩ indet
      IFst      : ∀{d} →
                  ((d1 d2 : ihexp) →
                    d ≠ ⟨ d1 , d2 ⟩) →
                  ((τ1 τ2 τ1' τ2' : htyp) (d' : ihexp) →
                    d ≠ (d' ⟨(τ1 ⊠ τ2) ⇒ (τ1' ⊠ τ2')⟩)) →
                  d indet →
                  (fst d) indet
      ISnd      : ∀{d} →
                  ((d1 d2 : ihexp) →
                    d ≠ ⟨ d1 , d2 ⟩) →
                  ((τ1 τ2 τ1' τ2' : htyp) (d' : ihexp) →
                    d ≠ (d' ⟨(τ1 ⊠ τ2) ⇒ (τ1' ⊠ τ2')⟩)) →
                  d indet →
                  (snd d) indet
      IEHole    : ∀{u σ} →
                  ⦇-⦈⟨ u , σ ⟩ indet
      INEHole   : ∀{d u σ} →
                  d final →
                  ⦇⌜ d ⌟⦈⟨ u , σ ⟩ indet
      ICastArr  : ∀{d τ1 τ2 τ3 τ4} →
                  τ1 ==> τ2 ≠ τ3 ==> τ4 →
                  d indet →
                  d ⟨ (τ1 ==> τ2) ⇒ (τ3 ==> τ4) ⟩ indet
      ICastSum  : ∀{d τ1 τ2 τ3 τ4} →
                  τ1 ⊕ τ2 ≠ τ3 ⊕ τ4 →
                  d indet →
                  d ⟨ (τ1 ⊕ τ2) ⇒ (τ3 ⊕ τ4) ⟩ indet
      ICastProd : ∀{d τ1 τ2 τ3 τ4} →
                  τ1 ⊠ τ2 ≠ τ3 ⊠ τ4 →
                  d indet →
                  d ⟨ (τ1 ⊠ τ2) ⇒ (τ3 ⊠ τ4) ⟩ indet
      ICastGroundHole : ∀{τ d} →
                        τ ground →
                        d indet →
                        d ⟨ τ ⇒  ⦇-⦈ ⟩ indet
      ICastHoleGround : ∀{d τ} →
                        ((d' : ihexp) (τ' : htyp) → d ≠ (d' ⟨ τ' ⇒ ⦇-⦈ ⟩)) →
                        d indet →
                        τ ground →
                        d ⟨ ⦇-⦈ ⇒ τ ⟩ indet
      IFailedCast : ∀{d τ1 τ2} →
                    d final →
                    τ1 ground →
                    τ2 ground →
                    τ1 ≠ τ2 →
                    d ⟨ τ1 ⇒⦇-⦈⇏ τ2 ⟩ indet

    -- final expressions
    data _final : (d : ihexp) → Set where
      FBoxedVal : ∀{d} → d boxedval → d final
      FIndet    : ∀{d} → d indet → d final


  -- contextual dynamics

  -- evaluation contexts
  data ectx : Set where
    ⊙ : ectx
    _·+₁_  : ectx → ihexp → ectx
    _·+₂_  : ihexp → ectx → ectx
    _∘₁_   : ectx → ihexp → ectx
    _∘₂_   : ihexp → ectx → ectx
    inl    : htyp → ectx → ectx
    inr    : htyp → ectx → ectx
    case   : ectx → Nat → ihexp → Nat → ihexp → ectx
    ⟨_,_⟩₁ : ectx → ihexp → ectx
    ⟨_,_⟩₂ : ihexp → ectx → ectx
    fst    : ectx → ectx
    snd    : ectx → ectx
    ⦇⌜_⌟⦈⟨_⟩   : ectx → (Nat × env ) → ectx
    _⟨_⇒_⟩ : ectx → htyp → htyp → ectx
    _⟨_⇒⦇-⦈⇏_⟩ : ectx → htyp → htyp → ectx

  -- note: this judgement is redundant: in the absence of the premises in
  -- the red brackets, all syntactically well formed ectxs are valid. with
  -- finality premises, that's not true, and that would propagate through
  -- additions to the calculus. so we leave it here for clarity but note
  -- that, as written, in any use case it's either trival to prove or
  -- provides no additional information

   --ε is an evaluation context
  data _evalctx : (ε : ectx) → Set where
    ECDot   : ⊙ evalctx
    ECPlus1  : ∀{d ε} →
               ε evalctx →
               (ε ·+₁ d) evalctx
    ECPlus2  : ∀{d ε} →
               -- d final → -- red brackets
               ε evalctx →
               (d ·+₂ ε) evalctx
    ECAp1    : ∀{d ε} →
               ε evalctx →
               (ε ∘₁ d) evalctx
    ECAp2    : ∀{d ε} →
               -- d final → -- red brackets
               ε evalctx →
               (d ∘₂ ε) evalctx
    ECInl    : ∀{τ ε} →
               ε evalctx →
               (inl τ ε) evalctx
    ECInr    : ∀{τ ε} →
               ε evalctx →
               (inr τ ε) evalctx
    ECCase   : ∀{ε x d1 y d2} →
               ε evalctx →
               (case ε x d1 y d2) evalctx
    ECPair1  : ∀{d ε} →
               ε evalctx →
               ⟨ ε , d ⟩₁ evalctx
    ECPair2  : ∀{d ε} →
               -- d final → -- red brackets
               ε evalctx →
               ⟨ d , ε ⟩₂ evalctx
    ECFst    : ∀{ε} →
               (fst ε) evalctx
    ECSnd    : ∀{ε} →
               (snd ε) evalctx
    ECNEHole : ∀{ε u σ} →
               ε evalctx →
               ⦇⌜ ε ⌟⦈⟨ u , σ ⟩ evalctx
    ECCast   : ∀{ε τ1 τ2} →
               ε evalctx →
               (ε ⟨ τ1 ⇒ τ2 ⟩) evalctx
    ECFailedCast : ∀{ε τ1 τ2} →
                   ε evalctx →
                   ε ⟨ τ1 ⇒⦇-⦈⇏ τ2 ⟩ evalctx

  -- d is the result of filling the hole in ε with d'
  data _==_⟦_⟧ : (d : ihexp) (ε : ectx) (d' : ihexp) → Set where
    FHOuter  : ∀{d} → d == ⊙ ⟦ d ⟧
    FHPlus1  : ∀{d1 d1' d2 ε} →
               d1 == ε ⟦ d1' ⟧ →
               (d1 ·+ d2) == (ε ·+₁ d2) ⟦ d1' ⟧
    FHPlus2  : ∀{d1 d2 d2' ε} →
               -- d1 final → -- red brackets
               d2 == ε ⟦ d2' ⟧ →
               (d1 ·+ d2) == (d1 ·+₂ ε) ⟦ d2' ⟧
    FHAp1    : ∀{d1 d1' d2 ε} →
               d1 == ε ⟦ d1' ⟧ →
               (d1 ∘ d2) == (ε ∘₁ d2) ⟦ d1' ⟧
    FHAp2    : ∀{d1 d2 d2' ε} →
               -- d1 final → -- red brackets
               d2 == ε ⟦ d2' ⟧ →
               (d1 ∘ d2) == (d1 ∘₂ ε) ⟦ d2' ⟧
    FHInl    : ∀{d d' ε τ} →
               d == ε ⟦ d' ⟧ →
               (inl τ d) == (inl τ ε) ⟦ d' ⟧
    FHInr    : ∀{d d' ε τ} →
               d == ε ⟦ d' ⟧ →
               (inr τ d) == (inr τ ε) ⟦ d' ⟧
    FHCase   : ∀{d d' x d1 y d2 ε} →
               d == ε ⟦ d' ⟧ →
               (case d x d1 y d2) == (case ε x d1 y d2) ⟦ d' ⟧
    FHPair1  : ∀{d1 d1' d2 ε} →
               d1 == ε ⟦ d1' ⟧ →
               ⟨ d1 , d2 ⟩ == ⟨ ε , d2 ⟩₁ ⟦ d1' ⟧
    FHPair2  : ∀{d1 d2 d2' ε} →
               d2 == ε ⟦ d2' ⟧ →
               ⟨ d1 , d2 ⟩ == ⟨ d1 , ε ⟩₂ ⟦ d2' ⟧
    FHFst    : ∀{d d' ε} →
               d == ε ⟦ d' ⟧ →
               fst d == (fst ε) ⟦ d' ⟧
    FHSnd    : ∀{d d' ε} →
               d == ε ⟦ d' ⟧ →
               snd d == (snd ε) ⟦ d' ⟧
    FHNEHole : ∀{d d' ε u σ} →
               d == ε ⟦ d' ⟧ →
               ⦇⌜ d ⌟⦈⟨ (u , σ ) ⟩ ==  ⦇⌜ ε ⌟⦈⟨ (u , σ ) ⟩ ⟦ d' ⟧
    FHCast   : ∀{d d' ε τ1 τ2} →
               d == ε ⟦ d' ⟧ →
               d ⟨ τ1 ⇒ τ2 ⟩ == ε ⟨ τ1 ⇒ τ2 ⟩ ⟦ d' ⟧
    FHFailedCast : ∀{d d' ε τ1 τ2} →
                   d == ε ⟦ d' ⟧ →
                   (d ⟨ τ1 ⇒⦇-⦈⇏ τ2 ⟩) == (ε ⟨ τ1 ⇒⦇-⦈⇏ τ2 ⟩) ⟦ d' ⟧

  -- matched ground types
  data _▸gnd_ : htyp → htyp → Set where
    MGArr  : ∀{τ1 τ2} →
             (τ1 ==> τ2) ≠ (⦇-⦈ ==> ⦇-⦈) →
             (τ1 ==> τ2) ▸gnd (⦇-⦈ ==> ⦇-⦈)
    MGSum  : ∀{τ1 τ2} →
             (τ1 ⊕ τ2) ≠ (⦇-⦈ ⊕ ⦇-⦈) →
             (τ1 ⊕ τ2) ▸gnd (⦇-⦈ ⊕ ⦇-⦈)
    MGProd : ∀{τ1 τ2} →
             (τ1 ⊠ τ2) ≠ (⦇-⦈ ⊠ ⦇-⦈) →
             (τ1 ⊠ τ2) ▸gnd (⦇-⦈ ⊠ ⦇-⦈)

  -- instruction transition judgement
  data _→>_ : (d d' : ihexp) → Set where
    ITPlus     : ∀{n1 n2 n3} →
                 (n1 nat+ n2) == n3 →
                 ((N n1) ·+ (N n2)) →> (N n3)
    ITLam      : ∀{x τ d1 d2} →
                 -- d2 final → -- red brackets
                 ((·λ x ·[ τ ] d1) ∘ d2) →> ([ d2 / x ] d1)
    ITApCast   : ∀{d1 d2 τ1 τ2 τ1' τ2'} →
                 -- d1 final → -- red brackets
                 -- d2 final → -- red brackets
                 ((d1 ⟨ (τ1 ==> τ2) ⇒ (τ1' ==> τ2')⟩) ∘ d2) →>
                   ((d1 ∘ (d2 ⟨ τ1' ⇒ τ1 ⟩)) ⟨ τ2 ⇒ τ2' ⟩)
    ITCaseInl  : ∀{d τ x d1 y d2} →
                 -- d final → -- red brackets,
                 (case (inl τ d) x d1 y d2) →> ([ d / x ] d1)
    ITCaseInr  : ∀{d τ x d1 y d2} →
                 -- d final → -- red brackets,
                 (case (inr τ d) x d1 y d2) →> ([ d / y ] d2)
    ITCaseCast : ∀{d τ1 τ2 τ1' τ2' x d1 y d2} →
                 -- d final → -- red brackets
                 (case (d ⟨ τ1 ⊕ τ2 ⇒ τ1' ⊕ τ2' ⟩) x d1 y d2) →>
                   (case d x ([ (X x) ⟨ τ1 ⇒ τ1' ⟩ / x ] d1) y ([ (X y) ⟨ τ2 ⇒ τ2' ⟩ / y ] d2))
    ITFstPair  : ∀{d1 d2} →
                 -- d1 final → -- red brackets
                 -- d2 final → -- red brackets
                 fst ⟨ d1 , d2 ⟩ →> d1
    ITFstCast  : ∀{d τ1 τ2 τ1' τ2' } →
                 -- d final → -- red brackets
                 fst (d ⟨ τ1 ⊠ τ2 ⇒ τ1' ⊠ τ2' ⟩) →> ((fst d) ⟨ τ1 ⇒ τ1' ⟩)
    ITSndPair  : ∀{d1 d2} →
                 -- d1 final → -- red brackets
                 -- d2 final → -- red brackets
                 snd ⟨ d1 , d2 ⟩ →> d2
    ITSndCast  : ∀{d τ1 τ2 τ1' τ2' } →
                 -- d final → -- red brackets
                 snd (d ⟨ τ1 ⊠ τ2 ⇒ τ1' ⊠ τ2' ⟩) →> ((snd d) ⟨ τ2 ⇒ τ2' ⟩)
    ITCastID   : ∀{d τ} →
                 -- d final → -- red brackets
                 (d ⟨ τ ⇒ τ ⟩) →> d
    ITCastSucceed : ∀{d τ} →
                    -- d final → -- red brackets
                    τ ground →
                    (d ⟨ τ ⇒ ⦇-⦈ ⇒ τ ⟩) →> d
    ITCastFail : ∀{d τ1 τ2} →
                 -- d final → -- red brackets
                 τ1 ground →
                 τ2 ground →
                 τ1 ≠ τ2 →
                 (d ⟨ τ1 ⇒ ⦇-⦈ ⇒ τ2 ⟩) →> (d ⟨ τ1 ⇒⦇-⦈⇏ τ2 ⟩)
    ITGround   : ∀{d τ τ'} →
                 -- d final → -- red brackets
                 τ ▸gnd τ' →
                 (d ⟨ τ ⇒ ⦇-⦈ ⟩) →> (d ⟨ τ ⇒ τ' ⇒ ⦇-⦈ ⟩)
    ITExpand   : ∀{d τ τ'} →
                 -- d final → -- red brackets
                 τ ▸gnd τ' →
                 (d ⟨ ⦇-⦈ ⇒ τ ⟩) →> (d ⟨ ⦇-⦈ ⇒ τ' ⇒ τ ⟩)

  -- single step (in contextual evaluation sense)
  data _↦_ : (d d' : ihexp) → Set where
    Step : ∀{d d0 d' d0' ε} →
           d == ε ⟦ d0 ⟧ →
           d0 →> d0' →
           d' == ε ⟦ d0' ⟧ →
           d ↦ d'

  -- reflexive transitive closure of single steps into multi steps
  data _↦*_ : (d d' : ihexp) → Set where
    MSRefl : ∀{d} → d ↦* d
    MSStep : ∀{d d' d''} →
             d ↦ d' →
             d' ↦* d'' →
             d  ↦* d''

  -- those internal expressions where every cast is the identity cast and
  -- there are no failed casts
  data cast-id : ihexp → Set where
    CINum    : ∀{n} →
               cast-id (N n)
    CIPlus   : ∀{d1 d2} →
               cast-id d1 →
               cast-id d2 →
               cast-id (d1 ·+ d2)
    CIVar    : ∀{x} →
               cast-id (X x)
    CILam    : ∀{x τ d} →
               cast-id d →
               cast-id (·λ x ·[ τ ] d)
    CIAp     : ∀{d1 d2} →
               cast-id d1 →
               cast-id d2 →
               cast-id (d1 ∘ d2)
    CIInl    : ∀{τ d} →
               cast-id d →
               cast-id (inl τ d)
    CIInr    : ∀{τ d} →
               cast-id d →
               cast-id (inr τ d)
    CICase   : ∀{d x d1 y d2} →
               cast-id d →
               cast-id d1 →
               cast-id d2 →
               cast-id (case d x d1 y d2)
    CIPair   : ∀{d1 d2} →
               cast-id d1 →
               cast-id d2 →
               cast-id ⟨ d1 , d2 ⟩
    CIFst    : ∀{d} →
               cast-id d →
               cast-id (fst d)
    CISnd    : ∀{d} →
               cast-id d →
               cast-id (snd d)
    CIHole   : ∀{u} →
               cast-id (⦇-⦈⟨ u ⟩)
    CINEHole : ∀{d u} →
               cast-id d →
               cast-id (⦇⌜ d ⌟⦈⟨ u ⟩)
    CICast   : ∀{d τ} →
               cast-id d →
               cast-id (d ⟨ τ ⇒ τ ⟩)


  -- freshness
  mutual
    -- ... with respect to a hole context
    data envfresh : Nat → env → Set where
      EFId    : ∀{x Γ} →
                x # Γ →
                envfresh x (Id Γ)
      EFSubst : ∀{x d σ y} →
                fresh x d →
                envfresh x σ →
                x ≠ y →
                envfresh x (Subst d y σ)

    -- ... for internal expressions
    data fresh : Nat → ihexp → Set where
      FNum    : ∀{x n} →
                fresh x (N n)
      FPlus   : ∀{x d1 d2} →
                fresh x d1 →
                fresh x d2 →
                fresh x (d1 ·+ d2)
      FVar    : ∀{x y} →
                x ≠ y →
                fresh x (X y)
      FLam    : ∀{x y τ d} →
                x ≠ y →
                fresh x d →
                fresh x (·λ y ·[ τ ] d)
      FAp     : ∀{x d1 d2} →
                fresh x d1 →
                fresh x d2 →
                fresh x (d1 ∘ d2)
      FInl    : ∀{x d τ} →
                fresh x d →
                fresh x (inl τ d)
      FInr    : ∀{x d τ} →
                fresh x d →
                fresh x (inr τ d)
      FCase   : ∀{x d y d1 z d2} →
                fresh x d →
                x ≠ y →
                fresh x d1 →
                x ≠ z →
                fresh x d2 →
                fresh x (case d y d1 z d2)
      FPair   : ∀{x d1 d2} →
                fresh x d1 →
                fresh x d2 →
                fresh x ⟨ d1 , d2 ⟩
      FFst    : ∀{x d} →
                fresh x d →
                fresh x (fst d)
      FSnd    : ∀{x d} →
                fresh x d →
                fresh x (snd d)
      FHole   : ∀{x u σ} →
                envfresh x σ →
                fresh x (⦇-⦈⟨ u , σ ⟩)
      FNEHole : ∀{x d u σ} →
                envfresh x σ →
                fresh x d →
                fresh x (⦇⌜ d ⌟⦈⟨ u , σ ⟩)
      FCast   : ∀{x d τ1 τ2} →
                fresh x d →
                fresh x (d ⟨ τ1 ⇒ τ2 ⟩)
      FFailedCast : ∀{x d τ1 τ2} →
                    fresh x d →
                    fresh x (d ⟨ τ1 ⇒⦇-⦈⇏ τ2 ⟩)

  -- x is not used in a binding site in d
  mutual
    data unbound-in-σ : Nat → env → Set where
      UBσId    : ∀{x Γ} → unbound-in-σ x (Id Γ)
      UBσSubst : ∀{x d y σ} →
                 unbound-in x d →
                 unbound-in-σ x σ →
                 x ≠ y →
                 unbound-in-σ x (Subst d y σ)

    data unbound-in : (x : Nat) (d : ihexp) → Set where
      UBNum    : ∀{x n} → unbound-in x (N n)
      UBPlus   : ∀{x d1 d2} →
                 unbound-in x d1 →
                 unbound-in x d2 →
                 unbound-in x (d1 ·+ d2)
      UBVar    : ∀{x y} → unbound-in x (X y)
      UBLam2   : ∀{x d y τ} →
                 x ≠ y →
                 unbound-in x d →
                 unbound-in x (·λ y ·[ τ ] d)
      UBAp     : ∀{x d1 d2} →
                 unbound-in x d1 →
                 unbound-in x d2 →
                 unbound-in x (d1 ∘ d2)
      UBInl    : ∀{x d τ} →
                 unbound-in x d →
                 unbound-in x (inl τ d)
      UBInr    : ∀{x d τ} →
                 unbound-in x d →
                 unbound-in x (inr τ d)
      UBCase   : ∀{x d y d1 z d2} →
                 unbound-in x d →
                 x ≠ y →
                 unbound-in x d1 →
                 x ≠ z →
                 unbound-in x d2 →
                 unbound-in x (case d y d1 z d2)
      UBPair   : ∀{x d1 d2} →
                 unbound-in x d1 →
                 unbound-in x d2 →
                 unbound-in x ⟨ d1 , d2 ⟩
      UBFst    : ∀{x d} →
                 unbound-in x d →
                 unbound-in x (fst d)
      UBSnd    : ∀{x d} →
                 unbound-in x d →
                 unbound-in x (snd d)
      UBHole   : ∀{x u σ} →
                 unbound-in-σ x σ →
                 unbound-in x (⦇-⦈⟨ u , σ ⟩)
      UBNEHole : ∀{x u σ d} →
                 unbound-in-σ x σ →
                 unbound-in x d →
                 unbound-in x (⦇⌜ d ⌟⦈⟨ u , σ ⟩)
      UBCast   : ∀{x d τ1 τ2} →
                 unbound-in x d →
                 unbound-in x (d ⟨ τ1 ⇒ τ2 ⟩)
      UBFailedCast : ∀{x d τ1 τ2} →
                     unbound-in x d →
                     unbound-in x (d ⟨ τ1 ⇒⦇-⦈⇏ τ2 ⟩)
  mutual
    data binders-disjoint-σ : env → ihexp → Set where
      BDσId    : ∀{Γ d} → binders-disjoint-σ (Id Γ) d
      BDσSubst : ∀{d1 d2 y σ} →
                 binders-disjoint d2 d1 →
                 binders-disjoint-σ σ d2 →
                 unbound-in y d2 →
                 binders-disjoint-σ (Subst d1 y σ) d2

    -- two terms that do not share any binders
    data binders-disjoint : ihexp → ihexp → Set where
      BDNum    : ∀{d n} → binders-disjoint (N n) d
      BDPlus   : ∀{d1 d2 d3} →
                 binders-disjoint d1 d3 →
                 binders-disjoint d2 d3 →
                 binders-disjoint (d1 ·+ d2) d3
      BDVar    : ∀{x d} → binders-disjoint (X x) d
      BDLam    : ∀{x τ d1 d2} →
                 binders-disjoint d1 d2 →
                 unbound-in x d2 →
                 binders-disjoint (·λ x ·[ τ ] d1) d2
      BDAp     : ∀{d1 d2 d3} →
                 binders-disjoint d1 d3 →
                 binders-disjoint d2 d3 →
                 binders-disjoint (d1 ∘ d2) d3
      BDInl    : ∀{d1 d2 τ} →
                 binders-disjoint d1 d2 →
                 binders-disjoint (inl τ d1) d2
      BDInr    : ∀{d1 d2 τ} →
                 binders-disjoint d1 d2 →
                 binders-disjoint (inr τ d1) d2
      BDCase   : ∀{d x d1 y d2 d3} →
                 binders-disjoint d d3 →
                 unbound-in x d3 →
                 binders-disjoint d1 d3 →
                 unbound-in y d3 →
                 binders-disjoint d2 d3 →
                 binders-disjoint (case d x d1 y d2) d3
      BDPair   : ∀{d1 d2 d3} →
                 binders-disjoint d1 d3 →
                 binders-disjoint d2 d3 →
                 binders-disjoint ⟨ d1 , d2 ⟩ d3
      BDFst    : ∀{d1 d2} →
                 binders-disjoint d1 d2 →
                 binders-disjoint (fst d1) d2
      BDSnd    : ∀{d1 d2} →
                 binders-disjoint d1 d2 →
                 binders-disjoint (snd d1) d2
      BDHole   : ∀{u σ d2} →
                 binders-disjoint-σ σ d2 →
                 binders-disjoint (⦇-⦈⟨ u , σ ⟩) d2
      BDNEHole : ∀{u σ d1 d2} →
                 binders-disjoint-σ σ d2 →
                 binders-disjoint d1 d2 →
                 binders-disjoint (⦇⌜ d1 ⌟⦈⟨ u , σ ⟩) d2
      BDCast   : ∀{d1 d2 τ1 τ2} →
                 binders-disjoint d1 d2 →
                 binders-disjoint (d1 ⟨ τ1 ⇒ τ2 ⟩) d2
      BDFailedCast : ∀{d1 d2 τ1 τ2} →
                     binders-disjoint d1 d2 →
                     binders-disjoint (d1 ⟨ τ1 ⇒⦇-⦈⇏ τ2 ⟩) d2

  mutual
  -- each term has to be binders unique, and they have to be pairwise
  -- disjoint with the collection of bound vars
    data binders-unique-σ : env → Set where
      BUσId    : ∀{Γ} →
                 binders-unique-σ (Id Γ)
      BUσSubst : ∀{d y σ} →
                 binders-unique d →
                 binders-unique-σ σ →
                 binders-disjoint-σ σ d →
                 binders-unique-σ (Subst d y σ)

    -- all the variable names in the term are unique
    data binders-unique : ihexp → Set where
      BUNum    : ∀{n} →
                 binders-unique (N n)
      BUPlus   : ∀{d1 d2} →
                 binders-unique d1 →
                 binders-unique d2 →
                 binders-disjoint d1 d2 →
                 binders-unique (d1 ·+ d2)
      BUVar    : ∀{x} →
                 binders-unique (X x)
      BULam    : {x : Nat} {τ : htyp} {d : ihexp} →
                 binders-unique d →
                 unbound-in x d →
                 binders-unique (·λ x ·[ τ ] d)
      BUEHole  : ∀{u σ} →
                 binders-unique-σ σ →
                 binders-unique (⦇-⦈⟨ u , σ ⟩)
      BUNEHole : ∀{u σ d} →
                 binders-unique d →
                 binders-unique-σ σ →
                 binders-unique (⦇⌜ d ⌟⦈⟨ u , σ ⟩)
      BUAp     : ∀{d1 d2} →
                 binders-unique d1 →
                 binders-unique d2 →
                 binders-disjoint d1 d2 →
                 binders-unique (d1 ∘ d2)
      BUInl    : ∀{d τ} →
                 binders-unique d →
                 binders-unique (inl τ d)
      BUInr    : ∀{d τ} →
                 binders-unique d →
                 binders-unique (inr τ d)
      BUCase   : ∀{d x d1 y d2} →
                 binders-unique d →
                 binders-unique d1 →
                 binders-unique d2 →
                 binders-disjoint d d1 →
                 binders-disjoint d d2 →
                 binders-disjoint d1 d2 →
                 unbound-in x d →
                 unbound-in x d1 →
                 unbound-in x d2 →
                 unbound-in y d →
                 unbound-in y d1 →
                 unbound-in y d2 →
                 binders-unique (case d x d1 y d2)
      BUPair   : ∀{d1 d2} →
                 binders-unique d1 →
                 binders-unique d2 →
                 binders-disjoint d1 d2 →
                 binders-unique ⟨ d1 , d2 ⟩
      BUFst    : ∀{d} →
                 binders-unique d →
                 binders-unique (fst d)
      BUSnd    : ∀{d} →
                 binders-unique d →
                 binders-unique (snd d)
      BUCast   : ∀{d τ1 τ2} →
                 binders-unique d →
                 binders-unique (d ⟨ τ1 ⇒ τ2 ⟩)
      BUFailedCast : ∀{d τ1 τ2} →
                     binders-unique d →
                     binders-unique (d ⟨ τ1 ⇒⦇-⦈⇏ τ2 ⟩)
