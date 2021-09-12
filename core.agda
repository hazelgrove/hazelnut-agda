open import Nat
open import Prelude
open import contexts

module core where
  -- types
  data htyp : Set where
    num   : htyp
    ⦇-⦈   : htyp
    _==>_ : htyp → htyp → htyp
    _⊕_   : htyp → htyp → htyp
    
  -- arrow type constructors bind very tightly
  infixr 25  _==>_
  infixr 25 _⊕_
  
  -- external expressions
  data hexp : Set where
    N       : Nat → hexp
    _·+_    : hexp → hexp → hexp
    _·:_    : hexp → htyp → hexp
    X       : Nat → hexp
    ·λ      : Nat → hexp → hexp
    ·λ_[_]_ : Nat → htyp → hexp → hexp
    _∘_     : hexp → hexp → hexp
    inl     : hexp → hexp
    inr     : hexp → hexp
    case    : hexp → Nat → hexp → Nat → hexp → hexp
    ⦇-⦈[_]   : Nat → hexp
    ⦇⌜_⌟⦈[_] : hexp → Nat → hexp

  -- the type of type contexts, i.e. Γs in the judegments below
  tctx : Set
  tctx = htyp ctx

  mutual
    -- identity substitution, substitition environments
    data env : Set where
      Id : (Γ : tctx) → env
      Subst : (d : ihexp) → (y : Nat) → env → env

    -- internal expressions
    data ihexp : Set where
      N         : Nat → ihexp
      _·+_      : ihexp → ihexp → ihexp
      X         : Nat → ihexp
      ·λ_[_]_   : Nat → htyp → ihexp → ihexp
      _∘_       : ihexp → ihexp → ihexp
      inl       : htyp → ihexp → ihexp
      inr       : htyp → ihexp → ihexp
      case      : ihexp → Nat → ihexp → Nat → ihexp → ihexp
      ⦇-⦈⟨_⟩     : (Nat × env) → ihexp
      ⦇⌜_⌟⦈⟨_⟩   : ihexp → (Nat × env) → ihexp
      _⟨_⇒_⟩     : ihexp → htyp → htyp → ihexp
      _⟨_⇒⦇-⦈⇏_⟩ : ihexp → htyp → htyp → ihexp

  -- convenient notation for chaining together two agreeable casts
  _⟨_⇒_⇒_⟩ : ihexp → htyp → htyp → htyp → ihexp
  d ⟨ t1 ⇒ t2 ⇒ t3 ⟩ = d ⟨ t1 ⇒ t2 ⟩ ⟨ t2 ⇒ t3 ⟩

  -- type consistency
  data _~_ : (t1 t2 : htyp) → Set where
    TCRefl  : {τ : htyp} → τ ~ τ
    TCHole1 : {τ : htyp} → τ ~ ⦇-⦈
    TCHole2 : {τ : htyp} → ⦇-⦈ ~ τ
    TCArr   : {τ1 τ2 τ1' τ2' : htyp} →
              τ1 ~ τ1' →
              τ2 ~ τ2' →
              τ1 ==> τ2 ~ τ1' ==> τ2'
    TCSum   : {τ1 τ2 τ1' τ2' : htyp} →
              τ1 ~ τ1' →
              τ2 ~ τ2' →
              τ1 ⊕ τ2 ~ τ1' ⊕ τ2'
  
  -- type inconsistency
  _~̸_ : htyp → htyp → Set
  t1 ~̸ t2 = (t1 ~ t2) → ⊥

  -- matching for arrows
  data _▸arr_ : htyp → htyp → Set where
    MAHole : ⦇-⦈ ▸arr ⦇-⦈ ==> ⦇-⦈
    MAArr  : {τ1 τ2 : htyp} → τ1 ==> τ2 ▸arr τ1 ==> τ2
    
  -- matching for sums
  data _▸sum_ : htyp → htyp → Set where
    MSHole : ⦇-⦈ ▸sum ⦇-⦈ ⊕ ⦇-⦈
    MSSum  : {τ1 τ2 : htyp} → τ1 ⊕ τ2 ▸sum τ1 ⊕ τ2
    
  mutual
    -- types τ1 and τ2 join consistently, forming type τ3
    data _join_==_ : htyp → htyp → htyp → Set where
      TJRefl  : {τ : htyp} → τ join τ == τ
      TJHole1 : {τ : htyp} → τ join ⦇-⦈ == τ
      TJHole2 : {τ : htyp} → ⦇-⦈ join τ == τ
      TJArr   : {τ1 τ2 τ1' τ2' τ3 τ4 : htyp} →
                τ1 meet τ1' == τ3 →
                τ2 join τ2' == τ4 →
                (τ1 ==> τ2) join (τ1' ==> τ2') == (τ3 ==> τ4)
      TJSum   : {τ1 τ2 τ1' τ2' τ3 τ4 : htyp} →
                τ1 join τ1' == τ3 →
                τ2 join τ2' == τ4 →
                (τ1 ⊕ τ2) join (τ1' ⊕ τ2') == (τ3 ⊕ τ4)
      
    -- types τ1 and τ2 meet consistently, forming type τ3
    data _meet_==_ : htyp → htyp → htyp → Set where
      TMRefl  : {τ : htyp} → τ meet τ == τ
      TMHole1 : {τ : htyp} → τ meet ⦇-⦈ == ⦇-⦈
      TMHole2 : {τ : htyp} → ⦇-⦈ meet τ == ⦇-⦈
      TMArr   : {τ1 τ2 τ1' τ2' τ3 τ4 : htyp} →
                τ1 join τ1' == τ3 →
                τ2 meet τ2' == τ4 →
                (τ1 ==> τ2) meet (τ1' ==> τ2') == (τ3 ==> τ4)
      TMSum   : {τ1 τ2 τ1' τ2' τ3 τ4 : htyp} →
                τ1 meet τ1' == τ3 →
                τ2 meet τ2' == τ4 →
                (τ1 ⊕ τ2) meet (τ1' ⊕ τ2') == (τ3 ⊕ τ4)

  mutual
    -- we can only take the join of consistent types, and each of
    -- the types is consistent with their join
    join-consistency : ∀{τ1 τ2 τ} →
                     τ1 join τ2 == τ →
                     (τ1 ~ τ2) × (τ1 ~ τ) × (τ2 ~ τ)
    join-consistency TJRefl = TCRefl , TCRefl , TCRefl
    join-consistency TJHole1 = TCHole1 , TCRefl , TCHole2
    join-consistency TJHole2 = TCHole2 , TCHole2 , TCRefl
    join-consistency (TJArr m j)
      with meet-consistency m | join-consistency j
    ... | t1~t1' , t1~t3 , t1'~t3 | t2~t2' , t2~t4 , t2'~t4 =
      TCArr t1~t1' t2~t2' , TCArr t1~t3 t2~t4 , TCArr t1'~t3 t2'~t4
    join-consistency (TJSum j1 j2)
      with join-consistency j1 | join-consistency j2
    ... | t1~t1' , t1~t3 , t1'~t3 | t2~t2' , t2~t4 , t2'~t4 =
      TCSum t1~t1' t2~t2' , TCSum t1~t3 t2~t4 , TCSum t1'~t3 t2'~t4

    -- we can only take the meet of consistent types, and each of
    -- the types is consistent with their meet
    meet-consistency : ∀{τ1 τ2 τ} →
                     τ1 meet τ2 == τ →
                     (τ1 ~ τ2) × (τ1 ~ τ) × (τ2 ~ τ)
    meet-consistency TMRefl = TCRefl , TCRefl , TCRefl
    meet-consistency TMHole1 = TCHole1 , TCHole1 , TCRefl
    meet-consistency TMHole2 = TCHole2 , TCRefl , TCHole1
    meet-consistency (TMArr j m)
      with join-consistency j | meet-consistency m
    ... | t1~t1' , t1~t3 , t1'~t3 | t2~t2' , t2~t4 , t2'~t4 =
      TCArr t1~t1' t2~t2' , TCArr t1~t3 t2~t4 , TCArr t1'~t3 t2'~t4
    meet-consistency (TMSum m1 m2)
      with meet-consistency m1 | meet-consistency m2
    ... | t1~t1' , t1~t3 , t1'~t3 | t2~t2' , t2~t4 , t2'~t4 =
      TCSum t1~t1' t2~t2' , TCSum t1~t3 t2~t4 , TCSum t1'~t3 t2'~t4
      
  -- the type of hole contexts, i.e. Δs in the judgements
  hctx : Set
  hctx = (htyp ctx × htyp) ctx

  -- notation for a triple to match the CMTT syntax
  _::_[_] : Nat → htyp → tctx → (Nat × (tctx × htyp))
  u :: τ [ Γ ] = u , (Γ , τ)

  -- the hole name u does not appear in the term e
  data hole-name-new : (e : hexp) (u : Nat) → Set where
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
             hole-name-new (·λ x [ τ ] e) u
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
    HNHole : ∀{u u'} →
             u' ≠ u →
             hole-name-new (⦇-⦈[ u' ]) u
    HNNEHole : ∀{u u' e} →
               u' ≠ u →
               hole-name-new e u →
               hole-name-new (⦇⌜ e ⌟⦈[ u' ]) u

  -- two terms that do not share any hole names
  data holes-disjoint : (e1 : hexp) → (e2 : hexp) → Set where
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
             holes-disjoint (·λ x [ τ ] e1) e2
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
    HDHole : ∀{u e2} →
             hole-name-new e2 u →
             holes-disjoint (⦇-⦈[ u ]) e2
    HDNEHole : ∀{u e1 e2} →
               hole-name-new e2 u →
               holes-disjoint e1 e2 →
               holes-disjoint (⦇⌜ e1 ⌟⦈[ u ]) e2

  -- bidirectional type checking judgements for hexp
  mutual
    -- synthesis
    data _⊢_=>_ : (Γ : tctx) (e : hexp) (τ : htyp) → Set where
      SNum    : {Γ : tctx} {n : Nat} →
                Γ ⊢ N n => num
      SPlus   : {Γ : tctx} {e1 e2 : hexp}  →
                holes-disjoint e1 e2 →
                Γ ⊢ e1 <= num →
                Γ ⊢ e2 <= num →
                Γ ⊢ (e1 ·+ e2) => num
      SAsc    : {Γ : tctx} {e : hexp} {τ : htyp} →
                Γ ⊢ e <= τ →
                Γ ⊢ (e ·: τ) => τ
      SVar    : {Γ : tctx} {τ : htyp} {x : Nat} →
                (x , τ) ∈ Γ →
                Γ ⊢ X x => τ
      SLam    : {Γ : tctx} {e : hexp} {τ1 τ2 : htyp} {x : Nat} →
                x # Γ →
                (Γ ,, (x , τ1)) ⊢ e => τ2 →
                Γ ⊢ ·λ x [ τ1 ] e => τ1 ==> τ2
      SAp     : {Γ : tctx} {e1 e2 : hexp} {τ τ1 τ2 : htyp} →
                holes-disjoint e1 e2 →
                Γ ⊢ e1 => τ1 →
                τ1 ▸arr τ2 ==> τ →
                Γ ⊢ e2 <= τ2 →
                Γ ⊢ (e1 ∘ e2) => τ
      SEHole  : {Γ : tctx} {u : Nat} → Γ ⊢ ⦇-⦈[ u ] => ⦇-⦈
      SNEHole : {Γ : tctx} {e : hexp} {τ : htyp} {u : Nat} →
                hole-name-new e u →
                Γ ⊢ e => τ →
                Γ ⊢ ⦇⌜ e ⌟⦈[ u ] => ⦇-⦈

    -- analysis
    data _⊢_<=_ : (Γ : htyp ctx) (e : hexp) (τ : htyp) → Set where
      ASubsume : {Γ : tctx} {e : hexp} {τ τ' : htyp} →
                 Γ ⊢ e => τ' →
                 τ ~ τ' →
                 Γ ⊢ e <= τ
      ALam     : {Γ : tctx} {e : hexp} {τ τ1 τ2 : htyp} {x : Nat} →
                 x # Γ →
                 τ ▸arr τ1 ==> τ2 →
                 (Γ ,, (x , τ1)) ⊢ e <= τ2 →
                 Γ ⊢ (·λ x e) <= τ
      AInl     : {Γ : tctx} {e : hexp} {t+ t1 t2 : htyp} →
                 t+ ▸sum (t1 ⊕ t2) →
                 Γ ⊢ e <= t1 →
                 Γ ⊢ inl e <= t+
      AInr     : {Γ : tctx} {e : hexp} {t+ t1 t2 : htyp} →
                 t+ ▸sum (t1 ⊕ t2) →
                 Γ ⊢ e <= t2 →
                 Γ ⊢ inr e <= t+
      ACase    : {Γ : tctx} {e e1 e2 : hexp} {t t+ t1 t2 : htyp} {x y : Nat} →
                 x # Γ →
                 y # Γ →
                 t+ ▸sum (t1 ⊕ t2) →
                 Γ ⊢ e => t+ →
                 (Γ ,, (x , t1)) ⊢ e1 <= t →
                 (Γ ,, (y , t2)) ⊢ e2 <= t →
                 Γ ⊢ case e x e1 y e2 <= t
                 
  -- those types without holes
  data _tcomplete : htyp → Set where
    TCNum : num tcomplete
    TCArr : ∀{τ1 τ2} → τ1 tcomplete → τ2 tcomplete → (τ1 ==> τ2) tcomplete
    TCSum : ∀{τ1 τ2} → τ1 tcomplete → τ2 tcomplete → (τ1 ⊕ τ2) tcomplete

  -- those external expressions without holes
  data _ecomplete : hexp → Set where
    ECNum  : ∀{n} → (N n) ecomplete
    ECPlus : ∀{e1 e2} → e1 ecomplete → e2 ecomplete → (e1 ·+ e2) ecomplete
    ECAsc  : ∀{τ e} → τ tcomplete → e ecomplete → (e ·: τ) ecomplete
    ECVar  : ∀{x} → (X x) ecomplete
    ECLam1 : ∀{x e} → e ecomplete → (·λ x e) ecomplete
    ECLam2 : ∀{x e τ} → e ecomplete → τ tcomplete → (·λ x [ τ ] e) ecomplete
    ECAp   : ∀{e1 e2} → e1 ecomplete → e2 ecomplete → (e1 ∘ e2) ecomplete
    ECInl  : ∀{e} → e ecomplete → (inl e) ecomplete
    ECInr  : ∀{e} → e ecomplete → (inr e) ecomplete
    ECCase : ∀{e x e1 y e2} → e ecomplete → e1 ecomplete → e2 ecomplete →
             (case e x e1 y e2) ecomplete
             
  -- those internal expressions without holes
  data _dcomplete : ihexp → Set where
    DCNum  : ∀{n} → (N n) dcomplete
    DCPlus : ∀{d1 d2} → d1 dcomplete → d2 dcomplete → (d1 ·+ d2) dcomplete
    DCVar  : ∀{x} → (X x) dcomplete
    DCLam  : ∀{x τ d} → d dcomplete → τ tcomplete → (·λ x [ τ ] d) dcomplete
    DCAp   : ∀{d1 d2} → d1 dcomplete → d2 dcomplete → (d1 ∘ d2) dcomplete
    DCInl  : ∀{τ d} → τ tcomplete → d dcomplete → (inl τ d) dcomplete
    DCInr  : ∀{τ d} → τ tcomplete → d dcomplete → (inr τ d) dcomplete
    DCCase : ∀{d x d1 y d2} → d dcomplete → d1 dcomplete → d2 dcomplete →
             (case d x d1 y d2) dcomplete
    DCCast : ∀{d τ1 τ2} → d dcomplete → τ1 tcomplete → τ2 tcomplete →
             (d ⟨ τ1 ⇒ τ2 ⟩) dcomplete

  -- contexts that only produce complete types
  _gcomplete : tctx → Set
  Γ gcomplete = (x : Nat) (τ : htyp) → (x , τ) ∈ Γ → τ tcomplete

  -- those internal expressions where every cast is the identity cast and
  -- there are no failed casts
  data cast-id : ihexp → Set where
    CINum    : ∀{n} → cast-id (N n)
    CIPlus   : ∀{d1 d2} → cast-id d1 → cast-id d2 → cast-id (d1 ·+ d2)
    CIVar    : ∀{x} → cast-id (X x)
    CILam    : ∀{x τ d} → cast-id d → cast-id (·λ x [ τ ] d)
    CIAp     : ∀{d1 d2} → cast-id d1 → cast-id d2 → cast-id (d1 ∘ d2)
    CIInl    : ∀{τ d} → cast-id d → cast-id (inl τ d)
    CIInr    : ∀{τ d} → cast-id d → cast-id (inr τ d)
    CICase   : ∀{d x d1 y d2} → cast-id d → cast-id d1 → cast-id d2 →
               cast-id (case d x d1 y d2)
    CIHole   : ∀{u} → cast-id (⦇-⦈⟨ u ⟩)
    CINEHole : ∀{d u} → cast-id d → cast-id (⦇⌜ d ⌟⦈⟨ u ⟩)
    CICast   : ∀{d τ} → cast-id d → cast-id (d ⟨ τ ⇒ τ ⟩)

  -- expansion
  mutual
    -- synthesis
    data _⊢_⇒_~>_⊣_ : (Γ : tctx) (e : hexp) (τ : htyp) (d : ihexp) (Δ : hctx) → Set where
      ESNum  : ∀{Γ n} → Γ ⊢ (N n) ⇒ num ~> (N n) ⊣ ∅
      ESPlus : ∀{Γ e1 e2 d1 d2 Δ1 Δ2 τ1 τ2} →
               Δ1 ## Δ2 →
               holes-disjoint e1 e2 →
               Γ ⊢ e1 ⇐ num ~> d1 :: τ1 ⊣ Δ1 →
               Γ ⊢ e2 ⇐ num ~> d2 :: τ2 ⊣ Δ2 →
               Γ ⊢ e1 ·+ e2 ⇒ num ~> (d1 ⟨ τ1 ⇒ num ⟩) ·+ (d2 ⟨ τ2 ⇒ num ⟩) ⊣ (Δ1 ∪ Δ2)
      ESAsc  : ∀{Γ e τ d τ' Δ} →
               Γ ⊢ e ⇐ τ ~> d :: τ' ⊣ Δ →
               Γ ⊢ (e ·: τ) ⇒ τ ~> d ⟨ τ' ⇒ τ ⟩ ⊣ Δ
      ESVar  : ∀{Γ x τ} →
               (x , τ) ∈ Γ →
               Γ ⊢ X x ⇒ τ ~> X x ⊣ ∅
      ESLam  : ∀{Γ x τ1 τ2 e d Δ} →
               (x # Γ) →
               (Γ ,, (x , τ1)) ⊢ e ⇒ τ2 ~> d ⊣ Δ →
               Γ ⊢ ·λ x [ τ1 ] e ⇒ (τ1 ==> τ2) ~> ·λ x [ τ1 ] d ⊣ Δ
      ESAp   : ∀{Γ e1 τ τ1 τ1' τ2 τ2' d1 Δ1 e2 d2 Δ2} →
               holes-disjoint e1 e2 →
               Δ1 ## Δ2 →
               Γ ⊢ e1 => τ1 →
               τ1 ▸arr τ2 ==> τ →
               Γ ⊢ e1 ⇐ (τ2 ==> τ) ~> d1 :: τ1' ⊣ Δ1 →
               Γ ⊢ e2 ⇐ τ2 ~> d2 :: τ2' ⊣ Δ2 →
               Γ ⊢ e1 ∘ e2 ⇒ τ ~> (d1 ⟨ τ1' ⇒ τ2 ==> τ ⟩) ∘ (d2 ⟨ τ2' ⇒ τ2 ⟩) ⊣ (Δ1 ∪ Δ2)
      ESEHole  : ∀{Γ u} →
                 Γ ⊢ ⦇-⦈[ u ] ⇒ ⦇-⦈ ~> ⦇-⦈⟨ u , Id Γ ⟩ ⊣  ■ (u :: ⦇-⦈ [ Γ ])
      ESNEHole : ∀{Γ e τ d u Δ} →
                 Δ ## (■ (u , Γ , ⦇-⦈)) →
                 Γ ⊢ e ⇒ τ ~> d ⊣ Δ →
                 Γ ⊢ ⦇⌜ e ⌟⦈[ u ] ⇒ ⦇-⦈ ~> ⦇⌜ d ⌟⦈⟨ u , Id Γ  ⟩ ⊣ (Δ ,, u :: ⦇-⦈ [ Γ ])
      

    -- analysis
    data _⊢_⇐_~>_::_⊣_ : (Γ : tctx) (e : hexp) (τ : htyp)
                         (d : ihexp) (τ' : htyp) (Δ : hctx) → Set where
      EALam  : ∀{Γ x τ τ1 τ2 e d τ2' Δ} →
               (x # Γ) →
               τ ▸arr τ1 ==> τ2 →
               (Γ ,, (x , τ1)) ⊢ e ⇐ τ2 ~> d :: τ2' ⊣ Δ →
               Γ ⊢ ·λ x e ⇐ τ ~> ·λ x [ τ1 ] d :: τ1 ==> τ2' ⊣ Δ
      EAInl  : ∀{Γ τ τ1 τ2 e d τ1' Δ} →
               τ ▸sum τ1 ⊕ τ2 →
               Γ ⊢ e ⇐ τ1 ~> d :: τ1' ⊣ Δ →
               Γ ⊢ inl e ⇐ τ ~> inl τ2 d :: τ1' ⊕ τ2 ⊣ Δ
      EAInr  : ∀{Γ τ τ1 τ2 e d τ2' Δ} →
               τ ▸sum τ1 ⊕ τ2 →
               Γ ⊢ e ⇐ τ2 ~> d :: τ2' ⊣ Δ →
               Γ ⊢ inr e ⇐ τ ~> inr τ1 d :: τ1 ⊕ τ2' ⊣ Δ
      EACase : ∀{Γ e τ+ d Δ τ1 τ2 τ x e1 d1 τr1 Δ1 y e2 d2 τr2 Δ2 τr} →
               holes-disjoint e e1 →
               holes-disjoint e e2 →
               holes-disjoint e1 e2 →
               Δ ## Δ1 →
               Δ ## Δ2 →
               Δ1 ## Δ2 →
               Γ ⊢ e ⇒ τ+ ~> d ⊣ Δ →
               τ+ ▸sum τ1 ⊕ τ2 →
               (Γ ,, (x , τ1)) ⊢ e1 ⇐ τ ~> d1 :: τr1 ⊣ Δ1 →
               (Γ ,, (y , τ2)) ⊢ e2 ⇐ τ ~> d2 :: τr2 ⊣ Δ2 →
               τr1 join τr2 == τr →
               Γ ⊢ case e x e1 y e2 ⇐ τ ~> case (d ⟨ τ+ ⇒ τ1 ⊕ τ2 ⟩)
                                                x (d1 ⟨ τr1 ⇒ τr ⟩)
                                                y (d2 ⟨ τr2 ⇒ τr ⟩) :: τr ⊣ ((Δ ∪ Δ1) ∪ Δ2)
      EASubsume : ∀{e Γ τ' d Δ τ} →
                  ((u : Nat) → e ≠ ⦇-⦈[ u ]) →
                  ((e' : hexp) (u : Nat) → e ≠ ⦇⌜ e' ⌟⦈[ u ]) →
                  Γ ⊢ e ⇒ τ' ~> d ⊣ Δ →
                  τ ~ τ' →
                  Γ ⊢ e ⇐ τ ~> d :: τ' ⊣ Δ
      EAEHole   : ∀{Γ u τ} →
                  Γ ⊢ ⦇-⦈[ u ] ⇐ τ ~> ⦇-⦈⟨ u , Id Γ  ⟩ :: τ ⊣ ■ (u :: τ [ Γ ])
      EANEHole  : ∀{Γ e u τ d τ' Δ} →
                  Δ ## (■ (u , Γ , τ)) →
                  Γ ⊢ e ⇒ τ' ~> d ⊣ Δ →
                  Γ ⊢ ⦇⌜ e ⌟⦈[ u ] ⇐ τ ~> ⦇⌜ d ⌟⦈⟨ u , Id Γ  ⟩ :: τ ⊣ (Δ ,, u :: τ [ Γ ])

  -- ground types
  data _ground : (τ : htyp) → Set where
    GNum  : num ground
    GArrHole : ⦇-⦈ ==> ⦇-⦈ ground
    GSumHole : ⦇-⦈ ⊕ ⦇-⦈ ground
    
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
      TANum   : ∀{Δ Γ n} → Δ , Γ ⊢ (N n) :: num
      TAPlus  : ∀{Δ Γ d1 d2} →
                Δ , Γ ⊢ d1 :: num →
                Δ , Γ ⊢ d2 :: num →
                Δ , Γ ⊢ (d1 ·+ d2) :: num
      TAVar   : ∀{Δ Γ x τ} → (x , τ) ∈ Γ → Δ , Γ ⊢ X x :: τ
      TALam   : ∀{Δ Γ x τ1 d τ2} →
                x # Γ →
                Δ , (Γ ,, (x , τ1)) ⊢ d :: τ2 →
                Δ , Γ ⊢ ·λ x [ τ1 ] d :: (τ1 ==> τ2)
      TAAp    : ∀{Δ Γ d1 d2 τ1 τ} →
                Δ , Γ ⊢ d1 :: τ1 ==> τ →
                Δ , Γ ⊢ d2 :: τ1 →
                Δ , Γ ⊢ d1 ∘ d2 :: τ
      TAInl   : ∀{Δ Γ d τ1 τ2} →
                Δ , Γ ⊢ d :: τ1 →
                Δ , Γ ⊢ inl τ2 d :: τ1 ⊕ τ2
      TAInr   : ∀{Δ Γ d τ1 τ2} →
                Δ , Γ ⊢ d :: τ2 →
                Δ , Γ ⊢ inr τ1 d :: τ1 ⊕ τ2
      TACase  : ∀{Δ Γ d τ1 τ2 τ x d1 y d2} →
                Δ , Γ ⊢ d :: τ1 ⊕ τ2 →
                Δ , (Γ ,, (x , τ1)) ⊢ d1 :: τ →
                Δ , (Γ ,, (y , τ2)) ⊢ d2 :: τ →
                Δ , Γ ⊢ case d x d1 y d2 :: τ
      TAEHole : ∀{Δ Γ σ u Γ' τ} →
                (u , (Γ' , τ)) ∈ Δ →
                Δ , Γ ⊢ σ :s: Γ' →
                Δ , Γ ⊢ ⦇-⦈⟨ u , σ ⟩ :: τ
      TANEHole : ∀{Δ Γ d τ' Γ' u σ τ} →
                 (u , (Γ' , τ)) ∈ Δ →
                 Δ , Γ ⊢ d :: τ' →
                 Δ , Γ ⊢ σ :s: Γ' →
                 Δ , Γ ⊢ ⦇⌜ d ⌟⦈⟨ u , σ ⟩ :: τ
      TACast  : ∀{Δ Γ d τ1 τ2} →
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
  [ d / y ] (·λ x [ x₁ ] d')
    with natEQ x y
  [ d / y ] (·λ .y [ τ ] d') | Inl refl = ·λ y [ τ ] d'
  [ d / y ] (·λ x [ τ ] d')  | Inr x₁ = ·λ x [ τ ] ( [ d / y ] d')
  [ d / y ] (d1 ∘ d2) = ([ d / y ] d1) ∘ ([ d / y ] d2)
  [ d / y ] (inl τ d') = inl τ ([ d / y ] d')
  [ d / y ] (inr τ d') = inr τ ([ d / y ] d')
  [ d / y ] (case d' x d1 z d2)
    with natEQ x y | natEQ z y
  ... | Inl refl | Inl refl = case ([ d / y ] d') x d1 z d2
  ... | Inl refl | Inr neq  = case ([ d / y ] d') x d1 z ([ d / y ] d2)
  ... | Inr neq  | Inl refl = case ([ d / y ] d') x ([ d / y ] d1) z d2
  ... | Inr neq1 | Inr neq2 = case ([ d / y ] d') x ([ d / y ] d1) z ([ d / y ] d2)
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
    VNum : ∀{n} → (N n) val
    VLam : ∀{x τ d} → (·λ x [ τ ] d) val
    VInl : ∀{d τ} → d val → (inl τ d) val
    VInr : ∀{d τ} → d val → (inr τ d) val

  -- boxed values
  data _boxedval : (d : ihexp) → Set where
    BVVal      : ∀{d} → d val → d boxedval
    BVInl      : ∀{d τ} → d boxedval → (inl τ d) boxedval
    BVInr      : ∀{d τ} → d boxedval → (inr τ d) boxedval
    BVArrCast  : ∀{d τ1 τ2 τ3 τ4} →
                 τ1 ==> τ2 ≠ τ3 ==> τ4 →
                 d boxedval →
                 d ⟨ (τ1 ==> τ2) ⇒ (τ3 ==> τ4) ⟩ boxedval
    BVSumCast  : ∀{d τ1 τ2 τ3 τ4} →
                 τ1 ⊕ τ2 ≠ τ3 ⊕ τ4 →
                 d boxedval →
                 d ⟨ (τ1 ⊕ τ2) ⇒ (τ3 ⊕ τ4) ⟩ boxedval
    BVHoleCast : ∀{τ d} →
                 τ ground →
                 d boxedval →
                 d ⟨ τ ⇒ ⦇-⦈ ⟩ boxedval
    
  mutual
    -- indeterminate forms
    data _indet : (d : ihexp) → Set where
      IPlus1   : ∀{d1 d2} →
                 d1 indet →
                 d2 final →
                 (d1 ·+ d2) indet
      IPlus2   : ∀{d1 d2} →
                 d1 final →
                 d2 indet →
                 (d1 ·+ d2) indet
      IAp      : ∀{d1 d2} →
                 ((τ1 τ2 τ3 τ4 : htyp) (d1' : ihexp) →
                  d1 ≠ (d1' ⟨(τ1 ==> τ2) ⇒ (τ3 ==> τ4)⟩)) →
                 d1 indet →
                 d2 final →
                 (d1 ∘ d2) indet
      IInl     : ∀{d τ} →
                 d indet →
                 (inl τ d) indet
      IInr     : ∀{d τ} →
                 d indet →
                 (inr τ d) indet
      ICase    : ∀{d x d1 y d2} →
                 ((τ : htyp) (d' : ihexp) →
                  d ≠ inl τ d') →
                 ((τ : htyp) (d' : ihexp) →
                  d ≠ inr τ d') →
                 ((τ1 τ2 τ1' τ2' : htyp) (d' : ihexp) →
                  d ≠ (d' ⟨(τ1 ⊕ τ2) ⇒ (τ1' ⊕ τ2')⟩)) →
                 d indet →
                 (case d x d1 y d2) indet
      IEHole   : ∀{u σ} → ⦇-⦈⟨ u , σ ⟩ indet
      INEHole  : ∀{d u σ} →
                 d final →
                 ⦇⌜ d ⌟⦈⟨ u , σ ⟩ indet
      ICastArr : ∀{d τ1 τ2 τ3 τ4} →
                 τ1 ==> τ2 ≠ τ3 ==> τ4 →
                 d indet →
                 d ⟨ (τ1 ==> τ2) ⇒ (τ3 ==> τ4) ⟩ indet
      ICastSum : ∀{d τ1 τ2 τ3 τ4} →
                 τ1 ⊕ τ2 ≠ τ3 ⊕ τ4 →
                 d indet →
                 d ⟨ (τ1 ⊕ τ2) ⇒ (τ3 ⊕ τ4) ⟩ indet
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
      FIndet    : ∀{d} → d indet    → d final


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
    ECPlus1 : ∀{d ε} →
              ε evalctx →
              (ε ·+₁ d) evalctx
    ECPlus2 : ∀{d ε} →
              -- d final → -- red brackets
              ε evalctx →
              (d ·+₂ ε) evalctx
    ECAp1   : ∀{d ε} →
              ε evalctx →
              (ε ∘₁ d) evalctx
    ECAp2   : ∀{d ε} →
              -- d final → -- red brackets
              ε evalctx →
              (d ∘₂ ε) evalctx
    ECCase  : ∀{ε x d1 y d2} →
              ε evalctx →
              (case ε x d1 y d2) evalctx
    ECNEHole : ∀{ε u σ} →
               ε evalctx →
               ⦇⌜ ε ⌟⦈⟨ u , σ ⟩ evalctx
    ECCast  : ∀{ε τ1 τ2} →
              ε evalctx →
              (ε ⟨ τ1 ⇒ τ2 ⟩) evalctx
    ECFailedCast : ∀{ε τ1 τ2} →
                   ε evalctx →
                   ε ⟨ τ1 ⇒⦇-⦈⇏ τ2 ⟩ evalctx

  -- d is the result of filling the hole in ε with d'
  data _==_⟦_⟧ : (d : ihexp) (ε : ectx) (d' : ihexp) → Set where
    FHOuter : ∀{d} → d == ⊙ ⟦ d ⟧
    FHPlus1 : ∀{d1 d1' d2 ε} →
              d1 == ε ⟦ d1' ⟧ →
              (d1 ·+ d2) == (ε ·+₁ d2) ⟦ d1' ⟧
    FHPlus2 : ∀{d1 d2 d2' ε} →
              -- d1 final → -- red brackets
              d2 == ε ⟦ d2' ⟧ →
              (d1 ·+ d2) == (d1 ·+₂ ε) ⟦ d2' ⟧
    FHAp1   : ∀{d1 d1' d2 ε} →
              d1 == ε ⟦ d1' ⟧ →
              (d1 ∘ d2) == (ε ∘₁ d2) ⟦ d1' ⟧
    FHAp2    : ∀{d1 d2 d2' ε} →
               -- d1 final → -- red brackets
               d2 == ε ⟦ d2' ⟧ →
               (d1 ∘ d2) == (d1 ∘₂ ε) ⟦ d2' ⟧
    FHCase   : ∀{d d' x d1 y d2 ε} →
               d == ε ⟦ d' ⟧ →
               (case d x d1 y d2) == (case ε x d1 y d2) ⟦ d' ⟧
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
    MGArr : ∀{τ1 τ2} →
            (τ1 ==> τ2) ≠ (⦇-⦈ ==> ⦇-⦈) →
            (τ1 ==> τ2) ▸gnd (⦇-⦈ ==> ⦇-⦈)
    MGSum : ∀{τ1 τ2} →
            (τ1 ⊕ τ2) ≠ (⦇-⦈ ⊕ ⦇-⦈) →
            (τ1 ⊕ τ2) ▸gnd (⦇-⦈ ⊕ ⦇-⦈)

  -- instruction transition judgement
  data _→>_ : (d d' : ihexp) → Set where
    ITPlus     : ∀{n1 n2 n3} →
                 (n1 nat+ n2) == n3 →
                 ((N n1) ·+ (N n2)) →> (N n3)
    ITLam      : ∀{x τ d1 d2} →
                 -- d2 final → -- red brackets
                 ((·λ x [ τ ] d1) ∘ d2) →> ([ d2 / x ] d1)
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

  -- freshness
  mutual
    -- ... with respect to a hole context
    data envfresh : Nat → env → Set where
      EFId : ∀{x Γ} → x # Γ → envfresh x (Id Γ)
      EFSubst : ∀{x d σ y} →
                fresh x d →
                envfresh x σ →
                x ≠ y →
                envfresh x (Subst d y σ)

    -- ... for inernal expressions
    data fresh : Nat → ihexp → Set where
      FNum    : ∀{x n} → fresh x (N n)
      FPlus   : ∀{x d1 d2} → fresh x d1 → fresh x d2 → fresh x (d1 ·+ d2)
      FVar    : ∀{x y} → x ≠ y → fresh x (X y)
      FLam    : ∀{x y τ d} → x ≠ y → fresh x d → fresh x (·λ y [ τ ] d)
      FAp     : ∀{x d1 d2} → fresh x d1 → fresh x d2 → fresh x (d1 ∘ d2)
      FInl    : ∀{x d τ} → fresh x d → fresh x (inl τ d)
      FInr    : ∀{x d τ} → fresh x d → fresh x (inr τ d)
      FCase   : ∀{x d y d1 z d2} → fresh x d → x ≠ y → fresh x d1 → x ≠ z → fresh x d2 →
                fresh x (case d y d1 z d2)
      FHole   : ∀{x u σ} → envfresh x σ → fresh x (⦇-⦈⟨ u , σ ⟩)
      FNEHole : ∀{x d u σ} → envfresh x σ → fresh x d → fresh x (⦇⌜ d ⌟⦈⟨ u , σ ⟩)
      FCast   : ∀{x d τ1 τ2} → fresh x d → fresh x (d ⟨ τ1 ⇒ τ2 ⟩)
      FFailedCast : ∀{x d τ1 τ2} → fresh x d → fresh x (d ⟨ τ1 ⇒⦇-⦈⇏ τ2 ⟩)

  -- ... for external expressions
  data freshh : Nat → hexp → Set where
    FRHNum    : ∀{x n} → freshh x (N n)
    FRHPlus   : ∀{x d1 d2} → freshh x d1 → freshh x d2 → freshh x (d1 ·+ d2)
    FRHAsc    : ∀{x e τ} → freshh x e → freshh x (e ·: τ)
    FRHVar    : ∀{x y} → x ≠ y → freshh x (X y)
    FRHLam1   : ∀{x y e} → x ≠ y → freshh x e → freshh x (·λ y e)
    FRHLam2   : ∀{x τ e y} → x ≠ y → freshh x e → freshh x (·λ y [ τ ] e)
    FRHAp     : ∀{x e1 e2} → freshh x e1 → freshh x e2 → freshh x (e1 ∘ e2)
    FInl      : ∀{x d} → freshh x d → freshh x (inl d)
    FInr      : ∀{x d} → freshh x d → freshh x (inr d)
    FCase     : ∀{x d y d1 z d2} → freshh x d → x ≠ y → freshh x d1 → x ≠ z → freshh x d2 →
                freshh x (case d y d1 z d2)
    FRHEHole  : ∀{x u} → freshh x (⦇-⦈[ u ])
    FRHNEHole : ∀{x u e} → freshh x e → freshh x (⦇⌜ e ⌟⦈[ u ])

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
                 unbound-in x (·λ_[_]_ y τ d)
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
                 binders-disjoint d1 d2 →
                 binders-disjoint-σ σ d2 →
                 binders-disjoint-σ (Subst d1 y σ) d2

    -- two terms that do not share any binders
    data binders-disjoint : (d1 : ihexp) → (d2 : ihexp) → Set where
      BDNum    : ∀{d n} → binders-disjoint (N n) d
      BDPlus   : ∀{d1 d2 d3} →
                 binders-disjoint d1 d3 →
                 binders-disjoint d2 d3 →
                 binders-disjoint (d1 ·+ d2) d3
      BDVar    : ∀{x d} → binders-disjoint (X x) d
      BDLam    : ∀{x τ d1 d2} →
                 binders-disjoint d1 d2 →
                 unbound-in x d2 →
                 binders-disjoint (·λ_[_]_ x τ d1) d2
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
      BUσId    : ∀{Γ} → binders-unique-σ (Id Γ)
      BUσSubst : ∀{d y σ} →
                 binders-unique d →
                 binders-unique-σ σ →
                 binders-disjoint-σ σ d →
                 binders-unique-σ (Subst d y σ)

    -- all the variable names in the term are unique
    data binders-unique : ihexp → Set where
      BUHole   : ∀{n} → binders-unique (N n)
      BUVar    : ∀{x} → binders-unique (X x)
      BULam    : {x : Nat} {τ : htyp} {d : ihexp} →
                 binders-unique d →
                 unbound-in x d →
                 binders-unique (·λ_[_]_ x τ d)
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
      BUCast   : ∀{d τ1 τ2} →
                 binders-unique d →
                 binders-unique (d ⟨ τ1 ⇒ τ2 ⟩)
      BUFailedCast : ∀{d τ1 τ2} →
                     binders-unique d →
                     binders-unique (d ⟨ τ1 ⇒⦇-⦈⇏ τ2 ⟩)
