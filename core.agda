open import Nat
open import Prelude
open import contexts

module core where
  -- type patterns
  data htyppat : Set where
    α   : Nat → htyppat
    ⦇-⦈ : htyppat

  -- types
  data htyp : Set where
    num   : htyp
    ⦇-⦈   : htyp
    _==>_ : htyp → htyp → htyp
    _⊕_   : htyp → htyp → htyp
    _⊠_   : htyp → htyp → htyp
    α     : Nat → htyp
    ⦇⌜_⌟⦈ : Nat → htyp

  -- the type of type variable contexts, i.e. Θ
  tvctx : Set
  tvctx = htyp ctx
    
  -- type constructors bind very tightly
  infixr 25  _==>_
  infixr 25 _⊕_
  infixr 25 _⊠_
  
  -- external expressions
  data hexp : Set where
    N        : Nat → hexp
    _·+_     : hexp → hexp → hexp
    _·:_     : hexp → htyp → hexp
    X        : Nat → hexp
    ·λ       : Nat → hexp → hexp
    ·λ_·[_]_ : Nat → htyp → hexp → hexp
    _∘_      : hexp → hexp → hexp
    inl      : hexp → hexp
    inr      : hexp → hexp
    case     : hexp → Nat → hexp → Nat → hexp → hexp
    ⟨_,_⟩    : hexp → hexp → hexp
    fst      : hexp → hexp
    snd      : hexp → hexp
    ⦇-⦈[_]   : Nat → hexp
    ⦇⌜_⌟⦈[_] : hexp → Nat → hexp

  -- the type of type contexts, i.e. Γs in the judgements below
  tctx : Set
  tctx = htyp ctx

  -- type substitution
  [_/_]_ : htyp → htyppat → htyp → htyp 
  [ τ / ⦇-⦈ ] τ'           = τ'
  [ τ / α a ] num          = num
  [ τ / α a ] (τ1 ==> τ2)  = ([ τ / α a ] τ1) ==> ([ τ / α a ] τ2)
  [ τ / α a ] (τ1 ⊕ τ2)    = ([ τ / α a ] τ1) ⊕ ([ τ / α a ] τ2)
  [ τ / α a ] (τ1 ⊠ τ2)    = ([ τ / α a ] τ1) ⊠ ([ τ / α a ] τ2)
  [ τ / α a ] τ'@(α a')    with natEQ a a'
  ... | Inl refl           = τ
  ... | Inr a≢a'           = τ'
  [ τ / α a ] ⦇-⦈          = ⦇-⦈
  [ α a'' / α a ] ⦇⌜ a' ⌟⦈ with natEQ a a'
  ... | Inl refl           = ⦇⌜ a'' ⌟⦈
  ... | Inr a≢a'           = ⦇⌜ a' ⌟⦈
  [ τ / α a ] ⦇⌜ a' ⌟⦈     = {! !}  -- TODO: Not sure what to do here

  -- type validity
  data _valid : {Θ : tvctx} (t : htyp) -> Set where
    TVArr    : {Θ : tvctx} {τ1 τ2 : htyp} →
               τ1 valid →
               τ2 valid →
               τ1 ==> τ2 valid
    TVVar    : {Θ : tvctx} {τ : htyp} (a : Nat) →
               (a , τ) ∈ Θ →
               α a valid 
    TVEHole  : {Θ : tvctx} → ⦇-⦈ valid
    TVNEHole : {Θ : tvctx} (a : Nat) →
               a # Θ →
               ⦇⌜ a ⌟⦈ valid

  -- type consistency
  data _~_ : (t1 t2 : htyp) → Set where
    TCRefl  : {τ : htyp} → τ ~ τ
    TCHole1 : {τ : htyp} → τ ~ ⦇-⦈
    TCHole2 : {τ : htyp} → ⦇-⦈ ~ τ
    TCNEHole1 : {a : Nat} {τ : htyp} → ⦇⌜ a ⌟⦈ ~ τ
    TCNEHole2 : {a : Nat} {τ : htyp} → τ ~ ⦇⌜ a ⌟⦈
    TCArr   : {τ1 τ2 τ1' τ2' : htyp} →
              τ1 ~ τ1' →
              τ2 ~ τ2' →
              τ1 ==> τ2 ~ τ1' ==> τ2'
    TCSum   : {τ1 τ2 τ1' τ2' : htyp} →
              τ1 ~ τ1' →
              τ2 ~ τ2' →
              τ1 ⊕ τ2 ~ τ1' ⊕ τ2'
    TCProd  : {τ1 τ2 τ1' τ2' : htyp} →
              τ1 ~ τ1' →
              τ2 ~ τ2' →
              τ1 ⊠ τ2 ~ τ1' ⊠ τ2'
  
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

  -- matching for sums
  data _▸prod_ : htyp → htyp → Set where
    MPHole : ⦇-⦈ ▸prod ⦇-⦈ ⊠ ⦇-⦈
    MPProd : {τ1 τ2 : htyp} → τ1 ⊠ τ2 ▸prod τ1 ⊠ τ2
    
  -- the type of hole contexts, i.e. Δs in the judgements
  hctx : Set
  hctx = (htyp ctx × htyp) ctx
  
  -- bidirectional type checking judgements for hexp
  mutual
    -- synthesis
    data _⊢_=>_ : (Γ : tctx) (e : hexp) (τ : htyp) → Set where
      SNum    : {Γ : tctx} {n : Nat} →
                Γ ⊢ N n => num
      SPlus   : {Γ : tctx} {e1 e2 : hexp}  →
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
                Γ ⊢ ·λ x ·[ τ1 ] e => τ1 ==> τ2
      SAp     : {Γ : tctx} {e1 e2 : hexp} {τ τ1 τ2 : htyp} →
                Γ ⊢ e1 => τ1 →
                τ1 ▸arr τ2 ==> τ →
                Γ ⊢ e2 <= τ2 →
                Γ ⊢ (e1 ∘ e2) => τ
      SPair   : ∀{e1 e2 τ1 τ2 Γ} →
                Γ ⊢ e1 => τ1 →
                Γ ⊢ e2 => τ2 →
                Γ ⊢ ⟨ e1 , e2 ⟩ => τ1 ⊠ τ2
      SFst    : ∀{e τ τ1 τ2 Γ} →
                Γ ⊢ e => τ →
                τ ▸prod τ1 ⊠ τ2 →
                Γ ⊢ fst e => τ1
      SSnd    : ∀{e τ τ1 τ2 Γ} →
                Γ ⊢ e => τ →
                τ ▸prod τ1 ⊠ τ2 →
                Γ ⊢ snd e => τ2
      SEHole  : {Γ : tctx} {u : Nat} →
                Γ ⊢ ⦇-⦈[ u ] => ⦇-⦈
      SNEHole : {Γ : tctx} {e : hexp} {τ : htyp} {u : Nat} →
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
      AInl     : {Γ : tctx} {e : hexp} {τ+ τ1 τ2 : htyp} →
                 τ+ ▸sum (τ1 ⊕ τ2) →
                 Γ ⊢ e <= τ1 →
                 Γ ⊢ inl e <= τ+
      AInr     : {Γ : tctx} {e : hexp} {τ+ τ1 τ2 : htyp} →
                 τ+ ▸sum (τ1 ⊕ τ2) →
                 Γ ⊢ e <= τ2 →
                 Γ ⊢ inr e <= τ+
      ACase    : {Γ : tctx} {e e1 e2 : hexp} {τ τ+ τ1 τ2 : htyp} {x y : Nat} →
                 x # Γ →
                 y # Γ →
                 τ+ ▸sum (τ1 ⊕ τ2) →
                 Γ ⊢ e => τ+ →
                 (Γ ,, (x , τ1)) ⊢ e1 <= τ →
                 (Γ ,, (y , τ2)) ⊢ e2 <= τ →
                 Γ ⊢ case e x e1 y e2 <= τ
                 
  -- those types without holes
  data _tcomplete : htyp → Set where
    TCNum  : num tcomplete
    TCArr  : ∀{τ1 τ2} → τ1 tcomplete → τ2 tcomplete → (τ1 ==> τ2) tcomplete
    TCSum  : ∀{τ1 τ2} → τ1 tcomplete → τ2 tcomplete → (τ1 ⊕ τ2) tcomplete
    TCProd : ∀{τ1 τ2} → τ1 tcomplete → τ2 tcomplete → (τ1 ⊠ τ2) tcomplete

  -- those external expressions without holes
  data _ecomplete : hexp → Set where
    ECNum  : ∀{n} →
             (N n) ecomplete
    ECPlus : ∀{e1 e2} →
             e1 ecomplete →
             e2 ecomplete →
             (e1 ·+ e2) ecomplete
    ECAsc  : ∀{τ e} →
             τ tcomplete →
             e ecomplete →
             (e ·: τ) ecomplete
    ECVar  : ∀{x} →
             (X x) ecomplete
    ECLam1 : ∀{x e} →
             e ecomplete →
             (·λ x e) ecomplete
    ECLam2 : ∀{x e τ} →
             e ecomplete →
             τ tcomplete →
             (·λ x ·[ τ ] e) ecomplete
    ECAp   : ∀{e1 e2} →
             e1 ecomplete →
             e2 ecomplete →
             (e1 ∘ e2) ecomplete
    ECInl  : ∀{e} →
             e ecomplete →
             (inl e) ecomplete
    ECInr  : ∀{e} →
             e ecomplete →
             (inr e) ecomplete
    ECCase : ∀{e x e1 y e2} →
             e ecomplete →
             e1 ecomplete →
             e2 ecomplete →
             (case e x e1 y e2) ecomplete
    ECPair : ∀{e1 e2} →
             e1 ecomplete →
             e2 ecomplete →
             ⟨ e1 , e2 ⟩ ecomplete
    ECFst  : ∀{e} →
             e ecomplete →
             (fst e) ecomplete
    ECSnd  : ∀{e} →
             e ecomplete →
             (snd e) ecomplete
            
  -- contexts that only produce complete types
  _gcomplete : tctx → Set
  Γ gcomplete = (x : Nat) (τ : htyp) → (x , τ) ∈ Γ → τ tcomplete


  -- ground types
  data _ground : htyp → Set where
    GNum      : num ground
    GArrHole  : ⦇-⦈ ==> ⦇-⦈ ground
    GSumHole  : ⦇-⦈ ⊕ ⦇-⦈ ground
    GProdHole : ⦇-⦈ ⊠ ⦇-⦈ ground

