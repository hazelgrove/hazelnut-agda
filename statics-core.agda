open import List
open import Nat
open import Prelude
open import contexts
open import core

module statics-core where
  open core public
  
   -- zippered form of types
  data ztyp : Set where
    ▹_◃    : htyp → ztyp
    _==>₁_ : ztyp → htyp → ztyp
    _==>₂_ : htyp → ztyp → ztyp
    _⊕₁_   : ztyp → htyp → ztyp
    _⊕₂_   : htyp → ztyp → ztyp
    _⊠₁_   : ztyp → htyp → ztyp
    _⊠₂_   : htyp → ztyp → ztyp
  
  -- zippered form of expressions
  data zexp : Set where
    ▹_◃        : hexp → zexp
    _·:₁_      : zexp → htyp → zexp
    _·:₂_      : hexp → ztyp → zexp
    ·λ         : Nat → zexp → zexp
    ·λ_·[_]₁_  : Nat → ztyp → hexp → zexp
    ·λ_·[_]₂_  : Nat → htyp → zexp → zexp
    _∘₁_       : zexp → hexp → zexp
    _∘₂_       : hexp → zexp → zexp
    _·+₁_      : zexp → hexp → zexp
    _·+₂_      : hexp → zexp → zexp
    ⦇⌜_⌟⦈[_]   : zexp → Nat → zexp
    inl        : zexp → zexp
    inr        : zexp → zexp
    case₁      : zexp → Nat → hexp → Nat → hexp → zexp
    case₂      : hexp → Nat → zexp → Nat → hexp → zexp
    case₃      : hexp → Nat → hexp → Nat → zexp → zexp
    ⟨_,_⟩₁     : zexp → hexp → zexp
    ⟨_,_⟩₂     : hexp → zexp → zexp
    fst        : zexp → zexp
    snd        : zexp → zexp
    
  -- erasure of cursor for types and expressions, judgementally. see
  -- jugemental-erase.agda for an argument that this defines an isomorphic
  -- object to the direct metafunction provided in the text of the paper
  data erase-t : ztyp → htyp → Set where
    ETTop   : ∀{t} →
              erase-t (▹ t ◃) t
    ETArrL  : ∀{t1 t1' t2} →
              erase-t t1 t1' →
              erase-t (t1 ==>₁ t2) (t1' ==> t2)
    ETArrR  : ∀{t1 t2 t2'} →
              erase-t t2 t2' →
              erase-t (t1 ==>₂ t2) (t1 ==> t2')
    ETPlusL : ∀{t1 t1' t2} →
              erase-t t1 t1' →
              erase-t (t1 ⊕₁ t2) (t1' ⊕ t2)
    ETPlusR : ∀{t1 t2 t2'} →
              erase-t t2 t2' →
              erase-t (t1 ⊕₂ t2) (t1 ⊕ t2')
    ETProdL : ∀{t1 t1' t2} →
              erase-t t1 t1' →
              erase-t (t1 ⊠₁ t2) (t1' ⊠ t2)
    ETProdR : ∀{t1 t2 t2'} →
              erase-t t2 t2' →
              erase-t (t1 ⊠₂ t2) (t1 ⊠ t2')
    
  data erase-e : zexp → hexp → Set where
    EETop      : ∀{x} →
                 erase-e (▹ x ◃) x
    EEPlusL    : ∀{e1 e1' e2} →
                 erase-e e1 e1' →
                 erase-e (e1 ·+₁ e2) (e1' ·+ e2)
    EEPlusR    : ∀{e1 e2 e2'} →
                 erase-e e2 e2' →
                 erase-e (e1 ·+₂ e2) (e1 ·+ e2')
    EEAscL     : ∀{e e' t} →
                 erase-e e e' →
                 erase-e (e ·:₁ t) (e' ·: t)
    EEAscR     : ∀{e t t'} →
                 erase-t t t' →
                 erase-e (e ·:₂ t) (e ·: t')
    EELam      : ∀{x e e'} →
                 erase-e e e' →
                 erase-e (·λ x e) (·λ x e')
    EEHalfLamL : ∀{x e t t'} →
                 erase-t t t' →
                 erase-e (·λ x ·[ t ]₁ e) (·λ x ·[ t' ] e)
    EEHalfLamR : ∀{x e e' t} →
                 erase-e e e' →
                 erase-e (·λ x ·[ t ]₂ e) (·λ x ·[ t ] e')
    EEApL      : ∀{e1 e1' e2} →
                 erase-e e1 e1' →
                 erase-e (e1 ∘₁ e2) (e1' ∘ e2)
    EEApR      : ∀{e1 e2 e2'} →
                 erase-e e2 e2' →
                 erase-e (e1 ∘₂ e2) (e1 ∘ e2')
    EEInl      : ∀{e e'} →
                 erase-e e e' →
                 erase-e (inl e) (inl e')
    EEInr      : ∀{e e'} →
                 erase-e e e' →
                 erase-e (inr e) (inr e')
    EECase1    : ∀{e e' x e1 y e2} →
                 erase-e e e' →
                 erase-e (case₁ e x e1 y e2) (case e' x e1 y e2)
    EECase2    : ∀{e x e1 e1' y e2} →
                 erase-e e1 e1' →
                 erase-e (case₂ e x e1 y e2) (case e x e1' y e2)
    EECase3    : ∀{e x e1 y e2 e2'} →
                 erase-e e2 e2' →
                 erase-e (case₃ e x e1 y e2) (case e x e1 y e2')
    EEPairL    : ∀{e1 e1' e2} →
                 erase-e e1 e1' →
                 erase-e ⟨ e1 , e2 ⟩₁ ⟨ e1' , e2 ⟩
    EEPairR    : ∀{e1 e2 e2'} →
                 erase-e e2 e2' →
                 erase-e ⟨ e1 , e2 ⟩₂ ⟨ e1 , e2' ⟩
    EEFst      : ∀{e e'} →
                 erase-e e e' →
                 erase-e (fst e) (fst e')
    EESnd      : ∀{e e'} →
                 erase-e e e' →
                 erase-e (snd e) (snd e')
    EENEHole   : ∀{e e' u} →
                 erase-e e e' →
                 erase-e ⦇⌜ e ⌟⦈[ u ] ⦇⌜ e' ⌟⦈[ u ]
    
  -- the three grammars that define actions
  data direction : Set where
    child  : Nat → direction
    parent : direction

  -- in contrast to the POPL 2017 hazelnut paper, we include named holes in static
  -- semantics since they are required by the dynamic semantics. a given action
  -- may introduce a different number of holes depending on the context it is
  -- applied in, so the action must always supply enough names for every location
  -- in the term where a hole could occur. moreover, care must be taken to have
  -- the same hole names always correspond to the same hole locations. for example,
  -- when we show that each derivation has an equivalently subsumption-minimal
  -- derivation, this is needed to guarentee the same action (which includes hole names)
  -- can be used in the minimal derivation.
  data shape : Set where
    arrow  : shape
    num    : shape
    asc    : shape
    var    : Nat → Nat → shape
    lam    : Nat → Nat → Nat → shape
    ap     : Nat → Nat → shape
    numlit : Nat → Nat → shape
    plus   : Nat → Nat → shape
    nehole : Nat → shape
    sum    : shape
    inl    : Nat → Nat → shape
    inr    : Nat → Nat → shape
    case   : Nat → Nat → Nat → Nat → Nat → shape
    prod   : shape
    pair   : Nat → Nat → shape
    fst    : Nat → shape
    snd    : Nat → shape

  data action : Set where
    move      : direction → action
    construct : shape → action
    del       : Nat → action
    finish    : action

  -- type actions
  data _+_+>_ : (t : ztyp) → (α : action) → (t' : ztyp) → Set where
    TMArrChild1   : {t1 t2 : htyp} →
                    ▹ t1 ==> t2 ◃ + move (child 1) +> (▹ t1 ◃ ==>₁ t2)
    TMArrChild2   : {t1 t2 : htyp} →
                    ▹ t1 ==> t2 ◃ + move (child 2) +> (t1 ==>₂ ▹ t2 ◃)
    TMArrParent1  : {t1 t2 : htyp} →
                    (▹ t1 ◃ ==>₁ t2) + move parent +> ▹ t1 ==> t2 ◃
    TMArrParent2  : {t1 t2 : htyp} →
                    (t1 ==>₂ ▹ t2 ◃) + move parent +> ▹ t1 ==> t2 ◃
    TMPlusChild1  : {t1 t2 : htyp} →
                    ▹ t1 ⊕ t2 ◃ + move (child 1) +> (▹ t1 ◃ ⊕₁ t2)
    TMPlusChild2  : {t1 t2 : htyp} →
                    ▹ t1 ⊕ t2 ◃ + move (child 2) +> (t1 ⊕₂ ▹ t2 ◃)
    TMPlusParent1 : {t1 t2 : htyp} →
                    (▹ t1 ◃ ⊕₁ t2) + move parent +> ▹ t1 ⊕ t2 ◃
    TMPlusParent2 : {t1 t2 : htyp} →
                    (t1 ⊕₂ ▹ t2 ◃) + move parent +> ▹ t1 ⊕ t2 ◃
    TMProdChild1  : {t1 t2 : htyp} →
                    ▹ t1 ⊠ t2 ◃ + move (child 1) +> (▹ t1 ◃ ⊠₁ t2)
    TMProdChild2  : {t1 t2 : htyp} →
                    ▹ t1 ⊠ t2 ◃ + move (child 2) +> (t1 ⊠₂ ▹ t2 ◃)
    TMProdParent1 : {t1 t2 : htyp} →
                    (▹ t1 ◃ ⊠₁ t2) + move parent +> ▹ t1 ⊠ t2 ◃
    TMProdParent2 : {t1 t2 : htyp} →
                    (t1 ⊠₂ ▹ t2 ◃) + move parent +> ▹ t1 ⊠ t2 ◃
    TMDel         : {t : htyp} {u : Nat} →
                    (▹ t ◃) + del u +> (▹ ⦇-⦈ ◃)
    TMConArrow    : {t : htyp} →
                    (▹ t ◃) + construct arrow +> (t ==>₂ ▹ ⦇-⦈ ◃)
    TMConPlus     : {t : htyp} →
                    (▹ t ◃) + construct sum +> (t ⊕₂ ▹ ⦇-⦈ ◃)
    TMConProd     : {t : htyp} →
                    (▹ t ◃) + construct prod +> (t ⊠₂ ▹ ⦇-⦈ ◃)
    TMConNum      : (▹ ⦇-⦈ ◃) + construct num +> (▹ num ◃)
    TMArrZip1     : {t1 t1' : ztyp} {t2 : htyp} {α : action} →
                    (t1 + α +> t1') →
                    ((t1 ==>₁ t2) + α +> (t1' ==>₁ t2))
    TMArrZip2     : {t2 t2' : ztyp} {t1 : htyp} {α : action} →
                    (t2 + α +> t2') →
                    ((t1 ==>₂ t2) + α +> (t1 ==>₂ t2'))
    TMPlusZip1    : {t1 t1' : ztyp} {t2 : htyp} {α : action} →
                    (t1 + α +> t1') →
                    ((t1 ⊕₁ t2) + α +> (t1' ⊕₁ t2))
    TMPlusZip2    : {t2 t2' : ztyp} {t1 : htyp} {α : action} →
                    (t2 + α +> t2') →
                    ((t1 ⊕₂ t2) + α +> (t1 ⊕₂ t2'))
    TMProdZip1    : {t1 t1' : ztyp} {t2 : htyp} {α : action} →
                    (t1 + α +> t1') →
                    ((t1 ⊠₁ t2) + α +> (t1' ⊠₁ t2))
    TMProdZip2    : {t2 t2' : ztyp} {t1 : htyp} {α : action} →
                    (t2 + α +> t2') →
                    ((t1 ⊠₂ t2) + α +> (t1 ⊠₂ t2'))

  -- expression movement
  data _+_+>e_ : (e : zexp) → (α : action) → (e' : zexp) → Set where
    EMPlusChild1     : {e1 e2 : hexp} →
                       (▹ e1 ·+ e2 ◃) + move (child 1) +>e (▹ e1 ◃ ·+₁ e2)
    EMPlusChild2     : {e1 e2 : hexp} →
                       (▹ e1 ·+ e2 ◃) + move (child 2) +>e (e1 ·+₂ ▹ e2 ◃)
    EMPlusParent1    : {e1 e2 : hexp} →
                       (▹ e1 ◃ ·+₁ e2) + move parent +>e (▹ e1 ·+ e2 ◃)
    EMPlusParent2    : {e1 e2 : hexp} →
                       (e1 ·+₂ ▹ e2 ◃) + move parent +>e (▹ e1 ·+ e2 ◃)    
    EMAscChild1      : {e : hexp} {t : htyp} →
                       (▹ e ·: t ◃) + move (child 1) +>e (▹ e ◃ ·:₁ t)
    EMAscChild2      : {e : hexp} {t : htyp} →
                       (▹ e ·: t ◃) + move (child 2) +>e (e  ·:₂ ▹ t ◃)
    EMAscParent1     : {e : hexp} {t : htyp} →
                       (▹ e ◃ ·:₁ t) + move parent +>e (▹ e ·: t ◃)
    EMAscParent2     : {e : hexp} {t : htyp} →
                       (e ·:₂ ▹ t ◃) + move parent +>e (▹ e ·: t ◃)
    EMLamChild1      : {e : hexp} {x : Nat} →
                       ▹ (·λ x e) ◃ + move (child 1) +>e ·λ x (▹ e ◃)
    EMLamParent      : {e : hexp} {x : Nat} →
                       ·λ x (▹ e ◃) + move parent +>e ▹ (·λ x e) ◃
    EMHalfLamChild1  : {e : hexp} {t : htyp} {x : Nat} →
                       ▹ (·λ x ·[ t ] e) ◃ + move (child 1) +>e (·λ x ·[ ▹ t ◃ ]₁ e)
    EMHalfLamChild2  : {e : hexp} {t : htyp} {x : Nat} →
                       ▹ (·λ x ·[ t ] e) ◃ + move (child 2) +>e (·λ x ·[ t ]₂ ▹ e ◃)
    EMHalfLamParent1 : {e : hexp} {t : htyp} {x : Nat} →
                       (·λ x ·[ ▹ t ◃ ]₁ e)  + move parent +>e ▹ (·λ x ·[ t ] e) ◃
    EMHalfLamParent2 : {e : hexp} {t : htyp} {x : Nat} →
                       (·λ x ·[ t ]₂ ▹ e ◃) + move parent +>e ▹ (·λ x ·[ t ] e) ◃
    EMApChild1       : {e1 e2 : hexp} →
                       (▹ e1 ∘ e2 ◃) + move (child 1)+>e (▹ e1 ◃ ∘₁ e2)
    EMApChild2       : {e1 e2 : hexp} →
                       (▹ e1 ∘ e2 ◃) + move (child 2) +>e (e1 ∘₂ ▹ e2 ◃)
    EMApParent1      : {e1 e2 : hexp} →
                       (▹ e1 ◃ ∘₁ e2) + move parent +>e (▹ e1 ∘ e2 ◃)
    EMApParent2      : {e1 e2 : hexp} →
                       (e1 ∘₂ ▹ e2 ◃) + move parent +>e (▹ e1 ∘ e2 ◃)
    EMInlChild1      : {e : hexp} →
                       ▹ inl e ◃ + move (child 1) +>e inl ▹ e ◃
    EMInlParent      : {e : hexp} →
                       inl ▹ e ◃ + move parent +>e ▹ inl e  ◃
    EMInrChild1      : {e : hexp} →
                       ▹ inr e ◃ + move (child 1) +>e inr ▹ e ◃
    EMInrParent      : {e : hexp} →
                       inr ▹ e ◃ + move parent +>e ▹ inr e  ◃
    EMCaseParent1    : {e e1 e2 : hexp} {x y : Nat} →
                       case₁ ▹ e ◃ x e1 y e2 + move parent +>e ▹ case e x e1 y e2 ◃
    EMCaseParent2    : {e e1 e2 : hexp} {x y : Nat} →
                       case₂ e x ▹ e1 ◃ y e2 + move parent +>e ▹ case e x e1 y e2 ◃
    EMCaseParent3    : {e e1 e2 : hexp} {x y : Nat} →
                       case₃ e x e1 y ▹ e2 ◃ + move parent +>e ▹ case e x e1 y e2 ◃
    EMCaseChild1     : {e e1 e2 : hexp} {x y : Nat} →
                       ▹ case e x e1 y e2 ◃ + move (child 1) +>e case₁ ▹ e ◃ x e1 y e2
    EMCaseChild2     : {e e1 e2 : hexp} {x y : Nat} →
                       ▹ case e x e1 y e2 ◃ + move (child 2) +>e case₂ e x ▹ e1 ◃ y e2
    EMCaseChild3     : {e e1 e2 : hexp} {x y : Nat} →
                       ▹ case e x e1 y e2 ◃ + move (child 3) +>e case₃ e x e1 y ▹ e2 ◃
    EMPairChild1     : {e1 e2 : hexp} →
                       (▹ ⟨ e1 , e2 ⟩ ◃) + move (child 1)+>e ⟨ ▹ e1 ◃ , e2 ⟩₁
    EMPairChild2     : {e1 e2 : hexp} →
                       (▹ ⟨ e1 , e2 ⟩ ◃) + move (child 2) +>e ⟨ e1 , ▹ e2 ◃ ⟩₂
    EMPairParent1    : {e1 e2 : hexp} →
                       ( ⟨ ▹ e1 ◃ , e2 ⟩₁ ) + move parent +>e (▹ ⟨ e1 , e2 ⟩ ◃)
    EMPairParent2    : {e1 e2 : hexp} →
                       ( ⟨ e1 , ▹ e2 ◃ ⟩₂ ) + move parent +>e (▹ ⟨ e1 , e2 ⟩ ◃)
    EMFstChild1      : {e : hexp} →
                       ▹ fst e ◃ + move (child 1) +>e fst ▹ e ◃
    EMFstParent      : {e : hexp} →
                       fst ▹ e ◃ + move parent +>e ▹ fst e  ◃
    EMSndChild1      : {e : hexp} →
                       ▹ snd e ◃ + move (child 1) +>e snd ▹ e ◃
    EMSndParent      : {e : hexp} →
                       snd ▹ e ◃ + move parent +>e ▹ snd e  ◃
    EMNEHoleChild1   : {e : hexp} {u : Nat} →
                       (▹ ⦇⌜ e ⌟⦈[ u ] ◃) + move (child 1) +>e ⦇⌜ ▹ e ◃ ⌟⦈[ u ]
    EMNEHoleParent   : {e : hexp} {u : Nat} →
                       ⦇⌜ ▹ e ◃ ⌟⦈[ u ] + move parent +>e (▹ ⦇⌜ e ⌟⦈[ u ] ◃)
  
  mutual
  -- synthetic action expressions. 
    data _⊢_=>_~_~>_=>_ : (Γ : tctx) → (e1 : zexp) → (t1 : htyp) → (α : action) →
                          (e2 : zexp) → (t2 : htyp) → Set where
      SAFinish    : {Γ : tctx} {e : hexp} {t : htyp} {u : Nat} →
                    Γ ⊢ e => t →
                    Γ ⊢ ▹ ⦇⌜ e ⌟⦈[ u ] ◃ => ⦇-⦈ ~ finish ~> ▹ e ◃ => t
      SAMove      : {δ : direction} {e e' : zexp} {Γ : tctx} {t : htyp} →
                    e + move δ +>e e' →
                    Γ ⊢ e => t ~ move δ ~> e' => t
      SADel       : {Γ : tctx} {e : hexp} {t : htyp} {u : Nat} →
                    Γ ⊢ ▹ e ◃ => t ~ del u ~> ▹ ⦇-⦈[ u ] ◃ => ⦇-⦈
      SAConNumlit : {Γ : tctx} {n : Nat} {u u1 : Nat} →
                    Γ ⊢ ▹ ⦇-⦈[ u ] ◃ => ⦇-⦈ ~ construct (numlit n u1) ~> ▹ N n ◃ => num
      SAConPlus1  : {Γ : tctx} {e : hexp} {t : htyp} {u1 u2 : Nat} →
                    t ~ num →
                    Γ ⊢ ▹ e ◃ => t ~ construct (plus u1 u2) ~> e ·+₂ ▹ ⦇-⦈[ u2 ] ◃ => num
      SAConPlus2  : {Γ : tctx} {e : hexp} {t : htyp} {u1 u2 : Nat} →
                    t ~̸ num →
                    Γ ⊢ ▹ e ◃ => t ~ construct (plus u1 u2) ~>
                      ⦇⌜ e ⌟⦈[ u1 ] ·+₂ ▹ ⦇-⦈[ u2 ] ◃ => num
      SAConAsc    : {Γ : tctx} {e : hexp} {t : htyp} →
                    Γ ⊢ ▹ e ◃ => t ~ construct asc  ~> (e ·:₂ ▹ t ◃ ) => t
      SAConVar    : {Γ : tctx} {x : Nat} {t : htyp} {u u1 : Nat} →
                    (x , t) ∈ Γ →
                      Γ ⊢ ▹ ⦇-⦈[ u ] ◃ => ⦇-⦈ ~ construct (var x u1) ~> ▹ X x ◃ => t
      SAConLam    : {Γ : tctx} {x : Nat} {u u1 u2 : Nat} →
                    x # Γ →
                    Γ ⊢ ▹ ⦇-⦈[ u ] ◃ => ⦇-⦈ ~ construct (lam x u1 u2) ~>
                      (·λ x ·[ ▹ ⦇-⦈ ◃ ]₁ ⦇-⦈[ u2 ]) => (⦇-⦈ ==> ⦇-⦈)
      SAConApArr  : {Γ : tctx} {t t1 t2 : htyp} {e : hexp} {u1 u2 : Nat} →
                    t ▸arr (t1 ==> t2) →
                    Γ ⊢ ▹ e ◃ => t ~ construct (ap u1 u2) ~>
                      e ∘₂ ▹ ⦇-⦈[ u2 ] ◃ => t2
      SAConApOtw  : {Γ : tctx} {t : htyp} {e : hexp} {u1 u2 : Nat} →
                    t ~̸ (⦇-⦈ ==> ⦇-⦈) →
                    Γ ⊢ ▹ e ◃ => t ~ construct (ap u1 u2) ~>
                      ⦇⌜ e ⌟⦈[ u1 ] ∘₂ ▹ ⦇-⦈[ u2 ] ◃ => ⦇-⦈  
      SAConInl    : {Γ : tctx} {t : htyp} {u u1 u2 : Nat} →
                    Γ ⊢ ▹ ⦇-⦈[ u ] ◃ => t ~ construct (inl u1 u2) ~>
                      inl (⦇-⦈[ u2 ]) ·:₂ (▹ ⦇-⦈ ◃ ⊕₁ ⦇-⦈) => (⦇-⦈ ⊕ ⦇-⦈)
      SAConInr    : {Γ : tctx} {t : htyp} {u u1 u2 : Nat} →
                    Γ ⊢ ▹ ⦇-⦈[ u ] ◃ => t ~ construct (inr u1 u2) ~>
                      inr (⦇-⦈[ u2 ]) ·:₂ (⦇-⦈ ⊕₂ ▹ ⦇-⦈ ◃) => (⦇-⦈ ⊕ ⦇-⦈)
      SAConCase1  : {Γ : tctx} {x y : Nat} {t t1 t2 : htyp} {e : hexp} {u1 u2 u3 : Nat} →
                    x # Γ →
                    y # Γ →
                    t ▸sum (t1 ⊕ t2) →
                    Γ ⊢ ▹ e ◃ => t ~ construct (case x y u1 u2 u3) ~>
                      (case₂ e x (▹ ⦇-⦈[ u2 ] ◃) y ⦇-⦈[ u3 ]) ·:₁ ⦇-⦈ => ⦇-⦈
      SAConCase2  : {Γ : tctx} {x y : Nat} {t : htyp} {e : hexp} → {u1 u2 u3 : Nat} →
                    x # Γ →
                    y # Γ →
                    t ~̸ (⦇-⦈ ⊕ ⦇-⦈) →
                    Γ ⊢ ▹ e ◃ => t ~ construct (case x y u1 u2 u3) ~>
                      (case₁ (⦇⌜ ▹ e ◃ ⌟⦈[ u1 ]) x ⦇-⦈[ u2 ] y ⦇-⦈[ u3 ]) ·:₁ ⦇-⦈ => ⦇-⦈
      SAConPair   : {Γ : tctx} {t : htyp} {u u1 u2 : Nat} →
                    Γ ⊢ ▹ ⦇-⦈[ u ] ◃ => t ~ construct (pair u1 u2) ~>
                      ⟨ ▹ ⦇-⦈[ u1 ] ◃ , ⦇-⦈[ u2 ] ⟩₁ => (⦇-⦈ ⊠ ⦇-⦈)
      SAConFst1   : {Γ : tctx} {t t1 t2 : htyp} {e : hexp} {u : Nat} →
                    t ▸prod (t1 ⊠ t2) →
                    Γ ⊢ ▹ e ◃ => t ~ construct (fst u) ~> ▹ fst e ◃ => t1
      SAConFst2   : {Γ : tctx} {t : htyp} {e : hexp} {u : Nat} →
                    t ~̸ (⦇-⦈ ⊠ ⦇-⦈) →
                    Γ ⊢ ▹ e ◃ => t ~ construct (fst u) ~> fst ⦇⌜ ▹ e ◃ ⌟⦈[ u ] => ⦇-⦈
      SAConSnd1   : {Γ : tctx} {t t1 t2 : htyp} {e : hexp} {u : Nat} →
                    t ▸prod (t1 ⊠ t2) →
                    Γ ⊢ ▹ e ◃ => t ~ construct (snd u) ~> ▹ snd e ◃ => t2
      SAConSnd2   : {Γ : tctx} {t : htyp} {e : hexp} {u : Nat} →
                    t ~̸ (⦇-⦈ ⊠ ⦇-⦈) →
                    Γ ⊢ ▹ e ◃ => t ~ construct (snd u) ~> snd ⦇⌜ ▹ e ◃ ⌟⦈[ u ]  => ⦇-⦈
      SAConNEHole : {Γ : tctx} {e : hexp} {t : htyp} {u : Nat} →
                    Γ ⊢ ▹ e ◃ => t ~ construct (nehole u) ~> ⦇⌜ ▹ e ◃ ⌟⦈[ u ] => ⦇-⦈
      SAZipPlus1  : {Γ : tctx} {e : hexp} {eh eh' : zexp} {α : action} →
                    Γ ⊢ eh ~ α ~> eh' ⇐ num →
                    Γ ⊢ (eh ·+₁ e) => num ~ α ~> (eh' ·+₁ e) => num
      SAZipPlus2  : {Γ : tctx} {e : hexp} {eh eh' : zexp} {α : action} →
                    Γ ⊢ eh ~ α ~> eh' ⇐ num →
                    Γ ⊢ (e ·+₂ eh) => num ~ α ~> (e ·+₂ eh') => num
      SAZipAsc1   : {Γ : tctx} {e e' : zexp} {α : action} {t : htyp} →
                    Γ ⊢ e ~ α ~> e' ⇐ t →
                    Γ ⊢ (e ·:₁ t) => t ~ α ~> (e' ·:₁ t) => t
      SAZipAsc2   : {Γ : tctx} {e : hexp} {α : action} {t t' : ztyp} {t◆ t'◆ : htyp} →
                    t + α +> t' →
                    erase-t t' t'◆ →
                    erase-t t t◆ →
                    Γ ⊢ e <= t'◆ →
                    Γ ⊢ (e ·:₂ t) => t◆ ~ α ~> (e ·:₂ t') => t'◆
      SAZipLam1   : {Γ : tctx} {e : hexp} {t1 t1' : ztyp} {t1◆ t1'◆ t2 t2' : htyp} {x : Nat}
                    {α : action} →
                    x # Γ →
                    erase-t t1 t1◆ →
                    erase-t t1' t1'◆ →
                    t1 + α +> t1' →
                    (Γ ,, (x , t1◆)) ⊢ e => t2 →
                    (Γ ,, (x , t1'◆)) ⊢ e => t2' →
                    Γ ⊢ (·λ x ·[ t1 ]₁ e) => (t1◆ ==> t2) ~ α ~>
                      (·λ x ·[ t1' ]₁ e) => (t1'◆ ==> t2')
      SAZipLam2   : {Γ : tctx} {e e' : zexp} {e◆ : hexp} {t1 t2 t2' : htyp} {x : Nat}
                    {α : action }→
                    x # Γ →
                    erase-e e e◆ →
                    (Γ ,, (x , t1)) ⊢ e◆ => t2 →
                    (Γ ,, (x , t1)) ⊢ e => t2 ~ α ~> e' => t2' →
                    Γ ⊢ (·λ x ·[ t1 ]₂ e) => (t1 ==> t2) ~ α ~>
                      (·λ x ·[ t1 ]₂ e') => (t1 ==> t2')
      SAZipApArr  : {Γ : tctx} {t t1 t2 t3 t4 : htyp} {α : action}
                    {eh eh' : zexp} {e eh◆ : hexp} →
                    t ▸arr (t3 ==> t4) →
                    erase-e eh eh◆ →
                    Γ ⊢ (eh◆) => t2 →
                    Γ ⊢ eh => t2 ~ α ~> eh' => t →
                    Γ ⊢ e <= t3 →
                    Γ ⊢ (eh ∘₁ e) => t1 ~ α ~> (eh' ∘₁ e) => t4
      SAZipApAna  : {Γ : tctx} {t' t2 t : htyp} {e : hexp}
                    {eh eh' : zexp} {α : action}  →
                    t' ▸arr (t2 ==> t) →
                    Γ ⊢ e => t' →
                    Γ ⊢ eh ~ α ~> eh' ⇐ t2 →
                    Γ ⊢ (e ∘₂ eh) => t ~ α ~> (e ∘₂ eh') => t              
      SAZipPair1  : {Γ : tctx} {t1 t1' t2 : htyp} {α : action} {eh eh' : zexp}
                    {e eh◆ : hexp} →
                    erase-e eh eh◆ →
                    Γ ⊢ (eh◆) => t1 →
                    Γ ⊢ eh => t1 ~ α ~> eh' => t1' →
                    Γ ⊢ e => t2 →
                    Γ ⊢ ⟨ eh , e ⟩₁ => (t1 ⊠ t2) ~ α ~> ⟨ eh' , e ⟩₁ => (t1' ⊠ t2)
      SAZipPair2  : {Γ : tctx} {t1 t2 t2' : htyp} {α : action} {eh eh' : zexp}
                    {e eh◆ : hexp} →
                    Γ ⊢ e => t1 →
                    erase-e eh eh◆ →
                    Γ ⊢ (eh◆) => t2 →
                    Γ ⊢ eh => t2 ~ α ~> eh' => t2' →
                    Γ ⊢ ⟨ e , eh ⟩₂ => (t1 ⊠ t2) ~ α ~> ⟨ e , eh' ⟩₂ => (t1 ⊠ t2')
      SAZipFst    : {Γ : tctx} {t× t×' t1 t1' t2 t2' : htyp} {α : action}
                    {eh eh' : zexp} {eh◆ : hexp} →
                    t× ▸prod (t1 ⊠ t2) →
                    t×' ▸prod (t1' ⊠ t2') →
                    erase-e eh eh◆ →
                    Γ ⊢ (eh◆) => t× →
                    Γ ⊢ eh => t× ~ α ~> eh' => t×' →
                    Γ ⊢ fst eh => t1 ~ α ~> fst eh' => t1'
      SAZipSnd    : {Γ : tctx} {t× t×' t1 t1' t2 t2' : htyp} {α : action}
                    {eh eh' : zexp} {eh◆ : hexp} →
                    t× ▸prod (t1 ⊠ t2) →
                    t×' ▸prod (t1' ⊠ t2') →
                    erase-e eh eh◆ →
                    Γ ⊢ (eh◆) => t× →
                    Γ ⊢ eh => t× ~ α ~> eh' => t×' →
                    Γ ⊢ snd eh => t2 ~ α ~> snd eh' => t2'
      SAZipNEHole : {Γ : tctx} {e e' : zexp} {u : Nat} {t t' : htyp} {α : action}
                    {e◆ : hexp} →
                    erase-e e e◆ →
                    Γ ⊢ e◆ => t →
                    Γ ⊢ e => t ~ α ~> e' => t' →
                    Γ ⊢ ⦇⌜ e ⌟⦈[ u ] => ⦇-⦈ ~ α ~>  ⦇⌜ e' ⌟⦈[ u ] => ⦇-⦈
                
    -- analytic action expressions
    data _⊢_~_~>_⇐_ : (Γ : tctx) → (e : zexp) → (α : action) →
                        (e' : zexp) → (t : htyp) → Set where
      AASubsume   : {Γ : tctx} {e e' : zexp} {t t' t'' : htyp} {α : action} {e◆ : hexp} →
                    erase-e e e◆ →
                    Γ ⊢ e◆ => t' →
                    Γ ⊢ e => t' ~ α ~> e' => t'' →
                    t ~ t'' →
                    Γ ⊢ e ~ α ~> e' ⇐ t
      AAFinish    : {Γ : tctx} {e : hexp} {t : htyp} {u : Nat} →
                    Γ ⊢ e <= t →
                    Γ ⊢ ▹ ⦇⌜ e ⌟⦈[ u ] ◃ ~ finish ~> ▹ e ◃ ⇐ t
      AAMove      : {e e' : zexp} {δ : direction} {Γ : tctx} {t : htyp} →
                    e + move δ +>e e' →
                    Γ ⊢ e ~ move δ ~> e' ⇐ t
      AADel       : {e : hexp} {Γ : tctx} {t : htyp} {u : Nat} →
                    Γ ⊢ ▹ e ◃ ~ del u ~> ▹ ⦇-⦈[ u ] ◃ ⇐ t
      AAConNumlit : {Γ : tctx} {t : htyp} {n u u1 : Nat} →
                    t ~̸ num →
                    Γ ⊢ ▹ ⦇-⦈[ u ] ◃ ~ construct (numlit n u1) ~> ⦇⌜ ▹ (N n) ◃ ⌟⦈[ u1 ] ⇐ t
      AAConAsc    : {Γ : tctx} {e : hexp} {t : htyp} →
                    Γ ⊢ ▹ e ◃ ~ construct asc ~> (e ·:₂ ▹ t ◃) ⇐ t
      AAConVar    : {Γ : tctx} {t t' : htyp} {x u u1 : Nat} →
                    t ~̸ t' →
                    (x , t') ∈ Γ →
                    Γ ⊢ ▹ ⦇-⦈[ u ] ◃ ~ construct (var x u1) ~> ⦇⌜ ▹ X x ◃ ⌟⦈[ u1 ] ⇐ t
      AAConLam1   : {Γ : tctx} {x : Nat} {t t1 t2 : htyp} {u u1 u2 : Nat} →
                    x # Γ →
                    t ▸arr (t1 ==> t2) →
                    Γ ⊢ ▹ ⦇-⦈[ u ] ◃ ~ construct (lam x u1 u2) ~>
                      ·λ x (▹ ⦇-⦈[ u2 ] ◃) ⇐ t
      AAConLam2   : {Γ : tctx} {x : Nat} {t : htyp} {u u1 u2 : Nat} →
                    x # Γ →
                    t ~̸ (⦇-⦈ ==> ⦇-⦈) →
                    Γ ⊢ ▹ ⦇-⦈[ u ] ◃ ~ construct (lam x u1 u2) ~>
                      ⦇⌜ ·λ x ⦇-⦈[ u2 ] ·:₂ (▹ ⦇-⦈ ◃ ==>₁ ⦇-⦈) ⌟⦈[ u1 ] ⇐ t
      AAConInl1   : {Γ : tctx} {t+ t1 t2 : htyp} {u u1 u2 : Nat} →
                    t+ ▸sum (t1 ⊕ t2) →
                    Γ ⊢ ▹ ⦇-⦈[ u ] ◃ ~ construct (inl u1 u2) ~> inl ▹ ⦇-⦈[ u2 ] ◃ ⇐ t+
      AAConInl2   : {Γ : tctx} {t : htyp} {u u1 u2 : Nat} →
                    t ~̸ (⦇-⦈ ⊕ ⦇-⦈) →
                    Γ ⊢ ▹ ⦇-⦈[ u ] ◃ ~ construct (inl u1 u2) ~>
                      ⦇⌜ inl ⦇-⦈[ u2 ] ·:₂ (▹ ⦇-⦈ ◃ ⊕₁ ⦇-⦈) ⌟⦈[ u1 ] ⇐ t
      AAConInr1   : {Γ : tctx} {t+ t1 t2 : htyp} {u u1 u2 : Nat} →
                    t+ ▸sum (t1 ⊕ t2) →
                    Γ ⊢ ▹ ⦇-⦈[ u ] ◃ ~ construct (inr u1 u2) ~> inr ▹ ⦇-⦈[ u2 ] ◃ ⇐ t+
      AAConInr2   : {Γ : tctx} {t : htyp} {u u1 u2 : Nat} →
                    t ~̸ (⦇-⦈ ⊕ ⦇-⦈) →
                    Γ ⊢ ▹ ⦇-⦈[ u ] ◃ ~ construct (inr u1 u2) ~>
                      ⦇⌜ inr ⦇-⦈[ u2 ] ·:₂ (▹ ⦇-⦈ ◃ ⊕₁ ⦇-⦈) ⌟⦈[ u1 ] ⇐ t
      AAConCase   : {Γ : tctx} {x y : Nat} {t : htyp} {u u1 u2 u3 : Nat} →
                    x # Γ →
                    y # Γ →
                    Γ ⊢ ▹ ⦇-⦈[ u ] ◃ ~ construct (case x y u1 u2 u3) ~>
                      case₁ ▹ ⦇-⦈[ u1 ] ◃ x ⦇-⦈[ u2 ] y ⦇-⦈[ u3 ] ⇐ t
      AAZipLam    : {Γ : tctx} {x : Nat} {t t1 t2 : htyp} {e e' : zexp} {α : action} →
                    x # Γ →
                    t ▸arr (t1 ==> t2) →
                    (Γ ,, (x , t1)) ⊢ e ~ α ~> e' ⇐ t2 →
                    Γ ⊢ (·λ x e) ~ α ~> (·λ x e') ⇐ t
      AAZipInl    : {Γ : tctx} {t+ t1 t2 : htyp} {e e' : zexp} {α : action} →
                    t+ ▸sum (t1 ⊕ t2) →
                    Γ ⊢ e ~ α ~> e' ⇐ t1 →
                    Γ ⊢ inl e ~ α ~> inl e' ⇐ t+
      AAZipInr    : {Γ : tctx} {t+ t1 t2 : htyp} {e e' : zexp} {α : action} →
                    t+ ▸sum (t1 ⊕ t2) →
                    Γ ⊢ e ~ α ~> e' ⇐ t2 →
                    Γ ⊢ inr e ~ α ~> inr e' ⇐ t+
      AAZipCase1  : {Γ : tctx} {e e' : zexp} {e◆ e1 e2 : hexp} {x y : Nat}
                    {t t0 t+ t1 t2 : htyp} {α : action} →
                    x # Γ →
                    y # Γ →
                    erase-e e e◆ →
                    Γ ⊢ e◆ => t0 →
                    Γ ⊢ e => t0 ~ α ~> e' => t+ →
                    t+ ▸sum (t1 ⊕ t2) →
                    (Γ ,, (x , t1)) ⊢ e1 <= t →
                    (Γ ,, (y , t2)) ⊢ e2 <= t →
                    Γ ⊢ case₁ e x e1 y e2 ~ α ~> case₁ e' x e1 y e2 ⇐ t 
      AAZipCase2  : {Γ : tctx} {e1 e1' : zexp} {e e2 : hexp} {x y : Nat}
                    {t t+ t1 t2 : htyp} {α : action} →
                    x # Γ →
                    y # Γ →
                    Γ ⊢ e => t+ →
                    t+ ▸sum (t1 ⊕ t2) →
                    (Γ ,, (x , t1)) ⊢ e1 ~ α ~> e1' ⇐ t →
                    Γ ⊢ case₂ e x e1 y e2 ~ α ~> case₂ e x e1' y e2 ⇐ t
      AAZipCase3  : {Γ : tctx} {e2 e2' : zexp} {e e1 : hexp} {x y : Nat}
                    {t t+ t1 t2 : htyp} {α : action} →
                    x # Γ →
                    y # Γ →
                    Γ ⊢ e => t+ →
                    t+ ▸sum (t1 ⊕ t2) →
                    (Γ ,, (y , t2)) ⊢ e2 ~ α ~> e2' ⇐ t →
                    Γ ⊢ case₃ e x e1 y e2 ~ α ~> case₃ e x e1 y e2' ⇐ t
      
