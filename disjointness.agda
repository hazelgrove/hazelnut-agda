open import Prelude
open import Nat
open import core
open import contexts
open import lemmas-disjointness
open import dom-eq

module disjointness where
  -- if a hole name is new in a term, then the resultant context is
  -- disjoint from any singleton context with that hole name
  mutual
    elab-new-disjoint-synth : ∀ {e u τ d Δ Γ Γ' τ'} →
                              hole-name-new e u →
                              Γ ⊢ e ⇒ τ ~> d ⊣ Δ →
                              Δ ## (■ (u , Γ' , τ'))
    elab-new-disjoint-synth HNNum ESNum = empty-disj _
    elab-new-disjoint-synth (HNPlus hn hn₁) (ESPlus apt x x₁ x₂) = disjoint-parts (elab-new-disjoint-ana hn x₁) (elab-new-disjoint-ana hn₁ x₂)
    elab-new-disjoint-synth (HNAsc hn) (ESAsc x) = elab-new-disjoint-ana hn x
    elab-new-disjoint-synth HNVar (ESVar x₁) = empty-disj (■ (_ , _ , _))
    elab-new-disjoint-synth (HNLam1 hn) ()
    elab-new-disjoint-synth (HNLam2 hn) (ESLam x₁ exp) = elab-new-disjoint-synth hn exp
    elab-new-disjoint-synth (HNHole x) ESEHole = disjoint-singles x
    elab-new-disjoint-synth (HNNEHole x hn) (ESNEHole x₁ exp) = disjoint-parts (disjoint-singles x) (elab-new-disjoint-synth hn exp)
    elab-new-disjoint-synth (HNAp hn hn₁) (ESAp x x₁ x₂ x₃ x₄ x₅) =
                                            disjoint-parts (elab-new-disjoint-ana hn x₄)
                                                  (elab-new-disjoint-ana hn₁ x₅)

    elab-new-disjoint-ana : ∀{e u τ d Δ Γ Γ' τ' τ2} →
                            hole-name-new e u →
                            Γ ⊢ e ⇐ τ ~> d :: τ2 ⊣ Δ →
                            Δ ## (■ (u , Γ' , τ'))
    elab-new-disjoint-ana hn (EASubsume x x₁ x₂ x₃) = elab-new-disjoint-synth hn x₂
    elab-new-disjoint-ana (HNLam1 hn) (EALam x₁ x₂ ex) = elab-new-disjoint-ana hn ex
    elab-new-disjoint-ana (HNHole x) EAEHole = disjoint-singles x
    elab-new-disjoint-ana (HNNEHole x hn) (EANEHole x₁ x₂) = disjoint-parts (disjoint-singles x) (elab-new-disjoint-synth hn x₂)
    elab-new-disjoint-ana (HNInl hn) (EAInl x x₁) = elab-new-disjoint-ana hn x₁
    elab-new-disjoint-ana (HNInr hn) (EAInr x x₁) = elab-new-disjoint-ana hn x₁
    elab-new-disjoint-ana (HNCase hn hn₁ hn₂) (EACase x x₁ x₂ x₃ x₄ x₅ _ _ x₆ x₇ x₈ x₉) = disjoint-parts (elab-new-disjoint-synth hn x₆) (disjoint-parts (elab-new-disjoint-ana hn₁ x₈) (elab-new-disjoint-ana hn₂ x₉))

  -- dual of the above: if elaborating a term produces a context that's
  -- disjoint with a singleton context, it must be that the index is a new
  -- hole name in the original term
  mutual
    elab-disjoint-new-synth : ∀{e τ d Δ u Γ Γ' τ'} →
                              Γ ⊢ e ⇒ τ ~> d ⊣ Δ →
                              Δ ## (■ (u , Γ' , τ')) →
                              hole-name-new e u
    elab-disjoint-new-synth ESNum disj = HNNum
    elab-disjoint-new-synth (ESPlus {Δ1 = Δ1} apt x x₁ x₂) disj
      with elab-disjoint-new-ana x₁ (disjoint-union1 disj) | elab-disjoint-new-ana x₂ (disjoint-union2 {Γ1 = Δ1} disj)
    ... | ih1 | ih2 = HNPlus ih1 ih2
    elab-disjoint-new-synth (ESVar x₁) disj = HNVar
    elab-disjoint-new-synth (ESLam x₁ ex) disj = HNLam2 (elab-disjoint-new-synth ex disj)
    elab-disjoint-new-synth (ESAp {Δ1 = Δ1} x x₁ x₂ x₃ x₄ x₅) disj
      with elab-disjoint-new-ana x₄ (disjoint-union1 disj) | elab-disjoint-new-ana x₅ (disjoint-union2 {Γ1 = Δ1} disj)
    ... | ih1 | ih2 = HNAp ih1 ih2
    elab-disjoint-new-synth {Γ = Γ} ESEHole disj = HNHole (singles-notequal disj)
    elab-disjoint-new-synth {Γ = Γ} (ESNEHole {u = u} {Δ = Δ} x ex) disj = HNNEHole (singles-notequal (disjoint-union1 {Γ2 = Δ} disj)) (elab-disjoint-new-synth ex (disjoint-union2 {Γ1 = ■ (u , Γ , ⦇-⦈)} {Γ2 = Δ} disj))
    elab-disjoint-new-synth (ESAsc x) disj = HNAsc (elab-disjoint-new-ana x disj)

    elab-disjoint-new-ana : ∀{e τ d Δ u Γ Γ' τ2 τ'} →
                            Γ ⊢ e ⇐ τ ~> d :: τ2 ⊣ Δ →
                            Δ ## (■ (u , Γ' , τ')) →
                            hole-name-new e u
    elab-disjoint-new-ana (EALam x₁ x₂ ex) disj = HNLam1 (elab-disjoint-new-ana ex disj)
    elab-disjoint-new-ana (EASubsume x x₁ x₂ x₃) disj = elab-disjoint-new-synth x₂ disj
    elab-disjoint-new-ana EAEHole disj = HNHole (singles-notequal disj)
    elab-disjoint-new-ana {Γ = Γ} (EANEHole {u = u} {τ = τ} {Δ = Δ} x x₁) disj = HNNEHole (singles-notequal (disjoint-union1 {Γ2 = Δ} disj)) (elab-disjoint-new-synth x₁ (disjoint-union2 {Γ1 = ■ (u , Γ , τ)} {Γ2 = Δ} disj))
    elab-disjoint-new-ana (EAInl x x₁) disj = HNInl (elab-disjoint-new-ana x₁ disj)
    elab-disjoint-new-ana (EAInr x x₁) disj = HNInr (elab-disjoint-new-ana x₁ disj)
    elab-disjoint-new-ana {Γ = Γ} (EACase {Δ = Δ} {Δ1 = Δ1} {Δ2 = Δ2} x x₁ x₂ x₃ x₄ x₅ _ _ x₆ x₇ x₈ x₉) disj = HNCase (elab-disjoint-new-synth x₆ (disjoint-union1 disj)) (elab-disjoint-new-ana x₈ (disjoint-union1 {Γ2 = Δ2} (disjoint-union2 {Γ1 = Δ} disj))) (elab-disjoint-new-ana x₉ (disjoint-union2 {Γ1 = Δ1} (disjoint-union2 {Γ1 = Δ} disj)))

  -- collect up the hole names of a term as the indices of a trivial context
  data holes : (e : hexp) (H : ⊤ ctx) → Set where
    HNum   : ∀{n} → holes (N n) ∅
    HPlus  : ∀{e1 e2 H1 H2} → holes e1 H1 → holes e2 H2 → holes (e1 ·+ e2) (H1 ∪ H2)
    HAsc   : ∀{e τ H} → holes e H → holes (e ·: τ) H
    HVar   : ∀{x} → holes (X x) ∅
    HLam1  : ∀{x e H} → holes e H → holes (·λ x e) H
    HLam2  : ∀{x e τ H} → holes e H → holes (·λ x [ τ ] e) H
    HAp    : ∀{e1 e2 H1 H2} → holes e1 H1 → holes e2 H2 → holes (e1 ∘ e2) (H1 ∪ H2)
    HInl   : ∀{e H} → holes e H → holes (inl e) H
    HInr   : ∀{e H} → holes e H → holes (inr e) H
    HCase  : ∀{e x e1 y e2 H H1 H2} → holes e H → holes e1 H1 → holes e2 H2 → holes (case e x e1 y e2) (H ∪ (H1 ∪ H2))
    HEHole : ∀{u} → holes (⦇-⦈[ u ]) (■ (u , <>))
    HNEHole : ∀{e u H} → holes e H → holes (⦇⌜ e ⌟⦈[ u ]) (H ,, (u , <>))

  -- the above judgement has mode (∀,∃). this doesn't prove uniqueness; any
  -- contex that extends the one computed here will be indistinguishable
  -- but we'll treat this one as canonical
  find-holes : (e : hexp) → Σ[ H ∈ ⊤ ctx ](holes e H)
  find-holes (N n) = ∅ , HNum
  find-holes (e1 ·+ e2) with find-holes e1 | find-holes e2
  ... | (h1 , d1) | (h2 , d2)  = (h1 ∪ h2 ) , (HPlus d1 d2)
  find-holes (e ·: x) with find-holes e
  ... | (h , d) = h , (HAsc d)
  find-holes (X x) = ∅ , HVar
  find-holes (·λ x e) with find-holes e
  ... | (h , d) = h , HLam1 d
  find-holes (·λ x [ x₁ ] e) with find-holes e
  ... | (h , d) = h , HLam2 d
  find-holes (e1 ∘ e2) with find-holes e1 | find-holes e2
  ... | (h1 , d1) | (h2 , d2)  = (h1 ∪ h2 ) , (HAp d1 d2)
  find-holes ⦇-⦈[ x ] = (■ (x , <>)) , HEHole
  find-holes ⦇⌜ e ⌟⦈[ x ] with find-holes e
  ... | (h , d) = h ,, (x , <>) , HNEHole d
  find-holes (inl e) with find-holes e
  ... | (h , d) = h , HInl d
  find-holes (inr e) with find-holes e
  ... | (h , d) = h , HInr d
  find-holes (case e x e₁ x₁ e₂) with find-holes e | find-holes e₁ | find-holes e₂
  ... | (h , d) | (h1 , d1) | (h2 , d2) = (h ∪ (h1 ∪ h2)) , HCase d d1 d2
  
  -- if a hole name is new then it's apart from the collection of hole
  -- names
  lem-apart-new : ∀{e H u} → holes e H → hole-name-new e u → u # H
  lem-apart-new HNum x = refl
  lem-apart-new (HPlus {H1 = H1} {H2 = H2} h h₁) (HNPlus hn hn₁) = apart-parts H1 H2 _ (lem-apart-new h hn) (lem-apart-new h₁ hn₁)
  lem-apart-new (HAsc h) (HNAsc hn) = lem-apart-new h hn
  lem-apart-new HVar HNVar = refl
  lem-apart-new (HLam1 h) (HNLam1 hn) = lem-apart-new h hn
  lem-apart-new (HLam2 h) (HNLam2 hn) = lem-apart-new h hn
  lem-apart-new (HAp {H1 = H1} {H2 = H2} h h₁) (HNAp hn hn₁) = apart-parts H1 H2 _ (lem-apart-new h hn) (lem-apart-new h₁ hn₁)
  lem-apart-new HEHole (HNHole x) = apart-singleton (flip x)
  lem-apart-new (HNEHole {u = u'} {H = H} h) (HNNEHole  {u = u}  x hn) = apart-parts (■ (u' , <>)) H u (apart-singleton (flip x)) (lem-apart-new h hn) 
  lem-apart-new (HInl h) (HNInl hn) = lem-apart-new h hn
  lem-apart-new (HInr h) (HNInr hn) = lem-apart-new h hn
  lem-apart-new (HCase {H = H} {H1 = H1} {H2 = H2} h h₁ h₂) (HNCase {u = u'} hn hn₁ hn₂) = apart-parts H (H1 ∪ H2) u' (lem-apart-new h hn) (apart-parts H1 H2 u' (lem-apart-new h₁ hn₁) (lem-apart-new h₂ hn₂))

  -- if the holes of two expressions are disjoint, so are their collections
  -- of hole names
  holes-disjoint-disjoint : ∀{e1 e2 H1 H2} →
                            holes e1 H1 →
                            holes e2 H2 →
                            holes-disjoint e1 e2 →
                            H1 ## H2
  holes-disjoint-disjoint HNum he2 HDNum = empty-disj _
  holes-disjoint-disjoint (HPlus he1 he2) he3 (HDPlus hd hd₁) = disjoint-parts (holes-disjoint-disjoint he1 he3 hd) (holes-disjoint-disjoint he2 he3 hd₁)
  holes-disjoint-disjoint (HAsc he1) he2 (HDAsc hd) = holes-disjoint-disjoint he1 he2 hd
  holes-disjoint-disjoint HVar he2 HDVar = empty-disj _
  holes-disjoint-disjoint (HLam1 he1) he2 (HDLam1 hd) = holes-disjoint-disjoint he1 he2 hd
  holes-disjoint-disjoint (HLam2 he1) he2 (HDLam2 hd) = holes-disjoint-disjoint he1 he2 hd
  holes-disjoint-disjoint (HAp he1 he2) he3 (HDAp hd hd₁) = disjoint-parts (holes-disjoint-disjoint he1 he3 hd) (holes-disjoint-disjoint he2 he3 hd₁)
  holes-disjoint-disjoint HEHole he2 (HDHole x) = lem-apart-sing-disj (lem-apart-new he2 x)
  holes-disjoint-disjoint (HNEHole he1) he2 (HDNEHole x hd) = disjoint-parts (lem-apart-sing-disj (lem-apart-new he2 x)) (holes-disjoint-disjoint he1 he2 hd)
  holes-disjoint-disjoint (HInl he1) he2 (HDInl hd) = holes-disjoint-disjoint he1 he2 hd
  holes-disjoint-disjoint (HInr he1) he2 (HDInr hd) = holes-disjoint-disjoint he1 he2 hd
  holes-disjoint-disjoint (HCase he1 he3 he4) he2 (HDCase hd hd₁ hd₂) = disjoint-parts (holes-disjoint-disjoint he1 he2 hd) (disjoint-parts (holes-disjoint-disjoint he3 he2 hd₁) (holes-disjoint-disjoint he4 he2 hd₂))
  

  -- the holes of an expression have the same domain as the context
  -- produced during expansion; that is, we don't add anything we don't
  -- find in the term during expansion.
  mutual
    holes-delta-ana : ∀{Γ H e τ d τ' Δ} →
                      holes e H →
                      Γ ⊢ e ⇐ τ ~> d :: τ' ⊣ Δ →
                      dom-eq Δ H
    holes-delta-ana (HLam1 h) (EALam x₁ x₂ exp) = holes-delta-ana h exp
    holes-delta-ana h (EASubsume x x₁ x₂ x₃) = holes-delta-synth h x₂
    holes-delta-ana (HEHole {u = u}) EAEHole = dom-single u
    holes-delta-ana (HNEHole {u = u} h) (EANEHole x x₁) = dom-union (lem-apart-sing-disj (lem-apart-new h (elab-disjoint-new-synth x₁ x))) (dom-single u) (holes-delta-synth h x₁)
    holes-delta-ana (HInl h) (EAInl x x₁) = holes-delta-ana h x₁
    holes-delta-ana (HInr h) (EAInr x x₁) = holes-delta-ana h x₁
    holes-delta-ana (HCase h h₁ h₂) (EACase {Δ = Δ} x x₁ x₂ x₃ x₄ x₅ _ _ x₆ x₇ x₈ x₉) = dom-union (##-comm (disjoint-parts (##-comm (holes-disjoint-disjoint h h₁ x)) (##-comm (holes-disjoint-disjoint h h₂ x₁)))) (holes-delta-synth h x₆) (dom-union (holes-disjoint-disjoint h₁ h₂ x₂) (holes-delta-ana h₁ x₈) (holes-delta-ana h₂ x₉))
    
    holes-delta-synth : ∀{Γ H e τ d Δ} →
                        holes e H →
                        Γ ⊢ e ⇒ τ ~> d ⊣ Δ →
                        dom-eq Δ H
    holes-delta-synth HNum ESNum = dom-∅
    holes-delta-synth (HPlus h h₁) (ESPlus apt x x₁ x₂) = dom-union (holes-disjoint-disjoint h h₁ x) (holes-delta-ana h x₁) (holes-delta-ana h₁ x₂)
    holes-delta-synth (HAsc h) (ESAsc x) = holes-delta-ana h x
    holes-delta-synth HVar (ESVar x₁) = dom-∅
    holes-delta-synth (HLam2 h) (ESLam x₁ exp) = holes-delta-synth h exp
    holes-delta-synth (HAp h h₁) (ESAp x x₁ x₂ x₃ x₄ x₅) = dom-union (holes-disjoint-disjoint h h₁ x) (holes-delta-ana h x₄) (holes-delta-ana h₁ x₅)
    holes-delta-synth (HEHole {u = u}) ESEHole = dom-single u
    holes-delta-synth (HNEHole {u = u} h) (ESNEHole x exp) = dom-union (lem-apart-sing-disj (lem-apart-new h (elab-disjoint-new-synth exp x))) (dom-single u) (holes-delta-synth h exp)
    

  -- this is the main result of this file:
  --
  -- if you elaborate two hole-disjoint expressions analytically, the Δs
  -- produced are disjoint.
  --
  -- the proof technique here is explcitly *not* structurally inductive on the
  -- expansion judgement, because that approach relies on weakening of
  -- expansion, which is false because of the substitution contexts. giving
  -- expansion weakning would take away unicity, so we avoid the whole
  -- question.
  elab-ana-disjoint : ∀{e1 e2 τ1 τ2 e1' e2' τ1' τ2' Γ1 Γ2 Δ1 Δ2} →
                      holes-disjoint e1 e2 →
                      Γ1 ⊢ e1 ⇐ τ1 ~> e1' :: τ1' ⊣ Δ1 →
                      Γ2 ⊢ e2 ⇐ τ2 ~> e2' :: τ2' ⊣ Δ2 →
                      Δ1 ## Δ2
  elab-ana-disjoint {e1} {e2} hd ana1 ana2
    with find-holes e1 | find-holes e2
  ... | (_ , he1) | (_ , he2) = dom-eq-disj (holes-disjoint-disjoint he1 he2 hd)
                                            (holes-delta-ana he1 ana1)
                                            (holes-delta-ana he2 ana2)

  elab-synth-disjoint : ∀{e1 e2 τ1 τ2 e1' e2' Γ1 Γ2 Δ1 Δ2} →
                        holes-disjoint e1 e2 →
                        Γ1 ⊢ e1 ⇒ τ1 ~> e1' ⊣ Δ1 →
                        Γ2 ⊢ e2 ⇒ τ2 ~> e2' ⊣ Δ2 →
                        Δ1 ## Δ2
  elab-synth-disjoint {e1} {e2} hd synth1 synth2
    with find-holes e1 | find-holes e2
  ... | (_ , he1) | (_ , he2) = dom-eq-disj (holes-disjoint-disjoint he1 he2 hd)
                                            (holes-delta-synth he1 synth1)
                                            (holes-delta-synth he2 synth2)

  elab-synth-ana-disjoint : ∀{e1 e2 τ1 τ2 e1' e2' τ2' Γ1 Γ2 Δ1 Δ2} →
                            holes-disjoint e1 e2 →
                            Γ1 ⊢ e1 ⇒ τ1 ~> e1' ⊣ Δ1 →
                            Γ2 ⊢ e2 ⇐ τ2 ~> e2' :: τ2' ⊣ Δ2 →
                            Δ1 ## Δ2
  elab-synth-ana-disjoint {e1} {e2} hd synth ana
    with find-holes e1 | find-holes e2
  ... | (_ , he1) | (_ , he2) = dom-eq-disj (holes-disjoint-disjoint he1 he2 hd)
                                            (holes-delta-synth he1 synth)
                                            (holes-delta-ana he2 ana)
