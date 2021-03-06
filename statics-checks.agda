open import Nat
open import Prelude
open import List
open import contexts
open import judgemental-erase
open import lemmas-matching
open import moveerase
open import sensibility
open import statics-core
open import synth-unicity

module statics-checks where
  -- these three judmgements lift the action semantics judgements to relate
  -- an expression and a list of pair-wise composable actions to the
  -- expression that's produced by tracing through the action semantics for
  -- each element in that list.
  --
  -- we do this just by appealing to the original judgement with
  -- constraints on the terms to enforce composability.
  --
  -- in all three cases, we assert that the empty list of actions
  -- constitutes a reflexivity step, so when you run out of actions to
  -- preform you have to be where you wanted to be.
  --
  -- note that the only difference between the types for each judgement and
  -- the original action semantics is that the action is now a list of
  -- actions.
  data runtype : (t : ztyp) (Lα : List action) (t' : ztyp) → Set where
     DoRefl : {t : ztyp} →
              runtype t [] t
     DoType : {t : ztyp} {α : action} {t' t'' : ztyp}
              {L : List action} →
              t + α +> t' →
              runtype t' L t'' →
              runtype t (α :: L) t''

  data runsynth : (Γ : tctx) (e : zexp) (t1 : htyp) (Lα : List action)
                  (e' : zexp) (t2 : htyp) → Set where
     DoRefl  : {Γ : tctx} {e : zexp} {t : htyp} →
               runsynth Γ e t [] e t
     DoSynth : {Γ : tctx} {e : zexp} {t : htyp} {α : action} {e' e'' : zexp} {t' t'' : htyp}
               {L : List action} →
               Γ ⊢ e => t ~ α ~> e' => t' →
               runsynth Γ e' t' L e'' t'' →
               runsynth Γ e t (α :: L) e'' t''

  data runana : (Γ : tctx) (e : zexp) (Lα : List action) (e' : zexp) (t : htyp) → Set where
     DoRefl : {Γ : tctx} {e : zexp} {t : htyp} →
              runana Γ e [] e t
     DoAna  : {Γ : tctx} {e : zexp} {α : action} {e' e'' : zexp} {t : htyp}
              {L : List action} →
              Γ ⊢ e ~ α ~> e' ⇐ t →
              runana Γ e' L e'' t →
              runana Γ e (α :: L) e'' t

  -- all three run judgements lift to the list monoid as expected. these
  -- theorems are simple because the structure of lists is simple, but they
  -- amount a reasoning principle about the composition of action sequences
  -- by letting you split lists in (nearly) arbitrary places and argue
  -- about the consequences of the splits before composing them together.
  runtype++ : ∀{t t' t'' L1 L2 } →
              runtype t  L1 t' →
              runtype t' L2 t'' →
              runtype t (L1 ++ L2) t''
  runtype++ DoRefl d2 = d2
  runtype++ (DoType x d1) d2 = DoType x (runtype++ d1 d2)

  runsynth++ : ∀{Γ e t L1 e' t' L2 e'' t''} →
               runsynth Γ e t L1 e' t' →
               runsynth Γ e' t' L2 e'' t'' →
               runsynth Γ e t (L1 ++ L2) e'' t''
  runsynth++ DoRefl d2 = d2
  runsynth++ (DoSynth x d1) d2 = DoSynth x (runsynth++ d1 d2)

  runana++ : ∀{Γ e t L1 e' L2 e''} →
             runana Γ e  L1 e' t →
             runana Γ e' L2 e'' t →
             runana Γ e (L1 ++ L2) e'' t
  runana++ DoRefl d2 = d2
  runana++ (DoAna x d1) d2 = DoAna x (runana++ d1 d2)

  -- the following collection of lemmas asserts that the various runs
  -- interoperate nicely. in many cases, these amount to observing
  -- something like congruence: if a subterm is related to something by one
  -- of the judgements, it can be replaced by the thing to which it is
  -- related in a larger context without disrupting that larger
  -- context.
  --
  -- taken together, this is a little messier than a proper congruence,
  -- because the action semantics demand well-typedness at each step, and
  -- therefore there are enough premises to each lemma to supply to the
  -- action semantics rules.
  --
  -- therefore, these amount to a checksum on the zipper actions under the
  -- lifing of the action semantics to the list monoid.
  --
  -- they only check the zipper actions they happen to be include, however,
  -- which is driven by the particular lists we use in the proofs of
  -- contructability and reachability, which may or may not be all of
  -- them. additionally, the lemmas given here are what is needed for these
  -- proofs, not anything that's more general.

    -- type zippers
  ziplem-tmarr1 : ∀{t1 t1' t2 L} →
                  runtype t1' L t1 →
                  runtype (t1' ==>₁ t2) L (t1 ==>₁ t2)
  ziplem-tmarr1 DoRefl = DoRefl
  ziplem-tmarr1 (DoType x L') = DoType (TMArrZip1 x) (ziplem-tmarr1 L')

  ziplem-tmarr2 : ∀{t1 t2 t2' L} →
                  runtype t2' L t2 →
                  runtype (t1 ==>₂ t2') L (t1 ==>₂ t2)
  ziplem-tmarr2 DoRefl = DoRefl
  ziplem-tmarr2 (DoType x L') = DoType (TMArrZip2 x) (ziplem-tmarr2 L')

  ziplem-tmplus1 : ∀{t1 t1' t2 L} →
                   runtype t1' L t1 →
                   runtype (t1' ⊕₁ t2) L (t1 ⊕₁ t2)
  ziplem-tmplus1 DoRefl = DoRefl
  ziplem-tmplus1 (DoType x L') = DoType (TMPlusZip1 x) (ziplem-tmplus1 L')

  ziplem-tmplus2 : ∀{t1 t2 t2' L} →
                   runtype t2' L t2 →
                   runtype (t1 ⊕₂ t2') L (t1 ⊕₂ t2)
  ziplem-tmplus2 DoRefl = DoRefl
  ziplem-tmplus2 (DoType x L') = DoType (TMPlusZip2 x) (ziplem-tmplus2 L')

  ziplem-tmprod1 : ∀{t1 t1' t2 L} →
                   runtype t1' L t1 →
                   runtype (t1' ⊠₁ t2) L (t1 ⊠₁ t2)
  ziplem-tmprod1 DoRefl = DoRefl
  ziplem-tmprod1 (DoType x L') = DoType (TMProdZip1 x) (ziplem-tmprod1 L')

  ziplem-tmprod2 : ∀{t1 t2 t2' L} →
                   runtype t2' L t2 →
                   runtype (t1 ⊠₂ t2') L (t1 ⊠₂ t2)
  ziplem-tmprod2 DoRefl = DoRefl
  ziplem-tmprod2 (DoType x L') = DoType (TMProdZip2 x) (ziplem-tmprod2 L')
  
    -- expression zippers
  ziplem-asc1 : ∀{Γ t L e e'} →
                runana Γ e L e' t →
                runsynth Γ (e ·:₁ t) t L (e' ·:₁ t) t
  ziplem-asc1 DoRefl = DoRefl
  ziplem-asc1 (DoAna a r) = DoSynth (SAZipAsc1 a) (ziplem-asc1 r)

  ziplem-asc2 : ∀{Γ t L t' t◆ t'◆ u} →
                erase-t t t◆ →
                erase-t t' t'◆ →
                runtype t L t' →
                runsynth Γ (⦇-⦈[ u ] ·:₂ t) t◆ L (⦇-⦈[ u ] ·:₂ t') t'◆
  ziplem-asc2 {Γ} er er' rt with erase-t◆ er | erase-t◆ er'
  ... | refl | refl = ziplem-asc2' {Γ = Γ} rt
   where
     ziplem-asc2' : ∀{t L t' Γ u} →
                    runtype t L t' →
                    runsynth Γ (⦇-⦈[ u ] ·:₂ t) (t ◆t) L (⦇-⦈[ u ] ·:₂ t') (t' ◆t)
     ziplem-asc2' DoRefl = DoRefl
     ziplem-asc2' (DoType x rt) =
       DoSynth (SAZipAsc2 x (◆erase-t _ _ refl) (◆erase-t _ _ refl) (ASubsume SEHole TCHole1))
               (ziplem-asc2' rt)

  ziplem-lam : ∀{Γ x e t t1 t2 L e'} →
               x # Γ →
               t ▸arr (t1 ==> t2) →
               runana (Γ ,, (x , t1)) e L e' t2 →
               runana Γ (·λ x e) L (·λ x e') t
  ziplem-lam a m DoRefl = DoRefl
  ziplem-lam a m (DoAna x₁ d) = DoAna (AAZipLam a m x₁) (ziplem-lam a m d)

  ziplem-halflam1 : ∀{Γ u t1 t1' t1◆ t1'◆ x l} →
                    x # Γ →
                    erase-t t1 t1◆ →
                    erase-t t1' t1'◆ →
                    runtype t1 l t1' →
                    runsynth Γ (·λ x ·[ t1 ]₁ ⦇-⦈[ u ]) (t1◆ ==> ⦇-⦈) l
                      (·λ x ·[ t1' ]₁ ⦇-⦈[ u ]) (t1'◆ ==> ⦇-⦈)
  ziplem-halflam1 apt et et' DoRefl
    with eraset-det et et'
  ... | refl = DoRefl
  ziplem-halflam1 apt et et' (DoType x rt) =
    DoSynth (SAZipLam1 apt et (rel◆t _) x SEHole SEHole)
            (ziplem-halflam1 apt (rel◆t _) et' rt)
  
  ziplem-halflam2 : ∀{Γ e e' e◆ t1 t2 t2' x L} →
                    x # Γ →
                    erase-e e e◆ →
                    (Γ ,, (x , t1)) ⊢ e◆ => t2 →
                    runsynth (Γ ,, (x , t1)) e t2 L e' t2' →
                    runsynth Γ (·λ x ·[ t1 ]₂ e) (t1 ==> t2) L
                      (·λ x ·[ t1 ]₂ e') (t1 ==> t2')
  ziplem-halflam2 apt ee wt DoRefl = DoRefl
  ziplem-halflam2 apt ee wt (DoSynth x rs) =
    DoSynth (SAZipLam2 apt ee wt x)
            (ziplem-halflam2 apt (rel◆ _) (actsense-synth ee (rel◆ _) x wt) rs)
  
  ziplem-plus1 : ∀{Γ e L e' f} →
                 runana Γ e L e' num →
                 runsynth Γ (e ·+₁ f) num L (e' ·+₁ f) num
  ziplem-plus1 DoRefl = DoRefl
  ziplem-plus1 (DoAna x d) = DoSynth (SAZipPlus1 x) (ziplem-plus1 d)

  ziplem-plus2 : ∀{Γ e L e' f} →
                 runana Γ e L e' num →
                 runsynth Γ (f ·+₂ e) num L (f ·+₂ e') num
  ziplem-plus2 DoRefl = DoRefl
  ziplem-plus2 (DoAna x d) = DoSynth (SAZipPlus2 x) (ziplem-plus2 d)

  ziplem-ap2 : ∀{Γ e L e' t t' f tf} →
               Γ ⊢ f => t' →
               t' ▸arr (t ==> tf) →
               runana Γ e L e' t →
               runsynth Γ (f ∘₂ e) tf L (f ∘₂ e') tf
  ziplem-ap2 wt m DoRefl = DoRefl
  ziplem-ap2 wt m (DoAna x d) = DoSynth (SAZipApAna m wt x) (ziplem-ap2 wt m d)

  ziplem-nehole-a : ∀{Γ e e' L t t' u} →
                    (Γ ⊢ e ◆e => t) →
                    runsynth Γ e t L e' t' →
                    runsynth Γ ⦇⌜ e ⌟⦈[ u ] ⦇-⦈ L ⦇⌜ e' ⌟⦈[ u ] ⦇-⦈
  ziplem-nehole-a wt DoRefl = DoRefl
  ziplem-nehole-a wt (DoSynth {e = e} x d) =
    DoSynth (SAZipNEHole (rel◆ e) wt x)
            (ziplem-nehole-a (actsense-synth (rel◆ e) (rel◆ _) x wt) d)

  ziplem-nehole-b : ∀{Γ e e' L t t' t'' u} →
                    (Γ ⊢ e ◆e => t) →
                    (t'' ~ t') →
                    runsynth Γ e t L e' t' →
                    runana Γ ⦇⌜ e ⌟⦈[ u ] L ⦇⌜ e' ⌟⦈[ u ] t''
  ziplem-nehole-b wt c DoRefl = DoRefl
  ziplem-nehole-b wt c (DoSynth x rs) =
    DoAna (AASubsume (erase-in-hole (rel◆ _)) (SNEHole wt) (SAZipNEHole (rel◆ _) wt x) TCHole1)
          (ziplem-nehole-b (actsense-synth (rel◆ _) (rel◆ _) x wt) c rs)


  -- because the point of the reachability theorems is to show that we
  -- didn't forget to define any of the action semantic cases, it's
  -- important that theorems include the fact that the witness only uses
  -- move -- otherwise, you could cheat by just prepending [ del ] to the
  -- list produced by constructability. constructability does also use
  -- some, but not all, of the possible movements, so this would no longer
  -- demonstrate the property we really want. to that end, we define a
  -- predicate on lists that they contain only (move _) and that the
  -- various things above that produce the lists we use have this property.

  -- predicate
  data movements : List action → Set where
    AM:: : {L : List action} {δ : direction} →
           movements L →
           movements ((move δ) :: L)
    AM[] : movements []

  -- movements breaks over the list monoid, as expected
  movements++ : {l1 l2 : List action} →
                movements l1 →
                movements l2 →
                movements (l1 ++ l2)
  movements++ (AM:: m1) m2 = AM:: (movements++ m1 m2)
  movements++ AM[] m2 = m2


  -- these are zipper lemmas that are specific to list of movement
  -- actions. they are not true for general actions, but because
  -- reachability is restricted to movements, we get some milage out of
  -- them anyway.
  endpoints : ∀{Γ e t L e' t'} →
              Γ ⊢ (e ◆e) => t →
              runsynth Γ e t L e' t' →
              movements L →
              t == t'
  endpoints _ DoRefl AM[] = refl
  endpoints wt (DoSynth x rs) (AM:: mv)
    with endpoints (actsense-synth (rel◆ _) (rel◆ _) x wt) rs mv
  ... | refl = π2 (moveerase-synth (rel◆ _) wt x)

  ziplem-moves-asc2 : ∀{ Γ l t t' e t◆} →
                      movements l →
                      erase-t t t◆ →
                      Γ ⊢ e <= t◆ →
                      runtype t l t' →
                      runsynth Γ (e ·:₂ t) t◆ l (e ·:₂ t') t◆
  ziplem-moves-asc2 _ _ _ DoRefl = DoRefl
  ziplem-moves-asc2 (AM:: m) er wt (DoType x rt) with moveeraset' er x
  ... | er' =  DoSynth (SAZipAsc2 x er' er wt) (ziplem-moves-asc2 m er' wt rt)

  synthana-moves : ∀{t t' l e e' Γ} →
                   Γ ⊢ e ◆e => t' →
                   movements l →
                   t ~ t' →
                   runsynth Γ e t' l e' t' →
                   runana Γ e l e' t
  synthana-moves _ _ _ DoRefl = DoRefl
  synthana-moves wt (AM:: m) c (DoSynth x rs) with π2 (moveerase-synth (rel◆ _) wt x)
  ... | refl =
    DoAna (AASubsume (rel◆ _) wt x c)
          (synthana-moves (actsense-synth (rel◆ _) (rel◆ _) x wt) m c rs)

  ziplem-moves-halflam1 : ∀{Γ e t1 t1' t1◆ t1'◆ t2 t2' x l} →
                          x # Γ →
                          erase-t t1 t1◆ →
                          erase-t t1' t1'◆ →
                          movements l →
                          runtype t1 l t1' →
                          (Γ ,, (x , t1◆)) ⊢ e => t2 →
                          (Γ ,, (x , t1'◆)) ⊢ e => t2' →
                          runsynth Γ (·λ x ·[ t1 ]₁ e) (t1◆ ==> t2) l
                          (·λ x ·[ t1' ]₁ e) (t1'◆ ==> t2')
  ziplem-moves-halflam1 apt et et' AM[] DoRefl wt1 wt2
    with eraset-det et et'
  ... | refl with synthunicity wt1 wt2
  ... | refl = DoRefl
  ziplem-moves-halflam1 apt et et' (AM:: mv) (DoType x rt) wt1 wt2
    with erase-t◆ et | erase-t◆ et'
  ... | refl | refl with moveeraset x
  ... | qq rewrite qq with ziplem-moves-halflam1 apt (rel◆t _) (rel◆t _) mv rt wt1 wt2
  ... | ww = DoSynth (SAZipLam1 apt et (rel◆t _) x wt1 wt1) ww
  
  ziplem-moves-ap1 : ∀{Γ l e1 e1' e2 t t' tx} →
                     Γ ⊢ e1 ◆e => t →
                     t ▸arr (tx ==> t') →
                     Γ ⊢ e2 <= tx →
                     movements l →
                     runsynth Γ e1 t l e1' t →
                     runsynth Γ (e1 ∘₁ e2) t' l (e1' ∘₁ e2) t'
  ziplem-moves-ap1 _ _ _ _ DoRefl = DoRefl
  ziplem-moves-ap1 wt1 mch wt2 (AM:: m) (DoSynth x rs) with π2 (moveerase-synth (rel◆ _) wt1 x)
  ... | refl =
    DoSynth (SAZipApArr mch (rel◆ _) wt1 x wt2)
    (ziplem-moves-ap1 (actsense-synth (rel◆ _) (rel◆ _) x wt1) mch wt2 m rs)

  -- zip lemmas for sums
  ziplem-inl : ∀{t t1 t2 Γ e L e'} →
               t ▸sum (t1 ⊕ t2) →
               runana Γ e L e' t1 →
               runana Γ (inl e) L (inl e') t
  ziplem-inl m DoRefl = DoRefl
  ziplem-inl m (DoAna x r) = DoAna (AAZipInl m x) (ziplem-inl m r)

  ziplem-inr : ∀{t t1 t2 Γ e L e'} →
               t ▸sum (t1 ⊕ t2) →
               runana Γ e L e' t2 →
               runana Γ (inr e) L (inr e') t
  ziplem-inr m DoRefl = DoRefl
  ziplem-inr m (DoAna x r) = DoAna (AAZipInr m x) (ziplem-inr m r)

  ziplem-case1a : ∀{x Γ y e e◆ t0 t+ e' e1 e2 L t1 t2 t} →
                  x # Γ →
                  y # Γ →
                  erase-e e e◆ →
                  Γ ⊢ e◆ => t0 →
                  runsynth Γ e t0 L e' t+ →
                  t+ ▸sum (t1 ⊕ t2) →
                  (Γ ,, (x , t1)) ⊢ e1 <= t →
                  (Γ ,, (y , t2)) ⊢ e2 <= t →
                  movements L →
                  runana Γ (case₁ e x e1 y e2) L (case₁ e' x e1 y e2) t
  ziplem-case1a x# y# er wt0 DoRefl m wt1 wt2 mv = DoRefl
  ziplem-case1a x# y# er wt0 (DoSynth α rs) m wt1 wt2 (AM:: mv)
    with endpoints (actsense-synth er (rel◆ _) α wt0) rs mv
  ... | refl with (π2 (moveerase-synth er wt0 α))
  ... | refl =
    DoAna (AAZipCase1 x# y# er wt0 α m wt1 wt2)
          (ziplem-case1a x# y# (eq-er-trans (π1 (moveerase-synth er wt0 α)) er)
                         wt0 rs m wt1 wt2 mv)

  ziplem-case1b : ∀{Γ e e' t L t' x y t0 e◆ u u1 u2} →
                  x # Γ →
                  y # Γ →
                  erase-e e e◆ →
                  Γ ⊢ e◆ => t →
                  runsynth Γ e t L e' t' →
                  runana Γ (case₁ ⦇⌜ e ⌟⦈[ u ] x ⦇-⦈[ u1 ] y ⦇-⦈[ u2 ]) L
                           (case₁ ⦇⌜ e' ⌟⦈[ u ] x ⦇-⦈[ u1 ] y ⦇-⦈[ u2 ]) t0
  ziplem-case1b _ _ _ _ DoRefl = DoRefl
  ziplem-case1b x# y# er wt (DoSynth x₁ rs) =
    DoAna (AAZipCase1 x# y# (erase-in-hole er) (SNEHole wt) (SAZipNEHole er wt x₁)
          MSHole (ASubsume SEHole TCHole1) (ASubsume SEHole TCHole1))
          (ziplem-case1b x# y# (rel◆ _) (actsense-synth er (rel◆ _) x₁ wt) rs)


  ziplem-case2 : ∀{t t+ t1 t2 Γ x y e e1 e1' e2 l} →
                 x # Γ →
                 y # Γ →
                 Γ ⊢ e => t+ →
                 (Γ ,, (y , t2)) ⊢ e2 <= t →
                 t+ ▸sum (t1 ⊕ t2) →
                 runana (Γ ,, (x , t1)) e1 l e1' t →
                 runana Γ (case₂ e x e1 y e2) l (case₂ e x e1' y e2) t
  ziplem-case2 x# y# wt1 wt2 m DoRefl = DoRefl
  ziplem-case2 x# y# wt1 wt2 m (DoAna x₁ ra) =
    DoAna (AAZipCase2 x# y# wt1 m x₁)
          (ziplem-case2 x# y# wt1 wt2 m ra)

  ziplem-case3  : ∀{t t+ t1 t2 Γ x y e e1 e2 e2' l} →
                  x # Γ →
                  y # Γ →
                  Γ ⊢ e => t+ →
                  (Γ ,, (x , t1)) ⊢ e1 <= t →
                  t+ ▸sum (t1 ⊕ t2) →
                  runana (Γ ,, (y , t2)) e2 l e2' t →
                  runana Γ (case₃ e x e1 y e2) l (case₃ e x e1 y e2') t
  ziplem-case3 x# y# wt1 wt2 m DoRefl = DoRefl
  ziplem-case3 x# y# wt1 wt2 m (DoAna x₁ ra) =
    DoAna (AAZipCase3 x# y# wt1 m x₁)
          (ziplem-case3 x# y# wt1 wt2 m ra)

  -- zip lemma for products
  ziplem-pair1 : ∀ {t1 t1' t2 Γ e1 e1◆ l e1' e2} →
                 erase-e e1 e1◆ →
                 Γ ⊢ e1◆ => t1 →
                 runsynth Γ e1 t1 l e1' t1' →
                 Γ ⊢ e2 => t2 → 
                 runsynth Γ ⟨ e1 , e2 ⟩₁ (t1 ⊠ t2) l ⟨ e1' , e2 ⟩₁ (t1' ⊠ t2)
  ziplem-pair1 er wt1 DoRefl wt2 = DoRefl
  ziplem-pair1 er wt1 (DoSynth x rs) wt2 =
    DoSynth (SAZipPair1 er wt1 x wt2)
            (ziplem-pair1 (rel◆ _) (actsense-synth er (rel◆ _) x wt1) rs wt2)
  
  ziplem-pair2 : ∀ {t1 t2 t2' Γ e1 e2 e2◆ l e2'} →
                 Γ ⊢ e1 => t1 →
                 erase-e e2 e2◆ →
                 Γ ⊢ e2◆ => t2 →
                 runsynth Γ e2 t2 l e2' t2' →
                 runsynth Γ ⟨ e1 , e2 ⟩₂ (t1 ⊠ t2) l ⟨ e1 , e2' ⟩₂ (t1 ⊠ t2')
  ziplem-pair2 wt1 er wt2 DoRefl = DoRefl
  ziplem-pair2 wt1 er wt2 (DoSynth x rs) =
    DoSynth (SAZipPair2 wt1 er wt2 x)
            (ziplem-pair2 wt1 (rel◆ _) (actsense-synth er (rel◆ _) x wt2) rs)

  ziplem-moves-fst : ∀ {t× t×' t1 t1' t2 t2' Γ e e◆ l e'} →
                   t× ▸prod (t1 ⊠ t2) → 
                   t×' ▸prod (t1' ⊠ t2') →
                   erase-e e e◆ →
                   Γ ⊢ e◆ => t× →
                   movements l →
                   runsynth Γ e t× l e' t×' →
                   runsynth Γ (fst e) t1 l (fst e') t1'
  ziplem-moves-fst pr pr' er wt m DoRefl with ▸prod-unicity pr pr'
  ... | refl = DoRefl
  ziplem-moves-fst pr pr' er wt (AM:: m) (DoSynth x rs)
    with endpoints (actsense-synth er (rel◆ _) x wt) rs m
  ... | refl with moveerase-synth er wt x
  ... | q , refl with ▸prod-unicity pr pr'
  ... | refl =
    DoSynth (SAZipFst pr pr' er wt x)
            (ziplem-moves-fst pr pr' (eq-er-trans q er) wt m rs)

  ziplem-moves-snd : ∀ {t× t×' t1 t1' t2 t2' Γ e e◆ l e'} →
                   t× ▸prod (t1 ⊠ t2) → 
                   t×' ▸prod (t1' ⊠ t2') →
                   erase-e e e◆ →
                   Γ ⊢ e◆ => t× →
                   movements l →
                   runsynth Γ e t× l e' t×' →
                   runsynth Γ (snd e) t2 l (snd e') t2'
  ziplem-moves-snd pr pr' er wt m DoRefl with ▸prod-unicity pr pr'
  ... | refl = DoRefl
  ziplem-moves-snd pr pr' er wt (AM:: m) (DoSynth x rs)
    with endpoints (actsense-synth er (rel◆ _) x wt) rs m
  ... | refl with moveerase-synth er wt x
  ... | q , refl with ▸prod-unicity pr pr'
  ... | refl =
    DoSynth (SAZipSnd pr pr' er wt x)
            (ziplem-moves-snd pr pr' (eq-er-trans q er) wt m rs)
