open import Nat
open import Prelude
open import List
open import judgemental-erase
open import statics-checks
open import statics-core

module constructability where
  -- we construct expressions and types by induction on their
  -- structure. for each sub term, we call the relevant theorem, then
  -- assemble the results with carefully chosen lists of actions that allow
  -- us to call the appropriate zipper lemmas and maintain well-typedness
  -- at every stage of the contruction.
  --
  -- the proof term at each stage except subsumption is, morally, just the
  -- mapping of the fragment of the action semantics used by the constructs
  -- in the list in the current formation context into the list monoid.

  -- if the name of the given hole is irrelevant
  irr-hole : Nat
  irr-hole = 0
  
  -- construction of types
  construct-type : (t : htyp) → Σ[ L ∈ List action ] runtype (▹ ⦇-⦈ ◃) L (▹ t ◃)
  construct-type num  = [ construct num ] , DoType TMConNum DoRefl
  construct-type ⦇-⦈ = [ del irr-hole ] , DoType TMDel DoRefl
  construct-type (t1 ==> t2) with construct-type t1 | construct-type t2
  ... | (l1 , ih1) | (l2 , ih2) = l1 ++ construct arrow :: l2 ++ [ move parent ] ,
                                  runtype++ ih1
                                   (DoType TMConArrow
                                     (runtype++ (ziplem-tmarr2 ih2)
                                       (DoType TMArrParent2 DoRefl)))
  construct-type (t1 ⊕ t2) with construct-type t1 | construct-type t2
  ... | (l1 , ih1) | (l2 , ih2) = l1 ++ construct sum :: l2 ++ [ move parent ] ,
                                  runtype++ ih1
                                    (DoType TMConPlus
                                       (runtype++ (ziplem-tmplus2 ih2)
                                         (DoType TMPlusParent2 DoRefl)))
  construct-type (t1 ⊠ t2) with construct-type t1 | construct-type t2
  ... | (l1 , ih1) | (l2 , ih2) = l1 ++ construct prod :: l2 ++ [ move parent ] ,
                                  runtype++ ih1
                                    (DoType TMConProd
                                      (runtype++ (ziplem-tmprod2 ih2)
                                        (DoType TMProdParent2 DoRefl)))
  mutual
    -- construction of expressions in synthetic positions
    construct-synth : {Γ : tctx} {u : Nat} {t : htyp} {e : hexp} →
                      (Γ ⊢ e => t) →
                      Σ[ L ∈ List action ]
                        runsynth Γ ▹ ⦇-⦈[ u ] ◃ ⦇-⦈ L ▹ e ◃ t
      -- the three base cases
    construct-synth (SVar x) = [ construct (var _ irr-hole) ] , DoSynth (SAConVar x) DoRefl
    construct-synth SNum = [ construct (numlit _ irr-hole) ] , DoSynth SAConNumlit DoRefl
    construct-synth SEHole = [ del _ ] , DoSynth SADel DoRefl
    
      -- the inductive cases
    construct-synth (SPlus e1 e2 ) with construct-ana e1 | construct-ana e2
    ... | (l1 , ih1) | (l2 , ih2) =
      construct (plus irr-hole irr-hole) :: (l2 ++ move parent ::
         move (child 1) :: (l1 ++ [ move parent ])) ,
      DoSynth (SAConPlus1 TCHole2)
       (runsynth++ (ziplem-plus2 ih2)
        (DoSynth (SAMove EMPlusParent2)
         (DoSynth (SAMove EMPlusChild1)
          (runsynth++ (ziplem-plus1 ih1)
           (DoSynth (SAMove EMPlusParent1) DoRefl)))))     

    construct-synth {t = t} (SAsc x) with construct-type t | construct-ana x
    ... | (l1 , ih1) | (l2 , ih2) =
      construct asc :: (l1 ++ move parent :: move (child 1) :: (l2 ++ [ move parent ])) ,
      DoSynth SAConAsc
       (runsynth++ (ziplem-asc2 ETTop ETTop ih1)
        (DoSynth (SAMove EMAscParent2)
         (DoSynth (SAMove EMAscChild1)
          (runsynth++ (ziplem-asc1 ih2)
           (DoSynth (SAMove EMAscParent1) DoRefl)))))
           
    construct-synth {t = t1 ==> t2} (SLam x wt) with construct-type t1 | construct-synth wt
    ... | l1 , ih1 | l2 , ih2 =
      construct (lam _ irr-hole irr-hole) ::
        (l1 ++ (move parent :: move (child 2) :: (l2 ++ [ move parent ]))) ,
      DoSynth (SAConLam x)
       (runsynth++ (ziplem-halflam1 x ETTop (rel◆t _) ih1)
        (DoSynth (SAMove EMHalfLamParent1)
         (DoSynth (SAMove EMHalfLamChild2)
          (runsynth++ (ziplem-halflam2 x EETop SEHole ih2)
           (DoSynth (SAMove EMHalfLamParent2) DoRefl)))))
    
    construct-synth (SAp e1 m e2) with construct-synth e1 | construct-ana e2
    ... | l1 , ih1 | l2 , ih2 =
      l1 ++ construct (ap irr-hole irr-hole) :: (l2 ++ [ move parent ]) ,
      runsynth++ ih1
       (DoSynth (SAConApArr m)
        (runsynth++ (ziplem-ap2 e1 m ih2)
         (DoSynth (SAMove EMApParent2) DoRefl)))

    construct-synth (SNEHole {u = u} wt) with construct-synth wt
    ... | l , ih = l ++ construct (nehole u) :: move parent :: [] ,
                   runsynth++ ih
                    (DoSynth SAConNEHole
                     (DoSynth (SAMove EMNEHoleParent) DoRefl))

    construct-synth (SPair e1 e2) with construct-synth e1 | construct-synth e2
    ... | l1 , ih1 | l2 , ih2 =
      construct (pair irr-hole irr-hole) :: (l1 ++ move parent :: move (child 2)
        :: l2 ++ [ move parent ]) ,
      DoSynth SAConPair
       (runsynth++ (ziplem-pair1 EETop SEHole ih1 SEHole)
        (DoSynth (SAMove EMPairParent1)
         (DoSynth (SAMove EMPairChild2)
          (runsynth++ (ziplem-pair2 e1 EETop SEHole ih2)
           (DoSynth (SAMove EMPairParent2) DoRefl)))))
                                          
    construct-synth (SFst e pr) with construct-synth e
    ... | l , ih = l ++ [ construct (fst irr-hole) ] ,
                   runsynth++ ih (DoSynth (SAConFst1 pr) DoRefl)
    
    construct-synth (SSnd e pr) with construct-synth e
    ... | l , ih = l ++ [ construct (snd irr-hole) ] ,
                   runsynth++ ih (DoSynth (SAConSnd1 pr) DoRefl)
    
    -- construction of expressions in analytic positions
    construct-ana : {Γ : tctx} {u : Nat} {t : htyp} {e : hexp} →
                    (Γ ⊢ e <= t) →
                    Σ[ L ∈ List action ]
                      runana Γ ▹ ⦇-⦈[ u ] ◃ L ▹ e ◃ t
    construct-ana (ASubsume x c) with construct-synth x
    ... | l , ih = construct (nehole irr-hole) :: l ++ (move parent :: finish :: []) ,
                   DoAna (AASubsume EETop SEHole SAConNEHole TCHole1)
                    (runana++  (ziplem-nehole-b SEHole c ih)
                     (DoAna (AAMove EMNEHoleParent)
                      (DoAna (AAFinish (ASubsume x c)) DoRefl)))

    construct-ana (ALam a m e) with construct-ana e
    ... | l , ih = construct (lam _ irr-hole irr-hole) :: (l ++ [ move parent ]) ,
                   DoAna (AAConLam1 a m)
                    (runana++ (ziplem-lam a m ih)
                     (DoAna (AAMove EMLamParent) DoRefl))

    construct-ana (AInl m wt) with construct-ana wt
    ... | l , ih = construct (inl irr-hole irr-hole) :: l ++ [ move parent ]  ,
                   DoAna (AAConInl1 m)
                    (runana++ (ziplem-inl m ih)
                     (DoAna (AAMove EMInlParent) DoRefl))

    construct-ana (AInr m wt) with construct-ana wt
    ... | l , ih = construct (inr irr-hole irr-hole) :: l ++ [ move parent ]  ,
                   DoAna (AAConInr1 m)
                    (runana++ (ziplem-inr m ih)
                     (DoAna (AAMove EMInrParent) DoRefl))

    construct-ana (ACase {x = x} {y = y} x# y# m wt0 wt1 wt2)
      with construct-synth wt0
         | construct-ana wt1
         | construct-ana wt2
    ... | l0 , ih0 | l1 , ih1 | l2 , ih2 =
      construct (case x y irr-hole irr-hole irr-hole) :: construct (nehole irr-hole) ::
      l0 ++ (move parent :: finish :: move parent :: move (child 2) ::
      l1 ++ (move parent :: move (child 3) ::
      l2 ++ [ move parent ])) ,
      DoAna (AAConCase x# y#)
       (DoAna (AAZipCase1 x# y# EETop SEHole SAConNEHole MSHole
              (ASubsume SEHole TCHole1) (ASubsume SEHole TCHole1))
        (runana++ (ziplem-case1b x# y# EETop SEHole ih0)
         (DoAna (AAZipCase1 x# y# (EENEHole EETop)
                (SNEHole wt0) (SAMove EMNEHoleParent) MSHole (ASubsume SEHole TCHole1)
                (ASubsume SEHole TCHole1))
          (DoAna (AAZipCase1 x# y# EETop (SNEHole wt0) (SAFinish wt0) m
                 (ASubsume SEHole TCHole1) (ASubsume SEHole TCHole1))
           (DoAna (AAMove EMCaseParent1)
            (DoAna (AAMove EMCaseChild2)
             (runana++ (ziplem-case2 x# y# wt0 (ASubsume SEHole TCHole1) m ih1)
              (DoAna (AAMove EMCaseParent2)
               (DoAna (AAMove EMCaseChild3)
                (runana++ (ziplem-case3 x# y# wt0 wt1 m ih2)
                 (DoAna (AAMove EMCaseParent3) DoRefl)))))))))))
