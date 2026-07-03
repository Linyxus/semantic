import Semantic.CoreCapybara.Capybara.Syntax
import Semantic.CoreCapybara.Capybara.Substitution

namespace CoreCapybara

inductive CapySubcapt : CapyCtx s -> CapyCaptureSet s -> CapyCaptureSet s -> Prop where
| sc_trans :
  CapySubcapt Γ C1 C2 ->
  CapySubcapt Γ C2 C3 ->
  -------------------
  CapySubcapt Γ C1 C3
| sc_elem :
  CapyCaptureSet.Subset C1 C2 ->
  -------------------
  CapySubcapt Γ C1 C2
| sc_mode {C : CapyCaptureSet s} :
  m1 ≤ m2 ->
  -------------------
  CapySubcapt Γ (C.applyMut m1) (C.applyMut m2)
| sc_union :
  CapySubcapt Γ C1 C3 ->
  CapySubcapt Γ C2 C3 ->
  -------------------
  CapySubcapt Γ (.union C1 C2) C3
| sc_var :
  CapyCtx.LookupVar Γ x T ->
  ----------------------------------
  CapySubcapt Γ (.var (.M .epsilon) (.bound x)) T.captureSet
| sc_cvar :
  CapyCtx.LookupCVar Γ c .access_only (.bound C) ->
  ----------------------------------
  CapySubcapt Γ (.cvar (.M .epsilon) c) C
| sc_ro :
  ----------------------------------
  CapySubcapt Γ C.applyRO C
| sc_ro_mono :
  CapySubcapt Γ C1 C2 ->
  ----------------------------------
  CapySubcapt Γ C1.applyRO C2.applyRO
| sc_drop_mono :
  CapySubcapt Γ C1 C2 ->
  ----------------------------------
  CapySubcapt Γ (C1.applyAccess .drop) (C2.applyAccess .drop)

inductive CapyHasKind : CapyCtx s -> CapyCaptureSet s -> Mutability -> Prop where
| empty {m : Mutability} :
  -------------------
  CapyHasKind Γ {} m
| union {C1 C2 : CapyCaptureSet s} :
  CapyHasKind Γ C1 m ->
  CapyHasKind Γ C2 m ->
  -------------------
  CapyHasKind Γ (C1 ∪ C2) m
| sc {C1 C2 : CapyCaptureSet s} :
  CapySubcapt Γ C1 C2 ->
  CapyHasKind Γ C2 m ->
  -------------------
  CapyHasKind Γ C1 m
| rw {C : CapyCaptureSet s} :
  -------------------
  CapyHasKind Γ C .epsilon
| imm {c : BVar s .cvar} :
  CapyCtx.LookupCVar Γ c a (.unbound .ro) ->
  -------------------
  CapyHasKind Γ (.cvar (.M .epsilon) c) .ro
| ro {C : CapyCaptureSet s} :
  -------------------
  CapyHasKind Γ C.applyRO .ro

inductive CapySubbound : CapyCtx s -> CapyCaptureBound s -> CapyCaptureBound s -> Prop where
| capset :
  CapySubcapt Γ C1 C2 ->
  -------------------
  CapySubbound Γ (.bound C1) (.bound C2)
| unbound {m1 m2 : Mutability} :
  m1 ≤ m2 ->
  -------------------
  CapySubbound Γ (.unbound m1) (.unbound m2)

inductive CapyIsPeak : CapyCtx s -> CapyCaptureSet s -> Prop where
| peak_peak :
  CapyCtx.LookupCVar Γ c a (.unbound m) ->
  --------------------------------
  CapyIsPeak Γ (.cvar mu c)
| peak_pseudo :
  --------------------------------
  CapyIsPeak Γ (.pseudo_peak C)

inductive CapySepCheck : CapyCtx s -> CapyCaptureSet s -> CapyCaptureSet s -> Prop where
| sep_symm :
  CapySepCheck Γ C1 C2 ->
  -------------------
  CapySepCheck Γ C2 C1
| sep_union :
  CapySepCheck Γ C1 C3 ->
  CapySepCheck Γ C2 C3 ->
  -------------------
  CapySepCheck Γ (C1 ∪ C2) C3
| sep_empty {C : CapyCaptureSet s} :
  -------------------
  CapySepCheck Γ {} C
| sep_ro :
  C1.IsClosed ->
  C2.IsClosed ->
  CapyCaptureSet.AccessOnly Γ C1 ->
  CapyCaptureSet.AccessOnly Γ C2 ->
  CapyHasKind Γ C1 .ro ->
  CapyHasKind Γ C2 .ro ->
  -------------------
  CapySepCheck Γ C1 C2
| sep_sc {C1 C2 C1' : CapyCaptureSet s} :
  CapySepCheck Γ C1 C2 ->
  CapySubcapt Γ C1' C1 ->
  CapyCaptureSet.EquivP Γ C1' C1 ->
  --------------------
  CapySepCheck Γ C1' C2
| sep_distinct :
  -- Distinctness is MODE-ERASED (2026-07-02, user decision): two atoms on the
  -- SAME peak at different access modes ALIAS — plain `C1 ≠ C2` would let
  -- `{ε c} >< {ro c}` through, which is unsound (read-vs-write interference on
  -- one resource) and which no covering lock can pay for in the compilation.
  -- Distinct peaks are distinct capture ROOTS, i.e. distinct mode-erased atoms.
  C1.modeErase ≠ C2.modeErase ->
  CapyIsPeak Γ C1 -> CapyIsPeak Γ C2 ->
  --------------------
  CapySepCheck Γ (C1.applyAccess mu1) (C2.applyAccess mu2)

inductive CapyDisjCheck : CapyCtx s -> CapyCaptureSet s -> CapyCaptureSet s -> Prop where
| disj_symm :
  CapyDisjCheck Γ C1 C2 ->
  -------------------
  CapyDisjCheck Γ C2 C1
| disj_empty {C : CapyCaptureSet s} :
  -------------------
  CapyDisjCheck Γ {} C
| disj_union :
  CapyDisjCheck Γ C1 C3 ->
  CapyDisjCheck Γ C2 C3 ->
  -------------------
  CapyDisjCheck Γ (C1 ∪ C2) C3
| disj_peaks :
  C1.IsClosed ->
  CapyDisjCheck Γ (CapyCaptureSet.peaks Γ C1) C2 ->
  --------------------
  CapyDisjCheck Γ C1 C2
| disj_droppable {c1 c2 : BVar s .cvar} :
  Γ.TwoDistinctDroppable c1 c2 ->
  --------------------
  CapyDisjCheck Γ (.cvar a1 c1) (.cvar a2 c2)

-- obsolete: superseded by direct kind/separation checks
-- inductive Satisfy : CapyCtx s -> SepCtx s -> Prop where
-- | satisfy {Ψ : SepCtx s} :
--   (hkind : ∀ C m, Ψ.Has C m -> CapyHasKind Γ C m) ->
--   (hsep : ∀ C1 m1 C2 m2, Ψ.HasTwoDistinct C1 m1 C2 m2 -> CapySepCheck Γ C1 C2) ->
--   -------------------------------------------
--   Satisfy Γ Ψ

inductive CapySubtyp : CapyCtx s -> CapyTy sort s -> CapyTy sort s -> Prop where
| top {T : CapyTy .capt s} :
  T.IsPureType ->
  -------------------
  CapySubtyp Γ T .top
| refl :
  -------------------
  CapySubtyp Γ T T
| trans :
  (hT2 : T2.IsClosed) ->
  CapySubtyp Γ T1 T2 ->
  CapySubtyp Γ T2 T3 ->
  -------------------
  CapySubtyp Γ T1 T3
| tvar :
  CapyCtx.LookupTVar Γ X S ->
  -------------------
  CapySubtyp Γ (.tvar X) S.core
| arrow {T : CapyTy .capt (s,C)} :
  CapySubcapt Γ cs1 cs2 ->
  CapySubtyp
    (Γ,C<:.unbound .epsilon,x:T)
    (U1.rename Rename.implicit_cvar) (U2.rename Rename.implicit_cvar) ->
  --------------------------
  CapySubtyp Γ (.arrow T cs1 U1) (.arrow T cs2 U2)
| poly {S1 S2 : CapyPureTy s} :
  CapySubtyp Γ S2.core S1.core ->
  CapySubcapt Γ cs1 cs2 ->
  CapySubtyp (Γ,X<:S2) T1 T2 ->
  --------------------------
  CapySubtyp Γ (.poly S1.core cs1 T1) (.poly S2.core cs2 T2)
| cpoly :
  CapySubbound Γ cb2 cb1 ->
  CapySubcapt Γ cs1 cs2 ->
  CapySubtyp (Γ,C<:cb2) T1 T2 ->
  ----------------------------------------
  CapySubtyp Γ (.cpoly cb1 cs1 T1) (.cpoly cb2 cs2 T2)
| exi :
  CapySubtyp (Γ,C<:.unbound .epsilon) T1 T2 ->
  ----------------------------------------
  CapySubtyp Γ (.exi T1) (.exi T2)
| typ :
  CapySubtyp Γ T1 T2 ->
  ----------------------------------------
  CapySubtyp Γ (.typ T1) (.typ T2)

inductive CapySeqComp : CapyCtx s -> CapyCaptureSet s -> CapyCaptureSet s -> Prop where
| seq_sc :
  CapySubcapt Γ C1 C1' ->
  CapyCaptureSet.EquivP Γ C1 C1' ->
  CapySeqComp Γ C1' C2 ->
  --------------------
  CapySeqComp Γ C1 C2
| seq_union :
  CapySeqComp Γ C1 C ->
  CapySeqComp Γ C2 C ->
  --------------------
  CapySeqComp Γ (C1 ∪ C2) C
| seq_access_only :
  C1.IsClosed ->
  CapyCaptureSet.AccessOnly Γ C1 ->
  ----------------------
  CapySeqComp Γ C1 C2
| seq_drop :
  CapyDisjCheck Γ C1 C2 ->
  ----------------------
  CapySeqComp Γ C1.applyDrop C2

/-- Typing judgement. Always assigns an existential-sorted type: capturing
    types are lifted via `.typ`, genuine existentials use `.exi`. -/
inductive CapyHasType : CapyCaptureSet s -> CapyCtx s -> CapyExp s -> CapyTy .exi s -> Prop where
| var :
  Γ.IsClosed ->
  Γ.LookupVar x T ->
  ----------------------------
  CapyHasType
    (.var (.M .epsilon) (.bound x))
    Γ
    (.var (.bound x))
    (.typ (T.refineCaptureSet (.var (.M .epsilon) (.bound x))))
| readonly :
  Γ.IsClosed ->
  Γ.LookupVar x (.cell C .epsilon) ->
  ---------------------------------
  CapyHasType
    (.var (.M .ro) (.bound x))
    Γ
    (.var (.bound x))
    (.typ (.cell (.var (.M .ro) (.bound x)) .ro))
| fresh :
  D.IsClosed ->
  CapyCaptureSet.AccessOnly Γ D ->
  Γ.LookupVar x (T.subst (CapySubst.openCVar D)) ->
  CapyCaptureSet.droppable Γ D ->
  -- Well-formedness of the existential WITNESS `T` (2026-07-02, user decision):
  -- the rule constrains `T` only through the looked-up `T[openCVar D]`, but the
  -- compilation (`compile_subst_subtyp`) needs the witness itself well-formed —
  -- all `poly` bounds pure, and no literal frozen (`pseudo_peak`) atoms.
  -- (`T.IsClosed` is NOT needed: it reflects back from the looked-up type's
  -- closedness, `CapyTy.isClosed_of_subst`.)
  T.PureBounds ->
  T.NoPseudoPeak ->
  --------------------------------
  CapyHasType (D ∪ D.applyDrop) Γ (.var (.bound x)) (.exi T)
| abs {T1 : CapyTy .capt (s,C)} {T2 : CapyTy .exi (s,x)} :
  T1.IsClosed ->
  -- Well-formedness of the DOMAIN annotation (2026-07-02, mirroring the `fresh`
  -- rule's witness premises): the compiled function re-abstracts the domain's
  -- capture behind a fresh capture variable `cx <: ⟦T1.captureSet⟧`, so the
  -- compilation needs (a) `T1` free of literal frozen (`pseudo_peak`) atoms —
  -- the body compiler context stores `T1` as `x`'s annotation and must stay
  -- `NoPseudoPeak` — and (b) the re-abstraction bound `⟦T1.captureSet⟧` valid as
  -- a target capture bound, i.e. access-only (no `.drop`-mode captures in a
  -- domain annotation).  Both hold for all surface-written types.
  T1.NoPseudoPeak ->
  CapyCaptureSet.AccessOnly (Γ,C<:.unbound .epsilon) T1.captureSet ->
  CapyHasType
    ((cs.rename Rename.succ).rename Rename.succ ∪ (.var (.M .epsilon) (.bound .here)))
    (Γ,C<:.unbound .epsilon,x:T1)
    (e.rename Rename.implicit_cvar)
    (T2.rename Rename.implicit_cvar) ->
  ----------------------------
  CapyHasType {} Γ (.abs T1 e) (.typ (.arrow T1 cs T2))
| tabs {S : CapyPureTy s} {T : CapyTy .exi (s,X)} :
  S.IsClosed ->
  CapyHasType (cs.rename Rename.succ) (Γ,X<:S) e T ->
  ----------------------------
  CapyHasType {} Γ (.tabs S e) (.typ (.poly S.core cs T))
| cabs {cb : CapyCaptureBound s} {T : CapyTy .exi (s,C)} :
  cb.IsClosed ->
  cb.IsValid Γ ->
  CapyHasType (cs.rename Rename.succ) (Γ,C<:cb) e T ->
  -----------------------------
  CapyHasType {} Γ (.cabs cb e) (.typ (.cpoly cb cs T))
| app :
  -- Well-formedness premises (2026-07-02, mirroring the `fresh`/`abs` premise
  -- families; all hold for surface programs, whose declared types and capture
  -- instantiations carry no `.drop`-mode captures and no free names):
  --  * the FUNCTION's capture is access-only — applying a function must not
  --    consume it.  The compiled application is an ANF `letin` chain whose heads
  --    all resolve (through the bound intermediates' stored types) to `x`'s
  --    capture image; the target `letin`'s sequential composition
  --    (`SeqComp.seq_access_only`) and its kill-free body context need this.
  CapyCaptureSet.AccessOnly Γ (.var (.M .epsilon) x) ->
  --  * the self-cvar instantiation `D` is closed and access-only — it becomes
  --    the target `capp`'s capture argument, whose rule demands a closed,
  --    `IsValid` (access-only) bound.
  D.IsClosed ->
  CapyCaptureSet.AccessOnly Γ D ->
  --  * the ARGUMENT's capture is access-only — the re-abstraction cvar `cx` is
  --    instantiated with the argument's own capture image `⟦{ε y}⟧` (NOT the
  --    domain's full latent, which would leak into the compiled application's
  --    capture through the codomain modal's `W` and overflow the conclusion
  --    capture `⟦{ε x} ∪ {ε y}⟧`); it becomes the SECOND target `capp`'s
  --    capture argument, whose rule demands a valid (access-only) bound.
  CapyCaptureSet.AccessOnly Γ (.var (.M .epsilon) y) ->
  --  * pseudo-peak freedom of the instantiation `D` and the arrow's annotations
  --    `T1`/`T2` (2026-07-02, user decision; the `fresh`/`abs` well-formedness
  --    family): the compiled separation transport (`CapySepCheck.compile`)
  --    refutes its `sep_distinct` pseudo branches from the operands' pseudo-peak
  --    freedom, and the operands here are `D` and the arrow's interference
  --    footprint (built from `T1`/`T2`'s annotations).  Frozen (`pseudo_peak`)
  --    atoms are compiler-internal devices; surface-written types and capture
  --    instantiations never contain them.
  D.NoPseudoPeak ->
  T1.NoPseudoPeak ->
  T2.NoPseudoPeak ->
  --  * pure `poly`/`cpoly` bounds in the arrow's annotations `T1`/`T2` (2026-07-03,
  --    completing the `fresh`/`abs` well-formedness family — `NoPseudoPeak` above was
  --    added for this rule but its `PureBounds` twin was missed): the codomain and
  --    domain compilations (`compile_subst_subtyp` for the arg-fit `.1` and codomain
  --    `.2` bridges) require the substituted type's `poly` bounds pure.  Surface types
  --    have pure bounds; this never rules out a surface program.
  T1.PureBounds ->
  T2.PureBounds ->
  --  * the DOMAIN annotation's capture is access-only (2026-07-02, user decision;
  --    mirrors the `abs` rule's identical premise): the compiled wrap-lock's
  --    self-cvar key item carries `T1.captureSet`'s access modes on `c`, and the
  --    `unwrap` Satisfy discharge lowers `⟦D⟧.applyAccess a ⊑ ⟦D⟧` — valid for
  --    ε/ro modes, not for `.drop`.  `abs` demands this at every introduction;
  --    subsumption at the use-site is what loses it, so it is re-required here.
  CapyCaptureSet.AccessOnly (Γ,C<:.unbound .epsilon) T1.captureSet ->
  CapyHasType (.var (.M .epsilon) x) Γ (.var x)
    (.typ (.arrow T1 (.var (.M .epsilon) x) T2)) ->
  CapyHasType (.var (.M .epsilon) y) Γ (.var y)
    (.typ (T1.subst (CapySubst.openCVar D))) ->
  CapySepCheck Γ D (CapyTy.interfere_set (.arrow T1 (.var (.M .epsilon) x) T2)) ->
  ----------------------------
  CapyHasType (.var (.M .epsilon) x ∪ .var (.M .epsilon) y) Γ (.app x y)
    (T2.subst (CapySubst.openVar y))
| tapp {S : CapyPureTy s} :
  S.IsClosed ->
  CapyHasType (.var (.M .epsilon) x) Γ (.var x)
    (.typ (.poly S.core (.var (.M .epsilon) x) T)) ->
  ----------------------------
  CapyHasType (.var (.M .epsilon) x) Γ (.tapp x S)
    (T.subst (CapySubst.openTVar S))
| capp {D : CapyCaptureSet s} :
  D.IsClosed ->
  CapyCaptureBound.IsValid Γ (.bound D) ->
  CapyHasType (.var (.M .epsilon) x) Γ (.var x)
    (.typ (.cpoly (.bound D) (.var (.M .epsilon) x) T)) ->
  ----------------------------
  CapyHasType (.var (.M .epsilon) x) Γ (.capp x D)
    (T.subst (CapySubst.openCVar D))
| letin :
  CapySeqComp Γ C1 C2 ->
  CapyHasType C1 Γ e1 (.typ T) ->
  CapyHasType (C2.rename Rename.succ) (Γ,x:T) e2 (U.rename Rename.succ) ->
  --------------------------------
  CapyHasType (C1 ∪ C2) Γ (.letin e1 e2) U
| letin_unpack {T : CapyTy .capt (s,C)} :
  CapySeqComp Γ C1 C2 ->
  CapyHasType C1 Γ e1 (.exi T) ->
  CapyHasType
    (((C2.rename Rename.succ).rename Rename.succ) ∪
     (.cvar (.M .epsilon) (.there .here)) ∪
     (.cvar .drop (.there .here)))
    (Γ,C[.can_drop]<:.unbound .epsilon,x:T)
    (e2.rename Rename.implicit_cvar)
    ((U.rename Rename.succ).rename Rename.succ) ->
  --------------------------------
  CapyHasType (C1 ∪ C2) Γ (.letin e1 e2) U
| unit :
  ----------------------------
  CapyHasType {} Γ (.unit) (.typ .unit)
| btrue :
  ----------------------------
  CapyHasType {} Γ (.btrue) (.typ .bool)
| bfalse :
  ----------------------------
  CapyHasType {} Γ (.bfalse) (.typ .bool)
| alloc :
  -- `alloc` introduces a fresh capability: the result is the existential
  -- `∃C. cell{C}` — a read-write cell capturing the freshly bound `C`.
  CapyHasType {} Γ (.var x) (.typ .bool) ->
  ----------------------------
  CapyHasType {} Γ (.alloc x) (.exi (.cell (.cvar (.M .epsilon) .here) .epsilon))
| drop :
  Γ.IsClosed ->
  CapyCaptureSet.droppable Γ (CapyCaptureSet.var (.M .epsilon) x) ->
  CapyHasType Cx Γ (.var x) (.typ (.cell (.var (.M .epsilon) x) .epsilon)) ->
  ----------------------------
  CapyHasType (.var .drop x) Γ (.drop x) (.typ .unit)
| read :
  CapyHasType Cx Γ (.var x) (.typ (.cell Cx .ro)) ->
  ----------------------------
  CapyHasType Cx Γ (.read x) (.typ .bool)
| write :
  CapyHasType Cx Γ (.var x) (.typ (.cell Cx .epsilon)) ->
  CapyHasType {} Γ (.var y) (.typ .bool) ->
  ----------------------------
  CapyHasType Cx Γ (.write x y) (.typ .unit)
| cond :
  CapyHasType C1 Γ (.var x) (.typ .bool) ->
  CapyHasType C2 Γ e2 T ->
  CapyHasType C3 Γ e3 T ->
  ----------------------------
  CapyHasType (C1 ∪ C2 ∪ C3) Γ (.cond x e2 e3) T
| par :
  CapyHasType C1 Γ e1 E1 ->
  CapyHasType C2 Γ e2 E2 ->
  CapySepCheck Γ C1 C2 ->
  ----------------------------
  CapyHasType (C1 ∪ C2) Γ (.par e1 e2) (.typ .unit)
| invoke :
  CapyHasType (.var (.M .epsilon) x) Γ (.var x) (.typ (.cap (.var (.M .epsilon) x))) ->
  CapyHasType {} Γ (.var y) (.typ .unit) ->
  ------------------------------------------------
  CapyHasType (.var (.M .epsilon) x) Γ (.app x y) (.typ .unit)
| subtyp :
  CapyHasType C1 Γ e E1 ->
  CapySubcapt Γ C1 C2 ->
  CapySubtyp Γ E1 E2 ->
  C2.IsClosed -> E2.IsClosed ->
  ----------------------------
  CapyHasType C2 Γ e E2

notation:65 (name := capyHasTypeNotation) C " # " Γ " ⊢ " e " : " T => CapyHasType C Γ e T

/-- `LookupCVar`'s authority component agrees with the functional `lookup_authority`. -/
theorem CapyCtx.LookupCVar.authority {Γ : CapyCtx s} {c : BVar s .cvar} {a : CapyAuthority}
    {cb : CapyCaptureBound s} (h : Γ.LookupCVar c a cb) :
    Γ.lookup_authority c = a := by
  induction h with
  | here => rfl
  | there _ ih => simp only [CapyCtx.lookup_authority]; exact ih

/-- `LookupCVar`'s bound component agrees with the functional `lookup_cvar`. -/
theorem CapyCtx.LookupCVar.bound {Γ : CapyCtx s} {c : BVar s .cvar} {a : CapyAuthority}
    {cb : CapyCaptureBound s} (h : Γ.LookupCVar c a cb) :
    Γ.lookup_cvar c = cb := by
  induction h with
  | here => rfl
  | there _ ih => simp only [CapyCtx.lookup_cvar, ih]

/-- A cvar atom of `D.applyRO` comes from a cvar atom of `D` (same cvar). -/
theorem CapyCaptureSet.cvar_mem_applyRO_inv {s : Sig} {a : Access} {c : BVar s .cvar}
    {D : CapyCaptureSet s} (hsub : CapyCaptureSet.Subset (.cvar a c) D.applyRO) :
    ∃ a0, CapyCaptureSet.Subset (.cvar a0 c) D := by
  induction D with
  | empty => simp only [CapyCaptureSet.applyRO] at hsub; cases hsub
  | union D1 D2 ih1 ih2 =>
    simp only [CapyCaptureSet.applyRO] at hsub
    cases hsub with
    | union_right_left h => obtain ⟨a0, hm⟩ := ih1 h; exact ⟨a0, .union_right_left hm⟩
    | union_right_right h => obtain ⟨a0, hm⟩ := ih2 h; exact ⟨a0, .union_right_right hm⟩
  | var m' x => simp only [CapyCaptureSet.applyRO] at hsub; cases hsub
  | cvar m' c' => simp only [CapyCaptureSet.applyRO] at hsub; cases hsub; exact ⟨m', .refl⟩
  | pseudo_peak C _ => simp only [CapyCaptureSet.applyRO] at hsub; cases hsub

/-- A cvar atom of `D.applyDrop` comes from a cvar atom of `D` (same cvar). -/
theorem CapyCaptureSet.cvar_mem_applyDrop_inv {s : Sig} {a : Access} {c : BVar s .cvar}
    {D : CapyCaptureSet s} (hsub : CapyCaptureSet.Subset (.cvar a c) D.applyDrop) :
    ∃ a0, CapyCaptureSet.Subset (.cvar a0 c) D := by
  induction D with
  | empty => simp only [CapyCaptureSet.applyDrop] at hsub; cases hsub
  | union D1 D2 ih1 ih2 =>
    simp only [CapyCaptureSet.applyDrop] at hsub
    cases hsub with
    | union_right_left h => obtain ⟨a0, hm⟩ := ih1 h; exact ⟨a0, .union_right_left hm⟩
    | union_right_right h => obtain ⟨a0, hm⟩ := ih2 h; exact ⟨a0, .union_right_right hm⟩
  | var m' x => simp only [CapyCaptureSet.applyDrop] at hsub; cases hsub
  | cvar m' c' => simp only [CapyCaptureSet.applyDrop] at hsub; cases hsub; exact ⟨m', .refl⟩
  | pseudo_peak C _ => simp only [CapyCaptureSet.applyDrop] at hsub; cases hsub

/-- `applyAccess` preserves cvar membership: a cvar atom of `D.applyAccess m` occurs
    (at some access mode) in `D` itself. -/
theorem CapyCaptureSet.cvar_subset_applyAccess_inv {s : Sig} {D : CapyCaptureSet s} {a m : Access}
    {c : BVar s .cvar} (h : CapyCaptureSet.Subset (.cvar a c) (D.applyAccess m)) :
    ∃ a', CapyCaptureSet.Subset (.cvar a' c) D := by
  cases m with
  | M m0 =>
    cases m0 with
    | epsilon =>
      simp only [CapyCaptureSet.applyAccess_M, CapyCaptureSet.applyMut_epsilon] at h; exact ⟨a, h⟩
    | ro =>
      simp only [CapyCaptureSet.applyAccess_M, CapyCaptureSet.applyMut_ro] at h
      exact CapyCaptureSet.cvar_mem_applyRO_inv h
  | drop =>
    simp only [CapyCaptureSet.applyAccess_drop] at h
    exact CapyCaptureSet.cvar_mem_applyDrop_inv h

/-- `applyAccess` distributes over union (mirrors `applyMut`/`applyDrop`/`applyRO`,
    which are each defined by structural recursion through `union`). -/
theorem CapyCaptureSet.applyAccess_union {s : Sig} {D1 D2 : CapyCaptureSet s} {m : Access} :
    (D1.union D2).applyAccess m = (D1.applyAccess m).union (D2.applyAccess m) := by
  cases m with
  | M m0 =>
    cases m0 with
    | epsilon => simp only [CapyCaptureSet.applyAccess_M, CapyCaptureSet.applyMut_epsilon]
    | ro => simp only [CapyCaptureSet.applyAccess_M, CapyCaptureSet.applyMut_ro,
        CapyCaptureSet.applyRO]
  | drop => simp only [CapyCaptureSet.applyAccess_drop, CapyCaptureSet.applyDrop]

/-- A cvar atom of `D` occurs, at possibly-different access mode, in `D.applyAccess m`. -/
theorem CapyCaptureSet.cvar_subset_applyAccess {s : Sig} {D : CapyCaptureSet s} {a0 : Access}
    {c : BVar s .cvar} (m : Access) (h : CapyCaptureSet.Subset (.cvar a0 c) D) :
    ∃ a', CapyCaptureSet.Subset (.cvar a' c) (D.applyAccess m) := by
  induction D with
  | empty => cases h
  | union D1 D2 ih1 ih2 =>
    cases h with
    | union_right_left h1 =>
      obtain ⟨a', ha'⟩ := ih1 h1
      refine ⟨a', ?_⟩
      rw [CapyCaptureSet.applyAccess_union]
      exact .union_right_left ha'
    | union_right_right h2 =>
      obtain ⟨a', ha'⟩ := ih2 h2
      refine ⟨a', ?_⟩
      rw [CapyCaptureSet.applyAccess_union]
      exact .union_right_right ha'
  | var m' x => cases h
  | cvar m' c' =>
    cases h
    cases m with
    | M m0 =>
      cases m0 with
      | epsilon =>
        refine ⟨a0, ?_⟩
        simp only [CapyCaptureSet.applyAccess_M, CapyCaptureSet.applyMut_epsilon]
        exact CapyCaptureSet.Subset.refl
      | ro =>
        refine ⟨a0.applyRO, ?_⟩
        simp only [CapyCaptureSet.applyAccess_M, CapyCaptureSet.applyMut_ro,
          CapyCaptureSet.applyRO_cvar]
        exact CapyCaptureSet.Subset.refl
    | drop =>
      refine ⟨.drop, ?_⟩
      simp only [CapyCaptureSet.applyAccess_drop, CapyCaptureSet.applyDrop]
      exact CapyCaptureSet.Subset.refl
  | pseudo_peak C _ => cases h

/-- `Subset` is transitive when the left side is a single `cvar` atom (the general
    case is not needed here). -/
theorem CapyCaptureSet.atom_subset_trans {s : Sig} {D1 D2 : CapyCaptureSet s}
    (h : CapyCaptureSet.Subset D1 D2) :
    ∀ {a : Access} {c : BVar s .cvar}, CapyCaptureSet.Subset (.cvar a c) D1 →
    CapyCaptureSet.Subset (.cvar a c) D2 := by
  induction h with
  | refl => intro a c hmem; exact hmem
  | empty => intro a c hmem; cases hmem
  | union_left _ _ ih1 ih2 =>
    intro a c hmem
    cases hmem with
    | union_right_left hm => exact ih1 hm
    | union_right_right hm => exact ih2 hm
  | union_right_left _ ih =>
    intro a c hmem; exact CapyCaptureSet.Subset.union_right_left (ih hmem)
  | union_right_right _ ih =>
    intro a c hmem; exact CapyCaptureSet.Subset.union_right_right (ih hmem)

/-- `Subset` is transitive when the left side is a single `pseudo_peak` atom (the
    `pseudo_peak` analogue of `atom_subset_trans`). -/
theorem CapyCaptureSet.pseudo_atom_subset_trans {s : Sig} {D1 D2 : CapyCaptureSet s}
    (h : CapyCaptureSet.Subset D1 D2) :
    ∀ {D : CapyCaptureSet s}, CapyCaptureSet.Subset (.pseudo_peak D) D1 →
    CapyCaptureSet.Subset (.pseudo_peak D) D2 := by
  induction h with
  | refl => intro D hmem; exact hmem
  | empty => intro D hmem; cases hmem
  | union_left _ _ ih1 ih2 =>
    intro D hmem
    cases hmem with
    | union_right_left hm => exact ih1 hm
    | union_right_right hm => exact ih2 hm
  | union_right_left _ ih =>
    intro D hmem; exact CapyCaptureSet.Subset.union_right_left (ih hmem)
  | union_right_right _ ih =>
    intro D hmem; exact CapyCaptureSet.Subset.union_right_right (ih hmem)

/-- `peaks` is monotone with respect to (syntactic) capture-set `Subset`. -/
theorem CapyCaptureSet.peaks_subset_mono {Γ : CapyCtx s} {C1 C2 : CapyCaptureSet s}
    (h : CapyCaptureSet.Subset C1 C2) :
    CapyCaptureSet.Subset (CapyCaptureSet.peaks Γ C1) (CapyCaptureSet.peaks Γ C2) := by
  induction h with
  | refl => exact CapyCaptureSet.Subset.refl
  | empty => simp only [CapyCaptureSet.peaks]; exact CapyCaptureSet.Subset.empty
  | union_left _ _ ih1 ih2 =>
    conv_lhs => unfold CapyCaptureSet.peaks
    exact CapyCaptureSet.Subset.union_left ih1 ih2
  | union_right_left _ ih =>
    conv_rhs => unfold CapyCaptureSet.peaks
    exact CapyCaptureSet.Subset.union_right_left ih
  | union_right_right _ ih =>
    conv_rhs => unfold CapyCaptureSet.peaks
    exact CapyCaptureSet.Subset.union_right_right ih

/-- **The peak-stability lemma.**  A *stable* peak (`CapyCtx.IsStableCVar` — either
    `can_drop`, or `.unbound`) of a subtype's capture set `cs1` remains a peak of any
    supertype `cs2` (`CapySubcapt Γ cs1 cs2`): `CapySubcapt`'s only peak-dissolving
    step, `sc_cvar`, requires the dissolved cvar to be `.access_only` AND `.bound` —
    exactly the case `IsStableCVar` excludes.  This is what lets a compiled lock
    restricted to stable peaks survive capture-set subtyping (unlike the full,
    unrestricted lock — see `CapySubtyp.compile`'s arrow/poly/cpoly cases). -/
theorem CapyCtx.peaks_subcapt_stable_subset {Γ : CapyCtx s} {cs1 cs2 : CapyCaptureSet s}
    (h : CapySubcapt Γ cs1 cs2) :
    ∀ {c : BVar s .cvar}, Γ.IsStableCVar c → ∀ {a : Access},
    CapyCaptureSet.Subset (.cvar a c) (CapyCaptureSet.peaks Γ cs1) →
    ∃ a', CapyCaptureSet.Subset (.cvar a' c) (CapyCaptureSet.peaks Γ cs2) := by
  induction h with
  | sc_trans _ _ ih1 ih2 =>
    intro c hstab a hmem
    obtain ⟨a', hmem'⟩ := ih1 hstab hmem
    exact ih2 hstab hmem'
  | sc_elem hsub =>
    intro c hstab a hmem
    exact ⟨a, CapyCaptureSet.atom_subset_trans (CapyCaptureSet.peaks_subset_mono hsub) hmem⟩
  | sc_mode hle =>
    intro c hstab a hmem
    rename_i _ m2 _ _
    rw [CapyCaptureSet.peaks_applyMut_comm, ← CapyCaptureSet.applyAccess_M] at hmem
    obtain ⟨a'', hmem'⟩ := CapyCaptureSet.cvar_subset_applyAccess_inv hmem
    obtain ⟨a''', hmem''⟩ := CapyCaptureSet.cvar_subset_applyAccess (.M m2) hmem'
    rw [CapyCaptureSet.applyAccess_M, ← CapyCaptureSet.peaks_applyMut_comm] at hmem''
    exact ⟨a''', hmem''⟩
  | sc_union _ _ ih1 ih2 =>
    intro c hstab a hmem
    unfold CapyCaptureSet.peaks at hmem
    cases hmem with
    | union_right_left h1 => exact ih1 hstab h1
    | union_right_right h2 => exact ih2 hstab h2
  | sc_var hlk =>
    intro c hstab a hmem
    rw [CapyCaptureSet.var_peaks hlk, CapyCaptureSet.applyAccess_M,
      CapyCaptureSet.applyMut_epsilon] at hmem
    exact ⟨a, hmem⟩
  | sc_cvar hlk =>
    intro c hstab a hmem
    rename_i c' C
    simp only [CapyCaptureSet.peaks] at hmem
    cases hmem
    exfalso
    rcases hstab with hd | ⟨m, hm⟩
    · rw [hlk.authority] at hd; cases hd
    · rw [hlk.bound] at hm; cases hm
  | sc_ro =>
    intro c hstab a hmem
    rename_i C
    rw [CapyCaptureSet.peaks_applyRO_comm] at hmem
    exact CapyCaptureSet.cvar_mem_applyRO_inv hmem
  | sc_ro_mono _ ih =>
    intro c hstab a hmem
    rename_i C1 C2
    rw [CapyCaptureSet.peaks_applyRO_comm] at hmem
    obtain ⟨a', hmem'⟩ := CapyCaptureSet.cvar_mem_applyRO_inv hmem
    obtain ⟨a'', hmem''⟩ := ih hstab hmem'
    obtain ⟨a''', h⟩ := CapyCaptureSet.cvar_subset_applyAccess (.M .ro) hmem''
    rw [CapyCaptureSet.applyAccess_M, CapyCaptureSet.applyMut_ro] at h
    exact ⟨a''', by rw [CapyCaptureSet.peaks_applyRO_comm]; exact h⟩
  | sc_drop_mono _ ih =>
    intro c hstab a hmem
    rw [CapyCaptureSet.applyAccess_drop, CapyCaptureSet.peaks_applyDrop_comm] at hmem
    obtain ⟨a', hmem'⟩ := CapyCaptureSet.cvar_mem_applyDrop_inv hmem
    obtain ⟨a'', hmem''⟩ := ih hstab hmem'
    obtain ⟨a''', h⟩ := CapyCaptureSet.cvar_subset_applyAccess (.drop) hmem''
    rw [CapyCaptureSet.applyAccess_drop] at h
    exact ⟨a''', by
      rw [CapyCaptureSet.applyAccess_drop, CapyCaptureSet.peaks_applyDrop_comm]; exact h⟩

/-- `Subset` commutes with `applyAccess` (a monotone image map). -/
theorem CapyCaptureSet.Subset.applyAccess_mono {s : Sig} {C1 C2 : CapyCaptureSet s}
    (h : CapyCaptureSet.Subset C1 C2) (m : Access) :
    CapyCaptureSet.Subset (C1.applyAccess m) (C2.applyAccess m) := by
  induction h with
  | refl => exact CapyCaptureSet.Subset.refl
  | empty =>
    cases m with
    | M m0 =>
      cases m0 with
      | epsilon =>
        simp only [CapyCaptureSet.applyAccess_M, CapyCaptureSet.applyMut_epsilon]
        exact CapyCaptureSet.Subset.empty
      | ro =>
        simp only [CapyCaptureSet.applyAccess_M, CapyCaptureSet.applyMut_ro,
          CapyCaptureSet.applyRO]
        exact CapyCaptureSet.Subset.empty
    | drop =>
      simp only [CapyCaptureSet.applyAccess_drop, CapyCaptureSet.applyDrop]
      exact CapyCaptureSet.Subset.empty
  | union_left _ _ ih1 ih2 =>
    rw [CapyCaptureSet.applyAccess_union]
    exact CapyCaptureSet.Subset.union_left ih1 ih2
  | union_right_left _ ih =>
    rw [CapyCaptureSet.applyAccess_union]
    exact CapyCaptureSet.Subset.union_right_left ih
  | union_right_right _ ih =>
    rw [CapyCaptureSet.applyAccess_union]
    exact CapyCaptureSet.Subset.union_right_right ih

/-- A cvar atom of `D.applyRO` comes from a cvar atom of `D` at a matching
    access mode (strengthens `cvar_mem_applyRO_inv` with the exact equality). -/
theorem CapyCaptureSet.cvar_mem_applyRO_inv' {s : Sig} {a : Access} {c : BVar s .cvar}
    {D : CapyCaptureSet s} (hsub : CapyCaptureSet.Subset (.cvar a c) D.applyRO) :
    ∃ a0, CapyCaptureSet.Subset (.cvar a0 c) D ∧ a = a0.applyRO := by
  induction D with
  | empty => simp only [CapyCaptureSet.applyRO] at hsub; cases hsub
  | union D1 D2 ih1 ih2 =>
    simp only [CapyCaptureSet.applyRO] at hsub
    cases hsub with
    | union_right_left h => obtain ⟨a0, hm, he⟩ := ih1 h; exact ⟨a0, .union_right_left hm, he⟩
    | union_right_right h => obtain ⟨a0, hm, he⟩ := ih2 h; exact ⟨a0, .union_right_right hm, he⟩
  | var m' x => simp only [CapyCaptureSet.applyRO] at hsub; cases hsub
  | cvar m' c' => simp only [CapyCaptureSet.applyRO] at hsub; cases hsub; exact ⟨m', .refl, rfl⟩
  | pseudo_peak C _ => simp only [CapyCaptureSet.applyRO] at hsub; cases hsub

/-- A cvar atom of `D.applyDrop` is always held at `.drop` access. -/
theorem CapyCaptureSet.cvar_mem_applyDrop_access {s : Sig} {a : Access} {c : BVar s .cvar}
    {D : CapyCaptureSet s} (hsub : CapyCaptureSet.Subset (.cvar a c) D.applyDrop) :
    a = .drop := by
  induction D with
  | empty => simp only [CapyCaptureSet.applyDrop] at hsub; cases hsub
  | union D1 D2 ih1 ih2 =>
    simp only [CapyCaptureSet.applyDrop] at hsub
    cases hsub with
    | union_right_left h => exact ih1 h
    | union_right_right h => exact ih2 h
  | var m' x => simp only [CapyCaptureSet.applyDrop] at hsub; cases hsub
  | cvar m' c' => simp only [CapyCaptureSet.applyDrop] at hsub; cases hsub; rfl
  | pseudo_peak C _ => simp only [CapyCaptureSet.applyDrop] at hsub; cases hsub

/-- **The peak-stability witness lemma.**  Strengthens `peaks_subcapt_stable_subset`
    with an explicit `CapySubcapt` witness relating the ORIGIN atom to its surviving
    image: a stable peak `.cvar a c` of `cs1` not only survives (at some access `a'`)
    into `cs2`'s peaks, but the two atoms are themselves related by `CapySubcapt`. This
    is what lets a peak's whole *item* (union over access modes) be related to its
    image item, not just individual atoms in isolation. -/
theorem CapyCtx.peaks_subcapt_stable_witness {Γ : CapyCtx s} {cs1 cs2 : CapyCaptureSet s}
    (h : CapySubcapt Γ cs1 cs2) :
    ∀ {c : BVar s .cvar}, Γ.IsStableCVar c → ∀ {a : Access},
    CapyCaptureSet.Subset (.cvar a c) (CapyCaptureSet.peaks Γ cs1) →
    ∃ a', CapySubcapt Γ (.cvar a c) (.cvar a' c) ∧
      CapyCaptureSet.Subset (.cvar a' c) (CapyCaptureSet.peaks Γ cs2) := by
  induction h with
  | sc_trans _ _ ih1 ih2 =>
    intro c hstab a hmem
    obtain ⟨a', hsc1, hmem'⟩ := ih1 hstab hmem
    obtain ⟨a'', hsc2, hmem''⟩ := ih2 hstab hmem'
    exact ⟨a'', CapySubcapt.sc_trans hsc1 hsc2, hmem''⟩
  | sc_elem hsub =>
    intro c hstab a hmem
    exact ⟨a, CapySubcapt.sc_elem CapyCaptureSet.Subset.refl,
      CapyCaptureSet.atom_subset_trans (CapyCaptureSet.peaks_subset_mono hsub) hmem⟩
  | sc_mode hle =>
    intro c hstab a hmem
    cases hle with
    | refl => exact ⟨a, CapySubcapt.sc_elem CapyCaptureSet.Subset.refl, hmem⟩
    | ro_eps =>
      rename_i C
      rw [CapyCaptureSet.peaks_applyMut_comm] at hmem
      simp only [CapyCaptureSet.applyMut_ro] at hmem
      obtain ⟨a0, hmem0, ha⟩ := CapyCaptureSet.cvar_mem_applyRO_inv' hmem
      refine ⟨a0, ?_, ?_⟩
      · rw [ha]; exact CapySubcapt.sc_ro (C := .cvar a0 c)
      · rw [CapyCaptureSet.peaks_applyMut_comm]
        simp only [CapyCaptureSet.applyMut_epsilon]
        exact hmem0
  | sc_union _ _ ih1 ih2 =>
    intro c hstab a hmem
    unfold CapyCaptureSet.peaks at hmem
    cases hmem with
    | union_right_left h1 => exact ih1 hstab h1
    | union_right_right h2 => exact ih2 hstab h2
  | sc_var hlk =>
    intro c hstab a hmem
    rw [CapyCaptureSet.var_peaks hlk, CapyCaptureSet.applyAccess_M,
      CapyCaptureSet.applyMut_epsilon] at hmem
    exact ⟨a, CapySubcapt.sc_elem CapyCaptureSet.Subset.refl, hmem⟩
  | sc_cvar hlk =>
    intro c hstab a hmem
    rename_i c' C
    simp only [CapyCaptureSet.peaks] at hmem
    cases hmem
    exfalso
    rcases hstab with hd | ⟨m, hm⟩
    · rw [hlk.authority] at hd; cases hd
    · rw [hlk.bound] at hm; cases hm
  | sc_ro =>
    intro c hstab a hmem
    rename_i C
    rw [CapyCaptureSet.peaks_applyRO_comm] at hmem
    obtain ⟨a0, hmem0, ha⟩ := CapyCaptureSet.cvar_mem_applyRO_inv' hmem
    exact ⟨a0, by rw [ha]; exact CapySubcapt.sc_ro (C := .cvar a0 c), hmem0⟩
  | sc_ro_mono _ ih =>
    intro c hstab a hmem
    rename_i C1 C2
    rw [CapyCaptureSet.peaks_applyRO_comm] at hmem
    obtain ⟨a0, hmem0, ha⟩ := CapyCaptureSet.cvar_mem_applyRO_inv' hmem
    obtain ⟨a1, hsc, hmem1⟩ := ih hstab hmem0
    refine ⟨a1.applyRO, ?_, ?_⟩
    · rw [ha]; exact CapySubcapt.sc_ro_mono hsc
    · rw [CapyCaptureSet.peaks_applyRO_comm]
      have h2 := hmem1.applyAccess_mono (.M .ro)
      simpa only [CapyCaptureSet.applyAccess_M, CapyCaptureSet.applyMut_ro,
        CapyCaptureSet.applyRO_cvar] using h2
  | sc_drop_mono _ ih =>
    intro c hstab a hmem
    rw [CapyCaptureSet.applyAccess_drop, CapyCaptureSet.peaks_applyDrop_comm] at hmem
    have ha : a = Access.drop := CapyCaptureSet.cvar_mem_applyDrop_access hmem
    obtain ⟨a0, hmem0⟩ := CapyCaptureSet.cvar_mem_applyDrop_inv hmem
    obtain ⟨a1, _, hmem1⟩ := ih hstab hmem0
    refine ⟨.drop, ?_, ?_⟩
    · rw [ha]; exact CapySubcapt.sc_elem CapyCaptureSet.Subset.refl
    · rw [CapyCaptureSet.applyAccess_drop, CapyCaptureSet.peaks_applyDrop_comm]
      have h2 := hmem1.applyAccess_mono Access.drop
      simpa only [CapyCaptureSet.applyAccess_drop, CapyCaptureSet.applyDrop] using h2

/-- A pseudo-peak atom of `X.applyRO` comes from a pseudo-peak atom of `X`, with its
    content transformed by the SAME `applyRO` (strengthens the analogous cvar fact,
    `cvar_mem_applyRO_inv'`, for frozen peaks — `.pseudo_peak D`'s `applyRO`-image is
    `.pseudo_peak D.applyRO`, computed on the CONTENT rather than an access tag). -/
theorem CapyCaptureSet.pseudo_mem_applyRO_inv' {s : Sig} {D : CapyCaptureSet s}
    {X : CapyCaptureSet s} (hsub : CapyCaptureSet.Subset (.pseudo_peak D) X.applyRO) :
    ∃ D0, CapyCaptureSet.Subset (.pseudo_peak D0) X ∧ D = D0.applyRO := by
  induction X with
  | empty => simp only [CapyCaptureSet.applyRO] at hsub; cases hsub
  | union X1 X2 ih1 ih2 =>
    simp only [CapyCaptureSet.applyRO] at hsub
    cases hsub with
    | union_right_left h => obtain ⟨D0, hm, he⟩ := ih1 h; exact ⟨D0, .union_right_left hm, he⟩
    | union_right_right h => obtain ⟨D0, hm, he⟩ := ih2 h; exact ⟨D0, .union_right_right hm, he⟩
  | var m' x => simp only [CapyCaptureSet.applyRO] at hsub; cases hsub
  | cvar m' c' => simp only [CapyCaptureSet.applyRO] at hsub; cases hsub
  | pseudo_peak C _ => simp only [CapyCaptureSet.applyRO] at hsub; cases hsub; exact ⟨C, .refl, rfl⟩

/-- A pseudo-peak atom of `X.applyDrop` comes from a pseudo-peak atom of `X`, with its
    content transformed by the SAME `applyDrop`. -/
theorem CapyCaptureSet.pseudo_mem_applyDrop_inv' {s : Sig} {D : CapyCaptureSet s}
    {X : CapyCaptureSet s} (hsub : CapyCaptureSet.Subset (.pseudo_peak D) X.applyDrop) :
    ∃ D0, CapyCaptureSet.Subset (.pseudo_peak D0) X ∧ D = D0.applyDrop := by
  induction X with
  | empty => simp only [CapyCaptureSet.applyDrop] at hsub; cases hsub
  | union X1 X2 ih1 ih2 =>
    simp only [CapyCaptureSet.applyDrop] at hsub
    cases hsub with
    | union_right_left h => obtain ⟨D0, hm, he⟩ := ih1 h; exact ⟨D0, .union_right_left hm, he⟩
    | union_right_right h => obtain ⟨D0, hm, he⟩ := ih2 h; exact ⟨D0, .union_right_right hm, he⟩
  | var m' x => simp only [CapyCaptureSet.applyDrop] at hsub; cases hsub
  | cvar m' c' => simp only [CapyCaptureSet.applyDrop] at hsub; cases hsub
  | pseudo_peak C _ =>
    simp only [CapyCaptureSet.applyDrop] at hsub; cases hsub; exact ⟨C, .refl, rfl⟩

/-- **The frozen-peak stability witness lemma.**  The `pseudo_peak` analogue of
    `peaks_subcapt_stable_witness`: a frozen peak is ALWAYS stable (`Peak.IsStable`'s
    `.pseudo` case is unconditional — no `CapySubcapt` rule descends into a
    `pseudo_peak`'s content structurally, only `applyMut`/`applyRO`/`applyDrop`
    transform it as a unit), so no side condition is needed. -/
theorem CapyCtx.peaks_subcapt_pseudo_witness {Γ : CapyCtx s} {cs1 cs2 : CapyCaptureSet s}
    (h : CapySubcapt Γ cs1 cs2) :
    ∀ {D : CapyCaptureSet s},
    CapyCaptureSet.Subset (.pseudo_peak D) (CapyCaptureSet.peaks Γ cs1) →
    ∃ D', CapySubcapt Γ (.pseudo_peak D) (.pseudo_peak D') ∧
      CapyCaptureSet.Subset (.pseudo_peak D') (CapyCaptureSet.peaks Γ cs2) ∧
      D.modeErase = D'.modeErase := by
  induction h with
  | sc_trans _ _ ih1 ih2 =>
    intro D hmem
    obtain ⟨D', hsc1, hmem', he1⟩ := ih1 hmem
    obtain ⟨D'', hsc2, hmem'', he2⟩ := ih2 hmem'
    exact ⟨D'', CapySubcapt.sc_trans hsc1 hsc2, hmem'', he1.trans he2⟩
  | sc_elem hsub =>
    intro D hmem
    exact ⟨D, CapySubcapt.sc_elem CapyCaptureSet.Subset.refl,
      CapyCaptureSet.pseudo_atom_subset_trans (CapyCaptureSet.peaks_subset_mono hsub) hmem, rfl⟩
  | sc_mode hle =>
    intro D hmem
    cases hle with
    | refl => exact ⟨D, CapySubcapt.sc_elem CapyCaptureSet.Subset.refl, hmem, rfl⟩
    | ro_eps =>
      rename_i C
      rw [CapyCaptureSet.peaks_applyMut_comm] at hmem
      simp only [CapyCaptureSet.applyMut_ro] at hmem
      obtain ⟨D0, hmem0, hD⟩ := CapyCaptureSet.pseudo_mem_applyRO_inv' hmem
      refine ⟨D0, ?_, ?_, ?_⟩
      · rw [hD]; exact CapySubcapt.sc_ro (C := .pseudo_peak D0)
      · rw [CapyCaptureSet.peaks_applyMut_comm]
        simp only [CapyCaptureSet.applyMut_epsilon]
        exact hmem0
      · rw [hD]; simp only [CapyCaptureSet.modeErase_applyRO]
  | sc_union _ _ ih1 ih2 =>
    intro D hmem
    unfold CapyCaptureSet.peaks at hmem
    cases hmem with
    | union_right_left h1 => exact ih1 h1
    | union_right_right h2 => exact ih2 h2
  | sc_var hlk =>
    intro D hmem
    rw [CapyCaptureSet.var_peaks hlk, CapyCaptureSet.applyAccess_M,
      CapyCaptureSet.applyMut_epsilon] at hmem
    exact ⟨D, CapySubcapt.sc_elem CapyCaptureSet.Subset.refl, hmem, rfl⟩
  | sc_cvar hlk =>
    intro D hmem
    simp only [CapyCaptureSet.peaks] at hmem
    cases hmem
  | sc_ro =>
    intro D hmem
    rename_i C
    rw [CapyCaptureSet.peaks_applyRO_comm] at hmem
    obtain ⟨D0, hmem0, hD⟩ := CapyCaptureSet.pseudo_mem_applyRO_inv' hmem
    refine ⟨D0, by rw [hD]; exact CapySubcapt.sc_ro (C := .pseudo_peak D0), hmem0, ?_⟩
    rw [hD]; simp only [CapyCaptureSet.modeErase_applyRO]
  | sc_ro_mono _ ih =>
    intro D hmem
    rename_i C1 C2
    rw [CapyCaptureSet.peaks_applyRO_comm] at hmem
    obtain ⟨D0, hmem0, hD⟩ := CapyCaptureSet.pseudo_mem_applyRO_inv' hmem
    obtain ⟨D1, hsc, hmem1, he⟩ := ih hmem0
    refine ⟨D1.applyRO, ?_, ?_, ?_⟩
    · rw [hD]; exact CapySubcapt.sc_ro_mono hsc
    · rw [CapyCaptureSet.peaks_applyRO_comm]
      have h2 := hmem1.applyAccess_mono (.M .ro)
      simpa only [CapyCaptureSet.applyAccess_M, CapyCaptureSet.applyMut_ro,
        CapyCaptureSet.applyRO] using h2
    · rw [hD]
      simp only [CapyCaptureSet.modeErase_applyRO]
      exact he
  | sc_drop_mono _ ih =>
    intro D hmem
    rw [CapyCaptureSet.applyAccess_drop, CapyCaptureSet.peaks_applyDrop_comm] at hmem
    obtain ⟨D0, hmem0, hD⟩ := CapyCaptureSet.pseudo_mem_applyDrop_inv' hmem
    obtain ⟨D1, hsc, hmem1, he⟩ := ih hmem0
    refine ⟨D1.applyDrop, ?_, ?_, ?_⟩
    · rw [hD]
      have h2 := CapySubcapt.sc_drop_mono hsc
      simpa only [CapyCaptureSet.applyAccess_drop] using h2
    · rw [CapyCaptureSet.applyAccess_drop, CapyCaptureSet.peaks_applyDrop_comm]
      have h2 := hmem1.applyAccess_mono Access.drop
      simpa only [CapyCaptureSet.applyAccess_drop, CapyCaptureSet.applyDrop] using h2
    · rw [hD]
      simp only [CapyCaptureSet.modeErase_applyDrop]
      exact he

end CoreCapybara
