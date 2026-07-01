import Semantic.CoreCapybara.Compilation.Coherence
import Semantic.CoreCapybara.Compilation.CoherenceMorphism
import Semantic.CoreCapybara.Compilation.SubstLemmas
import Semantic.CoreCapybara.Compilation.LockKernel
import Semantic.CoreCapybara.Compilation.PeakCombinatorics
open CoreCapybara
namespace Compilation

/-!
# Subtyping compilation

`CapySubtyp Γ A B ⟹ Subtyp ⟦Γ⟧ ⟦A⟧ ⟦B⟧` — source subtyping compiles to target
subtyping.  This is BOTH the `subtyp` case of the main term-compilation theorem
AND the bridge used by `fresh`'s variable re-derivation (`compile_var_typ_empty`).

Structural/leaf cases (`top`/`refl`/`trans`/`tvar`/`typ`) are discharged here.
The `exi` case needs the `consCVar` coherence-preservation lemma (K2); the
`arrow`/`poly`/`cpoly` cases need the function-lock subtyping kernel (K1) — both
tracked in `notes/fresh-roadmap.md`.
-/

/-- Compilation distributes over `applyRO` (`applyRO = applyMut .ro`). -/
theorem CapyCaptureSet.compile_applyRO {cs : CapyCaptureSet s1} {sc : SrcCtx s1 s2} :
    CapyCaptureSet.compile cs.applyRO sc = (CapyCaptureSet.compile cs sc).applyRO := by
  rw [← CapyCaptureSet.applyMut_ro, CapyCaptureSet.compile_applyMut, CaptureSet.applyMut_ro]

/-- Compilation preserves capture-set subset (it is a homomorphism on the
    union/empty structure that `Subset` is defined over). -/
theorem CapyCaptureSet.compile_subset {C1 C2 : CapyCaptureSet s1} {sc : SrcCtx s1 s2}
    (h : CapyCaptureSet.Subset C1 C2) :
    CaptureSet.Subset (CapyCaptureSet.compile C1 sc) (CapyCaptureSet.compile C2 sc) := by
  induction h with
  | refl => exact .refl
  | empty => simp only [CapyCaptureSet.compile]; exact .empty
  | union_left _ _ ih1 ih2 => simp only [CapyCaptureSet.compile]; exact .union_left ih1 ih2
  | union_right_left _ ih => simp only [CapyCaptureSet.compile]; exact .union_right_left ih
  | union_right_right _ ih => simp only [CapyCaptureSet.compile]; exact .union_right_right ih

/-- A syntactically-empty capture set (only `.empty`/unions thereof) is a subset of
    `.empty`. -/
theorem CapyCaptureSet.IsEmpty.subset_empty {cs : CapyCaptureSet s} (h : cs.IsEmpty) :
    CapyCaptureSet.Subset cs .empty := by
  induction h with
  | empty => exact CapyCaptureSet.Subset.refl
  | union _ _ ih1 ih2 => exact CapyCaptureSet.Subset.union_left ih1 ih2

/-- **A type's own top-level capture set is monotone under subtyping.**  Every
    `.capt`-sorted `CapySubtyp` rule either carries its own `CapySubcapt` premise on
    the two sides' capture sets directly (`arrow`/`poly`/`cpoly`), or the capture
    sets agree structurally (`refl`/`tvar`, both `.empty`), or `T <: .top` forces
    `T`'s capture set empty (`top`, via `IsPureType`).  Needed to justify the
    `arrow` compile's *middle* `cpoly` lock (`TypeCompiler.lean`'s
    `.bound ⟦T.captureSet⟧`), which keys off the ARROW'S OWN domain type's capture
    set, not a capture-set-level premise. -/
theorem CapySubtyp.captureSet_subcapt' {s : Sig} {Γ : CapyCtx s} {sort : CapyTySort}
    {Ta Tb : CapyTy sort s} (h : CapySubtyp Γ Ta Tb) :
    ∀ (hsort : sort = .capt),
      CapySubcapt Γ (hsort ▸ Ta : CapyTy .capt s).captureSet
        (hsort ▸ Tb : CapyTy .capt s).captureSet := by
  induction h with
  | top hpure =>
    intro hsort
    simp only [CapyTy.captureSet]
    exact CapySubcapt.sc_elem (CapyCaptureSet.IsEmpty.subset_empty hpure)
  | refl => intro hsort; exact CapySubcapt.sc_elem CapyCaptureSet.Subset.refl
  | trans _ _ _ ih1 ih2 => intro hsort; exact CapySubcapt.sc_trans (ih1 hsort) (ih2 hsort)
  | tvar _ =>
    intro hsort
    simp only [CapyTy.captureSet]
    exact CapySubcapt.sc_elem CapyCaptureSet.Subset.empty
  | arrow hcs _ _ =>
    intro hsort
    simp only [CapyTy.captureSet]
    exact hcs
  | poly _ hcs _ _ _ =>
    intro hsort
    simp only [CapyTy.captureSet]
    exact hcs
  | cpoly _ hcs _ _ =>
    intro hsort
    simp only [CapyTy.captureSet]
    exact hcs
  | exi _ _ => intro hsort; cases hsort
  | typ _ _ => intro hsort; cases hsort

theorem CapySubtyp.captureSet_subcapt {s : Sig} {Γ : CapyCtx s} {Ta Tb : CapyTy .capt s}
    (h : CapySubtyp Γ Ta Tb) :
    CapySubcapt Γ Ta.captureSet Tb.captureSet :=
  CapySubtyp.captureSet_subcapt' h rfl

/-- **`CapySubcapt` transports along a source context renaming.**  Same shape as
    `CapyCtx.IsStableCVar.renamesTo_iff`: `RenamesTo`'s lookup-correspondence
    realigns each of `sc_var`/`sc_cvar`'s context lookups, and the rest is
    structural (`rename` commutes with `union`/`applyMut`/`applyRO`/`applyAccess`).
    Needed to weaken `arrow`'s function-capture premise `hcs : CapySubcapt Γ0 cs1
    cs2` past the two extra binders (self-cvar, domain-cvar) the codomain modal
    lock sits under. -/
theorem CapyCaptureSet.Subset.rename {s1 s2 : Sig} {C1 C2 : CapyCaptureSet s1}
    {f : Rename s1 s2} (h : CapyCaptureSet.Subset C1 C2) :
    CapyCaptureSet.Subset (C1.rename f) (C2.rename f) := by
  induction h with
  | refl => exact CapyCaptureSet.Subset.refl
  | empty => exact CapyCaptureSet.Subset.empty
  | union_left _ _ ih1 ih2 => exact CapyCaptureSet.Subset.union_left ih1 ih2
  | union_right_left _ ih => exact CapyCaptureSet.Subset.union_right_left ih
  | union_right_right _ ih => exact CapyCaptureSet.Subset.union_right_right ih

theorem CapySubcapt.renamesTo {s1 s2 : Sig} {Γ1 : CapyCtx s1} {Γ2 : CapyCtx s2}
    {f : Rename s1 s2} (hf : Γ1.RenamesTo Γ2 f) {C1 C2 : CapyCaptureSet s1}
    (h : CapySubcapt Γ1 C1 C2) : CapySubcapt Γ2 (C1.rename f) (C2.rename f) := by
  induction h with
  | sc_trans _ _ ih1 ih2 => exact CapySubcapt.sc_trans (ih1 hf) (ih2 hf)
  | sc_elem hsub => exact CapySubcapt.sc_elem (CapyCaptureSet.Subset.rename hsub)
  | sc_mode hle =>
    simp only [CapyCaptureSet.applyMut_rename]
    exact CapySubcapt.sc_mode hle
  | sc_union _ _ ih1 ih2 =>
    simp only [CapyCaptureSet.rename]
    exact CapySubcapt.sc_union (ih1 hf) (ih2 hf)
  | sc_var hlk =>
    simp only [CapyCaptureSet.rename, Var.rename, ← CapyTy.captureSet_rename]
    exact CapySubcapt.sc_var (hf.var hlk)
  | sc_cvar hlk =>
    simp only [CapyCaptureSet.rename]
    exact CapySubcapt.sc_cvar (hf.cvar hlk)
  | sc_ro =>
    rw [CapyCaptureSet.applyRO_rename]
    exact CapySubcapt.sc_ro
  | sc_ro_mono _ ih =>
    rw [CapyCaptureSet.applyRO_rename, CapyCaptureSet.applyRO_rename]
    exact CapySubcapt.sc_ro_mono (ih hf)
  | sc_drop_mono _ ih =>
    rw [CapyCaptureSet.applyAccess_rename, CapyCaptureSet.applyAccess_rename]
    exact CapySubcapt.sc_drop_mono (ih hf)

/-- **Subcapturing compiles to subcapturing.**  Source and target `Subcapt` share
    the same constructor structure, so this is a clean structural induction (the
    `sc_var`/`sc_cvar` cases use the `varLookup`/`cvarLookup` coherence fields). -/
theorem CapySubcapt.compile {s1 : Sig} {Γ : CapyCtx s1} {C1 C2 : CapyCaptureSet s1}
    (h : CapySubcapt Γ C1 C2) :
    ∀ {s2 : Sig} (ctx : CompilerCtx s1 s2), ctx.capyCtx = Γ → ctx.Coherent →
    Subcapt ctx.coreCtx (CapyCaptureSet.compile C1 ctx.srcCtx)
      (CapyCaptureSet.compile C2 ctx.srcCtx) := by
  induction h with
  | sc_trans _ _ ih1 ih2 =>
    intro s2 ctx hΓ hcoh
    exact Subcapt.sc_trans (ih1 ctx hΓ hcoh) (ih2 ctx hΓ hcoh)
  | sc_elem hsub =>
    intro s2 ctx hΓ hcoh
    exact Subcapt.sc_elem (CapyCaptureSet.compile_subset hsub)
  | sc_mode hle =>
    intro s2 ctx hΓ hcoh
    simp only [CapyCaptureSet.compile_applyMut]
    exact Subcapt.sc_mode hle
  | sc_union _ _ ih1 ih2 =>
    intro s2 ctx hΓ hcoh
    simp only [CapyCaptureSet.compile]
    exact Subcapt.sc_union (ih1 ctx hΓ hcoh) (ih2 ctx hΓ hcoh)
  | sc_var hlk =>
    intro s2 ctx hΓ hcoh
    obtain ⟨bv, _, hlv, _⟩ := hcoh.varLookup (hΓ ▸ hlk)
    simp only [CapyCaptureSet.compile, CaptureSet.applyAccess_M, CaptureSet.applyMut_epsilon, hlv]
    exact Subcapt.sc_elem CaptureSet.Subset.refl
  | sc_cvar hlk =>
    intro s2 ctx hΓ hcoh
    simp only [CapyCaptureSet.compile]
    exact Subcapt.sc_cvar (hcoh.cvarLookup (hΓ ▸ hlk))
  | sc_ro =>
    intro s2 ctx hΓ hcoh
    simp only [CapyCaptureSet.compile_applyRO]
    exact Subcapt.sc_ro
  | sc_ro_mono _ ih =>
    intro s2 ctx hΓ hcoh
    simp only [CapyCaptureSet.compile_applyRO]
    exact Subcapt.sc_ro_mono (ih ctx hΓ hcoh)
  | sc_drop_mono _ ih =>
    intro s2 ctx hΓ hcoh
    simp only [CapyCaptureSet.compile_applyAccess]
    exact Subcapt.sc_drop_mono (ih ctx hΓ hcoh)

/-- **Capture bounds compile to capture bounds.**  Target `Subbound` only has two
    constructors (`capset`, and `top` for "anything `<: .unbound`"), so every source
    case other than `capset` (which needs `CapySubcapt.compile`) is discharged by
    `Subbound.top` — the compiled `.unbound _` forgets its mutability annotation
    (`CapyCaptureBound.compile`), so both `unbound` and `bound_unbound` compile to a
    `Subbound _ B .unbound` instance for the appropriate `B`. -/
theorem CapySubbound.compile {s1 : Sig} {Γ : CapyCtx s1} {cb1 cb2 : CapyCaptureBound s1}
    (h : CapySubbound Γ cb1 cb2) {s2 : Sig} (ctx : CompilerCtx s1 s2)
    (hΓ : ctx.capyCtx = Γ) (hcoh : ctx.Coherent) :
    Subbound ctx.coreCtx (CapyCaptureBound.compile cb1 ctx.srcCtx)
      (CapyCaptureBound.compile cb2 ctx.srcCtx) := by
  cases h with
  | capset hsc =>
    simp only [CapyCaptureBound.compile]
    exact Subbound.capset (CapySubcapt.compile hsc ctx hΓ hcoh)
  | unbound _ =>
    simp only [CapyCaptureBound.compile]
    exact Subbound.top
  | bound_unbound _ =>
    simp only [CapyCaptureBound.compile]
    exact Subbound.top

/-- **`CapyHasKind` compiles to `HasKind`, EXCEPT for `imm`.**  `empty`/`union`/`sc`/
    `rw`/`ro` mirror their target counterparts directly (`ro` via
    `CapyCaptureSet.compile_applyRO`).  `imm` is a genuine, currently-unresolved gap:
    its premise `CapyCtx.LookupCVar Γ c a (.unbound .ro)` records `c`'s OWN declared
    mutability statically, for the lifetime of `Γ`.  Target Core has no such static
    per-cvar mutability — `HasKind _ _ .ro` is only derivable structurally
    (`.applyRO`) or via an ENCLOSING lock's `mutability : MutabilityCtx` (`imm`,
    `Ctx.LookupLock` + `MutabilityCtx.Has`).  A compiled `.unbound` cvar's mutability
    lock (`CapyCaptureBound.mutabilityCtx`) is pushed only *alongside* the `cpoly`
    that introduces it, guarding that `cpoly`'s own body (`E`'s compile context,
    `ctx.weakenTarget.consCVar cb .here`, sits OUTSIDE the `.modal _ Ψ _` wrapper that
    carries `Ψ`) — so at a general compile point there is no invariant connecting an
    arbitrary `.unbound m`-bound source cvar back to some ancestor lock recording `m`.
    Closing this needs new `CompilerCtx.Coherent` infrastructure (threading a
    "mutability provenance" invariant through `consCVar`/`weakenTarget`), out of scope
    for the pairwise-separation fix (`compile_peakSepCtx_subcapt_sep`) this file is
    otherwise built around. -/
theorem CapyHasKind.compile {s1 : Sig} {Γ : CapyCtx s1} {C : CapyCaptureSet s1}
    {m : Mutability} (h : CapyHasKind Γ C m) {s2 : Sig} (ctx : CompilerCtx s1 s2)
    (hΓ : ctx.capyCtx = Γ) (hcoh : ctx.Coherent) :
    HasKind ctx.coreCtx (CapyCaptureSet.compile C ctx.srcCtx) m := by
  induction h with
  | empty => simp only [CapyCaptureSet.compile]; exact HasKind.empty
  | union _ _ ih1 ih2 =>
    simp only [CapyCaptureSet.compile]
    exact HasKind.union ih1 ih2
  | sc hsc _ ih2 =>
    exact HasKind.sc (CapySubcapt.compile hsc ctx hΓ hcoh) ih2
  | rw => exact HasKind.rw
  | imm _ => sorry
  | ro =>
    simp only [CapyCaptureSet.compile_applyRO]
    exact HasKind.ro

/-- **Peak items are `CapySubcapt`-related across a same-context `CapySubcapt`.**
    For a *stable* cvar `d`, the peak item it keys in `cs1`'s peaks is related, by
    `CapySubcapt`, to the peak item it keys in `cs2`'s peaks — the source-level fact
    underlying stable-peak-lock transport (`CapySubtyp.compile`'s arrow/poly/cpoly
    cases). Built by unioning `CapyCtx.peaks_subcapt_stable_witness`'s per-atom
    witness over `d`'s access-mode occurrences in `cs1`'s peaks. -/
theorem peakItem_subcapt_stable {s : Sig} {Γ : CapyCtx s} {cs1 cs2 : CapyCaptureSet s}
    (h : CapySubcapt Γ cs1 cs2) {d : BVar s .cvar} (hstab : Γ.IsStableCVar d) :
    CapySubcapt Γ (peakItem (CapyCaptureSet.peakset Γ cs1) d)
      (peakItem (CapyCaptureSet.peakset Γ cs2) d) := by
  have key : ∀ (L : List Access),
      (∀ b ∈ L, (CapyCaptureSet.cvar b d) ⊆ CapyCaptureSet.peaks Γ cs1) →
      CapySubcapt Γ (L.foldr (fun b acc => CapyCaptureSet.cvar b d ∪ acc) .empty)
        (peakItem (CapyCaptureSet.peakset Γ cs2) d) := by
    intro L
    induction L with
    | nil =>
      intro _
      simp only [List.foldr_nil]
      exact CapySubcapt.sc_elem CapyCaptureSet.Subset.empty
    | cons b L' ih =>
      intro hL
      rw [List.foldr_cons]
      refine CapySubcapt.sc_union ?_ (ih (fun b' hb' => hL b' (List.mem_cons_of_mem _ hb')))
      obtain ⟨a', hsc, hmem'⟩ := CapyCtx.peaks_subcapt_stable_witness h hstab
        (hL b List.mem_cons_self)
      exact CapySubcapt.sc_trans hsc (CapySubcapt.sc_elem (PC.cvar_subset_peakItem hmem'))
  exact key (accessedAt (CapyCaptureSet.peakset Γ cs1) d)
    (fun b hb => PC.accessedAt_go_subset _ (by simpa only [accessedAt] using hb))

/-- **Frozen peak items are `CapySubcapt`-related across a same-context `CapySubcapt`,
    UNCONDITIONALLY** (a frozen peak is always stable — `Peak.IsStable`'s `.pseudo`
    case). The `pseudo_peak` analogue of `peakItem_subcapt_stable`, built by
    structural induction over `cs1`'s peaks directly (`pseudoItem` is not list-folded
    like `peakItem`, so the induction tracks atom-wise containment rather than an
    `accessedAt` list). -/
theorem pseudoItem_subcapt_stable {s : Sig} {Γ : CapyCtx s} {cs1 cs2 : CapyCaptureSet s}
    (h : CapySubcapt Γ cs1 cs2) {D : CapyCaptureSet s} :
    CapySubcapt Γ (pseudoItem (CapyCaptureSet.peakset Γ cs1) D)
      (pseudoItem (CapyCaptureSet.peakset Γ cs2) D) := by
  have key : ∀ (cs : CapyCaptureSet s),
      (∀ C, CapyCaptureSet.Subset (.pseudo_peak C) cs →
        CapyCaptureSet.Subset (.pseudo_peak C) (CapyCaptureSet.peaks Γ cs1)) →
      CapySubcapt Γ (pseudoItem.go D cs) (pseudoItem (CapyCaptureSet.peakset Γ cs2) D) := by
    intro cs
    induction cs with
    | empty =>
      intro _
      simp only [pseudoItem.go]
      exact CapySubcapt.sc_elem CapyCaptureSet.Subset.empty
    | union cs1' cs2' ih1 ih2 =>
      intro hall
      simp only [pseudoItem.go]
      exact CapySubcapt.sc_union
        (ih1 (fun C hC => hall C (CapyCaptureSet.Subset.union_right_left hC)))
        (ih2 (fun C hC => hall C (CapyCaptureSet.Subset.union_right_right hC)))
    | cvar a c =>
      intro _
      simp only [pseudoItem.go]
      exact CapySubcapt.sc_elem CapyCaptureSet.Subset.empty
    | var a x =>
      intro _
      simp only [pseudoItem.go]
      exact CapySubcapt.sc_elem CapyCaptureSet.Subset.empty
    | pseudo_peak C _ =>
      intro hall
      simp only [pseudoItem.go]
      by_cases hCD : C.modeErase = D
      · rw [if_pos hCD]
        obtain ⟨C', hsc, hmem', he⟩ := CapyCtx.peaks_subcapt_pseudo_witness h
          (hall C CapyCaptureSet.Subset.refl)
        exact CapySubcapt.sc_trans hsc
          (CapySubcapt.sc_elem (hCD ▸ he ▸ PC.pseudo_subset_pseudoItem hmem'))
      · rw [if_neg hCD]
        exact CapySubcapt.sc_elem CapyCaptureSet.Subset.empty
  exact key (CapyCaptureSet.peaks Γ cs1) (fun _ hC => hC)

/-- **Same-context stable-peak lock transport.**  The `Satisfy`-`hsep` obligation
    for `Subtyp.modal_modal` when going from a compiled lock `Ψ1` (keyed by `cs1`'s
    stable peaks) to `Ψ2` (keyed by `cs2`'s stable peaks) in the SAME context, given
    `CapySubcapt Γ cs1 cs2` — the sound replacement for the FUNDAMENTAL GAP documented
    at `CapySubtyp.compile`: since `peakSepCtx` only locks *stable* peaks, and stable
    peaks survive `CapySubcapt` (`peakItem_subcapt_stable`), two distinct stable peaks
    of `cs1` compile to items that are still separated once `cs2`'s lock is assumed. -/
theorem compile_peakSepCtx_subcapt_sep {s1 s2 : Sig}
    {Γ : CapyCtx s1} {cs1 cs2 : CapyCaptureSet s1} {ctx : CompilerCtx s1 s2}
    {Ψmut2 : MutabilityCtx s2}
    (h : CapySubcapt Γ cs1 cs2) (hΓeq : ctx.capyCtx = Γ) (hcoh : ctx.Coherent) :
    ∀ (C1 C2 : CaptureSet (s2,,Kind.lock)),
      (peakSepCtx Γ (CapyCaptureSet.peakset Γ cs1)
        (ctx.srcCtx.rename Rename.succ)).HasTwoDistinct C1 C2 →
      SepCheck
        (ctx.coreCtx.push_lock
          ({ sep := peakSepCtx Γ (CapyCaptureSet.peakset Γ cs2) ctx.srcCtx,
             mutability := Ψmut2 } : ModalCtx s2))
        C1 C2 := by
  -- Every peak `p` of `cs1` survives (identically — no substitution here) as a peak of
  -- `cs2`, with its keyed source item `CapySubcapt`-related to the image's.
  have build : ∀ (p : Peak s1), Peak.IsStable Γ p →
      p ∈ peakList (CapyCaptureSet.peakset Γ cs1) →
      p ∈ peakList (CapyCaptureSet.peakset Γ cs2) ∧
      CapySubcapt Γ (peakKeyItem (CapyCaptureSet.peakset Γ cs1) p)
        (peakKeyItem (CapyCaptureSet.peakset Γ cs2) p) := by
    intro p hpstab hpmem
    cases p with
    | cvar d =>
      simp only [peakKeyItem]
      have hd := PC.mem_peakCvars_of_cvar_mem hpmem
      obtain ⟨a0, hocc⟩ := PC.peakCvars_occ hd
      obtain ⟨a', hmem'⟩ := CapyCtx.peaks_subcapt_stable_subset h hpstab hocc
      exact ⟨PC.cvar_mem_peakList (PC.cvar_mem_peakCvars hmem'), peakItem_subcapt_stable h hpstab⟩
    | pseudo D =>
      simp only [peakKeyItem]
      have hD := PC.mem_peakPseudos_of_pseudo_mem hpmem
      obtain ⟨C, hCsub, hCD⟩ := PC.peakPseudos_occ hD
      obtain ⟨C', _, hmem', he⟩ := CapyCtx.peaks_subcapt_pseudo_witness h hCsub
      have hD' : D ∈ peakPseudos (CapyCaptureSet.peakset Γ cs2) :=
        (he.symm.trans hCD) ▸ PC.pseudoBase_mem_peakPseudos hmem'
      exact ⟨PC.pseudo_mem_peakList hD', pseudoItem_subcapt_stable h⟩
  intro C1 C2 hdist
  obtain ⟨p1, hp1f, p2, hp2f, hpne, hPdisj⟩ := PC.peakSepCtx_hasTwoDistinct_ne hdist
  obtain ⟨hp1, hp1s⟩ := List.mem_filter.mp hp1f
  obtain ⟨hp2, hp2s⟩ := List.mem_filter.mp hp2f
  have hp1stab : Peak.IsStable Γ p1 := decide_eq_true_iff.mp hp1s
  have hp2stab : Peak.IsStable Γ p2 := decide_eq_true_iff.mp hp2s
  obtain ⟨hp1mem2, hsc1⟩ := build p1 hp1stab hp1
  obtain ⟨hp2mem2, hsc2⟩ := build p2 hp2stab hp2
  have mem1' : p1 ∈
      (peakList (CapyCaptureSet.peakset Γ cs2)).filter (fun p => decide (Peak.IsStable Γ p)) :=
    List.mem_filter.mpr ⟨hp1mem2, decide_eq_true_iff.mpr hp1stab⟩
  have mem2' : p2 ∈
      (peakList (CapyCaptureSet.peakset Γ cs2)).filter (fun p => decide (Peak.IsStable Γ p)) :=
    List.mem_filter.mpr ⟨hp2mem2, decide_eq_true_iff.mpr hp2stab⟩
  have htd := (PC.peakSepCtx_hasTwoDistinct_of (sc := ctx.srcCtx) mem1' mem2' hpne).rename
    (f := Rename.succ (k := Kind.lock))
  have htd' := (PC.peakSepCtx_hasTwoDistinct_of (sc := ctx.srcCtx) mem2' mem1'
    (Ne.symm hpne)).rename (f := Rename.succ (k := Kind.lock))
  have hw1 : Subcapt (ctx.coreCtx.push (Binding.lock
        ({ sep := peakSepCtx Γ (CapyCaptureSet.peakset Γ cs2) ctx.srcCtx,
           mutability := Ψmut2 } : ModalCtx s2)))
      (CapyCaptureSet.compile (peakKeyItem (CapyCaptureSet.peakset Γ cs1) p1)
        (ctx.srcCtx.rename Rename.succ))
      ((CapyCaptureSet.compile (peakKeyItem (CapyCaptureSet.peakset Γ cs2) p1)
        ctx.srcCtx).rename Rename.succ) := by
    rw [CapyCaptureSet.compile_rename]
    exact Subcapt.weaken (CapySubcapt.compile hsc1 ctx hΓeq hcoh) _
  have hw2 : Subcapt (ctx.coreCtx.push (Binding.lock
        ({ sep := peakSepCtx Γ (CapyCaptureSet.peakset Γ cs2) ctx.srcCtx,
           mutability := Ψmut2 } : ModalCtx s2)))
      (CapyCaptureSet.compile (peakKeyItem (CapyCaptureSet.peakset Γ cs1) p2)
        (ctx.srcCtx.rename Rename.succ))
      ((CapyCaptureSet.compile (peakKeyItem (CapyCaptureSet.peakset Γ cs2) p2)
        ctx.srcCtx).rename Rename.succ) := by
    rw [CapyCaptureSet.compile_rename]
    exact Subcapt.weaken (CapySubcapt.compile hsc2 ctx hΓeq hcoh) _
  rcases hPdisj with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact SepCheck.sep_symm (SepCheck.sep_mono (SepCheck.sep_symm (SepCheck.sep_mono
      (SepCheck.sep_lock (ℓ := BVar.here) Ctx.LookupLock.here htd) hw1))
      hw2)
  · exact SepCheck.sep_symm (SepCheck.sep_mono (SepCheck.sep_symm (SepCheck.sep_mono
      (SepCheck.sep_lock (ℓ := BVar.here) Ctx.LookupLock.here htd') hw2))
      hw1)

/-- Source subtyping compiles to target subtyping. -/
theorem CapySubtyp.compile {s1 : Sig} {Γ : CapyCtx s1} {sort : CapyTySort}
    {A B : CapyTy sort s1} (h : CapySubtyp Γ A B) :
    ∀ {s2 : Sig} (ctx : CompilerCtx s1 s2), ctx.capyCtx = Γ → ctx.Coherent →
    A.IsClosed → B.IsClosed →
    Subtyp ctx.coreCtx (CapyTy.compile A ctx) (CapyTy.compile B ctx) := by
  induction h with
  | top hpure =>
    intro s2 ctx hΓ hcoh hA hB
    simp only [CapyTy.compile]
    exact Subtyp.top (CapyTy.compile_isPure hpure)
  | refl =>
    intro s2 ctx hΓ hcoh hA hB
    exact Subtyp.refl
  | trans hT2 _ _ ih1 ih2 =>
    intro s2 ctx hΓ hcoh hA hB
    exact Subtyp.trans (CapyTy.compile_isClosed _ _ hT2 hcoh.srcClosed)
      (ih1 ctx hΓ hcoh hA hT2) (ih2 ctx hΓ hcoh hT2 hB)
  | tvar hlk =>
    intro s2 ctx hΓ hcoh hA hB
    simp only [CapyTy.compile]
    exact Subtyp.tvar (hcoh.tvarLookup (hΓ ▸ hlk))
  | typ _ ih =>
    intro s2 ctx hΓ hcoh hA hB
    cases hA with | typ hA1 => cases hB with | typ hB1 =>
    simp only [CapyTy.compile]
    exact Subtyp.typ (ih ctx hΓ hcoh hA1 hB1)
  | exi _ ih =>
    intro s2 ctx hΓ hcoh hA hB
    cases hA with | exi hA1 => cases hB with | exi hB1 =>
    simp only [CapyTy.compile]
    refine Subtyp.exi (ih (ctx.weakenTarget.consCVar (.unbound .epsilon) .here) ?_ ?_ ?_ ?_)
    · simp only [CompilerCtx.consCVar_capyCtx, CompilerCtx.weakenTarget_capyCtx, hΓ]
    · exact (hcoh.weakenTarget (b := placeholderBinding .cvar)
        (Binding.IsClosed.cvar CaptureBound.IsClosed.unbound)).consCVar
        CapyCaptureBound.IsClosed.unbound Ctx.LookupCVar.here
    · exact hA1
    · exact hB1
  -- K1: function-lock subtyping kernel.  The assembly (`Subtyp.poly`/`cpoly` for the
  -- bound + `Subtyp.typ` + `trans` through `.modal cs2 Ψ1 E2`, with `Subtyp.modal` for
  -- the `cs`/body change) reduces each case to ONE `Subtyp.modal_modal` premise:
  --   `Satisfy (Γt.push_lock Ψ2) (Ψ1.rename succ)`
  -- whose `hsep` demands every two distinct peaks of `cs1` separate under `cs2`'s lock.
  --
  -- RESOLVED (2026-07-01): originally a FUNDAMENTAL GAP (see git history for the
  -- original counterexample — `sc_cvar` merges two `.access_only`/`.bound` peaks into
  -- one, destroying a lock's separation).  Fixed via design choice (a): `peakSepCtx`
  -- (`TypeCompiler.lean`) now locks only *stable* peaks (`Peak.IsStable` — `.can_drop`
  -- or `.unbound`), which `CapySubcapt.sc_cvar` can never dissolve
  -- (`CapyCtx.peaks_subcapt_stable_witness`, `Capybara/TypeSystem/Core.lean`).  The
  -- `modal_modal` `hsep` obligation is now discharged by `compile_peakSepCtx_subcapt_sep`
  -- (above), built from `peakItem_subcapt_stable`.
  | arrow hcs hu ih3 =>
    intro s2 ctx hΓ hcoh hA hB
    cases hA with | arrow hTcl hcs1cl hU1cl =>
    cases hB with | arrow hTcl2 hcs2cl hU2cl =>
    simp only [CapyTy.compile]
    rename_i Γ0 cs1 cs2 U1 U2 T
    -- OUTER cpoly: the hand-written self-cvar `c` (`TypeCompiler.lean`'s `.arrow`
    -- clause) is bound `.unbound` unconditionally on BOTH sides, so `Subbound.top`
    -- discharges it trivially (no cb1-vs-cb2 divergence risk, unlike `cpoly`'s own
    -- bound — this bound is a fixed constant, not compiled from a source `cb`).
    refine Subtyp.cpoly Subbound.top Subcapt.refl (Subtyp.typ ?_)
    have hΓc : (ctx.weakenTarget (Binding.cvar Authority.access_only CaptureBound.unbound)
        ).capyCtx = Γ0 := by
      simp only [CompilerCtx.weakenTarget_capyCtx, hΓ]
    have hcohc : (ctx.weakenTarget (Binding.cvar Authority.access_only CaptureBound.unbound)
        ).Coherent :=
      hcoh.weakenTarget (Binding.IsClosed.cvar CaptureBound.IsClosed.unbound)
    have hlkc : (ctx.weakenTarget (Binding.cvar Authority.access_only CaptureBound.unbound)
        ).coreCtx.LookupCVar BVar.here Authority.access_only
        (CapyCaptureBound.compile (.unbound .epsilon)
          (ctx.weakenTarget (Binding.cvar Authority.access_only CaptureBound.unbound)).srcCtx) :=
      Ctx.LookupCVar.here
    have hcohB : ((ctx.weakenTarget (Binding.cvar Authority.access_only CaptureBound.unbound)
        ).consCVar (.unbound .epsilon) BVar.here).Coherent :=
      hcohc.consCVar CapyCaptureBound.IsClosed.unbound hlkc
    have hΓB : ((ctx.weakenTarget (Binding.cvar Authority.access_only CaptureBound.unbound)
        ).consCVar (.unbound .epsilon) BVar.here).capyCtx = Γ0,C<:.unbound .epsilon := by
      simp only [CompilerCtx.consCVar_capyCtx, CompilerCtx.weakenTarget_capyCtx, hΓ]
    -- MIDDLE cpoly: the domain re-abstraction cvar `cx`, bound to `⟦T.captureSet⟧`.
    -- The domain `T` is now the SAME type on both sides (2026-07-01 invariance
    -- override, see `CapySubtyp.arrow`), so this bound is LITERALLY identical on
    -- both sides — `Subbound.capset Subcapt.refl`, no `captureSet_subcapt` needed.
    refine Subtyp.cpoly (Subbound.capset Subcapt.refl) Subcapt.refl (Subtyp.typ ?_)
    -- The domain arrow's own domain slot (`CapyTy.compile ((T.rename succ).refineCaptureSet
    -- {x}) ctxDomain`) is now IDENTICAL on both sides (same `T`, same `ctxDomain`), so
    -- `Subtyp.arrow`'s own domain premise is `Subtyp.refl`.  Only the codomain modal
    -- kernel (`W`/`Ψ`/`E`, keyed on `cs1 ∪ {x}` vs `cs2 ∪ {x}` and `U1` vs `U2`) remains.
    refine Subtyp.arrow Subtyp.refl Subcapt.refl (Subtyp.typ ?_)
    -- GAP: only the codomain modal lock kernel (`W`/`Ψ`/`E`, keyed on `cs1 ∪ {x}` vs
    -- `cs2 ∪ {x}` and `U1` vs `U2`) remains — structurally the SAME `Subtyp.trans` +
    -- `Subtyp.modal` + `Subtyp.modal_modal` + `compile_peakSepCtx_subcapt_sep` kernel
    -- already proven for `poly`/`cpoly` (`Cf`/`Ψ.sep` compile identically via
    -- `ctxLock`, no bound-irrelevance issue: `ctxLock`'s CAPYCTX already carries the
    -- REAL `T` for the param var, and `weakenTarget`'s `srcCtx` field never depends on
    -- which binding value is pushed — only `coreCtx` does, and `compile` never reads
    -- `coreCtx` — so `Cf`/`Ψ` need no `CompileCong` bridge at all here, UNLIKE `poly`).
    -- The one NEW piece: `ih3`'s conclusion is stated over `U1.rename
    -- Rename.implicit_cvar`/`U2.rename Rename.implicit_cvar` (inserting the unused
    -- self-cvar slot `C`, since `hu` — `CapySubtyp.arrow`'s body premise — is typed at
    -- `Γ0,Cε,x:T`, one level deeper in SOURCE signature than `ctxE`'s own `(s1,x)`,
    -- which has NO `C` slot at all — E's own compile-context skips the self-cvar
    -- entirely).  Bridging needs `CapyTy.compile_mapsTo` (`ContextMorphism.lean`) —
    -- `compile (T.rename fs) ctx2 = (compile T ctx1).rename ft` for an injective
    -- SOURCE rename `fs` (here `Rename.implicit_cvar`) and a `ctx1.MapsTo ctx2 fs ft`
    -- witness — to relate `compile (U ctx1 : level (s1,x))` to `compile (U.rename
    -- implicit_cvar) ctx''` at the REAL `(s1,C,x)`-level context `ih3` needs.
    -- Constructing that `MapsTo` witness (relating `ctxE`'s C-free context to the
    -- REAL `Γ0,Cε,x:T`-matching one) turns out to hit a DEEPER, structural blocker,
    -- confirmed by unfolding both `ih3`'s premises and `CompilerCtx.Coherent`:
    --
    -- `ih3` (and every route to `hCfSub`/`Satisfy` via `CapySubcapt.compile`/
    -- `CapyHasKind.compile`) demands `ctx.Coherent` on whatever context it is fed.
    -- `CompilerCtx.Coherent.varLookup` is UNIVERSALLY quantified over every var in
    -- `capyCtx`, including `x` itself: it demands `ctx.srcCtx.lookupVar x =
    -- CapyCaptureSet.compile T.captureSet ctx.srcCtx` — the *faithful* image.  But
    -- `ctxLock`/`ctxDomain` (`TypeCompiler.lean`'s `.arrow` clause) deliberately give
    -- `x` a DIFFERENT image — the re-abstracted domain cvar `{cx}` (`.cvar (.M
    -- .epsilon) (.there .here)`) — "so `x ↦ cx` flows through" the compiled lock.
    -- `ctxLock` is therefore PROVABLY NOT `CompilerCtx.Coherent` (the `varLookup`
    -- obligation at `x`'s own slot is false in general), so `ih3` cannot be invoked
    -- there, and `CapySubcapt.compile`/`CapyHasKind.compile` cannot be used to build
    -- `hCfSub`/`Satisfy` there either — this blocks not just the `body` (E1-vs-E2)
    -- goal but the "outer lock" `Subtyp.modal`/`modal_modal` assembly too.
    --
    -- This exact non-alignment is ALREADY known and named in this codebase:
    -- `SrcAligned.consVar` (`OpenCVarSubtyp.lean`) documents its own faithful-image
    -- requirement as "the *aligned* surrogate of the `arrow` compiler's
    -- `ctxLock`/`ctxDomain`, which instead store the self-capture `{cx}`", and a
    -- later comment there states plainly this "makes `SrcAligned` FAIL for
    -- `ctxLock`/`ctxDomain`".  The apparatus that DOES cope with it —
    -- `SrcCtx.realign`, `NoPseudoPeak`, `CVarInjective`, `PeakSubstIso`/
    -- `StablePreserving`, `compile_peakSepCtx_sep_backward(_realign)` — lives in
    -- `CapyTy.compile_subst_subtyp` (`OpenCVarSubtyp.lean`, ~4000 lines), which
    -- solves the ANALOGOUS problem for substitution-invariance (`compile (T.subst σ)
    -- ctxSub = (compile T ctxOrig).subst σt`).  Adapting that apparatus from
    -- "one type under a substitution" to "two `CapySubtyp`-related types `U1`/`U2`
    -- sharing one non-aligned `ctxLock`/`ctxE`" is substantial, genuinely new proof
    -- engineering — out of scope for this session.  See memory
    -- `project_capybara_arrow_resolution` for the pointer.
    sorry
  | poly hs hcs ht ih1 ih3 =>
    intro s2 ctx hΓ hcoh hA hB
    cases hA with | poly hS1cl hcs1cl hT1cl =>
    cases hB with | poly hS2cl hcs2cl hT2cl =>
    simp only [CapyTy.compile]
    rename_i Γ0 cs1 cs2 T1 T2 S1 S2
    have hS1p : Ty.IsPureType (CapyTy.compile S1.core ctx) := CapyTy.compile_isPure S1.p
    have hS2p : Ty.IsPureType (CapyTy.compile S2.core ctx) := CapyTy.compile_isPure S2.p
    have hS2cl' : Ty.IsClosed (CapyTy.compile S2.core ctx) :=
      CapyTy.compile_isClosed S2.core ctx hS2cl hcoh.srcClosed
    set S2c : PureTy s2 := ⟨CapyTy.compile S2.core ctx, hS2p⟩ with hS2c_def
    refine Subtyp.poly
      (S1 := ⟨CapyTy.compile S1.core ctx, hS1p⟩) (S2 := S2c)
      (ih1 ctx hΓ hcoh hS2cl hS1cl) Subcapt.refl (Subtyp.typ ?_)
    have hbS2 : Binding.IsClosed (Binding.tvar S2c) := Binding.IsClosed.tvar hS2cl'
    have hcohW : (ctx.weakenTarget (Binding.tvar S2c)).Coherent := hcoh.weakenTarget hbS2
    have hΓW : (ctx.weakenTarget (Binding.tvar S2c)).capyCtx = Γ0 := by
      simp only [CompilerCtx.weakenTarget_capyCtx, hΓ]
    have hCfSub : Subcapt (ctx.coreCtx.push (Binding.tvar S2c))
        (CapyCaptureSet.compile cs1 ctx.srcCtx.weaken)
        (CapyCaptureSet.compile cs2 ctx.srcCtx.weaken) :=
      CapySubcapt.compile hcs (ctx.weakenTarget (Binding.tvar S2c)) hΓW hcohW
    refine Subtyp.trans ?_ (Subtyp.modal hCfSub ?body) (Subtyp.modal_modal ?_ ?_ ?_ ?sat)
    · exact Ty.IsClosed.modal
        (CapyCaptureSet.compile_isClosed hcs2cl hcoh.srcClosed.weaken)
        ⟨peakSepCtx_isClosed (CapyCaptureSet.peaks_isClosed _ _)
          hcoh.srcClosed.weaken, MutabilityCtx.IsClosed.empty⟩
        (CapyTy.compile_isClosed T2 (ctx.weakenTarget.consTVar CapyPureTy.top BVar.here)
          hT2cl hcoh.srcClosed.weaken.consTVar)
    case body =>
      have hcong : ((ctx.weakenTarget (Binding.tvar S2c)).consTVar S2 BVar.here).CompileCong
          (ctx.weakenTarget.consTVar CapyPureTy.top BVar.here) :=
        CompilerCtx.CompileCong.consTVar_boundIrrel S2 CapyPureTy.top BVar.here
      have heq1 : CapyTy.compile T1 ((ctx.weakenTarget (Binding.tvar S2c)).consTVar S2 BVar.here)
          = CapyTy.compile T1 (ctx.weakenTarget.consTVar CapyPureTy.top BVar.here) :=
        CapyTy.compile_eq_of T1 _ _ hcong
      have heq2 : CapyTy.compile T2 ((ctx.weakenTarget (Binding.tvar S2c)).consTVar S2 BVar.here)
          = CapyTy.compile T2 (ctx.weakenTarget.consTVar CapyPureTy.top BVar.here) :=
        CapyTy.compile_eq_of T2 _ _ hcong
      have hlk : (ctx.weakenTarget (Binding.tvar S2c)).coreCtx.LookupTVar BVar.here
          (CapyPureTy.compile S2 (ctx.weakenTarget (Binding.tvar S2c))) := by
        rw [CapyPureTy.compile_rename (ctx := ctx) (ctx' := ctx.weakenTarget (Binding.tvar S2c))
          (ρ := Rename.succ) rfl rfl]
        exact Ctx.LookupTVar.here
      have hcohW' : ((ctx.weakenTarget (Binding.tvar S2c)).consTVar S2 BVar.here).Coherent :=
        hcohW.consTVar hS2cl hlk
      have hΓW' : ((ctx.weakenTarget (Binding.tvar S2c)).consTVar S2 BVar.here).capyCtx
          = Γ0,X<:S2 := by
        simp only [CompilerCtx.consTVar_capyCtx, CompilerCtx.weakenTarget_capyCtx, hΓ,
          CapyCtx.push_tvar]
      have hLock : Binding.IsClosed
          (Binding.lock (⟨peakSepCtx ctx.capyCtx (CapyCaptureSet.peakset ctx.capyCtx cs1)
            ctx.srcCtx.weaken, MutabilityCtx.empty⟩ : ModalCtx (s2,,Kind.tvar))) :=
        Binding.IsClosed.lock ⟨peakSepCtx_isClosed (CapyCaptureSet.peaks_isClosed _ _)
          hcohW.srcClosed, MutabilityCtx.IsClosed.empty⟩
      have hE1 := ih3
        (((ctx.weakenTarget (Binding.tvar S2c)).consTVar S2 BVar.here).weakenTarget
          (Binding.lock ⟨peakSepCtx ctx.capyCtx (CapyCaptureSet.peakset ctx.capyCtx cs1)
            ctx.srcCtx.weaken, MutabilityCtx.empty⟩))
        (by simp only [CompilerCtx.weakenTarget_capyCtx, hΓW'])
        (hcohW'.weakenTarget hLock) hT1cl hT2cl
      have hrename1 : CapyTy.compile T1
          (((ctx.weakenTarget (Binding.tvar S2c)).consTVar S2 BVar.here).weakenTarget
            (Binding.lock ⟨peakSepCtx ctx.capyCtx (CapyCaptureSet.peakset ctx.capyCtx cs1)
              ctx.srcCtx.weaken, MutabilityCtx.empty⟩))
          = (CapyTy.compile T1
              ((ctx.weakenTarget (Binding.tvar S2c)).consTVar S2 BVar.here)).rename
            Rename.succ :=
        CapyTy.compile_rename T1 _ _ Rename.succ rfl rfl
      have hrename2 : CapyTy.compile T2
          (((ctx.weakenTarget (Binding.tvar S2c)).consTVar S2 BVar.here).weakenTarget
            (Binding.lock ⟨peakSepCtx ctx.capyCtx (CapyCaptureSet.peakset ctx.capyCtx cs1)
              ctx.srcCtx.weaken, MutabilityCtx.empty⟩))
          = (CapyTy.compile T2
              ((ctx.weakenTarget (Binding.tvar S2c)).consTVar S2 BVar.here)).rename
            Rename.succ :=
        CapyTy.compile_rename T2 _ _ Rename.succ rfl rfl
      rw [hrename1, hrename2, heq1, heq2] at hE1
      exact hE1
    · exact Ctx.IsClosed.push hcoh.closed (Binding.IsClosed.tvar hS2cl')
    · exact ⟨peakSepCtx_isClosed (CapyCaptureSet.peaks_isClosed _ _)
        hcoh.srcClosed.weaken, MutabilityCtx.IsClosed.empty⟩
    · exact ⟨peakSepCtx_isClosed (CapyCaptureSet.peaks_isClosed _ _)
        hcoh.srcClosed.weaken, MutabilityCtx.IsClosed.empty⟩
    case sat =>
      apply Satisfy.satisfy
      · intro C m hmem
        simp only [ModalCtx.rename, MutabilityCtx.rename] at hmem
        cases hmem
      · intro C1 C2 hdist
        simp only [ModalCtx.rename] at hdist
        rw [← peakSepCtx_rename] at hdist
        have hcs' : CapySubcapt ctx.capyCtx cs1 cs2 := hΓ ▸ hcs
        exact compile_peakSepCtx_subcapt_sep (Ψmut2 := MutabilityCtx.empty)
          (ctx := ctx.weakenTarget (Binding.tvar S2c)) hcs' rfl hcohW C1 C2 hdist
  | cpoly hsb hcs ht ih3 =>
    intro s2 ctx hΓ hcoh hA hB
    cases hA with | cpoly hcb1cl hcs1cl hT1cl =>
    cases hB with | cpoly hcb2cl hcs2cl hT2cl =>
    simp only [CapyTy.compile]
    rename_i Γ0 cb2 cb1 cs1 cs2 T1 T2
    have hSubbound : Subbound ctx.coreCtx (CapyCaptureBound.compile cb2 ctx.srcCtx)
        (CapyCaptureBound.compile cb1 ctx.srcCtx) :=
      CapySubbound.compile hsb ctx hΓ hcoh
    set cb2c : CaptureBound s2 := CapyCaptureBound.compile cb2 ctx.srcCtx with hcb2c_def
    refine Subtyp.cpoly hSubbound Subcapt.refl (Subtyp.typ ?_)
    have hcb2cl' : CaptureBound.IsClosed cb2c :=
      CapyCaptureBound.compile_isClosed hcb2cl hcoh.srcClosed
    have hbCV : Binding.IsClosed (Binding.cvar Authority.access_only cb2c) :=
      Binding.IsClosed.cvar hcb2cl'
    have hcohW : (ctx.weakenTarget (Binding.cvar Authority.access_only cb2c)).Coherent :=
      hcoh.weakenTarget hbCV
    have hΓW : (ctx.weakenTarget (Binding.cvar Authority.access_only cb2c)).capyCtx = Γ0 := by
      simp only [CompilerCtx.weakenTarget_capyCtx, hΓ]
    have hCfSub : Subcapt (ctx.coreCtx.push (Binding.cvar Authority.access_only cb2c))
        (CapyCaptureSet.compile cs1 ctx.srcCtx.weaken)
        (CapyCaptureSet.compile cs2 ctx.srcCtx.weaken) :=
      CapySubcapt.compile hcs (ctx.weakenTarget (Binding.cvar Authority.access_only cb2c))
        hΓW hcohW
    refine Subtyp.trans ?_ (Subtyp.modal hCfSub ?body) (Subtyp.modal_modal ?_ ?_ ?_ ?sat)
    · exact Ty.IsClosed.modal
        (CapyCaptureSet.compile_isClosed hcs2cl hcoh.srcClosed.weaken)
        ⟨peakSepCtx_isClosed (CapyCaptureSet.peaks_isClosed _ _)
          hcoh.srcClosed.weaken, CapyCaptureBound.mutabilityCtx_isClosed⟩
        (CapyTy.compile_isClosed T2 (ctx.weakenTarget.consCVar cb2 BVar.here)
          hT2cl hcoh.srcClosed.weaken.consCVar)
    case body =>
      -- GAP: unlike `poly` (whose `ctxE` uses a bound-IRRELEVANT placeholder `.top`,
      -- since a tvar's bound never affects `peaks`/`IsStableCVar`), `cpoly`'s `ctxE`
      -- (`TypeCompiler.lean`) threads the REAL `cb` into the freshly-bound cvar's own
      -- slot: `ctx.weakenTarget.consCVar cb .here`.  A cvar's OWN bound genuinely
      -- affects `CapyCtx.IsStableCVar` (`∃ m, lookup_cvar c = .unbound m`), so
      -- `compile T1 (…consCVar cb1 .here)` (what THIS goal needs, from unfolding
      -- `compile (.cpoly cb1 cs1 T1) ctx`) and `compile T1 (…consCVar cb2 .here)`
      -- (what `ih3` — typed at `ht : CapySubtyp (Γ0,C<:cb2) T1 T2` — actually gives)
      -- can genuinely disagree whenever `T1` has a NESTED `poly`/`cpoly`/`arrow` whose
      -- lock keys off `.here`'s stability, since `CapySubbound Γ cb2 cb1` allows a
      -- strict narrowing (`bound_unbound`: `cb1 = .unbound m` stable ↝ `cb2 = .bound C`
      -- possibly unstable), never the reverse.  `CompilerCtx.CompileCong.consCVar`
      -- (`LockKernel.lean`) confirms this is not a `CompileCong`-style irrelevance —
      -- it requires the SAME `cb` on both sides, unlike `consTVar`'s
      -- `consTVar_boundIrrel`.  Closing this needs a genuinely new monotonicity
      -- argument (compiling under a narrower cvar bound only ever *adds* lock
      -- entries), out of scope for the pairwise-separation fix this file is built
      -- around.
      sorry
    · exact Ctx.IsClosed.push hcoh.closed (Binding.IsClosed.cvar hcb2cl')
    · exact ⟨peakSepCtx_isClosed (CapyCaptureSet.peaks_isClosed _ _)
        hcoh.srcClosed.weaken, CapyCaptureBound.mutabilityCtx_isClosed⟩
    · exact ⟨peakSepCtx_isClosed (CapyCaptureSet.peaks_isClosed _ _)
        hcoh.srcClosed.weaken, CapyCaptureBound.mutabilityCtx_isClosed⟩
    case sat =>
      apply Satisfy.satisfy
      · intro C m hmem
        simp only [ModalCtx.rename] at hmem
        cases hsb with
        | capset _ =>
          simp only [CapyCaptureBound.mutabilityCtx, MutabilityCtx.rename] at hmem
          cases hmem
        | unbound hle =>
          simp only [CapyCaptureBound.mutabilityCtx, MutabilityCtx.rename] at hmem
          cases hmem with
          | here =>
            cases m with
            | epsilon => exact HasKind.rw
            | ro =>
              cases hle
              exact HasKind.imm Ctx.LookupLock.here MutabilityCtx.Has.here
          | there hmem => cases hmem
        | bound_unbound hck =>
          rename_i C' _
          simp only [CapyCaptureBound.mutabilityCtx, MutabilityCtx.rename] at hmem
          cases hmem with
          | here =>
            cases m with
            | epsilon => exact HasKind.rw
            | ro =>
              set ctxL := (ctx.weakenTarget (Binding.cvar Authority.access_only cb2c)).weakenTarget
                (Binding.lock ⟨peakSepCtx ctx.capyCtx (CapyCaptureSet.peakset ctx.capyCtx cs2)
                  ctx.srcCtx.weaken, MutabilityCtx.empty⟩) with hctxL_def
              have hΓL : ctxL.capyCtx = Γ0 := by
                simp only [hctxL_def, CompilerCtx.weakenTarget_capyCtx, hΓ]
              have hcohL : ctxL.Coherent :=
                hcohW.weakenTarget (Binding.IsClosed.lock
                  ⟨peakSepCtx_isClosed (CapyCaptureSet.peaks_isClosed _ _)
                    hcoh.srcClosed.weaken, MutabilityCtx.IsClosed.empty⟩)
              have hHK : HasKind ctxL.coreCtx (CapyCaptureSet.compile C' ctxL.srcCtx) .ro :=
                CapyHasKind.compile hck ctxL hΓL hcohL
              have hlkc : ctxL.coreCtx.LookupCVar (.there BVar.here) Authority.access_only
                  ((cb2c.rename Rename.succ).rename Rename.succ) :=
                Ctx.LookupCVar.there Ctx.LookupCVar.here
              have hsc : Subcapt ctxL.coreCtx (.cvar (.M .epsilon) (.there BVar.here))
                  (CapyCaptureSet.compile C' ctxL.srcCtx) := by
                simp only [hctxL_def, CompilerCtx.weakenTarget_srcCtx,
                  CapyCaptureSet.compile_rename]
                rw [hcb2c_def] at hlkc
                simp only [CapyCaptureBound.compile, CaptureBound.rename] at hlkc
                exact Subcapt.sc_cvar hlkc
              exact HasKind.sc hsc hHK
          | there hmem => cases hmem
      · intro C1 C2 hdist
        simp only [ModalCtx.rename] at hdist
        rw [← peakSepCtx_rename] at hdist
        have hcs' : CapySubcapt ctx.capyCtx cs1 cs2 := hΓ ▸ hcs
        exact compile_peakSepCtx_subcapt_sep (Ψmut2 := CapyCaptureBound.mutabilityCtx cb2 BVar.here)
          (ctx := ctx.weakenTarget (Binding.cvar Authority.access_only cb2c)) hcs' rfl hcohW C1 C2
          hdist

/-!
## `AccessOnly` / `droppable` transport  (Workstream A — `fresh`'s `ao`/`drp`)

Source `AccessOnly`/`droppable` are stated over `peakset` membership of `.cvar`
atoms (+ `lookup_authority`).  To transport them to the target we relate the
target peaks of a compiled set to the compiled source peaks, then read off the
source hypothesis per peak cvar (compilation preserves the access mode, and the
`cvarLookup` coherence field preserves authority).
-/

/-- Compilation preserves `PeaksOnly` for `NoPseudoPeak` sets (a `.cvar` atom
    compiles to a `.cvar`).  The `NoPseudoPeak` hypothesis excludes the `pseudo_peak`
    case, which would be false (a frozen `pseudo_peak (var x)` is `PeaksOnly` but
    compiles transparently to a non-peak `⟦var x⟧`).  All real callers feed either a
    `peakItem` (cvar-only) or a `resourcePeaks` result — both `NoPseudoPeak`. -/
theorem CapyCaptureSet.compile_peaksOnly {cs : CapyCaptureSet s1} {sc : SrcCtx s1 s2}
    (h : cs.PeaksOnly) (hnp : cs.NoPseudoPeak) : (CapyCaptureSet.compile cs sc).PeaksOnly := by
  induction hnp with
  | empty => exact CaptureSet.PeaksOnly.empty
  | union _ _ ih1 ih2 =>
    cases h with
    | union h1 h2 => exact CaptureSet.PeaksOnly.union (ih1 h1) (ih2 h2)
  | cvar => exact CaptureSet.PeaksOnly.cvar
  -- `var` cannot occur under `PeaksOnly` (`h`); `pseudo_peak` cannot occur under
  -- `NoPseudoPeak` (the induction has no such case).
  | var => nomatch h

/-- Target peak-resolution fixes a `PeaksOnly` set (nothing left to resolve). -/
theorem CaptureSet.peaks_of_peaksOnly {Γ : Ctx s} {cs : CaptureSet s}
    (h : cs.PeaksOnly) : CaptureSet.peaks Γ cs = cs := by
  induction h with
  | empty => simp only [CaptureSet.peaks]
  | union _ _ ih1 ih2 => simp only [CaptureSet.peaks, ih1, ih2]; rfl
  | cvar => simp only [CaptureSet.peaks]

/-- **(A1, resource view) Target peaks of a compiled set = compiled source
    `resourcePeaks`.**  `⟦C⟧ = ⟦resourcePeaks Γ C⟧` by (★) `compile_resourcePeaks`;
    the latter is `PeaksOnly` AND `NoPseudoPeak`, hence fixed by the target `peaks`.
    Using `resourcePeaks` (not `peaks`) is what makes `compile_peaksOnly` apply: a
    frozen peak is resolved into its content, so no `pseudo_peak` survives. -/
theorem CapyCaptureSet.compile_resourcePeaks_target {s1 s2 : Sig} {ctx : CompilerCtx s1 s2}
    (hcoh : ctx.Coherent) {C : CapyCaptureSet s1} (hC : C.IsClosed) :
    CaptureSet.peaks ctx.coreCtx (CapyCaptureSet.compile C ctx.srcCtx)
      = CapyCaptureSet.compile (CapyCaptureSet.resourcePeaks ctx.capyCtx C) ctx.srcCtx := by
  have hAligned : SrcAligned ctx.capyCtx ctx.srcCtx := by
    intro x T hlook
    obtain ⟨_, _, hB, _⟩ := hcoh.varLookup hlook
    exact hB
  rw [← CapyCaptureSet.compile_resourcePeaks hcoh.capyClosed hAligned hC]
  exact CaptureSet.peaks_of_peaksOnly
    (CapyCaptureSet.compile_peaksOnly (CapyCaptureSet.resourcePeaks_peaksOnly ctx.capyCtx C)
      (CapyCaptureSet.resourcePeaks_noPseudoPeak ctx.capyCtx C))

/-- **(A2, resource view)** A target cvar atom of a compiled `NoPseudoPeak` `PeaksOnly`
    set traces to a source cvar of `cs` (with the same access mode, via `lookupCVar`) —
    SORRY-FREE.  The frozen-peak ("Step-2 lock") case, where a target cvar inside
    `⟦pseudo_peak C⟧` is a cvar of the frozen peak's CONTENT rather than a separate lock
    peak (so it has no source-cvar witness under opaque `Subset`), cannot arise here.
    A plain `PeaksOnly`-only LOCK-view tracer covering frozen peaks is unprovable for
    exactly that reason; callers use this resource view or the peak-LOCAL disjunction
    below. -/
theorem CapyCaptureSet.compile_cvar_subset_inv_resource {s1 s2 : Sig}
    {cs : CapyCaptureSet s1} (hpo : cs.PeaksOnly) (hnp : cs.NoPseudoPeak)
    {sc : SrcCtx s1 s2} :
    ∀ {a : Access} {c' : BVar s2 .cvar},
      CaptureSet.Subset (.cvar a c') (CapyCaptureSet.compile cs sc) →
      ∃ c, sc.lookupCVar c = c' ∧ CapyCaptureSet.Subset (.cvar a c) cs := by
  induction hnp with
  | empty =>
    intro a c' h; simp only [CapyCaptureSet.compile] at h; cases h
  | cvar =>
    intro a c' h; simp only [CapyCaptureSet.compile] at h; cases h
    exact ⟨_, rfl, CapyCaptureSet.Subset.refl⟩
  | union _ _ ih1 ih2 =>
    cases hpo with
    | union hpo1 hpo2 =>
      intro a c' h
      simp only [CapyCaptureSet.compile] at h
      cases h with
      | union_right_left h1 =>
        obtain ⟨c, hc, hsub⟩ := ih1 hpo1 h1
        exact ⟨c, hc, CapyCaptureSet.Subset.union_right_left hsub⟩
      | union_right_right h2 =>
        obtain ⟨c, hc, hsub⟩ := ih2 hpo2 h2
        exact ⟨c, hc, CapyCaptureSet.Subset.union_right_right hsub⟩
  | var => nomatch hpo

/-- **(A2′, peak-LOCAL tracer — SORRY-FREE.)**
    A target cvar atom of a compiled `PeaksOnly` set is EITHER the `lookupCVar`-image
    of a source cvar atom OR a cvar *inside a frozen peak's content* (a `pseudo_peak C`
    occurrence).  Whereas a plain source-cvar tracer is false for frozen peaks (the
    atom has no source-cvar witness), this DISJUNCTION is provable: it is local to
    `cs`'s atoms (no non-local `peakItem` gathering), so it inducts cleanly. -/
theorem CapyCaptureSet.compile_atom_source {s1 s2 : Sig} {cs : CapyCaptureSet s1}
    (hpo : cs.PeaksOnly) {sc : SrcCtx s1 s2} :
    ∀ {a : Access} {Z : BVar s2 .cvar},
      CaptureSet.Subset (.cvar a Z) (CapyCaptureSet.compile cs sc) →
      (∃ c, sc.lookupCVar c = Z ∧ CapyCaptureSet.Subset (.cvar a c) cs) ∨
      (∃ C, CapyCaptureSet.Subset (.pseudo_peak C) cs ∧
        CaptureSet.Subset (.cvar a Z) (CapyCaptureSet.compile C sc)) := by
  induction hpo with
  | empty => intro a Z h; simp only [CapyCaptureSet.compile] at h; cases h
  | cvar =>
    intro a Z h; simp only [CapyCaptureSet.compile] at h; cases h
    exact Or.inl ⟨_, rfl, CapyCaptureSet.Subset.refl⟩
  | union _ _ ih1 ih2 =>
    intro a Z h; simp only [CapyCaptureSet.compile] at h
    cases h with
    | union_right_left h1 =>
      rcases ih1 h1 with ⟨c, hc, hsub⟩ | ⟨C, hsub, hcsub⟩
      · exact Or.inl ⟨c, hc, CapyCaptureSet.Subset.union_right_left hsub⟩
      · exact Or.inr ⟨C, CapyCaptureSet.Subset.union_right_left hsub, hcsub⟩
    | union_right_right h2 =>
      rcases ih2 h2 with ⟨c, hc, hsub⟩ | ⟨C, hsub, hcsub⟩
      · exact Or.inl ⟨c, hc, CapyCaptureSet.Subset.union_right_right hsub⟩
      · exact Or.inr ⟨C, CapyCaptureSet.Subset.union_right_right hsub, hcsub⟩
  | pseudo_peak =>
    intro a Z h; simp only [CapyCaptureSet.compile] at h
    exact Or.inr ⟨_, CapyCaptureSet.Subset.refl, h⟩

/-- **(A3) Compilation preserves `AccessOnly`** (RESOURCE view: via `resourcePeaks`,
    so a frozen peak's content drops are seen).  Sorry-free. -/
theorem CapyCaptureSet.compile_accessOnly {s1 s2 : Sig} {ctx : CompilerCtx s1 s2}
    (hcoh : ctx.Coherent) {D : CapyCaptureSet s1} (hD : D.IsClosed)
    (h : CapyCaptureSet.AccessOnly ctx.capyCtx D) :
    CaptureSet.AccessOnly ctx.coreCtx (CapyCaptureSet.compile D ctx.srcCtx) := by
  intro c' hmem
  simp only [CaptureSet.peakset] at hmem
  rw [CapyCaptureSet.compile_resourcePeaks_target hcoh hD] at hmem
  obtain ⟨c, _, hsub⟩ := CapyCaptureSet.compile_cvar_subset_inv_resource
    (CapyCaptureSet.resourcePeaks_peaksOnly ctx.capyCtx D)
    (CapyCaptureSet.resourcePeaks_noPseudoPeak ctx.capyCtx D) hmem
  exact h c hsub

/-- **(A4) Compilation preserves `droppable`** (authority via `cvarLookup`; RESOURCE
    view via `resourcePeaks`).  Sorry-free. -/
theorem CapyCaptureSet.compile_droppable {s1 s2 : Sig} {ctx : CompilerCtx s1 s2}
    (hcoh : ctx.Coherent) {D : CapyCaptureSet s1} (hD : D.IsClosed)
    (h : CapyCaptureSet.droppable ctx.capyCtx D) :
    CaptureSet.droppable ctx.coreCtx (CapyCaptureSet.compile D ctx.srcCtx) := by
  intro a c' hmem
  simp only [CaptureSet.peakset] at hmem
  rw [CapyCaptureSet.compile_resourcePeaks_target hcoh hD] at hmem
  obtain ⟨c, hc, hsub⟩ := CapyCaptureSet.compile_cvar_subset_inv_resource
    (CapyCaptureSet.resourcePeaks_peaksOnly ctx.capyCtx D)
    (CapyCaptureSet.resourcePeaks_noPseudoPeak ctx.capyCtx D) hmem
  have hauth : ctx.capyCtx.lookup_authority c = .can_drop := h a c hsub
  have hspec := ctx.capyCtx.lookup_cvar_spec c
  rw [hauth] at hspec
  have hcore := hcoh.cvarLookup hspec
  simp only [CapyAuthority.compile] at hcore
  rw [← hc]
  exact (Ctx.LookupCVar.eq_authority hcore).symm

end Compilation
