import Semantic.CoreCapybara.LegacyCompilation.SepCovered
open CoreCapybara

namespace Compilation

/-!
# Compiling separation checks (`CapySepCheck` ⟹ `SepCheck`)

The transport from source separation derivations to target ones.  Structural
cases map rule-to-rule (`sep_symm`/`sep_union`/`sep_empty`/`sep_ro`); `sep_sc`
maps to the *stronger* target `sep_mono` (dropping the `EquivP` requirement,
which the target does not need — `EquivP` is still consumed here, to transport
the ambient covering to the premise's larger capture).  The one genuinely
non-structural case is `sep_distinct`: the source *postulates* that distinct
peaks never alias; the target must read this off the ambient covering lock
(`CompilerCtx.SepCovered`), which the compiled program's enclosing wrap lock
provides.  This is why the covering hypothesis is stated at the conclusion
operands `C1 ∪ C2`: the `EquivP` discipline of `sep_sc` keeps every capture in
a `CapySepCheck` derivation peak-equal to the conclusion pair, so covering the
conclusion covers every leaf.

The operands are required `NoPseudoPeak` (frozen peaks are a substitution
artifact, never surface syntax — separation premises of source rules are
surface sets), which rules the `pseudo` peaks out of `sep_distinct`.
-/

/-- `CoveredBy` (mutability-aware subset) embeds into `CapySubcapt`
    (`refl ↦ sc_mode`, `union ↦ sc_union`/`sc_elem`). -/
theorem CapyCaptureSet.CoveredBy.toSubcapt {s : Sig} {Γ : CapyCtx s}
    {C1 C2 : CapyCaptureSet s} (h : C1.CoveredBy C2) : CapySubcapt Γ C1 C2 := by
  induction h with
  | refl hm => exact CapySubcapt.sc_mode hm
  | empty => exact CapySubcapt.sc_elem CapyCaptureSet.Subset.empty
  | union_left _ _ ih1 ih2 => exact CapySubcapt.sc_union ih1 ih2
  | union_right_left _ ih =>
    exact CapySubcapt.sc_trans ih
      (CapySubcapt.sc_elem (CapyCaptureSet.Subset.union_right_left
        CapyCaptureSet.Subset.refl))
  | union_right_right _ ih =>
    exact CapySubcapt.sc_trans ih
      (CapySubcapt.sc_elem (CapyCaptureSet.Subset.union_right_right
        CapyCaptureSet.Subset.refl))

/-- **Per-atom `CapySubcapt` witness across a `CoveredBy`.**  The `CoveredBy`
    analogue of `CapyCtx.peaks_subcapt_stable_witness`: a `cvar` atom of the covered
    set survives (at some access `a'`) into the covering set, with the two atoms
    themselves `CapySubcapt`-related.  `CoveredBy` being purely structural, the
    induction needs no context reasoning — only the `refl`/`ro_eps` mutability step
    reads `sc_ro`. -/
theorem cvar_witness_coveredby {s : Sig} {Γ : CapyCtx s} {C1 C2 : CapyCaptureSet s}
    (h : C1.CoveredBy C2) :
    ∀ {c : BVar s .cvar} {a : Access}, CapyCaptureSet.Subset (.cvar a c) C1 →
      ∃ a', CapySubcapt Γ (.cvar a c) (.cvar a' c) ∧
        CapyCaptureSet.Subset (.cvar a' c) C2 := by
  induction h with
  | refl hm =>
    intro c a hmem
    cases hm with
    | refl => exact ⟨a, CapySubcapt.sc_elem CapyCaptureSet.Subset.refl, hmem⟩
    | ro_eps =>
      simp only [CapyCaptureSet.applyMut_ro] at hmem
      obtain ⟨a0, hmem0, ha⟩ := CapyCaptureSet.cvar_mem_applyRO_inv' hmem
      exact ⟨a0, by rw [ha]; exact CapySubcapt.sc_ro (C := .cvar a0 c), hmem0⟩
  | empty => intro c a hmem; cases hmem
  | union_left _ _ ih1 ih2 =>
    intro c a hmem
    cases hmem with
    | union_right_left h1 => exact ih1 h1
    | union_right_right h2 => exact ih2 h2
  | union_right_left _ ih =>
    intro c a hmem
    obtain ⟨a', hsc, hmem'⟩ := ih hmem
    exact ⟨a', hsc, CapyCaptureSet.Subset.union_right_left hmem'⟩
  | union_right_right _ ih =>
    intro c a hmem
    obtain ⟨a', hsc, hmem'⟩ := ih hmem
    exact ⟨a', hsc, CapyCaptureSet.Subset.union_right_right hmem'⟩

/-- **Per-frozen-peak `CapySubcapt` witness across a `CoveredBy`.**  The `pseudo_peak`
    analogue of `cvar_witness_coveredby` (mirrors `CapyCtx.peaks_subcapt_pseudo_witness`):
    a frozen peak of the covered set survives into the covering set with equal
    mode-erased base and a `CapySubcapt`-related content. -/
theorem pseudo_witness_coveredby {s : Sig} {Γ : CapyCtx s} {C1 C2 : CapyCaptureSet s}
    (h : C1.CoveredBy C2) :
    ∀ {D : CapyCaptureSet s}, CapyCaptureSet.Subset (.pseudo_peak D) C1 →
      ∃ D', CapySubcapt Γ (.pseudo_peak D) (.pseudo_peak D') ∧
        CapyCaptureSet.Subset (.pseudo_peak D') C2 ∧ D.modeErase = D'.modeErase := by
  induction h with
  | refl hm =>
    intro D hmem
    cases hm with
    | refl => exact ⟨D, CapySubcapt.sc_elem CapyCaptureSet.Subset.refl, hmem, rfl⟩
    | ro_eps =>
      simp only [CapyCaptureSet.applyMut_ro] at hmem
      obtain ⟨D0, hmem0, hD⟩ := CapyCaptureSet.pseudo_mem_applyRO_inv' hmem
      refine ⟨D0, ?_, hmem0, ?_⟩
      · rw [hD]; exact CapySubcapt.sc_ro (C := .pseudo_peak D0)
      · rw [hD]; simp only [CapyCaptureSet.modeErase_applyRO]
  | empty => intro D hmem; cases hmem
  | union_left _ _ ih1 ih2 =>
    intro D hmem
    cases hmem with
    | union_right_left h1 => exact ih1 h1
    | union_right_right h2 => exact ih2 h2
  | union_right_left _ ih =>
    intro D hmem
    obtain ⟨D', hsc, hmem', he⟩ := ih hmem
    exact ⟨D', hsc, CapyCaptureSet.Subset.union_right_left hmem', he⟩
  | union_right_right _ ih =>
    intro D hmem
    obtain ⟨D', hsc, hmem', he⟩ := ih hmem
    exact ⟨D', hsc, CapyCaptureSet.Subset.union_right_right hmem', he⟩

/-- **Peak items are `CapySubcapt`-related across a `CoveredBy`** (the `CoveredBy`
    analogue of `peakItem_subcapt_stable`): the item cvar `c` keys in the covered
    peak set is below the item it keys in the covering peak set, unioned over `c`'s
    access-mode occurrences via `cvar_witness_coveredby`. -/
theorem peakItem_subcapt_coveredby {s : Sig} {Γ : CapyCtx s} {Q P : CapyPeakSet s}
    (h : Q.cs.CoveredBy P.cs) (c : BVar s .cvar) :
    CapySubcapt Γ (peakItem Q c) (peakItem P c) := by
  have key : ∀ (L : List Access),
      (∀ b ∈ L, CapyCaptureSet.Subset (.cvar b c) Q.cs) →
      CapySubcapt Γ (L.foldr (fun b acc => CapyCaptureSet.cvar b c ∪ acc) .empty)
        (peakItem P c) := by
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
      obtain ⟨a', hsc, hmem'⟩ := cvar_witness_coveredby (Γ := Γ) h (hL b List.mem_cons_self)
      exact CapySubcapt.sc_trans hsc (CapySubcapt.sc_elem (PC.cvar_subset_peakItem hmem'))
  exact key (accessedAt Q c)
    (fun b hb => PC.accessedAt_go_subset _ (by simpa only [accessedAt] using hb))

/-- **Frozen-peak items are `CapySubcapt`-related across a `CoveredBy`** (the
    `CoveredBy` analogue of `pseudoItem_subcapt_stable`), by structural induction over
    the covered peak set with `pseudo_witness_coveredby`. -/
theorem pseudoItem_subcapt_coveredby {s : Sig} {Γ : CapyCtx s} {Q P : CapyPeakSet s}
    (h : Q.cs.CoveredBy P.cs) (D : CapyCaptureSet s) :
    CapySubcapt Γ (pseudoItem Q D) (pseudoItem P D) := by
  have key : ∀ (cs : CapyCaptureSet s),
      (∀ C, CapyCaptureSet.Subset (.pseudo_peak C) cs →
        CapyCaptureSet.Subset (.pseudo_peak C) Q.cs) →
      CapySubcapt Γ (pseudoItem.go D cs) (pseudoItem P D) := by
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
        obtain ⟨C', hsc, hmem', he⟩ := pseudo_witness_coveredby (Γ := Γ) h
          (hall C CapyCaptureSet.Subset.refl)
        exact CapySubcapt.sc_trans hsc
          (CapySubcapt.sc_elem (hCD ▸ he ▸ PC.pseudo_subset_pseudoItem hmem'))
      · rw [if_neg hCD]
        exact CapySubcapt.sc_elem CapyCaptureSet.Subset.empty
  exact key Q.cs (fun _ hC => hC)

/-- **Covering embedding from a `CoveredBy` of peak sets.**  Every peak of the covered
    peak set `Q` survives as a peak of the covering peak set `P`, with its key item
    `CapySubcapt`-below the survivor's — the `hb` argument `CompilerCtx.SepCovered.mono`
    consumes (the `CoveredBy` analogue of `peak_build_of_subcapt`). -/
theorem covering_build {s : Sig} {Γ : CapyCtx s} (Q P : CapyPeakSet s)
    (h : Q.cs.CoveredBy P.cs) :
    ∀ p : Peak s, p ∈ peakList Q →
      p ∈ peakList P ∧ CapySubcapt Γ (peakKeyItem Q p) (peakKeyItem P p) := by
  intro p hmem
  cases p with
  | cvar c =>
    simp only [peakKeyItem]
    obtain ⟨a0, hocc⟩ := PC.peakCvars_occ (PC.mem_peakCvars_of_cvar_mem hmem)
    obtain ⟨a', _, hmem'⟩ := cvar_witness_coveredby (Γ := Γ) h hocc
    exact ⟨PC.cvar_mem_peakList (PC.cvar_mem_peakCvars hmem'),
      peakItem_subcapt_coveredby h c⟩
  | pseudo D =>
    simp only [peakKeyItem]
    obtain ⟨C, hCsub, hCD⟩ := PC.peakPseudos_occ (PC.mem_peakPseudos_of_pseudo_mem hmem)
    obtain ⟨C', _, hmem', he⟩ := pseudo_witness_coveredby (Γ := Γ) h hCsub
    have hD' : D ∈ peakPseudos P :=
      (he.symm.trans hCD) ▸ PC.pseudoBase_mem_peakPseudos hmem'
    exact ⟨PC.pseudo_mem_peakList hD', pseudoItem_subcapt_coveredby h D⟩

/-- **Restriction of the ambient covering along a peak-level subset** (`SubP`):
    the consumer-facing packaging of `covering_build` — what lets the `app`
    case's covering of the use-set `{εx} ∪ {εy}` cover the separation operands
    `D ∪ interfere_set` (via `CapyHasType.app_use_covered`). -/
theorem CompilerCtx.SepCovered.of_subP {s1 s2 : Sig} {ctx : CompilerCtx s1 s2}
    {U U' : CapyCaptureSet s1}
    (hcov : ctx.SepCovered U) (hsub : ctx.SubCoherent)
    (h : CapyCaptureSet.SubP ctx.capyCtx U' U) :
    ctx.SepCovered U' :=
  hcov.mono hsub (fun p _ hmem =>
    covering_build (CapyCaptureSet.peakset ctx.capyCtx U')
      (CapyCaptureSet.peakset ctx.capyCtx U) h p hmem)

/-- Transport of the ambient covering across an `EquivP`-narrowed left operand
    (the `sep_sc` premise direction): peak-equivalence keeps the stable peaks
    and their key items `CapySubcapt`-comparable, so a covering of `C1' ∪ C2`
    restricts to one of `C1 ∪ C2`. -/
theorem CompilerCtx.SepCovered.of_equivP_union {s1 s2 : Sig}
    {ctx : CompilerCtx s1 s2} {C1 C1' C2 : CapyCaptureSet s1}
    (hcov : ctx.SepCovered (C1' ∪ C2)) (hsub : ctx.SubCoherent)
    (heq : CapyCaptureSet.EquivP ctx.capyCtx C1' C1) :
    ctx.SepCovered (C1 ∪ C2) := by
  have hs : CapyCaptureSet.CoveredBy
      (CapyCaptureSet.peaks ctx.capyCtx C1) (CapyCaptureSet.peaks ctx.capyCtx C1') := heq.2
  have hcb : CapyCaptureSet.CoveredBy
      (CapyCaptureSet.peaks ctx.capyCtx (C1 ∪ C2))
      (CapyCaptureSet.peaks ctx.capyCtx (C1' ∪ C2)) := by
    rw [CapyCaptureSet.peaks_union, CapyCaptureSet.peaks_union]
    exact CapyCaptureSet.CoveredBy.union_left
      (CapyCaptureSet.CoveredBy.union_right_left hs)
      (CapyCaptureSet.CoveredBy.union_right_right CapyCaptureSet.CoveredBy.refl')
  refine hcov.mono hsub ?_
  intro p _ hmem
  exact covering_build (CapyCaptureSet.peakset ctx.capyCtx (C1 ∪ C2))
    (CapyCaptureSet.peakset ctx.capyCtx (C1' ∪ C2)) hcb p hmem

/-- `applyRO` preserves pseudo-freedom (it only relabels access modes on `cvar`/`var`
    atoms and recurses into content, never introducing a frozen peak). -/
theorem CapyCaptureSet.NoPseudoPeak.applyRO {s : Sig} {C : CapyCaptureSet s}
    (h : C.NoPseudoPeak) : C.applyRO.NoPseudoPeak := by
  induction h with
  | empty => exact CapyCaptureSet.NoPseudoPeak.empty
  | union _ _ ih1 ih2 => exact CapyCaptureSet.NoPseudoPeak.union ih1 ih2
  | cvar => exact CapyCaptureSet.NoPseudoPeak.cvar
  | var => exact CapyCaptureSet.NoPseudoPeak.var

/-- `CoveredBy` transports pseudo-freedom **downward**: if the covering set is
    pseudo-free, so is the covered set (`refl` uses `applyRO`-preservation, and a
    frozen peak of a union is inverted through the covering set's own structure). -/
theorem CapyCaptureSet.CoveredBy.noPseudoPeak_of {s : Sig} {C1 C2 : CapyCaptureSet s}
    (h : C1.CoveredBy C2) (hnp : C2.NoPseudoPeak) : C1.NoPseudoPeak := by
  induction h with
  | refl hm =>
    cases hm with
    | refl => exact hnp
    | ro_eps => exact CapyCaptureSet.NoPseudoPeak.applyRO hnp
  | empty => exact CapyCaptureSet.NoPseudoPeak.empty
  | union_left _ _ ih1 ih2 => exact CapyCaptureSet.NoPseudoPeak.union (ih1 hnp) (ih2 hnp)
  | union_right_left _ ih => cases hnp with | union ha _ => exact ih ha
  | union_right_right _ ih => cases hnp with | union _ hb => exact ih hb

/-- Pseudo-freedom of `peaks Γ C` reflects back to `C`: a `pseudo_peak` in `C`
    surfaces (as a `pseudo_peak` of its resolved content) in `peaks Γ C`, so a
    pseudo-free `peaks Γ C` forces `C` itself to be pseudo-free. -/
theorem CapyCaptureSet.noPseudoPeak_of_peaks {s : Sig} {Γ : CapyCtx s}
    {C : CapyCaptureSet s} (h : (CapyCaptureSet.peaks Γ C).NoPseudoPeak) :
    C.NoPseudoPeak := by
  induction C with
  | empty => exact CapyCaptureSet.NoPseudoPeak.empty
  | union C1 C2 ih1 ih2 =>
    have h' : (CapyCaptureSet.peaks Γ C1 ∪ CapyCaptureSet.peaks Γ C2).NoPseudoPeak := by
      rw [← CapyCaptureSet.peaks_union]; exact h
    cases h' with
    | union ha hb => exact CapyCaptureSet.NoPseudoPeak.union (ih1 ha) (ih2 hb)
  | cvar a c => exact CapyCaptureSet.NoPseudoPeak.cvar
  | var a x => exact CapyCaptureSet.NoPseudoPeak.var
  | pseudo_peak D _ =>
    simp only [CapyCaptureSet.peaks] at h
    cases h

/-- `NoPseudoPeak` transports backwards across `EquivP`: `C1`'s peaks are `CoveredBy`
    `C1'`'s peaks, which are pseudo-free (`C1'` is, and the context introduces none);
    downward-preservation makes `C1`'s peaks pseudo-free, which reflects back to `C1`. -/
theorem CapyCaptureSet.NoPseudoPeak.of_equivP {s : Sig} {Γ : CapyCtx s}
    {C1' C1 : CapyCaptureSet s}
    (hnp : C1'.NoPseudoPeak) (hctx : Γ.NoPseudoPeak)
    (heq : CapyCaptureSet.EquivP Γ C1' C1) :
    C1.NoPseudoPeak := by
  have hcb : CapyCaptureSet.CoveredBy
      (CapyCaptureSet.peaks Γ C1) (CapyCaptureSet.peaks Γ C1') := heq.2
  exact CapyCaptureSet.noPseudoPeak_of_peaks
    (CapyCaptureSet.CoveredBy.noPseudoPeak_of hcb
      (CapyCaptureSet.peaks_noPseudoPeak hctx hnp))

/-- **Source separation checks compile.**  The ambient covering (`SepCovered`)
    at the conclusion operands is what pays for the source's `sep_distinct`
    axiom; everything else is rule-to-rule. -/
theorem CapySepCheck.compile {s1 : Sig} {Γ : CapyCtx s1}
    {C1 C2 : CapyCaptureSet s1} (h : CapySepCheck Γ C1 C2) :
    ∀ {s2 : Sig} (ctx : CompilerCtx s1 s2), ctx.capyCtx = Γ →
      ctx.Coherent → ctx.SubCoherent → ctx.capyCtx.NoPseudoPeak →
      C1.NoPseudoPeak → C2.NoPseudoPeak →
      ctx.SepCovered (C1 ∪ C2) →
      SepCheck ctx.coreCtx (CapyCaptureSet.compile C1 ctx.srcCtx)
        (CapyCaptureSet.compile C2 ctx.srcCtx) := by
  induction h with
  | sep_symm h ih =>
    intro s2 ctx hΓ hcoh hsub hnpp hnp1 hnp2 hcov
    -- conclusion pair (C2, C1); premise pair (C1, C2): union-commute the covering
    exact SepCheck.sep_symm (ih ctx hΓ hcoh hsub hnpp hnp2 hnp1 (hcov.of_subcapt hsub
      (CapySubcapt.sc_union
        (CapySubcapt.sc_elem (CapyCaptureSet.Subset.union_right_right
          CapyCaptureSet.Subset.refl))
        (CapySubcapt.sc_elem (CapyCaptureSet.Subset.union_right_left
          CapyCaptureSet.Subset.refl)))))
  | sep_union h1 h2 ih1 ih2 =>
    intro s2 ctx hΓ hcoh hsub hnpp hnp1 hnp2 hcov
    simp only [CapyCaptureSet.compile]
    cases hnp1 with
    | union hnp1l hnp1r =>
      -- premise pairs (C1, C3), (C2, C3) both under ((C1 ∪ C2) ∪ C3)
      refine SepCheck.sep_union
        (ih1 ctx hΓ hcoh hsub hnpp hnp1l hnp2 (hcov.of_subcapt hsub (CapySubcapt.sc_union
          (CapySubcapt.sc_elem (CapyCaptureSet.Subset.union_right_left
            (CapyCaptureSet.Subset.union_right_left CapyCaptureSet.Subset.refl)))
          (CapySubcapt.sc_elem (CapyCaptureSet.Subset.union_right_right
            CapyCaptureSet.Subset.refl)))))
        (ih2 ctx hΓ hcoh hsub hnpp hnp1r hnp2 (hcov.of_subcapt hsub (CapySubcapt.sc_union
          (CapySubcapt.sc_elem (CapyCaptureSet.Subset.union_right_left
            (CapyCaptureSet.Subset.union_right_right CapyCaptureSet.Subset.refl)))
          (CapySubcapt.sc_elem (CapyCaptureSet.Subset.union_right_right
            CapyCaptureSet.Subset.refl)))))
  | sep_empty =>
    intro s2 ctx hΓ hcoh hsub hnpp hnp1 hnp2 hcov
    simp only [CapyCaptureSet.compile]
    exact SepCheck.sep_empty
  | sep_ro hc1 hc2 hao1 hao2 hk1 hk2 =>
    intro s2 ctx hΓ hcoh hsub hnpp hnp1 hnp2 hcov
    exact SepCheck.sep_ro
      (CapyCaptureSet.compile_isClosed hc1 hcoh.srcClosed)
      (CapyCaptureSet.compile_isClosed hc2 hcoh.srcClosed)
      (CapyCaptureSet.compile_accessOnly hcoh hc1 (hΓ ▸ hao1))
      (CapyCaptureSet.compile_accessOnly hcoh hc2 (hΓ ▸ hao2))
      (CapyHasKind.compile hk1 ctx hΓ hsub)
      (CapyHasKind.compile hk2 ctx hΓ hsub)
  | sep_sc h hsc heq ih =>
    intro s2 ctx hΓ hcoh hsub hnpp hnp1 hnp2 hcov
    -- target `sep_mono` needs no `EquivP`; the source `EquivP` transports the
    -- covering (and pseudo-freedom) to the premise's larger left operand instead
    exact SepCheck.sep_mono
      (ih ctx hΓ hcoh hsub hnpp
        (CapyCaptureSet.NoPseudoPeak.of_equivP hnp1 (hΓ ▸ hnpp) (hΓ ▸ heq)) hnp2
        (hcov.of_equivP_union hsub (hΓ ▸ heq)))
      (CapySubcapt.compile hsc ctx hΓ hsub)
  | sep_distinct hne hp1 hp2 =>
    intro s2 ctx hΓ hcoh hsub hnpp hnp1 hnp2 hcov
    rename_i C1 C2 mu1 mu2
    subst hΓ
    cases hp1 with
    | peak_pseudo =>
      -- a frozen-peak operand contradicts surface pseudo-freedom
      rename_i Cb
      cases mu1 with
      | M m =>
        cases m with
        | epsilon => cases hnp1
        | ro => cases hnp1
      | drop => cases hnp1
    | peak_peak hlk1 =>
      rename_i c1 a1 m1 muA
      cases hp2 with
      | peak_pseudo =>
        rename_i Cb
        cases mu2 with
        | M m =>
          cases m with
          | epsilon => cases hnp2
          | ro => cases hnp2
        | drop => cases hnp2
      | peak_peak hlk2 =>
        rename_i c2 a2 m2 muB
        -- both operands are cvar atoms: `(.cvar muA c1).applyAccess mu1 = .cvar aA c1` etc.
        obtain ⟨aA, hCA⟩ : ∃ a', (CapyCaptureSet.cvar muA c1).applyAccess mu1 =
            .cvar a' c1 := by
          cases mu1 with
          | M m =>
            cases m with
            | epsilon => exact ⟨muA, rfl⟩
            | ro => exact ⟨muA.applyRO, rfl⟩
          | drop => exact ⟨.drop, rfl⟩
        obtain ⟨aB, hCB⟩ : ∃ a', (CapyCaptureSet.cvar muB c2).applyAccess mu2 =
            .cvar a' c2 := by
          cases mu2 with
          | M m =>
            cases m with
            | epsilon => exact ⟨muB, rfl⟩
            | ro => exact ⟨muB.applyRO, rfl⟩
          | drop => exact ⟨.drop, rfl⟩
        rw [hCA, hCB] at hcov ⊢
        by_cases hcc : c1 = c2
        · -- same peak cvar: refuted by the rule's MODE-ERASED distinctness
          -- premise (2026-07-02 strengthening — same-root operands alias)
          simp only [CapyCaptureSet.modeErase] at hne
          exact absurd (by rw [hcc]) hne
        · -- genuinely distinct stable peaks: read the pair off the covering
          set U : CapyCaptureSet _ := .cvar aA c1 ∪ .cvar aB c2 with hU
          have hpeaksU : CapyCaptureSet.peaks ctx.capyCtx U =
              .cvar aA c1 ∪ .cvar aB c2 := by
            simp only [hU, CapyCaptureSet.peaks_union]
            conv_lhs => unfold CapyCaptureSet.peaks
          have hoccA : CapyCaptureSet.Subset (.cvar aA c1)
              (CapyCaptureSet.peakset ctx.capyCtx U).cs := by
            change CapyCaptureSet.Subset _ (CapyCaptureSet.peaks ctx.capyCtx U)
            rw [hpeaksU]
            exact CapyCaptureSet.Subset.union_right_left CapyCaptureSet.Subset.refl
          have hoccB : CapyCaptureSet.Subset (.cvar aB c2)
              (CapyCaptureSet.peakset ctx.capyCtx U).cs := by
            change CapyCaptureSet.Subset _ (CapyCaptureSet.peaks ctx.capyCtx U)
            rw [hpeaksU]
            exact CapyCaptureSet.Subset.union_right_right CapyCaptureSet.Subset.refl
          have hstabA : Peak.IsStable ctx.capyCtx (Peak.cvar c1) :=
            Or.inr ⟨m1, hlk1.eq_lookup.symm⟩
          have hstabB : Peak.IsStable ctx.capyCtx (Peak.cvar c2) :=
            Or.inr ⟨m2, hlk2.eq_lookup.symm⟩
          have memA : Peak.cvar c1 ∈
              (peakList (CapyCaptureSet.peakset ctx.capyCtx U)).filter
                (fun p => decide (Peak.IsStable ctx.capyCtx p)) :=
            List.mem_filter.mpr ⟨PC.cvar_mem_peakList (PC.cvar_mem_peakCvars hoccA),
              decide_eq_true_iff.mpr hstabA⟩
          have memB : Peak.cvar c2 ∈
              (peakList (CapyCaptureSet.peakset ctx.capyCtx U)).filter
                (fun p => decide (Peak.IsStable ctx.capyCtx p)) :=
            List.mem_filter.mpr ⟨PC.cvar_mem_peakList (PC.cvar_mem_peakCvars hoccB),
              decide_eq_true_iff.mpr hstabB⟩
          have hpne : Peak.cvar c1 ≠ Peak.cvar c2 := fun h => hcc (Peak.cvar.inj h)
          have hbase := hcov (Peak.cvar c1) (Peak.cvar c2) memA memB hpne
          simp only [peakKeyItem] at hbase
          have hscA : CapySubcapt ctx.capyCtx (.cvar aA c1)
              (peakItem (CapyCaptureSet.peakset ctx.capyCtx U) c1) :=
            CapySubcapt.sc_elem (PC.cvar_subset_peakItem hoccA)
          have hscB : CapySubcapt ctx.capyCtx (.cvar aB c2)
              (peakItem (CapyCaptureSet.peakset ctx.capyCtx U) c2) :=
            CapySubcapt.sc_elem (PC.cvar_subset_peakItem hoccB)
          exact SepCheck.sep_symm (SepCheck.sep_mono (SepCheck.sep_symm
            (SepCheck.sep_mono hbase (CapySubcapt.compile hscA ctx rfl hsub)))
            (CapySubcapt.compile hscB ctx rfl hsub))

end Compilation
