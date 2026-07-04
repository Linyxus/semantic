import Semantic.CoreCapybara.LegacyCompilation.CompileSubstOpenVar

/-! # `CompileNarrow`: the codomain lock-narrowing recursion (`LHS <: G`).

The app-case codomain bridge factors `hcore_base : LHS <: F` as `LHS <: G <: F`,
where `G <: F` is the honest backward `compile_subst_subtyp.2` and `LHS <: G` is a
pure **lock narrowing**: the compiled codomain body `compile (T2↑ᵢ) ctxLock` at the
EXPECTED-domain context (parameter bound at `T1`) is a subtype of the same body at the
ACTUAL-argument context (parameter bound at `T0y`, with `T0y <: T1[D]`).  The two
compiled types differ ONLY in the `sep` fields of their nested modal locks (the sole
`capyCtx`-reading site of `CapyTy.compile`); the difference is the peak surplus of
`peaks(T1)` over `peaks(T0y)`, discharged — in the UNFAVORABLE `Ψ_big <: Ψ_small`
direction — by the covered backward dispatch fed from the ambient
`SepCovered (D ∪ interfere_set(arrow))` (mode-safe: the surplus items are access-only by
the app rule's `hT1ao`, and the covering pipeline is mode-preserving).

This file builds the pieces bottom-up:
  1. `compile_modal_narrow_node` — the ARROW/POLY/CPOLY NODE: one modal lock narrowing,
     assembled from `Subtyp.modal_modal` (lock swap, fed by
     `compile_peakSepCtx_sep_backward_covered`) + `Subtyp.modal` (body recursion). -/

open CoreCapybara

namespace Compilation

set_option linter.style.longLine false

/-- **Arrow-node lock narrowing (reusable heart).**  A single compiled modal lock is
    narrowed from the substituted ORIGIN lock (keyed by `cs`'s peaks at `Γorig`,
    `σtW`-substituted — the `T1`/EXPECTED side) to the SUB lock (keyed by `cs.subst σ`'s
    peaks at `Γsub` — the `T0y`/ACTUAL side), given:
    * `hcover` — the per-pair covering premise `compile_peakSepCtx_sep_backward_covered`
      consumes (produced downstream by `TgtPairCovered.toHcover` from the ambient
      `SepCovered (D ∪ interfere_set)`);
    * `hkind` — the (usually vacuous: arrows lock an EMPTY mutability) mutability half of
      the swap's `Satisfy`;
    * `hbody` — the body subtyping under the SUB lock (the structural recursion).
    The result is `Subtyp` between the two compiled modals, assembled by
    `trans (modal_modal …) (modal refl hbody)`. -/
theorem compile_modal_narrow_node {s1 s2w s2w' : Sig}
    {Γorig : CapyCtx s1} {scOrig : SrcCtx s1 s2w} {σtW : Subst s2w s2w'}
    {cs : CapyCaptureSet s1} {coreCtxW : Ctx s2w'}
    {ΨmutOrig : MutabilityCtx s2w} {Ψ2 : ModalCtx s2w'}
    {csM : CaptureSet s2w'} {EA EAct : Ty .exi s2w'}
    (hΓcl : coreCtxW.IsClosed)
    (hcsMcl : csM.IsClosed)
    (hΨ1cl : (ModalCtx.subst
        ⟨peakSepCtx Γorig (CapyCaptureSet.peakset Γorig cs) scOrig, ΨmutOrig⟩ σtW).IsClosed)
    (hΨ2cl : Ψ2.IsClosed)
    (hEAcl : EA.IsClosed)
    (hkind : ∀ C m,
        ((ModalCtx.subst ⟨peakSepCtx Γorig (CapyCaptureSet.peakset Γorig cs) scOrig, ΨmutOrig⟩
          σtW).rename Rename.succ).mutability.Has C m →
        HasKind (coreCtxW.push_lock Ψ2) C m)
    (hcover : ∀ (p1 p2 : Peak s1),
        p1 ∈ (peakList (CapyCaptureSet.peakset Γorig cs)).filter
          (fun p => decide (Peak.IsStable Γorig p)) →
        p2 ∈ (peakList (CapyCaptureSet.peakset Γorig cs)).filter
          (fun p => decide (Peak.IsStable Γorig p)) →
        p1 ≠ p2 →
        SepCheck coreCtxW
          ((CapyCaptureSet.compile (peakKeyItem (CapyCaptureSet.peakset Γorig cs) p1) scOrig).subst σtW)
          ((CapyCaptureSet.compile (peakKeyItem (CapyCaptureSet.peakset Γorig cs) p2) scOrig).subst σtW))
    (hbody : Subtyp (coreCtxW.push_lock Ψ2)
        (EA.rename Rename.succ) (EAct.rename Rename.succ)) :
    Subtyp coreCtxW
      (.modal csM
        (ModalCtx.subst ⟨peakSepCtx Γorig (CapyCaptureSet.peakset Γorig cs) scOrig, ΨmutOrig⟩ σtW)
        EA)
      (.modal csM Ψ2 EAct) := by
  refine Subtyp.trans (Ty.IsClosed.modal hcsMcl hΨ2cl hEAcl)
    (Subtyp.modal_modal hΓcl hΨ1cl hΨ2cl ?hsat)
    (Subtyp.modal Subcapt.refl hbody)
  refine Satisfy.satisfy hkind (fun C1 C2 hd => ?_)
  -- The origin lock `Ψ1.rename succ` unfolds (defeq) to `((peakSepCtx …).subst σtW).rename succ`;
  -- the dispatch names a distinct stable origin pair, and `hcover` (weakened past the sub lock)
  -- discharges each — for an ARBITRARY sub lock `Ψ2` (the substituted `T0y` side of the narrowing),
  -- since the sub lock enters only as the `push_lock` weakening target.
  obtain ⟨p1, hp1, p2, hp2, hpne, hPdisj⟩ := peakSepCtx_subst_rename_HasTwoDistinct_ne hd
  rcases hPdisj with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact (hcover p1 p2 hp1 hp2 hpne).renamesTo
      (Ctx.RenamesTo.weaken (Binding.lock Ψ2)) Rename.injective_succ
  · exact (hcover p2 p1 hp2 hp1 (Ne.symm hpne)).renamesTo
      (Ctx.RenamesTo.weaken (Binding.lock Ψ2)) Rename.injective_succ

/-! ## Nested-lock peak inventory (generalizing `appPeaks_*` to arbitrary base captures)

`AppPeaks.lean`'s inventory is specialized to the OUTER function lock (`appWsrc = {εx}↑↑ ∪
{ε param}`, self-capture `{εx}`).  The narrowing recursion meets a nested arrow's lock at
EVERY depth of `T2`, whose key set is `(cs'↑↑) ∪ {ε param}` for the nested arrow's own
capture `cs'` (which may mention the buried outer parameter — the site of the narrowing
surplus).  These additive generalizations parameterize the base capture `B := cs'` and the
self bound `cb`; the outer lemmas are the `B := {εx}`, `cb := .unbound .epsilon` instances. -/

/-- **Generalized arrow-lock peaks unfold** (the `appPeaks_unfold` analog for an arbitrary
    base capture `B` and self bound `cb`).  A wrapped arrow's lock key set `(B↑↑) ∪ {ε param}`
    — self-cvar `c <: cb`, then value parameter at type `T` — has peaks splitting into `B`'s
    peaks (weakened past both binders) and `T.captureSet`'s peaks (weakened past `c`). -/
theorem peaks_arrowLock_unfold {s : Sig} (Γ : CapyCtx s) (cb : CapyCaptureBound s)
    (T : CapyTy .capt (s,C)) (B : CapyCaptureSet s) :
    CapyCaptureSet.peaks ((Γ.push_cvar_default cb).push_var T)
        (((B.rename Rename.succ).rename Rename.succ)
          ∪ CapyCaptureSet.var (.M .epsilon) (.bound .here))
      = (((CapyCaptureSet.peaks Γ B).rename Rename.succ).rename Rename.succ)
        ∪ ((CapyCaptureSet.peaks (Γ.push_cvar_default cb) T.captureSet).rename Rename.succ) := by
  simp only [CapyCtx.push_var, CapyCtx.push_cvar_default, CapyCtx.push_cvar]
  rw [CapyCaptureSet.peaks_union]
  congr 1
  · exact CapyCaptureSet.peaks_double_weaken
  · have h := @CapyCaptureSet.peaksVarBound_here_var (s,C)
      (Γ.push (CapyBinding.cvar .access_only cb)) T (.M .epsilon)
    rw [CapyCaptureSet.applyAccess_M, CapyCaptureSet.applyMut_epsilon] at h
    simp only [CapyCaptureSet.peaks]
    exact h

/-! ### Stage 1 — the embedding lemma family (nested arrow-lock peak classification)

These generalize `AppPeaks.lean`'s `appPeaks_occ_there`/`appPeaks_occ_c`/`appPeaks_item_there`
to an ARBITRARY base capture `B` and self bound `cb` (the outer instances are `B := {εx}`,
`cb := .unbound ε`).  They classify a cvar peak of the nested wrap-lock key set
`(B↑↑) ∪ {ε param}` into a `B`-origin (a weakened `Γ`-cvar `.there (.there c')`) or the
nested self-cvar `c` (`.there .here`, sourced from the param type's capture). -/

/-- **(a) Weakened-`Γ`-cvar descent** (general `appPeaks_occ_there`).  A `.there (.there c')`
    cvar occurrence in the nested wrap-lock key set descends to an occurrence over `Γ` of the
    footprint slice `B ∪ T.captureSet.dropCVar`. -/
theorem peaks_arrowLock_occ_there {s : Sig} {Γ : CapyCtx s} {cb : CapyCaptureBound s}
    {T : CapyTy .capt (s,C)} {B : CapyCaptureSet s} {a : Access} {c' : BVar s .cvar}
    (h : (CapyCaptureSet.cvar a (.there (.there c')))
        ⊆ CapyCaptureSet.peaks ((Γ.push_cvar_default cb).push_var T)
            (((B.rename Rename.succ).rename Rename.succ)
              ∪ CapyCaptureSet.var (.M .epsilon) (.bound .here))) :
    (CapyCaptureSet.cvar a c') ⊆ CapyCaptureSet.peaks Γ (B ∪ T.captureSet.dropCVar) := by
  replace h := peaks_arrowLock_unfold Γ cb T B ▸ h
  rw [CapyCaptureSet.peaks_union]
  rcases CapyCaptureSet.cvar_subset_union_inv h with hA | hB
  · -- base-capture summand: two weakenings peel to `peaks Γ B`
    have hsub := CapyCaptureSet.cvar_there_subset_rename_succ_inv
      (CapyCaptureSet.cvar_there_subset_rename_succ_inv hA)
    exact CapyCaptureSet.Subset.union_right_left hsub
  · -- param-type summand: one weakening then `dropCVar` descent
    have hsub := CapyCaptureSet.cvar_there_subset_rename_succ_inv hB
    have hdrop := CapyCaptureSet.cvar_there_subset_dropCVar hsub
    refine CapyCaptureSet.Subset.union_right_right ?_
    rw [CapyCaptureSet.peaks_dropCVar (a := .access_only) (cb := cb)]
    exact hdrop

/-- **(b) Self-cvar descent** (general `appPeaks_occ_c`).  The nested self-cvar `c`
    (peak `.there .here`) occurs in the wrap-lock key set only from the param type's
    capture annotation. -/
theorem peaks_arrowLock_occ_c {s : Sig} {Γ : CapyCtx s} {cb : CapyCaptureBound s}
    {T : CapyTy .capt (s,C)} {B : CapyCaptureSet s} {a : Access}
    (h : (CapyCaptureSet.cvar a (.there .here))
        ⊆ CapyCaptureSet.peaks ((Γ.push_cvar_default cb).push_var T)
            (((B.rename Rename.succ).rename Rename.succ)
              ∪ CapyCaptureSet.var (.M .epsilon) (.bound .here))) :
    (CapyCaptureSet.cvar a .here)
      ⊆ CapyCaptureSet.peaks (Γ.push_cvar_default cb) T.captureSet := by
  replace h := peaks_arrowLock_unfold Γ cb T B ▸ h
  rcases CapyCaptureSet.cvar_subset_union_inv h with hA | hB
  · have hmid := CapyCaptureSet.cvar_there_subset_rename_succ_inv hA
    obtain ⟨c0, hc0, _⟩ := CapyCaptureSet.cvar_subset_rename_succ_inv hmid
    exact absurd hc0 (by simp)
  · exact CapyCaptureSet.cvar_there_subset_rename_succ_inv hB

/-- **(c) Weakened-`Γ`-cvar item containment** (general `appPeaks_item_there`).  The lock
    item of a `.there (.there c')` peak in the nested wrap-lock is contained in the (doubly
    weakened) lock item of the underlying `c'` over `Γ`'s footprint slice. -/
theorem peaks_arrowLock_item_there {s : Sig} {Γ : CapyCtx s} {cb : CapyCaptureBound s}
    {T : CapyTy .capt (s,C)} {B : CapyCaptureSet s} {c' : BVar s .cvar} :
    CapyCaptureSet.Subset
      (peakItem (CapyCaptureSet.peakset ((Γ.push_cvar_default cb).push_var T)
          (((B.rename Rename.succ).rename Rename.succ)
            ∪ CapyCaptureSet.var (.M .epsilon) (.bound .here))) (.there (.there c')))
      (((peakItem (CapyCaptureSet.peakset Γ (B ∪ T.captureSet.dropCVar)) c').rename
          Rename.succ).rename Rename.succ) := by
  apply peakItem_subset_of
  intro a h
  have h1 := peaks_arrowLock_occ_there h
  have h2 := PC.cvar_subset_peakItem (P := CapyCaptureSet.peakset Γ (B ∪ T.captureSet.dropCVar)) h1
  exact CapyCaptureSet.cvar_subset_rename_fwd (ρ := Rename.succ (k := .var))
    (CapyCaptureSet.cvar_subset_rename_fwd (ρ := Rename.succ (k := .cvar)) h2)

/-- **(d) Stability transport for a weakened `Γ`-cvar peak** (general `appPeaks_stable_there`).
    Stability of a `.there (.there c')` peak in the nested wrap-lock context is exactly the
    stability of `c'` in `Γ` (the two source weakenings preserve stability). -/
theorem peaks_arrowLock_stable_there {s : Sig} {Γ : CapyCtx s} {cb : CapyCaptureBound s}
    {T : CapyTy .capt (s,C)} {c' : BVar s .cvar} :
    Peak.IsStable ((Γ.push_cvar_default cb).push_var T) (Peak.cvar (.there (.there c')))
      ↔ Γ.IsStableCVar c' := by
  have h1 : Peak.IsStable ((Γ.push_cvar_default cb).push_var T) (Peak.cvar (.there (.there c')))
          ↔ Peak.IsStable (Γ.push_cvar_default cb) (Peak.cvar (.there c')) :=
    Peak.IsStable.renamesTo_iff (p := Peak.cvar (.there c'))
      (CapyCtx.RenamesTo.weaken (CapyBinding.var T))
  have h2 : Peak.IsStable (Γ.push_cvar_default cb) (Peak.cvar (.there c'))
          ↔ Peak.IsStable Γ (Peak.cvar c') :=
    Peak.IsStable.renamesTo_iff (p := Peak.cvar c')
      (CapyCtx.RenamesTo.weaken (CapyBinding.cvar .access_only cb))
  exact h1.trans h2

/-- **(e) The nested self-cvar peak is always stable** (general `appPeaks_stable_c`).  Bound
    `.unbound ε` by the wrap, it is a stable peak of the nested wrap-lock context. -/
theorem peaks_arrowLock_stable_c {s : Sig} {Γ : CapyCtx s}
    {T : CapyTy .capt (s,C)} :
    Peak.IsStable ((Γ.push_cvar_default (.unbound .epsilon)).push_var T)
      (Peak.cvar (.there .here)) := by
  have h1 : Peak.IsStable ((Γ.push_cvar_default (.unbound .epsilon)).push_var T)
        (Peak.cvar (.there .here))
      ↔ Peak.IsStable (Γ.push_cvar_default (.unbound .epsilon)) (Peak.cvar .here) :=
    Peak.IsStable.renamesTo_iff (p := Peak.cvar .here)
      (CapyCtx.RenamesTo.weaken (CapyBinding.var T))
  rw [h1]
  change (Γ.push_cvar_default (.unbound .epsilon)).IsStableCVar BVar.here
  exact Or.inr ⟨.epsilon, rfl⟩

/-- **(f) The nested wrap-lock has no frozen (pseudo) peaks** (general `appPeaks_noPseudo`). -/
theorem peaks_arrowLock_noPseudo {s : Sig} {Γ : CapyCtx s} {cb : CapyCaptureBound s}
    {T : CapyTy .capt (s,C)} {B : CapyCaptureSet s}
    (hΓ : Γ.NoPseudoPeak) (hT : T.NoPseudoPeak) (hB : B.NoPseudoPeak) :
    peakPseudos (CapyCaptureSet.peakset ((Γ.push_cvar_default cb).push_var T)
        (((B.rename Rename.succ).rename Rename.succ)
          ∪ CapyCaptureSet.var (.M .epsilon) (.bound .here))) = [] := by
  have hΓLnp : ((Γ.push_cvar_default cb).push_var T).NoPseudoPeak := ⟨hΓ, hT.captureSet⟩
  have hpeaks : (CapyCaptureSet.peaks ((Γ.push_cvar_default cb).push_var T)
      (((B.rename Rename.succ).rename Rename.succ)
        ∪ CapyCaptureSet.var (.M .epsilon) (.bound .here))).NoPseudoPeak :=
    CapyCaptureSet.peaks_noPseudoPeak hΓLnp
      (CapyCaptureSet.NoPseudoPeak.union
        ((hB.rename Rename.succ).rename Rename.succ) CapyCaptureSet.NoPseudoPeak.var)
  simp only [peakPseudos, CapyCaptureSet.peakset,
    PC.peakPseudos_go_nil_of_noPseudoPeak hpeaks, dedup]

/-- **(g) Stable-peak inventory of the nested wrap-lock** (general `appPeaks_mem_inventory`).
    Each stable peak of the nested wrap-lock is either the self-cvar `c` (`.there .here`) or a
    weakened `Γ`-cvar (`.there (.there c')`) whose `c'` is a stable footprint-slice peak. -/
theorem peaks_arrowLock_mem_inventory {s : Sig} {Γ : CapyCtx s} {cb : CapyCaptureBound s}
    {T : CapyTy .capt (s,C)} {B : CapyCaptureSet s}
    (hΓ : Γ.NoPseudoPeak) (hT : T.NoPseudoPeak) (hB : B.NoPseudoPeak)
    {p : Peak ((s,C),x)}
    (hp : p ∈ (peakList (CapyCaptureSet.peakset ((Γ.push_cvar_default cb).push_var T)
        (((B.rename Rename.succ).rename Rename.succ)
          ∪ CapyCaptureSet.var (.M .epsilon) (.bound .here)))).filter
        (fun q => decide (Peak.IsStable ((Γ.push_cvar_default cb).push_var T) q))) :
    p = Peak.cvar (.there .here) ∨
    ∃ c' : BVar s .cvar, p = Peak.cvar (.there (.there c')) ∧ Γ.IsStableCVar c' ∧
      Peak.cvar c' ∈ (peakList (CapyCaptureSet.peakset Γ (B ∪ T.captureSet.dropCVar))).filter
        (fun q => decide (Peak.IsStable Γ q)) := by
  rw [List.mem_filter] at hp
  obtain ⟨hmem, hstab⟩ := hp
  have hstab' : Peak.IsStable ((Γ.push_cvar_default cb).push_var T) p := of_decide_eq_true hstab
  have hpseudo := peaks_arrowLock_noPseudo (Γ := Γ) (cb := cb) (T := T) (B := B) hΓ hT hB
  simp only [peakList, hpseudo, List.map_nil, List.append_nil, List.mem_map] at hmem
  obtain ⟨d, hd, hpd⟩ := hmem
  subst hpd
  rcases appPeaks_cvar_shape d with hshape | ⟨c', hshape⟩
  · exact Or.inl (congrArg Peak.cvar hshape)
  · subst hshape
    refine Or.inr ⟨c', rfl, ?_, ?_⟩
    · exact (peaks_arrowLock_stable_there (Γ := Γ) (cb := cb) (T := T)).mp hstab'
    · have hΓstab : Γ.IsStableCVar c' :=
        (peaks_arrowLock_stable_there (Γ := Γ) (cb := cb) (T := T)).mp hstab'
      obtain ⟨a, hocc⟩ := PC.peakCvars_occ hd
      have hoccU := peaks_arrowLock_occ_there (Γ := Γ) (cb := cb) (T := T) (B := B) hocc
      have hcmem := PC.cvar_mem_peakCvars
        (P := CapyCaptureSet.peakset Γ (B ∪ T.captureSet.dropCVar)) hoccU
      refine List.mem_filter.mpr ⟨PC.cvar_mem_peakList hcmem, ?_⟩
      exact decide_eq_true_eq.mpr hΓstab

/-- **(h) Self-cvar item atoms** (general `appPeaks_item_c_atoms`).  Every cvar atom of the
    self-cvar peak's lock item is the self-cvar `c` (`.there .here`), whose occurrence
    descends to the param type's capture. -/
theorem peaks_arrowLock_item_c_atoms {s : Sig} {Γ : CapyCtx s} {cb : CapyCaptureBound s}
    {T : CapyTy .capt (s,C)} {B : CapyCaptureSet s} {a : Access} {d : BVar ((s,C),x) .cvar}
    (h : (CapyCaptureSet.cvar a d)
        ⊆ peakItem (CapyCaptureSet.peakset ((Γ.push_cvar_default cb).push_var T)
            (((B.rename Rename.succ).rename Rename.succ)
              ∪ CapyCaptureSet.var (.M .epsilon) (.bound .here))) (.there .here)) :
    d = .there .here
      ∧ (CapyCaptureSet.cvar a .here)
          ⊆ CapyCaptureSet.peaks (Γ.push_cvar_default cb) T.captureSet := by
  obtain ⟨hd, hocc⟩ := cvar_subset_peakItem_inv h
  exact ⟨hd, peaks_arrowLock_occ_c (B := B) hocc⟩

/-- **(i) The self-cvar never occurs at `.drop` mode** (general `appPeaks_c_no_drop`).  When
    the param type's capture is access-only, the self-cvar's occurrence mode is non-`.drop`
    (via the `peaks`→`resourcePeaks` bridge). -/
theorem peaks_arrowLock_c_no_drop {s : Sig} {Γ : CapyCtx s} {cb : CapyCaptureBound s}
    {T : CapyTy .capt (s,C)}
    (hao : CapyCaptureSet.AccessOnly (Γ.push_cvar_default cb) T.captureSet) {a : Access}
    (h : (CapyCaptureSet.cvar a .here)
        ⊆ CapyCaptureSet.peaks (Γ.push_cvar_default cb) T.captureSet) :
    a ≠ .drop := by
  intro ha
  subst ha
  exact hao BVar.here
    (CapyCaptureSet.cvar_peaks_subset_resourcePeaks (Γ.push_cvar_default cb) T.captureSet h)

/-! ## Stage 2 — the arrow-lock narrowing heart (covering + abstract self-separation) -/

/-- **Arrow-lock narrowing with the covering pipeline wired in.**  A single arrow's compiled
    modal lock is narrowed (origin/`T1` side ↦ arbitrary sub/`T0y` side) using an ambient
    covering datum `hCov : TgtPairCovered Q …` for the coverable (closure) peaks plus one
    abstract self-separation hypothesis `hself` for the residual pairs that no covering or
    lock reaches.  The two are combined by `hcover_arrow_of_covered` into the per-pair
    `hcover` that `compile_modal_narrow_node` consumes.

    **`hself` is a KNOWN-GAP threaded hypothesis, not a proof obligation of this file.** For two
    distinct stable origin peaks with at least one OUTSIDE the covering scope `Q` (i.e. involving
    this arrow's fresh access-only self-cvar), it asks a target `SepCheck` between their compiled,
    `σtW`-substituted key items in the BARE `coreCtxW` — where no lock witnesses the pair and the
    cvar carries no droppable authority.  It shares its shape with `app_capture_self_sep_modepoly`
    (CompileSubstOpenVar.lean:963).

    ⚠ It currently has NO in-model discharge story.  The "compiled-roots distinctness" route
    (which would have separated a fresh access-only root from ANY distinct peak, closing this and
    963 uniformly) was REFUTED as UNSOUND: the target model deliberately permits distinct
    access-only cvars to ro-alias (the purpose of `sep_ro`), and `EnvSepWf` disjointness is
    `.can_drop`-only, so no source fact backs uniform disjointness.  The live candidates —
    O1 (drop-denotation refinement, closes only `.drop`-moded phantom pairs) and candidate B
    (droppable premise) — do NOT touch `hself`; only O3 (intensional locks, under which lock
    footprints stop resolving through stored types, so the `T1`/`T0y` locks become syntactically
    identical) would make the whole narrowing surplus + this obligation DISSOLVE rather than be
    discharged.  Pending the user's O1/O3/B ruling, `hself` is threaded (like the ambient
    covering) to the `Preservation.lean:1166` wiring and pinned there. -/
theorem compile_arrowLock_narrow {sc scov s1 s2w s2w' : Sig}
    {Q : Peak s1 → Prop}
    {ctxCov : CompilerCtx sc scov} {U : CapyCaptureSet sc}
    {Γorig : CapyCtx s1} {scOrig : SrcCtx s1 s2w} {σtW : Subst s2w s2w'}
    {cs : CapyCaptureSet s1} {coreCtxW : Ctx s2w'}
    {ΨmutOrig : MutabilityCtx s2w} {Ψ2 : ModalCtx s2w'}
    {csM : CaptureSet s2w'} {EA EAct : Ty .exi s2w'}
    (hΓcl : coreCtxW.IsClosed)
    (hcsMcl : csM.IsClosed)
    (hΨ1cl : (ModalCtx.subst
        ⟨peakSepCtx Γorig (CapyCaptureSet.peakset Γorig cs) scOrig, ΨmutOrig⟩ σtW).IsClosed)
    (hΨ2cl : Ψ2.IsClosed)
    (hEAcl : EA.IsClosed)
    (hkind : ∀ C m,
        ((ModalCtx.subst ⟨peakSepCtx Γorig (CapyCaptureSet.peakset Γorig cs) scOrig, ΨmutOrig⟩
          σtW).rename Rename.succ).mutability.Has C m →
        HasKind (coreCtxW.push_lock Ψ2) C m)
    (hCov : TgtPairCovered Q ctxCov U Γorig scOrig cs coreCtxW σtW)
    (hself : ∀ (p1 p2 : Peak s1),
        p1 ∈ (peakList (CapyCaptureSet.peakset Γorig cs)).filter
          (fun p => decide (Peak.IsStable Γorig p)) →
        p2 ∈ (peakList (CapyCaptureSet.peakset Γorig cs)).filter
          (fun p => decide (Peak.IsStable Γorig p)) →
        p1 ≠ p2 →
        (¬ Q p1 ∨ ¬ Q p2) →
        SepCheck coreCtxW
          ((CapyCaptureSet.compile (peakKeyItem (CapyCaptureSet.peakset Γorig cs) p1) scOrig).subst σtW)
          ((CapyCaptureSet.compile (peakKeyItem (CapyCaptureSet.peakset Γorig cs) p2) scOrig).subst σtW))
    (hbody : Subtyp (coreCtxW.push_lock Ψ2)
        (EA.rename Rename.succ) (EAct.rename Rename.succ)) :
    Subtyp coreCtxW
      (.modal csM
        (ModalCtx.subst ⟨peakSepCtx Γorig (CapyCaptureSet.peakset Γorig cs) scOrig, ΨmutOrig⟩ σtW)
        EA)
      (.modal csM Ψ2 EAct) :=
  compile_modal_narrow_node hΓcl hcsMcl hΨ1cl hΨ2cl hEAcl hkind
    (hcover_arrow_of_covered hCov hself) hbody

end Compilation
