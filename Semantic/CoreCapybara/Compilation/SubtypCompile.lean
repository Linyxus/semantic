import Semantic.CoreCapybara.Compilation.Coherence
import Semantic.CoreCapybara.Compilation.CoherenceMorphism
import Semantic.CoreCapybara.Compilation.SubstLemmas
import Semantic.CoreCapybara.Compilation.LockKernel
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
  -- ★★ FUNDAMENTAL GAP (verified 2026-06-28) — needs a human design decision. ★★
  --
  -- This is UNDERIVABLE, and not merely "infrastructure not yet built".  Concrete
  -- counterexample (all pieces source-derivable):
  --   Γ = …, d:[*]<:_, c₁:[access_only]<:.bound {d}, c₂:[access_only]<:.bound {d}
  --   cs1 = {c₁,c₂},  cs2 = {d}.
  --   `CapySubcapt Γ {c₁,c₂} {d}` holds  (sc_cvar c₁, sc_cvar c₂, sc_union).
  --   ⇒ `CapySubtyp Γ (.cpoly cb1 {c₁,c₂} T1) (.cpoly cb2 {d} T2)` is derivable.
  -- Compiled locks:  Ψ1 = peakSepCtx{c₁,c₂}  (TWO items ⟦c₁⟧,⟦c₂⟧ — must separate);
  --                  Ψ2 = peakSepCtx{d}      (ONE item ⟦d⟧).
  -- The `modal_modal` premise becomes  `SepCheck (Γt.push_lock Ψ2) ⟦c₁⟧ ⟦c₂⟧`, with
  -- NO applicable rule:  sep_lock — c₁,c₂ are not two distinct items of Ψ2 (only d);
  --   sep_droppable — c₁,c₂ are `access_only`, not `can_drop`;  sep_mono — {c₁},{c₂}<:{d}
  --   collapses both sides to d⊥d (false);  sep_ro — bodies captured at `.epsilon`, not ro.
  --
  -- ROOT CAUSE.  The compiler stamps the lock Ψ1 = peakSepCtx(peaks cs1) onto every
  -- function type, INJECTING the assumption "all of cs1's peaks pairwise separate"
  -- (target `wrap` PUSHES Ψ1 for the body; `unwrap` discharges it).  But the SOURCE
  -- never establishes this: `abs`/`tabs`/`cabs` (Capybara/TypeSystem/Core.lean:247-266)
  -- do NOT sep-check captures — source separation is a USE-site check (`app`:272,
  -- `par`:348).  So there is NO source well-formedness to thread (the earlier
  -- "thread source separation" plan is unworkable — the invariant does not exist),
  -- and `sc_cvar` legitimately merges two distinct cs1-peaks into one cs2-bound,
  -- destroying the separation Ψ1 demands.
  --
  -- FIX is a DESIGN choice (human): (a) weaken the compiled function-type lock so it
  -- only records separations stable under subcapturing; or (b) add capture sep-checking
  -- to source `abs`/`tabs`/`cabs` so Ψ1 is justified and threadable; or (c) change the
  -- modal-lock subtyping discipline.  `fresh` does NOT hit this — it routes through B2c
  -- (`compile_subst_subtyp`), whose split peaks come from a DROPPABLE `D`, separated by
  -- `sep_droppable`.  See `notes/fresh-roadmap.md` ("FUNDAMENTAL GAP").
  | arrow _ _ _ ih1 ih3 =>
    intro s2 ctx hΓ hcoh hA hB
    sorry
  | poly _ _ _ ih1 ih3 =>
    intro s2 ctx hΓ hcoh hA hB
    sorry
  | cpoly _ _ _ ih3 =>
    intro s2 ctx hΓ hcoh hA hB
    sorry

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

/-- **(A2, LOCK view) A target cvar atom of a compiled `PeaksOnly` set comes from a
    source cvar** (with the same access mode, mapped by `lookupCVar`).  This is the
    LOCK-side tracer used by the B2c separation dispatch (`OpenCVarSubtyp` `1187`/
    `1249`), where the input `peaks Γ cs` CAN contain frozen peaks.  The `pseudo_peak`
    case is the documented Step-2 lock gap: a target cvar inside `⟦pseudo_peak C⟧`
    is NOT a separate lock peak, so it has no source-cvar witness via opaque `Subset`.
    The RESOURCE callers use the sorry-free `compile_cvar_subset_inv_resource` instead. -/
theorem CapyCaptureSet.compile_cvar_subset_inv {s1 s2 : Sig} {cs : CapyCaptureSet s1}
    (hpo : cs.PeaksOnly) {sc : SrcCtx s1 s2} :
    ∀ {a : Access} {c' : BVar s2 .cvar},
      CaptureSet.Subset (.cvar a c') (CapyCaptureSet.compile cs sc) →
      ∃ c, sc.lookupCVar c = c' ∧ CapyCaptureSet.Subset (.cvar a c) cs := by
  induction hpo with
  | empty =>
    intro a c' h
    simp only [CapyCaptureSet.compile] at h
    cases h
  | cvar =>
    intro a c' h
    simp only [CapyCaptureSet.compile] at h
    cases h
    exact ⟨_, rfl, CapyCaptureSet.Subset.refl⟩
  | union _ _ ih1 ih2 =>
    intro a c' h
    simp only [CapyCaptureSet.compile] at h
    cases h with
    | union_right_left h1 =>
      obtain ⟨c, hc, hsub⟩ := ih1 h1
      exact ⟨c, hc, CapyCaptureSet.Subset.union_right_left hsub⟩
    | union_right_right h2 =>
      obtain ⟨c, hc, hsub⟩ := ih2 h2
      exact ⟨c, hc, CapyCaptureSet.Subset.union_right_right hsub⟩
  -- ★ STEP-2 LOCK GAP.  A target cvar of `⟦pseudo_peak C⟧ = ⟦C⟧` is a cvar of the
  -- frozen peak's CONTENT, not a separate lock peak — so it has no source-cvar
  -- witness `cvar a c ⊆ pseudo_peak C` under opaque `Subset`.  Closing this is the
  -- Step-2 lock half: make `peakSepCtx`/`peakCvars` key the lock by PEAK (cvar ⊔
  -- pseudo_peak) so a frozen peak is one item, and trace target cvars accordingly.
  -- (The RESOURCE view is already decoupled: `compile_cvar_subset_inv_resource`.)
  | pseudo_peak =>
    intro a c' h
    simp only [CapyCaptureSet.compile] at h
    sorry
/-- **(A2, resource view)** Like `compile_cvar_subset_inv`, but for a `NoPseudoPeak`
    set, where it is SORRY-FREE: a target cvar atom of `⟦cs⟧` traces to a source cvar
    of `cs`.  The frozen-peak case (the Step-2 lock gap that keeps
    `compile_cvar_subset_inv` open) cannot arise here. -/
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
