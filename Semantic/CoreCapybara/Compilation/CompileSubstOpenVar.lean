import Semantic.CoreCapybara.Compilation.OpenCVarSubtyp
import Semantic.CoreCapybara.Compilation.SepCovered
import Semantic.CoreCapybara.Compilation.AppSatisfy

/-! # `CompileSubstOpenVar`: the covered backward lock-`Satisfy` dispatch.

The codomain bridge of the compiled application needs the backward direction of
`CapyTy.compile_subst_subtyp` (`(compile T ctxOrig).subst σt <: compile (T.subst σ) ctxSub`)
at `σ = openVar y`, where the redirected value parameter `p ↦ y` carries only the
subsumption slack `T0y <: T1[openCVar D]` (not the exact `SubstsTo.var` capture equation
`compile_subst_subtyp` demands).

The K1 lock-*merge* instability that the old `compile_peakSepCtx_sep_backward` comment
warns about is RESOLVED (stable-peak locks ⇒ `subPeakOf_inj`, no merge).  The genuine
residue is a peak *surplus*: the ORIGIN lock is keyed by the faithful (`Γorig`) parameter
type `T1` (the EXPECTED, larger peak set), while the SUB lock is keyed by the argument's
ACTUAL smaller type `T0y`, so a `HasTwoDistinct` of the substituted-origin lock can name an
expected peak with no sub-image.  The ambient covering `SepCovered U` (over `U ⊇` the
expected peaks — the same covering `app_satisfy_bridge` uses) supplies the missing
separations.

`compile_peakSepCtx_sep_backward_covered` is the DISPATCH core: it reduces the
substituted-origin lock's `HasTwoDistinct` to a distinct *stable origin peak* pair and
discharges it from a per-pair covering premise (already transported to `coreCtxW` through
`σtW`).  Establishing that premise from a literal `SepCovered` is the `app_satisfy_bridge`-
style transport, done at the wiring site. -/

open CoreCapybara

namespace Compilation

set_option linter.style.longLine false

/-- **Covered backward lock-`Satisfy` separation half (dispatch core).**
    From a `HasTwoDistinct` of the substituted-origin lock (renamed under the pushed lock
    binder), derive the required `SepCheck` in the SUB-lock context — using a per-pair
    covering premise `hcover` that separates the compiled, `σtW`-substituted key items of
    any two distinct stable ORIGIN peaks.  The peak surplus (expected-vs-actual) is
    invisible here: `peakSepCtx_subst_rename_HasTwoDistinct_ne` already names a distinct
    stable origin pair, and `hcover` covers *all* such pairs (the covering ranges over the
    expected/larger peak set). -/
theorem compile_peakSepCtx_sep_backward_covered {s1 s2w s1' s2w' : Sig}
    {Γorig : CapyCtx s1} {Γsub : CapyCtx s1'}
    {scOrig : SrcCtx s1 s2w} {scSub : SrcCtx s1' s2w'}
    {σ : CapySubst s1 s1'} {σtW : Subst s2w s2w'}
    {cs : CapyCaptureSet s1} {coreCtxW : Ctx s2w'} {ΨmutSub : MutabilityCtx s2w'}
    (hcover : ∀ (p1 p2 : Peak s1),
        p1 ∈ (peakList (CapyCaptureSet.peakset Γorig cs)).filter
          (fun p => decide (Peak.IsStable Γorig p)) →
        p2 ∈ (peakList (CapyCaptureSet.peakset Γorig cs)).filter
          (fun p => decide (Peak.IsStable Γorig p)) →
        p1 ≠ p2 →
        SepCheck coreCtxW
          ((CapyCaptureSet.compile (peakKeyItem (CapyCaptureSet.peakset Γorig cs) p1) scOrig).subst σtW)
          ((CapyCaptureSet.compile (peakKeyItem (CapyCaptureSet.peakset Γorig cs) p2) scOrig).subst σtW)) :
    ∀ (C1 C2 : CaptureSet (s2w',,Kind.lock)),
      (((peakSepCtx Γorig (CapyCaptureSet.peakset Γorig cs) scOrig).subst σtW).rename
        Rename.succ).HasTwoDistinct C1 C2 →
      SepCheck
        (coreCtxW.push_lock
          ({ sep := peakSepCtx Γsub (CapyCaptureSet.peakset Γsub (cs.subst σ)) scSub,
             mutability := ΨmutSub } : ModalCtx s2w'))
        C1 C2 := by
  intro C1 C2 hdist
  obtain ⟨p1, hp1, p2, hp2, hpne, hPdisj⟩ := peakSepCtx_subst_rename_HasTwoDistinct_ne hdist
  rcases hPdisj with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact (hcover p1 p2 hp1 hp2 hpne).renamesTo
      (Ctx.RenamesTo.weaken (Binding.lock _)) Rename.injective_succ
  · exact (hcover p2 p1 hp2 hp1 (Ne.symm hpne)).renamesTo
      (Ctx.RenamesTo.weaken (Binding.lock _)) Rename.injective_succ

/-- The `openVar` peak map: a var-opening freezes NO cvar (the top binder is a var),
    so every cvar maps to itself.  Twin of `openCVarToPeak` with an empty frozen set. -/
def openVarToPeak {s : Sig} : BVar (s,x) .cvar → Peak s
| .there c0 => Peak.cvar c0

/-- The `PeakSubstIso` for a value-variable opening: trivial on cvars (no frozen
    peaks), so `inj`/`uniqueFrozen` are immediate.  Needed as the var-opening
    factor of the codomain's composite `σ = (openVar y) ∘ (openCVar D)`. -/
def PeakSubstIso.openVar {s : Sig} (z : Var .var s) :
    PeakSubstIso (CapySubst.openVar z) where
  toPeak := openVarToPeak
  image := by intro c; cases c with | there x => rfl
  inj := by
    intro c1 c2 h12
    cases c1 with
    | there x1 =>
      cases c2 with
      | there x2 =>
        simp only [openVarToPeak, Peak.cvar.injEq] at h12
        exact congrArg BVar.there h12
  uniqueFrozen := by
    intro c1 c2 D1 D2 h1 h2
    cases c1 with
    | there x1 => simp only [openVarToPeak] at h1; exact absurd h1 (by simp)

/-- The var-opening iso freezes no cvar, so it is `CvarOnly` — exactly the side
    condition `PeakSubstIso.comp` needs on its right (`σ2 = openVar y`) factor for
    the codomain composite `σ = (openCVar D).lift ∘ (openVar y)`. -/
theorem PeakSubstIso.openVar_cvarOnly {s : Sig} (z : Var .var s) :
    (PeakSubstIso.openVar z).CvarOnly :=
  fun c => by cases c with | there x => exact ⟨x, rfl⟩

/-- Stability-preservation of the var-opening iso: pushing a value binder and then
    opening it leaves every (necessarily `.there`) cvar's stability unchanged (the
    var binder never touches cvar stability).  The `openVar` factor of the codomain
    composite's `StablePreserving`. -/
theorem PeakSubstIso.StablePreserving.openVar {s : Sig} {Γ : CapyCtx s}
    {T : CapyTy .capt s} {z : Var .var s} :
    (PeakSubstIso.openVar z).StablePreserving (Γ.push_var T) Γ := by
  intro c
  cases c with
  | there c0 =>
    simp only [PeakSubstIso.openVar, openVarToPeak, Peak.IsStable]
    exact CapyCtx.IsStableCVar.renamesTo_iff (CapyCtx.RenamesTo.weaken (CapyBinding.var T))

/-- **Covered forward lock-`Satisfy` separation half (dispatch core).**  The forward
    analog of `compile_peakSepCtx_sep_backward_covered`, and the covered twin of
    `compile_peakSepCtx_sep_forward`: same signature, but its distinct-stable-peak
    obligation is discharged by an ambient per-pair COVERING premise `hcover`
    (distinct stable ORIGIN peaks ⇒ their compiled `σtW`-substituted key items separate
    at `coreCtxW`) rather than the (unsound-to-require) droppability `TgtPairDroppableOn`.

    Structurally this mirrors `compile_peakSepCtx_sep_forward`, but the cvar–cvar key
    (`keyCC`) is rebuilt at the *item* level like `keyCP`: two distinct stable cvar
    sub-peaks map to two DISTINCT stable ORIGIN cvar peaks via the source-level preimage
    `sub_cvar_peak_origin` (injective through `hiso`), so there is no target-atom "split"
    to pay by droppability — `hcover` separates the two origin key items directly and each
    sub item shrinks in via `peakItem_subst_supset`.  The cvar–pseudo and pseudo–pseudo
    cases are IDENTICAL to the non-covered forward (they already read the pushed origin
    lock via `sep_lock`, never droppability). -/
theorem compile_peakSepCtx_sep_forward_covered {s1 s2w s1' s2w' : Sig}
    {Γorig : CapyCtx s1} {Γsub : CapyCtx s1'}
    {scOrig : SrcCtx s1 s2w} {scSub : SrcCtx s1' s2w'}
    {σ : CapySubst s1 s1'} {σtW : Subst s2w s2w'}
    {cs : CapyCaptureSet s1} {coreCtxW : Ctx s2w'} {ΨmutR : MutabilityCtx s2w}
    (_hΓO : Γorig.IsClosed) (hΓS : Γsub.IsClosed)
    (_haOrigW : SrcAligned Γorig scOrig) (haSubW : SrcAligned Γsub scSub)
    (hcompatW : SubstCompat scSub scOrig σ σtW)
    (_hcsCl : cs.IsClosed) (_hsubcl : (cs.subst σ).IsClosed)
    (hΓOnp : Γorig.NoPseudoPeak) (hcsnp : cs.NoPseudoPeak)
    (_hinjW : scSub.CVarInjective)
    (hiso : PeakSubstIso σ)
    (hscS : CapySubst.IsClosed σ)
    (htv' : ∀ X, ∃ Y, σ.tvar X = CapyPureTy.tvar Y)
    (hsubsto : Γorig.SubstsTo Γsub σ)
    (hcover : ∀ (p1 p2 : Peak s1),
        p1 ∈ (peakList (CapyCaptureSet.peakset Γorig cs)).filter
          (fun p => decide (Peak.IsStable Γorig p)) →
        p2 ∈ (peakList (CapyCaptureSet.peakset Γorig cs)).filter
          (fun p => decide (Peak.IsStable Γorig p)) →
        p1 ≠ p2 →
        SepCheck coreCtxW
          ((CapyCaptureSet.compile (peakKeyItem (CapyCaptureSet.peakset Γorig cs) p1) scOrig).subst σtW)
          ((CapyCaptureSet.compile (peakKeyItem (CapyCaptureSet.peakset Γorig cs) p2) scOrig).subst σtW))
    (hstab : hiso.StablePreserving Γorig Γsub) :
    ∀ (C1 C2 : CaptureSet (s2w',,Kind.lock)),
      (peakSepCtx Γsub (CapyCaptureSet.peakset Γsub (cs.subst σ))
        (scSub.rename Rename.succ)).HasTwoDistinct C1 C2 →
      SepCheck
        (coreCtxW.push_lock
          (({ sep := peakSepCtx Γorig (CapyCaptureSet.peakset Γorig cs) scOrig,
              mutability := ΨmutR } : ModalCtx s2w).subst σtW))
        C1 C2 := by
  intro C1 C2 hdist
  obtain ⟨c1, hc1, c2, hc2, hcne, hCdisj⟩ := peakSepCtx_HasTwoDistinct_ne hdist
  -- The COVERED cvar–cvar key: distinct stable cvar sub-peaks map (source-level, injective)
  -- to distinct stable ORIGIN cvar peaks, separated directly by `hcover`; each sub item
  -- shrinks into its σtW-substituted origin item.  No droppability, no atom "split".
  have keyCC : ∀ (d1 d2 : BVar s1' Kind.cvar), d1 ≠ d2 →
      Γsub.IsStableCVar d1 → Γsub.IsStableCVar d2 →
      d1 ∈ peakCvars (CapyCaptureSet.peakset Γsub (cs.subst σ)) →
      d2 ∈ peakCvars (CapyCaptureSet.peakset Γsub (cs.subst σ)) →
      SepCheck
        (coreCtxW.push_lock
          (({ sep := peakSepCtx Γorig (CapyCaptureSet.peakset Γorig cs) scOrig,
              mutability := ΨmutR } : ModalCtx s2w).subst σtW))
        (CapyCaptureSet.compile
          (peakItem (CapyCaptureSet.peakset Γsub (cs.subst σ)) d1)
          (scSub.rename Rename.succ))
        (CapyCaptureSet.compile
          (peakItem (CapyCaptureSet.peakset Γsub (cs.subst σ)) d2)
          (scSub.rename Rename.succ)) := by
    intro d1 d2 hne hd1stab hd2stab hd1 hd2
    obtain ⟨c01, hc01, hc01pc⟩ := sub_cvar_peak_origin hiso hsubsto htv' hd1
    obtain ⟨c02, hc02, hc02pc⟩ := sub_cvar_peak_origin hiso hsubsto htv' hd2
    have hne01 : c01 ≠ c02 := by
      intro he
      apply hne
      have h := hc01
      rw [he, hc02] at h
      exact (CapyCaptureSet.cvar.inj h).2.symm
    have hc01stab : Γorig.IsStableCVar c01 :=
      (hstab c01).mpr (by rw [hiso.toPeak_eq_cvar_of_image hc01]; exact hd1stab)
    have hc02stab : Γorig.IsStableCVar c02 :=
      (hstab c02).mpr (by rw [hiso.toPeak_eq_cvar_of_image hc02]; exact hd2stab)
    have hsep := hcover (Peak.cvar c01) (Peak.cvar c02)
      (List.mem_filter.mpr ⟨cvar_mem_peakList hc01pc, decide_eq_true_iff.mpr hc01stab⟩)
      (List.mem_filter.mpr ⟨cvar_mem_peakList hc02pc, decide_eq_true_iff.mpr hc02stab⟩)
      (fun h => hne01 (Peak.cvar.inj h))
    simp only [peakKeyItem] at hsep
    refine SepCheck.sep_symm (SepCheck.sep_mono (SepCheck.sep_symm (SepCheck.sep_mono
      (hsep.renamesTo (Ctx.RenamesTo.weaken (Binding.lock _)) Rename.injective_succ) ?_)) ?_)
    · apply Subcapt.sc_elem
      rw [CapyCaptureSet.compile_rename]
      exact CaptureSet.Subset.rename (f := Rename.succ)
        (peakItem_subst_supset hcompatW hiso htv' hsubsto hc01)
    · apply Subcapt.sc_elem
      rw [CapyCaptureSet.compile_rename]
      exact CaptureSet.Subset.rename (f := Rename.succ)
        (peakItem_subst_supset hcompatW hiso htv' hsubsto hc02)
  -- CVAR–FROZEN key: IDENTICAL to `compile_peakSepCtx_sep_forward` (reads the pushed origin
  -- lock via `sep_lock`; never droppability).
  have keyCP : ∀ (d1 : BVar s1' Kind.cvar) (D2 : CapyCaptureSet s1'),
      Γsub.IsStableCVar d1 →
      d1 ∈ peakCvars (CapyCaptureSet.peakset Γsub (cs.subst σ)) →
      D2 ∈ peakPseudos (CapyCaptureSet.peakset Γsub (cs.subst σ)) →
      SepCheck
        (coreCtxW.push_lock
          (({ sep := peakSepCtx Γorig (CapyCaptureSet.peakset Γorig cs) scOrig,
              mutability := ΨmutR } : ModalCtx s2w).subst σtW))
        (CapyCaptureSet.compile
          (peakItem (CapyCaptureSet.peakset Γsub (cs.subst σ)) d1)
          (scSub.rename Rename.succ))
        (CapyCaptureSet.compile
          (pseudoItem (CapyCaptureSet.peakset Γsub (cs.subst σ)) D2)
          (scSub.rename Rename.succ)) := by
    intro d1 D2 hd1stab hd1m hD2m
    obtain ⟨c01, hc01, hc01pc⟩ := sub_cvar_peak_origin hiso hsubsto htv' hd1m
    obtain ⟨c02, D02, hc02, hD2eq, hc02pc⟩ :=
      sub_pseudo_peak_origin hiso hsubsto hΓOnp hcsnp hD2m
    have hne01 : c01 ≠ c02 := by
      intro he; rw [he, hc02] at hc01; simp at hc01
    have hc01stab : Γorig.IsStableCVar c01 :=
      (hstab c01).mpr (by rw [hiso.toPeak_eq_cvar_of_image hc01]; exact hd1stab)
    have hc02stab : Γorig.IsStableCVar c02 := by
      obtain ⟨D02', hc02eq⟩ := hiso.toPeak_eq_pseudo_of_image hc02
      exact (hstab c02).mpr (by rw [hc02eq]; trivial)
    have htd := (peakSepCtx_subst_HasTwoDistinct_of
      (sc := scOrig) (σt := σtW)
      (List.mem_filter.mpr ⟨cvar_mem_peakList hc01pc, decide_eq_true_iff.mpr hc01stab⟩)
      (List.mem_filter.mpr ⟨cvar_mem_peakList hc02pc, decide_eq_true_iff.mpr hc02stab⟩)
      (fun h => hne01 (Peak.cvar.inj h))).rename
      (f := Rename.succ (k := Kind.lock))
    refine SepCheck.sep_symm (SepCheck.sep_mono (SepCheck.sep_symm (SepCheck.sep_mono
      (SepCheck.sep_lock (ℓ := BVar.here) Ctx.LookupLock.here htd) ?_)) ?_)
    · apply Subcapt.sc_elem
      rw [CapyCaptureSet.compile_rename]
      exact CaptureSet.Subset.rename (f := Rename.succ)
        (peakItem_subst_supset hcompatW hiso htv' hsubsto hc01)
    · apply Subcapt.sc_elem
      rw [hD2eq, CapyCaptureSet.compile_rename]
      exact CaptureSet.Subset.rename (f := Rename.succ)
        (pseudoItem_subst_supset hΓS haSubW hcompatW hcsnp hsubsto hΓOnp hiso hscS hc02)
  -- Peak-level dispatch: IDENTICAL to `compile_peakSepCtx_sep_forward`.
  have key' : ∀ (p1 p2 : Peak s1'), p1 ≠ p2 →
      p1 ∈ (peakList (CapyCaptureSet.peakset Γsub (cs.subst σ))).filter
        (fun p => decide (Peak.IsStable Γsub p)) →
      p2 ∈ (peakList (CapyCaptureSet.peakset Γsub (cs.subst σ))).filter
        (fun p => decide (Peak.IsStable Γsub p)) →
      SepCheck
        (coreCtxW.push_lock
          (({ sep := peakSepCtx Γorig (CapyCaptureSet.peakset Γorig cs) scOrig,
              mutability := ΨmutR } : ModalCtx s2w).subst σtW))
        (CapyCaptureSet.compile
          (peakKeyItem (CapyCaptureSet.peakset Γsub (cs.subst σ)) p1)
          (scSub.rename Rename.succ))
        (CapyCaptureSet.compile
          (peakKeyItem (CapyCaptureSet.peakset Γsub (cs.subst σ)) p2)
          (scSub.rename Rename.succ)) := by
    intro p1 p2 hne hp1f hp2f
    obtain ⟨hp1, hp1s⟩ := List.mem_filter.mp hp1f
    obtain ⟨hp2, hp2s⟩ := List.mem_filter.mp hp2f
    cases p1 with
    | cvar d1 =>
      cases p2 with
      | cvar d2 =>
        have h1 := mem_peakCvars_of_cvar_mem hp1
        have h2 := mem_peakCvars_of_cvar_mem hp2
        exact keyCC d1 d2 (fun h => hne (congrArg Peak.cvar h))
          (decide_eq_true_iff.mp hp1s) (decide_eq_true_iff.mp hp2s) h1 h2
      | pseudo D2 =>
        exact keyCP d1 D2 (decide_eq_true_iff.mp hp1s) (mem_peakCvars_of_cvar_mem hp1)
          (mem_peakPseudos_of_pseudo_mem hp2)
    | pseudo D1 =>
      cases p2 with
      | cvar d2 =>
        exact SepCheck.sep_symm (keyCP d2 D1 (decide_eq_true_iff.mp hp2s)
          (mem_peakCvars_of_cvar_mem hp2) (mem_peakPseudos_of_pseudo_mem hp1))
      | pseudo D2 =>
        exfalso
        obtain ⟨C1', hC1, hC1m⟩ := peakPseudos_occ (mem_peakPseudos_of_pseudo_mem hp1)
        obtain ⟨C2', hC2, hC2m⟩ := peakPseudos_occ (mem_peakPseudos_of_pseudo_mem hp2)
        obtain ⟨c01, D01, m1, hc01, hC1eq⟩ :=
          pseudo_sub_peak_frozen_source hiso hsubsto hΓOnp hcsnp hC1
        obtain ⟨c02, D02, m2, hc02, hC2eq⟩ :=
          pseudo_sub_peak_frozen_source hiso hsubsto hΓOnp hcsnp hC2
        have ht1 : hiso.toPeak c01 = Peak.pseudo D01 := by
          have him := hiso.image c01; rw [hc01] at him
          cases htc : hiso.toPeak c01 with
          | cvar e => rw [htc] at him; simp [Peak.asCaptureSet] at him
          | pseudo D'' =>
            rw [htc] at him
            simp only [Peak.asCaptureSet, CapyCaptureSet.pseudo_peak.injEq] at him
            rw [him]
        have ht2 : hiso.toPeak c02 = Peak.pseudo D02 := by
          have him := hiso.image c02; rw [hc02] at him
          cases htc : hiso.toPeak c02 with
          | cvar e => rw [htc] at him; simp [Peak.asCaptureSet] at him
          | pseudo D'' =>
            rw [htc] at him
            simp only [Peak.asCaptureSet, CapyCaptureSet.pseudo_peak.injEq] at him
            rw [him]
        have hc12 : c01 = c02 := hiso.uniqueFrozen ht1 ht2
        subst hc12
        have hD : D01 = D02 := by
          rw [hc01] at hc02; exact CapyCaptureSet.pseudo_peak.inj hc02
        apply hne
        have e1 : D1 = (CapyCaptureSet.peaks Γsub D01).modeErase := by
          rw [← hC1m, hC1eq, CapyCaptureSet.modeErase_applyAccess]
        have e2 : D2 = (CapyCaptureSet.peaks Γsub D02).modeErase := by
          rw [← hC2m, hC2eq, CapyCaptureSet.modeErase_applyAccess]
        rw [e1, e2, hD]
  rcases hCdisj with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact key' c1 c2 hcne hc1 hc2
  · exact key' c2 c1 (Ne.symm hcne) hc2 hc1

/-- **Covered forward dispatch without the `SrcAligned` premise** (the `realign` surrogate
    route), the covered twin of `compile_peakSepCtx_sep_forward_realign`.  Runs the
    `SrcAligned`-based covered dispatch at the always-aligned `realign Γ sc`, transporting the
    per-pair covering premise `hcover` from the real `scOrig` to `realign Γorig scOrig`
    (peak key items are bound-var-free, so their compiled images are `lookupCVar`-insensitive). -/
theorem compile_peakSepCtx_sep_forward_covered_realign {s1 s2w s1' s2w' : Sig}
    {Γorig : CapyCtx s1} {Γsub : CapyCtx s1'}
    {scOrig : SrcCtx s1 s2w} {scSub : SrcCtx s1' s2w'}
    {σ : CapySubst s1 s1'} {σtW : Subst s2w s2w'}
    {cs : CapyCaptureSet s1} {coreCtxW : Ctx s2w'} {ΨmutR : MutabilityCtx s2w}
    (hΓO : Γorig.IsClosed) (hΓS : Γsub.IsClosed)
    (hcompatAlW : SubstCompat (SrcCtx.realign Γsub scSub) (SrcCtx.realign Γorig scOrig) σ σtW)
    (hcsCl : cs.IsClosed) (hsubcl : (cs.subst σ).IsClosed)
    (hΓOnp : Γorig.NoPseudoPeak) (hcsnp : cs.NoPseudoPeak)
    (hinjW : scSub.CVarInjective)
    (hiso : PeakSubstIso σ)
    (hscS : CapySubst.IsClosed σ)
    (htv' : ∀ X, ∃ Y, σ.tvar X = CapyPureTy.tvar Y)
    (hsubsto : Γorig.SubstsTo Γsub σ)
    (hcover : ∀ (p1 p2 : Peak s1),
        p1 ∈ (peakList (CapyCaptureSet.peakset Γorig cs)).filter
          (fun p => decide (Peak.IsStable Γorig p)) →
        p2 ∈ (peakList (CapyCaptureSet.peakset Γorig cs)).filter
          (fun p => decide (Peak.IsStable Γorig p)) →
        p1 ≠ p2 →
        SepCheck coreCtxW
          ((CapyCaptureSet.compile (peakKeyItem (CapyCaptureSet.peakset Γorig cs) p1) scOrig).subst σtW)
          ((CapyCaptureSet.compile (peakKeyItem (CapyCaptureSet.peakset Γorig cs) p2) scOrig).subst σtW))
    (hstab : hiso.StablePreserving Γorig Γsub) :
    ∀ (C1 C2 : CaptureSet (s2w',,Kind.lock)),
      (peakSepCtx Γsub (CapyCaptureSet.peakset Γsub (cs.subst σ))
        (scSub.rename Rename.succ)).HasTwoDistinct C1 C2 →
      SepCheck
        (coreCtxW.push_lock
          (({ sep := peakSepCtx Γorig (CapyCaptureSet.peakset Γorig cs) scOrig,
              mutability := ΨmutR } : ModalCtx s2w).subst σtW))
        C1 C2 := by
  have hInEq : peakSepCtx Γsub (CapyCaptureSet.peakset Γsub (cs.subst σ))
        ((SrcCtx.realign Γsub scSub).rename (Rename.succ (k := Kind.lock)))
      = peakSepCtx Γsub (CapyCaptureSet.peakset Γsub (cs.subst σ))
        (scSub.rename (Rename.succ (k := Kind.lock))) :=
    peakSepCtx_eq_of_lookupCVar (CapyCaptureSet.peaks_noBoundVar Γsub (cs.subst σ)) (fun c => by
      rw [SrcCtx.lookupCVar_rename, SrcCtx.lookupCVar_rename, SrcCtx.realign_lookupCVar])
  have hOutEq : peakSepCtx Γorig (CapyCaptureSet.peakset Γorig cs) (SrcCtx.realign Γorig scOrig)
      = peakSepCtx Γorig (CapyCaptureSet.peakset Γorig cs) scOrig :=
    peakSepCtx_eq_of_lookupCVar (CapyCaptureSet.peaks_noBoundVar Γorig cs)
      (fun c => SrcCtx.realign_lookupCVar Γorig scOrig c)
  -- Per-peak key-item transport: bound-var-free key items compile identically under
  -- `realign` and the real `scOrig`, so the covering premise carries over.
  have hpeqW : ∀ (p : Peak s1),
      CapyCaptureSet.compile (peakKeyItem (CapyCaptureSet.peakset Γorig cs) p)
          (SrcCtx.realign Γorig scOrig)
        = CapyCaptureSet.compile (peakKeyItem (CapyCaptureSet.peakset Γorig cs) p) scOrig :=
    fun p => CapyCaptureSet.compile_eq_of_lookupCVar
      (peakKeyItem_noBoundVar (CapyCaptureSet.peaks_noBoundVar Γorig cs) p)
      (fun c => SrcCtx.realign_lookupCVar Γorig scOrig c)
  have hcoverW : ∀ (p1 p2 : Peak s1),
      p1 ∈ (peakList (CapyCaptureSet.peakset Γorig cs)).filter
        (fun p => decide (Peak.IsStable Γorig p)) →
      p2 ∈ (peakList (CapyCaptureSet.peakset Γorig cs)).filter
        (fun p => decide (Peak.IsStable Γorig p)) →
      p1 ≠ p2 →
      SepCheck coreCtxW
        ((CapyCaptureSet.compile (peakKeyItem (CapyCaptureSet.peakset Γorig cs) p1)
          (SrcCtx.realign Γorig scOrig)).subst σtW)
        ((CapyCaptureSet.compile (peakKeyItem (CapyCaptureSet.peakset Γorig cs) p2)
          (SrcCtx.realign Γorig scOrig)).subst σtW) := by
    intro p1 p2 h1 h2 hp12
    rw [hpeqW p1, hpeqW p2]
    exact hcover p1 p2 h1 h2 hp12
  intro C1 C2 hdist
  rw [← hInEq] at hdist
  rw [← hOutEq]
  exact compile_peakSepCtx_sep_forward_covered (scOrig := SrcCtx.realign Γorig scOrig)
    (scSub := SrcCtx.realign Γsub scSub) hΓO hΓS
    (SrcCtx.realign_aligned Γorig scOrig) (SrcCtx.realign_aligned Γsub scSub) hcompatAlW
    hcsCl hsubcl hΓOnp hcsnp hinjW.realign hiso hscS htv' hsubsto
    hcoverW hstab
    C1 C2 hdist

/-- **Covering → `hcover` bridge (engine).**  Produces the per-pair covering premise
    `hcover` that `compile_peakSepCtx_sep_forward_covered` (and its backward twin
    `compile_peakSepCtx_sep_backward_covered`) consumes, FROM a literal ambient
    `CompilerCtx.SepCovered` covering.  Mirrors the separation half of
    `app_satisfy_bridge`: two distinct stable dispatch-peaks `p1 ≠ p2` embed
    (injectively, via their source origin) into two distinct stable *covered* peaks
    `e p1 ≠ e p2` of the ambient use-set `U`; the ambient covering `hcov` separates
    the covered key items in `ctxCov.coreCtx`; that `SepCheck` weakens along the ANF
    tower rename `ρ` into `coreCtxW`; and each dispatch key item's `σtW`-substituted
    image shrinks (`sep_mono`, both sides) into the (renamed) covered item.

    The re-route supplies `ρ`/`hren` (the ANF tower weakening — `app_satisfy_bridge`
    uses the same `Ctx.RenamesTo.weaken` chain) and the embedding data
    `e`/`hemb_mem`/`hemb_inj`/`hemb_sub` (the `argOpen`/`openCVar` item containments —
    the analogs of `app_satisfy_bridge`'s `itemC`/`itemT` `Subcapt` facts). EVERY
    covering pair is sourced from `hcov`; no pair is left un-sourced. -/
theorem hcover_of_sepCovered
    {sc scov s1 s2w s2w' : Sig}
    {ctxCov : CompilerCtx sc scov} {U : CapyCaptureSet sc}
    {Γorig : CapyCtx s1} {scOrig : SrcCtx s1 s2w}
    {cs : CapyCaptureSet s1} {coreCtxW : Ctx s2w'} {σtW : Subst s2w s2w'}
    {ρ : Rename scov s2w'}
    (hcov : ctxCov.SepCovered U)
    (hren : ctxCov.coreCtx.RenamesTo coreCtxW ρ) (hρinj : ρ.Injective)
    (e : Peak s1 → Peak sc)
    (hemb_mem : ∀ p : Peak s1,
        p ∈ (peakList (CapyCaptureSet.peakset Γorig cs)).filter
          (fun p => decide (Peak.IsStable Γorig p)) →
        e p ∈ (peakList (CapyCaptureSet.peakset ctxCov.capyCtx U)).filter
          (fun p => decide (Peak.IsStable ctxCov.capyCtx p)))
    (hemb_inj : ∀ p1 p2 : Peak s1,
        p1 ∈ (peakList (CapyCaptureSet.peakset Γorig cs)).filter
          (fun p => decide (Peak.IsStable Γorig p)) →
        p2 ∈ (peakList (CapyCaptureSet.peakset Γorig cs)).filter
          (fun p => decide (Peak.IsStable Γorig p)) →
        p1 ≠ p2 → e p1 ≠ e p2)
    (hemb_sub : ∀ p : Peak s1,
        p ∈ (peakList (CapyCaptureSet.peakset Γorig cs)).filter
          (fun p => decide (Peak.IsStable Γorig p)) →
        Subcapt coreCtxW
          ((CapyCaptureSet.compile (peakKeyItem (CapyCaptureSet.peakset Γorig cs) p) scOrig).subst σtW)
          ((CapyCaptureSet.compile
            (peakKeyItem (CapyCaptureSet.peakset ctxCov.capyCtx U) (e p)) ctxCov.srcCtx).rename ρ)) :
    ∀ (p1 p2 : Peak s1),
      p1 ∈ (peakList (CapyCaptureSet.peakset Γorig cs)).filter
        (fun p => decide (Peak.IsStable Γorig p)) →
      p2 ∈ (peakList (CapyCaptureSet.peakset Γorig cs)).filter
        (fun p => decide (Peak.IsStable Γorig p)) →
      p1 ≠ p2 →
      SepCheck coreCtxW
        ((CapyCaptureSet.compile (peakKeyItem (CapyCaptureSet.peakset Γorig cs) p1) scOrig).subst σtW)
        ((CapyCaptureSet.compile (peakKeyItem (CapyCaptureSet.peakset Γorig cs) p2) scOrig).subst σtW) := by
  intro p1 p2 h1 h2 hne
  have hsepCov := hcov (e p1) (e p2) (hemb_mem p1 h1) (hemb_mem p2 h2) (hemb_inj p1 p2 h1 h2 hne)
  have hsepW := hsepCov.renamesTo hren hρinj
  exact SepCheck.sep_symm
    (SepCheck.sep_mono
      (SepCheck.sep_symm (SepCheck.sep_mono hsepW (hemb_sub p1 h1)))
      (hemb_sub p2 h2))

/-! ## Covering-threading infrastructure (the covering analog of `TgtPairDroppableOn`)

Standalone infrastructure for re-routing `compile_subst_subtyp`'s FORWARD peak
separation from droppability to COVERING, mirroring the `#5`
`TgtPairDroppableOn`/`TgtCvarOccurs` threading template in `OpenCVarSubtyp.lean`.

Where `TgtPairDroppableOn P Γt σt` is a purely *local target-side* property that
lifts through binders by cheap target weakening, the covering analog must carry a
*global source-side* covering `SepCovered U` plus the per-node data
`hcover_of_sepCovered` needs threaded — the ANF tower rename `ρ`, the source-origin
peak embedding `e`, and the item-containment `hemb_sub`.  `TgtPairCovered` bundles
exactly those, scoped (like `TgtCvarOccurs`) by a source-peak predicate `Q`. -/

/-- **Bundled covering datum at a dispatch node** — the covering counterpart of
    `TgtPairDroppableOn`.  Packages EXACTLY the inputs `hcover_of_sepCovered`
    consumes to produce the per-pair `hcover` that `compile_peakSepCtx_sep_forward_covered`
    wants at a node `(Γorig, scOrig, cs, coreCtxW, σtW)`: the ambient covering
    `SepCovered U` over `ctxCov`, the ANF tower rename `ρ` (with injectivity and the
    `RenamesTo` witness), the injective source-origin peak embedding `e`, and the
    membership / item-containment facts.  The embedding facts are *scoped* by a
    source-peak predicate `Q` — only peaks the compiled type actually locks need an
    ambient source (cf. `TgtPairDroppableOn`'s `TgtCvarOccurs` scope). -/
structure TgtPairCovered
    {sc scov s1 s2w s2w' : Sig}
    (Q : Peak s1 → Prop)
    (ctxCov : CompilerCtx sc scov) (U : CapyCaptureSet sc)
    (Γorig : CapyCtx s1) (scOrig : SrcCtx s1 s2w)
    (cs : CapyCaptureSet s1) (coreCtxW : Ctx s2w') (σtW : Subst s2w s2w') where
  /-- The ANF tower weakening rename `ctxCov.coreCtx → coreCtxW`. -/
  ρ : Rename scov s2w'
  /-- The ambient covering lock invariant over `ctxCov` at use-set `U`. -/
  hcov : ctxCov.SepCovered U
  /-- `ρ` weakens the covering's target context into the dispatch context. -/
  hren : ctxCov.coreCtx.RenamesTo coreCtxW ρ
  hρinj : ρ.Injective
  /-- The source-origin peak embedding: each in-scope dispatch peak of `(Γorig, cs)`
      maps to a covered peak of `(ctxCov.capyCtx, U)`. -/
  e : Peak s1 → Peak sc
  hemb_mem : ∀ p : Peak s1, Q p →
      p ∈ (peakList (CapyCaptureSet.peakset Γorig cs)).filter
        (fun p => decide (Peak.IsStable Γorig p)) →
      e p ∈ (peakList (CapyCaptureSet.peakset ctxCov.capyCtx U)).filter
        (fun p => decide (Peak.IsStable ctxCov.capyCtx p))
  hemb_inj : ∀ p1 p2 : Peak s1, Q p1 → Q p2 →
      p1 ∈ (peakList (CapyCaptureSet.peakset Γorig cs)).filter
        (fun p => decide (Peak.IsStable Γorig p)) →
      p2 ∈ (peakList (CapyCaptureSet.peakset Γorig cs)).filter
        (fun p => decide (Peak.IsStable Γorig p)) →
      p1 ≠ p2 → e p1 ≠ e p2
  hemb_sub : ∀ p : Peak s1, Q p →
      p ∈ (peakList (CapyCaptureSet.peakset Γorig cs)).filter
        (fun p => decide (Peak.IsStable Γorig p)) →
      Subcapt coreCtxW
        ((CapyCaptureSet.compile (peakKeyItem (CapyCaptureSet.peakset Γorig cs) p) scOrig).subst σtW)
        ((CapyCaptureSet.compile
          (peakKeyItem (CapyCaptureSet.peakset ctxCov.capyCtx U) (e p)) ctxCov.srcCtx).rename ρ)

/-- **`TgtPairCovered → hcover` (the payoff).**  A `TgtPairCovered` whose scope `Q`
    covers *every* stable dispatch peak yields the per-pair covering premise
    `hcover` that `compile_peakSepCtx_sep_forward_covered` (and `_covered_realign`)
    consumes — by feeding its fields to `hcover_of_sepCovered`. -/
theorem TgtPairCovered.toHcover
    {sc scov s1 s2w s2w' : Sig}
    {Q : Peak s1 → Prop}
    {ctxCov : CompilerCtx sc scov} {U : CapyCaptureSet sc}
    {Γorig : CapyCtx s1} {scOrig : SrcCtx s1 s2w}
    {cs : CapyCaptureSet s1} {coreCtxW : Ctx s2w'} {σtW : Subst s2w s2w'}
    (h : TgtPairCovered Q ctxCov U Γorig scOrig cs coreCtxW σtW)
    (hQ : ∀ p : Peak s1,
        p ∈ (peakList (CapyCaptureSet.peakset Γorig cs)).filter
          (fun p => decide (Peak.IsStable Γorig p)) → Q p) :
    ∀ (p1 p2 : Peak s1),
      p1 ∈ (peakList (CapyCaptureSet.peakset Γorig cs)).filter
        (fun p => decide (Peak.IsStable Γorig p)) →
      p2 ∈ (peakList (CapyCaptureSet.peakset Γorig cs)).filter
        (fun p => decide (Peak.IsStable Γorig p)) →
      p1 ≠ p2 →
      SepCheck coreCtxW
        ((CapyCaptureSet.compile (peakKeyItem (CapyCaptureSet.peakset Γorig cs) p1) scOrig).subst σtW)
        ((CapyCaptureSet.compile (peakKeyItem (CapyCaptureSet.peakset Γorig cs) p2) scOrig).subst σtW) :=
  hcover_of_sepCovered h.hcov h.hren h.hρinj h.e
    (fun p hp => h.hemb_mem p (hQ p hp) hp)
    (fun p1 p2 h1 h2 => h.hemb_inj p1 p2 (hQ p1 h1) (hQ p2 h2) h1 h2)
    (fun p hp => h.hemb_sub p (hQ p hp) hp)

/-- **Scope antitonicity** (the analog of `TgtPairDroppableOn.mono`).  A covering
    for a scope `Q` restricts to any smaller scope `Q'` — a smaller set of dispatch
    peaks is easier to cover. -/
def TgtPairCovered.mono
    {sc scov s1 s2w s2w' : Sig}
    {Q Q' : Peak s1 → Prop}
    {ctxCov : CompilerCtx sc scov} {U : CapyCaptureSet sc}
    {Γorig : CapyCtx s1} {scOrig : SrcCtx s1 s2w}
    {cs : CapyCaptureSet s1} {coreCtxW : Ctx s2w'} {σtW : Subst s2w s2w'}
    (hQ : ∀ p, Q' p → Q p)
    (h : TgtPairCovered Q ctxCov U Γorig scOrig cs coreCtxW σtW) :
    TgtPairCovered Q' ctxCov U Γorig scOrig cs coreCtxW σtW where
  ρ := h.ρ
  hcov := h.hcov
  hren := h.hren
  hρinj := h.hρinj
  e := h.e
  hemb_mem := fun p hp => h.hemb_mem p (hQ p hp)
  hemb_inj := fun p1 p2 h1 h2 => h.hemb_inj p1 p2 (hQ p1 h1) (hQ p2 h2)
  hemb_sub := fun p hp => h.hemb_sub p (hQ p hp)

/-- Composition of target-context renaming morphisms (reusable). -/
theorem Ctx.RenamesTo.trans {s1 s2 s3 : Sig} {Γ1 : Ctx s1} {Γ2 : Ctx s2} {Γ3 : Ctx s3}
    {f : Rename s1 s2} {g : Rename s2 s3}
    (h1 : Γ1.RenamesTo Γ2 f) (h2 : Γ2.RenamesTo Γ3 g) :
    Γ1.RenamesTo Γ3 (f.comp g) where
  var hl := by have := h2.var (h1.var hl); rwa [Ty.rename_comp] at this
  cvar hl := by have := h2.cvar (h1.cvar hl); rwa [CaptureBound.rename_comp] at this
  tvar hl := by have := h2.tvar (h1.tvar hl); rwa [PureTy.rename_comp] at this
  lock hl := by have := h2.lock (h1.lock hl); rwa [ModalCtx.rename_comp] at this

/-- **Target-side lift** (the covering counterpart of `TgtPairDroppableOn.liftGen`).
    Transports a covering datum through a fresh *target* binder + a `σtW`-lift — the
    exact transport the `poly` (tvar) and `cpoly` (cvar) forward-dispatch locks need.
    The SOURCE side (`Γorig`, `cs`, `ctxCov`, `U`, hence the peaks, stability and the
    embedding `e`) is UNTOUCHED, so `hcov`/`e`/`hemb_mem`/`hemb_inj` carry over
    verbatim; only the ANF rename `ρ` extends by `succ` and `hemb_sub` transports by
    `Subcapt.weaken` (both sides renamed by `succ`, matched via `compile_rename` /
    `weaken_subst_comm_base` / `rename_comp`).  This is why `poly`/`cpoly` locks are
    GAP-FREE: no new source resource is introduced, so the ambient covering suffices. -/
def TgtPairCovered.liftTarget
    {sc scov s1 s2w s2w' : Sig}
    {Q : Peak s1 → Prop}
    {ctxCov : CompilerCtx sc scov} {U : CapyCaptureSet sc}
    {Γorig : CapyCtx s1} {scOrig : SrcCtx s1 s2w}
    {cs : CapyCaptureSet s1} {coreCtxW : Ctx s2w'} {σtW : Subst s2w s2w'}
    {k : Kind} (b : Binding s2w' k)
    (h : TgtPairCovered Q ctxCov U Γorig scOrig cs coreCtxW σtW) :
    TgtPairCovered Q ctxCov U Γorig (scOrig.rename Rename.succ) cs
      (coreCtxW.push b) (σtW.lift (k := k)) where
  ρ := h.ρ.comp Rename.succ
  hcov := h.hcov
  hren := Ctx.RenamesTo.trans h.hren (Ctx.RenamesTo.weaken b)
  hρinj := fun kk a c hh => h.hρinj kk (Rename.injective_succ kk hh)
  e := h.e
  hemb_mem := h.hemb_mem
  hemb_inj := h.hemb_inj
  hemb_sub := fun p hQp hp => by
    have hw := Subcapt.weaken (h.hemb_sub p hQp hp) b
    rw [CaptureSet.rename_comp] at hw
    rw [CapyCaptureSet.compile_rename, ← CaptureSet.weaken_subst_comm_base]
    exact hw

/-- **Per-node `hcover` via a target lift** — the covering source for a forward-dispatch
    lock reached through a fresh target binder + `σtW`-lift (no source-use-set change):
    `liftTarget b` then `toHcover`.  This is EXACTLY the mechanism the `poly` (tvar) and
    `cpoly` (cvar) forward dispatches use — both lift the covering through the binder
    that node introduces WITHOUT enlarging the locked source use-set. -/
theorem TgtPairCovered.toHcover_liftTarget
    {sc scov s1 s2w s2w' : Sig} {Q : Peak s1 → Prop}
    {ctxCov : CompilerCtx sc scov} {U : CapyCaptureSet sc}
    {Γorig : CapyCtx s1} {scOrig : SrcCtx s1 s2w}
    {cs : CapyCaptureSet s1} {coreCtxW : Ctx s2w'} {σtW : Subst s2w s2w'}
    {k : Kind} (b : Binding s2w' k)
    (h : TgtPairCovered Q ctxCov U Γorig scOrig cs coreCtxW σtW)
    (hQ : ∀ p : Peak s1,
        p ∈ (peakList (CapyCaptureSet.peakset Γorig cs)).filter
          (fun p => decide (Peak.IsStable Γorig p)) → Q p) :
    ∀ (p1 p2 : Peak s1),
      p1 ∈ (peakList (CapyCaptureSet.peakset Γorig cs)).filter
        (fun p => decide (Peak.IsStable Γorig p)) →
      p2 ∈ (peakList (CapyCaptureSet.peakset Γorig cs)).filter
        (fun p => decide (Peak.IsStable Γorig p)) →
      p1 ≠ p2 →
      SepCheck (coreCtxW.push b)
        ((CapyCaptureSet.compile (peakKeyItem (CapyCaptureSet.peakset Γorig cs) p1)
          (scOrig.rename Rename.succ)).subst (σtW.lift (k := k)))
        ((CapyCaptureSet.compile (peakKeyItem (CapyCaptureSet.peakset Γorig cs) p2)
          (scOrig.rename Rename.succ)).subst (σtW.lift (k := k))) :=
  (h.liftTarget b).toHcover hQ

/-- **Per-node `hcover` constructor: the `poly` lock** (`compile_subst_subtyp`, ~line 5782).
    The `poly` forward-dispatch lock is `peakSepCtx` over `cs` at the UNEXTENDED source
    context `Γorig`, reached through the fresh TVAR binder `X <: S2`.  A covering datum at
    the parent node yields the lock's `hcover` directly.  GAP-FREE: the tvar binder adds no
    source resource, so every locked peak is still an ambient peak of `(ctxCov.capyCtx, U)`. -/
theorem hcover_poly_of_covered
    {sc scov s1 s2w s2w' : Sig} {Q : Peak s1 → Prop}
    {ctxCov : CompilerCtx sc scov} {U : CapyCaptureSet sc}
    {Γorig : CapyCtx s1} {scOrig : SrcCtx s1 s2w}
    {cs : CapyCaptureSet s1} {coreCtxW : Ctx s2w'} {σtW : Subst s2w s2w'}
    (S2 : PureTy s2w')
    (h : TgtPairCovered Q ctxCov U Γorig scOrig cs coreCtxW σtW)
    (hQ : ∀ p : Peak s1,
        p ∈ (peakList (CapyCaptureSet.peakset Γorig cs)).filter
          (fun p => decide (Peak.IsStable Γorig p)) → Q p) :
    ∀ (p1 p2 : Peak s1),
      p1 ∈ (peakList (CapyCaptureSet.peakset Γorig cs)).filter
        (fun p => decide (Peak.IsStable Γorig p)) →
      p2 ∈ (peakList (CapyCaptureSet.peakset Γorig cs)).filter
        (fun p => decide (Peak.IsStable Γorig p)) →
      p1 ≠ p2 →
      SepCheck (coreCtxW.push (Binding.tvar S2))
        ((CapyCaptureSet.compile (peakKeyItem (CapyCaptureSet.peakset Γorig cs) p1)
          (scOrig.rename Rename.succ)).subst (σtW.lift (k := Kind.tvar)))
        ((CapyCaptureSet.compile (peakKeyItem (CapyCaptureSet.peakset Γorig cs) p2)
          (scOrig.rename Rename.succ)).subst (σtW.lift (k := Kind.tvar))) :=
  h.toHcover_liftTarget (Binding.tvar S2) hQ

/-- **Per-node `hcover` constructor: the `cpoly` lock** (`compile_subst_subtyp`, ~line 6042).
    Identical to `hcover_poly_of_covered`, but through the fresh CVAR binder `c <: cb` the
    `cpoly` node introduces.  The lock is again `peakSepCtx` over `cs` at the UNEXTENDED
    `Γorig` (the new cvar cannot appear in `cs`, which is closed before the binder), so the
    covering transports by a single target lift — GAP-FREE. -/
theorem hcover_cpoly_of_covered
    {sc scov s1 s2w s2w' : Sig} {Q : Peak s1 → Prop}
    {ctxCov : CompilerCtx sc scov} {U : CapyCaptureSet sc}
    {Γorig : CapyCtx s1} {scOrig : SrcCtx s1 s2w}
    {cs : CapyCaptureSet s1} {coreCtxW : Ctx s2w'} {σtW : Subst s2w s2w'}
    (a : Authority) (cb : CaptureBound s2w')
    (h : TgtPairCovered Q ctxCov U Γorig scOrig cs coreCtxW σtW)
    (hQ : ∀ p : Peak s1,
        p ∈ (peakList (CapyCaptureSet.peakset Γorig cs)).filter
          (fun p => decide (Peak.IsStable Γorig p)) → Q p) :
    ∀ (p1 p2 : Peak s1),
      p1 ∈ (peakList (CapyCaptureSet.peakset Γorig cs)).filter
        (fun p => decide (Peak.IsStable Γorig p)) →
      p2 ∈ (peakList (CapyCaptureSet.peakset Γorig cs)).filter
        (fun p => decide (Peak.IsStable Γorig p)) →
      p1 ≠ p2 →
      SepCheck (coreCtxW.push (Binding.cvar a cb))
        ((CapyCaptureSet.compile (peakKeyItem (CapyCaptureSet.peakset Γorig cs) p1)
          (scOrig.rename Rename.succ)).subst (σtW.lift (k := Kind.cvar)))
        ((CapyCaptureSet.compile (peakKeyItem (CapyCaptureSet.peakset Γorig cs) p2)
          (scOrig.rename Rename.succ)).subst (σtW.lift (k := Kind.cvar))) :=
  h.toHcover_liftTarget (Binding.cvar a cb) hQ

/-- **Per-node `hcover` constructor: the `arrow` lock** (`compile_subst_subtyp`, ~line 5247).
    UNLIKE `poly`/`cpoly`, the arrow's wrap-lock is `peakSepCtx` over an ENLARGED source
    use-set `W = (cs.rename succ succ) ∪ {var(bound .here)}` at the context extended by the
    argument-capture cvar `c` (`consCVar (unbound ε)`) and the value parameter `x`
    (`consVar T1`).  `W`'s stable peaks therefore split into two classes:

    * CLOSURE peaks (from `cs`) — still ambient peaks of `(ctxCov.capyCtx, U)`, so the ambient
      covering `h : TgtPairCovered Q …` (scope `Q` = "closure peak") sources every
      closure–closure pair exactly as `poly`/`cpoly` do.
    * DOMAIN peaks (the fresh arg-capture cvar `c`, reached through `x`'s capture `{c}`) — NOT in
      `U` (`c ∉ U`; `c` is introduced by THIS arrow), so the ambient covering CANNOT source any
      pair that involves `c` — in particular the MIXED arg-vs-closure pair `(cvar c, cvar d)`.

    The missing separations are collected in the extra premise `hdomSep`: the residual `hcover`
    over every stable pair with at least one DOMAIN peak (`¬ Q p1 ∨ ¬ Q p2`).  This is the
    arrow's OWN domain-vs-closure separation `c >< cs`.

    ★ THE FORK RESOLUTION — `hdomSep` is NOT dischargeable in a subtyping context:
    * NOT via `sep_lock` on `coreCtxW`'s own context.  `coreCtxW = ctxLockOrig.coreCtx` is the
      ambient target context extended by `push_cvar c`, `push_cvar (cx <: ⟦C⟧)`,
      `push_var (x : ⟦Tdom⟧)` — NONE a lock (`CompilerCtx.consCVar`/`consVar` leave `coreCtx`
      untouched; only `weakenTarget` pushes, and the arrow pushes cvar/cvar/var bindings, no
      lock).  The arrow's own separation lock `Ψ_orig` is pushed ON TOP of `coreCtxW` (it is the
      `modal_modal` `Satisfy`'s `push_lock`, visible only in the GOAL
      `coreCtxW.push_lock (Ψ_orig.subst σtW)`, NOT in `hcover`'s context `coreCtxW`); and `c` is
      fresh, so no enclosing lock in `coreCtxW` mentions it.
    * NOT via arrow well-formedness.  The `abs` rule (`Capybara/TypeSystem/Core.lean`) has NO
      domain-vs-closure separation premise — the arrow type asserts `c >< cs` only INSIDE its
      own compiled lock `Ψ` (a caller obligation), never as a WF fact.
    * IT IS dischargeable at an APP site — from the `app` rule's
      `CapySepCheck Γ D (interfere_set (arrow …))` premise, exactly as `app_satisfy_bridge`
      discharges the arrow lock's `Satisfy` via `CapySepCheck.compile` + the ambient covering.
      But `compile_subst_subtyp` is a pure type-subtyping lemma with no term / app context, so
      that surface separation (`hsep`/`hx`) is absent — the genuine design gap.

    So `poly`/`cpoly` are GAP-FREE under covering but the `arrow` is NOT: it needs `hdomSep`,
    whose source (the arrow's own pushed lock `Ψ_orig`) is exactly what the current droppability
    dispatch reads via `sep_lock` and what the covered `hcover`-over-`coreCtxW` interface
    structurally excludes. -/
theorem hcover_arrow_of_covered
    {sc scov s1 s2w s2w' : Sig} {Q : Peak s1 → Prop}
    {ctxCov : CompilerCtx sc scov} {U : CapyCaptureSet sc}
    {Γorig : CapyCtx s1} {scOrig : SrcCtx s1 s2w}
    {cs : CapyCaptureSet s1} {coreCtxW : Ctx s2w'} {σtW : Subst s2w s2w'}
    (h : TgtPairCovered Q ctxCov U Γorig scOrig cs coreCtxW σtW)
    (hdomSep : ∀ (p1 p2 : Peak s1),
        p1 ∈ (peakList (CapyCaptureSet.peakset Γorig cs)).filter
          (fun p => decide (Peak.IsStable Γorig p)) →
        p2 ∈ (peakList (CapyCaptureSet.peakset Γorig cs)).filter
          (fun p => decide (Peak.IsStable Γorig p)) →
        p1 ≠ p2 →
        (¬ Q p1 ∨ ¬ Q p2) →
        SepCheck coreCtxW
          ((CapyCaptureSet.compile (peakKeyItem (CapyCaptureSet.peakset Γorig cs) p1) scOrig).subst σtW)
          ((CapyCaptureSet.compile (peakKeyItem (CapyCaptureSet.peakset Γorig cs) p2) scOrig).subst σtW)) :
    ∀ (p1 p2 : Peak s1),
      p1 ∈ (peakList (CapyCaptureSet.peakset Γorig cs)).filter
        (fun p => decide (Peak.IsStable Γorig p)) →
      p2 ∈ (peakList (CapyCaptureSet.peakset Γorig cs)).filter
        (fun p => decide (Peak.IsStable Γorig p)) →
      p1 ≠ p2 →
      SepCheck coreCtxW
        ((CapyCaptureSet.compile (peakKeyItem (CapyCaptureSet.peakset Γorig cs) p1) scOrig).subst σtW)
        ((CapyCaptureSet.compile (peakKeyItem (CapyCaptureSet.peakset Γorig cs) p2) scOrig).subst σtW) := by
  intro p1 p2 h1 h2 hne
  rcases Classical.em (Q p1) with hq1 | hq1
  · rcases Classical.em (Q p2) with hq2 | hq2
    · -- both peaks ambient (closure): source from the ambient covering `h` (as `poly`/`cpoly`).
      have hsepCov := h.hcov (h.e p1) (h.e p2)
        (h.hemb_mem p1 hq1 h1) (h.hemb_mem p2 hq2 h2)
        (h.hemb_inj p1 p2 hq1 hq2 h1 h2 hne)
      have hsepW := hsepCov.renamesTo h.hren h.hρinj
      exact SepCheck.sep_symm
        (SepCheck.sep_mono
          (SepCheck.sep_symm (SepCheck.sep_mono hsepW (h.hemb_sub p1 hq1 h1)))
          (h.hemb_sub p2 hq2 h2))
    · exact hdomSep p1 p2 h1 h2 hne (Or.inr hq2)
  · exact hdomSep p1 p2 h1 h2 hne (Or.inl hq1)

/-! ### The app-site covering core for the c-slot `hsep` (occurrence-bounded)

`TgtSplitCoveredOn.openCVar_covered`'s residual premise `hsep` asks, for two
DISTINCT target-peak cvars `c1 ≠ c2` of `⟦D⟧`, a MODE-POLYMORPHIC target
`SepCheck` (`∀ m1 m2`).  The app rule has no droppability for `D`
(`hDao : D.AccessOnly`), so the fully mode-polymorphic version is UNDERIVABLE at
the `.drop` corner — the only mode-poly target rule is `sep_droppable`, which
needs `.can_drop` authority, and compiled cvars are `.access_only`
(`placeholderBinding`); every other route (`sep_lock`+`sep_mono`, the source
covering compiled through `CapySepCheck.compile`) shrinks through
`Subcapt`/`CoveredBy`, both mutability-monotone with `.drop` comparable only to
itself (`Access.Le`).  See the accompanying design dossier.

What IS fully green is the OCCURRENCE-BOUNDED core below: for output modes `≤`
the occurrence modes (the non-`.drop` pairs, which the split dispatch's non-drop
branches consume), the ambient covering pays exactly the source `sep_distinct`
axiom.  These lemmas are the reusable non-`.drop` bulk of ANY future discharge of
the c-slot `hsep` (whatever sound device closes the `.drop` corner). -/

/-- A target `cvar` atom lowered to a mode `≤` its occurrence mode is a
    `Subcapt`: `refl` when equal, `sc_ro` for the `.ro ≤ .ε` step (the only
    strict case).  The `.drop` mode is comparable only to itself (`refl`). -/
theorem Subcapt.cvar_of_le {s : Sig} {Γ : Ctx s} {m a : Access} {c : BVar s .cvar}
    (h : m ≤ a) : Subcapt Γ (CaptureSet.cvar m c) (CaptureSet.cvar a c) := by
  cases h with
  | M hm =>
    cases hm with
    | refl => exact Subcapt.refl
    | ro_eps => exact Subcapt.sc_ro (C := CaptureSet.cvar (.M .epsilon) c)
  | drop => exact Subcapt.refl

/-- **Covering core (at the occurrence modes).**  Two DISTINCT source cvar peaks
    `d1 ≠ d2` of `D` (both `CapyIsPeak`, i.e. bound `.unbound` ⇒ stable, and each
    occurring at `a1`/`a2` in `peaks Γ D`) whose separation the ambient covering
    `SepCovered D` pays, compile to a target `SepCheck` at exactly those
    occurrence modes.  This inlines `CapySepCheck.compile`'s `sep_distinct` leaf
    (SepCheckCompile.lean:361) — restrict the ambient covering to the two
    occurrence atoms via `of_subP`, then read the pair off it and shrink each
    operand with `sep_mono` — packaged for the app site.  We inline (rather than
    call `CapySepCheck.compile`) so the lemma stays `sorryAx`-free: the FULL
    `CapySepCheck.compile` is tainted by `sorryAx` through its OTHER cases. -/
theorem sepCheck_of_SepCovered_distinct {s1 s2 : Sig} {ctx : CompilerCtx s1 s2}
    (hsub : ctx.SubCoherent)
    {D : CapyCaptureSet s1} {d1 d2 : BVar s1 .cvar} {a1 a2 : Access}
    (hne : d1 ≠ d2)
    (hp1 : CapyIsPeak ctx.capyCtx (CapyCaptureSet.cvar a1 d1))
    (hp2 : CapyIsPeak ctx.capyCtx (CapyCaptureSet.cvar a2 d2))
    (ho1 : CapyCaptureSet.Subset (CapyCaptureSet.cvar a1 d1)
      (CapyCaptureSet.peaks ctx.capyCtx D))
    (ho2 : CapyCaptureSet.Subset (CapyCaptureSet.cvar a2 d2)
      (CapyCaptureSet.peaks ctx.capyCtx D))
    (hcovD : ctx.SepCovered D) :
    SepCheck ctx.coreCtx
      (CaptureSet.cvar a1 (ctx.srcCtx.lookupCVar d1))
      (CaptureSet.cvar a2 (ctx.srcCtx.lookupCVar d2)) := by
  -- Restrict the ambient covering to the two occurrence atoms `U`.
  have hSubP : CapyCaptureSet.SubP ctx.capyCtx
      (CapyCaptureSet.cvar a1 d1 ∪ CapyCaptureSet.cvar a2 d2) D := by
    unfold CapyCaptureSet.SubP
    rw [CapyCaptureSet.peaks_union]
    simp only [CapyCaptureSet.peaks]
    exact CapyCaptureSet.CoveredBy.union_left ho1.coveredBy ho2.coveredBy
  have hcov' : ctx.SepCovered
      (CapyCaptureSet.cvar a1 d1 ∪ CapyCaptureSet.cvar a2 d2) :=
    hcovD.of_subP hsub hSubP
  -- Read the pair off the covering directly (replaying `CapySepCheck.compile`'s
  -- `sep_distinct` leaf; the FULL `CapySepCheck.compile` pulls in `sorryAx` via
  -- its OTHER cases, so we inline only this leaf to stay `sorryAx`-free).
  set U : CapyCaptureSet s1 :=
    CapyCaptureSet.cvar a1 d1 ∪ CapyCaptureSet.cvar a2 d2 with hU
  have hpeaksU : CapyCaptureSet.peaks ctx.capyCtx U
      = CapyCaptureSet.cvar a1 d1 ∪ CapyCaptureSet.cvar a2 d2 := by
    rw [hU, CapyCaptureSet.peaks_union]
    simp only [CapyCaptureSet.peaks]
  have hoccA : CapyCaptureSet.Subset (CapyCaptureSet.cvar a1 d1)
      (CapyCaptureSet.peakset ctx.capyCtx U).cs := by
    change CapyCaptureSet.Subset _ (CapyCaptureSet.peaks ctx.capyCtx U)
    rw [hpeaksU]
    exact CapyCaptureSet.Subset.union_right_left CapyCaptureSet.Subset.refl
  have hoccB : CapyCaptureSet.Subset (CapyCaptureSet.cvar a2 d2)
      (CapyCaptureSet.peakset ctx.capyCtx U).cs := by
    change CapyCaptureSet.Subset _ (CapyCaptureSet.peaks ctx.capyCtx U)
    rw [hpeaksU]
    exact CapyCaptureSet.Subset.union_right_right CapyCaptureSet.Subset.refl
  obtain ⟨_, m1', hlk1⟩ :
      ∃ auth m, CapyCtx.LookupCVar ctx.capyCtx d1 auth (.unbound m) := by
    cases hp1 with | peak_peak hlk => exact ⟨_, _, hlk⟩
  obtain ⟨_, m2', hlk2⟩ :
      ∃ auth m, CapyCtx.LookupCVar ctx.capyCtx d2 auth (.unbound m) := by
    cases hp2 with | peak_peak hlk => exact ⟨_, _, hlk⟩
  have hstabA : Peak.IsStable ctx.capyCtx (Peak.cvar d1) := Or.inr ⟨m1', hlk1.eq_lookup.symm⟩
  have hstabB : Peak.IsStable ctx.capyCtx (Peak.cvar d2) := Or.inr ⟨m2', hlk2.eq_lookup.symm⟩
  have memA : Peak.cvar d1 ∈ (peakList (CapyCaptureSet.peakset ctx.capyCtx U)).filter
      (fun p => decide (Peak.IsStable ctx.capyCtx p)) :=
    List.mem_filter.mpr ⟨PC.cvar_mem_peakList (PC.cvar_mem_peakCvars hoccA),
      decide_eq_true_iff.mpr hstabA⟩
  have memB : Peak.cvar d2 ∈ (peakList (CapyCaptureSet.peakset ctx.capyCtx U)).filter
      (fun p => decide (Peak.IsStable ctx.capyCtx p)) :=
    List.mem_filter.mpr ⟨PC.cvar_mem_peakList (PC.cvar_mem_peakCvars hoccB),
      decide_eq_true_iff.mpr hstabB⟩
  have hpne : Peak.cvar d1 ≠ Peak.cvar d2 := fun h => hne (Peak.cvar.inj h)
  have hbase := hcov' (Peak.cvar d1) (Peak.cvar d2) memA memB hpne
  simp only [peakKeyItem] at hbase
  have hscA : CapySubcapt ctx.capyCtx (CapyCaptureSet.cvar a1 d1)
      (peakItem (CapyCaptureSet.peakset ctx.capyCtx U) d1) :=
    CapySubcapt.sc_elem (PC.cvar_subset_peakItem hoccA)
  have hscB : CapySubcapt ctx.capyCtx (CapyCaptureSet.cvar a2 d2)
      (peakItem (CapyCaptureSet.peakset ctx.capyCtx U) d2) :=
    CapySubcapt.sc_elem (PC.cvar_subset_peakItem hoccB)
  exact SepCheck.sep_symm (SepCheck.sep_mono (SepCheck.sep_symm
    (SepCheck.sep_mono hbase (CapySubcapt.compile hscA ctx rfl hsub)))
    (CapySubcapt.compile hscB ctx rfl hsub))

/-- **Covering core (occurrence-BOUNDED, the B3.5 shape).**  Extends
    `sepCheck_of_SepCovered_distinct` to every output-mode pair `m1 ≤ a1`,
    `m2 ≤ a2` by shrinking each operand along `Subcapt.cvar_of_le` (`sep_mono`).
    This is the c-slot `hsep` body restricted to coverable (non-`.drop`) output
    modes; a future discharge of `TgtSplitCoveredOn.openCVar_covered` consumes it
    on the split dispatch's non-drop branches (the `.drop` branch needs a
    separate sound device — see dossier). -/
theorem sepCheck_of_SepCovered_distinct_bounded {s1 s2 : Sig}
    {ctx : CompilerCtx s1 s2}
    (hsub : ctx.SubCoherent)
    {D : CapyCaptureSet s1} {d1 d2 : BVar s1 .cvar} {a1 a2 : Access}
    (hne : d1 ≠ d2)
    (hp1 : CapyIsPeak ctx.capyCtx (CapyCaptureSet.cvar a1 d1))
    (hp2 : CapyIsPeak ctx.capyCtx (CapyCaptureSet.cvar a2 d2))
    (ho1 : CapyCaptureSet.Subset (CapyCaptureSet.cvar a1 d1)
      (CapyCaptureSet.peaks ctx.capyCtx D))
    (ho2 : CapyCaptureSet.Subset (CapyCaptureSet.cvar a2 d2)
      (CapyCaptureSet.peaks ctx.capyCtx D))
    (hcovD : ctx.SepCovered D) :
    ∀ (m1 m2 : Access), m1 ≤ a1 → m2 ≤ a2 →
      SepCheck ctx.coreCtx
        (CaptureSet.cvar m1 (ctx.srcCtx.lookupCVar d1))
        (CaptureSet.cvar m2 (ctx.srcCtx.lookupCVar d2)) := by
  intro m1 m2 hm1 hm2
  have hbase := sepCheck_of_SepCovered_distinct hsub hne hp1 hp2 ho1 ho2 hcovD
  exact SepCheck.sep_symm
    (SepCheck.sep_mono
      (SepCheck.sep_symm (SepCheck.sep_mono hbase (Subcapt.cvar_of_le hm1)))
      (Subcapt.cvar_of_le hm2))

/-- **★ APP-SITE DESIGN-GAP LEMMA (pinned `sorry`, NOT an axiom) ★** — the
    residual mode-polymorphic c-slot separation premise of
    `TgtSplitCoveredOn.openCVar_covered` at the application site (instantiated at
    `C := ⟦D⟧`, `Γt := ctx.coreCtx`).  It asks, for any two DISTINCT target-peak
    cvars `c1 ≠ c2` of the compiled capture argument `⟦D⟧`, a target `SepCheck`
    at ARBITRARY output modes `m1 m2` — the self-separation of `D`'s peaks.

    **Why this is left `sorry` (see the design dossier):** the `∀ m1 m2` includes
    `.drop`, and for an ACCESS-ONLY `D` (`hDao`) the obligation
    `SepCheck ctx.coreCtx (.cvar .drop ⟦d1⟧) (.cvar .drop ⟦d2⟧)` is UNDERIVABLE in
    the target: the only mode-polymorphic `SepCheck` rule is `sep_droppable`,
    which needs `.can_drop` authority (compiled cvars are `.access_only`,
    `placeholderBinding`); every other route (`sep_lock`+`sep_mono`, the source
    covering compiled through `CapySepCheck.compile`) shrinks through
    `Subcapt`/`CoveredBy`, which are mutability-monotone with `.drop` comparable
    only to itself (`Access.Le`).  The obligation is reached when the callee's
    domain `T1` carries a NESTED `.drop`-mode occurrence of the self-cvar `c`
    (admissible for a well-typed `T1` — `hT1ao` bounds only the TOP-LEVEL
    `T1.captureSet`, `dropFree_not_subtyp_stable` permits nested drop-latents),
    so the arg-fit `compile_subst_subtyp` SPLIT requests a `.drop`-moded pair of
    `⟦D⟧`'s two distinct peaks.  It is SEMANTICALLY TRUE (distinct heap roots do
    not interfere at any mode, incl. `.drop` — no double-free) but has no
    syntactic witness under the current target `SepCheck` (which deliberately
    lacks a distinctness rule).

    **Non-`.drop` core is DONE:** for output modes bounded by the occurrence
    modes, `sepCheck_of_SepCovered_distinct_bounded` (above) proves exactly this
    body from the ambient covering `hcovD` (the covering pays the source
    `sep_distinct` axiom, mode-matched).  Wiring it here additionally needs the
    target→source trace (`compile_resourcePeaks_target` +
    `compile_cvar_subset_inv_resource`), whose residuals — `resourcePeaks`⇒`peaks`
    for `⟦D⟧` and `.unbound`-stability of the traced peaks — are themselves open
    (no bridge lemma exists), so folding them in would only ADD `sorry`s.

    **Candidate sound devices** (design decision for the user; do NOT build here):
    (A) a scoped target `SepCheck` rule making distinct COMPILED source-cvar
    roots separable at any mode (re-imports the source `sep_distinct` assumption,
    scoped, + one Noninterference lemma); or (B) a source-rule premise linking
    `T1`'s latent drop-effect on `c` to `D`'s droppability. `.drop`-filtering of
    lock/peak items is UNSOUND (it starves the fresh case's `sep_droppable`
    payment — refuted by consumer census). -/
theorem app_capture_self_sep_modepoly {s1 s2 : Sig} {ctx : CompilerCtx s1 s2}
    {D : CapyCaptureSet s1}
    (hcoh : ctx.Coherent) (hnpp : ctx.capyCtx.NoPseudoPeak)
    (hinj : ctx.srcCtx.CVarInjective)
    (hDcl : D.IsClosed) (hDnpp : D.NoPseudoPeak)
    (hDao : CapyCaptureSet.AccessOnly ctx.capyCtx D)
    (hcovD : ctx.SepCovered D) :
    ∀ (a1 a2 : Access) (c1 c2 : BVar s2 .cvar), c1 ≠ c2 →
      (CaptureSet.cvar a1 c1) ⊆
        CaptureSet.peaks ctx.coreCtx (CapyCaptureSet.compile D ctx.srcCtx) →
      (CaptureSet.cvar a2 c2) ⊆
        CaptureSet.peaks ctx.coreCtx (CapyCaptureSet.compile D ctx.srcCtx) →
      ∀ (m1 m2 : Access),
        SepCheck ctx.coreCtx (CaptureSet.cvar m1 c1) (CaptureSet.cvar m2 c2) := by
  sorry

end Compilation
