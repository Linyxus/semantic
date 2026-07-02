import Semantic.CoreCapybara.Compilation.SepCheckCompile
open CoreCapybara

namespace CoreCapybara

/-!
# Right/left restriction of a source separation to a stable peak atom

The **restriction metatheorem** for the source separation judgment
`CapySepCheck`: a separation fact `CapySepCheck Γ C1 C2` restricts on the right
to any single stable-peak `cvar` atom of `C2`'s peak resolution (and, dually, on
the left to a stable-peak atom of `C1`).

The proof is one induction over the derivation proving BOTH directions
simultaneously (so `sep_symm` can swap them).  The motive carries a *mode-slack*
parameter `b ≤ a`: the queried occurrence `.cvar a c'` may weaken to any
`.cvar b c'` below it in the conclusion.  The slack is what makes the `sep_sc`
left case go through: `cvar_subset_coveredby` re-targets the occurrence at a
possibly *stronger* access `a'` (with `a ≤ a'`), and the fixed output access `b`
survives by `b ≤ a ≤ a'`, rather than by an `EquivP` that would fail under a
strict mode drop.

## Supporting infrastructure

* `cvar_peak_hasKind_ro` — a stable peak atom of a read-only set is itself
  read-only, via the atom-to-atom `CapySubcapt` witness
  (`CapyCtx.peaks_subcapt_stable_witness`) plumbed into `CapyHasKind.sc`.
* `cvar_peaks_subset_resourcePeaks` — a bare `cvar` atom of `peaks Γ C` is a
  bare `cvar` atom of `resourcePeaks Γ C` (mode-preserving); `peaks` and
  `resourcePeaks` apply identical `rename`/`applyAccess` transforms, differing
  only at `pseudo_peak` nodes (which no bare-`cvar` `Subset` can enter).  This
  bridges the `sep_ro` premise `AccessOnly` (stated over `resourcePeaks`) to the
  occurrence hypothesis (stated over `peaks`), excluding a `.drop` output.
-/

/-- Renaming a `cvar` atom preserves its access mode: forward monotonicity. -/
theorem CapyCaptureSet.cvar_subset_rename_fwd {s s' : Sig} {X : CapyCaptureSet s}
    {ρ : Rename s s'} {a : Access} {c : BVar s .cvar}
    (h : (CapyCaptureSet.cvar a c) ⊆ X) :
    (CapyCaptureSet.cvar a (ρ.var c)) ⊆ X.rename ρ := by
  induction X with
  | empty => cases h
  | union X1 X2 ih1 ih2 =>
    simp only [CapyCaptureSet.rename]
    cases h with
    | union_right_left h => exact .union_right_left (ih1 h)
    | union_right_right h => exact .union_right_right (ih2 h)
  | var m v => cases h
  | cvar m c1 =>
    cases h
    simp only [CapyCaptureSet.rename]
    exact CapyCaptureSet.Subset.refl
  | pseudo_peak C0 _ => cases h

/-- A `cvar` atom of `X.rename ρ` comes from a `cvar` atom of `X` at the same
    access mode (inverse of `cvar_subset_rename_fwd`). -/
theorem CapyCaptureSet.cvar_subset_rename_inv {s s' : Sig} {X : CapyCaptureSet s}
    {ρ : Rename s s'} {a : Access} {c : BVar s' .cvar}
    (h : (CapyCaptureSet.cvar a c) ⊆ X.rename ρ) :
    ∃ c0, c = ρ.var c0 ∧ (CapyCaptureSet.cvar a c0) ⊆ X := by
  induction X with
  | empty => simp only [CapyCaptureSet.rename] at h; cases h
  | union X1 X2 ih1 ih2 =>
    simp only [CapyCaptureSet.rename] at h
    cases h with
    | union_right_left h => obtain ⟨c0, hc, hX⟩ := ih1 h; exact ⟨c0, hc, .union_right_left hX⟩
    | union_right_right h => obtain ⟨c0, hc, hX⟩ := ih2 h; exact ⟨c0, hc, .union_right_right hX⟩
  | var m v => simp only [CapyCaptureSet.rename] at h; cases h
  | cvar m c1 =>
    simp only [CapyCaptureSet.rename] at h
    cases h
    exact ⟨c1, rfl, CapyCaptureSet.Subset.refl⟩
  | pseudo_peak C0 _ => simp only [CapyCaptureSet.rename] at h; cases h

/-- `applyRO` preserves `cvar` membership at the read-only image of the mode. -/
theorem CapyCaptureSet.cvar_subset_applyRO_fwd {s : Sig} {X : CapyCaptureSet s}
    {a : Access} {c : BVar s .cvar} (h : (CapyCaptureSet.cvar a c) ⊆ X) :
    (CapyCaptureSet.cvar a.applyRO c) ⊆ X.applyRO := by
  induction X with
  | empty => cases h
  | union X1 X2 ih1 ih2 =>
    simp only [CapyCaptureSet.applyRO]
    cases h with
    | union_right_left h => exact .union_right_left (ih1 h)
    | union_right_right h => exact .union_right_right (ih2 h)
  | var m v => cases h
  | cvar m c1 =>
    cases h
    simp only [CapyCaptureSet.applyRO]
    exact CapyCaptureSet.Subset.refl
  | pseudo_peak C0 _ => cases h

/-- `applyDrop` sends every `cvar` atom to `.drop` mode. -/
theorem CapyCaptureSet.cvar_subset_applyDrop_fwd {s : Sig} {X : CapyCaptureSet s}
    {a : Access} {c : BVar s .cvar} (h : (CapyCaptureSet.cvar a c) ⊆ X) :
    (CapyCaptureSet.cvar .drop c) ⊆ X.applyDrop := by
  induction X with
  | empty => cases h
  | union X1 X2 ih1 ih2 =>
    simp only [CapyCaptureSet.applyDrop]
    cases h with
    | union_right_left h => exact .union_right_left (ih1 h)
    | union_right_right h => exact .union_right_right (ih2 h)
  | var m v => cases h
  | cvar m c1 =>
    cases h
    simp only [CapyCaptureSet.applyDrop]
    exact CapyCaptureSet.Subset.refl
  | pseudo_peak C0 _ => cases h

/-- Mode-preserving transfer through `rename`: if every `cvar` atom of `X`
    survives (mode-preserved) into `Y`, so does every `cvar` atom of `X.rename ρ`
    into `Y.rename ρ`. -/
theorem CapyCaptureSet.cvar_rename_mono {s s' : Sig} {X Y : CapyCaptureSet s}
    {ρ : Rename s s'}
    (hm : ∀ {a : Access} {c : BVar s .cvar},
      (CapyCaptureSet.cvar a c) ⊆ X → (CapyCaptureSet.cvar a c) ⊆ Y)
    {a : Access} {c : BVar s' .cvar} (h : (CapyCaptureSet.cvar a c) ⊆ X.rename ρ) :
    (CapyCaptureSet.cvar a c) ⊆ Y.rename ρ := by
  obtain ⟨c0, hc, hX⟩ := CapyCaptureSet.cvar_subset_rename_inv h
  subst hc
  exact CapyCaptureSet.cvar_subset_rename_fwd (hm hX)

/-- Mode-preserving transfer through `applyAccess`. -/
theorem CapyCaptureSet.cvar_applyAccess_mono {s : Sig} {X Y : CapyCaptureSet s} {m : Access}
    (hm : ∀ {a : Access} {c : BVar s .cvar},
      (CapyCaptureSet.cvar a c) ⊆ X → (CapyCaptureSet.cvar a c) ⊆ Y)
    {a : Access} {c : BVar s .cvar} (h : (CapyCaptureSet.cvar a c) ⊆ X.applyAccess m) :
    (CapyCaptureSet.cvar a c) ⊆ Y.applyAccess m := by
  cases m with
  | M m0 =>
    cases m0 with
    | epsilon =>
      simp only [CapyCaptureSet.applyAccess_M, CapyCaptureSet.applyMut_epsilon] at h ⊢
      exact hm h
    | ro =>
      simp only [CapyCaptureSet.applyAccess_M, CapyCaptureSet.applyMut_ro] at h ⊢
      obtain ⟨a0, hX, ha⟩ := CapyCaptureSet.cvar_mem_applyRO_inv' h
      subst ha
      exact CapyCaptureSet.cvar_subset_applyRO_fwd (hm hX)
  | drop =>
    simp only [CapyCaptureSet.applyAccess_drop] at h ⊢
    have ha := CapyCaptureSet.cvar_mem_applyDrop_access h
    obtain ⟨a0, hX⟩ := CapyCaptureSet.cvar_mem_applyDrop_inv h
    subst ha
    exact CapyCaptureSet.cvar_subset_applyDrop_fwd (hm hX)

mutual
/-- Bridge (var-bound helper): a bare `cvar` atom of `peaksVarBound` is one of
    `resourcePeaksVarBound` (mode-preserving). -/
theorem CapyCaptureSet.cvar_peaksVarBound_subset_resourcePeaksVarBound
    {s : Sig} (Γ : CapyCtx s) (m : Access) (x : BVar s .var) {a : Access} {c : BVar s .cvar}
    (h : (CapyCaptureSet.cvar a c) ⊆ CapyCaptureSet.peaksVarBound Γ m x) :
    (CapyCaptureSet.cvar a c) ⊆ CapyCaptureSet.resourcePeaksVarBound Γ m x := by
  match Γ, x, h with
  | .push Γ (.var T), .here, h =>
    rw [CapyCaptureSet.peaksVarBound] at h
    rw [CapyCaptureSet.resourcePeaksVarBound]
    exact CapyCaptureSet.cvar_applyAccess_mono
      (fun hh => CapyCaptureSet.cvar_rename_mono
        (fun hhh => CapyCaptureSet.cvar_peaks_subset_resourcePeaks Γ T.captureSet hhh) hh) h
  | .push Γ b, .there x, h =>
    rw [CapyCaptureSet.peaksVarBound] at h
    rw [CapyCaptureSet.resourcePeaksVarBound]
    exact CapyCaptureSet.cvar_rename_mono
      (fun hh => CapyCaptureSet.cvar_peaksVarBound_subset_resourcePeaksVarBound Γ m x hh) h
termination_by (sizeOf Γ, sizeOf x + 1)

/-- **Bridge**: a bare `cvar` atom of `peaks Γ C` is a bare `cvar` atom of
    `resourcePeaks Γ C`, at the same access mode. -/
theorem CapyCaptureSet.cvar_peaks_subset_resourcePeaks
    {s : Sig} (Γ : CapyCtx s) (C : CapyCaptureSet s) {a : Access} {c : BVar s .cvar}
    (h : (CapyCaptureSet.cvar a c) ⊆ CapyCaptureSet.peaks Γ C) :
    (CapyCaptureSet.cvar a c) ⊆ CapyCaptureSet.resourcePeaks Γ C := by
  match Γ, C, h with
  | _, .empty, h => rw [CapyCaptureSet.peaks] at h; cases h
  | Γ, .union C1 C2, h =>
    rw [CapyCaptureSet.peaks] at h
    rw [CapyCaptureSet.resourcePeaks]
    cases h with
    | union_right_left h =>
      exact .union_right_left (CapyCaptureSet.cvar_peaks_subset_resourcePeaks Γ C1 h)
    | union_right_right h =>
      exact .union_right_right (CapyCaptureSet.cvar_peaks_subset_resourcePeaks Γ C2 h)
  | _, .cvar m c0, h =>
    rw [CapyCaptureSet.peaks] at h; rw [CapyCaptureSet.resourcePeaks]; exact h
  | _, .var _ (.free _), h => rw [CapyCaptureSet.peaks] at h; cases h
  | Γ, .var m (.bound x), h =>
    rw [CapyCaptureSet.peaks] at h; rw [CapyCaptureSet.resourcePeaks]
    exact CapyCaptureSet.cvar_peaksVarBound_subset_resourcePeaksVarBound Γ m x h
  | Γ, .pseudo_peak C0, h => rw [CapyCaptureSet.peaks] at h; cases h
termination_by (sizeOf Γ, sizeOf C)
end

/-- **A stable peak atom of a read-only set is itself read-only.**  By induction
    on the `CapyHasKind _ _ .ro` derivation; the `sc` step transports the atom
    occurrence to the supertype with an atom-to-atom `CapySubcapt` witness
    (`CapyCtx.peaks_subcapt_stable_witness`), which `CapyHasKind.sc` consumes,
    absorbing the access-mode change. -/
theorem cvar_peak_hasKind_ro {s : Sig} {Γ : CapyCtx s} {c' : BVar s .cvar}
    (hstab : Γ.IsStableCVar c') :
    ∀ {C : CapyCaptureSet s} {k : Mutability}, CapyHasKind Γ C k → k = .ro →
      ∀ {a : Access}, (CapyCaptureSet.cvar a c') ⊆ CapyCaptureSet.peaks Γ C →
        CapyHasKind Γ (CapyCaptureSet.cvar a c') .ro := by
  intro C k hk
  induction hk with
  | empty =>
    intro _ a hmem
    have hmem' : (CapyCaptureSet.cvar a c') ⊆ CapyCaptureSet.peaks Γ CapyCaptureSet.empty := hmem
    rw [CapyCaptureSet.peaks] at hmem'; cases hmem'
  | union hk1 hk2 ih1 ih2 =>
    intro hkeq a hmem
    simp only [CapyCaptureSet.peaks_union] at hmem
    cases hmem with
    | union_right_left h => exact ih1 hkeq h
    | union_right_right h => exact ih2 hkeq h
  | sc hsc hk2 ih2 =>
    intro hkeq a hmem
    obtain ⟨a2, hsc_atom, hmem2⟩ := CapyCtx.peaks_subcapt_stable_witness hsc hstab hmem
    exact CapyHasKind.sc hsc_atom (ih2 hkeq hmem2)
  | rw => intro hkeq _ _; exact Mutability.noConfusion hkeq
  | imm hlk =>
    intro _ a hmem
    rw [CapyCaptureSet.peaks] at hmem; cases hmem
    exact CapyHasKind.imm hlk
  | ro =>
    intro _ a hmem
    rename_i C0
    rw [CapyCaptureSet.peaks_applyRO_comm] at hmem
    obtain ⟨a0, hmem0, ha⟩ := CapyCaptureSet.cvar_mem_applyRO_inv' hmem
    subst ha
    exact CapyHasKind.ro (C := CapyCaptureSet.cvar a0 c')

/-- Mode-lowering of a single `cvar` atom is a `CapySubcapt`: `b ≤ a` gives
    `.cvar b c' ⊑ .cvar a c'`. -/
theorem subcapt_cvar_le {s : Sig} {Γ : CapyCtx s} {a b : Access}
    {c' : BVar s .cvar} (hle : b ≤ a) :
    CapySubcapt Γ (CapyCaptureSet.cvar b c') (CapyCaptureSet.cvar a c') := by
  cases hle with
  | M hm =>
    cases hm with
    | refl => exact CapySubcapt.sc_elem CapyCaptureSet.Subset.refl
    | ro_eps =>
      exact CapySubcapt.sc_mode (C := CapyCaptureSet.cvar (.M .epsilon) c')
        (m1 := .ro) (m2 := .epsilon) Mutability.Le.ro_eps
  | drop => exact CapySubcapt.sc_elem CapyCaptureSet.Subset.refl

/-- A single non-`drop` `cvar` atom is access-only. -/
theorem cvar_accessOnly_of_ne_drop {s : Sig} {Γ : CapyCtx s} {b : Access}
    {c' : BVar s .cvar} (hb : b ≠ .drop) :
    CapyCaptureSet.AccessOnly Γ (CapyCaptureSet.cvar b c') := by
  intro c hsub
  simp only [CapyCaptureSet.resourcePeaks] at hsub
  cases hsub
  exact hb rfl

/-- **The restriction metatheorem (both directions, with mode slack).**  A
    separation `CapySepCheck Γ C1 C2` restricts on the right to any stable peak
    `cvar` atom of `C2` (and dually on the left for `C1`), and the queried access
    `a` may weaken to any `b ≤ a` in the conclusion. -/
theorem CapySepCheck.restrict_aux {s : Sig} {Γ : CapyCtx s} {C1 C2 : CapyCaptureSet s}
    (h : CapySepCheck Γ C1 C2) :
    (∀ {a b : Access} {c' : BVar s .cvar},
        (CapyCaptureSet.cvar a c') ⊆ CapyCaptureSet.peaks Γ C2 →
        Γ.IsStableCVar c' → b ≤ a → CapySepCheck Γ C1 (CapyCaptureSet.cvar b c')) ∧
    (∀ {a b : Access} {c' : BVar s .cvar},
        (CapyCaptureSet.cvar a c') ⊆ CapyCaptureSet.peaks Γ C1 →
        Γ.IsStableCVar c' → b ≤ a → CapySepCheck Γ (CapyCaptureSet.cvar b c') C2) := by
  induction h with
  | sep_symm h' ih =>
    refine ⟨?_, ?_⟩
    · intro a b c' hmem hstab hle
      exact CapySepCheck.sep_symm (ih.2 hmem hstab hle)
    · intro a b c' hmem hstab hle
      exact CapySepCheck.sep_symm (ih.1 hmem hstab hle)
  | sep_union h1 h2 ih1 ih2 =>
    refine ⟨?_, ?_⟩
    · intro a b c' hmem hstab hle
      exact CapySepCheck.sep_union (ih1.1 hmem hstab hle) (ih2.1 hmem hstab hle)
    · intro a b c' hmem hstab hle
      rw [CapyCaptureSet.peaks_union] at hmem
      cases hmem with
      | union_right_left h => exact ih1.2 h hstab hle
      | union_right_right h => exact ih2.2 h hstab hle
  | sep_empty =>
    refine ⟨?_, ?_⟩
    · intro a b c' hmem hstab hle
      exact CapySepCheck.sep_empty
    · intro a b c' hmem hstab hle
      have hmem' : (CapyCaptureSet.cvar a c') ⊆ CapyCaptureSet.peaks Γ CapyCaptureSet.empty := hmem
      rw [CapyCaptureSet.peaks] at hmem'; cases hmem'
  | sep_ro hcl1 hcl2 hao1 hao2 hk1 hk2 =>
    refine ⟨?_, ?_⟩
    · intro a b c' hmem hstab hle
      have hane : a ≠ .drop := by
        intro haeq; subst haeq
        exact hao2 c' (CapyCaptureSet.cvar_peaks_subset_resourcePeaks _ _ hmem)
      have hbne : b ≠ .drop := by intro hbeq; subst hbeq; cases hle; exact hane rfl
      have hka := cvar_peak_hasKind_ro hstab hk2 rfl hmem
      exact CapySepCheck.sep_ro hcl1 CapyCaptureSet.IsClosed.cvar hao1
        (cvar_accessOnly_of_ne_drop hbne) hk1 (CapyHasKind.sc (subcapt_cvar_le hle) hka)
    · intro a b c' hmem hstab hle
      have hane : a ≠ .drop := by
        intro haeq; subst haeq
        exact hao1 c' (CapyCaptureSet.cvar_peaks_subset_resourcePeaks _ _ hmem)
      have hbne : b ≠ .drop := by intro hbeq; subst hbeq; cases hle; exact hane rfl
      have hka := cvar_peak_hasKind_ro hstab hk1 rfl hmem
      exact CapySepCheck.sep_ro CapyCaptureSet.IsClosed.cvar hcl2
        (cvar_accessOnly_of_ne_drop hbne) hao2 (CapyHasKind.sc (subcapt_cvar_le hle) hka) hk2
  | sep_sc hsep hsc hequiv ih =>
    refine ⟨?_, ?_⟩
    · intro a b c' hmem hstab hle
      exact CapySepCheck.sep_sc (ih.1 hmem hstab hle) hsc hequiv
    · intro a b c' hmem hstab hle
      obtain ⟨a', hle', hmem'⟩ := CapyCaptureSet.CoveredBy.cvar_subset_coveredby hmem hequiv.1
      exact ih.2 hmem' hstab (Access.Le.trans hle hle')
  | sep_distinct hne hp1 hp2 =>
    refine ⟨?_, ?_⟩
    · intro a b c' hmem hstab hle
      rw [CapyCaptureSet.peaks_applyAccess_comm] at hmem
      cases hp2 with
      | peak_peak hlk2 =>
        simp only [CapyCaptureSet.peaks] at hmem
        obtain ⟨a', h'⟩ := CapyCaptureSet.cvar_subset_applyAccess_inv hmem
        cases h'
        refine CapySepCheck.sep_distinct (mu2 := .M .epsilon) ?_ hp1
          (CapyIsPeak.peak_peak (mu := b) hlk2)
        simpa only [CapyCaptureSet.modeErase] using hne
      | peak_pseudo =>
        simp only [CapyCaptureSet.peaks] at hmem
        obtain ⟨a', h'⟩ := CapyCaptureSet.cvar_subset_applyAccess_inv hmem
        cases h'
    · intro a b c' hmem hstab hle
      rw [CapyCaptureSet.peaks_applyAccess_comm] at hmem
      cases hp1 with
      | peak_peak hlk1 =>
        simp only [CapyCaptureSet.peaks] at hmem
        obtain ⟨a', h'⟩ := CapyCaptureSet.cvar_subset_applyAccess_inv hmem
        cases h'
        refine CapySepCheck.sep_distinct (mu1 := .M .epsilon) ?_
          (CapyIsPeak.peak_peak (mu := b) hlk1) hp2
        simpa only [CapyCaptureSet.modeErase] using hne
      | peak_pseudo =>
        simp only [CapyCaptureSet.peaks] at hmem
        obtain ⟨a', h'⟩ := CapyCaptureSet.cvar_subset_applyAccess_inv hmem
        cases h'

/-- **Right restriction.**  A separation `CapySepCheck Γ C1 C2` restricts on the
    right to any single stable peak `cvar` atom of `C2`. -/
theorem CapySepCheck.restrict_right {s : Sig} {Γ : CapyCtx s} {C1 C2 : CapyCaptureSet s}
    (h : CapySepCheck Γ C1 C2) {a : Access} {c' : BVar s .cvar}
    (hmem : (CapyCaptureSet.cvar a c') ⊆ CapyCaptureSet.peaks Γ C2)
    (hstab : Γ.IsStableCVar c') :
    CapySepCheck Γ C1 (CapyCaptureSet.cvar a c') :=
  h.restrict_aux.1 hmem hstab Access.Le.refl

/-- **Left restriction.**  A separation `CapySepCheck Γ C1 C2` restricts on the
    left to any single stable peak `cvar` atom of `C1`. -/
theorem CapySepCheck.restrict_left {s : Sig} {Γ : CapyCtx s} {C1 C2 : CapyCaptureSet s}
    (h : CapySepCheck Γ C1 C2) {a : Access} {c' : BVar s .cvar}
    (hmem : (CapyCaptureSet.cvar a c') ⊆ CapyCaptureSet.peaks Γ C1)
    (hstab : Γ.IsStableCVar c') :
    CapySepCheck Γ (CapyCaptureSet.cvar a c') C2 :=
  h.restrict_aux.2 hmem hstab Access.Le.refl

end CoreCapybara
