import Semantic.CoreCapybara.LegacyCapybara.TypeSystem.Core

namespace CoreCapybara

/-!
# Use-set coverage of application interference (surface well-formedness)

At an application `x y` (subject typed at the self-refined arrow
`[c](x:T1)^{εx} → T2`), the separation obligations that compilation must
discharge — the `unwrap`'s lock items and the leaves of the `hsep` premise's
derivation — concern exactly the peaks of `D ∪ interfere_set(arrow)`.  The
covering-lock discipline threads an ambient covering of the *judgment
capture*'s peaks; this lemma bridges the two: the interference footprint's
peaks are already among the use-set `{εx} ∪ {εy}`'s peaks.

This is a property of **how surface types are formed** (user decision,
2026-07-02): a function's capture (`{εx}`, resolving through its stored type)
transitively covers its domain/codomain annotation peaks, and the
instantiation `D` is the argument's inferred capture, whose peaks resolve
within `{εy}`'s.  It is *not* derivable from the typing rules alone (a stored
arrow whose domain annotation mentions a capability the function never
captures is a counterexample), so it is stated here as the single assumed
surface fact, consumed by `CapyHasType.compile`'s `app` case.
-/

/-- `NoPseudoPeak` is preserved by any substitution whose capture-variable
    images are pseudo-peak free (term-variable images are always variables). -/
theorem CapyCaptureSet.NoPseudoPeak.subst_of {s1 s2 : Sig}
    {cs : CapyCaptureSet s1} {σ : CapySubst s1 s2} (h : cs.NoPseudoPeak)
    (hσ : ∀ c, (σ.cvar c).NoPseudoPeak) :
    (cs.subst σ).NoPseudoPeak := by
  induction h with
  | empty => exact CapyCaptureSet.NoPseudoPeak.empty
  | union _ _ ih1 ih2 => exact CapyCaptureSet.NoPseudoPeak.union ih1 ih2
  | cvar => exact (hσ _).applyAccess
  | var => exact CapyCaptureSet.NoPseudoPeak.var

/-- `dropCVar` preserves pseudo-peak freedom (structural). -/
theorem CapyCaptureSet.NoPseudoPeak.dropCVar {s : Sig}
    {cs : CapyCaptureSet (s,C)} (h : cs.NoPseudoPeak) :
    cs.dropCVar.NoPseudoPeak := by
  induction h with
  | empty => exact CapyCaptureSet.NoPseudoPeak.empty
  | union _ _ ih1 ih2 => exact CapyCaptureSet.NoPseudoPeak.union ih1 ih2
  | cvar =>
    rename_i c
    cases c with
    | here => exact CapyCaptureSet.NoPseudoPeak.empty
    | there c' => exact CapyCaptureSet.NoPseudoPeak.cvar
  | var =>
    rename_i x
    cases x with
    | bound b =>
      cases b with
      | there y => exact CapyCaptureSet.NoPseudoPeak.var
    | free n => exact CapyCaptureSet.NoPseudoPeak.var

/-- `dropTVar` preserves pseudo-peak freedom. -/
theorem CapyCaptureSet.NoPseudoPeak.dropTVar {s : Sig}
    {cs : CapyCaptureSet (s,X)} (h : cs.NoPseudoPeak) :
    cs.dropTVar.NoPseudoPeak :=
  h.subst_of (fun c => by
    cases c with
    | there c' =>
      simp only [CapySubst.openTVar]
      exact CapyCaptureSet.NoPseudoPeak.cvar)

/-- `dropVar` preserves pseudo-peak freedom (structural). -/
theorem CapyCaptureSet.NoPseudoPeak.dropVar {s : Sig}
    {cs : CapyCaptureSet (s,x)} (h : cs.NoPseudoPeak) :
    cs.dropVar.NoPseudoPeak := by
  induction h with
  | empty => exact CapyCaptureSet.NoPseudoPeak.empty
  | union _ _ ih1 ih2 => exact CapyCaptureSet.NoPseudoPeak.union ih1 ih2
  | cvar =>
    rename_i c
    cases c with
    | there c' => exact CapyCaptureSet.NoPseudoPeak.cvar
  | var =>
    rename_i x
    cases x with
    | bound b =>
      cases b with
      | here => exact CapyCaptureSet.NoPseudoPeak.empty
      | there y => exact CapyCaptureSet.NoPseudoPeak.var
    | free n => exact CapyCaptureSet.NoPseudoPeak.var

/-- A pseudo-peak-free type has a pseudo-peak-free interference footprint. -/
theorem CapyTy.NoPseudoPeak.interfere_set {sort : CapyTySort} {s : Sig}
    {T : CapyTy sort s} (h : T.NoPseudoPeak) :
    T.interfere_set.NoPseudoPeak := by
  match T with
  | .top | .tvar _ | .unit | .bool =>
    simp only [CapyTy.interfere_set]
    exact CapyCaptureSet.NoPseudoPeak.empty
  | .cap cs | .cell cs _ =>
    simp only [CapyTy.interfere_set]
    exact h
  | .arrow S Cf E =>
    simp only [CapyTy.interfere_set]
    exact CapyCaptureSet.NoPseudoPeak.union
      (CapyCaptureSet.NoPseudoPeak.union h.2.1
        (CapyCaptureSet.NoPseudoPeak.dropCVar h.1.captureSet))
      (CapyCaptureSet.NoPseudoPeak.dropVar h.2.2.interfere_set)
  | .poly _ Cf E =>
    simp only [CapyTy.interfere_set]
    exact CapyCaptureSet.NoPseudoPeak.union h.2.1
      (CapyCaptureSet.NoPseudoPeak.dropTVar h.2.2.interfere_set)
  | .cpoly _ Cf E =>
    simp only [CapyTy.interfere_set]
    exact CapyCaptureSet.NoPseudoPeak.union h.2.1
      (CapyCaptureSet.NoPseudoPeak.dropCVar h.2.2.interfere_set)
  | .exi T' =>
    simp only [CapyTy.interfere_set]
    exact CapyCaptureSet.NoPseudoPeak.dropCVar
      (CapyTy.NoPseudoPeak.interfere_set (T := T') h)
  | .typ T' =>
    simp only [CapyTy.interfere_set]
    exact CapyTy.NoPseudoPeak.interfere_set (T := T') h
termination_by sizeOf T

/-- `Subset` implies `CoveredBy` (subset is the mode-strict fragment of the
    covering relation). -/
theorem CapyCaptureSet.Subset.coveredBy {s : Sig} {C1 C2 : CapyCaptureSet s}
    (h : C1 ⊆ C2) : C1.CoveredBy C2 := by
  induction h with
  | refl => exact .refl'
  | empty => exact .empty
  | union_left _ _ ih1 ih2 => exact .union_left ih1 ih2
  | union_right_left _ ih => exact .union_right_left ih
  | union_right_right _ ih => exact .union_right_right ih

/-- Covering-restriction glue for the `unwrap` Satisfy discharge: adjoining a
    peak ATOM of `U` to `D` stays peak-below `D ∪ U`, so a covering of
    `D ∪ U`'s peaks restricts to `D ∪ {a c'}`'s. -/
theorem CapyCaptureSet.SubP.union_peak_atom {s : Sig} {Γ : CapyCtx s}
    {D U : CapyCaptureSet s} {a : Access} {c' : BVar s .cvar}
    (h : (CapyCaptureSet.cvar a c') ⊆ CapyCaptureSet.peaks Γ U) :
    CapyCaptureSet.SubP Γ (D ∪ .cvar a c') (D ∪ U) := by
  simp only [CapyCaptureSet.SubP, CapyCaptureSet.peaks_union]
  refine CapyCaptureSet.CoveredBy.union_left
    (CapyCaptureSet.CoveredBy.union_right_left CapyCaptureSet.CoveredBy.refl') ?_
  have hpk : CapyCaptureSet.peaks Γ (.cvar a c') = .cvar a c' := by
    rw [CapyCaptureSet.peaks]
  rw [hpk]
  exact CapyCaptureSet.CoveredBy.union_right_right h.coveredBy

/-- SURFACE-WF: the application's separation operands (`D` and the subject
    arrow's interference footprint) are peak-covered by the application's
    use-set `{εx} ∪ {εy}`. -/
theorem CapyHasType.app_use_covered {s : Sig} {Γ : CapyCtx s}
    {x y : Var .var s} {D : CapyCaptureSet s}
    {T1 : CapyTy .capt (s,C)} {T2 : CapyTy .exi (s,x)}
    (hx : CapyHasType (.var (.M .epsilon) x) Γ (.var x)
      (.typ (.arrow T1 (.var (.M .epsilon) x) T2)))
    (hy : CapyHasType (.var (.M .epsilon) y) Γ (.var y)
      (.typ (T1.subst (CapySubst.openCVar D)))) :
    CapyCaptureSet.SubP Γ
      (D ∪ (CapyTy.arrow T1 (.var (.M .epsilon) x) T2).interfere_set)
      (.var (.M .epsilon) x ∪ .var (.M .epsilon) y) := by
  sorry

end CoreCapybara
