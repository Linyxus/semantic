import Semantic.CoreCapybara.LegacyCompilation.PeakCombinatorics
import Semantic.CoreCapybara.LegacyCompilation.ContextMorphism
import Semantic.CoreCapybara.LegacyCompilation.SepRestrict

/-! # AppPeaks: peaks correspondence for the arrow wrap-lock key set

Correspondence between the peaks/items of the compiled-function lock key set
`peakset ΓL Wsrc` (computed at the extended source context `ΓL`) and the peaks/items
over `Γ` of the interference footprint slice `U0`.
-/

namespace CoreCapybara

open CapyCaptureSet

/-- Local defeq-normalizers so `simp only` can close `∪`/`.union` and `∅`/`empty`
    mismatches produced by the `dropCVar`/`peaks`/`rename` equation lemmas. -/
private theorem cup_eq_union {s : Sig} {A B : CapyCaptureSet s} : A ∪ B = A.union B := rfl
private theorem emp_eq_empty {s : Sig} : (∅ : CapyCaptureSet s) = CapyCaptureSet.empty := rfl

/-- Dropping the freshly-inserted cvar binder undoes a single cvar-weakening. -/
theorem CapyCaptureSet.dropCVar_rename_succ {s : Sig} (X : CapyCaptureSet s) :
    (X.rename (Rename.succ (k := .cvar))).dropCVar = X := by
  induction X with
  | empty => rfl
  | union C1 C2 ih1 ih2 =>
    simp only [CapyCaptureSet.rename, CapyCaptureSet.dropCVar, ih1, ih2, cup_eq_union]
  | var m v =>
    cases v with
    | bound y => rfl
    | free n => rfl
  | cvar m c => rfl
  | pseudo_peak C ih => simp only [CapyCaptureSet.rename, CapyCaptureSet.dropCVar, ih]

/-- `dropCVar` commutes with peak-resolution across the freshly-pushed cvar binder. -/
theorem CapyCaptureSet.peaks_dropCVar {s : Sig} {Γ : CapyCtx s} {a : CapyAuthority}
    {cb : CapyCaptureBound s} {cs : CapyCaptureSet (s,C)} :
    CapyCaptureSet.peaks Γ cs.dropCVar
      = (CapyCaptureSet.peaks (Γ.push_cvar a cb) cs).dropCVar := by
  induction cs with
  | empty =>
    simp only [CapyCaptureSet.dropCVar, CapyCaptureSet.peaks]
  | union C1 C2 ih1 ih2 =>
    simp only [CapyCaptureSet.dropCVar, CapyCaptureSet.peaks,
      ih1, ih2, cup_eq_union]
  | cvar m c =>
    cases c with
    | here => simp only [CapyCaptureSet.dropCVar, CapyCaptureSet.peaks]
    | there c' => simp only [CapyCaptureSet.dropCVar, CapyCaptureSet.peaks]
  | var m v =>
    cases v with
    | bound y =>
      cases y with
      | there y' =>
        change CapyCaptureSet.peaks Γ (CapyCaptureSet.var m (Var.bound y'))
            = (CapyCaptureSet.peaks (Γ.push (CapyBinding.cvar a cb))
                ((CapyCaptureSet.var m (Var.bound y')).rename (Rename.succ (k := .cvar)))).dropCVar
        rw [CapyCaptureSet.peaks_rename_succ_eq, CapyCaptureSet.dropCVar_rename_succ]
    | free n =>
      simp only [CapyCaptureSet.dropCVar, CapyCaptureSet.peaks, emp_eq_empty]
  | pseudo_peak C ih =>
    simp only [CapyCaptureSet.dropCVar, CapyCaptureSet.peaks, ih]

/-- A cvar atom sits below a union iff it sits below one of the two arms. -/
theorem CapyCaptureSet.cvar_subset_union_inv {s : Sig} {a : Access} {c : BVar s .cvar}
    {C1 C2 : CapyCaptureSet s} (h : (CapyCaptureSet.cvar a c) ⊆ C1 ∪ C2) :
    (CapyCaptureSet.cvar a c) ⊆ C1 ∨ (CapyCaptureSet.cvar a c) ⊆ C2 := by
  cases h with
  | union_right_left h => exact Or.inl h
  | union_right_right h => exact Or.inr h

/-- Subset-inversion across a single cvar-weakening: a cvar atom below `X.rename succ`
    comes from a `.there`-shaped atom below `X`. -/
theorem CapyCaptureSet.cvar_subset_rename_succ_inv {s : Sig} {k0 : Kind} {a : Access}
    {c : BVar (s,,k0) .cvar} {X : CapyCaptureSet s}
    (h : (CapyCaptureSet.cvar a c) ⊆ X.rename Rename.succ) :
    ∃ c0 : BVar s .cvar, c = BVar.there c0 ∧ (CapyCaptureSet.cvar a c0) ⊆ X := by
  induction X with
  | empty => cases h
  | union C1 C2 ih1 ih2 =>
    rcases CapyCaptureSet.cvar_subset_union_inv h with h1 | h2
    · obtain ⟨c0, hc, hsub⟩ := ih1 h1
      exact ⟨c0, hc, CapyCaptureSet.Subset.union_right_left hsub⟩
    · obtain ⟨c0, hc, hsub⟩ := ih2 h2
      exact ⟨c0, hc, CapyCaptureSet.Subset.union_right_right hsub⟩
  | var m v => simp only [CapyCaptureSet.rename] at h; cases h
  | cvar m c'' =>
    simp only [CapyCaptureSet.rename, Rename.succ] at h
    cases h
    exact ⟨c'', rfl, CapyCaptureSet.Subset.refl⟩
  | pseudo_peak C ih => simp only [CapyCaptureSet.rename] at h; cases h

/-- Subset-inversion across a single cvar-weakening, for a `.there`-headed atom:
    it unshifts to its predecessor below `X`. -/
theorem CapyCaptureSet.cvar_there_subset_rename_succ_inv {s : Sig} {k0 : Kind} {a : Access}
    {d : BVar s .cvar} {X : CapyCaptureSet s}
    (h : (CapyCaptureSet.cvar a (BVar.there (k0 := k0) d)) ⊆ X.rename Rename.succ) :
    (CapyCaptureSet.cvar a d) ⊆ X := by
  obtain ⟨c0, hc0, hsub⟩ := CapyCaptureSet.cvar_subset_rename_succ_inv h
  have hd : d = c0 := by simp only [BVar.there.injEq] at hc0; exact hc0
  rw [hd]; exact hsub

/-- A `.there`-shaped cvar atom below `W` descends, after `dropCVar`, to its
    unshifted cvar atom. -/
theorem CapyCaptureSet.cvar_there_subset_dropCVar {s : Sig} {a : Access} {c' : BVar s .cvar}
    {W : CapyCaptureSet (s,C)} (h : (CapyCaptureSet.cvar a (.there c')) ⊆ W) :
    (CapyCaptureSet.cvar a c') ⊆ W.dropCVar := by
  induction W with
  | empty => cases h
  | union C1 C2 ih1 ih2 =>
    rcases CapyCaptureSet.cvar_subset_union_inv h with h1 | h2
    · exact CapyCaptureSet.Subset.union_right_left (ih1 h1)
    · exact CapyCaptureSet.Subset.union_right_right (ih2 h2)
  | cvar m c'' =>
    cases h
    simp only [CapyCaptureSet.dropCVar]
    exact CapyCaptureSet.Subset.refl
  | var m v => cases h
  | pseudo_peak C ih => cases h

end CoreCapybara

open CoreCapybara

namespace Compilation

/-- A `foldr`-union of `cvar a c` atoms is a subset of `Q` when each atom is. -/
theorem foldr_cvar_subset {s : Sig} {c : BVar s .cvar} {Q : CapyCaptureSet s}
    (L : List Access) (hL : ∀ a ∈ L, (CapyCaptureSet.cvar a c) ⊆ Q) :
    L.foldr (fun a acc => (CapyCaptureSet.cvar a c) ∪ acc) .empty ⊆ Q := by
  induction L with
  | nil => exact CapyCaptureSet.Subset.empty
  | cons a L' ih =>
    simp only [List.foldr_cons]
    exact CapyCaptureSet.Subset.union_left (hL a List.mem_cons_self)
      (ih (fun b hb => hL b (List.mem_cons_of_mem _ hb)))

/-- Inversion of a cvar atom below such a `foldr`: it matches the shared cvar `c`
    and its access mode is one of the folded list. -/
theorem cvar_subset_foldr_inv {s : Sig} {c d : BVar s .cvar} {a : Access}
    (L : List Access)
    (h : (CapyCaptureSet.cvar a d)
        ⊆ L.foldr (fun a acc => (CapyCaptureSet.cvar a c) ∪ acc) .empty) :
    d = c ∧ a ∈ L := by
  induction L with
  | nil => exact absurd h (by intro hh; cases hh)
  | cons a0 L' ih =>
    simp only [List.foldr_cons] at h
    rcases CapyCaptureSet.cvar_subset_union_inv h with h1 | h2
    · cases h1
      exact ⟨rfl, List.mem_cons_self⟩
    · obtain ⟨hd, hmem⟩ := ih h2
      exact ⟨hd, List.mem_cons_of_mem _ hmem⟩

/-- `peakItem P c` is a subset of `Q` when every occurrence of `c` in `P` maps into `Q`. -/
theorem peakItem_subset_of {s : Sig} {P : CapyPeakSet s} {c : BVar s .cvar} {Q : CapyCaptureSet s}
    (hmap : ∀ (a : Access), (CapyCaptureSet.cvar a c) ⊆ P.cs → (CapyCaptureSet.cvar a c) ⊆ Q) :
    peakItem P c ⊆ Q := by
  simp only [peakItem]
  apply foldr_cvar_subset
  intro a ha
  refine hmap a (PC.accessedAt_go_subset P.cs ?_)
  simpa only [accessedAt] using ha

/-- Inversion of a cvar atom below `peakItem P c`: it matches `c`, and `c` occurs
    in `P` at that access mode. -/
theorem cvar_subset_peakItem_inv {s : Sig} {P : CapyPeakSet s} {c d : BVar s .cvar} {a : Access}
    (h : (CapyCaptureSet.cvar a d) ⊆ peakItem P c) :
    d = c ∧ (CapyCaptureSet.cvar a c) ⊆ P.cs := by
  simp only [peakItem] at h
  obtain ⟨hd, hmem⟩ := cvar_subset_foldr_inv _ h
  refine ⟨hd, PC.accessedAt_go_subset P.cs ?_⟩
  simpa only [accessedAt] using hmem

section AppPeaks

variable {s : Sig} (Γ : CapyCtx s) (x : BVar s .var) (T1 : CapyTy .capt (s,C))

/-- The self-capture cvar binder inserted by the arrow wrap: `c <: ε`.  Uses
    `push_cvar_default` to match `CompilerCtx.consCVar` syntactically (so
    `ctxLockA.capyCtx = appΓL ctx.capyCtx x T1` holds definitionally at the use site);
    `push_cvar_default` is `push_cvar .access_only`. -/
abbrev appΓC : CapyCtx (s,C) := Γ.push_cvar_default (CapyCaptureBound.unbound .epsilon)

/-- The extended source context at which the function body's lock key set is
    computed: the self cvar `c`, then the value parameter of type `T1`. -/
abbrev appΓL : CapyCtx ((s,C),x) := (appΓC Γ).push_var T1

/-- The wrap-lock key set: the function's capture `{ε x}` weakened past the two
    binders, plus the value parameter `.here`. -/
abbrev appWsrc : CapyCaptureSet ((s,C),x) :=
  (((CapyCaptureSet.var (.M .epsilon) (.bound x)).rename Rename.succ).rename Rename.succ)
    ∪ CapyCaptureSet.var (.M .epsilon) (.bound .here)

/-- The interference footprint slice over `Γ`. -/
abbrev appU0 : CapyCaptureSet s :=
  (CapyCaptureSet.var (.M .epsilon) (.bound x)) ∪ T1.captureSet.dropCVar

/-- The `.here` arm of `peaksVarBound` at a `.var` binder (stated with the tail
    context abstract so the arm fires cleanly). -/
theorem CapyCaptureSet.peaksVarBound_here_var {s : Sig} {Γ : CapyCtx s} {T : CapyTy .capt s}
    {m : Access} :
    CapyCaptureSet.peaksVarBound (Γ.push (.var T)) m .here
      = ((CapyCaptureSet.peaks Γ T.captureSet).rename Rename.succ).applyAccess m := by
  simp only [CapyCaptureSet.peaksVarBound]

/-- Peaks peels two source weakenings (stated with the pushed binders abstract, so
    `peaks_rename_succ_eq` fires cleanly — cf. `CapyCaptureSet.peaks_lock_field_congr`). -/
theorem CapyCaptureSet.peaks_double_weaken {s : Sig} {Γ : CapyCtx s} {C : CapyCaptureSet s}
    {b1 : CapyBinding s .cvar} {b2 : CapyBinding (s,,Kind.cvar) .var} :
    CapyCaptureSet.peaks ((Γ.push b1).push b2) ((C.rename Rename.succ).rename Rename.succ)
      = ((CapyCaptureSet.peaks Γ C).rename Rename.succ).rename Rename.succ := by
  simp only [CapyCaptureSet.peaks_rename_succ_eq]

/-- The lock key set of the wrapped function unfolds into two summands: the
    self-capture atom's peaks (weakened past both binders) and the parameter type's
    peaks (weakened past one binder).  `applyAccess (.M .epsilon)` is the identity,
    so it is dropped from the parameter summand. -/
theorem appPeaks_unfold :
    CapyCaptureSet.peaks (appΓL Γ T1) (appWsrc x)
      = (((CapyCaptureSet.peaks Γ (.var (.M .epsilon) (.bound x))).rename Rename.succ).rename
          Rename.succ)
        ∪ ((CapyCaptureSet.peaks (appΓC Γ) T1.captureSet).rename Rename.succ) := by
  simp only [appWsrc, appΓL, appΓC, CapyCtx.push_var, CapyCtx.push_cvar_default, CapyCtx.push_cvar]
  rw [CapyCaptureSet.peaks_union]
  congr 1
  · exact CapyCaptureSet.peaks_double_weaken
  · have h := @CapyCaptureSet.peaksVarBound_here_var (s,C)
      (Γ.push (CapyBinding.cvar .access_only (CapyCaptureBound.unbound .epsilon))) T1 (.M .epsilon)
    rw [CapyCaptureSet.applyAccess_M, CapyCaptureSet.applyMut_epsilon] at h
    simp only [CapyCaptureSet.peaks]
    exact h

/-- Every capture variable of the extended sig `((s,C),x)` is one of the two peak
    shapes: the self-capture cvar `c` (`.there .here`) or a weakened `Γ`-cvar
    (`.there (.there c')`). -/
theorem appPeaks_cvar_shape (d : BVar ((s,C),x) .cvar) :
    d = .there .here ∨ ∃ c' : BVar s .cvar, d = .there (.there c') := by
  cases d with
  | there d' =>
    cases d' with
    | here => exact Or.inl rfl
    | there c' => exact Or.inr ⟨c', rfl⟩

/-- (a) A weakened `Γ`-cvar occurrence in the wrap-lock key set descends to an
    occurrence over `Γ` of the interference footprint slice `U0`. -/
theorem appPeaks_occ_there {a : Access} {c' : BVar s .cvar}
    (h : (CapyCaptureSet.cvar a (.there (.there c')))
        ⊆ CapyCaptureSet.peaks (appΓL Γ T1) (appWsrc x)) :
    (CapyCaptureSet.cvar a c') ⊆ CapyCaptureSet.peaks Γ (appU0 x T1) := by
  replace h := appPeaks_unfold Γ x T1 ▸ h
  simp only [appU0]
  rw [CapyCaptureSet.peaks_union]
  rcases CapyCaptureSet.cvar_subset_union_inv h with hA | hB
  · -- self-capture summand: two weakenings peel to `peaks Γ {x}`
    have hsub := CapyCaptureSet.cvar_there_subset_rename_succ_inv
      (CapyCaptureSet.cvar_there_subset_rename_succ_inv hA)
    exact CapyCaptureSet.Subset.union_right_left hsub
  · -- parameter-type summand: one weakening then `dropCVar` descent
    have hsub := CapyCaptureSet.cvar_there_subset_rename_succ_inv hB
    have hdrop := CapyCaptureSet.cvar_there_subset_dropCVar hsub
    refine CapyCaptureSet.Subset.union_right_right ?_
    rw [CapyCaptureSet.peaks_dropCVar (a := .access_only) (cb := CapyCaptureBound.unbound .epsilon)]
    exact hdrop

/-- (b) The self-capture cvar `c` (peak `.there .here`) occurs in the wrap-lock key
    set only from the parameter type's capture annotation. -/
theorem appPeaks_occ_c {a : Access}
    (h : (CapyCaptureSet.cvar a (.there .here)) ⊆ CapyCaptureSet.peaks (appΓL Γ T1) (appWsrc x)) :
    (CapyCaptureSet.cvar a .here) ⊆ CapyCaptureSet.peaks (appΓC Γ) T1.captureSet := by
  replace h := appPeaks_unfold Γ x T1 ▸ h
  rcases CapyCaptureSet.cvar_subset_union_inv h with hA | hB
  · -- the self-capture summand contributes only `.there (.there _)` shapes, never `c`
    have hmid := CapyCaptureSet.cvar_there_subset_rename_succ_inv hA
    obtain ⟨c0, hc0, _⟩ := CapyCaptureSet.cvar_subset_rename_succ_inv hmid
    exact absurd hc0 (by simp)
  · exact CapyCaptureSet.cvar_there_subset_rename_succ_inv hB

/-- (4) Stability of a weakened `Γ`-cvar peak in `ΓL` is exactly the stability of
    the underlying cvar in `Γ` (the two source weakenings preserve stability). -/
theorem appPeaks_stable_there {c' : BVar s .cvar} :
    Peak.IsStable (appΓL Γ T1) (Peak.cvar (.there (.there c'))) ↔ Γ.IsStableCVar c' := by
  have h1 : Peak.IsStable (appΓL Γ T1) (Peak.cvar (.there (.there c')))
          ↔ Peak.IsStable (appΓC Γ) (Peak.cvar (.there c')) :=
    Peak.IsStable.renamesTo_iff (p := Peak.cvar (.there c'))
      (CapyCtx.RenamesTo.weaken (CapyBinding.var T1))
  have h2 : Peak.IsStable (appΓC Γ) (Peak.cvar (.there c'))
          ↔ Peak.IsStable Γ (Peak.cvar c') :=
    Peak.IsStable.renamesTo_iff (p := Peak.cvar c')
      (CapyCtx.RenamesTo.weaken (CapyBinding.cvar .access_only (CapyCaptureBound.unbound .epsilon)))
  exact h1.trans h2

/-- (4) The self-capture cvar peak `c` (`.there .here`) is always stable in `ΓL`:
    it is bound `.unbound ε`. -/
theorem appPeaks_stable_c : Peak.IsStable (appΓL Γ T1) (Peak.cvar (.there .here)) := by
  have h1 : Peak.IsStable (appΓL Γ T1) (Peak.cvar (.there .here))
          ↔ Peak.IsStable (appΓC Γ) (Peak.cvar .here) :=
    Peak.IsStable.renamesTo_iff (p := Peak.cvar .here)
      (CapyCtx.RenamesTo.weaken (CapyBinding.var T1))
  rw [h1]
  change (appΓC Γ).IsStableCVar BVar.here
  exact Or.inr ⟨.epsilon, rfl⟩

/-- The extended context `ΓL` is pseudo-peak free when `Γ` and `T1` are. -/
theorem appΓL_noPseudo (hΓ : Γ.NoPseudoPeak) (hT1 : T1.NoPseudoPeak) :
    (appΓL Γ T1).NoPseudoPeak :=
  ⟨hΓ, hT1.captureSet⟩

/-- The wrap-lock key set is pseudo-peak free (unions of renamed var atoms). -/
theorem appWsrc_noPseudo : (appWsrc x).NoPseudoPeak :=
  CapyCaptureSet.NoPseudoPeak.union
    ((CapyCaptureSet.NoPseudoPeak.var.rename Rename.succ).rename Rename.succ)
    CapyCaptureSet.NoPseudoPeak.var

/-- (5) The compiled lock has no frozen (pseudo) peaks: `peakPseudos` is empty. -/
theorem appPeaks_noPseudo (hΓ : Γ.NoPseudoPeak) (hT1 : T1.NoPseudoPeak) :
    peakPseudos (CapyCaptureSet.peakset (appΓL Γ T1) (appWsrc x)) = [] := by
  have hpeaks : (CapyCaptureSet.peaks (appΓL Γ T1) (appWsrc x)).NoPseudoPeak :=
    CapyCaptureSet.peaks_noPseudoPeak (appΓL_noPseudo Γ T1 hΓ hT1) (appWsrc_noPseudo x)
  simp only [peakPseudos, CapyCaptureSet.peakset,
    PC.peakPseudos_go_nil_of_noPseudoPeak hpeaks, dedup]

/-- (7) The self-capture cvar `c` never occurs at `.drop` mode in an access-only
    parameter-type capture (via the `peaks`→`resourcePeaks` bridge). -/
theorem appPeaks_c_no_drop (hao : CapyCaptureSet.AccessOnly (appΓC Γ) T1.captureSet) {a : Access}
    (h : (CapyCaptureSet.cvar a .here) ⊆ CapyCaptureSet.peaks (appΓC Γ) T1.captureSet) :
    a ≠ .drop := by
  intro ha
  subst ha
  exact hao BVar.here
    (CapyCaptureSet.cvar_peaks_subset_resourcePeaks (appΓC Γ) T1.captureSet h)

/-- (8) Inventory of the stable peaks of the wrap-lock: each is either the
    self-capture cvar `c` (`.there .here`), or a weakened `Γ`-cvar
    (`.there (.there c')`) whose underlying `c'` is a stable peak of the footprint
    slice `U0` over `Γ`. -/
theorem appPeaks_mem_inventory (hΓ : Γ.NoPseudoPeak) (hT1 : T1.NoPseudoPeak)
    {p : Peak ((s,C),x)}
    (hp : p ∈ (peakList (CapyCaptureSet.peakset (appΓL Γ T1) (appWsrc x))).filter
        (fun q => decide (Peak.IsStable (appΓL Γ T1) q))) :
    p = Peak.cvar (.there .here) ∨
    ∃ c' : BVar s .cvar, p = Peak.cvar (.there (.there c')) ∧ Γ.IsStableCVar c' ∧
      Peak.cvar c' ∈ (peakList (CapyCaptureSet.peakset Γ (appU0 x T1))).filter
        (fun q => decide (Peak.IsStable Γ q)) := by
  rw [List.mem_filter] at hp
  obtain ⟨hmem, hstab⟩ := hp
  have hstab' : Peak.IsStable (appΓL Γ T1) p := of_decide_eq_true hstab
  -- no pseudo peaks, so `p` is a cvar peak
  have hpseudo := appPeaks_noPseudo Γ x T1 hΓ hT1
  simp only [peakList, hpseudo, List.map_nil, List.append_nil, List.mem_map] at hmem
  obtain ⟨d, hd, hpd⟩ := hmem
  subst hpd
  rcases appPeaks_cvar_shape d with hshape | ⟨c', hshape⟩
  · exact Or.inl (congrArg Peak.cvar hshape)
  · subst hshape
    refine Or.inr ⟨c', rfl, ?_, ?_⟩
    · exact (appPeaks_stable_there Γ T1).mp hstab'
    · have hΓstab : Γ.IsStableCVar c' := (appPeaks_stable_there Γ T1).mp hstab'
      obtain ⟨a, hocc⟩ := PC.peakCvars_occ hd
      have hoccU := appPeaks_occ_there Γ x T1 hocc
      have hcmem := PC.cvar_mem_peakCvars (P := CapyCaptureSet.peakset Γ (appU0 x T1)) hoccU
      refine List.mem_filter.mpr ⟨PC.cvar_mem_peakList hcmem, ?_⟩
      exact decide_eq_true_eq.mpr hΓstab

/-- (6) The lock item of a weakened `Γ`-cvar peak in `ΓL` is contained in the
    (doubly weakened) lock item of the underlying cvar over `Γ`'s footprint slice. -/
theorem appPeaks_item_there {c' : BVar s .cvar} :
    CapyCaptureSet.Subset
      (peakItem (CapyCaptureSet.peakset (appΓL Γ T1) (appWsrc x)) (.there (.there c')))
      (((peakItem (CapyCaptureSet.peakset Γ (appU0 x T1)) c').rename Rename.succ).rename
        Rename.succ) := by
  apply peakItem_subset_of
  intro a h
  have h1 := appPeaks_occ_there Γ x T1 h
  have h2 := PC.cvar_subset_peakItem (P := CapyCaptureSet.peakset Γ (appU0 x T1)) h1
  exact CapyCaptureSet.cvar_subset_rename_fwd (ρ := Rename.succ (k := .var))
    (CapyCaptureSet.cvar_subset_rename_fwd (ρ := Rename.succ (k := .cvar)) h2)

/-- (6) Every cvar atom of the self-capture peak's lock item is the self-capture
    cvar `c` (`.there .here`), whose occurrence descends to `T1`'s capture. -/
theorem appPeaks_item_c_atoms {a : Access} {d : BVar ((s,C),x) .cvar}
    (h : (CapyCaptureSet.cvar a d)
        ⊆ peakItem (CapyCaptureSet.peakset (appΓL Γ T1) (appWsrc x)) (.there .here)) :
    d = .there .here
      ∧ (CapyCaptureSet.cvar a .here) ⊆ CapyCaptureSet.peaks (appΓC Γ) T1.captureSet := by
  obtain ⟨hd, hocc⟩ := cvar_subset_peakItem_inv h
  exact ⟨hd, appPeaks_occ_c Γ x T1 hocc⟩

end AppPeaks

end Compilation
