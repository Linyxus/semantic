import Semantic.CoreCapybara.Denotation.Core
import Semantic.CoreCapybara.Denotation.Rebind
namespace CoreCapybara

/-- Interpret a variable in an environment to get its free variable index. -/
def interp_var (env : TypeEnv s) (x : Var .var s) : Nat :=
  match x with
  | .free n => n
  | .bound x => (env.lookup_var x).1

/-! ### Droppable-peak machinery for transporting `DropSepIn` along `Retype`

`DropSepIn` selects pairs of distinct `.can_drop` capture variables peaked in
a budget. To transport it along a substitution we factor budgets through
their computed peaks (`compute_peaks` is idempotent), and require of a
`Retype` a pairwise, capability-preserving correspondence between droppable
peaks on the two sides (`dpeak_fwd`/`dpeak_back`), plus stability of peak
membership under pre-computing peaks (`peaks`). -/

/-- `compute_peaks` is the identity on peaks-only capture sets. -/
theorem compute_peaks_peaksOnly_fixed {env : TypeEnv s} {P : CaptureSet s}
    (h : P.PeaksOnly) : compute_peaks env P = P := by
  induction h with
  | empty => rfl
  | union _ _ ih1 ih2 =>
    change (compute_peaks env _).union (compute_peaks env _) = _
    rw [ih1, ih2]
  | cvar => rfl

theorem compute_peaks_idem {env : TypeEnv s} (C : CaptureSet s) :
    compute_peaks env (compute_peaks env C) = compute_peaks env C :=
  compute_peaks_peaksOnly_fixed (compute_peaks_is_peak env C)

/-- `compute_peaks` commutes with `applyRO`. -/
theorem compute_peaks_applyRO {env : TypeEnv s} {C : CaptureSet s} :
    compute_peaks env C.applyRO = (compute_peaks env C).applyRO := by
  induction C with
  | empty => rfl
  | union C1 C2 ih1 ih2 =>
    change (compute_peaks env _).union (compute_peaks env _) = _
    rw [ih1, ih2]
    rfl
  | var m x =>
    cases x with
    | free n => rfl
    | bound b =>
      change (env.lookup_var b).2.cs.applyAccess m.applyRO
        = ((env.lookup_var b).2.cs.applyAccess m).applyRO
      rw [CaptureSet.applyAccess_applyRO]
  | cvar m c => rfl

/-- `compute_peaks` commutes with `applyDrop`. -/
theorem compute_peaks_applyDrop {env : TypeEnv s} {C : CaptureSet s} :
    compute_peaks env C.applyDrop = (compute_peaks env C).applyDrop := by
  induction C with
  | empty => rfl
  | union C1 C2 ih1 ih2 =>
    change (compute_peaks env _).union (compute_peaks env _) = _
    rw [ih1, ih2]
    rfl
  | var m x =>
    cases x with
    | free n => rfl
    | bound b =>
      change (env.lookup_var b).2.cs.applyDrop
        = ((env.lookup_var b).2.cs.applyAccess m).applyDrop
      rw [CaptureSet.applyAccess_applyDrop]
  | cvar m c => rfl

/-- `compute_peaks` commutes with `applyAccess`. -/
theorem compute_peaks_applyAccess {env : TypeEnv s} {C : CaptureSet s} {a : Access} :
    compute_peaks env (C.applyAccess a) = (compute_peaks env C).applyAccess a := by
  cases a with
  | M m =>
    cases m with
    | epsilon => rfl
    | ro => exact compute_peaks_applyRO
  | drop => exact compute_peaks_applyDrop

lemma subst_lift_eq_subst_rename
    {k : Kind} (cs0 : CaptureSet s1) (σ : Subst s1 s2) :
    (cs0.rename (Rename.succ (k := k))).subst (σ.lift (k := k)) =
      (cs0.subst σ).rename (Rename.succ (k := k)) := by
  induction cs0 with
  | empty => rfl
  | union cs1 cs2 ih1 ih2 =>
    change CaptureSet.subst (CaptureSet.union _ _) _ = _
    rw [show (CaptureSet.union (cs1.rename Rename.succ) (cs2.rename Rename.succ)).subst
           (σ.lift (k := k))
         = ((cs1.rename Rename.succ).subst σ.lift).union
           ((cs2.rename Rename.succ).subst σ.lift) from rfl]
    rw [ih1, ih2]
    rfl
  | var m x =>
    cases x with
    | free n => rfl
    | bound x => rfl
  | cvar m c =>
    change ((CaptureSet.cvar m c).rename (Rename.succ (k := k))).subst σ.lift =
      ((CaptureSet.cvar m c).subst σ).rename (Rename.succ (k := k))
    change CaptureSet.applyAccess m ((σ.cvar c).rename Rename.succ) =
      ((σ.cvar c).applyAccess m).rename Rename.succ
    exact CaptureSet.applyAccess_rename.symm

/-- A variable atom at mode `m` is the `applyAccess` image of the same atom
at the neutral mode. -/
theorem CaptureSet.var_applyAccess {m : Access} {w : Var .var s} :
    (CaptureSet.var (.M .epsilon) w).applyAccess m = CaptureSet.var m w := by
  cases m with
  | M mu => cases mu <;> rfl
  | drop => rfl

/-- Substitution is monotone with respect to the syntactic subset relation. -/
theorem CaptureSet.Subset.subst {C1 C2 : CaptureSet s1} {σ : Subst s1 s2}
    (h : C1 ⊆ C2) : C1.subst σ ⊆ C2.subst σ := by
  induction h with
  | refl => exact .refl
  | empty => exact .empty
  | union_left _ _ ih1 ih2 => exact .union_left ih1 ih2
  | union_right_left _ ih => exact .union_right_left ih
  | union_right_right _ ih => exact .union_right_right ih

/-- Peak computation is monotone with respect to the syntactic subset
relation. -/
theorem compute_peaks_subset_monotone {env : TypeEnv s} {C1 C2 : CaptureSet s}
    (h : C1 ⊆ C2) : compute_peaks env C1 ⊆ compute_peaks env C2 := by
  induction h with
  | refl => exact .refl
  | empty => exact .empty
  | union_left _ _ ih1 ih2 => exact .union_left ih1 ih2
  | union_right_left _ ih => exact .union_right_left ih
  | union_right_right _ ih => exact .union_right_right ih

/-- `c` occurs, at some access mode, among the computed peaks of `C`. -/
def TypeEnv.HasPeak (env : TypeEnv s) (C : CaptureSet s) (c : BVar s .cvar) : Prop :=
  ∃ a, (CaptureSet.cvar a c) ⊆ compute_peaks env C

/-- A droppable peak of a budget: a `.can_drop`-authority capture variable
among the budget's computed peaks. -/
def TypeEnv.HasDroppablePeak (env : TypeEnv s) (C : CaptureSet s) (c : BVar s .cvar) : Prop :=
  env.lookup_cvar_auth c = .can_drop ∧ env.HasPeak C c

theorem TypeEnv.HasPeak.of_peaks_eq {env : TypeEnv s} {C1 C2 : CaptureSet s}
    {c : BVar s .cvar}
    (heq : compute_peaks env C1 = compute_peaks env C2) :
    env.HasPeak C1 c ↔ env.HasPeak C2 c := by
  unfold TypeEnv.HasPeak
  rw [heq]

theorem TypeEnv.HasPeak.not_empty {env : TypeEnv s} {c : BVar s .cvar} :
    ¬ env.HasPeak .empty c := by
  rintro ⟨a, h⟩
  exact CaptureSet.cvar_not_subset_empty h

theorem TypeEnv.HasPeak.not_var_free {env : TypeEnv s} {c : BVar s .cvar}
    {m : Access} {n : Nat} :
    ¬ env.HasPeak (.var m (.free n)) c := by
  rintro ⟨a, h⟩
  exact CaptureSet.cvar_not_subset_empty h

theorem TypeEnv.HasPeak.union_iff {env : TypeEnv s} {C1 C2 : CaptureSet s}
    {c : BVar s .cvar} :
    env.HasPeak (C1.union C2) c ↔ env.HasPeak C1 c ∨ env.HasPeak C2 c := by
  constructor
  · rintro ⟨a, h⟩
    rcases CaptureSet.cvar_subset_union_inv h with h' | h'
    · exact .inl ⟨a, h'⟩
    · exact .inr ⟨a, h'⟩
  · rintro (⟨a, h⟩ | ⟨a, h⟩)
    · exact ⟨a, .union_right_left h⟩
    · exact ⟨a, .union_right_right h⟩

theorem TypeEnv.HasPeak.cvar_iff {env : TypeEnv s} {c c' : BVar s .cvar}
    {m : Access} :
    env.HasPeak (.cvar m c') c ↔ c = c' := by
  constructor
  · rintro ⟨a, h⟩
    exact (CaptureSet.cvar_subset_cvar_inv h).2
  · rintro rfl
    exact ⟨m, .refl⟩

/-- Peak membership is insensitive to `applyAccess` on the budget. -/
theorem TypeEnv.HasPeak.applyAccess_iff {env : TypeEnv s} {C : CaptureSet s}
    {a : Access} {c : BVar s .cvar} :
    env.HasPeak (C.applyAccess a) c ↔ env.HasPeak C c := by
  unfold TypeEnv.HasPeak
  rw [compute_peaks_applyAccess]
  constructor
  · rintro ⟨a', h⟩
    exact CaptureSet.cvar_subset_applyAccess_inv h
  · rintro ⟨a', h⟩
    cases a with
    | M m => exact CaptureSet.cvar_subset_applyMut_fwd m h
    | drop => exact ⟨.drop, CaptureSet.cvar_subset_applyDrop_fwd h⟩

theorem TypeEnv.HasDroppablePeak.applyAccess_iff {env : TypeEnv s} {C : CaptureSet s}
    {a : Access} {c : BVar s .cvar} :
    env.HasDroppablePeak (C.applyAccess a) c ↔ env.HasDroppablePeak C c :=
  and_congr Iff.rfl TypeEnv.HasPeak.applyAccess_iff

/-- Every droppable peak of a substituted peaks-only budget reflects through
one of the budget's capture-variable atoms. -/
theorem TypeEnv.HasDroppablePeak.subst_peaksOnly_inv {σ : Subst s1 s2} {env2 : TypeEnv s2}
    {P : CaptureSet s1} (hP : P.PeaksOnly) {d : BVar s2 .cvar}
    (h : TypeEnv.HasDroppablePeak env2 (P.subst σ) d) :
    ∃ (c : BVar s1 .cvar) (m : Access),
      (CaptureSet.cvar m c) ⊆ P ∧ TypeEnv.HasDroppablePeak env2 (σ.cvar c) d := by
  obtain ⟨hauth, hp⟩ := h
  revert hp
  induction hP with
  | empty =>
    intro hp
    exact absurd hp TypeEnv.HasPeak.not_empty
  | union _ _ ih1 ih2 =>
    intro hp
    rcases TypeEnv.HasPeak.union_iff.mp hp with hp' | hp'
    · obtain ⟨c, m, hsub, hd⟩ := ih1 hp'
      exact ⟨c, m, .union_right_left hsub, hd⟩
    · obtain ⟨c, m, hsub, hd⟩ := ih2 hp'
      exact ⟨c, m, .union_right_right hsub, hd⟩
  | cvar =>
    intro hp
    rename_i m c
    exact ⟨c, m, .refl, hauth, TypeEnv.HasPeak.applyAccess_iff.mp hp⟩

/-- Conversely, a droppable peak of the image of an atom of a budget is a
droppable peak of the substituted budget. -/
theorem TypeEnv.HasDroppablePeak.subst_of_atom {σ : Subst s1 s2} {env2 : TypeEnv s2}
    {P : CaptureSet s1} {c : BVar s1 .cvar} {m : Access}
    (hsub : (CaptureSet.cvar m c) ⊆ P) {d : BVar s2 .cvar}
    (hd : TypeEnv.HasDroppablePeak env2 (σ.cvar c) d) :
    TypeEnv.HasDroppablePeak env2 (P.subst σ) d := by
  obtain ⟨a, hp⟩ := (TypeEnv.HasDroppablePeak.applyAccess_iff (a := m)).mpr hd |>.2
  exact ⟨hd.1, a,
    CaptureSet.Subset.trans hp (compute_peaks_subset_monotone hsub.subst)⟩

/-- Peak membership transports along any environment rebinding. -/
theorem Rebind.peaks_at {env1 : TypeEnv s1} {f : Rename s1 s2} {env2 : TypeEnv s2}
    (ρ : Rebind env1 f env2) (cs : CaptureSet s1) (c : BVar s1 .cvar) :
    env1.HasPeak cs c ↔ env2.HasPeak (cs.rename f) (f.var c) := by
  unfold TypeEnv.HasPeak
  rw [← rebind_compute_peaks ρ]
  constructor
  · rintro ⟨a, h⟩
    exact ⟨a, h.rename'⟩
  · rintro ⟨a, h⟩
    obtain ⟨c', hfc, h'⟩ := (compute_peaks_is_peak env1 cs).cvar_subset_rename_inv h
    cases ρ.cvar_injective c' c hfc
    exact ⟨a, h'⟩

/-- Every peak of a renamed budget is the image of a peak. -/
theorem Rebind.peaks_at_inv {env1 : TypeEnv s1} {f : Rename s1 s2} {env2 : TypeEnv s2}
    (ρ : Rebind env1 f env2) (cs : CaptureSet s1) (d : BVar s2 .cvar)
    (h : env2.HasPeak (cs.rename f) d) :
    ∃ c, f.var c = d ∧ env1.HasPeak cs c := by
  obtain ⟨a, h⟩ := h
  rw [← rebind_compute_peaks ρ] at h
  obtain ⟨c', hfc, h'⟩ := (compute_peaks_is_peak env1 cs).cvar_subset_rename_inv h
  exact ⟨c', hfc, a, h'⟩

/-- Droppable peaks transport along any environment rebinding. -/
theorem Rebind.has_droppable_peak {env1 : TypeEnv s1} {f : Rename s1 s2} {env2 : TypeEnv s2}
    (ρ : Rebind env1 f env2) (cs : CaptureSet s1) (c : BVar s1 .cvar) :
    env1.HasDroppablePeak cs c ↔ env2.HasDroppablePeak (cs.rename f) (f.var c) := by
  unfold TypeEnv.HasDroppablePeak
  rw [ρ.cvar_auth c]
  exact and_congr Iff.rfl (ρ.peaks_at cs c)

theorem Rebind.has_droppable_peak_inv {env1 : TypeEnv s1} {f : Rename s1 s2} {env2 : TypeEnv s2}
    (ρ : Rebind env1 f env2) (cs : CaptureSet s1) (d : BVar s2 .cvar)
    (h : env2.HasDroppablePeak (cs.rename f) d) :
    ∃ c, f.var c = d ∧ env1.HasDroppablePeak cs c := by
  obtain ⟨hauth, hp⟩ := h
  obtain ⟨c, hfc, hp'⟩ := ρ.peaks_at_inv cs d hp
  subst hfc
  rw [← ρ.cvar_auth c] at hauth
  exact ⟨c, rfl, hauth, hp'⟩

/-- Over a non-capture binder, every peaks-only capture set is the weakening
of a peaks-only capture set of the base signature. -/
theorem CaptureSet.PeaksOnly.unrename {k : Kind} (hk : k ≠ .cvar)
    {P : CaptureSet (s,,k)} (h : P.PeaksOnly) :
    ∃ Q : CaptureSet s, Q.PeaksOnly ∧ Q.rename (Rename.succ (k := k)) = P := by
  induction h with
  | empty => exact ⟨.empty, .empty, rfl⟩
  | union _ _ ih1 ih2 =>
    obtain ⟨Q1, h1, rfl⟩ := ih1
    obtain ⟨Q2, h2, rfl⟩ := ih2
    exact ⟨Q1.union Q2, .union h1 h2, rfl⟩
  | cvar =>
    rename_i m c
    cases c with
    | here => exact absurd rfl hk
    | there c0 => exact ⟨.cvar m c0, .cvar, rfl⟩

theorem TypeEnv.HasPeak.not_of_isEmpty {env : TypeEnv s} {C : CaptureSet s}
    {c : BVar s .cvar} (h : C.IsEmpty) : ¬ env.HasPeak C c := by
  induction h with
  | empty => exact TypeEnv.HasPeak.not_empty
  | union _ _ ih1 ih2 =>
    intro hp
    rcases TypeEnv.HasPeak.union_iff.mp hp with hp | hp
    · exact ih1 hp
    · exact ih2 hp

/-- Peak membership of a substituted type's capture set agrees with that of
the substituted capture set (they agree syntactically except for type
variables, whose capture sets are empty on both sides). -/
theorem TypeEnv.HasPeak.ty_captureSet_subst {T : Ty .capt s1} {σ : Subst s1 s2}
    {env : TypeEnv s2} {d : BVar s2 .cvar} :
    env.HasPeak ((T.subst σ).captureSet) d ↔ env.HasPeak (T.captureSet.subst σ) d := by
  cases T with
  | tvar X =>
    constructor
    · intro h
      exact absurd h (TypeEnv.HasPeak.not_of_isEmpty (σ.tvar X).p)
    · intro h
      exact absurd h TypeEnv.HasPeak.not_empty
  | top => exact Iff.rfl
  | unit => exact Iff.rfl
  | bool => exact Iff.rfl
  | arrow T1 _ cs T2 => exact Iff.rfl
  | poly T1 _ cs T2 => exact Iff.rfl
  | cpoly cb _ cs T => exact Iff.rfl
  | modal _ cs Ψ T => exact Iff.rfl
  | cap cs => exact Iff.rfl
  | cell cs => exact Iff.rfl
  | reader cs => exact Iff.rfl

structure Retype (env1 : TypeEnv s1) (σ : Subst s1 s2) (env2 : TypeEnv s2) (D : PeakSet s1) where
  var :
    ∀ (x : BVar s1 .var),
      (env1.lookup_var x).1 = interp_var env2 (σ.var x)

  tvar :
    ∀ (X : BVar s1 .tvar),
      env1.lookup_tvar X ≈ Ty.val_denot env2 (σ.tvar X).core

  cvar :
    ∀ (C : BVar s1 .cvar),
      (env1.lookup_cvar C).1 = (σ.cvar C).subst (Subst.from_TypeEnv env2)

  /-- Per-variable peak correspondence: the peaks of a substituted variable
  agree, as membership, with the peaks of the substitution of the variable's
  stored peak set. -/
  var_peaks :
    ∀ (b : BVar s1 .var) (d : BVar s2 .cvar),
      env2.HasPeak (.var (.M .epsilon) (σ.var b)) d ↔
      env2.HasPeak ((env1.lookup_var b).2.cs.subst σ) d

  /-- Backward droppable-peak transport at a capture variable: a droppable
  peak of the image of `c` reflects to droppability of `c`, with equal
  capability set. -/
  dpeak_cvar_back :
    ∀ (c : BVar s1 .cvar) (d : BVar s2 .cvar),
      TypeEnv.HasDroppablePeak env2 (σ.cvar c) d →
      env1.lookup_cvar_auth c = .can_drop ∧
      (env1.lookup_cvar c).2 = (env2.lookup_cvar d).2

  /-- The image of a capture variable has at most one droppable peak. -/
  dpeak_cvar_unique :
    ∀ (c : BVar s1 .cvar) (d1 d2 : BVar s2 .cvar),
      TypeEnv.HasDroppablePeak env2 (σ.cvar c) d1 →
      TypeEnv.HasDroppablePeak env2 (σ.cvar c) d2 → d1 = d2

  /-- Forward droppable-peak transport at a capture variable. -/
  dpeak_cvar_fwd :
    ∀ (c : BVar s1 .cvar),
      env1.lookup_cvar_auth c = .can_drop →
      ∃ d, TypeEnv.HasDroppablePeak env2 (σ.cvar c) d ∧
        (env2.lookup_cvar d).2 = (env1.lookup_cvar c).2

  /-- Distinct capture variables have distinct droppable peaks. -/
  dpeak_cvar_inj :
    ∀ (c1 c2 : BVar s1 .cvar) (d : BVar s2 .cvar),
      TypeEnv.HasDroppablePeak env2 (σ.cvar c1) d →
      TypeEnv.HasDroppablePeak env2 (σ.cvar c2) d → c1 = c2

/-- Peak membership of a substituted budget only depends on the source budget
through its computed peaks. Derived from the `var_peaks` field. -/
theorem Retype.peaks
    {s1 s2 : Sig} {env1 : TypeEnv s1} {σ : Subst s1 s2} {env2 : TypeEnv s2} {D : PeakSet s1}
    (ρ : Retype env1 σ env2 D) (d : BVar s2 .cvar) (cs : CaptureSet s1) :
    env2.HasPeak (cs.subst σ) d ↔
    env2.HasPeak ((compute_peaks env1 cs).subst σ) d := by
  induction cs with
  | empty => exact Iff.rfl
  | union cs1 cs2 ih1 ih2 =>
    refine Iff.trans TypeEnv.HasPeak.union_iff ?_
    exact Iff.trans (or_congr ih1 ih2) TypeEnv.HasPeak.union_iff.symm
  | cvar m c => exact Iff.rfl
  | var m x =>
    cases x with
    | free n =>
      constructor
      · intro h
        exact absurd h TypeEnv.HasPeak.not_var_free
      · intro h
        exact absurd h TypeEnv.HasPeak.not_empty
    | bound b =>
      have hl : (CaptureSet.var m (Var.bound b)).subst σ
          = (CaptureSet.var (.M .epsilon) (σ.var b)).applyAccess m := by
        rw [CaptureSet.var_applyAccess]
        rfl
      have hr : (compute_peaks env1 (CaptureSet.var m (Var.bound b))).subst σ
          = ((env1.lookup_var b).2.cs.subst σ).applyAccess m := by
        change ((env1.lookup_var b).2.cs.applyAccess m).subst σ = _
        rw [CaptureSet.applyAccess_subst]
      rw [hl, hr]
      refine Iff.trans TypeEnv.HasPeak.applyAccess_iff ?_
      exact Iff.trans (ρ.var_peaks b d) TypeEnv.HasPeak.applyAccess_iff.symm

/-- Backward droppable-peak transport for peaks-only budgets: droppable peaks
of the substituted budget are covered, pairwise-injectively and with equal
capability sets, by droppable peaks of the source budget. -/
theorem Retype.dpeak_back
    {s1 s2 : Sig} {env1 : TypeEnv s1} {σ : Subst s1 s2} {env2 : TypeEnv s2} {D : PeakSet s1}
    (ρ : Retype env1 σ env2 D)
    (P : CaptureSet s1) (hP : P.PeaksOnly) (d1 d2 : BVar s2 .cvar)
    (h1 : TypeEnv.HasDroppablePeak env2 (P.subst σ) d1)
    (h2 : TypeEnv.HasDroppablePeak env2 (P.subst σ) d2) :
    ∃ c1 c2,
      (d1 ≠ d2 → c1 ≠ c2) ∧
      TypeEnv.HasDroppablePeak env1 P c1 ∧ TypeEnv.HasDroppablePeak env1 P c2 ∧
      (env1.lookup_cvar c1).2 = (env2.lookup_cvar d1).2 ∧
      (env1.lookup_cvar c2).2 = (env2.lookup_cvar d2).2 := by
  obtain ⟨c1, m1, hs1, hd1⟩ := TypeEnv.HasDroppablePeak.subst_peaksOnly_inv hP h1
  obtain ⟨c2, m2, hs2, hd2⟩ := TypeEnv.HasDroppablePeak.subst_peaksOnly_inv hP h2
  obtain ⟨hauth1, hcap1⟩ := ρ.dpeak_cvar_back c1 d1 hd1
  obtain ⟨hauth2, hcap2⟩ := ρ.dpeak_cvar_back c2 d2 hd2
  refine ⟨c1, c2, ?_,
    ⟨hauth1, m1, by rw [compute_peaks_peaksOnly_fixed hP]; exact hs1⟩,
    ⟨hauth2, m2, by rw [compute_peaks_peaksOnly_fixed hP]; exact hs2⟩,
    hcap1, hcap2⟩
  intro hne heq
  subst heq
  exact hne (ρ.dpeak_cvar_unique c1 d1 d2 hd1 hd2)

/-- Forward droppable-peak transport for peaks-only budgets. -/
theorem Retype.dpeak_fwd
    {s1 s2 : Sig} {env1 : TypeEnv s1} {σ : Subst s1 s2} {env2 : TypeEnv s2} {D : PeakSet s1}
    (ρ : Retype env1 σ env2 D)
    (P : CaptureSet s1) (hP : P.PeaksOnly) (c1 c2 : BVar s1 .cvar)
    (h1 : TypeEnv.HasDroppablePeak env1 P c1)
    (h2 : TypeEnv.HasDroppablePeak env1 P c2) :
    ∃ d1 d2,
      (c1 ≠ c2 → d1 ≠ d2) ∧
      TypeEnv.HasDroppablePeak env2 (P.subst σ) d1 ∧ TypeEnv.HasDroppablePeak env2 (P.subst σ) d2 ∧
      (env2.lookup_cvar d1).2 = (env1.lookup_cvar c1).2 ∧
      (env2.lookup_cvar d2).2 = (env1.lookup_cvar c2).2 := by
  obtain ⟨hauth1, a1, hp1⟩ := h1
  obtain ⟨hauth2, a2, hp2⟩ := h2
  rw [compute_peaks_peaksOnly_fixed hP] at hp1 hp2
  obtain ⟨d1, hd1, hcap1⟩ := ρ.dpeak_cvar_fwd c1 hauth1
  obtain ⟨d2, hd2, hcap2⟩ := ρ.dpeak_cvar_fwd c2 hauth2
  refine ⟨d1, d2, ?_,
    TypeEnv.HasDroppablePeak.subst_of_atom hp1 hd1,
    TypeEnv.HasDroppablePeak.subst_of_atom hp2 hd2,
    hcap1, hcap2⟩
  intro hne heq
  subst heq
  exact hne (ρ.dpeak_cvar_inj c1 c2 d1 hd1 hd2)

/-- The environment-separation invariant transports along any `Retype`:
budgets reduce to their peaks, and the `dpeak` fields provide a pairwise,
capability-preserving droppable-peak correspondence. -/
theorem Retype.dsep
    {s1 s2 : Sig} {env1 : TypeEnv s1} {σ : Subst s1 s2} {env2 : TypeEnv s2} {D : PeakSet s1}
    (ρ : Retype env1 σ env2 D) (cs : CaptureSet s1) :
    TypeEnv.DropSepIn env1 cs ↔ TypeEnv.DropSepIn env2 (cs.subst σ) := by
  constructor
  · intro h
    apply TypeEnv.DropSepIn.of_pairs
    intro d1 d2 a1 a2 hne hauth1 hauth2 hp1 hp2
    obtain ⟨c1, c2, hne', hc1, hc2, hcap1, hcap2⟩ :=
      ρ.dpeak_back (compute_peaks env1 cs) (compute_peaks_is_peak env1 cs) d1 d2
        ⟨hauth1, (ρ.peaks d1 cs).mp ⟨a1, hp1⟩⟩
        ⟨hauth2, (ρ.peaks d2 cs).mp ⟨a2, hp2⟩⟩
    obtain ⟨hauth1', a1', hpc1⟩ := hc1
    obtain ⟨hauth2', a2', hpc2⟩ := hc2
    rw [compute_peaks_idem] at hpc1 hpc2
    rw [← hcap1, ← hcap2]
    exact h.pairs c1 c2 a1' a2' (hne' hne) hauth1' hauth2' hpc1 hpc2
  · intro h
    apply TypeEnv.DropSepIn.of_pairs
    intro c1 c2 a1 a2 hne hauth1 hauth2 hp1 hp2
    obtain ⟨d1, d2, hne', hd1, hd2, hcap1, hcap2⟩ :=
      ρ.dpeak_fwd (compute_peaks env1 cs) (compute_peaks_is_peak env1 cs) c1 c2
        ⟨hauth1, a1, by rw [compute_peaks_idem]; exact hp1⟩
        ⟨hauth2, a2, by rw [compute_peaks_idem]; exact hp2⟩
    obtain ⟨hauth1', hpa1⟩ := hd1
    obtain ⟨hauth2', hpa2⟩ := hd2
    obtain ⟨a1', hp1'⟩ := (ρ.peaks d1 cs).mpr hpa1
    obtain ⟨a2', hp2'⟩ := (ρ.peaks d2 cs).mpr hpa2
    rw [← hcap1, ← hcap2]
    exact h.pairs d1 d2 a1' a2' (hne' hne) hauth1' hauth2' hp1' hp2'

/-- The peak-membership hypothesis needed to lift a `Retype` under a value
binder, when the two stored peak sets are the computed peaks of an argument
type and of its substitution (as in the arrow case of `val_denot`). -/
theorem Retype.lift_hps
    {s1 s2 : Sig} {env1 : TypeEnv s1} {σ : Subst s1 s2} {env2 : TypeEnv s2} {D : PeakSet s1}
    (ρ : Retype env1 σ env2 D) (T1 : Ty .capt s1) :
    ∀ (d : BVar s2 .cvar),
      env2.HasPeak (compute_peakset env2 (T1.subst σ).captureSet).cs d ↔
      env2.HasPeak ((compute_peakset env1 T1.captureSet).cs.subst σ) d := by
  intro d
  refine Iff.trans (TypeEnv.HasPeak.of_peaks_eq (compute_peaks_idem _)) ?_
  exact Iff.trans TypeEnv.HasPeak.ty_captureSet_subst (ρ.peaks d T1.captureSet)

lemma weaken_interp_var {x : Var .var s} {ps : PeakSet s} :
  interp_var env x = interp_var (env.extend_var n ps) (x.rename Rename.succ) := by
  cases x <;> rfl

lemma tweaken_interp_var {x : Var .var s} :
  interp_var env x = interp_var (env.extend_tvar d) (x.rename Rename.succ) := by
  cases x <;> rfl

lemma cweaken_interp_var {cs : CaptureSet {}} {cap : CapabilitySet} {a : Authority}
  {x : Var .var s} :
  interp_var env x = interp_var (env.extend_cvar cs cap a) (x.rename Rename.succ) := by
  cases x <;> rfl

theorem Retype.liftVar
  {s1 s2 : Sig} {env1 : TypeEnv s1} {σ : Subst s1 s2} {env2 : TypeEnv s2} {D : PeakSet s1}
  {x : Nat} {ps1 : PeakSet s1} {ps2 : PeakSet s2}
  (ρ : Retype env1 σ env2 D)
  (hps : ∀ (d : BVar s2 .cvar),
    env2.HasPeak ps2.cs d ↔ env2.HasPeak (ps1.cs.subst σ) d) :
  Retype (env1.extend_var x ps1) (σ.lift) (env2.extend_var x ps2) (D.rename Rename.succ) where
  var := fun
    | .here => rfl
    | .there y => by
      change (env1.lookup_var y).1
        = interp_var (env2.extend_var x ps2) ((σ.var y).rename Rename.succ)
      rw [← weaken_interp_var (ps:=ps2)]
      exact ρ.var y
  tvar := fun
    | .there X => by
      change
        env1.lookup_tvar X ≈
          Ty.val_denot (env2.extend_var x ps2) (((σ.tvar X).rename Rename.succ).core)
      apply Denot.equiv_trans _ _ _ (ρ.tvar X)
      apply weaken_val_denot (ps:=ps2)
  cvar := fun
    | .there C => by
      change (env1.lookup_cvar C).1
        = ((σ.cvar C).rename Rename.succ).subst (Subst.from_TypeEnv (env2.extend_var x ps2))
      rw [ρ.cvar C]
      apply rebind_resolved_capture_set (Rebind.weaken (ps:=ps2))
  var_peaks := fun b dv => by
    cases b with
    | here =>
      cases dv with
      | there d0 =>
        have hsubst :
            ((env1.extend_var x ps1).lookup_var BVar.here).2.cs.subst σ.lift
            = (ps1.cs.subst σ).rename Rename.succ := by
          change (ps1.cs.rename Rename.succ).subst σ.lift = _
          exact subst_lift_eq_subst_rename _ _
        rw [hsubst]
        have hl : (env2.extend_var x ps2).HasPeak
            (.var (.M .epsilon) (Subst.lift σ |>.var BVar.here)) (.there d0) ↔
            (env2.extend_var x ps2).HasPeak (ps2.cs.rename Rename.succ) (.there d0) := by
          refine TypeEnv.HasPeak.of_peaks_eq ?_
          exact (compute_peaks_peaksOnly_fixed (ps2.h.rename Rename.succ)).symm
        refine Iff.trans hl ?_
        have h1 := (Rebind.weaken (env := env2) (x := x) (ps := ps2)).peaks_at ps2.cs d0
        have h2 := (Rebind.weaken (env := env2) (x := x) (ps := ps2)).peaks_at
          (ps1.cs.subst σ) d0
        exact Iff.trans (Iff.trans h1.symm (hps d0)) h2
    | there z =>
      cases dv with
      | there d0 =>
        have hsubst :
            ((env1.extend_var x ps1).lookup_var (BVar.there z)).2.cs.subst σ.lift
            = ((env1.lookup_var z).2.cs.subst σ).rename Rename.succ := by
          change ((env1.lookup_var z).2.cs.rename Rename.succ).subst σ.lift = _
          exact subst_lift_eq_subst_rename _ _
        rw [hsubst]
        have h1 := (Rebind.weaken (env := env2) (x := x) (ps := ps2)).peaks_at
          (.var (.M .epsilon) (σ.var z)) d0
        have h2 := (Rebind.weaken (env := env2) (x := x) (ps := ps2)).peaks_at
          ((env1.lookup_var z).2.cs.subst σ) d0
        exact Iff.trans (Iff.trans h1.symm (ρ.var_peaks z d0)) h2
  dpeak_cvar_back := fun c dv hd => by
    cases c with
    | there c0 =>
      obtain ⟨d0, hfd, hd0⟩ :=
        (Rebind.weaken (env := env2) (x := x) (ps := ps2)).has_droppable_peak_inv (σ.cvar c0) dv hd
      subst hfd
      obtain ⟨hauth, hcap⟩ := ρ.dpeak_cvar_back c0 d0 hd0
      exact ⟨hauth, hcap⟩
  dpeak_cvar_unique := fun c dv1 dv2 hd1 hd2 => by
    cases c with
    | there c0 =>
      obtain ⟨d01, hfd1, hd01⟩ :=
        (Rebind.weaken (env := env2) (x := x) (ps := ps2)).has_droppable_peak_inv
          (σ.cvar c0) dv1 hd1
      obtain ⟨d02, hfd2, hd02⟩ :=
        (Rebind.weaken (env := env2) (x := x) (ps := ps2)).has_droppable_peak_inv
          (σ.cvar c0) dv2 hd2
      subst hfd1
      subst hfd2
      rw [ρ.dpeak_cvar_unique c0 d01 d02 hd01 hd02]
  dpeak_cvar_fwd := fun c hauth => by
    cases c with
    | there c0 =>
      obtain ⟨d0, hd0, hcap⟩ := ρ.dpeak_cvar_fwd c0 hauth
      refine ⟨.there d0, ?_, hcap⟩
      exact ((Rebind.weaken (env := env2) (x := x) (ps := ps2)).has_droppable_peak
        (σ.cvar c0) d0).mp hd0
  dpeak_cvar_inj := fun c1 c2 dv hd1 hd2 => by
    cases c1 with
    | there c01 =>
      cases c2 with
      | there c02 =>
        obtain ⟨d01, hfd1, hd01⟩ :=
          (Rebind.weaken (env := env2) (x := x) (ps := ps2)).has_droppable_peak_inv
            (σ.cvar c01) dv hd1
        obtain ⟨d02, hfd2, hd02⟩ :=
          (Rebind.weaken (env := env2) (x := x) (ps := ps2)).has_droppable_peak_inv
            (σ.cvar c02) dv hd2
        subst hfd1
        cases BVar.there.inj hfd2
        exact congrArg BVar.there (ρ.dpeak_cvar_inj c01 c02 d01 hd01 hd02)

private lemma subset_to_coveredby {A B : CaptureSet s} (h : A ⊆ B) : A.CoveredBy B := by
  induction h with
  | refl => exact CaptureSet.CoveredBy.refl'
  | empty => exact .empty
  | union_left _ _ ih1 ih2 => exact .union_left ih1 ih2
  | union_right_left _ ih => exact .union_right_left ih
  | union_right_right _ ih => exact .union_right_right ih

private lemma coveredby_rename_cancel {A B : CaptureSet s} {k : Kind}
    (hpoA : A.PeaksOnly) (hpoB : B.PeaksOnly)
    (h : (A.rename (Rename.succ (k := k))).CoveredBy
      (B.rename (Rename.succ (k := k)))) :
    A.CoveredBy B := by
  induction hpoA with
  | empty => exact .empty
  | cvar =>
    rename_i m c
    simp only [CaptureSet.rename, Rename.succ] at h
    obtain ⟨m', hle, hsub'⟩ := CaptureSet.CoveredBy.cvar_subset_coveredby CaptureSet.Subset.refl h
    obtain ⟨c', hfc, hsub''⟩ := hpoB.cvar_subset_rename_inv hsub'
    cases BVar.there.inj hfc
    have hcov'' : (CaptureSet.cvar m' c).CoveredBy B := subset_to_coveredby hsub''
    cases hle with
    | M hmu =>
      cases hmu with
      | refl => exact hcov''
      | ro_eps => exact CaptureSet.CoveredBy.mut_mono_left Mutability.Le.ro_eps hcov''
    | drop => exact hcov''
  | union _ _ ih1 ih2 =>
    simp only [CaptureSet.rename] at h
    exact .union_left (ih1 h.union_coveredby_left) (ih2 h.union_coveredby_right)

-- Drops the innermost cvar binder, mapping .here cvar to .empty
private def CaptureSet.drop_here_cvar : CaptureSet (s,C) -> CaptureSet s
| .empty => .empty
| .union cs1 cs2 => .union cs1.drop_here_cvar cs2.drop_here_cvar
| .var m (.free n) => .var m (.free n)
| .var m (.bound (.there x)) => .var m (.bound x)
| .cvar _ .here => .empty
| .cvar m (.there c) => .cvar m c

-- When cs' has no .here cvar (i.e. covered by a set with only .there cvars),
-- drop_here_cvar followed by rename Rename.succ is the identity.
private lemma drop_here_cvar_rename_succ_of_coveredby
    {s : Sig} {env : TypeEnv (s,C)} {D : PeakSet s} (cs' : CaptureSet (s,C))
    (hcov : (compute_peaks env cs').CoveredBy (D.cs.rename (Rename.succ (k := .cvar)))) :
    cs'.drop_here_cvar.rename (Rename.succ (k := .cvar)) = cs' := by
  induction cs' with
  | empty => rfl
  | union cs1 cs2 ih1 ih2 =>
    simp only [compute_peaks] at hcov
    change CaptureSet.rename (CaptureSet.union _ _) _ = _
    rw [show (CaptureSet.union cs1.drop_here_cvar cs2.drop_here_cvar).rename
           (Rename.succ (k := .cvar))
         = (cs1.drop_here_cvar.rename Rename.succ).union
           (cs2.drop_here_cvar.rename Rename.succ) from rfl]
    rw [ih1 hcov.union_coveredby_left, ih2 hcov.union_coveredby_right]
    rfl
  | var m x =>
    cases x with
    | free n => rfl
    | bound x =>
      cases x with
      | there x => rfl
  | cvar m c =>
    cases c with
    | here =>
      simp only [compute_peaks] at hcov
      obtain ⟨m', _, hsub⟩ :=
        CaptureSet.CoveredBy.cvar_subset_coveredby CaptureSet.Subset.refl hcov
      obtain ⟨c', hfc, _⟩ := D.h.cvar_subset_rename_inv hsub
      simp [Rename.succ] at hfc
    | there c => rfl

private lemma drop_here_tvar_rename_succ (cs : CaptureSet (s,X)) :
    cs.drop_here_tvar.rename (Rename.succ (k := .tvar)) = cs := by
  induction cs with
  | empty => rfl
  | union cs1 cs2 ih1 ih2 =>
    change CaptureSet.rename (CaptureSet.union _ _) _ = _
    rw [show (CaptureSet.union cs1.drop_here_tvar cs2.drop_here_tvar).rename
           (Rename.succ (k := .tvar))
         = (cs1.drop_here_tvar.rename Rename.succ).union
           (cs2.drop_here_tvar.rename Rename.succ) from rfl]
    rw [ih1, ih2]
    rfl
  | var m x =>
    cases x with
    | free n => rfl
    | bound x =>
      cases x with
      | there x => rfl
  | cvar m c =>
    cases c with
    | there c => rfl

theorem Retype.liftTVar
  {s1 s2 : Sig} {env1 : TypeEnv s1} {σ : Subst s1 s2} {env2 : TypeEnv s2} {D : PeakSet s1}
  {d : Denot}
  (ρ : Retype env1 σ env2 D) :
  Retype (env1.extend_tvar d) (σ.lift) (env2.extend_tvar d) (D.rename Rename.succ) where
  var := fun
    | .there x => by
      change (env1.lookup_var x).1
        = interp_var (env2.extend_tvar d) ((σ.var x).rename Rename.succ)
      rw [← tweaken_interp_var]
      exact ρ.var x
  tvar := fun
    | .here => by
      change d ≈ Ty.val_denot (env2.extend_tvar d) (PureTy.tvar (BVar.here (s := s2))).core
      apply Denot.eq_to_equiv
      unfold PureTy.tvar Ty.val_denot
      rfl
    | .there X => by
      change
        env1.lookup_tvar X ≈
          Ty.val_denot (env2.extend_tvar d) (((σ.tvar X).rename Rename.succ).core)
      apply Denot.equiv_trans _ _ _ (ρ.tvar X)
      apply tweaken_val_denot
  cvar := fun
    | .there C => by
      change (env1.lookup_cvar C).1
        = ((σ.cvar C).rename Rename.succ).subst (Subst.from_TypeEnv (env2.extend_tvar d))
      rw [ρ.cvar C]
      apply rebind_resolved_capture_set Rebind.tweaken
  var_peaks := fun b dv => by
    cases b with
    | there z =>
      cases dv with
      | there d0 =>
        have hsubst :
            ((env1.extend_tvar d).lookup_var (BVar.there z)).2.cs.subst σ.lift
            = ((env1.lookup_var z).2.cs.subst σ).rename Rename.succ := by
          change ((env1.lookup_var z).2.cs.rename Rename.succ).subst σ.lift = _
          exact subst_lift_eq_subst_rename _ _
        rw [hsubst]
        have h1 := (Rebind.tweaken (env := env2) (d := d)).peaks_at
          (.var (.M .epsilon) (σ.var z)) d0
        have h2 := (Rebind.tweaken (env := env2) (d := d)).peaks_at
          ((env1.lookup_var z).2.cs.subst σ) d0
        exact Iff.trans (Iff.trans h1.symm (ρ.var_peaks z d0)) h2
  dpeak_cvar_back := fun c dv hd => by
    cases c with
    | there c0 =>
      obtain ⟨d0, hfd, hd0⟩ :=
        (Rebind.tweaken (env := env2) (d := d)).has_droppable_peak_inv (σ.cvar c0) dv hd
      subst hfd
      obtain ⟨hauth, hcap⟩ := ρ.dpeak_cvar_back c0 d0 hd0
      exact ⟨hauth, hcap⟩
  dpeak_cvar_unique := fun c dv1 dv2 hd1 hd2 => by
    cases c with
    | there c0 =>
      obtain ⟨d01, hfd1, hd01⟩ :=
        (Rebind.tweaken (env := env2) (d := d)).has_droppable_peak_inv (σ.cvar c0) dv1 hd1
      obtain ⟨d02, hfd2, hd02⟩ :=
        (Rebind.tweaken (env := env2) (d := d)).has_droppable_peak_inv (σ.cvar c0) dv2 hd2
      subst hfd1
      subst hfd2
      rw [ρ.dpeak_cvar_unique c0 d01 d02 hd01 hd02]
  dpeak_cvar_fwd := fun c hauth => by
    cases c with
    | there c0 =>
      obtain ⟨d0, hd0, hcap⟩ := ρ.dpeak_cvar_fwd c0 hauth
      refine ⟨.there d0, ?_, hcap⟩
      exact ((Rebind.tweaken (env := env2) (d := d)).has_droppable_peak (σ.cvar c0) d0).mp hd0
  dpeak_cvar_inj := fun c1 c2 dv hd1 hd2 => by
    cases c1 with
    | there c01 =>
      cases c2 with
      | there c02 =>
        obtain ⟨d01, hfd1, hd01⟩ :=
          (Rebind.tweaken (env := env2) (d := d)).has_droppable_peak_inv (σ.cvar c01) dv hd1
        obtain ⟨d02, hfd2, hd02⟩ :=
          (Rebind.tweaken (env := env2) (d := d)).has_droppable_peak_inv (σ.cvar c02) dv hd2
        subst hfd1
        cases BVar.there.inj hfd2
        exact congrArg BVar.there (ρ.dpeak_cvar_inj c01 c02 d01 hd01 hd02)

theorem Retype.liftCVar
  {s1 s2 : Sig} {env1 : TypeEnv s1} {σ : Subst s1 s2} {env2 : TypeEnv s2} {D : PeakSet s1}
  (ρ : Retype env1 σ env2 D) (cs : CaptureSet {}) (cap : CapabilitySet := .empty)
  (a : Authority := .access_only) :
  Retype (env1.extend_cvar cs cap a) (σ.lift) (env2.extend_cvar cs cap a)
    (D.rename Rename.succ) where
  var := fun
    | .there x => by
      change (env1.lookup_var x).1
        = interp_var (env2.extend_cvar cs cap a) ((σ.var x).rename Rename.succ)
      rw [← cweaken_interp_var]
      exact ρ.var x
  tvar := fun
    | .there X => by
      change
        env1.lookup_tvar X ≈
          Ty.val_denot (env2.extend_cvar cs cap a) (((σ.tvar X).rename Rename.succ).core)
      apply Denot.equiv_trans _ _ _ (ρ.tvar X)
      apply cweaken_val_denot
  cvar := fun
    | .here => by
      change cs = (CaptureSet.cvar (.M Mutability.epsilon) (BVar.here (s := s2))).subst
        (Subst.from_TypeEnv (env2.extend_cvar cs cap a))
      rfl
    | .there C => by
      change (env1.lookup_cvar C).1
        = ((σ.cvar C).rename Rename.succ).subst (Subst.from_TypeEnv (env2.extend_cvar cs cap a))
      rw [ρ.cvar C]
      apply rebind_resolved_capture_set Rebind.cweaken
  var_peaks := fun b dv => by
    cases b with
    | there z =>
      have hsubst :
          ((env1.extend_cvar cs cap a).lookup_var (BVar.there z)).2.cs.subst σ.lift
          = ((env1.lookup_var z).2.cs.subst σ).rename Rename.succ := by
        change ((env1.lookup_var z).2.cs.rename Rename.succ).subst σ.lift = _
        exact subst_lift_eq_subst_rename _ _
      rw [hsubst]
      cases dv with
      | here =>
        constructor
        · intro h
          obtain ⟨d0, hfd, -⟩ :=
            (Rebind.cweaken (env := env2) (cs := cs) (cap := cap) (a := a)).peaks_at_inv
              (.var (.M .epsilon) (σ.var z)) .here h
          cases (show BVar.there d0 = BVar.here from hfd)
        · intro h
          obtain ⟨d0, hfd, -⟩ :=
            (Rebind.cweaken (env := env2) (cs := cs) (cap := cap) (a := a)).peaks_at_inv
              ((env1.lookup_var z).2.cs.subst σ) .here h
          cases (show BVar.there d0 = BVar.here from hfd)
      | there d0 =>
        have h1 := (Rebind.cweaken (env := env2) (cs := cs) (cap := cap) (a := a)).peaks_at
          (.var (.M .epsilon) (σ.var z)) d0
        have h2 := (Rebind.cweaken (env := env2) (cs := cs) (cap := cap) (a := a)).peaks_at
          ((env1.lookup_var z).2.cs.subst σ) d0
        exact Iff.trans (Iff.trans h1.symm (ρ.var_peaks z d0)) h2
  dpeak_cvar_back := fun c dv hd => by
    cases c with
    | here =>
      obtain ⟨hauth, a', hp⟩ := hd
      obtain ⟨-, heq⟩ := CaptureSet.cvar_subset_cvar_inv hp
      subst heq
      exact ⟨hauth, rfl⟩
    | there c0 =>
      obtain ⟨d0, hfd, hd0⟩ :=
        (Rebind.cweaken (env := env2) (cs := cs) (cap := cap) (a := a)).has_droppable_peak_inv
          (σ.cvar c0) dv hd
      subst hfd
      obtain ⟨hauth, hcap⟩ := ρ.dpeak_cvar_back c0 d0 hd0
      exact ⟨hauth, hcap⟩
  dpeak_cvar_unique := fun c dv1 dv2 hd1 hd2 => by
    cases c with
    | here =>
      obtain ⟨-, a1, hp1⟩ := hd1
      obtain ⟨-, a2, hp2⟩ := hd2
      rw [(CaptureSet.cvar_subset_cvar_inv hp1).2, (CaptureSet.cvar_subset_cvar_inv hp2).2]
    | there c0 =>
      obtain ⟨d01, hfd1, hd01⟩ :=
        (Rebind.cweaken (env := env2) (cs := cs) (cap := cap) (a := a)).has_droppable_peak_inv
          (σ.cvar c0) dv1 hd1
      obtain ⟨d02, hfd2, hd02⟩ :=
        (Rebind.cweaken (env := env2) (cs := cs) (cap := cap) (a := a)).has_droppable_peak_inv
          (σ.cvar c0) dv2 hd2
      subst hfd1
      subst hfd2
      rw [ρ.dpeak_cvar_unique c0 d01 d02 hd01 hd02]
  dpeak_cvar_fwd := fun c hauth => by
    cases c with
    | here =>
      exact ⟨.here, ⟨hauth, .M .epsilon, .refl⟩, rfl⟩
    | there c0 =>
      obtain ⟨d0, hd0, hcap⟩ := ρ.dpeak_cvar_fwd c0 hauth
      refine ⟨.there d0, ?_, hcap⟩
      exact ((Rebind.cweaken (env := env2) (cs := cs) (cap := cap) (a := a)).has_droppable_peak
        (σ.cvar c0) d0).mp hd0
  dpeak_cvar_inj := fun c1 c2 dv hd1 hd2 => by
    cases c1 with
    | here =>
      cases c2 with
      | here => rfl
      | there c02 =>
        obtain ⟨-, a1, hp1⟩ := hd1
        obtain ⟨d02, hfd2, -⟩ :=
          (Rebind.cweaken (env := env2) (cs := cs) (cap := cap) (a := a)).has_droppable_peak_inv
            (σ.cvar c02) dv hd2
        rw [(CaptureSet.cvar_subset_cvar_inv hp1).2] at hfd2
        cases (show BVar.there d02 = BVar.here from hfd2)
    | there c01 =>
      cases c2 with
      | here =>
        obtain ⟨-, a2, hp2⟩ := hd2
        obtain ⟨d01, hfd1, -⟩ :=
          (Rebind.cweaken (env := env2) (cs := cs) (cap := cap) (a := a)).has_droppable_peak_inv
            (σ.cvar c01) dv hd1
        rw [(CaptureSet.cvar_subset_cvar_inv hp2).2] at hfd1
        cases (show BVar.there d01 = BVar.here from hfd1)
      | there c02 =>
        obtain ⟨d01, hfd1, hd01⟩ :=
          (Rebind.cweaken (env := env2) (cs := cs) (cap := cap) (a := a)).has_droppable_peak_inv
            (σ.cvar c01) dv hd1
        obtain ⟨d02, hfd2, hd02⟩ :=
          (Rebind.cweaken (env := env2) (cs := cs) (cap := cap) (a := a)).has_droppable_peak_inv
            (σ.cvar c02) dv hd2
        subst hfd1
        cases BVar.there.inj hfd2
        exact congrArg BVar.there (ρ.dpeak_cvar_inj c01 c02 d01 hd01 hd02)

def retype_resolved_capture_set
  {s1 s2 : Sig} {env1 : TypeEnv s1} {σ : Subst s1 s2} {env2 : TypeEnv s2} {D : PeakSet s1}
  (ρ : Retype env1 σ env2 D) (C : CaptureSet s1) :
  C.subst (Subst.from_TypeEnv env1) = (C.subst σ).subst (Subst.from_TypeEnv env2) := by
  induction C with
  | empty => rfl
  | union C1 C2 ih1 ih2 =>
    simp only [CaptureSet.subst, ih1, ih2]
  | var m x =>
    cases x with
    | free n =>
      rfl
    | bound x =>
      cases hσ : σ.var x with
      | bound y =>
        simpa only [CaptureSet.subst, Var.subst, Subst.from_TypeEnv, interp_var, hσ] using
          congrArg (fun n => CaptureSet.var m (.free n)) (ρ.var x)
      | free n =>
        simpa only [CaptureSet.subst, Var.subst, Subst.from_TypeEnv, interp_var, hσ] using
          congrArg (fun n => CaptureSet.var m (.free n)) (ρ.var x)
  | cvar m C =>
    cases m with
    | M mu =>
      cases mu with
      | epsilon =>
        simpa only [CaptureSet.subst, CaptureSet.applyAccess_M, CaptureSet.applyMut_epsilon,
          Subst.from_TypeEnv] using ρ.cvar C
      | ro =>
        change ((env1.lookup_cvar C).1).applyRO =
          ((σ.cvar C).applyRO).subst (Subst.from_TypeEnv env2)
        rw [CaptureSet.applyRO_subst]
        rw [ρ.cvar C]
    | drop =>
      change ((env1.lookup_cvar C).1).applyDrop =
        ((σ.cvar C).applyDrop).subst (Subst.from_TypeEnv env2)
      rw [CaptureSet.applyDrop_subst]
      rw [ρ.cvar C]

def retype_captureset_denot
  {s1 s2 : Sig} {env1 : TypeEnv s1} {σ : Subst s1 s2} {env2 : TypeEnv s2} {D : PeakSet s1}
  (ρ : Retype env1 σ env2 D) (C : CaptureSet s1) :
  CaptureSet.denot env1 C = CaptureSet.denot env2 (C.subst σ) := by
  unfold CaptureSet.denot
  congr 1
  exact retype_resolved_capture_set ρ C

def retype_capturebound_denot
  {s1 s2 : Sig} {env1 : TypeEnv s1} {σ : Subst s1 s2} {env2 : TypeEnv s2} {D : PeakSet s1}
  (ρ : Retype env1 σ env2 D) (B : CaptureBound s1) :
  CaptureBound.denot env1 B = CaptureBound.denot env2 (B.subst σ) := by
  cases B with
  | unbound =>
    rfl
  | bound C =>
    funext m
    simp [CaptureBound.denot, CaptureBound.subst, retype_captureset_denot ρ C]

private theorem SepCtx.Has.subst_retype
  {K : SepCtx s1} {σ : Subst s1 s2}
  (h : SepCtx.Has K C m) :
  SepCtx.Has (K.subst σ) (C.subst σ) m := by
  induction h with
  | here =>
    exact .here
  | there h ih =>
    exact .there ih

private theorem SepCtx.Has.subst_inv_retype
  {K : SepCtx s1} {σ : Subst s1 s2}
  (h : SepCtx.Has (K.subst σ) C m) :
  ∃ C0, C = C0.subst σ ∧ SepCtx.Has K C0 m := by
  induction K with
  | empty =>
    cases h
  | cons K C0 m0 ih =>
    cases h with
    | here =>
      exact ⟨C0, rfl, .here⟩
    | there h' =>
      obtain ⟨C1, hC1, hh⟩ := ih h'
      exact ⟨C1, hC1, .there hh⟩

private theorem SepCtx.HasTwoDistinct.subst_retype
  {K : SepCtx s1} {σ : Subst s1 s2}
  (h : SepCtx.HasTwoDistinct K C1 m1 C2 m2) :
  SepCtx.HasTwoDistinct (K.subst σ) (C1.subst σ) m1 (C2.subst σ) m2 := by
  induction h with
  | here_there hhas =>
    exact .here_there (hhas.subst_retype)
  | there h ih =>
    exact .there ih
  | symm h ih =>
    exact .symm ih

private theorem SepCtx.HasTwoDistinct.subst_inv_retype
  {K : SepCtx s1} {σ : Subst s1 s2}
  (h : SepCtx.HasTwoDistinct (K.subst σ) C1 m1 C2 m2) :
  ∃ D1 D2,
    C1 = D1.subst σ ∧
    C2 = D2.subst σ ∧
    SepCtx.HasTwoDistinct K D1 m1 D2 m2 := by
  generalize he0 : K.subst σ = K0 at h
  induction h generalizing K with
  | here_there hhas =>
    cases K with
    | empty =>
      cases he0
    | cons K1 C0 m0 =>
      cases he0
      obtain ⟨D2, hD2, hh⟩ := SepCtx.Has.subst_inv_retype hhas
      exact ⟨C0, D2, rfl, hD2, .here_there hh⟩
  | there h ih =>
    cases K with
    | empty =>
      cases he0
    | cons K1 C0 m0 =>
      cases he0
      obtain ⟨D1, D2, hD1, hD2, hh⟩ := ih rfl
      exact ⟨D1, D2, hD1, hD2, .there hh⟩
  | symm h ih =>
    obtain ⟨D2, D1, hD2, hD1, hh⟩ := ih he0
    exact ⟨D1, D2, hD1, hD2, .symm hh⟩

private theorem retype_satisfy_iff
    {s1 s2 : Sig} {env1 : TypeEnv s1} {σ : Subst s1 s2} {env2 : TypeEnv s2} {D : PeakSet s1}
    (ρ : Retype env1 σ env2 D) (Ψ : SepCtx s1) (m : Memory) :
    TypeEnv.Satisfy env1 Ψ m ↔ TypeEnv.Satisfy env2 (Ψ.subst σ) m := by
  constructor
  · intro hsat
    constructor
    · intro C mode hhas
      obtain ⟨C0, rfl, hhas0⟩ := SepCtx.Has.subst_inv_retype hhas
      simpa only [retype_resolved_capture_set (ρ := ρ) (C := C0)] using
        hsat.wf C0 mode hhas0
    · intro C mode hhas
      obtain ⟨C0, rfl, hhas0⟩ := SepCtx.Has.subst_inv_retype hhas
      simpa only [retype_captureset_denot (ρ := ρ) (C := C0)] using
        hsat.kind C0 mode hhas0
    · intro C1 m1 C2 m2 hdistinct
      obtain ⟨D1, D2, rfl, rfl, hdistinct0⟩ := SepCtx.HasTwoDistinct.subst_inv_retype hdistinct
      simpa only [retype_captureset_denot (ρ := ρ) (C := D1),
        retype_captureset_denot (ρ := ρ) (C := D2)] using
        hsat.sep D1 m1 D2 m2 hdistinct0
  · intro hsat
    constructor
    · intro C mode hhas
      have hhas' := hhas.subst_retype (σ := σ)
      simpa only [retype_resolved_capture_set (ρ := ρ) (C := C)] using
        hsat.wf (C.subst σ) mode hhas'
    · intro C mode hhas
      have hhas' := hhas.subst_retype (σ := σ)
      simpa only [retype_captureset_denot (ρ := ρ) (C := C)] using
        hsat.kind (C.subst σ) mode hhas'
    · intro C1 m1 C2 m2 hdistinct
      have hdistinct' := hdistinct.subst_retype (σ := σ)
      simpa only [retype_captureset_denot (ρ := ρ) (C := C1),
        retype_captureset_denot (ρ := ρ) (C := C2)] using
        hsat.sep (C1.subst σ) m1 (C2.subst σ) m2 hdistinct'

set_option maxHeartbeats 800000 in
-- The cpoly case requires more heartbeats due to accumulated elaboration state in the mutual block
mutual

def retype_val_denot
  {s1 s2 : Sig} {env1 : TypeEnv s1} {σ : Subst s1 s2} {env2 : TypeEnv s2} {D : PeakSet s1}
  (ρ : Retype env1 σ env2 D) (T : Ty .capt s1) :
  Ty.val_denot env1 T ≈ Ty.val_denot env2 (T.subst σ) :=
  match T with
  | .top | .unit | .bool => by
    intro m e
    simp [Ty.val_denot, Ty.subst]
  | .tvar X => by
    have h := ρ.tvar X
    intro m e
    simp only [Ty.val_denot, Ty.subst]
    exact h m e
  | .cap cs | .cell cs | .reader cs => by
    intro m e
    simp only [Ty.val_denot, Ty.subst]
    rw [← retype_resolved_capture_set ρ]
    rw [← retype_captureset_denot ρ cs]
  | .arrow T1 _ cs T2 => by
    have ih1 := retype_val_denot ρ T1
    intro m e
    simp only [Ty.val_denot, Ty.subst]
    rw [← retype_resolved_capture_set ρ]
    rw [← retype_captureset_denot ρ cs]
    constructor
    · intro ⟨hwf_e, hwf_cs, cs', T0, t0, hr, hwf_cs', hR0_sub, hd⟩
      refine ⟨hwf_e, hwf_cs, cs', T0, t0, hr, hwf_cs', hR0_sub, ?_⟩
      intro arg m' hsub hcompat hdsep harg
      let R0 := expand_captures m.heap cs'
      let ps1 := compute_peakset env1 T1.captureSet
      let ps2 := compute_peakset env2 (T1.subst σ).captureSet
      have ih2 := retype_exi_exp_denot
        (ρ.liftVar (x:=arg) (ps1:=ps1) (ps2:=ps2) (ρ.lift_hps T1)) T2 R0
      have harg' := (ih1 m' (.var (.free arg))).mpr harg
      specialize hd arg m' hsub hcompat ((ρ.dsep cs).mpr hdsep) harg'
      exact (ih2 m' _).mp hd
    · intro ⟨hwf_e, hwf_cs, cs', T0, t0, hr, hwf_cs', hR0_sub, hd⟩
      refine ⟨hwf_e, hwf_cs, cs', T0, t0, hr, hwf_cs', hR0_sub, ?_⟩
      intro arg m' hsub hcompat hdsep harg
      let R0 := expand_captures m.heap cs'
      let ps1 := compute_peakset env1 T1.captureSet
      let ps2 := compute_peakset env2 (T1.subst σ).captureSet
      have ih2 := retype_exi_exp_denot
        (ρ.liftVar (x:=arg) (ps1:=ps1) (ps2:=ps2) (ρ.lift_hps T1)) T2 R0
      have harg' := (ih1 m' (.var (.free arg))).mp harg
      specialize hd arg m' hsub hcompat ((ρ.dsep cs).mp hdsep) harg'
      exact (ih2 m' _).mpr hd
  | .poly T1 _ cs T2 => by
    have ih1 := retype_val_denot ρ T1
    intro m e
    simp only [Ty.val_denot, Ty.subst]
    rw [← retype_resolved_capture_set ρ]
    rw [← retype_captureset_denot ρ cs]
    constructor
    · intro ⟨hwf_e, hwf_cs, cs', S0, t0, hr, hwf_cs', hR0_sub, hd⟩
      refine ⟨hwf_e, hwf_cs, cs', S0, t0, hr, hwf_cs', hR0_sub, ?_⟩
      intro m' denot hsub hcompat hdsep hproper himply_simple_ans himply hpure
      let R0 := expand_captures m.heap cs'
      have ih2 := retype_exi_exp_denot (ρ.liftTVar (d:=denot)) T2 R0
      have himply' : denot.ImplyAfter m' (Ty.val_denot env1 T1) := by
        intro m'' hsub' e' hdenot
        exact (ih1 m'' e').mpr (himply m'' hsub' e' hdenot)
      specialize hd m' denot hsub hcompat ((ρ.dsep cs).mpr hdsep)
        hproper himply_simple_ans himply' hpure
      exact (ih2 m' _).mp hd
    · intro ⟨hwf_e, hwf_cs, cs', S0, t0, hr, hwf_cs', hR0_sub, hd⟩
      refine ⟨hwf_e, hwf_cs, cs', S0, t0, hr, hwf_cs', hR0_sub, ?_⟩
      intro m' denot hsub hcompat hdsep hproper himply_simple_ans himply hpure
      let R0 := expand_captures m.heap cs'
      have ih2 := retype_exi_exp_denot (ρ.liftTVar (d:=denot)) T2 R0
      have himply' : denot.ImplyAfter m' (Ty.val_denot env2 (T1.subst σ)) := by
        intro m'' hsub' e' hdenot
        exact (ih1 m'' e').mp (himply m'' hsub' e' hdenot)
      specialize hd m' denot hsub hcompat ((ρ.dsep cs).mp hdsep)
        hproper himply_simple_ans himply' hpure
      exact (ih2 m' _).mpr hd
  | .cpoly B _ cs T => by
    have hB := retype_capturebound_denot ρ B
    intro m e
    simp only [Ty.val_denot, Ty.subst]
    rw [← retype_resolved_capture_set ρ]
    rw [← retype_captureset_denot ρ cs]
    rw [hB]
    constructor
    · intro ⟨hwf_e, hwf_cs, cs', B0, t0, hr, hwf_cs', hR0_sub, hd⟩
      refine ⟨hwf_e, hwf_cs, cs', B0, t0, hr, hwf_cs', hR0_sub, ?_⟩
      intro m' CS hwf_CS hdf hsub hcompat hdsep hsub_bound
      let R0 := expand_captures m.heap cs'
      let cap1 : CapabilitySet := CS.ground_denot m'
      let ρ1 : Retype (env1.extend_cvar CS cap1) σ.lift
                      (env2.extend_cvar CS cap1) (D.rename Rename.succ) :=
        ρ.liftCVar (cs:=CS) (cap:=cap1)
      have ih2 := retype_exi_exp_denot ρ1 T R0
      specialize hd m' CS hwf_CS hdf hsub hcompat ((ρ.dsep cs).mpr hdsep) hsub_bound
      exact (ih2 m' _).mp hd
    · intro ⟨hwf_e, hwf_cs, cs', B0, t0, hr, hwf_cs', hR0_sub, hd⟩
      refine ⟨hwf_e, hwf_cs, cs', B0, t0, hr, hwf_cs', hR0_sub, ?_⟩
      intro m' CS hwf_CS hdf hsub hcompat hdsep hsub_bound
      let R0 := expand_captures m.heap cs'
      let cap2 : CapabilitySet := CS.ground_denot m'
      let ρ2 : Retype (env1.extend_cvar CS cap2) σ.lift
                      (env2.extend_cvar CS cap2) (D.rename Rename.succ) :=
        ρ.liftCVar (cs:=CS) (cap:=cap2)
      specialize hd m' CS hwf_CS hdf hsub hcompat ((ρ.dsep cs).mp hdsep) hsub_bound
      exact (retype_exi_exp_denot ρ2 T R0 m' _).mpr hd
  | .modal _ cs Ψ T => by
    intro m e
    simp only [Ty.val_denot, Ty.subst]
    rw [← retype_resolved_capture_set ρ]
    rw [← retype_captureset_denot ρ cs]
    constructor
    · rintro ⟨hwf_e, hwf_cs, cs0, sepctx0, t0, hres, hwf_cs0, hwf_sepctx0,
        hsat, hR0_sub, hbody⟩
      refine ⟨hwf_e, hwf_cs, cs0, sepctx0, t0, hres, hwf_cs0, hwf_sepctx0, ?_, hR0_sub, ?_⟩
      · intro m' hsub hsat'
        exact hsat m' hsub ((retype_satisfy_iff ρ Ψ m').mpr hsat')
      · intro m' hsub hcompat hdsep hkind hsep
        let R0 := expand_captures m.heap cs0
        have ih := retype_exi_exp_denot ρ T R0
        have hkind' :
            ∀ (C : CaptureSet s1) (mode : Mutability),
              Ψ.Has C mode -> CapabilitySet.HasKind (C.denot env1 m') mode := by
          intro C mode hhas
          simpa only [retype_captureset_denot (ρ := ρ) (C := C)] using
            hkind (C.subst σ) mode (hhas.subst_retype)
        have hsep' :
            ∀ (C1 : CaptureSet s1) (m1 : Mutability) (C2 : CaptureSet s1) (m2 : Mutability),
              Ψ.HasTwoDistinct C1 m1 C2 m2 ->
              CapabilitySet.Noninterference (C1.denot env1 m') (C2.denot env1 m') := by
          intro C1 m1 C2 m2 hdistinct
          simpa only [retype_captureset_denot (ρ := ρ) (C := C1),
            retype_captureset_denot (ρ := ρ) (C := C2)] using
              hsep (C1.subst σ) m1 (C2.subst σ) m2 (hdistinct.subst_retype)
        exact (ih m' _).mp (hbody m' hsub hcompat ((ρ.dsep cs).mpr hdsep) hkind' hsep')
    · rintro ⟨hwf_e, hwf_cs, cs0, sepctx0, t0, hres, hwf_cs0, hwf_sepctx0,
        hsat, hR0_sub, hbody⟩
      refine ⟨hwf_e, hwf_cs, cs0, sepctx0, t0, hres, hwf_cs0, hwf_sepctx0, ?_, hR0_sub, ?_⟩
      · intro m' hsub hsat'
        exact hsat m' hsub ((retype_satisfy_iff ρ Ψ m').mp hsat')
      · intro m' hsub hcompat hdsep hkind hsep
        let R0 := expand_captures m.heap cs0
        have ih := retype_exi_exp_denot ρ T R0
        have hkind' :
            ∀ (C : CaptureSet s2) (mode : Mutability),
              (Ψ.subst σ).Has C mode -> CapabilitySet.HasKind (C.denot env2 m') mode := by
          intro C mode hhas
          obtain ⟨C0, rfl, hhas0⟩ := SepCtx.Has.subst_inv_retype hhas
          simpa only [retype_captureset_denot (ρ := ρ) (C := C0)] using
            hkind C0 mode hhas0
        have hsep' :
            ∀ (C1 : CaptureSet s2) (m1 : Mutability) (C2 : CaptureSet s2) (m2 : Mutability),
              (Ψ.subst σ).HasTwoDistinct C1 m1 C2 m2 ->
              CapabilitySet.Noninterference (C1.denot env2 m') (C2.denot env2 m') := by
          intro C1 m1 C2 m2 hdistinct
          obtain ⟨D1, D2, rfl, rfl, hdistinct0⟩ := SepCtx.HasTwoDistinct.subst_inv_retype hdistinct
          simpa only [retype_captureset_denot (ρ := ρ) (C := D1),
            retype_captureset_denot (ρ := ρ) (C := D2)] using
              hsep D1 m1 D2 m2 hdistinct0
        exact (ih m' _).mpr (hbody m' hsub hcompat ((ρ.dsep cs).mp hdsep) hkind' hsep')

def retype_exi_val_denot
  {s1 s2 : Sig} {env1 : TypeEnv s1} {σ : Subst s1 s2} {env2 : TypeEnv s2} {D : PeakSet s1}
  (ρ : Retype env1 σ env2 D) (T : Ty .exi s1) :
  Ty.exi_val_denot env1 T ≈ Ty.exi_val_denot env2 (T.subst σ) :=
  match T with
  | .typ T => by
    have ih := retype_val_denot ρ T
    intro s e
    simp only [Ty.exi_val_denot, Ty.subst]
    exact ih s e
  | .exi T => by
    intro s e
    simp only [Ty.exi_val_denot, Ty.subst]
    -- Both sides are match expressions on resolve s.heap e
    cases hresolve : resolve s.heap e
    · -- resolve = none
      simp
    · -- resolve = some e'
      rename_i e'
      cases e'
      case pack =>
        rename_i CS y
        simp only [List.empty_eq, and_congr_right_iff]
        -- Goal: CS.WfInHeap s.heap → drop-free → (... ↔ ...)
        intro _hwf _hdf
        exact retype_val_denot
          (ρ.liftCVar (cs:=CS) (cap:=CS.ground_denot s) (a:=.can_drop)) T s (Exp.var y)
      all_goals {
        -- resolve returned non-pack
        simp
      }

def retype_exi_exp_denot
  {s1 s2 : Sig} {env1 : TypeEnv s1} {σ : Subst s1 s2} {env2 : TypeEnv s2} {D : PeakSet s1}
  (ρ : Retype env1 σ env2 D) (T : Ty .exi s1) (R : CapabilitySet) :
  Ty.exi_exp_denot env1 T R ≈ Ty.exi_exp_denot env2 (T.subst σ) R := by
  have ih := retype_exi_val_denot ρ T
  intro m e
  simp only [Ty.exi_exp_denot]
  constructor
  · intro h
    refine eval_post_monotonic ?_ h
    intro m'' v hpost
    exact ⟨(ih m'' v).mp hpost.1, hpost.2⟩
  · intro h
    refine eval_post_monotonic ?_ h
    intro m'' v hpost
    exact ⟨(ih m'' v).mpr hpost.1, hpost.2⟩

end

def Retype.open_arg {s : Sig} {env : TypeEnv s} {y : Var .var s} {ps : PeakSet s}
  (hps : ∀ (d : BVar s .cvar),
    env.HasPeak ps.cs d ↔ env.HasPeak (.var (.M .epsilon) y) d) :
  Retype
    (env.extend_var (interp_var env y) ps)
    (Subst.openVar y)
    env
    ⟨CaptureSet.empty, .empty⟩ where
  var := fun x => by cases x <;> rfl
  tvar := fun
    | .there X => by
      change env.lookup_tvar X ≈ Ty.val_denot env (PureTy.tvar X).core
      apply Denot.eq_to_equiv
      unfold PureTy.tvar Ty.val_denot
      rfl
  cvar := fun
    | .there C => by
      change
        (env.lookup_cvar C).1 =
          (CaptureSet.cvar (.M Mutability.epsilon) C).subst (Subst.from_TypeEnv env)
      rfl
  var_peaks := fun b d => by
    cases b with
    | here =>
      change env.HasPeak (.var (.M .epsilon) y) d ↔
        env.HasPeak ((ps.cs.rename Rename.succ).subst (Subst.openVar y)) d
      rw [CaptureSet.weaken_openVar]
      exact (hps d).symm
    | there z =>
      change env.HasPeak (.var (.M .epsilon) (.bound z)) d ↔
        env.HasPeak (((env.lookup_var z).2.cs.rename Rename.succ).subst (Subst.openVar y)) d
      rw [CaptureSet.weaken_openVar]
      refine TypeEnv.HasPeak.of_peaks_eq ?_
      rw [compute_peaks_peaksOnly_fixed (env.lookup_var z).2.h]
      rfl
  dpeak_cvar_back := fun c d hd => by
    cases c with
    | there c0 =>
      obtain ⟨hauth, a, hp⟩ := hd
      obtain ⟨-, heq⟩ := CaptureSet.cvar_subset_cvar_inv hp
      subst heq
      exact ⟨hauth, rfl⟩
  dpeak_cvar_unique := fun c d1 d2 hd1 hd2 => by
    cases c with
    | there c0 =>
      obtain ⟨-, a1, hp1⟩ := hd1
      obtain ⟨-, a2, hp2⟩ := hd2
      rw [(CaptureSet.cvar_subset_cvar_inv hp1).2, (CaptureSet.cvar_subset_cvar_inv hp2).2]
  dpeak_cvar_fwd := fun c hauth => by
    cases c with
    | there c0 =>
      exact ⟨c0, ⟨hauth, .M .epsilon, .refl⟩, rfl⟩
  dpeak_cvar_inj := fun c1 c2 d hd1 hd2 => by
    cases c1 with
    | there c01 =>
      cases c2 with
      | there c02 =>
        obtain ⟨-, a1, hp1⟩ := hd1
        obtain ⟨-, a2, hp2⟩ := hd2
        exact congrArg BVar.there
          (((CaptureSet.cvar_subset_cvar_inv hp1).2).symm.trans
            (CaptureSet.cvar_subset_cvar_inv hp2).2)

theorem open_arg_val_denot
    {env : TypeEnv s} {y : Var .var s} {ps : PeakSet s} {T : Ty .capt (s,x)}
    (hps : ∀ (d : BVar s .cvar),
      env.HasPeak ps.cs d ↔ env.HasPeak (.var (.M .epsilon) y) d) :
  Ty.val_denot (env.extend_var (interp_var env y) ps) T ≈
    Ty.val_denot env (T.subst (Subst.openVar y)) := by
  apply retype_val_denot (Retype.open_arg hps)

theorem open_arg_exi_val_denot
    {env : TypeEnv s} {y : Var .var s} {ps : PeakSet s} {T : Ty .exi (s,x)}
    (hps : ∀ (d : BVar s .cvar),
      env.HasPeak ps.cs d ↔ env.HasPeak (.var (.M .epsilon) y) d) :
  Ty.exi_val_denot (env.extend_var (interp_var env y) ps) T ≈
    Ty.exi_val_denot env (T.subst (Subst.openVar y)) := by
  apply retype_exi_val_denot (Retype.open_arg hps)

theorem open_arg_exi_exp_denot
    {env : TypeEnv s} {y : Var .var s} {ps : PeakSet s}
    {T : Ty .exi (s,x)} {R : CapabilitySet}
    (hps : ∀ (d : BVar s .cvar),
      env.HasPeak ps.cs d ↔ env.HasPeak (.var (.M .epsilon) y) d) :
  Ty.exi_exp_denot (env.extend_var (interp_var env y) ps) T R ≈
    Ty.exi_exp_denot env (T.subst (Subst.openVar y)) R := by
  apply retype_exi_exp_denot (Retype.open_arg hps)

def Retype.open_targ {env : TypeEnv s} {S : PureTy s} :
  Retype
    (env.extend_tvar (Ty.val_denot env S.core))
    (Subst.openTVar S)
    env
    ⟨CaptureSet.empty, .empty⟩ where
  var := fun x => by cases x; rfl
  tvar := fun
    | .here => by
      change Ty.val_denot env S.core ≈ Ty.val_denot env S.core
      apply Denot.eq_to_equiv; rfl
    | .there X => by
      change (env.extend_tvar (Ty.val_denot env S.core)).lookup_tvar X.there
        ≈ Ty.val_denot env (PureTy.tvar X).core
      apply Denot.eq_to_equiv
      unfold PureTy.tvar Ty.val_denot
      rfl
  cvar := fun
    | .there C => by
      change
        (env.lookup_cvar C).1 =
          (CaptureSet.cvar (.M Mutability.epsilon) C).subst (Subst.from_TypeEnv env)
      rfl
  var_peaks := fun b d => by
    cases b with
    | there z =>
      change env.HasPeak (.var (.M .epsilon) (.bound z)) d ↔
        env.HasPeak (((env.lookup_var z).2.cs.rename Rename.succ).subst (Subst.openTVar S)) d
      rw [CaptureSet.weaken_openTVar]
      refine TypeEnv.HasPeak.of_peaks_eq ?_
      rw [compute_peaks_peaksOnly_fixed (env.lookup_var z).2.h]
      rfl
  dpeak_cvar_back := fun c d hd => by
    cases c with
    | there c0 =>
      obtain ⟨hauth, a, hp⟩ := hd
      obtain ⟨-, heq⟩ := CaptureSet.cvar_subset_cvar_inv hp
      subst heq
      exact ⟨hauth, rfl⟩
  dpeak_cvar_unique := fun c d1 d2 hd1 hd2 => by
    cases c with
    | there c0 =>
      obtain ⟨-, a1, hp1⟩ := hd1
      obtain ⟨-, a2, hp2⟩ := hd2
      rw [(CaptureSet.cvar_subset_cvar_inv hp1).2, (CaptureSet.cvar_subset_cvar_inv hp2).2]
  dpeak_cvar_fwd := fun c hauth => by
    cases c with
    | there c0 =>
      exact ⟨c0, ⟨hauth, .M .epsilon, .refl⟩, rfl⟩
  dpeak_cvar_inj := fun c1 c2 d hd1 hd2 => by
    cases c1 with
    | there c01 =>
      cases c2 with
      | there c02 =>
        obtain ⟨-, a1, hp1⟩ := hd1
        obtain ⟨-, a2, hp2⟩ := hd2
        exact congrArg BVar.there
          (((CaptureSet.cvar_subset_cvar_inv hp1).2).symm.trans
            (CaptureSet.cvar_subset_cvar_inv hp2).2)

theorem open_targ_val_denot {env : TypeEnv s} {S : PureTy s} {T : Ty .capt (s,X)} :
  Ty.val_denot (env.extend_tvar (Ty.val_denot env S.core)) T ≈
    Ty.val_denot env (T.subst (Subst.openTVar S)) := by
  apply retype_val_denot Retype.open_targ

theorem open_targ_exi_val_denot {env : TypeEnv s} {S : PureTy s} {T : Ty .exi (s,X)} :
  Ty.exi_val_denot (env.extend_tvar (Ty.val_denot env S.core)) T ≈
    Ty.exi_val_denot env (T.subst (Subst.openTVar S)) := by
  apply retype_exi_val_denot Retype.open_targ

theorem open_targ_exi_exp_denot
    {env : TypeEnv s} {S : PureTy s} {T : Ty .exi (s,X)} {R : CapabilitySet} :
  Ty.exi_exp_denot (env.extend_tvar (Ty.val_denot env S.core)) T R ≈
    Ty.exi_exp_denot env (T.subst (Subst.openTVar S)) R := by
  apply retype_exi_exp_denot Retype.open_targ

/-- GAP (capture instantiation erases peak identity): opening a capture
binder with a capture set `C` is not a peak-faithful operation. On the source
side the bound variable `.here` is a single atomic peak with the stored
authority and capability; its image `C` may have zero (e.g. a ground witness
at `unpack`) or several (e.g. a union argument at `capp`) droppable peaks,
with unrelated capability sets. The `.here` branches of the droppable-peak
transport fields below are therefore `sorry`ed — each is refuted
definition-level in `CoreCapybara.Gaps` (`open_carg_dpeak_fwd_false`,
`open_carg_dpeak_unique_false`). The `.there` branches and the variable-peak
correspondence are proven. This is the precise way in which `Retype`/
`openCVar` transport "erases capture-variable identity and authority"
(see the `CoreCapybara.Gaps` module docstring): the closure premise
`env.DropSepIn cs` of `val_denot` cannot cross a `capp`/`unpack` boundary
when the budget peaks at the instantiated capture variable. -/
def Retype.open_carg {env : TypeEnv s} {C : CaptureSet s} (cap : CapabilitySet := .empty)
  (a : Authority := .access_only) :
  Retype
    (env.extend_cvar (C.subst (Subst.from_TypeEnv env)) cap a)
    (Subst.openCVar C)
    env
    ⟨CaptureSet.empty, .empty⟩ where
  var := fun x => by cases x; rfl
  tvar := fun
    | .there X => by
      change (env.extend_cvar (C.subst (Subst.from_TypeEnv env)) cap a).lookup_tvar X.there
        ≈ Ty.val_denot env (PureTy.tvar X).core
      apply Denot.eq_to_equiv
      unfold PureTy.tvar Ty.val_denot
      rfl
  cvar := fun
    | .here => by
      change C.subst (Subst.from_TypeEnv env) = C.subst (Subst.from_TypeEnv env)
      rfl
    | .there C0 => by
      change
        (env.lookup_cvar C0).1 =
          (CaptureSet.cvar (.M Mutability.epsilon) C0).subst (Subst.from_TypeEnv env)
      rfl
  var_peaks := fun b d => by
    cases b with
    | there z =>
      change env.HasPeak (.var (.M .epsilon) (.bound z)) d ↔
        env.HasPeak (((env.lookup_var z).2.cs.rename Rename.succ).subst (Subst.openCVar C)) d
      rw [CaptureSet.weaken_openCVar]
      refine TypeEnv.HasPeak.of_peaks_eq ?_
      rw [compute_peaks_peaksOnly_fixed (env.lookup_var z).2.h]
      rfl
  dpeak_cvar_back := fun c d hd => by
    cases c with
    | here =>
      -- GAP: a droppable peak of `C` need not match the stored authority and
      -- capability of the instantiated binder.
      sorry
    | there c0 =>
      obtain ⟨hauth, a', hp⟩ := hd
      obtain ⟨-, heq⟩ := CaptureSet.cvar_subset_cvar_inv hp
      subst heq
      exact ⟨hauth, rfl⟩
  dpeak_cvar_unique := fun c d1 d2 hd1 hd2 => by
    cases c with
    | here =>
      -- GAP: `C` may have several droppable peaks; refuted in
      -- `CoreCapybara.Gaps.open_carg_dpeak_unique_false`.
      sorry
    | there c0 =>
      obtain ⟨-, a1, hp1⟩ := hd1
      obtain ⟨-, a2, hp2⟩ := hd2
      rw [(CaptureSet.cvar_subset_cvar_inv hp1).2, (CaptureSet.cvar_subset_cvar_inv hp2).2]
  dpeak_cvar_fwd := fun c hauth => by
    cases c with
    | here =>
      -- GAP: a droppable binder may be instantiated with a peak-free (ground)
      -- capture set; refuted in `CoreCapybara.Gaps.open_carg_dpeak_fwd_false`.
      sorry
    | there c0 =>
      exact ⟨c0, ⟨hauth, .M .epsilon, .refl⟩, rfl⟩
  dpeak_cvar_inj := fun c1 c2 d hd1 hd2 => by
    cases c1 with
    | here =>
      cases c2 with
      | here => rfl
      | there c02 =>
        -- GAP: `C` may peak at a capture variable that is also a direct peak
        -- of the budget.
        sorry
    | there c01 =>
      cases c2 with
      | here =>
        -- GAP: symmetric to the previous branch.
        sorry
      | there c02 =>
        obtain ⟨-, a1, hp1⟩ := hd1
        obtain ⟨-, a2, hp2⟩ := hd2
        exact congrArg BVar.there
          (((CaptureSet.cvar_subset_cvar_inv hp1).2).symm.trans
            (CaptureSet.cvar_subset_cvar_inv hp2).2)

theorem open_carg_val_denot
    {env : TypeEnv s} {C : CaptureSet s} {T : Ty .capt (s,C)} (cap : CapabilitySet := .empty)
    (a : Authority := .access_only) :
  Ty.val_denot (env.extend_cvar (C.subst (Subst.from_TypeEnv env)) cap a) T ≈
    Ty.val_denot env (T.subst (Subst.openCVar C)) := by
  apply retype_val_denot (Retype.open_carg cap a)

theorem open_carg_exi_val_denot
    {env : TypeEnv s} {C : CaptureSet s} {T : Ty .exi (s,C)} (cap : CapabilitySet := .empty)
    (a : Authority := .access_only) :
  Ty.exi_val_denot (env.extend_cvar (C.subst (Subst.from_TypeEnv env)) cap a) T ≈
    Ty.exi_val_denot env (T.subst (Subst.openCVar C)) := by
  apply retype_exi_val_denot (Retype.open_carg cap a)

theorem open_carg_exi_exp_denot
    {env : TypeEnv s} {C : CaptureSet s} {T : Ty .exi (s,C)} {R : CapabilitySet}
    (cap : CapabilitySet := .empty) (a : Authority := .access_only) :
  Ty.exi_exp_denot (env.extend_cvar (C.subst (Subst.from_TypeEnv env)) cap a) T R ≈
    Ty.exi_exp_denot env (T.subst (Subst.openCVar C)) R := by
  apply retype_exi_exp_denot (Retype.open_carg cap a)

end CoreCapybara
