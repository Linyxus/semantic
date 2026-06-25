import Semantic.CoreCapybara.Denotation.Core
import Semantic.CoreCapybara.Denotation.Rebind
namespace CoreCapybara

open KripkeModel (StoreTyping WorldLe)

/-- Interpret a variable in an environment to get its free variable index. -/
def interp_var (env : TypeEnv s) (x : Var .var s) : Nat :=
  match x with
  | .free n => n
  | .bound x => (env.lookup_var x).1

/-! ### Peak machinery for transporting denotations along `Retype`

Peak membership (`HasPeak`) transports along environment rebindings, relating a
denotation under an environment to the denotation of its substitution. -/

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
  | arrow T1 cs T2 => exact Iff.rfl
  | poly T1 cs T2 => exact Iff.rfl
  | cpoly cb cs T => exact Iff.rfl
  | modal cs Ψ T => exact Iff.rfl
  | cap cs => exact Iff.rfl
  | cell cs => exact Iff.rfl
  | reader cs => exact Iff.rfl

structure Retype (env1 : TypeEnv s1) (σ : Subst s1 s2) (env2 : TypeEnv s2) (D : PeakSet s1) where
  var :
    ∀ (x : BVar s1 .var),
      (env1.lookup_var x).1 = interp_var env2 (σ.var x)

  tvar :
    ∀ (X : BVar s1 .tvar),
      IDenot.Equiv (env1.lookup_tvar X) (Ty.val_denot env2 (σ.tvar X).core)

  cvar :
    ∀ (C : BVar s1 .cvar),
      (env1.lookup_cvar C).1 = (σ.cvar C).subst (Subst.from_TypeEnv env2)

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
  (ρ : Retype env1 σ env2 D) :
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
        IDenot.Equiv (env1.lookup_tvar X)
          (Ty.val_denot (env2.extend_var x ps2) (((σ.tvar X).rename Rename.succ).core))
      apply IDenot.equiv_trans (ρ.tvar X)
      apply weaken_val_denot (ps:=ps2)
  cvar := fun
    | .there C => by
      change (env1.lookup_cvar C).1
        = ((σ.cvar C).rename Rename.succ).subst (Subst.from_TypeEnv (env2.extend_var x ps2))
      rw [ρ.cvar C]
      apply rebind_resolved_capture_set (Rebind.weaken (ps:=ps2))
theorem Retype.liftTVar
  {s1 s2 : Sig} {env1 : TypeEnv s1} {σ : Subst s1 s2} {env2 : TypeEnv s2} {D : PeakSet s1}
  {d : IDenot}
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
      change IDenot.Equiv d
        (Ty.val_denot (env2.extend_tvar d) (PureTy.tvar (BVar.here (s := s2))).core)
      intro k st m e
      unfold PureTy.tvar Ty.val_denot
      rfl
    | .there X => by
      change
        IDenot.Equiv (env1.lookup_tvar X)
          (Ty.val_denot (env2.extend_tvar d) (((σ.tvar X).rename Rename.succ).core))
      apply IDenot.equiv_trans (ρ.tvar X)
      apply tweaken_val_denot
  cvar := fun
    | .there C => by
      change (env1.lookup_cvar C).1
        = ((σ.cvar C).rename Rename.succ).subst (Subst.from_TypeEnv (env2.extend_tvar d))
      rw [ρ.cvar C]
      apply rebind_resolved_capture_set Rebind.tweaken
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
        IDenot.Equiv (env1.lookup_tvar X)
          (Ty.val_denot (env2.extend_cvar cs cap a) (((σ.tvar X).rename Rename.succ).core))
      apply IDenot.equiv_trans (ρ.tvar X)
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
-- cpoly case accumulates elaboration state across the mutual block
mutual

def retype_val_denot
  {s1 s2 : Sig} {env1 : TypeEnv s1} {σ : Subst s1 s2} {env2 : TypeEnv s2} {D : PeakSet s1}
  (ρ : Retype env1 σ env2 D) (T : Ty .capt s1) :
  IDenot.Equiv (Ty.val_denot env1 T) (Ty.val_denot env2 (T.subst σ)) :=
  match T with
  | .top | .unit | .bool => by
    intro k st m e
    simp [Ty.val_denot, Ty.subst]
  | .tvar X => by
    have h := ρ.tvar X
    intro k st m e
    simp only [Ty.val_denot, Ty.subst]
    exact h k st m e
  | .cap cs => by
    intro k st m e
    simp only [Ty.val_denot, Ty.subst]
    rw [← retype_resolved_capture_set ρ]
    rw [← retype_captureset_denot ρ cs]
  | .cell cs Tc | .reader cs Tc => by
    have ih := retype_val_denot ρ Tc
    have heq : Ty.val_denot env1 Tc = Ty.val_denot env2 (Tc.subst σ) := by
      funext k st m e; exact propext (ih k st m e)
    intro k st m e
    simp only [Ty.val_denot, Ty.subst]
    rw [← retype_resolved_capture_set ρ]
    rw [← retype_captureset_denot ρ cs]
    rw [heq]
  | .arrow T1 cs T2 => by
    have ih1 := retype_val_denot ρ T1
    intro k st m e
    simp only [Ty.val_denot, Ty.subst]
    rw [← retype_resolved_capture_set ρ]
    rw [← retype_captureset_denot ρ cs]
    constructor
    · intro ⟨hwf_e, hwf_cs, cs', T0, t0, hr, hwf_cs', hR0_sub, hd⟩
      refine ⟨hwf_e, hwf_cs, cs', T0, t0, hr, hwf_cs', hR0_sub, ?_⟩
      intro st' m' arg hwle hmt hcompat harg
      let ps1 := compute_peakset env1 T1.captureSet
      let ps2 := compute_peakset env2 (T1.subst σ).captureSet
      have ih2 := retype_exi_val_denot
        (ρ.liftVar (x:=arg) (ps1:=ps1) (ps2:=ps2)) T2
      have harg' := (ih1 k st' m' (.var (.free arg))).mpr harg
      have hd' := hd st' m' arg hwle hmt hcompat harg'
      refine eval_post_monotonic_general ?_ hd'
      intro m'' hsub'' t v hpost
      obtain ⟨htr, st'', hwle'', hmt'', hval, hpb, hwl⟩ := hpost
      exact ⟨htr, st'', hwle'', hmt'', (ih2 k st'' m'' v).mp hval, hpb, hwl⟩
    · intro ⟨hwf_e, hwf_cs, cs', T0, t0, hr, hwf_cs', hR0_sub, hd⟩
      refine ⟨hwf_e, hwf_cs, cs', T0, t0, hr, hwf_cs', hR0_sub, ?_⟩
      intro st' m' arg hwle hmt hcompat harg
      let ps1 := compute_peakset env1 T1.captureSet
      let ps2 := compute_peakset env2 (T1.subst σ).captureSet
      have ih2 := retype_exi_val_denot
        (ρ.liftVar (x:=arg) (ps1:=ps1) (ps2:=ps2)) T2
      have harg' := (ih1 k st' m' (.var (.free arg))).mp harg
      have hd' := hd st' m' arg hwle hmt hcompat harg'
      refine eval_post_monotonic_general ?_ hd'
      intro m'' hsub'' t v hpost
      obtain ⟨htr, st'', hwle'', hmt'', hval, hpb, hwl⟩ := hpost
      exact ⟨htr, st'', hwle'', hmt'', (ih2 k st'' m'' v).mpr hval, hpb, hwl⟩
  | .poly T1 cs T2 => by
    have ih1 := retype_val_denot ρ T1
    intro k st m e
    simp only [Ty.val_denot, Ty.subst]
    rw [← retype_resolved_capture_set ρ]
    rw [← retype_captureset_denot ρ cs]
    constructor
    · intro ⟨hwf_e, hwf_cs, cs', S0, t0, hr, hwf_cs', hR0_sub, hd⟩
      refine ⟨hwf_e, hwf_cs, cs', S0, t0, hr, hwf_cs', hR0_sub, ?_⟩
      intro st' m' denot hwle hmt hcompat hproper himply_simple_ans himply hpure
      have ih2 := retype_exi_val_denot (ρ.liftTVar (d:=denot)) T2
      have himply' : ∀ st'' m'', WorldLe st'' m'' st' m' → ∀ e',
          denot k st'' m'' e' → Ty.val_denot env1 T1 k st'' m'' e' := by
        intro st'' m'' hwle'' e' hdenot
        exact (ih1 k st'' m'' e').mpr (himply st'' m'' hwle'' e' hdenot)
      have hd' := hd st' m' denot hwle hmt hcompat hproper himply_simple_ans himply' hpure
      refine eval_post_monotonic_general ?_ hd'
      intro m'' hsub'' t v hpost
      obtain ⟨htr, st'', hwle3, hmt3, hval, hpb, hwl⟩ := hpost
      exact ⟨htr, st'', hwle3, hmt3, (ih2 k st'' m'' v).mp hval, hpb, hwl⟩
    · intro ⟨hwf_e, hwf_cs, cs', S0, t0, hr, hwf_cs', hR0_sub, hd⟩
      refine ⟨hwf_e, hwf_cs, cs', S0, t0, hr, hwf_cs', hR0_sub, ?_⟩
      intro st' m' denot hwle hmt hcompat hproper himply_simple_ans himply hpure
      have ih2 := retype_exi_val_denot (ρ.liftTVar (d:=denot)) T2
      have himply' : ∀ st'' m'', WorldLe st'' m'' st' m' → ∀ e',
          denot k st'' m'' e' → Ty.val_denot env2 (T1.subst σ) k st'' m'' e' := by
        intro st'' m'' hwle'' e' hdenot
        exact (ih1 k st'' m'' e').mp (himply st'' m'' hwle'' e' hdenot)
      have hd' := hd st' m' denot hwle hmt hcompat hproper himply_simple_ans himply' hpure
      refine eval_post_monotonic_general ?_ hd'
      intro m'' hsub'' t v hpost
      obtain ⟨htr, st'', hwle3, hmt3, hval, hpb, hwl⟩ := hpost
      exact ⟨htr, st'', hwle3, hmt3, (ih2 k st'' m'' v).mpr hval, hpb, hwl⟩
  | .cpoly B cs T => by
    have hB := retype_capturebound_denot ρ B
    intro k st m e
    simp only [Ty.val_denot, Ty.subst]
    rw [← retype_resolved_capture_set ρ]
    rw [← retype_captureset_denot ρ cs]
    rw [hB]
    constructor
    · intro ⟨hwf_e, hwf_cs, cs', B0, t0, hr, hwf_cs', hR0_sub, hd⟩
      refine ⟨hwf_e, hwf_cs, cs', B0, t0, hr, hwf_cs', hR0_sub, ?_⟩
      intro st' m' CS hwf_CS hdf hwle hmt hcompat hsub_bound
      have ih2 := retype_exi_val_denot (ρ.liftCVar (cs:=CS) (cap := CS.ground_denot m')) T
      have hd' := hd st' m' CS hwf_CS hdf hwle hmt hcompat hsub_bound
      refine eval_post_monotonic_general ?_ hd'
      intro m'' hsub'' t v hpost
      obtain ⟨htr, st'', hwle3, hmt3, hval, hpb, hwl⟩ := hpost
      exact ⟨htr, st'', hwle3, hmt3, (ih2 k st'' m'' v).mp hval, hpb, hwl⟩
    · intro ⟨hwf_e, hwf_cs, cs', B0, t0, hr, hwf_cs', hR0_sub, hd⟩
      refine ⟨hwf_e, hwf_cs, cs', B0, t0, hr, hwf_cs', hR0_sub, ?_⟩
      intro st' m' CS hwf_CS hdf hwle hmt hcompat hsub_bound
      have ih2 := retype_exi_val_denot (ρ.liftCVar (cs:=CS) (cap := CS.ground_denot m')) T
      have hd' := hd st' m' CS hwf_CS hdf hwle hmt hcompat hsub_bound
      refine eval_post_monotonic_general ?_ hd'
      intro m'' hsub'' t v hpost
      obtain ⟨htr, st'', hwle3, hmt3, hval, hpb, hwl⟩ := hpost
      exact ⟨htr, st'', hwle3, hmt3, (ih2 k st'' m'' v).mpr hval, hpb, hwl⟩
  | .modal cs Ψ T => by
    intro k st m e
    simp only [Ty.val_denot, Ty.subst]
    rw [← retype_resolved_capture_set ρ]
    rw [← retype_captureset_denot ρ cs]
    constructor
    · rintro ⟨hwf_e, hwf_cs, cs0, sepctx0, t0, hres, hwf_cs0, hwf_sepctx0,
        hsat, hR0_sub, hbody⟩
      refine ⟨hwf_e, hwf_cs, cs0, sepctx0, t0, hres, hwf_cs0, hwf_sepctx0, ?_, hR0_sub, ?_⟩
      · intro m' hsub hsat'
        exact hsat m' hsub ((retype_satisfy_iff ρ Ψ m').mpr hsat')
      · intro st' m' hwle hmt hcompat hkind hsep
        have ih := retype_exi_val_denot ρ T
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
        have hd' := hbody st' m' hwle hmt hcompat hkind' hsep'
        refine eval_post_monotonic_general ?_ hd'
        intro m'' hsub'' t v hpost
        obtain ⟨htr, st'', hwle3, hmt3, hval, hpb, hwl⟩ := hpost
        exact ⟨htr, st'', hwle3, hmt3, (ih k st'' m'' v).mp hval, hpb, hwl⟩
    · rintro ⟨hwf_e, hwf_cs, cs0, sepctx0, t0, hres, hwf_cs0, hwf_sepctx0,
        hsat, hR0_sub, hbody⟩
      refine ⟨hwf_e, hwf_cs, cs0, sepctx0, t0, hres, hwf_cs0, hwf_sepctx0, ?_, hR0_sub, ?_⟩
      · intro m' hsub hsat'
        exact hsat m' hsub ((retype_satisfy_iff ρ Ψ m').mp hsat')
      · intro st' m' hwle hmt hcompat hkind hsep
        have ih := retype_exi_val_denot ρ T
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
        have hd' := hbody st' m' hwle hmt hcompat hkind' hsep'
        refine eval_post_monotonic_general ?_ hd'
        intro m'' hsub'' t v hpost
        obtain ⟨htr, st'', hwle3, hmt3, hval, hpb, hwl⟩ := hpost
        exact ⟨htr, st'', hwle3, hmt3, (ih k st'' m'' v).mpr hval, hpb, hwl⟩

def retype_exi_val_denot
  {s1 s2 : Sig} {env1 : TypeEnv s1} {σ : Subst s1 s2} {env2 : TypeEnv s2} {D : PeakSet s1}
  (ρ : Retype env1 σ env2 D) (T : Ty .exi s1) :
  IDenot.Equiv (Ty.exi_val_denot env1 T) (Ty.exi_val_denot env2 (T.subst σ)) :=
  match T with
  | .typ T => by
    have ih := retype_val_denot ρ T
    intro k st m e
    simp only [Ty.exi_val_denot, Ty.subst]
    exact ih k st m e
  | .exi T => by
    intro k st m e
    simp only [Ty.exi_val_denot, Ty.subst]
    cases hresolve : resolve m.heap e
    · simp only
    · rename_i e'
      cases e'
      case pack =>
        rename_i CS y
        simp only [List.empty_eq, and_congr_right_iff]
        intro _hwf _hdf
        exact retype_val_denot
          (ρ.liftCVar (cs:=CS) (cap:=CS.ground_denot m) (a:=.can_drop)) T k st m (Exp.var y)
      all_goals {
        simp only
      }

def retype_exi_exp_denot
  {s1 s2 : Sig} {env1 : TypeEnv s1} {σ : Subst s1 s2} {env2 : TypeEnv s2} {D : PeakSet s1}
  (ρ : Retype env1 σ env2 D) (T : Ty .exi s1) (R : CapabilitySet) :
  IDenot.Equiv (Ty.exi_exp_denot env1 T R) (Ty.exi_exp_denot env2 (T.subst σ) R) := by
  have ih := retype_exi_val_denot ρ T
  intro k st m e
  simp only [Ty.exi_exp_denot]
  constructor
  · intro h hmt
    refine eval_post_monotonic_general ?_ (h hmt)
    intro mm hsub t v hpost
    obtain ⟨htr, st', hwle, hmt', hval, hpb, hwl⟩ := hpost
    exact ⟨htr, st', hwle, hmt', (ih k st' mm v).mp hval, hpb, hwl⟩
  · intro h hmt
    refine eval_post_monotonic_general ?_ (h hmt)
    intro mm hsub t v hpost
    obtain ⟨htr, st', hwle, hmt', hval, hpb, hwl⟩ := hpost
    exact ⟨htr, st', hwle, hmt', (ih k st' mm v).mpr hval, hpb, hwl⟩

end

def Retype.open_arg {s : Sig} {env : TypeEnv s} {y : Var .var s} {ps : PeakSet s} :
  Retype
    (env.extend_var (interp_var env y) ps)
    (Subst.openVar y)
    env
    ⟨CaptureSet.empty, .empty⟩ where
  var := fun x => by cases x <;> rfl
  tvar := fun
    | .there X => by
      change IDenot.Equiv (env.lookup_tvar X) (Ty.val_denot env (PureTy.tvar X).core)
      intro k st m e
      unfold PureTy.tvar Ty.val_denot
      rfl
  cvar := fun
    | .there C => by
      change
        (env.lookup_cvar C).1 =
          (CaptureSet.cvar (.M Mutability.epsilon) C).subst (Subst.from_TypeEnv env)
      rfl
theorem open_arg_val_denot
    {env : TypeEnv s} {y : Var .var s} {ps : PeakSet s} {T : Ty .capt (s,x)} :
  IDenot.Equiv (Ty.val_denot (env.extend_var (interp_var env y) ps) T)
    (Ty.val_denot env (T.subst (Subst.openVar y))) := by
  apply retype_val_denot (Retype.open_arg (ps := ps))

theorem open_arg_exi_val_denot
    {env : TypeEnv s} {y : Var .var s} {ps : PeakSet s} {T : Ty .exi (s,x)} :
  IDenot.Equiv (Ty.exi_val_denot (env.extend_var (interp_var env y) ps) T)
    (Ty.exi_val_denot env (T.subst (Subst.openVar y))) := by
  apply retype_exi_val_denot (Retype.open_arg (ps := ps))

theorem open_arg_exi_exp_denot
    {env : TypeEnv s} {y : Var .var s} {ps : PeakSet s}
    {T : Ty .exi (s,x)} {R : CapabilitySet} :
  IDenot.Equiv (Ty.exi_exp_denot (env.extend_var (interp_var env y) ps) T R)
    (Ty.exi_exp_denot env (T.subst (Subst.openVar y)) R) := by
  apply retype_exi_exp_denot (Retype.open_arg (ps := ps))

def Retype.open_targ {env : TypeEnv s} {S : PureTy s} :
  Retype
    (env.extend_tvar (Ty.val_denot env S.core))
    (Subst.openTVar S)
    env
    ⟨CaptureSet.empty, .empty⟩ where
  var := fun x => by cases x; rfl
  tvar := fun
    | .here => by
      change IDenot.Equiv (Ty.val_denot env S.core) (Ty.val_denot env S.core)
      exact IDenot.equiv_refl _
    | .there X => by
      change IDenot.Equiv ((env.extend_tvar (Ty.val_denot env S.core)).lookup_tvar X.there)
        (Ty.val_denot env (PureTy.tvar X).core)
      intro k st m e
      unfold PureTy.tvar Ty.val_denot
      rfl
  cvar := fun
    | .there C => by
      change
        (env.lookup_cvar C).1 =
          (CaptureSet.cvar (.M Mutability.epsilon) C).subst (Subst.from_TypeEnv env)
      rfl
theorem open_targ_val_denot {env : TypeEnv s} {S : PureTy s} {T : Ty .capt (s,X)} :
  IDenot.Equiv (Ty.val_denot (env.extend_tvar (Ty.val_denot env S.core)) T)
    (Ty.val_denot env (T.subst (Subst.openTVar S))) := by
  apply retype_val_denot Retype.open_targ

theorem open_targ_exi_val_denot {env : TypeEnv s} {S : PureTy s} {T : Ty .exi (s,X)} :
  IDenot.Equiv (Ty.exi_val_denot (env.extend_tvar (Ty.val_denot env S.core)) T)
    (Ty.exi_val_denot env (T.subst (Subst.openTVar S))) := by
  apply retype_exi_val_denot Retype.open_targ

theorem open_targ_exi_exp_denot
    {env : TypeEnv s} {S : PureTy s} {T : Ty .exi (s,X)} {R : CapabilitySet} :
  IDenot.Equiv (Ty.exi_exp_denot (env.extend_tvar (Ty.val_denot env S.core)) T R)
    (Ty.exi_exp_denot env (T.subst (Subst.openTVar S)) R) := by
  apply retype_exi_exp_denot Retype.open_targ

/-- Opening a capture binder by substituting the capture set `C` for the
innermost bound capture variable. -/
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
      change IDenot.Equiv
        ((env.extend_cvar (C.subst (Subst.from_TypeEnv env)) cap a).lookup_tvar X.there)
        (Ty.val_denot env (PureTy.tvar X).core)
      intro k st m e
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
theorem open_carg_val_denot
    {env : TypeEnv s} {C : CaptureSet s} {T : Ty .capt (s,C)} (cap : CapabilitySet := .empty)
    (a : Authority := .access_only) :
  IDenot.Equiv (Ty.val_denot (env.extend_cvar (C.subst (Subst.from_TypeEnv env)) cap a) T)
    (Ty.val_denot env (T.subst (Subst.openCVar C))) := by
  apply retype_val_denot (Retype.open_carg cap a)

theorem open_carg_exi_val_denot
    {env : TypeEnv s} {C : CaptureSet s} {T : Ty .exi (s,C)} (cap : CapabilitySet := .empty)
    (a : Authority := .access_only) :
  IDenot.Equiv (Ty.exi_val_denot (env.extend_cvar (C.subst (Subst.from_TypeEnv env)) cap a) T)
    (Ty.exi_val_denot env (T.subst (Subst.openCVar C))) := by
  apply retype_exi_val_denot (Retype.open_carg cap a)

theorem open_carg_exi_exp_denot
    {env : TypeEnv s} {C : CaptureSet s} {T : Ty .exi (s,C)} {R : CapabilitySet}
    (cap : CapabilitySet := .empty) (a : Authority := .access_only) :
  IDenot.Equiv (Ty.exi_exp_denot (env.extend_cvar (C.subst (Subst.from_TypeEnv env)) cap a) T R)
    (Ty.exi_exp_denot env (T.subst (Subst.openCVar C)) R) := by
  apply retype_exi_exp_denot (Retype.open_carg cap a)

end CoreCapybara
