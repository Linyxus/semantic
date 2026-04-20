import Semantic.Consume.Denotation.Core
import Semantic.Consume.Denotation.Rebind
namespace Consume

/-- Interpret a variable in an environment to get its free variable index. -/
def interp_var (env : TypeEnv s) (x : Var .var s) : Nat :=
  match x with
  | .free n => n
  | .bound x => (env.lookup_var x).1

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

lemma weaken_interp_var {x : Var .var s} {ps : PeakSet s} :
  interp_var env x = interp_var (env.extend_var n ps) (x.rename Rename.succ) := by
  cases x <;> rfl

lemma tweaken_interp_var {x : Var .var s} :
  interp_var env x = interp_var (env.extend_tvar d) (x.rename Rename.succ) := by
  cases x <;> rfl

lemma cweaken_interp_var {cs : CaptureSet {}} {cap : CapabilitySet} {x : Var .var s} :
  interp_var env x = interp_var (env.extend_cvar cs cap) (x.rename Rename.succ) := by
  cases x <;> rfl

theorem Retype.liftVar
  {s1 s2 : Sig} {env1 : TypeEnv s1} {σ : Subst s1 s2} {env2 : TypeEnv s2} {D : PeakSet s1}
  {x : Nat} {ps1 : PeakSet s1} {ps2 : PeakSet s2}
  (ρ : Retype env1 σ env2 D) :
  Retype (env1.extend_var x ps1) (σ.lift) (env2.extend_var x ps2) (D.rename Rename.succ) where
  var := fun
    | .here => rfl
    | .there y => by
      conv =>
        lhs
        simp only [TypeEnv.extend_var, TypeEnv.lookup_var]
      conv =>
        rhs
        simp only [Subst.lift]
        simp only [<-weaken_interp_var (ps:=ps2)]
      exact ρ.var y
  tvar := fun
    | .there X => by
      conv =>
        lhs
        simp only [TypeEnv.extend_var, TypeEnv.lookup_tvar]
      conv =>
        rhs
        simp only [Subst.lift]
      apply Denot.equiv_trans _ _ _ (ρ.tvar X)
      apply weaken_val_denot (ps:=ps2)
  cvar := fun
    | .there C => by
      simp only [TypeEnv.extend_var, Subst.lift, TypeEnv.lookup_cvar]
      rw [ρ.cvar C]
      apply rebind_resolved_capture_set (Rebind.weaken (ps:=ps2))

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
    | refl => exact hcov''
    | ro_eps => exact CaptureSet.CoveredBy.mut_mono_left Mutability.Le.ro_eps hcov''
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
    simp [CaptureSet.drop_here_cvar, CaptureSet.rename,
          ih1 hcov.union_coveredby_left, ih2 hcov.union_coveredby_right]
  | var m x => cases x with
    | free n => simp [CaptureSet.drop_here_cvar, CaptureSet.rename, Var.rename, Rename.succ]
    | bound x => cases x with
      | there x => simp [CaptureSet.drop_here_cvar, CaptureSet.rename, Var.rename, Rename.succ]
  | cvar m c => cases c with
    | here =>
      simp only [compute_peaks] at hcov
      obtain ⟨m', _, hsub⟩ := CaptureSet.CoveredBy.cvar_subset_coveredby CaptureSet.Subset.refl hcov
      obtain ⟨c', hfc, _⟩ := D.h.cvar_subset_rename_inv hsub
      simp [Rename.succ] at hfc
    | there c => simp [CaptureSet.drop_here_cvar, CaptureSet.rename, Rename.succ]

private lemma drop_here_tvar_rename_succ (cs : CaptureSet (s,X)) :
    cs.drop_here_tvar.rename (Rename.succ (k := .tvar)) = cs := by
  induction cs with
  | empty => rfl
  | union cs1 cs2 ih1 ih2 => simp [CaptureSet.drop_here_tvar, CaptureSet.rename, ih1, ih2]
  | var m x => cases x with
    | free n => simp [CaptureSet.drop_here_tvar, CaptureSet.rename, Var.rename, Rename.succ]
    | bound x => cases x with
      | there x => simp [CaptureSet.drop_here_tvar, CaptureSet.rename, Var.rename, Rename.succ]
  | cvar m c => cases c with
    | there c => simp [CaptureSet.drop_here_tvar, CaptureSet.rename, Rename.succ]

private lemma subst_lift_eq_subst_rename
    {k : Kind} (cs0 : CaptureSet s1) (σ : Subst s1 s2) :
    (cs0.rename (Rename.succ (k := k))).subst (σ.lift (k := k)) =
      (cs0.subst σ).rename (Rename.succ (k := k)) := by
  induction cs0 with
  | empty => rfl
  | union cs1 cs2 ih1 ih2 => simp [CaptureSet.subst, CaptureSet.rename, ih1, ih2]
  | var m x => cases x with
    | free n =>
      simp [CaptureSet.subst, CaptureSet.rename, Var.subst, Var.rename,
        Subst.lift, Rename.succ]
    | bound x =>
      simp [CaptureSet.subst, CaptureSet.rename, Var.subst, Var.rename,
        Subst.lift, Rename.succ]
  | cvar m c =>
      simp [CaptureSet.subst, CaptureSet.rename, Subst.lift, Rename.succ,
        CaptureSet.applyMut_rename]

theorem Retype.liftTVar
  {s1 s2 : Sig} {env1 : TypeEnv s1} {σ : Subst s1 s2} {env2 : TypeEnv s2} {D : PeakSet s1}
  {d : Denot}
  (ρ : Retype env1 σ env2 D) :
  Retype (env1.extend_tvar d) (σ.lift) (env2.extend_tvar d) (D.rename Rename.succ) where
  var := fun
    | .there x => by
      conv => lhs; simp [TypeEnv.extend_tvar, TypeEnv.lookup_var]
      conv => rhs; simp [Subst.lift, <-tweaken_interp_var]
      exact ρ.var x
  tvar := fun
    | .here => by
      apply Denot.eq_to_equiv
      simp [TypeEnv.extend_tvar, TypeEnv.lookup_tvar, Subst.lift,
            PureTy.tvar, Ty.val_denot]
    | .there X => by
      conv =>
        lhs
        simp [TypeEnv.extend_tvar, TypeEnv.lookup_tvar]
      conv =>
        rhs
        simp [Subst.lift]
      apply Denot.equiv_trans _ _ _ (ρ.tvar X)
      apply tweaken_val_denot
  cvar := fun
    | .there C => by
      simp [TypeEnv.extend_tvar, Subst.lift]
      change (env1.lookup_cvar C).1 = _
      rw [ρ.cvar C]
      apply rebind_resolved_capture_set Rebind.tweaken

theorem Retype.liftCVar
  {s1 s2 : Sig} {env1 : TypeEnv s1} {σ : Subst s1 s2} {env2 : TypeEnv s2} {D : PeakSet s1}
  (ρ : Retype env1 σ env2 D) (cs : CaptureSet {}) (cap : CapabilitySet := .empty) :
  Retype (env1.extend_cvar cs cap) (σ.lift) (env2.extend_cvar cs cap) (D.rename Rename.succ) where
  var := fun
    | .there x => by
      conv => lhs; simp [TypeEnv.extend_cvar, TypeEnv.lookup_var]
      conv => rhs; simp [Subst.lift, <-cweaken_interp_var]
      exact ρ.var x
  tvar := fun
    | .there X => by
      conv =>
        lhs
        simp [TypeEnv.extend_cvar, TypeEnv.lookup_tvar]
      conv =>
        rhs
        simp [Subst.lift]
      apply Denot.equiv_trans _ _ _ (ρ.tvar X)
      apply cweaken_val_denot
  cvar := fun
    | .here => by
      simp [TypeEnv.extend_cvar, TypeEnv.lookup_cvar, Subst.lift,
        CaptureSet.subst, Subst.from_TypeEnv]
    | .there C => by
      simp [TypeEnv.extend_cvar, Subst.lift]
      change (env1.lookup_cvar C).1 = _
      rw [ρ.cvar C]
      apply rebind_resolved_capture_set Rebind.cweaken

def retype_resolved_capture_set
  {s1 s2 : Sig} {env1 : TypeEnv s1} {σ : Subst s1 s2} {env2 : TypeEnv s2} {D : PeakSet s1}
  (ρ : Retype env1 σ env2 D) (C : CaptureSet s1) :
  C.subst (Subst.from_TypeEnv env1) = (C.subst σ).subst (Subst.from_TypeEnv env2) := by
  induction C
  case empty => rfl
  case union C1 C2 ih1 ih2 =>
    simp [CaptureSet.subst, ih1, ih2]
  case var x =>
    cases x
    case bound x =>
      simp [CaptureSet.subst, Var.subst]
      have := ρ.var x
      cases hσ : σ.var x
      case bound y =>
        simp [Subst.from_TypeEnv, interp_var] at this ⊢
        rw [hσ] at this
        simp at this
        rw [this]
      case free n =>
        simp [Subst.from_TypeEnv, interp_var] at this ⊢
        rw [hσ] at this
        simp at this
        rw [this]
    case free n =>
      simp [CaptureSet.subst, Var.subst]
  case cvar m C =>
    simp [CaptureSet.subst]
    cases m
    · -- epsilon case: applyMut .epsilon is identity
      exact ρ.cvar C
    · -- ro case: applyMut .ro applies applyRO
      conv => lhs; simp only [Subst.from_TypeEnv]; rw [ρ.cvar C]
      simp [CaptureSet.applyRO_subst]

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

set_option maxHeartbeats 800000 in
-- The cpoly case requires more heartbeats due to accumulated elaboration state in the mutual block.
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
    simp [Ty.val_denot, Ty.subst]
    exact h m e
  | .cap cs | .cell cs | .reader cs => by
    intro m e
    simp only [Ty.val_denot, Ty.subst]
    rw [← retype_resolved_capture_set ρ]
    rw [← retype_captureset_denot ρ cs]
  | .arrow T1 cs T2 => by
    have ih1 := retype_val_denot ρ T1
    intro m e
    simp only [Ty.val_denot, Ty.subst]
    rw [← retype_resolved_capture_set ρ]
    rw [← retype_captureset_denot ρ cs]
    constructor
    · intro ⟨hwf_e, hwf_cs, cs', T0, t0, hr, hwf_cs', hR0_sub, hd⟩
      refine ⟨hwf_e, hwf_cs, cs', T0, t0, hr, hwf_cs', hR0_sub, ?_⟩
      intro arg m' hsub harg
      let R0 := expand_captures m.heap cs'
      let ps1 := compute_peakset env1 T1.captureSet
      let ps2 := compute_peakset env2 (T1.subst σ).captureSet
      have ih2 := retype_exi_exp_denot (ρ.liftVar (x:=arg) (ps1:=ps1) (ps2:=ps2)) T2 R0
      have harg' := (ih1 m' (.var (.free arg))).mpr harg
      specialize hd arg m' hsub harg'
      exact (ih2 m' _).mp hd
    · intro ⟨hwf_e, hwf_cs, cs', T0, t0, hr, hwf_cs', hR0_sub, hd⟩
      refine ⟨hwf_e, hwf_cs, cs', T0, t0, hr, hwf_cs', hR0_sub, ?_⟩
      intro arg m' hsub harg
      let R0 := expand_captures m.heap cs'
      let ps1 := compute_peakset env1 T1.captureSet
      let ps2 := compute_peakset env2 (T1.subst σ).captureSet
      have ih2 := retype_exi_exp_denot (ρ.liftVar (x:=arg) (ps1:=ps1) (ps2:=ps2)) T2 R0
      have harg' := (ih1 m' (.var (.free arg))).mp harg
      specialize hd arg m' hsub harg'
      exact (ih2 m' _).mpr hd
  | .poly T1 cs T2 => by
    have ih1 := retype_val_denot ρ T1
    intro m e
    simp only [Ty.val_denot, Ty.subst]
    rw [← retype_resolved_capture_set ρ]
    rw [← retype_captureset_denot ρ cs]
    constructor
    · intro ⟨hwf_e, hwf_cs, cs', S0, t0, hr, hwf_cs', hR0_sub, hd⟩
      refine ⟨hwf_e, hwf_cs, cs', S0, t0, hr, hwf_cs', hR0_sub, ?_⟩
      intro m' denot hsub hproper himply_simple_ans himply hpure
      let R0 := expand_captures m.heap cs'
      have ih2 := retype_exi_exp_denot (ρ.liftTVar (d:=denot)) T2 R0
      have himply' : denot.ImplyAfter m' (Ty.val_denot env1 T1) := by
        intro m'' hsub' e' hdenot
        exact (ih1 m'' e').mpr (himply m'' hsub' e' hdenot)
      specialize hd m' denot hsub hproper himply_simple_ans himply' hpure
      exact (ih2 m' _).mp hd
    · intro ⟨hwf_e, hwf_cs, cs', S0, t0, hr, hwf_cs', hR0_sub, hd⟩
      refine ⟨hwf_e, hwf_cs, cs', S0, t0, hr, hwf_cs', hR0_sub, ?_⟩
      intro m' denot hsub hproper himply_simple_ans himply hpure
      let R0 := expand_captures m.heap cs'
      have ih2 := retype_exi_exp_denot (ρ.liftTVar (d:=denot)) T2 R0
      have himply' : denot.ImplyAfter m' (Ty.val_denot env2 (T1.subst σ)) := by
        intro m'' hsub' e' hdenot
        exact (ih1 m'' e').mp (himply m'' hsub' e' hdenot)
      specialize hd m' denot hsub hproper himply_simple_ans himply' hpure
      exact (ih2 m' _).mpr hd
  | .cpoly B cs T => by
    have hB := retype_capturebound_denot ρ B
    intro m e
    simp only [Ty.val_denot, Ty.subst]
    rw [← retype_resolved_capture_set ρ]
    rw [← retype_captureset_denot ρ cs]
    rw [hB]
    constructor
    · intro ⟨hwf_e, hwf_cs, cs', B0, t0, hr, hwf_cs', hR0_sub, hd⟩
      refine ⟨hwf_e, hwf_cs, cs', B0, t0, hr, hwf_cs', hR0_sub, ?_⟩
      intro m' CS hwf_CS hsub hsub_bound
      let R0 := expand_captures m.heap cs'
      let cap1 : CapabilitySet := CS.ground_denot m'
      let ρ1 : Retype (env1.extend_cvar CS cap1) σ.lift
                      (env2.extend_cvar CS cap1) (D.rename Rename.succ) :=
        ρ.liftCVar (cs:=CS) (cap:=cap1)
      have ih2 := retype_exi_exp_denot ρ1 T R0
      specialize hd m' CS hwf_CS hsub hsub_bound
      exact (ih2 m' _).mp hd
    · intro ⟨hwf_e, hwf_cs, cs', B0, t0, hr, hwf_cs', hR0_sub, hd⟩
      refine ⟨hwf_e, hwf_cs, cs', B0, t0, hr, hwf_cs', hR0_sub, ?_⟩
      intro m' CS hwf_CS hsub hsub_bound
      let R0 := expand_captures m.heap cs'
      let cap2 : CapabilitySet := CS.ground_denot m'
      let ρ2 : Retype (env1.extend_cvar CS cap2) σ.lift
                      (env2.extend_cvar CS cap2) (D.rename Rename.succ) :=
        ρ.liftCVar (cs:=CS) (cap:=cap2)
      have ih2 := retype_exi_exp_denot ρ2 T R0
      specialize hd m' CS hwf_CS hsub hsub_bound
      exact (ih2 m' _).mpr hd

def retype_exi_val_denot
  {s1 s2 : Sig} {env1 : TypeEnv s1} {σ : Subst s1 s2} {env2 : TypeEnv s2} {D : PeakSet s1}
  (ρ : Retype env1 σ env2 D) (T : Ty .exi s1) :
  Ty.exi_val_denot env1 T ≈ Ty.exi_val_denot env2 (T.subst σ) :=
  match T with
  | .typ T => by
    have ih := retype_val_denot ρ T
    intro s e
    simp [Ty.exi_val_denot, Ty.subst]
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
        simp
        -- Goal: CS.WfInHeap s.heap → (... ↔ ...)
        intro _hwf
        have ih := retype_val_denot (ρ.liftCVar (cs:=CS) (cap:=CS.ground_denot s)) T
        exact ih s (Exp.var y)
      all_goals {
        -- resolve returned non-pack
        simp
      }

def retype_exp_denot
  {s1 s2 : Sig} {env1 : TypeEnv s1} {σ : Subst s1 s2} {env2 : TypeEnv s2} {D : PeakSet s1}
  (ρ : Retype env1 σ env2 D) (T : Ty .capt s1) (R : CapabilitySet) :
  Ty.exp_denot env1 T R ≈ Ty.exp_denot env2 (T.subst σ) R := by
  have ih := retype_val_denot ρ T
  intro m e
  simp [Ty.exp_denot]
  constructor
  · intro h
    apply eval_post_monotonic _ h
    apply Denot.imply_to_entails
    exact (Denot.equiv_to_imply ih).1
  · intro h
    apply eval_post_monotonic _ h
    apply Denot.imply_to_entails
    exact (Denot.equiv_to_imply ih).2

def retype_exi_exp_denot
  {s1 s2 : Sig} {env1 : TypeEnv s1} {σ : Subst s1 s2} {env2 : TypeEnv s2} {D : PeakSet s1}
  (ρ : Retype env1 σ env2 D) (T : Ty .exi s1) (R : CapabilitySet) :
  Ty.exi_exp_denot env1 T R ≈ Ty.exi_exp_denot env2 (T.subst σ) R := by
  have ih := retype_exi_val_denot ρ T
  intro m e
  simp [Ty.exi_exp_denot]
  constructor
  · intro h
    apply eval_post_monotonic _ h
    apply Denot.imply_to_entails
    exact (Denot.equiv_to_imply ih).1
  · intro h
    apply eval_post_monotonic _ h
    apply Denot.imply_to_entails
    exact (Denot.equiv_to_imply ih).2

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
      apply Denot.eq_to_equiv
      simp [TypeEnv.extend_var, TypeEnv.lookup_tvar, Subst.openVar,
            PureTy.tvar, Ty.val_denot]
  cvar := fun
    | .there C => by
      simp [TypeEnv.extend_var, Subst.openVar, TypeEnv.lookup_cvar,
        CaptureSet.subst, Subst.from_TypeEnv]

theorem open_arg_val_denot
    {env : TypeEnv s} {y : Var .var s} {ps : PeakSet s} {T : Ty .capt (s,x)} :
  Ty.val_denot (env.extend_var (interp_var env y) ps) T ≈
    Ty.val_denot env (T.subst (Subst.openVar y)) := by
  apply retype_val_denot Retype.open_arg

theorem open_arg_exi_val_denot
    {env : TypeEnv s} {y : Var .var s} {ps : PeakSet s} {T : Ty .exi (s,x)} :
  Ty.exi_val_denot (env.extend_var (interp_var env y) ps) T ≈
    Ty.exi_val_denot env (T.subst (Subst.openVar y)) := by
  apply retype_exi_val_denot Retype.open_arg

theorem open_arg_exi_exp_denot
    {env : TypeEnv s} {y : Var .var s} {ps : PeakSet s}
    {T : Ty .exi (s,x)} {R : CapabilitySet} :
  Ty.exi_exp_denot (env.extend_var (interp_var env y) ps) T R ≈
    Ty.exi_exp_denot env (T.subst (Subst.openVar y)) R := by
  apply retype_exi_exp_denot Retype.open_arg

def Retype.open_targ {env : TypeEnv s} {S : PureTy s} :
  Retype
    (env.extend_tvar (Ty.val_denot env S.core))
    (Subst.openTVar S)
    env
    ⟨CaptureSet.empty, .empty⟩ where
  var := fun x => by cases x; rfl
  tvar := fun
    | .here => by
      apply Denot.eq_to_equiv
      simp [TypeEnv.extend_tvar, TypeEnv.lookup_tvar, Subst.openTVar]
    | .there X => by
      apply Denot.eq_to_equiv
      simp [TypeEnv.extend_tvar, TypeEnv.lookup_tvar, Subst.openTVar,
            PureTy.tvar, Ty.val_denot]
  cvar := fun
    | .there C => by
      simp [TypeEnv.extend_tvar, Subst.openTVar, TypeEnv.lookup_cvar,
        CaptureSet.subst, Subst.from_TypeEnv]

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

def Retype.open_carg {env : TypeEnv s} {C : CaptureSet s} (cap : CapabilitySet := .empty) :
  Retype
    (env.extend_cvar (C.subst (Subst.from_TypeEnv env)) cap)
    (Subst.openCVar C)
    env
    ⟨CaptureSet.empty, .empty⟩ where
  var := fun x => by cases x; rfl
  tvar := fun
    | .there X => by
      apply Denot.eq_to_equiv
      simp [TypeEnv.lookup_tvar, Subst.openCVar, TypeEnv.extend_cvar,
            PureTy.tvar, Ty.val_denot]
  cvar := fun
    | .here => by
      simp [TypeEnv.lookup_cvar, Subst.openCVar, TypeEnv.extend_cvar]
    | .there C => by
      simp [Subst.openCVar, TypeEnv.lookup_cvar, TypeEnv.extend_cvar,
        CaptureSet.subst, Subst.from_TypeEnv]

theorem open_carg_val_denot
    {env : TypeEnv s} {C : CaptureSet s} {T : Ty .capt (s,C)} (cap : CapabilitySet := .empty) :
  Ty.val_denot (env.extend_cvar (C.subst (Subst.from_TypeEnv env)) cap) T ≈
    Ty.val_denot env (T.subst (Subst.openCVar C)) := by
  apply retype_val_denot (Retype.open_carg cap)

theorem open_carg_exi_val_denot
    {env : TypeEnv s} {C : CaptureSet s} {T : Ty .exi (s,C)} (cap : CapabilitySet := .empty) :
  Ty.exi_val_denot (env.extend_cvar (C.subst (Subst.from_TypeEnv env)) cap) T ≈
    Ty.exi_val_denot env (T.subst (Subst.openCVar C)) := by
  apply retype_exi_val_denot (Retype.open_carg cap)

theorem open_carg_exi_exp_denot
    {env : TypeEnv s} {C : CaptureSet s} {T : Ty .exi (s,C)} {R : CapabilitySet}
    (cap : CapabilitySet := .empty) :
  Ty.exi_exp_denot (env.extend_cvar (C.subst (Subst.from_TypeEnv env)) cap) T R ≈
    Ty.exi_exp_denot env (T.subst (Subst.openCVar C)) R := by
  apply retype_exi_exp_denot (Retype.open_carg cap)

end Consume
