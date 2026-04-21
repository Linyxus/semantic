import Semantic.ModalCapybara.Denotation.Core
import Semantic.ModalCapybara.Denotation.Rebind
namespace ModalCapybara

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

private lemma subst_lift_eq_subst_rename
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
    change CaptureSet.applyMut m ((σ.cvar c).rename Rename.succ) =
      ((σ.cvar c).applyMut m).rename Rename.succ
    exact CaptureSet.applyMut_rename.symm

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

theorem Retype.liftCVar
  {s1 s2 : Sig} {env1 : TypeEnv s1} {σ : Subst s1 s2} {env2 : TypeEnv s2} {D : PeakSet s1}
  (ρ : Retype env1 σ env2 D) (cs : CaptureSet {}) (cap : CapabilitySet := .empty) :
  Retype (env1.extend_cvar cs cap) (σ.lift) (env2.extend_cvar cs cap) (D.rename Rename.succ) where
  var := fun
    | .there x => by
      change (env1.lookup_var x).1
        = interp_var (env2.extend_cvar cs cap) ((σ.var x).rename Rename.succ)
      rw [← cweaken_interp_var]
      exact ρ.var x
  tvar := fun
    | .there X => by
      change
        env1.lookup_tvar X ≈
          Ty.val_denot (env2.extend_cvar cs cap) (((σ.tvar X).rename Rename.succ).core)
      apply Denot.equiv_trans _ _ _ (ρ.tvar X)
      apply cweaken_val_denot
  cvar := fun
    | .here => by
      change cs = (CaptureSet.cvar Mutability.epsilon (BVar.here (s := s2))).subst
        (Subst.from_TypeEnv (env2.extend_cvar cs cap))
      rfl
    | .there C => by
      change (env1.lookup_cvar C).1
        = ((σ.cvar C).rename Rename.succ).subst (Subst.from_TypeEnv (env2.extend_cvar cs cap))
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
    | epsilon =>
      simpa only [CaptureSet.subst, CaptureSet.applyMut_epsilon, Subst.from_TypeEnv] using
        ρ.cvar C
    | ro =>
      simpa only [CaptureSet.subst, CaptureSet.applyMut_ro, CaptureSet.applyRO_subst,
        Subst.from_TypeEnv] using
        congrArg CaptureSet.applyRO (ρ.cvar C)

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
  | .modal cs Ψ T => by
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
      · intro m' hsub hkind hsep
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
        exact (ih m' _).mp (hbody m' hsub hkind' hsep')
    · rintro ⟨hwf_e, hwf_cs, cs0, sepctx0, t0, hres, hwf_cs0, hwf_sepctx0,
        hsat, hR0_sub, hbody⟩
      refine ⟨hwf_e, hwf_cs, cs0, sepctx0, t0, hres, hwf_cs0, hwf_sepctx0, ?_, hR0_sub, ?_⟩
      · intro m' hsub hsat'
        exact hsat m' hsub ((retype_satisfy_iff ρ Ψ m').mp hsat')
      · intro m' hsub hkind hsep
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
        exact (ih m' _).mpr (hbody m' hsub hkind' hsep')

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
  simp only [Ty.exp_denot]
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
  simp only [Ty.exi_exp_denot]
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
      change env.lookup_tvar X ≈ Ty.val_denot env (PureTy.tvar X).core
      apply Denot.eq_to_equiv
      unfold PureTy.tvar Ty.val_denot
      rfl
  cvar := fun
    | .there C => by
      change
        (env.lookup_cvar C).1 =
          (CaptureSet.cvar Mutability.epsilon C).subst (Subst.from_TypeEnv env)
      rfl

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
          (CaptureSet.cvar Mutability.epsilon C).subst (Subst.from_TypeEnv env)
      rfl

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
      change (env.extend_cvar (C.subst (Subst.from_TypeEnv env)) cap).lookup_tvar X.there
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
          (CaptureSet.cvar Mutability.epsilon C0).subst (Subst.from_TypeEnv env)
      rfl

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

end ModalCapybara
