import Semantic.CCPrec.Denotation.Core
import Semantic.CCPrec.Denotation.Rebind
namespace CCPrec

/-- Interpret a variable in an environment to get its free variable index. -/
def interp_var (env : TypeEnv s) (x : Var .var s) : Nat :=
  match x with
  | .free n => n
  | .bound x => env.lookup_var x

structure Retype (env1 : TypeEnv s1) (σ : Subst s1 s2) (env2 : TypeEnv s2) where
  var :
    ∀ (x : BVar s1 .var),
      env1.lookup_var x = interp_var env2 (σ.var x)

  tvar :
    ∀ (X : BVar s1 .tvar),
      env1.lookup_tvar X ≈ Ty.shape_val_denot env2 (σ.tvar X)

  cvar :
    ∀ (C : BVar s1 .cvar),
      env1.lookup_cvar C = (σ.cvar C).subst (Subst.from_TypeEnv env2)

lemma weaken_interp_var {x : Var .var s} :
  interp_var env x = interp_var (env.extend_var n) (x.rename Rename.succ) := by
  cases x <;> rfl

lemma tweaken_interp_var {x : Var .var s} :
  interp_var env x = interp_var (env.extend_tvar d) (x.rename Rename.succ) := by
  cases x <;> rfl

lemma cweaken_interp_var {cs : CaptureSet {}} {x : Var .var s} :
  interp_var env x = interp_var (env.extend_cvar cs) (x.rename Rename.succ) := by
  cases x <;> rfl

theorem Retype.liftVar
  {x : Nat}
  (ρ : Retype env1 σ env2) :
  Retype (env1.extend_var x) (σ.lift) (env2.extend_var x) where
  var := fun
    | .here => rfl
    | .there y => by
      change env1.lookup_var y = interp_var (env2.extend_var x) ((σ.var y).rename Rename.succ)
      rw [← weaken_interp_var]
      exact ρ.var y
  tvar := fun
    | .there X => by
      change
        env1.lookup_tvar X ≈
          Ty.shape_val_denot (env2.extend_var x) ((σ.tvar X).rename Rename.succ)
      apply PreDenot.equiv_trans _ _ _ (ρ.tvar X)
      apply weaken_shape_val_denot
  cvar := fun
    | .there C => by
      change env1.lookup_cvar C = ((σ.cvar C).rename Rename.succ).subst
        (Subst.from_TypeEnv (env2.extend_var x))
      rw [ρ.cvar C]
      apply rebind_resolved_capture_set Rebind.weaken

theorem Retype.liftTVar
  {d : PreDenot}
  (ρ : Retype env1 σ env2) :
  Retype (env1.extend_tvar d) (σ.lift) (env2.extend_tvar d) where
  var := fun
    | .there x => by
      change env1.lookup_var x = interp_var (env2.extend_tvar d) ((σ.var x).rename Rename.succ)
      rw [← tweaken_interp_var]
      exact ρ.var x
  tvar := fun
    | .here => by
      change d ≈ Ty.shape_val_denot (env2.extend_tvar d) (.tvar .here)
      unfold Ty.shape_val_denot
      apply PreDenot.equiv_refl
    | .there X => by
      change
        env1.lookup_tvar X ≈
          Ty.shape_val_denot (env2.extend_tvar d) ((σ.tvar X).rename Rename.succ)
      apply PreDenot.equiv_trans _ _ _ (ρ.tvar X)
      apply tweaken_shape_val_denot
  cvar := fun
    | .there C => by
      change env1.lookup_cvar C = ((σ.cvar C).rename Rename.succ).subst
        (Subst.from_TypeEnv (env2.extend_tvar d))
      rw [ρ.cvar C]
      apply rebind_resolved_capture_set Rebind.tweaken

theorem Retype.liftCVar
  {cs : CaptureSet {}}
  (ρ : Retype env1 σ env2) :
  Retype (env1.extend_cvar cs) (σ.lift) (env2.extend_cvar cs) where
  var := fun
    | .there x => by
      change
        env1.lookup_var x = interp_var (env2.extend_cvar cs) ((σ.var x).rename Rename.succ)
      rw [← cweaken_interp_var]
      exact ρ.var x
  tvar := fun
    | .there X => by
      change
        env1.lookup_tvar X ≈
          Ty.shape_val_denot (env2.extend_cvar cs) ((σ.tvar X).rename Rename.succ)
      apply PreDenot.equiv_trans _ _ _ (ρ.tvar X)
      apply cweaken_shape_val_denot
  cvar := fun
    | .here => by
      change (env2.extend_cvar cs).lookup_cvar .here = cs
      rfl
    | .there C => by
      change env1.lookup_cvar C = ((σ.cvar C).rename Rename.succ).subst
        (Subst.from_TypeEnv (env2.extend_cvar cs))
      rw [ρ.cvar C]
      apply rebind_resolved_capture_set Rebind.cweaken

mutual

def retype_shape_val_denot
  {s1 s2 : Sig} {env1 : TypeEnv s1} {σ : Subst s1 s2} {env2 : TypeEnv s2}
  (ρ : Retype env1 σ env2) (T : Ty .shape s1) :
  Ty.shape_val_denot env1 T ≈ Ty.shape_val_denot env2 (T.subst σ) :=
  match T with
  | .top => by
    apply PreDenot.eq_to_equiv
    simp only [Ty.shape_val_denot, Ty.subst]
  | .tvar X => by
    simpa only [Ty.shape_val_denot, Ty.subst] using ρ.tvar X
  | .unit => by
    apply PreDenot.eq_to_equiv
    simp only [Ty.shape_val_denot, Ty.subst]
  | .cap => by
    apply PreDenot.eq_to_equiv
    simp only [Ty.shape_val_denot, Ty.subst]
  | .bool => by
    apply PreDenot.eq_to_equiv
    simp only [Ty.shape_val_denot, Ty.subst]
  | .cell => by
    apply PreDenot.eq_to_equiv
    simp only [Ty.shape_val_denot, Ty.subst]
  | .arrow T1 T2 => by
    have ih1 := retype_capt_val_denot ρ T1
    intro A s0 e0
    suffices hmain :
      (e0.WfInHeap s0.heap ∧
        ∃ cs T0 t0,
          resolve s0.heap e0 = some (Exp.abs cs T0 t0) ∧
            cs.WfInHeap s0.heap ∧
            expand_captures s0.heap cs ⊆ A ∧
              ∀ (arg : Nat) (H' : Memory),
                H'.subsumes s0 →
                  Ty.capt_val_denot env1 T1 H' (Exp.var (.free arg)) →
                    Ty.exi_exp_denot (env1.extend_var arg) T2
                      (expand_captures s0.heap cs)
                      H'
                      (t0.subst (Subst.openVar (.free arg)))) ↔
      (e0.WfInHeap s0.heap ∧
        ∃ cs T0 t0,
          resolve s0.heap e0 = some (Exp.abs cs T0 t0) ∧
            cs.WfInHeap s0.heap ∧
            expand_captures s0.heap cs ⊆ A ∧
              ∀ (arg : Nat) (H' : Memory),
                H'.subsumes s0 →
                  Ty.capt_val_denot env2 (T1.subst σ) H' (Exp.var (.free arg)) →
                    Ty.exi_exp_denot (env2.extend_var arg) (T2.subst σ.lift)
                      (expand_captures s0.heap cs)
                      H'
                      (t0.subst (Subst.openVar (.free arg)))) by
      simpa only [Ty.shape_val_denot, Ty.subst] using hmain
    constructor
    · intro h
      obtain ⟨hwf_e, cs, T0, t0, hr, hwf, hR0_sub, hd⟩ := h
      refine ⟨hwf_e, cs, T0, t0, hr, hwf, hR0_sub, ?_⟩
      intro arg H' hsub harg
      cases T1
      case capt C S =>
        have ih2 := retype_exi_exp_denot (ρ.liftVar (x:=arg)) T2
        have harg' := (ih1 H' (.var (.free arg))).mpr harg
        specialize hd arg H' hsub harg'
        exact (ih2 (expand_captures s0.heap cs) H' _).mp hd
    · intro h
      obtain ⟨hwf_e, cs0, T0, t0, hr, hwf, hR0_sub, hd⟩ := h
      refine ⟨hwf_e, cs0, T0, t0, hr, hwf, hR0_sub, ?_⟩
      intro arg H' hsub harg
      cases T1
      case capt C S =>
        have ih2 := retype_exi_exp_denot (ρ.liftVar (x:=arg)) T2
        have harg' := (ih1 H' (.var (.free arg))).mp harg
        specialize hd arg H' hsub harg'
        exact (ih2 (expand_captures s0.heap cs0) H' _).mpr hd
  | .poly T1 T2 => by
    have ih1 := retype_shape_val_denot ρ T1
    intro A s0 e0
    suffices hmain :
      (e0.WfInHeap s0.heap ∧
        ∃ cs S0 t0,
          resolve s0.heap e0 = some (Exp.tabs cs S0 t0) ∧
            cs.WfInHeap s0.heap ∧
            expand_captures s0.heap cs ⊆ A ∧
              ∀ (H' : Memory) (denot : PreDenot),
                H'.subsumes s0 →
                  denot.is_proper →
                    denot.ImplyAfter H' (Ty.shape_val_denot env1 T1) →
                      Ty.exi_exp_denot (env1.extend_tvar denot) T2
                        (expand_captures s0.heap cs)
                        H'
                        (t0.subst (Subst.openTVar Ty.top))) ↔
      (e0.WfInHeap s0.heap ∧
        ∃ cs S0 t0,
          resolve s0.heap e0 = some (Exp.tabs cs S0 t0) ∧
            cs.WfInHeap s0.heap ∧
            expand_captures s0.heap cs ⊆ A ∧
              ∀ (H' : Memory) (denot : PreDenot),
                H'.subsumes s0 →
                  denot.is_proper →
                    denot.ImplyAfter H' (Ty.shape_val_denot env2 (T1.subst σ)) →
                      Ty.exi_exp_denot (env2.extend_tvar denot) (T2.subst σ.lift)
                        (expand_captures s0.heap cs)
                        H'
                        (t0.subst (Subst.openTVar Ty.top))) by
      simpa only [Ty.shape_val_denot, Ty.subst] using hmain
    constructor
    · intro h
      obtain ⟨hwf_e, cs, S0, t0, hr, hwf, hR0_sub, hd⟩ := h
      refine ⟨hwf_e, cs, S0, t0, hr, hwf, hR0_sub, ?_⟩
      intro H' denot hsub hproper himply
      have ih2 := retype_exi_exp_denot (ρ.liftTVar (d:=denot)) T2
      have himply' : denot.ImplyAfter H' (Ty.shape_val_denot env1 T1) := by
        intro H'' hsub' A' e hdenot
        exact (ih1 _ _ _).mpr (himply H'' hsub' A' e hdenot)
      specialize hd H' denot hsub hproper himply'
      exact (ih2 (expand_captures s0.heap cs) H' _).mp hd
    · intro h
      obtain ⟨hwf_e, cs0, S0, t0, hr, hwf, hR0_sub, hd⟩ := h
      refine ⟨hwf_e, cs0, S0, t0, hr, hwf, hR0_sub, ?_⟩
      intro H' denot hsub hproper himply
      have ih2 := retype_exi_exp_denot (ρ.liftTVar (d:=denot)) T2
      have himply' : denot.ImplyAfter H' (Ty.shape_val_denot env2 (T1.subst σ)) := by
        intro H'' hsub' A' e hdenot
        exact (ih1 _ _ _).mp (himply H'' hsub' A' e hdenot)
      specialize hd H' denot hsub hproper himply'
      exact (ih2 (expand_captures s0.heap cs0) H' _).mpr hd
  | .cpoly B T => by
    have hB := retype_capturebound_denot ρ B
    intro A s0 e0
    suffices hmain :
      (e0.WfInHeap s0.heap ∧
        ∃ cs B0 t0,
          resolve s0.heap e0 = some (Exp.cabs cs B0 t0) ∧
            cs.WfInHeap s0.heap ∧
            expand_captures s0.heap cs ⊆ A ∧
              ∀ (H' : Memory) (CS : CaptureSet {}),
                CS.WfInHeap H'.heap →
                  H'.subsumes s0 →
                    (CaptureSet.denot TypeEnv.empty CS H').BoundedBy
                      (CaptureBound.denot env2 (B.subst σ) H') →
                      Ty.exi_exp_denot (env1.extend_cvar CS) T
                        (expand_captures s0.heap cs)
                        H'
                        (t0.subst (Subst.openCVar CS))) ↔
      (e0.WfInHeap s0.heap ∧
        ∃ cs B0 t0,
          resolve s0.heap e0 = some (Exp.cabs cs B0 t0) ∧
            cs.WfInHeap s0.heap ∧
            expand_captures s0.heap cs ⊆ A ∧
              ∀ (H' : Memory) (CS : CaptureSet {}),
                CS.WfInHeap H'.heap →
                  H'.subsumes s0 →
                    (CaptureSet.denot TypeEnv.empty CS H').BoundedBy
                      (CaptureBound.denot env2 (B.subst σ) H') →
                      Ty.exi_exp_denot (env2.extend_cvar CS) (T.subst σ.lift)
                        (expand_captures s0.heap cs)
                        H'
                        (t0.subst (Subst.openCVar CS))) by
      simpa only [Ty.shape_val_denot, Ty.subst, hB] using hmain
    constructor
    · intro h
      obtain ⟨hwf_e, cs, B0, t0, hr, hwf, hR0_sub, hd⟩ := h
      refine ⟨hwf_e, cs, B0, t0, hr, hwf, hR0_sub, ?_⟩
      intro H' CS hwf hsub hsub_bound
      have ih2 := retype_exi_exp_denot (ρ.liftCVar (cs:=CS)) T
      specialize hd H' CS hwf hsub hsub_bound
      exact (ih2 (expand_captures s0.heap cs) H' _).mp hd
    · intro h
      obtain ⟨hwf_e, cs0, B0, t0, hr, hwf, hR0_sub, hd⟩ := h
      refine ⟨hwf_e, cs0, B0, t0, hr, hwf, hR0_sub, ?_⟩
      intro H' CS hwf hsub hsub_bound
      have ih2 := retype_exi_exp_denot (ρ.liftCVar (cs:=CS)) T
      specialize hd H' CS hwf hsub hsub_bound
      exact (ih2 (expand_captures s0.heap cs0) H' _).mpr hd

def retype_capturebound_denot
  {s1 s2 : Sig} {env1 : TypeEnv s1} {σ : Subst s1 s2} {env2 : TypeEnv s2}
  (ρ : Retype env1 σ env2) (B : CaptureBound s1) :
  CaptureBound.denot env1 B = CaptureBound.denot env2 (B.subst σ) := by
  cases B
  case unbound => rfl
  case bound C =>
    simp only [CaptureBound.denot, CaptureBound.subst]
    funext m
    congr 1
    exact congrFun (retype_captureset_denot ρ C) m

def retype_resolved_capture_set
  {s1 s2 : Sig} {env1 : TypeEnv s1} {σ : Subst s1 s2} {env2 : TypeEnv s2}
  (ρ : Retype env1 σ env2) (C : CaptureSet s1) :
  C.subst (Subst.from_TypeEnv env1) = (C.subst σ).subst (Subst.from_TypeEnv env2) := by
  induction C
  case empty => rfl
  case union C1 C2 ih1 ih2 =>
    simp [CaptureSet.subst, ih1, ih2]
  case var x =>
    cases x
    case bound x =>
      change
        CaptureSet.var (.free (env1.lookup_var x)) =
          (CaptureSet.var (σ.var x)).subst (Subst.from_TypeEnv env2)
      cases hσ : σ.var x
      case bound y =>
        change CaptureSet.var (.free (env1.lookup_var x)) =
          CaptureSet.var (.free (env2.lookup_var y))
        have hvar : env1.lookup_var x = env2.lookup_var y := by
          have hvar := ρ.var x
          rw [hσ] at hvar
          simpa [interp_var] using hvar
        simp [hvar]
      case free n =>
        change CaptureSet.var (.free (env1.lookup_var x)) = CaptureSet.var (.free n)
        have hvar : env1.lookup_var x = n := by
          have hvar := ρ.var x
          rw [hσ] at hvar
          simpa [interp_var] using hvar
        simp [hvar]
    case free n =>
      simp [CaptureSet.subst, Var.subst]
  case cvar C =>
    simpa only [CaptureSet.subst] using ρ.cvar C

def retype_captureset_denot
  {s1 s2 : Sig} {env1 : TypeEnv s1} {σ : Subst s1 s2} {env2 : TypeEnv s2}
  (ρ : Retype env1 σ env2) (C : CaptureSet s1) :
  CaptureSet.denot env1 C = CaptureSet.denot env2 (C.subst σ) := by
  unfold CaptureSet.denot
  congr 1
  exact retype_resolved_capture_set ρ C

def retype_capt_val_denot
  {s1 s2 : Sig} {env1 : TypeEnv s1} {σ : Subst s1 s2} {env2 : TypeEnv s2}
  (ρ : Retype env1 σ env2) (T : Ty .capt s1) :
  Ty.capt_val_denot env1 T ≈ Ty.capt_val_denot env2 (T.subst σ) :=
  match T with
  | .capt C S => by
    have hC := retype_captureset_denot ρ C
    have hS := retype_shape_val_denot ρ S
    intro s e
    suffices hmain :
      e.IsSimpleAns ∧
        e.WfInHeap s.heap ∧
        (C.subst (Subst.from_TypeEnv env1)).WfInHeap s.heap ∧
        Ty.shape_val_denot env1 S (CaptureSet.denot env1 C s) s e ↔
      e.IsSimpleAns ∧
        e.WfInHeap s.heap ∧
        ((C.subst σ).subst (Subst.from_TypeEnv env2)).WfInHeap s.heap ∧
        Ty.shape_val_denot env2 (S.subst σ) (CaptureSet.denot env1 C s) s e by
      simpa only [Ty.capt_val_denot, Ty.subst, hC] using hmain
    constructor
    · intro h
      obtain ⟨hsimple, hwf_e, hwf_C, hshape⟩ := h
      refine ⟨hsimple, hwf_e, ?_, ?_⟩
      · rw [← retype_resolved_capture_set ρ C]
        exact hwf_C
      · exact (hS (C.denot env1 s) s e).mp hshape
    · intro h
      obtain ⟨hsimple, hwf_e, hwf_C, hshape⟩ := h
      refine ⟨hsimple, hwf_e, ?_, ?_⟩
      · rw [retype_resolved_capture_set ρ C]
        exact hwf_C
      · exact (hS (C.denot env1 s) s e).mpr hshape

def retype_exi_val_denot
  {s1 s2 : Sig} {env1 : TypeEnv s1} {σ : Subst s1 s2} {env2 : TypeEnv s2}
  (ρ : Retype env1 σ env2) (T : Ty .exi s1) :
  Ty.exi_val_denot env1 T ≈ Ty.exi_val_denot env2 (T.subst σ) :=
  match T with
  | .typ T => by
    have ih := retype_capt_val_denot ρ T
    intro s e
    simpa only [Ty.exi_val_denot, Ty.subst] using ih s e
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
        have ih := retype_capt_val_denot (ρ.liftCVar (cs:=CS)) T
        exact ih s (Exp.var y)
      all_goals {
        -- resolve returned non-pack
        simp
      }

def retype_capt_exp_denot
  {s1 s2 : Sig} {env1 : TypeEnv s1} {σ : Subst s1 s2} {env2 : TypeEnv s2}
  (ρ : Retype env1 σ env2) (T : Ty .capt s1) :
  Ty.capt_exp_denot env1 T ≈ Ty.capt_exp_denot env2 (T.subst σ) := by
  have ih := retype_capt_val_denot ρ T
  intro A s e
  simp only [Ty.capt_exp_denot]
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
  {s1 s2 : Sig} {env1 : TypeEnv s1} {σ : Subst s1 s2} {env2 : TypeEnv s2}
  (ρ : Retype env1 σ env2) (T : Ty .exi s1) :
  Ty.exi_exp_denot env1 T ≈ Ty.exi_exp_denot env2 (T.subst σ) := by
  have ih := retype_exi_val_denot ρ T
  intro A s e
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

def Retype.open_arg {env : TypeEnv s} {y : Var .var s} :
  Retype
    (env.extend_var (interp_var env y))
    (Subst.openVar y)
    env where
  var := fun x => by cases x <;> rfl
  tvar := fun
    | .there X => by
      change env.lookup_tvar X ≈ Ty.shape_val_denot env (.tvar X)
      unfold Ty.shape_val_denot
      apply PreDenot.equiv_refl
  cvar := fun
    | .there C => by
      change env.lookup_cvar C = (CaptureSet.cvar C).subst (Subst.from_TypeEnv env)
      rfl

theorem open_arg_shape_val_denot {env : TypeEnv s} {y : Var .var s} {T : Ty .shape (s,x)} :
  Ty.shape_val_denot (env.extend_var (interp_var env y)) T ≈
    Ty.shape_val_denot env (T.subst (Subst.openVar y)) := by
  apply retype_shape_val_denot Retype.open_arg

theorem open_arg_capt_val_denot {env : TypeEnv s} {y : Var .var s} {T : Ty .capt (s,x)} :
  Ty.capt_val_denot (env.extend_var (interp_var env y)) T ≈
    Ty.capt_val_denot env (T.subst (Subst.openVar y)) := by
  apply retype_capt_val_denot Retype.open_arg

theorem open_arg_exi_val_denot {env : TypeEnv s} {y : Var .var s} {T : Ty .exi (s,x)} :
  Ty.exi_val_denot (env.extend_var (interp_var env y)) T ≈
    Ty.exi_val_denot env (T.subst (Subst.openVar y)) := by
  apply retype_exi_val_denot Retype.open_arg

theorem open_arg_exi_exp_denot {env : TypeEnv s} {y : Var .var s} {T : Ty .exi (s,x)} :
  Ty.exi_exp_denot (env.extend_var (interp_var env y)) T ≈
    Ty.exi_exp_denot env (T.subst (Subst.openVar y)) := by
  apply retype_exi_exp_denot Retype.open_arg

def Retype.open_targ {env : TypeEnv s} {S : Ty .shape s} :
  Retype
    (env.extend_tvar (Ty.shape_val_denot env S))
    (Subst.openTVar S)
    env where
  var := fun x => by cases x; rfl
  tvar := fun
    | .here => by
      apply PreDenot.eq_to_equiv
      rfl
    | .there X => by
      apply PreDenot.eq_to_equiv
      simp [TypeEnv.extend_tvar, TypeEnv.lookup_tvar]
      simp [Subst.openTVar, Ty.shape_val_denot]
      rfl
  cvar := fun
    | .there C => by
      simp only [List.empty_eq]
      unfold TypeEnv.lookup_cvar
      rfl

theorem open_targ_shape_val_denot {env : TypeEnv s} {S : Ty .shape s} {T : Ty .shape (s,X)} :
  Ty.shape_val_denot (env.extend_tvar (Ty.shape_val_denot env S)) T ≈
    Ty.shape_val_denot env (T.subst (Subst.openTVar S)) := by
  apply retype_shape_val_denot Retype.open_targ

theorem open_targ_capt_val_denot {env : TypeEnv s} {S : Ty .shape s} {T : Ty .capt (s,X)} :
  Ty.capt_val_denot (env.extend_tvar (Ty.shape_val_denot env S)) T ≈
    Ty.capt_val_denot env (T.subst (Subst.openTVar S)) := by
  apply retype_capt_val_denot Retype.open_targ

theorem open_targ_exi_val_denot {env : TypeEnv s} {S : Ty .shape s} {T : Ty .exi (s,X)} :
  Ty.exi_val_denot (env.extend_tvar (Ty.shape_val_denot env S)) T ≈
    Ty.exi_val_denot env (T.subst (Subst.openTVar S)) := by
  apply retype_exi_val_denot Retype.open_targ

theorem open_targ_exi_exp_denot {env : TypeEnv s} {S : Ty .shape s} {T : Ty .exi (s,X)} :
  Ty.exi_exp_denot (env.extend_tvar (Ty.shape_val_denot env S)) T ≈
    Ty.exi_exp_denot env (T.subst (Subst.openTVar S)) := by
  apply retype_exi_exp_denot Retype.open_targ

def Retype.open_carg {env : TypeEnv s} {C : CaptureSet s} :
  Retype
    (env.extend_cvar (C.subst (Subst.from_TypeEnv env)))
    (Subst.openCVar C)
    env where
  var := fun x => by cases x; rfl
  tvar := fun
    | .there X => by
      change (env.extend_cvar (C.subst (Subst.from_TypeEnv env))).lookup_tvar X.there
        ≈ Ty.shape_val_denot env (.tvar X)
      unfold Ty.shape_val_denot
      apply PreDenot.equiv_refl
  cvar := fun
    | .here => by
      change (env.extend_cvar (C.subst (Subst.from_TypeEnv env))).lookup_cvar .here
        = C.subst (Subst.from_TypeEnv env)
      rfl
    | .there C0 => by
      change (env.extend_cvar (C.subst (Subst.from_TypeEnv env))).lookup_cvar C0.there
        = (CaptureSet.cvar C0).subst (Subst.from_TypeEnv env)
      rfl

theorem open_carg_shape_val_denot {env : TypeEnv s} {C : CaptureSet s} {T : Ty .shape (s,C)} :
  Ty.shape_val_denot (env.extend_cvar (C.subst (Subst.from_TypeEnv env))) T ≈
    Ty.shape_val_denot env (T.subst (Subst.openCVar C)) := by
  apply retype_shape_val_denot Retype.open_carg

theorem open_carg_exi_val_denot {env : TypeEnv s} {C : CaptureSet s} {T : Ty .exi (s,C)} :
  Ty.exi_val_denot (env.extend_cvar (C.subst (Subst.from_TypeEnv env))) T ≈
    Ty.exi_val_denot env (T.subst (Subst.openCVar C)) := by
  apply retype_exi_val_denot Retype.open_carg

theorem open_carg_exi_exp_denot {env : TypeEnv s} {C : CaptureSet s} {T : Ty .exi (s,C)} :
  Ty.exi_exp_denot (env.extend_cvar (C.subst (Subst.from_TypeEnv env))) T ≈
    Ty.exi_exp_denot env (T.subst (Subst.openCVar C)) := by
  apply retype_exi_exp_denot Retype.open_carg

end CCPrec
