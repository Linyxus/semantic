import Semantic.Capybara.Denotation.Core
import Semantic.Capybara.Denotation.Rebind
namespace Capybara

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
      conv =>
        lhs
        simp [TypeEnv.extend_var, TypeEnv.lookup_var]
      conv =>
        rhs
        simp [Subst.lift]
        simp [<-weaken_interp_var]
      exact ρ.var y
  tvar := fun
    | .there X => by
      conv =>
        lhs
        simp [TypeEnv.extend_var, TypeEnv.lookup_tvar]
      conv =>
        rhs
        simp [Subst.lift]
      apply PreDenot.equiv_trans _ _ _ (ρ.tvar X)
      apply weaken_shape_val_denot
  cvar := fun
    | .there C => by
      simp [TypeEnv.extend_var, Subst.lift]
      change env1.lookup_cvar C = _
      rw [ρ.cvar C]
      apply rebind_resolved_capture_set Rebind.weaken

theorem Retype.liftTVar
  {d : PreDenot}
  (ρ : Retype env1 σ env2) :
  Retype (env1.extend_tvar d) (σ.lift) (env2.extend_tvar d) where
  var := fun
    | .there x => by
      conv => lhs; simp [TypeEnv.extend_tvar, TypeEnv.lookup_var]
      conv => rhs; simp [Subst.lift, <-tweaken_interp_var]
      exact ρ.var x
  tvar := fun
    | .here => by
      conv => lhs; simp [TypeEnv.extend_tvar, TypeEnv.lookup_tvar]
      conv =>
        rhs
        simp [Subst.lift, Ty.shape_val_denot]
        simp [TypeEnv.extend_tvar, TypeEnv.lookup_tvar]
      apply PreDenot.equiv_refl
    | .there X => by
      conv =>
        lhs
        simp [TypeEnv.extend_tvar, TypeEnv.lookup_tvar]
      conv =>
        rhs
        simp [Subst.lift]
      apply PreDenot.equiv_trans _ _ _ (ρ.tvar X)
      apply tweaken_shape_val_denot
  cvar := fun
    | .there C => by
      simp [TypeEnv.extend_tvar, Subst.lift]
      change env1.lookup_cvar C = _
      rw [ρ.cvar C]
      apply rebind_resolved_capture_set Rebind.tweaken

theorem Retype.liftCVar
  {cs : CaptureSet {}}
  (ρ : Retype env1 σ env2) :
  Retype (env1.extend_cvar cs) (σ.lift) (env2.extend_cvar cs) where
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
      apply PreDenot.equiv_trans _ _ _ (ρ.tvar X)
      apply cweaken_shape_val_denot
  cvar := fun
    | .here => by
      simp [TypeEnv.extend_cvar, TypeEnv.lookup_cvar, Subst.lift,
        CaptureSet.subst, Subst.from_TypeEnv]
    | .there C => by
      simp [TypeEnv.extend_cvar, Subst.lift]
      change env1.lookup_cvar C = _
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
    simp [Ty.shape_val_denot, Ty.subst]
  | .tvar X => by
    simp [Ty.shape_val_denot, Ty.subst]
    exact ρ.tvar X
  | .unit => by
    apply PreDenot.eq_to_equiv
    simp [Ty.shape_val_denot, Ty.subst]
  | .cap => by
    apply PreDenot.eq_to_equiv
    simp [Ty.shape_val_denot, Ty.subst]
  | .bool => by
    apply PreDenot.eq_to_equiv
    simp [Ty.shape_val_denot, Ty.subst]
  | .cell => by
    apply PreDenot.eq_to_equiv
    simp [Ty.shape_val_denot, Ty.subst]
  | .reader => by
    apply PreDenot.eq_to_equiv
    simp [Ty.shape_val_denot, Ty.subst]
  | .arrow T1 T2 => by
    have ih1 := retype_capt_val_denot ρ T1
    intro A s0 e0
    simp [Ty.shape_val_denot, Ty.subst]
    intro hwf_e
    constructor
    · intro h
      obtain ⟨cs, T0, t0, hr, hwf, hR0_sub, hd⟩ := h
      use cs, T0, t0
      constructor
      · exact hr
      · constructor
        · exact hwf
        · constructor
          · exact hR0_sub
          · intro arg H' hsub harg
            cases T1
            case capt C S =>
              have ih2 := retype_exi_exp_denot (ρ.liftVar (x:=arg)) T2
              have harg' := (ih1 H' (.var (.free arg))).mpr harg
              specialize hd arg H' hsub harg'
              -- The capability set uses expand_captures
              exact (ih2 (expand_captures s0.heap cs ∪
                         (reachability_of_loc H'.heap arg)) H' _).mp hd
    · intro h
      obtain ⟨cs0, T0, t0, hr, hwf, hR0_sub, hd⟩ := h
      use cs0, T0, t0
      constructor
      · exact hr
      · constructor
        · exact hwf
        · constructor
          · exact hR0_sub
          · intro arg H' hsub harg
            cases T1
            case capt C S =>
              have ih2 := retype_exi_exp_denot (ρ.liftVar (x:=arg)) T2
              have harg' := (ih1 H' (.var (.free arg))).mp harg
              specialize hd arg H' hsub harg'
              -- The capability set uses expand_captures
              exact (ih2 (expand_captures s0.heap cs0 ∪
                         (reachability_of_loc H'.heap arg)) H' _).mpr hd
  | .poly T1 T2 => by
    have ih1 := retype_shape_val_denot ρ T1
    intro A s0 e0
    simp [Ty.shape_val_denot, Ty.subst]
    intro hwf_e
    constructor
    · intro h
      obtain ⟨cs, S0, t0, hr, hwf, hR0_sub, hd⟩ := h
      use cs, S0, t0
      constructor
      · exact hr
      · constructor
        · exact hwf
        · constructor
          · exact hR0_sub
          · intro H' denot hsub hproper himply
            have ih2 := retype_exi_exp_denot (ρ.liftTVar (d:=denot)) T2
            have himply' : denot.ImplyAfter H' (Ty.shape_val_denot env1 T1) := by
              intro H'' hsub' A' e hdenot
              exact (ih1 _ _ _).mpr (himply H'' hsub' A' e hdenot)
            specialize hd H' denot hsub hproper himply'
            exact (ih2 (expand_captures s0.heap cs) H' _).mp hd
    · intro h
      obtain ⟨cs0, S0, t0, hr, hwf, hR0_sub, hd⟩ := h
      use cs0, S0, t0
      constructor
      · exact hr
      · constructor
        · exact hwf
        · constructor
          · exact hR0_sub
          · intro H' denot hsub hproper himply
            have ih2 := retype_exi_exp_denot (ρ.liftTVar (d:=denot)) T2
            have himply' : denot.ImplyAfter H' (Ty.shape_val_denot env2 (T1.subst σ)) := by
              intro H'' hsub' A' e hdenot
              exact (ih1 _ _ _).mp (himply H'' hsub' A' e hdenot)
            specialize hd H' denot hsub hproper himply'
            exact (ih2 (expand_captures s0.heap cs0) H' _).mpr hd
  | .cpoly B T => by
    -- B : Mutability, and Mutability.denot doesn't depend on environment
    intro A s0 e0
    simp [Ty.shape_val_denot, Ty.subst]
    intro hwf_e
    constructor
    · intro h
      obtain ⟨cs, B0, t0, hr, hwf, hR0_sub, hd⟩ := h
      use cs, B0, t0
      constructor
      · exact hr
      · constructor
        · exact hwf
        · constructor
          · exact hR0_sub
          · intro H' CS hwf hsub hsub_bound
            have ih2 := retype_exi_exp_denot (ρ.liftCVar (cs:=CS)) T
            specialize hd H' CS hwf hsub hsub_bound
            exact (ih2 (expand_captures s0.heap cs) H' _).mp hd
    · intro h
      obtain ⟨cs0, B0, t0, hr, hwf, hR0_sub, hd⟩ := h
      use cs0, B0, t0
      constructor
      · exact hr
      · constructor
        · exact hwf
        · constructor
          · exact hR0_sub
          · intro H' CS hwf hsub hsub_bound
            have ih2 := retype_exi_exp_denot (ρ.liftCVar (cs:=CS)) T
            specialize hd H' CS hwf hsub hsub_bound
            exact (ih2 (expand_captures s0.heap cs0) H' _).mpr hd

-- Mutability.denot doesn't depend on environment, so retyping is trivial
def retype_mutability_denot (B : Mutability) :
  B.denot = B.denot := rfl

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
    simp [Ty.capt_val_denot, Ty.subst]
    rw [← hC]
    intro hwf_e hwf
    constructor
    · intro ⟨hwf_C, hshape⟩
      constructor
      · -- Use retype_resolved_capture_set to show equality of resolved capture sets
        rw [←retype_resolved_capture_set ρ C]
        exact hwf_C
      · exact (hS (C.denot env1 s) s e).mp hshape
    · intro ⟨hwf_C, hshape⟩
      constructor
      · -- Use retype_resolved_capture_set to show equality of resolved capture sets
        rw [retype_resolved_capture_set ρ C]
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
  simp [Ty.capt_exp_denot]
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

def Retype.open_arg {env : TypeEnv s} {y : Var .var s} :
  Retype
    (env.extend_var (interp_var env y))
    (Subst.openVar y)
    env where
  var := fun x => by cases x <;> rfl
  tvar := fun
    | .there X => by
      conv =>
        lhs
        simp [TypeEnv.extend_var, TypeEnv.lookup_tvar]
      conv =>
        rhs
        simp [Subst.openVar]
      apply PreDenot.eq_to_equiv
      simp [Ty.shape_val_denot]
  cvar := fun
    | .there C => by
      simp [TypeEnv.extend_var, Subst.openVar, TypeEnv.lookup_cvar,
        CaptureSet.subst, Subst.from_TypeEnv]

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
  cvar := fun
    | .there C => by
      simp [TypeEnv.extend_tvar, Subst.openTVar, TypeEnv.lookup_cvar,
        CaptureSet.subst, Subst.from_TypeEnv]

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
      apply PreDenot.eq_to_equiv
      simp [TypeEnv.lookup_tvar, Subst.openCVar, TypeEnv.extend_cvar,
        Ty.shape_val_denot]
  cvar := fun
    | .here => by
      simp [TypeEnv.lookup_cvar, Subst.openCVar, TypeEnv.extend_cvar]
    | .there C => by
      simp [Subst.openCVar, TypeEnv.lookup_cvar, TypeEnv.extend_cvar,
        CaptureSet.subst, Subst.from_TypeEnv]

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

end Capybara
