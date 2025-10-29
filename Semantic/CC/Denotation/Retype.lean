import Semantic.CC.Denotation.Core
import Semantic.CC.Denotation.Rebind
namespace CC

/-- Interpret a variable in an environment to get its free variable index and capability set. -/
def interp_var (env : TypeEnv s) (x : Var .var s) : Nat × CapabilitySet :=
  match x with
  | .free n => ⟨n, {n}⟩
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
      env1.lookup_cvar C = CaptureSet.denot env2 (σ.cvar C)

lemma weaken_interp_var {x : Var .var s} :
  interp_var env x = interp_var (env.extend_var n R) (x.rename Rename.succ) := by
  cases x <;> rfl

lemma tweaken_interp_var {x : Var .var s} :
  interp_var env x = interp_var (env.extend_tvar d) (x.rename Rename.succ) := by
  cases x <;> rfl

lemma cweaken_interp_var {x : Var .var s} :
  interp_var env x = interp_var (env.extend_cvar c) (x.rename Rename.succ) := by
  cases x <;> rfl

theorem Retype.liftVar
  {x : Nat} {R : CapabilitySet}
  (ρ : Retype env1 σ env2) :
  Retype (env1.extend_var x R) (σ.lift) (env2.extend_var x R) where
  var := fun
    | .here => rfl
    | .there y => by
      conv =>
        lhs
        simp [TypeEnv.extend_var, TypeEnv.lookup_var, TypeEnv.lookup]
      conv =>
        rhs
        simp [Subst.lift]
        simp [<-weaken_interp_var]
      exact ρ.var y
  tvar := fun
    | .there X => by
      conv =>
        lhs
        simp [TypeEnv.extend_var, TypeEnv.lookup_tvar, TypeEnv.lookup]
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
      apply rebind_captureset_denot Rebind.weaken

theorem Retype.liftTVar
  {d : PreDenot}
  (ρ : Retype env1 σ env2) :
  Retype (env1.extend_tvar d) (σ.lift) (env2.extend_tvar d) where
  var := fun
    | .there x => by
      conv => lhs; simp [TypeEnv.extend_tvar, TypeEnv.lookup_var, TypeEnv.lookup]
      conv => rhs; simp [Subst.lift, <-tweaken_interp_var]
      exact ρ.var x
  tvar := fun
    | .here => by
      conv => lhs; simp [TypeEnv.extend_tvar, TypeEnv.lookup_tvar, TypeEnv.lookup]
      conv =>
        rhs
        simp [Subst.lift, Ty.shape_val_denot]
        simp [TypeEnv.extend_tvar, TypeEnv.lookup_tvar, TypeEnv.lookup]
      apply PreDenot.equiv_refl
    | .there X => by
      conv =>
        lhs
        simp [TypeEnv.extend_tvar, TypeEnv.lookup_tvar, TypeEnv.lookup]
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
      apply rebind_captureset_denot Rebind.tweaken

theorem Retype.liftCVar
  {c : CapabilitySet}
  (ρ : Retype env1 σ env2) :
  Retype (env1.extend_cvar c) (σ.lift) (env2.extend_cvar c) where
  var := fun
    | .there x => by
      conv => lhs; simp [TypeEnv.extend_cvar, TypeEnv.lookup_var, TypeEnv.lookup]
      conv => rhs; simp [Subst.lift, <-cweaken_interp_var]
      exact ρ.var x
  tvar := fun
    | .there X => by
      conv =>
        lhs
        simp [TypeEnv.extend_cvar, TypeEnv.lookup_tvar, TypeEnv.lookup]
      conv =>
        rhs
        simp [Subst.lift]
      apply PreDenot.equiv_trans _ _ _ (ρ.tvar X)
      apply cweaken_shape_val_denot
  cvar := fun
    | .here => by
      conv => lhs; simp [TypeEnv.extend_cvar, TypeEnv.lookup_cvar, TypeEnv.lookup]
      conv =>
        rhs
        simp [Subst.lift, CaptureSet.denot]
        simp [TypeEnv.extend_cvar, TypeEnv.lookup_cvar, TypeEnv.lookup]
    | .there C => by
      simp [TypeEnv.extend_cvar, Subst.lift]
      change env1.lookup_cvar C = _
      rw [ρ.cvar C]
      apply rebind_captureset_denot Rebind.cweaken

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
  | .arrow T1 T2 => by
    have ih1 := retype_capt_val_denot ρ T1
    intro A s0 e0
    simp [Ty.shape_val_denot, Ty.subst]
    constructor
    · intro h
      obtain ⟨cs, T0, t0, hr, hd⟩ := h
      use cs, T0, t0
      apply And.intro hr
      intro arg H' hsub harg
      cases T1
      case capt C S =>
        simp [Ty.subst, Ty.captureSet] at hd ⊢
        have hC := retype_captureset_denot ρ C
        have ih2 := retype_exi_exp_denot (ρ.liftVar (x:=arg) (R:=reachability_of_loc H' arg)) T2
        have harg' := (ih1 H' (.var (.free arg))).mpr harg
        specialize hd arg H' hsub harg'
        rw [hC] at hd
        exact (ih2 (A ∪ (C.subst σ).denot env2) H' _).mp hd
    · intro h
      obtain ⟨cs0, T0, t0, hr, hd⟩ := h
      use cs0, T0, t0
      apply And.intro hr
      intro arg H' hsub harg
      cases T1
      case capt C S =>
        simp [Ty.subst, Ty.captureSet] at hd ⊢
        have hC := retype_captureset_denot ρ C
        have ih2 := retype_exi_exp_denot (ρ.liftVar (x:=arg) (R:=reachability_of_loc H' arg)) T2
        have harg' := (ih1 H' (.var (.free arg))).mp harg
        specialize hd arg H' hsub harg'
        have := (ih2 (A ∪ (C.subst σ).denot env2) H' _).mpr hd
        rw [← hC] at this
        exact this
  | .poly T1 T2 => by
    have ih1 := retype_shape_val_denot ρ T1
    intro A s0 e0
    simp [Ty.shape_val_denot, Ty.subst]
    constructor
    · intro h
      obtain ⟨cs, S0, t0, hr, hd⟩ := h
      use cs, S0, t0
      apply And.intro hr
      intro H' denot hsub hproper himply
      have ih2 := retype_exi_exp_denot (ρ.liftTVar (d:=denot)) T2
      have himply' : denot.ImplyAfter H' (Ty.shape_val_denot env1 T1) := by
        intro H'' hsub' A' e hdenot
        exact (ih1 _ _ _).mpr (himply H'' hsub' A' e hdenot)
      specialize hd H' denot hsub hproper himply'
      exact (ih2 A H' _).mp hd
    · intro h
      obtain ⟨cs0, S0, t0, hr, hd⟩ := h
      use cs0, S0, t0
      apply And.intro hr
      intro H' denot hsub hproper himply
      have ih2 := retype_exi_exp_denot (ρ.liftTVar (d:=denot)) T2
      have himply' : denot.ImplyAfter H' (Ty.shape_val_denot env2 (T1.subst σ)) := by
        intro H'' hsub' A' e hdenot
        exact (ih1 _ _ _).mp (himply H'' hsub' A' e hdenot)
      specialize hd H' denot hsub hproper himply'
      exact (ih2 A H' _).mpr hd
  | .cpoly B T => by
    have hB := retype_capturebound_denot ρ B
    intro A s0 e0
    simp [Ty.shape_val_denot, Ty.subst, hB]
    constructor
    · intro h
      obtain ⟨cs, B0, t0, hr, hd⟩ := h
      use cs, B0, t0
      apply And.intro hr
      intro H' CS hsub hsub_bound
      let A0 := CS.denot TypeEnv.empty
      have ih2 := retype_exi_exp_denot (ρ.liftCVar (c:=A0)) T
      specialize hd H' CS hsub hsub_bound
      exact (ih2 A H' _).mp hd
    · intro h
      obtain ⟨cs0, B0, t0, hr, hd⟩ := h
      use cs0, B0, t0
      apply And.intro hr
      intro H' CS hsub hsub_bound
      let A0 := CS.denot TypeEnv.empty
      have ih2 := retype_exi_exp_denot (ρ.liftCVar (c:=A0)) T
      specialize hd H' CS hsub hsub_bound
      exact (ih2 A H' _).mpr hd

def retype_capturebound_denot
  {s1 s2 : Sig} {env1 : TypeEnv s1} {σ : Subst s1 s2} {env2 : TypeEnv s2}
  (ρ : Retype env1 σ env2) (B : CaptureBound s1) :
  CaptureBound.denot env1 B = CaptureBound.denot env2 (B.subst σ) := by
  cases B
  case unbound => rfl
  case bound C =>
    simp [CaptureBound.denot, CaptureBound.subst]
    apply retype_captureset_denot ρ C

def retype_captureset_denot
  {s1 s2 : Sig} {env1 : TypeEnv s1} {σ : Subst s1 s2} {env2 : TypeEnv s2}
  (ρ : Retype env1 σ env2) (C : CaptureSet s1) :
  CaptureSet.denot env1 C = CaptureSet.denot env2 (C.subst σ) := by
  induction C
  case empty => rfl
  case union C1 C2 ih1 ih2 =>
    simp [CaptureSet.denot, CaptureSet.subst, ih1, ih2]
  case var x =>
    cases x
    case bound x =>
      simp [CaptureSet.denot, CaptureSet.subst, Var.subst]
      have := ρ.var x
      cases hσ : σ.var x
      case bound y =>
        simp [CaptureSet.denot, interp_var] at this ⊢
        rw [hσ] at this
        simp at this
        rw [this]
      case free n =>
        simp [CaptureSet.denot, interp_var] at this ⊢
        rw [hσ] at this
        simp at this
        rw [this]
    case free n =>
      simp [CaptureSet.denot, CaptureSet.subst, Var.subst]
  case cvar C =>
    simp [CaptureSet.denot, CaptureSet.subst]
    exact ρ.cvar C

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
    intro hwf
    exact hS (C.denot env1) s e

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
    simp [Ty.exi_val_denot, Ty.subst]
    constructor
    · intro h
      obtain ⟨A, hval⟩ := h
      use A
      have ih := retype_capt_val_denot (ρ.liftCVar (c:=A)) T
      exact (ih s e).mp hval
    · intro h
      obtain ⟨A, hval⟩ := h
      use A
      have ih := retype_capt_val_denot (ρ.liftCVar (c:=A)) T
      exact (ih s e).mpr hval

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
    (env.extend_var (interp_var env y).1 (interp_var env y).2)
    (Subst.openVar y)
    env where
  var := fun x => by cases x <;> rfl
  tvar := fun
    | .there X => by
      conv =>
        lhs
        simp [TypeEnv.extend_var, TypeEnv.lookup_tvar, TypeEnv.lookup]
      conv =>
        rhs
        simp [Subst.openVar]
      apply PreDenot.eq_to_equiv
      simp [Ty.shape_val_denot, TypeEnv.lookup_tvar]
  cvar := fun
    | .there C => by
      simp [TypeEnv.extend_var, Subst.openVar]
      unfold TypeEnv.lookup_cvar
      rfl

theorem open_arg_shape_val_denot {env : TypeEnv s} {y : Var .var s} {T : Ty .shape (s,x)} :
  Ty.shape_val_denot (env.extend_var (interp_var env y).1 (interp_var env y).2) T ≈
    Ty.shape_val_denot env (T.subst (Subst.openVar y)) := by
  apply retype_shape_val_denot Retype.open_arg

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
      simp [TypeEnv.extend_tvar, TypeEnv.lookup_tvar, TypeEnv.lookup]
      simp [Subst.openTVar, Ty.shape_val_denot]
      rfl
  cvar := fun
    | .there C => by
      simp [TypeEnv.extend_tvar, Subst.openTVar]
      unfold TypeEnv.lookup_cvar
      rfl

theorem open_targ_shape_val_denot {env : TypeEnv s} {S : Ty .shape s} {T : Ty .shape (s,X)} :
  Ty.shape_val_denot (env.extend_tvar (Ty.shape_val_denot env S)) T ≈
    Ty.shape_val_denot env (T.subst (Subst.openTVar S)) := by
  apply retype_shape_val_denot Retype.open_targ

def Retype.open_carg {env : TypeEnv s} {C : CaptureSet s} :
  Retype
    (env.extend_cvar (C.denot env))
    (Subst.openCVar C)
    env where
  var := fun x => by cases x; rfl
  tvar := fun
    | .there X => by
      apply PreDenot.eq_to_equiv
      simp [TypeEnv.extend_cvar, TypeEnv.lookup_tvar, TypeEnv.lookup]
      simp [Subst.openCVar, Ty.shape_val_denot]
      rfl
  cvar := fun
    | .here => by
      simp [TypeEnv.extend_cvar, TypeEnv.lookup_cvar, TypeEnv.lookup]
      simp [Subst.openCVar]
    | .there C => by
      simp [TypeEnv.extend_cvar, Subst.openCVar]
      unfold TypeEnv.lookup_cvar
      rfl

theorem open_carg_shape_val_denot {env : TypeEnv s} {C : CaptureSet s} {T : Ty .shape (s,C)} :
  Ty.shape_val_denot (env.extend_cvar (C.denot env)) T ≈
    Ty.shape_val_denot env (T.subst (Subst.openCVar C)) := by
  apply retype_shape_val_denot Retype.open_carg

end CC
