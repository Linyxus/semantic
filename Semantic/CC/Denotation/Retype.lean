import Semantic.CC.Denotation.Core
import Semantic.CC.Denotation.Rebind
namespace Fsub

structure Retype (env1 : TypeEnv s1) (σ : Subst s1 s2) (env2 : TypeEnv s2) where
  var :
    ∀ (x : BVar s1 .var),
      env1.lookup_var x = interp_var env2 (σ.var x)

  tvar :
    ∀ (X : BVar s1 .tvar),
      env1.lookup_tvar X ≈ Ty.val_denot env2 (σ.tvar X)

lemma weaken_interp_var {x : Var s} :
  interp_var env x = interp_var (env.extend_var arg) (x.rename Rename.succ) := by
  cases x <;> rfl

lemma tweaken_interp_var {x : Var s} :
  interp_var env x = interp_var (env.extend_tvar d) (x.rename Rename.succ) := by
  cases x <;> rfl

theorem Retype.liftVar
  (ρ : Retype env1 σ env2) :
  Retype (env1.extend_var x) (σ.lift) (env2.extend_var x) where
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
      apply Denot.equiv_trans _ _ _ (ρ.tvar X)
      apply weaken_val_denot

theorem Retype.liftTVar
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
        simp [Subst.lift, Ty.val_denot, TypeEnv.extend_tvar, TypeEnv.lookup_tvar, TypeEnv.lookup]
      apply Denot.equiv_refl
    | .there X => by
      conv =>
        lhs
        simp [TypeEnv.extend_tvar, TypeEnv.lookup_tvar, TypeEnv.lookup]
      conv =>
        rhs
        simp [Subst.lift]
      apply Denot.equiv_trans _ _ _ (ρ.tvar X)
      apply tweaken_val_denot

mutual

theorem retype_val_denot
  (ρ : Retype env1 σ env2) :
  Ty.val_denot env1 T ≈ Ty.val_denot env2 (T.subst σ) :=
  match T with
  | .top => by
    apply Denot.eq_to_equiv
    simp [Ty.val_denot, Ty.subst]
  | .tvar X => by
    simp [Ty.val_denot, Ty.subst]
    exact ρ.tvar X
  | .singleton x => by
    simp [Ty.val_denot, Ty.subst]
    intro s e
    simp
    cases x with
    | bound x =>
      conv =>
        arg 1
        simp [Var.subst, interp_var]
      have := ρ.var x
      simp [this]
      aesop
    | free n =>
      simp [Var.subst, interp_var]
  | .arrow T1 T2 => by
    have ih1 := retype_val_denot ρ (T:=T1)
    simp [Ty.val_denot, Ty.subst]
    intro s0 e0
    simp; constructor
    next =>
      intro h
      have ⟨T0, body, hr, hd⟩ := h
      use T0, body
      apply And.intro hr
      intro s' arg h_s harg
      have ih2 := retype_exp_denot (ρ.liftVar (x:=arg)) (T:=T2)
      have harg' := (ih1 _ _).mpr harg
      specialize hd s' arg h_s harg'
      have hd' := (ih2 _ _).mp hd
      exact hd'
    next =>
      intro h
      have ⟨T0, body, hr, hd⟩ := h
      use T0, body
      apply And.intro hr
      intro s' arg h_s harg
      have ih2 := retype_exp_denot (ρ.liftVar (x:=arg)) (T:=T2)
      have harg' := (ih1 _ _).mp harg
      specialize hd s' arg h_s harg'
      have hd' := (ih2 _ _).mpr hd
      exact hd'
  | .poly T1 T2 => by
    have ih1 := retype_val_denot ρ (T:=T1)
    simp [Ty.val_denot, Ty.subst]
    intro s0 e0; simp
    constructor
    next =>
      intro h
      have ⟨T0, e0, hr, hd⟩ := h
      use T0, e0
      apply And.intro hr
      intro H denot Hs hdenot_mono hdenot_trans himply
      have ih2 := retype_exp_denot (ρ.liftTVar (d:=denot)) (T:=T2)
      have himply' : denot.ImplyAfter H (Ty.val_denot env1 T1) := by
        intro s hs e hdenot
        have := (ih1 s e).mpr (himply s hs e hdenot)
        exact this
      specialize hd H denot Hs hdenot_mono hdenot_trans himply'
      have hd' := (ih2 H (e0.subst (Subst.openTVar .top))).mp hd
      exact hd'
    next =>
      intro h
      have ⟨T0, e0, hr, hd⟩ := h
      use T0, e0
      apply And.intro hr
      intro H denot Hs hdenot_mono hdenot_trans himply
      have ih2 := retype_exp_denot (ρ.liftTVar (d:=denot)) (T:=T2)
      have himply' : denot.ImplyAfter H (Ty.val_denot env2 (T1.subst σ)) := by
        intro s hs e hdenot
        have := (ih1 s e).mp (himply s hs e hdenot)
        exact this
      specialize hd H denot Hs hdenot_mono hdenot_trans himply'
      have hd' := (ih2 H (e0.subst (Subst.openTVar .top))).mpr hd
      exact hd'

theorem retype_exp_denot
  (ρ : Retype env1 σ env2) :
  Ty.exp_denot env1 T ≈ Ty.exp_denot env2 (T.subst σ) := by
  have ih := retype_val_denot ρ (T:=T)
  intro s e
  simp [Ty.exp_denot]
  constructor
  · intro h
    apply eval_post_monotonic _ h
    apply Denot.imply_to_entails
    apply (Denot.equiv_to_imply ih).1
  · intro h
    apply eval_post_monotonic _ h
    apply Denot.imply_to_entails
    apply (Denot.equiv_to_imply ih).2

end

def Retype.open_arg {env : TypeEnv s} {y : Var s} :
  Retype
    (env.extend_var (interp_var env y))
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
      apply Denot.eq_to_equiv
      simp [Ty.val_denot, TypeEnv.lookup_tvar]

theorem open_arg_val_denot {env : TypeEnv s} {y : Var s} {T : Ty (s,x)} :
  Ty.val_denot (env.extend_var (interp_var env y)) T ≈
    Ty.val_denot env (T.subst (Subst.openVar y)) := by
  apply retype_val_denot Retype.open_arg

def Retype.open_targ {env : TypeEnv s} {S : Ty s} :
  Retype
    (env.extend_tvar (Ty.val_denot env S))
    (Subst.openTVar S)
    env where
  var := fun x => by cases x; rfl
  tvar := fun
    | .here => by
      apply Denot.eq_to_equiv
      rfl
    | .there X => by
      apply Denot.eq_to_equiv
      simp [TypeEnv.extend_tvar, TypeEnv.lookup_tvar, TypeEnv.lookup]
      simp [Subst.openTVar, Ty.val_denot]
      rfl

theorem open_targ_val_denot {env : TypeEnv s} {S : Ty s} {T : Ty (s,X)} :
  Ty.val_denot (env.extend_tvar (Ty.val_denot env S)) T ≈
    Ty.val_denot env (T.subst (Subst.openTVar S)) := by
  apply retype_val_denot Retype.open_targ

end Fsub
