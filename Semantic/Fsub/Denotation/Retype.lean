import Semantic.Fsub.Denotation.Core
import Semantic.Fsub.Denotation.Rebind
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
      change env1.lookup_var y = interp_var (env2.extend_var x) ((σ.var y).rename Rename.succ)
      conv => rhs; simp [<-weaken_interp_var]
      exact ρ.var y
  tvar := fun
    | .there X => by
      conv => lhs; simp [TypeEnv.extend_var, TypeEnv.lookup_tvar, TypeEnv.lookup]
      conv => rhs; simp [Subst.lift]
      exact Denot.equiv_trans _ _ _ (ρ.tvar X) weaken_val_denot

theorem Retype.liftTVar
  (ρ : Retype env1 σ env2) :
  Retype (env1.extend_tvar d) (σ.lift) (env2.extend_tvar d) where
  var := fun
    | .there x => by
      change env1.lookup_var x = interp_var (env2.extend_tvar d) ((σ.var x).rename Rename.succ)
      conv => rhs; simp [<-tweaken_interp_var]
      exact ρ.var x
  tvar := fun
    | .here => by
      conv => lhs; simp [TypeEnv.extend_tvar, TypeEnv.lookup_tvar, TypeEnv.lookup]
      conv => rhs; simp [Subst.lift, Ty.val_denot, TypeEnv.extend_tvar, TypeEnv.lookup_tvar,
                         TypeEnv.lookup]
      apply Denot.equiv_refl
    | .there X => by
      conv => lhs; simp [TypeEnv.extend_tvar, TypeEnv.lookup_tvar, TypeEnv.lookup]
      conv => rhs; simp [Subst.lift]
      exact Denot.equiv_trans _ _ _ (ρ.tvar X) tweaken_val_denot

mutual

theorem retype_val_denot
  (ρ : Retype env1 σ env2) :
  Ty.val_denot env1 T ≈ Ty.val_denot env2 (T.subst σ) :=
  match T with
  | .top => by simp [Denot.Equiv, Ty.val_denot, Ty.subst]
  | .tvar X => by
    simpa only [Ty.val_denot, Ty.subst] using ρ.tvar X
  | .singleton x => by
    apply Denot.eq_to_equiv; funext s e
    simp only [Ty.val_denot, Ty.subst]
    cases x with
    | bound x =>
      simp only [Var.subst, interp_var]
      exact congrArg (fun n => e = .var (.free n)) (ρ.var x)
    | free n => simp [Var.subst, interp_var]
  | .arrow T1 T2 => by
    have ih1 := retype_val_denot ρ (T:=T1)
    simp only [Ty.val_denot, Ty.subst]
    intro s0 e0; constructor
    · intro h
      obtain ⟨T0, body, hr, hd⟩ := h
      exact ⟨T0, body, hr, fun s' arg h_s harg =>
        (retype_exp_denot (ρ.liftVar (x:=arg)) (T:=T2) _ _).mp
          (hd s' arg h_s ((ih1 _ _).mpr harg))⟩
    · intro h
      obtain ⟨T0, body, hr, hd⟩ := h
      exact ⟨T0, body, hr, fun s' arg h_s harg =>
        (retype_exp_denot (ρ.liftVar (x:=arg)) (T:=T2) _ _).mpr
          (hd s' arg h_s ((ih1 _ _).mp harg))⟩
  | .poly T1 T2 => by
    have ih1 := retype_val_denot ρ (T:=T1)
    simp only [Ty.val_denot, Ty.subst]
    intro s0 e0; constructor
    · intro h
      obtain ⟨T0, e0, hr, hd⟩ := h
      refine ⟨T0, e0, hr, fun H denot Hs hm ht himply => ?_⟩
      exact (retype_exp_denot (ρ.liftTVar (d:=denot)) (T:=T2) H _).mp
        (hd H denot Hs hm ht (fun s hs e hd => (ih1 s e).mpr (himply s hs e hd)))
    · intro h
      obtain ⟨T0, e0, hr, hd⟩ := h
      refine ⟨T0, e0, hr, fun H denot Hs hm ht himply => ?_⟩
      exact (retype_exp_denot (ρ.liftTVar (d:=denot)) (T:=T2) H _).mpr
        (hd H denot Hs hm ht (fun s hs e hd => (ih1 s e).mp (himply s hs e hd)))

theorem retype_exp_denot
  (ρ : Retype env1 σ env2) :
  Ty.exp_denot env1 T ≈ Ty.exp_denot env2 (T.subst σ) := by
  have ⟨himp1, himp2⟩ := Denot.equiv_to_imply (retype_val_denot ρ (T:=T))
  intro s e; simp only [Ty.exp_denot]; constructor
  · intro h; exact eval_post_monotonic (Denot.imply_to_entails _ _ himp1) h
  · intro h; exact eval_post_monotonic (Denot.imply_to_entails _ _ himp2) h

end

def Retype.open_arg {env : TypeEnv s} {y : Var s} :
  Retype
    (env.extend_var (interp_var env y))
    (Subst.openVar y)
    env where
  var := fun x => by cases x <;> rfl
  tvar := fun
    | .there X => by
      simp only [TypeEnv.extend_var, TypeEnv.lookup_tvar, Subst.openVar, Ty.val_denot]
      exact Denot.equiv_refl _

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
    | .here => by apply Denot.eq_to_equiv; rfl
    | .there X => by
      apply Denot.eq_to_equiv
      simp [TypeEnv.extend_tvar, TypeEnv.lookup_tvar]
      simp [Subst.openTVar, Ty.val_denot]
      rfl

theorem open_targ_val_denot {env : TypeEnv s} {S : Ty s} {T : Ty (s,X)} :
  Ty.val_denot (env.extend_tvar (Ty.val_denot env S)) T ≈
    Ty.val_denot env (T.subst (Subst.openTVar S)) := by
  apply retype_val_denot Retype.open_targ

end Fsub
