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
  Ty.val_denot env1 T ≈ Ty.val_denot env2 (T.subst σ) := sorry

theorem retype_exp_denot
  (ρ : Retype env1 σ env2) :
  Ty.exp_denot env1 T ≈ Ty.exp_denot env2 (T.subst σ) := sorry

end

end Fsub
