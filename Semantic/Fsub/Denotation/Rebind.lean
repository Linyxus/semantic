import Semantic.Fsub.Denotation.Core
namespace Fsub

structure Rebind (env1 : TypeEnv s1) (f : Rename s1 s2) (env2 : TypeEnv s2) : Prop where
  var :
    ∀ (x : BVar s1 k),
      env1.lookup x = env2.lookup (f.var x)

def Rebind.liftVar
  (ρ : Rebind env1 f env2) :
  Rebind (env1.extend_var x) (f.lift) (env2.extend_var x) where
  var := fun
    | .here => rfl
    | .there y => by
      simpa only [TypeEnv.extend_var, Rename.lift, TypeEnv.lookup] using ρ.var y

def Rebind.liftTVar
  (ρ : Rebind env1 f env2) :
  Rebind (env1.extend_tvar d) (f.lift) (env2.extend_tvar d) where
  var := fun
    | .here => rfl
    | .there y => by
      simpa only [TypeEnv.extend_tvar, Rename.lift, TypeEnv.lookup] using ρ.var y

theorem rebind_interp_var
  (ρ : Rebind env1 f env2) :
  interp_var env1 x = interp_var env2 (x.rename f) := by
  cases x with
  | bound x => simp only [interp_var, Var.rename, TypeEnv.lookup_var, ρ.var x]
  | free n => rfl

mutual

def rebind_val_denot
  (ρ : Rebind env1 f env2) :
  Ty.val_denot env1 T ≈ Ty.val_denot env2 (T.rename f) :=
  match T with
  | .top => by simp [Denot.Equiv, Ty.val_denot, Ty.rename]
  | .tvar X => by
    apply Denot.eq_to_equiv
    simp only [Ty.val_denot, Ty.rename, TypeEnv.lookup_tvar, ρ.var X]
  | .singleton x => by
    apply Denot.eq_to_equiv
    simp only [Ty.val_denot, Ty.rename, rebind_interp_var ρ (x:=x)]
  | .arrow T1 T2 => by
    have ih1 := rebind_val_denot ρ (T:=T1)
    simp only [Ty.val_denot, Ty.rename]
    intro s0 e0; constructor
    · intro h
      obtain ⟨T0, body, hr, hd⟩ := h
      exact ⟨T0, body, hr, fun s' arg h_s harg =>
        (rebind_exp_denot (ρ.liftVar (x:=arg)) (T:=T2) _ _).mp
          (hd s' arg h_s ((ih1 _ _).mpr harg))⟩
    · intro h
      obtain ⟨T0, body, hr, hd⟩ := h
      exact ⟨T0, body, hr, fun s' arg h_s harg =>
        (rebind_exp_denot (ρ.liftVar (x:=arg)) (T:=T2) _ _).mpr
          (hd s' arg h_s ((ih1 _ _).mp harg))⟩
  | .poly T1 T2 => by
    have ih1 := rebind_val_denot ρ (T:=T1)
    simp only [Ty.val_denot, Ty.rename]
    intro s0 e0; constructor
    · intro h
      obtain ⟨T0, e0, hr, hd⟩ := h
      refine ⟨T0, e0, hr, fun H denot Hsub hm ht himply => ?_⟩
      exact (rebind_exp_denot (ρ.liftTVar (d:=denot)) (T:=T2) H _).mp
        (hd H denot Hsub hm ht (fun s hs e hd => (ih1 s e).mpr (himply s hs e hd)))
    · intro h
      obtain ⟨T0, e0, hr, hd⟩ := h
      refine ⟨T0, e0, hr, fun H denot Hsub hm ht himply => ?_⟩
      exact (rebind_exp_denot (ρ.liftTVar (d:=denot)) (T:=T2) H _).mpr
        (hd H denot Hsub hm ht (fun s hs e hd => (ih1 s e).mp (himply s hs e hd)))

def rebind_exp_denot
  (ρ : Rebind env1 f env2) :
  Ty.exp_denot env1 T ≈ Ty.exp_denot env2 (T.rename f) := by
  have ⟨himp1, himp2⟩ := Denot.equiv_to_imply (rebind_val_denot ρ (T:=T))
  intro s e; simp only [Ty.exp_denot]; constructor
  · intro h; exact eval_post_monotonic (Denot.imply_to_entails _ _ himp1) h
  · intro h; exact eval_post_monotonic (Denot.imply_to_entails _ _ himp2) h

end

def Rebind.weaken {env : TypeEnv s} :
  Rebind env Rename.succ (env.extend_var x) where
  var _ := rfl

def Rebind.tweaken {env : TypeEnv s} :
  Rebind env Rename.succ (env.extend_tvar d) where
  var _ := rfl

lemma weaken_val_denot {env : TypeEnv s} :
  Ty.val_denot env T ≈ Ty.val_denot (env.extend_var x) (T.rename Rename.succ) := by
  apply rebind_val_denot (ρ:=Rebind.weaken) (T:=T)

lemma tweaken_val_denot {env : TypeEnv s} :
  Ty.val_denot env T ≈ Ty.val_denot (env.extend_tvar d) (T.rename Rename.succ) := by
  apply rebind_val_denot (ρ:=Rebind.tweaken) (T:=T)

end Fsub
