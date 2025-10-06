import Semantic.FsubNext.Denotation.Core
namespace FsubNext

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
      simp [TypeEnv.extend_var, Rename.lift, TypeEnv.lookup]
      exact ρ.var y

def Rebind.liftTVar
  (ρ : Rebind env1 f env2) :
  Rebind (env1.extend_tvar d) (f.lift) (env2.extend_tvar d) where
  var := fun
    | .here => rfl
    | .there y => by
      simp [TypeEnv.extend_tvar, Rename.lift, TypeEnv.lookup]
      exact ρ.var y

theorem rebind_interp_var
  (ρ : Rebind env1 f env2) :
  interp_var env1 x = interp_var env2 (x.rename f) := by
  cases x
  case bound x =>
    simp [interp_var, Var.rename]
    have := ρ.var x
    grind [TypeEnv.lookup_var]
  case free n => rfl

mutual

def rebind_val_denot
  (ρ : Rebind env1 f env2) :
  Ty.val_denot env1 T ≈ Ty.val_denot env2 (T.rename f) :=
  match T with
  | .top => by
    apply Denot.eq_to_equiv
    simp [Ty.val_denot, Ty.rename]
  | .tvar X => by
    simp [Ty.val_denot, Ty.rename]
    apply Denot.eq_to_equiv
    have h := ρ.var X
    simp [TypeEnv.lookup_tvar]
    grind
  | .singleton x => by
    simp [Ty.val_denot, Ty.rename]
    have := rebind_interp_var ρ (x:=x)
    apply Denot.eq_to_equiv
    simp [this]
  | .arrow T1 T2 => by
    have ih1 := rebind_val_denot ρ (T:=T1)
    simp [Ty.val_denot, Ty.rename]
    intro s0 e0
    simp; constructor
    next =>
      intro h
      have ⟨T0, body, hr, hd⟩ := h
      use T0, body
      apply And.intro hr
      intro arg harg
      have ih2 := rebind_exp_denot (ρ.liftVar (x:=arg)) (T:=T2)
      have harg' := (ih1 _ _).mpr harg
      specialize hd _ harg'
      have hd' := (ih2 _ _).mp hd
      exact hd'
    next =>
      intro h
      have ⟨T0, body, hr, hd⟩ := h
      use T0, body
      apply And.intro hr
      intro arg harg
      have ih2 := rebind_exp_denot (ρ.liftVar (x:=arg)) (T:=T2)
      have harg' := (ih1 _ _).mp harg
      specialize hd _ harg'
      have hd' := (ih2 _ _).mpr hd
      exact hd'
  | .poly T1 T2 => by
    have ih1 := rebind_val_denot ρ (T:=T1)
    simp [Ty.val_denot, Ty.rename]
    intro s0 e0; simp
    constructor
    next =>
      intro h
      have ⟨T0, e0, hr, hd⟩ := h
      use T0, e0
      apply And.intro hr
      intro denot himply
      have ih2 := rebind_exp_denot (ρ.liftTVar (d:=denot)) (T:=T2)
      have himply' : denot.Imply (Ty.val_denot env1 T1) := by
        intro s e hdenot
        have := (ih1 s e).mpr (himply s e hdenot)
        exact this
      specialize hd denot himply'
      have hd' := (ih2 s0 (e0.subst (Subst.openTVar .top))).mp hd
      exact hd'
    next =>
      intro h
      have ⟨T0, e0, hr, hd⟩ := h
      use T0, e0
      apply And.intro hr
      intro denot himply
      have ih2 := rebind_exp_denot (ρ.liftTVar (d:=denot)) (T:=T2)
      have himply' : denot.Imply (Ty.val_denot env2 (T1.rename f)) := by
        intro s e hdenot
        have := (ih1 s e).mp (himply s e hdenot)
        exact this
      specialize hd denot himply'
      have hd' := (ih2 s0 (e0.subst (Subst.openTVar .top))).mpr hd
      exact hd'

def rebind_exp_denot
  (ρ : Rebind env1 f env2) :
  Ty.exp_denot env1 T ≈ Ty.exp_denot env2 (T.rename f) := by
  have ih := rebind_val_denot ρ (T:=T)
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

def Rebind.weaken {env : TypeEnv s} :
  Rebind env Rename.succ (env.extend_var x) where
  var := fun _ => rfl

def Rebind.tweaken {env : TypeEnv s} :
  Rebind env Rename.succ (env.extend_tvar d) where
  var := fun _ => rfl

lemma weaken_val_denot {env : TypeEnv s} :
  Ty.val_denot env T ≈ Ty.val_denot (env.extend_var x) (T.rename Rename.succ) := by
  apply rebind_val_denot (ρ:=Rebind.weaken) (T:=T)

lemma tweaken_val_denot {env : TypeEnv s} :
  Ty.val_denot env T ≈ Ty.val_denot (env.extend_tvar d) (T.rename Rename.succ) := by
  apply rebind_val_denot (ρ:=Rebind.tweaken) (T:=T)

end FsubNext
