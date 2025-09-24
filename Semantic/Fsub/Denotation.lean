import Semantic.Fsub.Eval
import Semantic.Fsub.TypeSystem

namespace Fsub

def resolve : Store -> Exp {} -> Option (Exp {})
| s, .var (.free x) =>
  match s.lookup x with
  | some v => some v.unwrap
  | none => none
| _, other => some other

/-- Denotation of types. -/
def Denot := Store -> Exp {} -> Prop

def Denot.Imply (d1 d2 : Denot) : Prop :=
  ∀ s e,
    (d1 s e) ->
    (d2 s e)

inductive TypeInfo : Kind -> Type where
| var : Nat -> TypeInfo .var
| tvar : Denot -> TypeInfo .tvar

inductive TypeEnv : Sig -> Type where
| empty : TypeEnv {}
| extend :
  TypeEnv s ->
  TypeInfo k ->
  TypeEnv (s,,k)

def TypeEnv.extend_var (Γ : TypeEnv s) (x : Nat) : TypeEnv (s,x) :=
  Γ.extend (.var x)

def TypeEnv.extend_tvar (Γ : TypeEnv s) (T : Denot) : TypeEnv (s,X) :=
  Γ.extend (.tvar T)

def TypeEnv.lookup : (Γ : TypeEnv s) -> (x : BVar s k) -> TypeInfo k
| .extend _ info, .here => info
| .extend Γ _,    .there x => Γ.lookup x

def TypeEnv.lookup_var (Γ : TypeEnv s) (x : BVar s .var) : Nat :=
  match Γ.lookup x with
  | .var y => y

def TypeEnv.lookup_tvar (Γ : TypeEnv s) (x : BVar s .tvar) : Denot :=
  match Γ.lookup x with
  | .tvar T => T

def interp_var (env : TypeEnv s) (x : Var s) : Nat :=
  match x with
  | .free n => n
  | .bound x => env.lookup_var x

mutual

def Ty.val_denot : TypeEnv s -> Ty s -> Denot
| _, .top => fun _ _ => True
| env, .tvar X => env.lookup_tvar X
| env, .singleton x => fun _ e =>
  e = .var (.free (interp_var env x))
| env, .poly T1 T2 => fun s e =>
  ∃ T0 e0,
    resolve s e = some (.tabs T0 e0) ∧
    (∀ (denot : Denot),
      denot.Imply (Ty.val_denot env T1) ->
      Ty.exp_denot (env.extend_tvar denot) T2 s (e0.subst (Subst.openTVar .top)))
| env, .arrow T1 T2 => fun s e =>
  ∃ T0 e0,
    resolve s e = some (.abs T0 e0) ∧
    (∀ arg,
      Ty.val_denot env T1 s (.var (.free arg)) ->
      Ty.exp_denot (env.extend_var arg) T2 s (e0.subst (Subst.openVar (.free arg))))

def Ty.exp_denot : TypeEnv s -> Ty s -> Denot
| env, T => fun s e =>
  ∃ s' v,
    Reduce s e s' v ∧
    Ty.val_denot env T s' v

end

def EnvTyping : Ctx s -> TypeEnv s -> Store -> Prop
| .empty, .empty, store => True
| .push Γ (.var T), .extend env (.var n), store =>
  Ty.val_denot env T store (.var (.free n)) ∧
    EnvTyping Γ env store
| .push Γ (.tvar S), .extend env (.tvar d), store =>
  d.Imply (Ty.val_denot env S) ∧
  EnvTyping Γ env store

def Subst.from_TypeEnv (env : TypeEnv s) : Subst s {} where
  var := fun x => .free (env.lookup_var x)
  tvar := fun _ => .top  -- types can be simply erased

def SemanticTyping (Γ : Ctx s) (e : Exp s) (T : Ty s) : Prop :=
  ∀ env store,
    EnvTyping Γ env store ->
    Ty.exp_denot env T store (e.subst (Subst.from_TypeEnv env))

notation:65 Γ " ⊨ " e " : " T => SemanticTyping Γ e T

theorem Subst.from_TypeEnv_weaken_open :
  (Subst.from_TypeEnv env).lift.comp (Subst.openVar (.free x)) =
    Subst.from_TypeEnv (env.extend_var x) := by
  apply Subst.funext
  · intro x
    cases x <;> rfl
  · intro X
    cases X; rfl

theorem Exp.from_TypeEnv_weaken_open {e : Exp (s,x)} :
  (e.subst (Subst.from_TypeEnv env).lift).subst (Subst.openVar (.free x)) =
    e.subst (Subst.from_TypeEnv (env.extend_var x)) := by
  simp [Exp.subst_comp]
  simp [Subst.from_TypeEnv_weaken_open]

theorem Subst.from_TypeEnv_weaken_open_tvar :
  (Subst.from_TypeEnv env).lift.comp (Subst.openTVar .top) =
    Subst.from_TypeEnv (env.extend_tvar d) := by
  apply Subst.funext
  · intro x
    cases x; rfl
  · intro X
    cases X
    case here => rfl
    case there x => rfl

theorem Exp.from_TypeEnv_weaken_open_tvar {e : Exp (s,X)} :
  (e.subst (Subst.from_TypeEnv env).lift).subst (Subst.openTVar .top) =
    e.subst (Subst.from_TypeEnv (env.extend_tvar d)) := by
  simp [Exp.subst_comp]
  rw [Subst.from_TypeEnv_weaken_open_tvar]

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

mutual

def rebind_val_denot
  (ρ : Rebind env1 f env2) :
  Ty.val_denot env1 T = Ty.val_denot env2 (T.rename f) :=
  match T with
  | .top => by
    simp [Ty.val_denot, Ty.rename]
  | .tvar X => by
    simp [Ty.val_denot, Ty.rename]
    sorry
  | .singleton x => by
    simp [Ty.val_denot, Ty.rename]
    sorry
  | .arrow T1 T2 => by
    have ih1 := rebind_val_denot ρ (T:=T1)
    sorry
  | .poly T1 T2 => by
    have ih1 := rebind_val_denot ρ (T:=T1)
    sorry

def rebind_exp_denot
  (ρ : Rebind env1 f env2) :
  Ty.exp_denot env1 T = Ty.exp_denot env2 (T.rename f) := by
  have ih := rebind_val_denot ρ (T:=T)
  simp [Ty.exp_denot, ih]

end

-- structure EnvMorphism (env1 : TypeEnv s1) (σ : Subst s1 s2) (env2 : TypeEnv s2) : Prop where
--   var :
--     ∀ (x : BVar s1 .var),
--       env1.lookup_var x = interp_var env2 (σ.var x)
--   tvar :
--     ∀ (X : BVar s1 .tvar),
--       env1.lookup_tvar X = Ty.val_denot env2 (σ.tvar X)

-- def EnvMorphism.liftVar
--   (ρ : EnvMorphism env1 σ env2) :
--   EnvMorphism (env1.extend_var x) (σ.lift) (env2.extend_var x) where
--   var := fun
--     | .here => rfl
--     | .there y => sorry
--   tvar := fun
--     | .there X => sorry

-- mutual

-- theorem map_val_denot
--   (ρ : EnvMorphism env1 σ env2) :
--   Ty.val_denot env1 T = Ty.val_denot env2 (T.subst σ) :=
--   match T with
--   | .top => by
--     simp [Ty.val_denot, Ty.subst]
--   | .tvar X => by
--     simp [Ty.val_denot, Ty.subst]
--     rw [ρ.tvar X]
--   | .singleton x => by
--     simp [Ty.val_denot, Ty.subst]
--     cases x
--     case free fx => rfl
--     case bound bx =>
--       simp [interp_var, ρ.var bx]
--       rfl
--   | .arrow T1 T2 => by
--     have ih1 := map_val_denot ρ (T:=T1)
--     sorry
--   | .poly T1 T2 => sorry

-- theorem map_exp_denot
--   (ρ : EnvMorphism env1 σ env2) :
--   Ty.exp_denot env1 T = Ty.exp_denot env2 (T.subst σ) := by
--   have ih := map_val_denot ρ (T:=T)
--   simp [Ty.exp_denot, ih]

-- end

end Fsub
