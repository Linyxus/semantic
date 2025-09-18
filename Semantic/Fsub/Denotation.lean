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

mutual

def Ty.val_denot : TypeEnv s -> Ty s -> Denot
| _, .top => fun _ _ => True
| env, .tvar X => env.lookup_tvar X
| _, .singleton (.free x) => fun _ e =>
  e = .var (.free x)
| env, .singleton (.bound x) => fun _ e =>
  e = .var (.free (env.lookup_var x))
| env, .poly T1 T2 => fun s e =>
  ∃ T0 e0,
    resolve s e = some (.tabs T0 e0) ∧
    (∀ (denot : Denot),
      denot.Imply (Ty.val_denot env T1) ->
      Ty.val_denot (env.extend_tvar denot) T2 s (e0.subst (Subst.openTVar T0)))
| env, .arrow T1 T2 => fun s e =>
  ∃ T0 e0,
    resolve s e = some (.abs T0 e0) ∧
    (∀ arg,
      Ty.val_denot env T1 s (.var (.free arg)) ->
      Ty.val_denot (env.extend_var arg) T2 s (e0.subst (Subst.openVar (.free arg))))

def Ty.exp_denot : TypeEnv s -> Ty s -> Denot
| env, T => fun s e =>
  ∃ s' v,
    Reduce s e s' v ∧
    Ty.val_denot env T s' v

end

def EnvTyping : Ctx s -> TypeEnv s -> Store -> Prop
| .empty, .empty, store => True
| .push Γ (.var T), .extend env (.var n), store =>
  ∃ v,
    store.lookup n = some v ∧
    Ty.val_denot env T store v.unwrap ∧
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

end Fsub
