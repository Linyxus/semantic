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
| _, .top => fun _ e => e.IsAns
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

def Denot.Equiv (d1 d2 : Denot) : Prop :=
  ∀ s e,
    (d1 s e) ↔ (d2 s e)

instance Denot.instHasEquiv : HasEquiv Denot where
  Equiv := Denot.Equiv

def Denot.equiv_refl (d : Denot) : d ≈ d := by
  intro s e
  constructor
  · intro h
    exact h
  · intro h
    exact h

def Denot.equiv_symm (d1 d2 : Denot) : d1 ≈ d2 -> d2 ≈ d1 := by
  intro h
  intro s e
  constructor
  · intro h0
    apply (h s e).mpr h0
  · intro h0
    apply (h s e).mp h0

def Denot.equiv_trans (d1 d2 d3 : Denot) : d1 ≈ d2 -> d2 ≈ d3 -> d1 ≈ d3 := by
  intro h12
  intro h23
  intro s e
  have h1 := h12 s e
  have h2 := h23 s e
  grind

theorem Denot.eq_to_equiv (d1 d2 : Denot) : d1 = d2 -> d1 ≈ d2 := by
  intro h
  intro s e
  grind

theorem Denot.equiv_ltr {d1 d2 : Denot}
  (heqv : d1 ≈ d2)
  (h1 : d1 s e) :
  d2 s e := by
  apply (heqv s e).mp h1

theorem Denot.equiv_rtl {d1 d2 : Denot}
  (heqv : d1 ≈ d2)
  (h2 : d2 s e) :
  d1 s e := by
  apply (heqv s e).mpr h2

theorem Denot.imply_refl (d : Denot) : d.Imply d := by
  intro s e h
  exact h

theorem Denot.imply_trans {d1 d2 d3 : Denot}
  (h1 : d1.Imply d2)
  (h2 : d2.Imply d3) :
  d1.Imply d3 := by
  intro s e h
  aesop

def Denot.ans : Denot :=
  fun _ e => Exp.IsAns e

def TypeEnv.inert (env : TypeEnv s) : Prop :=
  ∀ (x : BVar s .tvar),
    (env.lookup_tvar x).Imply Denot.ans

theorem resolve_var_or_val
  (hv : resolve store e = some v) :
  (∃ x, e = .var x) ∨ e = v := by
  cases e
  all_goals try (solve | aesop | simp [resolve] at hv; aesop)

theorem resolve_ans_to_val
  (hv : resolve store e = some v)
  (hans : v.IsAns) :
  e.IsAns := by
  cases (resolve_var_or_val hv)
  case inl h =>
    have ⟨x, h⟩ := h
    rw [h]
    apply Exp.IsAns.is_var
  case inr h => aesop

theorem val_denot_ans {env : TypeEnv s}
  (henv : env.inert) :
  (Ty.val_denot env T).Imply Denot.ans := by
  cases T
  case top =>
    intro s e h
    simp [Ty.val_denot] at h
    aesop
  case tvar X =>
    simp [Ty.val_denot]
    apply henv
  case singleton x =>
    intro s e h
    simp [Ty.val_denot] at h
    rw [h]
    simp [Denot.ans]
    apply Exp.IsAns.is_var
  case poly T1 T2 =>
    intro s e h
    simp [Ty.val_denot] at h
    have ⟨T0, e0, hr, hfun⟩ := h
    apply resolve_ans_to_val hr
    constructor; constructor
  case arrow T1 T2 =>
    intro s e h
    simp [Ty.val_denot] at h
    have ⟨T0, e0, hr, hfun⟩ := h
    apply resolve_ans_to_val hr
    constructor; constructor

end Fsub
