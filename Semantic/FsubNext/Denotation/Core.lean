import Semantic.FsubNext.Eval
import Semantic.FsubNext.TypeSystem

namespace FsubNext

def resolve : Heap -> Exp {} -> Option (Exp {})
| s, .var (.free x) =>
  match s x with
  | some v => some v.unwrap
  | none => none
| _, other => some other

/-- Denotation of types. -/
def Denot := Heap -> Exp {} -> Prop

def Denot.as_post (d : Denot) : Hpost :=
  fun e h => d h e

def Denot.is_monotonic (d : Denot) : Prop :=
  ∀ {h1 h2 : Heap} {e},
    h2.subsumes h1 ->
    d h1 e ->
    d h2 e

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
| env, .arrow T1 T2 => fun s e =>
  ∃ T0 e0,
    resolve s e = some (.abs T0 e0) ∧
    (∀ (s' : Heap) arg,
      (s'.subsumes s) ->
      Ty.val_denot env T1 s' (.var (.free arg)) ->
      Ty.exp_denot (env.extend_var arg) T2 s' (e0.subst (Subst.openVar (.free arg))))
| env, .poly T1 T2 => fun s e =>
  ∃ T0 e0,
    resolve s e = some (.tabs T0 e0) ∧
    (∀ (denot : Denot),
      denot.is_monotonic ->
      denot.Imply (Ty.val_denot env T1) ->
      Ty.exp_denot (env.extend_tvar denot) T2 s (e0.subst (Subst.openTVar .top)))

def Ty.exp_denot : TypeEnv s -> Ty s -> Denot
| env, T => fun s e =>
  Eval s e (Ty.val_denot env T).as_post

end

def EnvTyping : Ctx s -> TypeEnv s -> Heap -> Prop
| .empty, .empty, store => True
| .push Γ (.var T), .extend env (.var n), store =>
  Ty.val_denot env T store (.var (.free n)) ∧
    EnvTyping Γ env store
| .push Γ (.tvar S), .extend env (.tvar d), store =>
  d.is_monotonic ∧
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

theorem Denot.equiv_to_imply {d1 d2 : Denot}
  (heqv : d1 ≈ d2) :
  (d1.Imply d2) ∧ (d2.Imply d1) := by
  constructor
  · intro s e h
    apply (heqv s e).mp h
  · intro s e h
    apply (heqv s e).mpr h

theorem Denot.imply_to_entails (d1 d2 : Denot)
  (himp : d1.Imply d2) :
  d1.as_post.entails d2.as_post := by
  intro h e h1
  apply himp h e h1

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

theorem typed_env_is_inert
  (ht : EnvTyping Γ env store) :
  env.inert := by
  induction Γ with
  | empty =>
    cases env with
    | empty =>
      simp [TypeEnv.inert]
      intro x
      cases x
  | push Γ k ih =>
    cases env with
    | extend env' info =>
      cases k with
      | var T =>
        cases info with
        | var n =>
          simp [EnvTyping] at ht
          have ⟨_, ht'⟩ := ht
          have ih_result := ih ht'
          simp [TypeEnv.inert] at ih_result ⊢
          intro x
          cases x with
          | there x =>
            simp [TypeEnv.lookup_tvar, TypeEnv.lookup]
            exact ih_result x
      | tvar S =>
        cases info with
        | tvar d =>
          simp [EnvTyping] at ht
          have ⟨_, himpl, ht'⟩ := ht
          have ih_result := ih ht'
          simp [TypeEnv.inert] at ih_result ⊢
          intro x
          cases x with
          | here =>
            simp [TypeEnv.lookup_tvar, TypeEnv.lookup]
            apply Denot.imply_trans himpl (val_denot_ans ih_result)
          | there x =>
            simp [TypeEnv.lookup_tvar, TypeEnv.lookup]
            exact ih_result x

def TypeEnv.is_monotonic (env : TypeEnv s) : Prop :=
  ∀ (X : BVar s .tvar),
    (env.lookup_tvar X).is_monotonic

theorem typed_env_is_monotonic
  (ht : EnvTyping Γ env store) :
  env.is_monotonic := by
  induction Γ with
  | empty =>
    cases env with
    | empty =>
      simp [TypeEnv.is_monotonic]
      intro x
      cases x
  | push Γ k ih =>
    cases env with
    | extend env' info =>
      cases k with
      | var T =>
        cases info with
        | var n =>
          simp [EnvTyping] at ht
          have ⟨_, ht'⟩ := ht
          have ih_result := ih ht'
          simp [TypeEnv.is_monotonic] at ih_result ⊢
          intro x
          cases x with
          | there x =>
            simp [TypeEnv.lookup_tvar, TypeEnv.lookup]
            exact ih_result x
      | tvar S =>
        cases info with
        | tvar d =>
          simp [EnvTyping] at ht
          have ⟨hmono, _, ht'⟩ := ht
          have ih_result := ih ht'
          simp [TypeEnv.is_monotonic] at ih_result ⊢
          intro x
          cases x with
          | here =>
            simp [TypeEnv.lookup_tvar, TypeEnv.lookup]
            exact hmono
          | there x =>
            simp [TypeEnv.lookup_tvar, TypeEnv.lookup]
            exact ih_result x

def Denot.as_post_is_monotonic {d : Denot}
  (hmon : d.is_monotonic) :
  d.as_post.is_monotonic := by
  intro h1 h2 e hsub hde
  apply hmon hsub hde

mutual

def val_denot_is_monotonic {T : Ty s}
  (henv : TypeEnv.is_monotonic env) :
  (Ty.val_denot env T).is_monotonic :=
  match T with
  | .top => by
    intro hheap ht
    simp [Ty.val_denot] at ht ⊢
    assumption
  | .tvar X => by
    intro hheap ht
    simp [Ty.val_denot] at ht ⊢
    apply henv X hheap ht
  | .singleton x => by
    intro hheap ht
    simp [Ty.val_denot] at ht ⊢
    exact ht
  | .arrow T1 T2 => by
    have ih1 : (Ty.val_denot env T1).is_monotonic :=
      val_denot_is_monotonic (T:=T1) henv
    intro hheap ht
    rename_i h1 h2 e
    simp [Ty.val_denot] at ht ⊢
    have ⟨T0, e0, hr, hfun⟩ := ht
    use T0, e0
    constructor
    · cases e with
      | var x =>
        cases x with
        | free fx =>
          simp [resolve] at hr ⊢
          cases hres : h1 fx with
          | none => simp [hres] at hr
          | some v =>
            simp [hres] at hr
            have := hheap fx v hres
            simp [this, hr]
        | bound bx => cases bx
      | abs _ _ => simp [resolve] at hr ⊢; exact hr
      | tabs _ _ => simp [resolve] at hr ⊢
      | app _ _ | tapp _ _ | letin _ _ => simp [resolve] at hr
    · intro s' arg hs' harg
      have hs0 := Heap.subsumes_trans hs' hheap
      apply hfun s' arg hs0 harg
  | .poly T1 T2 => by
    intro hheap ht
    rename_i h1 h2 e
    simp [Ty.val_denot] at ht ⊢
    have ⟨T0, e0, hr, hfun⟩ := ht
    use T0, e0
    constructor
    · -- Show: resolve h2 e = some (.tabs T0 e0)
      -- This follows from heap subsumption, similar to the arrow case
      cases e with
      | var x =>
        cases x with
        | free fx =>
          simp [resolve] at hr ⊢
          cases hres : h1 fx with
          | none => simp [hres] at hr
          | some v =>
            simp [hres] at hr
            have := hheap fx v hres
            simp [this, hr]
        | bound bx => cases bx
      | abs _ _ => simp [resolve] at hr ⊢
      | tabs _ _ => simp [resolve] at hr ⊢; exact hr
      | app _ _ | tapp _ _ | letin _ _ => simp [resolve] at hr
    · -- Show: ∀ denot, denot.is_monotonic -> denot.Imply (Ty.val_denot env T1) -> ...
      intro denot hdenot_mono himply
      -- Need to show: Ty.exp_denot (env.extend_tvar denot) T2 h2 (e0.subst ...)
      -- We have from hfun: Ty.exp_denot (env.extend_tvar denot) T2 h1 (e0.subst ...)
      have heval1 := hfun denot hdenot_mono himply
      -- Need to lift from h1 to h2 using exp_denot_is_monotonic
      have henv' : (env.extend_tvar denot).is_monotonic := by
        intro X
        simp [TypeEnv.extend_tvar, TypeEnv.lookup_tvar]
        cases X with
        | here =>
          simp [TypeEnv.lookup]
          -- denot is monotonic by assumption
          exact hdenot_mono
        | there X' => exact henv X'
      have hmon : (Ty.exp_denot (env.extend_tvar denot) T2).is_monotonic :=
        exp_denot_is_monotonic (T:=T2) (env:=env.extend_tvar denot) henv'
      apply hmon hheap heval1

def exp_denot_is_monotonic {T : Ty s}
  (henv : TypeEnv.is_monotonic env) :
  (Ty.exp_denot env T).is_monotonic := by
  have ih : (Ty.val_denot env T).is_monotonic :=
    val_denot_is_monotonic henv (T:=T)
  intro h1 h2 e hheap ht
  simp [Ty.exp_denot] at ht ⊢
  apply eval_monotonic
  · apply Denot.as_post_is_monotonic
    exact ih
  · exact hheap
  · exact ht

end

end FsubNext
