import Semantic.Fsub.Eval
import Semantic.Fsub.TypeSystem

namespace Fsub

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

def Denot.is_transparent (d : Denot) : Prop :=
  ∀ {h : Heap} {x : Nat} {v},
    h x = some v ->
    d h v.unwrap ->
    d h (.var (.free x))

def Denot.Imply (d1 d2 : Denot) : Prop :=
  ∀ s e,
    (d1 s e) ->
    (d2 s e)

def Denot.ImplyAt (d1 : Denot) (h : Heap) (d2 : Denot) : Prop :=
  ∀ e, d1 h e -> d2 h e

def Denot.ImplyAfter (d1 : Denot) (h : Heap) (d2 : Denot) : Prop :=
  ∀ h', h'.subsumes h -> d1.ImplyAt h' d2

theorem Denot.imply_implyat {d1 d2 : Denot}
  (himp : d1.Imply d2) :
  d1.ImplyAt h d2 := by
  grind [Imply, ImplyAt]

theorem Denot.implyat_trans
  {d1 d2 : Denot}
  (himp1 : d1.ImplyAt h d2)
  (himp2 : d2.ImplyAt h d3) :
  d1.ImplyAt h d3 := by
  grind [ImplyAt]

lemma Denot.imply_after_to_entails_after {d1 d2 : Denot}
  (himp : d1.ImplyAfter h d2) :
  d1.as_post.entails_after h d2.as_post :=
  himp

lemma Denot.imply_after_subsumes {d1 d2 : Denot}
  (himp : d1.ImplyAfter h1 d2)
  (hheap : h2.subsumes h1) :
  d1.ImplyAfter h2 d2 :=
  fun H hs => himp H (Heap.subsumes_trans hs hheap)

lemma Denot.imply_after_to_imply_at {d1 d2 : Denot}
  (himp : d1.ImplyAfter h d2) :
  d1.ImplyAt h d2 := by
  grind [ImplyAfter, ImplyAt, Heap.subsumes_refl]

lemma Denot.imply_after_trans {d1 d2 d3 : Denot}
  (himp1 : d1.ImplyAfter h d2)
  (himp2 : d2.ImplyAfter h d3) :
  d1.ImplyAfter h d3 := by
  grind [ImplyAfter, ImplyAt]

lemma Denot.apply_imply_at {d1 d2 : Denot}
  (ht : d1 h e)
  (himp : d1.ImplyAt h d2) :
  d2 h e :=
  himp e ht

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
    (∀ (s' : Heap) (denot : Denot),
      (s'.subsumes s) ->
      denot.is_monotonic ->
      denot.is_transparent ->
      denot.ImplyAfter s' (Ty.val_denot env T1) ->
      Ty.exp_denot (env.extend_tvar denot) T2 s' (e0.subst (Subst.openTVar .top)))

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
  d.is_transparent ∧
  d.ImplyAfter store (Ty.val_denot env S) ∧
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
    Subst.from_TypeEnv (env.extend_var x) :=
  Subst.funext (fun x => by cases x <;> rfl) (fun X => by cases X; rfl)

theorem Exp.from_TypeEnv_weaken_open {e : Exp (s,x)} :
  (e.subst (Subst.from_TypeEnv env).lift).subst (Subst.openVar (.free x)) =
    e.subst (Subst.from_TypeEnv (env.extend_var x)) :=
  (Exp.subst_comp (e:=e)).trans (congrArg _ Subst.from_TypeEnv_weaken_open)

theorem Subst.from_TypeEnv_weaken_open_tvar :
  (Subst.from_TypeEnv env).lift.comp (Subst.openTVar .top) =
    Subst.from_TypeEnv (env.extend_tvar d) :=
  Subst.funext (fun x => by cases x; rfl) (fun X => by cases X <;> rfl)

theorem Exp.from_TypeEnv_weaken_open_tvar {e : Exp (s,X)} :
  (e.subst (Subst.from_TypeEnv env).lift).subst (Subst.openTVar .top) =
    e.subst (Subst.from_TypeEnv (env.extend_tvar d)) :=
  (Exp.subst_comp (e:=e)).trans (congrArg _ Subst.from_TypeEnv_weaken_open_tvar)

def Denot.Equiv (d1 d2 : Denot) : Prop :=
  ∀ s e,
    (d1 s e) ↔ (d2 s e)

instance Denot.instHasEquiv : HasEquiv Denot where
  Equiv := Denot.Equiv

def Denot.equiv_refl (d : Denot) : d ≈ d := fun _ _ => Iff.rfl

def Denot.equiv_symm (d1 d2 : Denot) : d1 ≈ d2 -> d2 ≈ d1 :=
  fun h s e => (h s e).symm

def Denot.equiv_trans (d1 d2 d3 : Denot) : d1 ≈ d2 -> d2 ≈ d3 -> d1 ≈ d3 :=
  fun h12 h23 s e =>
    ⟨fun h => (h23 s e).mp ((h12 s e).mp h), fun h => (h12 s e).mpr ((h23 s e).mpr h)⟩

theorem Denot.eq_to_equiv (d1 d2 : Denot) : d1 = d2 -> d1 ≈ d2 := by
  intro h s e; rw [h]

theorem Denot.equiv_ltr {d1 d2 : Denot}
  (heqv : d1 ≈ d2)
  (h1 : d1 s e) :
  d2 s e :=
  (heqv s e).mp h1

theorem Denot.equiv_rtl {d1 d2 : Denot}
  (heqv : d1 ≈ d2)
  (h2 : d2 s e) :
  d1 s e :=
  (heqv s e).mpr h2

theorem Denot.equiv_to_imply {d1 d2 : Denot}
  (heqv : d1 ≈ d2) :
  (d1.Imply d2) ∧ (d2.Imply d1) :=
  ⟨fun s e h => (heqv s e).mp h, fun s e h => (heqv s e).mpr h⟩

theorem Denot.equiv_to_imply_l {d1 d2 : Denot}
  (heqv : d1 ≈ d2) :
  d1.Imply d2 := (Denot.equiv_to_imply heqv).1

theorem Denot.equiv_to_imply_r {d1 d2 : Denot}
  (heqv : d1 ≈ d2) :
  d2.Imply d1 := (Denot.equiv_to_imply heqv).2

theorem Denot.imply_to_entails (d1 d2 : Denot)
  (himp : d1.Imply d2) :
  d1.as_post.entails d2.as_post :=
  himp

theorem Denot.imply_refl (d : Denot) : d.Imply d := by
  grind [Imply]

theorem Denot.imply_trans {d1 d2 d3 : Denot}
  (h1 : d1.Imply d2)
  (h2 : d2.Imply d3) :
  d1.Imply d3 := by
  grind [Imply]

theorem resolve_var_heap_some
  (hheap : heap x = some v) :
  resolve heap (.var (.free x)) = some v.unwrap := by
  simp [resolve, hheap]

theorem resolve_val
  (hval : v.IsVal) :
  resolve heap v = some v := by
  cases hval <;> rfl

theorem resolve_var_heap_trans
  (hheap : heap x = some v) :
  resolve heap (.var (.free x)) = resolve heap (v.unwrap) := by
  simp [resolve_var_heap_some hheap, resolve_val v.isVal]

/-- If `resolve h1 e = some r` and `h2` subsumes `h1`, then `resolve h2 e = some r`. -/
theorem resolve_subsumes
  {h1 h2 : Heap} (hh : h2.subsumes h1)
  {e : Exp {}} {r : Exp {}} (hr : resolve h1 e = some r) :
  resolve h2 e = some r := by
  cases e with
  | var x =>
    cases x with
    | free fx =>
      simp only [resolve] at hr ⊢
      cases hres : h1 fx with
      | none => simp [hres] at hr
      | some v => simp [hres] at hr; simp [hh fx v hres, hr]
    | bound bx => cases bx
  | abs _ _ | tabs _ _ | app _ _ | tapp _ _ | letin _ _ =>
    simpa only [resolve] using hr

def TypeEnv.is_monotonic (env : TypeEnv s) : Prop :=
  ∀ (X : BVar s .tvar),
    (env.lookup_tvar X).is_monotonic

def TypeEnv.is_transparent (env : TypeEnv s) : Prop :=
  ∀ (X : BVar s .tvar),
    (env.lookup_tvar X).is_transparent

theorem typed_env_is_monotonic
  (ht : EnvTyping Γ env store) :
  env.is_monotonic := by
  induction Γ with
  | empty => cases env; simp only [TypeEnv.is_monotonic]; intro x; cases x
  | push Γ k ih =>
    cases env with
    | extend env' info =>
      cases k with
      | var T => cases info with | var n =>
        simp only [EnvTyping] at ht; have ih_result := ih ht.2
        simp only [TypeEnv.is_monotonic] at ih_result ⊢
        intro x; cases x with
        | there x => simp only [TypeEnv.lookup_tvar, TypeEnv.lookup]; exact ih_result x
      | tvar S => cases info with | tvar d =>
        simp only [EnvTyping] at ht; have ih_result := ih ht.2.2.2
        simp only [TypeEnv.is_monotonic] at ih_result ⊢
        intro x; cases x with
        | here => simp only [TypeEnv.lookup_tvar, TypeEnv.lookup]; exact ht.1
        | there x => simp only [TypeEnv.lookup_tvar, TypeEnv.lookup]; exact ih_result x

def Denot.as_post_is_monotonic {d : Denot}
  (hmon : d.is_monotonic) :
  d.as_post.is_monotonic :=
  hmon

theorem typed_env_is_transparent
  (ht : EnvTyping Γ env store) :
  env.is_transparent := by
  induction Γ with
  | empty => cases env; simp only [TypeEnv.is_transparent]; intro x; cases x
  | push Γ k ih =>
    cases env with
    | extend env' info =>
      cases k with
      | var T => cases info with | var n =>
        simp only [EnvTyping] at ht; have ih_result := ih ht.2
        simp only [TypeEnv.is_transparent] at ih_result ⊢
        intro x; cases x with
        | there x => simp only [TypeEnv.lookup_tvar, TypeEnv.lookup]; exact ih_result x
      | tvar S => cases info with | tvar d =>
        simp only [EnvTyping] at ht; have ih_result := ih ht.2.2.2
        simp only [TypeEnv.is_transparent] at ih_result ⊢
        intro x; cases x with
        | here => simp only [TypeEnv.lookup_tvar, TypeEnv.lookup]; exact ht.2.1
        | there x => simp only [TypeEnv.lookup_tvar, TypeEnv.lookup]; exact ih_result x

theorem val_denot_is_transparent
  (henv : TypeEnv.is_transparent env) :
  (Ty.val_denot env T).is_transparent :=
  match T with
  | .top => by intro _ _; simp [Ty.val_denot]
  | .tvar X => by simp only [Ty.val_denot]; exact henv X
  | .singleton z => by
    intro hx hval; simp only [Ty.val_denot] at hval
    cases ‹Val _› with | mk v hv => cases hval; cases hv
  | .arrow T1 T2 | .poly T1 T2 => by
    intro hx ht; simp only [Ty.val_denot] at ht ⊢
    rw [resolve_var_heap_trans hx]; exact ht

mutual

def val_denot_is_monotonic {T : Ty s}
  (henv : TypeEnv.is_monotonic env) :
  (Ty.val_denot env T).is_monotonic :=
  match T with
  | .top => by intro _ _; simp [Ty.val_denot]
  | .tvar X => by intro hheap ht; simp only [Ty.val_denot] at ht ⊢; exact henv X hheap ht
  | .singleton x => by intro _ ht; simp only [Ty.val_denot] at ht ⊢; exact ht
  | .arrow T1 T2 => by
    intro hheap ht; simp only [Ty.val_denot] at ht ⊢
    obtain ⟨T0, e0, hr, hfun⟩ := ht
    exact ⟨T0, e0, resolve_subsumes hheap hr,
      fun s' arg hs' harg => hfun s' arg (Heap.subsumes_trans hs' hheap) harg⟩
  | .poly T1 T2 => by
    intro hheap ht; simp only [Ty.val_denot] at ht ⊢
    obtain ⟨T0, e0, hr, hfun⟩ := ht
    exact ⟨T0, e0, resolve_subsumes hheap hr,
      fun H denot Hsub hm ht himply =>
        hfun H denot (Heap.subsumes_trans Hsub hheap) hm ht himply⟩

def exp_denot_is_monotonic {T : Ty s}
  (henv : TypeEnv.is_monotonic env) :
  (Ty.exp_denot env T).is_monotonic := by
  have ih : (Ty.val_denot env T).is_monotonic := val_denot_is_monotonic henv (T:=T)
  intro h1 h2 e hheap ht; simp only [Ty.exp_denot] at ht ⊢
  apply eval_monotonic
  · apply Denot.as_post_is_monotonic
    exact ih
  · exact hheap
  · exact ht

end

theorem env_typing_monotonic
  (ht : EnvTyping Γ env store1)
  (hstore : store2.subsumes store1) :
  EnvTyping Γ env store2 := by
  induction Γ with
  | empty => cases env with | empty => constructor
  | push Γ k ih =>
    cases env with
    | extend env' info =>
      cases k with
      | var T => cases info with | var n =>
        simp only [EnvTyping] at ht ⊢; obtain ⟨hval, ht'⟩ := ht
        exact ⟨val_denot_is_monotonic (typed_env_is_monotonic ht') hstore hval, ih ht'⟩
      | tvar S => cases info with | tvar d =>
        simp only [EnvTyping] at ht ⊢; obtain ⟨hmono, htrans, himply, ht'⟩ := ht
        exact ⟨hmono, htrans, Denot.imply_after_subsumes himply hstore, ih ht'⟩

def SemSubtyp (Γ : Ctx s) (T1 T2 : Ty s) : Prop :=
  ∀ env H,
    EnvTyping Γ env H ->
    (Ty.val_denot env T1).ImplyAfter H (Ty.val_denot env T2)

theorem denot_implyat_lift
  (himp : (Ty.val_denot env T1).ImplyAfter H (Ty.val_denot env T2)) :
  (Ty.exp_denot env T1).ImplyAfter H (Ty.exp_denot env T2) := by
  intro H' hheap v h1; simp only [Ty.exp_denot] at h1 ⊢
  exact eval_post_monotonic_general
    (Hpost.entails_after_subsumes (Denot.imply_after_to_entails_after himp) hheap) h1

end Fsub
