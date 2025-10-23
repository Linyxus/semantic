import Semantic.CC.Eval
import Semantic.CC.TypeSystem

namespace CC

def resolve : Heap -> Exp {} -> Option (Exp {})
| s, .var (.free x) =>
  match s x with
  | some (.val v) => some v.unwrap
  | _ => none
| s, .var (.bound x) => by cases x
| _, other => some other

/-- Denotation of types. -/
def Denot := Heap -> Exp {} -> Prop

/-- Pre-denotation -/
def PreDenot := CapabilitySet -> Denot

def Denot.as_post (d : Denot) : Hpost :=
  fun e h => d h e

def Denot.is_monotonic (d : Denot) : Prop :=
  ∀ {h1 h2 : Heap} {e},
    h2.subsumes h1 ->
    d h1 e ->
    d h2 e

def Denot.is_transparent (d : Denot) : Prop :=
  ∀ {h : Heap} {x : Nat} {v},
    h x = some (.val v) ->
    d h v.unwrap ->
    d h (.var (.free x))

def Denot.is_proper (d : Denot) : Prop :=
  d.is_monotonic ∧ d.is_transparent

def PreDenot.is_proper (pd : PreDenot) : Prop :=
  ∀ C, (pd C).is_proper

def Denot.Imply (d1 d2 : Denot) : Prop :=
  ∀ s e,
    (d1 s e) ->
    (d2 s e)

def PreDenot.Imply (pd1 pd2 : PreDenot) : Prop :=
  ∀ C,
    (pd1 C).Imply (pd2 C)

def Denot.ImplyAt (d1 : Denot) (h : Heap) (d2 : Denot) : Prop :=
  ∀ e, d1 h e -> d2 h e

def PreDenot.ImplyAt (pd1 pd2 : PreDenot) (h : Heap) : Prop :=
  ∀ C, (pd1 C).ImplyAt h (pd2 C)

def Denot.ImplyAfter (d1 : Denot) (h : Heap) (d2 : Denot) : Prop :=
  ∀ h', h'.subsumes h -> d1.ImplyAt h' d2

def PreDenot.ImplyAfter (pd1 : PreDenot) (h : Heap) (pd2 : PreDenot) : Prop :=
  ∀ C, (pd1 C).ImplyAfter h (pd2 C)

theorem Denot.imply_implyat {d1 d2 : Denot}
  (himp : d1.Imply d2) :
  d1.ImplyAt h d2 := by
  intro e h1
  apply himp h e h1

theorem Denot.implyat_trans
  {d1 d2 : Denot}
  (himp1 : d1.ImplyAt h d2)
  (himp2 : d2.ImplyAt h d3) :
  d1.ImplyAt h d3 := by
  intro e h1
  apply himp2 e (himp1 e h1)

lemma Denot.imply_after_to_entails_after {d1 d2 : Denot}
  (himp : d1.ImplyAfter h d2) :
  d1.as_post.entails_after h d2.as_post := by
  intro h' hsub e h1
  apply himp h' hsub e h1

lemma Denot.imply_after_subsumes {d1 d2 : Denot}
  (himp : d1.ImplyAfter h1 d2)
  (hheap : h2.subsumes h1) :
  d1.ImplyAfter h2 d2 := by
  intro H hs
  apply himp H
  apply Heap.subsumes_trans hs hheap

lemma Denot.imply_after_to_imply_at {d1 d2 : Denot}
  (himp : d1.ImplyAfter h d2) :
  d1.ImplyAt h d2 := by
  intro e h1
  apply himp h (Heap.subsumes_refl h) e h1

lemma Denot.imply_after_trans {d1 d2 d3 : Denot}
  (himp1 : d1.ImplyAfter h d2)
  (himp2 : d2.ImplyAfter h d3) :
  d1.ImplyAfter h d3 := by
  intro h' hsub e h1
  apply himp2 h' hsub
  apply himp1 h' hsub e h1

lemma Denot.apply_imply_at {d1 d2 : Denot}
  (ht : d1 h e)
  (himp : d1.ImplyAt h d2) :
  d2 h e := by
  apply himp e ht

inductive TypeInfo : Kind -> Type where
| var : Nat -> CapabilitySet -> TypeInfo .var
| tvar : PreDenot -> TypeInfo .tvar
| cvar : CapabilitySet -> TypeInfo .cvar

inductive TypeEnv : Sig -> Type where
| empty : TypeEnv {}
| extend :
  TypeEnv s ->
  TypeInfo k ->
  TypeEnv (s,,k)

def TypeEnv.extend_var (Γ : TypeEnv s) (x : Nat) (access : CapabilitySet) : TypeEnv (s,x) :=
  Γ.extend (.var x access)

def TypeEnv.extend_tvar (Γ : TypeEnv s) (T : PreDenot) : TypeEnv (s,X) :=
  Γ.extend (.tvar T)

def TypeEnv.extend_cvar (Γ : TypeEnv s) (underlying : CapabilitySet) : TypeEnv (s,C) :=
  Γ.extend (.cvar underlying)

def TypeEnv.lookup : (Γ : TypeEnv s) -> (x : BVar s k) -> TypeInfo k
| .extend _ info, .here => info
| .extend Γ _,    .there x => Γ.lookup x

def TypeEnv.lookup_var (Γ : TypeEnv s) (x : BVar s .var) : Nat × CapabilitySet :=
  match Γ.lookup x with
  | .var y a => ⟨y, a⟩

def TypeEnv.lookup_tvar (Γ : TypeEnv s) (x : BVar s .tvar) : PreDenot :=
  match Γ.lookup x with
  | .tvar T => T

def TypeEnv.lookup_cvar (Γ : TypeEnv s) (x : BVar s .cvar) : CapabilitySet :=
  match Γ.lookup x with
  | .cvar c => c

def CaptureSet.denot : TypeEnv s -> CaptureSet s -> CapabilitySet
| _, .empty => CapabilitySet.empty
| env, .union cs1 cs2 =>
  (cs1.denot env) ∪ (cs2.denot env)
| env, .var (.bound x) => (env.lookup_var x).2
| _, .var (.free x) => {x}
| env, .cvar c => env.lookup_cvar c

def CaptureBound.denot : TypeEnv s -> CaptureBound s -> CapabilitySet
| _, .unbound => CapabilitySet.any
| env, .bound cs => cs.denot env

mutual

def Ty.shape_val_denot : TypeEnv s -> Ty .shape s -> PreDenot
| _, .top => fun _ _ _ => True
| env, .tvar X => env.lookup_tvar X
| _, .unit => fun _ H e => resolve H e = some .unit
| _, .cap => fun A H e =>
  ∃ label : Nat,
    e = .var (.free label) ∧
    H label = some .capability ∧
    label ∈ A
| env, .arrow T1 T2 => fun A H e =>
  ∃ T0 t0,
    resolve H e = some (.abs T0 t0) ∧
    (∀ (arg : Nat) (H' : Heap),
      H'.subsumes H ->
      Ty.capt_val_denot env T1 H' (.var (.free arg)) ->
      Ty.exi_exp_denot
        (env.extend_var arg (T1.captureSet.denot env))
        T2 A H' (t0.subst (Subst.openVar (.free arg))))
| env, .poly T1 T2 => fun A H e =>
  ∃ S0 t0,
    resolve H e = some (.tabs S0 t0) ∧
    (∀ (H' : Heap) (denot : PreDenot),
      H'.subsumes H ->
      denot.is_proper ->
      denot.ImplyAfter H' (Ty.shape_val_denot env T1) ->
      Ty.exi_exp_denot
        (env.extend_tvar denot)
        T2 A H' (t0.subst (Subst.openTVar .top)))
| env, .cpoly B T => fun A H e =>
  ∃ B0 t0,
    resolve H e = some (.cabs B0 t0) ∧
    (∀ (H' : Heap) (A0 : CapabilitySet),
      H'.subsumes H ->
      (A0 ⊆ B.denot env) ->
      Ty.exi_exp_denot
        (env.extend_cvar A0)
        T A H' (t0.subst (Subst.openCVar .empty)))

def Ty.capt_val_denot : TypeEnv s -> Ty .capt s -> Denot
| ρ, .capt C S => Ty.shape_val_denot ρ S (C.denot ρ)

def Ty.exi_val_denot : TypeEnv s -> Ty .exi s -> Denot
| ρ, .typ T => Ty.capt_val_denot ρ T
| ρ, .exi T => fun H e =>
  ∃ (A : CapabilitySet),
    Ty.capt_val_denot (ρ.extend_cvar A) T H e

def Ty.capt_exp_denot : TypeEnv s -> Ty .capt s -> PreDenot
| ρ, T => fun A H e =>
  Eval A H e (Ty.capt_val_denot ρ T).as_post

def Ty.exi_exp_denot : TypeEnv s -> Ty .exi s -> PreDenot
| ρ, T => fun A H e =>
  Eval A H e (Ty.exi_val_denot ρ T).as_post

end

def EnvTyping : Ctx s -> TypeEnv s -> Heap -> Prop
| .empty, .empty, _ => True
| .push Γ (.var T), .extend env (.var n access), H =>
  Ty.capt_val_denot env T H (.var (.free n)) ∧
  access = T.captureSet.denot env ∧
  EnvTyping Γ env H
| .push Γ (.tvar S), .extend env (.tvar denot), H =>
  denot.is_proper ∧
  denot.ImplyAfter H (Ty.shape_val_denot env S) ∧
  EnvTyping Γ env H
| .push Γ (.cvar B), .extend env (.cvar access), H =>
  (access ⊆ B.denot env) ∧
  EnvTyping Γ env H

def Subst.from_TypeEnv (env : TypeEnv s) : Subst s {} where
  var := fun x => .free (env.lookup_var x).1
  tvar := fun _ => .top
  cvar := fun _ => {}

def SemanticTyping (C : CaptureSet s) (Γ : Ctx s) (e : Exp s) (T : Ty .exi s) : Prop :=
  ∀ ρ H,
    EnvTyping Γ ρ H ->
    Ty.exi_exp_denot ρ T (C.denot ρ) H (e.subst (Subst.from_TypeEnv ρ))

notation:65 C "#" Γ " ⊨ " e " : " T => SemanticTyping C Γ e T

-- theorem Subst.from_TypeEnv_weaken_open :
--   (Subst.from_TypeEnv env).lift.comp (Subst.openVar (.free x)) =
--     Subst.from_TypeEnv (env.extend_var x) := by
--   apply Subst.funext
--   · intro x
--     cases x <;> rfl
--   · intro X
--     cases X; rfl

-- theorem Exp.from_TypeEnv_weaken_open {e : Exp (s,x)} :
--   (e.subst (Subst.from_TypeEnv env).lift).subst (Subst.openVar (.free x)) =
--     e.subst (Subst.from_TypeEnv (env.extend_var x)) := by
--   simp [Exp.subst_comp]
--   simp [Subst.from_TypeEnv_weaken_open]

-- theorem Subst.from_TypeEnv_weaken_open_tvar :
--   (Subst.from_TypeEnv env).lift.comp (Subst.openTVar .top) =
--     Subst.from_TypeEnv (env.extend_tvar d) := by
--   apply Subst.funext
--   · intro x
--     cases x; rfl
--   · intro X
--     cases X
--     case here => rfl
--     case there x => rfl

-- theorem Exp.from_TypeEnv_weaken_open_tvar {e : Exp (s,X)} :
--   (e.subst (Subst.from_TypeEnv env).lift).subst (Subst.openTVar .top) =
--     e.subst (Subst.from_TypeEnv (env.extend_tvar d)) := by
--   simp [Exp.subst_comp]
--   rw [Subst.from_TypeEnv_weaken_open_tvar]

-- def Denot.Equiv (d1 d2 : Denot) : Prop :=
--   ∀ s e,
--     (d1 s e) ↔ (d2 s e)

-- instance Denot.instHasEquiv : HasEquiv Denot where
--   Equiv := Denot.Equiv

-- def Denot.equiv_refl (d : Denot) : d ≈ d := by
--   intro s e
--   constructor
--   · intro h
--     exact h
--   · intro h
--     exact h

-- def Denot.equiv_symm (d1 d2 : Denot) : d1 ≈ d2 -> d2 ≈ d1 := by
--   intro h
--   intro s e
--   constructor
--   · intro h0
--     apply (h s e).mpr h0
--   · intro h0
--     apply (h s e).mp h0

-- def Denot.equiv_trans (d1 d2 d3 : Denot) : d1 ≈ d2 -> d2 ≈ d3 -> d1 ≈ d3 := by
--   intro h12
--   intro h23
--   intro s e
--   have h1 := h12 s e
--   have h2 := h23 s e
--   grind

-- theorem Denot.eq_to_equiv (d1 d2 : Denot) : d1 = d2 -> d1 ≈ d2 := by
--   intro h
--   intro s e
--   grind

-- theorem Denot.equiv_ltr {d1 d2 : Denot}
--   (heqv : d1 ≈ d2)
--   (h1 : d1 s e) :
--   d2 s e := by
--   apply (heqv s e).mp h1

-- theorem Denot.equiv_rtl {d1 d2 : Denot}
--   (heqv : d1 ≈ d2)
--   (h2 : d2 s e) :
--   d1 s e := by
--   apply (heqv s e).mpr h2

-- theorem Denot.equiv_to_imply {d1 d2 : Denot}
--   (heqv : d1 ≈ d2) :
--   (d1.Imply d2) ∧ (d2.Imply d1) := by
--   constructor
--   · intro s e h
--     apply (heqv s e).mp h
--   · intro s e h
--     apply (heqv s e).mpr h

-- theorem Denot.equiv_to_imply_l {d1 d2 : Denot}
--   (heqv : d1 ≈ d2) :
--   d1.Imply d2 := (Denot.equiv_to_imply heqv).1

-- theorem Denot.equiv_to_imply_r {d1 d2 : Denot}
--   (heqv : d1 ≈ d2) :
--   d2.Imply d1 := (Denot.equiv_to_imply heqv).2

-- theorem Denot.imply_to_entails (d1 d2 : Denot)
--   (himp : d1.Imply d2) :
--   d1.as_post.entails d2.as_post := by
--   intro h e h1
--   apply himp h e h1

-- theorem Denot.imply_refl (d : Denot) : d.Imply d := by
--   intro s e h
--   exact h

-- theorem Denot.imply_trans {d1 d2 d3 : Denot}
--   (h1 : d1.Imply d2)
--   (h2 : d2.Imply d3) :
--   d1.Imply d3 := by
--   intro s e h
--   aesop

-- def Denot.ans : Denot :=
--   fun _ e => Exp.IsAns e

-- def TypeEnv.inert (env : TypeEnv s) : Prop :=
--   ∀ (x : BVar s .tvar),
--     (env.lookup_tvar x).Imply Denot.ans

-- theorem resolve_var_heap_some
--   (hheap : heap x = some v) :
--   resolve heap (.var (.free x)) = some v.unwrap := by
--   simp [resolve, hheap]

-- theorem resolve_val
--   (hval : v.IsVal) :
--   resolve heap v = some v := by
--   cases hval <;> rfl

-- theorem resolve_var_heap_trans
--   (hheap : heap x = some v) :
--   resolve heap (.var (.free x)) = resolve heap (v.unwrap) := by
--   rw [resolve_var_heap_some hheap]
--   rw [resolve_val v.isVal]

-- theorem resolve_var_or_val
--   (hv : resolve store e = some v) :
--   (∃ x, e = .var x) ∨ e = v := by
--   cases e
--   all_goals try (solve | aesop | simp [resolve] at hv; aesop)

-- theorem resolve_ans_to_val
--   (hv : resolve store e = some v)
--   (hans : v.IsAns) :
--   e.IsAns := by
--   cases (resolve_var_or_val hv)
--   case inl h =>
--     have ⟨x, h⟩ := h
--     rw [h]
--     apply Exp.IsAns.is_var
--   case inr h => aesop

-- def TypeEnv.is_monotonic (env : TypeEnv s) : Prop :=
--   ∀ (X : BVar s .tvar),
--     (env.lookup_tvar X).is_monotonic

-- def TypeEnv.is_transparent (env : TypeEnv s) : Prop :=
--   ∀ (X : BVar s .tvar),
--     (env.lookup_tvar X).is_transparent

-- theorem typed_env_is_monotonic
--   (ht : EnvTyping Γ env store) :
--   env.is_monotonic := by
--   induction Γ with
--   | empty =>
--     cases env with
--     | empty =>
--       simp [TypeEnv.is_monotonic]
--       intro x
--       cases x
--   | push Γ k ih =>
--     cases env with
--     | extend env' info =>
--       cases k with
--       | var T =>
--         cases info with
--         | var n =>
--           simp [EnvTyping] at ht
--           have ⟨_, ht'⟩ := ht
--           have ih_result := ih ht'
--           simp [TypeEnv.is_monotonic] at ih_result ⊢
--           intro x
--           cases x with
--           | there x =>
--             simp [TypeEnv.lookup_tvar, TypeEnv.lookup]
--             exact ih_result x
--       | tvar S =>
--         cases info with
--         | tvar d =>
--           simp [EnvTyping] at ht
--           have ⟨hmono, _, _, ht'⟩ := ht
--           have ih_result := ih ht'
--           simp [TypeEnv.is_monotonic] at ih_result ⊢
--           intro x
--           cases x with
--           | here =>
--             simp [TypeEnv.lookup_tvar, TypeEnv.lookup]
--             exact hmono
--           | there x =>
--             simp [TypeEnv.lookup_tvar, TypeEnv.lookup]
--             exact ih_result x

-- def Denot.as_post_is_monotonic {d : Denot}
--   (hmon : d.is_monotonic) :
--   d.as_post.is_monotonic := by
--   intro h1 h2 e hsub hde
--   apply hmon hsub hde

-- theorem typed_env_is_transparent
--   (ht : EnvTyping Γ env store) :
--   env.is_transparent := by
--   induction Γ with
--   | empty =>
--     cases env with
--     | empty =>
--       simp [TypeEnv.is_transparent]
--       intro x
--       cases x
--   | push Γ k ih =>
--     cases env with
--     | extend env' info =>
--       cases k with
--       | var T =>
--         cases info with
--         | var n =>
--           simp [EnvTyping] at ht
--           have ⟨_, ht'⟩ := ht
--           have ih_result := ih ht'
--           simp [TypeEnv.is_transparent] at ih_result ⊢
--           intro x
--           cases x with
--           | there x =>
--             simp [TypeEnv.lookup_tvar, TypeEnv.lookup]
--             exact ih_result x
--       | tvar S =>
--         cases info with
--         | tvar d =>
--           simp [EnvTyping] at ht
--           have ⟨_, htrans, _, ht'⟩ := ht
--           have ih_result := ih ht'
--           simp [TypeEnv.is_transparent] at ih_result ⊢
--           intro x
--           cases x with
--           | here =>
--             simp [TypeEnv.lookup_tvar, TypeEnv.lookup]
--             exact htrans
--           | there x =>
--             simp [TypeEnv.lookup_tvar, TypeEnv.lookup]
--             exact ih_result x

-- theorem val_denot_is_transparent
--   (henv : TypeEnv.is_transparent env) :
--   (Ty.val_denot env T).is_transparent :=
--   match T with
--   | .top => by
--     rename_i h x v; intro hlk hv
--     simp [Ty.val_denot]
--   | .tvar X => by
--     simp [Ty.val_denot]
--     exact henv X
--   | .arrow T1 T2 => by
--     intro hx ht
--     simp [Ty.val_denot] at ht ⊢
--     have heq := resolve_var_heap_trans hx
--     rw [heq]
--     exact ht
--   | .poly T1 T2 => by
--     intro hx ht
--     simp [Ty.val_denot] at ht ⊢
--     have heq := resolve_var_heap_trans hx
--     rw [heq]
--     exact ht

-- mutual

-- def val_denot_is_monotonic {T : Ty .shape s}
--   (henv : TypeEnv.is_monotonic env) :
--   (Ty.val_denot env T).is_monotonic :=
--   match T with
--   | .top => by
--     intro hheap ht
--     simp [Ty.val_denot] at ht ⊢
--   | .tvar X => by
--     intro hheap ht
--     simp [Ty.val_denot] at ht ⊢
--     apply henv X hheap ht
--   | .arrow T1 T2 => by
--     have ih1 : (Ty.val_denot env T1).is_monotonic :=
--       val_denot_is_monotonic (T:=T1) henv
--     intro hheap ht
--     rename_i h1 h2 e
--     simp [Ty.val_denot] at ht ⊢
--     have ⟨T0, e0, hr, hfun⟩ := ht
--     use T0, e0
--     constructor
--     · cases e with
--       | var x =>
--         cases x with
--         | free fx =>
--           simp [resolve] at hr ⊢
--           cases hres : h1 fx with
--           | none => simp [hres] at hr
--           | some v =>
--             simp [hres] at hr
--             have := hheap fx v hres
--             simp [this, hr]
--         | bound bx => cases bx
--       | abs _ _ => simp [resolve] at hr ⊢; exact hr
--       | tabs _ _ => simp [resolve] at hr ⊢
--       | app _ _ | tapp _ _ | letin _ _ => simp [resolve] at hr
--     · intro s' arg hs' harg
--       have hs0 := Heap.subsumes_trans hs' hheap
--       apply hfun s' arg hs0 harg
--   | .poly T1 T2 => by
--     intro hheap ht
--     rename_i h1 h2 e
--     simp [Ty.val_denot] at ht ⊢
--     have ⟨T0, e0, hr, hfun⟩ := ht
--     use T0, e0
--     constructor
--     · -- Show: resolve h2 e = some (.tabs T0 e0)
--       -- This follows from heap subsumption, similar to the arrow case
--       cases e with
--       | var x =>
--         cases x with
--         | free fx =>
--           simp [resolve] at hr ⊢
--           cases hres : h1 fx with
--           | none => simp [hres] at hr
--           | some v =>
--             simp [hres] at hr
--             have := hheap fx v hres
--             simp [this, hr]
--         | bound bx => cases bx
--       | abs _ _ => simp [resolve] at hr ⊢
--       | tabs _ _ => simp [resolve] at hr ⊢; exact hr
--       | app _ _ | tapp _ _ | letin _ _ => simp [resolve] at hr
--     · -- Show: ∀ denot, monotonic -> transparent -> imply -> ...
--       intro H denot Hsub hdenot_mono hdenot_trans himply
--       -- Need to show: Ty.exp_denot (env.extend_tvar denot) T2 h2 (e0.subst ...)
--       -- We have from hfun: Ty.exp_denot (env.extend_tvar denot) T2 h1 (e0.subst ...)
--       have heval1 :=
--         hfun H denot (Heap.subsumes_trans Hsub hheap) hdenot_mono hdenot_trans himply
--       -- Need to lift from h1 to h2 using exp_denot_is_monotonic
--       have henv' : (env.extend_tvar denot).is_monotonic := by
--         intro X
--         simp [TypeEnv.extend_tvar, TypeEnv.lookup_tvar]
--         cases X with
--         | here =>
--           simp [TypeEnv.lookup]
--           -- denot is monotonic by assumption
--           exact hdenot_mono
--         | there X' => exact henv X'
--       have hmon : (Ty.exp_denot (env.extend_tvar denot) T2).is_monotonic :=
--         exp_denot_is_monotonic (T:=T2) (env:=env.extend_tvar denot) henv'
--       exact heval1

-- def exp_denot_is_monotonic {T : Ty .shape s}
--   (henv : TypeEnv.is_monotonic env) :
--   (Ty.exp_denot env T).is_monotonic := by
--   have ih : (Ty.val_denot env T).is_monotonic :=
--     val_denot_is_monotonic henv (T:=T)
--   intro h1 h2 e hheap ht
--   simp [Ty.exp_denot] at ht ⊢
--   apply eval_monotonic
--   · apply Denot.as_post_is_monotonic
--     exact ih
--   · exact hheap
--   · exact ht

-- end

-- theorem env_typing_monotonic
--   (ht : EnvTyping Γ env store1)
--   (hstore : store2.subsumes store1) :
--   EnvTyping Γ env store2 := by
--   induction Γ with
--   | empty =>
--     cases env with
--     | empty => constructor
--   | push Γ k ih =>
--     cases env with
--     | extend env' info =>
--       cases k with
--       | var T =>
--         cases info with
--         | var n =>
--           simp [EnvTyping] at ht ⊢
--           have ⟨hval, ht'⟩ := ht
--           constructor
--           · -- Show: Ty.val_denot env' T store2 (.var (.free n))
--             -- We have: hval : Ty.val_denot env' T store1 (.var (.free n))
--             -- Need to use monotonicity of val_denot
--             have henv := typed_env_is_monotonic ht'
--             exact val_denot_is_monotonic henv hstore hval
--           · -- Show: EnvTyping Γ env' store2
--             exact ih ht'
--       | tvar S =>
--         cases info with
--         | tvar d =>
--           simp [EnvTyping] at ht ⊢
--           have ⟨hmono, htrans, himply, ht'⟩ := ht
--           constructor
--           · exact hmono
--           · constructor
--             · exact htrans
--             · constructor
--               · apply Denot.imply_after_subsumes himply hstore
--               · exact ih ht'


-- def SemSubtyp (Γ : Ctx s) (T1 T2 : Ty .shape s) : Prop :=
--   ∀ env H,
--     EnvTyping Γ env H ->
--     (Ty.val_denot env T1).ImplyAfter H (Ty.val_denot env T2)

-- theorem denot_implyat_lift
--   (himp : (Ty.val_denot env T1).ImplyAfter H (Ty.val_denot env T2)) :
--   (Ty.exp_denot env T1).ImplyAfter H (Ty.exp_denot env T2) := by
--   intro H' hheap v h1
--   simp [Ty.exp_denot] at h1 ⊢
--   apply eval_post_monotonic_general _ h1
--   apply Hpost.entails_after_subsumes <;> try exact hheap
--   apply Denot.imply_after_to_entails_after himp

end CC
