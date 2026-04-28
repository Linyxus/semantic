import Semantic.Stlc.TypeSystem
import Semantic.Stlc.BigStep.Denotation
import Mathlib.Tactic

/-!
Soundness proof for STLC.

This module proves that syntactic typing implies semantic typing.
-/

namespace Stlc
namespace BigStep

/-!
Numeric values evaluate to themselves.
-/
theorem eval_num_val {v : Exp 0}
  (hv : v.IsNumVal) :
  Eval v v := by
  induction hv <;> grind [Eval]

theorem eval_num_val_eq
  (hv : v.IsNumVal)
  (hev : Eval v v') :
  v = v' := by
  induction hv generalizing v'
  case nzero => cases hev; rfl
  case nsucc _ ih => cases hev; aesop

theorem eval_bool_val_eq
  (hv : v.IsBoolVal)
  (hev : Eval v v') :
  v = v' := by
  cases hv <;> (cases hev; rfl)

/-!
Values evaluate to themselves.
-/
theorem eval_val {v : Exp 0}
  (hv : v.IsVal) :
  Eval v v := by
  cases hv <;> try grind [Eval]
  case bool hv => cases hv <;> grind [Eval]
  case num hv => exact eval_num_val hv

theorem eval_val_eq
  (hv : v.IsVal)
  (hev : Eval v v') :
  v = v' := by
  cases hv <;> try grind [Eval]
  case bool hv => exact eval_bool_val_eq hv hev
  case num hv => exact eval_num_val_eq hv hev

/-!
Looking up a variable in a typed store yields a value satisfying the type's denotation.
-/
theorem typed_store_lookup
  (hts : TypedStore s Γ)
  (hb : Ctx.Lookup Γ x T) :
  Ty.val_denot T (s.lookup x) := by
  induction hb
  case here => cases s; simp only [TypedStore] at hts; simp only [Store.lookup]; aesop
  case there ih => cases s; simp only [Store.lookup]; cases hts; grind

theorem sem_typ_var
  (hb : Ctx.Lookup Γ x T) :
  (Γ ⊨ (.var x) : T) := by
  intro s hts; simp only [Ty.exp_denot]
  exact ⟨s.lookup x, eval_val Store.lookup_is_val, typed_store_lookup hts hb⟩

theorem sem_typ_nsucc
  (ht : Γ ⊨ e : Ty.nat) :
  (Γ ⊨ .nsucc e : Ty.nat) := by
  intro s hts; specialize ht s hts; simp only [Ty.exp_denot] at *
  obtain ⟨v0, hev0, hv0⟩ := ht; simp only [Ty.val_denot] at hv0
  exact ⟨.nsucc v0, by grind [Exp.subst, Eval],
         by simp only [Ty.val_denot]; grind [Exp.IsNumVal]⟩

theorem val_denot_is_val
  (hv : Ty.val_denot T v) :
  v.IsVal := by
  cases T
  case bool => simp only [Ty.val_denot] at hv; grind [Exp.IsVal]
  case nat => simp only [Ty.val_denot] at hv; grind [Exp.IsVal]
  case arrow => simp only [Ty.val_denot] at hv; apply abs_val_is_val hv.left

theorem sem_typ_abs
  (ht : (Γ,x:T) ⊨ e : U) :
  (Γ ⊨ .abs T e : Ty.arrow T U) := by
  intro s hts; simp only [Ty.exp_denot, Exp.subst]
  constructor; constructor
  { apply eval_val; grind [Exp.IsVal] }
  { simp only [Ty.val_denot]
    constructor; try grind [Exp.IsAbsVal]
    intro arg harg
    unfold SemanticTyping at ht
    have hvarg := val_denot_is_val harg
    let s' := Store.cons arg hvarg s
    have hts' : TypedStore s' (Γ,x:T) := by simp only [TypedStore, s']; aesop
    specialize ht s' hts'; simp only [Ty.exp_denot] at ht ⊢
    have ⟨v0, hev0, hv0⟩ := ht
    refine ⟨v0, ?_, hv0⟩
    apply Eval.ev_app
    · exact eval_val (by grind [Exp.IsVal])
    · exact eval_val hvarg
    · simp only [Exp.subst_comp]; rw [Subst.fromStore_openVar_comp (hv := hvarg)]; exact hev0
  }

theorem sem_typ_app
  (ht1 : Γ ⊨ e1 : Ty.arrow T U)
  (ht2 : Γ ⊨ e2 : T) :
  (Γ ⊨ .app e1 e2 : U) := by
  intro s hts; specialize ht1 s hts; specialize ht2 s hts; simp only [Ty.exp_denot] at *
  obtain ⟨vf, hevf, hvf⟩ := ht1; obtain ⟨va, heva, hva⟩ := ht2
  simp only [Ty.val_denot] at hvf; cases hvf.left
  have app_typed := hvf.right va hva; simp only [Ty.exp_denot] at app_typed
  obtain ⟨v, hev, vdenot⟩ := app_typed
  use v; refine ⟨?_, vdenot⟩
  apply Eval.ev_app hevf heva
  cases hev; rename_i hev1 hev2 hev3
  cases (eval_val_eq (by constructor) hev1)
  cases (eval_val_eq (val_denot_is_val hva) hev2); exact hev3

theorem sem_typ_pred
  (ht : Γ ⊨ e : Ty.nat) :
  (Γ ⊨ .pred e : Ty.nat) := by
  intro s hts; specialize ht s hts; simp only [Ty.exp_denot] at *
  obtain ⟨v0, hev0, v0denot⟩ := ht; simp only [Ty.val_denot] at v0denot; cases v0denot
  case nzero =>
    exact ⟨.nzero, Eval.ev_pred_nzero hev0, by simp only [Ty.val_denot]; constructor⟩
  case nsucc n0 hv =>
    exact ⟨n0, Eval.ev_pred_nsucc hev0 hv, by simp only [Ty.val_denot]; assumption⟩

theorem sem_typ_iszero
  (ht : Γ ⊨ e : Ty.nat) :
  (Γ ⊨ .iszero e : Ty.bool) := by
  intro s hts; specialize ht s hts; simp only [Ty.exp_denot] at *
  obtain ⟨v0, hev0, v0denot⟩ := ht; simp only [Ty.val_denot] at v0denot; cases v0denot
  case nzero =>
    exact ⟨.btrue, Eval.ev_iszero_nzero hev0, by simp only [Ty.val_denot]; constructor⟩
  case nsucc n0 hv =>
    exact ⟨.bfalse, Eval.ev_iszero_nsucc hev0 hv, by simp only [Ty.val_denot]; constructor⟩

theorem sem_typ_cond
  (ht1 : Γ ⊨ e1 : Ty.bool)
  (ht2 : Γ ⊨ e2 : T)
  (ht3 : Γ ⊨ e3 : T) :
  (Γ ⊨ .cond e1 e2 e3 : T) := by
  intro s hts; specialize ht1 s hts; specialize ht2 s hts; specialize ht3 s hts
  simp only [Ty.exp_denot] at *
  obtain ⟨v1, hev1, v1denot⟩ := ht1; obtain ⟨v2, hev2, v2denot⟩ := ht2
  obtain ⟨v3, hev3, v3denot⟩ := ht3; simp only [Ty.val_denot] at v1denot; cases v1denot
  · exact ⟨v2, Eval.ev_cond_true hev1 hev2 hev3, v2denot⟩
  · exact ⟨v3, Eval.ev_cond_false hev1 hev2 hev3, v3denot⟩

/-!
Soundness: syntactic typing implies semantic typing.
-/
theorem semantic_soundness
  (ht : Γ ⊢ e : T) :
  (Γ ⊨ e : T) := by
  induction ht <;>
    try (solve |
      grind [sem_typ_var, sem_typ_abs, sem_typ_app, sem_typ_nsucc,
        sem_typ_pred, sem_typ_iszero, sem_typ_cond])
  all_goals (intro s hts; simp only [Ty.exp_denot])
  case btrue =>
    exact ⟨.btrue, by grind [Exp.subst, Eval],
           by simp only [Ty.val_denot]; grind [Exp.IsBoolVal]⟩
  case bfalse =>
    exact ⟨.bfalse, by grind [Exp.subst, Eval],
           by simp only [Ty.val_denot]; grind [Exp.IsBoolVal]⟩
  case nzero =>
    exact ⟨.nzero, by grind [Exp.subst, Eval],
           by simp only [Ty.val_denot]; grind [Exp.IsNumVal]⟩

end BigStep
end Stlc
