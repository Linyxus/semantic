import Semantic.Stlc.TypeSystem
import Semantic.Stlc.SmallStep.Denotation
import Mathlib.Tactic

/-!
Soundness proof for small-step STLC.

This module proves that syntactic typing implies semantic typing.
-/

namespace Stlc
namespace SmallStep

/-!
Basic properties of reduction.
-/

theorem reduce_refl {e : Exp 0} :
  Reduce e e := Reduce.red_refl

theorem reduce_trans {e1 e2 e3 : Exp 0} :
  Reduce e1 e2 -> Reduce e2 e3 -> Reduce e1 e3 := by
  intro h12 h23
  induction h12 generalizing e3
  case red_refl => exact h23
  case red_step h_step h_reduce ih =>
    exact Reduce.red_step h_step (ih h23)

theorem step_to_reduce {e1 e2 : Exp 0} :
  Step e1 e2 -> Reduce e1 e2 :=
  fun h => Reduce.red_step h reduce_refl

/-!
Numeric values cannot step.
-/
theorem num_val_no_step {nv : Exp 0}
  (hnv : nv.IsNumVal)
  (hstep : Step nv nv') : False := by
  induction hnv generalizing nv' <;> try (solve | cases hstep)
  case nsucc hnv ih => cases hstep; aesop

/-!
Values cannot step.
-/
theorem val_no_step {v : Exp 0}
  (hv : v.IsVal)
  (hstep : Step v v') : False := by
  cases hv <;> try (solve | cases hstep)
  case bool hv => cases hv <;> cases hstep
  case num => grind [num_val_no_step]

-- Values reduce only to themselves
theorem reduce_val_eq {v : Exp 0} :
  v.IsVal -> ∀ v', Reduce v v' -> v = v' := by
  intro hv v' hred
  induction hred
  case red_refl => rfl
  case red_step hstep _ ih => exfalso; grind [val_no_step]

-- Values reduce to themselves
theorem reduce_val {v : Exp 0} :
  v.IsVal -> Reduce v v := by grind [reduce_refl]

theorem val_denot_is_val
  (hv : Ty.val_denot T v) :
  v.IsVal := by
  cases T
  case bool => simp only [Ty.val_denot] at hv; grind [Exp.IsVal]
  case nat => simp only [Ty.val_denot] at hv; grind [Exp.IsVal]
  case arrow => simp only [Ty.val_denot] at hv; apply abs_val_is_val hv.left

/-!
Looking up a variable in a typed store yields a value satisfying the type's denotation.
-/
theorem lookup_typed_store
  (hts : TypedStore s Γ)
  (hb : Ctx.Lookup Γ x T) :
  Ty.val_denot T (s.lookup x) := by
  induction hb
  case here => cases s; simp only [TypedStore] at hts; simp only [Store.lookup]; aesop
  case there ih => cases s; simp only [Store.lookup]; cases hts; grind

theorem sem_typ_var
  (hb : Ctx.Lookup Γ x T) :
  Γ ⊨ .var x : T := by
  intro s hts; simp only [Ty.exp_denot]
  exact ⟨s.lookup x, reduce_val Store.lookup_is_val, lookup_typed_store hts hb⟩

theorem sem_typ_abs
  (ht : (Γ,x:T) ⊨ e : U) :
  Γ ⊨ .abs T e : .arrow T U := by
  intro s hts; simp only [Ty.exp_denot, Exp.subst]
  constructor; constructor
  { apply reduce_val; grind [Exp.IsVal] }
  { simp only [Ty.val_denot]
    constructor; try grind [Exp.IsAbsVal]
    intro arg harg
    unfold SemanticTyping at ht
    have hvarg := val_denot_is_val harg
    let s' := Store.cons arg hvarg s
    have hts' : TypedStore s' (Γ,x:T) := by simp only [TypedStore, s']; aesop
    specialize ht s' hts'; simp only [Ty.exp_denot] at ht ⊢
    obtain ⟨v0, hred0, hv0⟩ := ht
    refine ⟨v0, ?_, hv0⟩
    have subst_eq : (e.subst (Subst.fromStore s).liftVar).subst (Subst.openVar arg) =
                    e.subst (Subst.fromStore s') := by
      simp only [Exp.subst_comp]; rw [Subst.fromStore_openVar_comp (hv := hvarg)]
    exact Reduce.red_step (subst_eq ▸ Step.st_app_beta hvarg) hred0
  }

-- Generic congruence lifting: each step of h is lifted by `lift_step`.
private theorem reduce_congr {e e' : Exp 0} {f : Exp 0 → Exp 0}
    (lift_step : ∀ {a b : Exp 0}, Step a b -> Step (f a) (f b))
    (h : Reduce e e') : Reduce (f e) (f e') := by
  induction h
  case red_refl => exact reduce_refl
  case red_step hstep _ ih => exact reduce_trans (step_to_reduce (lift_step hstep)) ih

-- Congruence lemmas for Reduce
theorem reduce_app_left {e1 e1' e2 : Exp 0} :
  Reduce e1 e1' -> Reduce (Exp.app e1 e2) (Exp.app e1' e2) :=
  reduce_congr (f := (Exp.app · e2)) Step.st_app_1

theorem reduce_app_right {e1 e2 e2' : Exp 0} :
  e1.IsVal -> Reduce e2 e2' -> Reduce (Exp.app e1 e2) (Exp.app e1 e2') := fun hv =>
  reduce_congr (f := Exp.app e1) (Step.st_app_2 hv)

theorem sem_typ_app
  (ht1 : Γ ⊨ e1 : Ty.arrow T U)
  (ht2 : Γ ⊨ e2 : T) :
  Γ ⊨ .app e1 e2 : U := by
  intro s hts; specialize ht1 s hts; specialize ht2 s hts; simp only [Ty.exp_denot] at *
  obtain ⟨vf, hredf, hvf⟩ := ht1; obtain ⟨va, hreda, hva⟩ := ht2
  simp only [Ty.val_denot] at hvf; cases hvf.left
  have app_typed := hvf.right va hva; simp only [Ty.exp_denot] at app_typed
  obtain ⟨v, hredapp, vdenot⟩ := app_typed
  refine ⟨v, ?_, vdenot⟩
  -- Strategy: e1 → vf, e2 → va, app vf va → v
  have hvf_val := val_denot_is_val (T := Ty.arrow T U)
    (by simp only [Ty.val_denot]; exact ⟨by constructor, hvf.right⟩)
  exact reduce_trans (reduce_app_left hredf)
    (reduce_trans (reduce_app_right hvf_val hreda) hredapp)

-- Congruence lemma for nsucc
theorem reduce_nsucc {e e' : Exp 0} :
  Reduce e e' -> Reduce (Exp.nsucc e) (Exp.nsucc e') :=
  reduce_congr (f := Exp.nsucc) Step.st_nsucc

theorem sem_typ_nsucc
  (ht : Γ ⊨ e : Ty.nat) :
  (Γ ⊨ .nsucc e : Ty.nat) := by
  intro s hts; specialize ht s hts; simp only [Ty.exp_denot] at *
  obtain ⟨v0, hred0, hv0⟩ := ht; simp only [Ty.val_denot] at hv0
  exact ⟨.nsucc v0, reduce_nsucc hred0, by simp only [Ty.val_denot]; grind [Exp.IsNumVal]⟩

-- Congruence lemma for pred
theorem reduce_pred {e e' : Exp 0} :
  Reduce e e' -> Reduce (Exp.pred e) (Exp.pred e') :=
  reduce_congr (f := Exp.pred) Step.st_pred

theorem sem_typ_pred
  (ht : Γ ⊨ e : Ty.nat) :
  (Γ ⊨ .pred e : Ty.nat) := by
  intro s hts; specialize ht s hts; simp only [Ty.exp_denot] at *
  obtain ⟨v0, hred0, v0denot⟩ := ht; simp only [Ty.val_denot] at v0denot
  cases v0denot
  case nzero =>
    exact ⟨.nzero, reduce_trans (reduce_pred hred0) (step_to_reduce Step.st_pred_nzero),
           by simp only [Ty.val_denot]; constructor⟩
  case nsucc n0 hv =>
    exact ⟨n0, reduce_trans (reduce_pred hred0) (step_to_reduce (Step.st_pred_nsucc hv)),
           by simp only [Ty.val_denot]; assumption⟩

-- Congruence lemma for iszero
theorem reduce_iszero {e e' : Exp 0} :
  Reduce e e' -> Reduce (Exp.iszero e) (Exp.iszero e') :=
  reduce_congr (f := Exp.iszero) Step.st_iszero

theorem sem_typ_iszero
  (ht : Γ ⊨ e : Ty.nat) :
  (Γ ⊨ .iszero e : Ty.bool) := by
  intro s hts; specialize ht s hts; simp only [Ty.exp_denot] at *
  obtain ⟨v0, hred0, v0denot⟩ := ht; simp only [Ty.val_denot] at v0denot
  cases v0denot
  case nzero =>
    exact ⟨.btrue, reduce_trans (reduce_iszero hred0) (step_to_reduce Step.st_iszero_nzero),
           by simp only [Ty.val_denot]; constructor⟩
  case nsucc n0 hv =>
    exact ⟨.bfalse, reduce_trans (reduce_iszero hred0) (step_to_reduce (Step.st_iszero_nsucc hv)),
           by simp only [Ty.val_denot]; constructor⟩

-- Congruence lemma for cond
theorem reduce_cond {e1 e1' e2 e3 : Exp 0} :
  Reduce e1 e1' -> Reduce (Exp.cond e1 e2 e3) (Exp.cond e1' e2 e3) :=
  reduce_congr (f := (Exp.cond · e2 e3)) Step.st_cond

theorem sem_typ_cond
  (ht1 : Γ ⊨ e1 : Ty.bool)
  (ht2 : Γ ⊨ e2 : T)
  (ht3 : Γ ⊨ e3 : T) :
  (Γ ⊨ .cond e1 e2 e3 : T) := by
  intro s hts; specialize ht1 s hts; specialize ht2 s hts; specialize ht3 s hts
  simp only [Ty.exp_denot] at *
  obtain ⟨v1, hred1, v1denot⟩ := ht1; obtain ⟨v2, hred2, v2denot⟩ := ht2
  obtain ⟨v3, hred3, v3denot⟩ := ht3; simp only [Ty.val_denot] at v1denot
  cases v1denot
  case btrue =>
    exact ⟨v2, reduce_trans (reduce_cond hred1)
                 (reduce_trans (step_to_reduce Step.st_cond_true) hred2), v2denot⟩
  case bfalse =>
    exact ⟨v3, reduce_trans (reduce_cond hred1)
                 (reduce_trans (step_to_reduce Step.st_cond_false) hred3), v3denot⟩

/-!
Soundness: syntactic typing implies semantic typing.
-/
theorem semantic_soundness
  (ht : Γ ⊢ e : T) :
  Γ ⊨ e : T := by
  induction ht
    <;> try (solve
      | grind [sem_typ_var, sem_typ_abs, sem_typ_app,
        sem_typ_nsucc, sem_typ_pred, sem_typ_iszero, sem_typ_cond]
      | intro s hts; simp only [Ty.exp_denot, Ty.val_denot];
        constructor; constructor; constructor; try constructor)

end SmallStep
end Stlc
