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
  case nsucc hnv ih =>
    cases hstep
    aesop

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
  case red_step hstep _ ih =>
    exfalso
    grind [val_no_step]

-- Values reduce to themselves
theorem reduce_val {v : Exp 0} :
  v.IsVal -> Reduce v v := by grind [reduce_refl]

theorem val_denot_is_val
  (hv : Ty.val_denot T v) :
  v.IsVal := by
  cases T
  case bool => simp [Ty.val_denot] at hv; grind [Exp.IsVal]
  case nat => simp [Ty.val_denot] at hv; grind [Exp.IsVal]
  case arrow => simp [Ty.val_denot] at hv; apply abs_val_is_val hv.left

/-!
Looking up a variable in a typed store yields a value satisfying the type's denotation.
-/
theorem lookup_typed_store
  (hts : TypedStore s Γ)
  (hb : Ctx.Lookup Γ x T) :
  Ty.val_denot T (s.lookup x) := by
  induction hb
  case here =>
    cases s; rename_i s0 v0
    simp [TypedStore] at hts
    simp [Store.lookup]
    aesop
  case there ih =>
    cases s; simp only [Store.lookup]
    cases hts
    grind

theorem sem_typ_var
  (hb : Ctx.Lookup Γ x T) :
  Γ ⊨ .var x : T := by
  intro s hts
  simp [Ty.exp_denot]
  use s.lookup x
  split_ands
  { apply reduce_val
    apply Store.lookup_is_val }
  { apply lookup_typed_store hts hb }

theorem sem_typ_abs
  (ht : (Γ,x:T) ⊨ e : U) :
  Γ ⊨ .abs T e : .arrow T U := by
  intro s hts
  simp [Ty.exp_denot]
  simp [Exp.subst]
  constructor; constructor
  { apply reduce_val; grind [Exp.IsVal] }
  { simp [Ty.val_denot]
    constructor; try grind [Exp.IsAbsVal]
    intro arg harg
    unfold SemanticTyping at ht
    have hvarg := val_denot_is_val harg
    let s' := Store.cons arg hvarg s
    have hts' : TypedStore s' (Γ,x:T) := by
      unfold s'
      simp [TypedStore]
      aesop
    specialize ht s' hts'
    simp [Ty.exp_denot] at ht ⊢
    have ⟨v0, hred0, hv0⟩ := ht
    use v0
    apply And.intro _ hv0
    { -- Need to show: Reduce (.app (.abs T e.subst(σ)) arg) v0
      -- Strategy: beta reduce then use hred0
      have beta_step : Step (.app (.abs T (e.subst (Subst.fromStore s).liftVar)) arg)
                            ((e.subst (Subst.fromStore s).liftVar).subst (Subst.openVar arg)) := by
        apply Step.st_app_beta hvarg
      have subst_eq : (e.subst (Subst.fromStore s).liftVar).subst (Subst.openVar arg) =
                      e.subst (Subst.fromStore s') := by
        simp [Exp.subst_comp]
        rw [Subst.fromStore_openVar_comp (hv := hvarg)]
      rw [subst_eq] at beta_step
      exact Reduce.red_step beta_step hred0
    }
  }

-- Congruence lemmas for Reduce
theorem reduce_app_left {e1 e1' e2 : Exp 0} :
  Reduce e1 e1' -> Reduce (.app e1 e2) (.app e1' e2) := by
  intro h
  induction h
  case red_refl => exact reduce_refl
  case red_step hstep hred ih =>
    exact reduce_trans (step_to_reduce (Step.st_app_1 hstep)) ih

theorem reduce_app_right {e1 e2 e2' : Exp 0} :
  e1.IsVal -> Reduce e2 e2' -> Reduce (.app e1 e2) (.app e1 e2') := by
  intro hv h
  induction h
  case red_refl => exact reduce_refl
  case red_step hstep hred ih =>
    exact reduce_trans (step_to_reduce (Step.st_app_2 hv hstep)) ih

theorem sem_typ_app
  (ht1 : Γ ⊨ e1 : Ty.arrow T U)
  (ht2 : Γ ⊨ e2 : T) :
  Γ ⊨ .app e1 e2 : U := by
  intro s hts
  specialize ht1 s hts
  specialize ht2 s hts
  simp only [Ty.exp_denot] at *
  obtain ⟨vf, hredf, hvf⟩ := ht1
  obtain ⟨va, hreda, hva⟩ := ht2
  simp [Ty.val_denot] at hvf
  cases hvf.left
  have app_typed := hvf.right va hva
  simp [Ty.exp_denot] at app_typed
  obtain ⟨v, hredapp, vdenot⟩ := app_typed
  use v
  apply And.intro _ vdenot
  -- Show: Reduce (.app (e1.subst σ) (e2.subst σ)) v
  -- Strategy: e1 → vf, e2 → va, app vf va → v
  have hvf_val :=
    val_denot_is_val (T := Ty.arrow T U) (by simp [Ty.val_denot]; exact ⟨by constructor, hvf.right⟩)
  have hva_val := val_denot_is_val hva
  have red1 : Reduce (.app (e1.subst (Subst.fromStore s)) (e2.subst (Subst.fromStore s)))
                     (.app _ (e2.subst (Subst.fromStore s))) :=
    reduce_app_left hredf
  have red2 : Reduce (.app _ (e2.subst (Subst.fromStore s)))
                     (.app _ va) :=
    reduce_app_right hvf_val hreda
  exact reduce_trans red1 (reduce_trans red2 hredapp)

-- Congruence lemma for nsucc
theorem reduce_nsucc {e e' : Exp 0} :
  Reduce e e' -> Reduce (.nsucc e) (.nsucc e') := by
  intro h
  induction h
  case red_refl => exact reduce_refl
  case red_step hstep hred ih =>
    exact reduce_trans (step_to_reduce (Step.st_nsucc hstep)) ih

theorem sem_typ_nsucc
  (ht : Γ ⊨ e : Ty.nat) :
  (Γ ⊨ .nsucc e : Ty.nat) := by
  intro s hts
  specialize ht s hts
  simp [Ty.exp_denot] at *
  obtain ⟨v0, hred0, hv0⟩ := ht
  simp [Ty.val_denot] at hv0
  use .nsucc v0
  split_ands
  { -- Show: Reduce (.nsucc (e.subst (Subst.fromStore s))) (.nsucc v0)
    exact reduce_nsucc hred0 }
  { -- Show: Ty.val_denot Ty.nat (.nsucc v0)
    simp [Ty.val_denot]
    grind [Exp.IsNumVal] }

-- Congruence lemma for pred
theorem reduce_pred {e e' : Exp 0} :
  Reduce e e' -> Reduce (.pred e) (.pred e') := by
  intro h
  induction h
  case red_refl => exact reduce_refl
  case red_step hstep hred ih =>
    exact reduce_trans (step_to_reduce (Step.st_pred hstep)) ih

theorem sem_typ_pred
  (ht : Γ ⊨ e : Ty.nat) :
  (Γ ⊨ .pred e : Ty.nat) := by
  intro s hts
  specialize ht s hts
  simp only [Ty.exp_denot] at *
  obtain ⟨v0, hred0, v0denot⟩ := ht
  simp [Ty.val_denot] at v0denot
  cases v0denot
  case nzero =>
    use .nzero
    apply And.intro _ (by grind [Ty.val_denot, Exp.IsNumVal])
    -- Show: Reduce (.pred (e.subst σ)) .nzero
    -- Strategy: e.subst σ → .nzero, then pred .nzero → .nzero
    have pred_step : Step (.pred .nzero) .nzero := Step.st_pred_nzero
    exact reduce_trans (reduce_pred hred0) (step_to_reduce pred_step)
  case nsucc n0 hv =>
    use n0
    apply And.intro _ (by grind [Ty.val_denot, Exp.IsNumVal])
    -- Show: Reduce (.pred (e.subst σ)) n0
    -- Strategy: e.subst σ → .nsucc n0, then pred (.nsucc n0) → n0
    have pred_step : Step (.pred (.nsucc n0)) n0 := Step.st_pred_nsucc hv
    exact reduce_trans (reduce_pred hred0) (step_to_reduce pred_step)

-- Congruence lemma for iszero
theorem reduce_iszero {e e' : Exp 0} :
  Reduce e e' -> Reduce (.iszero e) (.iszero e') := by
  intro h
  induction h
  case red_refl => exact reduce_refl
  case red_step hstep hred ih =>
    exact reduce_trans (step_to_reduce (Step.st_iszero hstep)) ih

theorem sem_typ_iszero
  (ht : Γ ⊨ e : Ty.nat) :
  (Γ ⊨ .iszero e : Ty.bool) := by
  intro s hts
  specialize ht s hts
  simp only [Ty.exp_denot] at *
  obtain ⟨v0, hred0, v0denot⟩ := ht
  simp [Ty.val_denot] at v0denot
  cases v0denot
  case nzero =>
    use .btrue
    apply And.intro _ (by grind [Ty.val_denot, Exp.IsBoolVal])
    -- Show: Reduce (.iszero (e.subst σ)) .btrue
    -- Strategy: e.subst σ → .nzero, then iszero .nzero → .btrue
    have iszero_step : Step (.iszero .nzero) .btrue := Step.st_iszero_nzero
    exact reduce_trans (reduce_iszero hred0) (step_to_reduce iszero_step)
  case nsucc n0 hv =>
    use .bfalse
    apply And.intro _ (by grind [Ty.val_denot, Exp.IsBoolVal])
    -- Show: Reduce (.iszero (e.subst σ)) .bfalse
    -- Strategy: e.subst σ → .nsucc n0, then iszero (.nsucc n0) → .bfalse
    have iszero_step : Step (.iszero (.nsucc n0)) .bfalse := Step.st_iszero_nsucc hv
    exact reduce_trans (reduce_iszero hred0) (step_to_reduce iszero_step)

-- Congruence lemma for cond
theorem reduce_cond {e1 e1' e2 e3 : Exp 0} :
  Reduce e1 e1' -> Reduce (.cond e1 e2 e3) (.cond e1' e2 e3) := by
  intro h
  induction h
  case red_refl => exact reduce_refl
  case red_step hstep hred ih =>
    exact reduce_trans (step_to_reduce (Step.st_cond hstep)) ih

theorem sem_typ_cond
  (ht1 : Γ ⊨ e1 : Ty.bool)
  (ht2 : Γ ⊨ e2 : T)
  (ht3 : Γ ⊨ e3 : T) :
  (Γ ⊨ .cond e1 e2 e3 : T) := by
  intro s hts
  specialize ht1 s hts
  specialize ht2 s hts
  specialize ht3 s hts
  simp only [Ty.exp_denot] at *
  obtain ⟨v1, hred1, v1denot⟩ := ht1
  obtain ⟨v2, hred2, v2denot⟩ := ht2
  obtain ⟨v3, hred3, v3denot⟩ := ht3
  simp [Ty.val_denot] at v1denot
  cases v1denot
  case btrue =>
    use v2
    apply And.intro _ v2denot
    -- Show: Reduce (.cond (e1.subst σ) (e2.subst σ) (e3.subst σ)) v2
    -- Strategy: e1.subst σ → .btrue, then cond .btrue e2' e3' → e2', then e2' → v2
    have cond_step :
      Step (.cond .btrue (e2.subst (Subst.fromStore s)) (e3.subst (Subst.fromStore s)))
                          (e2.subst (Subst.fromStore s)) := Step.st_cond_true
    exact reduce_trans (reduce_cond hred1) (reduce_trans (step_to_reduce cond_step) hred2)
  case bfalse =>
    use v3
    apply And.intro _ v3denot
    -- Show: Reduce (.cond (e1.subst σ) (e2.subst σ) (e3.subst σ)) v3
    -- Strategy: e1.subst σ → .bfalse, then cond .bfalse e2' e3' → e3', then e3' → v3
    have cond_step :
      Step (.cond .bfalse (e2.subst (Subst.fromStore s)) (e3.subst (Subst.fromStore s)))
                          (e3.subst (Subst.fromStore s)) := Step.st_cond_false
    exact reduce_trans (reduce_cond hred1) (reduce_trans (step_to_reduce cond_step) hred3)

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
      | intro s hts; simp [Ty.exp_denot, Ty.val_denot];
        constructor; constructor; constructor; try constructor)

end SmallStep
end Stlc
