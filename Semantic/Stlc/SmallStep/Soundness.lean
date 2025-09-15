import Semantic.Stlc.TypeSystem
import Semantic.Stlc.SmallStep.Denotation
import Mathlib.Tactic

namespace Stlc.SmallStep

-- Basic lemmas about Step and Reduce

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

-- Values don't step
theorem num_val_no_step {nv : Exp 0}
  (hnv : nv.IsNumVal)
  (hstep : Step nv nv') : False := by
  induction hnv generalizing nv' <;> try (solve | cases hstep)
  case nsucc hnv ih =>
    cases hstep
    aesop

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

theorem semantic_soundness
  (ht : Γ ⊢ e : T) :
  Γ ⊨ e : T := by
  induction ht <;> try grind [sem_typ_var, sem_typ_abs, sem_typ_app]
  all_goals sorry

end Stlc.SmallStep
