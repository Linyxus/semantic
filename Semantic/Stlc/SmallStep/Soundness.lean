import Semantic.Stlc.TypeSystem
import Semantic.Stlc.SmallStep.Denotation
import Mathlib.Tactic

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
  Γ ⊨ .abs T e : .arrow T U := by sorry

theorem semantic_soundness
  (ht : Γ ⊢ e : T) :
  Γ ⊨ e : T := by
  induction ht <;> try grind [sem_typ_var]
  all_goals sorry
