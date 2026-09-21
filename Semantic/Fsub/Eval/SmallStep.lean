import Semantic.Fsub.Syntax
import Semantic.Fsub.Substitution
import Semantic.Fsub.Heap

namespace Fsub

/-- Small-step reduction of configurations `(h, e)`.
  `Step h e h' e'` means that expression `e` in heap `h` steps to `e'` in heap `h'`. -/
inductive Step : Heap -> Exp {} -> Heap -> Exp {} -> Prop where
| step_apply {h : Heap} {x : Nat} :
  h x = some ⟨.abs T e, hv⟩ ->
  Step h (.app (.free x) y) h (e.subst (Subst.openVar y))
| step_tapply {h : Heap} {x : Nat} :
  h x = some ⟨.tabs T0 e, hv⟩ ->
  Step h (.tapp (.free x) S) h (e.subst (Subst.openTVar .top))
| step_ctx_letin :
  Step h e1 h' e1' ->
  Step h (.letin e1 e2) h' (.letin e1' e2)
| step_rename :
  Step h (.letin (.var x) e) h (e.subst (Subst.openVar x))
| step_lift {h : Heap} :
  (hv : Exp.IsVal v) ->
  (hfresh : h l = none) ->
  Step h (.letin v e) (h.extend l ⟨v, hv⟩) (e.subst (Subst.openVar (.free l)))

/-- Multi-step reduction: the reflexive-transitive closure of `Step`. -/
inductive Reduce : Heap -> Exp {} -> Heap -> Exp {} -> Prop where
| refl :
  Reduce h e h e
| step :
  Step h1 e1 h2 e2 ->
  Reduce h2 e2 h3 e3 ->
  Reduce h1 e1 h3 e3

theorem reduce_trans
  (hred1 : Reduce h1 e1 h2 e2)
  (hred2 : Reduce h2 e2 h3 e3) :
  Reduce h1 e1 h3 e3 := by
  induction hred1 with
  | refl => exact hred2
  | step hstep _ ih => exact Reduce.step hstep (ih hred2)

theorem reduce_ctx_letin
  (hred : Reduce h e1 h' e1') :
  Reduce h (.letin e1 e2) h' (.letin e1' e2) := by
  induction hred with
  | refl => exact Reduce.refl
  | step hstep _ ih => exact Reduce.step (Step.step_ctx_letin hstep) ih

/-- Answers (values and variables) are irreducible. -/
theorem step_ans_absurd
  (hans : Exp.IsAns e)
  (hstep : Step h e h' e') :
  False := by
  cases hans with
  | is_val hv => cases hv <;> cases hstep
  | is_var => cases hstep

theorem step_heap_monotonic
  (hstep : Step h e h' e') :
  h'.subsumes h := by
  induction hstep with
  | step_apply _ => exact Heap.subsumes_refl _
  | step_tapply _ => exact Heap.subsumes_refl _
  | step_ctx_letin _ ih => exact ih
  | step_rename => exact Heap.subsumes_refl _
  | step_lift _ hfresh => exact Heap.extend_subsumes hfresh

theorem reduce_heap_monotonic
  (hred : Reduce h e h' e') :
  h'.subsumes h := by
  induction hred with
  | refl => exact Heap.subsumes_refl _
  | step hstep _ ih => exact Heap.subsumes_trans ih (step_heap_monotonic hstep)

/-! ### Finite heaps

A heap is finite when all locations from some bound `N` onwards are unallocated.
This is exactly what is needed to always be able to allocate a fresh location,
which in turn is needed for `let x = v in e` to make progress. -/

def Heap.Finite (h : Heap) : Prop :=
  ∃ N, ∀ l, N ≤ l -> h l = none

theorem Heap.empty_finite : (∅ : Heap).Finite :=
  ⟨0, fun _ _ => rfl⟩

theorem Heap.Finite.exists_fresh {h : Heap}
  (hfin : h.Finite) :
  ∃ l, h l = none := by
  obtain ⟨N, hN⟩ := hfin
  exact ⟨N, hN N (Nat.le_refl N)⟩

theorem Heap.Finite.extend {h : Heap}
  (hfin : h.Finite) (l : Nat) (v : Val {}) :
  (h.extend l v).Finite := by
  obtain ⟨N, hN⟩ := hfin
  refine ⟨max N (l+1), fun l' hl' => ?_⟩
  simp only [Heap.extend]
  split
  · omega
  · exact hN l' (by omega)

theorem step_preserves_finite
  (hfin : h.Finite)
  (hstep : Step h e h' e') :
  h'.Finite := by
  induction hstep with
  | step_apply _ => exact hfin
  | step_tapply _ => exact hfin
  | step_ctx_letin _ ih => exact ih hfin
  | step_rename => exact hfin
  | step_lift _ _ => exact hfin.extend _ _

theorem reduce_preserves_finite
  (hfin : h.Finite)
  (hred : Reduce h e h' e') :
  h'.Finite := by
  induction hred with
  | refl => exact hfin
  | step hstep _ ih => exact ih (step_preserves_finite hfin hstep)

end Fsub
