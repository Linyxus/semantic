import Semantic.Fsub.Eval.Core

namespace Fsub

/-!
## Basic properties of evaluation

This file contains basic lemmas and properties about stores, reduction, and evaluation.
-/

/-- The reduction relation is transitive. -/
theorem reduce_trans
  (hr1 : Reduce s e s' e')
  (hr2 : Reduce s' e' s'' e'') :
  Reduce s e s'' e'' := by
  induction hr1
  case red_refl => exact hr2
  case red_step => constructor <;> aesop

/-- A single step can be lifted to a reduction. -/
theorem reduce_step
  (hs : Step s e s' e') :
  Reduce s e s' e' := by
  apply Reduce.red_step hs
  apply Reduce.red_refl

/-- Reduction is preserved under the let-in context.
If `e1` reduces to `e2`, then `let e1 in u` reduces to `let e2 in u`. -/
theorem reduce_ctx
  (hr : Reduce s1 e1 s2 e2) :
  Reduce s1 (.letin e1 u) s2 (.letin e2 u) := by
  induction hr
  case red_refl => apply Reduce.red_refl
  case red_step =>
    apply Reduce.red_step
    · apply Step.st_ctx; assumption
    · aesop

/-- A reduction followed by a single step yields a reduction. -/
theorem reduce_right_step
  (hr : Reduce s1 e1 s2 e2)
  (hs : Step s2 e2 s3 e3) :
  Reduce s1 e1 s3 e3 := by
  apply reduce_trans hr
  apply reduce_step hs

/-!
## Store properties

Properties about store operations: lookup, snoc, append, and len.
-/

/-- Store append is associative. -/
theorem Store.append_assoc (s1 s2 s3 : Store) :
  (s1 ++ s2) ++ s3 = s1 ++ (s2 ++ s3) := by
  induction s1 with
  | nil => rfl
  | cons v s1 ih =>
    show (Store.cons v s1 ++ s2) ++ s3 = Store.cons v s1 ++ (s2 ++ s3)
    change Store.cons v (s1 ++ s2) ++ s3 = Store.cons v (s1 ++ (s2 ++ s3))
    change Store.cons v ((s1 ++ s2) ++ s3) = Store.cons v (s1 ++ (s2 ++ s3))
    rw [ih]

/-- Appending an empty store is the identity operation. -/
theorem Store.append_nil (s : Store) : s ++ Store.nil = s := by
  induction s with
  | nil => rfl
  | cons v s ih =>
    change Store.cons v (s ++ Store.nil) = Store.cons v s
    rw [ih]

/-- The `snoc` operation (appending a single value) is equivalent to
appending a singleton store. -/
theorem Store.snoc_eq_append (s : Store) (v : Val {}) :
  s.snoc v = s ++ Store.cons v Store.nil := by
  induction s with
  | nil => rfl
  | cons w s ih =>
    change Store.cons w (s.snoc v) = Store.cons w s ++ Store.cons v Store.nil
    change Store.cons w (s.snoc v) = Store.cons w (s ++ Store.cons v Store.nil)
    rw [ih]

/-- **Store monotonicity for Step**: A single evaluation step either preserves
the store or extends it. The store is never shrunk or modified. -/
theorem step_store_monotone {s1 e1 s2 e2 : _} (h : Step s1 e1 s2 e2) :
  ∃ s0, s2 = s1 ++ s0 := by
  induction h with
  | st_ctx _ ih => exact ih
  | st_apply _ => use Store.nil; simp [Store.append_nil]
  | st_tapply _ => use Store.nil; simp [Store.append_nil]
  | st_rename => use Store.nil; simp [Store.append_nil]
  | st_lift hv =>
    use Store.cons ⟨_, hv⟩ Store.nil
    exact Store.snoc_eq_append _ _

/-- **Store monotonicity for Reduce**: The reduction relation only extends the store.
Given a reduction from `(s1, e1)` to `(s2, e2)`, the final store `s2` is an extension
of the initial store `s1`, i.e., there exists some store `s0` such that `s2 = s1 ++ s0`. -/
theorem reduce_store_monotone {s1 e1 s2 e2 : _} (h : Reduce s1 e1 s2 e2) :
  ∃ s0, s2 = s1 ++ s0 := by
  induction h with
  | red_refl => use Store.nil; simp [Store.append_nil]
  | red_step hstep _ ih =>
    obtain ⟨s_mid, eq_mid⟩ := step_store_monotone hstep
    obtain ⟨s_rest, eq_rest⟩ := ih
    use s_mid ++ s_rest
    rw [eq_rest, eq_mid, Store.append_assoc]

end Fsub
