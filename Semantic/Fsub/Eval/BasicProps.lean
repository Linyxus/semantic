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

/-!
## Level renaming for stores
-/

/-- The identity function on levels leaves stores unchanged. -/
theorem Store.rename_levels_id (s : Store) : s.rename_levels id = s := by
  induction s with
  | nil => rfl
  | cons v s ih =>
    simp [Store.rename_levels]
    constructor
    · cases v; simp [Val.rename_levels, Exp.rename_levels_id]
    · exact ih

/-- Level renaming composes functorially for stores. -/
theorem Store.rename_levels_comp (s : Store) (f g : Nat -> Nat) :
    (s.rename_levels f).rename_levels g = s.rename_levels (g ∘ f) := by
  induction s with
  | nil => rfl
  | cons v s ih =>
    simp [Store.rename_levels]
    constructor
    · cases v
      simp [Val.rename_levels, Exp.rename_levels_comp]
    · exact ih

/-!
## Store framing theorem

The framing theorem states that reduction is preserved when we insert additional values
in the middle of a store, with appropriate level renaming.
-/

/-- Shift all levels up by n. This is used when inserting values into the store. -/
def shift_levels (n : Nat) : Nat → Nat := fun x => x + n

/-- Shifting by 0 is the identity. -/
theorem shift_levels_zero : shift_levels 0 = id := by
  funext x; simp [shift_levels]

/-- Shifting levels composes additively. -/
theorem shift_levels_comp (m n : Nat) :
    shift_levels m ∘ shift_levels n = shift_levels (m + n) := by
  funext x; simp [shift_levels]; omega

/-- Store lookup with appended stores: if we look up in s1 ++ s2,
we either find it in s1 (if index < s1.len) or in s2 (shifted index). -/
theorem Store.lookup_append (s1 s2 : Store) (n : Nat) :
    (s1 ++ s2).lookup n = if n < s1.len then s1.lookup n else s2.lookup (n - s1.len) := by
  induction s1 generalizing n with
  | nil =>
    -- nil ++ s2 = s2, and nil.len = 0
    simp only [Store.len, Store.instAppend]
    change (Store.append Store.nil s2).lookup n =
      if n < 0 then Store.nil.lookup n else s2.lookup (n - 0)
    simp only [Store.append]
    change s2.lookup n = if n < 0 then Store.nil.lookup n else s2.lookup n
    simp
  | cons v s1 ih =>
    cases n with
    | zero =>
      -- Looking up at index 0 in cons v s1 ++ s2
      simp only [Store.len, Store.instAppend]
      change (Store.append (Store.cons v s1) s2).lookup 0 =
        if 0 < s1.len + 1 then (Store.cons v s1).lookup 0 else s2.lookup (0 - (s1.len + 1))
      simp only [Store.append, Store.lookup]
      simp
    | succ n' =>
      -- Looking up at index n'+1 in cons v s1 ++ s2
      simp only [Store.len, Store.instAppend]
      change (Store.append (Store.cons v s1) s2).lookup (n' + 1) =
        if n' + 1 < s1.len + 1 then (Store.cons v s1).lookup (n' + 1)
        else s2.lookup (n' + 1 - (s1.len + 1))
      simp only [Store.append, Store.lookup]
      change (s1 ++ s2).lookup n' =
        if n' + 1 < s1.len + 1 then s1.lookup n' else s2.lookup (n' + 1 - (s1.len + 1))
      rw [ih]
      by_cases h : n' < s1.len
      · simp [h]
      · simp [h]

/-- Length of appended stores. -/
theorem Store.len_append (s1 s2 : Store) : (s1 ++ s2).len = s1.len + s2.len := by
  induction s1 with
  | nil =>
    simp only [Store.len, Store.instAppend]
    change (Store.append Store.nil s2).len = 0 + s2.len
    simp only [Store.append]
    omega
  | cons v s1 ih =>
    simp only [Store.len, Store.instAppend]
    change (Store.append (Store.cons v s1) s2).len = (s1.len + 1) + s2.len
    simp only [Store.append, Store.len]
    change (s1 ++ s2).len + 1 = (s1.len + 1) + s2.len
    rw [ih]
    omega

/-- Store append distributes over level renaming. -/
theorem Store.append_rename_levels (s1 s2 : Store) (f : Nat → Nat) :
    (s1 ++ s2).rename_levels f = s1.rename_levels f ++ s2.rename_levels f := by
  induction s1 with
  | nil => rfl
  | cons v s1 ih =>
    simp only [Store.instAppend]
    change (Store.append (Store.cons v s1) s2).rename_levels f =
      Store.append ((Store.cons v s1).rename_levels f) (s2.rename_levels f)
    simp only [Store.append, Store.rename_levels]
    change Store.cons (v.rename_levels f) ((s1 ++ s2).rename_levels f) =
      Store.cons (v.rename_levels f) (s1.rename_levels f ++ s2.rename_levels f)
    rw [ih]

/-- Lookup in a level-renamed store with shifted index. -/
theorem Store.lookup_rename_levels_shift (s : Store) (n k : Nat) :
    (s.rename_levels (shift_levels k)).lookup n =
    Option.map (fun v => v.rename_levels (shift_levels k)) (s.lookup n) := by
  induction s generalizing n with
  | nil => simp [Store.lookup, Store.rename_levels]
  | cons v s ih =>
    cases n with
    | zero => simp [Store.lookup, Store.rename_levels]
    | succ n' => simp [Store.lookup, Store.rename_levels, ih]

/-- Frame-shift function: adjusts free variables when inserting a store segment.
When we insert `s2` after position `pos`, free variables >= pos get shifted up by `shift`. -/
def frame_shift (pos shift : Nat) : Nat → Nat :=
  fun n => if n < pos then n else n + shift

/-- Frame-shifting by 0 at any position is the identity. -/
theorem frame_shift_zero (pos : Nat) : frame_shift pos 0 = id := by
  funext n; simp [frame_shift]

theorem step_frame
  (hr : Step s1 e1 (s1 ++ extra) e2) :
  Step
    (s1 ++ s2)
    e1
    (s1 ++ s2 ++ (extra.rename_levels (frame_shift s1.len s2.len)))
    (e2.rename_levels (frame_shift s1.len s2.len)) := by
  generalize heq : s1 ++ extra = s_out at hr
  induction hr generalizing s2
  case st_ctx ih => sorry
  case st_apply => sorry
  case st_tapply => sorry
  case st_rename => sorry
  case st_lift => sorry

theorem reduce_frame
  (hr : Reduce s1 e1 (s1 ++ extra) e2) :
  Reduce
    (s1 ++ s2)
    e1
    (s1 ++ s2 ++ (extra.rename_levels (frame_shift s1.len s2.len)))
    (e2.rename_levels (frame_shift s1.len s2.len)) := by sorry

end Fsub
