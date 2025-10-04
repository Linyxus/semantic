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

/-- If appending a store to s1 gives s1 back, the appended store must be empty. -/
theorem Store.append_eq_self_iff_nil (s1 extra : Store) (h : s1 ++ extra = s1) :
    extra = Store.nil := by
  induction s1 with
  | nil =>
    -- nil ++ extra = nil, so extra = nil
    simp only [Store.instAppend] at h
    change Store.append Store.nil extra = Store.nil at h
    simp only [Store.append] at h
    exact h
  | cons v s1 ih =>
    -- cons v s1 ++ extra = cons v s1
    simp only [Store.instAppend] at h
    change Store.append (Store.cons v s1) extra = Store.cons v s1 at h
    simp only [Store.append] at h
    change Store.cons v (s1 ++ extra) = Store.cons v s1 at h
    injection h with h_v h_s
    exact ih h_s

/-- Left cancellation for store append: if s1 ++ s2 = s1 ++ s3, then s2 = s3. -/
theorem Store.append_left_cancel (s1 s2 s3 : Store) (h : s1 ++ s2 = s1 ++ s3) :
    s2 = s3 := by
  induction s1 with
  | nil =>
    -- nil ++ s2 = nil ++ s3
    simp only [Store.instAppend] at h
    change Store.append Store.nil s2 = Store.append Store.nil s3 at h
    simp only [Store.append] at h
    exact h
  | cons v s1 ih =>
    -- cons v s1 ++ s2 = cons v s1 ++ s3
    simp only [Store.instAppend] at h
    change Store.append (Store.cons v s1) s2 = Store.append (Store.cons v s1) s3 at h
    simp only [Store.append] at h
    change Store.cons v (s1 ++ s2) = Store.cons v (s1 ++ s3) at h
    injection h with h_v h_s
    exact ih h_s

/-- Corollary: if s1 ++ s2 = s1.snoc v, then s2 = cons v nil. -/
theorem Store.append_eq_snoc_iff (s1 s2 : Store) (v : Val {}) (h : s1 ++ s2 = s1.snoc v) :
    s2 = Store.cons v Store.nil := by
  rw [Store.snoc_eq_append] at h
  exact Store.append_left_cancel s1 s2 (Store.cons v Store.nil) h

/-- Alternate characterization of append with singleton. -/
theorem Store.append_singleton_eq (s1 : Store) (v : Val {}) :
    s1 ++ Store.cons v Store.nil = s1.snoc v := by
  exact (Store.snoc_eq_append s1 v).symm

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

/-!
## Substitution domain bounds
-/

/-- The openVar substitution has domain bounded by the variable's domain. -/
theorem Subst.openVar_has_dom {y : Var s} :
    (Subst.openVar y).has_dom y.dom := by
  constructor
  · intro x
    cases x with
    | here =>
      simp [Subst.openVar, Var.dom]
    | there x' =>
      simp [Subst.openVar, Var.dom]
  · intro X
    cases X with
    | there x' =>
      simp [Subst.openVar, Ty.dom]

/-- The openTVar substitution with .top has domain bounded by 0. -/
theorem Subst.openTVar_top_has_dom :
    (Subst.openTVar (.top : Ty s)).has_dom 0 := by
  constructor
  · intro x
    cases x with
    | there x' =>
      -- Bound variables stay bound
      simp [Subst.openTVar, Var.dom]
  · intro X
    cases X with
    | here =>
      -- The first type variable gets replaced with .top which has domain 0
      simp [Subst.openTVar, Ty.dom]
    | there X' =>
      -- Other type variables remain as type variables
      simp [Subst.openTVar, Ty.dom]

/-!
## Frame-shift preservation

If a term's domain is within the frame position, frame-shifting leaves it unchanged.
-/

/-- If a variable's domain is at most `l1`, renaming with `frame_shift l1 l2` is the identity. -/
theorem Var.rename_level_frame_shift (x : Var s) (l1 l2 : Nat) (h : x.dom <= l1) :
    x.rename_level (frame_shift l1 l2) = x := by
  cases x with
  | bound n => rfl
  | free n =>
    simp [Var.rename_level, frame_shift]
    unfold Var.dom at h
    simp at h
    omega

/-- If a type's domain is at most `l1`, renaming with `frame_shift l1 l2` is the identity. -/
theorem Ty.rename_levels_frame_shift (T : Ty s) (l1 l2 : Nat) (h : T.dom <= l1) :
    T.rename_levels (frame_shift l1 l2) = T := by
  induction T with
  | top => rfl
  | tvar _ => rfl
  | singleton x =>
    simp [Ty.rename_levels]
    apply Var.rename_level_frame_shift
    simp [Ty.dom] at h
    exact h
  | arrow T1 T2 ih1 ih2 =>
    simp [Ty.rename_levels]
    constructor
    · apply ih1
      simp [Ty.dom] at h
      omega
    · apply ih2
      simp [Ty.dom] at h
      omega
  | poly T1 T2 ih1 ih2 =>
    simp [Ty.rename_levels]
    constructor
    · apply ih1
      simp [Ty.dom] at h
      omega
    · apply ih2
      simp [Ty.dom] at h
      omega

/-- If an expression's domain is at most `l1`, renaming with `frame_shift l1 l2` is the identity. -/
theorem Exp.rename_levels_frame_shift (e : Exp s) (l1 l2 : Nat) (h : e.dom <= l1) :
    e.rename_levels (frame_shift l1 l2) = e := by
  induction e with
  | var x =>
    simp [Exp.rename_levels]
    apply Var.rename_level_frame_shift
    simp [Exp.dom] at h
    exact h
  | abs T e ih =>
    simp [Exp.rename_levels]
    constructor
    · apply Ty.rename_levels_frame_shift
      simp [Exp.dom] at h
      omega
    · apply ih
      simp [Exp.dom] at h
      omega
  | app x y =>
    simp [Exp.rename_levels]
    constructor
    · apply Var.rename_level_frame_shift
      simp [Exp.dom] at h
      omega
    · apply Var.rename_level_frame_shift
      simp [Exp.dom] at h
      omega
  | tabs T e ih =>
    simp [Exp.rename_levels]
    constructor
    · apply Ty.rename_levels_frame_shift
      simp [Exp.dom] at h
      omega
    · apply ih
      simp [Exp.dom] at h
      omega
  | tapp x T =>
    simp [Exp.rename_levels]
    constructor
    · apply Var.rename_level_frame_shift
      simp [Exp.dom] at h
      omega
    · apply Ty.rename_levels_frame_shift
      simp [Exp.dom] at h
      omega
  | letin e1 e2 ih1 ih2 =>
    simp [Exp.rename_levels]
    constructor
    · apply ih1
      simp [Exp.dom] at h
      omega
    · apply ih2
      simp [Exp.dom] at h
      omega

/-- A store is well-formed if all values at position i have domain <= i. -/
def Store.WfStore (s : Store) : Prop :=
  ∀ i v, s.lookup i = some v → v.unwrap.dom <= i

/-- If lookup succeeds at index i, then i < s.len -/
theorem Store.lookup_some_lt_len {s : Store} {i : Nat} {v : Val {}}
  (h : s.lookup i = some v) : i < s.len := by
  induction s generalizing i with
  | nil =>
    simp [Store.lookup] at h
  | cons w s ih =>
    cases i with
    | zero =>
      simp [Store.len]
    | succ i' =>
      simp [Store.lookup] at h
      have hi := ih h
      simp [Store.len]
      omega

theorem wf_store_append_inv
  (hwf : Store.WfStore (s1 ++ s2)) :
  Store.WfStore s1 := by
  intro i v hlookup
  -- If s1.lookup i = some v, then (s1 ++ s2).lookup i = some v
  have hi : i < s1.len := Store.lookup_some_lt_len hlookup
  have hlookup' : (s1 ++ s2).lookup i = some v := by
    rw [Store.lookup_append]
    simp [hi, hlookup]
  exact hwf i v hlookup'

/-- Lookup in snoc: when i < s.len, lookup in s.snoc v is same as lookup in s. -/
theorem Store.lookup_snoc_lt (s : Store) (v : Val {}) (i : Nat) (h : i < s.len) :
    (s.snoc v).lookup i = s.lookup i := by
  induction s generalizing i with
  | nil =>
    simp [Store.len] at h
  | cons w s ih =>
    cases i with
    | zero =>
      simp [Store.snoc, Store.lookup]
    | succ i' =>
      simp [Store.snoc, Store.lookup]
      apply ih
      simp [Store.len] at h
      omega

/-- Lookup in snoc: when i = s.len, lookup returns the snoced value. -/
theorem Store.lookup_snoc_eq (s : Store) (v : Val {}) :
    (s.snoc v).lookup s.len = some v := by
  induction s with
  | nil =>
    simp [Store.snoc, Store.lookup, Store.len]
  | cons w s ih =>
    simp [Store.snoc, Store.lookup, Store.len]
    exact ih

theorem Store.lookup_frame_shift {base1 base2 inserted : Store}
  (hwf : Store.WfStore (base1 ++ base2))
  (hl : (base1 ++ base2).lookup x = some v) :
  (base1 ++ inserted ++
    (base2.rename_levels (frame_shift base1.len inserted.len))).lookup
    (frame_shift base1.len inserted.len x) =
  some (v.rename_levels (frame_shift base1.len inserted.len)) := by
  -- Rewrite both sides using Store.lookup_append
  rw [Store.lookup_append] at hl
  rw [Store.lookup_append]
  -- Split on whether x < base1.len
  by_cases h : x < base1.len
  · -- Case 1: x < base1.len, lookup is in base1
    have heq : (frame_shift base1.len inserted.len x) = x := by
      simp [frame_shift, h]
    simp [heq] at *
    simp [h] at hl ⊢
    have h2 : x < (base1 ++ inserted).len := by
      rw [Store.len_append]
      omega
    simp [h2]
    simp [Store.lookup_append]
    simp [h]
    have heq : v.rename_levels (frame_shift base1.len inserted.len) = v := by
      generalize heq0 : v = v0
      cases v0
      simp [Val.rename_levels]
      apply Exp.rename_levels_frame_shift
      have hwf' := wf_store_append_inv hwf
      have hdom := hwf' x v hl
      subst v
      simp at hdom
      omega
    simp [heq]
    exact hl
  · -- Case 2: x >= base1.len, lookup is in base2
    sorry

/-- Lookup in snoc: when i > s.len, lookup fails. -/
theorem Store.lookup_snoc_gt (s : Store) (v : Val {}) (i : Nat) (h : i > s.len) :
    (s.snoc v).lookup i = none := by
  induction s generalizing i with
  | nil =>
    cases i with
    | zero =>
      simp [Store.len] at h
    | succ i' =>
      simp [Store.snoc, Store.lookup]
  | cons w s ih =>
    cases i with
    | zero =>
      simp [Store.len] at h
    | succ i' =>
      simp [Store.snoc, Store.lookup]
      apply ih
      simp [Store.len] at h
      omega

theorem step_wf_store {s1 : Store}
  (hwf : s1.WfStore)
  (hwf_e : Exp.WfIn e1 s1)
  (hstep : Step s1 e1 s2 e2) :
  s2.WfStore := by
  induction hstep with
  | st_ctx step ih =>
    -- e1 = .letin e1' u, need WfIn for e1'
    obtain ⟨hwf1, _⟩ := Exp.letin_wf_inv hwf_e
    exact ih hwf hwf1
  | st_apply _ =>
    -- s2 = s1
    exact hwf
  | st_tapply _ =>
    -- s2 = s1
    exact hwf
  | st_rename =>
    -- s2 = s1
    exact hwf
  | st_lift hv =>
    -- s2 = s1.snoc ⟨v, hv⟩
    -- Need to show ∀ i val, s2.lookup i = some val → val.unwrap.dom <= i
    rename_i v_exp s_old e_body
    intro i val hlookup
    -- Case analysis: either i < s_old.len, i = s_old.len, or i > s_old.len
    by_cases h : i < s_old.len
    · -- Case 1: i < s_old.len, so lookup is in the old store
      have hlookup_old : s_old.lookup i = some val := by
        rw [Store.lookup_snoc_lt s_old ⟨v_exp, hv⟩ i h] at hlookup
        exact hlookup
      exact hwf i val hlookup_old
    · -- Case 2 or 3: i >= s_old.len
      push_neg at h
      by_cases heq : i = s_old.len
      · -- Case 2: i = s_old.len
        subst heq
        have hval : val = ⟨v_exp, hv⟩ := by
          rw [Store.lookup_snoc_eq s_old ⟨v_exp, hv⟩] at hlookup
          injection hlookup with h
          exact h.symm
        subst hval
        simp
        -- Need to show v_exp.dom <= s_old.len
        -- From hwf_e: (v_exp.letin e_body).WfIn s_old
        unfold Exp.WfIn at hwf_e
        simp [Exp.dom] at hwf_e
        omega
      · -- Case 3: i > s_old.len
        have hgt : i > s_old.len := by omega
        rw [Store.lookup_snoc_gt s_old ⟨v_exp, hv⟩ i hgt] at hlookup
        -- hlookup says none = some val, contradiction
        contradiction

theorem step_wf
  (hwfs : Store.WfStore s1)
  (hwf : Exp.WfIn e1 s1)
  (hstep : Step s1 e1 s2 e2) :
  Exp.WfIn e2 s2 := by
  induction hstep with
  | st_ctx step ih =>
    -- e1 = .letin e1' u, e2 = .letin e2' u
    -- Get well-formedness of components
    obtain ⟨hwf1, hwf2⟩ := Exp.letin_wf_inv hwf
    -- By IH, e2' is well-formed in s2
    have hwf_e2' := ih hwfs hwf1
    -- Need to show .letin e2' u is well-formed in s2
    -- This means both e2' and u must be well-formed in s2
    unfold Exp.WfIn at hwf_e2' hwf2 ⊢
    simp [Exp.dom] at hwf_e2' hwf2 ⊢
    constructor
    · exact hwf_e2'
    · -- u was well-formed in s1, and store only grows
      obtain ⟨extra, heq⟩ := step_store_monotone step
      rw [heq]
      rw [Store.len_append]
      omega
  | st_apply hlookup =>
    -- e1 = .app (.free x) y, e2 = e.subst (Subst.openVar y)
    -- s2 = s_in (store unchanged)
    rename_i s_in x y T e hv
    unfold Exp.WfIn at hwf ⊢
    -- hwf says (Exp.app (Var.free x) y).dom <= s_in.len
    -- Goal is (e.subst (Subst.openVar y)).dom <= s_in.len
    -- From store well-formedness, e has domain <= x
    have he_dom : e.dom <= x := by
      have := hwfs x ⟨.abs T e, hv⟩ hlookup
      simp [Exp.dom] at this
      exact this.2
    -- From hwf, x and y are in scope
    have hx_bound : x < s_in.len := by
      simp only [Exp.dom, Var.dom] at hwf
      have : x + 1 <= s_in.len := by
        trans (max (x + 1) y.dom)
        · exact Nat.le_max_left _ _
        · exact hwf
      omega
    have hy_bound : y.dom <= s_in.len := by
      simp only [Exp.dom, Var.dom] at hwf
      trans (max (x + 1) y.dom)
      · exact Nat.le_max_right _ _
      · exact hwf
    -- Use substitution domain bound
    have hsub := Exp.subst_dom (e:=e) (Subst.openVar_has_dom (y:=y))
    omega
  | st_tapply hlookup =>
    -- e1 = .tapp (.free x) T_arg, e2 = e.subst (Subst.openTVar .top)
    -- s2 = s_in (store unchanged)
    rename_i s_in x T_arg T0 e hv
    unfold Exp.WfIn at hwf ⊢
    -- From store well-formedness, e has domain <= x
    have he_dom : e.dom <= x := by
      have := hwfs x ⟨.tabs T0 e, hv⟩ hlookup
      simp [Exp.dom] at this
      exact this.2
    -- From hwf, x is in scope
    have hx_bound : x < s_in.len := by
      simp only [Exp.dom, Var.dom] at hwf
      have : x + 1 <= s_in.len := by
        trans (max (x + 1) T_arg.dom)
        · exact Nat.le_max_left _ _
        · exact hwf
      omega
    -- openTVar .top has domain 0
    have hsub := Exp.subst_dom (e:=e) (Subst.openTVar_top_has_dom)
    omega
  | st_rename =>
    -- e1 = .letin (.var x) e_body, e2 = e_body.subst (Subst.openVar x)
    -- s2 = s1 (store unchanged)
    rename_i x e_body
    unfold Exp.WfIn at hwf ⊢
    simp [Exp.dom] at hwf ⊢
    obtain ⟨hx, he⟩ := hwf
    -- Use substitution domain bound
    have hsub := Exp.subst_dom (e:=e_body) (Subst.openVar_has_dom (y:=x))
    omega
  | st_lift hv =>
    -- e1 = .letin v e_body, e2 = e_body.subst (Subst.openVar (.free s_store.len))
    -- From the Step.st_lift constructor, s2 = s_store.snoc ⟨v, hv⟩
    rename_i v s_store e_body
    unfold Exp.WfIn at hwf ⊢
    simp [Exp.dom] at hwf ⊢
    -- hwf gives us max v.dom e_body.dom <= s_store.len
    have hv_dom : v.dom <= s_store.len := by
      have := Nat.le_max_left v.dom e_body.dom
      omega
    have he_dom : e_body.dom <= s_store.len := by
      have := Nat.le_max_right v.dom e_body.dom
      omega
    -- The free variable has domain s_store.len + 1
    have hfree : (Var.free (s:={}) s_store.len).dom = s_store.len + 1 := by
      simp [Var.dom]
    -- Use substitution domain bound
    have hsub := Exp.subst_dom (e:=e_body) (Subst.openVar_has_dom (y:=Var.free (s:={}) s_store.len))
    -- Need to show: (e_body.subst (Subst.openVar (.free s_store.len))).dom <= s2.len
    -- From Step.st_lift, s2 is definitionally s_store.snoc ⟨v, hv⟩
    -- So s2.len is (s_store.snoc ⟨v, hv⟩).len
    change (e_body.subst (Subst.openVar (Var.free s_store.len))).dom <= (s_store.snoc ⟨v, hv⟩).len
    rw [Store.snoc_eq_append, Store.len_append]
    simp [Store.len]
    rw [hfree] at hsub
    omega

theorem step_frame_old
  (hwf_s : Store.WfStore s1)
  (hwf : Exp.WfIn e1 s1)
  (hr : Step s1 e1 (s1 ++ extra) e2) :
  Step
    (s1 ++ s2)
    e1
    (s1 ++ s2 ++ (extra.rename_levels (frame_shift s1.len s2.len)))
    (e2.rename_levels (frame_shift s1.len s2.len)) := by
  generalize heq : s1 ++ extra = s_out at hr
  induction hr generalizing s2
  case st_ctx ih =>
    obtain ⟨hwf1, hwf2⟩ := Exp.letin_wf_inv hwf
    subst heq
    rename_i s1' e1' e2' u step
    simp [Exp.rename_levels]
    have hu : u.rename_levels (frame_shift s1'.len s2.len) = u := by
      apply Exp.rename_levels_frame_shift
      exact hwf2
    rw [hu]
    apply Step.st_ctx
    exact ih hwf_s hwf1 rfl
  case st_apply =>
    rename_i s1' x y T e hv hlookup
    -- From heq, we know extra = nil
    have hnil : extra = Store.nil := Store.append_eq_self_iff_nil s1' extra heq
    rw [hnil]
    simp [Store.append_nil, Store.rename_levels]
    -- The renaming is identity because:
    -- 1. e is locally closed (values in store have no free vars)
    -- 2. y is well-formed in s1'
    -- 3. Therefore e.subst (openVar y) is well-formed in s1'
    have hren : (e.subst (Subst.openVar y)).rename_levels (frame_shift s1'.len s2.len) =
                e.subst (Subst.openVar y) := by
      apply Exp.rename_levels_frame_shift
      -- The abs value has domain 0 (locally closed)
      -- Substituting with y (domain <= s1'.len) gives domain <= s1'.len
      have he_dom : e.dom <= x := by
        -- e comes from the abs value at position x in the store
        have := hwf_s x ⟨.abs T e, hv⟩ hlookup
        simp [Exp.dom] at this
        exact this.2
      have hy_dom : y.dom <= s1'.len := by
        unfold Exp.WfIn Exp.dom at hwf
        simp at hwf
        omega
      have hx_bound : x < s1'.len := by
        unfold Exp.WfIn Exp.dom Var.dom at hwf
        simp at hwf
        omega
      have hsub := Exp.subst_dom (e:=e) (Subst.openVar_has_dom (y:=y))
      omega
    rw [hren]
    -- Need to show the lookup works in s1' ++ s2
    have hlookup' : (s1' ++ s2).lookup x = some ⟨.abs T e, hv⟩ := by
      rw [Store.lookup_append]
      -- x < s1'.len because app is well-formed
      have hx : x < s1'.len := by
        unfold Exp.WfIn Exp.dom Var.dom at hwf
        simp at hwf
        omega
      simp [hx, hlookup]
    apply Step.st_apply hlookup'
  case st_tapply =>
    -- st_tapply: Step s1 (.tapp (.free x) T) s1 (e.subst (Subst.openTVar .top))
    -- where s1.lookup x = some ⟨.tabs T0 e, hv⟩
    rename_i s_store x T T0 e hv hlookup
    -- From heq, we know extra = nil (store doesn't change in st_tapply)
    have hnil : extra = Store.nil := Store.append_eq_self_iff_nil s_store extra heq
    rw [hnil]
    simp [Store.append_nil, Store.rename_levels]
    -- The renaming is identity because e.subst (openTVar .top) has domain <= s_store.len
    have hren : (e.subst (Subst.openTVar .top)).rename_levels (frame_shift s_store.len s2.len) =
                e.subst (Subst.openTVar .top) := by
      apply Exp.rename_levels_frame_shift
      -- The tabs value has domain <= x (the store index)
      have he_dom : e.dom <= x := by
        -- e comes from the tabs value at position x in the store
        have := hwf_s x ⟨.tabs T0 e, hv⟩ hlookup
        simp [Exp.dom] at this
        exact this.2
      have hx_bound : x < s_store.len := by
        unfold Exp.WfIn Exp.dom Var.dom at hwf
        simp at hwf
        omega
      have hsub := Exp.subst_dom (e:=e) (Subst.openTVar_top_has_dom)
      omega
    rw [hren]
    -- Need to show the lookup works in s_store ++ s2
    have hlookup' : (s_store ++ s2).lookup x = some ⟨.tabs T0 e, hv⟩ := by
      rw [Store.lookup_append]
      -- x < s_store.len because tapp is well-formed
      have hx : x < s_store.len := by
        unfold Exp.WfIn Exp.dom Var.dom at hwf
        simp at hwf
        omega
      simp [hx, hlookup]
    apply Step.st_tapply hlookup'
  case st_rename =>
    rename_i s_store x e_body
    obtain heq := Store.append_eq_self_iff_nil _ _ heq
    subst heq
    simp [Store.rename_levels, Store.append_nil]
    -- The renaming is identity because e.subst (openVar x) is well-formed in s_store
    have hren : (e_body.subst (Subst.openVar x)).rename_levels (frame_shift s_store.len s2.len) =
                e_body.subst (Subst.openVar x) := by
      apply Exp.rename_levels_frame_shift
      -- Need to show (e_body.subst (Subst.openVar x)).dom <= s_store.len
      have he_dom : e_body.dom <= s_store.len := by
        unfold Exp.WfIn at hwf
        simp [Exp.dom] at hwf
        omega
      have hx_dom : x.dom <= s_store.len := by
        unfold Exp.WfIn at hwf
        simp only [Exp.dom] at hwf
        omega
      have hsub := Exp.subst_dom (e:=e_body) (Subst.openVar_has_dom (y:=x))
      omega
    rw [hren]
    apply Step.st_rename
  case st_lift v s1 u hv =>
    -- From heq: s1 ++ extra = s1.snoc ⟨v, hv⟩
    -- Therefore: extra = Store.cons ⟨v, hv⟩ Store.nil
    have hval := Store.append_eq_snoc_iff s1 extra ⟨v, hv⟩ heq
    subst hval
    -- Now extra = Store.cons ⟨v, hv⟩ Store.nil
    simp [Store.rename_levels, Store.append_singleton_eq]

    -- v doesn't change under renaming because it's well-formed in s1
    have hv_ren : v.rename_levels (frame_shift s1.len s2.len) = v := by
      apply Exp.rename_levels_frame_shift
      obtain ⟨hwf_v, _⟩ := Exp.letin_wf_inv hwf
      unfold Exp.WfIn at hwf_v
      exact hwf_v
    simp [Val.rename_levels, hv_ren]

    -- Key lemma: substitution with shifted free variable
    have key_lemma :
      (u.subst (Subst.openVar (Var.free (s:={}) s1.len))).rename_levels
        (frame_shift s1.len s2.len) =
      u.subst (Subst.openVar (Var.free (s:={}) ((s1 ++ s2).len))) := by
      -- Use Exp.subst_rename_levels
      rw [Exp.subst_rename_levels]

      -- First, u doesn't change under renaming because it's well-formed in s1
      have hu_ren : u.rename_levels (frame_shift s1.len s2.len) = u := by
        apply Exp.rename_levels_frame_shift
        -- u is the body of a letin that's well-formed in s1
        obtain ⟨_, hwf_u⟩ := Exp.letin_wf_inv hwf
        exact hwf_u
      rw [hu_ren]

      -- Now show that renaming the substitution gives the right result
      have hsub_ren :
        (Subst.openVar (Var.free (s:={}) s1.len)).rename_levels
          (frame_shift s1.len s2.len) =
        Subst.openVar (Var.free (s:={}) ((s1 ++ s2).len)) := by
        apply Subst.funext
        · intro x
          cases x with
          | here =>
            -- The .here case maps to .free s1.len, which gets shifted
            simp [Subst.openVar, Subst.rename_levels, Var.rename_level]
            -- frame_shift s1.len s2.len s1.len = s1.len + s2.len
            simp [frame_shift]
            -- s1.len >= s1.len, so we get s1.len + s2.len
            have : ¬(s1.len < s1.len) := Nat.lt_irrefl _
            simp [Store.len_append]
          | there y =>
            -- The .there case preserves bound variables
            simp [Subst.openVar, Subst.rename_levels]
            -- Bound variables don't change under level renaming
            rfl
        · intro X
          -- Type variables are preserved
          simp [Subst.openVar, Subst.rename_levels]
          -- Type variables may have bound references, which don't change
          cases X with
          | there X' => rfl
      rw [hsub_ren]

    rw [key_lemma]
    apply Step.st_lift

theorem step_frame
  (hwf_s : Store.WfStore (base1 ++ base2))
  (hwf : Exp.WfIn e1 (base1 ++ base2))
  (hr : Step (base1 ++ base2) e1 (base1 ++ base2 ++ extra) e2) :
  Step
    (base1 ++ inserted ++ (base2.rename_levels (frame_shift base1.len inserted.len)))
    (e1.rename_levels (frame_shift base1.len inserted.len))
    (base1 ++ inserted ++ (base2.rename_levels (frame_shift base1.len inserted.len) ++
      (extra.rename_levels (frame_shift base1.len inserted.len))))
    (e2.rename_levels (frame_shift base1.len inserted.len)) := by
  generalize heq1 : base1 ++ base2 = s_in at hr
  generalize heq2 : s_in ++ extra = s_out at hr
  induction hr generalizing inserted with
  | st_ctx hr ih =>
    subst heq1 heq2
    simp [Exp.rename_levels]
    obtain ⟨hwf1, hwf2⟩ := Exp.letin_wf_inv hwf
    apply Step.st_ctx
    apply ih hwf1 rfl rfl
  | st_apply =>
    rename_i x y T e hv hlookup
    -- Store doesn't change in st_apply, so extra = nil
    have hnil : extra = Store.nil := by
      subst heq1
      exact Store.append_eq_self_iff_nil _ _ heq2
    subst hnil heq1
    simp [Store.append_nil, Store.rename_levels, Exp.rename_levels]
    simp [Exp.subst_rename_levels, Subst.openVar_rename_levels]
    apply Step.st_apply
    { sorry }
    all_goals sorry
  | st_tapply => sorry
  | st_rename => sorry
  | st_lift => sorry

/-!
## Reduction under renaming

First, we prove that reduction is preserved under level renaming.
-/

-- theorem step_rename_levels
--   (hs : Step s1 e1 s2 e2)
--   (f : Nat → Nat) :
--   Step
--     (s1.rename_levels f)
--     (e1.rename_levels f)
--     (s2.rename_levels f)
--     (e2.rename_levels f) := by
--   sorry

-- theorem reduce_rename_levels
--   (hr : Reduce s1 e1 s2 e2)
--   (f : Nat → Nat) :
--   Reduce
--     (s1.rename_levels f)
--     (e1.rename_levels f)
--     (s2.rename_levels f)
--     (e2.rename_levels f) := by
--   induction hr with
--   | red_refl => apply Reduce.red_refl
--   | red_step hstep _ ih =>
--     apply Reduce.red_step
--     · exact step_rename_levels hstep f
--     · exact ih

-- theorem reduce_frame
--   (hwf_s : Store.WfStore s1)
--   (hwf : Exp.WfIn e1 s1)
--   (hr : Reduce s1 e1 (s1 ++ extra) e2) :
--   Reduce
--     (s1 ++ s2)
--     e1
--     (s1 ++ s2 ++ (extra.rename_levels (frame_shift s1.len s2.len)))
--     (e2.rename_levels (frame_shift s1.len s2.len)) := by
--   generalize hs_out : s1 ++ extra = s_out at hr
--   induction hr generalizing extra s2 with
--   | @red_refl s_store e_orig =>
--     -- Base case: no reduction steps
--     -- From hs_out: s1 ++ extra = s_store, so extra = nil (since s_store = s1)
--     have hnil : extra = Store.nil := Store.append_eq_self_iff_nil _ _ hs_out
--     subst hnil
--     simp [Store.rename_levels, Store.append_nil]
--     -- Since e_orig is well-formed in s_store, renaming is identity
--     have hren : e_orig.rename_levels (frame_shift s_store.len s2.len) = e_orig := by
--       apply Exp.rename_levels_frame_shift
--       unfold Exp.WfIn at hwf
--       exact hwf
--     rw [hren]
--     apply Reduce.red_refl
--   | red_step hstep hrest ih =>
--     have ⟨delta1, h1⟩ := step_store_monotone hstep
--     have ⟨delta2, h2⟩ := reduce_store_monotone hrest
--     subst hs_out h1
--     rw [Store.append_assoc] at h2
--     have heq := Store.append_left_cancel _ _ _ h2
--     subst heq
--     have hstep' := step_frame (s2:=s2) hwf_s hwf hstep
--     apply Reduce.red_step hstep'
--     have hwf_s' := step_wf_store hwf_s hwf hstep
--     have hwf' := step_wf hwf_s hwf hstep

--     -- Distribute renaming over append
--     rw [Store.append_rename_levels (s1 := delta1) (s2 := delta2)]

--     -- Let me directly construct the equality we need for the IH
--     -- Recall: generalize hs_out : s1 ++ extra = s_out at hr
--     -- So s_out is the final store, and s1 is the initial store
--     -- After substitutions, s1 has become the unnamed s✝

--     -- The key insight: apply the IH to hrest with the frame being s2
--     --We need to prove: base_store ++ extra = base_store ++ (delta1 ++ delta2)
--     -- where base_store is the store after the step, which is (the unnamed store ++ delta1)

--     -- We can directly prove the equality the IH needs
--     -- The IH is expecting: base ++ extra = base ++ (delta1 ++ delta2)
--     -- where base is the store after the step
--     -- We can show this is just associativity when extra = delta2

--     -- The fundamental issue: after the step, we have a different base store
--     -- The IH can't directly help because it inserts the frame in the wrong place
--     --
--     -- The solution: we need to prove that reduce_frame holds using a DIFFERENT
--     -- induction principle, or we need additional lemmas about store commutation
--     --
--     -- For now, this case requires `step_rename_levels` to be proven first,
--     -- then additional lemmas about how renamings and store operations interact.
--     --
--     -- The high-level structure should be:
--     -- 1. Rename hrest to get the right variable shifts
--     -- 2. Insert the frame s2 into the renamed reduction
--     -- 3. Show this matches the goal using store algebraic properties

--     sorry

-- end Fsub
