import Semantic.Consume.Debruijn

/-!
This module defines the capture set syntax of CC.
-/

namespace Consume

/-- Mutability mode for captured variables: read-write (epsilon) or read-only (ro). -/
inductive Mutability : Type where
| epsilon : Mutability  -- default mode, read-write
| ro : Mutability       -- read-only

inductive Access : Type where
| M : Mutability -> Access
| drop : Access

namespace Mutability

inductive Le : Mutability -> Mutability -> Prop where
| refl {m : Mutability} :
    Le m m
| ro_eps :
    Le .ro .epsilon

instance instLE : LE Mutability := ⟨Mutability.Le⟩

/-- Transitivity of mutability ordering. -/
theorem Le.trans {m1 m2 m3 : Mutability} (h1 : m1 ≤ m2) (h2 : m2 ≤ m3) : m1 ≤ m3 := by
  cases h1 with
  | refl => exact h2
  | ro_eps => cases h2; exact .ro_eps

/-- Read-only is less than or equal to any mutability. -/
theorem Le.ro_le {m : Mutability} : .ro ≤ m := by
  cases m with
  | epsilon => exact .ro_eps
  | ro => exact .refl

end Mutability

namespace Access

/-- Read-only image of an access mode: access modes become read-only; `drop` is
    a different class of use mode than mutability, so it is left untouched. -/
def applyRO : Access -> Access
| .M _ => .M .ro
| .drop => .drop

@[simp]
theorem applyRO_idempotent {a : Access} : a.applyRO.applyRO = a.applyRO := by
  cases a <;> rfl

/-- Ordering on access modes: access modes follow the mutability ordering;
    `drop` is comparable only to itself. -/
inductive Le : Access -> Access -> Prop where
| M {m1 m2 : Mutability} : m1 ≤ m2 -> Le (.M m1) (.M m2)
| drop : Le .drop .drop

instance instLE : LE Access := ⟨Access.Le⟩

theorem Le.refl {a : Access} : a ≤ a := by
  cases a with
  | M _ => exact .M Mutability.Le.refl
  | drop => exact .drop

theorem Le.trans {a1 a2 a3 : Access} (h1 : a1 ≤ a2) (h2 : a2 ≤ a3) : a1 ≤ a3 := by
  cases h1 with
  | M h1' => cases h2 with | M h2' => exact .M (Mutability.Le.trans h1' h2')
  | drop => cases h2; exact .drop

/-- The read-only image is below the original mode. -/
theorem applyRO_le {a : Access} : a.applyRO ≤ a := by
  cases a with
  | M _ => exact .M Mutability.Le.ro_le
  | drop => exact .drop

end Access

/-- A variable, either bound (de Bruijn indexed) or free (heap pointer). -/
inductive Var : Kind -> Sig -> Type where
| bound : BVar s k -> Var k s
| free : Nat -> Var k s

/-- A set of captured variables. -/
inductive CaptureSet : Sig -> Type where
| empty : CaptureSet s
| union : CaptureSet s -> CaptureSet s -> CaptureSet s
| var : Access -> Var .var s -> CaptureSet s
| cvar : Access -> BVar s .cvar -> CaptureSet s

/-- Provides `{}` notation for the empty capture set. -/
@[simp]
instance CaptureSet.instEmptyCollection :
  EmptyCollection (CaptureSet s) where
  emptyCollection := CaptureSet.empty

/-- Provides `∪` notation for capture set union. -/
@[simp]
instance CaptureSet.instUnion : Union (CaptureSet s) where
  union := CaptureSet.union

/-- Applies a renaming to a variable. Free variables remain unchanged. -/
def Var.rename : Var k s1 -> Rename s1 s2 -> Var k s2
| .bound x, f => .bound (f.var x)
| .free n, _ => .free n

/-- Applies a renaming to all bound variables in a capture set. -/
def CaptureSet.rename : CaptureSet s1 -> Rename s1 s2 -> CaptureSet s2
| .empty, _ => .empty
| .union cs1 cs2, ρ => .union (cs1.rename ρ) (cs2.rename ρ)
| .var m x, ρ => .var m (x.rename ρ)
| .cvar m x, ρ => .cvar m (ρ.var x)

/-- Renaming by the identity renaming leaves a capture set unchanged. -/
theorem CaptureSet.rename_id {cs : CaptureSet s} :
    cs.rename (Rename.id) = cs := by
  induction cs
  case empty => rfl
  case union ih1 ih2 => simp only [CaptureSet.rename, ih1, ih2]
  case var m x => cases x <;> rfl
  case cvar m x => simp only [CaptureSet.rename, Rename.id]

/-- Renaming distributes over composition of renamings. -/
theorem CaptureSet.rename_comp {cs : CaptureSet s1} {f : Rename s1 s2} {g : Rename s2 s3} :
    (cs.rename f).rename g = cs.rename (f.comp g) := by
  induction cs generalizing s2 s3
  case empty => rfl
  case union ih1 ih2 => simp only [CaptureSet.rename, ih1, ih2]
  case var m x =>
    cases x
    · simp only [CaptureSet.rename, Var.rename, Rename.comp]
    · simp only [CaptureSet.rename, Var.rename]
  case cvar m x => simp only [CaptureSet.rename, Rename.comp]

/-- Applies read-only mutability to all elements in a capture set. -/
def CaptureSet.applyRO : CaptureSet s -> CaptureSet s
| .empty => .empty
| .union cs1 cs2 => .union (cs1.applyRO) (cs2.applyRO)
| .var a x => .var a.applyRO x
| .cvar a x => .cvar a.applyRO x

/-- Applies a mutability to all elements in a capture set.
  This is used to preserve mutability during substitution. -/
def CaptureSet.applyMut (m : Mutability) (cs : CaptureSet s) : CaptureSet s :=
  match m with
  | .epsilon => cs
  | .ro => cs.applyRO

-- applyRO simp lemmas (definitional)
@[simp] theorem CaptureSet.applyRO_empty : (CaptureSet.empty (s:=s)).applyRO = .empty := rfl
@[simp] theorem CaptureSet.applyRO_union {cs1 cs2 : CaptureSet s} :
    (cs1.union cs2).applyRO = cs1.applyRO.union cs2.applyRO := rfl
@[simp] theorem CaptureSet.applyRO_var {a : Access} {x : Var .var s} :
    (CaptureSet.var a x).applyRO = .var a.applyRO x := rfl
@[simp] theorem CaptureSet.applyRO_cvar {a : Access} {x : BVar s .cvar} :
    (CaptureSet.cvar a x).applyRO = .cvar a.applyRO x := rfl

-- applyMut simp lemmas
@[simp] theorem CaptureSet.applyMut_epsilon {cs : CaptureSet s} :
    cs.applyMut .epsilon = cs := rfl
@[simp] theorem CaptureSet.applyMut_ro {cs : CaptureSet s} :
    cs.applyMut .ro = cs.applyRO := rfl

/-- Applying applyRO twice is idempotent. -/
@[simp]
theorem CaptureSet.applyRO_applyRO {cs : CaptureSet s} :
    cs.applyRO.applyRO = cs.applyRO := by
  induction cs with
  | empty => rfl
  | union cs1 cs2 ih1 ih2 => simp only [ih1, ih2, CaptureSet.applyRO_union]
  | var a x => simp only [CaptureSet.applyRO, Access.applyRO_idempotent]
  | cvar a x => simp only [CaptureSet.applyRO, Access.applyRO_idempotent]

/-- Applying applyMut after applyRO simplifies. -/
@[simp]
theorem CaptureSet.applyRO_applyMut {cs : CaptureSet s} {m : Mutability} :
    cs.applyRO.applyMut m = cs.applyRO := by
  cases m <;> simp only [CaptureSet.applyMut_epsilon, CaptureSet.applyMut_ro, applyRO_applyRO]

/-- Applying applyRO after applyMut gives applyRO. -/
@[simp]
theorem CaptureSet.applyMut_applyRO {cs : CaptureSet s} {m : Mutability} :
    (cs.applyMut m).applyRO = cs.applyRO := by
  cases m <;> simp only [CaptureSet.applyMut_epsilon, CaptureSet.applyMut_ro, applyRO_applyRO]

/-- applyRO distributes over rename. -/
theorem CaptureSet.applyRO_rename {cs : CaptureSet s1} {f : Rename s1 s2} :
    cs.applyRO.rename f = (cs.rename f).applyRO := by
  induction cs with
  | empty => rfl
  | union cs1 cs2 ih1 ih2 =>
    simp only [CaptureSet.applyRO_union, CaptureSet.rename, ih1, ih2]
  | var a x => simp only [CaptureSet.rename, CaptureSet.applyRO]
  | cvar a x => simp only [CaptureSet.rename, CaptureSet.applyRO]

/-- applyMut distributes over rename. -/
theorem CaptureSet.applyMut_rename {cs : CaptureSet s1} {f : Rename s1 s2} {m : Mutability} :
    (cs.applyMut m).rename f = (cs.rename f).applyMut m := by
  cases m <;> simp only [CaptureSet.applyMut_epsilon, CaptureSet.applyMut_ro, applyRO_rename]

/-- Sets every element of a capture set to `drop` mode. -/
def CaptureSet.applyDrop : CaptureSet s -> CaptureSet s
| .empty => .empty
| .union cs1 cs2 => .union (cs1.applyDrop) (cs2.applyDrop)
| .var _ x => .var .drop x
| .cvar _ x => .cvar .drop x

/-- Applies an access mode to all elements: a mutability acts via `applyMut`,
    while `drop` sets every element to `drop` mode via `applyDrop`. -/
def CaptureSet.applyAccess (a : Access) (cs : CaptureSet s) : CaptureSet s :=
  match a with
  | .M m => cs.applyMut m
  | .drop => cs.applyDrop

@[simp] theorem CaptureSet.applyAccess_M {m : Mutability} {cs : CaptureSet s} :
    cs.applyAccess (.M m) = cs.applyMut m := rfl
@[simp] theorem CaptureSet.applyAccess_drop {cs : CaptureSet s} :
    cs.applyAccess .drop = cs.applyDrop := rfl

/-- applyDrop distributes over rename. -/
theorem CaptureSet.applyDrop_rename {cs : CaptureSet s1} {f : Rename s1 s2} :
    cs.applyDrop.rename f = (cs.rename f).applyDrop := by
  induction cs with
  | empty => rfl
  | union cs1 cs2 ih1 ih2 => simp only [CaptureSet.applyDrop, CaptureSet.rename, ih1, ih2]
  | var _ x => simp only [CaptureSet.applyDrop, CaptureSet.rename]
  | cvar _ x => simp only [CaptureSet.applyDrop, CaptureSet.rename]

/-- applyAccess distributes over rename. -/
theorem CaptureSet.applyAccess_rename {cs : CaptureSet s1} {f : Rename s1 s2} {a : Access} :
    (cs.applyAccess a).rename f = (cs.rename f).applyAccess a := by
  cases a with
  | M m => simp only [CaptureSet.applyAccess_M, applyMut_rename]
  | drop => simp only [CaptureSet.applyAccess_drop, applyDrop_rename]

/-- applyRO leaves a dropped capture set unchanged (`drop` is fixed under applyRO). -/
@[simp] theorem CaptureSet.applyDrop_applyRO {cs : CaptureSet s} :
    cs.applyDrop.applyRO = cs.applyDrop := by
  induction cs with
  | empty => rfl
  | union cs1 cs2 ih1 ih2 => simp only [CaptureSet.applyDrop, CaptureSet.applyRO, ih1, ih2]
  | var _ x => rfl
  | cvar _ x => rfl

/-- applyRO commutes with applyAccess by reading off the read-only image of the mode. -/
theorem CaptureSet.applyAccess_applyRO {cs : CaptureSet s} {a : Access} :
    (cs.applyAccess a).applyRO = cs.applyAccess a.applyRO := by
  cases a with
  | M m =>
    cases m with
    | epsilon =>
      simp only [CaptureSet.applyAccess_M, Access.applyRO, applyMut_epsilon, applyMut_ro]
    | ro =>
      simp only [CaptureSet.applyAccess_M, Access.applyRO, applyMut_ro, applyRO_applyRO]
  | drop => simp only [CaptureSet.applyAccess_drop, Access.applyRO, applyDrop_applyRO]

/-- applyDrop overwrites every mode, so it absorbs a preceding applyRO. -/
@[simp] theorem CaptureSet.applyRO_applyDrop {cs : CaptureSet s} :
    cs.applyRO.applyDrop = cs.applyDrop := by
  induction cs with
  | empty => rfl
  | union cs1 cs2 ih1 ih2 => simp only [CaptureSet.applyRO, CaptureSet.applyDrop, ih1, ih2]
  | var _ x => rfl
  | cvar _ x => rfl

/-- applyDrop is idempotent. -/
@[simp] theorem CaptureSet.applyDrop_applyDrop {cs : CaptureSet s} :
    cs.applyDrop.applyDrop = cs.applyDrop := by
  induction cs with
  | empty => rfl
  | union cs1 cs2 ih1 ih2 => simp only [CaptureSet.applyDrop, ih1, ih2]
  | var _ x => rfl
  | cvar _ x => rfl

/-- applyDrop absorbs a preceding applyAccess (it overwrites every mode). -/
@[simp] theorem CaptureSet.applyAccess_applyDrop {cs : CaptureSet s} {a : Access} :
    (cs.applyAccess a).applyDrop = cs.applyDrop := by
  cases a with
  | M m =>
    cases m with
    | epsilon => simp only [CaptureSet.applyAccess_M, applyMut_epsilon]
    | ro => simp only [CaptureSet.applyAccess_M, applyMut_ro, applyRO_applyDrop]
  | drop => simp only [CaptureSet.applyAccess_drop, applyDrop_applyDrop]

/-- The subset relation on capture sets. -/
inductive CaptureSet.Subset : CaptureSet s -> CaptureSet s -> Prop where
| refl :
  --------------------
  Subset C C
| empty :
  --------------------
  Subset .empty C
| union_left :
  Subset C1 C ->
  Subset C2 C ->
  --------------------
  Subset (C1.union C2) C
| union_right_left :
  Subset C C1 ->
  --------------------
  Subset C (C1.union C2)
| union_right_right {C1 : CaptureSet s} :
  Subset C C2 ->
  --------------------
  Subset C (C1.union C2)

/-- Provides `⊆` notation for capture set subset. -/
instance CaptureSet.instHasSubset : HasSubset (CaptureSet s) where
  Subset := CaptureSet.Subset

/-- A variable is closed if it contains no heap pointers. -/
inductive Var.IsClosed : Var k s -> Prop where
| bound : Var.IsClosed (.bound x)

/-- A capture set is closed if it contains no heap pointers. -/
inductive CaptureSet.IsClosed : CaptureSet s -> Prop where
| empty : CaptureSet.IsClosed .empty
| union : CaptureSet.IsClosed cs1 -> CaptureSet.IsClosed cs2 ->
    CaptureSet.IsClosed (cs1.union cs2)
| cvar : CaptureSet.IsClosed (.cvar m x)
| var_bound : CaptureSet.IsClosed (.var m (.bound x))

/-- applyRO preserves closedness. -/
theorem CaptureSet.applyRO_isClosed {cs : CaptureSet s}
    (hc : cs.IsClosed) : cs.applyRO.IsClosed := by
  induction cs with
  | empty => exact IsClosed.empty
  | union cs1 cs2 ih1 ih2 =>
    cases hc with | union h1 h2 =>
    exact IsClosed.union (ih1 h1) (ih2 h2)
  | var m' x =>
    cases hc with | var_bound =>
    exact IsClosed.var_bound
  | cvar m' c =>
    exact IsClosed.cvar

/-- applyMut preserves closedness. -/
theorem CaptureSet.applyMut_isClosed {cs : CaptureSet s} {m : Mutability}
    (hc : cs.IsClosed) : (cs.applyMut m).IsClosed := by
  cases m
  · exact hc
  · exact applyRO_isClosed hc

/-- Renaming preserves closedness of a capture set. -/
theorem CaptureSet.rename_isClosed {cs : CaptureSet s1} {f : Rename s1 s2}
    (hc : cs.IsClosed) : (cs.rename f).IsClosed := by
  induction cs with
  | empty => exact IsClosed.empty
  | union cs1 cs2 ih1 ih2 =>
    cases hc with | union h1 h2 =>
    simp only [CaptureSet.rename]
    exact IsClosed.union (ih1 h1) (ih2 h2)
  | var m' x =>
    cases hc with | var_bound =>
    simp only [CaptureSet.rename, Var.rename]
    exact IsClosed.var_bound
  | cvar m' c =>
    simp only [CaptureSet.rename]
    exact IsClosed.cvar

/-- Drops the outermost bound variable from a capture set. -/
def CaptureSet.drop_here_var : CaptureSet (s,x) -> CaptureSet s
| .empty => .empty
| .union cs1 cs2 => .union (cs1.drop_here_var) (cs2.drop_here_var)
| .var _ (.bound .here) => .empty
| .var m (.bound (.there x)) => .var m (.bound x)
| .var m (.free n) => .var m (.free n)
| .cvar m (.there c) => .cvar m c

def CaptureSet.drop_here_tvar : CaptureSet (s,X) -> CaptureSet s
| .empty => .empty
| .union cs1 cs2 => .union (cs1.drop_here_tvar) (cs2.drop_here_tvar)
| .var m (.free x) => .var m (.free x)
| .var m (.bound (.there x)) => .var m (.bound x)
| .cvar m (.there c) => .cvar m c

/-- Whether a capture set contains only peaks (capture variables). -/
inductive CaptureSet.PeaksOnly : CaptureSet s -> Prop where
| empty :
  ---------------------
  PeaksOnly .empty
| union {C1 C2 : CaptureSet s} :
  PeaksOnly C1 ->
  PeaksOnly C2 ->
  ---------------------
  PeaksOnly (C1.union C2)
| cvar {m : Access} {c : BVar s .cvar} :
  ---------------------
  PeaksOnly (.cvar m c)

structure PeakSet (s : Sig) where
  cs : CaptureSet s
  h : cs.PeaksOnly

/-- PeaksOnly is preserved under renaming. -/
theorem CaptureSet.PeaksOnly.rename {cs : CaptureSet s} (h : cs.PeaksOnly) (ρ : Rename s s') :
    (cs.rename ρ).PeaksOnly := by
  induction h with
  | empty => exact PeaksOnly.empty
  | union _ _ ih1 ih2 => exact PeaksOnly.union ih1 ih2
  | cvar => exact PeaksOnly.cvar

/-- PeaksOnly is preserved under applyRO. -/
theorem CaptureSet.PeaksOnly.applyRO {cs : CaptureSet s} (h : cs.PeaksOnly) :
    cs.applyRO.PeaksOnly := by
  induction h with
  | empty => exact PeaksOnly.empty
  | union _ _ ih1 ih2 => exact PeaksOnly.union ih1 ih2
  | cvar => exact PeaksOnly.cvar

/-- PeaksOnly is preserved under applyMut. -/
theorem CaptureSet.PeaksOnly.applyMut {cs : CaptureSet s} (h : cs.PeaksOnly) (m : Mutability) :
    (cs.applyMut m).PeaksOnly := by
  cases m with
  | epsilon => exact h
  | ro => exact h.applyRO

/-- PeaksOnly is preserved under applyDrop. -/
theorem CaptureSet.PeaksOnly.applyDrop {cs : CaptureSet s} (h : cs.PeaksOnly) :
    cs.applyDrop.PeaksOnly := by
  induction h with
  | empty => exact PeaksOnly.empty
  | union _ _ ih1 ih2 => exact PeaksOnly.union ih1 ih2
  | cvar => exact PeaksOnly.cvar

/-- PeaksOnly is preserved under applyAccess. -/
theorem CaptureSet.PeaksOnly.applyAccess {cs : CaptureSet s} (h : cs.PeaksOnly) (a : Access) :
    (cs.applyAccess a).PeaksOnly := by
  cases a with
  | M m => exact h.applyMut m
  | drop => exact h.applyDrop

def PeakSet.rename {s1 s2 : Sig} (ps : PeakSet s1) (ρ : Rename s1 s2) : PeakSet s2 :=
  ⟨ps.cs.rename ρ, ps.h.rename ρ⟩

/-- Whether this capture set is equivalent to an empty set. -/
inductive CaptureSet.IsEmpty : CaptureSet s -> Prop where
| empty :
  ----------------
  IsEmpty .empty
| union :
  IsEmpty cs1 ->
  IsEmpty cs2 ->
  ----------------
  IsEmpty (cs1.union cs2)

/-- Renaming preserves emptiness. -/
theorem CaptureSet.IsEmpty.rename {cs : CaptureSet s1} (h : cs.IsEmpty) (ρ : Rename s1 s2) :
    (cs.rename ρ).IsEmpty := by
  induction h with
  | empty => exact IsEmpty.empty
  | union _ _ ih1 ih2 => exact IsEmpty.union ih1 ih2

/-- The subset relation on capture sets. -/
inductive CaptureSet.CoveredBy : CaptureSet s -> CaptureSet s -> Prop where
| refl {C : CaptureSet s} {m1 m2 : Mutability} :
  (hm : m1 ≤ m2) ->
  --------------------
  CoveredBy (C.applyMut m1) (C.applyMut m2)
| empty :
  --------------------
  CoveredBy .empty C
| union_left :
  CoveredBy C1 C ->
  CoveredBy C2 C ->
  --------------------
  CoveredBy (C1.union C2) C
| union_right_left :
  CoveredBy C C1 ->
  --------------------
  CoveredBy C (C1.union C2)
| union_right_right {C1 : CaptureSet s} :
  CoveredBy C C2 ->
  --------------------
  CoveredBy C (C1.union C2)

namespace CaptureSet.CoveredBy

-- Helper: reflexivity for CoveredBy (any C covers itself)
theorem refl' {C : CaptureSet s} : C.CoveredBy C := by
  have h : (C.applyMut .epsilon).CoveredBy (C.applyMut .epsilon) := .refl Mutability.Le.refl
  simp only [CaptureSet.applyMut_epsilon] at h
  exact h

theorem mut_mono_left {C1 C2 : CaptureSet s} {m1 m2 : Mutability}
  (hm : m1 ≤ m2)
  (hsub : CaptureSet.CoveredBy (C1.applyMut m2) C2) :
    CaptureSet.CoveredBy (C1.applyMut m1) C2 := by
  cases hm with
  | refl => exact hsub
  | ro_eps =>
    -- m1 = .ro, m2 = .epsilon
    -- hsub : C1.CoveredBy C2
    -- Goal: C1.applyRO.CoveredBy C2
    simp only [CaptureSet.applyMut_epsilon] at hsub
    simp only [CaptureSet.applyMut_ro]
    induction hsub with
    | refl hm' =>
      simp only [CaptureSet.applyMut_applyRO]
      exact .refl Mutability.Le.ro_le
    | empty =>
      simp only [CaptureSet.applyRO]
      exact .empty
    | union_left _ _ ih1 ih2 =>
      simp only [CaptureSet.applyRO]
      exact .union_left ih1 ih2
    | union_right_left _ ih =>
      exact .union_right_left ih
    | union_right_right _ ih =>
      exact .union_right_right ih

-- General helper: extract from union equality
private theorem union_coveredby_left_aux {AB A B C : CaptureSet s}
  (he : A.union B = AB)
  (h : AB.CoveredBy C) : A.CoveredBy C := by
  induction h generalizing A B with
  | refl hm =>
    rename_i D m1 m2
    -- he : A.union B = D.applyMut m1
    -- Goal: A.CoveredBy (D.applyMut m2)
    cases m1 with
    | epsilon =>
      simp only [CaptureSet.applyMut_epsilon] at he
      subst he
      -- Goal: A.CoveredBy ((A.union B).applyMut m2)
      cases hm with
      | refl =>
        simp only [CaptureSet.applyMut_epsilon]
        exact .union_right_left refl'
    | ro =>
      simp only [CaptureSet.applyMut_ro] at he
      -- he : A.union B = D.applyRO
      -- Case split on D to handle the equality
      cases D with
      | empty =>
        simp only [CaptureSet.applyRO] at he
        contradiction
      | union D1 D2 =>
        simp only [CaptureSet.applyRO] at he
        injection he with hA hB
        subst hA
        -- Goal: D1.applyRO.CoveredBy ((D1.union D2).applyMut m2)
        cases m2 with
        | epsilon =>
          simp only [CaptureSet.applyMut_epsilon]
          -- Goal: D1.applyRO.CoveredBy (D1.union D2)
          have h1 : D1.applyRO.CoveredBy D1 := .refl Mutability.Le.ro_eps
          exact .union_right_left h1
        | ro =>
          simp only [CaptureSet.applyMut_ro, CaptureSet.applyRO]
          exact .union_right_left refl'
      | var m x =>
        simp only [CaptureSet.applyRO] at he
        contradiction
      | cvar m c =>
        simp only [CaptureSet.applyRO] at he
        contradiction
  | empty =>
    contradiction
  | union_left h1 _ _ _ =>
    injection he with hA _
    subst hA
    exact h1
  | union_right_left _ ih =>
    exact .union_right_left (ih he)
  | union_right_right _ ih =>
    exact .union_right_right (ih he)

-- Helper: if a union is covered by C, so is the left component
theorem union_coveredby_left {A B C : CaptureSet s}
  (h : (A ∪ B).CoveredBy C) : A.CoveredBy C :=
  union_coveredby_left_aux rfl h

-- General helper: extract from union equality (right component)
private theorem union_coveredby_right_aux {AB A B C : CaptureSet s}
  (he : A.union B = AB)
  (h : AB.CoveredBy C) : B.CoveredBy C := by
  induction h generalizing A B with
  | refl hm =>
    rename_i D m1 m2
    cases m1 with
    | epsilon =>
      simp only [CaptureSet.applyMut_epsilon] at he
      subst he
      cases hm with
      | refl =>
        simp only [CaptureSet.applyMut_epsilon]
        exact .union_right_right refl'
    | ro =>
      simp only [CaptureSet.applyMut_ro] at he
      cases D with
      | empty =>
        simp only [CaptureSet.applyRO] at he
        contradiction
      | union D1 D2 =>
        simp only [CaptureSet.applyRO] at he
        injection he with _ hB
        subst hB
        cases m2 with
        | epsilon =>
          simp only [CaptureSet.applyMut_epsilon]
          have h1 : D2.applyRO.CoveredBy D2 := .refl Mutability.Le.ro_eps
          exact .union_right_right h1
        | ro =>
          simp only [CaptureSet.applyMut_ro, CaptureSet.applyRO]
          exact .union_right_right refl'
      | var m x =>
        simp only [CaptureSet.applyRO] at he
        contradiction
      | cvar m c =>
        simp only [CaptureSet.applyRO] at he
        contradiction
  | empty =>
    contradiction
  | union_left _ h2 _ _ =>
    injection he with _ hB
    subst hB
    exact h2
  | union_right_left _ ih =>
    exact .union_right_left (ih he)
  | union_right_right _ ih =>
    exact .union_right_right (ih he)

-- Helper: if a union is covered by C, so is the right component
theorem union_coveredby_right {A B C : CaptureSet s}
  (h : (A ∪ B).CoveredBy C) : B.CoveredBy C :=
  union_coveredby_right_aux rfl h

theorem trans {C1 C2 C3 : CaptureSet s}
  (h1 : C1.CoveredBy C2) (h2 : C2.CoveredBy C3) : C1.CoveredBy C3 := by
  induction h1 generalizing C3 with
  | refl hm1 =>
    -- C1 = D.applyMut m1, C2 = D.applyMut m2, hm1 : m1 ≤ m2
    -- h2 : (D.applyMut m2).CoveredBy C3
    -- Goal: (D.applyMut m1).CoveredBy C3
    exact mut_mono_left hm1 h2
  | empty => exact empty
  | union_left _ _ ih1 ih2 =>
    -- C1 = C1a ∪ C1b
    -- Goal: (C1a ∪ C1b).CoveredBy C3
    exact .union_left (ih1 h2) (ih2 h2)
  | union_right_left _ ih =>
    -- C2 = C1' ∪ C2' where original h1 came from C1.CoveredBy C1'
    -- h2 : (C1' ∪ C2').CoveredBy C3
    -- ih : C1'.CoveredBy C3 → C1.CoveredBy C3
    exact ih (union_coveredby_left h2)
  | union_right_right _ ih =>
    -- C2 = C1' ∪ C2' where original h1 came from C1.CoveredBy C2'
    -- h2 : (C1' ∪ C2').CoveredBy C3
    -- ih : C2'.CoveredBy C3 → C1.CoveredBy C3
    exact ih (union_coveredby_right h2)

-- Helper: rename preserves CoveredBy
theorem rename {C1 C2 : CaptureSet s1} {f : Rename s1 s2}
  (hcov : C1.CoveredBy C2) : (C1.rename f).CoveredBy (C2.rename f) := by
  induction hcov with
  | refl hm =>
    simp only [CaptureSet.applyMut_rename]
    exact .refl hm
  | empty =>
    simp only [CaptureSet.rename]
    exact .empty
  | union_left _ _ ih1 ih2 =>
    simp only [CaptureSet.rename]
    exact .union_left ih1 ih2
  | union_right_left _ ih =>
    simp only [CaptureSet.rename]
    exact .union_right_left ih
  | union_right_right _ ih =>
    simp only [CaptureSet.rename]
    exact .union_right_right ih

-- Helper: applyRO preserves CoveredBy
theorem applyRO_mono {C1 C2 : CaptureSet s}
  (hcov : C1.CoveredBy C2) : C1.applyRO.CoveredBy C2.applyRO := by
  induction hcov with
  | refl hm =>
    simp only [CaptureSet.applyMut_applyRO]
    exact refl'
  | empty =>
    simp only [CaptureSet.applyRO]
    exact .empty
  | union_left _ _ ih1 ih2 =>
    simp only [CaptureSet.applyRO]
    exact .union_left ih1 ih2
  | union_right_left _ ih =>
    simp only [CaptureSet.applyRO]
    exact .union_right_left ih
  | union_right_right _ ih =>
    simp only [CaptureSet.applyRO]
    exact .union_right_right ih

-- Helper: applyMut preserves CoveredBy
theorem applyMut_mono {C1 C2 : CaptureSet s} {m : Mutability}
  (hcov : C1.CoveredBy C2) : (C1.applyMut m).CoveredBy (C2.applyMut m) := by
  cases m with
  | epsilon => simp only [CaptureSet.applyMut_epsilon]; exact hcov
  | ro => simp only [CaptureSet.applyMut_ro]; exact hcov.applyRO_mono

/-- Helper: if (.cvar a c) ⊆ D, then (.cvar a.applyRO c) ⊆ D.applyRO -/
private theorem cvar_subset_applyRO {a : Access} {c : BVar s .cvar} {D : CaptureSet s}
  (hsub : (.cvar a c) ⊆ D) : (.cvar a.applyRO c) ⊆ D.applyRO := by
  induction D with
  | empty => cases hsub
  | union D1 D2 ih1 ih2 =>
    simp only [CaptureSet.applyRO]
    cases hsub with
    | union_right_left h => exact .union_right_left (ih1 h)
    | union_right_right h => exact .union_right_right (ih2 h)
  | var _ _ => cases hsub
  | cvar m' c' =>
    cases hsub
    simp only [CaptureSet.applyRO]
    exact .refl

/-- Helper: a cvar inside `D.applyRO` comes from an original cvar in `D`, and its
    mode is the read-only image of that original mode. -/
private theorem cvar_subset_of_applyRO {a : Access} {c : BVar s .cvar} {D : CaptureSet s}
  (hsub : (.cvar a c) ⊆ D.applyRO) : ∃ a0, (.cvar a0 c) ⊆ D ∧ a = a0.applyRO := by
  induction D with
  | empty =>
    simp only [CaptureSet.applyRO] at hsub
    cases hsub
  | union D1 D2 ih1 ih2 =>
    simp only [CaptureSet.applyRO] at hsub
    cases hsub with
    | union_right_left h =>
      obtain ⟨a0, hm, he⟩ := ih1 h
      exact ⟨a0, .union_right_left hm, he⟩
    | union_right_right h =>
      obtain ⟨a0, hm, he⟩ := ih2 h
      exact ⟨a0, .union_right_right hm, he⟩
  | var m' x =>
    simp only [CaptureSet.applyRO] at hsub
    cases hsub
  | cvar m' c' =>
    simp only [CaptureSet.applyRO] at hsub
    cases hsub
    exact ⟨m', .refl, rfl⟩

/-- If a cvar is a subset of C1 and C1 is covered by C2, then the cvar (possibly with
    a weaker access mode) is a subset of C2. -/
theorem cvar_subset_coveredby {a : Access} {c : BVar s .cvar} {C1 C2 : CaptureSet s}
  (hsub : (.cvar a c) ⊆ C1)
  (hcov : C1.CoveredBy C2) :
  ∃ a', a ≤ a' ∧ (.cvar a' c) ⊆ C2 := by
  induction hcov generalizing a with
  | refl hm =>
    rename_i D m1 m2
    cases m1 with
    | epsilon =>
      simp only [CaptureSet.applyMut_epsilon] at hsub
      cases m2 with
      | epsilon =>
        simp only [CaptureSet.applyMut_epsilon]
        exact ⟨a, Access.Le.refl, hsub⟩
      | ro =>
        -- hm : .epsilon ≤ .ro is false, this case is impossible
        cases hm
    | ro =>
      simp only [CaptureSet.applyMut_ro] at hsub
      cases m2 with
      | epsilon =>
        simp only [CaptureSet.applyMut_epsilon]
        obtain ⟨a0, h, he⟩ := cvar_subset_of_applyRO hsub
        subst he
        exact ⟨a0, Access.applyRO_le, h⟩
      | ro =>
        simp only [CaptureSet.applyMut_ro]
        exact ⟨a, Access.Le.refl, hsub⟩
  | empty =>
    cases hsub
  | union_left _ _ ih1 ih2 =>
    cases hsub with
    | union_right_left hsub' => exact ih1 hsub'
    | union_right_right hsub' => exact ih2 hsub'
  | union_right_left _ ih =>
    obtain ⟨a', hle, hsub'⟩ := ih hsub
    exact ⟨a', hle, .union_right_left hsub'⟩
  | union_right_right _ ih =>
    obtain ⟨a', hle, hsub'⟩ := ih hsub
    exact ⟨a', hle, .union_right_right hsub'⟩

end CaptureSet.CoveredBy

end Consume
