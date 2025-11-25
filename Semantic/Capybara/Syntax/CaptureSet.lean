import Semantic.Capybara.Debruijn

/-!
This module defines the capture set syntax of CC.
-/

namespace Capybara

/-- Mutability mode for captured variables: read-write (epsilon) or read-only (ro). -/
inductive Mutability : Type where
| epsilon : Mutability  -- default mode, read-write
| ro : Mutability       -- read-only

/-- A variable, either bound (de Bruijn indexed) or free (heap pointer). -/
inductive Var : Kind -> Sig -> Type where
| bound : BVar s k -> Var k s
| free : Nat -> Var k s

/-- A set of captured variables. -/
inductive CaptureSet : Sig -> Type where
| empty : CaptureSet s
| union : CaptureSet s -> CaptureSet s -> CaptureSet s
| var : Mutability -> Var .var s -> CaptureSet s
| cvar : Mutability -> BVar s .cvar -> CaptureSet s

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
  case union ih1 ih2 => simp [CaptureSet.rename, ih1, ih2]
  case var m x => cases x <;> rfl
  case cvar m x => simp [CaptureSet.rename, Rename.id]

/-- Renaming distributes over composition of renamings. -/
theorem CaptureSet.rename_comp {cs : CaptureSet s1} {f : Rename s1 s2} {g : Rename s2 s3} :
    (cs.rename f).rename g = cs.rename (f.comp g) := by
  induction cs generalizing s2 s3
  case empty => rfl
  case union ih1 ih2 => simp [CaptureSet.rename, ih1, ih2]
  case var m x =>
    cases x
    · simp [CaptureSet.rename, Var.rename]; rfl
    · simp [CaptureSet.rename, Var.rename]
  case cvar m x => simp [CaptureSet.rename, Rename.comp]

/-- Applies a mutability to all elements in a capture set.
  This is used to preserve mutability during substitution. -/
def CaptureSet.applyMut (m : Mutability) : CaptureSet s -> CaptureSet s
| .empty => .empty
| .union cs1 cs2 => .union (cs1.applyMut m) (cs2.applyMut m)
| .var _ x => .var m x
| .cvar _ x => .cvar m x

/-- applyMut on a singleton cvar. -/
@[simp]
theorem CaptureSet.applyMut_cvar {m m' : Mutability} {x : BVar s .cvar} :
    (CaptureSet.cvar m' x).applyMut m = .cvar m x := rfl

/-- applyMut on a singleton var. -/
@[simp]
theorem CaptureSet.applyMut_var {m m' : Mutability} {x : Var .var s} :
    (CaptureSet.var m' x).applyMut m = .var m x := rfl

/-- applyMut on empty. -/
@[simp]
theorem CaptureSet.applyMut_empty {m : Mutability} :
    (CaptureSet.empty (s:=s)).applyMut m = .empty := rfl

/-- applyMut on union. -/
@[simp]
theorem CaptureSet.applyMut_union {m : Mutability} {cs1 cs2 : CaptureSet s} :
    (cs1.union cs2).applyMut m = (cs1.applyMut m).union (cs2.applyMut m) := rfl

/-- Applying applyMut twice simplifies to the outer application. -/
@[simp]
theorem CaptureSet.applyMut_applyMut {cs : CaptureSet s} {m m' : Mutability} :
    (cs.applyMut m').applyMut m = cs.applyMut m := by
  induction cs with
  | empty => rfl
  | union cs1 cs2 ih1 ih2 => simp [applyMut, ih1, ih2]
  | var _ x => rfl
  | cvar _ x => rfl

/-- applyMut distributes over rename. -/
theorem CaptureSet.applyMut_rename {cs : CaptureSet s1} {f : Rename s1 s2} {m : Mutability} :
    (cs.applyMut m).rename f = (cs.rename f).applyMut m := by
  induction cs with
  | empty => rfl
  | union cs1 cs2 ih1 ih2 => simp [applyMut, rename, ih1, ih2]
  | var _ x => simp [applyMut, rename]
  | cvar _ x => simp [applyMut, rename]

/-- The subset relation on capture sets. -/
inductive CaptureSet.Subset : CaptureSet s -> CaptureSet s -> Prop where
| refl :
  --------------------
  Subset C C
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

/-- applyMut preserves closedness. -/
theorem CaptureSet.applyMut_isClosed {cs : CaptureSet s} {m : Mutability}
    (hc : cs.IsClosed) : (cs.applyMut m).IsClosed := by
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

end Capybara
