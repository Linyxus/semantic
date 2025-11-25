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

/-- Applies read-only mutability to all elements in a capture set. -/
def CaptureSet.applyRO : CaptureSet s -> CaptureSet s
| .empty => .empty
| .union cs1 cs2 => .union (cs1.applyRO) (cs2.applyRO)
| .var _ x => .var .ro x
| .cvar _ x => .cvar .ro x

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
@[simp] theorem CaptureSet.applyRO_var {m : Mutability} {x : Var .var s} :
    (CaptureSet.var m x).applyRO = .var .ro x := rfl
@[simp] theorem CaptureSet.applyRO_cvar {m : Mutability} {x : BVar s .cvar} :
    (CaptureSet.cvar m x).applyRO = .cvar .ro x := rfl

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
  | union cs1 cs2 ih1 ih2 => simp [ih1, ih2]
  | var _ x => rfl
  | cvar _ x => rfl

/-- Applying applyMut after applyRO simplifies. -/
@[simp]
theorem CaptureSet.applyRO_applyMut {cs : CaptureSet s} {m : Mutability} :
    cs.applyRO.applyMut m = cs.applyRO := by
  cases m <;> simp [applyRO_applyRO]

/-- Applying applyRO after applyMut gives applyRO. -/
@[simp]
theorem CaptureSet.applyMut_applyRO {cs : CaptureSet s} {m : Mutability} :
    (cs.applyMut m).applyRO = cs.applyRO := by
  cases m <;> simp [applyRO_applyRO]

/-- applyRO distributes over rename. -/
theorem CaptureSet.applyRO_rename {cs : CaptureSet s1} {f : Rename s1 s2} :
    cs.applyRO.rename f = (cs.rename f).applyRO := by
  induction cs with
  | empty => rfl
  | union cs1 cs2 ih1 ih2 => simp [rename, ih1, ih2]
  | var _ x => simp [rename]
  | cvar _ x => simp [rename]

/-- applyMut distributes over rename. -/
theorem CaptureSet.applyMut_rename {cs : CaptureSet s1} {f : Rename s1 s2} {m : Mutability} :
    (cs.applyMut m).rename f = (cs.rename f).applyMut m := by
  cases m <;> simp [applyRO_rename]

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
  cases m <;> simp [applyRO_isClosed hc, hc]

end Capybara
