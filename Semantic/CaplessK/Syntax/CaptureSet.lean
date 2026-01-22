import Semantic.CaplessK.Debruijn
import Semantic.CaplessK.Syntax.Classifier

/-!
This module defines the capture set syntax of CC.
-/

namespace CaplessK

/-- A variable, either bound (de Bruijn indexed) or free (heap pointer). -/
inductive Var : Kind -> Sig -> Type where
| bound : BVar s k -> Var k s
| free : Nat -> Var k s

/-- A set of captured variables. -/
inductive CaptureSet : Sig -> Type where
| empty : CaptureSet s
| union : CaptureSet s -> CaptureSet s -> CaptureSet s
| var : Var .var s -> CapKind -> CaptureSet s
| cvar : BVar s .cvar -> CapKind -> CaptureSet s

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
| .var x, ρ => .var (x.rename ρ)
| .cvar x, ρ => .cvar (ρ.var x)

/-- Renaming by the identity renaming leaves a capture set unchanged. -/
theorem CaptureSet.rename_id {cs : CaptureSet s} :
    cs.rename (Rename.id) = cs := by
  induction cs
  case empty => rfl
  case union ih1 ih2 => simp [CaptureSet.rename, ih1, ih2]
  case var x => cases x <;> rfl
  case cvar x => simp [CaptureSet.rename, Rename.id]

/-- Renaming distributes over composition of renamings. -/
theorem CaptureSet.rename_comp {cs : CaptureSet s1} {f : Rename s1 s2} {g : Rename s2 s3} :
    (cs.rename f).rename g = cs.rename (f.comp g) := by
  induction cs generalizing s2 s3
  case empty => rfl
  case union ih1 ih2 => simp [CaptureSet.rename, ih1, ih2]
  case var x =>
    cases x
    · simp [CaptureSet.rename, Var.rename]; rfl
    · simp [CaptureSet.rename, Var.rename]
  case cvar x => simp [CaptureSet.rename, Rename.comp]

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
| cvar : CaptureSet.IsClosed (.cvar x)
| var_bound : CaptureSet.IsClosed (.var (.bound x))

end CaplessK
