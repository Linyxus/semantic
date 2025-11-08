import Semantic.CC.Debruijn

/-!
This module defines the capture set syntax of CC.
-/

namespace CC

inductive Var : Kind -> Sig -> Type where
| bound : BVar s k -> Var k s
| free : Nat -> Var k s

inductive CaptureSet : Sig -> Type where
| empty : CaptureSet s
| union : CaptureSet s -> CaptureSet s -> CaptureSet s
| var : Var .var s -> CaptureSet s
| cvar : BVar s .cvar -> CaptureSet s

@[simp]
instance CaptureSet.instEmptyCollection :
  EmptyCollection (CaptureSet s) where
  emptyCollection := CaptureSet.empty

@[simp]
instance CaptureSet.instUnion : Union (CaptureSet s) where
  union := CaptureSet.union

def Var.rename : Var k s1 -> Rename s1 s2 -> Var k s2
| .bound x, f => .bound (f.var x)
| .free n, _ => .free n

def CaptureSet.rename : CaptureSet s1 -> Rename s1 s2 -> CaptureSet s2
| .empty, _ => .empty
| .union cs1 cs2, ρ => .union (cs1.rename ρ) (cs2.rename ρ)
| .var x, ρ => .var (x.rename ρ)
| .cvar x, ρ => .cvar (ρ.var x)

theorem CaptureSet.rename_id {cs : CaptureSet s} :
    cs.rename (Rename.id) = cs := by
  induction cs
  case empty => rfl
  case union ih1 ih2 => simp [CaptureSet.rename, ih1, ih2]
  case var x => cases x <;> rfl
  case cvar x => simp [CaptureSet.rename, Rename.id]

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

instance CaptureSet.instHasSubset : HasSubset (CaptureSet s) where
  Subset := CaptureSet.Subset

/-- Closedness judgements. A syntax construct is closed if it contains no heap pointers. -/

inductive Var.IsClosed : Var k s -> Prop where
| bound : Var.IsClosed (.bound x)

inductive CaptureSet.IsClosed : CaptureSet s -> Prop where
| empty : CaptureSet.IsClosed .empty
| union : CaptureSet.IsClosed cs1 -> CaptureSet.IsClosed cs2 ->
    CaptureSet.IsClosed (cs1.union cs2)
| cvar : CaptureSet.IsClosed (.cvar x)
| var_bound : CaptureSet.IsClosed (.var (.bound x))

end CC
