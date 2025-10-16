import Semantic.CC.Debruijn
namespace CC

inductive Var : Kind -> Sig -> Type where
| bound : BVar s k -> Var k s
| free : Nat -> Var k s

inductive CaptureSet : Sig -> Type where
| empty : CaptureSet s
| union : CaptureSet s -> CaptureSet s -> CaptureSet s
| var : Var .var s -> CaptureSet s
| cvar : Var .cvar s -> CaptureSet s

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
| .cvar x, ρ => .cvar (x.rename ρ)

theorem CaptureSet.rename_id {cs : CaptureSet s} :
    cs.rename (Rename.id) = cs := by
  induction cs
  case empty => rfl
  case union ih1 ih2 => simp [CaptureSet.rename, ih1, ih2]
  case var x => cases x <;> rfl
  case cvar x => cases x <;> rfl

theorem CaptureSet.rename_comp {cs : CaptureSet s1} {f : Rename s1 s2} {g : Rename s2 s3} :
    (cs.rename f).rename g = cs.rename (f.comp g) := by
  induction cs generalizing s2 s3
  case empty => rfl
  case union ih1 ih2 => simp [CaptureSet.rename, ih1, ih2]
  case var x =>
    cases x
    · simp [CaptureSet.rename, Var.rename]; rfl
    · simp [CaptureSet.rename, Var.rename]
  case cvar x =>
    cases x
    · simp [CaptureSet.rename, Var.rename]; rfl
    · simp [CaptureSet.rename, Var.rename]

end CC
