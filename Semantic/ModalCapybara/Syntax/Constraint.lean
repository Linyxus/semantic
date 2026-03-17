import Semantic.ModalCapybara.Syntax.CaptureSet

namespace ModalCapybara

/-- A separation constraint. -/
inductive Constraint : Sig -> Type where
| empty : Constraint s
| cons :
  Constraint s ->
  CaptureSet s ->
  Mutability ->
  Constraint s

/-- Applies a renaming to all bound variables in a constraint. -/
def Constraint.rename : Constraint s1 -> Rename s1 s2 -> Constraint s2
| .empty, _ => .empty
| .cons K C m, ρ => .cons (K.rename ρ) (C.rename ρ) m

/-- Renaming by the identity renaming leaves a constraint unchanged. -/
theorem Constraint.rename_id {K : Constraint s} :
    K.rename Rename.id = K := by
  induction K with
  | empty => rfl
  | cons K C m ih =>
    simp [Constraint.rename, ih, CaptureSet.rename_id]

/-- Renaming distributes over composition of renamings. -/
theorem Constraint.rename_comp
    {K : Constraint s1} {f : Rename s1 s2} {g : Rename s2 s3} :
    (K.rename f).rename g = K.rename (f.comp g) := by
  induction K generalizing s2 s3 with
  | empty => rfl
  | cons K C m ih =>
    simp [Constraint.rename, ih, CaptureSet.rename_comp]

end ModalCapybara
