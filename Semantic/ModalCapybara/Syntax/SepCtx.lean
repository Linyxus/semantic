import Semantic.ModalCapybara.Syntax.CaptureSet

namespace ModalCapybara

/-- A separation constraint. -/
inductive SepCtx : Sig -> Type where
| empty : SepCtx s
| cons :
  SepCtx s ->
  CaptureSet s ->
  Mutability ->
  SepCtx s

/-- Applies a renaming to all bound variables in a separation context. -/
def SepCtx.rename : SepCtx s1 -> Rename s1 s2 -> SepCtx s2
| .empty, _ => .empty
| .cons K C m, ρ => .cons (K.rename ρ) (C.rename ρ) m

/-- Renaming by the identity renaming leaves a separation context unchanged. -/
theorem SepCtx.rename_id {K : SepCtx s} :
    K.rename Rename.id = K := by
  induction K with
  | empty => rfl
  | cons K C m ih =>
    simp [SepCtx.rename, ih, CaptureSet.rename_id]

/-- Renaming distributes over composition of renamings. -/
theorem SepCtx.rename_comp
    {K : SepCtx s1} {f : Rename s1 s2} {g : Rename s2 s3} :
    (K.rename f).rename g = K.rename (f.comp g) := by
  induction K generalizing s2 s3 with
  | empty => rfl
  | cons K C m ih =>
    simp [SepCtx.rename, ih, CaptureSet.rename_comp]

/-- A separation context is closed if it contains no heap pointers. -/
inductive SepCtx.IsClosed : SepCtx s -> Prop where
| empty : SepCtx.IsClosed .empty
| cons : SepCtx.IsClosed K -> CaptureSet.IsClosed C -> SepCtx.IsClosed (.cons K C m)

end ModalCapybara
