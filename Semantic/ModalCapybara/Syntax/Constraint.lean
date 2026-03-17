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

end ModalCapybara
