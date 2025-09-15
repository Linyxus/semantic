import Semantic.Stlc.TypeSystem
import Semantic.Stlc.BigStep.Eval
import Mathlib.Tactic

/-!
Type interpretation for big-step STLC.
This module defines the denotation of types based on big-step evaluation.
-/

namespace Stlc
namespace BigStep

/-!
Denotation of types.
-/
mutual

def Ty.val_denot : Ty -> Exp 0 -> Prop
| .bool => fun e =>
  e.IsBoolVal
| .nat => fun e  =>
  e.IsNumVal
| .arrow T U => fun e =>
  e.IsAbsVal ∧
  ∀ arg_v,
    Ty.val_denot T arg_v ->
    Ty.exp_denot U (.app e arg_v)

def Ty.exp_denot : Ty -> Exp 0 -> Prop
| T => fun e =>
  ∃ v,
    Eval e v
    ∧ Ty.val_denot T v

end

/-!
Predicate for well-typed stores.
-/
def TypedStore : Store n -> Ctx n -> Prop
| .nil, .empty => True
| .cons v _ s, .var Γ T =>
  Ty.val_denot T v ∧ TypedStore s Γ

/-!
Semantic typing relation.
-/
def SemanticTyping (Γ : Ctx n) (e : Exp n) (T : Ty) : Prop :=
  ∀ s,
    TypedStore s Γ ->
    Ty.exp_denot T (e.subst (Subst.fromStore s))

/-!
Notation for semantic typing.
-/
notation:65 Γ " ⊨ " e " : " T => SemanticTyping Γ e T

end BigStep
end Stlc
