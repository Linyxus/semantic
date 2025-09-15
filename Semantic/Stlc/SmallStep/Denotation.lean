import Semantic.Stlc.TypeSystem
import Semantic.Stlc.SmallStep.Eval
import Semantic.Stlc.Syntax
import Semantic.Stlc.Substitution
import Mathlib.Tactic

namespace Stlc.SmallStep

mutual

def Ty.val_denot : Ty -> Exp 0 -> Prop
| .bool => fun e =>
  e.IsBoolVal
| .nat => fun e =>
  e.IsNumVal
| .arrow T U => fun e =>
  e.IsAbsVal ∧
  ∀ arg_v,
    Ty.val_denot T arg_v ->
    Ty.exp_denot U (.app e arg_v)

def Ty.exp_denot : Ty -> Exp 0 -> Prop
| T => fun e =>
  ∃ v,
    Reduce e v
    ∧ Ty.val_denot T v

end

def TypedStore : Store n -> Ctx n -> Prop
| .nil, .empty => True
| .cons v _ s, .var Γ T =>
  Ty.val_denot T v ∧ TypedStore s Γ

def SemanticTyping (Γ : Ctx n) (e : Exp n) (T : Ty) : Prop :=
  ∀ s,
    TypedStore s Γ ->
    Ty.exp_denot T (e.subst (Subst.fromStore s))

notation:65 Γ " ⊨ " e " : " T => SemanticTyping Γ e T

end Stlc.SmallStep
