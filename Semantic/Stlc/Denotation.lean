import Semantic.Stlc.TypeSystem
import Semantic.Stlc.BigStep
import Mathlib.Tactic

mutual

def Ty.val_denot : Ty -> Exp 0 -> Prop
| .bool => fun e =>
  e.IsBoolVal
| .nat => fun e  =>
  e.IsNumVal
| .arrow T U => fun e =>
  ∀ arg_v,
    Ty.val_denot T arg_v ->
    Ty.exp_denot U (.app e arg_v)

def Ty.exp_denot : Ty -> Exp 0 -> Prop
| T => fun e =>
  ∃ v,
    Eval e v
    ∧ Ty.val_denot T v

end

-- def SemanticTyping (Γ : Ctx n) (e : Exp n) (T : Ty) : Prop :=
--   ∀ s,
--     TypedStore s Γ ->
--     Ty.exp_denot T ⟨s, e⟩

-- notation:65 Γ " ⊨ " e " : " T => SemanticTyping Γ e T
