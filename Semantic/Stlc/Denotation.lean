import Semantic.Stlc.TypeSystem
import Semantic.Stlc.Interpreter
import Mathlib.Tactic

mutual

def Ty.val_denot : Ty -> ∀ {n}, Config n -> Prop
| .bool => fun config =>
  config.e.is_bool_val
| .nat => fun config =>
  config.e.is_num_val
| .arrow T U => fun config =>
  ∀ arg_v,
    Ty.val_denot T ⟨config.s, arg_v⟩ ->
    Ty.exp_denot U ⟨config.s, .app config.e arg_v⟩

def Ty.exp_denot : Ty -> ∀ {n}, Config n -> Prop
| T => fun config =>
  ∃ v,
    Eval config.s config.e v
    ∧ Ty.val_denot T ⟨config.s, v⟩

end

def TypedStore : Store n -> Ctx n -> Prop
| .empty, .empty => True
| .val s v, .var Γ T =>
  TypedStore s Γ ∧ Ty.val_denot T ⟨s, v⟩

def SemanticTyping (Γ : Ctx n) (e : Exp n) (T : Ty) : Prop :=
  ∀ s,
    TypedStore s Γ ->
    Ty.exp_denot T ⟨s, e⟩

notation:65 Γ " ⊨ " e " : " T => SemanticTyping Γ e T
