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
  e.IsVal ∧
  ∀ arg_v,
    Ty.val_denot T arg_v ->
    Ty.exp_denot U (.app e arg_v)

def Ty.exp_denot : Ty -> Exp 0 -> Prop
| T => fun e =>
  ∃ v,
    Eval e v
    ∧ Ty.val_denot T v

end

inductive Store : Nat -> Type where
| nil : Store 0
| cons : (e : Exp 0) -> (hv : e.IsVal) -> Store n -> Store (n + 1)

def Store.lookup : Store n -> Var n -> Exp 0
| .cons v _ s, .here => v
| .cons _ _ s, .there i => s.lookup i

def TypedStore : Store n -> Ctx n -> Prop
| .nil, .empty => True
| .cons v _ s, .var Γ T =>
  Ty.val_denot T v ∧ TypedStore s Γ

def Subst.fromStore (s : Store n) : Subst n 0 where
  exp := fun x => s.lookup x

def SemanticTyping (Γ : Ctx n) (e : Exp n) (T : Ty) : Prop :=
  ∀ s,
    TypedStore s Γ ->
    Ty.exp_denot T (e.subst (Subst.fromStore s))

notation:65 Γ " ⊨ " e " : " T => SemanticTyping Γ e T

theorem Store.lookup_is_val {s : Store n} :
  (s.lookup x).IsVal := by
  induction x
  case here => cases s; aesop
  case there ih =>
    cases s; simp [Store.lookup]
    exact ih
