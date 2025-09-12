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

theorem typed_store_lookup
  (hts : TypedStore s Γ)
  (hb : Ctx.Lookup Γ x T) :
  Ty.val_denot T ⟨s, s.lookup x⟩ := by
  induction hb
  case here =>
    cases s; rename_i s0 v0
    simp [TypedStore] at hts
    simp [Store.lookup]
    sorry
  case there ih => sorry

theorem sem_typ_var
  (hb : Ctx.Lookup Γ x T) :
  (Γ ⊨ (.var x) : T) := by
  intro s hts
  simp [Ty.exp_denot]
  use s.lookup x
  split_ands
  { grind [Eval] }
  { sorry }

theorem sem_typ_nsucc
  (ht : Γ ⊨ e : Ty.nat) :
  (Γ ⊨ .nsucc e : Ty.nat) := by
  intro s hts
  specialize ht s hts
  simp [Ty.exp_denot] at *
  have ⟨v0, hev0, hv0⟩ := ht
  simp [Ty.val_denot] at hv0
  use .nsucc v0
  split_ands
  { grind [Eval] }
  { simp [Ty.val_denot]
    grind [Exp.is_num_val] }

theorem soundness
  (ht : Γ ⊢ e : T) :
  (Γ ⊨ e : T) := by
  induction ht
  case var => sorry
  case abs => sorry
  case app => sorry
  case btrue =>
    intro s hts
    simp [Ty.exp_denot]
    use .btrue
    split_ands
    { grind [Eval] }
    { simp [Ty.val_denot]; rfl }
  case bfalse =>
    intro s hts
    simp [Ty.exp_denot]
    use .bfalse
    split_ands
    { grind [Eval] }
    { simp [Ty.val_denot]; rfl }
  case nzero =>
    intro s hts
    simp [Ty.exp_denot]
    use .nzero
    split_ands
    { grind [Eval] }
    { simp [Ty.val_denot]; rfl }
  case nsucc ih => apply sem_typ_nsucc ih
  case pred => sorry
  case iszero => sorry
  case cond => sorry
