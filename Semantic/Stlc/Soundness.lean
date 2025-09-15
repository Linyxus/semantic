import Semantic.Stlc.TypeSystem
import Semantic.Stlc.Denotation
import Mathlib.Tactic

theorem eval_num_val {v : Exp 0}
  (hv : v.IsNumVal) :
  Eval v v := by
  induction hv <;> grind [Eval]

theorem eval_val {v : Exp 0}
  (hv : v.IsVal) :
  Eval v v := by
  cases hv <;> try grind [Eval]
  case bool hv => cases hv <;> grind [Eval]
  case num hv => apply eval_num_val hv

theorem typed_store_lookup
  (hts : TypedStore s Γ)
  (hb : Ctx.Lookup Γ x T) :
  Ty.val_denot T (s.lookup x) := by
  induction hb
  case here =>
    cases s; rename_i s0 v0
    simp [TypedStore] at hts
    simp [Store.lookup]
    aesop
  case there ih =>
    cases s; simp only [Store.lookup]
    cases hts
    grind

theorem sem_typ_var
  (hb : Ctx.Lookup Γ x T) :
  (Γ ⊨ (.var x) : T) := by
  intro s hts
  simp [Ty.exp_denot]
  use s.lookup x
  split_ands
  { apply eval_val
    apply Store.lookup_is_val }
  { apply typed_store_lookup hts hb }

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
  { grind [Exp.subst, Eval] }
  { simp [Ty.val_denot]
    grind [Exp.IsNumVal] }

theorem val_denot_is_val
  (hv : Ty.val_denot T v) :
  v.IsVal := by
  cases T
  case bool => simp [Ty.val_denot] at hv; grind [Exp.IsVal]
  case nat => simp [Ty.val_denot] at hv; grind [Exp.IsVal]
  case arrow => simp [Ty.val_denot] at hv; exact hv.left

theorem sem_typ_abs
  (ht : (Γ,x:T) ⊨ e : U) :
  (Γ ⊨ .abs T e : Ty.arrow T U) := by
  intro s hts
  simp [Ty.exp_denot]
  simp [Exp.subst]
  constructor; constructor
  { apply eval_val; grind [Exp.IsVal] }
  { simp [Ty.val_denot]
    constructor; try grind [Exp.IsVal]
    intro arg harg
    unfold SemanticTyping at ht
    have hvarg := val_denot_is_val harg
    let s' := Store.cons arg hvarg s
    have hts' : TypedStore s' (Γ,x:T) := by
      unfold s'
      simp [TypedStore]
      aesop
    specialize ht s' hts'
    sorry }

theorem soundness
  (ht : Γ ⊢ e : T) :
  (Γ ⊨ e : T) := by
  induction ht
  case var hb => apply sem_typ_var hb
  case abs => sorry
  case app => sorry
  case btrue =>
    intro s hts
    simp [Ty.exp_denot]
    use .btrue
    split_ands
    { grind [Exp.subst, Eval] }
    { simp [Ty.val_denot]; grind [Exp.IsBoolVal] }
  case bfalse =>
    intro s hts
    simp [Ty.exp_denot]
    use .bfalse
    split_ands
    { grind [Exp.subst, Eval] }
    { simp [Ty.val_denot]; grind [Exp.IsBoolVal] }
  case nzero =>
    intro s hts
    simp [Ty.exp_denot]
    use .nzero
    split_ands
    { grind [Exp.subst, Eval] }
    { simp [Ty.val_denot]; grind [Exp.IsNumVal] }
  case nsucc ih => apply sem_typ_nsucc ih
  case pred => sorry
  case iszero => sorry
  case cond => sorry
