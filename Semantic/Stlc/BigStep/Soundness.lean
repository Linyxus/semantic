import Semantic.Stlc.TypeSystem
import Semantic.Stlc.BigStep.Denotation
import Mathlib.Tactic

theorem eval_num_val {v : Exp 0}
  (hv : v.IsNumVal) :
  Eval v v := by
  induction hv <;> grind [Eval]

theorem eval_num_val_eq
  (hv : v.IsNumVal)
  (hev : Eval v v') :
  v = v' := by
  induction hv generalizing v'
  case nzero =>
    cases hev; rfl
  case nsucc _ ih =>
    cases hev
    aesop

theorem eval_bool_val_eq
  (hv : v.IsBoolVal)
  (hev : Eval v v') :
  v = v' := by
  cases hv
  case btrue =>
    cases hev; rfl
  case bfalse =>
    cases hev; rfl

theorem eval_val {v : Exp 0}
  (hv : v.IsVal) :
  Eval v v := by
  cases hv <;> try grind [Eval]
  case bool hv => cases hv <;> grind [Eval]
  case num hv => apply eval_num_val hv

theorem eval_val_eq
  (hv : v.IsVal)
  (hev : Eval v v') :
  v = v' := by
  cases hv <;> try grind [Eval]
  case bool hv => apply eval_bool_val_eq hv hev
  case num hv => apply eval_num_val_eq hv hev

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

theorem abs_val_is_val
  (hv : Exp.IsAbsVal v) :
  v.IsVal := by
  cases hv
  grind [Exp.IsVal]

theorem val_denot_is_val
  (hv : Ty.val_denot T v) :
  v.IsVal := by
  cases T
  case bool => simp [Ty.val_denot] at hv; grind [Exp.IsVal]
  case nat => simp [Ty.val_denot] at hv; grind [Exp.IsVal]
  case arrow => simp [Ty.val_denot] at hv; apply abs_val_is_val hv.left

theorem sem_typ_abs
  (ht : (Γ,x:T) ⊨ e : U) :
  (Γ ⊨ .abs T e : Ty.arrow T U) := by
  intro s hts
  simp [Ty.exp_denot]
  simp [Exp.subst]
  constructor; constructor
  { apply eval_val; grind [Exp.IsVal] }
  { simp [Ty.val_denot]
    constructor; try grind [Exp.IsAbsVal]
    intro arg harg
    unfold SemanticTyping at ht
    have hvarg := val_denot_is_val harg
    let s' := Store.cons arg hvarg s
    have hts' : TypedStore s' (Γ,x:T) := by
      unfold s'
      simp [TypedStore]
      aesop
    specialize ht s' hts'
    simp [Ty.exp_denot] at ht ⊢
    have ⟨v0, hev0, hv0⟩ := ht
    use v0
    apply And.intro _ hv0
    { apply Eval.ev_app
      · apply eval_val; grind [Exp.IsVal]
      · apply eval_val hvarg
      · simp [Exp.subst_comp]
        rw [Subst.fromStore_openVar_comp (hv := hvarg)]
        exact hev0
    }
  }

theorem sem_typ_app
  (ht1 : Γ ⊨ e1 : Ty.arrow T U)
  (ht2 : Γ ⊨ e2 : T) :
  (Γ ⊨ .app e1 e2 : U) := by
  intro s hts
  specialize ht1 s hts
  specialize ht2 s hts
  simp only [Ty.exp_denot] at *
  have ⟨vf, hevf, hvf⟩ := ht1
  have ⟨va, heva, hva⟩ := ht2
  simp [Ty.val_denot] at hvf
  cases hvf.left
  have := hvf.right va hva
  simp [Ty.exp_denot] at this
  have ⟨v, hev, vdenot⟩ := this
  use v
  apply And.intro _ vdenot
  apply Eval.ev_app
  { exact hevf }
  { exact heva }
  { cases hev
    rename_i hev1 hev2 hev3
    cases (eval_val_eq (by constructor) hev1)
    cases (eval_val_eq (val_denot_is_val hva) hev2)
    exact hev3 }

theorem sem_typ_pred
  (ht : Γ ⊨ e : Ty.nat) :
  (Γ ⊨ .pred e : Ty.nat) := by
  intro s hts
  specialize ht s hts
  simp only [Ty.exp_denot] at *
  have ⟨v0, hev0, v0denot⟩ := ht
  simp [Ty.val_denot] at v0denot
  cases v0denot
  case nzero =>
    use .nzero
    apply And.intro _ (by grind [Ty.val_denot, Exp.IsNumVal])
    exact Eval.ev_pred_nzero hev0
  case nsucc n0 hv =>
    use n0
    apply And.intro _ (by grind [Ty.val_denot, Exp.IsNumVal])
    exact Eval.ev_pred_nsucc hev0 hv

theorem sem_typ_iszero
  (ht : Γ ⊨ e : Ty.nat) :
  (Γ ⊨ .iszero e : Ty.bool) := by
  intro s hts
  specialize ht s hts
  simp only [Ty.exp_denot] at *
  have ⟨v0, hev0, v0denot⟩ := ht
  simp [Ty.val_denot] at v0denot
  cases v0denot
  case nzero =>
    use .btrue
    apply And.intro _ (by grind [Ty.val_denot, Exp.IsBoolVal])
    exact Eval.ev_iszero_nzero hev0
  case nsucc n0 hv =>
    use .bfalse
    apply And.intro _ (by grind [Ty.val_denot, Exp.IsBoolVal])
    exact Eval.ev_iszero_nsucc hev0 hv

theorem sem_typ_cond
  (ht1 : Γ ⊨ e1 : Ty.bool)
  (ht2 : Γ ⊨ e2 : T)
  (ht3 : Γ ⊨ e3 : T) :
  (Γ ⊨ .cond e1 e2 e3 : T) := by
  intro s hts
  specialize ht1 s hts
  specialize ht2 s hts
  specialize ht3 s hts
  simp only [Ty.exp_denot] at *
  have ⟨v1, hev1, v1denot⟩ := ht1
  have ⟨v2, hev2, v2denot⟩ := ht2
  have ⟨v3, hev3, v3denot⟩ := ht3
  simp [Ty.val_denot] at v1denot
  cases v1denot
  case btrue =>
    use v2
    apply And.intro _ v2denot
    exact Eval.ev_cond_true hev1 hev2 hev3
  case bfalse =>
    use v3
    apply And.intro _ v3denot
    exact Eval.ev_cond_false hev1 hev2 hev3

theorem soundness
  (ht : Γ ⊢ e : T) :
  (Γ ⊨ e : T) := by
  induction ht <;>
    try (solve |
      grind [sem_typ_var, sem_typ_abs, sem_typ_app, sem_typ_nsucc,
        sem_typ_pred, sem_typ_iszero, sem_typ_cond])
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
