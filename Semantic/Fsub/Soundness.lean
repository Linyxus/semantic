import Semantic.Fsub.Denotation
import Semantic.Fsub.Eval
namespace Fsub

mutual

theorem val_denot_mono
  (henv : TypeEnv.mono env) :
  (Ty.val_denot env T).Mono :=
  match T with
  | .top => by
    simp [Ty.val_denot, Denot.Mono]
    intro base1 base2 e he inserted
    apply Exp.rename_levels_preserves_IsAns he
  | .singleton x => by
    simp [Denot.Mono]
    sorry
  | .tvar X => by
    simp [Ty.val_denot]
    apply henv
  | .arrow T1 T2 => by
    sorry
  | .poly S T => sorry

theorem exp_denot_frame
  (henv : TypeEnv.mono env) :
  (Ty.exp_denot env T).Mono := by
  simp [Denot.Mono]
  intro base1 base2 e he inserted
  simp only [Ty.exp_denot] at he ⊢
  obtain ⟨s_out, v, hred, hv⟩ := he
  sorry

end

theorem exp_denot_reduce
  (hr : Reduce s1 e1 s2 e2)
  (hd : Ty.exp_denot env T s2 e2) :
  Ty.exp_denot env T s1 e1 := by
  simp [Ty.exp_denot] at hd ⊢
  obtain ⟨s0, v0, hr0, hv0⟩ := hd
  use s0, v0
  constructor
  · apply reduce_trans hr hr0
  · exact hv0

theorem step_ans_absurd
  (h : Exp.IsAns e)
  (hs : Step s e s' e') :
  False := by
  cases hs <;> try (solve | cases h | cases h; rename_i hv; cases hv)

theorem red_ans
  (h : Exp.IsAns e)
  (hr : Reduce s e s' e') :
  s = s' ∧ e = e' := by
  cases hr <;> try (solve | cases h | aesop)
  rename_i hs _
  exfalso; apply step_ans_absurd h hs

theorem sem_typ_var :
  Γ ⊨ (.var x) : (.singleton x) := by
  intro s e hts
  simp [Ty.exp_denot]
  constructor; constructor
  apply And.intro Reduce.red_refl _
  cases x
  case bound bx =>
    simp [Ty.val_denot]
    rfl
  case free fx =>
    simp [Ty.val_denot]
    rfl

theorem sem_typ_abs
  (ht : (Γ,x:T1) ⊨ e : T2) :
  Γ ⊨ (.abs T1 e) : (.arrow T1 T2) := by
  intro env store hts
  simp [Ty.exp_denot]
  constructor; constructor
  apply And.intro Reduce.red_refl _
  simp [Ty.val_denot]
  constructor; constructor
  constructor
  · rfl
  · unfold SemanticTyping at ht
    intro arg harg
    simp [Exp.from_TypeEnv_weaken_open]
    apply ht
    constructor
    { exact harg }
    { exact hts }

theorem sem_typ_tabs
  (ht : (Γ,X<:S) ⊨ e : T) :
  Γ ⊨ (.tabs S e) : (.poly S T) := by
  intro env store hts
  simp [Ty.exp_denot]
  constructor; constructor
  apply And.intro Reduce.red_refl _
  simp [Ty.val_denot]
  constructor; constructor
  constructor
  · rfl
  · unfold SemanticTyping at ht
    intro denot hdenot
    simp [Exp.from_TypeEnv_weaken_open_tvar (d:=denot)]
    apply ht
    constructor
    { exact hdenot }
    { exact hts }

theorem var_exp_denot_inv
  (hv : Ty.exp_denot env T store (.var x)) :
  Ty.val_denot env T store (.var x) := by
  simp [Ty.exp_denot] at hv
  have ⟨s', v, hr, hv⟩ := hv
  have := red_ans (by apply Exp.IsAns.is_var) hr
  aesop

theorem closed_var_inv (x : Var {}) :
  ∃ fx, x = .free fx := by
  cases x
  case bound bx => cases bx
  case free fx => aesop

theorem abs_val_denot_inv
  (hv : Ty.val_denot env (.arrow T1 T2) store (.var x)) :
  ∃ fx, x = .free fx
    ∧ ∃ T0 e0 hv, store.lookup fx = some ⟨.abs T0 e0, hv⟩
    ∧ (∀ arg,
      (Ty.val_denot env T1 store (.var (.free arg))) ->
      Ty.exp_denot (env.extend_var arg) T2 store (e0.subst (Subst.openVar (.free arg)))) := by
  cases x with
  | bound bx => cases bx
  | free fx =>
    simp [Ty.val_denot, resolve] at hv
    generalize hres : store.lookup fx = res
    cases res
    case none => aesop
    case some v =>
      cases v
      aesop

theorem tabs_val_denot_inv
  (hv : Ty.val_denot env (.poly T1 T2) store (.var x)) :
  ∃ fx, x = .free fx
    ∧ ∃ T0 e0 hv, store.lookup fx = some ⟨.tabs T0 e0, hv⟩
    ∧ (∀ (denot : Denot),
      denot.Imply (Ty.val_denot env T1) ->
      Ty.exp_denot (env.extend_tvar denot) T2 store (e0.subst (Subst.openTVar .top))) := by
  cases x with
  | bound bx => cases bx
  | free fx =>
    simp [Ty.val_denot, resolve] at hv
    generalize hres : store.lookup fx = res
    cases res
    case none => aesop
    case some v =>
      cases v
      aesop

theorem interp_var_subst (x : Var s) :
  .free (interp_var env x) = x.subst (Subst.from_TypeEnv env) := by
  cases x <;> rfl

theorem sem_typ_app
  (ht1 : Γ ⊨ (.var x) : (.arrow T1 T2))
  (ht2 : Γ ⊨ (.var y) : T1) :
  Γ ⊨ (.app x y) : (T2.subst (Subst.openVar y)) := by
  intro env store hts
  have h1 := ht1 env store hts
  simp [Exp.subst] at h1
  have h1' := var_exp_denot_inv h1
  have ⟨fx, hfx, T0, hbody, _, hlk, hfun⟩ := abs_val_denot_inv h1'
  simp [Exp.subst, hfx]
  have h2 := ht2 env store hts
  simp [Exp.subst] at h2
  have h2' := var_exp_denot_inv h2
  have ⟨farg, hfarg⟩ := closed_var_inv (y.subst (Subst.from_TypeEnv env))
  have heq := hfarg
  simp [<-interp_var_subst] at heq
  simp [hfarg] at *
  have := hfun farg h2'
  simp [Ty.exp_denot] at this ⊢
  have ⟨s', v, hr, hv⟩ := this
  use s', v
  constructor
  · apply Reduce.red_step _ hr
    constructor
    exact hlk
  · simp [<-heq] at hv
    apply Denot.equiv_ltr _ hv
    apply open_arg_val_denot

theorem sem_typ_tapp
  (ht : Γ ⊨ (.var x) : (.poly S T)) :
  Γ ⊨ (.tapp x S) : (T.subst (Subst.openTVar S)) := by
  intro env store hts
  have h1 := ht env store hts
  simp [Exp.subst] at h1
  have h1' := var_exp_denot_inv h1
  have ⟨fx, hfx, T0, e0, _, hlk, hfun⟩ := tabs_val_denot_inv h1'
  simp [Exp.subst, hfx]
  have := hfun (Ty.val_denot env S) (by apply Denot.imply_refl)
  simp [Ty.exp_denot] at this ⊢
  have ⟨s', v, hr, hv⟩ := this
  use s', v
  constructor
  · apply Reduce.red_step _ hr
    constructor
    exact hlk
  · apply Denot.equiv_ltr _ hv
    apply open_targ_val_denot

theorem sem_typ_letin
  (ht1 : Γ ⊨ e1 : T)
  (ht2 : (Γ,x:T) ⊨ e2 : (U.rename Rename.succ)) :
  Γ ⊨ (.letin e1 e2) : U := by
  intro env store hts
  have henv := typed_env_is_inert hts
  simp [Exp.subst]
  specialize ht1 env store hts
  simp [Ty.exp_denot] at ht1
  obtain ⟨s1, v1, hr1, hv1⟩ := ht1
  unfold SemanticTyping at ht2
  have := val_denot_ans henv (T:=T)
  have hv1_ans := this s1 v1 hv1
  simp [Denot.ans] at hv1_ans
  -- Now hv1_ans : Exp.IsAns v1, meaning v1 is either a variable or a value
  cases hv1_ans with
  | is_var =>
    rename_i x0
    cases x0
    case bound bx => cases bx
    case free fx =>
      have := reduce_ctx (u:=e2.subst (Subst.from_TypeEnv env).lift) hr1
      have := reduce_right_step this Step.st_rename
      apply exp_denot_reduce this
      specialize ht2 (env.extend_var fx) s1
      sorry
  | is_val => sorry

theorem soundness
  (ht : Γ ⊢ e : T) :
  Γ ⊨ e : T := by
  induction ht
  case var => apply sem_typ_var
  case abs => grind [sem_typ_abs]
  case tabs => grind [sem_typ_tabs]
  case app => grind [sem_typ_app]
  case tapp => grind [sem_typ_tapp]
  case letin => grind [sem_typ_letin]
  all_goals sorry

end Fsub
