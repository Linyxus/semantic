import Semantic.FsubNext.Denotation
import Semantic.FsubNext.Eval
namespace FsubNext

theorem sem_typ_var :
  Γ ⊨ (.var x) : (.singleton x) := by
  intro s e hts
  simp [Ty.exp_denot]
  apply Eval.eval_var
  cases x
  case free fx =>
    simp [Ty.val_denot, Denot.as_post, Var.subst, interp_var]
  case bound bx =>
    simp [Ty.val_denot, Denot.as_post, Var.subst, interp_var]
    rfl

theorem sem_typ_abs
  (ht : (Γ,x:T1) ⊨ e : T2) :
  Γ ⊨ (.abs T1 e) : (.arrow T1 T2) := by
  intro env store hts
  simp [Ty.exp_denot]
  apply Eval.eval_val
  · simp [Exp.subst]; constructor
  · simp [Ty.val_denot, Denot.as_post]
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
  apply Eval.eval_val
  · simp [Exp.subst]; constructor
  · simp [Ty.val_denot, Denot.as_post]
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

theorem abs_val_denot_inv
  (hv : Ty.val_denot env (.arrow T1 T2) store (.var x)) :
  ∃ fx, x = .free fx
    ∧ ∃ T0 e0 hv, store fx = some ⟨.abs T0 e0, hv⟩
    ∧ (∀ arg,
      (Ty.val_denot env T1 store (.var (.free arg))) ->
      Ty.exp_denot (env.extend_var arg) T2 store (e0.subst (Subst.openVar (.free arg)))) := by
  cases x with
  | bound bx => cases bx
  | free fx =>
    simp [Ty.val_denot, resolve] at hv
    generalize hres : store fx = res
    cases res
    case none => aesop
    case some v =>
      cases v
      aesop

theorem tabs_val_denot_inv
  (hv : Ty.val_denot env (.poly T1 T2) store (.var x)) :
  ∃ fx, x = .free fx
    ∧ ∃ T0 e0 hv, store fx = some ⟨.tabs T0 e0, hv⟩
    ∧ (∀ (denot : Denot),
      denot.Imply (Ty.val_denot env T1) ->
      Ty.exp_denot (env.extend_tvar denot) T2 store (e0.subst (Subst.openTVar .top))) := by
  cases x with
  | bound bx => cases bx
  | free fx =>
    simp [Ty.val_denot, resolve] at hv
    generalize hres : store fx = res
    cases res
    case none => aesop
    case some v =>
      cases v
      aesop

theorem interp_var_subst (x : Var s) :
  .free (interp_var env x) = x.subst (Subst.from_TypeEnv env) := by
  cases x <;> rfl

theorem var_exp_denot_inv
  (hv : Ty.exp_denot env T store (.var x)) :
  Ty.val_denot env T store (.var x) := by
  simp [Ty.exp_denot] at hv
  cases hv
  case eval_val hv _ => cases hv
  case eval_var hQ => exact hQ

theorem closed_var_inv (x : Var {}) :
  ∃ fx, x = .free fx := by
  cases x
  case bound bx => cases bx
  case free fx => aesop

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
  sorry

theorem soundness
  (ht : Γ ⊢ e : T) :
  Γ ⊨ e : T := by
  induction ht
  case var => apply sem_typ_var
  case abs => grind [sem_typ_abs]
  case tabs => grind [sem_typ_tabs]
  -- case app => grind [sem_typ_app]
  -- case tapp => grind [sem_typ_tapp]
  -- case letin => grind [sem_typ_letin]
  all_goals sorry

end FsubNext
