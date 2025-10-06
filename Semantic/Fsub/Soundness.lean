import Semantic.Fsub.Denotation
import Semantic.Fsub.Eval
namespace Fsub

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
      intro store' arg hsubsume harg
      simp [Exp.from_TypeEnv_weaken_open]
      apply ht (env.extend_var arg) store'
      constructor
      { exact harg }
      { apply env_typing_monotonic hts hsubsume }

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
      intro denot hdenot_mono hdenot_trans himply
      simp [Exp.from_TypeEnv_weaken_open_tvar (d:=denot)]
      apply ht
      constructor
      · exact hdenot_mono
      · constructor
        · exact hdenot_trans
        · constructor
          · exact himply
          · exact hts

theorem abs_val_denot_inv
  (hv : Ty.val_denot env (.arrow T1 T2) store (.var x)) :
  ∃ fx, x = .free fx
    ∧ ∃ T0 e0 hv, store fx = some ⟨.abs T0 e0, hv⟩
    ∧ (∀ (store' : Heap) arg,
      store'.subsumes store ->
      (Ty.val_denot env T1 store' (.var (.free arg))) ->
      Ty.exp_denot (env.extend_var arg) T2 store' (e0.subst (Subst.openVar (.free arg)))) := by
  cases x with
  | bound bx => cases bx
  | free fx =>
    simp [Ty.val_denot, resolve] at hv
    have ⟨T0, e0, hresolve, hfun⟩ := hv
    -- Analyze what's in the store at fx
    generalize hres : store fx = res at hresolve ⊢
    cases res
    case none => simp at hresolve
    case some v =>
      simp at hresolve
      cases v; rename_i val hval
      -- hresolve says val = .abs T0 e0
      subst hresolve
      use fx
      constructor
      · rfl
      · use T0, e0, (by constructor)

theorem tabs_val_denot_inv
  (hv : Ty.val_denot env (.poly T1 T2) store (.var x)) :
  ∃ fx, x = .free fx
    ∧ ∃ T0 e0 hv, store fx = some ⟨.tabs T0 e0, hv⟩
    ∧ (∀ (denot : Denot),
      denot.is_monotonic ->
      denot.is_transparent ->
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
      -- After substituting hres, resolve returns v.unwrap
      -- So hv becomes: ∃ T0 e0, v.unwrap = .tabs T0 e0 ∧ ...
      simp [hres] at hv
      obtain ⟨T0, e0, htabs, hfun⟩ := hv
      -- Now v.unwrap = .tabs T0 e0
      -- We need to show store fx = some ⟨.tabs T0 e0, _⟩
      -- We have hres : store fx = some v and htabs : v.unwrap = .tabs T0 e0
      use fx, rfl, T0, e0
      -- Need to provide proof that (tabs T0 e0).IsVal
      have hval : (Exp.tabs T0 e0).IsVal := by constructor
      use hval
      constructor
      · -- Show: store fx = some ⟨.tabs T0 e0, hval⟩
        cases v with
        | mk unwrap isVal =>
          simp at htabs
          subst htabs
          exact hres
      · exact hfun

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
  -- Apply hfun with store' = store (reflexive subsumption)
  have := hfun store farg (Heap.subsumes_refl store) h2'
  simp [Ty.exp_denot] at this ⊢
  -- Use heq : interp_var env y = farg to rewrite in both goal and hypothesis
  rw [<-heq]
  rw [<-heq] at this
  -- Convert postcondition via open_arg_val_denot
  have heqv := open_arg_val_denot (env:=env) (y:=y) (T:=T2)
  have hconv := eval_post_monotonic (Denot.imply_to_entails _ _ (Denot.equiv_to_imply heqv).1) this
  apply Eval.eval_apply hlk hconv

theorem sem_typ_tapp
  (ht : Γ ⊨ (.var x) : (.poly S T)) :
  Γ ⊨ (.tapp x S) : (T.subst (Subst.openTVar S)) := by
  intro env store hts
  have h1 := ht env store hts
  simp [Exp.subst] at h1
  have h1' := var_exp_denot_inv h1
  have ⟨fx, hfx, T0, e0, _, hlk, hfun⟩ := tabs_val_denot_inv h1'
  simp [Exp.subst, hfx]
  -- Need to show Ty.val_denot env S is monotonic and transparent
  have henv_mono := typed_env_is_monotonic hts
  have henv_trans := typed_env_is_transparent hts
  have hmono : (Ty.val_denot env S).is_monotonic := val_denot_is_monotonic henv_mono
  have htrans : (Ty.val_denot env S).is_transparent := val_denot_is_transparent henv_trans
  -- Apply hfun with monotonicity, transparency, and implication
  have this := hfun (Ty.val_denot env S) hmono htrans (Denot.imply_refl _)
  simp [Ty.exp_denot] at this ⊢
  -- Convert postcondition via open_targ_val_denot
  have heqv := open_targ_val_denot (env:=env) (S:=S) (T:=T)
  have hconv := eval_post_monotonic (Denot.imply_to_entails _ _ (Denot.equiv_to_imply heqv).1) this
  apply Eval.eval_tapply hlk hconv

theorem sem_typ_letin
  (ht1 : Γ ⊨ e1 : T)
  (ht2 : (Γ,x:T) ⊨ e2 : (U.rename Rename.succ)) :
  Γ ⊨ (.letin e1 e2) : U := by
  intro env store hts
  have henv := typed_env_is_inert hts
  simp [Exp.subst]
  simp [Ty.exp_denot]
  -- Use Eval.eval_letin with Q1 = (Ty.val_denot env T).as_post
  apply Eval.eval_letin (Q1 := (Ty.val_denot env T).as_post)
  case hpred =>
    -- Show (Ty.val_denot env T).as_post is monotonic
    intro h1 h2 e hsub hQ
    simp [Denot.as_post] at hQ ⊢
    -- Need to show val_denot is monotonic under heap extension
    have henv_mono := typed_env_is_monotonic hts
    exact val_denot_is_monotonic henv_mono hsub hQ
  case a =>
    -- Show Eval store (e1.subst ...) (Ty.val_denot env T).as_post
    have h1 := ht1 env store hts
    simp [Ty.exp_denot] at h1
    exact h1
  case h_val =>
    -- Handle the value case: e1 evaluated to a value v
    intro h1 v hs1 hv_isval hQ1 l' hfresh
    -- h1.subsumes store, v is a value, Q1 v h1 holds
    simp [Denot.as_post] at hQ1
    -- Apply ht2 with extended environment and heap
    have ht2' := ht2 (env.extend_var l') (h1.extend l' ⟨v, hv_isval⟩)
    simp [Ty.exp_denot] at ht2' ⊢
    -- Rewrite to make expressions match
    rw [<-Exp.from_TypeEnv_weaken_open] at ht2'
    -- Convert postcondition using weaken_val_denot
    apply eval_post_monotonic _ (ht2' _)
    · -- Show postcondition entailment
      apply Denot.imply_to_entails
      have heqv := weaken_val_denot (env:=env) (x:=l') (T:=U)
      apply (Denot.equiv_to_imply heqv).2
    · -- Show: EnvTyping (Γ,x:T) (env.extend_var l') (h1.extend l' ⟨v, hv_isval⟩)
      constructor
      · -- Show: Ty.val_denot env T (h1.extend l' ⟨v, hv_isval⟩) (Exp.var (Var.free l'))
        -- We have: hQ1 : Ty.val_denot env T h1 v (value v has type T)
        -- Strategy: Use monotonicity to lift hQ1 to extended heap, then use transparency

        -- Step 0: Prove heap subsumption
        have hext : (h1.extend l' ⟨v, hv_isval⟩).subsumes h1 := by
          intro x v' hx
          simp [Heap.extend]
          split
          · next heq =>
              rw [heq] at hx
              rw [hfresh] at hx
              contradiction
          · exact hx

        -- Step 1: Lift hQ1 to extended heap using monotonicity
        have henv_mono := typed_env_is_monotonic hts
        have hQ1_lifted : Ty.val_denot env T (h1.extend l' ⟨v, hv_isval⟩) v :=
          val_denot_is_monotonic henv_mono hext hQ1

        -- Step 2: Apply transparency
        have henv_trans := typed_env_is_transparent hts
        have htrans : (Ty.val_denot env T).is_transparent :=
          val_denot_is_transparent henv_trans

        -- Step 3: Use the heap lookup fact
        have hlookup : (h1.extend l' ⟨v, hv_isval⟩) l' = some ⟨v, hv_isval⟩ :=
          Heap.extend_lookup_eq h1 l' ⟨v, hv_isval⟩

        -- Step 4: Apply transparency with the lifted property
        -- Note: ⟨v, hv_isval⟩.unwrap = v
        apply htrans hlookup hQ1_lifted
      · -- Show: EnvTyping Γ env (h1.extend l' ⟨v, hv_isval⟩)
        -- Original typing preserved under heap extension
        -- h1.subsumes store, and (h1.extend l' ...).subsumes h1
        have hext : (h1.extend l' ⟨v, hv_isval⟩).subsumes h1 := by
          intro x v' hx
          simp [Heap.extend]
          split
          · -- Case: x = l', but h1 l' = none (from hfresh)
            -- So h1 x = h1 l' = none, contradicting hx : h1 x = some v'
            next heq =>
              rw [heq] at hx
              rw [hfresh] at hx
              contradiction
          · exact hx
        have hsub_trans : (h1.extend l' ⟨v, hv_isval⟩).subsumes store := by
          exact Heap.subsumes_trans hext hs1
        exact env_typing_monotonic hts hsub_trans
  case h_var =>
    -- Handle the variable case: e1 evaluated to variable x
    intro h1 x hs1 hQ1
    -- h1.subsumes store, Q1 (.var x) h1 holds
    simp [Denot.as_post] at hQ1
    -- Determine what x is
    have ⟨fx, hfx⟩ := closed_var_inv x
    subst hfx
    -- Apply ht2 with extended environment where the variable is bound to fx
    have ht2' := ht2 (env.extend_var fx) h1
    simp [Ty.exp_denot] at ht2' ⊢
    rw [<-Exp.from_TypeEnv_weaken_open] at ht2'
    -- Convert postcondition
    apply eval_post_monotonic _ (ht2' _)
    · -- Show postcondition entailment
      apply Denot.imply_to_entails
      have heqv := weaken_val_denot (env:=env) (x:=fx) (T:=U)
      apply (Denot.equiv_to_imply heqv).2
    · -- Show: EnvTyping (Γ,x:T) (env.extend_var fx) h1
      constructor
      · -- Variable fx has type T in heap h1
        exact hQ1
      · -- Original typing preserved: EnvTyping Γ env h1
        exact env_typing_monotonic hts hs1

theorem typed_env_lookup_tvar
  (hts : EnvTyping Γ env store)
  (hx : Ctx.Lookup Γ X (.tvar S)) :
  (env.lookup_tvar X).Imply (Ty.val_denot env S) := by sorry

theorem fundamental_subtyp
  (hsub : Subtyp Γ T1 T2) :
  SemSubtyp Γ T1 T2 := by
  induction hsub
  case top =>
    intro env store hts
    sorry
  case refl =>
    intro env store hts
    exact Denot.imply_refl _
  case trans ih1 ih2 =>
    intro env store hts
    specialize ih1 env store hts
    specialize ih2 env store hts
    apply Denot.imply_trans ih1 ih2
  case tvar =>
    intro env store hts
    simp [Ty.val_denot]
    sorry
  case singleton =>
    sorry
  case arrow ih1 ih2 =>
    intro env store hts
    intro s0 e0 h0
    simp [Ty.val_denot] at h0 ⊢
    sorry
  case poly => sorry

/-- The fundamental theorem of semantic type soundness. -/
theorem fundamental
  (ht : Γ ⊢ e : T) :
  Γ ⊨ e : T := by
  induction ht
  case var => apply sem_typ_var
  case abs => grind [sem_typ_abs]
  case tabs => grind [sem_typ_tabs]
  case app => grind [sem_typ_app]
  case tapp => grind [sem_typ_tapp]
  case letin => grind [sem_typ_letin]
  case subtyp => sorry

end Fsub
