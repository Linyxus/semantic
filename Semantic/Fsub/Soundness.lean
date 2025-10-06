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
  (hx : Ctx.LookupTVar Γ X S) :
  (env.lookup_tvar X).Imply (Ty.val_denot env S) := by
  induction hx generalizing store
  case here =>
    cases env; rename_i info0 env0
    cases info0
    simp [EnvTyping] at hts
    simp [TypeEnv.lookup_tvar, TypeEnv.lookup]
    have ⟨_, _, hd, _⟩ := hts
    apply Denot.imply_trans
    · exact hd
    · apply Denot.equiv_to_imply_l
      apply tweaken_val_denot
  case there b _ ih =>
    cases env; rename_i info0 env0
    cases info0
    case var =>
      cases b
      simp [EnvTyping] at hts
      obtain ⟨_, henv⟩ := hts
      specialize ih henv
      apply Denot.imply_trans
      · exact ih
      · apply Denot.equiv_to_imply_l
        apply weaken_val_denot
    case tvar =>
      cases b
      simp [EnvTyping] at hts
      obtain ⟨_, _, _, henv⟩ := hts
      specialize ih henv
      apply Denot.imply_trans
      · exact ih
      · apply Denot.equiv_to_imply_l
        apply tweaken_val_denot

theorem typed_env_lookup_var
  (hts : EnvTyping Γ env store)
  (hx : Ctx.LookupVar Γ x T) :
  Ty.val_denot env T store (.var (.free (env.lookup_var x))) := by
  induction hx generalizing store
  case here =>
    -- The environment must match the context structure
    rename_i Γ0 T0
    cases env; rename_i info0 env0
    cases info0; rename_i n
    simp [EnvTyping] at hts
    simp [TypeEnv.lookup_var, TypeEnv.lookup]
    -- Apply weaken_val_denot equivalence
    have heqv := weaken_val_denot (env:=env0) (x:=n) (T:=T0)
    apply (Denot.equiv_to_imply heqv).1
    exact hts.1
  case there b =>
    -- Need to handle two cases based on the binding (b✝)
    rename_i k Γ0 x0 T0 binding hlk
    -- binding is the Binding, hlk is the lookup proof, b is the IH
    cases binding
    case var =>
      -- binding is .var Tb
      rename_i Tb
      cases env; rename_i info0 env0
      cases info0; rename_i n
      simp [EnvTyping] at hts
      obtain ⟨_, henv0⟩ := hts
      -- Apply IH to get the result for env0
      have hih := b henv0
      -- Show that lookup_var .there reduces correctly
      simp [TypeEnv.lookup_var, TypeEnv.lookup]
      -- Apply weakening
      have heqv := weaken_val_denot (env:=env0) (x:=n) (T:=T0)
      apply (Denot.equiv_to_imply heqv).1
      exact hih
    case tvar =>
      -- binding is .tvar Sb
      rename_i Sb
      cases env; rename_i info0 env0
      cases info0; rename_i d
      simp [EnvTyping] at hts
      obtain ⟨_, _, _, henv0⟩ := hts
      have hih := b henv0
      simp [TypeEnv.lookup_var, TypeEnv.lookup]
      have heqv := tweaken_val_denot (env:=env0) (d:=d) (T:=T0)
      apply (Denot.equiv_to_imply heqv).1
      exact hih

lemma sem_subtyp_poly
  (hS : SemSubtyp Γ S2 S1) -- contravariant in bound
  (hT : SemSubtyp (Γ,X<:S2) T1 T2) -- covariant in body, under extended context
  : SemSubtyp Γ (.poly S1 T1) (.poly S2 T2) := by
  intro type_env heap hts
  intro heap' hheap
  intro ans hans
  simp [Ty.val_denot] at hans ⊢
  obtain ⟨T0, e0, hresolve, hfun⟩ := hans
  use T0, e0
  apply And.intro hresolve
  intro denot hdenot_mono hdenot_trans himply_S2
  have hS_at_heap' := hS type_env heap hts heap' hheap
  have himply_S1 : denot.Imply (Ty.val_denot type_env S1) := by
    intro s e hdenot
    have hS2 := himply_S2 s e hdenot
    specialize hS type_env s
    sorry
  -- Apply the original function with this denot
  specialize hfun denot hdenot_mono hdenot_trans himply_S1
  -- Now we have: exp_denot (env.extend_tvar denot) T1 heap' (e0.subst ...)
  -- Need: exp_denot (env.extend_tvar denot) T2 heap' (e0.subst ...)
  -- Use covariance hT
  specialize hT (type_env.extend_tvar denot)
  have henv' : EnvTyping (Γ,X<:S2) (type_env.extend_tvar denot) heap' := by
    constructor
    · exact hdenot_mono
    · constructor
      · exact hdenot_trans
      · constructor
        · exact himply_S2
        · apply env_typing_monotonic hts hheap
  specialize hT heap' henv'
  apply Denot.apply_imply_at hfun
  apply Denot.imply_after_to_imply_at
  apply denot_implyat_lift hT

lemma sem_subtyp_arrow
  (hT : SemSubtyp Γ T2 T1)
  (hU : SemSubtyp (Γ,x:T2) U1 U2) :
  SemSubtyp Γ (.arrow T1 U1) (.arrow T2 U2) := by
  intro type_env heap hts
  intro heap' hheap
  intro ans hans
  simp [Ty.val_denot] at hans ⊢
  obtain ⟨T0, e0, hresolve, hfun⟩ := hans
  use T0, e0
  apply And.intro hresolve
  intro H arg hheap1 ht_arg
  specialize hfun H arg hheap1
  have ht_arg' := hT type_env heap hts H (Heap.subsumes_trans hheap1 hheap) _ ht_arg
  specialize hfun ht_arg'
  specialize hU (type_env.extend_var arg)
  have henv' : EnvTyping (Γ,x:T2) (type_env.extend_var arg) H := by
    constructor
    · exact ht_arg
    · apply env_typing_monotonic hts
      apply Heap.subsumes_trans hheap1 hheap
  specialize hU H henv'
  apply Denot.apply_imply_at hfun
  apply Denot.imply_after_to_imply_at
  apply denot_implyat_lift hU

lemma sem_subtyp_top {T : Ty s} :
  SemSubtyp Γ T .top := by
  intro type_env heap hts
  intro heap' hheap
  have henv := typed_env_is_inert hts
  apply Denot.imply_implyat
  simp [Ty.val_denot]
  have := val_denot_ans henv (T:=T)
  exact this

lemma sem_subtyp_refl {T : Ty s} :
  SemSubtyp Γ T T := by
  intro type_env heap hts
  intro heap' hheap
  have henv := typed_env_is_inert hts
  apply Denot.imply_refl

lemma sem_subtyp_trans
  (hsub1 : SemSubtyp Γ T1 T2)
  (hsub2 : SemSubtyp Γ T2 T3) :
  SemSubtyp Γ T1 T3 := by
  intro type_env heap hts
  intro heap' hheap
  specialize hsub1 type_env heap hts heap' hheap
  specialize hsub2 type_env heap hts heap' hheap
  apply Denot.implyat_trans hsub1 hsub2

lemma sem_subtyp_tvar
  (hX : Ctx.LookupTVar Γ X S) :
  SemSubtyp Γ (.tvar X) S := by
  intro type_env heap hts
  intro heap' hheap
  apply Denot.imply_implyat
  simp [Ty.val_denot]
  apply typed_env_lookup_tvar hts hX

lemma sem_subtyp_singleton
  (hx : Ctx.LookupVar Γ x T) :
  SemSubtyp Γ (.singleton (.bound x)) T := by
  intro type_env heap hts
  intro heap' hheap
  simp [Ty.val_denot, interp_var]
  intro ans hans
  subst hans
  apply val_denot_is_monotonic _ hheap
  · apply typed_env_lookup_var hts hx
  · apply typed_env_is_monotonic hts

theorem fundamental_subtyp
  (hsub : Subtyp Γ T1 T2) :
  SemSubtyp Γ T1 T2 := by
  induction hsub
  case top => grind [sem_subtyp_top]
  case refl => grind [sem_subtyp_refl]
  case trans => grind [sem_subtyp_trans]
  case tvar => grind [sem_subtyp_tvar]
  case singleton => grind [sem_subtyp_singleton]
  case arrow => grind [sem_subtyp_arrow]
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
