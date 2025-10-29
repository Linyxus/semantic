import Semantic.CC.Denotation
import Semantic.CC.Eval
namespace CC

theorem typed_env_lookup_var
  (hts : EnvTyping Γ env store)
  (hx : Ctx.LookupVar Γ x T) :
  Ty.capt_val_denot env T store (.var (.free (env.lookup_var x).1)) := by
  induction hx generalizing store
  case here =>
    -- The environment must match the context structure
    rename_i Γ0 T0
    cases env; rename_i info0 env0
    cases info0; rename_i n access
    simp [EnvTyping] at hts
    simp [TypeEnv.lookup_var, TypeEnv.lookup]
    -- Apply weaken_capt_val_denot equivalence
    have heqv := weaken_capt_val_denot (env:=env0) (x:=n) (R:=access) (T:=T0)
    apply (Denot.equiv_to_imply heqv).1
    exact hts.1
  case there b =>
    -- Need to handle three cases based on the binding kind
    rename_i k Γ0 x0 T0 binding hlk
    cases binding
    case var =>
      -- binding is .var Tb
      rename_i Tb
      cases env; rename_i info0 env0
      cases info0; rename_i n access
      simp [EnvTyping] at hts
      obtain ⟨_, _, henv0⟩ := hts
      -- Apply IH to get the result for env0
      have hih := b henv0
      -- Show that lookup_var .there reduces correctly
      simp [TypeEnv.lookup_var, TypeEnv.lookup]
      -- Apply weakening
      have heqv := weaken_capt_val_denot (env:=env0) (x:=n) (R:=access) (T:=T0)
      apply (Denot.equiv_to_imply heqv).1
      exact hih
    case tvar =>
      -- binding is .tvar Sb
      rename_i Sb
      cases env; rename_i info0 env0
      cases info0; rename_i d
      simp [EnvTyping] at hts
      obtain ⟨_, _, henv0⟩ := hts
      have hih := b henv0
      simp [TypeEnv.lookup_var, TypeEnv.lookup]
      have heqv := tweaken_capt_val_denot (env:=env0) (d:=d) (T:=T0)
      apply (Denot.equiv_to_imply heqv).1
      exact hih
    case cvar =>
      -- binding is .cvar Bb
      rename_i Bb
      cases env; rename_i info0 env0
      cases info0; rename_i A
      simp [EnvTyping] at hts
      obtain ⟨_, henv0⟩ := hts
      have hih := b henv0
      simp [TypeEnv.lookup_var, TypeEnv.lookup]
      have heqv := cweaken_capt_val_denot (env:=env0) (c:=A) (T:=T0)
      apply (Denot.equiv_to_imply heqv).1
      exact hih

theorem sem_typ_var
  (hx : Γ.LookupVar x T) :
  (.var (.bound x)) # Γ ⊨ (.var (.bound x)) : (.typ T) := by
  intro env store hts
  simp [Ty.exi_exp_denot, Ty.exi_val_denot]
  apply Eval.eval_var
  simp [Denot.as_mpost]
  exact typed_env_lookup_var hts hx

-- theorem sem_typ_abs
--   (ht : Cbody # (Γ,x:T1) ⊨ e : T2) :
--   Cfun # Γ ⊨ (.abs T1 e) : (.typ (.capt Cfun (.arrow T1 T2))) := by
--   intro env store hts
--   simp [Ty.exi_exp_denot, Ty.capt_val_denot, Ty.shape_val_denot, Ty.exi_val_denot]
--   apply Eval.eval_val
--   · simp [Exp.subst]; constructor
--   · simp [Denot.as_post]
--     use T1, e
--     constructor
--     · rfl
--     · intro arg H' hsubsume harg
--       simp [Exp.from_TypeEnv_weaken_open]
--       unfold SemanticTyping at ht
--       apply ht (env.extend_var arg (T1.captureSet.denot env)) H'
--       constructor
--       { exact harg }
--       { apply env_typing_monotonic hts hsubsume }

theorem sem_typ_abs {T2 : Ty TySort.exi (s,x)} {Cf : CaptureSet s}
  (ht : (Cf.rename Rename.succ ∪ .var (.bound .here)) # Γ,x:T1 ⊨ e : T2) :
  ∅ # Γ ⊨ Exp.abs Cf T1 e : .typ (Ty.capt Cf (T1.arrow T2)) := by
  intro env store hts
  simp [Ty.exi_exp_denot, Ty.exi_val_denot, Ty.capt_val_denot, Ty.shape_val_denot]
  apply Eval.eval_val
  · simp [Exp.subst]; constructor
  · simp [Denot.as_mpost]
    constructor
    · -- Prove well-formedness
      sorry  -- TODO: Prove WfInHeap for substituted capture set, type, and body
    · -- Provide the arrow denotation structure
      use (Cf.subst (Subst.from_TypeEnv env)), (T1.subst (Subst.from_TypeEnv env)),
        (e.subst (Subst.from_TypeEnv env).lift)
      constructor
      · -- Show that resolve gives back the abstraction
        simp [resolve, Exp.subst]
      · -- Show the function property
        intro arg H' hsubsume harg
        rw [Exp.from_TypeEnv_weaken_open (R := reachability_of_loc H' arg)]
        -- Apply the hypothesis
        have henv :
          EnvTyping (Γ,x:T1) (env.extend_var arg (reachability_of_loc H' arg)) H' := by
          constructor
          · exact harg
          · constructor
            · rfl
            · apply env_typing_monotonic hts hsubsume
        have this := ht (env.extend_var arg (reachability_of_loc H' arg)) H' henv
        simp [Ty.exi_exp_denot] at this
        -- Show capability sets match
        have hcap_rename :
          (Cf.rename Rename.succ).denot (env.extend_var arg (reachability_of_loc H' arg))
          = Cf.denot env := by
          have := rebind_captureset_denot (Rebind.weaken (env:=env) (x:=arg)
            (R:=reachability_of_loc H' arg)) Cf
          exact this.symm
        have hcap_var :
          (CaptureSet.var (.bound .here)).denot
            (env.extend_var arg (reachability_of_loc H' arg))
          = T1.captureSet.denot env := by
          simp [CaptureSet.denot, TypeEnv.lookup_var, TypeEnv.lookup, TypeEnv.extend_var]
          sorry  -- TODO: Need lemma relating reachability_of_loc to type's capture set
        rw [← hcap_rename, ← hcap_var]
        simp [CaptureSet.denot]
        exact this

-- theorem sem_typ_tabs
--   (ht : (Γ,X<:S) ⊨ e : T) :
--   Γ ⊨ (.tabs S e) : (.poly S T) := by
--   intro env store hts
--   simp [Ty.exp_denot]
--   apply Eval.eval_val
--   · simp [Exp.subst]; constructor
--   · simp [Ty.val_denot, Denot.as_post]
--     constructor; constructor
--     constructor
--     · rfl
--     · unfold SemanticTyping at ht
--       intro H denot Hs hdenot_mono hdenot_trans himply
--       simp [Exp.from_TypeEnv_weaken_open_tvar (d:=denot)]
--       apply ht
--       constructor
--       · exact hdenot_mono
--       · constructor
--         · exact hdenot_trans
--         · constructor
--           · exact himply
--           · apply env_typing_monotonic hts Hs

theorem sem_typ_tabs {T : Ty TySort.exi (s,X)} {Cf : CaptureSet s}
  (ht : Cf.rename Rename.succ # (Γ,X<:S) ⊨ e : T) :
  ∅ # Γ ⊨ Exp.tabs Cf S e : .typ (Ty.capt Cf (S.poly T)) := by
  intro env store hts
  simp [Ty.exi_exp_denot, Ty.exi_val_denot, Ty.capt_val_denot, Ty.shape_val_denot]
  apply Eval.eval_val
  · simp [Exp.subst]; constructor
  · simp [Denot.as_mpost]
    constructor
    · sorry  -- TODO: Prove WfInHeap for substituted capture set, type bound, and body
    · -- Need to provide cs, S0 and t0 for the poly denotation
      use (Cf.subst (Subst.from_TypeEnv env)), (S.subst (Subst.from_TypeEnv env)),
        (e.subst (Subst.from_TypeEnv env).lift)
      constructor
      · -- Show that resolve gives back the type abstraction
        simp [resolve, Exp.subst]
      · -- Show the polymorphic function property
        intro H' denot hsubsume hproper himply
        rw [Exp.from_TypeEnv_weaken_open_tvar (d := denot)]
        -- Apply the hypothesis
        have henv : EnvTyping (Γ,X<:S) (env.extend_tvar denot) H' := by
          constructor
          · exact hproper
          · constructor
            · exact himply
            · apply env_typing_monotonic hts hsubsume
        have this := ht (env.extend_tvar denot) H' henv
        simp [Ty.exi_exp_denot] at this
        -- Show capability sets match
        have hcap_rename :
          (Cf.rename Rename.succ).denot (env.extend_tvar denot) = Cf.denot env := by
          have := rebind_captureset_denot (Rebind.tweaken (env:=env) (d:=denot)) Cf
          exact this.symm
        rw [← hcap_rename]
        exact this

theorem sem_typ_cabs {T : Ty TySort.exi (s,C)} {Cf : CaptureSet s}
  (ht : Cf.rename Rename.succ # Γ,C<:cb ⊨ e : T) :
  ∅ # Γ ⊨ Exp.cabs Cf cb e : .typ (Ty.capt Cf (Ty.cpoly cb T)) := by
  intro env store hts
  simp [Ty.exi_exp_denot, Ty.exi_val_denot, Ty.capt_val_denot, Ty.shape_val_denot]
  apply Eval.eval_val
  · simp [Exp.subst]; constructor
  · simp [Denot.as_mpost]
    constructor
    · sorry  -- TODO: Prove WfInHeap for substituted capture set, bound, and body
    · -- Need to provide cs, B0 and t0 for the cpoly denotation
      use (Cf.subst (Subst.from_TypeEnv env)), (cb.subst (Subst.from_TypeEnv env)),
        (e.subst (Subst.from_TypeEnv env).lift)
      constructor
      · -- Show that resolve gives back the capture abstraction
        simp [resolve, Exp.subst]
      · -- Show the capture polymorphic function property
        intro H' CS hsubsume hsub_bound
        let A0 := CS.denot TypeEnv.empty
        -- Apply the hypothesis
        have henv : EnvTyping (Γ,C<:cb) (env.extend_cvar A0) H' := by
          constructor
          · exact hsub_bound
          · apply env_typing_monotonic hts hsubsume
        have this := ht (env.extend_cvar A0) H' henv
        simp [Ty.exi_exp_denot] at this
        -- Need to relate the two expression forms
        have hexp_equiv :
          (e.subst (Subst.from_TypeEnv (env.extend_cvar A0))) =
          ((e.subst (Subst.from_TypeEnv env).lift).subst (Subst.openCVar CS)) := by
          sorry  -- TODO: Need lemma from_TypeEnv_weaken_open_cvar for expression equality
        rw [hexp_equiv] at this
        -- Show capability sets match
        have hcap_rename :
          (Cf.rename Rename.succ).denot (env.extend_cvar A0) = Cf.denot env := by
          have := rebind_captureset_denot (Rebind.cweaken (env:=env) (c:=A0)) Cf
          exact this.symm
        rw [← hcap_rename]
        exact this

theorem abs_val_denot_inv {A : CapabilitySet}
  (hv : Ty.shape_val_denot env (.arrow T1 T2) A store (.var x)) :
  ∃ fx, x = .free fx
    ∧ ∃ cs T0 e0 hval R,
      store.heap fx = some (Cell.val ⟨Exp.abs cs T0 e0, hval, R⟩)
    ∧ (∀ (H' : Memory) (arg : Nat),
      H'.subsumes store ->
      Ty.capt_val_denot env T1 H' (.var (.free arg)) ->
      Ty.exi_exp_denot
        (env.extend_var arg (T1.captureSet.denot env))
        T2 (A ∪ T1.captureSet.denot env) H'
        (e0.subst (Subst.openVar (.free arg)))) := by
  cases x with
  | bound bx => cases bx
  | free fx =>
    simp [Ty.shape_val_denot, resolve] at hv
    obtain ⟨cs, T0, e0, hresolve, hfun⟩ := hv
    -- Analyze what's in the store at fx
    generalize hres : store.heap fx = res at hresolve ⊢
    cases res
    case none => simp at hresolve
    case some cell =>
      -- Match on the cell to extract HeapVal
      cases cell with
      | val hval =>
        -- hval : HeapVal, hresolve should relate to hval.unwrap
        simp [resolve] at hresolve
        cases hval with | mk unwrap isVal reachability =>
        simp at hresolve
        subst hresolve
        use fx, rfl, cs, T0, e0, isVal, reachability
        constructor
        · exact hres
        · intro H' arg hsub harg
          -- Need to relate reachability_of_loc to T1.captureSet.denot
          sorry  -- TODO: Lemma relating reachability_of_loc H' arg = T1.captureSet.denot env
      | capability =>
        simp [resolve] at hresolve

-- theorem tabs_val_denot_inv
--   (hv : Ty.val_denot env (.poly T1 T2) store (.var x)) :
--   ∃ fx, x = .free fx
--     ∧ ∃ T0 e0 hv, store fx = some ⟨.tabs T0 e0, hv⟩
--     ∧ (∀ (s' : Heap) (denot : Denot),
--       s'.subsumes store ->
--       denot.is_monotonic ->
--       denot.is_transparent ->
--       denot.ImplyAfter s' (Ty.val_denot env T1) ->
--       Ty.exp_denot (env.extend_tvar denot) T2 s' (e0.subst (Subst.openTVar .top))) := by
--   cases x with
--   | bound bx => cases bx
--   | free fx =>
--     simp [Ty.val_denot, resolve] at hv
--     generalize hres : store fx = res
--     cases res
--     case none => aesop
--     case some v =>
--       -- After substituting hres, resolve returns v.unwrap
--       -- So hv becomes: ∃ T0 e0, v.unwrap = .tabs T0 e0 ∧ ...
--       simp [hres] at hv
--       obtain ⟨T0, e0, htabs, hfun⟩ := hv
--       -- Now v.unwrap = .tabs T0 e0
--       -- We need to show store fx = some ⟨.tabs T0 e0, _⟩
--       -- We have hres : store fx = some v and htabs : v.unwrap = .tabs T0 e0
--       use fx, rfl, T0, e0
--       -- Need to provide proof that (tabs T0 e0).IsVal
--       have hval : (Exp.tabs T0 e0).IsVal := by constructor
--       use hval
--       constructor
--       · -- Show: store fx = some ⟨.tabs T0 e0, hval⟩
--         cases v with
--         | mk unwrap isVal =>
--           simp at htabs
--           subst htabs
--           exact hres
--       · exact hfun

theorem var_subst_is_free {x : BVar s .var} :
  ∃ fx, (Subst.from_TypeEnv env).var x = .free fx := by
  use (env.lookup_var x).1
  rfl

theorem var_exp_denot_inv {A : CapabilitySet}
  (hv : Ty.exi_exp_denot env T A store (.var x)) :
  Ty.exi_val_denot env T store (.var x) := by
  simp [Ty.exi_exp_denot] at hv
  cases hv
  case eval_val _ hQ => exact hQ
  case eval_var hQ => exact hQ

theorem closed_var_inv (x : Var .var {}) :
  ∃ fx, x = .free fx := by
  cases x
  case bound bx => cases bx
  case free fx => use fx

-- theorem sem_typ_app
--   (ht1 : Γ ⊨ (.var x) : (.arrow T1 T2))
--   (ht2 : Γ ⊨ (.var y) : T1) :
--   Γ ⊨ (.app x y) : (T2.subst (Subst.openVar y)) := by
--   intro env store hts
--   have h1 := ht1 env store hts
--   simp [Exp.subst] at h1
--   have h1' := var_exp_denot_inv h1
--   have ⟨fx, hfx, T0, hbody, _, hlk, hfun⟩ := abs_val_denot_inv h1'
--   simp [Exp.subst, hfx]
--   have h2 := ht2 env store hts
--   simp [Exp.subst] at h2
--   have h2' := var_exp_denot_inv h2
--   have ⟨farg, hfarg⟩ := closed_var_inv (y.subst (Subst.from_TypeEnv env))
--   have heq := hfarg
--   simp [<-interp_var_subst] at heq
--   simp [hfarg] at *
--   -- Apply hfun with store' = store (reflexive subsumption)
--   have := hfun store farg (Heap.subsumes_refl store) h2'
--   simp [Ty.exp_denot] at this ⊢
--   -- Use heq : interp_var env y = farg to rewrite in both goal and hypothesis
--   rw [<-heq]
--   rw [<-heq] at this
--   -- Convert postcondition via open_arg_val_denot
--   have heqv := open_arg_val_denot (env:=env) (y:=y) (T:=T2)
--   have hconv :=
--     eval_post_monotonic (Denot.imply_to_entails _ _ (Denot.equiv_to_imply heqv).1) this
--   apply Eval.eval_apply hlk hconv

theorem sem_typ_app
  (hx : C # Γ ⊨ .var x : (Ty.capt Cx (.arrow T1 T2)).typ)
  (hy : C # Γ ⊨ .var y : .typ T1) :
  C # Γ ⊨ Exp.app x y : T2.subst (Subst.openVar y) := by
  intro env store hts

  -- Apply hx and extract function properties
  have h1 := hx env store hts
  simp [Exp.subst] at h1
  have h1' := var_exp_denot_inv h1
  simp only [Ty.exi_val_denot, Ty.capt_val_denot] at h1'
  -- h1' is a conjunction: well-formedness ∧ shape_val_denot
  have ⟨fx, hfx, cs, T0, e0, hval, R, hlk, hfun⟩ := abs_val_denot_inv h1'.2

  -- Apply hy and extract argument properties
  have h2 := hy env store hts
  simp [Exp.subst] at h2
  have h2' := var_exp_denot_inv h2
  simp only [Ty.exi_val_denot] at h2'

  -- Show that after substitution, variables become specific free variables
  have hx_free : x.subst (Subst.from_TypeEnv env) = .free (interp_var env x).1 := by
    cases x with
    | bound bx => simp only [Var.subst, Subst.from_TypeEnv, interp_var]
    | free fx => simp only [Var.subst, interp_var]

  have hy_free : y.subst (Subst.from_TypeEnv env) = .free (interp_var env y).1 := by
    cases y with
    | bound bvar => simp only [Var.subst, Subst.from_TypeEnv, interp_var]
    | free fvar => simp only [Var.subst, interp_var]

  -- Connect with the fx from abs_val_denot_inv
  rw [hx_free] at hfx
  have hfx' : fx = (interp_var env x).1 := by cases hfx; rfl
  subst hfx'

  -- Similarly for y
  rw [hy_free] at h2'

  -- Simplify the goal
  simp [Exp.subst, hx_free, hy_free, Ty.exi_exp_denot]

  -- Apply the function to the argument
  -- Note: hfun expects the argument capability set to be T1.captureSet.denot env
  have happ := hfun store (interp_var env y).1 (Memory.subsumes_refl store) h2'

  -- PROBLEM 1: Need to relate extended environment to substitution
  -- The equivalence relates (interp_var env y).2 but we need to show it equals T1.captureSet
  have hy_capset : (interp_var env y).2 = T1.captureSet.denot env := by
    sorry  -- Need to prove: typed variables have matching capability sets
           -- This should follow from EnvTyping and the fact that y has type .typ T1

  -- PROBLEM 2: Need opening lemma for existential types
  have heqv : ∀ A,
    Ty.exi_exp_denot (env.extend_var (interp_var env y).1 (T1.captureSet.denot env)) T2 A ≈
    Ty.exi_exp_denot env (T2.subst (Subst.openVar y)) A := by
    sorry  -- MISSING LEMMA: open_arg_exi_exp_denot
           -- Should be liftable from open_arg_shape_val_denot

  -- Convert using equivalence
  have happ' : Ty.exi_exp_denot env (T2.subst (Subst.openVar y))
                  (Cx.denot env ∪ T1.captureSet.denot env) store
                  (e0.subst (Subst.openVar (.free (interp_var env y).1))) := by
    have h := heqv (Cx.denot env ∪ T1.captureSet.denot env) store
                   (e0.subst (Subst.openVar (.free (interp_var env y).1)))
    exact h.1 happ

  -- PROBLEM 3: Capability sets don't match
  -- happ' uses: (Cx.denot env ∪ T1.captureSet.denot env)
  -- Goal uses: C.denot env
  -- Need to show these are compatible or use monotonicity

  have hcap : C.denot env ⊆ Cx.denot env ∪ T1.captureSet.denot env := by
    sorry  -- MISSING: capability set relationship from typing
           -- The typing rule has both function and argument with capture set C
           -- But the function's type has capture set Cx
           -- Need to understand: does C ⊆ Cx hold? Or something else?

  -- Use capability set monotonicity
  have happ'' : Eval (C.denot env) store (e0.subst (Subst.openVar (.free (interp_var env y).1)))
                  (Ty.exi_val_denot env (T2.subst (Subst.openVar y))).as_mpost := by
    sorry  -- MISSING LEMMA: Eval monotonicity wrt capability sets
           -- Need: If A ⊆ B and Eval B H e Q, then Eval A H e Q (under some conditions)

  apply Eval.eval_apply hlk happ''

-- theorem sem_typ_tapp
--   (ht : Γ ⊨ (.var x) : (.poly S T)) :
--   Γ ⊨ (.tapp x S) : (T.subst (Subst.openTVar S)) := by
--   intro env store hts
--   have h1 := ht env store hts
--   simp [Exp.subst] at h1
--   have h1' := var_exp_denot_inv h1
--   have ⟨fx, hfx, T0, e0, _, hlk, hfun⟩ := tabs_val_denot_inv h1'
--   simp [Exp.subst, hfx]
--   -- Need to show Ty.val_denot env S is monotonic and transparent
--   have henv_mono := typed_env_is_monotonic hts
--   have henv_trans := typed_env_is_transparent hts
--   have hmono : (Ty.val_denot env S).is_monotonic := val_denot_is_monotonic henv_mono
--   have htrans : (Ty.val_denot env S).is_transparent := val_denot_is_transparent henv_trans
--   -- Prove reflexivity of ImplyAfter
--   have himply : (Ty.val_denot env S).ImplyAfter store (Ty.val_denot env S) := by
--     intro h' hsub e he
--     exact he
--   -- Apply hfun with heap, denot, monotonicity, transparency, and implication
--   have this := hfun store (Ty.val_denot env S) (Heap.subsumes_refl store) hmono htrans himply
--   simp [Ty.exp_denot] at this ⊢
--   -- Convert postcondition via open_targ_val_denot
--   have heqv := open_targ_val_denot (env:=env) (S:=S) (T:=T)
--   have hconv :=
--     eval_post_monotonic (Denot.imply_to_entails _ _ (Denot.equiv_to_imply heqv).1) this
--   apply Eval.eval_tapply hlk hconv

-- theorem sem_typ_letin
--   (ht1 : Γ ⊨ e1 : T)
--   (ht2 : (Γ,x:T) ⊨ e2 : (U.rename Rename.succ)) :
--   Γ ⊨ (.letin e1 e2) : U := by
--   intro env store hts
--   simp [Exp.subst]
--   simp [Ty.exp_denot]
--   -- Use Eval.eval_letin with Q1 = (Ty.val_denot env T).as_post
--   apply Eval.eval_letin (Q1 := (Ty.val_denot env T).as_post)
--   case hpred =>
--     -- Show (Ty.val_denot env T).as_post is monotonic
--     intro h1 h2 e hsub hQ
--     simp [Denot.as_post] at hQ ⊢
--     -- Need to show val_denot is monotonic under heap extension
--     have henv_mono := typed_env_is_monotonic hts
--     exact val_denot_is_monotonic henv_mono hsub hQ
--   case a =>
--     -- Show Eval store (e1.subst ...) (Ty.val_denot env T).as_post
--     have h1 := ht1 env store hts
--     simp [Ty.exp_denot] at h1
--     exact h1
--   case h_val =>
--     -- Handle the value case: e1 evaluated to a value v
--     intro h1 v hs1 hv_isval hQ1 l' hfresh
--     -- h1.subsumes store, v is a value, Q1 v h1 holds
--     simp [Denot.as_post] at hQ1
--     -- Apply ht2 with extended environment and heap
--     have ht2' := ht2 (env.extend_var l') (h1.extend l' ⟨v, hv_isval⟩)
--     simp [Ty.exp_denot] at ht2' ⊢
--     -- Rewrite to make expressions match
--     rw [<-Exp.from_TypeEnv_weaken_open] at ht2'
--     -- Convert postcondition using weaken_val_denot
--     apply eval_post_monotonic _ (ht2' _)
--     · -- Show postcondition entailment
--       apply Denot.imply_to_entails
--       have heqv := weaken_val_denot (env:=env) (x:=l') (T:=U)
--       apply (Denot.equiv_to_imply heqv).2
--     · -- Show: EnvTyping (Γ,x:T) (env.extend_var l') (h1.extend l' ⟨v, hv_isval⟩)
--       constructor
--       · -- Show: Ty.val_denot env T (h1.extend l' ⟨v, hv_isval⟩) (Exp.var (Var.free l'))
--         -- We have: hQ1 : Ty.val_denot env T h1 v (value v has type T)
--         -- Strategy: Use monotonicity to lift hQ1 to extended heap, then use transparency

--         -- Step 0: Prove heap subsumption
--         have hext : (h1.extend l' ⟨v, hv_isval⟩).subsumes h1 := by
--           intro x v' hx
--           simp [Heap.extend]
--           split
--           · next heq =>
--               rw [heq] at hx
--               rw [hfresh] at hx
--               contradiction
--           · exact hx

--         -- Step 1: Lift hQ1 to extended heap using monotonicity
--         have henv_mono := typed_env_is_monotonic hts
--         have hQ1_lifted : Ty.val_denot env T (h1.extend l' ⟨v, hv_isval⟩) v :=
--           val_denot_is_monotonic henv_mono hext hQ1

--         -- Step 2: Apply transparency
--         have henv_trans := typed_env_is_transparent hts
--         have htrans : (Ty.val_denot env T).is_transparent :=
--           val_denot_is_transparent henv_trans

--         -- Step 3: Use the heap lookup fact
--         have hlookup : (h1.extend l' ⟨v, hv_isval⟩) l' = some ⟨v, hv_isval⟩ :=
--           Heap.extend_lookup_eq h1 l' ⟨v, hv_isval⟩

--         -- Step 4: Apply transparency with the lifted property
--         -- Note: ⟨v, hv_isval⟩.unwrap = v
--         apply htrans hlookup hQ1_lifted
--       · -- Show: EnvTyping Γ env (h1.extend l' ⟨v, hv_isval⟩)
--         -- Original typing preserved under heap extension
--         -- h1.subsumes store, and (h1.extend l' ...).subsumes h1
--         have hext : (h1.extend l' ⟨v, hv_isval⟩).subsumes h1 := by
--           intro x v' hx
--           simp [Heap.extend]
--           split
--           · -- Case: x = l', but h1 l' = none (from hfresh)
--             -- So h1 x = h1 l' = none, contradicting hx : h1 x = some v'
--             next heq =>
--               rw [heq] at hx
--               rw [hfresh] at hx
--               contradiction
--           · exact hx
--         have hsub_trans : (h1.extend l' ⟨v, hv_isval⟩).subsumes store := by
--           exact Heap.subsumes_trans hext hs1
--         exact env_typing_monotonic hts hsub_trans
--   case h_var =>
--     -- Handle the variable case: e1 evaluated to variable x
--     intro h1 x hs1 hQ1
--     -- h1.subsumes store, Q1 (.var x) h1 holds
--     simp [Denot.as_post] at hQ1
--     -- Determine what x is
--     have ⟨fx, hfx⟩ := closed_var_inv x
--     subst hfx
--     -- Apply ht2 with extended environment where the variable is bound to fx
--     have ht2' := ht2 (env.extend_var fx) h1
--     simp [Ty.exp_denot] at ht2' ⊢
--     rw [<-Exp.from_TypeEnv_weaken_open] at ht2'
--     -- Convert postcondition
--     apply eval_post_monotonic _ (ht2' _)
--     · -- Show postcondition entailment
--       apply Denot.imply_to_entails
--       have heqv := weaken_val_denot (env:=env) (x:=fx) (T:=U)
--       apply (Denot.equiv_to_imply heqv).2
--     · -- Show: EnvTyping (Γ,x:T) (env.extend_var fx) h1
--       constructor
--       · -- Variable fx has type T in heap h1
--         exact hQ1
--       · -- Original typing preserved: EnvTyping Γ env h1
--         exact env_typing_monotonic hts hs1

-- theorem typed_env_lookup_tvar
--   (hts : EnvTyping Γ env store)
--   (hx : Ctx.LookupTVar Γ X S) :
--   (env.lookup_tvar X).ImplyAfter store (Ty.val_denot env S) := by
--   induction hx generalizing store
--   case here =>
--     -- In here case, S✝ is the actual type from the predecessor context
--     -- Goal: d.ImplyAfter store (Ty.val_denot (env0.extend_tvar d) (S✝.rename Rename.succ))
--     cases env; rename_i info0 env0
--     cases info0; rename_i d
--     simp [EnvTyping] at hts
--     simp [TypeEnv.lookup_tvar, TypeEnv.lookup]
--     have ⟨_, _, hd, _⟩ := hts
--     apply Denot.imply_after_trans
--     · exact hd
--     · -- Convert equivalence to ImplyAfter
--       intro h' hsub e he
--       exact (tweaken_val_denot h' e).mp he
--   case there b _ ih =>
--     -- In there case, we need to lift the IH through weakening
--     -- IH gives: (env0.lookup_tvar X✝).ImplyAfter store (Ty.val_denot env0 S✝)
--     -- Need: (env0.lookup_tvar X✝).ImplyAfter store
--     --       (Ty.val_denot (env0.extend_...) (S✝.rename Rename.succ))
--     cases env; rename_i info0 env0
--     cases info0
--     case var =>
--       rename_i n
--       cases b
--       simp [EnvTyping] at hts
--       obtain ⟨_, henv⟩ := hts
--       specialize ih henv
--       simp [TypeEnv.lookup_tvar, TypeEnv.lookup]
--       apply Denot.imply_after_trans
--       · exact ih
--       · intro h' hsub e he
--         exact (weaken_val_denot h' e).mp he
--     case tvar =>
--       rename_i d
--       cases b
--       simp [EnvTyping] at hts
--       obtain ⟨_, _, _, henv⟩ := hts
--       specialize ih henv
--       simp [TypeEnv.lookup_tvar, TypeEnv.lookup]
--       apply Denot.imply_after_trans
--       · exact ih
--       · intro h' hsub e he
--         exact (tweaken_val_denot h' e).mp he

-- lemma sem_subtyp_poly
--   (hS : SemSubtyp Γ S2 S1) -- contravariant in bound
--   (hT : SemSubtyp (Γ,X<:S2) T1 T2) -- covariant in body, under extended context
--   : SemSubtyp Γ (.poly S1 T1) (.poly S2 T2) := by
--   intro type_env heap hts
--   intro heap' hheap
--   intro ans hans
--   simp [Ty.val_denot] at hans ⊢
--   obtain ⟨T0, e0, hresolve, hfun⟩ := hans
--   use T0, e0
--   apply And.intro hresolve
--   intro H denot Hsub hdenot_mono hdenot_trans himply_S2
--   -- hfun expects denot.ImplyAfter H (Ty.val_denot type_env S1)
--   -- We have himply_S2 : denot.ImplyAfter H (Ty.val_denot type_env S2)
--   -- And hS : SemSubtyp Γ S2 S1, i.e., S2 <: S1
--   -- So we need to compose: denot -> S2 -> S1
--   have himply_S1 : denot.ImplyAfter H (Ty.val_denot type_env S1) := by
--     intro h' hs' e hdenot
--     have hS2 := himply_S2 h' hs' e hdenot
--     -- Apply hS at h'
--     have hS_trans := Heap.subsumes_trans hs' (Heap.subsumes_trans Hsub hheap)
--     apply hS type_env heap hts h' hS_trans e hS2
--   -- Apply the original function with this denot
--   have heval1 := hfun H denot Hsub hdenot_mono hdenot_trans himply_S1
--   -- Now use covariance hT
--   have henv' : EnvTyping (Γ,X<:S2) (type_env.extend_tvar denot) H := by
--     constructor
--     · exact hdenot_mono
--     · constructor
--       · exact hdenot_trans
--       · constructor
--         · exact himply_S2
--         · apply env_typing_monotonic hts (Heap.subsumes_trans Hsub hheap)
--   have hT_applied := hT (type_env.extend_tvar denot) H henv'
--   apply Denot.apply_imply_at heval1
--   apply Denot.imply_after_to_imply_at
--   apply denot_implyat_lift hT_applied

-- lemma sem_subtyp_arrow
--   (hT : SemSubtyp Γ T2 T1)
--   (hU : SemSubtyp (Γ,x:T2) U1 U2) :
--   SemSubtyp Γ (.arrow T1 U1) (.arrow T2 U2) := by
--   intro type_env heap hts
--   intro heap' hheap
--   intro ans hans
--   simp [Ty.val_denot] at hans ⊢
--   obtain ⟨T0, e0, hresolve, hfun⟩ := hans
--   use T0, e0
--   apply And.intro hresolve
--   intro H arg hheap1 ht_arg
--   specialize hfun H arg hheap1
--   have ht_arg' := hT type_env heap hts H (Heap.subsumes_trans hheap1 hheap) _ ht_arg
--   specialize hfun ht_arg'
--   specialize hU (type_env.extend_var arg)
--   have henv' : EnvTyping (Γ,x:T2) (type_env.extend_var arg) H := by
--     constructor
--     · exact ht_arg
--     · apply env_typing_monotonic hts
--       apply Heap.subsumes_trans hheap1 hheap
--   specialize hU H henv'
--   apply Denot.apply_imply_at hfun
--   apply Denot.imply_after_to_imply_at
--   apply denot_implyat_lift hU

-- lemma sem_subtyp_top {T : Ty .shape s} :
--   SemSubtyp Γ T .top := by
--   intro type_env heap hts
--   intro heap' hheap
--   intro e he
--   simp [Ty.val_denot]

-- lemma sem_subtyp_refl {T : Ty .shape s} :
--   SemSubtyp Γ T T := by
--   intro type_env heap hts
--   intro heap' hheap
--   apply Denot.imply_refl

-- lemma sem_subtyp_trans
--   (hsub1 : SemSubtyp Γ T1 T2)
--   (hsub2 : SemSubtyp Γ T2 T3) :
--   SemSubtyp Γ T1 T3 := by
--   intro type_env heap hts
--   intro heap' hheap
--   specialize hsub1 type_env heap hts heap' hheap
--   specialize hsub2 type_env heap hts heap' hheap
--   apply Denot.implyat_trans hsub1 hsub2

-- lemma sem_subtyp_tvar
--   (hX : Ctx.LookupTVar Γ X S) :
--   SemSubtyp Γ (.tvar X) S := by
--   intro type_env heap hts
--   intro heap' hheap
--   simp [Ty.val_denot]
--   apply typed_env_lookup_tvar hts hX heap' hheap

-- theorem fundamental_subtyp
--   (hsub : Subtyp Γ T1 T2) :
--   SemSubtyp Γ T1 T2 := by
--   induction hsub
--   case top => grind [sem_subtyp_top]
--   case refl => grind [sem_subtyp_refl]
--   case trans => grind [sem_subtyp_trans]
--   case tvar => grind [sem_subtyp_tvar]
--   case arrow => grind [sem_subtyp_arrow]
--   case poly => grind [sem_subtyp_poly]

-- theorem sem_typ_subtyp
--   (ht : Γ ⊨ e : T1)
--   (hsub : Subtyp Γ T1 T2) :
--   Γ ⊨ e : T2 := by
--   intro env store hts
--   have h1 := ht env store hts
--   simp [Ty.exp_denot] at h1 ⊢
--   have hsub' := fundamental_subtyp hsub env store hts
--   apply eval_post_monotonic_general _ h1
--   apply Denot.imply_after_to_entails_after
--   exact hsub'

/-- The fundamental theorem of semantic type soundness. -/
theorem fundamental
  (ht : C # Γ ⊢ e : T) :
  C # Γ ⊨ e : T := by
  induction ht
  case var hx => apply sem_typ_var hx
  case abs => grind [sem_typ_abs]
  case tabs ih => apply sem_typ_tabs ih
  case cabs ih => apply sem_typ_cabs ih
  case app => grind [sem_typ_app]
  -- case tapp => grind [sem_typ_tapp]
  -- case capp => grind [sem_typ_capp]
  -- case letin => grind [sem_typ_letin]
  -- case subtyp => grind [sem_typ_subtyp]
  all_goals sorry

end CC
