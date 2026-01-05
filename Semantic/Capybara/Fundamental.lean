import Semantic.Capybara.Denotation
import Semantic.Capybara.Semantics
namespace Capybara

theorem typed_env_lookup_var
  (hts : EnvTyping Γ env store)
  (hx : Ctx.LookupVar Γ x T) :
  Ty.val_denot env T store (.var (.free (env.lookup_var x).1)) := by
  induction hx generalizing store
  case here =>
    -- The environment must match the context structure
    rename_i Γ0 T0
    cases env with
    | extend env0 info =>
      cases info with
      | var n ps =>
        simp only [EnvTyping, TypeEnv.lookup_var] at hts ⊢
        -- Apply weaken_val_denot equivalence
        have heqv := weaken_val_denot (env:=env0) (x:=n) (ps:=ps) (T:=T0)
        apply (Denot.equiv_to_imply heqv).1
        exact hts.1
  case there b =>
    -- Need to handle three cases based on the binding kind
    rename_i k Γ0 x0 T0 binding hlk
    cases binding
    case var =>
      -- binding is .var Tb
      rename_i Tb
      cases env with
      | extend env0 info =>
        cases info with
        | var n ps =>
          simp only [EnvTyping, TypeEnv.lookup_var] at hts ⊢
          obtain ⟨_, _, henv0⟩ := hts
          -- Apply IH to get the result for env0
          have hih := b henv0
          -- Apply weakening
          have heqv := weaken_val_denot (env:=env0) (x:=n) (ps:=ps) (T:=T0)
          apply (Denot.equiv_to_imply heqv).1
          exact hih
    case tvar =>
      -- binding is .tvar Sb
      rename_i Sb
      match env with
      | .extend env0 (.tvar d) =>
        simp only [EnvTyping, TypeEnv.lookup_var] at hts ⊢
        obtain ⟨_, _, _, _, _, henv0⟩ := hts
        have hih := b henv0
        have heqv := tweaken_val_denot (env:=env0) (d:=d) (T:=T0)
        apply (Denot.equiv_to_imply heqv).1
        exact hih
    case cvar =>
      -- binding is .cvar Bb
      rename_i Bb
      match env with
      | .extend env0 (.cvar cs) =>
        simp only [EnvTyping, TypeEnv.lookup_var] at hts ⊢
        obtain ⟨_, _, henv0⟩ := hts
        have hih := b henv0
        have heqv := cweaken_val_denot (env:=env0) (cs:=cs) (T:=T0)
        apply (Denot.equiv_to_imply heqv).1
        exact hih


theorem typed_env_lookup_var_reachability
  (hts : EnvTyping Γ env m)
  (hx : Ctx.LookupVar Γ x T) :
  reachability_of_loc m.heap (env.lookup_var x).1 ⊆ T.captureSet.denot env m := by
  -- Use typed_env_lookup_var to get the value denotation
  have hval := typed_env_lookup_var hts hx
  -- Apply val_denot_enforces_captures to get reachability bound
  have hreach := val_denot_enforces_captures hts (.var (.free (env.lookup_var x).1)) hval
  -- resolve_reachability of a free variable is reachability_of_loc by definition
  simp only [resolve_reachability] at hreach
  exact hreach

theorem sem_typ_var
  (hx : Γ.LookupVar x T) :
  (.var .epsilon (.bound x)) # Γ ⊨ (Exp.var (.bound x)) :
    (.typ (T.refineCaptureSet (.var .epsilon (.bound x)))) := by
  intro env m hts
  simp only [Ty.exi_exp_denot, Ty.exi_val_denot]
  apply Eval.eval_var
  simp only [Denot.as_mpost]
  -- From typed_env_lookup_var, we get that .var (.free n) satisfies T
  have h_lookup := typed_env_lookup_var hts hx
  -- Use val_denot_refine to get the refined type denotation
  have h_refined := val_denot_refine (x := .bound x) h_lookup
  simp only [Var.subst, Subst.from_TypeEnv] at h_refined
  exact h_refined


theorem expand_captures_eq_ground_denot (cs : CaptureSet {}) (m : Memory) :
  expand_captures m.heap cs = cs.ground_denot m := by
  induction cs with
  | empty => rfl
  | var m v =>
    cases v with
    | free x => rfl
    | bound bv => cases bv
  | cvar m cv => cases cv
  | union cs1 cs2 ih1 ih2 =>
    simp [expand_captures, CaptureSet.ground_denot, ih1, ih2]

theorem sem_typ_abs {T2 : Ty TySort.exi (s,x)} {Cf : CaptureSet s}
  (hclosed_abs : (Exp.abs Cf T1 e).IsClosed)
  (ht : (Cf.rename Rename.succ ∪ .var .epsilon (.bound .here)) # Γ,x:T1 ⊨ e : T2) :
  ∅ # Γ ⊨ Exp.abs Cf T1 e : (T1.arrow Cf T2).typ := by
  intro env store hts
  simp only [Ty.exi_exp_denot, Ty.exi_val_denot]
  apply Eval.eval_val
  · simp [Exp.subst]; constructor
  · simp only [Denot.as_mpost, Ty.val_denot]
    -- Goal structure for arrow val_denot:
    -- 1. e.WfInHeap m.heap
    -- 2. (cs.subst ...).WfInHeap m.heap
    -- 3. ∃ cs' T0 t0, resolve ... = some (.abs cs' T0 t0) ∧ ...
    constructor
    · -- 1. Prove (abs ...).WfInHeap store.heap
      apply Exp.wf_subst
      · apply Exp.wf_of_closed hclosed_abs
      · apply from_TypeEnv_wf_in_heap hts
    · constructor
      · -- 2. Prove (Cf.subst ...).WfInHeap store.heap
        apply CaptureSet.wf_subst
        · apply CaptureSet.wf_of_closed
          cases hclosed_abs
          assumption
        · apply from_TypeEnv_wf_in_heap hts
      · -- 3. Provide existential witnesses: cs', T0, t0
        use (Cf.subst (Subst.from_TypeEnv env)), (T1.subst (Subst.from_TypeEnv env)),
          (e.subst (Subst.from_TypeEnv env).lift)
        constructor
        · -- Show that resolve gives back the abstraction
          simp [resolve, Exp.subst]
        · constructor
          · -- Prove cs'.WfInHeap store.heap
            apply CaptureSet.wf_subst
            · apply CaptureSet.wf_of_closed
              cases hclosed_abs
              assumption
            · apply from_TypeEnv_wf_in_heap hts
          · constructor
            · -- Prove expand_captures ... ⊆ Cf.denot env store
              rw [expand_captures_eq_ground_denot]
              simp [CaptureSet.denot]
              apply CapabilitySet.Subset.refl
            · -- Show the function property
              intro arg m' hsub harg
              -- Use compute_peakset which equals peakset by compute_peakset_correct
              let ps := compute_peakset env T1.captureSet
              rw [Exp.from_TypeEnv_weaken_open (ps:=ps)]
              -- Build EnvTyping using the computed peak set
              have henv :
                EnvTyping (Γ,x:T1) (env.extend_var arg ps) m' := by
                constructor
                · exact harg
                · constructor
                  · exact (compute_peakset_correct hts T1.captureSet).symm
                  · apply env_typing_monotonic hts hsub
              -- Apply the hypothesis directly (no Rebind needed)
              have htyped := ht (env.extend_var arg ps) m' henv
              simp only [Ty.exi_exp_denot] at htyped ⊢
              -- Show capability sets match
              have hcap_rename :
                (Cf.rename Rename.succ).denot (env.extend_var arg ps)
                = Cf.denot env := by
                have := rebind_captureset_denot
                  (Rebind.weaken (env:=env) (x:=arg) (ps:=ps)) Cf
                exact this.symm
              -- Variable .here denotes to the reachability we stored
              have hcap_var :
                (CaptureSet.var .epsilon (.bound .here)).denot (env.extend_var arg ps) m'
                = reachability_of_loc m'.heap arg := by
                simp [CaptureSet.denot, CaptureSet.ground_denot, CaptureSet.subst,
                      Subst.from_TypeEnv, Var.subst]
                rfl
              -- Use monotonicity to relate capture set denotations at different memories
              have hCf_mono : Cf.denot env store = Cf.denot env m' := by
                -- Extract closedness of Cf from hclosed_abs
                have hCf_closed : Cf.IsClosed := by
                  cases hclosed_abs
                  assumption
                -- Closed capture sets are well-formed in any heap
                have hwf_Cf : (Cf.subst (Subst.from_TypeEnv env)).WfInHeap store.heap := by
                  apply CaptureSet.wf_subst
                  · apply CaptureSet.wf_of_closed hCf_closed
                  · apply from_TypeEnv_wf_in_heap hts
                exact capture_set_denot_is_monotonic hwf_Cf hsub
              -- Show the authority matches by rewriting with equalities
              have hauthority :
                (Cf.rename Rename.succ ∪ .var .epsilon (.bound .here)).denot
                  (env.extend_var arg ps) m' =
                expand_captures store.heap (Cf.subst (Subst.from_TypeEnv env)) ∪
                  reachability_of_loc m'.heap arg := by
                calc (Cf.rename Rename.succ ∪ .var .epsilon (.bound .here)).denot
                      (env.extend_var arg ps) m'
                  _ = (Cf.rename Rename.succ).denot (env.extend_var arg ps) m' ∪
                      (CaptureSet.var .epsilon (.bound .here)).denot
                        (env.extend_var arg ps) m' := by
                    simp [CaptureSet.denot, CaptureSet.ground_denot,
                          CaptureSet.subst]
                  _ = Cf.denot env m' ∪ reachability_of_loc m'.heap arg := by
                    rw [congrFun hcap_rename m', hcap_var]
                  _ = Cf.denot env store ∪
                      reachability_of_loc m'.heap arg := by
                    rw [← hCf_mono]
                  _ = (Cf.subst (Subst.from_TypeEnv env)).ground_denot store ∪
                      reachability_of_loc m'.heap arg := by
                    simp [CaptureSet.denot]
                  _ = expand_captures store.heap (Cf.subst (Subst.from_TypeEnv env)) ∪
                      reachability_of_loc m'.heap arg := by
                    rw [← expand_captures_eq_ground_denot]
              rw [← hauthority]
              exact htyped


theorem sem_typ_tabs {T : Ty TySort.exi (s,X)} {Cf : CaptureSet s} {S : PureTy s}
  (hclosed_tabs : (Exp.tabs Cf S e).IsClosed)
  (ht : Cf.rename Rename.succ # (Γ,X<:S) ⊨ e : T) :
  ∅ # Γ ⊨ Exp.tabs Cf S e : (S.core.poly Cf T).typ := by
  intro env store hts
  simp only [Ty.exi_exp_denot, Ty.exi_val_denot]
  apply Eval.eval_val
  · simp [Exp.subst]; constructor
  · simp only [Denot.as_mpost, Ty.val_denot]
    -- Goal structure for poly val_denot:
    -- 1. e.WfInHeap m.heap
    -- 2. (cs.subst ...).WfInHeap m.heap
    -- 3. ∃ cs' S0 t0, resolve ... = some (.tabs cs' S0 t0) ∧ ...
    constructor
    · -- 1. Prove (tabs ...).WfInHeap store.heap
      apply Exp.wf_subst
      · apply Exp.wf_of_closed hclosed_tabs
      · apply from_TypeEnv_wf_in_heap hts
    · constructor
      · -- 2. Prove (Cf.subst ...).WfInHeap store.heap
        apply CaptureSet.wf_subst
        · apply CaptureSet.wf_of_closed
          cases hclosed_tabs
          assumption
        · apply from_TypeEnv_wf_in_heap hts
      · -- 3. Provide existential witnesses: cs', S0, t0
        use (Cf.subst (Subst.from_TypeEnv env)), (S.subst (Subst.from_TypeEnv env)),
          (e.subst (Subst.from_TypeEnv env).lift)
        constructor
        · -- Show that resolve gives back the type abstraction
          simp [resolve, Exp.subst]
        · constructor
          · -- Prove cs'.WfInHeap store.heap
            apply CaptureSet.wf_subst
            · apply CaptureSet.wf_of_closed
              cases hclosed_tabs
              assumption
            · apply from_TypeEnv_wf_in_heap hts
          · constructor
            · -- Prove expand_captures ... ⊆ Cf.denot env store
              rw [expand_captures_eq_ground_denot]
              simp [CaptureSet.denot]
              apply CapabilitySet.Subset.refl
            · -- Show the polymorphic function property
              intro m' denot hsub hproper himply_simple_ans himply hpure
              rw [Exp.from_TypeEnv_weaken_open_tvar (d := denot)]
              -- Build EnvTyping using the type denotation
              have henv : EnvTyping (Γ,X<:S) (env.extend_tvar denot) m' := by
                constructor
                · exact hproper
                · constructor
                  · -- denot.implies_wf: now included in is_proper
                    exact hproper.2.2.2
                  · constructor
                    · exact himply_simple_ans
                    · constructor
                      · exact himply
                      · constructor
                        · exact hpure
                        · apply env_typing_monotonic hts hsub
              -- Apply the hypothesis
              have htyped := ht (env.extend_tvar denot) m' henv
              simp only [Ty.exi_exp_denot] at htyped ⊢
              -- Show capability sets match
              have hcap_rename :
                (Cf.rename Rename.succ).denot (env.extend_tvar denot) = Cf.denot env := by
                have := rebind_captureset_denot (Rebind.tweaken (env:=env) (d:=denot)) Cf
                exact this.symm
              -- Use monotonicity to relate capture set denotations at different memories
              have hCf_mono : Cf.denot env store = Cf.denot env m' := by
                -- Extract closedness of Cf from hclosed_tabs
                have hCf_closed : Cf.IsClosed := by
                  cases hclosed_tabs
                  assumption
                -- Closed capture sets are well-formed in any heap
                have hwf_Cf : (Cf.subst (Subst.from_TypeEnv env)).WfInHeap store.heap := by
                  apply CaptureSet.wf_subst
                  · apply CaptureSet.wf_of_closed hCf_closed
                  · apply from_TypeEnv_wf_in_heap hts
                exact capture_set_denot_is_monotonic hwf_Cf hsub
              -- Show the authority matches
              have hauthority :
                (Cf.rename Rename.succ).denot (env.extend_tvar denot) m' =
                expand_captures store.heap (Cf.subst (Subst.from_TypeEnv env)) := by
                calc (Cf.rename Rename.succ).denot (env.extend_tvar denot) m'
                  _ = Cf.denot env m' := by rw [congrFun hcap_rename m']
                  _ = Cf.denot env store := by rw [← hCf_mono]
                  _ = (Cf.subst (Subst.from_TypeEnv env)).ground_denot store := by
                    simp [CaptureSet.denot]
                  _ = expand_captures store.heap (Cf.subst (Subst.from_TypeEnv env)) := by
                    rw [← expand_captures_eq_ground_denot]
              rw [← hauthority]
              exact htyped


theorem sem_typ_cabs {T : Ty TySort.exi (s,C)} {Cf : CaptureSet s} {cb : Mutability}
  (hclosed_cabs : (Exp.cabs Cf cb e).IsClosed)
  (ht : Cf.rename Rename.succ # Γ,C<:cb ⊨ e : T) :
  ∅ # Γ ⊨ Exp.cabs Cf cb e : (Ty.cpoly cb Cf T).typ := by
  intro env store hts
  simp only [Ty.exi_exp_denot, Ty.exi_val_denot]
  apply Eval.eval_val
  · simp [Exp.subst]; constructor
  · simp only [Denot.as_mpost, Ty.val_denot]
    -- Goal structure for cpoly val_denot:
    -- 1. e.WfInHeap m.heap
    -- 2. (cs.subst ...).WfInHeap m.heap
    -- 3. ∃ cs' B0 t0, resolve ... = some (.cabs cs' B0 t0) ∧ ...
    constructor
    · -- 1. Prove (cabs ...).WfInHeap store.heap
      apply Exp.wf_subst
      · apply Exp.wf_of_closed hclosed_cabs
      · apply from_TypeEnv_wf_in_heap hts
    · constructor
      · -- 2. Prove (Cf.subst ...).WfInHeap store.heap
        apply CaptureSet.wf_subst
        · apply CaptureSet.wf_of_closed
          cases hclosed_cabs
          assumption
        · apply from_TypeEnv_wf_in_heap hts
      · -- 3. Provide existential witnesses: cs', B0, t0
        use (Cf.subst (Subst.from_TypeEnv env)), cb,
          (e.subst (Subst.from_TypeEnv env).lift)
        constructor
        · -- Show that resolve gives back the capture abstraction
          simp [resolve, Exp.subst]
        · constructor
          · -- Prove cs'.WfInHeap store.heap
            apply CaptureSet.wf_subst
            · apply CaptureSet.wf_of_closed
              cases hclosed_cabs
              assumption
            · apply from_TypeEnv_wf_in_heap hts
          · constructor
            · -- Prove expand_captures ... ⊆ Cf.denot env store
              rw [expand_captures_eq_ground_denot]
              simp [CaptureSet.denot]
              apply CapabilitySet.Subset.refl
            · -- Show the capture polymorphic function property
              intro m' CS hwf hsub hsub_bound
              rw [Exp.from_TypeEnv_weaken_open_cvar (cs:=CS)]
              -- Build EnvTyping
              have henv : EnvTyping (Γ,C<:cb) (env.extend_cvar CS) m' := by
                constructor
                · exact hwf  -- CS.WfInHeap m'.heap
                · constructor
                  · -- Need to show: (CS.ground_denot m').BoundedBy (cb.denot m')
                    have heq : CS.ground_denot = CaptureSet.denot TypeEnv.empty CS := by
                      funext m
                      simp [CaptureSet.denot, Subst.from_TypeEnv_empty, CaptureSet.subst_id]
                    rw [heq]
                    exact hsub_bound
                  · apply env_typing_monotonic hts hsub
              -- Apply the hypothesis
              have htyped := ht (env.extend_cvar CS) m' henv
              simp only [Ty.exi_exp_denot] at htyped ⊢
              -- Show capability sets match
              have hcap_rename :
                (Cf.rename Rename.succ).denot (env.extend_cvar CS) = Cf.denot env := by
                have := rebind_captureset_denot (Rebind.cweaken (env:=env) (cs:=CS)) Cf
                exact this.symm
              -- Use monotonicity
              have hCf_mono : Cf.denot env store = Cf.denot env m' := by
                have hCf_closed : Cf.IsClosed := by
                  cases hclosed_cabs
                  assumption
                have hwf_Cf : (Cf.subst (Subst.from_TypeEnv env)).WfInHeap store.heap := by
                  apply CaptureSet.wf_subst
                  · apply CaptureSet.wf_of_closed hCf_closed
                  · apply from_TypeEnv_wf_in_heap hts
                exact capture_set_denot_is_monotonic hwf_Cf hsub
              -- Show the authority matches
              have hauthority :
                (Cf.rename Rename.succ).denot (env.extend_cvar CS) m' =
                expand_captures store.heap (Cf.subst (Subst.from_TypeEnv env)) := by
                calc (Cf.rename Rename.succ).denot (env.extend_cvar CS) m'
                  _ = Cf.denot env m' := by rw [congrFun hcap_rename m']
                  _ = Cf.denot env store := by rw [← hCf_mono]
                  _ = (Cf.subst (Subst.from_TypeEnv env)).ground_denot store := by
                    simp [CaptureSet.denot]
                  _ = expand_captures store.heap (Cf.subst (Subst.from_TypeEnv env)) := by
                    rw [← expand_captures_eq_ground_denot]
              rw [← hauthority]
              exact htyped


theorem sem_typ_pack
  {T : Ty .capt (s,C)} {cs : CaptureSet s} {x : Var .var s} {Γ : Ctx s}
  (hclosed_e : (Exp.pack cs x).IsClosed)
  (ht : CaptureSet.var .epsilon x # Γ ⊨ Exp.var x : (T.subst (Subst.openCVar cs)).typ) :
  CaptureSet.var .epsilon x # Γ ⊨ Exp.pack cs x : T.exi := by
  intro env store hts
  simp [Ty.exi_exp_denot, Ty.exi_val_denot]
  -- pack cs x is a value, so we use eval_val
  apply Eval.eval_val
  · constructor -- pack is a value
  · simp [Denot.as_mpost]
    -- Goal: match (resolve store.heap (pack cs x).subst ...) with ...
    -- Simplify: resolve of a pack returns the pack itself
    have : (Exp.pack cs x).subst (Subst.from_TypeEnv env) =
           Exp.pack (cs.subst (Subst.from_TypeEnv env)) (x.subst (Subst.from_TypeEnv env)) := by
      simp [Exp.subst]
    rw [this]
    simp [resolve]
    -- Goal: CS.WfInHeap ∧ capt_val_denot (env.extend_cvar ...) T store ...
    constructor
    · -- Well-formedness of the capture set
      -- cs is closed (from hclosed_e), so cs.subst is well-formed
      have hclosed_cs : cs.IsClosed := by
        cases hclosed_e with
        | pack hcs_closed _hx_closed => exact hcs_closed
      apply CaptureSet.wf_subst
      · exact CaptureSet.wf_of_closed hclosed_cs
      · exact from_TypeEnv_wf_in_heap hts
    · -- From ht, we have semantic typing for x at type T.subst (Subst.openCVar cs)
      have hx := ht env store hts
      simp [Ty.exi_exp_denot, Ty.exi_val_denot] at hx
      -- hx : Eval ... store ((Exp.var x).subst ...)
      --      (capt_val_denot env (T.subst (Subst.openCVar cs))).as_mpost
      -- Since (Exp.var x).subst is a variable, invert the Eval
      have : (Exp.var x).subst (Subst.from_TypeEnv env) =
             Exp.var (x.subst (Subst.from_TypeEnv env)) := by
        cases x <;> simp [Exp.subst, Var.subst]
      rw [this] at hx
      cases hx
      case eval_var hQ =>
        -- hQ : (val_denot env (T.subst (Subst.openCVar cs))).as_mpost ...
        simp [Denot.as_mpost] at hQ
        -- hQ : val_denot env (T.subst (Subst.openCVar cs)) store (var (x.subst ...))
        -- Now use retype lemma to convert from T.subst (Subst.openCVar cs) at env
        -- to T at env.extend_cvar (cs.subst ...)
        have hretype := @open_carg_val_denot s env cs T
        exact (hretype store (Exp.var (x.subst (Subst.from_TypeEnv env)))).mpr hQ
      case eval_val =>
        -- Variables can only use eval_var, not eval_val
        contradiction


theorem abs_val_denot_inv
  (hv : Ty.val_denot env (.arrow T1 cs T2) store (.var x)) :
  ∃ fx, x = .free fx
    ∧ ∃ cs' T0 e0 hval R,
      store.heap fx = some (Cell.val ⟨Exp.abs cs' T0 e0, hval, R⟩)
    ∧ expand_captures store.heap cs' ⊆ cs.denot env store
    ∧ (∀ (arg : Nat) (m' : Memory),
      m'.subsumes store ->
      Ty.val_denot env T1 m' (.var (.free arg)) ->
      Ty.exi_exp_denot
        (env.extend_var arg (compute_peakset env T1.captureSet))
        T2 (expand_captures store.heap cs' ∪ (reachability_of_loc m'.heap arg)) m'
        (e0.subst (Subst.openVar (.free arg)))) := by
  cases x with
  | bound bx => cases bx
  | free fx =>
    simp only [Ty.val_denot, resolve] at hv
    obtain ⟨hwf_e, hwf_cs, cs', T0, e0, hresolve, hwf_cs', hR0_sub, hfun⟩ := hv
    -- Analyze what's in the store at fx
    generalize hres : store.heap fx = res at hresolve ⊢
    cases res
    case none => simp at hresolve
    case some cell =>
      -- Match on the cell to extract HeapVal
      cases cell with
      | val hval =>
        -- hval : HeapVal, hresolve should relate to hval.unwrap
        simp at hresolve
        cases hval with | mk unwrap isVal reachability =>
        simp at hresolve
        subst hresolve
        use fx, rfl, cs', T0, e0, isVal, reachability, hres, hR0_sub, hfun
      | capability =>
        simp at hresolve
      | masked =>
        simp at hresolve


theorem tabs_val_denot_inv
  (hv : Ty.val_denot env (.poly T1 cs T2) store (.var x)) :
  ∃ fx, x = .free fx
    ∧ ∃ cs' S0 e0 hval R,
      store.heap fx = some (Cell.val ⟨Exp.tabs cs' S0 e0, hval, R⟩)
    ∧ expand_captures store.heap cs' ⊆ cs.denot env store
    ∧ (∀ (m' : Memory) (denot : Denot),
      m'.subsumes store ->
      denot.is_proper ->
      denot.implies_simple_ans ->
      denot.ImplyAfter m' (Ty.val_denot env T1) ->
      denot.enforce_pure ->
      Ty.exi_exp_denot
        (env.extend_tvar denot)
        T2 (expand_captures store.heap cs') m'
        (e0.subst (Subst.openTVar .top))) := by
  cases x with
  | bound bx => cases bx
  | free fx =>
    simp only [Ty.val_denot, resolve] at hv
    obtain ⟨hwf_e, hwf_cs, cs', S0, e0, hresolve, hwf_cs', hR0_sub, hfun⟩ := hv
    -- Analyze what's in the store at fx
    generalize hres : store.heap fx = res at hresolve ⊢
    cases res
    case none => simp at hresolve
    case some cell =>
      -- Match on the cell to extract HeapVal
      cases cell with
      | val hval =>
        -- hval : HeapVal, hresolve should relate to hval.unwrap
        simp at hresolve
        cases hval with | mk unwrap isVal reachability =>
        simp at hresolve
        subst hresolve
        use fx, rfl, cs', S0, e0, isVal, reachability, hres, hR0_sub, hfun
      | capability =>
        simp at hresolve
      | masked =>
        simp at hresolve

theorem cabs_val_denot_inv
  (hv : Ty.val_denot env (.cpoly B cs T) store (.var x)) :
  ∃ fx, x = .free fx
    ∧ ∃ cs' B0 e0 hval R,
      store.heap fx = some (Cell.val ⟨Exp.cabs cs' B0 e0, hval, R⟩)
    ∧ expand_captures store.heap cs' ⊆ cs.denot env store
    ∧ (∀ (m' : Memory) (CS : CaptureSet {}),
      CS.WfInHeap m'.heap ->
      m'.subsumes store ->
      ((CS.denot TypeEnv.empty m').BoundedBy (B.denot m')) ->
      Ty.exi_exp_denot
        (env.extend_cvar CS)
        T (expand_captures store.heap cs') m'
        (e0.subst (Subst.openCVar CS))) := by
  cases x with
  | bound bx => cases bx
  | free fx =>
    simp only [Ty.val_denot, resolve] at hv
    obtain ⟨hwf_e, hwf_cs, cs', B0, e0, hresolve, hwf_cs', hR0_sub, hfun⟩ := hv
    -- Analyze what's in the store at fx
    generalize hres : store.heap fx = res at hresolve ⊢
    cases res
    case none => simp at hresolve
    case some cell =>
      -- Match on the cell to extract HeapVal
      cases cell with
      | val hval =>
        -- hval : HeapVal, hresolve should relate to hval.unwrap
        simp at hresolve
        cases hval with | mk unwrap isVal reachability =>
        simp at hresolve
        subst hresolve
        use fx, rfl, cs', B0, e0, isVal, reachability, hres, hR0_sub, hfun
      | capability =>
        simp at hresolve
      | masked =>
        simp at hresolve


theorem cap_val_denot_inv
  (hv : Ty.val_denot env (.cap cs) store (.var x)) :
  ∃ fx, x = .free fx ∧ store.heap fx = some (.capability .basic) ∧
    (cs.denot env store).covers .epsilon fx := by
  cases x with
  | bound bx => cases bx
  | free fx =>
    simp only [Ty.val_denot, Memory.lookup] at hv
    obtain ⟨hwf_e, hwf_cs, label, heq, hlookup, hmem⟩ := hv
    have : fx = label := by
      injection heq with h1
      rename_i heq_var
      injection heq_var
    subst this
    use fx, rfl, hlookup, hmem

theorem unit_val_denot_inv
  (hv : Ty.val_denot env .unit store (.var x)) :
  ∃ fx, x = .free fx
    ∧ ∃ hval R,
      store.heap fx = some (Cell.val ⟨Exp.unit, hval, R⟩) := by
  cases x with
  | bound bx => cases bx
  | free fx =>
    simp only [Ty.val_denot, resolve] at hv
    generalize hres : store.heap fx = res at hv ⊢
    cases res
    case none => simp at hv
    case some cell =>
      cases cell with
      | val hval =>
        simp at hv
        cases hval with | mk unwrap isVal reachability =>
        simp at hv
        subst hv
        use fx, rfl, isVal, reachability, hres
      | capability =>
        simp at hv
      | masked =>
        simp at hv

theorem cell_val_denot_inv
  (hv : Ty.val_denot env (.cell cs) store (.var x)) :
  ∃ fx b0, x = .free fx ∧ store.heap fx = some (.capability (.mcell b0)) ∧
    (cs.denot env store).covers .epsilon fx := by
  cases x with
  | bound bx => cases bx
  | free fx =>
    simp only [Ty.val_denot, Memory.lookup] at hv
    obtain ⟨hwf_cs, label, b0, heq, hlookup, hmem⟩ := hv
    have : fx = label := by
      injection heq with h1
      rename_i heq_var
      injection heq_var
    subst this
    use fx, b0, rfl, hlookup, hmem

theorem reader_val_denot_inv
  (hv : Ty.val_denot env (.reader cs) store (.var x)) :
  ∃ fx y b0 hval R,
    x = .free fx ∧
    store.heap fx = some (Cell.val ⟨Exp.reader (.free y), hval, R⟩) ∧
    store.heap y = some (.capability (.mcell b0)) ∧
    (cs.denot env store).covers .ro y := by
  cases x with
  | bound bx => cases bx
  | free fx =>
    have hv' := hv
    simp only [Ty.val_denot] at hv'
    rcases hv' with ⟨_, _, y, b0, hres, hlookup, hcov⟩
    -- From hres, the heap at fx must store a reader value
    have hheap :
        ∃ v, store.heap fx = some (Cell.val v) ∧ v.unwrap = Exp.reader (.free y) := by
      unfold resolve at hres
      cases hmem : store.heap fx with
      | none => simp [hmem] at hres
      | some cell =>
        cases cell with
        | val v =>
          simp [hmem] at hres
          exact ⟨v, rfl, hres⟩
        | capability => simp [hmem] at hres
        | masked => simp [hmem] at hres
    obtain ⟨v, hlookup_fx, hvunwrap⟩ := hheap
    cases v with
    | mk unwrap isVal reachability =>
      cases hvunwrap
      refine ⟨fx, y, b0, isVal, reachability, rfl, ?_, ?_, hcov⟩
      · simp [hlookup_fx]
      · simpa [Memory.lookup] using hlookup

theorem bool_val_denot_inv
  (hv : Ty.val_denot env .bool store (.var x)) :
  ∃ fx, ∃ b : Bool, ∃ hval R,
    x = .free fx ∧
    store.heap fx = some (Cell.val ⟨(if b then Exp.btrue else Exp.bfalse), hval, R⟩) := by
  cases x with
  | bound bx => cases bx
  | free fx =>
    simp [Ty.val_denot, resolve] at hv
    generalize hres : store.heap fx = res at hv ⊢
    cases res
    case none => simp at hv
    case some cell =>
      cases cell with
      | val hval =>
        simp at hv
        cases hval with | mk unwrap isVal reachability =>
        simp at hv
        cases hv with
        | inl hl =>
          subst hl
          use fx, true, isVal, reachability, rfl, hres
        | inr hr =>
          subst hr
          use fx, false, isVal, reachability, rfl, hres
      | capability =>
        simp at hv
      | masked =>
        simp at hv

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

/-- For closed capture sets, the denotation is preserved under substitution with from_TypeEnv,
provided the environment satisfies the cvar invariant. -/
theorem closed_captureset_subst_denot
  {s : Sig} {env : TypeEnv s} {D : CaptureSet s}
  (hD_closed : D.IsClosed) :
  (D.subst (Subst.from_TypeEnv env)).denot TypeEnv.empty = D.denot env := by
  induction hD_closed with
  | empty =>
    rfl
  | union _ _ ih1 ih2 =>
    simp only [CaptureSet.subst, CaptureSet.denot] at ih1 ih2 ⊢
    funext m
    simp only [CaptureSet.ground_denot]
    rw [congrFun ih1 m, congrFun ih2 m]
  | cvar =>
    rename_i m cv
    cases m <;> simp [CaptureSet.denot, Subst.from_TypeEnv_empty, CaptureSet.subst_id]
  | var_bound =>
    rename_i m xb
    simp only [CaptureSet.subst, CaptureSet.denot, Var.subst, Subst.from_TypeEnv]


theorem sem_typ_app
  {T1 : Ty .capt s} {T2 : Ty .exi (s,x)}
  {x y : BVar s .var} -- x and y must be BOUND variables (from typing rule)
  (hx : (.var .epsilon (.bound x)) # Γ ⊨ Exp.var (.bound x) :
    .typ ((Ty.arrow T1 (.var .epsilon (.bound x)) T2)))
  (hy : (.var .epsilon (.bound y)) # Γ ⊨ Exp.var (.bound y) : .typ T1) :
  ((.var .epsilon (.bound x)) ∪ (.var .epsilon (.bound y))) # Γ ⊨
    Exp.app (.bound x) (.bound y) : T2.subst (Subst.openVar (.bound y)) := by
  intro env store hts

  -- Extract function denotation
  have h1 := hx env store hts
  simp [Exp.subst, Subst.from_TypeEnv, Var.subst] at h1
  have h1' := var_exp_denot_inv h1
  -- refineCaptureSet for arrow replaces the capture set:
  --   (Ty.arrow T1 cs T2).refineCaptureSet cs' = Ty.arrow T1 cs' T2
  -- So h1' : Ty.val_denot env (Ty.arrow T1 (.var .epsilon (.bound x)) T2) ...
  simp only [Ty.exi_val_denot] at h1'

  -- Extract the arrow structure
  have ⟨fx, hfx, cs', T0, e0, hval, R, hlk, hR0_sub, hfun⟩ := abs_val_denot_inv h1'

  -- Extract argument denotation
  have h2 := hy env store hts
  simp [Exp.subst, Subst.from_TypeEnv, Var.subst] at h2
  have h2' := var_exp_denot_inv h2
  simp only [Ty.exi_val_denot] at h2'

  -- Determine concrete locations
  have : fx = (env.lookup_var x).1 := by cases hfx; rfl
  subst this
  let fy := (env.lookup_var y).1

  -- Simplify goal
  simp [Exp.subst, Subst.from_TypeEnv, Var.subst, CaptureSet.denot, Ty.exi_exp_denot]

  -- Apply function to argument
  have happ := hfun fy store (Memory.subsumes_refl store) h2'

  -- The opening lemma relates extended environment to substituted type
  let ps := compute_peakset env T1.captureSet
  let R := expand_captures store.heap cs' ∪ reachability_of_loc store.heap fy
  have heqv := open_arg_exi_exp_denot (env:=env) (y:=.bound y) (ps:=ps) (T:=T2) (R:=R)

  -- Note that interp_var env (Var.bound y) = env.lookup_var y = fy
  have hinterp : interp_var env (Var.bound y) = fy := rfl

  -- Convert the denotation using the equivalence
  rw [hinterp] at heqv
  have happ' :=
    (heqv store (e0.subst (Subst.openVar (Var.free fy)))).1 happ

  simp [Ty.exi_exp_denot] at happ'

  -- Widen the authority using union monotonicity
  -- We have: hR0_sub : expand_captures store.heap cs' ⊆ (.var .epsilon (.bound x)).denot env store
  -- R = expand_captures store.heap cs' ∪ reachability_of_loc store.heap fy
  -- Goal: R ⊆ (.var .epsilon (.bound x)).denot env store ∪ reachability_of_loc store.heap fy
  have hunion_mono : R ⊆
                     CaptureSet.denot env (CaptureSet.var .epsilon (Var.bound x)) store ∪
                     reachability_of_loc store.heap fy := by
    apply CapabilitySet.Subset.union_left
    · exact CapabilitySet.Subset.trans hR0_sub CapabilitySet.Subset.union_right_left
    · exact CapabilitySet.Subset.union_right_right

  have happ'' := eval_capability_set_monotonic happ' hunion_mono

  apply Eval.eval_apply hlk happ''

theorem sem_typ_tapp
  {S : PureTy s} {T : Ty .exi (s,X)}
  {x : BVar s .var} -- x must be a BOUND variable (from typing rule)
  (hx : (.var .epsilon (.bound x)) # Γ ⊨ Exp.var (.bound x) :
    .typ (Ty.poly S.core (.var .epsilon (.bound x)) T)) :
  (.var .epsilon (.bound x)) # Γ ⊨ Exp.tapp (.bound x) S : T.subst (Subst.openTVar S) := by
  intro env store hts

  -- Extract function denotation
  have h1 := hx env store hts
  simp [Exp.subst, Subst.from_TypeEnv, Var.subst] at h1
  have h1' := var_exp_denot_inv h1
  simp only [Ty.exi_val_denot] at h1'

  -- Extract the poly structure
  have ⟨fx, hfx, cs, S0, e0, hval, R, hlk, hR0_sub, hfun⟩ := tabs_val_denot_inv h1'

  -- Determine concrete location
  have : fx = (env.lookup_var x).1 := by cases hfx; rfl
  subst this

  -- Simplify goal
  simp [Exp.subst, Subst.from_TypeEnv, Var.subst, CaptureSet.denot, Ty.exi_exp_denot]

  -- Apply the polymorphic function to the type argument S.core
  -- We need to provide: is_proper, implies_simple_ans, ImplyAfter, enforce_pure
  have himply_simple := val_denot_implies_simple_ans (typed_env_is_implying_simple_ans hts) S.core
  have happ := hfun store (Ty.val_denot env S.core) (Memory.subsumes_refl store)
    (val_denot_is_proper hts)  -- Type denotations are proper
    himply_simple  -- implies_simple_ans
    (by intro m' hsub; exact Denot.imply_implyat (Denot.imply_refl _))  -- ImplyAfter
    (pure_ty_enforce_pure (typed_env_enforces_pure hts) S.p)  -- enforce_pure

  -- The opening lemma relates extended environment to substituted type
  have heqv := open_targ_exi_exp_denot (env:=env) (S:=S) (T:=T) (R:=expand_captures store.heap cs)

  -- Convert the denotation using the equivalence
  have happ' := (heqv store (e0.subst (Subst.openTVar .top))).1 happ

  simp [Ty.exi_exp_denot] at happ'

  -- Widen the authority using monotonicity
  have happ'' := eval_capability_set_monotonic happ' hR0_sub

  apply Eval.eval_tapply hlk happ''

theorem typed_env_lookup_cvar_aux
  (hts : EnvTyping Γ env m)
  (hc : Ctx.LookupCVar Γ c cb) :
  ((env.lookup_cvar c).ground_denot m).BoundedBy (cb.denot m) := by
  -- Mutability.denot doesn't depend on environment, so rebinding is trivial
  induction hc generalizing m
  case here =>
    rename_i Γ' cb'
    match env with
    | .extend env' (.cvar cs) =>
      simp only [EnvTyping, TypeEnv.lookup_cvar] at hts ⊢
      exact hts.2.1
  case there b0 b hc_prev ih =>
    cases b0
    case var =>
      rename_i Γ' c' cb' Tb
      match env with
      | .extend env' (.var x ps) =>
        simp only [EnvTyping, TypeEnv.lookup_cvar] at hts ⊢
        obtain ⟨_, _, henv'⟩ := hts
        have hih := ih henv'
        exact hih
    case tvar =>
      rename_i Γ' c' cb' Sb
      match env with
      | .extend env' (.tvar d) =>
        simp only [EnvTyping, TypeEnv.lookup_cvar] at hts ⊢
        obtain ⟨_, _, _, _, _, henv'⟩ := hts
        have hih := ih henv'
        exact hih
    case cvar =>
      rename_i Γ' c' cb' Bb
      match env with
      | .extend env' (.cvar cs) =>
        simp only [EnvTyping, TypeEnv.lookup_cvar] at hts ⊢
        obtain ⟨_, _, henv'⟩ := hts
        have hih := ih henv'
        exact hih

theorem sem_typ_capp
  {x : BVar s .var}
  {T : Ty .exi (s,C)}
  {D : CaptureSet s}
  {m : Mutability}
  (hD_closed : D.IsClosed)
  (hD_kind : HasKind Γ D m)
  (hx : (.var .epsilon (.bound x)) # Γ ⊨ Exp.var (.bound x) :
    .typ (.cpoly m (.var .epsilon (.bound x)) T)) :
  (.var .epsilon (.bound x)) # Γ ⊨ Exp.capp (.bound x) D : T.subst (Subst.openCVar D) := by
  intro env store hts

  -- Extract function denotation
  have h1 := hx env store hts
  simp [Exp.subst, Subst.from_TypeEnv, Var.subst] at h1
  have h1' := var_exp_denot_inv h1
  simp only [Ty.exi_val_denot] at h1'

  -- Extract the cpoly structure
  have ⟨fx, hfx, cs, B0, e0, hval, R, hlk, hR0_sub, hfun⟩ := cabs_val_denot_inv h1'

  -- Determine concrete location
  have : fx = (env.lookup_var x).1 := by cases hfx; rfl
  subst this

  -- Simplify goal
  simp [Exp.subst, Subst.from_TypeEnv, Var.subst, Ty.exi_exp_denot]

  -- After substitution, D becomes a closed capture set
  let D' := D.subst (Subst.from_TypeEnv env)

  -- For closed capture sets, the denotation is preserved under substitution
  have hD'_denot : D'.denot TypeEnv.empty = D.denot env := by
    exact closed_captureset_subst_denot hD_closed

  -- D' is also closed
  have hD'_wf : D'.WfInHeap store.heap := by
    -- First show D is wf by closedness
    have hD_wf : D.WfInHeap store.heap := CaptureSet.wf_of_closed hD_closed
    -- Then show the substitution is wf
    have hσ_wf : (Subst.from_TypeEnv env).WfInHeap store.heap :=
      from_TypeEnv_wf_in_heap hts
    -- Apply wf_subst
    exact CaptureSet.wf_subst hD_wf hσ_wf

  -- Apply the polymorphic function to the capture argument D'
  have happ := hfun store D'
    hD'_wf              -- Closed capture sets are well-formed
    (Memory.subsumes_refl store)          -- Memory subsumes itself
    (by -- Prove that (D'.denot TypeEnv.empty store).BoundedBy (m.denot store)
      -- m.denot store = .top m
      -- So we need: (D'.denot TypeEnv.empty store).BoundedBy (.top m)
      -- Which requires (D'.denot TypeEnv.empty store).HasKind m
      rw [hD'_denot]
      simp [Mutability.denot]
      apply CapabilitySet.BoundedBy.top
      -- Need to show (D.denot env store).HasKind m
      -- Inline proof based on HasKind cases
      cases hD_kind with
      | eps => exact CapabilitySet.HasKind.eps
      | ro =>
        simp only [CaptureSet.denot, CaptureSet.applyRO_subst]
        rw [← ground_denot_applyRO_comm]
        exact CapabilitySet.HasKind.applyRO
      | cvar_ro hlookup =>
        simp only [CaptureSet.denot, CaptureSet.subst, Subst.from_TypeEnv]
        -- Need to show (env.lookup_cvar c).ground_denot store has kind .ro
        have hbound := typed_env_lookup_cvar_aux hts hlookup
        simp [Mutability.denot] at hbound
        cases hbound with
        | top hkind => exact hkind)

  -- Now apply the opening lemma
  have heqv := open_carg_exi_exp_denot (env:=env) (C:=D) (T:=T) (R:=expand_captures store.heap cs)

  -- Convert using the equivalence
  have happ2 :=
    (heqv store (e0.subst (Subst.openCVar D'))).1 happ

  simp [Ty.exi_exp_denot] at happ2

  -- Widen the authority using monotonicity
  have happ3 := eval_capability_set_monotonic happ2 hR0_sub

  apply Eval.eval_capply hlk happ3


theorem sem_typ_invoke
  {x y : BVar s .var} -- x and y must be BOUND variables (from typing rule)
  (hx : (.var .epsilon (.bound x)) # Γ ⊨ Exp.var (.bound x) :
    .typ (.cap (.var .epsilon (.bound x))))
  (hy : (.var .epsilon (.bound y)) # Γ ⊨ Exp.var (.bound y) :
    .typ .unit) :
  ((.var .epsilon (.bound x)) ∪ (.var .epsilon (.bound y))) # Γ ⊨
    Exp.app (.bound x) (.bound y) : .typ .unit := by
  intro env store hts

  -- Extract capability denotation from hx
  have h1 := hx env store hts
  simp [Exp.subst, Subst.from_TypeEnv, Var.subst] at h1
  have h1' := var_exp_denot_inv h1
  simp only [Ty.exi_val_denot] at h1'

  -- Extract the capability structure
  have ⟨fx, hfx, hlk_cap, hmem_cap⟩ := cap_val_denot_inv h1'

  -- Extract unit denotation from hy
  have h2 := hy env store hts
  simp [Exp.subst, Subst.from_TypeEnv, Var.subst] at h2
  have h2' := var_exp_denot_inv h2
  simp only [Ty.exi_val_denot] at h2'

  -- Extract the unit structure
  have ⟨fy, hfy, hval_unit, R, hlk_unit⟩ := unit_val_denot_inv h2'

  -- Determine concrete locations
  have : fx = (env.lookup_var x).1 := by cases hfx; rfl
  subst this
  have : fy = (env.lookup_var y).1 := by cases hfy; rfl
  subst this

  -- Simplify goal
  simp [Exp.subst, Subst.from_TypeEnv, Var.subst, Ty.exi_exp_denot, Ty.exi_val_denot,
        Ty.val_denot, CaptureSet.denot]

  -- Show env.lookup_var x is covered in the union of capability sets
  have hcov :
    (CaptureSet.denot env (.var .epsilon (.bound x) ∪ .var .epsilon (.bound y)) store).covers
      .epsilon (env.lookup_var x).1 := by
    apply CapabilitySet.covers.left
    exact hmem_cap

  -- Apply eval_invoke
  apply Eval.eval_invoke hcov hlk_cap hlk_unit

  -- Show the postcondition holds for unit: resolve returns .unit
  simp only [Denot.as_mpost, resolve]


theorem sem_typ_unit :
  {} # Γ ⊨ Exp.unit : .typ .unit := by
  intro env store hts
  simp [Ty.exi_exp_denot, Ty.exi_val_denot, Exp.subst, CaptureSet.denot]
  apply Eval.eval_val
  · exact Exp.IsVal.unit
  · simp only [Denot.as_mpost, Ty.val_denot, resolve]

theorem sem_typ_btrue :
  {} # Γ ⊨ Exp.btrue : .typ .bool := by
  intro env store hts
  simp [Ty.exi_exp_denot, Ty.exi_val_denot, Exp.subst, CaptureSet.denot]
  apply Eval.eval_val
  · exact Exp.IsVal.btrue
  · simp only [Denot.as_mpost, Ty.val_denot, resolve]
    left; trivial

theorem sem_typ_bfalse :
  {} # Γ ⊨ Exp.bfalse : .typ .bool := by
  intro env store hts
  simp [Ty.exi_exp_denot, Ty.exi_val_denot, Exp.subst, CaptureSet.denot]
  apply Eval.eval_val
  · exact Exp.IsVal.bfalse
  · simp only [Denot.as_mpost, Ty.val_denot, resolve]
    right; trivial



theorem sem_typ_cond
  {C1 C2 C3 : CaptureSet s} {Γ : Ctx s}
  {x : Var .var s} {e2 e3 : Exp s} {T : Ty .exi s}
  (hclosed_C1 : C1.IsClosed)
  (hclosed_C2 : C2.IsClosed)
  (hclosed_C3 : C3.IsClosed)
  (_hclosed_guard : x.IsClosed)
  (_hclosed_then : e2.IsClosed)
  (_hclosed_else : e3.IsClosed)
  (ht1 : C1 # Γ ⊨ (.var x) : .typ .bool)
  (ht2 : C2 # Γ ⊨ e2 : T)
  (ht3 : C3 # Γ ⊨ e3 : T) :
  (C1 ∪ C2 ∪ C3) # Γ ⊨ (.cond x e2 e3) : T := by
  intro env store hts
  simp [Exp.subst, Ty.exi_exp_denot]
  -- Let Q1 be the guard postcondition
  set Q1 := (Ty.exi_val_denot env (.typ .bool)).as_mpost
  -- Monotonicity of Q1
  have hpred : Q1.is_monotonic := Denot.as_mpost_is_monotonic
    (exi_val_denot_is_monotonic (typed_env_is_monotonic hts) (.typ .bool))
  -- Bool independence of Q1
  have hbool : Q1.is_bool_independent := Denot.as_mpost_is_bool_independent
    (exi_val_denot_is_bool_independent (typed_env_is_bool_independent hts) (.typ .bool))
  -- Evaluate the guard under base authority
  have hguard_base := ht1 env store hts
  simp [Ty.exi_exp_denot] at hguard_base
  -- Widen authority to C1 ∪ C2 ∪ C3
  have hsubC1 : CaptureSet.denot env C1 store ⊆ CaptureSet.denot env (C1 ∪ C2 ∪ C3) store := by
    -- Goal: C1 ⊆ (C1 ∪ C2) ∪ C3
    set A := CaptureSet.denot env C1 store
    set B := CaptureSet.denot env C2 store
    set C := CaptureSet.denot env C3 store
    have hA : A ⊆ A ∪ B := CapabilitySet.Subset.union_right_left
    have hAB : A ∪ B ⊆ (A ∪ B) ∪ C := CapabilitySet.Subset.union_right_left
    exact CapabilitySet.Subset.trans hA hAB
  have hguard := eval_capability_set_monotonic hguard_base hsubC1
  -- Assemble eval_cond
  refine Eval.eval_cond (Q1 := Q1) hpred hbool hguard ?h_nonstuck ?h_true ?h_false
  · -- non-stuck: guard evaluates to a literal boolean
    intro m1 v hQ1
    -- hQ1 : Q1 v m1 = Ty.val_denot env .bool m1 v
    -- Ty.val_denot .bool = resolve m.heap e = .btrue ∨ resolve m.heap e = .bfalse
    simp only [Q1, Denot.as_mpost, Ty.exi_val_denot, Ty.val_denot] at hQ1
    exact hQ1
  · -- true branch
    intro m1 v hsub hQtrue hres
    have hts' : EnvTyping Γ env m1 := env_typing_monotonic hts hsub
    have hthen := ht2 env m1 hts'
    simp [Ty.exi_exp_denot] at hthen
    have hsubC2 : CaptureSet.denot env C2 m1 ⊆ CaptureSet.denot env (C1 ∪ C2 ∪ C3) m1 := by
      set A := CaptureSet.denot env C1 m1
      set B := CaptureSet.denot env C2 m1
      set C := CaptureSet.denot env C3 m1
      have hB : B ⊆ A ∪ B := CapabilitySet.Subset.union_right_right
      have hAB : A ∪ B ⊆ (A ∪ B) ∪ C := CapabilitySet.Subset.union_right_left
      exact CapabilitySet.Subset.trans hB hAB
    -- widen authority, then lift over memory subsumption using post monotonicity
    have hthen' := eval_capability_set_monotonic hthen hsubC2
    -- Align capability sets computed at store versus m1 using monotonicity
    have hwf_union :
        ((C1 ∪ C2 ∪ C3).subst (Subst.from_TypeEnv env)).WfInHeap store.heap := by
      apply CaptureSet.wf_subst
      · apply CaptureSet.wf_of_closed
        exact CaptureSet.IsClosed.union (CaptureSet.IsClosed.union hclosed_C1 hclosed_C2) hclosed_C3
      · exact from_TypeEnv_wf_in_heap hts
    have hcap_eq :
        CaptureSet.denot env (C1 ∪ C2 ∪ C3) m1 =
        CaptureSet.denot env (C1 ∪ C2 ∪ C3) store :=
      (capture_set_denot_is_monotonic
        (C := C1 ∪ C2 ∪ C3) (ρ := env) (m1 := store) (m2 := m1)
        hwf_union hsub).symm
    have hthen_store :
        Eval (CaptureSet.denot env (C1 ∪ C2 ∪ C3) store) m1
          (e2.subst (Subst.from_TypeEnv env)) (Ty.exi_val_denot env T).as_mpost := by
      exact hcap_eq ▸ hthen'
    exact hthen_store
  · -- false branch
    intro m1 v hsub hQfalse hres
    have hts' : EnvTyping Γ env m1 := env_typing_monotonic hts hsub
    have helse := ht3 env m1 hts'
    simp [Ty.exi_exp_denot] at helse
    have hsubC3 : CaptureSet.denot env C3 m1 ⊆ CaptureSet.denot env (C1 ∪ C2 ∪ C3) m1 := by
      simp [CaptureSet.denot, CaptureSet.subst, CaptureSet.ground_denot]
      apply CapabilitySet.Subset.union_right_right
    have helse' := eval_capability_set_monotonic helse hsubC3
    have hwf_union :
        ((C1 ∪ C2 ∪ C3).subst (Subst.from_TypeEnv env)).WfInHeap store.heap := by
      apply CaptureSet.wf_subst
      · apply CaptureSet.wf_of_closed
        exact CaptureSet.IsClosed.union (CaptureSet.IsClosed.union hclosed_C1 hclosed_C2) hclosed_C3
      · exact from_TypeEnv_wf_in_heap hts
    have hcap_eq :
        CaptureSet.denot env (C1 ∪ C2 ∪ C3) m1 =
        CaptureSet.denot env (C1 ∪ C2 ∪ C3) store :=
      (capture_set_denot_is_monotonic
        (C := C1 ∪ C2 ∪ C3) (ρ := env) (m1 := store) (m2 := m1)
        hwf_union hsub).symm
    have helse_store :
        Eval (CaptureSet.denot env (C1 ∪ C2 ∪ C3) store) m1
          (e3.subst (Subst.from_TypeEnv env)) (Ty.exi_val_denot env T).as_mpost := by
      exact hcap_eq ▸ helse'
    exact helse_store

theorem sem_typ_reader
  (_hclosed : Γ.IsClosed)
  (hx : Γ.LookupVar x (.cell C)) :
  (.var .ro (.bound x)) # Γ ⊨ Exp.reader (.bound x) :
    (.typ (.reader (.var .ro (.bound x)))) := by
  intro env store hts
  simp [Ty.exi_exp_denot, Ty.exi_val_denot, Exp.subst, CaptureSet.denot]
  apply Eval.eval_val
  · exact Exp.IsVal.reader
  · simp only [Denot.as_mpost, Ty.val_denot]
    -- Get the cell denotation from the lookup
    have hcell := typed_env_lookup_var hts hx
    -- hcell : Ty.val_denot env (.cell C) store (.var (.free (env.lookup_var x).1))
    have ⟨_, b0, rfl, hlookup_cell, _⟩ := cell_val_denot_inv hcell
    -- Ty.val_denot .reader cs = e.WfInHeap ∧ cs'.WfInHeap ∧ ∃ label b0, ...
    refine ⟨?hwf_e, ?hwf_cs, (env.lookup_var x).1, b0, ?hres, ?hlookup, ?hcover⟩
    · -- e.WfInHeap
      exact Exp.WfInHeap.wf_reader (Var.WfInHeap.wf_free hlookup_cell)
    · -- cs.subst.WfInHeap
      exact CaptureSet.WfInHeap.wf_var_free hlookup_cell
    · -- resolve = some (.reader (.free label))
      simp [resolve, Var.subst, Subst.from_TypeEnv]
    · -- lookup = .capability (.mcell b0)
      simpa [Memory.lookup] using hlookup_cell
    · -- covers .ro label
      have hden :
        CaptureSet.denot env (CaptureSet.var .ro (Var.bound x)) store
          = CapabilitySet.singleton .ro (env.lookup_var x).1 := by
        simp [CaptureSet.denot, CaptureSet.subst, Subst.from_TypeEnv, Var.subst,
              CaptureSet.ground_denot, CapabilitySet.applyMut, CapabilitySet.applyRO,
              CapabilitySet.singleton, reachability_of_loc, hlookup_cell]
      have hcov_singleton :
          CapabilitySet.covers .ro (env.lookup_var x).1
            (CapabilitySet.singleton .ro (env.lookup_var x).1) :=
        CapabilitySet.covers.here (l:=(env.lookup_var x).1) Mutability.Le.refl
      simpa [hden] using hcov_singleton

theorem sem_typ_read
  {x : BVar s .var}
  (hx : (.var .epsilon (.bound x)) # Γ ⊨ Exp.var (.bound x) : .typ (.reader C)) :
  (.var .epsilon (.bound x)) # Γ ⊨ Exp.read (.bound x) : .typ .bool := by
  intro env store hts

  -- Extract reader denotation from hx
  have h1 := hx env store hts
  simp [Exp.subst, Subst.from_TypeEnv, Var.subst] at h1
  have h1' := var_exp_denot_inv h1
  simp only [Ty.exi_val_denot] at h1'

  -- Extract the reader structure
  have ⟨fx, y, b0, hval_reader, R, hfx, hlookup_reader, hlookup_cell, hcov_reader⟩ :=
    reader_val_denot_inv h1'

  -- Determine concrete location
  have : fx = (env.lookup_var x).1 := by cases hfx; rfl
  subst this

  -- Simplify goal
  simp [Exp.subst, Subst.from_TypeEnv, Var.subst, Ty.exi_exp_denot, Ty.exi_val_denot,
        CaptureSet.denot]

  -- The reachability stored with the reader gives the needed .ro capability
  have hreach :
    reachability_of_loc store.heap (env.lookup_var x).1 = CapabilitySet.singleton .ro y := by
    have heq := reachability_of_loc_eq_resolve_reachability store (env.lookup_var x).1
      ⟨Exp.reader (.free y), hval_reader, R⟩ hlookup_reader
    simpa [resolve_reachability] using heq

  have hcov :
      CapabilitySet.covers .ro y
        (((CaptureSet.var .epsilon (Var.bound x)).subst (Subst.from_TypeEnv env)).ground_denot
          store) := by
    have hden :
        (((CaptureSet.var .epsilon (Var.bound x)).subst (Subst.from_TypeEnv env)).ground_denot
          store) = CapabilitySet.singleton .ro y := by
      simp [CaptureSet.subst, Var.subst, Subst.from_TypeEnv, CaptureSet.ground_denot,
            CapabilitySet.applyMut, hreach]
    simpa [hden] using (CapabilitySet.covers.here (l:=y) Mutability.Le.refl)

  have hlookup_reader' :
      store.lookup (env.lookup_var x).1 =
        some (Cell.val ⟨Exp.reader (.free y), hval_reader, R⟩) := by
    simpa [Memory.lookup] using hlookup_reader

  have hlookup_cell' : store.lookup y = some (.capability (.mcell b0)) := by
    simpa [Memory.lookup] using hlookup_cell

  apply Eval.eval_read hcov hlookup_reader' hlookup_cell'

  -- Show the postcondition holds for the boolean result
  simp only [Denot.as_mpost, Ty.val_denot, resolve]
  cases b0 <;> simp

theorem sem_typ_write
  {x y : BVar s .var}
  (hx : (.var .epsilon (.bound x)) # Γ ⊨ Exp.var (.bound x) : .typ (.cell Cx))
  (hy : (.var .epsilon (.bound y)) # Γ ⊨ Exp.var (.bound y) : .typ .bool) :
  ((.var .epsilon (.bound x)) ∪ (.var .epsilon (.bound y))) # Γ ⊨
    Exp.write (.bound x) (.bound y) : .typ .unit := by
  intro env store hts

  -- Extract cell denotation from hx
  have h1 := hx env store hts
  simp [Exp.subst, Subst.from_TypeEnv, Var.subst] at h1
  have h1' := var_exp_denot_inv h1
  simp only [Ty.exi_val_denot] at h1'

  -- Extract the cell structure
  have ⟨fx, b0, hfx, hlk_cell, hmem_cell⟩ := cell_val_denot_inv h1'

  -- Extract bool denotation from hy
  have h2 := hy env store hts
  simp [Exp.subst, Subst.from_TypeEnv, Var.subst] at h2
  have h2' := var_exp_denot_inv h2
  simp only [Ty.exi_val_denot] at h2'

  -- Extract the bool structure
  have ⟨fy, b, hval, R, hfy, hlk_bool⟩ := bool_val_denot_inv h2'

  -- Determine concrete locations
  have : fx = (env.lookup_var x).1 := by cases hfx; rfl
  subst this
  have : fy = (env.lookup_var y).1 := by cases hfy; rfl
  subst this

  -- Simplify goal
  simp [Exp.subst, Subst.from_TypeEnv, Var.subst, Ty.exi_exp_denot, Ty.exi_val_denot,
        CaptureSet.denot]

  -- Prove covers: env.lookup_var x is covered by the denotation of the write's capture set
  have hcov :
    ((((CaptureSet.var .epsilon (Var.bound x)).union (CaptureSet.var .epsilon (Var.bound y))).subst
      (Subst.from_TypeEnv env)).ground_denot store).covers .epsilon (env.lookup_var x).1 := by
    simp only [CaptureSet.subst, Var.subst, Subst.from_TypeEnv, CaptureSet.ground_denot,
          CapabilitySet.applyMut, reachability_of_loc, hlk_cell, CapabilitySet.singleton]
    apply CapabilitySet.covers.left
    exact CapabilitySet.covers.here Mutability.Le.refl

  -- Apply eval_write based on the boolean value
  cases b
  · -- b = false
    apply Eval.eval_write_false hcov (hx := hlk_cell) hlk_bool
    simp only [Denot.as_mpost, Ty.val_denot, resolve]
  · -- b = true
    apply Eval.eval_write_true hcov (hx := hlk_cell) hlk_bool
    simp only [Denot.as_mpost, Ty.val_denot, resolve]

theorem sem_typ_par
  {C1 C2 : CaptureSet s} {Γ : Ctx s}
  {e1 e2 : Exp s} {E : Ty .exi s}
  (ht1 : C1 # Γ ⊨ e1 : E)
  (ht2 : C2 # Γ ⊨ e2 : E) :
  (C1 ∪ C2) # Γ ⊨ (.par e1 e2) : E := by
  intro env store hts
  simp [Exp.subst, Ty.exi_exp_denot]
  -- Evaluate both branches and combine with eval_par
  have he1 := ht1 env store hts
  have he2 := ht2 env store hts
  simp [Ty.exi_exp_denot] at he1 he2
  have hni : CapabilitySet.Noninterference (CaptureSet.denot env C1 store)
                                           (CaptureSet.denot env C2 store) := by
    sorry
  exact Eval.eval_par he1 he2 hni CapabilitySet.Subset.refl


theorem sem_typ_letin
  {C : CaptureSet s} {Γ : Ctx s} {e1 : Exp s} {T : Ty .capt s}
  {e2 : Exp (s,,Kind.var)} {U : Ty .exi s}
  (hclosed_C : C.IsClosed)
  (_hclosed_e : (Exp.letin e1 e2).IsClosed)
  (ht1 : C # Γ ⊨ e1 : .typ T)
  (ht2 : C.rename Rename.succ # (Γ,x:T) ⊨ e2 : U.rename Rename.succ) :
  C # Γ ⊨ (Exp.letin e1 e2) : U := by
  intro env store hts
  simp [Exp.subst]
  simp [Ty.exi_exp_denot]
  -- Use Eval.eval_letin with Q1 = (Ty.val_denot env T).as_mpost
  apply Eval.eval_letin (Q1 := (Ty.val_denot env T).as_mpost)
  case hpred =>
    -- Show (Ty.val_denot env T).as_mpost is monotonic
    intro m1 m2 e hwf hsub hQ
    simp [Denot.as_mpost] at hQ ⊢
    have henv_mono := typed_env_is_monotonic hts
    exact val_denot_is_monotonic henv_mono T hsub hQ
  case hbool =>
    -- Show (Ty.val_denot env T).as_mpost is bool independent
    apply Denot.as_mpost_is_bool_independent
    exact val_denot_is_bool_independent (typed_env_is_bool_independent hts) T
  case a =>
    -- Show Eval ... store (e1.subst ...) (Ty.val_denot env T).as_mpost
    have h1 := ht1 env store hts
    simp [Ty.exi_exp_denot, Ty.exi_val_denot] at h1
    exact h1
  case h_nonstuck =>
    intro m1 v hQ1
    simp [Denot.as_mpost] at hQ1
    -- hQ1 : Ty.val_denot env T m1 v
    constructor
    · -- Prove v.IsSimpleAns
      exact val_denot_implies_simple_ans (typed_env_is_implying_simple_ans hts) T m1 v hQ1
    · -- Prove v.WfInHeap m1.heap
      exact val_denot_implies_wf (typed_env_is_implying_wf hts) T m1 v hQ1
  case h_val =>
    -- Handle the value case: e1 evaluated to a simple value v
    intro m1 v hs1 hv hwf_v hQ1 l' hfresh
    -- m1.subsumes store, v is a simple value, Q1 v m1 holds
    simp [Denot.as_mpost] at hQ1
    -- Construct the HeapVal for v
    let heapval : HeapVal := ⟨v, hv, compute_reachability m1.heap v hv⟩
    -- Apply ht2 with extended environment and memory
    let ps := CaptureSet.peakset Γ T.captureSet
    have ht2' := ht2 (env.extend_var l' ps)
      (m1.extend_val l' heapval hwf_v rfl hfresh)
    simp [Ty.exi_exp_denot] at ht2' ⊢
    -- Rewrite to make expressions match
    rw [<-Exp.from_TypeEnv_weaken_open] at ht2'
    -- Show that capability sets match
    have hcap_rename :
      (C.rename Rename.succ).denot (env.extend_var l' ps)
      = C.denot env := by
      have := rebind_captureset_denot (Rebind.weaken (env:=env) (x:=l') (ps:=ps)) C
      exact this.symm
    have hC_mono : C.denot env store = C.denot env (m1.extend_val l' heapval hwf_v rfl hfresh) := by
      have hwf_C : (C.subst (Subst.from_TypeEnv env)).WfInHeap store.heap := by
        apply CaptureSet.wf_subst
        · apply CaptureSet.wf_of_closed hclosed_C
        · apply from_TypeEnv_wf_in_heap hts
      have hext_subsumes_store : (m1.extend_val l' heapval hwf_v rfl hfresh).subsumes store :=
        Memory.subsumes_trans (Memory.extend_val_subsumes m1 l' heapval hwf_v rfl hfresh) hs1
      exact capture_set_denot_is_monotonic hwf_C hext_subsumes_store
    -- Convert postcondition using weaken_exi_val_denot
    rw [hC_mono, ← hcap_rename]
    apply eval_post_monotonic _ (ht2' _)
    · -- Show postcondition entailment
      apply Denot.imply_to_entails
      have heqv := weaken_exi_val_denot (env:=env) (x:=l') (ps:=ps) (T:=U)
      apply (Denot.equiv_to_imply heqv).2
    · -- Show: EnvTyping (Γ,x:T) (env.extend_var l')
      --       (m1.extend_val l' heapval hwf_v hfresh)
      constructor
      · -- Show: Ty.capt_val_denot env T
        --       (m1.extend_val l' heapval hwf_v hfresh) (Exp.var (Var.free l'))
        -- Strategy: Use monotonicity + transparency

        -- Step 1: Prove memory subsumption
        have hext : (m1.extend_val l' heapval hwf_v rfl hfresh).subsumes m1 :=
          Memory.extend_val_subsumes m1 l' heapval hwf_v rfl hfresh

        -- Step 2: Lift hQ1 to extended memory using monotonicity
        have henv_mono := typed_env_is_monotonic hts
        have hQ1_lifted : Ty.val_denot env T
          (m1.extend_val l' heapval hwf_v rfl hfresh) v :=
          val_denot_is_monotonic henv_mono T hext hQ1

        -- Step 3: Apply transparency
        have henv_trans := typed_env_is_transparent hts
        have htrans : (Ty.val_denot env T).is_transparent :=
          val_denot_is_transparent henv_trans T

        -- Step 4: Use the memory lookup fact
        have hlookup : (m1.extend_val l' heapval hwf_v rfl hfresh).lookup l' =
          some (Cell.val heapval) := by
          simp [Memory.extend_val]
          exact Heap.extend_lookup_eq m1.heap l' heapval

        -- Step 5: Apply transparency
        apply htrans hlookup hQ1_lifted
      · -- Show: EnvTyping Γ env (m1.extend_val l' heapval hwf_v rfl hfresh)
        -- Original typing preserved under memory extension
        have hext : (m1.extend_val l' heapval hwf_v rfl hfresh).subsumes m1 :=
          Memory.extend_val_subsumes m1 l' heapval hwf_v rfl hfresh
        -- Combine subsumptions: extended memory subsumes m1, m1 subsumes store
        have hsubsume : (m1.extend_val l' heapval hwf_v rfl hfresh).subsumes store :=
          Memory.subsumes_trans hext hs1
        constructor
        · rfl
        · exact env_typing_monotonic hts hsubsume
  case h_var =>
    -- Handle the variable case: e1 evaluated to a variable x
    intro m1 x hs1 hwf_x hQ1
    simp [Denot.as_mpost] at hQ1
    -- Extract the free variable number from x
    cases x
    case bound bv =>
      -- Bound variables in empty signature are impossible
      cases bv
    case free fx =>
      -- Apply ht2 with extended environment (no memory extension needed)
      let ps := CaptureSet.peakset Γ T.captureSet
      have ht2' := ht2 (env.extend_var fx ps) m1
      simp [Ty.exi_exp_denot] at ht2' ⊢
      -- Rewrite to make expressions match
      rw [<-Exp.from_TypeEnv_weaken_open] at ht2'
      -- Show that capability sets match
      have hcap_rename :
        (C.rename Rename.succ).denot (env.extend_var fx ps)
        = C.denot env := by
        have := rebind_captureset_denot (Rebind.weaken (env:=env) (x:=fx) (ps:=ps)) C
        exact this.symm
      have hC_mono : C.denot env store = C.denot env m1 := by
        have hwf_C : (C.subst (Subst.from_TypeEnv env)).WfInHeap store.heap := by
          apply CaptureSet.wf_subst
          · apply CaptureSet.wf_of_closed hclosed_C
          · apply from_TypeEnv_wf_in_heap hts
        exact capture_set_denot_is_monotonic hwf_C hs1
      -- Convert postcondition using weaken_exi_val_denot
      rw [hC_mono, ← hcap_rename]
      apply eval_post_monotonic _ (ht2' _)
      · -- Show postcondition entailment
        apply Denot.imply_to_entails
        have heqv := weaken_exi_val_denot (env:=env) (x:=fx) (ps:=ps) (T:=U)
        apply (Denot.equiv_to_imply heqv).2
      · -- Show: EnvTyping (Γ,x:T) (env.extend_var fx) m1
        constructor
        · -- Show: Ty.capt_val_denot env T m1 (Exp.var (Var.free fx))
          exact hQ1
        · constructor
          · rfl
          · -- Show: EnvTyping Γ env m1
            exact env_typing_monotonic hts hs1

theorem sem_sc_trans
  (hsub1 : SemSubcapt Γ C1 C2)
  (hsub2 : SemSubcapt Γ C2 C3) :
  SemSubcapt Γ C1 C3 := by
  intro env store hts
  specialize hsub1 env store hts
  specialize hsub2 env store hts
  apply CapabilitySet.Subset.trans hsub1 hsub2

theorem sem_sc_elem {C1 C2 : CaptureSet s}
  (hmem : C1 ⊆ C2) :
  SemSubcapt Γ C1 C2 := by
  intro env m hts
  unfold CaptureSet.denot
  induction hmem
  case refl =>
    exact CapabilitySet.Subset.refl
  case union_left ih1 ih2 =>
    -- (C1 ∪ C2).subst σ = (C1.subst σ) ∪ (C2.subst σ)
    simp [CaptureSet.subst]
    -- ((C1.subst σ) ∪ (C2.subst σ)).ground_denot
    --   = (C1.subst σ).ground_denot ∪ (C2.subst σ).ground_denot
    simp [CaptureSet.ground_denot]
    apply CapabilitySet.Subset.union_left
    · exact ih1
    · exact ih2
  case union_right_left ih =>
    simp [CaptureSet.subst, CaptureSet.ground_denot]
    exact CapabilitySet.Subset.trans ih CapabilitySet.Subset.union_right_left
  case union_right_right ih =>
    simp [CaptureSet.subst, CaptureSet.ground_denot]
    exact CapabilitySet.Subset.trans ih CapabilitySet.Subset.union_right_right

theorem sem_sc_union {C1 C2 C3 : CaptureSet s}
  (hsub1 : SemSubcapt Γ C1 C3)
  (hsub2 : SemSubcapt Γ C2 C3) :
  SemSubcapt Γ (C1.union C2) C3 := by
  intro env m hts
  unfold CaptureSet.denot
  simp [CaptureSet.subst, CaptureSet.ground_denot]
  apply CapabilitySet.Subset.union_left
  · exact hsub1 env m hts
  · exact hsub2 env m hts

theorem sem_sc_var {x : BVar s .var} {T : Ty .capt s}
  (hlookup : Γ.LookupVar x T) :
  SemSubcapt Γ (.var .epsilon (.bound x)) T.captureSet := by
  intro env m hts
  unfold CaptureSet.denot
  simp [CaptureSet.subst, Subst.from_TypeEnv]
  have h := typed_env_lookup_var_reachability hts hlookup
  simp [Ty.captureSet] at h
  exact h

/-- applyRO on CaptureSet gives a subset in denotation. -/
theorem sem_sc_ro {C : CaptureSet s} :
  SemSubcapt Γ C.applyRO C := by
  intro env m _hts
  unfold CaptureSet.denot
  simp only [CaptureSet.applyRO_subst]
  -- Need: (C.subst σ).applyRO.ground_denot m ⊆ (C.subst σ).ground_denot m
  exact ground_denot_applyRO_subset

/-- applyRO is monotonic for subcapturing. -/
theorem sem_sc_ro_mono {C1 C2 : CaptureSet s}
  (hsub : SemSubcapt Γ C1 C2) :
  SemSubcapt Γ C1.applyRO C2.applyRO := by
  intro env m hts
  unfold CaptureSet.denot
  simp only [CaptureSet.applyRO_subst]
  -- Need: (C1.subst σ).applyRO.ground_denot m ⊆ (C2.subst σ).applyRO.ground_denot m
  exact ground_denot_applyRO_mono (hsub env m hts)

theorem fundamental_subcapt
  (hsub : Subcapt Γ C1 C2) :
  SemSubcapt Γ C1 C2 := by
  induction hsub
  case sc_trans => grind [sem_sc_trans]
  case sc_elem hsub => exact sem_sc_elem hsub
  case sc_union ih1 ih2 => exact sem_sc_union ih1 ih2
  case sc_var hlookup => exact sem_sc_var hlookup
  case sc_ro => exact sem_sc_ro
  case sc_ro_mono ih => exact sem_sc_ro_mono ih

theorem fundamental_haskind
  (hkind : HasKind Γ C m) :
  SemHasKind Γ C m := by
  induction hkind with
  | eps =>
    intro env mem htyping
    exact CapabilitySet.HasKind.eps
  | ro =>
    intro env mem htyping
    simp only [CaptureSet.denot, CaptureSet.applyRO_subst]
    rw [← ground_denot_applyRO_comm]
    exact CapabilitySet.HasKind.applyRO
  | cvar_ro hlookup =>
    intro env mem htyping
    simp only [CaptureSet.denot, CaptureSet.subst, Subst.from_TypeEnv]
    -- Need to show that the denotation of the capture variable has kind .ro
    -- Since c is bounded by .ro, its denotation is bounded by .top .ro
    have hbound := typed_env_lookup_cvar_aux htyping hlookup
    simp [Mutability.denot] at hbound
    -- hbound : BoundedBy ... (.top .ro), which requires HasKind .ro
    cases hbound with
    | top hkind => exact hkind


lemma sem_subtyp_top {T : Ty .capt s}
  (hpure : T.IsPureType) :
  SemSubtyp Γ T .top := by
  -- Unfold SemSubtyp for capturing types
  simp [SemSubtyp]
  -- Introduce the environment, memory, and typing assumption
  intro env H htyping
  -- Unfold ImplyAfter to handle memory subsumption
  simp [Denot.ImplyAfter]
  intro m' hsubsumes
  -- Unfold ImplyAt to get the implication at a specific memory
  simp [Denot.ImplyAt]
  intro e hdenot_T
  -- Need to prove: Ty.val_denot env .top m' e
  -- Which unfolds to: e.IsSimpleAns ∧ e.WfInHeap m'.heap ∧ resolve_reachability m'.heap e ⊆ .empty
  simp [Ty.val_denot]
  constructor
  · -- Prove IsSimpleAns
    have himply_simple := val_denot_implies_simple_ans (typed_env_is_implying_simple_ans htyping) T
    exact himply_simple m' e hdenot_T
  constructor
  · -- Prove well-formedness: e.WfInHeap m'.heap
    have hwf_env := typed_env_is_implying_wf htyping
    have hwf_denot := val_denot_implies_wf hwf_env T
    exact hwf_denot m' e hdenot_T
  · -- Prove reachability bound: resolve_reachability m'.heap e ⊆ .empty
    -- First get the typing for m' (need monotonicity)
    have htyping' := env_typing_monotonic htyping hsubsumes
    -- Use val_denot_enforces_captures to bound reachability by T.captureSet
    have hbound := val_denot_enforces_captures htyping' e hdenot_T
    -- Since T is pure, T.captureSet is empty, so its denotation is empty
    unfold Ty.IsPureType at hpure
    have hempty := hpure.denot_empty (env := env) (m := m')
    exact hempty.subset_of_subset hbound

/-

-- Helper lemma for extracting type variable bounds from EnvTyping
lemma env_typing_lookup_tvar {X : BVar s .tvar} {S : Ty .shape s} {env : TypeEnv s} {m : Memory}
  (hlookup : Ctx.LookupTVar Γ X S)
  (htyping : EnvTyping Γ env m) :
  (env.lookup_tvar X).ImplyAfter m (Ty.shape_val_denot env S) := by
  induction hlookup generalizing m
  case here Γ S =>
    match env with
    | .extend env0 (.tvar d) =>
      simp only [EnvTyping, TypeEnv.lookup_tvar] at htyping ⊢
      obtain ⟨hproper, himply, htyping'⟩ := htyping
      -- Need: d.ImplyAfter m (shape_val_denot (env0.extend_tvar d) (S.rename Rename.succ))
      -- Have: d.ImplyAfter m (Ty.shape_val_denot env0 S)
      -- Use weakening theorem to relate the denotations
      have hw : Ty.shape_val_denot env0 S ≈
                Ty.shape_val_denot (env0.extend_tvar d) (S.rename Rename.succ) :=
        tweaken_shape_val_denot (d := d)
      simp [TypeEnv.extend_tvar] at hw
      -- Convert equivalence to implication and compose
      simp [PreDenot.ImplyAfter]
      intro C
      simp [PreDenot.ImplyAfter] at himply
      specialize himply C
      simp [PreDenot.equiv_def] at hw
      specialize hw C
      have himply_right := (Denot.equiv_to_imply hw).1
      intro m' hsub e hd
      apply himply_right m' e
      apply himply m' hsub e hd
  case there Γ X S b a a_ih =>
    -- Need to case split on what kind of binding b is
    cases b with
    | var T =>
      -- Context extended with a term variable
      match env with
      | .extend env0 (.var v ps0) =>
        simp only [EnvTyping, TypeEnv.lookup_tvar] at htyping ⊢
        obtain ⟨hval_denot, _, htyping'⟩ := htyping
        -- Apply IH to get the result for the smaller environment
        have ih_result := a_ih htyping'
        -- Use weakening lemma for var extension
        have hw : Ty.shape_val_denot env0 S ≈
                  Ty.shape_val_denot (env0.extend_var v ps0) (S.rename Rename.succ) :=
          weaken_shape_val_denot (x := v) (ps := ps0)
        simp [TypeEnv.extend_var] at hw
        -- Convert equivalence to implication and compose
        simp [PreDenot.ImplyAfter]
        intro C
        simp [PreDenot.ImplyAfter] at ih_result
        specialize ih_result C
        simp [PreDenot.equiv_def] at hw
        specialize hw C
        have himply_right := (Denot.equiv_to_imply hw).1
        intro m' hsub e hd
        apply himply_right m' e
        apply ih_result m' hsub e hd

    | tvar T =>
      -- Context extended with a type variable
      match env with
      | .extend env0 (.tvar d) =>
        simp only [EnvTyping, TypeEnv.lookup_tvar] at htyping ⊢
        obtain ⟨hproper, himply_bound, htyping'⟩ := htyping
        -- Apply IH
        have ih_result := a_ih htyping'
        -- Use tweaken for tvar extension
        have hw : Ty.shape_val_denot env0 S ≈
                  Ty.shape_val_denot (env0.extend_tvar d) (S.rename Rename.succ) :=
          tweaken_shape_val_denot (d := d)
        simp [TypeEnv.extend_tvar] at hw
        -- Convert and compose
        simp [PreDenot.ImplyAfter]
        intro C
        simp [PreDenot.ImplyAfter] at ih_result
        specialize ih_result C
        simp [PreDenot.equiv_def] at hw
        specialize hw C
        have himply_right := (Denot.equiv_to_imply hw).1
        intro m' hsub e hd
        apply himply_right m' e
        apply ih_result m' hsub e hd

    | cvar cb =>
      -- Context extended with a capture variable
      match env with
      | .extend env0 (.cvar cs) =>
        simp only [EnvTyping, TypeEnv.lookup_tvar] at htyping ⊢
        obtain ⟨hwf_cb, hbound, htyping'⟩ := htyping
        -- Apply IH
        have ih_result := a_ih htyping'
        -- Use cweaken for cvar extension
        have hw : Ty.shape_val_denot env0 S ≈
                  Ty.shape_val_denot (env0.extend_cvar cs) (S.rename Rename.succ) :=
          cweaken_shape_val_denot (cs := cs)
        simp [TypeEnv.extend_cvar] at hw
        -- Convert and compose
        simp [PreDenot.ImplyAfter]
        intro C
        simp [PreDenot.ImplyAfter] at ih_result
        specialize ih_result C
        simp [PreDenot.equiv_def] at hw
        specialize hw C
        have himply_right := (Denot.equiv_to_imply hw).1
        intro m' hsub e hd
        apply himply_right m' e
        apply ih_result m' hsub e hd

lemma sem_subtyp_tvar {X : BVar s .tvar} {S : Ty .shape s}
  (hlookup : Ctx.LookupTVar Γ X S) :
  SemSubtyp Γ (.tvar X) S := by
  -- Unfold SemSubtyp for shape types
  simp [SemSubtyp]
  intro env H htyping
  -- Extract the type variable bound using the helper lemma
  have himply := env_typing_lookup_tvar hlookup htyping
  -- Unfold the denotations
  simp [Ty.shape_val_denot]
  -- The result follows directly from himply
  exact himply

-- Helper lemma: PreDenot.ImplyAfter is monotonic in the starting memory
lemma pre_denot_imply_after_monotonic {pd1 pd2 : PreDenot} {H m : Memory}
  (himply : pd1.ImplyAfter H pd2)
  (hsub : m.subsumes H) :
  pd1.ImplyAfter m pd2 := by
  simp [PreDenot.ImplyAfter] at himply ⊢
  intro C
  simp [Denot.ImplyAfter] at himply ⊢
  intro m' hsub_m'
  -- m' subsumes m, and m subsumes H, so m' subsumes H by transitivity
  have hsub_H : m'.subsumes H := Memory.subsumes_trans hsub_m' hsub
  exact himply C m' hsub_H

lemma sem_subtyp_arrow {T1 T2 : Ty .capt s} {U1 U2 : Ty .exi (s,x)}
  (harg : SemSubtyp Γ T2 T1)
  (hres : SemSubtyp (Γ,x:T2) U1 U2) :
  SemSubtyp Γ (.arrow T1 U1) (.arrow T2 U2) := by
  -- Unfold SemSubtyp for shape types
  simp [SemSubtyp]
  intro env H htyping
  -- Need to prove PreDenot.ImplyAfter for arrow types
  simp [PreDenot.ImplyAfter]
  intro A
  -- Need to prove Denot.ImplyAfter for arrow types at capability set A
  simp [Denot.ImplyAfter]
  intro m' hsubsumes e h_arrow_T1_U1
  -- Unfold the denotation of arrow types
  simp [Ty.shape_val_denot] at h_arrow_T1_U1 ⊢
  -- Extract the components from the T1 -> U1 denotation
  obtain ⟨hwf, cs, T0, t0, hresolve, hcs_wf, hR0_subset, hbody⟩ := h_arrow_T1_U1
  -- Construct the proof for T2 -> U2
  constructor
  · exact hwf  -- Well-formedness is preserved
  · use cs, T0, t0
    constructor
    · exact hresolve  -- Same resolution
    · constructor
      · exact hcs_wf  -- Capture set well-formedness preserved
      · constructor
        · exact hR0_subset  -- Same capture subset constraint
        · -- Need to prove the body property with contravariant arg and covariant result
          intro arg m'' hsub harg_T2
          -- Use the computed peak sets
          let psT1 := compute_peakset env T1.captureSet
          let psT2 := compute_peakset env T2.captureSet
          -- Apply contravariance: if arg satisfies T2, it also satisfies T1
          have harg_T1 : Ty.capt_val_denot env T1 m'' (.var (.free arg)) := by
            have harg_sem := harg env H htyping
            have hsub_H_m'' := Memory.subsumes_trans hsub hsubsumes
            exact harg_sem m'' hsub_H_m'' (.var (.free arg)) harg_T2
          -- Define the authority sets
          let R0 := expand_captures m'.heap cs
          let R := R0 ∪ (reachability_of_loc m''.heap arg)
          -- Apply hbody at the T1 peak set
          have hbody_spec := hbody arg m'' hsub harg_T1
          simp only [Ty.exi_exp_denot] at hbody_spec
          -- Transport from psT1 to psT2 using Rebind
          have hrebind :
              Rebind (env.extend_var arg psT1) Rename.id (env.extend_var arg psT2) :=
            { var := by
                intro x
                cases x <;> simp [TypeEnv.extend_var, TypeEnv.lookup_var, Rename.id]
              tvar := by
                intro X
                cases X; simp [TypeEnv.extend_var, TypeEnv.lookup_tvar, Rename.id]
              cvar := by
                intro C
                cases C; simp [TypeEnv.extend_var, TypeEnv.lookup_cvar, Rename.id] }
          have heq_val := rebind_exi_val_denot (ρ:=hrebind) U1
          -- Lift the evaluation along the exi-val equivalence
          have h_entails_body :
              Mpost.entails_after
                (Ty.exi_val_denot (env.extend_var arg psT1) U1).as_mpost m''
                (Ty.exi_val_denot (env.extend_var arg psT2) U1).as_mpost := by
            apply Mpost.entails_to_entails_after
            apply Denot.imply_to_entails _ _
            have heqv := Denot.equiv_to_imply (by simpa [Ty.rename_id] using heq_val)
            exact heqv.1
          have hbody_psT2 :
              Eval R m'' (t0.subst (Subst.openVar (.free arg)))
                (Ty.exi_val_denot (env.extend_var arg psT2) U1).as_mpost :=
            eval_post_monotonic_general h_entails_body hbody_spec
          -- Apply covariance: if body satisfies U1, it also satisfies U2
          -- Build EnvTyping for the extended context with T2's peak set
          have htyping_ext : EnvTyping (Γ,x:T2) (env.extend_var arg psT2) m'' := by
            simp [TypeEnv.extend_var]
            constructor
            · exact harg_T2
            · constructor
              · exact (compute_peakset_correct htyping T2.captureSet).symm
              · have hsub_H_m'' := Memory.subsumes_trans hsub hsubsumes
                exact env_typing_monotonic htyping hsub_H_m''
          -- Apply semantic subtyping for the result
          have hres_sem := hres (env.extend_var arg psT2) m'' htyping_ext
          have himply_entails := Denot.imply_after_to_m_entails_after hres_sem
          -- Apply monotonicity - goal is already at psT2, no back-rebind needed
          unfold Ty.exi_exp_denot at hbody_psT2 ⊢
          exact eval_post_monotonic_general himply_entails hbody_psT2

lemma sem_subtyp_trans {k : TySort} {T1 T2 T3 : Ty k s}
  (h12 : SemSubtyp Γ T1 T2)
  (h23 : SemSubtyp Γ T2 T3) :
  SemSubtyp Γ T1 T3 := by
  -- Unfold SemSubtyp and handle each type sort
  simp [SemSubtyp] at h12 h23 ⊢
  -- Match on the type sort
  cases k with
  | shape =>
    -- For shape types: prove (Ty.shape_val_denot env T1).ImplyAfter H (Ty.shape_val_denot env T3)
    intro env H htyping
    -- Extract the hypotheses for T1→T2 and T2→T3
    have h12' := h12 env H htyping
    have h23' := h23 env H htyping
    -- Unfold PreDenot.ImplyAfter
    simp [PreDenot.ImplyAfter] at h12' h23' ⊢
    intro R
    -- Extract the Denot.ImplyAfter hypotheses for this specific R
    have h12_R := h12' R
    have h23_R := h23' R
    -- Unfold Denot.ImplyAfter
    simp [Denot.ImplyAfter] at h12_R h23_R ⊢
    intro m' hsubsumes
    -- Apply transitivity of ImplyAt
    exact Denot.implyat_trans (h12_R m' hsubsumes) (h23_R m' hsubsumes)
  | capt =>
    -- For capturing types: prove (Ty.capt_val_denot env T1).ImplyAfter H (Ty.capt_val_denot env T3)
    intro env H htyping
    -- Extract the hypotheses for T1→T2 and T2→T3
    have h12' := h12 env H htyping
    have h23' := h23 env H htyping
    -- Unfold Denot.ImplyAfter
    simp [Denot.ImplyAfter] at h12' h23' ⊢
    intro m' hsubsumes
    -- Apply transitivity of ImplyAt
    exact Denot.implyat_trans (h12' m' hsubsumes) (h23' m' hsubsumes)
  | exi =>
    -- For existential types: prove (Ty.exi_val_denot env T1).ImplyAfter H (Ty.exi_val_denot env T3)
    intro env H htyping
    -- Extract the hypotheses for T1→T2 and T2→T3
    have h12' := h12 env H htyping
    have h23' := h23 env H htyping
    -- Unfold Denot.ImplyAfter
    simp [Denot.ImplyAfter] at h12' h23' ⊢
    intro m' hsubsumes
    -- Apply transitivity of ImplyAt
    exact Denot.implyat_trans (h12' m' hsubsumes) (h23' m' hsubsumes)

lemma sem_subtyp_refl {k : TySort} {T : Ty k s} :
  SemSubtyp Γ T T := by
  -- Unfold SemSubtyp and handle each type sort
  simp [SemSubtyp]
  -- Match on the type sort
  cases k with
  | shape =>
    -- For shape types, prove (Ty.shape_val_denot env T).ImplyAfter H (Ty.shape_val_denot env T)
    intro env H htyping
    simp [PreDenot.ImplyAfter]
    intro R
    simp [Denot.ImplyAfter]
    intro m' hsubsumes
    -- Apply reflexivity of implication
    exact Denot.imply_implyat (Denot.imply_refl _)
  | capt =>
    -- For capturing types, prove (Ty.capt_val_denot env T).ImplyAfter H (Ty.capt_val_denot env T)
    intro env H htyping
    simp [Denot.ImplyAfter]
    intro m' hsubsumes
    -- Apply reflexivity of implication
    exact Denot.imply_implyat (Denot.imply_refl _)
  | exi =>
    -- For existential types, prove (Ty.exi_val_denot env T).ImplyAfter H (Ty.exi_val_denot env T)
    intro env H htyping
    simp [Denot.ImplyAfter]
    intro m' hsubsumes
    -- Apply reflexivity of implication
    exact Denot.imply_implyat (Denot.imply_refl _)

-- Semantic subtyping for mutability bounds
-- Since Mutability.denot m = .top m, we have m1.denot ⊆ m2.denot iff m1 ≤ m2
lemma fundamental_subbound
  (hle : m1 ≤ m2) :
  SemSubbound Γ m1 m2 := by
  intro m
  simp [Mutability.denot]
  exact CapabilityBound.SubsetEq.top_top hle

lemma sem_subtyp_cpoly {m1 m2 : Mutability} {T1 T2 : Ty .exi (s,C)}
  (hB : SemSubbound Γ m1 m2) -- contravariant in bound (m1 ≤ m2)
  (hT : SemSubtyp (Γ,C<:m1) T1 T2) -- covariant in body under tighter bound
  : SemSubtyp Γ (.cpoly m2 T1) (.cpoly m1 T2) := by
  -- Unfold SemSubtyp for shape types
  simp [SemSubtyp]
  intro env H htyping
  -- Need to prove PreDenot.ImplyAfter for cpoly types
  simp [PreDenot.ImplyAfter]
  intro A
  -- Need to prove Denot.ImplyAfter for cpoly types at capability set A
  simp [Denot.ImplyAfter]
  intro m' hsubsumes e h_cpoly_m2_T1
  -- Unfold the denotation of cpoly types
  simp [Ty.shape_val_denot] at h_cpoly_m2_T1 ⊢
  -- Extract the components from m2 ∀C T1 denotation (left side)
  obtain ⟨hwf, cs, B0, t0, hresolve, hcs_wf, hR0_subset, hbody⟩ := h_cpoly_m2_T1
  -- Construct the proof for m1 ∀C T2 (right side)
  constructor
  · exact hwf  -- Well-formedness is preserved
  · use cs, B0, t0
    constructor
    · exact hresolve  -- Same resolution
    · constructor
      · exact hcs_wf  -- Capture set well-formedness preserved
      · constructor
        · exact hR0_subset  -- Same capture subset constraint
        · -- Need to prove the body property with contravariant bound and covariant body
          intro m'' CS hCS_wf hsub_m'' hCS_satisfies_m1
          -- hbody expects: (A0 m'').BoundedBy (m2.denot m'')
          -- We have hCS_satisfies_m1 : (A0 m'').BoundedBy (m1.denot m'')
          -- And hB : SemSubbound Γ m1 m2, i.e., m1.denot ⊆ m2.denot
          let A0 := CS.denot TypeEnv.empty
          have hCS_satisfies_m2 : (A0 m'').BoundedBy (m2.denot m'') := by
            -- Apply contravariance: m1.denot m'' ⊆ m2.denot m''
            exact CapabilitySet.BoundedBy.trans hCS_satisfies_m1 (hB m'')
          -- Apply the original function body with this CS
          have heval1 := hbody m'' CS hCS_wf hsub_m'' hCS_satisfies_m2
          -- Now use covariance hT
          have henv' : EnvTyping (Γ,C<:m1) (env.extend_cvar CS) m'' := by
            simp [TypeEnv.extend_cvar]
            constructor
            · exact hCS_wf
            · constructor
              · -- Convert hCS_satisfies_m1 from CS.denot TypeEnv.empty to CS.ground_denot
                have : CS.denot TypeEnv.empty = CS.ground_denot := by
                  simp [CaptureSet.denot, Subst.from_TypeEnv_empty, CaptureSet.subst_id]
                rw [← this]
                exact hCS_satisfies_m1
              · have hB_trans := Memory.subsumes_trans hsub_m'' hsubsumes
                exact env_typing_monotonic htyping hB_trans
          have hT_sem := hT (env.extend_cvar CS) m'' henv'
          -- hT_sem : (Ty.exi_val_denot (env.extend_cvar CS) T1).ImplyAfter m'' ...
          let R0 := expand_captures m'.heap cs
          -- Convert to postcondition entailment
          have himply_entails := Denot.imply_after_to_m_entails_after hT_sem
          -- Use eval_post_monotonic_general to lift heval1 from T1 to T2
          unfold Ty.exi_exp_denot at heval1 ⊢
          apply eval_post_monotonic_general _ heval1
          exact himply_entails

lemma sem_subtyp_capt {C1 C2 : CaptureSet s} {S1 S2 : Ty .shape s}
  (hC : SemSubcapt Γ C1 C2) -- covariant in capture set
  (hS : SemSubtyp Γ S1 S2) -- covariant in shape
  (hclosed_C2 : C2.IsClosed) -- C2 is closed
  : SemSubtyp Γ (.capt C1 S1) (.capt C2 S2) := by
  -- Unfold SemSubtyp for capt types
  simp [SemSubtyp]
  intro env H htyping
  -- Need to prove Denot.ImplyAfter for capt types
  simp [Denot.ImplyAfter, Denot.ImplyAt]
  intro m hsubsumes e h_capt_C1_S1
  -- Unfold the denotation of capt types
  simp [Ty.capt_val_denot] at h_capt_C1_S1 ⊢
  -- Extract components from C1 S1 denotation
  obtain ⟨hsimple, hwf, hC1_wf, hS1_at_C1⟩ := h_capt_C1_S1
  -- Construct proof for C2 S2
  constructor
  · exact hsimple  -- IsSimpleAns preserved
  constructor
  · exact hwf  -- Well-formedness preserved
  · constructor
    · -- Need: (C2.subst (Subst.from_TypeEnv env)).WfInHeap m.heap
      -- From closedness of C2, we get well-formedness at any heap
      -- First show it's well-formed at H.heap
      have hwf_C2_at_H : (C2.subst (Subst.from_TypeEnv env)).WfInHeap H.heap := by
        -- Use wf_subst with closedness of C2 and well-formedness of the substitution
        apply CaptureSet.wf_subst
        · -- C2.WfInHeap H.heap follows from closedness
          apply CaptureSet.wf_of_closed hclosed_C2
        · -- (Subst.from_TypeEnv env).WfInHeap H.heap follows from EnvTyping
          exact from_TypeEnv_wf_in_heap htyping
      -- Then lift to m.heap using monotonicity
      exact CaptureSet.wf_monotonic hsubsumes hwf_C2_at_H
    · -- Need: Ty.shape_val_denot env S2 (C2.denot env m) m e
      -- We have: hS1_at_C1 : Ty.shape_val_denot env S1 (C1.denot env m) m e
      -- Strategy:
      -- 1. Get C1.denot ⊆ C2.denot from hC
      -- 2. Use capability set covariance to get S1 at C2.denot
      -- 3. Use semantic subtyping hS to get S2 at C2.denot

      -- Step 1: Get capability set subsumption
      have hC_subset : C1.denot env m ⊆ C2.denot env m := by
        have htyping_m := env_typing_monotonic htyping hsubsumes
        exact hC env m htyping_m

      -- Step 2: Lift S1 from C1.denot to C2.denot
      have hS1_at_C2 : Ty.shape_val_denot env S1 (C2.denot env m) m e := by
        -- Use reachability monotonicity: shape types are covariant in capability sets
        have henv_mono := typed_env_is_reachability_monotonic htyping
        have hshape_mono := shape_val_denot_is_reachability_monotonic henv_mono S1
        simp [PreDenot.is_reachability_monotonic] at hshape_mono
        exact hshape_mono (C1.denot env m) (C2.denot env m) hC_subset m e hS1_at_C1

      -- Step 3: Apply semantic subtyping
      have hS_sem := hS env H htyping
      simp [PreDenot.ImplyAfter] at hS_sem
      have hS_at_H := hS_sem (C2.denot env m)
      simp [Denot.ImplyAfter, Denot.ImplyAt] at hS_at_H
      exact hS_at_H m hsubsumes e hS1_at_C2

lemma sem_subtyp_exi {T1 T2 : Ty .capt (s,C)}
  (hT : SemSubtyp (Γ,C<:.epsilon) T1 T2) -- covariant in body
  : SemSubtyp Γ (.exi T1) (.exi T2) := by
  -- Unfold SemSubtyp for exi types
  simp [SemSubtyp]
  intro env H htyping
  -- Need to prove Denot.ImplyAfter for exi types
  simp [Denot.ImplyAfter, Denot.ImplyAt]
  intro m hsubsumes e h_exi_T1
  -- Unfold the denotation of exi types
  simp [Ty.exi_val_denot] at h_exi_T1 ⊢
  -- Extract the pack from the exi denotation
  cases hresolve : resolve m.heap e with
  | none =>
    -- e doesn't resolve, contradiction
    simp [hresolve] at h_exi_T1
  | some cell =>
    simp [hresolve] at h_exi_T1 ⊢
    cases cell with
    | pack CS x =>
      -- h_exi_T1 : CS.WfInHeap m.heap ∧ Ty.capt_val_denot (env.extend_cvar CS) T1 m (.var x)
      -- Need: CS.WfInHeap m.heap ∧ Ty.capt_val_denot (env.extend_cvar CS) T2 m (.var x)
      obtain ⟨hwf_CS, h_body_T1⟩ := h_exi_T1

      -- Construct the well-formedness part of the goal
      constructor
      · exact hwf_CS

      · -- Construct EnvTyping for the extended context
        have henv' : EnvTyping (Γ,C<:.epsilon) (env.extend_cvar CS) m := by
          simp [TypeEnv.extend_cvar]
          constructor
          · -- Need: CS.WfInHeap m.heap
            exact hwf_CS
          · constructor
            · -- Need: (CS.ground_denot m).BoundedBy (.epsilon.denot m)
              -- .epsilon.denot m = .top .epsilon, and any set has kind .epsilon
              simp [Mutability.denot]
              exact CapabilitySet.BoundedBy.top CapabilitySet.HasKind.eps
            · exact env_typing_monotonic htyping hsubsumes

        -- Apply semantic subtyping
        have hT_sem := hT (env.extend_cvar CS) m henv'
        simp [Denot.ImplyAfter, Denot.ImplyAt] at hT_sem
        exact hT_sem m (Memory.subsumes_refl m) (.var x) h_body_T1
    | _ =>
      -- Other cell types don't match exi
      simp at h_exi_T1

lemma sem_subtyp_typ {T1 T2 : Ty .capt s}
  (hT : SemSubtyp Γ T1 T2) -- covariant in body
  : SemSubtyp Γ (.typ T1) (.typ T2) := by
  -- Unfold SemSubtyp for exi types
  simp [SemSubtyp]
  intro env H htyping
  -- Unfold exi_val_denot for .typ
  -- .typ T has denotation capt_val_denot env T
  simp [Ty.exi_val_denot]
  -- The goal is now: (capt_val_denot env T1).ImplyAfter H (capt_val_denot env T2)
  -- Which is exactly SemSubtyp Γ T1 T2 (for capt types)
  exact hT env H htyping

lemma sem_subtyp_poly {S1 S2 : Ty .shape s} {T1 T2 : Ty .exi (s,X)}
  (hS : SemSubtyp Γ S2 S1) -- contravariant in bound
  (hT : SemSubtyp (Γ,X<:S2) T1 T2) -- covariant in body
  : SemSubtyp Γ (.poly S1 T1) (.poly S2 T2) := by
  -- Unfold SemSubtyp for shape types
  simp [SemSubtyp]
  intro env H htyping
  -- Need to prove PreDenot.ImplyAfter for poly types
  simp [PreDenot.ImplyAfter]
  intro A
  -- Need to prove Denot.ImplyAfter for poly types at capability set A
  simp [Denot.ImplyAfter]
  intro m' hsubsumes e h_poly_S1_T1
  -- Unfold the denotation of poly types
  simp [Ty.shape_val_denot] at h_poly_S1_T1 ⊢
  -- Extract the components from the S1 ∀ T1 denotation
  obtain ⟨hwf, cs, S0, t0, hresolve, hcs_wf, hR0_subset, hbody⟩ := h_poly_S1_T1
  -- Construct the proof for S2 ∀ T2
  constructor
  · exact hwf  -- Well-formedness is preserved
  · use cs, S0, t0
    constructor
    · exact hresolve  -- Same resolution
    · constructor
      · exact hcs_wf  -- Capture set well-formedness preserved
      · constructor
        · exact hR0_subset  -- Same capture subset constraint
        · -- Need to prove the body property with contravariant bound and covariant body
          intro m'' denot hsub_m'' hdenot_proper himply_S2
          -- hbody expects denot.ImplyAfter m'' (Ty.shape_val_denot env S1)
          -- We have himply_S2 : denot.ImplyAfter m'' (Ty.shape_val_denot env S2)
          -- And hS : SemSubtyp Γ S2 S1, i.e., S2 <: S1
          -- So we need to compose: denot -> S2 -> S1
          have himply_S1 : denot.ImplyAfter m'' (Ty.shape_val_denot env S1) := by
            simp [PreDenot.ImplyAfter, Denot.ImplyAfter, Denot.ImplyAt]
            intro C m''' hsub_m''' e' hdenot
            -- We have: hdenot : (denot C) m''' e'
            -- Need: (Ty.shape_val_denot env S1 C) m''' e'
            -- From himply_S2: denot.ImplyAfter m'' (Ty.shape_val_denot env S2)
            simp [PreDenot.ImplyAfter, Denot.ImplyAfter, Denot.ImplyAt] at himply_S2
            have hS2 := himply_S2 C m''' hsub_m''' e' hdenot
            -- Now apply hS: SemSubtyp Γ S2 S1
            have hS_trans :=
              Memory.subsumes_trans hsub_m''' (Memory.subsumes_trans hsub_m'' hsubsumes)
            have hS_sem := hS env H htyping
            simp [PreDenot.ImplyAfter, Denot.ImplyAfter, Denot.ImplyAt] at hS_sem
            exact hS_sem C m''' hS_trans e' hS2
          -- Apply the original function body with this denot
          have heval1 := hbody m'' denot hsub_m'' hdenot_proper himply_S1
          -- Now use covariance hT
          have henv' : EnvTyping (Γ,X<:S2) (env.extend_tvar denot) m'' := by
            constructor
            · exact hdenot_proper
            · constructor
              · exact himply_S2
              · apply env_typing_monotonic htyping (Memory.subsumes_trans hsub_m'' hsubsumes)
          have hT_sem := hT (env.extend_tvar denot) m'' henv'
          -- hT_sem : (Ty.exi_val_denot (env.extend_tvar denot) T1).ImplyAfter m'' ...
          let R0 := expand_captures m'.heap cs
          -- Convert to postcondition entailment
          have himply_entails := Denot.imply_after_to_m_entails_after hT_sem
          -- Use eval_post_monotonic_general to lift heval1 from T1 to T2
          unfold Ty.exi_exp_denot at heval1 ⊢
          apply eval_post_monotonic_general _ heval1
          exact himply_entails

-/

theorem fundamental_subtyp
  (hT1 : T1.IsClosed) (hT2 : T2.IsClosed)
  (hsub : Subtyp Γ T1 T2) :
  SemSubtyp Γ T1 T2 := by
  induction hsub
  case top hpure => exact sem_subtyp_top hpure
  all_goals sorry
  -- case refl =>
  --   -- T1 = T2
  --   apply sem_subtyp_refl
  -- case trans T2_mid hT2_mid _hsub12 _hsub23 ih12 ih23 =>
  --   -- hsub is (T1 <: T2_mid <: T2), where T2_mid is the middle type
  --   -- hT2_mid : T2_mid.IsClosed (provided by the trans rule)
  --   -- ih12 : T1.IsClosed → T2_mid.IsClosed → SemSubtyp Γ T1 T2_mid
  --   -- ih23 : T2_mid.IsClosed → T2.IsClosed → SemSubtyp Γ T2_mid T2
  --   apply sem_subtyp_trans (ih12 hT1 hT2_mid) (ih23 hT2_mid hT2)
  -- case tvar hlookup =>
  --   -- T1 is a type variable, T2 is looked up from context
  --   apply sem_subtyp_tvar hlookup
  -- case arrow T1_arg T2_arg U1 U2 hsub_arg hsub_res ih_arg ih_res =>
  --   -- T1 = .arrow T1_arg U1, T2 = .arrow T2_arg U2
  --   -- Extract closedness from arrow types
  --   cases hT1 with | arrow hT1_arg_closed hU1_closed =>
  --   cases hT2 with | arrow hT2_arg_closed hU2_closed =>
  --   apply sem_subtyp_arrow (ih_arg hT2_arg_closed hT1_arg_closed) (ih_res hU1_closed hU2_closed)
  -- case poly S1 S2 T1_body T2_body hsub_bound hsub_body ih_bound ih_body =>
  --   -- T1 = .poly S1 T1_body, T2 = .poly S2 T2_body
  --   -- Extract closedness from poly types
  --   cases hT1 with | poly hS1_closed hT1_body_closed =>
  --   cases hT2 with | poly hS2_closed hT2_body_closed =>
  --   apply sem_subtyp_poly (ih_bound hS2_closed hS1_closed) (ih_body hT1_body_closed hT2_body_closed)
  -- case cpoly hsub_bound hsub_body ih_body =>
  --   -- The subtyping rule is: m2 ≤ m1 -> Subtyp (Γ,C<:m2) T1 T2
  --   --                        -> Subtyp Γ (.cpoly m1 T1) (.cpoly m2 T2)
  --   -- Extract closedness from cpoly types (Mutability bound has no closedness)
  --   cases hT1 with | cpoly hT1_body_closed =>
  --   cases hT2 with | cpoly hT2_body_closed =>
  --   apply sem_subtyp_cpoly (fundamental_subbound hsub_bound)
  --     (ih_body hT1_body_closed hT2_body_closed)
  -- case capt C1 C2 S1 S2 hsub_capt hsub_shape ih_shape =>
  --   -- Extract closedness from capt types
  --   cases hT1 with | capt hC1_closed hS1_closed =>
  --   cases hT2 with | capt hC2_closed hS2_closed =>
  --   -- Convert syntactic subcapture to semantic
  --   have ih_capt := fundamental_subcapt hsub_capt
  --   -- Apply the lemma
  --   apply sem_subtyp_capt ih_capt (ih_shape hS1_closed hS2_closed) hC2_closed
  -- case exi T1_body T2_body hsub_body ih_body =>
  --   -- Extract closedness from exi types
  --   cases hT1 with | exi hT1_body_closed =>
  --   cases hT2 with | exi hT2_body_closed =>
  --   -- Apply the lemma
  --   apply sem_subtyp_exi (ih_body hT1_body_closed hT2_body_closed)
  -- case typ T1_body T2_body hsub_body ih_body =>
  --   -- T1 = .typ T1_body, T2 = .typ T2_body
  --   -- Extract closedness from typ types
  --   cases hT1 with | typ hT1_body_closed =>
  --   cases hT2 with | typ hT2_body_closed =>
  --   -- Apply the lemma
  --   apply sem_subtyp_typ (ih_body hT1_body_closed hT2_body_closed)

/-

theorem sem_typ_subtyp
  {C1 C2 : CaptureSet s} {E1 E2 : Ty .exi s}
  (ht : C1 # Γ ⊨ e : E1)
  (hsubcapt : Subcapt Γ C1 C2)
  (hsubtyp : Subtyp Γ E1 E2)
  (_hclosed_C1 : C1.IsClosed) (hclosed_E1 : E1.IsClosed)
  (_hclosed_C2 : C2.IsClosed) (hclosed_E2 : E2.IsClosed) :
  C2 # Γ ⊨ e : E2 := by
  -- Unfold semantic typing
  intro env m htyping
  simp [Ty.exi_exp_denot]

  -- Get the evaluation from ht at C1 and E1
  have h_eval_E1 := ht env m htyping
  simp [Ty.exi_exp_denot] at h_eval_E1
  -- h_eval_E1 : Eval (C1.denot env m) m (e.subst ...) (exi_val_denot env E1).as_mpost

  -- Use fundamental_subcapt to get C1.denot ⊆ C2.denot
  have hsubcapt_sem := fundamental_subcapt hsubcapt env m htyping
  -- hsubcapt_sem : C1.denot env m ⊆ C2.denot env m

  -- Lift the evaluation from C1 to C2 using capability set monotonicity
  have h_eval_E1_at_C2 := eval_capability_set_monotonic h_eval_E1 hsubcapt_sem
  -- h_eval_E1_at_C2 : Eval (C2.denot env m) m (e.subst ...) (exi_val_denot env E1).as_mpost

  -- Use fundamental_subtyp to get E1 <: E2 semantically
  have hsubtyp_sem := fundamental_subtyp hclosed_E1 hclosed_E2 hsubtyp env m htyping
  -- hsubtyp_sem : (exi_val_denot env E1).ImplyAfter m (exi_val_denot env E2)

  -- Convert ImplyAfter to entailment
  have h_entails := Denot.imply_after_to_m_entails_after hsubtyp_sem
  -- h_entails : (exi_val_denot env E1).as_mpost.entails_after m (exi_val_denot env E2).as_mpost

  -- Lift the evaluation from E1 to E2 using postcondition monotonicity
  exact eval_post_monotonic_general h_entails h_eval_E1_at_C2

lemma simple_val_not_pack {e : Exp s}
  (hsimple : e.IsSimpleVal)
  (hpack : e.IsPack) : False := by
  -- IsSimpleVal and IsPack apply to disjoint sets of constructors
  cases hsimple <;> cases hpack

lemma resolve_pack_eq {e : Exp {}} {m : Memory} {CS : CaptureSet {}} {x : Var .var {}}
  (hres : resolve m.heap e = some (.pack CS x))
  (hpack : e.IsPack) : e = .pack CS x := by
  -- If resolve returns a pack and e is a pack, then e equals that pack
  cases hpack
  -- e = .pack cs y for some cs, y
  rename_i cs y
  simp [resolve] at hres
  obtain ⟨h1, h2⟩ := hres
  rw [h1, h2]

theorem resolve_is_pack {e : Exp {}} {m : Memory}
  (hres : resolve m.heap e = some v)
  (hv : v.IsPack) : e.IsPack := by
  -- Case analyze on e
  cases e <;> simp [resolve] at hres
  case pack cs x =>
    -- For packs, resolve returns the pack itself
    -- After simp, hres : .pack cs x = v
    rw [← hres] at hv
    exact hv
  case var y =>
    -- For variables, resolve looks up in the heap
    cases y
    case bound bv => cases bv
    case free fy =>
      -- resolve looks up m.heap fy
      -- If it returns some v where v.IsPack, then the heap contains a pack
      -- But packs are not simple values, so they shouldn't be in the heap
      -- We need to derive a contradiction
      cases hval : m.heap fy <;> simp [hval] at hres
      rename_i cell
      cases cell <;> simp at hres
      rename_i val
      -- After simp, hres : val.unwrap = v
      rw [← hres] at hv
      -- Now hv : val.unwrap.IsPack
      -- But val.isVal : val.unwrap.IsSimpleVal
      -- Use simple_val_not_pack to derive contradiction
      exfalso
      exact simple_val_not_pack val.isVal hv
  -- For all other expressions, resolve returns them unchanged
  all_goals {
    -- After simp, hres : e = v
    rw [← hres] at hv
    exact hv
  }

theorem sem_typ_unpack
  {C : CaptureSet s} {Γ : Ctx s} {t : Exp s} {T : Ty .capt (s,C)}
  {u : Exp (s,C,x)} {U : Ty .exi s}
  (hclosed_C : C.IsClosed)
  (ht : C # Γ ⊨ t : .exi T)
  (hu : (C.rename Rename.succ).rename Rename.succ #
        (Γ,C<:.epsilon,x:T) ⊨ u : (U.rename Rename.succ).rename Rename.succ) :
  C # Γ ⊨ (Exp.unpack t u) : U := by
  intro env store hts
  simp [Exp.subst]
  simp [Ty.exi_exp_denot]
  -- Use Eval.eval_unpack with Q1 = (Ty.exi_val_denot env (.exi T)).as_mpost
  apply Eval.eval_unpack (Q1 := (Ty.exi_val_denot env (.exi T)).as_mpost)
  case hpred =>
    -- Show (Ty.exi_val_denot env (.exi T)).as_mpost is monotonic
    intro m1 m2 e hwf hsub hQ
    simp [Denot.as_mpost] at hQ ⊢
    have henv_mono := typed_env_is_monotonic hts
    exact exi_val_denot_is_monotonic henv_mono (.exi T) hsub hQ
  case hbool =>
    -- Show (Ty.exi_val_denot env (.exi T)).as_mpost is bool independent
    apply Denot.as_mpost_is_bool_independent
    exact exi_val_denot_is_bool_independent (typed_env_is_bool_independent hts) (.exi T)
  case a =>
    -- Show Eval ... store (t.subst ...) (Ty.exi_val_denot env (.exi T)).as_mpost
    have ht' := ht env store hts
    simp [Ty.exi_exp_denot] at ht'
    exact ht'
  case h_nonstuck =>
    -- Prove that values satisfying exi_val_denot are packs and well-formed
    intro m1 v hQ1
    simp [Denot.as_mpost, Ty.exi_val_denot] at hQ1
    -- hQ1 : match resolve m1.heap v with | some (.pack CS x) => ... | _ => False
    -- Case analyze on resolve result
    cases hres : resolve m1.heap v <;> simp [hres] at hQ1
    rename_i exp
    cases exp <;> simp at hQ1
    -- Only pack case is valid
    rename_i CS x_pack
    obtain ⟨hwf_CS, hQ1_body⟩ := hQ1
    constructor
    · -- Prove v.IsPack
      -- Use resolve_is_pack: if resolve returns a pack, then v is a pack
      have hpack : (Exp.pack CS x_pack).IsPack := Exp.IsPack.pack
      exact resolve_is_pack hres hpack
    · -- Prove v.WfInHeap m1.heap
      -- First show that v = .pack CS x_pack
      have hpack : (Exp.pack CS x_pack).IsPack := Exp.IsPack.pack
      have hv_pack : v.IsPack := resolve_is_pack hres hpack
      have heq : v = .pack CS x_pack := resolve_pack_eq hres hv_pack
      -- Now prove well-formedness of the pack
      rw [heq]
      apply Exp.WfInHeap.wf_pack
      · -- Prove CS.WfInHeap m1.heap
        exact hwf_CS
      · -- Prove x_pack.WfInHeap m1.heap
        -- Extract from hQ1_body : Ty.capt_val_denot (env.extend_cvar CS) T m1 (Exp.var x_pack)
        cases T with
        | capt C_T S =>
          simp [Ty.capt_val_denot] at hQ1_body
          obtain ⟨_, hwf_var, _, _⟩ := hQ1_body
          cases hwf_var with
          | wf_var hwf_v =>
            exact hwf_v
  case h_val =>
    -- Handle the value case: t evaluated to a pack
    intro m1 x cs hs1 hwf_x hwf_cs hQ1
    simp [Denot.as_mpost] at hQ1
    -- hQ1 : Ty.exi_val_denot env (.exi T) m1 (.pack cs x)
    -- This means: Ty.capt_val_denot (env.extend_cvar cs) T m1 (.var x)
    simp [Ty.exi_val_denot] at hQ1
    -- Extract the variable from x
    cases x
    case bound bx => cases bx  -- No bound variables in empty signature
    case free fx =>
      -- Now hQ1 : After resolving pack cs (free fx), we get the value denot
      -- Simplify hQ1 by resolving the pack
      simp [resolve] at hQ1
      -- Now hQ1 : cs.WfInHeap m1.heap ∧ Ty.capt_val_denot ... m1 (.var (.free fx))
      obtain ⟨hwf_cs, hQ1_body⟩ := hQ1

      let ps := CaptureSet.peakset (Γ,C<:.epsilon) T.captureSet
      -- Apply hu with doubly extended environment
      have hu' := hu ((env.extend_cvar cs).extend_var fx ps) m1
      simp [Ty.exi_exp_denot] at hu' ⊢

      -- First, construct the typing context for hu'
      -- Need to show: EnvTyping (Γ,C<:unbound,x:T) (extended environment) m1
      have hts_extended :
        EnvTyping (Γ,C<:.epsilon,x:T) ((env.extend_cvar cs).extend_var fx ps) m1 := by
        -- This unfolds to a conjunction by EnvTyping definition
        constructor
        · -- Show: Ty.capt_val_denot (env.extend_cvar cs) T m1 (.var (.free fx))
          exact hQ1_body
        · constructor
          · rfl
          · -- Show: EnvTyping (Γ,C<:.epsilon) (env.extend_cvar cs) m1
            -- This is a 3-tuple: (cs.WfInHeap, bound check, env typing)
            constructor
            · -- Show: cs.WfInHeap m1.heap
              exact hwf_cs
            · constructor
              · -- Show: (cs.ground_denot m1).BoundedBy (.epsilon.denot m1)
                -- .epsilon.denot m1 = .top .epsilon, and every set has kind .epsilon
                simp [Mutability.denot]
                exact CapabilitySet.BoundedBy.top CapabilitySet.HasKind.eps
              · -- Show: EnvTyping Γ env m1
                exact env_typing_monotonic hts hs1

      -- Apply hu' with the typing context
      have hu'' := hu' hts_extended

      -- Expression substitution equality
      have hexp_eq :
        (u.subst (Subst.from_TypeEnv env).lift.lift).subst (Subst.unpack cs (Var.free fx)) =
          u.subst (Subst.from_TypeEnv ((env.extend_cvar cs).extend_var fx ps)) := by
        rw [Exp.subst_comp, Subst.from_TypeEnv_weaken_unpack (ps:=ps)]

      -- Capture set equality via rebinding
      have hcap_eq :
        ((C.rename Rename.succ).rename Rename.succ).denot
          ((env.extend_cvar cs).extend_var fx ps) m1 =
        C.denot env store := by
        -- Use rebind to show double-renamed C equals original C
        have h1 := rebind_captureset_denot (Rebind.cweaken (env:=env) (cs:=cs)) C
        have h2 := rebind_captureset_denot
          (Rebind.weaken (env:=env.extend_cvar cs) (x:=fx) (ps:=ps))
          (C.rename Rename.succ)
        calc
          ((C.rename Rename.succ).rename Rename.succ).denot
            ((env.extend_cvar cs).extend_var fx ps) m1
          _ = (C.rename Rename.succ).denot (env.extend_cvar cs) m1 := by rw [<-h2]
          _ = C.denot env m1 := by rw [<-h1]
          _ = C.denot env store := by
            have hwf_C : (C.subst (Subst.from_TypeEnv env)).WfInHeap store.heap := by
              apply CaptureSet.wf_subst
              · apply CaptureSet.wf_of_closed hclosed_C
              · apply from_TypeEnv_wf_in_heap hts
            exact (capture_set_denot_is_monotonic hwf_C hs1).symm

      -- Type equivalence via double rebind
      have heqv_composed : Ty.exi_val_denot env U ≈
        Ty.exi_val_denot ((env.extend_cvar cs).extend_var fx ps)
          ((U.rename Rename.succ).rename Rename.succ) := by
        have heqv1 := rebind_exi_val_denot (Rebind.cweaken (env:=env) (cs:=cs)) U
        have heqv2 := rebind_exi_val_denot
          (Rebind.weaken (env:=env.extend_cvar cs) (x:=fx) (ps:=ps))
          (U.rename Rename.succ)
        intro m e
        rw [heqv1, heqv2]

      -- Apply hu'' with conversions
      change Eval (C.denot env store) m1
        ((u.subst (Subst.from_TypeEnv env).lift.lift).subst (Subst.unpack cs (Var.free fx)))
        (Ty.exi_val_denot env U).as_mpost
      rw [hexp_eq, <-hcap_eq]
      apply eval_post_monotonic _ hu''
      apply Denot.imply_to_entails
      apply (Denot.equiv_to_imply heqv_composed).2

-/

/-- The fundamental theorem of semantic type soundness. -/
theorem fundamental
  (ht : C # Γ ⊢ e : T) :
  C # Γ ⊨ e : T := by
  have hclosed_e := HasType.exp_is_closed ht
  induction ht
  case var hx =>
    exact sem_typ_var hx
  case abs ih =>
    apply sem_typ_abs
    · exact hclosed_e
    · cases hclosed_e
      rename_i hclosed_cs hclosed_T1 hclosed_e0
      exact ih hclosed_e0
  case tabs ih =>
    apply sem_typ_tabs
    · exact hclosed_e
    · cases hclosed_e
      rename_i hclosed_cs hclosed_S hclosed_e0
      exact ih hclosed_e0
  case cabs ih =>
    apply sem_typ_cabs
    · exact hclosed_e
    · cases hclosed_e
      rename_i hclosed_cs hclosed_e0
      exact ih hclosed_e0
  case pack ih =>
    apply sem_typ_pack
    · exact hclosed_e
    · cases hclosed_e with | pack _ hx_closed =>
      exact ih (Exp.IsClosed.var hx_closed)
  case app =>
    rename_i hx hy
    -- From closedness of (app x y), extract that x and y are closed variables
    cases hclosed_e with
    | app hx_closed hy_closed =>
      -- Closed variables must be bound (not free heap pointers)
      cases hx_closed
      cases hy_closed
      -- Apply IHs to get semantic typing for the variables
      have ih_x := hx (Exp.IsClosed.var Var.IsClosed.bound)
      have ih_y := hy (Exp.IsClosed.var Var.IsClosed.bound)
      -- The types should match definitionally when refineCaptureSet is applied
      -- (Ty.arrow T1 cs T2).refineCaptureSet cs = Ty.arrow T1 cs T2
      -- sem_typ_app needs cs parameter - but it should unify from the hypotheses
      apply sem_typ_app
      · exact ih_x
      · exact ih_y
  case tapp =>
    rename_i hS_closed hx
    -- From closedness of (tapp x S), extract that x and S are closed
    cases hclosed_e with
    | tapp hx_closed hS_closed =>
      -- Closed variables must be bound (not free heap pointers)
      cases hx_closed
      -- Apply IH to get semantic typing for the variable
      have ih_x := hx (Exp.IsClosed.var Var.IsClosed.bound)
      -- Apply sem_typ_tapp theorem
      exact sem_typ_tapp ih_x
  case capp =>
    rename_i _ _ _ _ _ _ _ _ hD_closed hD_kind _ _ _ ih_x
    -- From closedness of (capp x D), extract that x and D are closed
    cases hclosed_e with
    | capp hx_closed hD_closed_exp =>
      -- Closed variables must be bound (not free heap pointers)
      cases hx_closed
      -- Apply IH to get semantic typing for the variable
      have hx := ih_x (Exp.IsClosed.var Var.IsClosed.bound)
      -- Apply sem_typ_capp theorem
      exact sem_typ_capp hD_closed_exp hD_kind hx
  case invoke =>
    rename_i ih_x ih_y
    -- From closedness of (app x y), extract that x and y are closed
    cases hclosed_e with
    | app hx_closed hy_closed =>
      -- Closed variables must be bound (not free heap pointers)
      cases hx_closed
      cases hy_closed
      -- Apply IHs to get semantic typing for the variables
      have hx := ih_x (Exp.IsClosed.var Var.IsClosed.bound)
      have hy := ih_y (Exp.IsClosed.var Var.IsClosed.bound)
      -- Apply sem_typ_invoke theorem
      exact sem_typ_invoke hx hy
  case unit => exact sem_typ_unit
  case btrue => exact sem_typ_btrue
  case bfalse => exact sem_typ_bfalse
  case cond ht1 ht2 ht3 ih1 ih2 ih3 =>
    -- hclosed_e gives closedness of cond e1 e2 e3
    cases hclosed_e with
    | cond hclosed_guard hclosed_then hclosed_else =>
      have hclosedC1 := HasType.use_set_is_closed ht1
      have hclosedC2 := HasType.use_set_is_closed ht2
      have hclosedC3 := HasType.use_set_is_closed ht3
      exact sem_typ_cond hclosedC1 hclosedC2 hclosedC3 hclosed_guard hclosed_then hclosed_else
        (ih1 (Exp.IsClosed.var hclosed_guard)) (ih2 hclosed_then) (ih3 hclosed_else)
  case reader hΓ_closed hx =>
    exact sem_typ_reader hΓ_closed hx
  case read =>
    rename_i hx_syn hx_ih
    cases hclosed_e with
    | read hx_closed =>
      cases hx_closed
      exact sem_typ_read
        (hx_ih (Exp.IsClosed.var Var.IsClosed.bound))
  case write =>
    rename_i hx_syn hy_syn hx_ih hy_ih
    cases hclosed_e with
    | write hx_closed hy_closed =>
      cases hx_closed
      cases hy_closed
      exact sem_typ_write
        (hx_ih (Exp.IsClosed.var Var.IsClosed.bound))
        (hy_ih (Exp.IsClosed.var Var.IsClosed.bound))
  case par ht1_syn ht2_syn ht1_ih ht2_ih =>
    -- Extract closedness of both branches
    cases hclosed_e with
    | par hclosed_e1 hclosed_e2 =>
      exact sem_typ_par (ht1_ih hclosed_e1) (ht2_ih hclosed_e2)
  case letin =>
    rename_i ht1_syn ht2_syn ht1_ih ht2_ih
    cases hclosed_e with
    | letin he1_closed he2_closed =>
      exact sem_typ_letin
        (HasType.use_set_is_closed ht1_syn)
        (Exp.IsClosed.letin he1_closed he2_closed)
        (ht1_ih he1_closed)
        (ht2_ih he2_closed)
  all_goals sorry
  -- case reader hΓ_closed hx =>
  --   exact sem_typ_reader hΓ_closed hx
  -- case pack =>
  --   rename_i ih
  --   apply sem_typ_pack
  --   · exact hclosed_e
  --   · cases hclosed_e with | pack _ hx_closed =>
  --     apply ih
  --     constructor
  --     exact hx_closed
  -- case unit => exact sem_typ_unit
  -- case btrue => exact sem_typ_btrue
  -- case bfalse => exact sem_typ_bfalse
  -- case cond ht1 ht2 ht3 ih1 ih2 ih3 =>
  --   -- hclosed_e gives closedness of cond e1 e2 e3
  --   cases hclosed_e with
  --   | cond hclosed_guard hclosed_then hclosed_else =>
  --     have hclosedC1 := HasType.use_set_is_closed ht1
  --     have hclosedC2 := HasType.use_set_is_closed ht2
  --     have hclosedC3 := HasType.use_set_is_closed ht3
  --     exact sem_typ_cond hclosedC1 hclosedC2 hclosedC3 hclosed_guard hclosed_then hclosed_else
  --       (ih1 (Exp.IsClosed.var hclosed_guard)) (ih2 hclosed_then) (ih3 hclosed_else)
  -- case invoke =>
  --   rename_i hx hy
  --   -- From closedness of (app x y), extract that x and y are closed
  --   cases hclosed_e with
  --   | app hx_closed hy_closed =>
  --     -- Closed variables must be bound (not free heap pointers)
  --     cases hx_closed
  --     cases hy_closed
  --     -- Apply IHs to get semantic typing for the variables
  --     -- Then apply sem_typ_invoke theorem
  --     exact sem_typ_invoke
  --       (hx (Exp.IsClosed.var Var.IsClosed.bound))
  --       (hy (Exp.IsClosed.var Var.IsClosed.bound))
  -- case letin =>
  --   rename_i ht1_syn ht2_syn ht1_ih ht2_ih
  --   cases hclosed_e with
  --   | letin he1_closed he2_closed =>
  --     exact sem_typ_letin
  --       (HasType.use_set_is_closed ht1_syn)
  --       (Exp.IsClosed.letin he1_closed he2_closed)
  --       (ht1_ih he1_closed)
  --       (ht2_ih he2_closed)
  -- case unpack =>
  --   rename_i ht_syn hu_syn ht_ih hu_ih
  --   cases hclosed_e with
  --   | unpack ht_closed hu_closed =>
  --     exact sem_typ_unpack
  --       (HasType.use_set_is_closed ht_syn)
  --       (ht_ih ht_closed)
  --       (hu_ih hu_closed)
  -- case read =>
  --   rename_i hx_syn hx_ih
  --   -- From closedness of (read x), extract that x is closed
  --   cases hclosed_e with
  --   | read hx_closed =>
  --     -- Closed variables must be bound (not free heap pointers)
  --     cases hx_closed
  --     -- Apply IH to get semantic typing for the variable
  --     exact sem_typ_read
  --       (hx_ih (Exp.IsClosed.var Var.IsClosed.bound))
  -- case write =>
  --   rename_i hx_syn hy_syn hx_ih hy_ih
  --   -- From closedness of (write x y), extract that x and y are closed
  --   cases hclosed_e with
  --   | write hx_closed hy_closed =>
  --     -- Closed variables must be bound (not free heap pointers)
  --     cases hx_closed
  --     cases hy_closed
  --     -- Apply IHs to get semantic typing for the variables
  --     exact sem_typ_write
  --       (hx_ih (Exp.IsClosed.var Var.IsClosed.bound))
  --       (hy_ih (Exp.IsClosed.var Var.IsClosed.bound))
  -- case subtyp ht_syn hsubcapt hsubtyp hclosed_C2 hclosed_E2 ht_ih =>
  --   -- Get closedness of C1 from the syntactic typing derivation
  --   have hclosed_C1 := HasType.use_set_is_closed ht_syn
  --   -- Get closedness of E1 from the syntactic typing derivation
  --   have hclosed_E1 := HasType.type_is_closed ht_syn
  --   -- Apply the semantic subtyping lemma
  --   apply sem_typ_subtyp (ht_ih hclosed_e) hsubcapt hsubtyp
  --     hclosed_C1 hclosed_E1 hclosed_C2 hclosed_E2

end Capybara
