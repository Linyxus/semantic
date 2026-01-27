import Semantic.CaplessK.Denotation
import Semantic.CaplessK.Semantics
namespace CaplessK

theorem typed_env_lookup_var
  (hts : EnvTyping Γ env store)
  (hx : Ctx.LookupVar Γ x T) :
  Ty.capt_val_denot env T store (.var (.free (env.lookup_var x))) := by
  induction hx generalizing store
  case here =>
    -- The environment must match the context structure
    rename_i Γ0 T0
    cases env; rename_i info0 env0
    cases info0; rename_i n
    simp [EnvTyping] at hts
    simp [TypeEnv.lookup_var, TypeEnv.lookup]
    -- Apply weaken_capt_val_denot equivalence
    have heqv := weaken_capt_val_denot (env:=env0) (x:=n) (T:=T0)
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
      cases info0; rename_i n
      simp [EnvTyping] at hts
      obtain ⟨_, henv0⟩ := hts
      -- Apply IH to get the result for env0
      have hih := b henv0
      -- Show that lookup_var .there reduces correctly
      simp [TypeEnv.lookup_var, TypeEnv.lookup]
      -- Apply weakening
      have heqv := weaken_capt_val_denot (env:=env0) (x:=n) (T:=T0)
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
      cases info0; rename_i cs
      simp [EnvTyping] at hts
      obtain ⟨_, _, _, henv0⟩ := hts
      have hih := b henv0
      simp [TypeEnv.lookup_var, TypeEnv.lookup]
      have heqv := cweaken_capt_val_denot (env:=env0) (cs:=cs) (T:=T0)
      apply (Denot.equiv_to_imply heqv).1
      exact hih

theorem typed_env_lookup_var_reachability
  (hts : EnvTyping Γ env m)
  (hx : Ctx.LookupVar Γ x T) :
  reachability_of_loc m.heap (env.lookup_var x) ⊆ T.captureSet.denot env m := by
  induction hx generalizing m
  case here =>
    -- Γ = .push Γ' (.var T'), x = .here
    rename_i Γ' T'
    cases env; rename_i info' env'
    cases info'; rename_i n
    simp [EnvTyping] at hts
    simp [TypeEnv.lookup_var, TypeEnv.lookup]
    -- From hts.1, we have: Ty.capt_val_denot env' T' m (.var (.free n))
    -- Need: reachability_of_loc m.heap n ⊆
    --       (T'.captureSet.rename Rename.succ).denot (env'.extend_var n) m
    -- Extract capture set from T'
    cases T' with | capt C S =>
    -- From hts.1: Ty.capt_val_denot env' (.capt C S) m (.var (.free n))
    -- This gives us: Ty.shape_val_denot env' S (C.denot env' m) m
    --   (.var (.free n))
    have hval := hts.1
    simp [Ty.capt_val_denot] at hval
    obtain ⟨_, _, _, hshape⟩ := hval
    -- Apply reachability safety to get:
    --   resolve_reachability m.heap (.var (.free n)) ⊆ C.denot env' m
    have hsafe := shape_val_denot_is_reachability_safe
      (typed_env_is_reachability_safe hts.2) S
    have hreach := hsafe (C.denot env' m) m (.var (.free n)) hshape
    -- resolve_reachability for variables equals reachability_of_loc
    simp [resolve_reachability] at hreach
    -- Simplify the goal to show it matches the expected form
    simp [Ty.captureSet, Ty.rename]
    -- Use rebinding to relate C.denot env' with
    -- (C.rename Rename.succ).denot (env'.extend n)
    have hreb := rebind_captureset_denot (Rebind.weaken (env:=env') (x:=n)) C
    -- hreb : C.denot env' = (C.rename Rename.succ).denot (env'.extend_var n)
    -- Need to apply this to memory m
    have hreb_m : C.denot env' m =
      (C.rename Rename.succ).denot (env'.extend (TypeInfo.var n)) m := by
      rw [hreb]
      rfl
    rw [<-hreb_m]
    exact hreach
  case there b hx_prev ih =>
    -- Handle three cases based on the binding kind
    cases b
    case var =>
      rename_i Γ' x' T' Tb
      cases env; rename_i info' env'
      cases info'; rename_i n
      simp [EnvTyping] at hts
      obtain ⟨_, henv'⟩ := hts
      have hih := ih henv'
      simp [TypeEnv.lookup_var, TypeEnv.lookup]
      -- Use rebinding to relate authorities in predecessor and extended env
      -- hih : reachability_of_loc m.heap (env'.lookup_var x') ⊆
      --       T'.captureSet.denot env' m
      -- Need: reachability_of_loc m.heap (env'.lookup_var x') ⊆
      --       (T'.rename Rename.succ).captureSet.denot (env'.extend_var n) m
      -- First, show that (T'.rename f).captureSet = T'.captureSet.rename f
      cases T' with | capt C S =>
      simp [Ty.captureSet, Ty.rename]
      simp [Ty.captureSet] at hih
      have hreb := rebind_captureset_denot
        (Rebind.weaken (env:=env') (x:=n)) C
      have hreb_m : C.denot env' m =
        (C.rename Rename.succ).denot (env'.extend (TypeInfo.var n)) m := by
        rw [hreb]
        rfl
      rw [<-hreb_m]
      exact hih
    case tvar =>
      rename_i Γ' x' T' Sb
      cases env; rename_i info' env'
      cases info'; rename_i d
      simp [EnvTyping] at hts
      obtain ⟨_, _, henv'⟩ := hts
      have hih := ih henv'
      simp [TypeEnv.lookup_var, TypeEnv.lookup]
      -- Use rebinding with tweaken for type variable extension
      -- hih : reachability_of_loc m.heap (env'.lookup_var x') ⊆
      --       T'.captureSet.denot env' m
      -- Need: reachability_of_loc m.heap (env'.lookup_var x') ⊆
      --       (T'.rename Rename.succ).captureSet.denot (env'.extend_tvar d) m
      -- First, show that (T'.rename f).captureSet = T'.captureSet.rename f
      cases T' with | capt C S =>
      simp [Ty.captureSet, Ty.rename]
      simp [Ty.captureSet] at hih
      have hreb := rebind_captureset_denot
        (Rebind.tweaken (env:=env') (d:=d)) C
      have hreb_m : C.denot env' m =
        (C.rename Rename.succ).denot (env'.extend (TypeInfo.tvar d)) m := by
        rw [hreb]
        rfl
      rw [<-hreb_m]
      exact hih
    case cvar =>
      rename_i Γ' x' T' Bb
      cases env; rename_i info' env'
      cases info'; rename_i cs
      simp [EnvTyping] at hts
      obtain ⟨_, _, _, henv'⟩ := hts
      have hih := ih henv'
      simp [TypeEnv.lookup_var, TypeEnv.lookup]
      -- Use rebinding with cweaken for capture variable extension
      -- hih : reachability_of_loc m.heap (env'.lookup_var x') ⊆
      --       T'.captureSet.denot env' m
      -- Need: reachability_of_loc m.heap (env'.lookup_var x') ⊆
      --       (T'.rename Rename.succ).captureSet.denot (env'.extend_cvar cs) m
      -- First, show that (T'.rename f).captureSet = T'.captureSet.rename f
      cases T' with | capt C S =>
      simp [Ty.captureSet, Ty.rename]
      simp [Ty.captureSet] at hih
      have hreb := rebind_captureset_denot
        (Rebind.cweaken (env:=env') (cs:=cs)) C
      have hreb_m : C.denot env' m =
        (C.rename Rename.succ).denot (env'.extend (TypeInfo.cvar cs)) m := by
        rw [hreb]
        rfl
      rw [<-hreb_m]
      exact hih

theorem shape_denot_with_var_reachability
  {C : CaptureSet s} {S : Ty .shape s}
  (hts : EnvTyping Γ env m)
  (hd : Ty.shape_val_denot env S (C.denot env m) m (.var (.free (env.lookup_var x)))) :
  Ty.shape_val_denot env S (reachability_of_loc m.heap (env.lookup_var x)) m
    (.var (.free (env.lookup_var x))) := by
  -- Direct application of the is_tight property of shape_val_denot
  exact shape_val_denot_is_tight (typed_env_is_tight hts) (C.denot env m) m (env.lookup_var x) hd

theorem sem_typ_var
  (hx : Γ.LookupVar x (.capt C S)) :
  (.var (.bound x) .top) # Γ ⊨ (.var (.bound x)) : (.typ (.capt (.var (.bound x) .top) S)) := by
  intro env store hts
  simp [Ty.exi_exp_denot, Ty.exi_val_denot, Ty.capt_val_denot]
  apply Eval.eval_var
  simp [Denot.as_mpost]
  -- From typed_env_lookup_var, we get that .var (.free n) satisfies .capt C S
  have h_lookup := typed_env_lookup_var hts hx
  simp [Ty.capt_val_denot] at h_lookup ⊢
  obtain ⟨hsimple, hwf, hwf_C, hshape⟩ := h_lookup
  constructor
  · -- Prove IsSimpleAns: variables are simple answers
    exact hsimple
  constructor
  · exact hwf
  constructor
  · -- (.var (.bound x)).subst env becomes (.var (.free n)) which is well-formed
    -- Need: CaptureSet.var (.free n) is well-formed, which requires heap lookup
    simp [CaptureSet.subst, Var.subst, Subst.from_TypeEnv]
    cases hwf with
    | wf_var hwf_var =>
      cases hwf_var with
      | wf_free hlookup =>
        exact CaptureSet.WfInHeap.wf_var_free hlookup
  · -- Use the key lemma: shape with C.denot implies shape with reachability_of_loc
    simp only [CaptureSet.denot, CaptureSet.subst, Var.subst, Subst.from_TypeEnv,
      CaptureSet.ground_denot]
    -- Get the cell existence from hwf to show reachability_of_loc is well-formed
    cases hwf with
    | wf_var hwf_var =>
      cases hwf_var with
      | wf_free hlookup =>
        -- reachability_of_loc is well-formed in the heap
        have hwf_reach : (reachability_of_loc store.heap (env.lookup_var x)).WfInHeap store.heap :=
          reachability_of_loc_locations_exist store.wf hlookup
        -- Projecting with .top is identity for well-formed capability sets
        -- The goal has the unfolded form of CapKind.top, convert it first
        change Ty.shape_val_denot env S
          ((reachability_of_loc store.heap (env.lookup_var x)).proj store.heap .top)
          store (Exp.var (Var.free (env.lookup_var x)))
        rw [CapabilitySet.proj_top hwf_reach]
        exact shape_denot_with_var_reachability hts hshape

theorem expand_captures_eq_ground_denot (cs : CaptureSet {}) (m : Memory) :
  expand_captures m.heap cs = cs.ground_denot m := by
  induction cs with
  | empty => rfl
  | var v =>
    cases v with
    | free x => rfl
    | bound bv => cases bv
  | cvar cv => cases cv
  | union cs1 cs2 ih1 ih2 =>
    simp [expand_captures, CaptureSet.ground_denot, ih1, ih2]

theorem sem_typ_abs {T2 : Ty TySort.exi (s,x)} {Cf : CaptureSet s}
  (hclosed_abs : (Exp.abs Cf T1 e).IsClosed)
  (ht : (Cf.rename Rename.succ ∪ .var (.bound .here) .top) # Γ,x:T1 ⊨ e : T2) :
  ∅ # Γ ⊨ Exp.abs Cf T1 e : .typ (Ty.capt Cf (T1.arrow T2)) := by
  intro env store hts
  simp [Ty.exi_exp_denot, Ty.exi_val_denot, Ty.capt_val_denot, Ty.shape_val_denot]
  apply Eval.eval_val
  · simp [Exp.subst]; constructor
  · simp [Denot.as_mpost]
    constructor
    · -- Prove IsSimpleAns: abs is a simple value
      simp [Exp.subst]
      apply Exp.IsSimpleAns.is_simple_val
      apply Exp.IsSimpleVal.abs
    constructor
    · -- Prove well-formedness: closed expressions remain well-formed after substitution
      -- Strategy: (1) closed => wf, (2) typed env => wf subst, (3) wf subst preserves wf
      apply Exp.wf_subst
      · -- Closedness implies well-formedness in any heap
        apply Exp.wf_of_closed hclosed_abs
      · -- The substitution from typed environment is well-formed
        apply from_TypeEnv_wf_in_heap hts
    · -- Provide the arrow denotation structure
      constructor
      · -- Prove WfInHeap for the capture set
        apply CaptureSet.wf_subst
        · apply CaptureSet.wf_of_closed
          cases hclosed_abs
          assumption
        · apply from_TypeEnv_wf_in_heap hts
      · -- Provide the shape_val_denot structure
        constructor
        · -- Prove e.WfInHeap m.heap
          apply Exp.wf_subst
          · apply Exp.wf_of_closed hclosed_abs
          · apply from_TypeEnv_wf_in_heap hts
        · -- Provide existential witnesses: cs, T0, t0
          use (Cf.subst (Subst.from_TypeEnv env)), (T1.subst (Subst.from_TypeEnv env)),
            (e.subst (Subst.from_TypeEnv env).lift)
          constructor
          · -- Show that resolve gives back the abstraction
            simp [resolve, Exp.subst]
          · constructor
            · -- Prove cs.WfInHeap m.heap
              apply CaptureSet.wf_subst
              · apply CaptureSet.wf_of_closed
                cases hclosed_abs
                assumption
              · apply from_TypeEnv_wf_in_heap hts
            · constructor
              · -- Prove expand_captures ... ⊆ ...
                -- By expand_captures_eq_ground_denot and denot definition
                rw [expand_captures_eq_ground_denot]
                simp [CaptureSet.denot]
                apply CapabilitySet.Subset.refl
              · -- Show the function property
                intro arg H' hsubsume harg
                rw [Exp.from_TypeEnv_weaken_open]
                -- Apply the hypothesis
                have henv :
                  EnvTyping (Γ,x:T1) (env.extend_var arg) H' := by
                  constructor
                  · exact harg
                  · apply env_typing_monotonic hts hsubsume
                have this := ht (env.extend_var arg) H' henv
                simp [Ty.exi_exp_denot] at this
                -- Show capability sets match
                have hcap_rename :
                  (Cf.rename Rename.succ).denot (env.extend_var arg)
                  = Cf.denot env := by
                  have := rebind_captureset_denot (Rebind.weaken (env:=env) (x:=arg)) Cf
                  exact this.symm
                -- Variable .here denotes to the reachability we stored
                have hcap_var :
                  (CaptureSet.var (.bound .here) .top).denot (env.extend_var arg) H'
                  = reachability_of_loc H'.heap arg := by
                  simp [CaptureSet.denot, CaptureSet.ground_denot, CaptureSet.subst,
                        Subst.from_TypeEnv, Var.subst, TypeEnv.lookup_var]
                  -- Need to show (reachability_of_loc H'.heap arg).proj H'.heap .top = reachability_of_loc H'.heap arg
                  -- Get cell existence from harg (the argument is well-typed, so it exists in the heap)
                  -- First, match on T1 to unfold Ty.capt_val_denot
                  cases T1 with
                  | capt C S =>
                    simp only [Ty.capt_val_denot] at harg
                    have ⟨_, hwf_arg, _, _⟩ := harg
                    cases hwf_arg with
                    | wf_var hwf_var =>
                      cases hwf_var with
                      | wf_free hlookup =>
                        have hwf_reach : (reachability_of_loc H'.heap arg).WfInHeap H'.heap :=
                          reachability_of_loc_locations_exist H'.wf hlookup
                        exact CapabilitySet.proj_top hwf_reach
                -- Use monotonicity to relate capture set denotations at different memories
                have hCf_mono : Cf.denot env store = Cf.denot env H' := by
                  -- Extract closedness of Cf from hclosed_abs
                  have hCf_closed : Cf.IsClosed := by
                    cases hclosed_abs
                    assumption
                  -- Closed capture sets are well-formed in any heap
                  have hwf_Cf : (Cf.subst (Subst.from_TypeEnv env)).WfInHeap store.heap := by
                    apply CaptureSet.wf_subst
                    · apply CaptureSet.wf_of_closed hCf_closed
                    · apply from_TypeEnv_wf_in_heap hts
                  exact capture_set_denot_is_monotonic hwf_Cf hsubsume
                -- Show the authority matches by rewriting with equalities
                have hauthority :
                  (Cf.rename Rename.succ ∪ .var (.bound .here) .top).denot
                    (env.extend_var arg) H' =
                  (expand_captures store.heap
                    (Cf.subst (Subst.from_TypeEnv env))).union
                    (reachability_of_loc H'.heap arg) := by
                  calc (Cf.rename Rename.succ ∪ .var (.bound .here) .top).denot
                        (env.extend_var arg) H'
                    _ = (Cf.rename Rename.succ).denot (env.extend_var arg) H' ∪
                        (CaptureSet.var (.bound .here) .top).denot
                          (env.extend_var arg) H' := by
                      simp [CaptureSet.denot, CaptureSet.ground_denot,
                            CaptureSet.subst]
                    _ = Cf.denot env H' ∪ reachability_of_loc H'.heap arg := by
                      rw [congrFun hcap_rename H', hcap_var]
                    _ = Cf.denot env store ∪
                        reachability_of_loc H'.heap arg := by
                      rw [← hCf_mono]
                    _ = (Cf.subst (Subst.from_TypeEnv env)).ground_denot store ∪
                        reachability_of_loc H'.heap arg := by
                      simp [CaptureSet.denot]
                    _ = expand_captures store.heap
                          (Cf.subst (Subst.from_TypeEnv env)) ∪
                        reachability_of_loc H'.heap arg := by
                      rw [← expand_captures_eq_ground_denot]
                    _ = (expand_captures store.heap
                          (Cf.subst (Subst.from_TypeEnv env))).union
                        (reachability_of_loc H'.heap arg) := by
                      rfl
                rw [← hauthority]
                exact this

theorem sem_typ_tabs {T : Ty TySort.exi (s,X)} {Cf : CaptureSet s}
  (hclosed_tabs : (Exp.tabs Cf S e).IsClosed)
  (ht : Cf.rename Rename.succ # (Γ,X<:S) ⊨ e : T) :
  ∅ # Γ ⊨ Exp.tabs Cf S e : .typ (Ty.capt Cf (S.poly T)) := by
  intro env store hts
  simp [Ty.exi_exp_denot, Ty.exi_val_denot, Ty.capt_val_denot, Ty.shape_val_denot]
  apply Eval.eval_val
  · simp [Exp.subst]; constructor
  · simp [Denot.as_mpost]
    constructor
    · -- Prove IsSimpleAns: tabs is a simple value
      simp [Exp.subst]
      apply Exp.IsSimpleAns.is_simple_val
      apply Exp.IsSimpleVal.tabs
    constructor
    · -- Prove well-formedness: closed expressions remain well-formed after substitution
      -- Strategy: (1) closed => wf, (2) typed env => wf subst, (3) wf subst preserves wf
      apply Exp.wf_subst
      · -- Closedness implies well-formedness in any heap
        apply Exp.wf_of_closed hclosed_tabs
      · -- The substitution from typed environment is well-formed
        apply from_TypeEnv_wf_in_heap hts
    · -- Need to provide cs, S0 and t0 for the poly denotation
      constructor
      · -- Prove WfInHeap for the capture set
        apply CaptureSet.wf_subst
        · apply CaptureSet.wf_of_closed
          cases hclosed_tabs
          assumption
        · apply from_TypeEnv_wf_in_heap hts
      · -- Provide the shape_val_denot structure
        constructor
        · -- Prove e.WfInHeap m.heap
          apply Exp.wf_subst
          · apply Exp.wf_of_closed hclosed_tabs
          · apply from_TypeEnv_wf_in_heap hts
        · -- Provide existential witnesses: cs, S0, t0
          use (Cf.subst (Subst.from_TypeEnv env)), (S.subst (Subst.from_TypeEnv env)),
            (e.subst (Subst.from_TypeEnv env).lift)
          constructor
          · -- Show that resolve gives back the type abstraction
            simp [resolve, Exp.subst]
          · constructor
            · -- Prove cs.WfInHeap store.heap
              apply CaptureSet.wf_subst
              · apply CaptureSet.wf_of_closed
                cases hclosed_tabs
                assumption
              · apply from_TypeEnv_wf_in_heap hts
            · constructor
              · -- Prove expand_captures ... ⊆ ...
                rw [expand_captures_eq_ground_denot]
                simp [CaptureSet.denot]
                apply CapabilitySet.Subset.refl
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
                -- Use monotonicity to relate capture set denotations at different memories
                have hCf_mono : Cf.denot env store = Cf.denot env H' := by
                  -- Extract closedness of Cf from hclosed_tabs
                  have hCf_closed : Cf.IsClosed := by
                    cases hclosed_tabs
                    assumption
                  -- Closed capture sets are well-formed in any heap
                  have hwf_Cf : (Cf.subst (Subst.from_TypeEnv env)).WfInHeap store.heap := by
                    apply CaptureSet.wf_subst
                    · apply CaptureSet.wf_of_closed hCf_closed
                    · apply from_TypeEnv_wf_in_heap hts
                  exact capture_set_denot_is_monotonic hwf_Cf hsubsume
                -- Show the authority matches
                have hauthority :
                  (Cf.rename Rename.succ).denot (env.extend_tvar denot) H' =
                  expand_captures store.heap (Cf.subst (Subst.from_TypeEnv env)) := by
                  calc (Cf.rename Rename.succ).denot (env.extend_tvar denot) H'
                    _ = Cf.denot env H' := by rw [congrFun hcap_rename H']
                    _ = Cf.denot env store := by rw [← hCf_mono]
                    _ = (Cf.subst (Subst.from_TypeEnv env)).ground_denot store := by
                      simp [CaptureSet.denot]
                    _ = expand_captures store.heap (Cf.subst (Subst.from_TypeEnv env)) := by
                      rw [← expand_captures_eq_ground_denot]
                rw [← hauthority]
                exact this

theorem sem_typ_cabs {T : Ty TySort.exi (s,C)} {Cf : CaptureSet s}
  (hclosed_cabs : (Exp.cabs Cf cb e).IsClosed)
  (ht : Cf.rename Rename.succ # Γ,C<:cb ⊨ e : T) :
  ∅ # Γ ⊨ Exp.cabs Cf cb e : .typ (Ty.capt Cf (Ty.cpoly cb T)) := by
  intro env store hts
  simp [Ty.exi_exp_denot, Ty.exi_val_denot, Ty.capt_val_denot, Ty.shape_val_denot]
  apply Eval.eval_val
  · simp [Exp.subst]; constructor
  · simp [Denot.as_mpost]
    constructor
    · -- Prove IsSimpleAns: cabs is a simple value
      simp [Exp.subst]
      apply Exp.IsSimpleAns.is_simple_val
      apply Exp.IsSimpleVal.cabs
    constructor
    · -- Prove well-formedness: closed expressions remain well-formed after substitution
      -- Strategy: (1) closed => wf, (2) typed env => wf subst, (3) wf subst preserves wf
      apply Exp.wf_subst
      · -- Closedness implies well-formedness in any heap
        apply Exp.wf_of_closed hclosed_cabs
      · -- The substitution from typed environment is well-formed
        apply from_TypeEnv_wf_in_heap hts
    · -- Need to provide cs, B0 and t0 for the cpoly denotation
      constructor
      · -- Prove WfInHeap for the capture set
        apply CaptureSet.wf_subst
        · apply CaptureSet.wf_of_closed
          cases hclosed_cabs
          assumption
        · apply from_TypeEnv_wf_in_heap hts
      · -- Provide the shape_val_denot structure
        constructor
        · -- Prove e.WfInHeap m.heap
          apply Exp.wf_subst
          · apply Exp.wf_of_closed hclosed_cabs
          · apply from_TypeEnv_wf_in_heap hts
        · -- Provide existential witnesses: cs, B0, t0
          use (Cf.subst (Subst.from_TypeEnv env)), (cb.subst (Subst.from_TypeEnv env)),
            (e.subst (Subst.from_TypeEnv env).lift)
          constructor
          · -- Show that resolve gives back the capture abstraction
            simp [resolve, Exp.subst]
          · constructor
            · -- Prove cs.WfInHeap store.heap
              apply CaptureSet.wf_subst
              · apply CaptureSet.wf_of_closed
                cases hclosed_cabs
                assumption
              · apply from_TypeEnv_wf_in_heap hts
            · constructor
              · -- Prove expand_captures ... ⊆ ...
                rw [expand_captures_eq_ground_denot]
                simp [CaptureSet.denot]
                apply CapabilitySet.Subset.refl
              · -- Show the capture polymorphic function property
                intro H' CS hwf hsubsume hsub_bound
                -- Apply the hypothesis
                have henv : EnvTyping (Γ,C<:cb) (env.extend_cvar CS) H' := by
                  constructor
                  · exact hwf
                  · constructor
                    · -- Prove (cb.subst (Subst.from_TypeEnv env)).WfInHeap H'.heap
                      apply CaptureBound.wf_subst
                      · apply CaptureBound.wf_of_closed
                        cases hclosed_cabs; assumption
                      · -- Lift Subst.WfInHeap from store to H' using monotonicity
                        have hwf_subst_store := from_TypeEnv_wf_in_heap hts
                        constructor
                        · intro x; exact Var.wf_monotonic hsubsume (hwf_subst_store.wf_var x)
                        · intro X; exact Ty.wf_monotonic hsubsume (hwf_subst_store.wf_tvar X)
                        · intro C K
                          exact CaptureSet.wf_monotonic hsubsume (hwf_subst_store.wf_cvar C K)
                    · constructor
                      · -- Rewrite hsub_bound to match expected type
                        -- Need to show: CS.ground_denot H' ⊆ ⟦cb⟧_[env] H'
                        -- Have: CaptureSet.denot TypeEnv.empty CS H' ⊆ CaptureBound.denot env cb H'
                        -- CaptureSet.denot TypeEnv.empty CS = CS.ground_denot by definition
                        -- For ground CS, subst with TypeEnv.empty is identity
                        have heq : CS.ground_denot = CaptureSet.denot TypeEnv.empty CS := by
                          funext m
                          simp [CaptureSet.denot, Subst.from_TypeEnv_empty, CaptureSet.subst_id]
                        rw [heq]
                        exact hsub_bound
                      · apply env_typing_monotonic hts hsubsume
                have this := ht (env.extend_cvar CS) H' henv
                simp [Ty.exi_exp_denot] at this
                -- Show capability sets match
                have hcap_rename :
                  (Cf.rename Rename.succ).denot (env.extend_cvar CS) = Cf.denot env := by
                  have := rebind_captureset_denot (Rebind.cweaken (env:=env) (cs:=CS)) Cf
                  exact this.symm
                -- Use monotonicity
                have hCf_mono : Cf.denot env store = Cf.denot env H' := by
                  have hCf_closed : Cf.IsClosed := by
                    cases hclosed_cabs
                    assumption
                  have hwf_Cf : (Cf.subst (Subst.from_TypeEnv env)).WfInHeap store.heap := by
                    apply CaptureSet.wf_subst
                    · apply CaptureSet.wf_of_closed hCf_closed
                    · apply from_TypeEnv_wf_in_heap hts
                  exact capture_set_denot_is_monotonic hwf_Cf hsubsume
                -- Show the authority matches
                have hauthority :
                  (Cf.rename Rename.succ).denot (env.extend_cvar CS) H' =
                  expand_captures store.heap (Cf.subst (Subst.from_TypeEnv env)) := by
                  calc (Cf.rename Rename.succ).denot (env.extend_cvar CS) H'
                    _ = Cf.denot env H' := by rw [congrFun hcap_rename H']
                    _ = Cf.denot env store := by rw [← hCf_mono]
                    _ = (Cf.subst (Subst.from_TypeEnv env)).ground_denot store := by
                      simp [CaptureSet.denot]
                    _ = expand_captures store.heap (Cf.subst (Subst.from_TypeEnv env)) := by
                      rw [← expand_captures_eq_ground_denot]
                rw [Exp.from_TypeEnv_weaken_open_cvar (cs:=CS)]
                rw [← hauthority]
                exact this

theorem sem_typ_pack
  {T : Ty .capt (s,C)} {cs : CaptureSet s} {x : Var .var s} {Γ : Ctx s}
  (hclosed_e : (Exp.pack cs x).IsClosed)
  (ht : CaptureSet.var x .top # Γ ⊨ Exp.var x : (T.subst (Subst.openCVar cs)).typ) :
  CaptureSet.var x .top # Γ ⊨ Exp.pack cs x : T.exi := by
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
        -- hQ : (capt_val_denot env (T.subst (Subst.openCVar cs))).as_mpost ...
        simp [Denot.as_mpost] at hQ
        -- hQ : capt_val_denot env (T.subst (Subst.openCVar cs)) store (var (x.subst ...))
        -- Now use retype lemma to convert from T.subst (Subst.openCVar cs) at env
        -- to T at env.extend_cvar (cs.subst ...)
        have hretype := @retype_capt_val_denot (s,C) s
          (env.extend_cvar (cs.subst (Subst.from_TypeEnv env)))
          (Subst.openCVar cs) env
          (@Retype.open_carg s env cs) T
        exact (hretype store (Exp.var (x.subst (Subst.from_TypeEnv env)))).mpr hQ
      case eval_val =>
        -- Variables can only use eval_var, not eval_val
        contradiction

theorem abs_val_denot_inv {A : CapabilitySet}
  (hv : Ty.shape_val_denot env (.arrow T1 T2) A store (.var x)) :
  ∃ fx, x = .free fx
    ∧ ∃ cs T0 e0 hval R,
      store.heap fx = some (Cell.val ⟨Exp.abs cs T0 e0, hval, R⟩)
    ∧ expand_captures store.heap cs ⊆ A
    ∧ (∀ (arg : Nat) (m' : Memory),
      m'.subsumes store ->
      Ty.capt_val_denot env T1 m' (.var (.free arg)) ->
      Ty.exi_exp_denot
        (env.extend_var arg)
        T2 (expand_captures store.heap cs ∪ (reachability_of_loc m'.heap arg)) m'
        (e0.subst (Subst.openVar (.free arg)))) := by
  cases x with
  | bound bx => cases bx
  | free fx =>
    simp [Ty.shape_val_denot, resolve] at hv
    obtain ⟨hwf_e, cs, T0, e0, hresolve, hwf_cs, hR0_sub, hfun⟩ := hv
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
        use fx, rfl, cs, T0, e0, isVal, reachability, hres, hR0_sub, hfun
      | capability =>
        simp at hresolve
      | masked =>
        simp at hresolve

theorem tabs_val_denot_inv {A : CapabilitySet}
  (hv : Ty.shape_val_denot env (.poly S T) A store (.var x)) :
  ∃ fx, x = .free fx
    ∧ ∃ cs S0 e0 hval R,
      store.heap fx = some (Cell.val ⟨Exp.tabs cs S0 e0, hval, R⟩)
    ∧ expand_captures store.heap cs ⊆ A
    ∧ (∀ (m' : Memory) (denot : PreDenot),
      m'.subsumes store ->
      denot.is_proper ->
      denot.ImplyAfter m' (Ty.shape_val_denot env S) ->
      Ty.exi_exp_denot
        (env.extend_tvar denot)
        T (expand_captures store.heap cs) m'
        (e0.subst (Subst.openTVar .top))) := by
  cases x with
  | bound bx => cases bx
  | free fx =>
    simp [Ty.shape_val_denot, resolve] at hv
    obtain ⟨hwf_e, cs, S0, e0, hresolve, hwf_cs, hR0_sub, hfun⟩ := hv
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
        use fx, rfl, cs, S0, e0, isVal, reachability, hres, hR0_sub, hfun
      | capability =>
        simp at hresolve
      | masked =>
        simp at hresolve

theorem cabs_val_denot_inv {A : CapabilitySet}
  (hv : Ty.shape_val_denot env (.cpoly B T) A store (.var x)) :
  ∃ fx, x = .free fx
    ∧ ∃ cs B0 e0 hval R,
      store.heap fx = some (Cell.val ⟨Exp.cabs cs B0 e0, hval, R⟩)
    ∧ expand_captures store.heap cs ⊆ A
    ∧ (∀ (m' : Memory) (CS : CaptureSet {}),
      CS.WfInHeap m'.heap ->
      m'.subsumes store ->
      ((CS.denot TypeEnv.empty m').BoundedBy (B.denot env m')) ->
      Ty.exi_exp_denot
        (env.extend_cvar CS)
        T (expand_captures store.heap cs) m'
        (e0.subst (Subst.openCVar CS))) := by
  cases x with
  | bound bx => cases bx
  | free fx =>
    simp [Ty.shape_val_denot, resolve] at hv
    obtain ⟨hwf_e, cs, B0, e0, hresolve, hwf_cs, hR0_sub, hfun⟩ := hv
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
        use fx, rfl, cs, B0, e0, isVal, reachability, hres, hR0_sub, hfun
      | capability =>
        simp at hresolve
      | masked =>
        simp at hresolve

theorem cap_val_denot_inv {A : CapabilitySet}
  (hv : Ty.shape_val_denot env .cap A store (.var x)) :
  ∃ fx, x = .free fx ∧ store.heap fx = some (.capability .basic) ∧ fx ∈ A := by
  cases x with
  | bound bx => cases bx
  | free fx =>
    simp only [Ty.shape_val_denot, Memory.lookup] at hv
    obtain ⟨hwf_e, label, heq, hlookup, hmem⟩ := hv
    have : fx = label := by
      injection heq with h1
      rename_i heq_var
      injection heq_var
    subst this
    use fx, rfl, hlookup, hmem

theorem unit_val_denot_inv
  (hv : Ty.shape_val_denot env .unit A store (.var x)) :
  ∃ fx, x = .free fx
    ∧ ∃ hval R,
      store.heap fx = some (Cell.val ⟨Exp.unit, hval, R⟩) := by
  cases x with
  | bound bx => cases bx
  | free fx =>
    simp [Ty.shape_val_denot, resolve] at hv
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

theorem cell_val_denot_inv {A : CapabilitySet}
  (hv : Ty.shape_val_denot env .cell A store (.var x)) :
  ∃ fx b0, x = .free fx ∧ store.heap fx = some (.capability (.mcell b0)) ∧ fx ∈ A := by
  cases x with
  | bound bx => cases bx
  | free fx =>
    simp only [Ty.shape_val_denot, Memory.lookup] at hv
    obtain ⟨label, b0, heq, hlookup, hmem⟩ := hv
    have : fx = label := by
      injection heq with h1
      rename_i heq_var
      injection heq_var
    subst this
    use fx, b0, rfl, hlookup, hmem

theorem bool_val_denot_inv
  (hv : Ty.shape_val_denot env .bool A store (.var x)) :
  ∃ fx, ∃ b : Bool, ∃ hval R,
    x = .free fx ∧
    store.heap fx = some (Cell.val ⟨(if b then Exp.btrue else Exp.bfalse), hval, R⟩) := by
  cases x with
  | bound bx => cases bx
  | free fx =>
    simp [Ty.shape_val_denot, resolve] at hv
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
  use env.lookup_var x
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
    simp only [CaptureSet.subst, CaptureSet.denot, Subst.from_TypeEnv]
    rw [CaptureSet.ground_subst_invariant]
  | var_bound =>
    simp only [CaptureSet.subst, CaptureSet.denot, Var.subst, Subst.from_TypeEnv]

theorem sem_typ_tapp
  {x : BVar s .var} -- x must be a BOUND variable (from typing rule)
  {S : Ty .shape s} -- Type argument
  {T : Ty .exi (s,X)} -- Result type (depends on type variable X)
  (hx : (.var (.bound x) .top) # Γ ⊨ .var (.bound x) :
    .typ (.capt (.var (.bound x) .top) (.poly S T))) :
  (.var (.bound x) .top) # Γ ⊨ Exp.tapp (.bound x) S :
    T.subst (Subst.openTVar S) := by
  intro env store hts

  -- Extract function denotation
  have h1 := hx env store hts
  simp [Exp.subst, Subst.from_TypeEnv, Var.subst] at h1
  have h1' := var_exp_denot_inv h1
  simp only [Ty.exi_val_denot, Ty.capt_val_denot] at h1'

  -- Extract the poly structure (now at h1'.2.2.2 due to extra IsSimpleAns conjunct)
  have ⟨fx, hfx, cs, S0, e0, hval, R, hlk, hR0_sub, hfun⟩ := tabs_val_denot_inv h1'.2.2.2

  -- Determine concrete location
  have : fx = env.lookup_var x := by cases hfx; rfl
  subst this

  -- Simplify goal
  simp [Exp.subst, Subst.from_TypeEnv, Var.subst, CaptureSet.denot, Ty.exi_exp_denot]

  -- Apply the polymorphic function to the type argument S
  -- We need to provide: denot.is_proper and denot.ImplyAfter
  have happ := hfun store (Ty.shape_val_denot env S) (Memory.subsumes_refl store)
    (shape_val_denot_is_proper hts)  -- Shape type denotations are proper
    (by intro C m' hsub; exact Denot.imply_implyat (Denot.imply_refl _))  -- ImplyAfter is reflexive

  -- The opening lemma relates extended environment to substituted type
  have heqv := open_targ_exi_exp_denot (env:=env) (S:=S) (T:=T)

  -- Convert the denotation using the equivalence
  have happ' :=
    (heqv (expand_captures store.heap cs)
      store (e0.subst (Subst.openTVar .top))).1 happ

  simp [Ty.exi_exp_denot] at happ'

  -- Widen the authority using monotonicity
  have happ'' := eval_capability_set_monotonic happ' hR0_sub

  apply Eval.eval_tapply hlk happ''

theorem sem_typ_capp
  {x : BVar s .var}
  {T : Ty .exi (s,C)}
  {D : CaptureSet s}
  (hD_closed : D.IsClosed)
  (hx : (.var (.bound x) .top) # Γ ⊨ .var (.bound x) :
    .typ (.capt (.var (.bound x) .top) (.cpoly (.bound D) T))) :
  (.var (.bound x) .top) # Γ ⊨ Exp.capp (.bound x) D : T.subst (Subst.openCVar D) := by
  intro env store hts

  -- Extract function denotation
  have h1 := hx env store hts
  simp [Exp.subst, Subst.from_TypeEnv, Var.subst] at h1
  have h1' := var_exp_denot_inv h1
  simp only [Ty.exi_val_denot, Ty.capt_val_denot] at h1'

  -- Extract the cpoly structure (now at h1'.2.2.2 due to extra IsSimpleAns conjunct)
  have ⟨fx, hfx, cs, B0, e0, hval, R, hlk, hR0_sub, hfun⟩ := cabs_val_denot_inv h1'.2.2.2

  -- Determine concrete location
  have : fx = env.lookup_var x := by cases hfx; rfl
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
    (by -- Prove that (D'.denot TypeEnv.empty store).BoundedBy
        --   ((.bound D).denot env store)
      rw [hD'_denot]
      -- Since cb = .bound D, we have:
      --   (.bound D).denot env store = CapabilityBound.set (D.denot env store)
      -- So we need: (D.denot env store).BoundedBy
      --   (CapabilityBound.set (D.denot env store))
      simp [CaptureBound.denot]
      exact CapabilitySet.BoundedBy.set CapabilitySet.Subset.refl)

  -- Now apply the opening lemma
  have heqv := open_carg_exi_exp_denot (env:=env) (C:=D) (T:=T)

  -- Convert using the equivalence
  have happ2 :=
    (heqv (expand_captures store.heap cs)
      store (e0.subst (Subst.openCVar D'))).1 happ

  simp [Ty.exi_exp_denot] at happ2

  -- Widen the authority using monotonicity
  have happ3 := eval_capability_set_monotonic happ2 hR0_sub

  apply Eval.eval_capply hlk happ3

theorem sem_typ_app
  {x y : BVar s .var} -- x and y must be BOUND variables (from typing rule)
  (hx : (.var (.bound x) .top) # Γ ⊨ .var (.bound x) :
    .typ (.capt (.var (.bound x) .top) (.arrow T1 T2)))
  (hy : (.var (.bound y) .top) # Γ ⊨ .var (.bound y) : .typ T1) :
  ((.var (.bound x) .top) ∪ (.var (.bound y) .top)) # Γ ⊨
    Exp.app (.bound x) (.bound y) : T2.subst (Subst.openVar (.bound y)) := by
  intro env store hts

  -- Extract function denotation
  have h1 := hx env store hts
  simp [Exp.subst, Subst.from_TypeEnv, Var.subst] at h1
  have h1' := var_exp_denot_inv h1
  simp only [Ty.exi_val_denot, Ty.capt_val_denot] at h1'

  -- Extract the arrow structure (now at h1'.2.2.2 due to extra IsSimpleAns conjunct)
  have ⟨fx, hfx, cs, T0, e0, hval, R, hlk, hR0_sub, hfun⟩ := abs_val_denot_inv h1'.2.2.2

  -- Extract argument denotation
  have h2 := hy env store hts
  simp [Exp.subst, Subst.from_TypeEnv, Var.subst] at h2
  have h2' := var_exp_denot_inv h2
  simp only [Ty.exi_val_denot] at h2'

  -- Determine concrete locations
  have : fx = env.lookup_var x := by cases hfx; rfl
  subst this
  let fy := env.lookup_var y

  -- Simplify goal
  simp [Exp.subst, Subst.from_TypeEnv, Var.subst, CaptureSet.denot, Ty.exi_exp_denot]

  -- Apply function to argument
  have happ := hfun fy store (Memory.subsumes_refl store) h2'

  -- The opening lemma relates extended environment to substituted type
  have heqv := open_arg_exi_exp_denot (env:=env) (y:=.bound y) (T:=T2)

  -- Note that interp_var env (Var.bound y) = env.lookup_var y = fy
  have hinterp : interp_var env (Var.bound y) = fy := rfl

  -- Convert the denotation using the equivalence
  rw [hinterp] at heqv
  have happ' :=
    (heqv (expand_captures store.heap cs ∪
           reachability_of_loc store.heap fy)
      store (e0.subst (Subst.openVar (Var.free fy)))).1 happ

  simp [Ty.exi_exp_denot] at happ'

  -- Widen the authority using union monotonicity
  have hunion_mono : expand_captures store.heap cs ∪ reachability_of_loc store.heap fy ⊆
                     CaptureSet.denot env (CaptureSet.var (Var.bound x) .top) store ∪
                     reachability_of_loc store.heap fy := by
    apply CapabilitySet.Subset.union_left
    · exact CapabilitySet.Subset.trans hR0_sub CapabilitySet.Subset.union_right_left
    · exact CapabilitySet.Subset.union_right_right

  have happ'' := eval_capability_set_monotonic happ' hunion_mono

  -- The goal has CaptureSet.denot with .proj .top, need to show equality
  -- Get well-formedness proofs for the reachability sets
  -- First case on T1 to unfold Ty.capt_val_denot for h2'
  cases T1 with
  | capt C S =>
    simp only [Ty.capt_val_denot] at h2'
    have ⟨_, hwf_x, _, _⟩ := h1'
    have ⟨_, hwf_y, _, _⟩ := h2'
    cases hwf_x with | wf_var hwf_x' => cases hwf_x' with | wf_free hlk_x =>
    cases hwf_y with | wf_var hwf_y' => cases hwf_y' with | wf_free hlk_y =>
    have hwf_reach_x := reachability_of_loc_locations_exist store.wf hlk_x
    have hwf_reach_y := reachability_of_loc_locations_exist store.wf hlk_y
    -- Unfold CaptureSet.denot in happ'' to get the proj form
    simp only [CaptureSet.denot, CaptureSet.ground_denot, CaptureSet.subst, Var.subst,
               Subst.from_TypeEnv] at happ''
    -- Now happ'' has: (reachability_of_loc ... x).proj ... .top ∪ reachability_of_loc ... y
    -- Add .proj .top to the y part using hwf_reach_y
    have heq_y : reachability_of_loc store.heap (env.lookup_var y) =
                 (reachability_of_loc store.heap (env.lookup_var y)).proj store.heap .top := by
      exact (CapabilitySet.proj_top hwf_reach_y).symm
    rw [heq_y] at happ''
    -- Convert the goal to use .top instead of the unfolded form
    change Eval ((reachability_of_loc store.heap (env.lookup_var x)).proj store.heap .top ∪
                 (reachability_of_loc store.heap (env.lookup_var y)).proj store.heap .top)
                store _ _
    exact Eval.eval_apply hlk happ''

theorem sem_typ_invoke
  {x y : BVar s .var} -- x and y must be BOUND variables (from typing rule)
  (hx : (.var (.bound x) .top) # Γ ⊨ .var (.bound x) : .typ (.capt (.var (.bound x) .top) .cap))
  (hy : (.var (.bound y) .top) # Γ ⊨ .var (.bound y) : .typ (.capt (.var (.bound y) .top) .unit)) :
  ((.var (.bound x) .top) ∪ (.var (.bound y) .top)) # Γ ⊨
    Exp.app (.bound x) (.bound y) : .typ (.capt {} .unit) := by
  intro env store hts

  -- Extract capability denotation from hx
  have h1 := hx env store hts
  simp [Exp.subst, Subst.from_TypeEnv, Var.subst] at h1
  have h1' := var_exp_denot_inv h1
  simp only [Ty.exi_val_denot, Ty.capt_val_denot] at h1'

  -- Extract the capability structure (now at h1'.2.2.2 due to extra IsSimpleAns conjunct)
  have ⟨fx, hfx, hlk_cap, hmem_cap⟩ := cap_val_denot_inv h1'.2.2.2

  -- Extract unit denotation from hy
  have h2 := hy env store hts
  simp [Exp.subst, Subst.from_TypeEnv, Var.subst] at h2
  have h2' := var_exp_denot_inv h2
  simp only [Ty.exi_val_denot, Ty.capt_val_denot] at h2'

  -- Extract the unit structure (now at h2'.2.2.2 due to extra IsSimpleAns conjunct)
  have ⟨fy, hfy, hval_unit, R, hlk_unit⟩ := unit_val_denot_inv h2'.2.2.2

  -- Determine concrete locations
  have : fx = env.lookup_var x := by cases hfx; rfl
  subst this
  have : fy = env.lookup_var y := by cases hfy; rfl
  subst this

  -- Simplify goal
  simp [Exp.subst, Subst.from_TypeEnv, Var.subst, Ty.exi_exp_denot, Ty.exi_val_denot,
        Ty.capt_val_denot, Ty.shape_val_denot, CaptureSet.denot]

  -- Show env.lookup_var x is in the union of capability sets
  have hmem : env.lookup_var x ∈
      CaptureSet.denot env (.var (.bound x) .top ∪ .var (.bound y) .top) store := by
    apply CapabilitySet.mem.left
    exact hmem_cap

  -- Apply eval_invoke
  apply Eval.eval_invoke hmem hlk_cap hlk_unit

  -- Show the postcondition holds for unit
  constructor
  · -- Prove IsSimpleAns for unit
    apply Exp.IsSimpleAns.is_simple_val
    apply Exp.IsSimpleVal.unit
  constructor
  · exact Exp.WfInHeap.wf_unit
  constructor
  · -- Empty capture set is always well-formed
    simp only [CaptureSet.subst]
    exact CaptureSet.WfInHeap.wf_empty
  · simp [resolve]

theorem sem_typ_unit :
  {} # Γ ⊨ Exp.unit : .typ (.capt {} .unit) := by
  intro env store hts
  simp [Ty.exi_exp_denot, Ty.exi_val_denot, Ty.capt_val_denot, Ty.shape_val_denot,
        Exp.subst, CaptureSet.denot]
  apply Eval.eval_val
  · exact Exp.IsVal.unit
  · constructor
    · -- Prove IsSimpleAns: unit is a simple value
      apply Exp.IsSimpleAns.is_simple_val
      apply Exp.IsSimpleVal.unit
    constructor
    · exact Exp.WfInHeap.wf_unit
    · constructor
      · apply CaptureSet.wf_subst
        · apply CaptureSet.wf_of_closed CaptureSet.IsClosed.empty
        · apply from_TypeEnv_wf_in_heap hts
      · simp [resolve]

theorem sem_typ_cond
  {C1 C2 C3 : CaptureSet s} {Γ : Ctx s}
  {x : Var .var s} {e2 e3 : Exp s} {T : Ty .exi s} {Cb : CaptureSet s}
  (hclosed_C1 : C1.IsClosed)
  (hclosed_C2 : C2.IsClosed)
  (hclosed_C3 : C3.IsClosed)
  (_hclosed_guard : x.IsClosed)
  (_hclosed_then : e2.IsClosed)
  (_hclosed_else : e3.IsClosed)
  (ht1 : C1 # Γ ⊨ (.var x) : .typ (.capt Cb .bool))
  (ht2 : C2 # Γ ⊨ e2 : T)
  (ht3 : C3 # Γ ⊨ e3 : T) :
  (C1 ∪ C2 ∪ C3) # Γ ⊨ (.cond x e2 e3) : T := by
  intro env store hts
  simp [Exp.subst, Ty.exi_exp_denot]
  -- Let Q1 be the guard postcondition
  set Q1 := (Ty.exi_val_denot env (.typ (.capt Cb .bool))).as_mpost
  -- Monotonicity of Q1
  have hpred : Q1.is_monotonic := Denot.as_mpost_is_monotonic
    (exi_val_denot_is_monotonic (typed_env_is_monotonic hts) (.typ (.capt Cb .bool)))
  -- Bool independence of Q1
  have hbool : Q1.is_bool_independent := Denot.as_mpost_is_bool_independent
    (exi_val_denot_is_bool_independent (typed_env_is_bool_independent hts) (.typ (.capt Cb .bool)))
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
    have hQ1' : Ty.capt_val_denot env (.capt Cb .bool) m1 v := by
      simpa [Q1, Denot.as_mpost, Ty.exi_val_denot] using hQ1
    have hshape : resolve m1.heap v = some .btrue ∨ resolve m1.heap v = some .bfalse := by
      have h := hQ1'
      simp [Ty.capt_val_denot, Ty.shape_val_denot] at h
      exact h.2.2.2
    exact hshape
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

theorem sem_typ_btrue :
  {} # Γ ⊨ Exp.btrue : .typ (.capt {} .bool) := by
  intro env store hts
  simp [Ty.exi_exp_denot, Ty.exi_val_denot, Ty.capt_val_denot, Ty.shape_val_denot,
        Exp.subst, CaptureSet.denot]
  apply Eval.eval_val
  · exact Exp.IsVal.btrue
  · constructor
    · apply Exp.IsSimpleAns.is_simple_val
      apply Exp.IsSimpleVal.btrue
    constructor
    · exact Exp.WfInHeap.wf_btrue
    · constructor
      · apply CaptureSet.wf_subst
        · apply CaptureSet.wf_of_closed CaptureSet.IsClosed.empty
        · apply from_TypeEnv_wf_in_heap hts
      · simp [resolve]

theorem sem_typ_bfalse :
  {} # Γ ⊨ Exp.bfalse : .typ (.capt {} .bool) := by
  intro env store hts
  simp [Ty.exi_exp_denot, Ty.exi_val_denot, Ty.capt_val_denot, Ty.shape_val_denot,
        Exp.subst, CaptureSet.denot]
  apply Eval.eval_val
  · exact Exp.IsVal.bfalse
  · constructor
    · apply Exp.IsSimpleAns.is_simple_val
      apply Exp.IsSimpleVal.bfalse
    constructor
    · exact Exp.WfInHeap.wf_bfalse
    · constructor
      · apply CaptureSet.wf_subst
        · apply CaptureSet.wf_of_closed CaptureSet.IsClosed.empty
        · apply from_TypeEnv_wf_in_heap hts
      · simp [resolve]

theorem sem_typ_read
  {x : BVar s .var} -- x must be a BOUND variable (from typing rule)
  (hx : (.var (.bound x) .top) # Γ ⊨ .var (.bound x) : .typ (.capt C .cell)) :
  (.var (.bound x) .top) # Γ ⊨ Exp.read (.bound x) : .typ (.capt {} .bool) := by
  intro env store hts

  -- Extract cell denotation from hx
  have h1 := hx env store hts
  simp [Exp.subst, Subst.from_TypeEnv, Var.subst] at h1
  have h1' := var_exp_denot_inv h1
  simp only [Ty.exi_val_denot, Ty.capt_val_denot] at h1'

  -- Extract the cell structure
  have ⟨fx, b0, hfx, hlk_cell, hmem_cell⟩ := cell_val_denot_inv h1'.2.2.2

  -- Determine concrete location
  have : fx = env.lookup_var x := by cases hfx; rfl
  subst this

  -- Simplify goal
  simp [Exp.subst, Subst.from_TypeEnv, Var.subst, Ty.exi_exp_denot, Ty.exi_val_denot,
        Ty.capt_val_denot, Ty.shape_val_denot, CaptureSet.denot]

  -- Apply eval_read with membership proof
  -- The membership proof: env.lookup_var x ∈ reachability_of_loc store.heap (env.lookup_var x)
  -- Since store contains a capability at that location, reachability is {env.lookup_var x}
  have hmem : env.lookup_var x ∈
    ((CaptureSet.var (Var.bound x) .top).subst (Subst.from_TypeEnv env)).ground_denot store := by
    simp [CaptureSet.subst, Var.subst, Subst.from_TypeEnv, CaptureSet.ground_denot,
          reachability_of_loc, hlk_cell]
    -- Need to show l ∈ (CapabilitySet.cap l).proj H .top
    -- First prove (cap l).WfInHeap H using hlk_cell
    have hwf_cap : (CapabilitySet.cap (env.lookup_var x)).WfInHeap store.heap := by
      intro l' hmem
      cases hmem
      exact ⟨.capability (.mcell b0), hlk_cell⟩
    -- Now use proj_top to show (cap l).proj H .top = cap l
    -- Use change to convert goal to explicit form, then simp with proj_top
    change CapabilitySet.mem (env.lookup_var x)
      ((CapabilitySet.cap (env.lookup_var x)).proj store.heap .top)
    simp only [CapabilitySet.proj_top hwf_cap]
    exact CapabilitySet.mem.here
  apply Eval.eval_read hmem hlk_cell

  -- Show the postcondition holds for the boolean result
  constructor
  · -- Prove IsSimpleAns for the boolean
    apply Exp.IsSimpleAns.is_simple_val
    cases b0
    · exact Exp.IsSimpleVal.bfalse
    · exact Exp.IsSimpleVal.btrue
  constructor
  · -- WfInHeap for the boolean
    cases b0
    · exact Exp.WfInHeap.wf_bfalse
    · exact Exp.WfInHeap.wf_btrue
  constructor
  · -- Empty capture set is always well-formed
    simp only [CaptureSet.subst]
    exact CaptureSet.WfInHeap.wf_empty
  · -- The result is btrue or bfalse
    cases b0 <;> simp [resolve]

theorem sem_typ_write
  {x y : BVar s .var} -- x and y must be BOUND variables (from typing rule)
  (hx : (.var (.bound x) .top) # Γ ⊨ .var (.bound x) : .typ (.capt Cx .cell))
  (hy : (.var (.bound y) .top) # Γ ⊨ .var (.bound y) : .typ (.capt {} .bool)) :
  ((.var (.bound x) .top) ∪ (.var (.bound y) .top)) # Γ ⊨
    Exp.write (.bound x) (.bound y) : .typ (.capt {} .unit) := by
  intro env store hts

  -- Extract cell denotation from hx
  have h1 := hx env store hts
  simp [Exp.subst, Subst.from_TypeEnv, Var.subst] at h1
  have h1' := var_exp_denot_inv h1
  simp only [Ty.exi_val_denot, Ty.capt_val_denot] at h1'

  -- Extract the cell structure
  have ⟨fx, b0, hfx, hlk_cell, hmem_cell⟩ := cell_val_denot_inv h1'.2.2.2

  -- Extract bool denotation from hy
  have h2 := hy env store hts
  simp [Exp.subst, Subst.from_TypeEnv, Var.subst] at h2
  have h2' := var_exp_denot_inv h2
  simp only [Ty.exi_val_denot, Ty.capt_val_denot] at h2'

  -- Extract the bool structure
  have ⟨fy, b, hval, R, hfy, hlk_bool⟩ := bool_val_denot_inv h2'.2.2.2

  -- Determine concrete locations
  have : fx = env.lookup_var x := by cases hfx; rfl
  subst this
  have : fy = env.lookup_var y := by cases hfy; rfl
  subst this

  -- Simplify goal
  simp [Exp.subst, Subst.from_TypeEnv, Var.subst, Ty.exi_exp_denot, Ty.exi_val_denot,
        Ty.capt_val_denot, Ty.shape_val_denot, CaptureSet.denot]

  -- Prove membership: env.lookup_var x is in the denotation of the write's capture set
  have hmem : env.lookup_var x ∈
    (((CaptureSet.var (Var.bound x) .top).union (CaptureSet.var (Var.bound y) .top)).subst
      (Subst.from_TypeEnv env)).ground_denot store := by
    simp [CaptureSet.subst, Var.subst, Subst.from_TypeEnv, CaptureSet.ground_denot,
          reachability_of_loc, hlk_cell]
    -- Need to show l ∈ (cap l).proj H .top ∪ (cap l').proj H .top
    -- First prove (cap l).WfInHeap H using hlk_cell
    have hwf_cap : (CapabilitySet.cap (env.lookup_var x)).WfInHeap store.heap := by
      intro l' hmem
      cases hmem
      exact ⟨.capability (.mcell b0), hlk_cell⟩
    -- Use proj_top to show (cap l).proj H .top = cap l
    apply CapabilitySet.mem.left
    change CapabilitySet.mem (env.lookup_var x)
      ((CapabilitySet.cap (env.lookup_var x)).proj store.heap .top)
    simp only [CapabilitySet.proj_top hwf_cap]
    exact CapabilitySet.mem.here

  -- Apply eval_write based on the boolean value
  cases b
  · -- b = false
    apply Eval.eval_write_false hmem (hx := hlk_cell) hlk_bool
    -- Show the postcondition holds for unit
    constructor
    · apply Exp.IsSimpleAns.is_simple_val
      apply Exp.IsSimpleVal.unit
    constructor
    · exact Exp.WfInHeap.wf_unit
    constructor
    · simp only [CaptureSet.subst]
      exact CaptureSet.WfInHeap.wf_empty
    · simp [resolve]
  · -- b = true
    apply Eval.eval_write_true hmem (hx := hlk_cell) hlk_bool
    -- Show the postcondition holds for unit
    constructor
    · apply Exp.IsSimpleAns.is_simple_val
      apply Exp.IsSimpleVal.unit
    constructor
    · exact Exp.WfInHeap.wf_unit
    constructor
    · simp only [CaptureSet.subst]
      exact CaptureSet.WfInHeap.wf_empty
    · simp [resolve]

theorem sem_typ_letin
  {C : CaptureSet s} {Γ : Ctx s} {e1 : Exp s} {T : Ty .capt s}
  {e2 : Exp (s,,Kind.var)} {U : Ty .exi s}
  (hclosed_C : C.IsClosed)
  (_hclosed_e : (Exp.letin e1 e2).IsClosed)
  (ht1 : C # Γ ⊨ e1 : T.typ)
  (ht2 : C.rename Rename.succ # (Γ,x:T) ⊨ e2 : U.rename Rename.succ) :
  C # Γ ⊨ (Exp.letin e1 e2) : U := by
  intro env store hts
  simp [Exp.subst]
  simp [Ty.exi_exp_denot]
  -- Use Eval.eval_letin with Q1 = (Ty.capt_val_denot env T).as_mpost
  apply Eval.eval_letin (Q1 := (Ty.capt_val_denot env T).as_mpost)
  case hpred =>
    -- Show (Ty.capt_val_denot env T).as_mpost is monotonic
    intro m1 m2 e hwf hsub hQ
    simp [Denot.as_mpost] at hQ ⊢
    have henv_mono := typed_env_is_monotonic hts
    exact capt_val_denot_is_monotonic henv_mono T hsub hQ
  case hbool =>
    -- Show (Ty.capt_val_denot env T).as_mpost is bool independent
    apply Denot.as_mpost_is_bool_independent
    exact capt_val_denot_is_bool_independent (typed_env_is_bool_independent hts) T
  case a =>
    -- Show Eval ... store (e1.subst ...) (Ty.capt_val_denot env T).as_mpost
    have h1 := ht1 env store hts
    simp [Ty.exi_exp_denot, Ty.exi_val_denot] at h1
    exact h1
  case h_nonstuck =>
    intro m1 v hQ1
    simp [Denot.as_mpost] at hQ1
    -- hQ1 : Ty.capt_val_denot env T m1 v
    -- Unfold capt_val_denot to get well-formedness and shape info
    cases T with
    | capt C_T S =>
      simp [Ty.capt_val_denot] at hQ1
      obtain ⟨hsimple, hwf_v, hwf_C, h_shape⟩ := hQ1
      constructor
      · -- Prove v.IsSimpleAns
        exact hsimple
      · -- Prove v.WfInHeap m1.heap
        exact hwf_v
  case h_val =>
    -- Handle the value case: e1 evaluated to a simple value v
    intro m1 v hs1 hv hwf_v hQ1 l' hfresh
    -- m1.subsumes store, v is a simple value, Q1 v m1 holds
    simp [Denot.as_mpost] at hQ1
    -- Construct the HeapVal for v
    let heapval : HeapVal := ⟨v, hv, compute_reachability m1.heap v hv⟩
    -- Prove that the reachability set is well-formed in the heap
    have hreach_wf : heapval.reachability.WfInHeap m1.heap :=
      compute_reachability_locations_exist m1.wf hwf_v
    -- Apply ht2 with extended environment and memory
    have ht2' := ht2 (env.extend_var l')
      (m1.extend_val l' heapval hwf_v rfl hreach_wf hfresh)
    simp [Ty.exi_exp_denot] at ht2' ⊢
    -- Rewrite to make expressions match
    rw [<-Exp.from_TypeEnv_weaken_open] at ht2'
    -- Show that capability sets match
    have hcap_rename :
      (C.rename Rename.succ).denot (env.extend_var l')
      = C.denot env := by
      have := rebind_captureset_denot (Rebind.weaken (env:=env) (x:=l')) C
      exact this.symm
    have hC_mono : C.denot env store = C.denot env (m1.extend_val l' heapval hwf_v rfl hreach_wf hfresh) := by
      have hwf_C : (C.subst (Subst.from_TypeEnv env)).WfInHeap store.heap := by
        apply CaptureSet.wf_subst
        · apply CaptureSet.wf_of_closed hclosed_C
        · apply from_TypeEnv_wf_in_heap hts
      have hext_subsumes_store : (m1.extend_val l' heapval hwf_v rfl hreach_wf hfresh).subsumes store :=
        Memory.subsumes_trans (Memory.extend_val_subsumes m1 l' heapval hwf_v rfl hreach_wf hfresh) hs1
      exact capture_set_denot_is_monotonic hwf_C hext_subsumes_store
    -- Convert postcondition using weaken_exi_val_denot
    rw [hC_mono, ← hcap_rename]
    apply eval_post_monotonic _ (ht2' _)
    · -- Show postcondition entailment
      apply Denot.imply_to_entails
      have heqv := weaken_exi_val_denot (env:=env) (x:=l') (T:=U)
      apply (Denot.equiv_to_imply heqv).2
    · -- Show: EnvTyping (Γ,x:T) (env.extend_var l')
      --       (m1.extend_val l' heapval hwf_v hfresh)
      constructor
      · -- Show: Ty.capt_val_denot env T
        --       (m1.extend_val l' heapval hwf_v hfresh) (Exp.var (Var.free l'))
        -- Strategy: Use monotonicity + transparency

        -- Step 1: Prove memory subsumption
        have hext : (m1.extend_val l' heapval hwf_v rfl hreach_wf hfresh).subsumes m1 :=
          Memory.extend_val_subsumes m1 l' heapval hwf_v rfl hreach_wf hfresh

        -- Step 2: Lift hQ1 to extended memory using monotonicity
        have henv_mono := typed_env_is_monotonic hts
        have hQ1_lifted : Ty.capt_val_denot env T
          (m1.extend_val l' heapval hwf_v rfl hreach_wf hfresh) v :=
          capt_val_denot_is_monotonic henv_mono T hext hQ1

        -- Step 3: Apply transparency
        have henv_trans := typed_env_is_transparent hts
        have htrans : (Ty.capt_val_denot env T).is_transparent :=
          capt_val_denot_is_transparent henv_trans T

        -- Step 4: Use the memory lookup fact
        have hlookup : (m1.extend_val l' heapval hwf_v rfl hreach_wf hfresh).lookup l' =
          some (Cell.val heapval) := by
          simp [Memory.extend_val]
          exact Heap.extend_lookup_eq m1.heap l' heapval

        -- Step 5: Apply transparency
        apply htrans hlookup hQ1_lifted
      · -- Show: EnvTyping Γ env (m1.extend_val l' heapval hwf_v rfl hreach_wf hfresh)
        -- Original typing preserved under memory extension
        have hext : (m1.extend_val l' heapval hwf_v rfl hreach_wf hfresh).subsumes m1 :=
          Memory.extend_val_subsumes m1 l' heapval hwf_v rfl hreach_wf hfresh
        -- Combine subsumptions: extended memory subsumes m1, m1 subsumes store
        have hsubsume : (m1.extend_val l' heapval hwf_v rfl hreach_wf hfresh).subsumes store :=
          Memory.subsumes_trans hext hs1
        exact env_typing_monotonic hts hsubsume
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
      have ht2' := ht2 (env.extend_var fx) m1
      simp [Ty.exi_exp_denot] at ht2' ⊢
      -- Rewrite to make expressions match
      rw [<-Exp.from_TypeEnv_weaken_open] at ht2'
      -- Show that capability sets match
      have hcap_rename :
        (C.rename Rename.succ).denot (env.extend_var fx)
        = C.denot env := by
        have := rebind_captureset_denot (Rebind.weaken (env:=env) (x:=fx)) C
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
        have heqv := weaken_exi_val_denot (env:=env) (x:=fx) (T:=U)
        apply (Denot.equiv_to_imply heqv).2
      · -- Show: EnvTyping (Γ,x:T) (env.extend_var fx) m1
        constructor
        · -- Show: Ty.capt_val_denot env T m1 (Exp.var (Var.free fx))
          exact hQ1
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

theorem typed_env_lookup_cvar_aux
  (hts : EnvTyping Γ env m)
  (hc : Ctx.LookupCVar Γ c cb) :
  ((env.lookup_cvar c).ground_denot m).BoundedBy ((cb.denot env) m) := by
  induction hc generalizing m
  case here =>
    -- Γ = .push Γ' (.cvar cb'), c = .here
    -- cb = cb'.rename Rename.succ
    rename_i Γ' cb'
    cases env; rename_i info' env'
    cases info'; rename_i cs
    simp [EnvTyping] at hts
    simp [TypeEnv.lookup_cvar, TypeEnv.lookup]
    -- Need: cs.ground_denot m ⊆ (cb'.rename Rename.succ).denot (env'.extend (TypeInfo.cvar cs)) m
    -- We have: cs.ground_denot m ⊆ cb'.denot env' m (from hts.2.2.1)
    -- Use rebinding: cb'.denot env' = (cb'.rename Rename.succ).denot (env'.extend_cvar cs)
    have hreb := rebind_capturebound_denot (Rebind.cweaken (env:=env') (cs:=cs)) cb'
    simp only [TypeEnv.extend_cvar] at hreb
    rw [<-hreb]
    exact hts.2.2.1
  case there b0 b hc_prev ih =>
    -- Handle three cases based on the binding kind
    cases b0
    case var =>
      -- Name the unnamed variables including cb'
      rename_i Γ' c' cb' Tb
      cases env; rename_i info' env'
      cases info'; rename_i x
      simp [EnvTyping] at hts
      obtain ⟨_, henv'⟩ := hts
      -- Apply IH to get the result for env'
      have hih := ih henv'
      simp [TypeEnv.lookup_cvar, TypeEnv.lookup]
      -- Use rebind lemma to relate denots in predecessor and extended env
      have hreb := rebind_capturebound_denot (Rebind.weaken (env:=env') (x:=x)) cb'
      simp only [TypeEnv.extend_var] at hreb
      rw [<-hreb]
      exact hih
    case tvar =>
      rename_i Γ' c' cb' Sb
      cases env; rename_i info' env'
      cases info'; rename_i d
      simp [EnvTyping] at hts
      obtain ⟨_, _, henv'⟩ := hts
      have hih := ih henv'
      simp [TypeEnv.lookup_cvar, TypeEnv.lookup]
      have hreb := rebind_capturebound_denot (Rebind.tweaken (env:=env') (d:=d)) cb'
      simp only [TypeEnv.extend_tvar] at hreb
      rw [<-hreb]
      exact hih
    case cvar =>
      rename_i Γ' c' cb' Bb
      cases env; rename_i info' env'
      cases info'; rename_i cs
      simp [EnvTyping] at hts
      obtain ⟨_, _, _, henv'⟩ := hts
      have hih := ih henv'
      simp [TypeEnv.lookup_cvar, TypeEnv.lookup]
      have hreb := rebind_capturebound_denot (Rebind.cweaken (env:=env') (cs:=cs)) cb'
      simp only [TypeEnv.extend_cvar] at hreb
      rw [<-hreb]
      exact hih

theorem typed_env_lookup_cvar
  (hts : EnvTyping Γ env m)
  (hc : Ctx.LookupCVar Γ c (.bound C)) :
  (env.lookup_cvar c).ground_denot m ⊆ C.denot env m := by
  have h := typed_env_lookup_cvar_aux hts hc
  simp [CaptureBound.denot] at h
  cases h with
  | set hsub => exact hsub

theorem sem_sc_var {x : BVar s .var} {C : CaptureSet s} {S : Ty .shape s} {L : CapKind}
  (hlookup : Γ.LookupVar x (.capt C S)) :
  SemSubcapt Γ (.var (.bound x) L) (C.proj L) := by
  intro env m hts
  -- Get the reachability subset from the typing hypothesis
  have h := typed_env_lookup_var_reachability hts hlookup
  simp [Ty.captureSet] at h
  -- Rewrite RHS using denot_proj_eq first
  rw [CaptureSet.denot_proj_eq]
  -- Now unfold LHS denotation
  simp only [CaptureSet.denot, CaptureSet.subst, Subst.from_TypeEnv, Var.subst,
             CaptureSet.ground_denot]
  -- Apply monotonicity of projection
  exact CapabilitySet.proj_subset_mono h

theorem sem_sc_cvar {c : BVar s .cvar} {C : CaptureSet s} {L : CapKind}
  (hlookup : Γ.LookupCVar c (.bound C)) :
  SemSubcapt Γ (.cvar c L) (C.proj L) := by
  intro env m hts
  -- Get the subset from the typing hypothesis
  have h := typed_env_lookup_cvar hts hlookup
  -- Rewrite RHS using denot_proj_eq first
  rw [CaptureSet.denot_proj_eq]
  -- Unfold LHS denotation
  simp only [CaptureSet.denot, CaptureSet.subst, Subst.from_TypeEnv]
  -- Rewrite LHS using ground_denot_proj_eq
  rw [CaptureSet.ground_denot_proj_eq]
  -- Apply monotonicity of projection
  exact CapabilitySet.proj_subset_mono h

theorem sem_sc_proj_r {C : CaptureSet s} {K : CapKind}
  (hk : HasKind Γ C K) :
  SemSubcapt Γ C (C.proj K) := by
  intro env m hts
  -- Rewrite RHS using denot_proj_eq
  rw [CaptureSet.denot_proj_eq]
  -- Need to show C.denot env m ⊆ (C.denot env m).proj m.heap K
  -- Prove by induction on HasKind
  induction hk generalizing m with
  | empty =>
    -- Empty capture set: trivial
    simp only [CaptureSet.denot, CaptureSet.subst, CaptureSet.ground_denot]
    exact CapabilitySet.Subset.empty
  | union _ _ ih1 ih2 =>
    -- Union case
    simp only [CaptureSet.denot, CaptureSet.subst, CaptureSet.ground_denot, CapabilitySet.proj]
    apply CapabilitySet.Subset.union_left
    · apply CapabilitySet.Subset.trans (ih1 m hts)
      exact CapabilitySet.Subset.union_right_left
    · apply CapabilitySet.Subset.trans (ih2 m hts)
      exact CapabilitySet.Subset.union_right_right
  | sub _ hsub ih =>
    -- Subsumption case
    apply CapabilitySet.Subset.trans (ih m hts)
    exact CapabilitySet.proj_subkind hsub
  | var_empty he =>
    -- Variable with empty kind annotation
    simp only [CaptureSet.denot, CaptureSet.subst, Subst.from_TypeEnv,
               Var.subst, CaptureSet.ground_denot]
    -- Empty projection gives empty set
    rw [CapabilitySet.proj_empty_kind he]
    exact CapabilitySet.Subset.empty
  | cvar_empty he =>
    -- Capture variable with empty kind annotation
    simp only [CaptureSet.denot, CaptureSet.subst, Subst.from_TypeEnv,
               CaptureSet.ground_denot]
    rw [CaptureSet.ground_denot_proj_eq, CapabilitySet.proj_empty_kind he]
    exact CapabilitySet.Subset.empty
  | var hlookup _ ih =>
    -- Variable case
    simp only [CaptureSet.denot, CaptureSet.subst, Subst.from_TypeEnv,
               Var.subst, CaptureSet.ground_denot]
    -- The denotation is (reachability_of_loc m.heap l).proj m.heap L
    -- We need: this ⊆ its projection to K
    -- By IH: (C.proj L).denot env m ⊆ ((C.proj L).denot env m).proj m.heap K
    -- We have: reachability subset of C.denot (from typed_env_lookup_var_reachability)
    have hreach := typed_env_lookup_var_reachability hts hlookup
    simp only [Ty.captureSet] at hreach
    -- Use double projection: proj to L, then proj to K = proj to (L.intersect K)
    rw [← CapabilitySet.proj_proj]
    -- Now goal is: (reach).proj L ⊆ ((reach).proj L).proj K
    -- Use that (C.proj L).denot contains (reach).proj L
    have h_in : (reachability_of_loc m.heap (env.lookup_var _)).proj m.heap _ ⊆
                (CaptureSet.proj C _).denot env m := by
      rw [CaptureSet.denot_proj_eq]
      exact CapabilitySet.proj_subset_mono hreach
    apply CapabilitySet.Subset.trans h_in
    exact ih m hts
  | cvar_unbound hlookup =>
    -- Capture variable with unbound type
    simp only [CaptureSet.denot, CaptureSet.subst, Subst.from_TypeEnv, CaptureSet.ground_denot]
    -- The denotation is (env.lookup_cvar c).proj L
    -- The kind is K.intersect L
    rw [CaptureSet.ground_denot_proj_eq]
    rw [← CapabilitySet.proj_proj]
    -- Need: (lookup_cvar).proj L ⊆ ((lookup_cvar).proj L).proj (K.intersect L)
    -- This simplifies using proj_proj again
    sorry
  | cvar_bound hlookup _ ih =>
    -- Capture variable with bound type
    simp only [CaptureSet.denot, CaptureSet.subst, Subst.from_TypeEnv, CaptureSet.ground_denot]
    rw [CaptureSet.ground_denot_proj_eq]
    -- Similar to var case
    have hcvar := typed_env_lookup_cvar hts hlookup
    have h_in : ((env.lookup_cvar _).ground_denot m).proj m.heap _ ⊆
                (CaptureSet.proj C _).denot env m := by
      rw [CaptureSet.denot_proj_eq]
      exact CapabilitySet.proj_subset_mono hcvar
    apply CapabilitySet.Subset.trans h_in
    exact ih m hts

theorem fundamental_subcapt
  (hsub : Subcapt Γ C1 C2) :
  SemSubcapt Γ C1 C2 := by
  induction hsub
  case sc_trans => grind [sem_sc_trans]
  case sc_elem hsub => exact sem_sc_elem hsub
  case sc_union ih1 ih2 => exact sem_sc_union ih1 ih2
  case sc_cvar hlookup => exact sem_sc_cvar hlookup
  case sc_var hlookup => exact sem_sc_var hlookup
  case sc_proj_r hk => exact sem_sc_proj_r hk

lemma sem_subtyp_top {T : Ty .shape s} :
  SemSubtyp Γ T .top := by
  -- Unfold SemSubtyp for shape types
  simp [SemSubtyp]
  -- Introduce the environment, memory, and typing assumption
  intro env H htyping
  -- Unfold ImplyAfter to handle memory subsumption
  simp [PreDenot.ImplyAfter]
  intro R
  simp [Denot.ImplyAfter]
  intro m' hsubsumes
  -- Unfold ImplyAt to get the implication at a specific memory
  simp [Denot.ImplyAt]
  intro e hdenot_T
  -- Need to prove: Ty.shape_val_denot env .top R m' e
  -- Which unfolds to: e.WfInHeap m'.heap ∧ resolve_reachability m'.heap e ⊆ R
  simp [Ty.shape_val_denot]
  constructor
  · -- Prove well-formedness: e.WfInHeap m'.heap
    -- Use the theorem that shape denotations imply well-formedness
    have hwf_env := typed_env_is_implying_wf htyping
    have hwf_denot := shape_val_denot_implies_wf hwf_env T
    exact hwf_denot R m' e hdenot_T
  · -- Prove reachability bound: resolve_reachability m'.heap e ⊆ R
    -- Use the theorem that shape denotations are reachability safe
    have hsafe_env := typed_env_is_reachability_safe htyping
    have hsafe_denot := shape_val_denot_is_reachability_safe hsafe_env T
    exact hsafe_denot R m' e hdenot_T

-- Helper lemma for extracting type variable bounds from EnvTyping
lemma env_typing_lookup_tvar {X : BVar s .tvar} {S : Ty .shape s} {env : TypeEnv s} {m : Memory}
  (hlookup : Ctx.LookupTVar Γ X S)
  (htyping : EnvTyping Γ env m) :
  (env.lookup_tvar X).ImplyAfter m (Ty.shape_val_denot env S) := by
  induction hlookup generalizing m
  case here Γ S =>
    cases env; rename_i info0 env0
    cases info0; rename_i d
    simp [EnvTyping] at htyping
    obtain ⟨hproper, himply, htyping'⟩ := htyping
    -- lookup_tvar BVar.here gives us d
    simp [TypeEnv.lookup_tvar, TypeEnv.lookup]
    -- Need: d.ImplyAfter m (shape_val_denot (env0.extend_tvar d) (S.rename Rename.succ))
    -- Have: d.ImplyAfter m (Ty.shape_val_denot env0 S)
    -- Use weakening theorem to relate the denotations
    have hw : Ty.shape_val_denot env0 S ≈
              Ty.shape_val_denot (env0.extend_tvar d) (S.rename Rename.succ) :=
      tweaken_shape_val_denot (d := d)
    simp [TypeEnv.extend_tvar] at hw
    -- Need to convert equiv to implication at the PreDenot level
    -- Unfold PreDenot.ImplyAfter and PreDenot.equiv_def
    simp [PreDenot.ImplyAfter]
    intro C
    -- Now we have himply : d.ImplyAfter m ((Ty.shape_val_denot env0 S) C)
    simp [PreDenot.ImplyAfter] at himply
    specialize himply C
    -- And hw gives us equiv at the Denot level
    simp [PreDenot.equiv_def] at hw
    specialize hw C
    -- Use Denot.equiv_to_imply
    have himply_right := (Denot.equiv_to_imply hw).1
    -- Compose the implications
    intro m' hsub e hd
    -- himply_right : Denot.Imply (Ty.shape_val_denot env0 S C)
    --                (Ty.shape_val_denot (env0.extend_tvar d) (S.rename Rename.succ) C)
    -- himply : d.ImplyAfter m ((Ty.shape_val_denot env0 S) C)
    apply himply_right m' e
    apply himply m' hsub e hd
  case there Γ X S b a a_ih =>
    -- Need to case split on what kind of binding b is
    cases b with
    | var T =>
      -- Context extended with a term variable
      cases env; rename_i info env0
      cases info; rename_i v
      simp [EnvTyping] at htyping
      obtain ⟨hval_denot, htyping'⟩ := htyping
      -- lookup_tvar X.there in an environment extended with a var
      simp [TypeEnv.lookup_tvar, TypeEnv.lookup]
      -- Apply IH to get the result for the smaller environment
      have ih_result := a_ih htyping'
      simp [TypeEnv.lookup_tvar] at ih_result
      -- Need: (env0.lookup_tvar X).ImplyAfter m
      --       (Ty.shape_val_denot (env0.extend_var v) (S.rename Rename.succ))
      -- Have: (env0.lookup_tvar X).ImplyAfter m (Ty.shape_val_denot env0 S)
      -- Use weakening lemma for var extension
      have hw : Ty.shape_val_denot env0 S ≈
                Ty.shape_val_denot (env0.extend_var v) (S.rename Rename.succ) :=
        weaken_shape_val_denot (x := v)
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
      cases env; rename_i info env0
      cases info; rename_i d
      simp [EnvTyping] at htyping
      obtain ⟨hproper, himply_bound, htyping'⟩ := htyping
      -- lookup_tvar X.there in an environment extended with a tvar
      simp [TypeEnv.lookup_tvar, TypeEnv.lookup]
      -- Apply IH
      have ih_result := a_ih htyping'
      simp [TypeEnv.lookup_tvar] at ih_result
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
      cases env; rename_i info env0
      cases info; rename_i cs
      simp [EnvTyping] at htyping
      obtain ⟨hwf_cb, hbound, htyping'⟩ := htyping
      -- lookup_tvar X.there in an environment extended with a cvar
      simp [TypeEnv.lookup_tvar, TypeEnv.lookup]
      -- Apply IH
      have ih_result := a_ih htyping'.2
      simp [TypeEnv.lookup_tvar] at ih_result
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
          intro arg m'' hsub_m'' harg_T2
          -- Apply contravariance: if arg satisfies T2, it also satisfies T1
          have harg_T1 : Ty.capt_val_denot env T1 m'' (.var (.free arg)) := by
            -- Extract semantic subtyping for arguments
            have harg_sem := harg env H htyping
            -- Apply it at m'' (need transitivity of subsumption)
            have hsub_H_m'' := Memory.subsumes_trans hsub_m'' hsubsumes
            exact harg_sem m'' hsub_H_m'' (.var (.free arg)) harg_T2
          -- Get the body satisfaction for U1
          specialize hbody arg m'' hsub_m'' harg_T1
          -- Apply covariance: if body satisfies U1, it also satisfies U2
          -- Need to show the environment typing holds for the extended context
          have htyping_ext : EnvTyping (Γ,x:T2) (env.extend_var arg) m'' := by
            -- Construct EnvTyping for the extended context
            simp [TypeEnv.extend_var]
            constructor
            · exact harg_T2
            · -- The original typing still holds with subsumption
              have hsub_H_m'' := Memory.subsumes_trans hsub_m'' hsubsumes
              -- Prove EnvTyping Γ env m'' from EnvTyping Γ env H and subsumption
              exact env_typing_monotonic htyping hsub_H_m''
          -- Apply semantic subtyping for the result
          have hres_sem := hres (env.extend_var arg) m'' htyping_ext
          -- hres_sem : (Ty.exi_val_denot (env.extend_var arg) U1).ImplyAfter m'' ...
          let R0 := expand_captures m'.heap cs
          let R := R0 ∪ (reachability_of_loc m''.heap arg)
          -- Need to convert Denot.ImplyAfter to Mpost.entails_after
          have himply_entails := Denot.imply_after_to_m_entails_after hres_sem
          -- Now use eval_post_monotonic_general to lift hbody from U1 to U2
          -- hbody : Ty.exi_exp_denot ... U1 R m'' (t0.subst...)
          unfold Ty.exi_exp_denot at hbody ⊢
          apply eval_post_monotonic_general _ hbody
          exact himply_entails

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

-- Semantic subtyping for capture bounds
def SemSubbound (Γ : Ctx s) (B1 B2 : CaptureBound s) : Prop :=
  ∀ env m,
    EnvTyping Γ env m ->
    B1.denot env m ⊆ B2.denot env m

-- Fundamental theorem for Subbound
lemma fundamental_subbound
  (hsub : Subbound Γ B1 B2) :
  SemSubbound Γ B1 B2 := by
  induction hsub with
  | capset hsubcapt =>
    -- Subbound Γ (.bound C1) (.bound C2) from Subcapt Γ C1 C2
    intro env m htyping
    simp [CaptureBound.denot]
    -- Need to show: CapabilityBound.set (C1.denot env m) ⊆
    --   CapabilityBound.set (C2.denot env m)
    have hsem := fundamental_subcapt hsubcapt
    exact CapabilityBound.SubsetEq.set (hsem env m htyping)
  | unbound =>
    -- Subbound Γ (.unbound k) (.unbound k)
    intro env m htyping
    simp [CaptureBound.denot]
    apply CapabilityBound.SubsetEq.refl
  | top =>
    -- Subbound Γ B .unbound
    intro env m htyping
    simp [CaptureBound.denot]
    -- .unbound denotes CapabilityBound.top, which is the largest bound
    apply CapabilityBound.SubsetEq.top

lemma sem_subtyp_cpoly {cb1 cb2 : CaptureBound s} {T1 T2 : Ty .exi (s,C)}
  (hB : SemSubbound Γ cb1 cb2) -- contravariant in bound (cb1 <: cb2)
  (hT : SemSubtyp (Γ,C<:cb1) T1 T2) -- covariant in body
  (hclosed_cb1 : cb1.IsClosed) -- cb1 is closed
  : SemSubtyp Γ (.cpoly cb2 T1) (.cpoly cb1 T2) := by
  -- Unfold SemSubtyp for shape types
  simp [SemSubtyp]
  intro env H htyping
  -- Need to prove PreDenot.ImplyAfter for cpoly types
  simp [PreDenot.ImplyAfter]
  intro A
  -- Need to prove Denot.ImplyAfter for cpoly types at capability set A
  simp [Denot.ImplyAfter]
  intro m' hsubsumes e h_cpoly_cb1_T1
  -- Unfold the denotation of cpoly types
  simp [Ty.shape_val_denot] at h_cpoly_cb1_T1 ⊢
  -- Extract the components from the cb2 ∀C T1 denotation (left side)
  obtain ⟨hwf, cs, B0, t0, hresolve, hcs_wf, hR0_subset, hbody⟩ := h_cpoly_cb1_T1
  -- Construct the proof for cb1 ∀C T2 (right side)
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
          intro m'' CS hCS_wf hsub_m'' hCS_satisfies_cb1
          -- hbody expects: (A0 m'').BoundedBy (cb2.denot env m'')
          -- We have hCS_satisfies_cb1 : (A0 m'').BoundedBy (cb1.denot env m'')
          -- And hB : SemSubbound Γ cb1 cb2, i.e., cb1 <: cb2
          -- So we need: cb1.denot env m'' ⊆ cb2.denot env m''
          let A0 := CS.denot TypeEnv.empty
          have hCS_satisfies_cb2 : (A0 m'').BoundedBy (cb2.denot env m'') := by
            -- Apply contravariance: cb1.denot env m'' ⊆ cb2.denot env m''
            have hB_trans := Memory.subsumes_trans hsub_m'' hsubsumes
            have htyping_m'' := env_typing_monotonic htyping hB_trans
            have hB_at_m'' := hB env m'' htyping_m''
            exact CapabilitySet.BoundedBy.trans hCS_satisfies_cb1 hB_at_m''
          -- Apply the original function body with this CS
          have heval1 := hbody m'' CS hCS_wf hsub_m'' hCS_satisfies_cb2
          -- Now use covariance hT
          have henv' : EnvTyping (Γ,C<:cb1) (env.extend_cvar CS) m'' := by
            simp [TypeEnv.extend_cvar]
            constructor
            · exact hCS_wf
            · constructor
              · -- Need: (cb1.subst (Subst.from_TypeEnv env)).WfInHeap m''.heap
                -- From closedness of cb1, we get well-formedness at any heap
                -- First show it's well-formed at H.heap
                have hwf_cb1_at_H : (cb1.subst (Subst.from_TypeEnv env)).WfInHeap H.heap := by
                  -- Use wf_subst with closedness of cb1 and well-formedness of the substitution
                  apply CaptureBound.wf_subst
                  · -- cb1.WfInHeap H.heap follows from closedness
                    apply CaptureBound.wf_of_closed hclosed_cb1
                  · -- (Subst.from_TypeEnv env).WfInHeap H.heap follows from EnvTyping
                    exact from_TypeEnv_wf_in_heap htyping
                -- Then lift to m''.heap using monotonicity
                have hB_trans := Memory.subsumes_trans hsub_m'' hsubsumes
                exact CaptureBound.wf_monotonic hB_trans hwf_cb1_at_H
              · constructor
                · -- Convert hCS_satisfies_cb1 from CS.denot TypeEnv.empty to CS.ground_denot
                  have : CS.denot TypeEnv.empty = CS.ground_denot := by
                    simp [CaptureSet.denot, Subst.from_TypeEnv_empty, CaptureSet.subst_id]
                  rw [← this]
                  exact hCS_satisfies_cb1
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
  (hT : SemSubtyp (Γ,C<:(.unbound .top)) T1 T2) -- covariant in body
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
        have henv' : EnvTyping (Γ,C<:(.unbound .top)) (env.extend_cvar CS) m := by
          simp [TypeEnv.extend_cvar]
          constructor
          · -- Need: CS.WfInHeap m.heap
            exact hwf_CS
          · constructor
            · -- Need: CaptureBound.unbound.subst (...).WfInHeap m.heap
              simp [CaptureBound.subst]
              apply CaptureBound.WfInHeap.wf_unbound
            · constructor
              · -- Need: (CS.ground_denot m).BoundedBy (CaptureBound.unbound.denot env m)
                simp [CaptureBound.denot]
                apply CapabilitySet.BoundedBy.top
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

theorem fundamental_subtyp
  (hT1 : T1.IsClosed) (hT2 : T2.IsClosed)
  (hsub : Subtyp Γ T1 T2) :
  SemSubtyp Γ T1 T2 := by
  induction hsub
  case top =>
    -- T1 is some shape type, T2 is .top
    apply sem_subtyp_top
  case refl =>
    -- T1 = T2
    apply sem_subtyp_refl
  case trans T2_mid hT2_mid _hsub12 _hsub23 ih12 ih23 =>
    -- hsub is (T1 <: T2_mid <: T2), where T2_mid is the middle type
    -- hT2_mid : T2_mid.IsClosed (provided by the trans rule)
    -- ih12 : T1.IsClosed → T2_mid.IsClosed → SemSubtyp Γ T1 T2_mid
    -- ih23 : T2_mid.IsClosed → T2.IsClosed → SemSubtyp Γ T2_mid T2
    apply sem_subtyp_trans (ih12 hT1 hT2_mid) (ih23 hT2_mid hT2)
  case tvar hlookup =>
    -- T1 is a type variable, T2 is looked up from context
    apply sem_subtyp_tvar hlookup
  case arrow T1_arg T2_arg U1 U2 hsub_arg hsub_res ih_arg ih_res =>
    -- T1 = .arrow T1_arg U1, T2 = .arrow T2_arg U2
    -- Extract closedness from arrow types
    cases hT1 with | arrow hT1_arg_closed hU1_closed =>
    cases hT2 with | arrow hT2_arg_closed hU2_closed =>
    apply sem_subtyp_arrow (ih_arg hT2_arg_closed hT1_arg_closed) (ih_res hU1_closed hU2_closed)
  case poly S1 S2 T1_body T2_body hsub_bound hsub_body ih_bound ih_body =>
    -- T1 = .poly S1 T1_body, T2 = .poly S2 T2_body
    -- Extract closedness from poly types
    cases hT1 with | poly hS1_closed hT1_body_closed =>
    cases hT2 with | poly hS2_closed hT2_body_closed =>
    apply sem_subtyp_poly (ih_bound hS2_closed hS1_closed) (ih_body hT1_body_closed hT2_body_closed)
  case cpoly cb1 cb2 T1_body T2_body hsub_bound hsub_body ih_body =>
    -- T1 = .cpoly cb2 T1_body, T2 = .cpoly cb1 T2_body (note the swap!)
    -- Extract closedness from cpoly types
    cases hT1 with | cpoly hcb2_closed hT1_body_closed =>
    cases hT2 with | cpoly hcb1_closed hT2_body_closed =>
    have ih_bound := fundamental_subbound hsub_bound
    apply sem_subtyp_cpoly ih_bound (ih_body hT1_body_closed hT2_body_closed) hcb1_closed
  case capt C1 C2 S1 S2 hsub_capt hsub_shape ih_shape =>
    -- Extract closedness from capt types
    cases hT1 with | capt hC1_closed hS1_closed =>
    cases hT2 with | capt hC2_closed hS2_closed =>
    -- Convert syntactic subcapture to semantic
    have ih_capt := fundamental_subcapt hsub_capt
    -- Apply the lemma
    apply sem_subtyp_capt ih_capt (ih_shape hS1_closed hS2_closed) hC2_closed
  case exi T1_body T2_body hsub_body ih_body =>
    -- Extract closedness from exi types
    cases hT1 with | exi hT1_body_closed =>
    cases hT2 with | exi hT2_body_closed =>
    -- Apply the lemma
    apply sem_subtyp_exi (ih_body hT1_body_closed hT2_body_closed)
  case typ T1_body T2_body hsub_body ih_body =>
    -- T1 = .typ T1_body, T2 = .typ T2_body
    -- Extract closedness from typ types
    cases hT1 with | typ hT1_body_closed =>
    cases hT2 with | typ hT2_body_closed =>
    -- Apply the lemma
    apply sem_subtyp_typ (ih_body hT1_body_closed hT2_body_closed)

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
        (Γ,C<:(.unbound .top),x:T) ⊨ u : (U.rename Rename.succ).rename Rename.succ) :
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

      -- Apply hu with doubly extended environment
      have hu' := hu ((env.extend_cvar cs).extend_var fx) m1
      simp [Ty.exi_exp_denot] at hu' ⊢

      -- First, construct the typing context for hu'
      -- Need to show: EnvTyping (Γ,C<:unbound,x:T) (extended environment) m1
      have hts_extended :
        EnvTyping (Γ,C<:(.unbound .top),x:T) ((env.extend_cvar cs).extend_var fx) m1 := by
        -- This unfolds to a conjunction by EnvTyping definition
        constructor
        · -- Show: Ty.capt_val_denot (env.extend_cvar cs) T m1 (.var (.free fx))
          exact hQ1_body
        · -- Show: EnvTyping (Γ,C<:(.unbound .top)) (env.extend_cvar cs) m1
          -- This is also a conjunction
          constructor
          · -- Show: cs.WfInHeap m1.heap
            exact hwf_cs
          · constructor
            · -- Show: (unbound.subst (from_TypeEnv env)).WfInHeap m1.heap
              simp [CaptureBound.subst]
              constructor  -- unbound is always wf
            · constructor
              · -- Show: cs.ground_denot m1 ⊆ ⟦unbound⟧_[env] m1
                -- Unbound denotes the top capability bound, so every set is bounded by it
                simp [CaptureBound.denot]
                exact CapabilitySet.BoundedBy.top
              · -- Show: EnvTyping Γ env m1
                exact env_typing_monotonic hts hs1

      -- Apply hu' with the typing context
      have hu'' := hu' hts_extended

      -- Expression substitution equality
      have hexp_eq :
        (u.subst (Subst.from_TypeEnv env).lift.lift).subst (Subst.unpack cs (Var.free fx)) =
          u.subst (Subst.from_TypeEnv ((env.extend_cvar cs).extend_var fx)) := by
        rw [Exp.subst_comp, Subst.from_TypeEnv_weaken_unpack]

      -- Capture set equality via rebinding
      have hcap_eq :
        ((C.rename Rename.succ).rename Rename.succ).denot
          ((env.extend_cvar cs).extend_var fx) m1 =
        C.denot env store := by
        -- Use rebind to show double-renamed C equals original C
        have h1 := rebind_captureset_denot (Rebind.cweaken (env:=env) (cs:=cs)) C
        have h2 := rebind_captureset_denot
          (Rebind.weaken (env:=env.extend_cvar cs) (x:=fx)) (C.rename Rename.succ)
        calc
          ((C.rename Rename.succ).rename Rename.succ).denot
            ((env.extend_cvar cs).extend_var fx) m1
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
        Ty.exi_val_denot ((env.extend_cvar cs).extend_var fx)
          ((U.rename Rename.succ).rename Rename.succ) := by
        have heqv1 := rebind_exi_val_denot (Rebind.cweaken (env:=env) (cs:=cs)) U
        have heqv2 := rebind_exi_val_denot
          (Rebind.weaken (env:=env.extend_cvar cs) (x:=fx)) (U.rename Rename.succ)
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

/-- The fundamental theorem of semantic type soundness. -/
theorem fundamental
  (ht : C # Γ ⊢ e : T) :
  C # Γ ⊨ e : T := by
  have hclosed_e := HasType.exp_is_closed ht
  induction ht
  case var hx => apply sem_typ_var hx
  case abs =>
    apply sem_typ_abs
    · exact hclosed_e
    · cases hclosed_e; aesop
  case tabs =>
    apply sem_typ_tabs
    · exact hclosed_e
    · cases hclosed_e; aesop
  case cabs =>
    apply sem_typ_cabs
    · exact hclosed_e
    · cases hclosed_e; aesop
  case pack =>
    rename_i ih
    apply sem_typ_pack
    · exact hclosed_e
    · cases hclosed_e with | pack _ hx_closed =>
      apply ih
      constructor
      exact hx_closed
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
  case app =>
    rename_i hx hy
    -- From closedness of (app x y), extract that x and y are closed variables
    cases hclosed_e with
    | app hx_closed hy_closed =>
      -- Closed variables must be bound (not free heap pointers)
      cases hx_closed
      cases hy_closed
      -- Apply IHs to get semantic typing for the variables
      -- Then apply sem_typ_app theorem
      exact sem_typ_app
        (hx (Exp.IsClosed.var Var.IsClosed.bound))
        (hy (Exp.IsClosed.var Var.IsClosed.bound))
  case invoke =>
    rename_i hx hy
    -- From closedness of (app x y), extract that x and y are closed
    cases hclosed_e with
    | app hx_closed hy_closed =>
      -- Closed variables must be bound (not free heap pointers)
      cases hx_closed
      cases hy_closed
      -- Apply IHs to get semantic typing for the variables
      -- Then apply sem_typ_invoke theorem
      exact sem_typ_invoke
        (hx (Exp.IsClosed.var Var.IsClosed.bound))
        (hy (Exp.IsClosed.var Var.IsClosed.bound))
  case tapp =>
    rename_i hS_closed hx
    -- From closedness of (tapp x S), extract that x and S are closed
    cases hclosed_e with
    | tapp hx_closed hS_closed =>
      -- Closed variables must be bound (not free heap pointers)
      cases hx_closed
      -- Apply IH to get semantic typing for the variable
      -- Then apply sem_typ_tapp theorem
      exact sem_typ_tapp
        (hx (Exp.IsClosed.var Var.IsClosed.bound))
  case capp =>
    rename_i hx hD_closed hih
    cases hclosed_e with
    | capp hx_closed hD_closed_exp =>
      cases hx_closed
      exact sem_typ_capp hD_closed_exp
        (hih (Exp.IsClosed.var Var.IsClosed.bound))
  case letin =>
    rename_i ht1_syn ht2_syn ht1_ih ht2_ih
    cases hclosed_e with
    | letin he1_closed he2_closed =>
      exact sem_typ_letin
        (HasType.use_set_is_closed ht1_syn)
        (Exp.IsClosed.letin he1_closed he2_closed)
        (ht1_ih he1_closed)
        (ht2_ih he2_closed)
  case unpack =>
    rename_i ht_syn hu_syn ht_ih hu_ih
    cases hclosed_e with
    | unpack ht_closed hu_closed =>
      exact sem_typ_unpack
        (HasType.use_set_is_closed ht_syn)
        (ht_ih ht_closed)
        (hu_ih hu_closed)
  case read =>
    rename_i hx_syn hx_ih
    -- From closedness of (read x), extract that x is closed
    cases hclosed_e with
    | read hx_closed =>
      -- Closed variables must be bound (not free heap pointers)
      cases hx_closed
      -- Apply IH to get semantic typing for the variable
      exact sem_typ_read
        (hx_ih (Exp.IsClosed.var Var.IsClosed.bound))
  case write =>
    rename_i hx_syn hy_syn hx_ih hy_ih
    -- From closedness of (write x y), extract that x and y are closed
    cases hclosed_e with
    | write hx_closed hy_closed =>
      -- Closed variables must be bound (not free heap pointers)
      cases hx_closed
      cases hy_closed
      -- Apply IHs to get semantic typing for the variables
      exact sem_typ_write
        (hx_ih (Exp.IsClosed.var Var.IsClosed.bound))
        (hy_ih (Exp.IsClosed.var Var.IsClosed.bound))
  case subtyp ht_syn hsubcapt hsubtyp hclosed_C2 hclosed_E2 ht_ih =>
    -- Get closedness of C1 from the syntactic typing derivation
    have hclosed_C1 := HasType.use_set_is_closed ht_syn
    -- Get closedness of E1 from the syntactic typing derivation
    have hclosed_E1 := HasType.type_is_closed ht_syn
    -- Apply the semantic subtyping lemma
    apply sem_typ_subtyp (ht_ih hclosed_e) hsubcapt hsubtyp
      hclosed_C1 hclosed_E1 hclosed_C2 hclosed_E2

end CaplessK
