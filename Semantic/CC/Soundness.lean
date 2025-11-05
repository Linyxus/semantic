import Semantic.CC.Denotation
import Semantic.CC.Semantics
namespace CC

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
  (ht : (Cf.rename Rename.succ ∪ .var (.bound .here)) # Γ,x:T1 ⊨ e : T2) :
  ∅ # Γ ⊨ Exp.abs Cf T1 e : .typ (Ty.capt Cf (T1.arrow T2)) := by
  intro env store hts
  simp [Ty.exi_exp_denot, Ty.exi_val_denot, Ty.capt_val_denot, Ty.shape_val_denot]
  apply Eval.eval_val
  · simp [Exp.subst]; constructor
  · simp [Denot.as_mpost]
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
                (CaptureSet.var (.bound .here)).denot (env.extend_var arg) H'
                = reachability_of_loc H'.heap arg := by
                simp [CaptureSet.denot, CaptureSet.ground_denot, CaptureSet.subst,
                      Subst.from_TypeEnv, Var.subst, TypeEnv.lookup_var]
                rfl
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
                (Cf.rename Rename.succ ∪ .var (.bound .here)).denot
                  (env.extend_var arg) H' =
                (expand_captures store.heap
                  (Cf.subst (Subst.from_TypeEnv env))).union
                  (reachability_of_loc H'.heap arg) := by
                calc (Cf.rename Rename.succ ∪ .var (.bound .here)).denot
                      (env.extend_var arg) H'
                  _ = (Cf.rename Rename.succ).denot (env.extend_var arg) H' ∪
                      (CaptureSet.var (.bound .here)).denot
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
  (hclosed_tabs : (Exp.tabs Cf S e).IsClosed)
  (ht : Cf.rename Rename.succ # (Γ,X<:S) ⊨ e : T) :
  ∅ # Γ ⊨ Exp.tabs Cf S e : .typ (Ty.capt Cf (S.poly T)) := by
  intro env store hts
  simp [Ty.exi_exp_denot, Ty.exi_val_denot, Ty.capt_val_denot, Ty.shape_val_denot]
  apply Eval.eval_val
  · simp [Exp.subst]; constructor
  · simp [Denot.as_mpost]
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
                      · intro C; exact CaptureSet.wf_monotonic hsubsume (hwf_subst_store.wf_cvar C)
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
  (ht : CaptureSet.var x # Γ ⊨ Exp.var x : (T.subst (Subst.openCVar cs)).typ) :
  CaptureSet.var x # Γ ⊨ Exp.pack cs x : T.exi := by
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
    -- Goal: capt_val_denot (env.extend_cvar (cs.subst ...)) T store (var (x.subst ...))
    -- From ht, we have semantic typing for x at type T.subst (Subst.openCVar cs)
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
      -- hQ : (capt_val_denot env (T.subst (Subst.openCVar cs))).as_mpost (var (x.subst ...)) store
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
    obtain ⟨cs, T0, e0, hresolve, hwf_cs, hR0_sub, hfun⟩ := hv
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
    obtain ⟨cs, S0, e0, hresolve, hwf_cs, hR0_sub, hfun⟩ := hv
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

theorem cabs_val_denot_inv {A : CapabilitySet}
  (hv : Ty.shape_val_denot env (.cpoly B T) A store (.var x)) :
  ∃ fx, x = .free fx
    ∧ ∃ cs B0 e0 hval R,
      store.heap fx = some (Cell.val ⟨Exp.cabs cs B0 e0, hval, R⟩)
    ∧ expand_captures store.heap cs ⊆ A
    ∧ (∀ (m' : Memory) (CS : CaptureSet {}),
      CS.WfInHeap m'.heap ->
      m'.subsumes store ->
      (CS.denot TypeEnv.empty m' ⊆ B.denot env m') ->
      Ty.exi_exp_denot
        (env.extend_cvar CS)
        T (expand_captures store.heap cs) m'
        (e0.subst (Subst.openCVar CS))) := by
  cases x with
  | bound bx => cases bx
  | free fx =>
    simp [Ty.shape_val_denot, resolve] at hv
    obtain ⟨cs, B0, e0, hresolve, hwf_cs, hR0_sub, hfun⟩ := hv
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

theorem cap_val_denot_inv {A : CapabilitySet}
  (hv : Ty.shape_val_denot env .cap A store (.var x)) :
  ∃ fx, x = .free fx ∧ store.heap fx = some .capability ∧ fx ∈ A := by
  cases x with
  | bound bx => cases bx
  | free fx =>
    simp only [Ty.shape_val_denot, Memory.lookup] at hv
    obtain ⟨label, heq, hlookup, hmem⟩ := hv
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
    change ((env.lookup_cvar _).subst (Subst.from_TypeEnv TypeEnv.empty)).ground_denot =
      (env.lookup_cvar _).ground_denot
    rw [Subst.from_TypeEnv_empty, CaptureSet.subst_id]
  | var_bound =>
    simp only [CaptureSet.subst, CaptureSet.denot, Var.subst, Subst.from_TypeEnv]

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

-- NOTE: This theorem is no longer valid after the refactor - lookup_var now returns Nat, not a pair
-- theorem bound_var_cap_eq_reachability
--   (hts : EnvTyping Γ env store) :
--   (env.lookup_var x).2 = reachability_of_loc store (env.lookup_var x).1 :=
--   typed_env_reachability_eq hts

theorem sem_typ_tapp
  {x : BVar s .var} -- x must be a BOUND variable (from typing rule)
  {S : Ty .shape s} -- Type argument
  {T : Ty .exi (s,X)} -- Result type (depends on type variable X)
  (hx : (.var (.bound x)) # Γ ⊨ .var (.bound x) : .typ (.capt (.var (.bound x)) (.poly S T))) :
  (.var (.bound x)) # Γ ⊨ Exp.tapp (.bound x) S : T.subst (Subst.openTVar S) := by
  intro env store hts

  -- Extract function denotation
  have h1 := hx env store hts
  simp [Exp.subst, Subst.from_TypeEnv, Var.subst] at h1
  have h1' := var_exp_denot_inv h1
  simp only [Ty.exi_val_denot, Ty.capt_val_denot] at h1'

  -- Extract the poly structure
  have ⟨fx, hfx, cs, S0, e0, hval, R, hlk, hR0_sub, hfun⟩ := tabs_val_denot_inv h1'.2.2

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
  (hx : (.var (.bound x)) # Γ ⊨ .var (.bound x) :
    .typ (.capt (.var (.bound x)) (.cpoly (.bound D) T))) :
  (.var (.bound x)) # Γ ⊨ Exp.capp (.bound x) D : T.subst (Subst.openCVar D) := by
  intro env store hts

  -- Extract function denotation
  have h1 := hx env store hts
  simp [Exp.subst, Subst.from_TypeEnv, Var.subst] at h1
  have h1' := var_exp_denot_inv h1
  simp only [Ty.exi_val_denot, Ty.capt_val_denot] at h1'

  -- Extract the cpoly structure
  have ⟨fx, hfx, cs, B0, e0, hval, R, hlk, hR0_sub, hfun⟩ := cabs_val_denot_inv h1'.2.2

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
    (by -- Prove that D'.denot TypeEnv.empty ⊆ (.bound D).denot env
      rw [hD'_denot]
      -- Since cb = .bound D, we need: D.denot env store ⊆ D.denot env store
      -- which is trivially true by reflexivity
      simp [CaptureBound.denot]
      exact CapabilitySet.Subset.refl)

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
  (hx : (.var (.bound x)) # Γ ⊨ .var (.bound x) : .typ (.capt (.var (.bound x)) (.arrow T1 T2)))
  (hy : (.var (.bound y)) # Γ ⊨ .var (.bound y) : .typ T1) :
  ((.var (.bound x)) ∪ (.var (.bound y))) # Γ ⊨
    Exp.app (.bound x) (.bound y) : T2.subst (Subst.openVar (.bound y)) := by
  intro env store hts

  -- Extract function denotation
  have h1 := hx env store hts
  simp [Exp.subst, Subst.from_TypeEnv, Var.subst] at h1
  have h1' := var_exp_denot_inv h1
  simp only [Ty.exi_val_denot, Ty.capt_val_denot] at h1'

  -- Extract the arrow structure
  have ⟨fx, hfx, cs, T0, e0, hval, R, hlk, hR0_sub, hfun⟩ := abs_val_denot_inv h1'.2.2

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
                     CaptureSet.denot env (CaptureSet.var (Var.bound x)) store ∪
                     reachability_of_loc store.heap fy := by
    apply CapabilitySet.Subset.union_left
    · exact CapabilitySet.Subset.trans hR0_sub CapabilitySet.Subset.union_right_left
    · exact CapabilitySet.Subset.union_right_right

  have happ'' := eval_capability_set_monotonic happ' hunion_mono

  apply Eval.eval_apply hlk happ''

theorem sem_typ_invoke
  {x y : BVar s .var} -- x and y must be BOUND variables (from typing rule)
  (hx : (.var (.bound x)) # Γ ⊨ .var (.bound x) : .typ (.capt (.var (.bound x)) .cap))
  (hy : (.var (.bound y)) # Γ ⊨ .var (.bound y) : .typ (.capt (.var (.bound y)) .unit)) :
  ((.var (.bound x)) ∪ (.var (.bound y))) # Γ ⊨
    Exp.app (.bound x) (.bound y) : .typ (.capt {} .unit) := by
  intro env store hts

  -- Extract capability denotation from hx
  have h1 := hx env store hts
  simp [Exp.subst, Subst.from_TypeEnv, Var.subst] at h1
  have h1' := var_exp_denot_inv h1
  simp only [Ty.exi_val_denot, Ty.capt_val_denot] at h1'

  -- Extract the capability structure
  have ⟨fx, hfx, hlk_cap, hmem_cap⟩ := cap_val_denot_inv h1'.2.2

  -- Extract unit denotation from hy
  have h2 := hy env store hts
  simp [Exp.subst, Subst.from_TypeEnv, Var.subst] at h2
  have h2' := var_exp_denot_inv h2
  simp only [Ty.exi_val_denot, Ty.capt_val_denot] at h2'

  -- Extract the unit structure
  have ⟨fy, hfy, hval_unit, R, hlk_unit⟩ := unit_val_denot_inv h2'.2.2

  -- Determine concrete locations
  have : fx = env.lookup_var x := by cases hfx; rfl
  subst this
  have : fy = env.lookup_var y := by cases hfy; rfl
  subst this

  -- Simplify goal
  simp [Exp.subst, Subst.from_TypeEnv, Var.subst, Ty.exi_exp_denot, Ty.exi_val_denot,
        Ty.capt_val_denot, Ty.shape_val_denot, CaptureSet.denot]

  -- Show env.lookup_var x is in the union of capability sets
  have hmem :
    env.lookup_var x ∈ CaptureSet.denot env (.var (.bound x) ∪ .var (.bound y)) store := by
    apply CapabilitySet.mem.left
    exact hmem_cap

  -- Apply eval_invoke
  apply Eval.eval_invoke hmem hlk_cap hlk_unit

  -- Show the postcondition holds for unit
  constructor
  · exact Exp.WfInHeap.wf_unit
  · constructor
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
    · exact Exp.WfInHeap.wf_unit
    · constructor
      · apply CaptureSet.wf_subst
        · apply CaptureSet.wf_of_closed CaptureSet.IsClosed.empty
        · apply from_TypeEnv_wf_in_heap hts
      · simp [resolve]

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
  case a =>
    -- Show Eval ... store (e1.subst ...) (Ty.capt_val_denot env T).as_mpost
    have h1 := ht1 env store hts
    simp [Ty.exi_exp_denot, Ty.exi_val_denot] at h1
    exact h1
  case h_val =>
    -- Handle the value case: e1 evaluated to a simple value v
    intro m1 v hs1 hv hwf_v hQ1 l' hfresh
    -- m1.subsumes store, v is a simple value, Q1 v m1 holds
    simp [Denot.as_mpost] at hQ1
    -- Construct the HeapVal for v
    let heapval : HeapVal := ⟨v, hv, compute_reachability m1.heap v hv⟩
    -- Apply ht2 with extended environment and memory
    have ht2' := ht2 (env.extend_var l')
      (m1.extend_val l' heapval hwf_v rfl hfresh)
    simp [Ty.exi_exp_denot] at ht2' ⊢
    -- Rewrite to make expressions match
    rw [<-Exp.from_TypeEnv_weaken_open] at ht2'
    -- Show that capability sets match
    have hcap_rename :
      (C.rename Rename.succ).denot (env.extend_var l')
      = C.denot env := by
      have := rebind_captureset_denot (Rebind.weaken (env:=env) (x:=l')) C
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
      have heqv := weaken_exi_val_denot (env:=env) (x:=l') (T:=U)
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
        have hQ1_lifted : Ty.capt_val_denot env T
          (m1.extend_val l' heapval hwf_v rfl hfresh) v :=
          capt_val_denot_is_monotonic henv_mono T hext hQ1

        -- Step 3: Apply transparency
        have henv_trans := typed_env_is_transparent hts
        have htrans : (Ty.capt_val_denot env T).is_transparent :=
          capt_val_denot_is_transparent henv_trans T

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
  (env.lookup_cvar c).ground_denot m ⊆ (cb.denot env) m := by
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
  exact h

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
    obtain ⟨_, _, hshape⟩ := hval
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

theorem sem_sc_var {x : BVar s .var} {C : CaptureSet s} {S : Ty .shape s}
  (hlookup : Γ.LookupVar x (.capt C S)) :
  SemSubcapt Γ (.var (.bound x)) C := by
  intro env m hts
  unfold CaptureSet.denot
  simp [CaptureSet.subst, Subst.from_TypeEnv]
  have h := typed_env_lookup_var_reachability hts hlookup
  simp [Ty.captureSet] at h
  exact h

theorem sem_sc_cvar {c : BVar s .cvar} {C : CaptureSet s}
  (hlookup : Γ.LookupCVar c (.bound C)) :
  SemSubcapt Γ (.cvar c) C := by
  intro env m hts
  unfold CaptureSet.denot
  simp [CaptureSet.subst, Subst.from_TypeEnv]
  exact typed_env_lookup_cvar hts hlookup

theorem fundamental_subcapt
  (hsub : Subcapt Γ C1 C2) :
  SemSubcapt Γ C1 C2 := by
  induction hsub
  case sc_trans => grind [sem_sc_trans]
  case sc_elem hsub => exact sem_sc_elem hsub
  case sc_union ih1 ih2 => exact sem_sc_union ih1 ih2
  case sc_cvar hlookup => exact sem_sc_cvar hlookup
  case sc_var hlookup => exact sem_sc_var hlookup

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

theorem sem_typ_unpack
  {C : CaptureSet s} {Γ : Ctx s} {t : Exp s} {T : Ty .capt (s,C)}
  {u : Exp (s,C,x)} {U : Ty .exi s}
  (hclosed_C : C.IsClosed)
  (ht : C # Γ ⊨ t : .exi T)
  (hu : (C.rename Rename.succ).rename Rename.succ #
        (Γ,C<:.unbound,x:T) ⊨ u : (U.rename Rename.succ).rename Rename.succ) :
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
  case a =>
    -- Show Eval ... store (t.subst ...) (Ty.exi_val_denot env (.exi T)).as_mpost
    have ht' := ht env store hts
    simp [Ty.exi_exp_denot] at ht'
    exact ht'
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
      -- Now hQ1 : Ty.capt_val_denot (env.extend_cvar cs) T m1 (.var (.free fx))

      -- Apply hu with doubly extended environment
      have hu' := hu ((env.extend_cvar cs).extend_var fx) m1
      simp [Ty.exi_exp_denot] at hu' ⊢

      -- First, construct the typing context for hu'
      -- Need to show: EnvTyping (Γ,C<:unbound,x:T) (extended environment) m1
      have hts_extended :
        EnvTyping (Γ,C<:.unbound,x:T) ((env.extend_cvar cs).extend_var fx) m1 := by
        -- This unfolds to a conjunction by EnvTyping definition
        constructor
        · -- Show: Ty.capt_val_denot (env.extend_cvar cs) T m1 (.var (.free fx))
          exact hQ1
        · -- Show: EnvTyping (Γ,C<:.unbound) (env.extend_cvar cs) m1
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
                -- unbound's denotation is the whole memory, so any set is subset
                simp [CaptureBound.denot]
                -- CLAUDE: Goal: cs.ground_denot m1 ⊆ CapabilitySet.any
                -- CLAUDE: This should be trivially true - CapabilitySet.any is the universal set
                constructor
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
  case subtyp => sorry --grind [sem_typ_subtyp]

end CC
