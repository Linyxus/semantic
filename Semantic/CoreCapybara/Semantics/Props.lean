import Semantic.CoreCapybara.Semantics.SmallStep
import Semantic.CoreCapybara.Semantics.BigStep
namespace CoreCapybara

/-- The result of looking up a variable in the heap is deterministic. -/
theorem Heap.lookup_deterministic {H : Heap}
  (hlookup1 : H l = some v1)
  (hlookup2 : H l = some v2) :
  v1 = v2 := Option.some.inj (hlookup1.symm.trans hlookup2)

/-- The result of looking up a variable in the memory is deterministic. -/
theorem Memory.lookup_deterministic {m : Memory}
  (hlookup1 : m.lookup l = some v1)
  (hlookup2 : m.lookup l = some v2) :
  v1 = v2 := by
  cases m
  simp only [Memory.lookup] at hlookup1 hlookup2
  exact Heap.lookup_deterministic hlookup1 hlookup2

/-- Every simple value is a value. -/
theorem Exp.isVal_of_isSimpleVal {v : Exp s} (hv : v.IsSimpleVal) : v.IsVal := by
  cases hv <;> constructor

-- NOTE: The former `step_capability_set_monotonic` / `small_step_capability_set_monotonic`
-- lemmas have been removed.  `Step`/`Reduce` are now indexed by a *trace* of the
-- heap events actually performed, not by a capability-set upper bound, so there is
-- no "larger authority" to be monotone in: the trace is exact, not an over-approximation.

/-- Helper: Congruence for Reduce in letin context. -/
theorem reduce_ctx_letin
  (hred : Reduce C m e1 m' e1') :
  Reduce C m (.letin e1 e2) m' (.letin e1' e2) := by
  induction hred with
  | refl => exact Reduce.refl
  | step h _ ih => exact Reduce.step (Step.step_ctx_letin h) ih

/-- Helper: Congruence for Reduce in unpack context. -/
theorem reduce_ctx_unpack
  (hred : Reduce C m e1 m' e1') :
  Reduce C m (.unpack e1 e2) m' (.unpack e1' e2) := by
  induction hred with
  | refl => exact Reduce.refl
  | step h _ ih => exact Reduce.step (Step.step_ctx_unpack h) ih

/-- Helper: Variables cannot step, so reduction is reflexive. -/
theorem reduce_var_inv
  (hred : Reduce C m (.var x) m' v') :
  m' = m ∧ v' = .var x := by
  generalize he : Exp.var x = e at hred
  induction hred with
  | refl => exact ⟨rfl, he ▸ rfl⟩
  | step hstep _ ih =>
    -- No Step rule applies to a bare variable
    subst he
    cases hstep

/-- Helper: Single step preserves memory subsumption. -/
theorem step_memory_monotonic
  (hstep : Step C m1 e1 m2 e2) :
  m2.subsumes m1 := by
  induction hstep with
  | step_apply | step_invoke | step_tapply | step_capply | step_unwrap
  | step_cond_var_true _ | step_cond_var_false _ | step_read _ _
  | step_rename | step_unpack | step_par_left | step_par_right =>
    exact Memory.subsumes_refl _
  | step_write_true hx _ | step_write_false hx _ =>
    exact Memory.update_mcell_subsumes _ _ _ _ ⟨_, hx⟩
  | step_alloc _ hfresh => exact Memory.extend_mcell_subsumes _ _ _ hfresh
  | step_drop hx => exact Memory.drop_mcell_subsumes _ _ ⟨_, hx⟩
  | step_ctx_letin _ ih | step_ctx_unpack _ ih => exact ih
  | step_lift hv hwf hfresh => exact Memory.extend_subsumes _ _ _ hwf rfl hfresh

/-- Helper: Reduction preserves memory subsumption. -/
theorem reduce_memory_monotonic
  (hred : Reduce C m1 e1 m2 e2) :
  m2.subsumes m1 := by
  induction hred with
  | refl => exact Memory.subsumes_refl _
  | step h rest ih =>
    exact Memory.subsumes_trans ih (step_memory_monotonic h)

theorem step_var_absurd
  (hstep : Step C m (.var x) m' e') : False := by
  cases hstep

theorem step_val_absurd
  (hv : Exp.IsSimpleVal v)
  (hstep : Step C m v m' e') :
  False := by
  cases hv <;> cases hstep

theorem step_ans_absurd
  (hans : e.IsAns)
  (hstep : Step C m e m' e') :
  False := by
  cases hans with
  | is_var => exact step_var_absurd hstep
  | is_val hv => cases hv <;> cases hstep

theorem reduce_ans_eq
  (hans : e.IsAns)
  (hred : Reduce C m e m' e') :
  m = m' ∧ e = e' := by
  induction hred with
  | refl => exact ⟨rfl, rfl⟩
  | step h rest ih =>
    have habsurd : False := step_ans_absurd hans h
    contradiction

theorem reduce_letin_inv
  (hred : Reduce t m (.letin e1 e2) m' a)
  (hans : a.IsAns) :
  (∃ t1 t2 m0 y0, Reduce t1 m e1 m0 (.var (.free y0)) ∧
     Reduce t2 m0 (e2.subst (Subst.openVar (.free y0))) m' a) ∨
  (∃ (t1 t2 : Trace) (m0 : Memory) (v0 : Exp {}) (hv : v0.IsSimpleVal)
     (hwf : Exp.WfInHeap v0 m0.heap) (l0 : Nat) (hfresh : m0.heap l0 = none),
    Reduce t1 m e1 m0 v0 ∧
    Reduce
      t2
      (m0.extend l0 ⟨v0, hv, compute_reachability m0.heap v0 hv⟩ hwf rfl hfresh)
      (e2.subst (Subst.openVar (.free l0)))
      m' a) := by
  -- Generalize the letin expression to enable induction.  The trace now
  -- decomposes across the step, so the sub-reductions carry their own traces.
  generalize hgen : Exp.letin e1 e2 = e_full at hred
  induction hred generalizing e1 e2 with
  | refl =>
    -- Base case: e_full = a, but a is an answer and e_full = .letin e1 e2
    rw [←hgen] at hans
    cases hans with
    | is_val hv => cases hv
  | step hstep rest ih =>
    rw [←hgen] at hstep
    cases hstep with
    | step_ctx_letin hstep_e1 =>
      -- e1 steps to e1'; combine with the reduction obtained from the IH.
      have ih_result := ih hans rfl
      cases ih_result with
      | inl h_var =>
        obtain ⟨t1, t2, m0, y0, hred_e1', hred_body⟩ := h_var
        exact Or.inl ⟨_, _, m0, y0, Reduce.step hstep_e1 hred_e1', hred_body⟩
      | inr h_val =>
        obtain ⟨t1, t2, m0, v0, hv, hwf, l0, hfresh, hred_e1', hred_body⟩ := h_val
        exact Or.inr ⟨_, _, m0, v0, hv, hwf, l0, hfresh, Reduce.step hstep_e1 hred_e1', hred_body⟩
    | step_rename =>
      -- e1 = .var (.free y); the e1-reduction is reflexive (empty trace).
      exact Or.inl ⟨_, _, _, _, Reduce.refl, rest⟩
    | step_lift hv hwf hfresh =>
      -- e1 is a simple value, allocated at l; the e1-reduction is reflexive.
      exact Or.inr ⟨_, _, _, _, hv, hwf, _, hfresh, Reduce.refl, rest⟩

theorem step_preserves_wf
  (hstep : Step C m1 e1 m2 e2)
  (hwf : e1.WfInHeap m1.heap) :
  e2.WfInHeap m2.heap := by
  cases hstep with
  | step_apply hlookup =>
    -- e1 = .app (.free x) (.free y), e2 = body.subst (openVar y)
    -- Extract well-formedness of x and y from the application
    rename_i x y cs T e_body hv R
    cases hwf with
    | wf_app hwf_x hwf_y =>
      -- Get well-formedness of the abstraction from the heap
      have hwf_abs : Exp.WfInHeap (.abs cs T e_body) m1.heap :=
        m1.wf.wf_val _ _ hlookup
      -- Extract well-formedness of the body
      have ⟨_, _, hwf_body⟩ := Exp.wf_inv_abs hwf_abs
      -- Build well-formed substitution
      have hwf_subst := Subst.wf_openVar hwf_y
      -- Apply substitution preservation
      exact Exp.wf_subst hwf_body hwf_subst
  | step_invoke _ _ =>
    -- e1 = .app (.free x) (.free y), e2 = .unit
    -- Unit is always well-formed
    exact Exp.WfInHeap.wf_unit
  | step_tapply hlookup =>
    -- e1 = .tapp (.free x) S, e2 = body.subst (openTVar .top)
    -- Extract well-formedness of x and S from the type application
    rename_i x S cs S' e_body hv R
    cases hwf with
    | wf_tapp hwf_x hwf_S =>
      -- Get well-formedness of the type abstraction from the heap
      have hwf_tabs : Exp.WfInHeap (.tabs cs S' e_body) m1.heap :=
        m1.wf.wf_val _ _ hlookup
      -- Extract well-formedness of the body
      have ⟨_, _, hwf_body⟩ := Exp.wf_inv_tabs hwf_tabs
      -- Build well-formed substitution: .top is always well-formed
      have hwf_top : PureTy.WfInHeap (PureTy.top (s:=∅)) m1.heap :=
        Ty.WfInHeap.wf_top
      have hwf_subst := Subst.wf_openTVar hwf_top
      -- Apply substitution preservation
      exact Exp.wf_subst hwf_body hwf_subst
  | step_capply hlookup =>
    -- e1 = .capp (.free x) CS, e2 = body.subst (openCVar CS)
    -- Extract well-formedness of x and CS from the capability application
    rename_i x CS cs B e_body hv R
    cases hwf with
    | wf_capp hwf_x hwf_CS =>
      -- Get well-formedness of the capability abstraction from the heap
      have hwf_cabs : Exp.WfInHeap (.cabs cs B e_body) m1.heap :=
        m1.wf.wf_val _ _ hlookup
      -- Extract well-formedness of the body
      have ⟨_, _, hwf_body⟩ := Exp.wf_inv_cabs hwf_cabs
      -- Build well-formed substitution
      have hwf_subst := Subst.wf_openCVar hwf_CS
      -- Apply substitution preservation
      exact Exp.wf_subst hwf_body hwf_subst
  | step_unwrap hlookup =>
    rename_i x cs Ψ R hv
    have hwf_boxed : Exp.WfInHeap (.boxed cs Ψ e2) m1.heap := by
      exact Memory.wf_lookup hlookup
    cases hwf_boxed with
    | wf_boxed _ _ hwf_body =>
      exact hwf_body
  | step_cond_var_true hlookup =>
    have ⟨_, hwf_then, _⟩ := Exp.wf_inv_cond hwf
    exact hwf_then
  | step_cond_var_false hlookup =>
    have ⟨_, _, hwf_else⟩ := Exp.wf_inv_cond hwf
    exact hwf_else
  | step_read hreader hcell =>
    -- e1 = .read (.free x), e2 = if b then .btrue else .bfalse
    -- Both branches are boolean values, always well-formed
    split
    · exact Exp.WfInHeap.wf_btrue
    · exact Exp.WfInHeap.wf_bfalse
  | step_write_true _ _ =>
    -- e1 = .write (.free x) (.free y), e2 = .unit
    -- Unit is always well-formed in any heap
    exact Exp.WfInHeap.wf_unit
  | step_write_false _ _ =>
    -- e1 = .write (.free x) (.free y), e2 = .unit
    -- Unit is always well-formed in any heap
    exact Exp.WfInHeap.wf_unit
  | step_alloc _ hfresh =>
    -- e1 = .alloc (.free x); e2 = .pack (.var (.M .epsilon) (.free l)) (.free l),
    -- where l is freshly allocated as a live mcell in m2.  The expected type
    -- pins the boolean, so `extend_mcell_lookup` is inlined into the `exact`.
    exact Exp.WfInHeap.wf_pack
      (CaptureSet.WfInHeap.wf_var_free (Memory.extend_mcell_lookup hfresh))
      (Var.WfInHeap.wf_free (Memory.extend_mcell_lookup hfresh))
  | step_drop _ =>
    -- e1 = .drop (.free x), e2 = .unit; unit is always well-formed
    exact Exp.WfInHeap.wf_unit
  | step_ctx_letin hstep_e1 =>
    -- e1 = .letin e1' e2', e2 = .letin e1'' e2'
    -- Use IH recursively
    have ⟨hwf_e1', hwf_e2'⟩ := Exp.wf_inv_letin hwf
    have hwf_e1'' := step_preserves_wf hstep_e1 hwf_e1'
    -- Memory might have changed, need monotonicity
    have hsub := step_memory_monotonic hstep_e1
    have hwf_e2'' := Exp.wf_monotonic hsub hwf_e2'
    exact Exp.WfInHeap.wf_letin hwf_e1'' hwf_e2''
  | step_ctx_unpack hstep_e1 =>
    -- e1 = .unpack e1' e2', e2 = .unpack e1'' e2'
    -- Use IH recursively
    have ⟨hwf_e1', hwf_e2'⟩ := Exp.wf_inv_unpack hwf
    have hwf_e1'' := step_preserves_wf hstep_e1 hwf_e1'
    -- Memory might have changed, need monotonicity
    have hsub := step_memory_monotonic hstep_e1
    have hwf_e2'' := Exp.wf_monotonic hsub hwf_e2'
    exact Exp.WfInHeap.wf_unpack hwf_e1'' hwf_e2''
  | step_rename =>
    -- e1 = .letin (.var (.free y)) e, e2 = e.subst (openVar y)
    rename_i y e_body
    -- Extract well-formedness from letin
    have ⟨hwf_var, hwf_body⟩ := Exp.wf_inv_letin hwf
    -- Extract Var.WfInHeap from Exp.WfInHeap
    cases hwf_var with
    | wf_var hwf_y =>
      -- Build well-formed substitution
      have hwf_subst := Subst.wf_openVar hwf_y
      -- Apply substitution preservation
      exact Exp.wf_subst hwf_body hwf_subst
  | step_lift hv hwf_v hfresh =>
    -- e1 = .letin v e, e2 = e.subst (openVar (.free l))
    rename_i v e_body l
    -- Extract well-formedness from letin
    have ⟨hwf_v', hwf_body⟩ := Exp.wf_inv_letin hwf
    -- Memory extends with the value
    -- The resulting memory is m1.extend l ...
    let m_ext := m1.extend l ⟨v, hv, compute_reachability m1.heap v hv⟩ hwf_v rfl hfresh
    -- Show (.free l) is well-formed in the extended heap
    have hwf_l : Var.WfInHeap (.free l : Var .var ∅) m_ext.heap := by
      have hlookup_l :
          m_ext.heap l = some (.val ⟨v, hv, compute_reachability m1.heap v hv⟩) := by
        unfold m_ext
        simpa only [Memory.lookup] using
          (Memory.extend_lookup_eq m1 l
            ⟨v, hv, compute_reachability m1.heap v hv⟩ hwf_v rfl hfresh)
      exact Var.WfInHeap.wf_free hlookup_l
    -- e_body is well-formed in the extended heap (by monotonicity)
    have hsub := Memory.extend_subsumes m1 l
      ⟨v, hv, compute_reachability m1.heap v hv⟩ hwf_v rfl hfresh
    have hwf_body_ext := Exp.wf_monotonic hsub hwf_body
    -- Build well-formed substitution
    have hwf_subst := Subst.wf_openVar hwf_l
    -- Apply substitution preservation
    exact Exp.wf_subst hwf_body_ext hwf_subst
  | step_unpack =>
    -- e1 = .unpack (.pack cs (.free x)) e, e2 = e.subst (unpack cs x)
    rename_i cs x e_body
    -- Extract well-formedness from unpack
    have ⟨hwf_pack, hwf_body⟩ := Exp.wf_inv_unpack hwf
    -- Extract well-formedness from pack
    cases hwf_pack with
    | wf_pack hwf_cs hwf_x =>
      -- Build well-formed substitution
      have hwf_subst := Subst.wf_unpack hwf_cs hwf_x
      -- Apply substitution preservation
      exact Exp.wf_subst hwf_body hwf_subst
  | step_par_left =>
    -- e1 = .par e1' e2', e2 = e1'
    cases hwf with
    | wf_par hwf1 hwf2 => exact hwf1
  | step_par_right =>
    -- e1 = .par e1' e2', e2 = e2'
    cases hwf with
    | wf_par hwf1 hwf2 => exact hwf2

theorem reduce_preserves_wf
  (hred : Reduce C m1 e1 m2 e2)
  (hwf : e1.WfInHeap m1.heap) :
  e2.WfInHeap m2.heap := by
  induction hred with
  | refl => exact hwf
  | step hstep rest ih =>
    have hwf_mid := step_preserves_wf hstep hwf
    exact ih hwf_mid

/-- Inversion lemma for reduction of unpack expressions -/
theorem reduce_unpack_inv
  (hred : Reduce t m (.unpack e1 e2) m' a)
  (hans : a.IsAns) :
  ∃ (t1 t2 : Trace) (m0 : Memory) (cs : CaptureSet {}) (x : Nat),
    Reduce t1 m e1 m0 (.pack cs (.free x)) ∧
    Reduce t2 m0 (e2.subst (Subst.unpack cs (.free x))) m' a := by
  -- Use generalization to make induction work; sub-reductions carry their own traces.
  generalize hgen : Exp.unpack e1 e2 = e_full at hred
  induction hred generalizing e1 e2 with
  | refl =>
    -- Base case: no reduction, but unpack is not an answer
    rw [←hgen] at hans
    cases hans; rename_i hv
    cases hv
  | step hstep rest ih =>
    rw [←hgen] at hstep
    cases hstep with
    | step_ctx_unpack hstep_e1 =>
      -- e1 steps to e1', then continue with induction
      rename_i e1'
      have ih_result := ih (e1 := e1') (e2 := e2) hans rfl
      obtain ⟨t1, t2, m0, cs, x, hred_e1', hred_body⟩ := ih_result
      exact ⟨_, _, m0, cs, x, Reduce.step hstep_e1 hred_e1', hred_body⟩
    | step_unpack =>
      -- e1 is already .pack cs (.free x); its reduction is reflexive (empty trace).
      exact ⟨_, _, _, _, _, Reduce.refl, rest⟩

-- The capability index is retained as a phantom for compatibility with the
-- capability-set-indexed `Eval`; the `step` witness now carries a trace, which
-- is existentially hidden here (progress only asserts that *some* step exists).
inductive IsProgressive : CapabilitySet -> Memory -> Exp {} -> Prop where
| done :
  e.IsAns ->
  IsProgressive R m e
| step :
  Step t m e m' e' ->
  IsProgressive C m e

/-- If an answer has an evaluation, then the postcondition holds for it. -/
theorem eval_ans_holds_post
  (heval : Eval C m e Q)
  (hans : e.IsAns) :
  Q e m := by
  cases heval with
  | eval_val hv hQ => exact hQ
  | eval_var hQ => exact hQ
  | eval_pack _ hQ => exact hQ
  | eval_alloc => cases hans; rename_i hv; cases hv
  | eval_drop => cases hans; rename_i hv; cases hv
  | eval_apply => cases hans; rename_i hv; cases hv
  | eval_invoke => cases hans; rename_i hv; cases hv
  | eval_tapply => cases hans; rename_i hv; cases hv
  | eval_capply => cases hans; rename_i hv; cases hv
  | eval_wrap hQ => exact hQ
  | eval_unwrap =>
    cases hans with
    | is_val hv => cases hv
  | eval_letin => cases hans; rename_i hv; cases hv
  | eval_unpack => cases hans; rename_i hv; cases hv
  | eval_cond =>
    cases hans with
    | is_val hv => cases hv
  | eval_read => cases hans; rename_i hv; cases hv
  | eval_write_true => cases hans; rename_i hv; cases hv
  | eval_write_false => cases hans; rename_i hv; cases hv
  | eval_par => cases hans; rename_i hv; cases hv

theorem eval_implies_progressive
  (heval : Eval C m e Q) :
  IsProgressive C m e := by
  induction heval with
  | eval_val hv hQ => exact IsProgressive.done (Exp.IsAns.is_val (Exp.isVal_of_isSimpleVal hv))
  | eval_var hQ => exact IsProgressive.done Exp.IsAns.is_var
  | eval_pack _ _ => exact IsProgressive.done (Exp.IsAns.is_val Exp.IsVal.pack)
  | eval_alloc hlookup _ =>
    -- e = .alloc (.free x); steps via step_alloc to a fresh live mcell
    obtain ⟨l, hfresh⟩ := Memory.exists_fresh _
    exact IsProgressive.step (Step.step_alloc (l := l) hlookup hfresh)
  | eval_drop hx _ _ =>
    -- e = .drop (.free x); steps via step_drop
    exact IsProgressive.step (Step.step_drop hx)
  | eval_apply hlookup eval_body ih =>
    rename_i cs T e_abs hv R C' y Q' m' x
    match y with
    | .bound idx => cases idx
    | .free y' => exact IsProgressive.step (Step.step_apply hlookup)
  | eval_invoke _ hlookup_x hlookup_y _ =>
    exact IsProgressive.step (Step.step_invoke hlookup_x hlookup_y)
  | eval_tapply hlookup eval_body ih =>
    exact IsProgressive.step (Step.step_tapply hlookup)
  | eval_capply hlookup eval_body ih =>
    exact IsProgressive.step (Step.step_capply hlookup)
  | eval_wrap hQ => exact IsProgressive.done (Exp.IsAns.is_val Exp.IsVal.boxed)
  | eval_unwrap hlookup eval_body ih =>
    exact IsProgressive.step (Step.step_unwrap hlookup)
  | eval_letin hpred hbool eval_e1 h_nonstuck h_val h_var hseq hagg ih_e1 ih_val ih_var =>
    -- e = .letin e1 e2
    -- By IH, e1 is progressive
    cases ih_e1 with
    | done hans =>
      -- e1 is an answer, use the variables directly without renaming
      -- By eval_ans_holds_post, the postcondition holds for e1
      have hQ1 := eval_ans_holds_post eval_e1 hans
      -- By h_nonstuck, e1 is a simple answer
      have ⟨hsimple_ans, hwf⟩ := h_nonstuck hQ1
      -- Case analyze on whether it's a simple value or variable
      cases hsimple_ans with
      | is_simple_val hv =>
        -- e1 is a simple value: step_lift to a fresh location (heap is finite).
        obtain ⟨l0, hfresh⟩ := Memory.exists_fresh _
        exact IsProgressive.step (Step.step_lift (l := l0) hv hwf hfresh)
      | is_var =>
        -- e1 is a variable, we need to show it's a free variable
        rename_i x_var
        cases x_var with
        | bound idx => cases idx
        | free y =>
          exact IsProgressive.step Step.step_rename
    | step hstep =>
      -- e1 can step, so letin e1 e2 can step via step_ctx_letin
      exact IsProgressive.step (Step.step_ctx_letin hstep)
  | eval_unpack hpred hbool eval_e1 h_nonstuck h_val hseq hagg ih_e1 ih_val =>
    -- e = .unpack e1 e2
    -- By IH, e1 is progressive
    cases ih_e1 with
    | done hans =>
      -- e1 is an answer
      -- By eval_ans_holds_post, the postcondition holds for e1
      have hQ1 := eval_ans_holds_post eval_e1 hans
      -- By h_nonstuck, e1 is a pack
      have ⟨hpack, hwf⟩ := h_nonstuck hQ1
      -- e1 is a pack, so we can use step_unpack
      cases hpack with
      | pack =>
        -- We need to show the variable is free
        rename_i cs x_var
        cases x_var with
        | bound idx => cases idx
        | free x =>
          exact IsProgressive.step Step.step_unpack
    | step hstep =>
      -- e1 can step, so unpack e1 e2 can step via step_ctx_unpack
      exact IsProgressive.step (Step.step_ctx_unpack hstep)
  | @eval_cond _ _ _ _ m0 x_guard hres _ _ _ _ =>
    -- e = .cond x_guard e2 e3; the guard resolves to a boolean (hres), so the
    -- conditional can step directly via step_cond_var_true/false.
    cases x_guard with
    | bound bx =>
      -- Impossible: we're in empty signature, no bound variables
      cases bx
    | free fx =>
      cases hres with
      | inl hbtrue =>
        cases hcell : m0.heap fx with
        | none =>
          simp [resolve, hcell] at hbtrue
        | some cell =>
          cases cell with
          | val hv =>
            cases hv with
            | mk unwrap hsimple reach =>
              have hunwrap : unwrap = .btrue := by
                simpa [resolve, hcell] using hbtrue
              cases hunwrap
              apply IsProgressive.step
              refine Step.step_cond_var_true (hv := hsimple) (R := reach) (by
                simp [Memory.lookup, hcell])
          | capability =>
            simp [resolve, hcell] at hbtrue
          | masked =>
            simp [resolve, hcell] at hbtrue
      | inr hbfalse =>
        cases hcell : m0.heap fx with
        | none =>
          simp [resolve, hcell] at hbfalse
        | some cell =>
          cases cell with
          | val hv =>
            cases hv with
            | mk unwrap hsimple reach =>
              have hunwrap : unwrap = .bfalse := by
                simpa [resolve, hcell] using hbfalse
              cases hunwrap
              apply IsProgressive.step
              refine Step.step_cond_var_false (hv := hsimple) (R := reach) (by
                simp [Memory.lookup, hcell])
          | capability =>
            simp [resolve, hcell] at hbfalse
          | masked =>
            simp [resolve, hcell] at hbfalse
  | eval_read _ hlookup_reader hlookup_cell _ =>
    -- e = .read (.free x), can step via step_read
    exact IsProgressive.step (Step.step_read hlookup_reader hlookup_cell)
  | eval_write_true _ hx hy _ =>
    -- e = .write (.free x) (.free y), can step via step_write_true
    exact IsProgressive.step (Step.step_write_true hx hy)
  | eval_write_false _ hx hy _ =>
    -- e = .write (.free x) (.free y), can step via step_write_false
    exact IsProgressive.step (Step.step_write_false hx hy)
  | eval_par _ _ _ _ _ _ =>
    -- e = .par e1 e2, can step via step_par_left
    exact IsProgressive.step Step.step_par_left

theorem step_preserves_eval
  (he : Eval C m1 e1 Q)
  (hcompat : m1.is_compatible C)
  (hstep : Step t m1 e1 m2 e2) :
  Eval C m2 e2 Q := by
  induction he generalizing m2 e2 with
  | eval_val hv hQ =>
    -- e1 is a value, which is an answer, but answers cannot step - contradiction
    have hans : Exp.IsAns _ := Exp.IsAns.is_val (Exp.isVal_of_isSimpleVal hv)
    exact absurd hstep (step_ans_absurd hans)
  | eval_var hQ =>
    -- e1 is a variable, which is an answer, but answers cannot step - contradiction
    rename_i x
    have hans : Exp.IsAns (.var x) := Exp.IsAns.is_var
    exact absurd hstep (step_ans_absurd hans)
  | eval_pack _ _ =>
    -- e1 = .pack cs x is a value; no step applies.
    cases hstep
  | eval_drop hx hQ _ =>
    -- e1 = .drop (.free x); the only step is step_drop, producing .unit at the
    -- dropped memory.  `drop_mcell` ignores its existence witness, so the step's
    -- memory and the eval's memory coincide definitionally, and `hQ` applies.
    cases hstep with
    | step_drop _ => exact Eval.eval_val Exp.IsSimpleVal.unit hQ
  | eval_alloc _ _ =>
    -- e1 = .alloc (.free x); the only step is step_alloc, producing the location
    -- pack `.pack {ε·l} l` at the extended memory.
    cases hstep with
    | step_alloc _ _ =>
      -- GENUINE GAP.  `Q` holds for the result pack (from `h_post`), but the only
      -- rule concluding `Eval _ _ (.pack …) _` is `eval_pack`, whose side
      -- condition `((.var (.M .epsilon) (.free l)).reachability m₂).to_drop ⊆ C`
      -- reduces to `{drop·l} ⊆ C`.  Here `l` is FRESHLY allocated (`m₁.heap l =
      -- none`), so `l ∉ C` for the universally-quantified ambient `C`, making the
      -- inclusion false.  Closing this requires `eval_alloc` (in BigStep) to
      -- thread the consumed-capability accounting so the new capability's drop is
      -- recorded in `C` — a metatheory/design change beyond this file.
      sorry
  | eval_apply hlookup heval ih =>
    -- e1 = .app (.free x) y
    -- The step must be step_apply or step_invoke
    -- Case analyze on the step
    cases hstep with
    | step_apply hlookup' =>
      -- Stepped to the substituted body
      -- Both lookups access the same location, so they return the same value
      rename_i cs1 T1 e_body1 hv1 R1 cs2 T2 e_body2 hv2 R2
      have heq := Memory.lookup_deterministic hlookup hlookup'
      -- Extract equality of abstraction bodies
      injection heq with heq_cell
      injection heq_cell with heq_val
      injection heq_val with heq_abs
      -- Name the unnamed equalities: reachability, signature, captures, type, body
      rename_i _ _ _ _ heq_body
      -- Rewrite using the body equality
      rw [←heq_body]
      -- Now we have the same expression that was already evaluated
      exact heval
    | step_invoke hlookup_x hlookup_y =>
      -- step_invoke says x contains a capability, but hlookup says x contains an abstraction
      -- This is a contradiction
      have heq := Memory.lookup_deterministic hlookup hlookup_x
      cases heq
  | eval_invoke hmem hlookup_x hlookup_y hQ =>
    -- e1 = .app (.free x) (.free y) where x contains a capability
    -- The step must be step_apply or step_invoke
    cases hstep with
    | step_apply hlookup' =>
      -- step_apply says x contains an abstraction, but hlookup_x says x contains a capability
      -- This is a contradiction
      have heq := Memory.lookup_deterministic hlookup_x hlookup'
      cases heq
    | step_invoke hlookup_x' hlookup_y' =>
      -- Stepped to .unit
      -- The postcondition holds by hQ
      exact Eval.eval_val Exp.IsSimpleVal.unit hQ
  | eval_tapply hlookup heval ih =>
    -- e1 = .tapp (.free x) S
    -- The only step is step_tapply
    cases hstep with
    | step_tapply hlookup' =>
      -- Stepped to the substituted body
      -- Both lookups access the same location, so they return the same value
      have heq := Memory.lookup_deterministic hlookup hlookup'
      -- Extract equality of type abstraction bodies
      injection heq with heq_cell
      injection heq_cell with heq_val
      injection heq_val with heq_abs
      -- Name the unnamed equalities
      rename_i _ _ _ _ heq_body
      -- Rewrite using the body equality
      rw [←heq_body]
      -- Now we have the same expression that was already evaluated
      exact heval
  | eval_capply hlookup heval ih =>
    -- e1 = .capp (.free x) CS
    -- The only step is step_capply
    cases hstep with
    | step_capply hlookup' =>
      -- Stepped to the substituted body
      -- Both lookups access the same location, so they return the same value
      have heq := Memory.lookup_deterministic hlookup hlookup'
      -- Extract equality of capability abstraction bodies
      injection heq with heq_cell
      injection heq_cell with heq_val
      injection heq_val with heq_abs
      -- Name the unnamed equalities
      rename_i _ _ _ _ heq_body
      -- Rewrite using the body equality
      rw [←heq_body]
      -- Now we have the same expression that was already evaluated
      exact heval
  | eval_wrap hQ =>
    cases hstep
  | eval_unwrap hlookup heval ih =>
    cases hstep with
    | step_unwrap hlookup' =>
      have heq := Memory.lookup_deterministic hlookup hlookup'
      cases heq
      exact heval
  | eval_letin hpred hbool heval_e1 h_nonstuck h_val h_var hseq hagg ih_e1 ih_val ih_var =>
    -- e1 = .letin e1' e2'
    -- Possible steps: step_ctx_letin, step_rename, step_lift
    cases hstep with
    | step_ctx_letin hstep_e1 =>
      -- e1' steps to some e1''; the IH needs compatibility for C1 (≤ Cagg).
      have hsub_C1 := CapabilitySet.Subset.trans CapabilitySet.Subset.union_right_left hagg
      have heval_e1'' := ih_e1 (Memory.is_compatible_subset hsub_C1 hcompat) hstep_e1
      -- Rebuild eval_letin with the new evaluation
      have hsub := step_memory_monotonic hstep_e1
      -- The handlers transport to the new memory; they now also receive and
      -- forward an `is_compatible C2` witness.
      apply Eval.eval_letin hpred hbool heval_e1'' h_nonstuck
      · -- h_val case
        intro m1 v hsub1 hcompat1 hv hwf_v hQ1 l' hfresh
        have hsub_full := Memory.subsumes_trans hsub1 hsub
        exact h_val hsub_full hcompat1 hv hwf_v hQ1 l' hfresh
      · -- h_var case
        intro m1 x hsub1 hcompat1 hwf_x hQ1
        have hsub_full := Memory.subsumes_trans hsub1 hsub
        exact h_var hsub_full hcompat1 hwf_x hQ1
      · -- sequencing/aggregation are capability-only, unchanged by the step
        exact hseq
      · exact hagg
    | step_rename =>
      -- e1' = .var (.free y), stepped to e2'.subst (openVar y).  Apply h_var at
      -- the current memory; compat for C2 follows from hcompat by antitonicity,
      -- and the result is boosted from C2 to Cagg.
      have hsub_C2 := CapabilitySet.Subset.trans CapabilitySet.Subset.union_right_right hagg
      have hQ1 := eval_ans_holds_post heval_e1 Exp.IsAns.is_var
      have ⟨_, hwf_y⟩ := h_nonstuck hQ1
      cases hwf_y with
      | wf_var hwf_y' =>
        exact eval_capability_set_monotonic
          (h_var (Memory.subsumes_refl _) (Memory.is_compatible_subset hsub_C2 hcompat) hwf_y' hQ1)
          hsub_C2
    | step_lift hv hwf_v hfresh =>
      -- e1' is a simple value, allocated at l.  Apply h_val at the current
      -- memory (compat for C2 by antitonicity), then boost from C2 to Cagg.
      have hsub_C2 := CapabilitySet.Subset.trans CapabilitySet.Subset.union_right_right hagg
      have hQ1 := eval_ans_holds_post heval_e1
        (Exp.IsAns.is_val (Exp.isVal_of_isSimpleVal hv))
      exact eval_capability_set_monotonic
        (h_val (Memory.subsumes_refl _) (Memory.is_compatible_subset hsub_C2 hcompat)
          hv hwf_v hQ1 _ hfresh)
        hsub_C2
  | eval_unpack hpred hbool heval_e1 h_nonstuck h_pack hseq hagg ih_e1 ih_pack =>
    -- e1 = .unpack e1' e2'
    -- Possible steps: step_ctx_unpack, step_unpack
    cases hstep with
    | step_ctx_unpack hstep_e1 =>
      -- e1' steps to some e1''; the IH needs compatibility for C1 (≤ Cagg).
      have hsub_C1 := CapabilitySet.Subset.trans CapabilitySet.Subset.union_right_left hagg
      have heval_e1'' := ih_e1 (Memory.is_compatible_subset hsub_C1 hcompat) hstep_e1
      -- Rebuild eval_unpack with the new evaluation
      have hsub := step_memory_monotonic hstep_e1
      apply Eval.eval_unpack hpred hbool heval_e1'' h_nonstuck
      · -- The pack handler transports to the new memory and forwards its
        -- `is_compatible (C2 ∪ R ∪ R.to_drop)` witness.
        intro m1 x cs hsub1 hcompat1 hwf_x hwf_cs hQ1
        have hsub_full := Memory.subsumes_trans hsub1 hsub
        exact h_pack hsub_full hcompat1 hwf_x hwf_cs hQ1
      · exact hseq
      · exact hagg
    | step_unpack =>
      -- e1' = .pack cs (.free x), stepped to e2'.subst (unpack cs x).
      -- GENUINE GAP.  The unpack handler `h_pack` yields the continuation at the
      -- *reachability-extended* capability set `C2 ∪ R ∪ R.to_drop`, where
      -- `R = cs.reachability m`.  But `step_preserves_eval` claims `Eval Cagg …`
      -- with the SAME `Cagg`, and `R ⊄ Cagg` in general (the unpack brings the
      -- packed capabilities into scope).  So same-`C` preservation is FALSE for
      -- the unpack step: the capability context legitimately grows here.  A
      -- faithful statement would let the post-step `C` vary; that is a change to
      -- the preservation theorem's interface, not a local repair.  (Even applying
      -- `h_pack` first needs `is_compatible (C2 ∪ R ∪ R.to_drop)`, i.e. the
      -- unpacked reachability being live — a soundness invariant of the logical
      -- relation, not available to syntactic preservation.)
      sorry
  | @eval_cond _ _ _ _ m_guard _ _ h_true h_false _ _ =>
    -- e1 = .cond x e2 e3; the guard is a variable, so it can only step via
    -- step_cond_var_true/false, after which `h_true`/`h_false` (which now take
    -- just the resolve fact) evaluate the chosen branch in the same memory.
    cases hstep with
    | step_cond_var_true hlookup =>
      -- The guard variable points to true; `resolve` follows from the lookup.
      simp only [Memory.lookup] at hlookup
      exact h_true (by simp only [resolve, hlookup])
    | step_cond_var_false hlookup =>
      -- The guard variable points to false; `resolve` follows from the lookup.
      simp only [Memory.lookup] at hlookup
      exact h_false (by simp only [resolve, hlookup])
  | eval_read hcov hlookup_reader hlookup_cell hQ =>
    -- e = .read (.free x), can only step via step_read
    cases hstep with
    | step_read hlookup_reader' hlookup_cell' =>
      -- The step produces the same boolean value as the evaluation (lookups agree).
      have heq_reader := Memory.lookup_deterministic hlookup_reader hlookup_reader'
      cases heq_reader
      have heq_cell := Memory.lookup_deterministic hlookup_cell hlookup_cell'
      cases heq_cell
      -- The result `if b then .btrue else .bfalse` is a simple value either way.
      exact Eval.eval_val (by split <;> constructor) hQ
  | eval_write_true _ hx hy hQ =>
    -- e = .write (.free x) (.free y), can only step via step_write_true or step_write_false
    cases hstep with
    | step_write_true hx' hy' =>
      -- Both lookups agree, so the memories are definitionally equal
      -- The result is unit, which is a value
      exact Eval.eval_val Exp.IsSimpleVal.unit hQ
    | step_write_false hx' hy' =>
      -- y is looked up as btrue in eval, but bfalse in step - contradiction
      have heq_y := Memory.lookup_deterministic hy hy'
      -- The cells must be equal
      injection heq_y with heq_val
      -- The ValPairs must be equal, extract unwrap field
      have h_unwrap : Exp.btrue = Exp.bfalse := congrArg (·.unwrap) heq_val
      cases h_unwrap
  | eval_write_false _ hx hy hQ =>
    -- e = .write (.free x) (.free y), can only step via step_write_false
    cases hstep with
    | step_write_true hx' hy' =>
      -- y is looked up as bfalse in eval, but btrue in step - contradiction
      have heq_y := Memory.lookup_deterministic hy hy'
      -- The cells must be equal
      injection heq_y with heq_val
      -- The ValPairs must be equal, extract unwrap field
      have h_unwrap : Exp.bfalse = Exp.btrue := congrArg (·.unwrap) heq_val
      cases h_unwrap
    | step_write_false hx' hy' =>
      -- Both lookups agree, so the memories are definitionally equal
      -- The result is unit, which is a value
      exact Eval.eval_val Exp.IsSimpleVal.unit hQ
  | eval_par heval1 heval2 _ hsub_cap ih1 ih2 =>
    -- e = .par e1 e2
    -- The step can be step_par_left or step_par_right
    -- hsub_cap : C1 ∪ C2 ⊆ C'
    cases hstep with
    | step_par_left =>
      -- Stepped to e1, need to boost from C1 to C'
      have h1 := CapabilitySet.Subset.trans CapabilitySet.Subset.union_right_left hsub_cap
      exact eval_capability_set_monotonic heval1 h1
    | step_par_right =>
      -- Stepped to e2, need to boost from C2 to C'
      have h2 := CapabilitySet.Subset.trans CapabilitySet.Subset.union_right_right hsub_cap
      exact eval_capability_set_monotonic heval2 h2

/-- A single step preserves memory–capability compatibility, EXCEPT when it
    drops an in-scope capability (see the `step_drop` gap below). -/
theorem step_preserves_compatible
  (hcompat : m1.is_compatible C)
  (hstep : Step t m1 e1 m2 e2) :
  m2.is_compatible C := by
  induction hstep with
  | step_apply | step_invoke | step_tapply | step_capply | step_unwrap
  | step_cond_var_true _ | step_cond_var_false _ | step_read _ _
  | step_rename | step_unpack | step_par_left | step_par_right =>
    -- Memory is unchanged by these steps.
    exact hcompat
  | step_write_true hx _ | step_write_false hx _ =>
    -- The cell is rewritten to a *live* mcell, preserving compatibility.
    exact Memory.is_compatible_update_mcell _ _ _ ⟨_, hx⟩ hcompat
  | step_alloc _ hfresh =>
    -- A fresh *live* mcell is added; compatibility is preserved.
    exact Memory.is_compatible_extend_mcell _ _ _ hfresh hcompat
  | step_lift hv hwf hfresh =>
    -- A fresh value cell is added (extend = extend_val on the heap).
    exact Memory.is_compatible_extend_val _ _ _ hwf rfl hfresh hcompat
  | step_drop hx =>
    -- GENUINE GAP.  step_drop turns the mcell at x DEAD.  If x ∈ C, then
    -- `is_compatible C` (which demands every mcell in C be live) is FALSIFIED by
    -- the drop.  Compatibility is not preserved by drops of in-scope
    -- capabilities — it is a soundness invariant the logical relation maintains
    -- (a well-typed program only drops capabilities it is relinquishing from its
    -- authority), not a syntactic consequence of an isolated drop step.
    sorry
  | step_ctx_letin _ ih | step_ctx_unpack _ ih => exact ih hcompat

theorem reduce_preserves_eval
  (he : Eval C m1 e1 Q)
  (hcompat : m1.is_compatible C)
  (hred : Reduce t m1 e1 m2 e2) :
  Eval C m2 e2 Q := by
  induction hred with
  | refl =>
    -- No reduction, so evaluation remains the same
    exact he
  | step hstep rest ih =>
    -- Preserve both the evaluation and the compatibility witness across the step.
    exact ih (step_preserves_eval he hcompat hstep) (step_preserves_compatible hcompat hstep)

theorem eval_to_reduce
  (heval : Eval C m1 e1 Q)
  (hcompat : m1.is_compatible C)
  (_hwf : e1.WfInHeap m1.heap) :
  ∀ m2 e2 t,
    e2.IsAns ->
    Reduce t m1 e1 m2 e2 ->
    Q e2 m2 := by
  intro m2 e2 t hans hred
  -- Reductions preserve evaluations, then any answer satisfies its postcondition.
  have heval' : Eval C m2 e2 Q := reduce_preserves_eval heval hcompat hred
  exact eval_ans_holds_post heval' hans

-- NOTE: `Heap/Memory.masked_update_mcell_comm`, `step_masked`, and `reduce_masked`
-- have been removed.  They expressed "a step under capability `C` stays within the
-- memory masked to `C.to_finset`", which depended entirely on the `covers`
-- premises that the trace-indexed `Step` no longer carries (and used the old
-- liveness-free `.mcell b` API).  With `Step` recording — rather than bounding —
-- accesses, there is no capability-relative masking invariant to state here.

/-- If `Eval C m e Q` holds and `m` is compatible with `C`, then there exist `m'`
    and `e'` such that `e'` is an answer, `m'` subsumes `m`, and `Q e' m'`. -/
theorem eval_exists_answer
  (heval : Eval C m e Q)
  (hcompat : m.is_compatible C) :
  ∃ m' e', e'.IsAns ∧ m'.subsumes m ∧ Q e' m' := by
  induction heval with
  | eval_val hv hQ =>
    exact ⟨_, _, Exp.IsAns.is_val (Exp.isVal_of_isSimpleVal hv), Memory.subsumes_refl _, hQ⟩
  | eval_var hQ =>
    exact ⟨_, _, Exp.IsAns.is_var, Memory.subsumes_refl _, hQ⟩
  | eval_pack _ hQ =>
    exact ⟨_, _, Exp.IsAns.is_val Exp.IsVal.pack, Memory.subsumes_refl _, hQ⟩
  | eval_alloc _ h_post =>
    obtain ⟨l, hfresh⟩ := Memory.exists_fresh _
    exact ⟨_, _, Exp.IsAns.is_val Exp.IsVal.pack,
           Memory.extend_mcell_subsumes _ _ _ hfresh, h_post l hfresh⟩
  | eval_drop hx hQ _ =>
    exact ⟨_, _, Exp.IsAns.is_val Exp.IsVal.unit,
           Memory.drop_mcell_subsumes _ _ ⟨_, hx⟩, hQ⟩
  | eval_apply _ _ ih => exact ih hcompat
  | eval_invoke _ _ _ hQ =>
    exact ⟨_, _, Exp.IsAns.is_val Exp.IsVal.unit, Memory.subsumes_refl _, hQ⟩
  | eval_tapply _ _ ih => exact ih hcompat
  | eval_capply _ _ ih => exact ih hcompat
  | eval_wrap hQ =>
    exact ⟨_, _, Exp.IsAns.is_val Exp.IsVal.boxed, Memory.subsumes_refl _, hQ⟩
  | eval_unwrap _ _ ih => exact ih hcompat
  | eval_letin hpred hbool eval_e1 h_nonstuck h_val h_var hseq hagg ih_e1 ih_val ih_var =>
    -- GENUINE GAP.  `e1` evaluates to an answer at some `m1'` (provable via `ih_e1`
    -- at compatibility for `C1 ≤ Cagg`), but CONTINUING past it needs
    -- `m1'.is_compatible C2`.  Compatibility is NOT preserved across the
    -- subsumption `m1'.subsumes m` induced by reducing `e1` (subsumption admits a
    -- live mcell evolving to dead), and is re-established only by the logical
    -- relation's soundness invariant — unavailable to this operational argument.
    sorry
  | eval_unpack hpred hbool eval_e1 h_nonstuck h_val hseq hagg ih_e1 ih_val =>
    -- GENUINE GAP.  As `eval_letin`, the continuation additionally needs
    -- compatibility at the reachability-extended set `C2 ∪ R ∪ R.to_drop`.
    sorry
  | eval_read _ _ _ hQ =>
    exact ⟨_, _, Exp.IsAns.is_val (by split <;> constructor), Memory.subsumes_refl _, hQ⟩
  | eval_write_true _ hx _ hQ =>
    exact ⟨_, _, Exp.IsAns.is_val Exp.IsVal.unit,
           Memory.update_mcell_subsumes _ _ _ _ ⟨_, hx⟩, hQ⟩
  | eval_write_false _ hx _ hQ =>
    exact ⟨_, _, Exp.IsAns.is_val Exp.IsVal.unit,
           Memory.update_mcell_subsumes _ _ _ _ ⟨_, hx⟩, hQ⟩
  | @eval_cond _ _ _ _ _ _ hres _ _ ih_true ih_false =>
    -- The guard resolves to a boolean; the chosen branch evaluates at the same
    -- memory, so its IH applies with the ambient compatibility witness.
    cases hres with
    | inl hbtrue => exact ih_true hbtrue hcompat
    | inr hbfalse => exact ih_false hbfalse hcompat
  | eval_par _ _ _ hsub_cap ih1 _ =>
    -- Use the left branch; its IH needs compatibility for C1 (≤ C').
    exact ih1 (Memory.is_compatible_subset
      (CapabilitySet.Subset.trans CapabilitySet.Subset.union_right_left hsub_cap) hcompat)

/-- If `Eval C m1 e1 Q` holds and `m1` is compatible with `C`, then `e1` reduces
    (emitting some trace) to an answer `e2` at `m2` with `Q e2 m2`. -/
theorem eval_reduce_exists_answer
  (heval : Eval C m1 e1 Q)
  (hcompat : m1.is_compatible C) :
  ∃ m2 e2 t, Reduce t m1 e1 m2 e2 ∧ e2.IsAns ∧ Q e2 m2 := by
  induction heval with
  | eval_val hv hQ =>
    exact ⟨_, _, _, Reduce.refl, Exp.IsAns.is_val (Exp.isVal_of_isSimpleVal hv), hQ⟩
  | eval_var hQ =>
    exact ⟨_, _, _, Reduce.refl, Exp.IsAns.is_var, hQ⟩
  | eval_pack _ hQ =>
    exact ⟨_, _, _, Reduce.refl, Exp.IsAns.is_val Exp.IsVal.pack, hQ⟩
  | eval_alloc hlookup h_post =>
    obtain ⟨l, hfresh⟩ := Memory.exists_fresh _
    exact ⟨_, _, _, Reduce.step (Step.step_alloc (l := l) hlookup hfresh) Reduce.refl,
           Exp.IsAns.is_val Exp.IsVal.pack, h_post l hfresh⟩
  | eval_drop hx hQ _ =>
    exact ⟨_, _, _, Reduce.step (Step.step_drop hx) Reduce.refl,
           Exp.IsAns.is_val Exp.IsVal.unit, hQ⟩
  | eval_apply hlookup _ ih =>
    obtain ⟨m2, e2, t, hred, hans, hQ⟩ := ih hcompat
    rename_i y _ _ _ _
    cases y with
    | bound idx => cases idx
    | free fy =>
      exact ⟨m2, e2, _, Reduce.step (Step.step_apply hlookup) hred, hans, hQ⟩
  | eval_invoke _ hlookup_x hlookup_y hQ =>
    exact ⟨_, _, _, Reduce.step (Step.step_invoke hlookup_x hlookup_y) Reduce.refl,
           Exp.IsAns.is_val Exp.IsVal.unit, hQ⟩
  | eval_tapply hlookup _ ih =>
    obtain ⟨m2, e2, t, hred, hans, hQ⟩ := ih hcompat
    exact ⟨m2, e2, _, Reduce.step (Step.step_tapply hlookup) hred, hans, hQ⟩
  | eval_capply hlookup _ ih =>
    obtain ⟨m2, e2, t, hred, hans, hQ⟩ := ih hcompat
    exact ⟨m2, e2, _, Reduce.step (Step.step_capply hlookup) hred, hans, hQ⟩
  | eval_wrap hQ =>
    exact ⟨_, _, _, Reduce.refl, Exp.IsAns.is_val Exp.IsVal.boxed, hQ⟩
  | eval_unwrap hlookup _ ih =>
    obtain ⟨m2, e2, t, hred, hans, hQ⟩ := ih hcompat
    exact ⟨m2, e2, _, Reduce.step (Step.step_unwrap hlookup) hred, hans, hQ⟩
  | eval_letin hpred hbool eval_e1 h_nonstuck h_val h_var hseq hagg ih_e1 ih_val ih_var =>
    -- GENUINE GAP (same as `eval_exists_answer`): continuing past `e1` needs
    -- `is_compatible C2` at the post-`e1` memory, not preserved across the
    -- subsumption induced by reducing `e1` (live mcells may go dead).
    sorry
  | eval_unpack hpred hbool eval_e1 h_nonstuck h_val hseq hagg ih_e1 ih_val =>
    -- GENUINE GAP: as `eval_letin`, plus the continuation set is the
    -- reachability-extended `C2 ∪ R ∪ R.to_drop`.
    sorry
  | eval_read _ hlookup_reader hlookup_cell hQ =>
    exact ⟨_, _, _, Reduce.step (Step.step_read hlookup_reader hlookup_cell) Reduce.refl,
           Exp.IsAns.is_val (by split <;> constructor), hQ⟩
  | eval_write_true _ hx hy hQ =>
    exact ⟨_, _, _, Reduce.step (Step.step_write_true hx hy) Reduce.refl,
           Exp.IsAns.is_val Exp.IsVal.unit, hQ⟩
  | eval_write_false _ hx hy hQ =>
    exact ⟨_, _, _, Reduce.step (Step.step_write_false hx hy) Reduce.refl,
           Exp.IsAns.is_val Exp.IsVal.unit, hQ⟩
  | @eval_cond _ _ _ _ m_guard x_guard hres _ _ ih_true ih_false =>
    -- The guard is a variable resolving to a boolean; derive its value lookup
    -- from `resolve`, step into the chosen branch, and continue via its IH.
    cases x_guard with
    | bound idx => cases idx
    | free fx =>
      cases hres with
      | inl hbtrue =>
        cases hcell : m_guard.heap fx with
        | none => simp [resolve, hcell] at hbtrue
        | some cell =>
          cases cell with
          | capability => simp [resolve, hcell] at hbtrue
          | masked => simp [resolve, hcell] at hbtrue
          | val hv =>
            have hunwrap : hv.unwrap = .btrue := by simpa [resolve, hcell] using hbtrue
            obtain ⟨unwrap, isVal, reachability⟩ := hv
            simp only at hunwrap
            subst hunwrap
            have hlookup : m_guard.lookup fx = some (.val ⟨.btrue, isVal, reachability⟩) := by
              simp only [Memory.lookup, hcell]
            obtain ⟨m2, e2, t, hred2, hans2, hQ2⟩ := ih_true hbtrue hcompat
            exact ⟨m2, e2, _, Reduce.step (Step.step_cond_var_true hlookup) hred2, hans2, hQ2⟩
      | inr hbfalse =>
        cases hcell : m_guard.heap fx with
        | none => simp [resolve, hcell] at hbfalse
        | some cell =>
          cases cell with
          | capability => simp [resolve, hcell] at hbfalse
          | masked => simp [resolve, hcell] at hbfalse
          | val hv =>
            have hunwrap : hv.unwrap = .bfalse := by simpa [resolve, hcell] using hbfalse
            obtain ⟨unwrap, isVal, reachability⟩ := hv
            simp only at hunwrap
            subst hunwrap
            have hlookup : m_guard.lookup fx = some (.val ⟨.bfalse, isVal, reachability⟩) := by
              simp only [Memory.lookup, hcell]
            obtain ⟨m2, e2, t, hred2, hans2, hQ2⟩ := ih_false hbfalse hcompat
            exact ⟨m2, e2, _, Reduce.step (Step.step_cond_var_false hlookup) hred2, hans2, hQ2⟩
  | eval_par _ _ _ hsub_cap ih1 _ =>
    -- Use the left branch; its IH needs compatibility for C1 (≤ C').  No
    -- capability boost is needed any more — the reduction carries its own trace.
    obtain ⟨m2, e2, t, hred, hans, hQ⟩ := ih1 (Memory.is_compatible_subset
      (CapabilitySet.Subset.trans CapabilitySet.Subset.union_right_left hsub_cap) hcompat)
    exact ⟨m2, e2, _, Reduce.step Step.step_par_left hred, hans, hQ⟩

theorem not_mutated_refl {m : Memory} : m.not_mutated m := fun _ _ _ hinit => hinit

theorem not_mutated_trans {m1 m2 m3 : Memory}
    (h12 : m1.not_mutated m2) (h23 : m2.not_mutated m3) :
    m1.not_mutated m3 := fun l b ℓ hinit => h23 l b ℓ (h12 l b ℓ hinit)

/-- A single step whose trace contains no write (`access .epsilon`) and no
    deallocation event does not mutate any mutable cell.  This is the trace-based
    replacement for the old `HasKind .ro → not_mutated`: read-only authority now
    manifests operationally as a write/dealloc-free trace, rather than as a
    capability-set side condition the (former, capability-indexed) `Step` carried. -/
theorem step_immutable
  (hwr : ∀ l, TraceItem.access .epsilon l ∉ t)
  (hdr : ∀ l, TraceItem.dealloc l ∉ t)
  (hstep : Step t m1 e1 m2 e2) :
  m1.not_mutated m2 := by
  intro l b ℓ hinit
  induction hstep with
  | step_apply | step_invoke | step_tapply | step_capply | step_unwrap
  | step_cond_var_true _ | step_cond_var_false _ | step_read _ _
  | step_rename | step_unpack | step_par_left | step_par_right =>
    -- Memory is unchanged.
    exact hinit
  | step_write_true _ _ | step_write_false _ _ =>
    -- The trace is `[access .epsilon x]`, excluded by `hwr`.
    exact absurd (List.mem_singleton.mpr rfl) (hwr _)
  | step_drop _ =>
    -- The trace is `[dealloc x]`, excluded by `hdr`.
    exact absurd (List.mem_singleton.mpr rfl) (hdr _)
  | step_alloc _ hfresh =>
    -- A fresh mcell is added at the fresh location; the queried cell (which is
    -- allocated, by hinit) is therefore distinct and untouched.
    simp only [Memory.extend_mcell, Heap.extend_mcell]
    split
    · rename_i heq; rw [heq, hfresh] at hinit; cases hinit
    · exact hinit
  | step_lift hv hwf hfresh =>
    -- A fresh value cell is added; the queried (allocated) cell is untouched.
    simp only [Memory.extend, Heap.extend]
    split
    · rename_i heq; rw [heq, hfresh] at hinit; cases hinit
    · exact hinit
  | step_ctx_letin _ ih | step_ctx_unpack _ ih => exact ih hwr hdr hinit

/-- A whole reduction whose (accumulated) trace contains no write or deallocation
    event does not mutate memory. -/
theorem reduce_immutable
    (hwr : ∀ l, TraceItem.access .epsilon l ∉ t)
    (hdr : ∀ l, TraceItem.dealloc l ∉ t)
    (hred : Reduce t m1 e1 m2 e2) :
    m1.not_mutated m2 := by
  induction hred with
  | refl => exact not_mutated_refl
  | step hstep rest ih =>
    -- The trace splits as t1 ++ t2; neither half can contain a write/dealloc.
    exact not_mutated_trans
      (step_immutable (fun l hm => hwr l (List.mem_append_left _ hm))
        (fun l hm => hdr l (List.mem_append_left _ hm)) hstep)
      (ih (fun l hm => hwr l (List.mem_append_right _ hm))
        (fun l hm => hdr l (List.mem_append_right _ hm)))

end CoreCapybara
