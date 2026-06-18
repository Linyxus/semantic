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

/-- Congruence: a reduction of the LEFT branch lifts to a reduction of the whole
  `par` (the right branch frozen).  A plain fold of `step_par_left`. -/
theorem reduce_par_left {C : Trace} {m m' : Memory} {e1 e1' e2 : Exp {}}
  (hred : Reduce C m e1 m' e1') :
  Reduce C m (.par e1 e2) m' (.par e1' e2) := by
  induction hred with
  | refl => exact Reduce.refl
  | step h _ ih => exact Reduce.step (Step.step_par_left h) ih

/-- Congruence: a reduction of the RIGHT branch lifts (the left branch frozen). -/
theorem reduce_par_right {C : Trace} {m m' : Memory} {e1 e2 e2' : Exp {}}
  (hred : Reduce C m e2 m' e2') :
  Reduce C m (.par e1 e2) m' (.par e1 e2') := by
  induction hred with
  | refl => exact Reduce.refl
  | step h _ ih => exact Reduce.step (Step.step_par_right h) ih

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
  | step_rename | step_unpack | step_par_join _ _ =>
    exact Memory.subsumes_refl _
  | step_par_left _ ih | step_par_right _ ih => exact ih
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
  -- Congruence preserves WF: the stepped branch via the (structural) recursive
  -- call, the untouched branch via monotonicity.  WF is structural, so — unlike
  -- the operational preservation lemmas — par needs no separation here.
  | step_par_left hsub_step =>
    cases hwf with
    | wf_par hwf_aL hwf_b =>
      exact Exp.WfInHeap.wf_par (step_preserves_wf hsub_step hwf_aL)
        (Exp.wf_monotonic (step_memory_monotonic hsub_step) hwf_b)
  | step_par_right hsub_step =>
    cases hwf with
    | wf_par hwf_aL hwf_b =>
      exact Exp.WfInHeap.wf_par (Exp.wf_monotonic (step_memory_monotonic hsub_step) hwf_aL)
        (step_preserves_wf hsub_step hwf_b)
  | step_par_join _ _ =>
    -- The join retires `par` to the canonical `.unit`, trivially well-formed.
    exact Exp.WfInHeap.wf_unit

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

-- Progress predicate (Route B): an expression is *progressive* in memory `m` if
-- it is already an answer, or it can take at least one small `Step`.  The old
-- capability-set index is gone — `Step`/`Eval` are now trace-indexed, with no
-- ambient authority to parameterize over; the `step` witness's trace is hidden
-- existentially (progress only asserts that *some* step exists).
inductive IsProgressive : Memory -> Exp {} -> Prop where
| done :
  e.IsAns ->
  IsProgressive m e
| step :
  Step t m e m' e' ->
  IsProgressive m e

/-- If an answer has an evaluation, then the postcondition holds for it with the
    empty trace.  An answer `BigStep`s only to itself emitting no events, so the
    bundled preservation half of `Eval` applies to that trivial run. -/
theorem eval_ans_holds_post {m : Memory} {e : Exp {}} {Q : Tpost}
  (heval : Eval m e Q)
  (hans : e.IsAns) :
  Q [] e m :=
  heval.2 _ _ _ (BigStep.of_isAns hans)

/-- A variable in the empty signature is always free (no bound variables exist). -/
theorem Var.free_cases {k : Kind} (x : Var k {}) : ∃ n, x = .free n := by
  cases x with
  | bound b => cases b
  | free n => exact ⟨n, rfl⟩

/-- A simple answer is either a simple value or a free variable. -/
theorem Exp.isSimpleAns_cases {e : Exp {}} (h : e.IsSimpleAns) :
    e.IsSimpleVal ∨ ∃ n, e = .var (.free n) := by
  cases h with
  | is_simple_val hv => exact Or.inl hv
  | is_var =>
    rename_i x
    obtain ⟨n, rfl⟩ := Var.free_cases x
    exact Or.inr ⟨n, rfl⟩

/-- A pack answer in the empty signature has a free witness variable. -/
theorem Exp.isPack_cases {e : Exp {}} (h : e.IsPack) :
    ∃ cs n, e = .pack cs (.free n) := by
  cases h with
  | pack =>
    rename_i cs x
    obtain ⟨n, rfl⟩ := Var.free_cases x
    exact ⟨cs, n, rfl⟩

/-- **Progress (small-step).**  A `Safe` configuration is *progressive*: it is
    already an answer, or it can take a small `Step`.  The recursion mirrors the
    `Safe` derivation; for `letin`/`unpack` the head's progress (`ih_e1`) is used,
    and when the head is already an answer, `h_ans` (applied to the trivial
    self-run `BigStep.of_isAns`) classifies it as a simple value or variable so
    that `step_lift`/`step_rename`/`step_unpack` fire. -/
theorem safe_implies_progressive {m : Memory} {e : Exp {}}
  (h : Safe m e) :
  IsProgressive m e := by
  induction h with
  | ans hans => exact IsProgressive.done hans
  | alloc hlookup =>
    -- e = .alloc (.free x); steps via step_alloc to a fresh live mcell
    obtain ⟨l, hfresh⟩ := Memory.exists_fresh _
    exact IsProgressive.step (Step.step_alloc (l := l) hlookup hfresh)
  | drop hx =>
    -- e = .drop (.free x); steps via step_drop
    exact IsProgressive.step (Step.step_drop hx)
  | @apply cs T e_abs hv R y m x hlookup _ _ =>
    -- e = .app (.free x) y; y is free (empty signature), so step_apply applies
    obtain ⟨y', rfl⟩ := Var.free_cases y
    exact IsProgressive.step (Step.step_apply hlookup)
  | invoke hlookup_x hlookup_y =>
    exact IsProgressive.step (Step.step_invoke hlookup_x hlookup_y)
  | tapply hlookup _ _ =>
    exact IsProgressive.step (Step.step_tapply hlookup)
  | capply hlookup _ _ =>
    exact IsProgressive.step (Step.step_capply hlookup)
  | unwrap hlookup _ _ =>
    exact IsProgressive.step (Step.step_unwrap hlookup)
  | letin _ h_ans _ _ ih_e1 _ _ =>
    -- e = .letin e1 e2; by `ih_e1`, e1 is progressive
    cases ih_e1 with
    | done hans =>
      -- e1 is an answer: classify it via h_ans on the trivial self-run
      obtain ⟨hsimple_ans, hwf⟩ := h_ans _ _ _ (BigStep.of_isAns hans)
      rcases Exp.isSimpleAns_cases hsimple_ans with hv | ⟨n, rfl⟩
      · -- e1 is a simple value: step_lift to a fresh location (heap is finite)
        obtain ⟨l0, hfresh⟩ := Memory.exists_fresh _
        exact IsProgressive.step (Step.step_lift (l := l0) hv hwf hfresh)
      · -- e1 is a free variable: step_rename
        exact IsProgressive.step Step.step_rename
    | step hstep =>
      -- e1 can step, so letin e1 e2 steps via step_ctx_letin
      exact IsProgressive.step (Step.step_ctx_letin hstep)
  | unpack _ h_ans _ ih_e1 _ =>
    -- e = .unpack e1 e2; by `ih_e1`, e1 is progressive
    cases ih_e1 with
    | done hans =>
      -- e1 is an answer: classify it as a pack with a free witness via h_ans
      obtain ⟨hpack, hwf⟩ := h_ans _ _ _ (BigStep.of_isAns hans)
      obtain ⟨cs, n, rfl⟩ := Exp.isPack_cases hpack
      exact IsProgressive.step Step.step_unpack
    | step hstep =>
      -- e1 can step, so unpack e1 e2 steps via step_ctx_unpack
      exact IsProgressive.step (Step.step_ctx_unpack hstep)
  | @cond e2 e3 m x hres _ _ _ _ =>
    -- e = .cond x e2 e3; the guard resolves to a boolean (hres), so the
    -- conditional can step directly via step_cond_var_true/false.
    obtain ⟨fx, rfl⟩ := Var.free_cases x
    cases hres with
    | inl hbtrue =>
      cases hcell : m.heap fx with
      | none => simp [resolve, hcell] at hbtrue
      | some cell =>
        cases cell with
        | val hv =>
          cases hv with
          | mk unwrap hsimple reach =>
            have hunwrap : unwrap = .btrue := by simpa [resolve, hcell] using hbtrue
            cases hunwrap
            exact IsProgressive.step
              (Step.step_cond_var_true (hv := hsimple) (R := reach)
                (by simp [Memory.lookup, hcell]))
        | capability => simp [resolve, hcell] at hbtrue
        | masked => simp [resolve, hcell] at hbtrue
    | inr hbfalse =>
      cases hcell : m.heap fx with
      | none => simp [resolve, hcell] at hbfalse
      | some cell =>
        cases cell with
        | val hv =>
          cases hv with
          | mk unwrap hsimple reach =>
            have hunwrap : unwrap = .bfalse := by simpa [resolve, hcell] using hbfalse
            cases hunwrap
            exact IsProgressive.step
              (Step.step_cond_var_false (hv := hsimple) (R := reach)
                (by simp [Memory.lookup, hcell]))
        | capability => simp [resolve, hcell] at hbfalse
        | masked => simp [resolve, hcell] at hbfalse
  | read hlookup_reader hlookup_cell =>
    -- e = .read (.free x), can step via step_read
    exact IsProgressive.step (Step.step_read hlookup_reader hlookup_cell)
  | write_true hx hy =>
    -- e = .write (.free x) (.free y), can step via step_write_true
    exact IsProgressive.step (Step.step_write_true hx hy)
  | write_false hx hy =>
    -- e = .write (.free x) (.free y), can step via step_write_false
    exact IsProgressive.step (Step.step_write_false hx hy)
  | par _ h2 ih1 ih2 =>
    -- Progress for interleaving `par`: step whichever branch is not yet an answer
    -- (congruence), or join once both are.  Fully provable — progress only needs
    -- SOME step to exist, and the sequential schedule (advance the left branch, then
    -- the right, then join) always supplies one.
    cases ih1 with
    | done hAans =>
      cases ih2 (BigStep.of_isAns hAans) with
      | done hBans => exact IsProgressive.step (Step.step_par_join hAans hBans)
      | step hstepB => exact IsProgressive.step (Step.step_par_right hstepB)
    | step hstepA => exact IsProgressive.step (Step.step_par_left hstepA)

/-- An `Eval` is progressive: its bundled `Safe` half gives small-step progress. -/
theorem eval_implies_progressive {m : Memory} {e : Exp {}} {Q : Tpost}
  (heval : Eval m e Q) :
  IsProgressive m e :=
  safe_implies_progressive heval.1

/- ============================================================================
   SMALL-STEP ↔ BIG-STEP BRIDGE (Route B).  The new `Eval := Safe ∧ preservation`
   is phrased over the relational `BigStep`.  These lemmas connect it to the
   small-step `Step`/`Reduce`, so the small-step preservation/progress results
   (consumed by `Safety`) go through.  The keystone is *head expansion*:
   prepending a `Step` to a `BigStep` run is again a `BigStep` run.
   ============================================================================ -/

/-- **Head expansion.**  A small `Step` prefixed to a `BigStep` run is itself a
    `BigStep` run, with the step's trace prepended.  Read-nondeterminism is no
    obstacle: the faithful `step_read` bit is one admissible `bs_read` outcome
    (`b' = b`), and `step_par_*` matches `bs_par_*`.  The `letin`/`unpack`
    congruence steps recurse through the inductive hypothesis. -/
theorem BigStep.head_expand {t : Trace} {m1 e1 m2 e2 : _}
    (hstep : Step t m1 e1 m2 e2) :
    ∀ {t' : Trace} {v : Exp {}} {m' : Memory},
      BigStep m2 e2 t' v m' → BigStep m1 e1 (t ++ t') v m' := by
  induction hstep with
  | step_apply hlk => intro t' v m' hbs; exact BigStep.bs_apply hlk hbs
  | step_invoke hlkx hlky =>
    intro t' v m' hbs
    obtain ⟨rfl, rfl, rfl⟩ := BigStep.simpleVal_eq Exp.IsSimpleVal.unit hbs
    exact BigStep.bs_invoke hlkx hlky
  | step_tapply hlk => intro t' v m' hbs; exact BigStep.bs_tapply hlk hbs
  | step_capply hlk => intro t' v m' hbs; exact BigStep.bs_capply hlk hbs
  | step_unwrap hlk => intro t' v m' hbs; exact BigStep.bs_unwrap hlk hbs
  | step_cond_var_true hlk =>
    intro t' v m' hbs
    simp only [Memory.lookup] at hlk
    exact BigStep.bs_cond_true (by simp only [resolve, hlk]) hbs
  | step_cond_var_false hlk =>
    intro t' v m' hbs
    simp only [Memory.lookup] at hlk
    exact BigStep.bs_cond_false (by simp only [resolve, hlk]) hbs
  | step_read hlkx hlky =>
    intro t' v m' hbs
    obtain ⟨rfl, rfl, rfl⟩ := BigStep.simpleVal_eq (by split <;> constructor) hbs
    exact BigStep.bs_read hlkx hlky
  | step_write_true hx hy =>
    intro t' v m' hbs
    obtain ⟨rfl, rfl, rfl⟩ := BigStep.simpleVal_eq Exp.IsSimpleVal.unit hbs
    exact BigStep.bs_write_true hx hy
  | step_write_false hx hy =>
    intro t' v m' hbs
    obtain ⟨rfl, rfl, rfl⟩ := BigStep.simpleVal_eq Exp.IsSimpleVal.unit hbs
    exact BigStep.bs_write_false hx hy
  | step_alloc hlk hfresh =>
    intro t' v m' hbs
    cases hbs with
    | bs_pack => exact BigStep.bs_alloc hlk hfresh
    | bs_val hv => cases hv
  | step_drop hx =>
    intro t' v m' hbs
    obtain ⟨rfl, rfl, rfl⟩ := BigStep.simpleVal_eq Exp.IsSimpleVal.unit hbs
    exact BigStep.bs_drop hx
  | step_ctx_letin _ ih =>
    intro t' v m' hbs
    cases hbs with
    | bs_letin_val hrun hv hwf hfresh hrun2 =>
      rw [← List.append_assoc]; exact BigStep.bs_letin_val (ih hrun) hv hwf hfresh hrun2
    | bs_letin_var hrun hrun2 =>
      rw [← List.append_assoc]; exact BigStep.bs_letin_var (ih hrun) hrun2
    | bs_val hv => cases hv
  | step_ctx_unpack _ ih =>
    intro t' v m' hbs
    cases hbs with
    | bs_unpack hrun hrun2 =>
      rw [← List.append_assoc]; exact BigStep.bs_unpack (ih hrun) hrun2
    | bs_val hv => cases hv
  | step_par_left _ ih =>
    -- A LEFT-branch step is ALIGNED with the sequential schedule (`bs_par` runs the
    -- left branch first), so head-expansion threads through the IH, exactly as for
    -- `step_ctx_letin`.
    intro t' v m' hbs
    cases hbs with
    | bs_par hrunL hrunR =>
      rw [← List.append_assoc]; exact BigStep.bs_par (ih hrunL) hrunR
    | bs_val hv => cases hv
  | step_par_join hans_a hans_b =>
    -- `par a b → .unit` (both answers); the reduct `.unit` self-runs trivially, and
    -- `bs_par` over the two answers' (empty) self-runs rebuilds the original.
    intro t' v m' hbs
    obtain ⟨rfl, rfl, rfl⟩ := BigStep.simpleVal_eq Exp.IsSimpleVal.unit hbs
    exact BigStep.bs_par (BigStep.of_isAns hans_a) (BigStep.of_isAns hans_b)
  | step_par_right _ _ =>
    -- GENUINE DESIGN GAP (interleaving ⊥ the raw sequential `BigStep`).  A RIGHT-branch
    -- step emits its event BEFORE the left branch runs, but the sequential `bs_par`
    -- fixes the trace order (left-trace ++ right-trace): the head-expanded trace
    -- `t ++ (s1 ++ s2)` (right-event, then left `s1`, then right `s2`) matches NO
    -- `bs_par` run — the only candidate is `s1 ++ (t ++ s2)`.  They agree only when the
    -- events COMMUTE, i.e. the branches are SEPARATED.  (Worse, the right step may even
    -- drop a cell the left branch needs — `par (read r) (drop z)`, `r→z` — so progress
    -- itself fails.)  Unit-typing fixed the result-confluence half of the story (the
    -- join is now a single `.unit`), but NOT this trace-order/liveness half: closing it
    -- still requires threading the type system's `Noninterference` through a
    -- sequentialization/diamond argument; it is FALSE at this raw, separation-free
    -- level.  This is the one fundamental gap interleaving `par` opens in the
    -- small-step↔big-step bridge.
    sorry
  | step_rename => intro t' v m' hbs; exact BigStep.bs_letin_var BigStep.bs_var hbs
  | step_unpack => intro t' v m' hbs; exact BigStep.bs_unpack BigStep.bs_pack hbs
  | step_lift hv hwf hfresh =>
    intro t' v' m' hbs
    exact BigStep.bs_letin_val (BigStep.bs_val hv) hv hwf hfresh hbs

/-- Small-step ⇒ big-step (to answers).  A `Reduce` to an answer `a` is realized
    by a single `BigStep` emitting the same trace: fold head-expansion over the
    reduction (`refl` is the answer's trivial self-run). -/
theorem reduce_to_bigstep {t : Trace} {m e m' a}
    (hred : Reduce t m e m' a) (hans : a.IsAns) : BigStep m e t a m' := by
  induction hred with
  | refl => exact BigStep.of_isAns hans
  | step hstep _ ih => exact BigStep.head_expand hstep (ih hans)

/-- **Preservation of `Safe` (small-step).**  A `Step` preserves big-step safety.
    Mirrors `step_preserves_wf`: invert the `Safe` derivation per redex; the
    `letin`/`unpack` continuations transport across the inner step by head
    expansion, since a post-step `BigStep` of the head head-expands to a pre-step
    one feeding the original handler. -/
theorem step_preserves_safe {t : Trace} {m1 e1 m2 e2}
    (hstep : Step t m1 e1 m2 e2) : Safe m1 e1 → Safe m2 e2 := by
  induction hstep with
  | step_apply hlk =>
    intro hsafe
    cases hsafe with
    | apply hlk2 hbody =>
      have heq := congrArg HeapVal.unwrap (Memory.lookup_val_eq hlk hlk2)
      simp only at heq; cases heq; exact hbody
    | invoke hlkx2 _ => rw [hlk] at hlkx2; exact absurd hlkx2 (by simp)
    | ans hans => cases hans with | is_val hv => cases hv
  | step_invoke _ _ => intro _; exact Safe.ans (Exp.IsAns.is_val Exp.IsVal.unit)
  | step_tapply hlk =>
    intro hsafe
    cases hsafe with
    | tapply hlk2 hbody =>
      have heq := congrArg HeapVal.unwrap (Memory.lookup_val_eq hlk hlk2)
      simp only at heq; cases heq; exact hbody
    | ans hans => cases hans with | is_val hv => cases hv
  | step_capply hlk =>
    intro hsafe
    cases hsafe with
    | capply hlk2 hbody =>
      have heq := congrArg HeapVal.unwrap (Memory.lookup_val_eq hlk hlk2)
      simp only at heq; cases heq; exact hbody
    | ans hans => cases hans with | is_val hv => cases hv
  | step_unwrap hlk =>
    intro hsafe
    cases hsafe with
    | unwrap hlk2 hbody =>
      have heq := congrArg HeapVal.unwrap (Memory.lookup_val_eq hlk hlk2)
      simp only at heq; cases heq; exact hbody
    | ans hans => cases hans with | is_val hv => cases hv
  | step_cond_var_true hlk =>
    intro hsafe
    cases hsafe with
    | cond hres h_true _ =>
      simp only [Memory.lookup] at hlk
      exact h_true (by simp only [resolve, hlk])
    | ans hans => cases hans with | is_val hv => cases hv
  | step_cond_var_false hlk =>
    intro hsafe
    cases hsafe with
    | cond hres _ h_false =>
      simp only [Memory.lookup] at hlk
      exact h_false (by simp only [resolve, hlk])
    | ans hans => cases hans with | is_val hv => cases hv
  | step_read _ _ => intro _; exact Safe.ans (Exp.IsAns.is_val (by split <;> constructor))
  | step_write_true _ _ => intro _; exact Safe.ans (Exp.IsAns.is_val Exp.IsVal.unit)
  | step_write_false _ _ => intro _; exact Safe.ans (Exp.IsAns.is_val Exp.IsVal.unit)
  | step_alloc _ _ => intro _; exact Safe.ans (Exp.IsAns.is_val Exp.IsVal.pack)
  | step_drop _ => intro _; exact Safe.ans (Exp.IsAns.is_val Exp.IsVal.unit)
  | step_ctx_letin hstep_inner ih =>
    intro hsafe
    cases hsafe with
    | letin hse1 h_ans h_val h_var =>
      refine Safe.letin (ih hse1) ?_ ?_ ?_
      · intro t1 v m1' hbs
        exact h_ans _ _ _ (BigStep.head_expand hstep_inner hbs)
      · intro t1 m1' v hbs hv hwf l' hfresh
        exact h_val (BigStep.head_expand hstep_inner hbs) hv hwf l' hfresh
      · intro t1 m1' x hbs
        exact h_var (BigStep.head_expand hstep_inner hbs)
    | ans hans => cases hans with | is_val hv => cases hv
  | step_ctx_unpack hstep_inner ih =>
    intro hsafe
    cases hsafe with
    | unpack hse1 h_ans h_val =>
      refine Safe.unpack (ih hse1) ?_ ?_
      · intro t1 v m1' hbs
        exact h_ans _ _ _ (BigStep.head_expand hstep_inner hbs)
      · intro t1 m1' x cs hbs
        exact h_val (BigStep.head_expand hstep_inner hbs)
    | ans hans => cases hans with | is_val hv => cases hv
  | step_par_left hstep_inner ih =>
    -- A LEFT step is aligned with the sequential `Safe.par`: the stepped left branch
    -- stays safe by the IH; the (frozen) right branch's continuation transports
    -- across the step by head-expansion (a post-step left-answer head-expands to a
    -- pre-step one feeding the original handler).  No separation needed.
    intro hsafe
    cases hsafe with
    | par hs1 h2 =>
      refine Safe.par (ih hs1) ?_
      intro t1 v m1' hbs
      exact h2 (BigStep.head_expand hstep_inner hbs)
    | ans hans => cases hans with | is_val hv => cases hv
  | step_par_right _ _ =>
    -- GENUINE DESIGN GAP (same root as `head_expand`'s `step_par_right`).  A RIGHT step
    -- (`m1 → m2`) must leave the LEFT branch safe, but it may have dropped a cell the
    -- left branch needs: `par (read r) (drop z)` with `r → z` — `Safe m1 (par …)` holds
    -- (sequentially: read then drop), yet after the right `drop z` step the left
    -- `read r` is STUCK, so `Safe m2 (par …)` FAILS.  Sound only under separation
    -- (`Noninterference` forbids the right branch dropping a left-branch cell); FALSE
    -- at this raw, separation-free level.
    sorry
  | step_par_join _ _ =>
    -- `par a b → .unit`; the canonical unit result is an answer, hence trivially safe.
    intro _
    exact Safe.ans (Exp.IsAns.is_val Exp.IsVal.unit)
  | step_rename =>
    intro hsafe
    cases hsafe with
    | letin _ _ _ h_var => exact h_var BigStep.bs_var
    | ans hans => cases hans with | is_val hv => cases hv
  | step_lift hv hwf hfresh =>
    intro hsafe
    cases hsafe with
    | letin _ _ h_val _ => exact h_val (BigStep.bs_val hv) hv hwf _ hfresh
    | ans hans => cases hans with | is_val hv2 => cases hv2
  | step_unpack =>
    intro hsafe
    cases hsafe with
    | unpack _ _ h_val => exact h_val BigStep.bs_pack
    | ans hans => cases hans with | is_val hv => cases hv

/-- **Preservation of `Eval` (small-step).**  Because the postcondition is keyed
    on the *whole* trace, a step *shifts* it by the step's own trace `t`: every
    answer reached after the step prepends `t` as seen from before it. -/
theorem step_preserves_eval {t : Trace} {m1 e1 m2 e2} {Q : Tpost}
    (he : Eval m1 e1 Q) (hstep : Step t m1 e1 m2 e2) :
    Eval m2 e2 (fun t' => Q (t ++ t')) := by
  refine ⟨step_preserves_safe hstep he.1, ?_⟩
  intro t' v m' hbs
  exact he.2 (t ++ t') v m' (BigStep.head_expand hstep hbs)

/-- `Reduce`-level head expansion: fold `BigStep.head_expand` over a reduction. -/
theorem BigStep.reduce_expand {t : Trace} {m1 e1 m2 e2}
    (hred : Reduce t m1 e1 m2 e2) :
    ∀ {t' : Trace} {v : Exp {}} {m' : Memory},
      BigStep m2 e2 t' v m' → BigStep m1 e1 (t ++ t') v m' := by
  induction hred with
  | refl => intro t' v m' hbs; exact hbs
  | step hstep _ ih =>
    intro t' v m' hbs
    rw [List.append_assoc]
    exact BigStep.head_expand hstep (ih hbs)

/-- Reduction preserves big-step safety (iterate `step_preserves_safe`). -/
theorem reduce_preserves_safe {t : Trace} {m1 e1 m2 e2}
    (hred : Reduce t m1 e1 m2 e2) : Safe m1 e1 → Safe m2 e2 := by
  induction hred with
  | refl => exact id
  | step hstep _ ih => exact fun hsafe => ih (step_preserves_safe hstep hsafe)

/-- **Preservation of `Eval` (reduction).**  As `step_preserves_eval`, with the
    postcondition shifted by the reduction's accumulated trace. -/
theorem reduce_preserves_eval {t : Trace} {m1 e1 m2 e2} {Q : Tpost}
    (he : Eval m1 e1 Q) (hred : Reduce t m1 e1 m2 e2) :
    Eval m2 e2 (fun t' => Q (t ++ t')) := by
  refine ⟨reduce_preserves_safe hred he.1, ?_⟩
  intro t' v m' hbs
  exact he.2 (t ++ t') v m' (BigStep.reduce_expand hred hbs)

/-- **Adequacy.**  If `Eval m e Q` and `e` reduces (small-step) to an answer `a`
    emitting trace `t`, then `Q t a m'`: the reduction is realized as a `BigStep`
    (`reduce_to_bigstep`), to which the preservation half of `Eval` applies. -/
theorem eval_to_reduce {t : Trace} {m e m' a} {Q : Tpost}
    (heval : Eval m e Q) (hans : a.IsAns) (hred : Reduce t m e m' a) : Q t a m' :=
  heval.2 t a m' (reduce_to_bigstep hred hans)

-- NOTE: `Heap/Memory.masked_update_mcell_comm`, `step_masked`, and `reduce_masked`
-- have been removed.  They expressed "a step under capability `C` stays within the
-- memory masked to `C.to_finset`", which depended entirely on the `covers`
-- premises that the trace-indexed `Step` no longer carries (and used the old
-- liveness-free `.mcell b` API).  With `Step` recording — rather than bounding —
-- accesses, there is no capability-relative masking invariant to state here.

-- NOTE: `eval_exists_answer` (big-step answer existence) now lives in `BigStep.lean`
-- as a corollary of `Safe.has_answer`; `step_preserves_compatible` is also gone —
-- `is_compatible` was tied to the old capability-indexed `Eval` and plays no role
-- in the trace-indexed `Eval := Safe ∧ preservation`.

/-- **Termination to an answer (small-step).**  A `Safe` configuration reduces
    (small-step) to an answer.  This is the small-step counterpart of
    `Safe.has_answer`; the `letin`/`unpack` heads are classified by `h_ans` on the
    big-step realization of the head's own reduction (`reduce_to_bigstep`). -/
theorem Safe.has_reduction {m : Memory} {e : Exp {}} (h : Safe m e) :
    ∃ t m' a, Reduce t m e m' a ∧ a.IsAns := by
  induction h with
  | ans hans => exact ⟨_, _, _, Reduce.refl, hans⟩
  | alloc hlk =>
    obtain ⟨l, hfresh⟩ := Memory.exists_fresh _
    exact ⟨_, _, _, Reduce.step (Step.step_alloc hlk hfresh) Reduce.refl,
      Exp.IsAns.is_val Exp.IsVal.pack⟩
  | @apply cs T e_abs hv R y m x hlk _ ih =>
    obtain ⟨t, m', a, hred, hans⟩ := ih
    obtain ⟨y', rfl⟩ := Var.free_cases y
    exact ⟨_, _, _, Reduce.step (Step.step_apply hlk) hred, hans⟩
  | invoke hlkx hlky =>
    exact ⟨_, _, _, Reduce.step (Step.step_invoke hlkx hlky) Reduce.refl,
      Exp.IsAns.is_val Exp.IsVal.unit⟩
  | tapply hlk _ ih =>
    obtain ⟨t, m', a, hred, hans⟩ := ih
    exact ⟨_, _, _, Reduce.step (Step.step_tapply hlk) hred, hans⟩
  | capply hlk _ ih =>
    obtain ⟨t, m', a, hred, hans⟩ := ih
    exact ⟨_, _, _, Reduce.step (Step.step_capply hlk) hred, hans⟩
  | unwrap hlk _ ih =>
    obtain ⟨t, m', a, hred, hans⟩ := ih
    exact ⟨_, _, _, Reduce.step (Step.step_unwrap hlk) hred, hans⟩
  | letin _ h_ans _ _ ih1 ih_val ih_var =>
    obtain ⟨t1, m1, a1, hred1, hans1⟩ := ih1
    have hbs1 := reduce_to_bigstep hred1 hans1
    obtain ⟨hsa, hwf⟩ := h_ans _ _ _ hbs1
    rcases Exp.isSimpleAns_cases hsa with hv | ⟨n, rfl⟩
    · obtain ⟨l, hfresh⟩ := Memory.exists_fresh m1
      obtain ⟨t2, m2, a2, hred2, hans2⟩ := ih_val hbs1 hv hwf l hfresh
      exact ⟨_, _, _, reduce_trans (reduce_ctx_letin hred1)
        (Reduce.step (Step.step_lift hv hwf hfresh) hred2), hans2⟩
    · obtain ⟨t2, m2, a2, hred2, hans2⟩ := ih_var hbs1
      exact ⟨_, _, _, reduce_trans (reduce_ctx_letin hred1)
        (Reduce.step Step.step_rename hred2), hans2⟩
  | unpack _ h_ans _ ih1 ih_val =>
    obtain ⟨t1, m1, a1, hred1, hans1⟩ := ih1
    have hbs1 := reduce_to_bigstep hred1 hans1
    obtain ⟨hpack, hwf⟩ := h_ans _ _ _ hbs1
    obtain ⟨cs, n, rfl⟩ := Exp.isPack_cases hpack
    obtain ⟨t2, m2, a2, hred2, hans2⟩ := ih_val hbs1
    exact ⟨_, _, _, reduce_trans (reduce_ctx_unpack hred1)
      (Reduce.step Step.step_unpack hred2), hans2⟩
  | read hlkx hlky =>
    exact ⟨_, _, _, Reduce.step (Step.step_read hlkx hlky) Reduce.refl,
      Exp.IsAns.is_val (by split <;> constructor)⟩
  | write_true hx hy =>
    exact ⟨_, _, _, Reduce.step (Step.step_write_true hx hy) Reduce.refl,
      Exp.IsAns.is_val Exp.IsVal.unit⟩
  | write_false hx hy =>
    exact ⟨_, _, _, Reduce.step (Step.step_write_false hx hy) Reduce.refl,
      Exp.IsAns.is_val Exp.IsVal.unit⟩
  | drop hx =>
    exact ⟨_, _, _, Reduce.step (Step.step_drop hx) Reduce.refl,
      Exp.IsAns.is_val Exp.IsVal.unit⟩
  | @cond e2 e3 m x hres _ _ ih_true ih_false =>
    obtain ⟨fx, rfl⟩ := Var.free_cases x
    cases hres with
    | inl hbtrue =>
      cases hcell : m.heap fx with
      | none => simp [resolve, hcell] at hbtrue
      | some cell =>
        cases cell with
        | val hv =>
          cases hv with
          | mk unwrap hsimple reach =>
            have hunwrap : unwrap = .btrue := by simpa [resolve, hcell] using hbtrue
            cases hunwrap
            obtain ⟨t, m', a, hred, hans⟩ := ih_true hbtrue
            exact ⟨_, _, _, Reduce.step
              (Step.step_cond_var_true (hv := hsimple) (R := reach)
                (by simp [Memory.lookup, hcell])) hred, hans⟩
        | capability => simp [resolve, hcell] at hbtrue
        | masked => simp [resolve, hcell] at hbtrue
    | inr hbfalse =>
      cases hcell : m.heap fx with
      | none => simp [resolve, hcell] at hbfalse
      | some cell =>
        cases cell with
        | val hv =>
          cases hv with
          | mk unwrap hsimple reach =>
            have hunwrap : unwrap = .bfalse := by simpa [resolve, hcell] using hbfalse
            cases hunwrap
            obtain ⟨t, m', a, hred, hans⟩ := ih_false hbfalse
            exact ⟨_, _, _, Reduce.step
              (Step.step_cond_var_false (hv := hsimple) (R := reach)
                (by simp [Memory.lookup, hcell])) hred, hans⟩
        | capability => simp [resolve, hcell] at hbfalse
        | masked => simp [resolve, hcell] at hbfalse
  | par _ _ ih1 ih2 =>
    -- Build the canonical (left-then-right-then-join) reduction to an answer: run e1
    -- fully (ih1), run e2 from e1's answer-memory (ih2, fed e1's big-step answer via
    -- `reduce_to_bigstep`), lift each through the par congruences, then join to `.unit`.
    -- This is a valid interleaving, so progress holds with NO separation needed.
    obtain ⟨ta, ma, aans, hreda, hansa⟩ := ih1
    obtain ⟨tb, mb, bans, hredb, hansb⟩ := ih2 (reduce_to_bigstep hreda hansa)
    exact ⟨_, _, _,
      reduce_trans (reduce_par_left hreda)
        (reduce_trans (reduce_par_right hredb)
          (Reduce.step (Step.step_par_join hansa hansb) Reduce.refl)),
      Exp.IsAns.is_val Exp.IsVal.unit⟩

/-- Answer existence (small-step): `Eval m e Q` reduces to an answer satisfying
    `Q`.  Combine `Safe.has_reduction` with the adequacy bridge. -/
theorem eval_reduce_exists_answer {m : Memory} {e : Exp {}} {Q : Tpost}
    (heval : Eval m e Q) :
    ∃ t m' a, Reduce t m e m' a ∧ a.IsAns ∧ Q t a m' := by
  obtain ⟨t, m', a, hred, hans⟩ := heval.1.has_reduction
  exact ⟨t, m', a, hred, hans, heval.2 t a m' (reduce_to_bigstep hred hans)⟩

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
  | step_rename | step_unpack | step_par_join _ _ =>
    -- Memory is unchanged.
    exact hinit
  | step_par_left _ ih | step_par_right _ ih =>
    -- Congruence: the only change is the sub-step's, handled by the IH.
    exact ih hwr hdr hinit
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

/-- **Per-location immutability (single step).**  A step that neither writes
    (`access .epsilon l`) nor drops (`dealloc l`) the specific cell `l` leaves
    that cell unchanged — same bit and liveness.  Fresh allocations land at fresh
    locations (distinct from the queried, already-allocated `l`); writes/drops at
    other locations miss `l`; a write/drop at `l` itself is excluded by the
    hypotheses.  This is the per-cell refinement of `step_immutable`, needed when
    the trace *may* legitimately touch freshly allocated cells. -/
theorem step_preserves_cell {t : Trace} {m1 e1 m2 e2 : _} {l : Nat} {b : Bool} {ℓ : Liveness}
    (hstep : Step t m1 e1 m2 e2) :
    TraceItem.access .epsilon l ∉ t -> TraceItem.dealloc l ∉ t ->
    m1.heap l = some (.capability (.mcell b ℓ)) ->
    m2.heap l = some (.capability (.mcell b ℓ)) := by
  induction hstep with
  | step_apply _ | step_invoke _ _ | step_tapply _ | step_capply _ | step_unwrap _
  | step_cond_var_true _ | step_cond_var_false _ | step_read _ _
  | step_rename | step_unpack | step_par_join _ _ =>
    intro _ _ hinit; exact hinit
  | step_par_left _ ih | step_par_right _ ih =>
    -- Congruence: the cell change is the sub-step's, handled by the IH.
    intro hwr hdr hinit; exact ih hwr hdr hinit
  | step_write_true _ _ | step_write_false _ _ =>
    intro hwr _ hinit
    simp only [Memory.update_mcell, Heap.update_cell]
    split
    · rename_i heq; subst heq; exact absurd (List.mem_singleton.mpr rfl) hwr
    · exact hinit
  | step_drop _ =>
    intro _ hdr hinit
    simp only [Memory.drop_mcell, Heap.update_cell]
    split
    · rename_i heq; subst heq; exact absurd (List.mem_singleton.mpr rfl) hdr
    · exact hinit
  | step_alloc _ hfresh =>
    intro _ _ hinit
    simp only [Memory.extend_mcell, Heap.extend_mcell]
    split
    · rename_i heq; rw [heq, hfresh] at hinit; cases hinit
    · exact hinit
  | step_lift hv hwf hfresh =>
    intro _ _ hinit
    simp only [Memory.extend, Heap.extend]
    split
    · rename_i heq; rw [heq, hfresh] at hinit; cases hinit
    · exact hinit
  | step_ctx_letin _ ih | step_ctx_unpack _ ih =>
    intro hwr hdr hinit; exact ih hwr hdr hinit

/-- **Per-location immutability (reduction).**  A whole reduction that never
    writes or drops the specific cell `l` leaves it unchanged. -/
theorem reduce_preserves_cell {t : Trace} {m1 e1 m2 e2 : _} {l : Nat} {b : Bool} {ℓ : Liveness}
    (hred : Reduce t m1 e1 m2 e2) :
    TraceItem.access .epsilon l ∉ t -> TraceItem.dealloc l ∉ t ->
    m1.heap l = some (.capability (.mcell b ℓ)) ->
    m2.heap l = some (.capability (.mcell b ℓ)) := by
  induction hred with
  | refl => intro _ _ hinit; exact hinit
  | step hstep _ ih =>
    intro hwr hdr hinit
    refine ih (fun hm => hwr (List.mem_append_right _ hm))
      (fun hm => hdr (List.mem_append_right _ hm)) ?_
    exact step_preserves_cell hstep (fun hm => hwr (List.mem_append_left _ hm))
      (fun hm => hdr (List.mem_append_left _ hm)) hinit

/- ============================================================================
   THE ONE FUNDAMENTAL GAP: interleaving `par` vs the sequential `BigStep` spec.

   Two `sorry`s remain in this file — `BigStep.head_expand` and `step_preserves_safe`,
   BOTH in the `step_par_right` case, BOTH the SAME root design tension.  They are NOT
   missing proofs: at this raw, separation-free level the claims are FALSE, with
   concrete counterexamples (see the inline comments):

     * Trace order: a right-branch step emits its event before the left branch runs,
       but the sequential `bs_par` fixes the trace as `left ++ right`.  So the
       head-expanded trace is realized by no `bs_par` run unless the two events
       COMMUTE.  (Interleaved traces are only Mazurkiewicz-equivalent to the
       sequential one.)
     * Liveness: a right step may drop a cell the left branch needs
       (`par (read r) (drop z)`, `r → z`), so `Safe`/progress fails outright.

   NOTE the design has split this into two independent sub-problems, ONE of which is
   now CLOSED:
     (a) RESULT-confluence — solved.  Unit-typing `par` (`par e1 e2 : .typ .unit`)
         plus the SINGLE canonical join (`step_par_join … → .unit`, `bs_par … → .unit`)
         makes the join deterministic: no value critical pair, so all schedules agree
         on the result.  (The old either-branch join was non-confluent at the join
         itself, independent of any effect reasoning.)
     (b) EFFECT/trace ordering + liveness — STILL OPEN, the two `sorry`s above.

   (b) is sound EXACTLY under separation — which the type system enforces
   (`SepCheck`/`Noninterference`) but which `Step`/`Safe`/`Eval` do not themselves
   carry.  Closing it is a genuine DESIGN step (human intervention): the interleaving
   adequacy must be a TYPED, top-level theorem threading `fundamental_sepcheck`'s
   `Noninterference` through a sequentialization (diamond / Mazurkiewicz) argument,
   observing traces up to permutation — not a raw per-step bridge lemma.  Every OTHER
   `par` case here (congruence-left, the join, progress, has_reduction, WF /
   memory-monotonicity / immutability) is proven outright; the gap is minimal and
   isolated to the one place true concurrency genuinely diverges from a sequential
   semantics.
   ============================================================================ -/

end CoreCapybara
