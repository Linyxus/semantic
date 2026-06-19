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

/-- Sequential congruence: a `SeqReduce` of the LEFT branch of `letin` lifts. -/
theorem seqreduce_ctx_letin
  (hred : SeqReduce C m e1 m' e1') :
  SeqReduce C m (.letin e1 e2) m' (.letin e1' e2) := by
  induction hred with
  | refl => exact SeqReduce.refl
  | step h _ ih => exact SeqReduce.step (SeqStep.step_ctx_letin h) ih

theorem seqreduce_ctx_unpack
  (hred : SeqReduce C m e1 m' e1') :
  SeqReduce C m (.unpack e1 e2) m' (.unpack e1' e2) := by
  induction hred with
  | refl => exact SeqReduce.refl
  | step h _ ih => exact SeqReduce.step (SeqStep.step_ctx_unpack h) ih

theorem seqreduce_par_left {C : Trace} {m m' : Memory} {e1 e1' e2 : Exp {}}
  (hred : SeqReduce C m e1 m' e1') :
  SeqReduce C m (.par e1 e2) m' (.par e1' e2) := by
  induction hred with
  | refl => exact SeqReduce.refl
  | step h _ ih => exact SeqReduce.step (SeqStep.step_par_left h) ih

/-- Sequential congruence for the RIGHT branch: the LEFT branch must be a (frozen)
  answer throughout, as `SeqStep.step_par_right` demands. -/
theorem seqreduce_par_right {C : Trace} {m m' : Memory} {a e2 e2' : Exp {}}
  (hans : a.IsAns) (hred : SeqReduce C m e2 m' e2') :
  SeqReduce C m (.par a e2) m' (.par a e2') := by
  induction hred with
  | refl => exact SeqReduce.refl
  | step h _ ih => exact SeqReduce.step (SeqStep.step_par_right hans h) ih

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

-- Progress predicate: an expression is *progressive* in memory `m` if it is
-- already an answer, or it can take at least one sequential `SeqStep`.  The `step`
-- witness's trace is hidden existentially (progress only asserts that *some* step
-- exists).
inductive IsProgressive : Memory -> Exp {} -> Prop where
| done :
  e.IsAns ->
  IsProgressive m e
| step :
  SeqStep t m e m' e' ->
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

/-- **Progress (sequential small-step).**  A `Safe` configuration is *progressive*:
    it is already an answer, or it can take a sequential `SeqStep`.  The recursion
    mirrors the `Safe` derivation; for `letin`/`unpack` the head's progress
    (`ih_e1`) is used, and when the head is already an answer, `h_ans` (applied to
    the trivial self-run `BigStep.of_isAns`) classifies it as a simple value or
    variable so that `step_lift`/`step_rename`/`step_unpack` fire. -/
theorem safe_implies_progressive {m : Memory} {e : Exp {}}
  (h : Safe m e) :
  IsProgressive m e := by
  induction h with
  | ans hans => exact IsProgressive.done hans
  | alloc hlookup =>
    -- e = .alloc (.free x); steps via step_alloc to a fresh live mcell
    obtain ⟨l, hfresh⟩ := Memory.exists_fresh _
    exact IsProgressive.step (SeqStep.step_alloc (l := l) hlookup hfresh)
  | drop hx =>
    -- e = .drop (.free x); steps via step_drop
    exact IsProgressive.step (SeqStep.step_drop hx)
  | @apply cs T e_abs hv R y m x hlookup _ _ =>
    -- e = .app (.free x) y; y is free (empty signature), so step_apply applies
    obtain ⟨y', rfl⟩ := Var.free_cases y
    exact IsProgressive.step (SeqStep.step_apply hlookup)
  | invoke hlookup_x hlookup_y =>
    exact IsProgressive.step (SeqStep.step_invoke hlookup_x hlookup_y)
  | tapply hlookup _ _ =>
    exact IsProgressive.step (SeqStep.step_tapply hlookup)
  | capply hlookup _ _ =>
    exact IsProgressive.step (SeqStep.step_capply hlookup)
  | unwrap hlookup _ _ =>
    exact IsProgressive.step (SeqStep.step_unwrap hlookup)
  | letin _ h_ans _ _ ih_e1 _ _ =>
    -- e = .letin e1 e2; by `ih_e1`, e1 is progressive
    cases ih_e1 with
    | done hans =>
      -- e1 is an answer: classify it via h_ans on the trivial self-run
      obtain ⟨hsimple_ans, hwf⟩ := h_ans _ _ _ (BigStep.of_isAns hans)
      rcases Exp.isSimpleAns_cases hsimple_ans with hv | ⟨n, rfl⟩
      · -- e1 is a simple value: step_lift to a fresh location (heap is finite)
        obtain ⟨l0, hfresh⟩ := Memory.exists_fresh _
        exact IsProgressive.step (SeqStep.step_lift (l := l0) hv hwf hfresh)
      · -- e1 is a free variable: step_rename
        exact IsProgressive.step SeqStep.step_rename
    | step hstep =>
      -- e1 can step, so letin e1 e2 steps via step_ctx_letin
      exact IsProgressive.step (SeqStep.step_ctx_letin hstep)
  | unpack _ h_ans _ ih_e1 _ =>
    -- e = .unpack e1 e2; by `ih_e1`, e1 is progressive
    cases ih_e1 with
    | done hans =>
      -- e1 is an answer: classify it as a pack with a free witness via h_ans
      obtain ⟨hpack, hwf⟩ := h_ans _ _ _ (BigStep.of_isAns hans)
      obtain ⟨cs, n, rfl⟩ := Exp.isPack_cases hpack
      exact IsProgressive.step SeqStep.step_unpack
    | step hstep =>
      -- e1 can step, so unpack e1 e2 steps via step_ctx_unpack
      exact IsProgressive.step (SeqStep.step_ctx_unpack hstep)
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
              (SeqStep.step_cond_var_true (hv := hsimple) (R := reach)
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
              (SeqStep.step_cond_var_false (hv := hsimple) (R := reach)
                (by simp [Memory.lookup, hcell]))
        | capability => simp [resolve, hcell] at hbfalse
        | masked => simp [resolve, hcell] at hbfalse
  | read hlookup_reader hlookup_cell =>
    -- e = .read (.free x), can step via step_read
    exact IsProgressive.step (SeqStep.step_read hlookup_reader hlookup_cell)
  | write_true hx hy =>
    -- e = .write (.free x) (.free y), can step via step_write_true
    exact IsProgressive.step (SeqStep.step_write_true hx hy)
  | write_false hx hy =>
    -- e = .write (.free x) (.free y), can step via step_write_false
    exact IsProgressive.step (SeqStep.step_write_false hx hy)
  | par _ h2 _ _ _ _ _ _ ih1 ih2 _ =>
    -- Progress for sequential `par`: advance the left branch until it is an answer
    -- (congruence), then the right branch (`step_par_right` needs the left answer),
    -- then join once both are answers.  Progress needs only SOME step to exist.
    cases ih1 with
    | done hAans =>
      cases ih2 (BigStep.of_isAns hAans) with
      | done hBans => exact IsProgressive.step (SeqStep.step_par_join hAans hBans)
      | step hstepB => exact IsProgressive.step (SeqStep.step_par_right hAans hstepB)
    | step hstepA => exact IsProgressive.step (SeqStep.step_par_left hstepA)

/-- An `Eval` is progressive: its bundled `Safe` half gives small-step progress. -/
theorem eval_implies_progressive {m : Memory} {e : Exp {}} {Q : Tpost}
  (heval : Eval m e Q) :
  IsProgressive m e :=
  safe_implies_progressive heval.1

/- ============================================================================
   SMALL-STEP ↔ BIG-STEP BRIDGE.  The new `Eval := Safe ∧ preservation`
   is phrased over the relational `BigStep`.  These lemmas connect it to the
   small-step `Step`/`Reduce`, so the small-step preservation/progress results
   (consumed by `Safety`) go through.  The keystone is *head expansion*:
   prepending a `Step` to a `BigStep` run is again a `BigStep` run.
   ============================================================================ -/

/-- An external touch of a prefix `t` is an external touch of `t ++ t'` (same mode):
    the suffix `t'` is processed after `t`, so it cannot un-do `t`'s external touch. -/
theorem Trace.extTouchesFromMode_append_left {t t' : Trace} {l : Nat} {cm : CapMode}
    {A : List Nat} (h : Trace.extTouchesFromMode A l cm t) :
    Trace.extTouchesFromMode A l cm (t ++ t') := by
  induction t generalizing A with
  | nil => simp only [Trace.extTouchesFromMode] at h
  | cons it t ih =>
    cases it with
    | alloc l' => exact ih h
    | access mu l' =>
      rcases h with hd | hr
      · exact Or.inl hd
      · exact Or.inr (ih hr)
    | dealloc l' =>
      rcases h with hd | hr
      · exact Or.inl hd
      · exact Or.inr (ih hr)

/-- `Noninterfere` is downward-closed in its SECOND argument under prefixing:
    if `t1` does not interfere with `t ++ t'`, it does not interfere with `t`
    (a prefix has fewer external touches). -/
theorem Trace.Noninterfere_of_append_right {t1 t t' : Trace}
    (h : Trace.Noninterfere t1 (t ++ t')) : Trace.Noninterfere t1 t := by
  intro l cm1 cm2 h1 h2
  exact h l cm1 cm2 h1 (Trace.extTouchesFromMode_append_left h2)

/-- **Head expansion (sequential).**  A `SeqStep` prefixed to a `BigStep` run is
    itself a `BigStep` run, with the step's trace prepended.  Read-nondeterminism is
    no obstacle: the faithful `step_read` bit is one admissible `bs_read` outcome
    (`b' = b`); the `letin`/`unpack`/`par` congruence steps recurse through the
    inductive hypothesis.  The `step_par_right` case threads exactly *because* the
    sequential schedule fixes the left branch as an answer before the right branch
    runs — matching `bs_par`'s left-then-right order — so the head-expanded trace
    aligns with a `bs_par` run.  (For unrestricted interleaving this is false at the
    exact trace: it holds only up to Mazurkiewicz permutation, which is the content
    of the standardization theorem relating `Step` to `SeqStep`.) -/
theorem BigStep.head_expand {t : Trace} {m1 e1 m2 e2 : _}
    (hstep : SeqStep t m1 e1 m2 e2) :
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
  | step_par_right hans_a _ ih =>
    -- A RIGHT-branch step under the sequential schedule has the LEFT branch `a`
    -- already an answer (`hans_a`).  So `a` runs trivially (empty trace, `isAns_inv`)
    -- and the head-expanded trace `t ++ ([] ++ s2)` IS a `bs_par` run: `a` (empty)
    -- then `b` head-expanded through the IH.  No permutation needed.
    intro t' v m' hbs
    cases hbs with
    | bs_par hrunA hrunB =>
      obtain ⟨rfl, rfl, rfl⟩ := BigStep.isAns_inv hrunA hans_a
      simpa using BigStep.bs_par (BigStep.of_isAns hans_a) (ih hrunB)
    | bs_val hv => cases hv
  | step_rename => intro t' v m' hbs; exact BigStep.bs_letin_var BigStep.bs_var hbs
  | step_unpack => intro t' v m' hbs; exact BigStep.bs_unpack BigStep.bs_pack hbs
  | step_lift hv hwf hfresh =>
    intro t' v' m' hbs
    exact BigStep.bs_letin_val (BigStep.bs_val hv) hv hwf hfresh hbs

/-- Sequential small-step ⇒ big-step (to answers).  A `SeqReduce` to an answer `a`
    is realized by a single `BigStep` emitting the same trace: fold head-expansion
    over the reduction (`refl` is the answer's trivial self-run). -/
theorem reduce_to_bigstep {t : Trace} {m e m' a}
    (hred : SeqReduce t m e m' a) (hans : a.IsAns) : BigStep m e t a m' := by
  induction hred with
  | refl => exact BigStep.of_isAns hans
  | step hstep _ ih => exact BigStep.head_expand hstep (ih hans)

/-- **A drop-free `Step` preserves liveness.**  Only `step_drop` emits a `dealloc`
    event and only it marks a cell `.dead`; every other redex keeps live cells live
    (writes change the *bit*, not the liveness; `alloc`/`lift` only add cells).  So a
    `Step` whose trace contains no `dealloc` keeps every live cell live.  This is the
    operational core of the platform's drop-freeness: with `.access_only` capture
    variables the reduction emits no `dealloc`, hence NO cell ever dies, hence the
    liveness frame (`Memory.SubsumeOk`) of `Safe.lift` holds for free. -/
theorem step_preserves_live {t : Trace} {m1 e1 m2 e2 : _} {l : Nat}
    (hstep : Step t m1 e1 m2 e2) (hdf : ∀ l, TraceItem.dealloc l ∉ t)
    (hlive : m1.IsLive l) : m2.IsLive l := by
  induction hstep with
  | step_apply _ | step_invoke _ _ | step_tapply _ | step_capply _ | step_unwrap _
  | step_cond_var_true _ | step_cond_var_false _ | step_read _ _
  | step_rename | step_unpack | step_par_join _ _ =>
    exact hlive
  | step_par_left _ ih | step_par_right _ ih => exact ih hdf hlive
  | step_ctx_letin _ ih | step_ctx_unpack _ ih => exact ih hdf hlive
  | step_write_true hx _ | step_write_false hx _ =>
    exact Memory.update_mcell_preserves_live _ hlive
  | step_drop _ =>
    exact absurd (List.mem_singleton.mpr rfl) (hdf _)
  | step_alloc _ hfresh =>
    obtain ⟨b, hb⟩ := hlive
    simp only [Memory.lookup] at hb
    refine ⟨b, ?_⟩
    simp only [Memory.lookup, Memory.extend_mcell, Heap.extend_mcell]
    split
    · rename_i heq; rw [heq, hfresh] at hb; cases hb
    · exact hb
  | step_lift hv hwf hfresh =>
    obtain ⟨b, hb⟩ := hlive
    simp only [Memory.lookup] at hb
    refine ⟨b, ?_⟩
    simp only [Memory.lookup, Memory.extend, Heap.extend]
    split
    · rename_i heq; rw [heq, hfresh] at hb; cases hb
    · exact hb

/-- A drop-free `Step` preserves the `AllLive` invariant (no cell ever dies; fresh
    cells start live). -/
theorem step_preserves_allLive {t : Trace} {m1 e1 m2 e2 : _}
    (hstep : Step t m1 e1 m2 e2) (hdf : ∀ l, TraceItem.dealloc l ∉ t)
    (hal : m1.AllLive) : m2.AllLive := by
  induction hstep with
  | step_apply _ | step_invoke _ _ | step_tapply _ | step_capply _ | step_unwrap _
  | step_cond_var_true _ | step_cond_var_false _ | step_read _ _
  | step_rename | step_unpack | step_par_join _ _ =>
    exact hal
  | step_par_left _ ih | step_par_right _ ih => exact ih hdf hal
  | step_ctx_letin _ ih | step_ctx_unpack _ ih => exact ih hdf hal
  | step_write_true hx _ | step_write_false hx _ =>
    intro l b ℓ hlk
    simp only [Memory.update_mcell, Heap.update_cell] at hlk
    split at hlk
    · injection hlk with hc; injection hc with hmc; injection hmc with _ hℓ; exact hℓ.symm
    · exact hal l b ℓ hlk
  | step_drop _ => exact absurd (List.mem_singleton.mpr rfl) (hdf _)
  | step_alloc _ hfresh =>
    intro l b ℓ hlk
    simp only [Memory.extend_mcell, Heap.extend_mcell] at hlk
    split at hlk
    · injection hlk with hc; injection hc with hmc; injection hmc with _ hℓ; exact hℓ.symm
    · exact hal l b ℓ hlk
  | step_lift hv hwf hfresh =>
    intro l b ℓ hlk
    simp only [Memory.extend, Heap.extend] at hlk
    split at hlk
    · exact absurd hlk (by simp)
    · exact hal l b ℓ hlk

/-- **Preservation of `Safe` (sequential small-step).**  A `SeqStep` preserves
    big-step safety.  Mirrors `step_preserves_wf`: invert the `Safe` derivation per
    redex; the `letin`/`unpack` continuations transport across the inner step by
    head expansion, since a post-step `BigStep` of the head head-expands to a
    pre-step one feeding the original handler.  Threads `Exp.WfInHeap` (for the `par`
    cases' head-expansion) and `m1.AllLive` (so the frozen `par` branch's robust
    safety `hrs2` applies at the `C2`-compatible `m1`), kept alive across steps by a
    drop-free hypothesis (`no dealloc`).  The forward Step-lemmas it calls
    (`step_memory_monotonic`, `step_preserves_wf`, `step_allocd_*`) are reused via
    `SeqStep.toStep`. -/
theorem step_preserves_safe {t : Trace} {m1 e1 m2 e2}
    (hstep : SeqStep t m1 e1 m2 e2) :
    Exp.WfInHeap e1 m1.heap → (∀ l, TraceItem.dealloc l ∉ t) → m1.AllLive →
      Safe m1 e1 → Safe m2 e2 := by
  induction hstep with
  | step_apply hlk =>
    intro _ _ _ hsafe
    cases hsafe with
    | apply hlk2 hbody =>
      have heq := congrArg HeapVal.unwrap (Memory.lookup_val_eq hlk hlk2)
      simp only at heq; cases heq; exact hbody
    | invoke hlkx2 _ => rw [hlk] at hlkx2; exact absurd hlkx2 (by simp)
    | ans hans => cases hans with | is_val hv => cases hv
  | step_invoke _ _ => intro _ _ _ _; exact Safe.ans (Exp.IsAns.is_val Exp.IsVal.unit)
  | step_tapply hlk =>
    intro _ _ _ hsafe
    cases hsafe with
    | tapply hlk2 hbody =>
      have heq := congrArg HeapVal.unwrap (Memory.lookup_val_eq hlk hlk2)
      simp only at heq; cases heq; exact hbody
    | ans hans => cases hans with | is_val hv => cases hv
  | step_capply hlk =>
    intro _ _ _ hsafe
    cases hsafe with
    | capply hlk2 hbody =>
      have heq := congrArg HeapVal.unwrap (Memory.lookup_val_eq hlk hlk2)
      simp only at heq; cases heq; exact hbody
    | ans hans => cases hans with | is_val hv => cases hv
  | step_unwrap hlk =>
    intro _ _ _ hsafe
    cases hsafe with
    | unwrap hlk2 hbody =>
      have heq := congrArg HeapVal.unwrap (Memory.lookup_val_eq hlk hlk2)
      simp only at heq; cases heq; exact hbody
    | ans hans => cases hans with | is_val hv => cases hv
  | step_cond_var_true hlk =>
    intro _ _ _ hsafe
    cases hsafe with
    | cond hres h_true _ =>
      simp only [Memory.lookup] at hlk
      exact h_true (by simp only [resolve, hlk])
    | ans hans => cases hans with | is_val hv => cases hv
  | step_cond_var_false hlk =>
    intro _ _ _ hsafe
    cases hsafe with
    | cond hres _ h_false =>
      simp only [Memory.lookup] at hlk
      exact h_false (by simp only [resolve, hlk])
    | ans hans => cases hans with | is_val hv => cases hv
  | step_read _ _ => intro _ _ _ _; exact Safe.ans (Exp.IsAns.is_val (by split <;> constructor))
  | step_write_true _ _ => intro _ _ _ _; exact Safe.ans (Exp.IsAns.is_val Exp.IsVal.unit)
  | step_write_false _ _ => intro _ _ _ _; exact Safe.ans (Exp.IsAns.is_val Exp.IsVal.unit)
  | step_alloc _ _ => intro _ _ _ _; exact Safe.ans (Exp.IsAns.is_val Exp.IsVal.pack)
  | step_drop _ => intro _ _ _ _; exact Safe.ans (Exp.IsAns.is_val Exp.IsVal.unit)
  | step_ctx_letin hstep_inner ih =>
    intro hwf hdf hal hsafe
    obtain ⟨hwf1, _⟩ := Exp.wf_inv_letin hwf
    cases hsafe with
    | letin hse1 h_ans h_val h_var =>
      refine Safe.letin (ih hwf1 hdf hal hse1) ?_ ?_ ?_
      · intro t1 v m1' hbs
        exact h_ans _ _ _ (BigStep.head_expand hstep_inner hbs)
      · intro t1 m1' v hbs hv hwf_v l' hfresh
        exact h_val (BigStep.head_expand hstep_inner hbs) hv hwf_v l' hfresh
      · intro t1 m1' x hbs
        exact h_var (BigStep.head_expand hstep_inner hbs)
    | ans hans => cases hans with | is_val hv => cases hv
  | step_ctx_unpack hstep_inner ih =>
    intro hwf hdf hal hsafe
    obtain ⟨hwf1, _⟩ := Exp.wf_inv_unpack hwf
    cases hsafe with
    | unpack hse1 h_ans h_val =>
      refine Safe.unpack (ih hwf1 hdf hal hse1) ?_ ?_
      · intro t1 v m1' hbs
        exact h_ans _ _ _ (BigStep.head_expand hstep_inner hbs)
      · intro t1 m1' x cs hbs
        exact h_val (BigStep.head_expand hstep_inner hbs)
    | ans hans => cases hans with | is_val hv => cases hv
  | @step_par_left t m1 a m2 a' b hstep_a ih =>
    intro hwf hdf hal hsafe
    obtain ⟨hwf_a, hwf_b⟩ := Exp.wf_inv_par hwf
    cases hsafe with
    | ans hans => cases hans with | is_val hv => cases hv
    | par hse_a h2 hb1 hb2 hrs2 hpres1 hpres2 hni =>
      rename_i C1 C2
      have hsub21 : m2.subsumes m1 := step_memory_monotonic hstep_a.toStep
      -- Reduct `a'`'s budget grows by the step's fresh allocations; `b` keeps `C2`.
      refine Safe.par (C1 := C1 ∪ capsOf (Trace.allocList t)) (C2 := C2)
        (ih hwf_a hdf hal hse_a) ?h2' ?hb1' ?hb2' ?hrs2' ?hpres1' ?hpres2' ?hni'
      case h2' =>
        intro t1 v1 m1' hbs
        exact h2 (BigStep.head_expand hstep_a hbs)
      case hb1' =>
        -- reduct `a'`: bound runs by `C1 ∪ capsOf (allocList t)` via head-expansion.
        intro m' s v m'' hsub' hwf' hbs
        have hwfa' := step_preserves_wf hstep_a.toStep hwf_a
        obtain ⟨ms, hbs_m2, _, _⟩ := hbs.simulate_down hsub' hwfa'
        have hfull : BigStep m1 a (t ++ s) v ms := BigStep.head_expand hstep_a hbs_m2
        have htok : TraceOk (t ++ s) C1 := hb1 (Memory.subsumes_refl _) hwf_a hfull
        have := TraceOkFrom.absorb_exempt (TraceOkFrom.split_append htok)
        rwa [List.append_nil] at this
      case hb2' =>
        intro m' s v m'' hsub' hwf' hbs
        exact hb2 (Memory.subsumes_trans hsub' hsub21) hwf' hbs
      case hrs2' =>
        intro m' hsub' hc
        exact hrs2 (Memory.subsumes_trans hsub' hsub21) hc
      case hpres1' =>
        intro mu l hmem
        rcases CapabilitySet.hasmem_union_iff.mp hmem with h1 | hA
        · exact (fun hc => hpres1 mu l h1 (Heap.none_of_subsumes_none hsub21 hc))
        · exact step_allocd_present hstep_a.toStep (Trace.mem_allocList.mp (capsOf_hasmem hA))
      case hpres2' =>
        intro mu l hmem
        exact (fun hc => hpres2 mu l hmem (Heap.none_of_subsumes_none hsub21 hc))
      case hni' =>
        refine CapabilitySet.Noninterference.ni_union hni
          (CapabilitySet.noninterference_capsOf_fresh ?_)
        intro l hl mu' hm
        exact hpres2 mu' l hm (step_allocd_fresh hstep_a.toStep (Trace.mem_allocList.mp hl))
  | @step_par_right t m1 b m2 b' a hans_a hstep_b ih =>
    intro hwf hdf hal hsafe
    obtain ⟨hwf_a, hwf_b⟩ := Exp.wf_inv_par hwf
    cases hsafe with
    | ans hans => cases hans with | is_val hv => cases hv
    | par hse_a h2 hb1 hb2 hrs2 hpres1 hpres2 hni =>
      rename_i C1 C2
      have hsub21 : m2.subsumes m1 := step_memory_monotonic hstep_b.toStep
      -- `b` is safe at `m1` (robust right-branch safety + `m1` `C2`-compatible, which
      -- holds because `AllLive m1` makes every present cell live), hence `Safe m2 b'`.
      have hse_b1 : Safe m1 b := hrs2 (Memory.subsumes_refl _) (hal.is_compatible C2)
      have hse_b2' : Safe m2 b' := ih hwf_b hdf hal hse_b1
      -- The frozen LEFT branch `a` is an ANSWER (`hans_a`, the sequential schedule),
      -- so its safety at the grown memory is immediate — no liveness-frame lift needed.
      have hsafe_a2 : Safe m2 a := Safe.ans hans_a
      -- Reduct `b'`'s budget is `C2 ∪ capsOf (allocList t)` (`b`'s step's fresh cells).
      have hb2_robust : ∀ {m' : Memory} {s : Trace} {v : Exp {}} {m''},
          m'.subsumes m2 -> Exp.WfInHeap b' m'.heap -> BigStep m' b' s v m'' ->
          TraceOk s (C2 ∪ capsOf (Trace.allocList t)) := by
        intro m' s v m'' hsub' hwf' hbs
        have hwfb' := step_preserves_wf hstep_b.toStep hwf_b
        obtain ⟨ms, hbs_m2, _, _⟩ := hbs.simulate_down hsub' hwfb'
        have hfull : BigStep m1 b (t ++ s) v ms := BigStep.head_expand hstep_b hbs_m2
        have htok : TraceOk (t ++ s) C2 := hb2 (Memory.subsumes_refl _) hwf_b hfull
        have := TraceOkFrom.absorb_exempt (TraceOkFrom.split_append htok)
        rwa [List.append_nil] at this
      -- Separation of the LEFT budget `C1` from the grown RIGHT budget.
      have hni_grown : CapabilitySet.Noninterference C1 (C2 ∪ capsOf (Trace.allocList t)) := by
        refine CapabilitySet.Noninterference.ni_symm (CapabilitySet.Noninterference.ni_union
          (CapabilitySet.Noninterference.ni_symm hni)
          (CapabilitySet.noninterference_capsOf_fresh ?_))
        intro l hl mu' hm
        exact hpres1 mu' l hm (step_allocd_fresh hstep_b.toStep (Trace.mem_allocList.mp hl))
      -- `WfInHeap b' m2.heap` (used by `hrs2'`'s `Safe.lift` below).
      have hwf_b2' : Exp.WfInHeap b' m2.heap := step_preserves_wf hstep_b.toStep hwf_b
      -- A cell `b'` EXTERNALLY touches in a run `s` from `m'' ⊒ m2` (while live in `m2`)
      -- has some covering mode in the grown budget.
      have hcov_of_touch : ∀ {m'' : Memory} {s : Trace} {v : Exp {}} {mf : Memory} {l : Nat}
          {bb : Bool}, m''.subsumes m2 -> BigStep m'' b' s v mf ->
          m2.lookup l = some (.capability (.mcell bb .live)) -> Trace.extTouches s l ->
          ∃ cm, (C2 ∪ capsOf (Trace.allocList t)).covers cm l := by
        intro m'' s v mf l bb hsub'' hbs_b' hlive htouch
        have hnal : ¬ Trace.allocd s l := fun ha => by
          have hnone : m''.heap l = none := hbs_b'.alloc_fresh ha
          have : m2.heap l = none := Heap.none_of_subsumes_none hsub'' hnone
          rw [show m2.lookup l = m2.heap l from rfl, this] at hlive; cases hlive
        obtain ⟨cm, hext⟩ :=
          Trace.extTouchesMode_of_touched hnal (Trace.touched_of_extTouches htouch)
        exact ⟨cm, (hb2_robust hsub'' (Exp.wf_monotonic hsub'' hwf_b2') hbs_b')
          |>.covers_of_extTouchesMode hext⟩
      refine Safe.par (C1 := C1) (C2 := C2 ∪ capsOf (Trace.allocList t))
        hsafe_a2 ?h2' ?hb1' (@hb2_robust) ?hrs2' ?hpres1' ?hpres2' hni_grown
      case h2' =>
        -- The LEFT branch `a` is an answer, so any `BigStep` of it from `m2` is the
        -- trivial self-run (`isAns_inv`): empty trace, memory unchanged.  Then the
        -- continuation is just `Safe m2 b'`.
        intro t1 v1 m1' hbs_a2
        obtain ⟨rfl, rfl, rfl⟩ := BigStep.isAns_inv hbs_a2 hans_a
        exact hse_b2'
      case hb1' =>
        intro m' s v m'' hsub' hwf' hbs
        exact hb1 (Memory.subsumes_trans hsub' hsub21) hwf' hbs
      case hrs2' =>
        -- `b'` safe at any `m' ⊒ m2` compatible with the grown budget: lift `Safe m2 b'`
        -- with the bound-driven liveness frame (a touched `b'`-cell, covered by the
        -- grown budget and present in `m'`, is live there by compatibility `hc`).
        intro m' hsub' hc
        refine Safe.lift hse_b2' hsub' (Q := fun s val m => BigStep m2 b' s val m)
          (fun _ _ _ h => h) ?_ hwf_b2'
        intro s v m _ hbs_b' l b hlive htouch
        obtain ⟨cm, hcov⟩ := hcov_of_touch (Memory.subsumes_refl _) hbs_b' hlive htouch
        obtain ⟨mu', hmem', _⟩ := CapabilitySet.covers_imp_exists_hasmem hcov
        -- `l` is present in `m'` (live in `m2`, `m' ⊒ m2`); compatibility `hc` makes it live.
        obtain ⟨c', hc'', hsubc⟩ := hsub' l (.capability (.mcell b .live)) hlive
        cases c' with
        | val _ => simp [Cell.subsumes] at hsubc
        | masked => simp [Cell.subsumes] at hsubc
        | capability cc =>
          cases cc with
          | mcell b'' ℓ'' =>
            have hℓ := hc mu' l b'' ℓ'' hmem' hc''
            exact ⟨b'', by rw [hℓ] at hc''; exact hc''⟩
          | basic => simp [Cell.subsumes] at hsubc
      case hpres1' =>
        intro mu l hmem
        exact (fun hc => hpres1 mu l hmem (Heap.none_of_subsumes_none hsub21 hc))
      case hpres2' =>
        intro mu l hmem
        rcases CapabilitySet.hasmem_union_iff.mp hmem with h2m | hA
        · exact (fun hc => hpres2 mu l h2m (Heap.none_of_subsumes_none hsub21 hc))
        · exact step_allocd_present hstep_b.toStep (Trace.mem_allocList.mp (capsOf_hasmem hA))
  | step_par_join _ _ =>
    -- `par a b → .unit`; the canonical unit result is an answer, hence trivially safe.
    intro _ _ _ _
    exact Safe.ans (Exp.IsAns.is_val Exp.IsVal.unit)
  | step_rename =>
    intro _ _ _ hsafe
    cases hsafe with
    | letin _ _ _ h_var => exact h_var BigStep.bs_var
    | ans hans => cases hans with | is_val hv => cases hv
  | step_lift hv hwf_v hfresh =>
    intro _ _ _ hsafe
    cases hsafe with
    | letin _ _ h_val _ => exact h_val (BigStep.bs_val hv) hv hwf_v _ hfresh
    | ans hans => cases hans with | is_val hv2 => cases hv2
  | step_unpack =>
    intro _ _ _ hsafe
    cases hsafe with
    | unpack _ _ h_val => exact h_val BigStep.bs_pack
    | ans hans => cases hans with | is_val hv => cases hv

/-- **Preservation of `Eval` (sequential small-step).**  Because the postcondition
    is keyed on the *whole* trace, a step *shifts* it by the step's own trace `t`:
    every answer reached after the step prepends `t` as seen from before it. -/
theorem step_preserves_eval {t : Trace} {m1 e1 m2 e2} {Q : Tpost}
    (he : Eval m1 e1 Q) (hwf : Exp.WfInHeap e1 m1.heap) (hdf : ∀ l, TraceItem.dealloc l ∉ t)
    (hal : m1.AllLive) (hstep : SeqStep t m1 e1 m2 e2) :
    Eval m2 e2 (fun t' => Q (t ++ t')) := by
  refine ⟨step_preserves_safe hstep hwf hdf hal he.1, ?_⟩
  intro t' v m' hbs
  exact he.2 (t ++ t') v m' (BigStep.head_expand hstep hbs)

/-- `SeqReduce`-level head expansion: fold `BigStep.head_expand` over a reduction. -/
theorem BigStep.reduce_expand {t : Trace} {m1 e1 m2 e2}
    (hred : SeqReduce t m1 e1 m2 e2) :
    ∀ {t' : Trace} {v : Exp {}} {m' : Memory},
      BigStep m2 e2 t' v m' → BigStep m1 e1 (t ++ t') v m' := by
  induction hred with
  | refl => intro t' v m' hbs; exact hbs
  | step hstep _ ih =>
    intro t' v m' hbs
    rw [List.append_assoc]
    exact BigStep.head_expand hstep (ih hbs)

/-- Sequential reduction preserves big-step safety (iterate `step_preserves_safe`).
    Threads `Exp.WfInHeap` and a drop-free hypothesis (no `dealloc` anywhere in the
    trace), both needed by `step_preserves_safe`'s `par` cases.  The forward Step
    preservation lemmas are reused via `SeqStep.toStep`. -/
theorem reduce_preserves_safe {t : Trace} {m1 e1 m2 e2}
    (hred : SeqReduce t m1 e1 m2 e2) (hwf : Exp.WfInHeap e1 m1.heap)
    (hdf : ∀ l, TraceItem.dealloc l ∉ t) (hal : m1.AllLive) : Safe m1 e1 → Safe m2 e2 := by
  induction hred with
  | refl => exact id
  | @step t1 m1 e1 m2 e2 t2 m3 e3 hstep hred_rest ih =>
    intro hsafe
    have hdf1 : ∀ l, TraceItem.dealloc l ∉ t1 := fun l hm => hdf l (List.mem_append_left _ hm)
    have hdf2 : ∀ l, TraceItem.dealloc l ∉ t2 := fun l hm => hdf l (List.mem_append_right _ hm)
    have hal2 := step_preserves_allLive hstep.toStep hdf1 hal
    exact ih (step_preserves_wf hstep.toStep hwf) hdf2 hal2
      (step_preserves_safe hstep hwf hdf1 hal hsafe)

/-- **Preservation of `Eval` (sequential reduction).**  As `step_preserves_eval`,
    with the postcondition shifted by the reduction's accumulated trace. -/
theorem reduce_preserves_eval {t : Trace} {m1 e1 m2 e2} {Q : Tpost}
    (he : Eval m1 e1 Q) (hwf : Exp.WfInHeap e1 m1.heap) (hdf : ∀ l, TraceItem.dealloc l ∉ t)
    (hal : m1.AllLive) (hred : SeqReduce t m1 e1 m2 e2) :
    Eval m2 e2 (fun t' => Q (t ++ t')) := by
  refine ⟨reduce_preserves_safe hred hwf hdf hal he.1, ?_⟩
  intro t' v m' hbs
  exact he.2 (t ++ t') v m' (BigStep.reduce_expand hred hbs)

/-- **Adequacy.**  If `Eval m e Q` and `e` reduces (sequential small-step) to an
    answer `a` emitting trace `t`, then `Q t a m'`: the reduction is realized as a
    `BigStep` (`reduce_to_bigstep`), to which the preservation half of `Eval`
    applies. -/
theorem eval_to_reduce {t : Trace} {m e m' a} {Q : Tpost}
    (heval : Eval m e Q) (hans : a.IsAns) (hred : SeqReduce t m e m' a) : Q t a m' :=
  heval.2 t a m' (reduce_to_bigstep hred hans)

/-- **Termination to an answer (sequential small-step).**  A `Safe` configuration
    reduces (sequentially) to an answer.  This is the small-step counterpart of
    `Safe.has_answer`; the `letin`/`unpack` heads are classified by `h_ans` on the
    big-step realization of the head's own reduction (`reduce_to_bigstep`).  The
    `par` case schedules left-then-right (the `par` answer is `.unit`), matching
    `SeqStep`'s gated `step_par_right`. -/
theorem Safe.has_reduction {m : Memory} {e : Exp {}} (h : Safe m e) :
    ∃ t m' a, SeqReduce t m e m' a ∧ a.IsAns := by
  induction h with
  | ans hans => exact ⟨_, _, _, SeqReduce.refl, hans⟩
  | alloc hlk =>
    obtain ⟨l, hfresh⟩ := Memory.exists_fresh _
    exact ⟨_, _, _, SeqReduce.step (SeqStep.step_alloc hlk hfresh) SeqReduce.refl,
      Exp.IsAns.is_val Exp.IsVal.pack⟩
  | @apply cs T e_abs hv R y m x hlk _ ih =>
    obtain ⟨t, m', a, hred, hans⟩ := ih
    obtain ⟨y', rfl⟩ := Var.free_cases y
    exact ⟨_, _, _, SeqReduce.step (SeqStep.step_apply hlk) hred, hans⟩
  | invoke hlkx hlky =>
    exact ⟨_, _, _, SeqReduce.step (SeqStep.step_invoke hlkx hlky) SeqReduce.refl,
      Exp.IsAns.is_val Exp.IsVal.unit⟩
  | tapply hlk _ ih =>
    obtain ⟨t, m', a, hred, hans⟩ := ih
    exact ⟨_, _, _, SeqReduce.step (SeqStep.step_tapply hlk) hred, hans⟩
  | capply hlk _ ih =>
    obtain ⟨t, m', a, hred, hans⟩ := ih
    exact ⟨_, _, _, SeqReduce.step (SeqStep.step_capply hlk) hred, hans⟩
  | unwrap hlk _ ih =>
    obtain ⟨t, m', a, hred, hans⟩ := ih
    exact ⟨_, _, _, SeqReduce.step (SeqStep.step_unwrap hlk) hred, hans⟩
  | letin _ h_ans _ _ ih1 ih_val ih_var =>
    obtain ⟨t1, m1, a1, hred1, hans1⟩ := ih1
    have hbs1 := reduce_to_bigstep hred1 hans1
    obtain ⟨hsa, hwf⟩ := h_ans _ _ _ hbs1
    rcases Exp.isSimpleAns_cases hsa with hv | ⟨n, rfl⟩
    · obtain ⟨l, hfresh⟩ := Memory.exists_fresh m1
      obtain ⟨t2, m2, a2, hred2, hans2⟩ := ih_val hbs1 hv hwf l hfresh
      exact ⟨_, _, _, seqreduce_trans (seqreduce_ctx_letin hred1)
        (SeqReduce.step (SeqStep.step_lift hv hwf hfresh) hred2), hans2⟩
    · obtain ⟨t2, m2, a2, hred2, hans2⟩ := ih_var hbs1
      exact ⟨_, _, _, seqreduce_trans (seqreduce_ctx_letin hred1)
        (SeqReduce.step SeqStep.step_rename hred2), hans2⟩
  | unpack _ h_ans _ ih1 ih_val =>
    obtain ⟨t1, m1, a1, hred1, hans1⟩ := ih1
    have hbs1 := reduce_to_bigstep hred1 hans1
    obtain ⟨hpack, hwf⟩ := h_ans _ _ _ hbs1
    obtain ⟨cs, n, rfl⟩ := Exp.isPack_cases hpack
    obtain ⟨t2, m2, a2, hred2, hans2⟩ := ih_val hbs1
    exact ⟨_, _, _, seqreduce_trans (seqreduce_ctx_unpack hred1)
      (SeqReduce.step SeqStep.step_unpack hred2), hans2⟩
  | read hlkx hlky =>
    exact ⟨_, _, _, SeqReduce.step (SeqStep.step_read hlkx hlky) SeqReduce.refl,
      Exp.IsAns.is_val (by split <;> constructor)⟩
  | write_true hx hy =>
    exact ⟨_, _, _, SeqReduce.step (SeqStep.step_write_true hx hy) SeqReduce.refl,
      Exp.IsAns.is_val Exp.IsVal.unit⟩
  | write_false hx hy =>
    exact ⟨_, _, _, SeqReduce.step (SeqStep.step_write_false hx hy) SeqReduce.refl,
      Exp.IsAns.is_val Exp.IsVal.unit⟩
  | drop hx =>
    exact ⟨_, _, _, SeqReduce.step (SeqStep.step_drop hx) SeqReduce.refl,
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
            exact ⟨_, _, _, SeqReduce.step
              (SeqStep.step_cond_var_true (hv := hsimple) (R := reach)
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
            exact ⟨_, _, _, SeqReduce.step
              (SeqStep.step_cond_var_false (hv := hsimple) (R := reach)
                (by simp [Memory.lookup, hcell])) hred, hans⟩
        | capability => simp [resolve, hcell] at hbfalse
        | masked => simp [resolve, hcell] at hbfalse
  | par _ _ _ _ _ _ _ _ ih1 ih2 _ =>
    -- Build the canonical sequential (left-then-right-then-join) reduction to an
    -- answer: run e1 fully (ih1), run e2 from e1's answer-memory (ih2, fed e1's
    -- big-step answer via `reduce_to_bigstep`), lift each through the `SeqReduce` par
    -- congruences (the right congruence needs e1's answer `hansa`), then join to `.unit`.
    obtain ⟨ta, ma, aans, hreda, hansa⟩ := ih1
    obtain ⟨tb, mb, bans, hredb, hansb⟩ := ih2 (reduce_to_bigstep hreda hansa)
    exact ⟨_, _, _,
      seqreduce_trans (seqreduce_par_left hreda)
        (seqreduce_trans (seqreduce_par_right hansa hredb)
          (SeqReduce.step (SeqStep.step_par_join hansa hansb) SeqReduce.refl)),
      Exp.IsAns.is_val Exp.IsVal.unit⟩

/-- Answer existence (sequential small-step): `Eval m e Q` reduces to an answer
    satisfying `Q`.  Combine `Safe.has_reduction` with the adequacy bridge. -/
theorem eval_reduce_exists_answer {m : Memory} {e : Exp {}} {Q : Tpost}
    (heval : Eval m e Q) :
    ∃ t m' a, SeqReduce t m e m' a ∧ a.IsAns ∧ Q t a m' := by
  obtain ⟨t, m', a, hred, hans⟩ := heval.1.has_reduction
  exact ⟨t, m', a, hred, hans, heval.2 t a m' (reduce_to_bigstep hred hans)⟩

theorem not_mutated_refl {m : Memory} : m.not_mutated m := fun _ _ _ hinit => hinit

theorem not_mutated_trans {m1 m2 m3 : Memory}
    (h12 : m1.not_mutated m2) (h23 : m2.not_mutated m3) :
    m1.not_mutated m3 := fun l b ℓ hinit => h23 l b ℓ (h12 l b ℓ hinit)

/-- A single step whose trace contains no write (`access .epsilon`) and no
    deallocation event does not mutate any mutable cell. -/
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

/- Scope and known limitations of `par` adequacy:
   * This bridge is stated for the SEQUENTIAL schedule `SeqStep`/`SeqReduce`, for
     which the big-step `bs_par` (left-then-right) is exact — so `head_expand` and
     all preservation/progress results are `sorry`-free.  Lifting adequacy to the
     full interleaving `Step` requires the standardization theorem: every `Step` run
     is permutation-equivalent (Mazurkiewicz) to a `SeqStep` run, via the diamond
     `BigStep.step_run_commute` and `Safe.par`'s separation.  That is the separate
     development (B); `SeqStep.toStep` is its trivial half.
   * `step_preserves_safe` keeps the frozen `par` branch's robust safety (`hrs2`)
     applicable by maintaining `AllLive` across steps, which needs a drop-free (no
     `dealloc`) hypothesis.  So `adequacy_platform` / `immutability_adequacy_platform`
     carry a dealloc-free side-condition.  Removing it needs separation-based framing
     of the frozen branch's cells (operational ownership transfer through `drop`). -/

end CoreCapybara
