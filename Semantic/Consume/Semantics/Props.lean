import Semantic.Consume.Semantics.SmallStep
import Semantic.Consume.Semantics.BigStep
namespace Consume

/-- The result of looking up a variable in the heap is deterministic. -/
theorem Heap.lookup_deterministic {H : Heap}
  (hlookup1 : H l = some v1)
  (hlookup2 : H l = some v2) :
  v1 = v2 := by grind

/-- The result of looking up a variable in the memory is deterministic. -/
theorem Memory.lookup_deterministic {m : Memory}
  (hlookup1 : m.lookup l = some v1)
  (hlookup2 : m.lookup l = some v2) :
  v1 = v2 := by
  cases m
  simp only [Memory.lookup] at hlookup1 hlookup2
  apply Heap.lookup_deterministic hlookup1 hlookup2

/- COMMENTED OUT (Step refactor): `Step` is no longer indexed by a capability
  set upper bound — it now records an `EvalTrace`. "Monotonicity in the authority
  `R`" is therefore vacuous/meaningless: there is no `R` to weaken. Preserved for
  future reference; a trace-aware analogue (if needed) would relate two traces.

/-- Step is monotonic with respect to capability sets:
    if a step can happen under authority R1, it can happen under any larger authority R2. -/
theorem step_capability_set_monotonic {R1 R2 : CapabilitySet}
  (hstep : Step R1 m e m' e') (hsub : R1 ⊆ R2) :
  Step R2 m e m' e' := by
  induction hstep with
  | step_apply hlookup =>
    apply Step.step_apply hlookup
  | step_invoke hmem hlookup_x hlookup_y =>
    exact Step.step_invoke (CapabilitySet.subset_preserves_covers hsub hmem) hlookup_x hlookup_y
  | step_tapply hlookup =>
    apply Step.step_tapply hlookup
  | step_capply hlookup =>
    apply Step.step_capply hlookup
  | step_cond_var_true hlookup =>
    apply Step.step_cond_var_true hlookup
  | step_cond_var_false hlookup =>
    apply Step.step_cond_var_false hlookup
  | step_read hmem hlookup_reader hlookup_cell =>
    apply Step.step_read (CapabilitySet.subset_preserves_covers hsub hmem)
      hlookup_reader hlookup_cell
  | step_write_true hmem hx hy =>
    apply Step.step_write_true (CapabilitySet.subset_preserves_covers hsub hmem) hx hy
  | step_write_false hmem hx hy =>
    apply Step.step_write_false (CapabilitySet.subset_preserves_covers hsub hmem) hx hy
  | step_ctx_letin _ ih =>
    apply Step.step_ctx_letin
    exact ih hsub
  | step_ctx_unpack _ ih =>
    apply Step.step_ctx_unpack
    exact ih hsub
  | step_rename =>
    apply Step.step_rename
  | step_lift hv hwf hfresh =>
    apply Step.step_lift hv hwf hfresh
  | step_unpack =>
    apply Step.step_unpack

/-- Reduce (multi-step reduction) is monotonic with respect to capability sets:
    if a reduction can happen under authority R1, it can happen under any larger authority R2. -/
theorem small_step_capability_set_monotonic {R1 R2 : CapabilitySet}
  (hred : Reduce R1 m e m' e') (hsub : R1 ⊆ R2) :
  Reduce R2 m e m' e' := by
  induction hred generalizing R2 with
  | refl =>
    apply Reduce.refl
  | step h rest ih =>
    exact Reduce.step (step_capability_set_monotonic h hsub) (ih hsub)
-/

/-- Helper: Congruence for Reduce in letin context. The trace is preserved. -/
theorem reduce_ctx_letin
  (hred : Reduce m e1 tr m' e1') :
  Reduce m (.letin e1 e2) tr m' (.letin e1' e2) := by
  induction hred with
  | refl => apply Reduce.refl
  | step h rest ih =>
    apply Reduce.step
    · apply Step.step_ctx_letin h
    · exact ih

/-- Helper: Congruence for Reduce in unpack context. The trace is preserved. -/
theorem reduce_ctx_unpack
  (hred : Reduce m e1 tr m' e1') :
  Reduce m (.unpack e1 e2) tr m' (.unpack e1' e2) := by
  induction hred with
  | refl => apply Reduce.refl
  | step h rest ih =>
    apply Reduce.step
    · apply Step.step_ctx_unpack h
    · exact ih

/-- Helper: Variables cannot step, so reduction is reflexive. -/
theorem reduce_var_inv
  (hred : Reduce m (.var x) tr m' v') :
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
  (hstep : Step m1 e1 tr m2 e2) :
  m2.subsumes m1 := by
  induction hstep with
  | step_alloc _ hfresh => exact Memory.extend_mcell_subsumes _ _ _ hfresh
  | step_apply => exact Memory.subsumes_refl _
  | step_invoke => exact Memory.subsumes_refl _
  | step_tapply => exact Memory.subsumes_refl _
  | step_capply => exact Memory.subsumes_refl _
  | step_cond_true _ => exact Memory.subsumes_refl _
  | step_cond_false _ => exact Memory.subsumes_refl _
  | step_read _ _ => exact Memory.subsumes_refl _
  | step_write_true hx _ => exact Memory.update_mcell_subsumes _ _ _ _ ⟨_, hx⟩
  | step_write_false hx _ => exact Memory.update_mcell_subsumes _ _ _ _ ⟨_, hx⟩
  | step_drop hx => exact Memory.drop_mcell_subsumes _ _ ⟨_, hx⟩
  | step_ctx_letin _ ih => exact ih
  | step_ctx_unpack _ ih => exact ih
  | step_rename => exact Memory.subsumes_refl _
  | step_lift hv hwf hfresh =>
    exact Memory.extend_val_subsumes _ _ _ hwf rfl hfresh
  | step_unpack => exact Memory.subsumes_refl _

/-- Helper: Reduction preserves memory subsumption. -/
theorem reduce_memory_monotonic
  (hred : Reduce m1 e1 tr m2 e2) :
  m2.subsumes m1 := by
  induction hred with
  | refl => exact Memory.subsumes_refl _
  | step h rest ih =>
    exact Memory.subsumes_trans ih (step_memory_monotonic h)

theorem step_var_absurd
  (hstep : Step m (.var x) tr m' e') : False := by
  cases hstep

theorem step_val_absurd
  (hv : Exp.IsSimpleVal v)
  (hstep : Step m v tr m' e') :
  False := by
  cases hv <;> cases hstep

theorem step_ans_absurd
  (hans : e.IsAns)
  (hstep : Step m e tr m' e') :
  False := by
  cases hans with
  | is_var => exact step_var_absurd hstep
  | is_val hv => cases hv <;> cases hstep

theorem reduce_ans_eq
  (hans : e.IsAns)
  (hred : Reduce m e tr m' e') :
  m = m' ∧ e = e' := by
  induction hred with
  | refl => exact ⟨rfl, rfl⟩
  | step h rest ih =>
    have habsurd : False := step_ans_absurd hans h
    contradiction

theorem reduce_letin_inv
  (hred : Reduce m (.letin e1 e2) tr m' a)
  (hans : a.IsAns) :
  (∃ m0 y0 tr1 tr2,
     Reduce m e1 tr1 m0 (.var (.free y0)) ∧
     Reduce m0 (e2.subst (Subst.openVar (.free y0))) tr2 m' a) ∨
  (∃ (m0 : Memory) (v0 : Exp {}) (hv : v0.IsSimpleVal) (hwf : Exp.WfInHeap v0 m0.heap)
     (l0 : Nat) (hfresh : m0.heap l0 = none) (tr1 : EvalTrace) (tr2 : EvalTrace),
    Reduce m e1 tr1 m0 v0 ∧
    Reduce
      (m0.extend l0 ⟨v0, hv, compute_reachability m0.heap v0 hv⟩ hwf rfl hfresh)
      (e2.subst (Subst.openVar (.free l0))) tr2
      m' a) := by
  -- Generalize the letin expression to enable induction
  generalize hgen : Exp.letin e1 e2 = e_full at hred
  induction hred generalizing e1 e2 with
  | refl =>
    -- Base case: e_full = a, but a is an answer and e_full = .letin e1 e2
    -- letin is never an answer, contradiction
    rw [←hgen] at hans
    cases hans with
    | is_val hv => cases hv
  | step hstep rest ih =>
    -- We have a step from e_full, and e_full = .letin e1 e2
    rw [←hgen] at hstep
    -- Case analysis on what step was taken from letin
    cases hstep with
    | step_ctx_letin hstep_e1 =>
      -- e1 steps to e1', and we have rest: Reduce m2 (.letin e1' e2) _ m' a
      -- Apply IH to the rest of the reduction
      rename_i e1'
      have ih_result := ih hans rfl
      -- Extract the result from IH, prepending the e1 step
      cases ih_result with
      | inl h_var =>
        obtain ⟨m0, y0, tr1, tr2, hred_e1', hred_body⟩ := h_var
        exact Or.inl ⟨m0, y0, _, tr2, Reduce.step hstep_e1 hred_e1', hred_body⟩
      | inr h_val =>
        obtain ⟨m0, v0, hv, hwf, l0, hfresh, tr1, tr2, hred_e1', hred_body⟩ := h_val
        exact Or.inr ⟨m0, v0, hv, hwf, l0, hfresh, _, tr2,
          Reduce.step hstep_e1 hred_e1', hred_body⟩
    | step_rename =>
      -- e1 = .var (.free y); reduction to it is reflexive, body continues via rest
      exact Or.inl ⟨_, _, _, _, Reduce.refl, rest⟩
    | step_lift hv hwf hfresh =>
      -- e1 is a simple value, allocated at l; reduction to it is reflexive
      exact Or.inr ⟨_, _, hv, hwf, _, hfresh, _, _, Reduce.refl, rest⟩

theorem step_preserves_wf
  (hstep : Step m1 e1 tr m2 e2)
  (hwf : e1.WfInHeap m1.heap) :
  e2.WfInHeap m2.heap := by
  cases hstep with
  | step_alloc hlookup hfresh =>
    -- e1 = .alloc (.free x), e2 = .pack (.var (.M .epsilon) (.free l)) (.free l)
    -- The fresh location l now holds a live mutable cell in the extended heap.
    apply Exp.WfInHeap.wf_pack
    · exact CaptureSet.WfInHeap.wf_var_free (Memory.extend_mcell_lookup hfresh)
    · exact Var.WfInHeap.wf_free (Memory.extend_mcell_lookup hfresh)
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
  | step_invoke hlookup_x hlookup_y =>
    -- e1 = .app (.free x) (.free y), e2 = .unit
    -- Unit is always well-formed
    apply Exp.WfInHeap.wf_unit
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
  | step_cond_true hres =>
    have ⟨_, hwf_then, _⟩ := Exp.wf_inv_cond hwf
    exact hwf_then
  | step_cond_false hres =>
    have ⟨_, _, hwf_else⟩ := Exp.wf_inv_cond hwf
    exact hwf_else
  | step_read hreader hcell =>
    -- e1 = .read (.free x), e2 = (if b then .btrue else .bfalse)
    -- Boolean values are always well-formed
    split
    · exact Exp.WfInHeap.wf_btrue
    · exact Exp.WfInHeap.wf_bfalse
  | step_write_true hx hy =>
    -- e1 = .write (.free x) (.free y), e2 = .unit
    -- Unit is always well-formed in any heap
    exact Exp.WfInHeap.wf_unit
  | step_write_false hx hy =>
    -- e1 = .write (.free x) (.free y), e2 = .unit
    -- Unit is always well-formed in any heap
    exact Exp.WfInHeap.wf_unit
  | step_drop hx =>
    -- e1 = .drop (.free x), e2 = .unit
    exact Exp.WfInHeap.wf_unit
  | step_ctx_letin hstep_e1 =>
    -- e1 = .letin e1' e2', e2 = .letin e1'' e2'
    -- Use IH recursively
    have ⟨hwf_e1', hwf_e2'⟩ := Exp.wf_inv_letin hwf
    have hwf_e1'' := step_preserves_wf hstep_e1 hwf_e1'
    -- Memory might have changed, need monotonicity
    have hsub := step_memory_monotonic hstep_e1
    have hwf_e2'' := Exp.wf_monotonic hsub hwf_e2'
    apply Exp.WfInHeap.wf_letin hwf_e1'' hwf_e2''
  | step_ctx_unpack hstep_e1 =>
    -- e1 = .unpack e1' e2', e2 = .unpack e1'' e2'
    -- Use IH recursively
    have ⟨hwf_e1', hwf_e2'⟩ := Exp.wf_inv_unpack hwf
    have hwf_e1'' := step_preserves_wf hstep_e1 hwf_e1'
    -- Memory might have changed, need monotonicity
    have hsub := step_memory_monotonic hstep_e1
    have hwf_e2'' := Exp.wf_monotonic hsub hwf_e2'
    apply Exp.WfInHeap.wf_unpack hwf_e1'' hwf_e2''
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
      exact Var.WfInHeap.wf_free (by
        change
          (m1.heap.extend l ⟨v, hv, compute_reachability m1.heap v hv⟩) l =
            some (.val ⟨v, hv, compute_reachability m1.heap v hv⟩)
        exact Heap.extend_lookup_eq _ _ _)
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

theorem reduce_preserves_wf
  (hred : Reduce m1 e1 tr m2 e2)
  (hwf : e1.WfInHeap m1.heap) :
  e2.WfInHeap m2.heap := by
  induction hred with
  | refl => exact hwf
  | step hstep rest ih =>
    have hwf_mid := step_preserves_wf hstep hwf
    exact ih hwf_mid

/-- Inversion lemma for reduction of unpack expressions -/
theorem reduce_unpack_inv
  (hred : Reduce m (.unpack e1 e2) tr m' a)
  (hans : a.IsAns) :
  ∃ (m0 : Memory) (cs : CaptureSet {}) (x : Nat) (tr1 tr2 : EvalTrace),
    Reduce m e1 tr1 m0 (.pack cs (.free x)) ∧
    Reduce m0 (e2.subst (Subst.unpack cs (.free x))) tr2 m' a := by
  -- Use generalization to make induction work
  generalize hgen : Exp.unpack e1 e2 = e_full at hred
  induction hred generalizing e1 e2 with
  | refl =>
    -- Base case: no reduction, but unpack is not an answer
    rw [←hgen] at hans
    cases hans; rename_i hv
    cases hv
  | step hstep rest ih =>
    -- Step case: analyze the step from unpack
    rw [←hgen] at hstep
    cases hstep with
    | step_ctx_unpack hstep_e1 =>
      -- e1 steps to e1', then continue with induction
      rename_i e1'
      have ih_result := ih (e1 := e1') (e2 := e2) hans rfl
      obtain ⟨m0, cs, x, tr1, tr2, hred_e1', hred_body⟩ := ih_result
      -- Prepend the e1 step to the reduction reaching the pack
      exact ⟨m0, cs, x, _, tr2, Reduce.step hstep_e1 hred_e1', hred_body⟩
    | step_unpack =>
      -- e1 is already .pack cs (.free x); reduction to it is reflexive
      rename_i cs x
      exact ⟨_, cs, x, [], _, Reduce.refl, rest⟩

inductive IsProgressive : CapabilitySet -> Memory -> Exp {} -> Prop where
| done :
  e.IsAns ->
  IsProgressive R m e
| step :
  Step m e tr m' e' ->
  IsProgressive C m e

/-- If an answer has an evaluation, then the postcondition holds for it. -/
theorem eval_ans_holds_post
  (heval : Eval C m e Q)
  (hans : e.IsAns) :
  Q e m := by
  cases heval with
  | eval_pack _ hQ => exact hQ
  | eval_val hv hQ => exact hQ
  | eval_var hQ => exact hQ
  | eval_alloc => cases hans; rename_i hv; cases hv
  | eval_drop => cases hans; rename_i hv; cases hv
  | eval_apply => cases hans; rename_i hv; cases hv
  | eval_invoke => cases hans; rename_i hv; cases hv
  | eval_tapply => cases hans; rename_i hv; cases hv
  | eval_capply => cases hans; rename_i hv; cases hv
  | eval_letin => cases hans; rename_i hv; cases hv
  | eval_unpack => cases hans; rename_i hv; cases hv
  | eval_cond =>
    cases hans with
    | is_val hv => cases hv
  | eval_read => cases hans; rename_i hv; cases hv
  | eval_write_true => cases hans; rename_i hv; cases hv
  | eval_write_false => cases hans; rename_i hv; cases hv

theorem eval_implies_progressive
  (heval : Eval C m e Q) :
  IsProgressive C m e := by
  induction heval with
  | eval_pack _ _ =>
    -- pack is a value, so it's an answer
    apply IsProgressive.done
    exact Exp.IsAns.is_val Exp.IsVal.pack
  | eval_alloc hlookup h_post =>
    -- e = .alloc (.free x): allocate a fresh mutable cell via step_alloc
    obtain ⟨l, hfresh⟩ := Memory.exists_fresh _
    exact IsProgressive.step (Step.step_alloc hlookup hfresh)
  | eval_val hv hQ =>
    -- e is a value, so it's an answer
    apply IsProgressive.done
    exact Exp.IsAns.is_val hv.to_IsVal
  | eval_var hQ =>
    -- e is a variable, so it's an answer
    apply IsProgressive.done
    exact Exp.IsAns.is_var
  | eval_apply hlookup _ _ =>
    -- e = .app (.free x) y, can step via step_apply (any argument variable y)
    exact IsProgressive.step (Step.step_apply hlookup)
  | eval_invoke _ hlookup_x hlookup_y _ =>
    -- e = .app (.free x) (.free y), can step via step_invoke
    exact IsProgressive.step (Step.step_invoke hlookup_x hlookup_y)
  | eval_tapply hlookup _ _ =>
    -- e = .tapp (.free x) S, can step via step_tapply
    exact IsProgressive.step (Step.step_tapply hlookup)
  | eval_capply hlookup _ _ =>
    -- e = .capp (.free x) CS, can step via step_capply
    exact IsProgressive.step (Step.step_capply hlookup)
  | eval_letin hpred hbool eval_e1 h_nonstuck h_val h_var hseq hagg ih_e1 _ _ =>
    -- e = .letin e1 e2
    -- By IH, e1 is progressive
    cases ih_e1 with
    | done hans =>
      -- e1 is an answer; by h_nonstuck it is a simple answer
      have hQ1 := eval_ans_holds_post eval_e1 hans
      have ⟨hsimple_ans, hwf⟩ := h_nonstuck hQ1
      cases hsimple_ans with
      | is_simple_val hv =>
        -- e1 is a simple value: lift it into a fresh location via step_lift
        obtain ⟨l0, hfresh⟩ := Memory.exists_fresh _
        exact IsProgressive.step (Step.step_lift (l := l0) hv hwf hfresh)
      | is_var =>
        -- e1 is a variable; it is free since we are in the empty signature
        rename_i x_var
        cases x_var with
        | bound idx => cases idx
        | free y =>
          exact IsProgressive.step Step.step_rename
    | step hstep =>
      -- e1 can step, so letin e1 e2 can step via step_ctx_letin
      exact IsProgressive.step (Step.step_ctx_letin hstep)
  | eval_unpack hpred hbool eval_e1 h_nonstuck h_val hseq hagg ih_e1 _ =>
    -- e = .unpack e1 e2
    cases ih_e1 with
    | done hans =>
      -- e1 is an answer; by h_nonstuck it is a pack
      have hQ1 := eval_ans_holds_post eval_e1 hans
      have ⟨hpack, hwf⟩ := h_nonstuck hQ1
      cases hpack with
      | pack =>
        rename_i cs x_var
        cases x_var with
        | bound idx => cases idx
        | free x =>
          exact IsProgressive.step Step.step_unpack
    | step hstep =>
      -- e1 can step, so unpack e1 e2 can step via step_ctx_unpack
      exact IsProgressive.step (Step.step_ctx_unpack hstep)
  | eval_cond hres _ _ _ _ =>
    -- e = .cond x e2 e3; the guard resolves to a boolean, so we can branch
    cases hres with
    | inl htrue => exact IsProgressive.step (Step.step_cond_true htrue)
    | inr hfalse => exact IsProgressive.step (Step.step_cond_false hfalse)
  | eval_read _ hlookup_reader hlookup_cell _ =>
    -- e = .read (.free x), can step via step_read
    exact IsProgressive.step (Step.step_read hlookup_reader hlookup_cell)
  | eval_write_true _ hx hy _ =>
    -- e = .write (.free x) (.free y), can step via step_write_true
    exact IsProgressive.step (Step.step_write_true hx hy)
  | eval_write_false _ hx hy _ =>
    -- e = .write (.free x) (.free y), can step via step_write_false
    exact IsProgressive.step (Step.step_write_false hx hy)
  | eval_drop hx _ _ =>
    -- e = .drop (.free x), can step via step_drop
    exact IsProgressive.step (Step.step_drop hx)

/- COMMENTED OUT (Step refactor): single-step preservation has two genuine gaps
  that need a definitional refactor (not just a missing hypothesis):

  * `eval_alloc`/`step_alloc`: the step produces a `pack` of a *fresh* capability
    `l`. Re-deriving `Eval C m2 (.pack ..) Q` must go through `eval_pack`, whose
    budget premise `(reachability l).to_drop ⊆ C` fails since the fresh `l ∉ C`.
    Preservation across `alloc` would require the budget `C` to *grow* with the
    freshly-allocated capability.

  * `eval_letin`/`eval_unpack` via `step_rename`/`step_lift`/`step_unpack`: the new
    rules require `m1.is_compatible C2` for the continuation, which `Step` does not
    supply (and which is not preserved across drops — the downstream linearity
    property). See the block below.

  Preserved verbatim for future reference / re-derivation.

theorem step_preserves_eval
  (he : Eval C m1 e1 Q)
  (hstep : Step C m1 e1 m2 e2) :
  Eval C m2 e2 Q := by
  induction he generalizing m2 e2 with
  | eval_pack _ _ =>
    -- pack is a value, which is an answer, but answers cannot step - contradiction
    rename_i cs x _ _
    have hans : Exp.IsAns (.pack cs x) := Exp.IsAns.is_val Exp.IsVal.pack
    exact absurd hstep (step_ans_absurd hans)
  | eval_val hv hQ =>
    -- e1 is a value, which is an answer, but answers cannot step - contradiction
    have hans : Exp.IsAns _ := Exp.IsAns.is_val hv.to_IsVal
    exact absurd hstep (step_ans_absurd hans)
  | eval_var hQ =>
    -- e1 is a variable, which is an answer, but answers cannot step - contradiction
    rename_i x
    have hans : Exp.IsAns (.var x) := Exp.IsAns.is_var
    exact absurd hstep (step_ans_absurd hans)
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
    | step_invoke hmem hlookup_x hlookup_y =>
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
    | step_invoke hmem' hlookup_x' hlookup_y' =>
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
  | eval_letin hpred hbool heval_e1 h_nonstuck h_val h_var ih_e1 ih_val ih_var =>
    -- e1 = .letin e1' e2'
    -- Possible steps: step_ctx_letin, step_rename, step_lift
    cases hstep with
    | step_ctx_letin hstep_e1 =>
      -- e1' steps to some e1''
      -- Apply IH to get the new evaluation of e1''
      have heval_e1'' := ih_e1 hstep_e1
      -- Rebuild eval_letin with the new evaluation
      -- First, we need to show that memory is monotonic
      have hsub := step_memory_monotonic hstep_e1
      -- The handlers need to be updated for the new memory
      -- h_val and h_var already work with any memory that subsumes m, so they're still valid
      apply Eval.eval_letin hpred hbool heval_e1'' h_nonstuck
      · -- h_val case
        intro m1 v hsub1 hv hwf_v hQ1 l' hfresh
        -- m1 subsumes m2 which subsumes m, so m1 subsumes m
        have hsub_full := Memory.subsumes_trans hsub1 hsub
        exact h_val hsub_full hv hwf_v hQ1 l' hfresh
      · -- h_var case
        intro m1 x hsub1 hwf_x hQ1
        -- m1 subsumes m2 which subsumes m, so m1 subsumes m
        have hsub_full := Memory.subsumes_trans hsub1 hsub
        exact h_var hsub_full hwf_x hQ1
    | step_rename =>
      -- e1' = .var (.free y), stepped to e2'.subst (openVar y)
      -- The postcondition holds for the variable
      have hQ1 := eval_ans_holds_post heval_e1 Exp.IsAns.is_var
      -- Extract well-formedness from h_nonstuck
      have ⟨_, hwf_y⟩ := h_nonstuck hQ1
      cases hwf_y with
      | wf_var hwf_y' =>
        -- Apply h_var - Lean will infer the memory from the implicit argument
        exact h_var (by apply Memory.subsumes_refl) hwf_y' hQ1
    | step_lift hv hwf_v hfresh =>
      -- e1' is a simple value, allocated at l
      -- The postcondition holds for the value
      have hQ1 := eval_ans_holds_post heval_e1 (Exp.IsAns.is_val (by
        cases hv with
        | abs => exact Exp.IsVal.abs
        | tabs => exact Exp.IsVal.tabs
        | cabs => exact Exp.IsVal.cabs
        | reader => exact Exp.IsVal.reader
        | unit => exact Exp.IsVal.unit
        | btrue => exact Exp.IsVal.btrue
        | bfalse => exact Exp.IsVal.bfalse))
      -- Apply h_val - Lean will infer the memory from the implicit argument
      exact h_val (by apply Memory.subsumes_refl) hv hwf_v hQ1 _ hfresh
  | eval_unpack hpred hbool heval_e1 h_nonstuck h_pack ih_e1 ih_pack =>
    -- e1 = .unpack e1' e2'
    -- Possible steps: step_ctx_unpack, step_unpack
    cases hstep with
    | step_ctx_unpack hstep_e1 =>
      -- e1' steps to some e1''
      -- Apply IH to get the new evaluation of e1''
      have heval_e1'' := ih_e1 hstep_e1
      -- Rebuild eval_unpack with the new evaluation
      have hsub := step_memory_monotonic hstep_e1
      apply Eval.eval_unpack hpred hbool heval_e1'' h_nonstuck
      -- The pack handler needs to work with the new memory
      intro m1 x cs hsub1 hwf_x hwf_cs hQ1
      -- m1 subsumes m2 which subsumes m, so m1 subsumes m
      have hsub_full := Memory.subsumes_trans hsub1 hsub
      exact h_pack hsub_full hwf_x hwf_cs hQ1
    | step_unpack =>
      -- e1' = .pack cs (.free x), stepped to e2'.subst (unpack cs x)
      -- The postcondition holds for the pack
      have hQ1 := eval_ans_holds_post heval_e1 (Exp.IsAns.is_val Exp.IsVal.pack)
      -- Extract well-formedness from h_nonstuck
      have ⟨hpack_form, hwf_pack⟩ := h_nonstuck hQ1
      -- Extract the pack structure
      cases hpack_form with
      | pack =>
        -- Extract well-formedness of cs and x
        cases hwf_pack with
        | wf_pack hwf_cs hwf_x =>
          -- Apply h_pack with reflexive subsumption
          exact h_pack (by apply Memory.subsumes_refl) hwf_x hwf_cs hQ1
  | eval_cond hpred hbool heval_e1 h_nonstuck h_true h_false ih =>
    -- e = .cond x e2 e3 where x is a Var
    -- Since the guard is now a variable, it can only step via
    -- step_cond_var_true or step_cond_var_false
    rename_i m_guard x e2 e3
    cases hstep with
    | step_cond_var_true hlookup =>
      -- The guard variable points to true
      have hQ1 := eval_ans_holds_post heval_e1 Exp.IsAns.is_var
      rename_i fx hv R
      have hheap : m_guard.heap fx =
          some (Cell.val { unwrap := .btrue, isVal := hv, reachability := R }) := by
        simpa [Memory.lookup] using hlookup
      have hres : resolve m_guard.heap (.var (.free fx)) = some .btrue := by
        simp only [resolve, hheap]
      exact h_true (Memory.subsumes_refl m_guard) hQ1 hres
    | step_cond_var_false hlookup =>
      -- The guard variable points to false
      have hQ1 := eval_ans_holds_post heval_e1 Exp.IsAns.is_var
      rename_i fx hv R
      have hheap : m_guard.heap fx =
          some (Cell.val { unwrap := .bfalse, isVal := hv, reachability := R }) := by
        simpa [Memory.lookup] using hlookup
      have hres : resolve m_guard.heap (.var (.free fx)) = some .bfalse := by
        simp only [resolve, hheap]
      exact h_false (Memory.subsumes_refl m_guard) hQ1 hres
  | eval_read hcov hlookup_reader hlookup_cell hQ =>
    -- e = .read (.free x), can only step via step_read
    cases hstep with
    | step_read _ hlookup_reader' hlookup_cell' =>
      -- The step produces the same boolean value
      have heq_reader := Memory.lookup_deterministic hlookup_reader hlookup_reader'
      cases heq_reader
      have heq_cell := Memory.lookup_deterministic hlookup_cell hlookup_cell'
      cases heq_cell
      -- The result is a value, so use eval_val with the same boolean
      rename_i b hv R
      cases b with
      | true =>
        exact Eval.eval_val Exp.IsSimpleVal.btrue hQ
      | false =>
        exact Eval.eval_val Exp.IsSimpleVal.bfalse hQ
  | eval_write_true _ hx hy hQ =>
    -- e = .write (.free x) (.free y), can only step via step_write_true or step_write_false
    cases hstep with
    | step_write_true _ hx' hy' =>
      -- Both lookups agree, so the memories are definitionally equal
      -- The result is unit, which is a value
      exact Eval.eval_val Exp.IsSimpleVal.unit hQ
    | step_write_false _ hx' hy' =>
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
    | step_write_true _ hx' hy' =>
      -- y is looked up as bfalse in eval, but btrue in step - contradiction
      have heq_y := Memory.lookup_deterministic hy hy'
      -- The cells must be equal
      injection heq_y with heq_val
      -- The ValPairs must be equal, extract unwrap field
      have h_unwrap : Exp.bfalse = Exp.btrue := congrArg (·.unwrap) heq_val
      cases h_unwrap
    | step_write_false _ hx' hy' =>
      -- Both lookups agree, so the memories are definitionally equal
      -- The result is unit, which is a value
      exact Eval.eval_val Exp.IsSimpleVal.unit hQ
-/

/- COMMENTED OUT (Step refactor): genuine gaps requiring a definitional refactor.

  All of the following depend on relating the budget-carrying `Eval C` to the
  trace-recording `Step`/`Reduce` (which no longer carry a capability set):

  * `reduce_preserves_eval`, `eval_to_reduce`: multi-step preservation. Even with
    an added `is_compatible` hypothesis, `is_compatible C` is NOT preserved across
    a `step_drop` (dropping a live cell that is still in `C` violates the liveness
    condition), so compatibility cannot be threaded across reduction steps. This is
    the downstream linearity/separation property and is not available here.

  * the `*_masked` infrastructure and `step_masked`/`reduce_masked`: these mask a
    memory by `C.to_finset`, where `C` was the `Step` capability-set upper bound.
    `Step` is now trace-indexed, so this masking story needs reframing.

  * `eval_exists_answer`, `eval_reduce_exists_answer`: producing the answer of a
    `letin`/`unpack` requires re-establishing `is_compatible C2` for the
    continuation, which (as above) is the separation property proven downstream.

  Preserved verbatim for future reference / re-derivation.

theorem reduce_preserves_eval
  (he : Eval C m1 e1 Q)
  (hred : Reduce C m1 e1 m2 e2) :
  Eval C m2 e2 Q := by
  induction hred with
  | refl =>
    -- No reduction, so evaluation remains the same
    exact he
  | step hstep rest ih =>
    -- Apply step_preserves_eval to the step
    have heval_step := step_preserves_eval he hstep
    -- Apply IH to the rest of the reduction
    exact ih heval_step

theorem eval_to_reduce
  (heval : Eval C m1 e1 Q)
  (_hwf : e1.WfInHeap m1.heap) :
  ∀ m2 e2,
    e2.IsAns ->
    Reduce C m1 e1 m2 e2 ->
    Q e2 m2 := by
  intro m2 e2 hans hred
  -- Reductions preserve evaluations, then any answer satisfies its postcondition.
  have heval' : Eval C m2 e2 Q := reduce_preserves_eval heval hred
  exact eval_ans_holds_post heval' hans

theorem Heap.restricted_has_capdom {H : Heap}
  (hd : H.HasCapDom D0) :
  (H.mask_caps D).HasCapDom (D0 ∩ D) := by
  unfold HasCapDom mask_caps
  intro l
  -- Use the precondition to relate H l to D0
  have h_cap_iff := hd l
  -- Case analysis on what's at location l in H
  split
  · -- Case: H l = some (.capability info)
    rename_i info heq
    -- By hd, since H l = some (.capability info), we have l ∈ D0
    have h_in_D0 : l ∈ D0 := h_cap_iff.mp ⟨info, heq⟩
    -- Now split on whether l ∈ D
    split_ifs with h_in_D
    · -- Subcase: l ∈ D, so (H.mask_caps D) l = some (.capability info)
      -- Need to show: ∃ info', some (.capability info) = some (.capability info') ↔ l ∈ D0 ∩ D
      simp only [Finset.mem_inter]
      constructor
      · intro _; exact ⟨h_in_D0, h_in_D⟩
      · intro _; exact ⟨info, rfl⟩
    · -- Subcase: l ∉ D, so (H.mask_caps D) l = some .masked
      -- Need to show: ∃ info, some .masked = some (.capability info) ↔ l ∈ D0 ∩ D
      simp only [Finset.mem_inter]
      constructor
      · intro ⟨_, h⟩; cases h
      · intro ⟨_, h_in_D'⟩; exact absurd h_in_D' h_in_D
  · -- Case: H l = some v (where v ≠ .capability for any info)
    rename_i v h_not_cap heq
    -- By hd, since H l ≠ some (.capability _), we have l ∉ D0
    have h_not_in_D0 : l ∉ D0 := by
      intro h_in
      have ⟨info', heq'⟩ := h_cap_iff.mpr h_in
      rw [heq] at heq'
      injection heq' with heq_cell
      exact h_not_cap info' heq_cell
    -- (H.mask_caps D) l = some v
    -- Need to show: ∃ info, some v = some (.capability info) ↔ l ∈ D0 ∩ D
    simp only [Finset.mem_inter]
    constructor
    · intro ⟨info', h_eq⟩
      injection h_eq with h_cell
      exact absurd h_cell (h_not_cap info')
    · intro ⟨h_in_D0', _⟩
      exact absurd h_in_D0' h_not_in_D0
  · -- Case: H l = none
    rename_i heq
    -- By hd, since H l = none, we have l ∉ D0
    have h_not_in_D0 : l ∉ D0 := by
      intro h_in
      have ⟨_, heq'⟩ := h_cap_iff.mpr h_in
      rw [heq] at heq'
      cases heq'
    -- (H.mask_caps D) l = none
    -- Need to show: ∃ info, none = some (.capability info) ↔ l ∈ D0 ∩ D
    simp only [Finset.mem_inter]
    constructor
    · intro ⟨_, h_eq⟩; cases h_eq
    · intro ⟨h_in_D0', _⟩
      exact absurd h_in_D0' h_not_in_D0

/-- Masking caps in a heap does not change the finite domain of the heap. -/
theorem Heap.masked_has_findom {H : Heap}
  (hdom : H.HasFinDom D) :
  (H.mask_caps D1).HasFinDom D := by
  unfold HasFinDom
  intro l
  constructor
  · -- Forward: (H.mask_caps D1) l ≠ none → l ∈ D
    intro h_masked_neq_none
    -- Case analysis on H l
    unfold mask_caps at h_masked_neq_none
    split at h_masked_neq_none
    · -- Case: H l = some .capability
      rename_i heq
      -- Then H l ≠ none, so by hdom, l ∈ D
      have : H l ≠ none := by rw [heq]; simp
      exact (hdom l).mp this
    · -- Case: H l = some v (non-capability)
      rename_i v _ heq
      -- Then H l ≠ none, so by hdom, l ∈ D
      have : H l ≠ none := by rw [heq]; simp
      exact (hdom l).mp this
    · -- Case: H l = none
      -- Then (H.mask_caps D1) l = none, contradicting h_masked_neq_none
      contradiction
  · -- Backward: l ∈ D → (H.mask_caps D1) l ≠ none
    intro h_in_D
    -- By hdom, l ∈ D implies H l ≠ none
    have h_orig_neq_none : H l ≠ none := (hdom l).mpr h_in_D
    -- So H l = some cell for some cell
    cases h_cell : H l
    · -- H l = none, contradicting h_orig_neq_none
      contradiction
    · -- H l = some cell
      rename_i cell
      -- Show (H.mask_caps D1) l ≠ none by case analysis on cell
      unfold mask_caps
      split
      · -- Case: H l = some .capability, split creates if-then-else
        split <;> simp
      · -- Case: H l = some v (non-capability)
        simp
      · -- Case: H l = none
        -- This contradicts h_cell : H l = some cell
        rename_i heq
        rw [h_cell] at heq
        simp at heq

theorem Var.wf_masked
  (hwf : Var.WfInHeap x H) :
  Var.WfInHeap x (H.mask_caps D) := by
  cases hwf with
  | wf_bound =>
    -- Bound variables are always well-formed
    apply Var.WfInHeap.wf_bound
  | wf_free hex =>
    -- Free variable case: H n = some val
    -- Need to show: (H.mask_caps D) n = some val' for some val'
    -- mask_caps preserves "some-ness": if H n = some val, then masked heap also has some value at n
    rename_i val n
    -- Construct a proof that (H.mask_caps D) n is non-none
    have h_masked : ∃ val', (H.mask_caps D) n = some val' := by
      unfold Heap.mask_caps
      rw [hex]
      -- Now we have (match some val with ...) and need to show it's some _
      cases val
      · -- val = .val hv
        rename_i hv
        use Cell.val hv
      · -- val = .capability info
        rename_i info
        by_cases h : n ∈ D
        · use Cell.capability info
          simp only [h, if_true]
        · use Cell.masked
          simp only [h, if_false]
      · -- val = .masked
        use Cell.masked
    obtain ⟨val', h_masked⟩ := h_masked
    exact Var.WfInHeap.wf_free h_masked

theorem CaptureSet.wf_masked
  (hwf : CaptureSet.WfInHeap cs H) :
  CaptureSet.WfInHeap cs (H.mask_caps D) := by
  induction hwf with
  | wf_empty =>
    apply CaptureSet.WfInHeap.wf_empty
  | wf_union _ _ ih1 ih2 =>
    apply CaptureSet.WfInHeap.wf_union <;> assumption
  | @wf_var_free H0 _ m x hex =>
    -- Same approach as Var.wf_masked: prove that a free var in masked heap maps to something
    have hwf_var : Var.WfInHeap (.free (k := .var) (s := {}) x) (H0.mask_caps D) :=
      Var.wf_masked (D := D) (Var.WfInHeap.wf_free (k := .var) (s := {}) hex)
    cases hwf_var with
    | wf_free hex' =>
      exact CaptureSet.WfInHeap.wf_var_free hex'
  | wf_var_bound =>
    apply CaptureSet.WfInHeap.wf_var_bound
  | wf_cvar =>
    apply CaptureSet.WfInHeap.wf_cvar

theorem CaptureBound.wf_masked
  (hwf : CaptureBound.WfInHeap cb H) :
  CaptureBound.WfInHeap cb (H.mask_caps D) := by
  induction hwf with
  | wf_unbound =>
    apply CaptureBound.WfInHeap.wf_unbound
  | wf_bound hwf_cs =>
    apply CaptureBound.WfInHeap.wf_bound
    exact CaptureSet.wf_masked hwf_cs

theorem Ty.wf_masked
  (hwf : Ty.WfInHeap T H) :
  Ty.WfInHeap T (H.mask_caps D) := by
  induction hwf with
  | wf_top =>
    apply Ty.WfInHeap.wf_top
  | wf_tvar =>
    apply Ty.WfInHeap.wf_tvar
  | wf_arrow hwf_T1 hwf_cs _ ih1 ih2 =>
    exact Ty.WfInHeap.wf_arrow ih1 (CaptureSet.wf_masked hwf_cs) ih2
  | wf_poly hwf_T1 hwf_cs _ ih1 ih2 =>
    exact Ty.WfInHeap.wf_poly ih1 (CaptureSet.wf_masked hwf_cs) ih2
  | wf_cpoly hwf_cb hwf_cs _ ih_T =>
    exact Ty.WfInHeap.wf_cpoly (CaptureBound.wf_masked hwf_cb) (CaptureSet.wf_masked hwf_cs) ih_T
  | wf_unit =>
    apply Ty.WfInHeap.wf_unit
  | wf_cap hwf_cs =>
    apply Ty.WfInHeap.wf_cap
    exact CaptureSet.wf_masked hwf_cs
  | wf_bool =>
    apply Ty.WfInHeap.wf_bool
  | wf_cell hwf_cs =>
    apply Ty.WfInHeap.wf_cell
    exact CaptureSet.wf_masked hwf_cs
  | wf_reader hwf_cs =>
    apply Ty.WfInHeap.wf_reader
    exact CaptureSet.wf_masked hwf_cs
  | wf_exi _ ih =>
    apply Ty.WfInHeap.wf_exi
    exact ih
  | wf_typ _ ih =>
    apply Ty.WfInHeap.wf_typ
    exact ih

theorem Exp.wf_masked
  (hwf : Exp.WfInHeap e H) :
  Exp.WfInHeap e (H.mask_caps D) := by
  induction hwf with
  | wf_var hwf_x =>
    apply Exp.WfInHeap.wf_var
    exact Var.wf_masked hwf_x
  | wf_abs hwf_cs hwf_T _ ih =>
    exact Exp.WfInHeap.wf_abs (CaptureSet.wf_masked hwf_cs) (Ty.wf_masked hwf_T) ih
  | wf_tabs hwf_cs hwf_T _ ih =>
    exact Exp.WfInHeap.wf_tabs (CaptureSet.wf_masked hwf_cs) (Ty.wf_masked hwf_T) ih
  | wf_cabs hwf_cs hwf_cb _ ih =>
    exact Exp.WfInHeap.wf_cabs (CaptureSet.wf_masked hwf_cs) (CaptureBound.wf_masked hwf_cb) ih
  | wf_reader hwf_x =>
    apply Exp.WfInHeap.wf_reader
    exact Var.wf_masked hwf_x
  | wf_pack hwf_cs hwf_x =>
    exact Exp.WfInHeap.wf_pack (CaptureSet.wf_masked hwf_cs) (Var.wf_masked hwf_x)
  | wf_app hwf_x hwf_y =>
    exact Exp.WfInHeap.wf_app (Var.wf_masked hwf_x) (Var.wf_masked hwf_y)
  | wf_tapp hwf_x hwf_T =>
    exact Exp.WfInHeap.wf_tapp (Var.wf_masked hwf_x) (Ty.wf_masked hwf_T)
  | wf_capp hwf_x hwf_cs =>
    exact Exp.WfInHeap.wf_capp (Var.wf_masked hwf_x) (CaptureSet.wf_masked hwf_cs)
  | wf_letin _ _ ih1 ih2 =>
    apply Exp.WfInHeap.wf_letin <;> assumption
  | wf_unpack _ _ ih1 ih2 =>
    apply Exp.WfInHeap.wf_unpack <;> assumption
  | wf_unit =>
    apply Exp.WfInHeap.wf_unit
  | wf_btrue =>
    apply Exp.WfInHeap.wf_btrue
  | wf_bfalse =>
    apply Exp.WfInHeap.wf_bfalse
  | wf_cond hwf_x _ _ ih1 ih2 =>
    exact Exp.WfInHeap.wf_cond (Var.wf_masked hwf_x) ih1 ih2
  | wf_read hwf_x =>
    apply Exp.WfInHeap.wf_read
    exact Var.wf_masked hwf_x
  | wf_write hwf_x hwf_y =>
    exact Exp.WfInHeap.wf_write (Var.wf_masked hwf_x) (Var.wf_masked hwf_y)
  | wf_alloc hwf_x =>
    apply Exp.WfInHeap.wf_alloc
    exact Var.wf_masked hwf_x

theorem reachability_of_loc_masked {H : Heap} (l : Nat) :
  reachability_of_loc H l = reachability_of_loc (H.mask_caps D) l := by
  unfold reachability_of_loc
  unfold Heap.mask_caps
  cases h_cell : H l
  · simp
  · rename_i cell
    cases cell
    · rename_i hv
      simp
    · by_cases h : l ∈ D
      · simp [h]
      · simp [h]
    · simp

theorem expand_captures_masked {H : Heap} (cs : CaptureSet {}) :
  expand_captures H cs = expand_captures (H.mask_caps D) cs := by
  induction cs with
  | empty =>
    unfold expand_captures
    rfl
  | var m x =>
    cases x with
    | free loc =>
      unfold expand_captures
      exact congrArg (CapabilitySet.applyMut m) (reachability_of_loc_masked loc)
    | bound x => nomatch x
  | union cs1 cs2 ih1 ih2 =>
    unfold expand_captures
    rw [ih1, ih2]
  | cvar m x => nomatch x

theorem masked_compute_reachability {H : Heap} :
  compute_reachability H v hv = compute_reachability (H.mask_caps D) v hv := by
  cases hv with
  | abs =>
    rename_i cs _ _
    simpa [compute_reachability] using
      (expand_captures_masked (H := H) (D := D) (cs := cs))
  | tabs =>
    rename_i cs _ _
    simpa [compute_reachability] using
      (expand_captures_masked (H := H) (D := D) (cs := cs))
  | cabs =>
    rename_i cs _ _
    simpa [compute_reachability] using
      (expand_captures_masked (H := H) (D := D) (cs := cs))
  | reader =>
    rename_i x
    cases x with
    | free _ =>
      simp only [compute_reachability]
    | bound idx => cases idx
  | unit => rfl
  | btrue => rfl
  | bfalse => rfl

def Memory.masked_caps (m : Memory) (mask : Finset Nat) : Memory where
  heap := m.heap.mask_caps mask
  wf := {
    wf_val := by
      intro l hv hlookup
      unfold Heap.mask_caps at hlookup
      split at hlookup
      · split at hlookup <;> simp at hlookup
      · rename_i v _ heq
        cases hlookup
        exact Exp.wf_masked (m.wf.wf_val l hv heq)
      · cases hlookup
    wf_reach := by
      intro l v hv R hlookup
      unfold Heap.mask_caps at hlookup
      split at hlookup
      · split at hlookup <;> simp at hlookup
      · rename_i cell _ heq
        cases hlookup
        rw [m.wf.wf_reach l v hv R heq]
        exact masked_compute_reachability
      · cases hlookup
  }
  findom := by
    obtain ⟨dom, hdom⟩ := m.findom
    use dom
    exact Heap.masked_has_findom hdom

-- Helper lemma: masking preserves value lookups
theorem masked_lookup_val {m : Memory} {M : Finset Nat} {l : Nat} {hv : HeapVal} :
  m.lookup l = some (.val hv) →
  (m.masked_caps M).lookup l = some (.val hv) := by
  intro hlookup
  change m.heap l = some (.val hv) at hlookup
  change (m.heap.mask_caps M) l = some (.val hv)
  unfold Heap.mask_caps
  rw [hlookup]

-- Helper lemma: masking preserves capability lookups when in the mask set
theorem masked_lookup_cap {m : Memory} {M : Finset Nat} {l : Nat} {info : CapabilityInfo} :
  m.lookup l = some (.capability info) →
  l ∈ M →
  (m.masked_caps M).lookup l = some (.capability info) := by
  intro hlookup hmem
  change m.heap l = some (.capability info) at hlookup
  change (m.heap.mask_caps M) l = some (.capability info)
  unfold Heap.mask_caps
  rw [hlookup]
  simp only [hmem, if_true]

-- Helper lemma: covers in CapabilitySet implies membership in to_finset
theorem covers_to_finset {x : Nat} {C : CapabilitySet} {m : Mutability} :
  C.covers m x → x ∈ C.to_finset := by
  intro hcov
  induction hcov with
  | here =>
    simp only [CapabilitySet.to_finset, Finset.mem_singleton]
  | left _ ih =>
    simp only [CapabilitySet.to_finset, Finset.mem_union]
    exact Or.inl ih
  | right _ ih =>
    simp only [CapabilitySet.to_finset, Finset.mem_union]
    exact Or.inr ih

-- Helper lemma: freshness is preserved by masking
theorem masked_preserves_fresh {m : Memory} {M : Finset Nat} {l : Nat} :
  m.heap l = none → (m.masked_caps M).heap l = none := by
  intro hfresh
  change (m.heap.mask_caps M) l = none
  unfold Heap.mask_caps
  rw [hfresh]

/-- Capability masking and extension commutes for heaps. -/
theorem Heap.masked_extend_comm {H : Heap} {l : Nat} {v : HeapVal} :
  (H.extend l v).mask_caps D =
  (H.mask_caps D).extend l v := by
  funext l'
  unfold Heap.extend Heap.mask_caps
  by_cases h_eq : l' = l
  · -- Case: l' = l
    rw [h_eq]
    simp only [if_true]
  · -- Case: l' ≠ l
    simp only [h_eq, if_false]

-- Helper lemma: Memory.extend with HeapVals differing only in reachability are equal
private theorem Memory.extend_heapval_reachability_irrel
  {m : Memory} {l : Nat} {v : Exp {}} {hv : v.IsSimpleVal}
  {R1 R2 : CapabilitySet}
  (hwf : Exp.WfInHeap v m.heap)
  (hreach1 : R1 = compute_reachability m.heap v hv)
  (hreach2 : R2 = compute_reachability m.heap v hv)
  (hfresh : m.heap l = none) :
  m.extend l ⟨v, hv, R1⟩ hwf hreach1 hfresh =
  m.extend l ⟨v, hv, R2⟩ hwf hreach2 hfresh := by
  cases hreach1
  cases hreach2
  rfl

theorem Memory.masked_extend_comm {m : Memory} {l : Nat} {v : HeapVal}
  (hwf_v : Exp.WfInHeap v.unwrap m.heap)
  (hreach : v.reachability = compute_reachability m.heap v.unwrap v.isVal)
  (hfresh : m.heap l = none) :
  (m.extend l v hwf_v hreach hfresh).masked_caps D =
  (m.masked_caps D).extend l v
    (Exp.wf_masked hwf_v)
    (by
      change v.reachability = compute_reachability (m.heap.mask_caps D) v.unwrap v.isVal
      exact hreach.trans (masked_compute_reachability
        (H := m.heap) (D := D) (v := v.unwrap) (hv := v.isVal)))
    (masked_preserves_fresh hfresh) := by
  -- Prove equality of Memory structures by showing their heaps are equal
  -- The other fields (wf and findom) are Props, so proof irrelevance applies
  unfold Memory.extend Memory.masked_caps
  simp only
  simpa using Heap.masked_extend_comm (H := m.heap) (l := l) (v := v) (D := D)

/-- Helper lemma: Heap masking and update_cell commute when the location is in the mask. -/
theorem Heap.masked_update_mcell_comm {H : Heap} {l : Nat} {b : Bool} {M : Finset Nat}
  (hmem : l ∈ M) :
  (H.update_cell l (.capability (.mcell b))).mask_caps M =
  (H.mask_caps M).update_cell l (.capability (.mcell b)) := by
  funext l'
  unfold Heap.update_cell Heap.mask_caps
  by_cases heq : l' = l
  · -- Case: l' = l
    subst heq
    simp only [hmem, if_true]
  · -- Case: l' ≠ l
    simp only [heq, if_false]

/-- Helper lemma: Memory masking and update_mcell commute when the location is in the mask. -/
theorem Memory.masked_update_mcell_comm {m : Memory} {l : Nat} {b : Bool} {M : Finset Nat}
  (hexists : ∃ b0, m.heap l = some (.capability (.mcell b0)))
  (hmem : l ∈ M) :
  (m.update_mcell l b hexists).masked_caps M =
  (m.masked_caps M).update_mcell l b (by
    obtain ⟨b0, hb0⟩ := hexists
    use b0
    change (m.heap.mask_caps M) l = some (.capability (.mcell b0))
    unfold Heap.mask_caps
    rw [hb0]
    simp only [hmem, if_true]) := by
  -- Prove equality by showing heaps are equal
  unfold Memory.update_mcell Memory.masked_caps
  simp only
  simpa using (Heap.masked_update_mcell_comm (H := m.heap) (l := l) (b := b) (M := M) hmem)

theorem step_masked
  (hstep : Step C m1 e1 m2 e2) :
  let M := C.to_finset
  Step C (m1.masked_caps M) e1 (m2.masked_caps M) e2 := by
  intro M
  induction hstep with
  | step_apply hlookup =>
    apply Step.step_apply
    exact masked_lookup_val hlookup
  | step_invoke hx hlookup_x hlookup_y =>
    exact Step.step_invoke hx (masked_lookup_cap hlookup_x (covers_to_finset hx))
                               (masked_lookup_val hlookup_y)
  | step_tapply hlookup =>
    apply Step.step_tapply
    exact masked_lookup_val hlookup
  | step_capply hlookup =>
    apply Step.step_capply
    exact masked_lookup_val hlookup
  | step_cond_var_true hlookup =>
    apply Step.step_cond_var_true
    exact masked_lookup_val hlookup
  | step_cond_var_false hlookup =>
    apply Step.step_cond_var_false
    exact masked_lookup_val hlookup
  | step_ctx_letin hstep' ih =>
    apply Step.step_ctx_letin
    exact ih
  | step_ctx_unpack hstep' ih =>
    apply Step.step_ctx_unpack
    exact ih
  | step_rename =>
    apply Step.step_rename
  | step_lift hv hwf hfresh =>
    -- Rewrite using masked_extend_comm
    rw [Memory.masked_extend_comm hwf rfl hfresh]
    -- Use helper lemma to show the two extend calls are equal
    rw [Memory.extend_heapval_reachability_irrel (Exp.wf_masked hwf)
         (by
           exact rfl.trans masked_compute_reachability)
         rfl
         (masked_preserves_fresh hfresh)]
    -- Now apply step_lift
    apply Step.step_lift hv (Exp.wf_masked hwf) (masked_preserves_fresh hfresh)
  | step_unpack =>
    apply Step.step_unpack
  | step_read hmem hlookup_reader hlookup_cell =>
    -- With y ∈ C, masking preserves the reader and mcell lookup
    exact Step.step_read hmem (masked_lookup_val hlookup_reader)
                               (masked_lookup_cap hlookup_cell (covers_to_finset hmem))
  | step_write_true hmem hx hy =>
    -- With x ∈ C, masking preserves the mcell lookup and commutes with update_mcell
    rename_i x m y b0 hv R
    rw [Memory.masked_update_mcell_comm (Exists.intro b0 hx) (covers_to_finset hmem)]
    exact Step.step_write_true hmem (masked_lookup_cap hx (covers_to_finset hmem))
                                     (masked_lookup_val hy)
  | step_write_false hmem hx hy =>
    -- Symmetric to step_write_true
    rename_i x m y b0 hv R
    rw [Memory.masked_update_mcell_comm (Exists.intro b0 hx) (covers_to_finset hmem)]
    exact Step.step_write_false hmem (masked_lookup_cap hx (covers_to_finset hmem))
                                      (masked_lookup_val hy)

theorem reduce_masked
  (hred : Reduce C m1 e1 m2 e2) :
  let M := C.to_finset
  Reduce C (m1.masked_caps M) e1 (m2.masked_caps M) e2 := by
  intro M
  induction hred with
  | refl =>
    apply Reduce.refl
  | step h rest ih =>
    exact Reduce.step (step_masked h) ih

/-- If Eval C m e Q holds, then there exist m' and e' such that e' is an answer,
    the memory m' subsumes m, and Q e' m' holds. -/
theorem eval_exists_answer
  (heval : Eval C m e Q) :
  ∃ m' e', e'.IsAns ∧ m'.subsumes m ∧ Q e' m' := by
  induction heval with
  | eval_pack _ hQ =>
    exact ⟨_, _, Exp.IsAns.is_val Exp.IsVal.pack, Memory.subsumes_refl _, hQ⟩
  | eval_val hv hQ =>
    exact ⟨_, _, Exp.IsAns.is_val hv.to_IsVal, Memory.subsumes_refl _, hQ⟩
  | eval_var hQ =>
    exact ⟨_, _, Exp.IsAns.is_var, Memory.subsumes_refl _, hQ⟩
  | eval_apply _ _ ih =>
    exact ih
  | eval_invoke _ _ _ hQ =>
    exact ⟨_, _, Exp.IsAns.is_val Exp.IsVal.unit, Memory.subsumes_refl _, hQ⟩
  | eval_tapply _ _ ih =>
    exact ih
  | eval_capply _ _ ih =>
    exact ih
  | eval_letin hpred hbool eval_e1 h_nonstuck h_val h_var ih_e1 ih_val ih_var =>
    obtain ⟨m1', v1, hans1, hsub1, hQ1⟩ := ih_e1
    have ⟨hsimple, hwf1⟩ := h_nonstuck hQ1
    cases hsimple with
    | is_simple_val hv =>
      obtain ⟨l', hfresh⟩ := Memory.exists_fresh m1'
      have hfresh' : m1'.heap l' = none := by
        simp only [Memory.lookup] at hfresh
        exact hfresh
      have ih_cont := ih_val hsub1 hv hwf1 hQ1 l' hfresh'
      obtain ⟨m2, e2, hans2, hsub2, hQ2⟩ := ih_cont
      exact ⟨m2, e2, hans2,
             Memory.subsumes_trans hsub2
               (Memory.subsumes_trans (Memory.extend_val_subsumes _ _ _ hwf1 rfl hfresh') hsub1),
             hQ2⟩
    | is_var =>
      rename_i x
      cases x with
      | bound idx => cases idx
      | free fx =>
        cases hwf1 with
        | wf_var hwf_x =>
          have ih_cont := ih_var hsub1 hwf_x hQ1
          obtain ⟨m2, e2, hans2, hsub2, hQ2⟩ := ih_cont
          exact ⟨m2, e2, hans2, Memory.subsumes_trans hsub2 hsub1, hQ2⟩
  | eval_unpack hpred hbool eval_e1 h_nonstuck h_val ih_e1 ih_val =>
    obtain ⟨m1', v1, hans1, hsub1, hQ1⟩ := ih_e1
    have ⟨hpack, hwf1⟩ := h_nonstuck hQ1
    cases hpack with
    | pack =>
      rename_i cs x
      cases x with
      | bound idx => cases idx
      | free fx =>
        cases hwf1 with
        | wf_pack hwf_cs hwf_x =>
          have ih_cont := ih_val hsub1 hwf_x hwf_cs hQ1
          obtain ⟨m2, e2, hans2, hsub2, hQ2⟩ := ih_cont
          exact ⟨m2, e2, hans2, Memory.subsumes_trans hsub2 hsub1, hQ2⟩
  | eval_read hcov hreader hcell hQ =>
    rename_i b
    cases b with
    | true =>
      exact ⟨_, _, Exp.IsAns.is_val Exp.IsVal.btrue, Memory.subsumes_refl _, hQ⟩
    | false =>
      exact ⟨_, _, Exp.IsAns.is_val Exp.IsVal.bfalse, Memory.subsumes_refl _, hQ⟩
  | eval_write_true _ hx _ hQ =>
    exact ⟨_, _, Exp.IsAns.is_val Exp.IsVal.unit,
           Memory.update_mcell_subsumes _ _ _ ⟨_, hx⟩, hQ⟩
  | eval_write_false _ hx _ hQ =>
    exact ⟨_, _, Exp.IsAns.is_val Exp.IsVal.unit,
           Memory.update_mcell_subsumes _ _ _ ⟨_, hx⟩, hQ⟩
  | eval_cond hpred hbool eval_guard h_nonstuck h_true h_false ih_guard ih_true ih_false =>
    obtain ⟨m1', v1, hans1, hsub1, hQ1⟩ := ih_guard
    have hres := h_nonstuck hQ1
    cases hres with
    | inl hbtrue =>
      have ih_cont := ih_true hsub1 hQ1 hbtrue
      obtain ⟨m2, e2, hans2, hsub2, hQ2⟩ := ih_cont
      exact ⟨m2, e2, hans2, Memory.subsumes_trans hsub2 hsub1, hQ2⟩
    | inr hbfalse =>
      have ih_cont := ih_false hsub1 hQ1 hbfalse
      obtain ⟨m2, e2, hans2, hsub2, hQ2⟩ := ih_cont
      exact ⟨m2, e2, hans2, Memory.subsumes_trans hsub2 hsub1, hQ2⟩

/-- If Eval C m1 e1 Q holds, then there exist m2 and e2 such that
    e1 reduces to e2 (an answer) under capability set C, and Q e2 m2 holds. -/
theorem eval_reduce_exists_answer
  (heval : Eval C m1 e1 Q) :
  ∃ m2 e2, Reduce C m1 e1 m2 e2 ∧ e2.IsAns ∧ Q e2 m2 := by
  induction heval with
  | eval_pack _ hQ =>
    exact ⟨_, _, Reduce.refl, Exp.IsAns.is_val Exp.IsVal.pack, hQ⟩
  | eval_val hv hQ =>
    exact ⟨_, _, Reduce.refl, Exp.IsAns.is_val hv.to_IsVal, hQ⟩
  | eval_var hQ =>
    exact ⟨_, _, Reduce.refl, Exp.IsAns.is_var, hQ⟩
  | eval_apply hlookup _ ih =>
    obtain ⟨m2, e2, hred, hans, hQ⟩ := ih
    rename_i y _ _ _ _
    cases y with
    | bound idx => cases idx
    | free fy =>
      exact ⟨m2, e2, Reduce.step (Step.step_apply hlookup) hred, hans, hQ⟩
  | eval_invoke hmem hlookup_x hlookup_y hQ =>
    exact ⟨_, _, Reduce.step (Step.step_invoke hmem hlookup_x hlookup_y) Reduce.refl,
           Exp.IsAns.is_val Exp.IsVal.unit, hQ⟩
  | eval_tapply hlookup _ ih =>
    obtain ⟨m2, e2, hred, hans, hQ⟩ := ih
    exact ⟨m2, e2, Reduce.step (Step.step_tapply hlookup) hred, hans, hQ⟩
  | eval_capply hlookup _ ih =>
    obtain ⟨m2, e2, hred, hans, hQ⟩ := ih
    exact ⟨m2, e2, Reduce.step (Step.step_capply hlookup) hred, hans, hQ⟩
  | eval_letin hpred hbool eval_e1 h_nonstuck h_val h_var ih_e1 ih_val ih_var =>
    rename_i C_case _ _ e2_cont _ _
    -- Get reduction of e1 to an answer, WITH postcondition
    obtain ⟨m1', v1, hred1, hans1, hQ1⟩ := ih_e1
    have ⟨hsimple, hwf1⟩ := h_nonstuck hQ1
    -- Lift reduction through letin context
    have hred_ctx := reduce_ctx_letin (e2 := e2_cont) hred1
    cases hsimple with
    | is_simple_val hv =>
      -- v1 is a simple value, allocate it and continue
      obtain ⟨l', hfresh⟩ := Memory.exists_fresh m1'
      have hfresh' : m1'.heap l' = none := by
        simp only [Memory.lookup] at hfresh
        exact hfresh
      -- Step from letin v1 e2 to e2.subst with allocation
      have hstep_lift := Step.step_lift (e := e2_cont) (C := C_case) (l := l') hv hwf1 hfresh'
      -- Get IH for continuation
      have hsub1 := reduce_memory_monotonic hred1
      have ih_cont := ih_val hsub1 hv hwf1 hQ1 l' hfresh'
      obtain ⟨m2, e2, hred2, hans2, hQ2⟩ := ih_cont
      -- Combine: letin e1 e2 -> letin v1 e2 -> e2.subst... -> answer
      exact ⟨m2, e2, reduce_trans hred_ctx (Reduce.step hstep_lift hred2), hans2, hQ2⟩
    | is_var =>
      -- v1 is a variable
      rename_i x
      cases x with
      | bound idx => cases idx
      | free fx =>
        -- Step from letin (var x) e2 to e2.subst x
        have hstep_rename := Step.step_rename (C := C_case) (m := m1') (y := fx) (e := e2_cont)
        -- Get IH for continuation
        have hsub1 := reduce_memory_monotonic hred1
        cases hwf1 with
        | wf_var hwf_x =>
          have ih_cont := ih_var hsub1 hwf_x hQ1
          obtain ⟨m2, e2, hred2, hans2, hQ2⟩ := ih_cont
          -- Combine: letin e1 e2 -> letin (var x) e2 -> e2.subst x -> answer
          exact ⟨m2, e2, reduce_trans hred_ctx (Reduce.step hstep_rename hred2), hans2, hQ2⟩
  | eval_unpack hpred hbool eval_e1 h_nonstuck h_val ih_e1 ih_val =>
    rename_i C_case _ _ e2_cont _ _
    -- Get reduction of e1 to an answer (a pack), WITH postcondition
    obtain ⟨m1', v1, hred1, hans1, hQ1⟩ := ih_e1
    have ⟨hpack, hwf1⟩ := h_nonstuck hQ1
    -- Lift reduction through unpack context
    have hred_ctx := reduce_ctx_unpack (e2 := e2_cont) hred1
    cases hpack with
      | pack =>
        rename_i cs x
        cases x with
        | bound idx => cases idx
        | free fx =>
          -- Step from unpack (pack cs x) e2 to e2.subst
          have hstep_unpack :=
            Step.step_unpack (C := C_case) (m := m1') (cs := cs) (x := fx) (e := e2_cont)
          -- Get IH for continuation
          have hsub1 := reduce_memory_monotonic hred1
          cases hwf1 with
          | wf_pack hwf_cs hwf_x =>
            have ih_cont := ih_val hsub1 hwf_x hwf_cs hQ1
            obtain ⟨m2, e2, hred2, hans2, hQ2⟩ := ih_cont
            -- Combine: unpack e1 e2 -> unpack (pack cs x) e2 -> e2.subst -> answer
            exact ⟨m2, e2, reduce_trans hred_ctx (Reduce.step hstep_unpack hred2), hans2, hQ2⟩
  | eval_read hcov hlookup_reader hlookup_cell hQ =>
    rename_i b
    cases b with
    | true =>
      exact ⟨_, _, Reduce.step (Step.step_read hcov hlookup_reader hlookup_cell) Reduce.refl,
             Exp.IsAns.is_val Exp.IsVal.btrue, hQ⟩
    | false =>
      exact ⟨_, _, Reduce.step (Step.step_read hcov hlookup_reader hlookup_cell) Reduce.refl,
             Exp.IsAns.is_val Exp.IsVal.bfalse, hQ⟩
  | eval_write_true hmem hx hy hQ =>
    exact ⟨_, _, Reduce.step (Step.step_write_true hmem hx hy) Reduce.refl,
           Exp.IsAns.is_val Exp.IsVal.unit, hQ⟩
  | eval_write_false hmem hx hy hQ =>
    exact ⟨_, _, Reduce.step (Step.step_write_false hmem hx hy) Reduce.refl,
           Exp.IsAns.is_val Exp.IsVal.unit, hQ⟩
  | eval_cond hpred hbool eval_guard h_nonstuck h_true h_false ih_guard ih_true ih_false =>
    -- Guard is a variable .var x, get postcondition from IH
    rename_i C_case x_guard e_true Q_res e_false m_start Q1
    obtain ⟨m_guard, v_guard, hred_guard, hans_guard, hQ1⟩ := ih_guard
    -- Use reduce_var_inv to show reduction of variable is reflexive
    have ⟨hm_eq, hv_eq⟩ := reduce_var_inv hred_guard
    subst hm_eq hv_eq
    -- Now v_guard = .var x_guard and m_guard = original memory
    have hres := h_nonstuck hQ1
    have hsub1 := Memory.subsumes_refl m_guard
    -- The guard must be .free since BVar {} is empty
    cases x_guard with
    | bound idx => cases idx
    | free fx =>
      cases hres with
      | inl hbtrue =>
        -- Guard resolves to true
        cases hcell : m_guard.heap fx with
        | none => simp [resolve, hcell] at hbtrue
        | some cell =>
          cases cell with
          | capability => simp [resolve, hcell] at hbtrue
          | masked => simp [resolve, hcell] at hbtrue
          | val hv =>
            have hunwrap : hv.unwrap = .btrue := by
              simpa [resolve, hcell] using hbtrue
            -- Destructure hv and substitute
            obtain ⟨unwrap, isVal, reachability⟩ := hv
            simp only at hunwrap
            subst hunwrap
            have hlookup : m_guard.lookup fx = some (.val ⟨.btrue, isVal, reachability⟩) := by
              simp only [Memory.lookup, hcell]
            have hstep :=
              Step.step_cond_var_true (C := C_case) (e1 := e_true) (e2 := e_false) hlookup
            have ih_cont := ih_true hsub1 hQ1 hbtrue
            obtain ⟨m2, e2, hred2, hans2, hQ2⟩ := ih_cont
            exact ⟨m2, e2, Reduce.step hstep hred2, hans2, hQ2⟩
      | inr hbfalse =>
        -- Guard resolves to false (symmetric)
        cases hcell : m_guard.heap fx with
        | none => simp [resolve, hcell] at hbfalse
        | some cell =>
          cases cell with
          | capability => simp [resolve, hcell] at hbfalse
          | masked => simp [resolve, hcell] at hbfalse
          | val hv =>
            have hunwrap : hv.unwrap = .bfalse := by
              simpa [resolve, hcell] using hbfalse
            -- Destructure hv and substitute
            obtain ⟨unwrap, isVal, reachability⟩ := hv
            simp only at hunwrap
            subst hunwrap
            have hlookup : m_guard.lookup fx = some (.val ⟨.bfalse, isVal, reachability⟩) := by
              simp only [Memory.lookup, hcell]
            have hstep :=
              Step.step_cond_var_false (C := C_case) (e1 := e_true) (e2 := e_false) hlookup
            have ih_cont := ih_false hsub1 hQ1 hbfalse
            obtain ⟨m2, e2, hred2, hans2, hQ2⟩ := ih_cont
            exact ⟨m2, e2, Reduce.step hstep hred2, hans2, hQ2⟩
-/

/- COMMENTED OUT (Step refactor): `step_immutable` concluded `m1.not_mutated m2`
  from `Step C m1 e1 m2 e2` together with `C.HasKind .ro` — i.e. the read-only
  authority `C` forbade write steps. `Step` no longer carries an authority `C`, so
  a write step is no longer gated by it; immutability is now naturally a property
  of the recorded trace (e.g. "the trace contains no `.access .epsilon` item"),
  which would require a trace-wellformedness predicate to state. The `applyRO`/
  `HasKind` helpers below existed only to support `step_immutable`. Preserved for
  future reference.

-- Helper: applyRO cannot cover epsilon
theorem applyRO_not_covers_epsilon {C : CapabilitySet} {l : Nat} :
    C.applyRO.covers .epsilon l -> False := by
  intro hcov
  induction C with
  | empty => cases hcov
  | cap m x =>
    simp only [CapabilitySet.applyRO] at hcov
    cases hcov with
    | here hle =>
      -- hle : .epsilon ≤ .ro, but this is false
      cases hle
  | union C1 C2 ih1 ih2 =>
    simp only [CapabilitySet.applyRO] at hcov
    cases hcov with
    | left h => exact ih1 h
    | right h => exact ih2 h

-- Helper lemma: if C has kind .ro, then C.covers .epsilon l is false
theorem hasKind_ro_not_covers_epsilon {C : CapabilitySet} {l : Nat}
    (hkind : C.HasKind .ro) :
    C.covers .epsilon l -> False := by
  intro hcov
  induction C with
  | empty => cases hcov
  | cap m x =>
    cases hkind with
    | ro_cap =>
      cases hcov with
      | here hle => cases hle
  | union C1 C2 ih1 ih2 =>
    cases hkind with
    | ro_union hk1 hk2 =>
      cases hcov with
      | left h => exact ih1 hk1 h
      | right h => exact ih2 hk2 h

theorem step_immutable {C : CapabilitySet}
  (himm : C.HasKind .ro)
  (hstep : Step C m1 e1 m2 e2) :
  m1.not_mutated m2 := by
  intro l b hinit
  induction hstep with
  | step_apply _ => exact hinit
  | step_invoke _ _ _ => exact hinit
  | step_tapply _ => exact hinit
  | step_capply _ => exact hinit
  | step_cond_var_true _ => exact hinit
  | step_cond_var_false _ => exact hinit
  | step_read _ _ _ => exact hinit
  | step_write_true hcov _ _ =>
    -- hcov : C.covers .epsilon x, but C.HasKind .ro
    exact absurd hcov (hasKind_ro_not_covers_epsilon himm)
  | step_write_false hcov _ _ =>
    exact absurd hcov (hasKind_ro_not_covers_epsilon himm)
  | step_ctx_letin _ ih => exact ih himm hinit
  | step_ctx_unpack _ ih => exact ih himm hinit
  | step_rename => exact hinit
  | step_lift hv hwf hfresh =>
    -- Memory.extend preserves mcells
    rename_i l'
    simp only [Memory.extend, Heap.extend]
    -- l ≠ l' because l has an mcell but l' is fresh (none)
    have hne : l ≠ l' := by
      intro heq
      rw [heq, hfresh] at hinit
      contradiction
    simp only [hne, if_false, hinit]
  | step_unpack => exact hinit

-/

theorem not_mutated_refl {m : Memory} : m.not_mutated m := by
  intro l b ℓ hinit
  exact hinit

theorem not_mutated_trans {m1 m2 m3 : Memory}
    (h12 : m1.not_mutated m2) (h23 : m2.not_mutated m3) :
    m1.not_mutated m3 := by
  intro l b ℓ hinit
  exact h23 l b ℓ (h12 l b ℓ hinit)

/- COMMENTED OUT (Step refactor): multi-step counterpart of `step_immutable`;
  see the note above. `Reduce` no longer carries a read-only authority `C`.

theorem reduce_immutable {C : CapabilitySet}
    (himm : C.HasKind .ro)
    (hred : Reduce C m1 e1 m2 e2) :
    m1.not_mutated m2 := by
  induction hred with
  | refl => exact not_mutated_refl
  | step hstep _ ih =>
    exact not_mutated_trans (step_immutable himm hstep) ih
-/

/-- Auxiliary for `EvalTrace.conforms_to`, threading the set `alloced` of
    locations allocated by *earlier* items in the trace. An allocation records
    its location and always conforms; an access/drop conforms when its location
    was already allocated within the trace, or is accounted for by `C` at the
    matching mode. -/
def EvalTrace.conforms_aux (C : CapabilitySet) : EvalTrace -> Finset Nat -> Prop
  | [], _ => True
  | (.alloc l) :: rest, alloced =>
      EvalTrace.conforms_aux C rest (insert l alloced)
  | (.access mu l) :: rest, alloced =>
      (l ∈ alloced ∨ C.covers (.access mu) l) ∧ EvalTrace.conforms_aux C rest alloced
  | (.drop l) :: rest, alloced =>
      (l ∈ alloced ∨ C.covers .drop l) ∧ EvalTrace.conforms_aux C rest alloced

/-- `tr.conforms_to C`: every access/drop in the trace is justified: each one
    either targets an address freshly allocated earlier in the trace, or is
    accounted for by the capability set `C` at the matching mode. -/
def EvalTrace.conforms_to (tr : EvalTrace) (C : CapabilitySet) : Prop :=
  EvalTrace.conforms_aux C tr ∅

/-- Conformance is monotone in the allocated set: more prior allocations only
    justify more accesses. -/
theorem EvalTrace.conforms_aux_alloced_mono {C : CapabilitySet} {tr : EvalTrace} :
    ∀ {A B : Finset Nat}, A ⊆ B →
      EvalTrace.conforms_aux C tr A → EvalTrace.conforms_aux C tr B := by
  induction tr with
  | nil => intro _ _ _ _; trivial
  | cons item rest ih =>
    intro A B hsub h
    cases item with
    | alloc l => exact ih (Finset.insert_subset_insert l hsub) h
    | access mu l => exact ⟨h.1.imp (fun hl => hsub hl) id, ih hsub h.2⟩
    | drop l => exact ⟨h.1.imp (fun hl => hsub hl) id, ih hsub h.2⟩

/-- Conformance is monotone in the budget: a larger budget accounts for at least
    as much. -/
theorem EvalTrace.conforms_aux_mono_C {C D : CapabilitySet} (hCD : C ⊆ D)
    {tr : EvalTrace} :
    ∀ {A : Finset Nat},
      EvalTrace.conforms_aux C tr A → EvalTrace.conforms_aux D tr A := by
  induction tr with
  | nil => intro _ _; trivial
  | cons item rest ih =>
    intro A h
    cases item with
    | alloc l => exact ih h
    | access mu l =>
      exact ⟨h.1.imp_right (CapabilitySet.subset_preserves_covers hCD), ih h.2⟩
    | drop l =>
      exact ⟨h.1.imp_right (CapabilitySet.subset_preserves_covers hCD), ih h.2⟩

/-- Conformance composes over concatenation: if both halves conform with the same
    starting allocation set, so does their concatenation (the first half only
    grows the allocation set available to the second). -/
theorem EvalTrace.conforms_aux_append {C : CapabilitySet} {tr1 tr2 : EvalTrace} :
    ∀ {A : Finset Nat},
      EvalTrace.conforms_aux C tr1 A → EvalTrace.conforms_aux C tr2 A →
        EvalTrace.conforms_aux C (tr1 ++ tr2) A := by
  induction tr1 with
  | nil => intro _ _ h2; exact h2
  | cons item rest ih =>
    intro A h1 h2
    cases item with
    | alloc l =>
      exact ih h1 (EvalTrace.conforms_aux_alloced_mono (Finset.subset_insert l A) h2)
    | access mu l => exact ⟨h1.1, ih h1.2 h2⟩
    | drop l => exact ⟨h1.1, ih h1.2 h2⟩

theorem eval_adequacy
    (heval : Eval C m e Q) :
    ∃ (tr : EvalTrace) (m' : Memory) (a : Exp {}),
      Reduce m e tr m' a ∧
      a.IsAns ∧
      Q a m' ∧
      tr.conforms_to C := by
  induction heval with
  | eval_pack hsub hQ =>
    exact ⟨[], _, _, Reduce.refl, Exp.IsAns.is_val Exp.IsVal.pack, hQ, trivial⟩
  | eval_alloc hlookup h_post =>
    obtain ⟨l, hfresh⟩ := Memory.exists_fresh _
    exact ⟨_, _, _, Reduce.step (Step.step_alloc hlookup hfresh) Reduce.refl,
      Exp.IsAns.is_val Exp.IsVal.pack, h_post l hfresh, trivial⟩
  | eval_val hv hQ =>
    exact ⟨[], _, _, Reduce.refl, Exp.IsAns.is_val hv.to_IsVal, hQ, trivial⟩
  | eval_var hQ =>
    exact ⟨[], _, _, Reduce.refl, Exp.IsAns.is_var, hQ, trivial⟩
  | eval_apply hlookup _ ih =>
    obtain ⟨tr, m', a, hred, hans, hQ, hconf⟩ := ih
    exact ⟨_, _, _, Reduce.step (Step.step_apply hlookup) hred, hans, hQ, hconf⟩
  | eval_invoke hcov hlookup_x hlookup_y hQ =>
    exact ⟨_, _, _, Reduce.step (Step.step_invoke hlookup_x hlookup_y) Reduce.refl,
      Exp.IsAns.is_val Exp.IsVal.unit, hQ, ⟨Or.inr hcov, trivial⟩⟩
  | eval_tapply hlookup _ ih =>
    obtain ⟨tr, m', a, hred, hans, hQ, hconf⟩ := ih
    exact ⟨_, _, _, Reduce.step (Step.step_tapply hlookup) hred, hans, hQ, hconf⟩
  | eval_capply hlookup _ ih =>
    obtain ⟨tr, m', a, hred, hans, hQ, hconf⟩ := ih
    exact ⟨_, _, _, Reduce.step (Step.step_capply hlookup) hred, hans, hQ, hconf⟩
  | eval_read hcov hreader hcell hQ =>
    refine ⟨_, _, _, Reduce.step (Step.step_read hreader hcell) Reduce.refl,
      ?_, hQ, ⟨Or.inr hcov, trivial⟩⟩
    split <;> exact Exp.IsAns.is_val (by constructor)
  | eval_write_true hcov hx hy hQ =>
    exact ⟨_, _, _, Reduce.step (Step.step_write_true hx hy) Reduce.refl,
      Exp.IsAns.is_val Exp.IsVal.unit, hQ, ⟨Or.inr hcov, trivial⟩⟩
  | eval_write_false hcov hx hy hQ =>
    exact ⟨_, _, _, Reduce.step (Step.step_write_false hx hy) Reduce.refl,
      Exp.IsAns.is_val Exp.IsVal.unit, hQ, ⟨Or.inr hcov, trivial⟩⟩
  | eval_drop hx hQ hcov =>
    exact ⟨_, _, _, Reduce.step (Step.step_drop hx) Reduce.refl,
      Exp.IsAns.is_val Exp.IsVal.unit, hQ, ⟨Or.inr hcov, trivial⟩⟩
  | eval_cond hres _ _ ih_true ih_false =>
    cases hres with
    | inl htrue =>
      obtain ⟨tr, m', a, hred, hans, hQ, hconf⟩ := ih_true htrue
      exact ⟨_, _, _, Reduce.step (Step.step_cond_true htrue) hred, hans, hQ, hconf⟩
    | inr hfalse =>
      obtain ⟨tr, m', a, hred, hans, hQ, hconf⟩ := ih_false hfalse
      exact ⟨_, _, _, Reduce.step (Step.step_cond_false hfalse) hred, hans, hQ, hconf⟩
  | eval_letin hpred hbool heval_e1 h_nonstuck h_val h_var hseq hagg ih_e1 ih_val ih_var =>
    rename_i C1 _ C2 _ Cagg _ _ _
    have hC1 : C1 ⊆ Cagg := CapabilitySet.Subset.trans CapabilitySet.Subset.union_right_left hagg
    have hC2 : C2 ⊆ Cagg := CapabilitySet.Subset.trans CapabilitySet.Subset.union_right_right hagg
    -- Reduce `e1` to an answer under its sub-budget `C1`.
    obtain ⟨tr1, m1, a1, hred1, hans1, hQ1, hconf1⟩ := ih_e1
    have hsub1 := reduce_memory_monotonic hred1
    obtain ⟨hsimple, hwf1⟩ := h_nonstuck hQ1
    -- GAP (separation/linearity): evaluating `e1` under `C1` should not break
    -- compatibility of the disjoint continuation budget `C2`. The newly-threaded
    -- `hseq : SeqComp C1 C2` (drops in `C1` never touch `C2`) is the hypothesis
    -- this needs, via a frame lemma over `Reduce`. NEEDS DISCUSSION.
    have hcompatC2 : m1.is_compatible C2 := sorry
    cases hsimple with
    | is_simple_val hv =>
      -- `a1` is a simple value: lift it into a fresh cell and run the continuation.
      obtain ⟨l0, hfresh0⟩ := Memory.exists_fresh m1
      obtain ⟨tr2, m2, a2, hred2, hans2, hQ2, hconf2⟩ :=
        ih_val hsub1 hcompatC2 hv hwf1 hQ1 l0 hfresh0
      refine ⟨_, _, _,
        reduce_trans (reduce_ctx_letin hred1)
          (Reduce.step (Step.step_lift hv hwf1 hfresh0) hred2),
        hans2, hQ2, ?_⟩
      exact EvalTrace.conforms_aux_append
        (EvalTrace.conforms_aux_mono_C hC1 hconf1)
        (EvalTrace.conforms_aux_mono_C hC2 hconf2)
    | is_var =>
      -- `a1` is a variable; it is free (empty signature). Rename and continue.
      rename_i x_var
      cases x_var with
      | bound idx => cases idx
      | free fy =>
        cases hwf1 with
        | wf_var hwf_x' =>
          obtain ⟨tr2, m2, a2, hred2, hans2, hQ2, hconf2⟩ :=
            ih_var hsub1 hcompatC2 hwf_x' hQ1
          refine ⟨_, _, _,
            reduce_trans (reduce_ctx_letin hred1)
              (Reduce.step Step.step_rename hred2),
            hans2, hQ2, ?_⟩
          exact EvalTrace.conforms_aux_append
            (EvalTrace.conforms_aux_mono_C hC1 hconf1)
            (EvalTrace.conforms_aux_mono_C hC2 hconf2)
  | eval_unpack hpred hbool heval_e1 h_nonstuck h_val hseq hagg ih_e1 ih_val =>
    rename_i C1 _ C2 _ Cagg _ _ _
    have hC1 : C1 ⊆ Cagg := CapabilitySet.Subset.trans CapabilitySet.Subset.union_right_left hagg
    -- Reduce `e1` to a pack under its sub-budget `C1`.
    obtain ⟨tr1, m1, a1, hred1, hans1, hQ1, hconf1⟩ := ih_e1
    have hsub1 := reduce_memory_monotonic hred1
    obtain ⟨hpack, hwf1⟩ := h_nonstuck hQ1
    cases hpack with
    | pack =>
      rename_i cs x_var
      cases x_var with
      | bound idx => cases idx
      | free fx =>
        cases hwf1 with
        | wf_pack hwf_cs hwf_x =>
          -- GAP 1 (separation/linearity, same as `letin`): the continuation budget
          -- `C2 ∪ R ∪ R.to_drop` must be compatible at `m1`. `Step` does not carry
          -- this. NEEDS DISCUSSION.
          have hcompatU :
              m1.is_compatible
                (C2 ∪ cs.reachability m1 ∪ (cs.reachability m1).to_drop) := sorry
          obtain ⟨tr2, m2, a2, hred2, hans2, hQ2, hconf2⟩ :=
            ih_val hsub1 hcompatU hwf_x hwf_cs hQ1
          refine ⟨_, _, _,
            reduce_trans (reduce_ctx_unpack hred1)
              (Reduce.step Step.step_unpack hred2),
            hans2, hQ2, ?_⟩
          -- GAP 2 (trace/reachability): `tr2` conforms to `C2 ∪ R ∪ R.to_drop`, where
          -- `R = cs.reachability m1` is the unpacked capability. Its locations are
          -- either freshly allocated during `e1` (hence in `tr1`'s allocation set) or
          -- pre-existing in `C1 ⊆ Cagg` — so the concatenation conforms to `Cagg`.
          -- Closing this needs the accumulator-precise append lemma plus an invariant
          -- relating `cs.reachability` to the earlier trace. NEEDS DISCUSSION.
          sorry

end Consume
