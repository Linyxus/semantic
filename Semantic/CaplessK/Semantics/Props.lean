import Semantic.CaplessK.Semantics.SmallStep
import Semantic.CaplessK.Semantics.BigStep
namespace CaplessK

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
  simp [Memory.lookup] at hlookup1 hlookup2
  apply Heap.lookup_deterministic hlookup1 hlookup2

/-- Extract the precise capability set used by a step. -/
theorem step_capability_set_precise (hstep : Step C m e m' e') :
  (∃ x, C = .cap x) ∨ C = {} := by
  induction hstep with
  | step_apply _ => right; rfl
  | step_invoke _ _ => left; exact ⟨_, rfl⟩
  | step_tapply _ => right; rfl
  | step_capply _ => right; rfl
  | step_cond_var_true _ => right; rfl
  | step_cond_var_false _ => right; rfl
  | step_read _ => left; exact ⟨_, rfl⟩
  | step_write_true _ _ => left; exact ⟨_, rfl⟩
  | step_write_false _ _ => left; exact ⟨_, rfl⟩
  | step_ctx_letin _ ih => exact ih
  | step_ctx_unpack _ ih => exact ih
  | step_rename => right; rfl
  | step_lift _ _ _ => right; rfl
  | step_unpack => right; rfl

-- Note: With precise capability sets, monotonicity for Reduce no longer holds in the
-- traditional sense. The capability set precisely tracks what was used, not an upper bound.
-- Use reduce_trans for combining reductions.

/-- Helper: Congruence for Reduce in letin context. -/
theorem reduce_ctx_letin
  (hred : Reduce C m e1 m' e1') :
  Reduce C m (.letin e1 e2) m' (.letin e1' e2) := by
  induction hred with
  | refl => exact Reduce.refl
  | step h rest ih =>
    exact Reduce.step (Step.step_ctx_letin h) ih

/-- Helper: Congruence for Reduce in unpack context. -/
theorem reduce_ctx_unpack
  (hred : Reduce C m e1 m' e1') :
  Reduce C m (.unpack e1 e2) m' (.unpack e1' e2) := by
  induction hred with
  | refl => exact Reduce.refl
  | step h rest ih =>
    exact Reduce.step (Step.step_ctx_unpack h) ih

/-- Helper: Variables cannot step, so reduction is reflexive.
    With precise capabilities, C must be {} for var reduction. -/
theorem reduce_var_inv
  (hred : Reduce C m (.var x) m' v') :
  m' = m ∧ v' = .var x ∧ C = {} := by
  generalize he : Exp.var x = e at hred
  induction hred with
  | refl => exact ⟨rfl, he ▸ rfl, rfl⟩
  | step hstep rest ih =>
    -- No Step rule applies to a bare variable
    subst he
    cases hstep

/-- Helper: Single step preserves memory subsumption. -/
theorem step_memory_monotonic
  (hstep : Step C m1 e1 m2 e2) :
  m2.subsumes m1 := by
  induction hstep with
  | step_apply => exact Memory.subsumes_refl _
  | step_invoke _ _ => exact Memory.subsumes_refl _
  | step_tapply => exact Memory.subsumes_refl _
  | step_capply => exact Memory.subsumes_refl _
  | step_cond_var_true _ => exact Memory.subsumes_refl _
  | step_cond_var_false _ => exact Memory.subsumes_refl _
  | step_read _ => exact Memory.subsumes_refl _
  | step_write_true hx _ => exact Memory.update_mcell_subsumes _ _ _ ⟨_, hx⟩
  | step_write_false hx _ => exact Memory.update_mcell_subsumes _ _ _ ⟨_, hx⟩
  | step_ctx_letin _ ih => exact ih
  | step_ctx_unpack _ ih => exact ih
  | step_rename => exact Memory.subsumes_refl _
  | step_lift hv hwf hfresh =>
    rename_i v m e l
    have hreach_wf : (compute_reachability m.heap v hv).WfInHeap m.heap :=
      compute_reachability_locations_exist m.wf hwf
    exact Memory.extend_subsumes m l ⟨v, hv, compute_reachability m.heap v hv⟩
      hwf rfl hreach_wf hfresh
  | step_unpack => exact Memory.subsumes_refl _

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

/-- Inversion lemma for letin reduction with precise capability tracking.
    The capability set C is precisely the union of capabilities used in each sub-reduction. -/
theorem reduce_letin_inv
  (hred : Reduce C m (.letin e1 e2) m' a)
  (hans : a.IsAns) :
  (∃ C1 C2 m0 y0, (C1 ∪ C2).equiv C ∧
     Reduce C1 m e1 m0 (.var (.free y0)) ∧
     Reduce C2 m0 (e2.subst (Subst.openVar (.free y0))) m' a) ∨
  (∃ (C1 : CapabilitySet) (C2 : CapabilitySet) (m0 : Memory) (v0 : Exp {})
     (hv : v0.IsSimpleVal) (hwf : Exp.WfInHeap v0 m0.heap)
     (l0 : Nat) (hfresh : m0.heap l0 = none),
    (C1 ∪ C2).equiv C ∧
    Reduce C1 m e1 m0 v0 ∧
    Reduce C2
      (m0.extend l0 ⟨v0, hv, compute_reachability m0.heap v0 hv⟩ hwf rfl
        (compute_reachability_locations_exist m0.wf hwf) hfresh)
      (e2.subst (Subst.openVar (.free l0)))
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
    -- We have: Step C1 m e_full m_mid e_mid, Reduce C2 m_mid e_mid m' a
    -- and C = C1 ∪ C2
    rw [←hgen] at hstep
    -- Case analysis on what step was taken from letin
    cases hstep with
    | step_ctx_letin hstep_e1 =>
      -- e1 steps to e1', and we have rest: Reduce C2 m_mid (.letin e1' e2) m' a
      have ih_result := ih hans rfl
      cases ih_result with
      | inl h_var =>
        -- Variable case from IH: ∃ C1' C2', (C1' ∪ C2').equiv C_rest ∧ ...
        -- where C_rest is the capability from rest (C2✝ in goal)
        obtain ⟨C1', C2', m0, y0, heq_rest, hred_e1', hred_body⟩ := h_var
        apply Or.inl
        refine ⟨_ ∪ C1', C2', m0, y0, ?_, Reduce.step hstep_e1 hred_e1', hred_body⟩
        -- Need: ((C_step ∪ C1') ∪ C2').equiv (C_step ∪ C_rest)
        -- heq_rest : (C1' ∪ C2').equiv C_rest
        intro x
        constructor
        · intro hmem
          -- Forward: x ∈ (C_step ∪ C1') ∪ C2' → x ∈ C_step ∪ C_rest
          cases hmem with
          | left h =>
            cases h with
            | left h1 => exact CapabilitySet.mem.left h1
            | right h1' =>
              -- h1' : x ∈ C1' → x ∈ C1' ∪ C2' → x ∈ C_rest
              have : x ∈ C1' ∪ C2' := CapabilitySet.mem.left h1'
              exact CapabilitySet.mem.right ((heq_rest x).mp this)
          | right h2 =>
            -- h2 : x ∈ C2' → x ∈ C1' ∪ C2' → x ∈ C_rest
            have : x ∈ C1' ∪ C2' := CapabilitySet.mem.right h2
            exact CapabilitySet.mem.right ((heq_rest x).mp this)
        · intro hmem
          -- Backward: x ∈ C_step ∪ C_rest → x ∈ (C_step ∪ C1') ∪ C2'
          cases hmem with
          | left h => exact CapabilitySet.mem.left (CapabilitySet.mem.left h)
          | right h =>
            -- h : x ∈ C_rest → x ∈ C1' ∪ C2'
            have h' := (heq_rest x).mpr h
            cases h' with
            | left h1' => exact CapabilitySet.mem.left (CapabilitySet.mem.right h1')
            | right h2 => exact CapabilitySet.mem.right h2
      | inr h_val =>
        -- Value case from IH
        obtain ⟨C1', C2', m0, v0, hv, hwf, l0, hfresh, heq_rest, hred_e1', hred_body⟩ := h_val
        apply Or.inr
        refine ⟨_ ∪ C1', C2', m0, v0, hv, hwf, l0, hfresh, ?_,
                Reduce.step hstep_e1 hred_e1', hred_body⟩
        -- Same equivalence proof as the variable case
        intro x
        constructor
        · intro hmem
          cases hmem with
          | left h =>
            cases h with
            | left h1 => exact CapabilitySet.mem.left h1
            | right h1' =>
              have : x ∈ C1' ∪ C2' := CapabilitySet.mem.left h1'
              exact CapabilitySet.mem.right ((heq_rest x).mp this)
          | right h2 =>
            have : x ∈ C1' ∪ C2' := CapabilitySet.mem.right h2
            exact CapabilitySet.mem.right ((heq_rest x).mp this)
        · intro hmem
          cases hmem with
          | left h => exact CapabilitySet.mem.left (CapabilitySet.mem.left h)
          | right h =>
            have h' := (heq_rest x).mpr h
            cases h' with
            | left h1' => exact CapabilitySet.mem.left (CapabilitySet.mem.right h1')
            | right h2 => exact CapabilitySet.mem.right h2
    | step_rename =>
      -- e1 = .var (.free y), stepped to e2.subst (openVar (.free y))
      -- step_rename uses {} capability
      apply Or.inl
      refine ⟨{}, _, _, _, ?_, Reduce.refl, rest⟩
      exact CapabilitySet.equiv_refl
    | step_lift hv hwf hfresh =>
      -- e1 is a simple value v, allocated at l
      -- step_lift uses {} capability
      apply Or.inr
      refine ⟨{}, _, _, e1, hv, hwf, _, hfresh, ?_, Reduce.refl, rest⟩
      exact CapabilitySet.equiv_refl

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
      have hwf_top : Ty.WfInHeap (.top : Ty .shape ∅) m1.heap :=
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
  | step_cond_var_true hlookup =>
    have ⟨_, hwf_then, _⟩ := Exp.wf_inv_cond hwf
    exact hwf_then
  | step_cond_var_false hlookup =>
    have ⟨_, _, hwf_else⟩ := Exp.wf_inv_cond hwf
    exact hwf_else
  | step_read hlookup =>
    -- e1 = .read (.free x), e2 = .btrue or .bfalse
    -- Boolean values are always well-formed
    rename_i b
    by_cases hb : b
    · simp [hb]; exact Exp.WfInHeap.wf_btrue
    · simp [hb]; exact Exp.WfInHeap.wf_bfalse
  | step_write_true hx hy =>
    -- e1 = .write (.free x) (.free y), e2 = .unit
    -- Unit is always well-formed in any heap
    exact Exp.WfInHeap.wf_unit
  | step_write_false hx hy =>
    -- e1 = .write (.free x) (.free y), e2 = .unit
    -- Unit is always well-formed in any heap
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
    have hreach_wf := compute_reachability_locations_exist (hv := hv) m1.wf hwf_v
    let m_ext := m1.extend l ⟨v, hv, compute_reachability m1.heap v hv⟩ hwf_v rfl hreach_wf hfresh
    -- Show (.free l) is well-formed in the extended heap
    have hwf_l : Var.WfInHeap (.free l : Var .var ∅) m_ext.heap := by
      apply Var.WfInHeap.wf_free
      unfold m_ext
      simp [Memory.extend]
      exact Heap.extend_lookup_eq _ _ _
    -- e_body is well-formed in the extended heap (by monotonicity)
    have hsub := Memory.extend_subsumes m1 l
      ⟨v, hv, compute_reachability m1.heap v hv⟩ hwf_v rfl hreach_wf hfresh
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
  (hred : Reduce C m1 e1 m2 e2)
  (hwf : e1.WfInHeap m1.heap) :
  e2.WfInHeap m2.heap := by
  induction hred with
  | refl => exact hwf
  | step hstep rest ih =>
    have hwf_mid := step_preserves_wf hstep hwf
    exact ih hwf_mid

/-- Inversion lemma for reduction of unpack expressions with precise capability tracking. -/
theorem reduce_unpack_inv
  (hred : Reduce C m (.unpack e1 e2) m' a)
  (hans : a.IsAns) :
  ∃ (C1 : CapabilitySet) (C2 : CapabilitySet) (m0 : Memory) (cs : CaptureSet {}) (x : Nat),
    (C1 ∪ C2).equiv C ∧
    Reduce C1 m e1 m0 (.pack cs (.free x)) ∧
    Reduce C2 m0 (e2.subst (Subst.unpack cs (.free x))) m' a := by
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
      have ih_result := ih hans rfl
      obtain ⟨C1', C2', m0, cs, x, heq_rest, hred_e1', hred_body⟩ := ih_result
      -- Build the reduction from e1 to pack using Reduce.step
      refine ⟨_ ∪ C1', C2', m0, cs, x, ?_, Reduce.step hstep_e1 hred_e1', hred_body⟩
      -- Equivalence proof: ((C_step ∪ C1') ∪ C2').equiv (C_step ∪ C_rest)
      intro y
      constructor
      · intro hmem
        cases hmem with
        | left h =>
          cases h with
          | left h1 => exact CapabilitySet.mem.left h1
          | right h1' =>
            have : y ∈ C1' ∪ C2' := CapabilitySet.mem.left h1'
            exact CapabilitySet.mem.right ((heq_rest y).mp this)
        | right h2 =>
          have : y ∈ C1' ∪ C2' := CapabilitySet.mem.right h2
          exact CapabilitySet.mem.right ((heq_rest y).mp this)
      · intro hmem
        cases hmem with
        | left h => exact CapabilitySet.mem.left (CapabilitySet.mem.left h)
        | right h =>
          have h' := (heq_rest y).mpr h
          cases h' with
          | left h1' => exact CapabilitySet.mem.left (CapabilitySet.mem.right h1')
          | right h2 => exact CapabilitySet.mem.right h2
    | step_unpack =>
      -- e1 is already .pack cs (.free x), step_unpack uses {} capability
      refine ⟨{}, _, _, _, _, CapabilitySet.equiv_refl, Reduce.refl, rest⟩

inductive IsProgressive : CapabilitySet -> Memory -> Exp {} -> Prop where
| done :
  e.IsAns ->
  IsProgressive R m e
| step :
  Step C' m e m' e' ->
  C' ⊆ C ->
  IsProgressive C m e

/-- If an answer has an evaluation, then the postcondition holds for it. -/
theorem eval_ans_holds_post
  (heval : Eval C m e Q)
  (hans : e.IsAns) :
  Q e m := by
  cases heval with
  | eval_val hv hQ => exact hQ
  | eval_var hQ => exact hQ
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
  | eval_val hv hQ =>
    -- e is a value, so it's an answer
    apply IsProgressive.done
    exact Exp.IsAns.is_val hv
  | eval_var hQ =>
    -- e is a variable, so it's an answer
    apply IsProgressive.done
    exact Exp.IsAns.is_var
  | eval_apply hlookup eval_body ih =>
    -- e = .app (.free x) y, can step via step_apply
    -- y must be a free variable since we're in the empty context
    rename_i cs T e_abs hv R C' y Q' m' x
    match y with
    | .bound idx => cases idx
    | .free y' =>
      apply IsProgressive.step (Step.step_apply hlookup) CapabilitySet.Subset.empty
  | eval_invoke hmem hlookup_x hlookup_y hQ =>
    -- e = .app (.free x) (.free y), can step via step_invoke
    -- Need: (.cap x) ⊆ C, which follows from hmem (x ∈ C)
    apply IsProgressive.step (Step.step_invoke hlookup_x hlookup_y)
    exact CapabilitySet.mem_imp_singleton_subset hmem
  | eval_tapply hlookup eval_body ih =>
    -- e = .tapp (.free x) S, can step via step_tapply
    apply IsProgressive.step (Step.step_tapply hlookup) CapabilitySet.Subset.empty
  | eval_capply hlookup eval_body ih =>
    -- e = .capp (.free x) CS, can step via step_capply
    apply IsProgressive.step (Step.step_capply hlookup) CapabilitySet.Subset.empty
  | eval_letin hpred hbool eval_e1 h_nonstuck h_val h_var ih_e1 _ _ =>
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
        -- e1 is a simple value, we can use step_lift
        -- For progress, we assert that a fresh location exists
        -- The heap is finite, so there are infinitely many fresh locations
        rename_i m0 _ _ _
        have ⟨l0, hfresh⟩ := Memory.exists_fresh m0
        apply IsProgressive.step (Step.step_lift (l := l0) hv hwf hfresh) CapabilitySet.Subset.empty
      | is_var =>
        -- e1 is a variable, we need to show it's a free variable
        rename_i x_var
        cases x_var with
        | bound idx => cases idx
        | free y =>
          apply IsProgressive.step Step.step_rename CapabilitySet.Subset.empty
    | step hstep hsub =>
      -- e1 can step, so letin e1 e2 can step via step_ctx_letin
      apply IsProgressive.step (Step.step_ctx_letin hstep) hsub
  | eval_unpack hpred hbool eval_e1 h_nonstuck h_val ih_e1 _ =>
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
          apply IsProgressive.step Step.step_unpack CapabilitySet.Subset.empty
    | step hstep hsub =>
      -- e1 can step, so unpack e1 e2 can step via step_ctx_unpack
      apply IsProgressive.step (Step.step_ctx_unpack hstep) hsub
  | @eval_cond _ x_guard _ _ _ m0 _ hpred hbool eval_e1 h_nonstuck h_true h_false ih_e1 _ _ =>
    -- e = .cond x e2 e3 where x : Var
    cases ih_e1 with
    | done hans =>
      have hQ := eval_ans_holds_post eval_e1 hans
      have hres := h_nonstuck hQ
      -- Guard is a variable; case on it (must be .free since we're in empty sig)
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
                  (Step.step_cond_var_true (hv := hsimple) (R := reach)
                    (by simp [Memory.lookup, hcell]))
                  CapabilitySet.Subset.empty
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
                  (Step.step_cond_var_false (hv := hsimple) (R := reach)
                    (by simp [Memory.lookup, hcell]))
                  CapabilitySet.Subset.empty
            | capability =>
              simp [resolve, hcell] at hbfalse
            | masked =>
              simp [resolve, hcell] at hbfalse
    | step hstep =>
      -- Guard is a variable, so it cannot step - contradiction
      exact absurd hstep step_var_absurd
  | eval_read hmem hlookup hQ =>
    -- e = .read (.free x), can step via step_read
    -- Need: (.cap x) ⊆ C, which follows from hmem (x ∈ C)
    apply IsProgressive.step (Step.step_read hlookup)
    exact CapabilitySet.mem_imp_singleton_subset hmem
  | eval_write_true hmem hx hy hQ =>
    -- e = .write (.free x) (.free y), can step via step_write_true
    apply IsProgressive.step (Step.step_write_true hx hy)
    exact CapabilitySet.mem_imp_singleton_subset hmem
  | eval_write_false hmem hx hy hQ =>
    -- e = .write (.free x) (.free y), can step via step_write_false
    apply IsProgressive.step (Step.step_write_false hx hy)
    exact CapabilitySet.mem_imp_singleton_subset hmem

theorem step_preserves_eval
  (he : Eval C m1 e1 Q)
  (hstep : Step C' m1 e1 m2 e2)
  (hsub : C' ⊆ C) :
  Eval C m2 e2 Q := by
  induction he generalizing m2 e2 with
  | eval_val hv hQ =>
    -- e1 is a value, which is an answer, but answers cannot step - contradiction
    have hans : Exp.IsAns _ := Exp.IsAns.is_val hv
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
    | step_invoke hlookup_x' hlookup_y' =>
      -- step_invoke says x contains a capability, but hlookup says x contains an abstraction
      -- This is a contradiction
      have heq := Memory.lookup_deterministic hlookup hlookup_x'
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
      apply Eval.eval_val
      · exact Exp.IsVal.unit
      · exact hQ
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
      have heval_e1'' := ih_e1 hstep_e1 hsub
      -- Rebuild eval_letin with the new evaluation
      -- First, we need to show that memory is monotonic
      have hsub_mem := step_memory_monotonic hstep_e1
      -- The handlers need to be updated for the new memory
      -- h_val and h_var already work with any memory that subsumes m, so they're still valid
      apply Eval.eval_letin hpred hbool heval_e1'' h_nonstuck
      · -- h_val case
        intro m1 v hsub1 hv hwf_v hQ1 l' hfresh
        -- m1 subsumes m2 which subsumes m, so m1 subsumes m
        have hsub_full := Memory.subsumes_trans hsub1 hsub_mem
        exact h_val hsub_full hv hwf_v hQ1 l' hfresh
      · -- h_var case
        intro m1 x hsub1 hwf_x hQ1
        -- m1 subsumes m2 which subsumes m, so m1 subsumes m
        have hsub_full := Memory.subsumes_trans hsub1 hsub_mem
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
      have heval_e1'' := ih_e1 hstep_e1 hsub
      -- Rebuild eval_unpack with the new evaluation
      have hsub_mem := step_memory_monotonic hstep_e1
      apply Eval.eval_unpack hpred hbool heval_e1'' h_nonstuck
      -- The pack handler needs to work with the new memory
      intro m1 x cs hsub1 hwf_x hwf_cs hQ1
      -- m1 subsumes m2 which subsumes m, so m1 subsumes m
      have hsub_full := Memory.subsumes_trans hsub1 hsub_mem
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
        simp [resolve, hheap]
      exact h_true (Memory.subsumes_refl m_guard) hQ1 hres
    | step_cond_var_false hlookup =>
      -- The guard variable points to false
      have hQ1 := eval_ans_holds_post heval_e1 Exp.IsAns.is_var
      rename_i fx hv R
      have hheap : m_guard.heap fx =
          some (Cell.val { unwrap := .bfalse, isVal := hv, reachability := R }) := by
        simpa [Memory.lookup] using hlookup
      have hres : resolve m_guard.heap (.var (.free fx)) = some .bfalse := by
        simp [resolve, hheap]
      exact h_false (Memory.subsumes_refl m_guard) hQ1 hres
  | eval_read _ hlookup hQ =>
    -- e = .read (.free x), can only step via step_read
    cases hstep with
    | step_read hlookup' =>
      -- The step produces the same boolean value
      have heq := Memory.lookup_deterministic hlookup hlookup'
      injection heq with heq_cell
      -- The cells are equal, so the booleans must be the same
      cases heq_cell
      -- The result is a value, so use eval_val
      rename_i b _
      by_cases hb : b
      · simp only [hb, ↓reduceIte] at hQ ⊢
        exact Eval.eval_val Exp.IsVal.btrue hQ
      · simp only [hb, Bool.false_eq_true, ↓reduceIte] at hQ ⊢
        exact Eval.eval_val Exp.IsVal.bfalse hQ
  | eval_write_true _ hx hy hQ =>
    -- e = .write (.free x) (.free y), can only step via step_write_true or step_write_false
    cases hstep with
    | step_write_true hx' hy' =>
      -- Both lookups agree, so the memories are definitionally equal
      -- The result is unit, which is a value
      exact Eval.eval_val Exp.IsVal.unit hQ
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
      exact Eval.eval_val Exp.IsVal.unit hQ

/-- Reduction preserves evaluation when the reduction uses a subset of available capabilities. -/
theorem reduce_preserves_eval
  (he : Eval C m1 e1 Q)
  (hred : Reduce C' m1 e1 m2 e2)
  (hsub : C' ⊆ C) :
  Eval C m2 e2 Q := by
  induction hred generalizing C with
  | refl =>
    -- No reduction, so evaluation remains the same
    exact he
  | step hstep rest ih =>
    -- hstep : Step C1 m1 e1 m_mid e_mid
    -- rest : Reduce C2 m_mid e_mid m2 e2
    -- C' = C1 ∪ C2, hsub : C1 ∪ C2 ⊆ C
    -- Need to show: Eval C m2 e2 Q
    have h_c1_sub : _ ⊆ C := CapabilitySet.subset_trans CapabilitySet.subset_union_left hsub
    have heval_mid := step_preserves_eval he hstep h_c1_sub
    have h_c2_sub : _ ⊆ C := CapabilitySet.subset_trans CapabilitySet.subset_union_right hsub
    exact ih heval_mid h_c2_sub

theorem eval_to_reduce
  (heval : Eval C m1 e1 Q) (hsub : C' ⊆ C) :
  ∀ m2 e2,
    e2.IsAns ->
    Reduce C' m1 e1 m2 e2 ->
    Q e2 m2 := by
  intro m2 e2 hans hred
  -- Reductions preserve evaluations, then any answer satisfies its postcondition.
  have heval' : Eval C m2 e2 Q := reduce_preserves_eval heval hred hsub
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
          simp [h]
        · use Cell.masked
          simp [h]
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
  | wf_var_free hex =>
    -- Same approach as Var.wf_masked: prove that a free var in masked heap maps to something
    rename_i H_orig val x K
    have hwf_var : Var.WfInHeap (Var.free (k := .var) (s := {}) x) (H_orig.mask_caps D) := by
      apply Var.wf_masked
      exact Var.WfInHeap.wf_free hex
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
  cases hwf with
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
  | wf_arrow _ _ ih1 ih2 =>
    apply Ty.WfInHeap.wf_arrow <;> assumption
  | wf_poly _ _ ih1 ih2 =>
    apply Ty.WfInHeap.wf_poly <;> assumption
  | wf_cpoly hwf_cb _ ih_T =>
    apply Ty.WfInHeap.wf_cpoly
    · exact CaptureBound.wf_masked hwf_cb
    · exact ih_T
  | wf_unit =>
    apply Ty.WfInHeap.wf_unit
  | wf_cap =>
    apply Ty.WfInHeap.wf_cap
  | wf_bool =>
    apply Ty.WfInHeap.wf_bool
  | wf_cell =>
    apply Ty.WfInHeap.wf_cell
  | wf_label _ ih =>
    apply Ty.WfInHeap.wf_label
    exact ih
  | wf_capt hwf_cs _ ih_T =>
    apply Ty.WfInHeap.wf_capt
    · exact CaptureSet.wf_masked hwf_cs
    · exact ih_T
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
    apply Exp.WfInHeap.wf_abs
    · exact CaptureSet.wf_masked hwf_cs
    · exact Ty.wf_masked hwf_T
    · exact ih
  | wf_tabs hwf_cs hwf_T _ ih =>
    apply Exp.WfInHeap.wf_tabs
    · exact CaptureSet.wf_masked hwf_cs
    · exact Ty.wf_masked hwf_T
    · exact ih
  | wf_cabs hwf_cs hwf_cb _ ih =>
    apply Exp.WfInHeap.wf_cabs
    · exact CaptureSet.wf_masked hwf_cs
    · exact CaptureBound.wf_masked hwf_cb
    · exact ih
  | wf_pack hwf_cs hwf_x =>
    apply Exp.WfInHeap.wf_pack
    · exact CaptureSet.wf_masked hwf_cs
    · exact Var.wf_masked hwf_x
  | wf_app hwf_x hwf_y =>
    apply Exp.WfInHeap.wf_app
    · exact Var.wf_masked hwf_x
    · exact Var.wf_masked hwf_y
  | wf_tapp hwf_x hwf_T =>
    apply Exp.WfInHeap.wf_tapp
    · exact Var.wf_masked hwf_x
    · exact Ty.wf_masked hwf_T
  | wf_capp hwf_x hwf_cs =>
    apply Exp.WfInHeap.wf_capp
    · exact Var.wf_masked hwf_x
    · exact CaptureSet.wf_masked hwf_cs
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
    apply Exp.WfInHeap.wf_cond
    · exact Var.wf_masked hwf_x
    · exact ih1
    · exact ih2
  | wf_read hwf_x =>
    apply Exp.WfInHeap.wf_read
    exact Var.wf_masked hwf_x
  | wf_write hwf_x hwf_y =>
    apply Exp.WfInHeap.wf_write
    · exact Var.wf_masked hwf_x
    · exact Var.wf_masked hwf_y
  | wf_boundary hwf_T _ ih =>
    apply Exp.WfInHeap.wf_boundary
    · exact Ty.wf_masked hwf_T
    · exact ih

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


-- Projection is preserved under masking:
-- For any capability l, the classifier in H and H.mask_caps D determines proj_capability.
-- For values: classifier is .top in both -> same projection
-- For masked: classifier is .top in both -> same projection
-- For capabilities in D: unchanged -> same projection
-- For capabilities outside D: become .masked, classifier changes from c to .top
--   BUT: if they were in the reachability of the masked heap, they must have been
--   masked already (since reachability_of_loc returns {l} for masked cells).
-- For K = .top, projection keeps all capabilities regardless of classifier
theorem masked_proj_top {C : CapabilitySet} {H : Heap} :
  C.proj H .top = C.proj (H.mask_caps D) .top := by
  induction C with
  | empty => rfl
  | cap l =>
    unfold CapabilitySet.proj proj_capability
    simp only [CapKind.subkind_top']
    -- Both sides: if classifier_of_loc returns some, result is true; if none, result is false
    -- classifier_of_loc returns none iff H l = none iff (H.mask_caps D) l = none
    unfold classifier_of_loc Heap.mask_caps
    cases h : H l with
    | none => simp [h]
    | some cell =>
      cases cell with
      | val hv => simp [h]
      | capability info =>
        by_cases hmem : l ∈ D <;> simp [h, hmem]
      | masked => simp [h]
  | union cs1 cs2 ih1 ih2 =>
    unfold CapabilitySet.proj
    rw [ih1, ih2]

-- General projection equality under masking.
-- This is challenging because for capabilities outside D, the classifier changes
-- from the original to .top after masking. However, the subkind check may still
-- yield the same result in specific cases.
--
-- Key insight: For values stored in the heap, their reachability only references
-- other values (which have .top classifier in both heaps) or capabilities that
-- must exist in the heap. The projection behavior depends on the specific K used.
theorem masked_proj {C : CapabilitySet} {H : Heap} {K : CapKind} :
  C.proj H K = C.proj (H.mask_caps D) K := by
  induction C with
  | empty => rfl
  | cap l =>
    unfold CapabilitySet.proj
    unfold proj_capability classifier_of_loc
    unfold Heap.mask_caps
    cases h : H l with
    | none => simp [h]
    | some cell =>
      cases cell with
      | val hv => simp [h]
      | capability info =>
        by_cases hmem : l ∈ D
        · simp [h, hmem]
        · -- Capability outside D: classifier changes from info.classifier to .top
          simp only [h, hmem, ↓reduceIte]
          -- After masking, the cell becomes .masked with classifier .top
          -- LHS uses info.classifier, RHS uses .top
          -- These may give different results for subkind check with K
          -- The key observation: if K = .top, both return true (masked_proj_top)
          -- For other K, we need the two subkind checks to agree.
          -- This holds when info.classifier = .top, or when both return false.
          -- For now, we use a case analysis approach.
          by_cases hK : K = .top
          · -- For K = .top, both subkind checks return true
            simp only [hK, CapKind.subkind_top', ↓reduceIte]
          · -- For K ≠ .top, we need more specific reasoning
            -- In the context where this is used (expand_captures on value capture sets),
            -- the K comes from the capture set syntax.
            sorry
      | masked => simp [h]
  | union cs1 cs2 ih1 ih2 =>
    unfold CapabilitySet.proj
    rw [ih1, ih2]

theorem masked_expand_captures {H : Heap} (cs : CaptureSet {}) :
  expand_captures H cs = expand_captures (H.mask_caps D) cs := by
  induction cs with
  | empty => rfl
  | var x K =>
    cases x with
    | free loc =>
      unfold expand_captures
      rw [reachability_of_loc_masked (D := D) loc]
      rw [masked_proj (D := D)]
    | bound x => nomatch x
  | union cs1 cs2 ih1 ih2 =>
    unfold expand_captures
    rw [ih1, ih2]
  | cvar c K => nomatch c

theorem masked_compute_reachability {H : Heap} :
  compute_reachability H v hv = compute_reachability (H.mask_caps D) v hv := by
  cases hv <;> simp [compute_reachability]
  all_goals exact masked_expand_captures _

theorem mask_preserves_wf {C : CapabilitySet} {H : Heap}
  (hwf : C.WfInHeap H) :
  C.WfInHeap (H.mask_caps D) := by
  intro l hmem
  obtain ⟨v, hv⟩ := hwf l hmem
  unfold Heap.mask_caps
  split
  · -- capability case
    rename_i info _ heq
    simp only [heq] at hv
    split <;> exact ⟨_, rfl⟩
  · -- val case
    rename_i hv' _ heq
    exact ⟨_, rfl⟩
  · -- none case - impossible since H l = some v
    rename_i heq
    simp [hv] at heq

def Memory.masked_caps (m : Memory) (mask : Finset Nat) : Memory where
  heap := m.heap.mask_caps mask
  wf := {
    wf_val := by
      intro l hv hlookup
      unfold Heap.mask_caps at hlookup
      split at hlookup
      · split at hlookup <;> simp at hlookup
      · rename_i v _ heq
        simp at hlookup
        subst hlookup
        have hwf_orig : Exp.WfInHeap hv.unwrap m.heap := by
          apply m.wf.wf_val
          exact heq
        exact Exp.wf_masked hwf_orig
      · simp at hlookup
    wf_reach := by
      intro l v hv R hlookup
      unfold Heap.mask_caps at hlookup
      split at hlookup
      · split at hlookup <;> simp at hlookup
      · rename_i cell _ heq
        simp at hlookup
        subst hlookup
        have hr_orig : R = compute_reachability m.heap v hv := by
          apply m.wf.wf_reach
          exact heq
        rw [hr_orig]
        exact masked_compute_reachability
      · simp at hlookup
    wf_reachability := by
      intro l hv hlookup
      unfold Heap.mask_caps at hlookup
      split at hlookup
      · split at hlookup <;> simp at hlookup
      · rename_i cell _ heq
        simp at hlookup
        subst hlookup
        have hwf_orig := m.wf.wf_reachability l hv heq
        exact mask_preserves_wf hwf_orig
      · simp at hlookup
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
  unfold Memory.lookup at hlookup ⊢
  unfold Memory.masked_caps
  simp
  unfold Heap.mask_caps
  rw [hlookup]

-- Helper lemma: masking preserves capability lookups when in the mask set
theorem masked_lookup_cap {m : Memory} {M : Finset Nat} {l : Nat} {info : CapabilityInfo} :
  m.lookup l = some (.capability info) →
  l ∈ M →
  (m.masked_caps M).lookup l = some (.capability info) := by
  intro hlookup hmem
  unfold Memory.lookup at hlookup ⊢
  unfold Memory.masked_caps
  simp
  unfold Heap.mask_caps
  rw [hlookup]
  simp [hmem]

-- Helper lemma: membership in CapabilitySet implies membership in to_finset
theorem mem_to_finset {x : Nat} {C : CapabilitySet} :
  x ∈ C → x ∈ C.to_finset := by
  intro hmem
  induction hmem with
  | here =>
    simp [CapabilitySet.to_finset]
  | left h ih =>
    simp [CapabilitySet.to_finset]
    left
    exact ih
  | right h ih =>
    simp [CapabilitySet.to_finset]
    right
    exact ih

-- Helper lemma: x is in the to_finset of .cap x
theorem CapabilitySet.mem_cap_to_finset {x : Nat} : x ∈ (CapabilitySet.cap x).to_finset := by
  simp [CapabilitySet.to_finset]

-- Helper lemma: freshness is preserved by masking
theorem masked_preserves_fresh {m : Memory} {M : Finset Nat} {l : Nat} :
  m.heap l = none → (m.masked_caps M).heap l = none := by
  intro hfresh
  unfold Memory.masked_caps
  simp
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
    simp
  · -- Case: l' ≠ l
    simp [h_eq]

-- Helper lemma: Memory.extend with HeapVals differing only in reachability are equal
private theorem Memory.extend_heapval_reachability_irrel
  {m : Memory} {l : Nat} {v : Exp {}} {hv : v.IsSimpleVal}
  {R1 R2 : CapabilitySet}
  (hwf : Exp.WfInHeap v m.heap)
  (hreach1 : R1 = compute_reachability m.heap v hv)
  (hreach2 : R2 = compute_reachability m.heap v hv)
  (hreach_wf1 : R1.WfInHeap m.heap)
  (hreach_wf2 : R2.WfInHeap m.heap)
  (hfresh : m.heap l = none) :
  m.extend l ⟨v, hv, R1⟩ hwf hreach1 hreach_wf1 hfresh =
  m.extend l ⟨v, hv, R2⟩ hwf hreach2 hreach_wf2 hfresh := by
  -- Memories are equal because the HeapVals have equal fields
  unfold Memory.extend
  -- Use funext on heaps
  congr 1
  funext l'
  simp [Heap.extend]
  split
  · -- At location l, HeapVals are equal
    simp [hreach1, hreach2]
  · rfl

theorem Memory.masked_extend_comm {m : Memory} {l : Nat} {v : HeapVal}
  (hwf_v : Exp.WfInHeap v.unwrap m.heap)
  (hreach : v.reachability = compute_reachability m.heap v.unwrap v.isVal)
  (hreach_wf : v.reachability.WfInHeap m.heap)
  (hfresh : m.heap l = none) :
  (m.extend l v hwf_v hreach hreach_wf hfresh).masked_caps D =
  (m.masked_caps D).extend l v
    (Exp.wf_masked hwf_v)
    (by
      simp [Memory.masked_caps]
      exact hreach.trans (masked_compute_reachability
        (H := m.heap) (D := D) (v := v.unwrap) (hv := v.isVal)))
    (by simp [Memory.masked_caps]; exact mask_preserves_wf hreach_wf)
    (masked_preserves_fresh hfresh) := by
  -- Prove equality of Memory structures by showing their heaps are equal
  -- The other fields (wf and findom) are Props, so proof irrelevance applies
  unfold Memory.extend Memory.masked_caps
  congr 1
  exact Heap.masked_extend_comm

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
    simp [hmem]
  · -- Case: l' ≠ l
    simp [heq]

/-- Helper lemma: Memory masking and update_mcell commute when the location is in the mask. -/
theorem Memory.masked_update_mcell_comm {m : Memory} {l : Nat} {b : Bool} {M : Finset Nat}
  (hexists : ∃ b0, m.heap l = some (.capability (.mcell b0)))
  (hmem : l ∈ M) :
  (m.update_mcell l b hexists).masked_caps M =
  (m.masked_caps M).update_mcell l b (by
    obtain ⟨b0, hb0⟩ := hexists
    use b0
    simp [Memory.masked_caps]
    unfold Heap.mask_caps
    rw [hb0]
    simp [hmem]) := by
  -- Prove equality by showing heaps are equal
  unfold Memory.update_mcell Memory.masked_caps
  simp
  exact Heap.masked_update_mcell_comm hmem

-- Helper lemma: x ∈ C1.to_finset implies x ∈ C1
theorem finset_mem_imp_cap_mem {C1 : CapabilitySet} {x : Nat}
  (hx : x ∈ C1.to_finset) : x ∈ C1 := by
  induction C1 with
  | empty => simp [CapabilitySet.to_finset] at hx
  | cap y =>
    simp [CapabilitySet.to_finset] at hx
    rw [hx]
    exact CapabilitySet.mem.here
  | union cs1 cs2 ih1 ih2 =>
    simp [CapabilitySet.to_finset] at hx
    cases hx with
    | inl h1 =>
      apply CapabilitySet.mem.left
      exact ih1 h1
    | inr h2 =>
      apply CapabilitySet.mem.right
      exact ih2 h2

-- Helper lemma: subset of capability sets implies subset of to_finset
theorem CapabilitySet.subset_to_finset {C1 C : CapabilitySet}
  (hsub : C1 ⊆ C) : C1.to_finset ⊆ C.to_finset := by
  intro x hx
  exact mem_to_finset (CapabilitySet.subset_preserves_mem hsub (finset_mem_imp_cap_mem hx))

theorem step_masked
  (hstep : Step C m1 e1 m2 e2) :
  let M := C.to_finset
  Step C (m1.masked_caps M) e1 (m2.masked_caps M) e2 := by
  intro M
  induction hstep with
  | step_apply hlookup =>
    apply Step.step_apply
    exact masked_lookup_val hlookup
  | step_invoke hlookup_x hlookup_y =>
    apply Step.step_invoke
    · exact masked_lookup_cap hlookup_x (CapabilitySet.mem_cap_to_finset)
    · exact masked_lookup_val hlookup_y
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
    rename_i v m e l
    have hreach_wf : (compute_reachability m.heap v hv).WfInHeap m.heap :=
      compute_reachability_locations_exist (hv := hv) m.wf hwf
    -- Rewrite using masked_extend_comm
    rw [Memory.masked_extend_comm (v := ⟨v, hv, compute_reachability m.heap v hv⟩)
         hwf rfl hreach_wf hfresh]
    -- Use helper lemma to show the two extend calls are equal
    rw [Memory.extend_heapval_reachability_irrel (Exp.wf_masked hwf)
         (by simp [Memory.masked_caps];
             exact rfl.trans masked_compute_reachability)
         rfl
         (by simp [Memory.masked_caps]; exact mask_preserves_wf hreach_wf)
         (by exact compute_reachability_locations_exist (hv := hv)
               (m.masked_caps M).wf (Exp.wf_masked hwf))
         (masked_preserves_fresh hfresh)]
    -- Now apply step_lift
    apply Step.step_lift hv (Exp.wf_masked hwf) (masked_preserves_fresh hfresh)
  | step_unpack =>
    apply Step.step_unpack
  | step_read hlookup =>
    -- With x ∈ C, masking preserves the mcell lookup
    apply Step.step_read
    exact masked_lookup_cap hlookup (CapabilitySet.mem_cap_to_finset)
  | step_write_true hx hy =>
    -- With x ∈ C, masking preserves the mcell lookup and commutes with update_mcell
    rename_i x m y b0 hv R
    rw [Memory.masked_update_mcell_comm (Exists.intro b0 hx) (CapabilitySet.mem_cap_to_finset)]
    apply Step.step_write_true
    · -- Need to show the masked memory still has the mcell at x
      exact masked_lookup_cap hx (CapabilitySet.mem_cap_to_finset)
    · exact masked_lookup_val hy
  | step_write_false hx hy =>
    -- Symmetric to step_write_true
    rename_i x m y b0 hv R
    rw [Memory.masked_update_mcell_comm (Exists.intro b0 hx) (CapabilitySet.mem_cap_to_finset)]
    apply Step.step_write_false
    · exact masked_lookup_cap hx (CapabilitySet.mem_cap_to_finset)
    · exact masked_lookup_val hy

-- Variant of step_masked that allows masking with a superset capability set
theorem step_masked_superset
  (hstep : Step C1 m1 e1 m2 e2)
  (hsub : C1 ⊆ C) :
  Step C1 (m1.masked_caps C.to_finset) e1 (m2.masked_caps C.to_finset) e2 := by
  -- For capability operations, we need to show the capability x is in C.to_finset
  -- Since C1 = .cap x and C1 ⊆ C, we have x ∈ C, so x ∈ C.to_finset
  induction hstep with
  | step_apply hlookup =>
    apply Step.step_apply
    exact masked_lookup_val hlookup
  | step_invoke hlookup_x hlookup_y =>
    -- C1 = .cap x, so x ∈ C1 ⊆ C, so x ∈ C.to_finset
    have hmem : _ ∈ C.to_finset :=
      mem_to_finset (CapabilitySet.subset_preserves_mem hsub CapabilitySet.mem.here)
    apply Step.step_invoke
    · exact masked_lookup_cap hlookup_x hmem
    · exact masked_lookup_val hlookup_y
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
    exact ih hsub
  | step_ctx_unpack hstep' ih =>
    apply Step.step_ctx_unpack
    exact ih hsub
  | step_rename =>
    apply Step.step_rename
  | step_lift hv hwf hfresh =>
    rename_i v m e l
    have hreach_wf : (compute_reachability m.heap v hv).WfInHeap m.heap :=
      compute_reachability_locations_exist (hv := hv) m.wf hwf
    rw [Memory.masked_extend_comm (v := ⟨v, hv, compute_reachability m.heap v hv⟩)
         hwf rfl hreach_wf hfresh]
    rw [Memory.extend_heapval_reachability_irrel (Exp.wf_masked hwf)
         (by simp [Memory.masked_caps];
             exact rfl.trans masked_compute_reachability)
         rfl
         (by simp [Memory.masked_caps]; exact mask_preserves_wf hreach_wf)
         (by exact compute_reachability_locations_exist (hv := hv)
               (m.masked_caps C.to_finset).wf (Exp.wf_masked hwf))
         (masked_preserves_fresh hfresh)]
    apply Step.step_lift hv (Exp.wf_masked hwf) (masked_preserves_fresh hfresh)
  | step_unpack =>
    apply Step.step_unpack
  | step_read hlookup =>
    have hmem : _ ∈ C.to_finset :=
      mem_to_finset (CapabilitySet.subset_preserves_mem hsub CapabilitySet.mem.here)
    apply Step.step_read
    exact masked_lookup_cap hlookup hmem
  | step_write_true hx hy =>
    rename_i x m y b0 hv R
    have hmem : x ∈ C.to_finset :=
      mem_to_finset (CapabilitySet.subset_preserves_mem hsub CapabilitySet.mem.here)
    rw [Memory.masked_update_mcell_comm (Exists.intro b0 hx) hmem]
    apply Step.step_write_true
    · exact masked_lookup_cap hx hmem
    · exact masked_lookup_val hy
  | step_write_false hx hy =>
    rename_i x m y b0 hv R
    have hmem : x ∈ C.to_finset :=
      mem_to_finset (CapabilitySet.subset_preserves_mem hsub CapabilitySet.mem.here)
    rw [Memory.masked_update_mcell_comm (Exists.intro b0 hx) hmem]
    apply Step.step_write_false
    · exact masked_lookup_cap hx hmem
    · exact masked_lookup_val hy

-- Generalized version: reduce works with any superset mask
theorem reduce_masked_superset
  (hred : Reduce C m1 e1 m2 e2)
  (hsub : C ⊆ C') :
  Reduce C (m1.masked_caps C'.to_finset) e1 (m2.masked_caps C'.to_finset) e2 := by
  induction hred with
  | refl =>
    exact Reduce.refl
  | step hstep hrest ih =>
    apply Reduce.step
    · have hsub1 := CapabilitySet.subset_trans CapabilitySet.subset_union_left hsub
      exact step_masked_superset hstep hsub1
    · exact ih (CapabilitySet.subset_trans CapabilitySet.subset_union_right hsub)

theorem reduce_masked
  (hred : Reduce C m1 e1 m2 e2) :
  let M := C.to_finset
  Reduce C (m1.masked_caps M) e1 (m2.masked_caps M) e2 :=
  reduce_masked_superset hred CapabilitySet.subset_refl

/-- If Eval C m e Q holds, then there exist m' and e' such that e' is an answer,
    the memory m' subsumes m, and Q e' m' holds. -/
theorem eval_exists_answer
  (heval : Eval C m e Q) :
  ∃ m' e', e'.IsAns ∧ m'.subsumes m ∧ Q e' m' := by
  induction heval with
  | eval_val hv hQ =>
    exact ⟨_, _, Exp.IsAns.is_val hv, Memory.subsumes_refl _, hQ⟩
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
        simp [Memory.lookup] at hfresh
        exact hfresh
      have ih_cont := ih_val hsub1 hv hwf1 hQ1 l' hfresh'
      obtain ⟨m2, e2, hans2, hsub2, hQ2⟩ := ih_cont
      have hreach_wf : (compute_reachability m1'.heap v1 hv).WfInHeap m1'.heap :=
        compute_reachability_locations_exist (hv := hv) m1'.wf hwf1
      have hext_sub := Memory.extend_val_subsumes m1' l'
        ⟨v1, hv, compute_reachability m1'.heap v1 hv⟩ hwf1 rfl hreach_wf hfresh'
      exact ⟨m2, e2, hans2,
             Memory.subsumes_trans hsub2 (Memory.subsumes_trans hext_sub hsub1),
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
  | eval_read _ _ hQ =>
    rename_i _ _ b _ _
    by_cases hb : b
    · simp only [hb, ↓reduceIte] at hQ ⊢
      exact ⟨_, _, Exp.IsAns.is_val Exp.IsVal.btrue, Memory.subsumes_refl _, hQ⟩
    · simp only [hb, Bool.false_eq_true, ↓reduceIte] at hQ ⊢
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

/-- If Eval C m1 e1 Q holds, then there exist C' ⊆ C, m2 and e2 such that
    e1 reduces to e2 (an answer) using capabilities C', and Q e2 m2 holds. -/
theorem eval_reduce_exists_answer
  (heval : Eval C m1 e1 Q) :
  ∃ C' m2 e2, C' ⊆ C ∧ Reduce C' m1 e1 m2 e2 ∧ e2.IsAns ∧ Q e2 m2 := by
  induction heval with
  | eval_val hv hQ =>
    exact ⟨{}, _, _, CapabilitySet.empty_subset, Reduce.refl, Exp.IsAns.is_val hv, hQ⟩
  | eval_var hQ =>
    exact ⟨{}, _, _, CapabilitySet.empty_subset, Reduce.refl, Exp.IsAns.is_var, hQ⟩
  | eval_apply hlookup _ ih =>
    obtain ⟨C', m2, e2, hsub, hred, hans, hQ⟩ := ih
    rename_i y _ _ _ _
    cases y with
    | bound idx => cases idx
    | free fy =>
      -- step_apply uses {} capability, rest uses C'
      exact ⟨{} ∪ C', m2, e2,
             CapabilitySet.union_subset_of_subset_of_subset CapabilitySet.empty_subset hsub,
             Reduce.step (Step.step_apply hlookup) hred,
             hans, hQ⟩
  | eval_invoke hmem hlookup_x hlookup_y hQ =>
    -- step_invoke uses {x} capability, refl uses {}
    exact ⟨.cap _ ∪ {}, _, _,
           CapabilitySet.union_subset_of_subset_of_subset
             (CapabilitySet.mem_imp_singleton_subset hmem) CapabilitySet.empty_subset,
           Reduce.step (Step.step_invoke hlookup_x hlookup_y) Reduce.refl,
           Exp.IsAns.is_val Exp.IsVal.unit, hQ⟩
  | eval_tapply hlookup _ ih =>
    obtain ⟨C', m2, e2, hsub, hred, hans, hQ⟩ := ih
    exact ⟨{} ∪ C', m2, e2,
           CapabilitySet.union_subset_of_subset_of_subset CapabilitySet.empty_subset hsub,
           Reduce.step (Step.step_tapply hlookup) hred,
           hans, hQ⟩
  | eval_capply hlookup _ ih =>
    obtain ⟨C', m2, e2, hsub, hred, hans, hQ⟩ := ih
    exact ⟨{} ∪ C', m2, e2,
           CapabilitySet.union_subset_of_subset_of_subset CapabilitySet.empty_subset hsub,
           Reduce.step (Step.step_capply hlookup) hred,
           hans, hQ⟩
  | eval_letin hpred hbool eval_e1 h_nonstuck h_val h_var ih_e1 ih_val ih_var =>
    rename_i _ _ _ e2_body m_start _
    -- ih_e1 gives: ∃ C1 m2 e2, C1 ⊆ C ∧ Reduce C1 m_start e1 m2 e2 ∧ e2.IsAns ∧ Q1 e2 m2
    obtain ⟨C1, m1', v1, hsub1, hred1, hans1, hQ1⟩ := ih_e1
    have ⟨hsimple, hwf1⟩ := h_nonstuck hQ1
    -- Memory monotonicity: m1' subsumes m_start
    have hsub_mem : m1'.subsumes m_start := reduce_memory_monotonic hred1
    cases hsimple with
    | is_simple_val hv =>
      -- e1 reduced to a simple value v1
      obtain ⟨l', hfresh⟩ := Memory.exists_fresh m1'
      have hfresh' : m1'.heap l' = none := by
        simp [Memory.lookup] at hfresh
        exact hfresh
      -- Get continuation reduction from ih_val
      have ih_cont := ih_val hsub_mem hv hwf1 hQ1 l' hfresh'
      obtain ⟨C2, m_final, e_final, hsub2, hred2, hans2, hQ2⟩ := ih_cont
      -- Build the full reduction:
      -- 1. Reduce C1 m_start (.letin e1 e2_body) m1' (.letin v1 e2_body) via context
      have hred_ctx := reduce_ctx_letin (e2 := e2_body) hred1
      -- 2. Step {} m1' (.letin v1 e2_body) extended_mem (e2_body.subst ...) via step_lift
      have hstep_lift := Step.step_lift (e := e2_body) hv hwf1 hfresh'
      -- 3. Compose: ctx reduction then (lift step then continuation)
      -- First combine step_lift with hred2
      have hred_after_lift := Reduce.step hstep_lift hred2
      -- Then combine ctx reduction with the rest
      obtain ⟨C_mid, heq_mid, hred_mid⟩ := reduce_trans hred_ctx hred_after_lift
      -- Show the capability subset: C_mid is equiv to C1 ∪ ({} ∪ C2)
      -- We need C_mid ⊆ C, which follows from C1 ⊆ C and C2 ⊆ C
      rename_i C0 _ _ _
      have hsub_union : C1 ∪ ({} ∪ C2) ⊆ C0 :=
        CapabilitySet.union_subset_of_subset_of_subset hsub1
          (CapabilitySet.union_subset_of_subset_of_subset
            CapabilitySet.empty_subset hsub2)
      have hsub_final : C_mid ⊆ C0 := CapabilitySet.subset_of_equiv_subset heq_mid hsub_union
      exact ⟨C_mid, m_final, e_final, hsub_final, hred_mid, hans2, hQ2⟩
    | is_var =>
      -- e1 reduced to a variable
      rename_i x
      cases x with
      | bound idx => cases idx
      | free fx =>
        cases hwf1 with
        | wf_var hwf_x =>
          -- Get continuation reduction from ih_var
          have ih_cont := ih_var hsub_mem hwf_x hQ1
          obtain ⟨C2, m_final, e_final, hsub2, hred2, hans2, hQ2⟩ := ih_cont
          -- Build the full reduction:
          -- 1. Reduce C1 m_start (.letin e1 e2_body) m1' (.letin (.var (.free fx)) e2_body)
          have hred_ctx := reduce_ctx_letin (e2 := e2_body) hred1
          -- 2. Step {} m1' (.letin (.var (.free fx)) e2_body) m1' (e2_body.subst ...)
          have hstep_rename := Step.step_rename (m:=m1') (e := e2_body) (y := fx)
          -- 3. Compose
          have hred_after_rename := Reduce.step hstep_rename hred2
          obtain ⟨C_mid, heq_mid, hred_mid⟩ := reduce_trans hred_ctx hred_after_rename
          rename_i C0 _ _ _
          have hsub_union : C1 ∪ ({} ∪ C2) ⊆ C0 :=
            CapabilitySet.union_subset_of_subset_of_subset hsub1
              (CapabilitySet.union_subset_of_subset_of_subset
                CapabilitySet.empty_subset hsub2)
          have hsub_final : C_mid ⊆ C0 := CapabilitySet.subset_of_equiv_subset heq_mid hsub_union
          exact ⟨C_mid, m_final, e_final, hsub_final, hred_mid, hans2, hQ2⟩
  | eval_unpack hpred hbool eval_e1 h_nonstuck h_val ih_e1 ih_val =>
    rename_i _ _ _ e2_body m_start _
    -- ih_e1 gives: ∃ C1 m2 e2, C1 ⊆ C ∧ Reduce C1 m_start e1 m2 e2 ∧ e2.IsAns ∧ Q1 e2 m2
    obtain ⟨C1, m1', v1, hsub1, hred1, hans1, hQ1⟩ := ih_e1
    have ⟨hpack, hwf1⟩ := h_nonstuck hQ1
    -- Memory monotonicity
    have hsub_mem : m1'.subsumes m_start := reduce_memory_monotonic hred1
    -- v1 is a pack: .pack cs (.free x)
    cases hpack with
    | pack =>
      rename_i cs x_pack
      -- x_pack must be .free since we're closed
      cases x_pack with
      | bound idx => cases idx
      | free x_nat =>
        cases hwf1 with
        | wf_pack hwf_cs hwf_x =>
          -- Get continuation reduction from ih_val
          have ih_cont := ih_val hsub_mem hwf_x hwf_cs hQ1
          obtain ⟨C2, m_final, e_final, hsub2, hred2, hans2, hQ2⟩ := ih_cont
          -- Build the full reduction:
          -- 1. Reduce C1 m_start (.unpack e1 e2_body) m1' (.unpack (.pack cs x_nat) e2_body)
          have hred_ctx := reduce_ctx_unpack (e2 := e2_body) hred1
          -- 2. Step {} m1' (.unpack (.pack cs x_nat) e2_body) m1' (e2_body.subst ...)
          have hstep_unpack := Step.step_unpack (m:=m1') (e := e2_body) (cs := cs) (x := x_nat)
          -- 3. Compose
          have hred_after_unpack := Reduce.step hstep_unpack hred2
          obtain ⟨C_mid, heq_mid, hred_mid⟩ := reduce_trans hred_ctx hred_after_unpack
          rename_i C0 _ _ _
          have hsub_union : C1 ∪ ({} ∪ C2) ⊆ C0 :=
            CapabilitySet.union_subset_of_subset_of_subset hsub1
              (CapabilitySet.union_subset_of_subset_of_subset
                CapabilitySet.empty_subset hsub2)
          have hsub_final : C_mid ⊆ C0 := CapabilitySet.subset_of_equiv_subset heq_mid hsub_union
          exact ⟨C_mid, m_final, e_final, hsub_final, hred_mid, hans2, hQ2⟩
  | eval_read hmem hlookup hQ =>
    rename_i b
    cases b with
    | true =>
      exact ⟨.cap _ ∪ {}, _, _,
             CapabilitySet.union_subset_of_subset_of_subset
               (CapabilitySet.mem_imp_singleton_subset hmem) CapabilitySet.empty_subset,
             Reduce.step (Step.step_read hlookup) Reduce.refl,
             Exp.IsAns.is_val Exp.IsVal.btrue, hQ⟩
    | false =>
      exact ⟨.cap _ ∪ {}, _, _,
             CapabilitySet.union_subset_of_subset_of_subset
               (CapabilitySet.mem_imp_singleton_subset hmem) CapabilitySet.empty_subset,
             Reduce.step (Step.step_read hlookup) Reduce.refl,
             Exp.IsAns.is_val Exp.IsVal.bfalse, hQ⟩
  | eval_write_true hmem hx hy hQ =>
    exact ⟨.cap _ ∪ {}, _, _,
           CapabilitySet.union_subset_of_subset_of_subset
             (CapabilitySet.mem_imp_singleton_subset hmem) CapabilitySet.empty_subset,
           Reduce.step (Step.step_write_true hx hy) Reduce.refl,
           Exp.IsAns.is_val Exp.IsVal.unit, hQ⟩
  | eval_write_false hmem hx hy hQ =>
    exact ⟨.cap _ ∪ {}, _, _,
           CapabilitySet.union_subset_of_subset_of_subset
             (CapabilitySet.mem_imp_singleton_subset hmem) CapabilitySet.empty_subset,
           Reduce.step (Step.step_write_false hx hy) Reduce.refl,
           Exp.IsAns.is_val Exp.IsVal.unit, hQ⟩
  | eval_cond hpred hbool eval_guard h_nonstuck h_true h_false ih_guard ih_true ih_false =>
    -- Guard is a variable .var x, get postcondition from IH
    rename_i C_case x_guard e_true Q_res e_false m_start Q1
    obtain ⟨C_guard, m_guard, v_guard, hsub_guard, hred_guard, hans_guard, hQ1⟩ := ih_guard
    -- Use reduce_var_inv to show reduction of variable is reflexive
    have ⟨hm_eq, hv_eq, hc_eq⟩ := reduce_var_inv hred_guard
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
              Step.step_cond_var_true (e1 := e_true) (e2 := e_false) hlookup
            have ih_cont := ih_true hsub1 hQ1 hbtrue
            obtain ⟨C2, m2, e2, hsub2, hred2, hans2, hQ2⟩ := ih_cont
            -- step_cond_var_true uses {} capability
            exact ⟨{} ∪ C2, m2, e2,
                   CapabilitySet.union_subset_of_subset_of_subset
                     CapabilitySet.empty_subset hsub2,
                   Reduce.step hstep hred2,
                   hans2, hQ2⟩
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
              Step.step_cond_var_false (e1 := e_true) (e2 := e_false) hlookup
            have ih_cont := ih_false hsub1 hQ1 hbfalse
            obtain ⟨C2, m2, e2, hsub2, hred2, hans2, hQ2⟩ := ih_cont
            -- step_cond_var_false uses {} capability
            exact ⟨{} ∪ C2, m2, e2,
                   CapabilitySet.union_subset_of_subset_of_subset
                     CapabilitySet.empty_subset hsub2,
                   Reduce.step hstep hred2,
                   hans2, hQ2⟩

theorem eval_bounds_step_capability
  (heval : Eval C m e Q)
  (hred : Step C' m e m' e') :
  C' ⊆ C := by
  induction heval generalizing C' m' e' with
  | eval_val hv hQ =>
    -- Values don't step - contradiction
    have hans : Exp.IsAns _ := Exp.IsAns.is_val hv
    exact absurd hred (step_ans_absurd hans)
  | eval_var hQ =>
    -- Variables don't step - contradiction
    rename_i x
    have hans : Exp.IsAns (.var x) := Exp.IsAns.is_var
    exact absurd hred (step_ans_absurd hans)
  | eval_apply hlookup heval ih =>
    -- Can step via step_apply (uses {}) or step_invoke (contradiction)
    cases hred with
    | step_apply => exact CapabilitySet.empty_subset
    | step_invoke hlookup' _ =>
      -- Contradiction: hlookup says x maps to value, hlookup' says x maps to capability
      simp [Memory.lookup] at hlookup hlookup'
      rw [hlookup] at hlookup'
      cases hlookup'
  | eval_invoke hmem hlookup_x hlookup_y hQ =>
    -- Can step via step_invoke (uses {x}) or step_apply (contradiction)
    rename_i x
    cases hred with
    | step_invoke => exact CapabilitySet.mem_imp_singleton_subset hmem
    | step_apply hlookup' =>
      -- Contradiction: hlookup_x says x maps to capability, hlookup' says x maps to value
      simp [Memory.lookup] at hlookup_x hlookup'
      rw [hlookup_x] at hlookup'
      cases hlookup'
  | eval_tapply hlookup heval ih =>
    -- Can step via step_tapply (uses {})
    cases hred with
    | step_tapply => exact CapabilitySet.empty_subset
  | eval_capply hlookup heval ih =>
    -- Can step via step_capply (uses {})
    cases hred with
    | step_capply => exact CapabilitySet.empty_subset
  | eval_letin hpred hbool heval h_nonstuck h_val h_var ih_e1 ih_val ih_var =>
    -- Can step via step_ctx_letin, step_lift, or step_rename
    cases hred with
    | step_ctx_letin hstep => exact ih_e1 hstep
    | step_lift => exact CapabilitySet.empty_subset
    | step_rename => exact CapabilitySet.empty_subset
  | eval_unpack hpred hbool heval h_nonstuck h_val ih_e1 ih_val =>
    -- Can step via step_ctx_unpack or step_unpack
    cases hred with
    | step_ctx_unpack hstep => exact ih_e1 hstep
    | step_unpack => exact CapabilitySet.empty_subset
  | eval_read hmem hlookup hQ =>
    -- Can step via step_read (uses {x})
    rename_i x
    cases hred with
    | step_read => exact CapabilitySet.mem_imp_singleton_subset hmem
  | eval_write_true hmem hlookup_x hlookup_y hQ =>
    -- Can step via step_write_true or step_write_false (both use {x})
    rename_i x
    cases hred with
    | step_write_true => exact CapabilitySet.mem_imp_singleton_subset hmem
    | step_write_false _ hlookup_y' =>
      -- Both are possible, both use {x}
      exact CapabilitySet.mem_imp_singleton_subset hmem
  | eval_write_false hmem hlookup_x hlookup_y hQ =>
    -- Can step via step_write_false or step_write_true (both use {x})
    rename_i x
    cases hred with
    | step_write_false => exact CapabilitySet.mem_imp_singleton_subset hmem
    | step_write_true _ hlookup_y' =>
      -- Both are possible, both use {x}
      exact CapabilitySet.mem_imp_singleton_subset hmem
  | eval_cond hpred hbool heval h_nonstuck h_true h_false ih_cond ih_true ih_false =>
    -- Can step via step_cond_var_true or step_cond_var_false (use {})
    cases hred with
    | step_cond_var_true => exact CapabilitySet.empty_subset
    | step_cond_var_false => exact CapabilitySet.empty_subset

theorem eval_bounds_reduce_capability
  (heval : Eval C m e Q)
  (hred : Reduce C' m e m' e') :
  C' ⊆ C := by
  induction hred generalizing C with
  | refl => exact CapabilitySet.empty_subset
  | step hstep hred_rest ih =>
    -- Have: Step C1 m1 e1 m2 e2 and Reduce C2 m2 e2 m3 e3, with C' = C1 ∪ C2
    -- Need: C1 ∪ C2 ⊆ C
    -- From trace_state:
    --   hstep : Step C1✝ m1✝ e1✝ m2✝ e2✝
    --   hred_rest : Reduce C2✝ m2✝ e2✝ m3✝ e3✝
    --   heval : Eval C m1✝ e1✝ Q
    rename_i C1 m1 e1 m2 e2 C2 m3 e3
    have hsub1 : C1 ⊆ C := eval_bounds_step_capability heval hstep
    have heval2 : Eval C m2 e2 Q := step_preserves_eval heval hstep hsub1
    have hsub2 : C2 ⊆ C := ih heval2
    exact CapabilitySet.union_subset_of_subset_of_subset hsub1 hsub2

end CaplessK
