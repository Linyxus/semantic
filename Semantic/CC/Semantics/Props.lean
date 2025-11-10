import Semantic.CC.Semantics.SmallStep
import Semantic.CC.Semantics.BigStep
namespace CC

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

/-- Step is monotonic with respect to capability sets:
    if a step can happen under authority R1, it can happen under any larger authority R2. -/
theorem step_capability_set_monotonic {R1 R2 : CapabilitySet}
  (hstep : Step R1 m e m' e') (hsub : R1 ⊆ R2) :
  Step R2 m e m' e' := by
  induction hstep with
  | step_apply hlookup =>
    apply Step.step_apply hlookup
  | step_invoke hmem hlookup_x hlookup_y =>
    apply Step.step_invoke
    · exact CapabilitySet.subset_preserves_mem hsub hmem
    · exact hlookup_x
    · exact hlookup_y
  | step_tapply hlookup =>
    apply Step.step_tapply hlookup
  | step_capply hlookup =>
    apply Step.step_capply hlookup
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
    apply Reduce.step
    · exact step_capability_set_monotonic h hsub
    · exact ih hsub

/-- Helper: Congruence for Reduce in letin context. -/
theorem reduce_ctx_letin
  (hred : Reduce C m e1 m' e1') :
  Reduce C m (.letin e1 e2) m' (.letin e1' e2) := by
  induction hred with
  | refl => apply Reduce.refl
  | step h rest ih =>
    apply Reduce.step
    · apply Step.step_ctx_letin h
    · exact ih

/-- Helper: Congruence for Reduce in unpack context. -/
theorem reduce_ctx_unpack
  (hred : Reduce C m e1 m' e1') :
  Reduce C m (.unpack e1 e2) m' (.unpack e1' e2) := by
  induction hred with
  | refl => apply Reduce.refl
  | step h rest ih =>
    apply Reduce.step
    · apply Step.step_ctx_unpack h
    · exact ih

/-- Helper: Single step preserves memory subsumption. -/
theorem step_memory_monotonic
  (hstep : Step C m1 e1 m2 e2) :
  m2.subsumes m1 := by
  induction hstep with
  | step_apply => exact Memory.subsumes_refl _
  | step_invoke => exact Memory.subsumes_refl _
  | step_tapply => exact Memory.subsumes_refl _
  | step_capply => exact Memory.subsumes_refl _
  | step_ctx_letin _ ih => exact ih
  | step_ctx_unpack _ ih => exact ih
  | step_rename => exact Memory.subsumes_refl _
  | step_lift hv hwf hfresh =>
    exact Memory.extend_subsumes _ _ _ hwf rfl hfresh
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

theorem reduce_letin_inv
  (hred : Reduce C m (.letin e1 e2) m' a)
  (hans : a.IsAns) :
  (∃ m0 y0, Reduce C m e1 m0 (.var (.free y0)) ∧
     Reduce C m0 (e2.subst (Subst.openVar (.free y0))) m' a) ∨
  (∃ (m0 : Memory) (v0 : Exp {}) (hv : v0.IsSimpleVal) (hwf : Exp.WfInHeap v0 m0.heap)
     (l0 : Nat) (hfresh : m0.heap l0 = none),
    Reduce C m e1 m0 v0 ∧
    Reduce
      C
      (m0.extend l0 ⟨v0, hv, compute_reachability m0.heap v0 hv⟩ hwf rfl hfresh)
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
    -- We have a step from e_full, and e_full = .letin e1 e2
    rw [←hgen] at hstep
    -- Case analysis on what step was taken from letin
    cases hstep with
    | step_ctx_letin hstep_e1 =>
      -- e1 steps to e1', and we have rest: Reduce C m2 (.letin e1' e2) m' a
      -- Apply IH to the rest of the reduction
      rename_i m_step e1'
      have ih_result := ih hans rfl
      -- Extract the result from IH
      cases ih_result with
      | inl h_var =>
        -- Variable case from IH
        obtain ⟨m0, y0, hred_e1', hred_body⟩ := h_var
        apply Or.inl
        exists m0, y0
        constructor
        · -- Need to show: Reduce C m_step e1 m0 (.var (.free y0))
          -- We have: hstep_e1 : Step C m_step e1 _ e1'
          -- and: hred_e1' : Reduce C _ e1' m0 (.var (.free y0))
          apply Reduce.step hstep_e1 hred_e1'
        · exact hred_body
      | inr h_val =>
        -- Value case from IH
        obtain ⟨m0, v0, hv, hwf, l0, hfresh, hred_e1', hred_body⟩ := h_val
        apply Or.inr
        exists m0, v0, hv, hwf, l0, hfresh
        constructor
        · -- Reduction from e1 to v0
          apply Reduce.step hstep_e1 hred_e1'
        · exact hred_body
    | step_rename =>
      -- e1 = .var (.free y), stepped to e2.subst (openVar (.free y))
      -- This is the variable case
      -- Unnamed variables in order: m1✝, e1✝, m3✝, e3✝, y✝
      rename_i m_src _ _ _ y
      apply Or.inl
      exists m_src, y
      constructor
      · apply Reduce.refl
      · exact rest
    | step_lift hv hwf hfresh =>
      -- e1 is a simple value v, allocated at l
      -- This is the value case
      -- Unnamed vars: m3✝(dst), e3✝(ans), l✝(loc), m1✝(src), e1✝
      rename_i mem_src _ mem_dst _ location
      apply Or.inr
      exists mem_src, e1, hv, hwf, location, hfresh
      constructor
      · -- e1 is already the value, so reduction is reflexive
        apply Reduce.refl
      · exact rest

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
  | step_invoke hmem hlookup_x hlookup_y =>
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
      apply Var.WfInHeap.wf_free
      unfold m_ext
      simp [Memory.extend]
      exact Heap.extend_lookup_eq _ _ _
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
  (hred : Reduce C m (.unpack e1 e2) m' a)
  (hans : a.IsAns) :
  ∃ (m0 : Memory) (cs : CaptureSet {}) (x : Nat),
    Reduce C m e1 m0 (.pack cs (.free x)) ∧
    Reduce C m0 (e2.subst (Subst.unpack cs (.free x))) m' a := by
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
      obtain ⟨m0, cs, x, hred_e1', hred_body⟩ := ih_result
      -- Build the reduction from e1 to pack
      -- hstep_e1 : Step C m1✝ e1 m2✝ e1'
      -- hred_e1' : Reduce C m2✝ e1' m0 (pack cs x)
      -- Combine them to get: Reduce C m1✝ e1 m0 (pack cs x)
      have hred_e1 : Reduce C _ e1 m0 (.pack cs (.free x)) :=
        Reduce.step hstep_e1 hred_e1'
      exact ⟨m0, cs, x, hred_e1, hred_body⟩
    | step_unpack =>
      -- e1 is already .pack cs (.free x)
      rename_i cs x
      -- rest is the reduction from the substituted body
      -- rest : Reduce C m1✝ (e2.subst (Subst.unpack cs x)) m3✝ e3✝
      -- We need: Reduce C m1✝ e1 m1✝ (pack cs x)
      -- Since e1 = pack cs x, this is Reduce.refl
      exact ⟨_, cs, x, Reduce.refl, rest⟩

theorem eval_to_reduce
  (heval : Eval C m1 e1 Q)
  (hwf : e1.WfInHeap m1.heap) :
  ∀ m2 e2,
    e2.IsAns ->
    Reduce C m1 e1 m2 e2 ->
    Q e2 m2 := by
  induction heval with
  | eval_val hv hQ =>
    intro m2 e2 hans hred
    rename_i v Q C m
    -- v is a value, so it's an answer
    have hans_v : Exp.IsAns v := Exp.IsAns.is_val hv
    -- Since v reduces to e2 and both are answers, they must be equal
    have ⟨heq_m, heq_e⟩ := reduce_ans_eq hans_v hred
    rw [←heq_m, ←heq_e]
    exact hQ
  | eval_var hQ =>
    intro m2 e2 hans hred
    rename_i Q C m x
    -- .var x is an answer
    have hans_var : Exp.IsAns (.var x) := Exp.IsAns.is_var
    -- Since .var x reduces to e2 and both are answers, they must be equal
    have ⟨heq_m, heq_e⟩ := reduce_ans_eq hans_var hred
    rw [←heq_m, ←heq_e]
    exact hQ
  | eval_apply hlookup eval_body ih =>
    -- e1 = .app (.free x) y
    -- Evaluation: lookup x, get abstraction, evaluate body
    -- Any reduction must step via step_apply first
    intro m2 e2 hans hred
    -- The application is not an answer, so reduction cannot be refl
    cases hred with
    | refl =>
      -- .app is not an answer, contradiction
      cases hans; rename_i hv
      cases hv
    | step hstep rest =>
      -- At least one step from application
      cases hstep with
      | step_apply hlookup' =>
        -- We stepped to the substituted body
        -- The two lookups must give the same result
        rename_i cs1 T1 e1 hv1 R1 C Q m x y cs2 T2 e2_body hv2 R2
        -- hlookup and hlookup' both look up x in m, so they must be equal
        have heq : (some (Cell.val ⟨.abs cs1 T1 e1, hv1, R1⟩) : Option Cell) =
                   some (Cell.val ⟨.abs cs2 T2 e2_body, hv2, R2⟩) := by
          rw [←hlookup, ←hlookup']
        -- From equality of Options, extract equality of contents
        injection heq with heq_cell
        injection heq_cell with heq_val
        injection heq_val with heq_abs
        -- From equality of abstractions, extract equality of bodies
        injection heq_abs with _ _ _ heq_body
        -- Now we know e1 = e2_body, so the substitutions are equal
        rw [←heq_body] at rest
        -- Apply IH to the rest of the reduction
        -- Need to show (e1.subst (Subst.openVar (.free y))).WfInHeap m.heap
        have hwf_subst_body : (e1.subst (Subst.openVar (.free y))).WfInHeap m.heap := by
          -- Extract well-formedness of y from hwf
          have hwf_app := hwf
          cases hwf_app with
          | wf_app hwf_x hwf_y =>
            -- From m.wf.wf_val and hlookup, get that the abstraction body is well-formed
            have hwf_abs : Exp.WfInHeap (.abs cs1 T1 e1) m.heap :=
              m.wf.wf_val _ _ hlookup
            -- Extract well-formedness of e1 from the abstraction
            cases hwf_abs with
            | wf_abs _ _ hwf_e1 =>
              -- Build well-formed substitution
              have hwf_subst := Subst.wf_openVar hwf_y
              -- Apply substitution preservation
              exact Exp.wf_subst hwf_e1 hwf_subst
        exact ih hwf_subst_body m2 e2 hans rest
      | step_invoke =>
        rename_i cs T e hv R C Q m x y hv_unit R_unit hlookup_y hmem hlookup_cap
        have heq := Memory.lookup_deterministic hlookup hlookup_cap
        cases heq
  | eval_invoke hmem hlookup_x hlookup_y hQ =>
    intro m2 e2 hans hred
    -- Application is not an answer, so reduction cannot be refl
    cases hred with
    | refl =>
      -- .app is not an answer, contradiction
      cases hans; rename_i hv
      cases hv
    | step hstep rest =>
      -- At least one step from application
      cases hstep with
      | step_apply hlookup' =>
        -- step_apply says x contains an abstraction
        -- but hlookup_x says x contains a capability - contradiction!
        have heq := Memory.lookup_deterministic hlookup_x hlookup'
        cases heq
      | step_invoke hmem' hlookup_x' hlookup_y' =>
        -- step_invoke steps to unit
        -- rest : Reduce C m unit m2 e2
        -- unit is an answer, so by reduce_ans_eq, unit = e2 and m = m2
        have hans_unit : Exp.IsAns .unit := Exp.IsAns.is_val .unit
        have ⟨heq_m, heq_e⟩ := reduce_ans_eq hans_unit rest
        rw [←heq_m, ←heq_e]
        exact hQ
  | eval_tapply hlookup eval_body ih =>
    intro m2 e2 hans hred
    -- Type application is not an answer, so reduction cannot be refl
    cases hred with
    | refl =>
      -- .tapp is not an answer, contradiction
      cases hans; rename_i hv
      cases hv
    | step hstep rest =>
      -- The only step from tapp is step_tapply
      cases hstep with
      | step_tapply hlookup' =>
        -- Both lookups access the same location, so they must return the same value
        rename_i cs1 T0_1 e1 hv1 R1 C Q S mem x cs2 S'_2 e2_body hv2 R2
        have heq := Memory.lookup_deterministic hlookup hlookup'
        -- Extract equality of type abstraction bodies
        injection heq with heq_cell
        injection heq_cell with heq_val
        injection heq_val with _ _ _ heq_body
        -- Now we know e1 = e2_body, so the substitutions are equal
        rw [←heq_body] at rest
        -- Apply IH to the rest of the reduction
        -- Need to show (e1.subst (Subst.openTVar .top)).WfInHeap mem.heap
        have hwf_subst_body : (e1.subst (Subst.openTVar .top)).WfInHeap mem.heap := by
          -- From mem.wf.wf_val and hlookup, get that the type abstraction is well-formed
          have hwf_tabs : Exp.WfInHeap (.tabs cs1 T0_1 e1) mem.heap :=
            mem.wf.wf_val _ _ hlookup
          -- Extract well-formedness of e1 from the type abstraction
          cases hwf_tabs with
          | wf_tabs _ _ hwf_e1 =>
            -- Build well-formed substitution: .top is always well-formed
            have hwf_top : Ty.WfInHeap (.top : Ty .shape ∅) mem.heap :=
              Ty.WfInHeap.wf_top
            have hwf_subst := Subst.wf_openTVar hwf_top
            -- Apply substitution preservation
            exact Exp.wf_subst hwf_e1 hwf_subst
        exact ih hwf_subst_body m2 e2 hans rest
  | eval_capply hlookup eval_body ih =>
    intro m2 e2 hans hred
    -- Capability application is not an answer, so reduction cannot be refl
    cases hred with
    | refl =>
      -- .capp is not an answer, contradiction
      cases hans; rename_i hv
      cases hv
    | step hstep rest =>
      -- The only step from capp is step_capply
      cases hstep with
      | step_capply hlookup' =>
        -- Both lookups access the same location, so they must return the same value
        rename_i cs1 B0_1 e1 hv1 R1 C CS Q mem x cs2 B2 e2_body hv2 R2
        have heq := Memory.lookup_deterministic hlookup hlookup'
        -- Extract equality of capability abstraction bodies
        injection heq with heq_cell
        injection heq_cell with heq_val
        injection heq_val with _ _ _ heq_body
        -- Now we know e1 = e2_body, so the substitutions are equal
        rw [←heq_body] at rest
        -- Apply IH to the rest of the reduction
        -- Need to show (e1.subst (Subst.openCVar CS)).WfInHeap mem.heap
        have hwf_subst_body : (e1.subst (Subst.openCVar CS)).WfInHeap mem.heap := by
          -- From mem.wf.wf_val and hlookup, get that the capability abstraction is well-formed
          have hwf_cabs : Exp.WfInHeap (.cabs cs1 B0_1 e1) mem.heap :=
            mem.wf.wf_val _ _ hlookup
          -- Extract well-formedness of CS from hwf
          have hwf_capp := hwf
          cases hwf_capp with
          | wf_capp _ hwf_CS =>
            -- Extract well-formedness of e1 from the capability abstraction
            cases hwf_cabs with
            | wf_cabs _ _ hwf_e1 =>
              -- Build well-formed substitution
              have hwf_subst := Subst.wf_openCVar hwf_CS
              -- Apply substitution preservation
              exact Exp.wf_subst hwf_e1 hwf_subst
        exact ih hwf_subst_body m2 e2 hans rest
  | eval_letin =>
    intro m2 e_ans hans hred
    rename_i e1_body e2_body ih h_val_ih h_var_ih
    -- Extract well-formedness of subexpressions
    have ⟨hwf_e1, hwf_e2⟩ := Exp.wf_inv_letin hwf
    -- Apply reduce_letin_inv to decompose the reduction
    have hinv := reduce_letin_inv hred hans
    cases hinv with
    | inl h_var =>
      -- Variable case: e1 reduces to a variable
      obtain ⟨m0, y0, hred_e1, hred_body⟩ := h_var
      -- Apply ih to establish Q1 for the variable
      have hans_var : Exp.IsAns (.var (.free y0)) := Exp.IsAns.is_var
      have hQ1 := ih hwf_e1 m0 (.var (.free y0)) hans_var hred_e1
      -- Extract Var.WfInHeap from the fact that e1 reduced to a variable
      have hwf_var : Var.WfInHeap (.free y0 : Var .var ∅) m0.heap := by
        -- The variable must be well-formed since reduction preserves well-formedness
        have hwf_result := reduce_preserves_wf hred_e1 hwf_e1
        -- Extract Var.WfInHeap from Exp.WfInHeap for the variable
        cases hwf_result with
        | wf_var h => exact h
      -- Build well-formed substitution
      have hwf_subst := Subst.wf_openVar hwf_var
      -- e2 is well-formed in m0 (by monotonicity from reduction)
      have hsub := reduce_memory_monotonic hred_e1
      have hwf_e2_m0 := Exp.wf_monotonic hsub hwf_e2
      -- Substituted body is well-formed
      have hwf_e2_subst := Exp.wf_subst hwf_e2_m0 hwf_subst
      -- Apply h_var_ih
      exact h_var_ih hsub hwf_var hQ1 hwf_e2_subst m2 e_ans hans hred_body
    | inr h_val =>
      -- Value case: e1 reduces to a simple value that gets allocated
      obtain ⟨m0, v0, hv, hwf_v, l0, hfresh, hred_e1, hred_body⟩ := h_val
      -- Apply ih to establish Q1 for the value
      have hv_isval : v0.IsVal := by
        cases hv with
        | abs => exact Exp.IsVal.abs
        | tabs => exact Exp.IsVal.tabs
        | cabs => exact Exp.IsVal.cabs
        | unit => exact Exp.IsVal.unit
      have hans_val : v0.IsAns := Exp.IsAns.is_val hv_isval
      have hQ1 := ih hwf_e1 m0 v0 hans_val hred_e1
      -- Build well-formedness for the substituted body in the extended heap
      have hsub := reduce_memory_monotonic hred_e1
      have hwf_e2_m0 := Exp.wf_monotonic hsub hwf_e2
      -- Show (.free l0) is well-formed in extended heap
      let m_ext := m0.extend l0 ⟨v0, hv, compute_reachability m0.heap v0 hv⟩ hwf_v rfl hfresh
      have hwf_l : Var.WfInHeap (.free l0 : Var .var ∅) m_ext.heap := by
        apply Var.WfInHeap.wf_free
        unfold m_ext
        simp [Memory.extend]
        exact Heap.extend_lookup_eq _ _ _
      -- e2 is well-formed in extended heap
      have hsub_ext := Memory.extend_subsumes m0 l0
        ⟨v0, hv, compute_reachability m0.heap v0 hv⟩ hwf_v rfl hfresh
      have hwf_e2_ext := Exp.wf_monotonic hsub_ext hwf_e2_m0
      -- Build well-formed substitution
      have hwf_subst := Subst.wf_openVar hwf_l
      -- Substituted body is well-formed in extended heap
      have hwf_e2_subst := Exp.wf_subst hwf_e2_ext hwf_subst
      -- Apply h_val_ih
      exact h_val_ih hsub hv hwf_v hQ1 l0 hfresh hwf_e2_subst m2 e_ans hans hred_body
  | eval_unpack hpred eval_e1 h_val ih =>
    intro m2 e_ans hans hred
    rename_i h_val_ih
    -- Extract well-formedness of subexpressions
    have ⟨hwf_e1, hwf_e2⟩ := Exp.wf_inv_unpack hwf
    -- Apply reduce_unpack_inv to decompose the reduction
    have hinv := reduce_unpack_inv hred hans
    obtain ⟨m0, cs, x, hred_e1, hred_body⟩ := hinv
    -- e1 reduces to pack in m0
    -- Use reduce_preserves_wf to get well-formedness of the pack
    have hwf_pack := reduce_preserves_wf hred_e1 hwf_e1
    -- Extract well-formedness of cs and x from pack
    cases hwf_pack with
    | wf_pack hwf_cs hwf_x =>
      -- The pack is an answer
      have hans_pack : Exp.IsAns (.pack cs (.free x)) := by
        apply Exp.IsAns.is_val
        exact Exp.IsVal.pack
      -- Apply IH to establish Q1 for the pack
      rename_i a_ih
      have hQ1 := a_ih hwf_e1 m0 (Exp.pack cs (.free x)) hans_pack hred_e1
      -- Memory subsumption from reduction
      have hsub := reduce_memory_monotonic hred_e1
      -- e2 is well-formed in m0.heap (by monotonicity)
      have hwf_e2_m0 := Exp.wf_monotonic hsub hwf_e2
      -- Build well-formed substitution
      have hwf_subst := Subst.wf_unpack hwf_cs hwf_x
      -- Substituted body is well-formed
      have hwf_e2_subst := Exp.wf_subst hwf_e2_m0 hwf_subst
      -- Apply h_val_ih
      exact h_val_ih hsub hwf_x hwf_cs hQ1 hwf_e2_subst m2 e_ans hans hred_body

inductive IsProgressive : Memory -> Exp {} -> Prop where
| done :
  e.IsAns ->
  IsProgressive m e
| step :
  Step C m e m' e' ->
  IsProgressive m e

theorem eval_implies_progressive
  (heval : Eval C m e Q) :
  IsProgressive m e := by sorry

end CC
