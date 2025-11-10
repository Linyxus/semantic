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
  (∃ y0, Reduce C m e1 m0 (.var (.free y0)) ∧
     Reduce C m0 (e2.subst (Subst.openVar (.free y0))) m' a) ∨
  (∃ (v0 : Exp {}) (hv : v0.IsSimpleVal) (hwf : Exp.WfInHeap v0 m0.heap)
     (l0 : Nat) (hfresh : m0.heap l0 = none),
    Reduce
      C
      (m0.extend l0 ⟨v0, hv, compute_reachability m0.heap v0 hv⟩ hwf rfl hfresh)
      (e2.subst (Subst.openVar (.free l0)))
      m' a) := sorry

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
    intro m2 e2 hans hred
    rename_i ih h_val_ih h_var_ih
    -- letin is not an answer, so reduction cannot be refl
    cases hred with
    | refl =>
      -- .letin is not an answer, contradiction
      cases hans; rename_i hv
      cases hv
    | step hstep rest =>
      -- Multiple possible steps for letin
      cases hstep with
      | step_ctx_letin hstep_e1 =>
        -- e1 steps to some e1', then we have rest: Reduce C m' (.letin e1' e2') m2 e2
        -- The key insight: rest is still reducing a letin, so it will eventually
        -- reach step_rename or step_lift. We need to apply this theorem recursively.
        -- But we don't have an evaluation for (.letin e1' e2') starting from m'.
        -- We need a lemma that lets us "step" evaluations forward, or we need
        -- to restructure the proof. For now, this requires additional machinery.
        sorry
      | step_rename =>
        -- e1 = .var (.free y), the step performs renaming
        rename_i y eval_e1
        -- Extract well-formedness of subexpressions from hwf
        have ⟨hwf_e1, hwf_e2⟩ := Exp.wf_inv_letin hwf
        -- The variable is an answer
        have hans_var : Exp.IsAns (.var (.free y)) := Exp.IsAns.is_var
        -- Apply ih to establish Q1 for the variable (no reduction needed)
        have hQ1 := ih hwf_e1 _ (.var (.free y)) hans_var Reduce.refl
        -- Extract Var.WfInHeap from Exp.WfInHeap
        have hwf_var := by
          cases hwf_e1 with
          | wf_var h => exact h
        -- Build well-formed substitution
        have hwf_subst := Subst.wf_openVar hwf_var
        -- Substituted body is well-formed
        have hwf_e2_subst := Exp.wf_subst hwf_e2 hwf_subst
        -- Apply h_var_ih: given Q1 for the variable and reduction of the substituted body,
        -- we get the final postcondition
        exact h_var_ih (Memory.subsumes_refl _) hwf_var hQ1 hwf_e2_subst m2 e2 hans rest
      | step_lift hv hwf_v hfresh =>
        -- e1 is a simple value, allocate it in heap
        -- Rename all the unnamed variables in order
        rename_i C_eval e1_val Q_eval e2_body m_eval Q1_eval hpred_eval
          a_eval h_val_eval h_var_eval l
        -- Extract well-formedness of e1 and e2
        have ⟨hwf_e1, hwf_e2⟩ := Exp.wf_inv_letin hwf
        -- Convert IsSimpleVal to IsVal to IsAns
        have hv_isval : e1_val.IsVal := by
          cases hv with
          | abs => exact Exp.IsVal.abs
          | tabs => exact Exp.IsVal.tabs
          | cabs => exact Exp.IsVal.cabs
          | unit => exact Exp.IsVal.unit
        have hans_val : e1_val.IsAns := Exp.IsAns.is_val hv_isval
        -- Apply ih to establish Q1 for the value
        have hQ1 := ih hwf_e1 _ e1_val hans_val Reduce.refl
        -- Build well-formedness proof for the substituted body in the extended heap
        -- First, extended memory subsumes original
        have hsub := Memory.extend_subsumes m_eval l
          ⟨e1_val, hv, compute_reachability m_eval.heap e1_val hv⟩ hwf_v rfl hfresh
        -- e2 is well-formed in the extended heap (by monotonicity)
        have hwf_e2_ext := Exp.wf_monotonic hsub hwf_e2
        -- Show (.free l) is well-formed in extended heap
        let m_ext := m_eval.extend l
          ⟨e1_val, hv, compute_reachability m_eval.heap e1_val hv⟩ hwf_v rfl hfresh
        have hwf_l : Var.WfInHeap (.free l : Var .var ∅) m_ext.heap := by
          apply Var.WfInHeap.wf_free
          unfold m_ext
          simp [Memory.extend]
          exact Heap.extend_lookup_eq _ _ _
        have hwf_subst := Subst.wf_openVar hwf_l
        -- Substituted body is well-formed in extended heap
        have hwf_e2_subst := Exp.wf_subst hwf_e2_ext hwf_subst
        -- Apply h_val_ih with m1 = m_eval (the original memory before extension)
        -- h_val_ih will handle extending the memory with l and evaluating the substituted body
        exact h_val_ih (Memory.subsumes_refl m_eval) hv hwf_v hQ1 l hfresh
          hwf_e2_subst m2 e2 hans rest
  | eval_unpack hpred eval_e1 h_val ih =>
    intro m2 e2 hans hred
    rename_i h_val_ih
    -- unpack is not an answer, so reduction cannot be refl
    cases hred with
    | refl =>
      -- .unpack is not an answer, contradiction
      cases hans; rename_i hv
      cases hv
    | step hstep rest =>
      -- Multiple possible steps for unpack
      cases hstep with
      | step_ctx_unpack hstep_e1 =>
        -- e1 steps to some e1', then we have rest: Reduce C m' (.unpack e1' e2') m2 e2
        -- This requires additional machinery similar to step_ctx_letin
        sorry
      | step_unpack =>
        -- e1 = .pack cs (.free x), the step unpacks and substitutes
        rename_i cs x
        -- Extract well-formedness of subexpressions from hwf
        have ⟨hwf_e1, hwf_e2⟩ := Exp.wf_inv_unpack hwf
        -- The pack is an answer
        have hans_pack : Exp.IsAns (.pack cs (.free x)) := by
          apply Exp.IsAns.is_val
          exact Exp.IsVal.pack
        -- Apply ih to establish Q1 for the pack (no reduction needed)
        have hQ1 := ih hwf_e1 _ (.pack cs (.free x)) hans_pack Reduce.refl
        -- Extract well-formedness of x and cs from the pack
        have hwf_pack := hwf_e1
        cases hwf_pack with
        | wf_pack hwf_cs hwf_x =>
          -- Build well-formed substitution
          have hwf_subst := Subst.wf_unpack hwf_cs hwf_x
          -- Substituted body is well-formed
          have hwf_e2_subst := Exp.wf_subst hwf_e2 hwf_subst
          -- Apply h_val_ih
          exact h_val_ih (Memory.subsumes_refl _) hwf_x hwf_cs hQ1
            hwf_e2_subst m2 e2 hans rest

end CC
