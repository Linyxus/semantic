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

theorem eval_to_reduce
  (heval : Eval C m1 e1 Q) :
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
        exact ih m2 e2 hans rest
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
        rename_i cs1 T1 e1 hv1 R1 C Q m x S cs2 T2 e2_body hv2 R2
        have heq := Memory.lookup_deterministic hlookup hlookup'
        -- Extract equality of type abstraction bodies
        injection heq with heq_cell
        injection heq_cell with heq_val
        injection heq_val with _ _ _ heq_body
        -- Now we know e1 = e2_body, so the substitutions are equal
        rw [←heq_body] at rest
        -- Apply IH to the rest of the reduction
        exact ih m2 e2 hans rest
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
        rename_i cs1 B1 e1 hv1 R1 C Q m x CS cs2 B2 e2_body hv2 R2
        have heq := Memory.lookup_deterministic hlookup hlookup'
        -- Extract equality of capability abstraction bodies
        injection heq with heq_cell
        injection heq_cell with heq_val
        injection heq_val with _ _ _ heq_body
        -- Now we know e1 = e2_body, so the substitutions are equal
        rw [←heq_body] at rest
        -- Apply IH to the rest of the reduction
        exact ih m2 e2 hans rest
  | eval_letin hpred eval_e1 h_val h_var ih =>
    intro m2 e2 hans hred
    sorry
  | eval_unpack hpred eval_e1 h_val ih =>
    intro m2 e2 hans hred
    sorry

end CC
