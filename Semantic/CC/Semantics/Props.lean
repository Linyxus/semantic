import Semantic.CC.Semantics.SmallStep
import Semantic.CC.Semantics.BigStep
namespace CC

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
  | single hstep =>
    apply Reduce.single
    exact step_capability_set_monotonic hstep hsub
  | trans _ _ ih1 ih2 =>
    exact Reduce.trans (ih1 hsub) (ih2 hsub)

/-- Helper: Congruence for Reduce in letin context. -/
theorem reduce_ctx_letin
  (hred : Reduce C m e1 m' e1') :
  Reduce C m (.letin e1 e2) m' (.letin e1' e2) := by
  induction hred with
  | refl => apply Reduce.refl
  | single hstep =>
    apply Reduce.single
    apply Step.step_ctx_letin hstep
  | trans _ _ ih1 ih2 =>
    exact Reduce.trans ih1 ih2

/-- Helper: Congruence for Reduce in unpack context. -/
theorem reduce_ctx_unpack
  (hred : Reduce C m e1 m' e1') :
  Reduce C m (.unpack e1 e2) m' (.unpack e1' e2) := by
  induction hred with
  | refl => apply Reduce.refl
  | single hstep =>
    apply Reduce.single
    apply Step.step_ctx_unpack hstep
  | trans _ _ ih1 ih2 =>
    exact Reduce.trans ih1 ih2

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
  | single hstep => exact step_memory_monotonic hstep
  | trans _ _ ih1 ih2 =>
    exact Memory.subsumes_trans ih2 ih1

theorem eval_to_reduce
  (heval : Eval C m1 e1 Q) :
  ∀ m2 e2,
    e2.IsAns ->
    Reduce C m1 e1 m2 e2 ->
    Q e2 m2 := by
  induction heval with
  | eval_val hv hQ => sorry
  | eval_var hQ =>
    intro m2 e2 hans hred
    sorry
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
    | single hstep =>
      -- Single step from application
      cases hstep with
      | step_apply hlookup' =>
        -- We stepped to the substituted body
        -- By IH on the body evaluation with Reduce.refl
        sorry
      | step_invoke =>
        -- This is for capability invocation, different from eval_apply
        sorry
    | trans hred1 hred2 =>
      -- Multi-step reduction
      sorry
  | eval_invoke hmem hlookup_x hlookup_y hQ =>
    intro m2 e2 hans hred
    sorry
  | eval_tapply hlookup eval_body ih =>
    intro m2 e2 hans hred
    sorry
  | eval_capply hlookup eval_body ih =>
    intro m2 e2 hans hred
    sorry
  | eval_letin hpred eval_e1 h_val h_var ih =>
    intro m2 e2 hans hred
    sorry
  | eval_unpack hpred eval_e1 h_val ih =>
    intro m2 e2 hans hred
    sorry

end CC
