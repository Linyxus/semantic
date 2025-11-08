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

-- /-- For any evaluation, an answer exists. -/
-- theorem eval_ans_exists
--   (heval : Eval C m e Q) :
--   ∃ a, Q a m ∧ a.IsAns := sorry

-- /-- Go from evaluation to reduction. -/
-- theorem eval_to_reduce_exists
--   (heval : Eval C m1 e1 Q) :
--   ∃ m2 e2,
--     Reduce C m1 e1 m2 e2 ∧
--     Q e2 m2 := by
--   induction heval with
--   | eval_val hv hQ =>
--     -- Base case: already a value
--     exact ⟨_, _, Reduce.refl, hQ⟩
--   | eval_var hQ =>
--     -- Base case: already a variable
--     exact ⟨_, _, Reduce.refl, hQ⟩
--   | eval_apply hlookup _ ih =>
--     -- Step from app to substituted body, then reduce
--     -- Note: In signature {}, there are no bound variables, so y must be a free variable
--     -- But the type doesn't enforce this statically. We rely on the semantics being well-formed.
--     obtain ⟨m2, e2, hred, hQ⟩ := ih
--     -- We need y to be .free for step_apply, but big-step allows any Var
--     -- This is a potential issue if y is not .free
--     sorry  -- Cannot prove without knowing y is .free
--   | eval_invoke hmem hlookup_x hlookup_y hQ =>
--     -- Single step to unit
--     exact ⟨_, _, Reduce.single (Step.step_invoke hmem hlookup_x hlookup_y), hQ⟩
--   | eval_tapply hlookup _ ih =>
--     -- SEMANTIC MISMATCH:
--     -- Big-step: Eval C m (e.subst (Subst.openTVar S)) Q
--     -- Small-step: Step C m (.tapp (.free x) S) m (e.subst (Subst.openTVar .top))
--     -- The big-step uses the actual type argument S, but small-step erases to .top
--     sorry
--   | eval_capply hlookup _ ih =>
--     -- SEMANTIC MISMATCH:
--     -- Big-step: Eval C m (e.subst (Subst.openCVar CS)) Q
--     -- Small-step: Step C m (.capp (.free x) CS) m (e.subst (Subst.openCVar .empty))
--     -- The big-step uses the actual capture set CS, but small-step erases to .empty
--     sorry
--   | eval_letin hpred _ h_val h_var ih =>
--     -- THE PROBLEMATIC CASE
--     -- By IH on e1, we get some m1', e1' with reduction and Q1 e1' m1'
--     obtain ⟨m1', e1', hred1, hQ1⟩ := ih
--     -- We can reduce letin e1 e2 to letin e1' e2 using congruence
--     -- But now we don't know if e1' is a value, variable, or something else!
--     sorry
--   | eval_unpack hpred _ h_val ih =>
--     -- Similar problem as eval_letin
--     sorry

theorem eval_to_reduce
  (heval : Eval C m1 e1 Q) :
  ∀ m2 e2,
    e2.IsAns ->
    Reduce C m1 e1 m2 e2 ->
    Q e2 m2 := by sorry

end CC
