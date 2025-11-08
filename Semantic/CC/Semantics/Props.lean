import Semantic.CC.Semantics.SmallStep
import Semantic.CC.Semantics.BigStep
namespace CC

/-- Step is monotonic with respect to capability sets:
    if a step can happen under authority R1, it can happen under any larger authority R2. -/
theorem step_capability_set_monotonic {R1 R2 : CapabilitySet}
  (hstep : Step R1 h e h' e') (hsub : R1 ⊆ R2) :
  Step R2 h e h' e' := by
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
  | step_lift hv hfresh =>
    apply Step.step_lift hv hfresh
  | step_unpack =>
    apply Step.step_unpack

/-- Reduce (multi-step reduction) is monotonic with respect to capability sets:
    if a reduction can happen under authority R1, it can happen under any larger authority R2. -/
theorem small_step_capability_set_monotonic {R1 R2 : CapabilitySet}
  (hred : Reduce R1 h e h' e') (hsub : R1 ⊆ R2) :
  Reduce R2 h e h' e' := by
  induction hred generalizing R2 with
  | refl =>
    apply Reduce.refl
  | single hstep =>
    apply Reduce.single
    exact step_capability_set_monotonic hstep hsub
  | trans _ _ ih1 ih2 =>
    exact Reduce.trans (ih1 hsub) (ih2 hsub)

end CC
