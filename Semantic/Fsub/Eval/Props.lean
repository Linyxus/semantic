import Semantic.Fsub.Eval.BigStep
import Semantic.Fsub.Eval.SmallStep

namespace Fsub

/-- A configuration is progressive when it is an answer or can take a step. -/
inductive IsProgressive : Heap -> Exp {} -> Prop where
| done :
  e.IsAns ->
  IsProgressive h e
| step :
  Step h e h' e' ->
  IsProgressive h e

/-- If an answer has an evaluation, then the postcondition holds for it. -/
theorem eval_ans_holds_post
  (heval : Eval h e Q)
  (hans : e.IsAns) :
  Q e h := by
  cases heval with
  | eval_val hv hQ => exact hQ
  | eval_var hQ => exact hQ
  | eval_apply => cases hans; rename_i hv; cases hv
  | eval_tapply => cases hans; rename_i hv; cases hv
  | eval_letin => cases hans; rename_i hv; cases hv

/-- Progress: a configuration with an evaluation is progressive,
  provided the heap is finite (so that fresh locations can be allocated). -/
theorem eval_implies_progressive
  (hfin : h.Finite)
  (heval : Eval h e Q) :
  IsProgressive h e := by
  induction heval with
  | eval_val hv _ => exact .done (.is_val hv)
  | eval_var _ => exact .done .is_var
  | eval_apply hlookup _ _ => exact .step (Step.step_apply hlookup)
  | eval_tapply hlookup _ _ => exact .step (Step.step_tapply hlookup)
  | eval_letin _ heval1 _ _ ih1 _ _ =>
    cases ih1 hfin with
    | done hans =>
      cases hans with
      | is_val hv =>
        obtain ⟨l, hfresh⟩ := hfin.exists_fresh
        exact .step (Step.step_lift hv hfresh)
      | is_var => exact .step Step.step_rename
    | step hstep => exact .step (Step.step_ctx_letin hstep)

/-- Preservation: evaluations are preserved along single steps. -/
theorem step_preserves_eval
  (heval : Eval h1 e1 Q)
  (hstep : Step h1 e1 h2 e2) :
  Eval h2 e2 Q := by
  induction heval generalizing h2 e2 with
  | eval_val hv _ => exact absurd hstep (step_ans_absurd (.is_val hv))
  | eval_var _ => exact absurd hstep (step_ans_absurd .is_var)
  | eval_apply hlookup heval_body _ =>
    cases hstep with
    | step_apply hlookup' =>
      rw [hlookup] at hlookup'
      cases hlookup'
      exact heval_body
  | eval_tapply hlookup heval_body _ =>
    cases hstep with
    | step_tapply hlookup' =>
      rw [hlookup] at hlookup'
      cases hlookup'
      exact heval_body
  | @eval_letin _ _ _ _ Q1 hpred heval1 h_val h_var ih1 _ _ =>
    cases hstep with
    | step_ctx_letin hstep1 =>
      have hsub := step_heap_monotonic hstep1
      apply Eval.eval_letin (Q1 := Q1) hpred (ih1 hstep1)
      · intro h1 v hs1 hv hQ1 l' hfresh
        exact h_val (Heap.subsumes_trans hs1 hsub) hv hQ1 l' hfresh
      · intro h1 x hs1 hQ1
        exact h_var (Heap.subsumes_trans hs1 hsub) hQ1
    | step_rename =>
      exact h_var (Heap.subsumes_refl _) (eval_ans_holds_post heval1 .is_var)
    | step_lift hv hfresh =>
      exact h_val (Heap.subsumes_refl _) hv (eval_ans_holds_post heval1 (.is_val hv)) _ hfresh

/-- Evaluations are preserved along multi-step reduction. -/
theorem reduce_preserves_eval
  (heval : Eval h1 e1 Q)
  (hred : Reduce h1 e1 h2 e2) :
  Eval h2 e2 Q := by
  induction hred with
  | refl => exact heval
  | step hstep _ ih => exact ih (step_preserves_eval heval hstep)

/-- Any answer reachable from a configuration with an evaluation satisfies the postcondition. -/
theorem eval_to_reduce
  (heval : Eval h1 e1 Q)
  (hred : Reduce h1 e1 h2 e2)
  (hans : e2.IsAns) :
  Q e2 h2 :=
  eval_ans_holds_post (reduce_preserves_eval heval hred) hans

end Fsub
