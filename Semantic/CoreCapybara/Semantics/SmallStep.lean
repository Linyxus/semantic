import Semantic.CoreCapybara.Syntax
import Semantic.CoreCapybara.Substitution
import Semantic.CoreCapybara.Semantics.Heap

namespace CoreCapybara

/-- Small-step evaluation relation instrumented with a trace.
  `Step t m e m' e'` means that expression `e` in memory `m` steps to `e'` in
  memory `m'`, emitting the trace `t` of heap events performed by this step. -/
inductive Step : Trace -> Memory -> Exp {} -> Memory -> Exp {} -> Prop where
| step_apply :
  m.lookup x = some (.val ⟨.abs cs T e, hv, R⟩) ->
  Step [] m (.app (.free x) (.free y)) m (e.subst (Subst.openVar (.free y)))
| step_invoke :
  m.lookup x = some (.capability .basic) ->
  m.lookup y = some (.val ⟨.unit, hv, R⟩) ->
  Step [.access .epsilon x] m (.app (.free x) (.free y)) m .unit
| step_tapply :
  m.lookup x = some (.val ⟨.tabs cs S' e, hv, R⟩) ->
  Step [] m (.tapp (.free x) S) m (e.subst (Subst.openTVar .top))
| step_capply :
  m.lookup x = some (.val ⟨.cabs cs B e, hv, R⟩) ->
  Step [] m (.capp (.free x) CS) m (e.subst (Subst.openCVar CS))
-- Boxed terms are values, so wrap has no reduction rule; only unwrap steps.
| step_unwrap :
  m.lookup x = some (.val ⟨.boxed cs Ψ e, hv, R⟩) ->
  Step [] m (.unwrap (.free x)) m e
| step_cond_var_true :
  m.lookup x = some (.val ⟨.btrue, hv, R⟩) ->
  Step [] m (.cond (.free x) e1 e2) m e1
| step_cond_var_false :
  m.lookup x = some (.val ⟨.bfalse, hv, R⟩) ->
  Step [] m (.cond (.free x) e1 e2) m e2
| step_read :
  m.lookup x = some (.val ⟨.reader (.free y), hv_reader, R_reader⟩) ->
  m.lookup y = some (.capability (.mcell b .live)) ->
  Step [.access .ro y] m (.read (.free x)) m (if b then .btrue else .bfalse)
| step_write_true :
  (hx : m.lookup x = some (.capability (.mcell b0 .live))) ->
  m.lookup y = some (.val ⟨.btrue, hv, R⟩) ->
  Step [.access .epsilon x] m (.write (.free x) (.free y))
    (m.update_mcell x true .live ⟨b0, hx⟩) .unit
| step_write_false :
  (hx : m.lookup x = some (.capability (.mcell b0 .live))) ->
  m.lookup y = some (.val ⟨.bfalse, hv, R⟩) ->
  Step [.access .epsilon x] m (.write (.free x) (.free y))
    (m.update_mcell x false .live ⟨b0, hx⟩) .unit
| step_alloc :
  m.lookup x = some (.val ⟨if b then .btrue else .bfalse, hv, R⟩) ->
  (hfresh : m.heap l = none) ->
  Step [.alloc l] m (.alloc (.free x))
    (m.extend_mcell l b hfresh)
    (.pack (.var (.M .epsilon) (.free l)) (.free l))
| step_drop :
  (hx : m.lookup x = some (.capability (.mcell b .live))) ->
  Step [.dealloc x] m (.drop (.free x))
    (m.drop_mcell x ⟨b, hx⟩) .unit
| step_ctx_letin :
  Step t m e1 m' e1' ->
  Step t m (.letin e1 e2) m' (.letin e1' e2)
| step_ctx_unpack :
  Step t m e1 m' e1' ->
  Step t m (.unpack e1 e2) m' (.unpack e1' e2)
-- `par e1 e2` runs BOTH branches with GENUINE INTERLEAVING: either branch may take
-- the next step (the two congruence rules), so a whole run is an arbitrary
-- interleaving of the branches' events.  Once BOTH branches are answers the single
-- join rule retires the construct to the canonical unit value `.unit` — which keeps
-- `par : .typ .unit` type-correct and the join confluent (single rule, fixed
-- result).  Separation (the `par` typing rule's `SepCheck Γ C1 C2`) is what makes
-- the interleaving sound; CSL soundness of parallel composition is
-- `Fundamental.sem_typ_par`.
| step_par_left :
  Step t m e1 m' e1' ->
  Step t m (.par C1 C2 e1 e2) m' (.par C1 C2 e1' e2)
| step_par_right :
  Step t m e2 m' e2' ->
  Step t m (.par C1 C2 e1 e2) m' (.par C1 C2 e1 e2')
| step_par_join :
  e1.IsAns -> e2.IsAns ->
  Step [] m (.par C1 C2 e1 e2) m .unit
| step_rename :
  Step [] m (.letin (.var (.free y)) e) m (e.subst (Subst.openVar (.free y)))
-- Lifting a value to the heap is not a capability event, so it emits no trace.
| step_lift :
  (hv : Exp.IsSimpleVal v) ->
  (hwf : Exp.WfInHeap v m.heap) ->
  (hfresh : m.heap l = none) ->
  Step
    []
    m (.letin v e)
    (m.extend l ⟨v, hv, compute_reachability m.heap v hv⟩ hwf rfl hfresh)
    (e.subst (Subst.openVar (.free l)))
| step_unpack :
  Step [] m (.unpack (.pack cs (.free x)) e) m (e.subst (Subst.unpack cs (.free x)))

/-- Multi-step reduction relation: reflexive-transitive closure of `Step`,
  accumulating the traces of the individual steps in order.
  `Reduce t m e m' e'` means that `e` in memory `m` reduces to `e'` in memory
  `m'`, emitting the concatenated trace `t`. -/
inductive Reduce : Trace -> Memory -> Exp {} -> Memory -> Exp {} -> Prop where
| refl :
  Reduce [] m e m e
| step :
  Step t1 m1 e1 m2 e2 ->
  Reduce t2 m2 e2 m3 e3 ->
  Reduce (t1 ++ t2) m1 e1 m3 e3

theorem reduce_trans
  (hred1 : Reduce t1 m1 e1 m2 e2)
  (hred2 : Reduce t2 m2 e2 m3 e3) :
  Reduce (t1 ++ t2) m1 e1 m3 e3 := by
  induction hred1 with
  | refl => exact hred2
  | step h rest ih =>
    rw [List.append_assoc]
    exact Reduce.step h (ih hred2)

/-- **Sequential** small-step relation.  Identical to `Step` except that `par` is
  scheduled left-to-right: the RIGHT branch may step only once the LEFT branch is an
  answer (`step_par_right` carries `e1.IsAns`).  This is the canonical schedule for
  which the sequential big-step bridge is *exact* (`bs_par` runs the branches in this
  order), so the small↔big preservation/progress results go through with no trace
  reordering.  Every `SeqStep` is a `Step` (`SeqStep.toStep`); the converse — every
  `Step` run is permutation-equivalent to a `SeqStep` run — is the standardization
  theorem relating the two schedules. -/
inductive SeqStep : Trace -> Memory -> Exp {} -> Memory -> Exp {} -> Prop where
| step_apply :
  m.lookup x = some (.val ⟨.abs cs T e, hv, R⟩) ->
  SeqStep [] m (.app (.free x) (.free y)) m (e.subst (Subst.openVar (.free y)))
| step_invoke :
  m.lookup x = some (.capability .basic) ->
  m.lookup y = some (.val ⟨.unit, hv, R⟩) ->
  SeqStep [.access .epsilon x] m (.app (.free x) (.free y)) m .unit
| step_tapply :
  m.lookup x = some (.val ⟨.tabs cs S' e, hv, R⟩) ->
  SeqStep [] m (.tapp (.free x) S) m (e.subst (Subst.openTVar .top))
| step_capply :
  m.lookup x = some (.val ⟨.cabs cs B e, hv, R⟩) ->
  SeqStep [] m (.capp (.free x) CS) m (e.subst (Subst.openCVar CS))
| step_unwrap :
  m.lookup x = some (.val ⟨.boxed cs Ψ e, hv, R⟩) ->
  SeqStep [] m (.unwrap (.free x)) m e
| step_cond_var_true :
  m.lookup x = some (.val ⟨.btrue, hv, R⟩) ->
  SeqStep [] m (.cond (.free x) e1 e2) m e1
| step_cond_var_false :
  m.lookup x = some (.val ⟨.bfalse, hv, R⟩) ->
  SeqStep [] m (.cond (.free x) e1 e2) m e2
| step_read :
  m.lookup x = some (.val ⟨.reader (.free y), hv_reader, R_reader⟩) ->
  m.lookup y = some (.capability (.mcell b .live)) ->
  SeqStep [.access .ro y] m (.read (.free x)) m (if b then .btrue else .bfalse)
| step_write_true :
  (hx : m.lookup x = some (.capability (.mcell b0 .live))) ->
  m.lookup y = some (.val ⟨.btrue, hv, R⟩) ->
  SeqStep [.access .epsilon x] m (.write (.free x) (.free y))
    (m.update_mcell x true .live ⟨b0, hx⟩) .unit
| step_write_false :
  (hx : m.lookup x = some (.capability (.mcell b0 .live))) ->
  m.lookup y = some (.val ⟨.bfalse, hv, R⟩) ->
  SeqStep [.access .epsilon x] m (.write (.free x) (.free y))
    (m.update_mcell x false .live ⟨b0, hx⟩) .unit
| step_alloc :
  m.lookup x = some (.val ⟨if b then .btrue else .bfalse, hv, R⟩) ->
  (hfresh : m.heap l = none) ->
  SeqStep [.alloc l] m (.alloc (.free x))
    (m.extend_mcell l b hfresh)
    (.pack (.var (.M .epsilon) (.free l)) (.free l))
| step_drop :
  (hx : m.lookup x = some (.capability (.mcell b .live))) ->
  SeqStep [.dealloc x] m (.drop (.free x))
    (m.drop_mcell x ⟨b, hx⟩) .unit
| step_ctx_letin :
  SeqStep t m e1 m' e1' ->
  SeqStep t m (.letin e1 e2) m' (.letin e1' e2)
| step_ctx_unpack :
  SeqStep t m e1 m' e1' ->
  SeqStep t m (.unpack e1 e2) m' (.unpack e1' e2)
| step_par_left :
  SeqStep t m e1 m' e1' ->
  SeqStep t m (.par C1 C2 e1 e2) m' (.par C1 C2 e1' e2)
-- The RIGHT branch steps only once the LEFT branch is an answer: this is the single
-- difference from `Step`, sequentializing the `par` schedule.
| step_par_right :
  e1.IsAns ->
  SeqStep t m e2 m' e2' ->
  SeqStep t m (.par C1 C2 e1 e2) m' (.par C1 C2 e1 e2')
| step_par_join :
  e1.IsAns -> e2.IsAns ->
  SeqStep [] m (.par C1 C2 e1 e2) m .unit
| step_rename :
  SeqStep [] m (.letin (.var (.free y)) e) m (e.subst (Subst.openVar (.free y)))
| step_lift :
  (hv : Exp.IsSimpleVal v) ->
  (hwf : Exp.WfInHeap v m.heap) ->
  (hfresh : m.heap l = none) ->
  SeqStep
    []
    m (.letin v e)
    (m.extend l ⟨v, hv, compute_reachability m.heap v hv⟩ hwf rfl hfresh)
    (e.subst (Subst.openVar (.free l)))
| step_unpack :
  SeqStep [] m (.unpack (.pack cs (.free x)) e) m (e.subst (Subst.unpack cs (.free x)))

/-- Multi-step sequential reduction: reflexive-transitive closure of `SeqStep`. -/
inductive SeqReduce : Trace -> Memory -> Exp {} -> Memory -> Exp {} -> Prop where
| refl :
  SeqReduce [] m e m e
| step :
  SeqStep t1 m1 e1 m2 e2 ->
  SeqReduce t2 m2 e2 m3 e3 ->
  SeqReduce (t1 ++ t2) m1 e1 m3 e3

theorem seqreduce_trans
  (hred1 : SeqReduce t1 m1 e1 m2 e2)
  (hred2 : SeqReduce t2 m2 e2 m3 e3) :
  SeqReduce (t1 ++ t2) m1 e1 m3 e3 := by
  induction hred1 with
  | refl => exact hred2
  | step h rest ih =>
    rw [List.append_assoc]
    exact SeqReduce.step h (ih hred2)

/-- Every sequential step is an (interleaving) step: `SeqStep ⊆ Step`. -/
theorem SeqStep.toStep (h : SeqStep t m e m' e') : Step t m e m' e' := by
  induction h with
  | step_apply hlk => exact Step.step_apply hlk
  | step_invoke hx hy => exact Step.step_invoke hx hy
  | step_tapply hlk => exact Step.step_tapply hlk
  | step_capply hlk => exact Step.step_capply hlk
  | step_unwrap hlk => exact Step.step_unwrap hlk
  | step_cond_var_true hlk => exact Step.step_cond_var_true hlk
  | step_cond_var_false hlk => exact Step.step_cond_var_false hlk
  | step_read hr hc => exact Step.step_read hr hc
  | step_write_true hx hy => exact Step.step_write_true hx hy
  | step_write_false hx hy => exact Step.step_write_false hx hy
  | step_alloc hlk hfresh => exact Step.step_alloc hlk hfresh
  | step_drop hx => exact Step.step_drop hx
  | step_ctx_letin _ ih => exact Step.step_ctx_letin ih
  | step_ctx_unpack _ ih => exact Step.step_ctx_unpack ih
  | step_par_left _ ih => exact Step.step_par_left ih
  | step_par_right _ _ ih => exact Step.step_par_right ih
  | step_par_join h1 h2 => exact Step.step_par_join h1 h2
  | step_rename => exact Step.step_rename
  | step_lift hv hwf hfresh => exact Step.step_lift hv hwf hfresh
  | step_unpack => exact Step.step_unpack

/-- Every sequential reduction is an (interleaving) reduction: `SeqReduce ⊆ Reduce`. -/
theorem SeqReduce.toReduce (h : SeqReduce t m e m' e') : Reduce t m e m' e' := by
  induction h with
  | refl => exact Reduce.refl
  | step hstep _ ih => exact Reduce.step hstep.toStep ih

end CoreCapybara
