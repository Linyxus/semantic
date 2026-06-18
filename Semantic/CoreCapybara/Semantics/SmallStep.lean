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
-- `par e1 e2` runs BOTH branches with interleaved (preemptive) scheduling.
-- Either branch may take the next step (the two congruence rules), so a whole
-- run is an arbitrary interleaving of the branches' events.  Once BOTH branches
-- have reached answers, the single join rule retires the construct, yielding the
-- canonical unit value `.unit` (both branches ran only for their effects; their
-- result values are discarded).
--   * Result = `.unit` keeps `par : .typ .unit` type-correct and, crucially,
--     CONFLUENT: a single join rule with a fixed result is not a critical pair,
--     so all schedules agree on the result (unlike an either-branch join).
--   * Separation — already required by the `par` typing rule (`SepCheck Γ C1 C2`)
--     — makes the final memory independent of the interleaving; that is the
--     content of the sequentialization theorems stated in `Semantics.Props`.
| step_par_left :
  Step t m e1 m' e1' ->
  Step t m (.par e1 e2) m' (.par e1' e2)
| step_par_right :
  Step t m e2 m' e2' ->
  Step t m (.par e1 e2) m' (.par e1 e2')
| step_par_join :
  e1.IsAns -> e2.IsAns ->
  Step [] m (.par e1 e2) m .unit
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

end CoreCapybara
