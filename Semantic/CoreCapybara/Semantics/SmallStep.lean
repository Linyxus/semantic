import Semantic.CoreCapybara.Syntax
import Semantic.CoreCapybara.Substitution
import Semantic.CoreCapybara.Semantics.Heap

namespace CoreCapybara

/-- Grow a capture set `C` by the cells freshly allocated within a trace `t`, each given
  full authority (access `.M .epsilon` and `.drop`).  Grows a `par` branch's annotation as
  it allocates, so a later access/drop of an own fresh cell is covered by the grown
  annotation's reachability.  A left fold, so `growByAllocs C [] = C` definitionally and it
  telescopes over `++` (`growByAllocs_append`).  For a live mcell `l`,
  `(growByAllocs C t).reachability m` set-equals `C.reachability m ∪ capsOf (allocList t)`. -/
def CaptureSet.growByAllocs : CaptureSet {} → Trace → CaptureSet {}
| C, [] => C
| C, (.alloc l :: t) =>
    CaptureSet.growByAllocs ((.var (.M .epsilon) (.free l)) ∪ ((.var .drop (.free l)) ∪ C)) t
| C, (.access _ _ :: t) => CaptureSet.growByAllocs C t
| C, (.dealloc _ :: t) => CaptureSet.growByAllocs C t

/-- `growByAllocs` telescopes over trace concatenation (it is a left fold). -/
theorem CaptureSet.growByAllocs_append (C : CaptureSet {}) (t1 t2 : Trace) :
    C.growByAllocs (t1 ++ t2) = (C.growByAllocs t1).growByAllocs t2 := by
  induction t1 generalizing C with
  | nil => rfl
  | cons it t1 ih => cases it <;> simp only [List.cons_append, CaptureSet.growByAllocs, ih]

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
-- Boxed terms are values: no `wrap` reduction rule, only `unwrap`.
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
-- `par e1 e2` interleaves both branches: either branch may take the next step (the two
-- congruence rules), so a run is an arbitrary interleaving of the branches' events.  Once
-- both are answers the single join rule reduces to `.unit`, keeping `par : .typ .unit`
-- type-correct and the join confluent.  Separation (the `par` typing rule's
-- `SepCheck Γ C1 C2`) is what makes the interleaving sound.
| step_par_left {C1 C2 : CaptureSet {}} :
  Step t m e1 m' e1' ->
  (ht : TraceOk t (C1.reachability m)) ->
  (hni : CapabilitySet.Noninterference (C1.reachability m) (C2.reachability m)) ->
  Step t m (.par C1 C2 e1 e2) m' (.par (C1.growByAllocs t) C2 e1' e2)
| step_par_right :
  (ht : TraceOk t (C2.reachability m)) ->
  (hni : CapabilitySet.Noninterference (C1.reachability m) (C2.reachability m)) ->
  Step t m e2 m' e2' ->
  Step t m (.par C1 C2 e1 e2) m' (.par C1 (C2.growByAllocs t) e1 e2')
| step_par_join :
  e1.IsAns -> e2.IsAns ->
  Step [] m (.par C1 C2 e1 e2) m .unit
| step_rename :
  Step [] m (.letin (.var (.free y)) e) m (e.subst (Subst.openVar (.free y)))
-- Lifting a value to the heap is not a capability event: it emits no trace.
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
| step_ctx_consumer_app :
  Step t m e m' e' ->
  Step t m (.consumer_app x e) m' (.consumer_app x e')
| step_consumer_apply :
  m.lookup x = some (.val ⟨.consumer T cs body, hv, R⟩) ->
  Step [] m (.consumer_app (.free x) (.pack D (.free w))) m
    (body.subst (Subst.unpack D (.free w)))

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

/-- Sequential small-step relation.  Identical to `Step` except that `par` is scheduled
  left-to-right: the right branch may step only once the left branch is an answer
  (`step_par_right` carries `e1.IsAns`).  This is the schedule for which the sequential
  big-step bridge is exact (`bs_par` runs the branches in this order), so the small↔big
  preservation/progress results go through with no trace reordering.  Every `SeqStep` over
  a `Safe` configuration is a `Step`; the converse — every `Step` run is
  permutation-equivalent to a `SeqStep` run — is the standardization theorem. -/
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
  SeqStep t m (.par C1 C2 e1 e2) m' (.par (C1.growByAllocs t) C2 e1' e2)
-- Right branch steps only once the left is an answer: the single difference from `Step`.
| step_par_right :
  e1.IsAns ->
  SeqStep t m e2 m' e2' ->
  SeqStep t m (.par C1 C2 e1 e2) m' (.par C1 (C2.growByAllocs t) e1 e2')
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
-- Consumer application: see `Step.step_ctx_consumer_app`/`step_consumer_apply`.
| step_ctx_consumer_app :
  SeqStep t m e m' e' ->
  SeqStep t m (.consumer_app x e) m' (.consumer_app x e')
| step_consumer_apply :
  m.lookup x = some (.val ⟨.consumer T cs body, hv, R⟩) ->
  SeqStep [] m (.consumer_app (.free x) (.pack D (.free w))) m
    (body.subst (Subst.unpack D (.free w)))

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

-- The `SeqStep ⊆ Step` inclusion (`SeqStep.toStep` / `SeqReduce.toReduce`) lives in
-- `Semantics/Standardization.lean`: discharging the `TraceOk` and `Noninterference` guards
-- on `Step`'s `par` rules needs the `Safe` invariant at every `par` node, available there.

end CoreCapybara
