import Semantic.Consume.Syntax
import Semantic.Consume.Substitution
import Semantic.Consume.Semantics.Heap

namespace Consume

inductive TraceItem : Type where
| access : Mutability -> Nat -> TraceItem
| drop : Nat -> TraceItem
| alloc : Nat -> TraceItem

@[reducible]
def EvalTrace : Type := List TraceItem

/-- Small-step evaluation relation recording an evaluation trace.
  `Step m e tr m' e'` means that expression `e` in memory `m` steps to `e'` in
  memory `m'`, performing the capability operations recorded in the trace `tr`.
  Each primitive operation contributes a single `TraceItem`; pure reductions
  contribute the empty trace, and the congruence rules propagate the trace of
  the sub-step. -/
inductive Step : Memory -> Exp {} -> EvalTrace -> Memory -> Exp {} -> Prop where
| step_alloc :
  m.lookup x = some (.val ⟨if b then .btrue else .bfalse, hv, R⟩) ->
  (hfresh : m.heap l = none) ->
  Step m (.alloc (.free x))
    [.alloc l]
    (m.extend_mcell l b hfresh)
    (.pack (.var (.M .epsilon) (.free l)) (.free l))
| step_apply :
  m.lookup x = some (.val ⟨.abs cs T e, hv, R⟩) ->
  Step m (.app (.free x) y) [] m (e.subst (Subst.openVar y))
| step_invoke :
  m.lookup x = some (.capability .basic) ->
  m.lookup y = some (.val ⟨.unit, hv, R⟩) ->
  Step m (.app (.free x) (.free y)) [.access .epsilon x] m .unit
| step_tapply :
  m.lookup x = some (.val ⟨.tabs cs S' e, hv, R⟩) ->
  Step m (.tapp (.free x) S) [] m (e.subst (Subst.openTVar .top))
| step_capply :
  m.lookup x = some (.val ⟨.cabs cs B e, hv, R⟩) ->
  Step m (.capp (.free x) CS) [] m (e.subst (Subst.openCVar CS))
| step_read :
  m.lookup x = some (.val ⟨.reader (.free y), hv_reader, R_reader⟩) ->
  m.lookup y = some (.capability (.mcell b .live)) ->
  Step m (.read (.free x)) [.access .ro y] m (if b then .btrue else .bfalse)
| step_write_true :
  (hx : m.lookup x = some (.capability (.mcell b0 .live))) ->
  m.lookup y = some (.val ⟨.btrue, hv, R⟩) ->
  Step m (.write (.free x) (.free y)) [.access .epsilon x]
    (m.update_mcell x true .live ⟨b0, hx⟩) .unit
| step_write_false :
  (hx : m.lookup x = some (.capability (.mcell b0 .live))) ->
  m.lookup y = some (.val ⟨.bfalse, hv, R⟩) ->
  Step m (.write (.free x) (.free y)) [.access .epsilon x]
    (m.update_mcell x false .live ⟨b0, hx⟩) .unit
| step_drop :
  (hx : m.lookup x = some (.capability (.mcell b .live))) ->
  Step m (.drop (.free x)) [.drop x] (m.drop_mcell x ⟨b, hx⟩) .unit
| step_ctx_letin :
  Step m e1 tr m' e1' ->
  Step m (.letin e1 e2) tr m' (.letin e1' e2)
| step_ctx_unpack :
  Step m e1 tr m' e1' ->
  Step m (.unpack e1 e2) tr m' (.unpack e1' e2)
| step_rename :
  Step m (.letin (.var (.free y)) e) [] m (e.subst (Subst.openVar (.free y)))
| step_lift :
  (hv : Exp.IsSimpleVal v) ->
  (hwf : Exp.WfInHeap v m.heap) ->
  (hfresh : m.heap l = none) ->
  Step
    m (.letin v e) []
    (m.extend l ⟨v, hv, compute_reachability m.heap v hv⟩ hwf rfl hfresh)
    (e.subst (Subst.openVar (.free l)))
| step_unpack :
  Step m (.unpack (.pack cs (.free x)) e) [] m (e.subst (Subst.unpack cs (.free x)))
| step_cond_true :
  resolve m.heap (.var x) = some .btrue ->
  Step m (.cond x e1 e2) [] m e1
| step_cond_false :
  resolve m.heap (.var x) = some .bfalse ->
  Step m (.cond x e1 e2) [] m e2

/-- Multi-step reduction relation: reflexive-transitive closure of `Step`,
  accumulating the concatenated evaluation trace.
  `Reduce m e tr m' e'` means that `e` in memory `m` reduces in multiple steps to
  `e'` in memory `m'`, performing the operations recorded in trace `tr`. -/
inductive Reduce : Memory -> Exp {} -> EvalTrace -> Memory -> Exp {} -> Prop where
| refl :
  Reduce m e [] m e
| step :
  Step m1 e1 tr1 m2 e2 ->
  Reduce m2 e2 tr2 m3 e3 ->
  Reduce m1 e1 (tr1 ++ tr2) m3 e3

theorem reduce_trans
  (hred1 : Reduce m1 e1 tr1 m2 e2)
  (hred2 : Reduce m2 e2 tr2 m3 e3) :
  Reduce m1 e1 (tr1 ++ tr2) m3 e3 := by
  induction hred1 with
  | refl => exact hred2
  | step h rest ih =>
    rw [List.append_assoc]
    exact Reduce.step h (ih hred2)

end Consume
