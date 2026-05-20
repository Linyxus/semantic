import Semantic.Consume.Syntax
import Semantic.Consume.Substitution
import Semantic.Consume.Semantics.Heap

namespace Consume

/-- Small-step evaluation relation indexed by a capability set upper bound.
  Step C m e m' e' means that expression e in memory m steps to e' in memory m'
  using at most capabilities from C. TODO: the small step semantics is just a
  placeholder for now and it does not work properly. To be revisited when the
  system has one more round of iteration. -/
inductive Step : CapabilitySet -> Memory -> Exp {} -> Memory -> Exp {} -> Prop where
| step_alloc :
  m.lookup x = some (.val ⟨if b then .btrue else .bfalse, hv, R⟩) ->
  (hfresh : m.heap l = none) ->
  Step C m (.alloc (.free x))
    (m.extend_mcell l b hfresh)
    (.pack (.var .epsilon (.free l)) (.free l))
| step_apply :
  m.lookup x = some (.val ⟨.abs cs T e, hv, R⟩) ->
  Step C m (.app (.free x) y) m (e.subst (Subst.openVar y))
| step_invoke :
  C.covers (.access .epsilon) x ->
  m.lookup x = some (.capability .basic) ->
  m.lookup y = some (.val ⟨.unit, hv, R⟩) ->
  Step C m (.app (.free x) (.free y)) m .unit
| step_tapply :
  m.lookup x = some (.val ⟨.tabs cs S' e, hv, R⟩) ->
  Step C m (.tapp (.free x) S) m (e.subst (Subst.openTVar .top))
| step_capply :
  m.lookup x = some (.val ⟨.cabs cs B e, hv, R⟩) ->
  Step C m (.capp (.free x) CS) m (e.subst (Subst.openCVar CS))
| step_read :
  C.covers (.access .ro) y ->
  m.lookup x = some (.val ⟨.reader (.free y), hv_reader, R_reader⟩) ->
  m.lookup y = some (.capability (.mcell b .live)) ->
  Step C m (.read (.free x)) m (if b then .btrue else .bfalse)
| step_write_true :
  C.covers (.access .epsilon) x ->
  (hx : m.lookup x = some (.capability (.mcell b0 .live))) ->
  m.lookup y = some (.val ⟨.btrue, hv, R⟩) ->
  Step C m (.write (.free x) (.free y)) (m.update_mcell x true .live ⟨b0, hx⟩) .unit
| step_write_false :
  C.covers (.access .epsilon) x ->
  (hx : m.lookup x = some (.capability (.mcell b0 .live))) ->
  m.lookup y = some (.val ⟨.bfalse, hv, R⟩) ->
  Step C m (.write (.free x) (.free y)) (m.update_mcell x false .live ⟨b0, hx⟩) .unit
| step_drop :
  C.covers .drop x ->
  (hx : m.lookup x = some (.capability (.mcell b .live))) ->
  Step C m (.drop (.free x)) (m.drop_mcell x ⟨b, hx⟩) .unit
| step_ctx_letin :
  Step C m e1 m' e1' ->
  Step C m (.letin e1 e2) m' (.letin e1' e2)
| step_ctx_unpack :
  Step C m e1 m' e1' ->
  Step C m (.unpack e1 e2) m' (.unpack e1' e2)
| step_rename :
  Step C m (.letin (.var (.free y)) e) m (e.subst (Subst.openVar (.free y)))
| step_lift :
  (hv : Exp.IsSimpleVal v) ->
  (hwf : Exp.WfInHeap v m.heap) ->
  (hfresh : m.heap l = none) ->
  Step
    C
    m (.letin v e)
    (m.extend l ⟨v, hv, compute_reachability m.heap v hv⟩ hwf rfl hfresh)
    (e.subst (Subst.openVar (.free l)))
| step_unpack :
  Step C m (.unpack (.pack cs (.free x)) e) m (e.subst (Subst.unpack cs (.free x)))
| step_cond_true :
  resolve m.heap (.var x) = some .btrue ->
  Step C m (.cond x e1 e2) m e1
| step_cond_false :
  resolve m.heap (.var x) = some .bfalse ->
  Step C m (.cond x e1 e2) m e2

/-- Multi-step reduction relation: reflexive-transitive closure of Step.
  Reduce C m e m' e' means that e in memory m takes multiple steps to e' in memory m'
  using at most capabilities from C. -/
inductive Reduce : CapabilitySet -> Memory -> Exp {} -> Memory -> Exp {} -> Prop where
| refl :
  Reduce C m e m e
| step :
  Step C m1 e1 m2 e2 ->
  Reduce C m2 e2 m3 e3 ->
  Reduce C m1 e1 m3 e3

theorem reduce_trans
  (hred1 : Reduce C m1 e1 m2 e2)
  (hred2 : Reduce C m2 e2 m3 e3) :
  Reduce C m1 e1 m3 e3 := by
  induction hred1 with
  | refl => exact hred2
  | step h rest ih => exact Reduce.step h (ih hred2)

end Consume
