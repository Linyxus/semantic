import Semantic.Capybara.Syntax
import Semantic.Capybara.Substitution
import Semantic.Capybara.Semantics.Heap

namespace Capybara

/-- Small-step evaluation relation indexed by a capability set upper bound.
  Step C m e m' e' means that expression e in memory m steps to e' in memory m'
  using at most capabilities from C. -/
inductive Step : CapabilitySet -> Memory -> Exp {} -> Memory -> Exp {} -> Prop where
| step_apply :
  m.lookup x = some (.val ⟨.abs cs T e, hv, R⟩) ->
  Step C m (.app (.free x) (.free y)) m (e.subst (Subst.openVar (.free y)))
| step_invoke :
  C.covers .epsilon x ->
  m.lookup x = some (.capability .basic) ->
  m.lookup y = some (.val ⟨.unit, hv, R⟩) ->
  Step C m (.app (.free x) (.free y)) m .unit
| step_tapply :
  m.lookup x = some (.val ⟨.tabs cs S' e, hv, R⟩) ->
  Step C m (.tapp (.free x) S) m (e.subst (Subst.openTVar .top))
| step_capply :
  m.lookup x = some (.val ⟨.cabs cs B e, hv, R⟩) ->
  Step C m (.capp (.free x) CS) m (e.subst (Subst.openCVar CS))
| step_cond_var_true :
  m.lookup x = some (.val ⟨.btrue, hv, R⟩) ->
  Step C m (.cond (.free x) e1 e2) m e1
| step_cond_var_false :
  m.lookup x = some (.val ⟨.bfalse, hv, R⟩) ->
  Step C m (.cond (.free x) e1 e2) m e2
| step_read :
  C.covers .ro y ->
  m.lookup x = some (.val ⟨.reader (.free y), hv_reader, R_reader⟩) ->
  m.lookup y = some (.capability (.mcell b)) ->
  Step C m (.read (.free x)) m (if b then .btrue else .bfalse)
| step_write_true :
  C.covers .epsilon x ->
  (hx : m.lookup x = some (.capability (.mcell b0))) ->
  m.lookup y = some (.val ⟨.btrue, hv, R⟩) ->
  Step C m (.write (.free x) (.free y)) (m.update_mcell x true ⟨b0, hx⟩) .unit
| step_write_false :
  C.covers .epsilon x ->
  (hx : m.lookup x = some (.capability (.mcell b0))) ->
  m.lookup y = some (.val ⟨.bfalse, hv, R⟩) ->
  Step C m (.write (.free x) (.free y)) (m.update_mcell x false ⟨b0, hx⟩) .unit
| step_ctx_letin :
  Step C m e1 m' e1' ->
  Step C m (.letin e1 e2) m' (.letin e1' e2)
| step_ctx_unpack :
  Step C m e1 m' e1' ->
  Step C m (.unpack e1 e2) m' (.unpack e1' e2)
-- For now, let `par` pick a random branch to step
| step_par_left :
  Step C m (.par e1 e2) m e1
| step_par_right :
  Step C m (.par e1 e2) m e2
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

end Capybara
