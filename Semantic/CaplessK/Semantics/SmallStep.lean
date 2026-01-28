import Semantic.CaplessK.Syntax
import Semantic.CaplessK.Substitution
import Semantic.CaplessK.Semantics.Heap

namespace CaplessK

/-- Small-step evaluation relation indexed by a precise capability set.
  Step C m e m' e' means that expression e in memory m steps to e' in memory m'
  using exactly the capabilities in C. -/
inductive Step : CapabilitySet -> Memory -> Exp {} -> Memory -> Exp {} -> Prop where
| step_apply :
  m.lookup x = some (.val ⟨.abs cs T e, hv, R⟩) ->
  Step {} m (.app (.free x) (.free y)) m (e.subst (Subst.openVar (.free y)))
| step_invoke :
  m.lookup x = some (.capability .basic) ->
  m.lookup y = some (.val ⟨.unit, hv, R⟩) ->
  Step (.cap x) m (.app (.free x) (.free y)) m .unit
| step_tapply :
  m.lookup x = some (.val ⟨.tabs cs S' e, hv, R⟩) ->
  Step {} m (.tapp (.free x) S) m (e.subst (Subst.openTVar .top))
| step_capply :
  m.lookup x = some (.val ⟨.cabs cs B e, hv, R⟩) ->
  Step {} m (.capp (.free x) CS) m (e.subst (Subst.openCVar CS))
| step_cond_var_true :
  m.lookup x = some (.val ⟨.btrue, hv, R⟩) ->
  Step {} m (.cond (.free x) e1 e2) m e1
| step_cond_var_false :
  m.lookup x = some (.val ⟨.bfalse, hv, R⟩) ->
  Step {} m (.cond (.free x) e1 e2) m e2
| step_read :
  m.lookup x = some (.capability (.mcell b)) ->
  Step (.cap x) m (.read (.free x)) m (if b then .btrue else .bfalse)
| step_write_true :
  (hx : m.lookup x = some (.capability (.mcell b0))) ->
  m.lookup y = some (.val ⟨.btrue, hv, R⟩) ->
  Step (.cap x) m (.write (.free x) (.free y)) (m.update_mcell x true ⟨b0, hx⟩) .unit
| step_write_false :
  (hx : m.lookup x = some (.capability (.mcell b0))) ->
  m.lookup y = some (.val ⟨.bfalse, hv, R⟩) ->
  Step (.cap x) m (.write (.free x) (.free y)) (m.update_mcell x false ⟨b0, hx⟩) .unit
| step_ctx_letin :
  Step C m e1 m' e1' ->
  Step C m (.letin e1 e2) m' (.letin e1' e2)
| step_ctx_unpack :
  Step C m e1 m' e1' ->
  Step C m (.unpack e1 e2) m' (.unpack e1' e2)
| step_rename :
  Step {} m (.letin (.var (.free y)) e) m (e.subst (Subst.openVar (.free y)))
| step_lift :
  (hv : Exp.IsSimpleVal v) ->
  (hwf : Exp.WfInHeap v m.heap) ->
  (hfresh : m.heap l = none) ->
  Step
    {}
    m (.letin v e)
    (m.extend l ⟨v, hv, compute_reachability m.heap v hv⟩ hwf rfl
      (compute_reachability_locations_exist m.wf hwf) hfresh)
    (e.subst (Subst.openVar (.free l)))
| step_unpack :
  Step {} m (.unpack (.pack cs (.free x)) e) m (e.subst (Subst.unpack cs (.free x)))

/-- Multi-step reduction relation: reflexive-transitive closure of Step.
  Reduce C m e m' e' means that e in memory m takes multiple steps to e' in memory m'
  using exactly the capabilities in C (union of all step capabilities).

  Note: The capability set is precise - it's exactly what was used.
  Due to union not being definitionally associative, we define an equivalence-respecting
  version of transitivity. -/
inductive Reduce : CapabilitySet -> Memory -> Exp {} -> Memory -> Exp {} -> Prop where
| refl :
  Reduce {} m e m e
| step :
  Step C1 m1 e1 m2 e2 ->
  Reduce C2 m2 e2 m3 e3 ->
  Reduce (C1 ∪ C2) m1 e1 m3 e3

-- Transitivity: the result capability set is equivalent to C1 ∪ C2
-- but may not be syntactically equal
theorem reduce_trans
  (hred1 : Reduce C1 m1 e1 m2 e2)
  (hred2 : Reduce C2 m2 e2 m3 e3) :
  ∃ C, C.equiv (C1 ∪ C2) ∧ Reduce C m1 e1 m3 e3 := by
  induction hred1 with
  | refl =>
    -- C1 = {}, need C equiv ({} ∪ C2) and Reduce C m e m3 e3
    exact ⟨C2, CapabilitySet.equiv_symm CapabilitySet.empty_union_equiv, hred2⟩
  | step hstep rest ih =>
    -- C1 = C1_step ∪ C1_rest
    -- ih : ∃ C, C.equiv (C1_rest ∪ C2) ∧ Reduce C m_mid e_mid m3 e3
    obtain ⟨C_rest, heq_rest, hred_rest⟩ := ih hred2
    -- Build: Reduce (C1_step ∪ C_rest) m1 e1 m3 e3
    refine ⟨_, ?_, Reduce.step hstep hred_rest⟩
    -- Need: (C1_step ∪ C_rest).equiv ((C1_step ∪ C1_rest) ∪ C2)
    intro x
    constructor
    · intro hmem
      cases hmem with
      | left h1 => exact CapabilitySet.mem.left (CapabilitySet.mem.left h1)
      | right hr =>
        have hx_in := (heq_rest x).mp hr
        cases hx_in with
        | left h1rest => exact CapabilitySet.mem.left (CapabilitySet.mem.right h1rest)
        | right h2 => exact CapabilitySet.mem.right h2
    · intro hmem
      cases hmem with
      | left h1 =>
        cases h1 with
        | left h1step => exact CapabilitySet.mem.left h1step
        | right h1rest =>
          have h := (heq_rest x).mpr (CapabilitySet.mem.left h1rest)
          exact CapabilitySet.mem.right h
      | right h2 =>
        have h := (heq_rest x).mpr (CapabilitySet.mem.right h2)
        exact CapabilitySet.mem.right h

end CaplessK
