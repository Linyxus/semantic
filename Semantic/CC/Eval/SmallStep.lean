import Semantic.CC.Syntax
import Semantic.CC.Substitution
import Semantic.CC.Eval.Heap

namespace CC

/-- Small-step evaluation relation indexed by a capability set.
  Step C h e h' e' means that expression e in heap h steps to e' in heap h',
  using capabilities in C. -/
inductive Step : CapabilitySet -> Heap -> Exp {} -> Heap -> Exp {} -> Prop where
| step_apply {h : Heap} {x y : Nat} {T : Ty .capt {}} {e : Exp ({},x)} :
  h x = some (.val ⟨.abs T e, .abs⟩) ->
  Step ∅ h (.app (.free x) (.free y)) h (e.subst (Subst.openVar (.free y)))
| step_invoke {h : Heap} {x y : Nat} :
  h x = some .capability ->
  h y = some (.val ⟨.unit, .unit⟩) ->
  Step {x} h (.app (.free x) (.free y)) h .unit
| step_tapply {h : Heap} {x : Nat} {S : Ty .shape {}} {S' : Ty .shape {}} {e : Exp ({},X)} :
  h x = some (.val ⟨.tabs S' e, .tabs⟩) ->
  Step ∅ h (.tapp (.free x) S) h (e.subst (Subst.openTVar .top))
| step_capply {h : Heap} {x : Nat} {CS : CaptureSet {}} {B : CaptureBound {}} {e : Exp ({},C)} :
  h x = some (.val ⟨.cabs B e, .cabs⟩) ->
  Step ∅ h (.capp (.free x) CS) h (e.subst (Subst.openCVar .empty))
| step_ctx_letin {h h' : Heap} {e1 e1' : Exp {}} {e2 : Exp ({},x)} {C : CapabilitySet} :
  Step C h e1 h' e1' ->
  Step C h (.letin e1 e2) h' (.letin e1' e2)
| step_ctx_unpack {h h' : Heap} {e1 e1' : Exp {}} {e2 : Exp ({},C,x)} {C : CapabilitySet} :
  Step C h e1 h' e1' ->
  Step C h (.unpack e1 e2) h' (.unpack e1' e2)
| step_rename {h : Heap} {y : Nat} {e : Exp ({},x)} :
  Step ∅ h (.letin (.var (.free y)) e) h (e.subst (Subst.openVar (.free y)))
| step_lift {h : Heap} {v : Exp {}} {e : Exp ({},x)} {l : Nat} :
  (hv : Exp.IsVal v) ->
  h l = none ->
  Step ∅ h (.letin v e) (h.extend l ⟨v, hv⟩) (e.subst (Subst.openVar (.free l)))
| step_unpack {h : Heap} {cs : CaptureSet {}} {x : Nat} {e : Exp ({},C,x)} :
  Step ∅ h (.unpack (.pack cs (.free x)) e) h (e.subst (Subst.unpack cs (.free x)))

end CC
