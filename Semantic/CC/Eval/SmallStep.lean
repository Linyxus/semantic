import Semantic.CC.Syntax
import Semantic.CC.Substitution
import Semantic.CC.Eval.Heap

namespace CC

/-- Small-step evaluation relation indexed by a capability set upper bound.
  Step C h e h' e' means that expression e in heap h steps to e' in heap h'
  using at most capabilities from C. -/
inductive Step : CapabilitySet -> Heap -> Exp {} -> Heap -> Exp {} -> Prop where
| step_apply {h : Heap} {x y : Nat} {T : Ty .capt {}} {e : Exp ({},x)} {C : CapabilitySet} :
  h x = some (.val ⟨.abs T e, .abs⟩) ->
  Step C h (.app (.free x) (.free y)) h (e.subst (Subst.openVar (.free y)))
| step_invoke {h : Heap} {x y : Nat} {C : CapabilitySet} :
  x ∈ C ->
  h x = some .capability ->
  h y = some (.val ⟨.unit, .unit⟩) ->
  Step C h (.app (.free x) (.free y)) h .unit
| step_tapply {h : Heap} {x : Nat} :
  h x = some (.val ⟨.tabs S' e, .tabs⟩) ->
  Step C h (.tapp (.free x) S) h (e.subst (Subst.openTVar .top))
| step_capply {h : Heap} {x : Nat} :
  h x = some (.val ⟨.cabs B e, .cabs⟩) ->
  Step C h (.capp (.free x) CS) h (e.subst (Subst.openCVar .empty))
| step_ctx_letin {h h' : Heap} {e1 e1' : Exp {}} {e2 : Exp ({},x)} {C : CapabilitySet} :
  Step C h e1 h' e1' ->
  Step C h (.letin e1 e2) h' (.letin e1' e2)
| step_ctx_unpack {h h' : Heap} {e1 e1' : Exp {}} {e2 : Exp ({},C,x)} {C : CapabilitySet} :
  Step C h e1 h' e1' ->
  Step C h (.unpack e1 e2) h' (.unpack e1' e2)
| step_rename {h : Heap} {y : Nat} {e : Exp ({},x)} {C : CapabilitySet} :
  Step C h (.letin (.var (.free y)) e) h (e.subst (Subst.openVar (.free y)))
| step_lift {h : Heap} {v : Exp {}} {e : Exp ({},x)} {l : Nat} {C : CapabilitySet} :
  (hv : Exp.IsVal v) ->
  h l = none ->
  Step C h (.letin v e) (h.extend l ⟨v, hv⟩) (e.subst (Subst.openVar (.free l)))
| step_unpack {h : Heap} {cs : CaptureSet {}} {x : Nat} {e : Exp ({},C,x)} {C : CapabilitySet} :
  Step C h (.unpack (.pack cs (.free x)) e) h (e.subst (Subst.unpack cs (.free x)))

/-- Multi-step reduction relation: reflexive-transitive closure of Step.
  Reduce C h e h' e' means that e in heap h reduces to e' in heap h'
  using at most capabilities from C. -/
inductive Reduce : CapabilitySet -> Heap -> Exp {} -> Heap -> Exp {} -> Prop where
| refl {h : Heap} {e : Exp {}} {C : CapabilitySet} :
  Reduce C h e h e
| single {h h' : Heap} {e e' : Exp {}} {C : CapabilitySet} :
  Step C h e h' e' ->
  Reduce C h e h' e'
| trans {h1 h2 h3 : Heap} {e1 e2 e3 : Exp {}} {C1 C2 : CapabilitySet} :
  Reduce C h1 e1 h2 e2 ->
  Reduce C h2 e2 h3 e3 ->
  Reduce C h1 e1 h3 e3

end CC
