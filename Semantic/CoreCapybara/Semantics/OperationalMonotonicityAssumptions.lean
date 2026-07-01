import Semantic.CoreCapybara.Semantics.BigStep

/-!
# Quarantined FALSE operational-monotonicity assumptions (Phase 7)

These three adapters are **genuinely false** for a faithful reference-valued `read`
(the cell stores a different location in `m1` vs `m2`, so a replayed run's value/trace
diverge — see the `Denotation/KripkeModel.lean` first-principles note: no `subsumes`
redefinition rescues it, because the type-erased memory cannot preserve cell types).

They were removed from `Fundamental.lean`'s import path by the Phase-6 rely–guarantee
`Safe.par` (branch behaviour is demanded only at rely-memories — semantically, at
*well-typed* future worlds — never at arbitrary subsuming memories).  They survive
here ONLY because the stale `Props`/`Standardization` adequacy proofs still consume
them; those developments are to be reworked on the budget-indexed, rely–guarantee
interface (see `roadmaps/generic-refs.md`, "Deferred After Fundamental"), at which
point this module is deleted.

Do NOT import this module from anything on `Fundamental.lean`'s path.
-/

namespace CoreCapybara

/-- **FALSE (operational monotonicity).**  Downward simulation: an `m2`-run replays
  from a smaller `m1 ⊑ m2` with the SAME trace.  False for faithful generic `read`. -/
theorem BigStep.simulate_down {m2 : Memory} {e : Exp {}} {t : Trace} {v : Exp {}}
    {m2' : Memory} (hbs : BigStep m2 e t v m2') :
    ∀ {m1 : Memory}, m2.subsumes m1 -> Exp.WfInHeap e m1.heap ->
      ∃ m1', BigStep m1 e t v m1' ∧ m2'.subsumes m1' ∧
        ∀ l, ((m1.IsLive l ↔ m2.IsLive l) ∨ Trace.allocd t l) ->
          (m1'.IsLive l ↔ m2'.IsLive l) := by
  sorry

/-- **FALSE (operational monotonicity).**  Safety lifts upward along subsumption.
  Same root as `simulate_down`. -/
theorem Safe.lift {k : Nat} {m1 m2 : Memory} {e : Exp {}} {Q : Tpost} (hsafe : Safe k m1 e)
    (hsub : m2.subsumes m1)
    (hpres : ∀ t v m', BigStep m1 e t v m' -> Q t v m')
    (hok : ∀ t v m, m.subsumes m1 -> Q t v m -> Memory.SubsumeOk m1 t m2)
    (hwf : Exp.WfInHeap e m1.heap) : Safe k m2 e := by
  sorry

/-- **FALSE (operational monotonicity).**  Branch-safety transports across a separated
  transition (the `Safe.lift` specialization the par-standardization uses). -/
theorem Safe.frame_lift {k : Nat} {ma ma' : Memory} {e : Exp {}} {B : CapabilitySet}
    (hse : Safe k ma e) (hsub : ma'.subsumes ma) (hwf : Exp.WfInHeap e ma.heap)
    (hbnd : ∀ {m' : Memory} {s : Trace} {v : Exp {}} {m''},
      m'.subsumes ma → Exp.WfInHeap e m'.heap → BigStep m' e s v m'' → TraceOk s B)
    (hlive : ∀ l b, (∃ mu, B.hasmem mu l) →
      ma.lookup l = some (.capability (.mcell b .live)) →
      ∃ b', ma'.lookup l = some (.capability (.mcell b' .live))) :
    Safe k ma' e := by
  sorry

end CoreCapybara
