import Semantic.CoreCapybara.Semantics.Standardization
import Semantic.CoreCapybara.Semantics.Equivariance

/-! # Church–Rosser / confluence up to location-iso (for partial reductions)

  The generalization of `standardization` from runs-to-answers to ARBITRARY partial
  reductions.  Two genuine interleaving reductions out of the same configuration can
  always be brought back together.

  Design points (for audit):

  * **Up to a location renaming `π : Equiv.Perm Nat`.**  Confluence is only provable
    up to a location bijection: `step_alloc` chooses fresh names freely, so two runs
    diverge already at a single `alloc` (memory AND expression differ, only iso-equal).
    `π` is exposed explicitly (rather than hidden behind `Memory.Iso`/`ConfigIso`) so the
    same `π` ties together the memory agreement, the expression agreement, and the trace
    equivalence.  Taking `π = Equiv.refl` is the special case where both runs happen to
    pick the same fresh names.

  * **Up to `Trace.Equiv` (Mazurkiewicz).**  The two paths' combined traces agree only
    after renaming one by `π` and quotienting by independent-event reordering — i.e.
    `Trace.Equiv ((t1 ++ s1).renameLoc π) (t2 ++ s2)`.  This is the observable content of
    data-race freedom: scheduling is unobservable.

  * **Separation precondition `Safe m e`.**  Separation is exactly what rules out data
    races and makes `par` confluent: two `par` branches writing the same cell would NOT
    be confluent, but such a program is not `Safe` (it fails `SepCheck`).  `Exp.WfInHeap`
    is the usual well-formedness premise.  These mirror `standardization`'s preconditions.

  Intended proof route: a local diamond (resolve the `alloc` name-clash by renaming one
  side via `Equiv.swap`, using the operational `*.renameLoc` equivariance from
  `Equivariance.lean`), lifted to runs by a strip lemma on top of the proven separation
  diamond `BigStep.step_run_commute`.

  Headline corollary (DRF / determinacy, to state separately): every interleaving run of
  a safe program to an answer reaches the SAME answer and memory up to `π`, with trace
  pinned down only up to `Trace.Equiv` — schedule-determinism. -/

namespace CoreCapybara

/-- **Confluence (Church–Rosser) up to `Trace.Equiv` and a location renaming.**
  From a safe, well-formed configuration `(m, e)`, any two interleaving reductions
  `Reduce t1 m e m1 e1` and `Reduce t2 m e m2 e2` have continuations `s1`, `s2` to a
  common reduct that agrees up to a single location renaming `π` on both memory and
  expression, and whose combined external traces agree (Mazurkiewicz `Trace.Equiv`)
  after renaming by `π`. -/
theorem confluence {m m1 m2 : Memory} {e e1 e2 : Exp {}} {t1 t2 : Trace}
    (hwf : Exp.WfInHeap e m.heap) (hsafe : Safe m e)
    (hr1 : Reduce t1 m e m1 e1) (hr2 : Reduce t2 m e m2 e2) :
    ∃ (s1 s2 : Trace) (mf1 mf2 : Memory) (ef1 ef2 : Exp {}) (π : Equiv.Perm Nat),
      Reduce s1 m1 e1 mf1 ef1 ∧
      Reduce s2 m2 e2 mf2 ef2 ∧
      mf2 = mf1.renameLoc π ∧
      ef2 = ef1.renameLoc π ∧
      Trace.Equiv ((t1 ++ s1).renameLoc π) (t2 ++ s2) := by
  sorry

end CoreCapybara
