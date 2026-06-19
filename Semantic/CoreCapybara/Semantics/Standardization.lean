import Semantic.CoreCapybara.Semantics.SmallStep

/-! # Standardization (theorem B): trace permutation & heap/memory isomorphism

  The standardization theorem relates the GENUINE interleaving `Step` to the
  SEQUENTIAL `SeqStep`: every `Step` run is equivalent to a `SeqStep` run, where
  "equivalent" means

  * its **trace** is a PERMUTATION of the sequential trace — an interleaving emits
    the same multiset of events as the left-then-right schedule, only reordered
    (Mazurkiewicz reordering of the two separated branches' events), and
  * its **final memory** is ISOMORPHIC to the sequential one — the two schedules may
    allocate fresh cells in different orders, so the final heaps agree up to a
    relabelling of (fresh) locations.

  This file defines those two equivalences (`Trace.Perm`, `Memory.Iso`).  The
  standardization theorem itself (`Step` run ⇒ ∃ `SeqReduce` run with `Trace.Perm`
  + `Memory.Iso`) is developed separately on top of the diamond
  `BigStep.step_run_commute`. -/

namespace CoreCapybara

/-! ## Trace permutation equivalence

  Two traces are equivalent when one is a reordering of the other — plain `List.Perm`.
  This is exactly the right notion: each branch, run in isolation, emits a fixed
  sequence of events; the interleaving SHUFFLES the two branches' events while the
  sequential schedule CONCATENATES them, and a shuffle of two lists is a permutation
  of their concatenation.  Using `List.Perm` gives us its whole API for free
  (it is an equivalence, and membership / multiplicity are invariant — which is all
  the immutability facts, being trace-membership facts, need). -/

/-- Rename the location mentioned by a single trace item along `σ`. -/
def TraceItem.renameLoc (σ : Nat → Nat) : TraceItem → TraceItem
| .access mu l => .access mu (σ l)
| .alloc l     => .alloc (σ l)
| .dealloc l   => .dealloc (σ l)

/-- Rename every location in a trace along `σ`.  Used in the combined standardization
  statement: when the two schedules allocate fresh cells under different names (a
  non-identity `σ` in the memory isomorphism below), the interleaving trace matches
  the sequential one only after renaming its locations by `σ` — i.e.
  `Trace.Perm (t.renameLoc σ) t'`.  When `σ = id` (matching allocation names) this is
  just `Trace.Perm t t'`. -/
def Trace.renameLoc (σ : Nat → Nat) (t : Trace) : Trace :=
  t.map (TraceItem.renameLoc σ)

/-- **Trace permutation equivalence.**  `t1` and `t2` record the same heap events up
  to reordering.  Defined as `List.Perm`, so the full `List.Perm` API applies. -/
def Trace.Perm (t1 t2 : Trace) : Prop := List.Perm t1 t2

namespace Trace.Perm

-- NB: `Trace.Perm` is a `def` for `List.Perm`, so dot-notation `h.symm` would resolve
-- to `Trace.Perm.symm` (self-recursion); we call the `List.Perm` lemmas explicitly.
theorem refl (t : Trace) : Trace.Perm t t := List.Perm.refl t

theorem symm {t1 t2 : Trace} (h : Trace.Perm t1 t2) : Trace.Perm t2 t1 :=
  List.Perm.symm h

theorem trans {t1 t2 t3 : Trace}
    (h1 : Trace.Perm t1 t2) (h2 : Trace.Perm t2 t3) : Trace.Perm t1 t3 :=
  List.Perm.trans h1 h2

/-- Membership is invariant under trace permutation — the transport principle the
  immutability facts (e.g. `access .epsilon l ∉ t`) ride on. -/
theorem mem_iff {t1 t2 : Trace} (h : Trace.Perm t1 t2) {it : TraceItem} :
    it ∈ t1 ↔ it ∈ t2 := List.Perm.mem_iff h

/-- A reordered interleaving of two branch-traces: `t1 ++ t2` (sequential) is a
  permutation of any interleaving.  Concretely, appending is permutation-commutative,
  the seed for relating `bs_par`'s `t1 ++ t2` to a shuffled `Step` trace. -/
theorem append_comm (t1 t2 : Trace) : Trace.Perm (t1 ++ t2) (t2 ++ t1) :=
  List.perm_append_comm

end Trace.Perm

/-! ## Heap / memory isomorphism

  Two heaps are isomorphic when a bijection `σ` on locations carries one onto the
  other: the cell at `l` in `h1` is the cell at `σ l` in `h2`.

  **This is the content-preserving form** — cell *contents* are carried unchanged, so
  it captures exactly a relabelling of ADDRESSES.  That is the right notion here:

  * Capability cells (`mcell`/`basic`, what `step_alloc` produces, and all platform
    cells) hold NO locations, so relabelling their addresses leaves contents correct.
  * In particular `σ = id` (the two schedules choose matching fresh names — which the
    diamond `BigStep.step_run_commute` preserves, since commuting a step past a
    separated run keeps the step's allocation name) collapses this to plain memory
    equality `m1 = m2`.

  **Design fork (flagged for audit).**  A value cell (`val ⟨e, _, R⟩`, produced by
  `step_lift`) embeds an `Exp {}` body and a reachability `CapabilitySet`, both of
  which may mention locations.  If the standardization ever RELABELS a location that
  such a body references, the faithful isomorphism would have to rename those embedded
  locations too — requiring a free-location renaming on the whole syntax
  (`Exp`/`Ty`/`CaptureSet`/…), which does not currently exist (the existing `.rename`
  is de-Bruijn-only and leaves `.free` untouched).  That apparatus (~100+ lines plus a
  lemma suite) is intentionally NOT built here: the content-preserving form above is
  expected to suffice (diamond ⇒ matching names ⇒ `σ = id`), and we escalate to the
  deep form only against a concrete obstruction. -/

/-- `Heap.IsoBy σ h1 h2`: the location bijection `σ` carries `h1` onto `h2` — the cell
  at `l` in `h1` sits at `σ l` in `h2` (contents unchanged). -/
def Heap.IsoBy (σ : Nat ≃ Nat) (h1 h2 : Heap) : Prop :=
  ∀ l, h2 (σ l) = h1 l

/-- Two heaps are isomorphic when some location bijection carries one onto the other. -/
def Heap.Iso (h1 h2 : Heap) : Prop := ∃ σ : Nat ≃ Nat, Heap.IsoBy σ h1 h2

/-- Two memories are isomorphic when their underlying heaps are. -/
def Memory.Iso (m1 m2 : Memory) : Prop := Heap.Iso m1.heap m2.heap

namespace Heap.Iso

theorem refl (h : Heap) : Heap.Iso h h := ⟨Equiv.refl Nat, fun _ => rfl⟩

theorem symm {h1 h2 : Heap} (hiso : Heap.Iso h1 h2) : Heap.Iso h2 h1 := by
  obtain ⟨σ, hσ⟩ := hiso
  refine ⟨σ.symm, fun l => ?_⟩
  have h := hσ (σ.symm l)
  rw [σ.apply_symm_apply] at h
  exact h.symm

theorem trans {h1 h2 h3 : Heap}
    (h12 : Heap.Iso h1 h2) (h23 : Heap.Iso h2 h3) : Heap.Iso h1 h3 := by
  obtain ⟨σ, hσ⟩ := h12
  obtain ⟨τ, hτ⟩ := h23
  refine ⟨σ.trans τ, fun l => ?_⟩
  simp only [Equiv.trans_apply]
  rw [hτ (σ l), hσ l]

end Heap.Iso

namespace Memory.Iso

theorem refl (m : Memory) : Memory.Iso m m := Heap.Iso.refl m.heap

theorem symm {m1 m2 : Memory} (h : Memory.Iso m1 m2) : Memory.Iso m2 m1 :=
  Heap.Iso.symm h

theorem trans {m1 m2 m3 : Memory}
    (h12 : Memory.Iso m1 m2) (h23 : Memory.Iso m2 m3) : Memory.Iso m1 m3 :=
  Heap.Iso.trans h12 h23

end Memory.Iso

end CoreCapybara
