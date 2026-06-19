import Semantic.CoreCapybara.Semantics.Props

/-! # Standardization (theorem B): trace equivalence & heap/memory isomorphism

  The standardization theorem relates the GENUINE interleaving `Step` to the
  SEQUENTIAL `SeqStep`: every `Step` run is equivalent to a `SeqStep` run, where
  "equivalent" means

  * its **trace** is `Trace.Equiv` to the sequential trace — the two record the same
    EXTERNAL access/drop *sequence* at every location (Mazurkiewicz trace equivalence
    with locations as independent objects: independent touches commute, same-location
    order is preserved).  Restricting to *external* touches makes it robust to
    fresh-cell renaming (a self-allocated cell is private, never externally touched),
    so trace equivalence needs no location bijection — it is orthogonal to the heap
    isomorphism below.
  * its **final memory** is `Memory.Iso` to the sequential one — the two schedules may
    allocate fresh cells in different orders, so the final heaps agree up to a
    relabelling of (fresh) locations.

  This file defines those two equivalences (`Trace.Equiv`, `Memory.Iso`).  The
  standardization theorem itself (`Step` run ⇒ ∃ `SeqReduce` run with `Trace.Equiv`
  + `Memory.Iso`) is developed separately on top of the diamond
  `BigStep.step_run_commute`. -/

namespace CoreCapybara

/-! ## Trace equivalence

  Two traces are equivalent when, at EVERY location, they record the same external
  access/drop *sequence* — the mode-carrying, order-preserving refinement of the
  existing `Trace.extTouchesFromMode` (existence) / `Trace.Noninterfere`.  This is
  Mazurkiewicz trace equivalence: touches to *different* locations are independent
  (commute), touches to the *same* location keep their order.

  Restricting to *external* touches (a self-allocated cell — its index in the running
  set `A` — is private and contributes nothing) makes the relation robust to
  fresh-cell renaming, so it carries no location bijection and is orthogonal to
  `Memory.Iso`.  It still transports the immutability facts: for an external (e.g.
  platform) cell `l`, `.access .epsilon ∈ extSeq l t ↔ access .epsilon l ∈ t`. -/

/-- The external access/drop **sequence** to `l` in `t`, given the running set `A` of
  locations already allocated within `t`.  Each external read/write contributes its
  `.access mu` mode and each external drop a `.drop`, in order; an `alloc` extends `A`
  (so a self-allocated cell is thereafter internal).  This is the order-recording
  refinement of `Trace.extTouchesFromMode`. -/
def Trace.extSeqFrom (A : List Nat) (l : Nat) : Trace → List CapMode
| []                   => []
| (.alloc l' :: t)     => Trace.extSeqFrom (l' :: A) l t
| (.access mu l' :: t) =>
    if l = l' ∧ l ∉ A then .access mu :: Trace.extSeqFrom A l t
    else Trace.extSeqFrom A l t
| (.dealloc l' :: t)   =>
    if l = l' ∧ l ∉ A then .drop :: Trace.extSeqFrom A l t
    else Trace.extSeqFrom A l t

/-- The external access/drop sequence to `l` in a whole trace (nothing allocated yet). -/
def Trace.extSeq (l : Nat) (t : Trace) : List CapMode := Trace.extSeqFrom [] l t

/-- **Trace equivalence.**  `t1` and `t2` have the same external access/drop sequence
  at every location.  An equivalence relation (it is per-location equality of
  sequences), and it subsumes "same external (location, mode) touch set". -/
def Trace.Equiv (t1 t2 : Trace) : Prop := ∀ l, Trace.extSeq l t1 = Trace.extSeq l t2

namespace Trace.Equiv

theorem refl (t : Trace) : Trace.Equiv t t := fun _ => rfl

theorem symm {t1 t2 : Trace} (h : Trace.Equiv t1 t2) : Trace.Equiv t2 t1 :=
  fun l => (h l).symm

theorem trans {t1 t2 t3 : Trace}
    (h1 : Trace.Equiv t1 t2) (h2 : Trace.Equiv t2 t3) : Trace.Equiv t1 t3 :=
  fun l => (h1 l).trans (h2 l)

end Trace.Equiv

/-- **Bridge to the existence-level external touch.**  A mode `cm` appears in the
  external sequence to `l` exactly when `l` is externally touched with mode `cm` —
  connecting `Trace.Equiv` to the existing `Trace.extTouchesFromMode`/`Noninterfere`
  machinery. -/
theorem Trace.mem_extSeqFrom_iff {A : List Nat} {l : Nat} {cm : CapMode} {t : Trace} :
    cm ∈ Trace.extSeqFrom A l t ↔ Trace.extTouchesFromMode A l cm t := by
  induction t generalizing A with
  | nil => simp [Trace.extSeqFrom, Trace.extTouchesFromMode]
  | cons it t ih =>
    cases it with
    | alloc l' =>
      simp only [Trace.extSeqFrom, Trace.extTouchesFromMode]; exact ih
    | access mu l' =>
      simp only [Trace.extSeqFrom, Trace.extTouchesFromMode]
      split
      · rename_i hcond
        simp only [List.mem_cons, ih]
        constructor
        · rintro (rfl | h)
          · exact Or.inl ⟨hcond.1, hcond.2, rfl⟩
          · exact Or.inr h
        · rintro (⟨_, _, rfl⟩ | h)
          · exact Or.inl rfl
          · exact Or.inr h
      · rename_i hcond
        rw [ih]
        constructor
        · exact Or.inr
        · rintro (⟨h1, h2, _⟩ | h)
          · exact absurd ⟨h1, h2⟩ hcond
          · exact h
    | dealloc l' =>
      simp only [Trace.extSeqFrom, Trace.extTouchesFromMode]
      split
      · rename_i hcond
        simp only [List.mem_cons, ih]
        constructor
        · rintro (rfl | h)
          · exact Or.inl ⟨hcond.1, hcond.2, rfl⟩
          · exact Or.inr h
        · rintro (⟨_, _, rfl⟩ | h)
          · exact Or.inl rfl
          · exact Or.inr h
      · rename_i hcond
        rw [ih]
        constructor
        · exact Or.inr
        · rintro (⟨h1, h2, _⟩ | h)
          · exact absurd ⟨h1, h2⟩ hcond
          · exact h

/-- Equivalent traces externally touch every location with the same modes — the
  transport principle the immutability facts (e.g. `access .epsilon l ∉ t`) ride on. -/
theorem Trace.Equiv.extTouchesMode_iff {t1 t2 : Trace} (h : Trace.Equiv t1 t2)
    {l : Nat} {cm : CapMode} :
    Trace.extTouchesMode t1 l cm ↔ Trace.extTouchesMode t2 l cm := by
  unfold Trace.extTouchesMode
  rw [← Trace.mem_extSeqFrom_iff, ← Trace.mem_extSeqFrom_iff,
      show Trace.extSeqFrom [] l t1 = Trace.extSeqFrom [] l t2 from h l]

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
