import Semantic.CoreCapybara.Semantics.Props

/-! # Standardization (theorem B)

  The standardization theorem relates the GENUINE interleaving `Step` to the
  SEQUENTIAL `SeqStep`: every interleaving run to an answer is matched by a sequential
  run reaching the **identical** final memory and answer, the only difference being a
  reordering of the trace.

  Why equality (not an isomorphism) of the final memory/answer: the local diamond
  `BigStep.step_run_commute` has an EXACT meet — commuting a step past a separated run
  reaches the *same* memory and keeps each step's chosen fresh-allocation name (its
  trace `[.alloc l]` is preserved verbatim).  So this is a confluence situation:
  separated `par` ⇒ unique normal form ⇒ every schedule of a given run reaches the
  same `(mf, a)`.  Only the trace genuinely differs, and only up to `Trace.Equiv`:

  * `Trace.Equiv` — the two traces record the same EXTERNAL access/drop *sequence* at
    every location (Mazurkiewicz trace equivalence with locations as independent
    objects: independent touches commute, same-location order is preserved).
    Restricting to *external* touches makes it robust to the differing internal
    allocation ORDER (a self-allocated cell is private, never externally touched).

  This file defines `Trace.Equiv` and states `standardization` (proof on top of the
  diamond `BigStep.step_run_commute`, fed by the separation carrier `Safe` via
  `Safe.par_noninterfere`). -/

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

/-! ### Projection algebra

  `extSeqFrom A l t` reads the alloc-set `A` only through `l`'s own membership (the
  sole place `A` is consulted is the `l ∉ A` guard), and a cell already in `A` is
  internal forever — these two facts give the decomposition over `++` that the
  `Trace.Equiv` reasoning is built on. -/

/-- `extSeqFrom` consults `A` only through `l`'s membership. -/
theorem Trace.extSeqFrom_mem_self {A1 A2 : List Nat} {l : Nat} {t : Trace}
    (h : l ∈ A1 ↔ l ∈ A2) :
    Trace.extSeqFrom A1 l t = Trace.extSeqFrom A2 l t := by
  induction t generalizing A1 A2 with
  | nil => rfl
  | cons it t ih =>
    cases it with
    | alloc l' =>
      simp only [Trace.extSeqFrom]
      exact ih (by simp only [List.mem_cons, h])
    | access mu l' =>
      simp only [Trace.extSeqFrom]
      have hc : (l = l' ∧ l ∉ A1) ↔ (l = l' ∧ l ∉ A2) := by rw [h]
      by_cases hcond : l = l' ∧ l ∉ A1
      · rw [if_pos hcond, if_pos (hc.mp hcond), ih h]
      · rw [if_neg hcond, if_neg (fun h2 => hcond (hc.mpr h2)), ih h]
    | dealloc l' =>
      simp only [Trace.extSeqFrom]
      have hc : (l = l' ∧ l ∉ A1) ↔ (l = l' ∧ l ∉ A2) := by rw [h]
      by_cases hcond : l = l' ∧ l ∉ A1
      · rw [if_pos hcond, if_pos (hc.mp hcond), ih h]
      · rw [if_neg hcond, if_neg (fun h2 => hcond (hc.mpr h2)), ih h]

/-- A cell already in the alloc-set is internal: it contributes nothing. -/
theorem Trace.extSeqFrom_eq_nil {A : List Nat} {l : Nat} {t : Trace} (hl : l ∈ A) :
    Trace.extSeqFrom A l t = [] := by
  induction t generalizing A with
  | nil => rfl
  | cons it t ih =>
    cases it with
    | alloc l' => simp only [Trace.extSeqFrom]; exact ih (List.mem_cons_of_mem _ hl)
    | access mu l' =>
      simp only [Trace.extSeqFrom, if_neg (show ¬(l = l' ∧ l ∉ A) from fun h => h.2 hl)]
      exact ih hl
    | dealloc l' =>
      simp only [Trace.extSeqFrom, if_neg (show ¬(l = l' ∧ l ∉ A) from fun h => h.2 hl)]
      exact ih hl

/-- The alloc-set acts as an all-or-nothing gate on `l`. -/
theorem Trace.extSeqFrom_eq_ite {A : List Nat} {l : Nat} {t : Trace} :
    Trace.extSeqFrom A l t = if l ∈ A then [] else Trace.extSeqFrom [] l t := by
  by_cases hl : l ∈ A
  · rw [if_pos hl, Trace.extSeqFrom_eq_nil hl]
  · rw [if_neg hl]
    exact Trace.extSeqFrom_mem_self (iff_of_false hl (by simp))

/-- Decomposition of the external sequence over trace concatenation: process `t1`,
  then `t2` with `t1`'s allocations added to the exempt set. -/
theorem Trace.extSeqFrom_append {A : List Nat} {l : Nat} {t1 t2 : Trace} :
    Trace.extSeqFrom A l (t1 ++ t2)
      = Trace.extSeqFrom A l t1 ++ Trace.extSeqFrom (Trace.allocList t1 ++ A) l t2 := by
  induction t1 generalizing A with
  | nil => rfl
  | cons it t1 ih =>
    cases it with
    | alloc l' =>
      simp only [List.cons_append, Trace.extSeqFrom, Trace.allocList, ih]
      congr 1
      exact Trace.extSeqFrom_mem_self (by simp only [List.mem_append, List.mem_cons]; tauto)
    | access mu l' =>
      by_cases hcond : l = l' ∧ l ∉ A
      · simp only [List.cons_append, Trace.extSeqFrom, Trace.allocList, if_pos hcond, ih,
          List.cons_append]
      · simp only [List.cons_append, Trace.extSeqFrom, Trace.allocList, if_neg hcond, ih]
    | dealloc l' =>
      by_cases hcond : l = l' ∧ l ∉ A
      · simp only [List.cons_append, Trace.extSeqFrom, Trace.allocList, if_pos hcond, ih,
          List.cons_append]
      · simp only [List.cons_append, Trace.extSeqFrom, Trace.allocList, if_neg hcond, ih]

/-- Two lists whose every element equals `c` commute under append (both are the same
  `replicate`). -/
theorem List.append_comm_of_const {α} {L1 L2 : List α} {c : α}
    (h1 : ∀ x ∈ L1, x = c) (h2 : ∀ x ∈ L2, x = c) : L1 ++ L2 = L2 ++ L1 := by
  have key : ∀ (M N : List α), (∀ x ∈ M, x = c) → (∀ x ∈ N, x = c) →
      M ++ N = List.replicate (M.length + N.length) c := by
    intro M N hM hN
    rw [List.eq_replicate_iff]
    refine ⟨by rw [List.length_append], fun x hx => ?_⟩
    rcases List.mem_append.mp hx with h | h
    · exact hM x h
    · exact hN x h
  rw [key L1 L2 h1 h2, key L2 L1 h2 h1, Nat.add_comm]

/-- **Commutation of separated traces.**  Two traces that do not interfere
  (`Noninterfere`) and whose allocations are disjoint from each other's external
  touches (the operational freshness — a branch's fresh cells are not pre-existing for
  the other) are `Trace.Equiv` when concatenated in either order.  This is the trace
  heart of the diamond: a shared external touch is `.ro` on both sides (so the merged
  per-location sequence is a run of identical `.ro`'s, order-free), and a freshly
  allocated cell is private (its sequence is empty on the other side). -/
theorem Trace.equiv_comm_of_noninterfere {t s : Trace}
    (hni : Trace.Noninterfere t s)
    (hf1 : ∀ l, Trace.allocd s l → Trace.extSeqFrom [] l t = [])
    (hf2 : ∀ l, Trace.allocd t l → Trace.extSeqFrom [] l s = []) :
    Trace.Equiv (t ++ s) (s ++ t) := by
  intro l
  change Trace.extSeqFrom [] l (t ++ s) = Trace.extSeqFrom [] l (s ++ t)
  rw [Trace.extSeqFrom_append, Trace.extSeqFrom_append, List.append_nil, List.append_nil,
      Trace.extSeqFrom_eq_ite (A := Trace.allocList t),
      Trace.extSeqFrom_eq_ite (A := Trace.allocList s)]
  by_cases hat : l ∈ Trace.allocList t
  · rw [if_pos hat, hf2 l (Trace.mem_allocList.mp hat)]
    by_cases has : l ∈ Trace.allocList s
    · rw [if_pos has, hf1 l (Trace.mem_allocList.mp has)]
    · rw [if_neg has]; simp
  · rw [if_neg hat]
    by_cases has : l ∈ Trace.allocList s
    · rw [if_pos has, hf1 l (Trace.mem_allocList.mp has)]; simp
    · rw [if_neg has]
      by_cases hP : Trace.extSeqFrom [] l t = []
      · rw [hP]; simp
      · by_cases hQ : Trace.extSeqFrom [] l s = []
        · rw [hQ]; simp
        · obtain ⟨cm2, hcm2⟩ := List.exists_mem_of_ne_nil _ hQ
          have hes2 : Trace.extTouchesMode s l cm2 := Trace.mem_extSeqFrom_iff.mp hcm2
          obtain ⟨cm1, hcm1⟩ := List.exists_mem_of_ne_nil _ hP
          have hes1 : Trace.extTouchesMode t l cm1 := Trace.mem_extSeqFrom_iff.mp hcm1
          refine List.append_comm_of_const (c := CapMode.access .ro)
            (fun x hx => ?_) (fun x hx => ?_)
          · exact (hni l x cm2 (Trace.mem_extSeqFrom_iff.mp hx) hes2).1
          · exact (hni l cm1 x hes1 (Trace.mem_extSeqFrom_iff.mp hx)).2

/-! ## The separation carrier and the standardization theorem

  The runtime separation invariant is `Safe` itself (plus `WfInHeap`): each `Safe.par`
  node bundles the robust budget bounds `hb1`/`hb2` and `Noninterference` `hni`, which
  compose — via `traceOk_noninterfere` — into `Trace.Noninterfere` between any two
  branch runs (`Safe.par_noninterfere`).  This non-interference is the fuel for
  reordering separated steps; it is what the platform supplies (the fundamental theorem
  hands us `Safe`). -/

/-- **Separation of branch runs.**  From `Safe.par`, any two runs of the two branches —
  from any memories `⊒` the par node's `m` — have non-interfering traces. -/
theorem Safe.par_noninterfere {m m1 m2 m1' m2' : Memory}
    {Cs1 Cs2 : CaptureSet {}} {e1 e2 v1 v2 : Exp {}}
    {t1 t2 : Trace}
    (hsafe : Safe m (.par Cs1 Cs2 e1 e2))
    (hr1 : BigStep m1 e1 t1 v1 m1') (hsub1 : m1.subsumes m) (hwf1 : Exp.WfInHeap e1 m1.heap)
    (hr2 : BigStep m2 e2 t2 v2 m2') (hsub2 : m2.subsumes m) (hwf2 : Exp.WfInHeap e2 m2.heap) :
    Trace.Noninterfere t1 t2 := by
  cases hsafe with
  | par _ _ hb1 hb2 _ _ _ _ _ _ hni =>
      exact traceOk_noninterfere (hb1 hsub1 hwf1 hr1) (hb2 hsub2 hwf2 hr2) hni
  | ans hans => cases hans with | is_val hv => cases hv

/-! ## `SeqReduce ⊆ Reduce` — the guard-discharge direction

  A sequential reduction of a `Safe` configuration lifts to a genuine-interleaving
  `Reduce`: a fold of the single-step lift `SeqStep.toStep`, threaded by
  `step_preserves_safe`/`step_preserves_wf`.  The non-structural content is at the `par`
  nodes, where the lift discharges `Step`'s `par`-rule guards (`step_par_{left,right}_lift`):
  each branch step's trace is bounded by the branch's annotation reachability, and the two
  branches' reachabilities are non-interfering. -/

/-- **Discharging the interleaving `par` guards from `Safe` (left branch).**

  At a `par` node, `SeqStep.toStep` turns a branch step `Step t m e1 m' e1'` into a
  *guarded* interleaving step, growing the annotation to `C1.growByAllocs t`.  The two
  guards `Step.step_par_left` demands — `ht : TraceOk t (C1.reachability m)` and
  `hni : Noninterference (C1.reachability m) (C2.reachability m)` — are discharged from the
  `Safe.par` carrier:

  * `hni` follows from the carrier's `Noninterference C1ᵇ C2ᵇ` by DOWNWARD CLOSURE
    (`Noninterference.subset_left`), using the link `hcov` (`Cᵢ.reachability m ⊆ Cᵢᵇ`).

  * `ht` follows by RUN EXTENSION: the reduct `e1'` is `Safe` (preservation), hence has a
    `BigStep` run (`Safe.has_answer`); head-expanding the step onto it gives a full run of
    `e1`, bounded by `C1ᵇ` via the carrier's `hb1`; `TraceOk.prefix` restricts to the
    step's trace `t`, and `TraceOk.mono` with the link `hcov.1` (`C1ᵇ ⊆ C1.reachability m`)
    re-bases it to the annotation's reachability.

  The annotation `C1` grows by `growByAllocs` in lockstep with the carrier budget `C1ᵇ`
  (by `capsOf`), so a branch's own freshly-allocated cells join its reachability; the link
  `hcov` keeps the two in sync (`Safe.hcov_step`). -/
theorem step_par_left_lift {t : Trace} {m m' : Memory} {C1 C2 : CaptureSet {}}
    {e1 e2 e1' : Exp {}}
    (hsafe : Safe m (.par C1 C2 e1 e2))
    (hwf : Exp.WfInHeap (.par C1 C2 e1 e2) m.heap)
    (hstep : SeqStep t m e1 m' e1')
    (hbranch : Step t m e1 m' e1') :
    Step t m (.par C1 C2 e1 e2) m' (.par (C1.growByAllocs t) C2 e1' e2) := by
  obtain ⟨hwf_e1, _⟩ := Exp.wf_inv_par hwf
  cases hsafe with
  | ans hans => cases hans with | is_val hv => cases hv
  | par hse_a h2 hb1 hb2 hrs1 hrs2 hpres1 hpres2 hcov1 hcov2 hni =>
    have hsafe1' : Safe m' e1' := step_preserves_safe hstep hwf_e1 hse_a
    obtain ⟨s, v, m'', hrun'⟩ := hsafe1'.has_answer
    have hfull : BigStep m e1 (t ++ s) v m'' := BigStep.head_expand hstep hrun'
    have htok : TraceOk (t ++ s) _ := hb1 (Memory.subsumes_refl _) hwf_e1 hfull
    have ht : TraceOk t (C1.reachability m) := TraceOk.mono hcov1.1 (TraceOk.prefix htok)
    have hni' : CapabilitySet.Noninterference (C1.reachability m) (C2.reachability m) :=
      (((hni.subset_left hcov1.2).ni_symm).subset_left hcov2.2).ni_symm
    exact Step.step_par_left hbranch ht hni'

/-- Right-branch companion of `step_par_left_lift` (right branch steps, left frozen as an
  answer; the right annotation `C2` grows).  Same discharge as the left case. -/
theorem step_par_right_lift {t : Trace} {m m' : Memory} {C1 C2 : CaptureSet {}}
    {e1 e2 e2' : Exp {}}
    (hsafe : Safe m (.par C1 C2 e1 e2))
    (hwf : Exp.WfInHeap (.par C1 C2 e1 e2) m.heap)
    (hans : e1.IsAns)
    (hstep : SeqStep t m e2 m' e2')
    (hbranch : Step t m e2 m' e2') :
    Step t m (.par C1 C2 e1 e2) m' (.par C1 (C2.growByAllocs t) e1 e2') := by
  obtain ⟨_, hwf_e2⟩ := Exp.wf_inv_par hwf
  cases hsafe with
  | ans hans' => cases hans' with | is_val hv => cases hv
  | par hse_a h2 hb1 hb2 hrs1 hrs2 hpres1 hpres2 hcov1 hcov2 hni =>
    have hse_e2 : Safe m e2 := h2 (BigStep.of_isAns hans)
    have hsafe2' : Safe m' e2' := step_preserves_safe hstep hwf_e2 hse_e2
    obtain ⟨s, v, m'', hrun'⟩ := hsafe2'.has_answer
    have hfull : BigStep m e2 (t ++ s) v m'' := BigStep.head_expand hstep hrun'
    have htok : TraceOk (t ++ s) _ := hb2 (Memory.subsumes_refl _) hwf_e2 hfull
    have ht : TraceOk t (C2.reachability m) := TraceOk.mono hcov2.1 (TraceOk.prefix htok)
    have hni' : CapabilitySet.Noninterference (C1.reachability m) (C2.reachability m) :=
      (((hni.subset_left hcov1.2).ni_symm).subset_left hcov2.2).ni_symm
    exact Step.step_par_right ht hni' hbranch

/-- The left branch of a `Safe` `par` node is safe. -/
theorem Safe.par_inv_left {m : Memory} {C1 C2 : CaptureSet {}} {e1 e2 : Exp {}}
    (h : Safe m (.par C1 C2 e1 e2)) : Safe m e1 := by
  cases h with
  | par hsa _ _ _ _ _ _ _ _ _ _ => exact hsa
  | ans hans => cases hans with | is_val hv => cases hv

/-- Once the left branch of a `Safe` `par` node is an answer, the right branch is safe
  (the sequential continuation `h2` applied to the left answer's trivial self-run). -/
theorem Safe.par_inv_right {m : Memory} {C1 C2 : CaptureSet {}} {e1 e2 : Exp {}}
    (h : Safe m (.par C1 C2 e1 e2)) (hans : e1.IsAns) : Safe m e2 := by
  cases h with
  | par _ h2 _ _ _ _ _ _ _ _ _ => exact h2 (BigStep.of_isAns hans)
  | ans hans' => cases hans' with | is_val hv => cases hv

/-- **`SeqStep ⊆ Step` over a `Safe` configuration.**  Every sequential step lifts to a
  guarded interleaving step.  All cases are a direct constructor re-use except the two
  `par` congruences, whose guard discharge is `step_par_{left,right}_lift`. -/
theorem SeqStep.toStep {t : Trace} {m m' : Memory} {e e' : Exp {}}
    (hstep : SeqStep t m e m' e') :
    Exp.WfInHeap e m.heap → Safe m e → Step t m e m' e' := by
  induction hstep with
  | step_apply h => exact fun _ _ => Step.step_apply h
  | step_invoke h1 h2 => exact fun _ _ => Step.step_invoke h1 h2
  | step_tapply h => exact fun _ _ => Step.step_tapply h
  | step_capply h => exact fun _ _ => Step.step_capply h
  | step_unwrap h => exact fun _ _ => Step.step_unwrap h
  | step_cond_var_true h => exact fun _ _ => Step.step_cond_var_true h
  | step_cond_var_false h => exact fun _ _ => Step.step_cond_var_false h
  | step_read h1 h2 => exact fun _ _ => Step.step_read h1 h2
  | step_write_true h1 h2 => exact fun _ _ => Step.step_write_true h1 h2
  | step_write_false h1 h2 => exact fun _ _ => Step.step_write_false h1 h2
  | step_alloc h1 h2 => exact fun _ _ => Step.step_alloc h1 h2
  | step_drop h => exact fun _ _ => Step.step_drop h
  | step_ctx_letin hstep_a ih =>
    intro hwf hsafe
    cases hwf with
    | wf_letin hwf1 _ =>
      cases hsafe with
      | letin hsa _ _ _ => exact Step.step_ctx_letin (ih hwf1 hsa)
      | ans hans => cases hans with | is_val hv => cases hv
  | step_ctx_unpack hstep_a ih =>
    intro hwf hsafe
    cases hwf with
    | wf_unpack hwf1 _ =>
      cases hsafe with
      | unpack hsa _ _ => exact Step.step_ctx_unpack (ih hwf1 hsa)
      | ans hans => cases hans with | is_val hv => cases hv
  | step_par_left hstep_a ih =>
    intro hwf hsafe
    obtain ⟨hwf1, _⟩ := Exp.wf_inv_par hwf
    exact step_par_left_lift hsafe hwf hstep_a (ih hwf1 (Safe.par_inv_left hsafe))
  | step_par_right hans_a hstep_b ih =>
    intro hwf hsafe
    obtain ⟨_, hwf2⟩ := Exp.wf_inv_par hwf
    exact step_par_right_lift hsafe hwf hans_a hstep_b (ih hwf2 (Safe.par_inv_right hsafe hans_a))
  | step_par_join h1 h2 => exact fun _ _ => Step.step_par_join h1 h2
  | step_rename => exact fun _ _ => Step.step_rename
  | step_lift hv hwf_v hfresh => exact fun _ _ => Step.step_lift hv hwf_v hfresh
  | step_unpack => exact fun _ _ => Step.step_unpack

/-- **`SeqReduce ⊆ Reduce`.**  Fold `SeqStep.toStep` over the sequential run, threading
  `Safe`/`WfInHeap` by `step_preserves_safe`/`step_preserves_wf`. -/
theorem SeqReduce.toReduce {t : Trace} {m m' : Memory} {e e' : Exp {}}
    (hwf : Exp.WfInHeap e m.heap)
    (hsafe : Safe m e)
    (hred : SeqReduce t m e m' e') :
    Reduce t m e m' e' := by
  revert hwf hsafe
  induction hred with
  | refl => exact fun _ _ => Reduce.refl
  | step hstep hrest ih =>
    intro hwf hsafe
    exact Reduce.step (SeqStep.toStep hstep hwf hsafe)
      (ih (step_preserves_wf hstep hwf) (step_preserves_safe hstep hwf hsafe))

/-! ## Small-step diamond engine

  Standardization reorders an interleaving run into the canonical left-first
  schedule.  The engine is a SMALL-STEP commutation of separated branch steps:
  a right step commutes past a left run, reaching the same memory and answer, the
  two traces being reordered.  This must stay at the small-step level (it cannot
  route through the BigStep diamond `step_run_commute`): `bs_read` is relationally
  nondeterministic, so `BigStep → SeqReduce` is false; small steps read the stored
  bit deterministically, so a reordered schedule of a GIVEN run reads the same bits.

  The kernel is the single-step frame `SeqStep.frame_off` (a step replays off a cell
  it never touches), lifted to the single-single commute `step_step_swap` and then to
  the step-vs-run commute `step_reduce_swap`. -/

/-- A single `SeqStep` preserves an existing value cell: value cells are immutable
  (only `mcell` liveness can change, and only fresh cells are added). -/
theorem SeqStep.val_preserved {t : Trace} {m m' : Memory} {e e' : Exp {}} {l : Nat} {w}
    (hstep : SeqStep t m e m' e') (hl : m.lookup l = some (.val w)) :
    m'.lookup l = some (.val w) := by
  obtain ⟨c', hc', hsubc⟩ := step_memory_monotonic hstep l _ hl
  cases c' with
  | val w' => simp only [Cell.subsumes] at hsubc; exact hsubc ▸ hc'
  | capability ci => simp only [Cell.subsumes] at hsubc; cases hsubc
  | masked => simp only [Cell.subsumes] at hsubc; cases hsubc

/-- A single `SeqStep` whose trace does not `allocd` `l` keeps `l` fresh: only
  `step_alloc` introduces an `alloc` event, and it allocates a fresh location. -/
theorem SeqStep.alloc_fresh {t : Trace} {m m' : Memory} {e e' : Exp {}} {l : Nat}
    (hstep : SeqStep t m e m' e') (hal : Trace.allocd t l) : m.lookup l = none := by
  induction hstep with
  | step_apply _ | step_invoke _ _ | step_tapply _ | step_capply _ | step_unwrap _
  | step_cond_var_true _ | step_cond_var_false _ | step_read _ _
  | step_write_true _ _ | step_write_false _ _ | step_drop _
  | step_rename | step_unpack | step_par_join _ _ | step_lift _ _ _ =>
    simp only [Trace.allocd] at hal
  | step_alloc _ hfresh =>
    simp only [Trace.allocd, or_false] at hal
    rw [Memory.lookup, hal]; exact hfresh
  | step_ctx_letin _ ih | step_ctx_unpack _ ih
  | step_par_left _ ih | step_par_right _ _ ih => exact ih hal

/-- A single `SeqStep` preserves a present cell it does not externally touch. -/
theorem SeqStep.untouched_preserved {t : Trace} {m m' : Memory} {e e' : Exp {}} {c : Nat}
    (hstep : SeqStep t m e m' e') (hne : m.lookup c ≠ none) (hnt : ¬ Trace.touched t c) :
    m'.lookup c = m.lookup c := by
  induction hstep with
  | step_apply _ | step_invoke _ _ | step_tapply _ | step_capply _ | step_unwrap _
  | step_cond_var_true _ | step_cond_var_false _ | step_read _ _
  | step_rename | step_unpack | step_par_join _ _ => rfl
  | step_write_true hx _ | step_write_false hx _ =>
    simp only [Trace.touched, or_false] at hnt
    exact Memory.update_mcell_lookup_ne hnt
  | step_drop hx =>
    simp only [Trace.touched, or_false] at hnt
    exact Memory.drop_mcell_lookup_ne hnt
  | step_alloc _ hfresh =>
    simp only [Memory.lookup, Memory.extend_mcell, Heap.extend_mcell]
    rw [if_neg (fun h => hne (by rw [Memory.lookup, h]; exact hfresh))]
  | step_lift hv hwf hfresh =>
    simp only [Memory.lookup, Memory.extend, Heap.extend]
    rw [if_neg (fun h => hne (by rw [Memory.lookup, h]; exact hfresh))]
  | step_ctx_letin _ ih | step_ctx_unpack _ ih => exact ih hne hnt
  | step_par_left _ ih => exact ih hne hnt
  | step_par_right _ _ ih => exact ih hne hnt

/-- A single `SeqStep` preserves a present cell it neither writes nor drops (reads
  are permitted).  Mirrors `BigStep.unmutated_preserved`. -/
theorem SeqStep.unmutated_preserved {t : Trace} {m m' : Memory} {e e' : Exp {}} {l : Nat}
    (hstep : SeqStep t m e m' e') (hne : m.lookup l ≠ none)
    (hw : ¬ (TraceItem.access .epsilon l ∈ t)) (hd : ¬ (TraceItem.dealloc l ∈ t)) :
    m'.lookup l = m.lookup l := by
  induction hstep with
  | step_apply _ | step_invoke _ _ | step_tapply _ | step_capply _ | step_unwrap _
  | step_cond_var_true _ | step_cond_var_false _ | step_read _ _
  | step_rename | step_unpack | step_par_join _ _ => rfl
  | step_write_true hx _ | step_write_false hx _ =>
    refine Memory.update_mcell_lookup_ne (fun h => hw ?_)
    rw [h]; exact List.mem_singleton.mpr rfl
  | step_drop hx =>
    refine Memory.drop_mcell_lookup_ne (fun h => hd ?_)
    rw [h]; exact List.mem_singleton.mpr rfl
  | step_alloc _ hfresh =>
    simp only [Memory.lookup, Memory.extend_mcell, Heap.extend_mcell]
    rw [if_neg (fun h => hne (by rw [Memory.lookup, h]; exact hfresh))]
  | step_lift hv hwf hfresh =>
    simp only [Memory.lookup, Memory.extend, Heap.extend]
    rw [if_neg (fun h => hne (by rw [Memory.lookup, h]; exact hfresh))]
  | step_ctx_letin _ ih | step_ctx_unpack _ ih => exact ih hne hw hd
  | step_par_left _ ih => exact ih hne hw hd
  | step_par_right _ _ ih => exact ih hne hw hd

/-- A value cell and a capability cell at the same location are impossible: so a
  value-cell lookup is distinct from any capability cell. -/
theorem Memory.val_ne_cap {m : Memory} {c x : Nat} {ci w}
    (hcap : m.lookup c = some (.capability ci)) (hval : m.lookup x = some (.val w)) :
    x ≠ c := fun h => by subst h; rw [hval] at hcap; cases hcap

/-- Two memories agreeing off `c` keep agreeing off `c` after an identical `update_mcell`. -/
theorem Memory.update_mcell_lookup_agree {ma mb : Memory} {x c : Nat} {bb : Bool} {ℓ pa pb}
    (hag : ∀ l, l ≠ c → ma.lookup l = mb.lookup l) :
    ∀ l, l ≠ c → (ma.update_mcell x bb ℓ pa).lookup l = (mb.update_mcell x bb ℓ pb).lookup l := by
  intro l hlc
  by_cases hlx : l = x
  · subst hlx; simp only [Memory.lookup, Memory.update_mcell, Heap.update_cell, if_true]
  · rw [Memory.update_mcell_lookup_ne hlx, Memory.update_mcell_lookup_ne hlx]; exact hag l hlc

/-- Two memories agreeing off `c` keep agreeing off `c` after an identical `drop_mcell`. -/
theorem Memory.drop_mcell_lookup_agree {ma mb : Memory} {x c : Nat} {pa pb}
    (hag : ∀ l, l ≠ c → ma.lookup l = mb.lookup l) :
    ∀ l, l ≠ c → (ma.drop_mcell x pa).lookup l = (mb.drop_mcell x pb).lookup l := by
  intro l hlc
  by_cases hlx : l = x
  · subst hlx; simp only [Memory.lookup, Memory.drop_mcell, Heap.update_cell, if_true]
  · rw [Memory.drop_mcell_lookup_ne hlx, Memory.drop_mcell_lookup_ne hlx]; exact hag l hlc

/-- Two memories agreeing off `c` keep agreeing off `c` after an identical `extend_mcell`. -/
theorem Memory.extend_mcell_lookup_agree {ma mb : Memory} {l c : Nat} {bb : Bool}
    {pa : ma.heap l = none} {pb : mb.heap l = none}
    (hag : ∀ k, k ≠ c → ma.lookup k = mb.lookup k) :
    ∀ k, k ≠ c → (ma.extend_mcell l bb pa).lookup k = (mb.extend_mcell l bb pb).lookup k := by
  intro k hkc
  by_cases hkl : k = l
  · subst hkl; rw [Memory.extend_mcell_lookup pa, Memory.extend_mcell_lookup pb]
  · simp only [Memory.lookup, Memory.extend_mcell, Heap.extend_mcell, if_neg hkl]; exact hag k hkc

/-- A present location differs from an absent one. -/
theorem Memory.present_ne_absent {m : Memory} {x c : Nat} {v}
    (hx : m.heap x = some v) (hc : m.lookup c = none) : x ≠ c :=
  fun h => by rw [h] at hx; rw [Memory.lookup] at hc; rw [hc] at hx; cases hx

/-- A freshly-unallocated location differs from any present location. -/
theorem Memory.fresh_ne_present {m : Memory} {l c : Nat}
    (hfresh : m.heap l = none) (hc : m.lookup c ≠ none) : l ≠ c :=
  fun h => hc (by rw [Memory.lookup, ← h]; exact hfresh)

/-- A freshly-unallocated location differs from any capability cell. -/
theorem Memory.fresh_ne_cap {m : Memory} {l c : Nat} {ci}
    (hfresh : m.heap l = none) (hcap : m.lookup c = some (.capability ci)) :
    l ≠ c := fun h => by subst h; rw [Memory.lookup, hfresh] at hcap; cases hcap

/-- Two memories agreeing off `c` keep agreeing off `c` after identical value `extend`s,
  given their stored reachabilities agree. -/
theorem Memory.extend_lookup_agree {ma mb : Memory} {l c : Nat} {v : Exp {}} {hv : v.IsSimpleVal}
    {wa : v.WfInHeap ma.heap} {wb : v.WfInHeap mb.heap} {pa pb}
    (hag : ∀ k, k ≠ c → ma.lookup k = mb.lookup k)
    (hreach : compute_reachability ma.heap v hv = compute_reachability mb.heap v hv) :
    ∀ k, k ≠ c →
      (ma.extend l ⟨v, hv, compute_reachability ma.heap v hv⟩ wa rfl pa).lookup k
        = (mb.extend l ⟨v, hv, compute_reachability mb.heap v hv⟩ wb rfl pb).lookup k := by
  intro k hkc
  by_cases hkl : k = l
  · subst hkl
    simp only [Memory.lookup, Memory.extend, Heap.extend_lookup_eq]
    exact congrArg (fun R => some (Cell.val ⟨v, hv, R⟩)) hreach
  · simp only [Memory.lookup, Memory.extend, Heap.extend, if_neg hkl]; exact hag k hkc

/-- **Single-step exact frame.**  The `SeqStep` analogue of `BigStep.frame_off`: if `e`
  steps from `ma`, and `mb` agrees with `ma` off a capability cell `c` that the step never
  touches, then `e` replays the SAME step from `mb` (same trace, same result expression),
  the results agree off `c`, and `c` is unchanged.  This is the kernel of the small-step
  diamond: separated steps operate off each other's cells, so each replays past the other. -/
theorem SeqStep.frame_off {ma mb ma' : Memory} {e e' : Exp {}} {t : Trace} {c : Nat}
    (hstep : SeqStep t ma e ma' e')
    (hc : ∃ ci, ma.lookup c = some (.capability ci))
    (hcb : ∃ ci, mb.lookup c = some (.capability ci))
    (hag : ∀ l, l ≠ c → ma.lookup l = mb.lookup l)
    (hnt : ¬ Trace.touched t c)
    (hwf : Exp.WfInHeap e mb.heap) :
    ∃ mb', SeqStep t mb e mb' e' ∧ (∀ l, l ≠ c → ma'.lookup l = mb'.lookup l) ∧
      mb'.lookup c = mb.lookup c := by
  induction hstep generalizing mb with
  | step_apply hlk =>
    obtain ⟨ci, hci⟩ := hc
    exact ⟨mb, SeqStep.step_apply ((hag _ (Memory.val_ne_cap hci hlk)) ▸ hlk), hag, rfl⟩
  | step_tapply hlk =>
    obtain ⟨ci, hci⟩ := hc
    exact ⟨mb, SeqStep.step_tapply ((hag _ (Memory.val_ne_cap hci hlk)) ▸ hlk), hag, rfl⟩
  | step_capply hlk =>
    obtain ⟨ci, hci⟩ := hc
    exact ⟨mb, SeqStep.step_capply ((hag _ (Memory.val_ne_cap hci hlk)) ▸ hlk), hag, rfl⟩
  | step_unwrap hlk =>
    obtain ⟨ci, hci⟩ := hc
    exact ⟨mb, SeqStep.step_unwrap ((hag _ (Memory.val_ne_cap hci hlk)) ▸ hlk), hag, rfl⟩
  | step_cond_var_true hlk =>
    obtain ⟨ci, hci⟩ := hc
    exact ⟨mb, SeqStep.step_cond_var_true ((hag _ (Memory.val_ne_cap hci hlk)) ▸ hlk), hag, rfl⟩
  | step_cond_var_false hlk =>
    obtain ⟨ci, hci⟩ := hc
    exact ⟨mb, SeqStep.step_cond_var_false ((hag _ (Memory.val_ne_cap hci hlk)) ▸ hlk), hag, rfl⟩
  | step_invoke hlkx hlky =>
    obtain ⟨ci, hci⟩ := hc
    have hxc : _ ≠ c := fun h => hnt (Or.inl h.symm)
    exact ⟨mb, SeqStep.step_invoke ((hag _ hxc) ▸ hlkx)
      ((hag _ (Memory.val_ne_cap hci hlky)) ▸ hlky), hag, rfl⟩
  | step_read hlkx hlky =>
    obtain ⟨ci, hci⟩ := hc
    have hyc : _ ≠ c := fun h => hnt (Or.inl h.symm)
    exact ⟨mb, SeqStep.step_read ((hag _ (Memory.val_ne_cap hci hlkx)) ▸ hlkx)
      ((hag _ hyc) ▸ hlky), hag, rfl⟩
  | step_write_true hx hy =>
    obtain ⟨ci, hci⟩ := hc
    have hxc : _ ≠ c := fun h => hnt (Or.inl h.symm)
    refine ⟨mb.update_mcell _ true .live ⟨_, (hag _ hxc) ▸ hx⟩,
      SeqStep.step_write_true ((hag _ hxc) ▸ hx) ((hag _ (Memory.val_ne_cap hci hy)) ▸ hy),
      Memory.update_mcell_lookup_agree hag, Memory.update_mcell_lookup_ne (Ne.symm hxc)⟩
  | step_write_false hx hy =>
    obtain ⟨ci, hci⟩ := hc
    have hxc : _ ≠ c := fun h => hnt (Or.inl h.symm)
    refine ⟨mb.update_mcell _ false .live ⟨_, (hag _ hxc) ▸ hx⟩,
      SeqStep.step_write_false ((hag _ hxc) ▸ hx) ((hag _ (Memory.val_ne_cap hci hy)) ▸ hy),
      Memory.update_mcell_lookup_agree hag, Memory.update_mcell_lookup_ne (Ne.symm hxc)⟩
  | step_drop hx =>
    obtain ⟨ci, hci⟩ := hc
    have hxc : _ ≠ c := fun h => hnt (Or.inl h.symm)
    refine ⟨mb.drop_mcell _ ⟨_, (hag _ hxc) ▸ hx⟩,
      SeqStep.step_drop ((hag _ hxc) ▸ hx),
      Memory.drop_mcell_lookup_agree hag, Memory.drop_mcell_lookup_ne (Ne.symm hxc)⟩
  | step_alloc hlk hfresh =>
    obtain ⟨ci, hci⟩ := hc
    have hlc := Memory.fresh_ne_cap hfresh hci
    have hfreshb : mb.heap _ = none := (hag _ hlc).symm.trans hfresh
    refine ⟨mb.extend_mcell _ _ hfreshb,
      SeqStep.step_alloc ((hag _ (Memory.val_ne_cap hci hlk)) ▸ hlk) hfreshb,
      Memory.extend_mcell_lookup_agree hag, ?_⟩
    simp only [Memory.lookup, Memory.extend_mcell, Heap.extend_mcell, if_neg (Ne.symm hlc)]
  | step_rename =>
    exact ⟨mb, SeqStep.step_rename, hag, rfl⟩
  | step_unpack =>
    exact ⟨mb, SeqStep.step_unpack, hag, rfl⟩
  | step_par_join h1 h2 =>
    exact ⟨mb, SeqStep.step_par_join h1 h2, hag, rfl⟩
  | step_lift hv hwf_v hfresh =>
    obtain ⟨ci, hci⟩ := hc
    obtain ⟨cib, hcib⟩ := hcb
    have hlc := Memory.fresh_ne_cap hfresh hci
    have hfreshb : mb.heap _ = none := (hag _ hlc).symm.trans hfresh
    have hwf_vb : _ := (Exp.wf_inv_letin hwf).1
    have hreach_eq : compute_reachability _ _ hv = compute_reachability mb.heap _ hv :=
      compute_reachability_frame hci hcib hag _ hv
    refine ⟨mb.extend _ ⟨_, hv, compute_reachability mb.heap _ hv⟩ hwf_vb rfl hfreshb,
      SeqStep.step_lift hv hwf_vb hfreshb,
      Memory.extend_lookup_agree hag hreach_eq, ?_⟩
    simp only [Memory.lookup, Memory.extend, Heap.extend, if_neg (Ne.symm hlc)]
  | step_ctx_letin hinner ih =>
    obtain ⟨mb', stepb, agb, cpresb⟩ := ih hc hcb hag hnt (Exp.wf_inv_letin hwf).1
    exact ⟨mb', SeqStep.step_ctx_letin stepb, agb, cpresb⟩
  | step_ctx_unpack hinner ih =>
    obtain ⟨mb', stepb, agb, cpresb⟩ := ih hc hcb hag hnt (Exp.wf_inv_unpack hwf).1
    exact ⟨mb', SeqStep.step_ctx_unpack stepb, agb, cpresb⟩
  | step_par_left hinner ih =>
    obtain ⟨mb', stepb, agb, cpresb⟩ := ih hc hcb hag hnt (Exp.wf_inv_par hwf).1
    exact ⟨mb', SeqStep.step_par_left stepb, agb, cpresb⟩
  | step_par_right hans hinner ih =>
    obtain ⟨mb', stepb, agb, cpresb⟩ := ih hc hcb hag hnt (Exp.wf_inv_par hwf).2
    exact ⟨mb', SeqStep.step_par_right hans stepb, agb, cpresb⟩

/-- **Single-step frame, absent variant.**  The `SeqStep` analogue of
  `BigStep.frame_off_absent`: if `e` (well-formed in `mb`) steps from `ma`, and `mb`
  agrees with `ma` off a cell `c` PRESENT in `ma` but ABSENT in `mb` (the other thread's
  fresh cell), then `e` replays from `mb`, results agree off `c`, `c` stays absent, and
  the step never touched `c` (it cannot, being absent in the well-formed `mb`). -/
theorem SeqStep.frame_off_absent {ma mb ma' : Memory} {e e' : Exp {}} {t : Trace} {c : Nat}
    (hstep : SeqStep t ma e ma' e')
    (hc : ma.lookup c ≠ none)
    (hcb : mb.lookup c = none)
    (hag : ∀ l, l ≠ c → ma.lookup l = mb.lookup l)
    (hwf : Exp.WfInHeap e mb.heap) :
    ∃ mb', SeqStep t mb e mb' e' ∧ (∀ l, l ≠ c → ma'.lookup l = mb'.lookup l) ∧
      mb'.lookup c = none ∧ ¬ Trace.touched t c := by
  induction hstep generalizing mb with
  | step_apply hlk =>
    match hwf with
    | .wf_app (.wf_free (n := xx) hx1) hwfy =>
      have hxc : xx ≠ c := fun h => by
        rw [h] at hx1; rw [show mb.heap c = none from hcb] at hx1; cases hx1
      exact ⟨mb, SeqStep.step_apply ((hag xx hxc) ▸ hlk), hag, hcb, by simp [Trace.touched]⟩
  | step_tapply hlk =>
    match hwf with
    | .wf_tapp (.wf_free (n := xx) hx1) _ =>
      have hxc : xx ≠ c := fun h => by
        rw [h] at hx1; rw [show mb.heap c = none from hcb] at hx1; cases hx1
      exact ⟨mb, SeqStep.step_tapply ((hag xx hxc) ▸ hlk), hag, hcb, by simp [Trace.touched]⟩
  | step_capply hlk =>
    match hwf with
    | .wf_capp (.wf_free (n := xx) hx1) _ =>
      have hxc : xx ≠ c := fun h => by
        rw [h] at hx1; rw [show mb.heap c = none from hcb] at hx1; cases hx1
      exact ⟨mb, SeqStep.step_capply ((hag xx hxc) ▸ hlk), hag, hcb, by simp [Trace.touched]⟩
  | step_unwrap hlk =>
    match hwf with
    | .wf_unwrap (.wf_free (n := xx) hx1) =>
      have hxc : xx ≠ c := fun h => by
        rw [h] at hx1; rw [show mb.heap c = none from hcb] at hx1; cases hx1
      exact ⟨mb, SeqStep.step_unwrap ((hag xx hxc) ▸ hlk), hag, hcb, by simp [Trace.touched]⟩
  | step_cond_var_true hlk =>
    obtain ⟨hwfx, hwf2, _⟩ := Exp.wf_inv_cond hwf
    match hwfx with
    | .wf_free (n := xb) hxb =>
      have hxc : xb ≠ c := fun h => by
        rw [h] at hxb; rw [show mb.heap c = none from hcb] at hxb; cases hxb
      have hlkb := (hag xb hxc) ▸ hlk
      exact ⟨mb, SeqStep.step_cond_var_true hlkb, hag, hcb, by simp [Trace.touched]⟩
  | step_cond_var_false hlk =>
    obtain ⟨hwfx, _, hwf3⟩ := Exp.wf_inv_cond hwf
    match hwfx with
    | .wf_free (n := xb) hxb =>
      have hxc : xb ≠ c := fun h => by
        rw [h] at hxb; rw [show mb.heap c = none from hcb] at hxb; cases hxb
      have hlkb := (hag xb hxc) ▸ hlk
      exact ⟨mb, SeqStep.step_cond_var_false hlkb, hag, hcb, by simp [Trace.touched]⟩
  | step_invoke hlkx hlky =>
    match hwf with
    | .wf_app (.wf_free (n := xx) hx1) (.wf_free (n := yy) hy1) =>
      have hxc : xx ≠ c := fun h => by
        rw [h] at hx1; rw [show mb.heap c = none from hcb] at hx1; cases hx1
      have hyc : yy ≠ c := fun h => by
        rw [h] at hy1; rw [show mb.heap c = none from hcb] at hy1; cases hy1
      exact ⟨mb, SeqStep.step_invoke ((hag xx hxc) ▸ hlkx) ((hag yy hyc) ▸ hlky), hag, hcb,
        by simp only [Trace.touched, or_false]; exact fun h => hxc h.symm⟩
  | step_read hlkx hlky =>
    match hwf with
    | .wf_read (.wf_free (n := xx) hx1) =>
      have hxc : xx ≠ c := fun h => by
        rw [h] at hx1; rw [show mb.heap c = none from hcb] at hx1; cases hx1
      have hlkxb := (hag xx hxc) ▸ hlkx
      match Memory.wf_lookup hlkxb with
      | .wf_reader (.wf_free (n := yy) hy1) =>
        have hyc : yy ≠ c := fun h => by
          rw [h] at hy1; rw [show mb.heap c = none from hcb] at hy1; cases hy1
        exact ⟨mb, SeqStep.step_read hlkxb ((hag yy hyc) ▸ hlky), hag, hcb,
          by simp only [Trace.touched, or_false]; exact fun h => hyc h.symm⟩
  | step_write_true hlkx hlky =>
    cases hwf with
    | wf_write hwfx hwfy => cases hwfx with | wf_free hxb => cases hwfy with | wf_free hyb =>
      have hxc := Memory.present_ne_absent hxb hcb
      have hyc := Memory.present_ne_absent hyb hcb
      refine ⟨mb.update_mcell _ true .live ⟨_, (hag _ hxc) ▸ hlkx⟩,
        SeqStep.step_write_true ((hag _ hxc) ▸ hlkx) ((hag _ hyc) ▸ hlky),
        Memory.update_mcell_lookup_agree hag, ?_,
        by simp only [Trace.touched, or_false]; exact fun h => hxc h.symm⟩
      rw [Memory.update_mcell_lookup_ne (Ne.symm hxc)]; exact hcb
  | step_write_false hlkx hlky =>
    cases hwf with
    | wf_write hwfx hwfy => cases hwfx with | wf_free hxb => cases hwfy with | wf_free hyb =>
      have hxc := Memory.present_ne_absent hxb hcb
      have hyc := Memory.present_ne_absent hyb hcb
      refine ⟨mb.update_mcell _ false .live ⟨_, (hag _ hxc) ▸ hlkx⟩,
        SeqStep.step_write_false ((hag _ hxc) ▸ hlkx) ((hag _ hyc) ▸ hlky),
        Memory.update_mcell_lookup_agree hag, ?_,
        by simp only [Trace.touched, or_false]; exact fun h => hxc h.symm⟩
      rw [Memory.update_mcell_lookup_ne (Ne.symm hxc)]; exact hcb
  | step_drop hlkx =>
    cases hwf with
    | wf_drop hwfx => cases hwfx with | wf_free hxb =>
      have hxc := Memory.present_ne_absent hxb hcb
      refine ⟨mb.drop_mcell _ ⟨_, (hag _ hxc) ▸ hlkx⟩, SeqStep.step_drop ((hag _ hxc) ▸ hlkx),
        Memory.drop_mcell_lookup_agree hag, ?_,
        by simp only [Trace.touched, or_false]; exact fun h => hxc h.symm⟩
      rw [Memory.drop_mcell_lookup_ne (Ne.symm hxc)]; exact hcb
  | step_alloc hlk hfresh =>
    have hlc := Memory.fresh_ne_present hfresh hc
    cases hwf with
    | wf_alloc hwfx => cases hwfx with | wf_free hx1 =>
      have hxc := Memory.present_ne_absent hx1 hcb
      have hfreshb : mb.heap _ = none := (hag _ hlc).symm.trans hfresh
      refine ⟨mb.extend_mcell _ _ hfreshb, SeqStep.step_alloc ((hag _ hxc) ▸ hlk) hfreshb,
        Memory.extend_mcell_lookup_agree hag, ?_, by simp [Trace.touched]⟩
      simp only [Memory.lookup, Memory.extend_mcell, Heap.extend_mcell, if_neg (Ne.symm hlc)]
      exact hcb
  | step_rename =>
    exact ⟨mb, SeqStep.step_rename, hag, hcb, by simp [Trace.touched]⟩
  | step_unpack =>
    exact ⟨mb, SeqStep.step_unpack, hag, hcb, by simp [Trace.touched]⟩
  | step_par_join h1 h2 =>
    exact ⟨mb, SeqStep.step_par_join h1 h2, hag, hcb, by simp [Trace.touched]⟩
  | step_lift hv hwf_v hfresh =>
    have hlc := Memory.fresh_ne_present hfresh hc
    have hwf_vb : _ := (Exp.wf_inv_letin hwf).1
    have hfreshb : mb.heap _ = none := (hag _ hlc).symm.trans hfresh
    have hreach_eq : compute_reachability _ _ hv = compute_reachability mb.heap _ hv :=
      compute_reachability_frame_wf hcb hag _ hv hwf_vb
    refine ⟨mb.extend _ ⟨_, hv, compute_reachability mb.heap _ hv⟩ hwf_vb rfl hfreshb,
      SeqStep.step_lift hv hwf_vb hfreshb,
      Memory.extend_lookup_agree hag hreach_eq, ?_, by simp [Trace.touched]⟩
    simp only [Memory.lookup, Memory.extend, Heap.extend, if_neg (Ne.symm hlc)]
    exact hcb
  | step_ctx_letin hinner ih =>
    obtain ⟨mb', stepb, agb, cpresb, hntb⟩ := ih hc hcb hag (Exp.wf_inv_letin hwf).1
    exact ⟨mb', SeqStep.step_ctx_letin stepb, agb, cpresb, hntb⟩
  | step_ctx_unpack hinner ih =>
    obtain ⟨mb', stepb, agb, cpresb, hntb⟩ := ih hc hcb hag (Exp.wf_inv_unpack hwf).1
    exact ⟨mb', SeqStep.step_ctx_unpack stepb, agb, cpresb, hntb⟩
  | step_par_left hinner ih =>
    obtain ⟨mb', stepb, agb, cpresb, hntb⟩ := ih hc hcb hag (Exp.wf_inv_par hwf).1
    exact ⟨mb', SeqStep.step_par_left stepb, agb, cpresb, hntb⟩
  | step_par_right hans hinner ih =>
    obtain ⟨mb', stepb, agb, cpresb, hntb⟩ := ih hc hcb hag (Exp.wf_inv_par hwf).2
    exact ⟨mb', SeqStep.step_par_right hans stepb, agb, cpresb, hntb⟩

/-- Single-step frame, fresh variant: `c` is a cell present in `ma` (a capability) but
  ABSENT in `mb` (the other thread allocated it).  Corollary of `frame_off_absent`. -/
theorem SeqStep.frame_off_fresh {ma mb ma' : Memory} {e e' : Exp {}} {t : Trace} {c : Nat}
    (hstep : SeqStep t ma e ma' e')
    (hc : ∃ ci, ma.lookup c = some (.capability ci))
    (hcb : mb.lookup c = none)
    (hag : ∀ l, l ≠ c → ma.lookup l = mb.lookup l)
    (hwf : Exp.WfInHeap e mb.heap) :
    ∃ mb', SeqStep t mb e mb' e' ∧ (∀ l, l ≠ c → ma'.lookup l = mb'.lookup l) ∧
      mb'.lookup c = none ∧ ¬ Trace.touched t c :=
  SeqStep.frame_off_absent hstep (by obtain ⟨ci, h⟩ := hc; rw [h]; simp) hcb hag hwf

/-- **Single-step diamond.**  A right step (`eR : m1 → m2`) commutes past a single
  separated left step (`eL : m2 → mb`): if their traces do not interfere, then `eL` can
  step FIRST from `m1` (to some `mc`) and the SAME `eR`-step fires from `mc`, reaching the
  SAME `mb`.  The small-step analogue of `BigStep.step_run_commute` (run = single `SeqStep`),
  inducting on the right step and framing the left step past it via `SeqStep.frame_off`. -/
theorem step_step_swap {ts s : Trace} {m1 m2 mb : Memory} {eR eR' eL eL1 : Exp {}}
    (hstep : Step ts m1 eR m2 eR')
    (hrun : SeqStep s m2 eL mb eL1)
    (hsep : Trace.Noninterfere s ts)
    (hwf1 : Exp.WfInHeap eL m1.heap)
    (hwf2 : Exp.WfInHeap eR m1.heap) :
    ∃ mc, SeqStep s m1 eL mc eL1 ∧ Step ts mc eR mb eR' := by
  induction hstep with
  | step_apply hlk =>
    exact ⟨mb, hrun, Step.step_apply (SeqStep.val_preserved hrun hlk)⟩
  | step_invoke hlkx hlky =>
    have hnal : ¬ Trace.allocd s _ := fun ha => by
      have := SeqStep.alloc_fresh hrun ha; rw [hlkx] at this; cases this
    have hntsx : ¬ Trace.touched s _ :=
      Trace.not_touched_of_noninterfere hsep (Or.inl ⟨rfl, by simp, rfl⟩) (by simp) hnal
    exact ⟨mb, hrun,
      Step.step_invoke (SeqStep.untouched_preserved hrun (by rw [hlkx]; simp) hntsx ▸ hlkx)
        (SeqStep.val_preserved hrun hlky)⟩
  | step_tapply hlk =>
    exact ⟨mb, hrun, Step.step_tapply (SeqStep.val_preserved hrun hlk)⟩
  | step_capply hlk =>
    exact ⟨mb, hrun, Step.step_capply (SeqStep.val_preserved hrun hlk)⟩
  | step_unwrap hlk =>
    exact ⟨mb, hrun, Step.step_unwrap (SeqStep.val_preserved hrun hlk)⟩
  | step_cond_var_true hlk =>
    exact ⟨mb, hrun, Step.step_cond_var_true (SeqStep.val_preserved hrun hlk)⟩
  | step_cond_var_false hlk =>
    exact ⟨mb, hrun, Step.step_cond_var_false (SeqStep.val_preserved hrun hlk)⟩
  | step_read hlkx hlky =>
    have hnal : ¬ Trace.allocd s _ := fun ha => by
      have := SeqStep.alloc_fresh hrun ha; rw [hlky] at this; cases this
    obtain ⟨hw, hd⟩ := Trace.not_mutated_of_noninterfere hsep (Or.inl ⟨rfl, by simp, rfl⟩) hnal
    exact ⟨mb, hrun,
      Step.step_read (SeqStep.val_preserved hrun hlkx)
        (SeqStep.unmutated_preserved hrun (by rw [hlky]; simp) hw hd ▸ hlky)⟩
  | step_write_true hx hy =>
    rename_i x m0 y b0 hv R
    have hyx : y ≠ x := fun h => by rw [h, hx] at hy; cases hy
    have hcx : (m0.update_mcell x true .live ⟨_, hx⟩).lookup x =
        some (Cell.capability (.mcell true .live)) := by
      simp only [Memory.lookup, Memory.update_mcell, Heap.update_cell, if_true]
    have hnal : ¬ Trace.allocd s x := fun ha => by
      have := SeqStep.alloc_fresh hrun ha
      rw [show (m0.update_mcell x true .live ⟨_, hx⟩).lookup x = _ from hcx] at this; cases this
    have hntsx : ¬ Trace.touched s x :=
      Trace.not_touched_of_noninterfere hsep (Or.inl ⟨rfl, by simp, rfl⟩) (by simp) hnal
    obtain ⟨mc, run, ag, cpres⟩ :=
      hrun.frame_off ⟨_, hcx⟩ ⟨_, hx⟩
        (fun l hl => Memory.update_mcell_lookup_ne hl) hntsx hwf1
    have mcx : mc.lookup x = some (Cell.capability (.mcell b0 .live)) := cpres.trans hx
    have mcy : mc.lookup y = some (Cell.val ⟨.btrue, hv, R⟩) :=
      (ag y hyx).symm.trans
        (SeqStep.val_preserved hrun (by rw [Memory.update_mcell_lookup_ne hyx]; exact hy))
    have hmb : mc.update_mcell x true .live ⟨_, mcx⟩ = mb := by
      apply Memory.ext_lookup; intro l
      by_cases hlx : l = x
      · subst hlx
        rw [show (mc.update_mcell l true .live ⟨_, mcx⟩).lookup l
                = some (Cell.capability (.mcell true .live)) from by
              simp only [Memory.lookup, Memory.update_mcell, Heap.update_cell, if_true],
            SeqStep.untouched_preserved hrun (by rw [hcx]; simp) hntsx, hcx]
      · rw [Memory.update_mcell_lookup_ne hlx, ag l hlx]
    exact ⟨mc, run, hmb ▸ Step.step_write_true mcx mcy⟩
  | step_write_false hx hy =>
    rename_i x m0 y b0 hv R
    have hyx : y ≠ x := fun h => by rw [h, hx] at hy; cases hy
    have hcx : (m0.update_mcell x false .live ⟨_, hx⟩).lookup x =
        some (Cell.capability (.mcell false .live)) := by
      simp only [Memory.lookup, Memory.update_mcell, Heap.update_cell, if_true]
    have hnal : ¬ Trace.allocd s x := fun ha => by
      have := SeqStep.alloc_fresh hrun ha
      rw [show (m0.update_mcell x false .live ⟨_, hx⟩).lookup x = _ from hcx] at this; cases this
    have hntsx : ¬ Trace.touched s x :=
      Trace.not_touched_of_noninterfere hsep (Or.inl ⟨rfl, by simp, rfl⟩) (by simp) hnal
    obtain ⟨mc, run, ag, cpres⟩ :=
      hrun.frame_off ⟨_, hcx⟩ ⟨_, hx⟩
        (fun l hl => Memory.update_mcell_lookup_ne hl) hntsx hwf1
    have mcx : mc.lookup x = some (Cell.capability (.mcell b0 .live)) := cpres.trans hx
    have mcy : mc.lookup y = some (Cell.val ⟨.bfalse, hv, R⟩) :=
      (ag y hyx).symm.trans
        (SeqStep.val_preserved hrun (by rw [Memory.update_mcell_lookup_ne hyx]; exact hy))
    have hmb : mc.update_mcell x false .live ⟨_, mcx⟩ = mb := by
      apply Memory.ext_lookup; intro l
      by_cases hlx : l = x
      · subst hlx
        rw [show (mc.update_mcell l false .live ⟨_, mcx⟩).lookup l
                = some (Cell.capability (.mcell false .live)) from by
              simp only [Memory.lookup, Memory.update_mcell, Heap.update_cell, if_true],
            SeqStep.untouched_preserved hrun (by rw [hcx]; simp) hntsx, hcx]
      · rw [Memory.update_mcell_lookup_ne hlx, ag l hlx]
    exact ⟨mc, run, hmb ▸ Step.step_write_false mcx mcy⟩
  | step_alloc hlk hfresh =>
    rename_i l m0 x b hv R
    have hcl : (m0.extend_mcell l b hfresh).lookup l =
        some (Cell.capability (.mcell b .live)) := Memory.extend_mcell_lookup hfresh
    obtain ⟨mc, run, ag, cpres, hnt⟩ :=
      hrun.frame_off_fresh ⟨_, hcl⟩ hfresh
        (fun k hk => by
          simp only [Memory.lookup, Memory.extend_mcell, Heap.extend_mcell, if_neg hk]) hwf1
    have mcx : mc.lookup x = some (.val ⟨if b then .btrue else .bfalse, hv, R⟩) :=
      SeqStep.val_preserved run hlk
    have hmb : mc.extend_mcell l b cpres = mb := by
      apply Memory.ext_lookup; intro k
      by_cases hkl : k = l
      · subst hkl
        rw [Memory.extend_mcell_lookup cpres,
            SeqStep.untouched_preserved hrun (by rw [hcl]; simp) hnt, hcl]
      · rw [show (mc.extend_mcell l b cpres).lookup k = mc.lookup k from by
              simp only [Memory.lookup, Memory.extend_mcell, Heap.extend_mcell, if_neg hkl],
            ag k hkl]
    exact ⟨mc, run, hmb ▸ Step.step_alloc mcx cpres⟩
  | step_drop hx =>
    rename_i x m0 b0
    have hcx : (m0.drop_mcell x ⟨_, hx⟩).lookup x =
        some (Cell.capability (.mcell false .dead)) := by
      simp only [Memory.lookup, Memory.drop_mcell, Heap.update_cell, if_true]
    have hnal : ¬ Trace.allocd s x := fun ha => by
      have := SeqStep.alloc_fresh hrun ha
      rw [show (m0.drop_mcell x ⟨_, hx⟩).lookup x = _ from hcx] at this; cases this
    have hntsx : ¬ Trace.touched s x :=
      Trace.not_touched_of_noninterfere hsep (Or.inl ⟨rfl, by simp, rfl⟩) (by simp) hnal
    obtain ⟨mc, run, ag, cpres⟩ :=
      hrun.frame_off ⟨_, hcx⟩ ⟨_, hx⟩
        (fun l hl => Memory.drop_mcell_lookup_ne hl) hntsx hwf1
    have mcx : mc.lookup x = some (Cell.capability (.mcell b0 .live)) := cpres.trans hx
    have hmb : mc.drop_mcell x ⟨_, mcx⟩ = mb := by
      apply Memory.ext_lookup; intro l
      by_cases hlx : l = x
      · subst hlx
        rw [show (mc.drop_mcell l ⟨_, mcx⟩).lookup l
                = some (Cell.capability (.mcell false .dead)) from by
              simp only [Memory.lookup, Memory.drop_mcell, Heap.update_cell, if_true],
            SeqStep.untouched_preserved hrun (by rw [hcx]; simp) hntsx, hcx]
      · rw [Memory.drop_mcell_lookup_ne hlx, ag l hlx]
    exact ⟨mc, run, hmb ▸ Step.step_drop mcx⟩
  | step_ctx_letin hinner ih =>
    obtain ⟨mc, run, stepc⟩ := ih hrun hsep hwf1 (Exp.wf_inv_letin hwf2).1
    exact ⟨mc, run, Step.step_ctx_letin stepc⟩
  | step_ctx_unpack hinner ih =>
    obtain ⟨mc, run, stepc⟩ := ih hrun hsep hwf1 (Exp.wf_inv_unpack hwf2).1
    exact ⟨mc, run, Step.step_ctx_unpack stepc⟩
  | step_par_left hinner ht hni ih =>
    cases hwf2 with
    | wf_par hwfC1 hwfC2 hwfa hwfb =>
      obtain ⟨mc, run, stepc⟩ := ih hrun hsep hwf1 hwfa
      have hr1 := CaptureSet.reachability_monotonic (step_memory_monotonic run) _ hwfC1
      have hr2 := CaptureSet.reachability_monotonic (step_memory_monotonic run) _ hwfC2
      exact ⟨mc, run, Step.step_par_left stepc (by rw [hr1]; exact ht)
        (by rw [hr1, hr2]; exact hni)⟩
  | step_par_right ht hni hinner ih =>
    cases hwf2 with
    | wf_par hwfC1 hwfC2 hwfa hwfb =>
      obtain ⟨mc, run, stepc⟩ := ih hrun hsep hwf1 hwfb
      have hr1 := CaptureSet.reachability_monotonic (step_memory_monotonic run) _ hwfC1
      have hr2 := CaptureSet.reachability_monotonic (step_memory_monotonic run) _ hwfC2
      exact ⟨mc, run, Step.step_par_right (by rw [hr2]; exact ht)
        (by rw [hr1, hr2]; exact hni) stepc⟩
  | step_par_join h1 h2 =>
    exact ⟨mb, hrun, Step.step_par_join h1 h2⟩
  | step_rename =>
    exact ⟨mb, hrun, Step.step_rename⟩
  | step_lift hv hwf hfresh =>
    rename_i v m0 _ l
    have hcl : (m0.extend l ⟨v, hv, compute_reachability m0.heap v hv⟩ hwf rfl hfresh).lookup l
        = some (Cell.val ⟨v, hv, compute_reachability m0.heap v hv⟩) := by
      simp only [Memory.lookup, Memory.extend, Heap.extend_lookup_eq]
    obtain ⟨mc, run, ag, cpres, hnt⟩ :=
      hrun.frame_off_absent (by rw [hcl]; simp) hfresh
        (fun k hk => by
          simp only [Memory.lookup, Memory.extend, Heap.extend, if_neg hk]) hwf1
    have hwfc : v.WfInHeap mc.heap := Exp.wf_monotonic (step_memory_monotonic run) hwf
    have hreach : compute_reachability mc.heap v hv = compute_reachability m0.heap v hv :=
      compute_reachability_monotonic (step_memory_monotonic run) v hv hwf
    have hmbl : (mc.extend l ⟨v, hv, compute_reachability mc.heap v hv⟩ hwfc rfl cpres).lookup l
        = some (Cell.val ⟨v, hv, compute_reachability mc.heap v hv⟩) := by
      simp only [Memory.lookup, Memory.extend, Heap.extend_lookup_eq]
    have hmb : mc.extend l ⟨v, hv, compute_reachability mc.heap v hv⟩ hwfc rfl cpres = mb := by
      apply Memory.ext_lookup; intro k
      by_cases hkl : k = l
      · subst hkl
        rw [hmbl, hreach, SeqStep.untouched_preserved hrun (by rw [hcl]; simp) hnt, hcl]
      · rw [show (mc.extend l ⟨v, hv, compute_reachability mc.heap v hv⟩ hwfc rfl cpres).lookup k
                = mc.lookup k from by
              simp only [Memory.lookup, Memory.extend, Heap.extend, if_neg hkl],
            ag k hkl]
    exact ⟨mc, run, hmb ▸ Step.step_lift hv hwfc cpres⟩
  | step_unpack =>
    exact ⟨mb, hrun, Step.step_unpack⟩

/-- A genuine interleaving `Step` grows the memory (final subsumes initial). -/
theorem Step.subsumes {t : Trace} {m m' : Memory} {e e' : Exp {}}
    (h : Step t m e m' e') : m'.subsumes m := by
  induction h with
  | step_apply _ | step_invoke _ _ | step_tapply _ | step_capply _ | step_unwrap _
  | step_cond_var_true _ | step_cond_var_false _ | step_read _ _
  | step_rename | step_unpack | step_par_join _ _ => exact Memory.subsumes_refl _
  | step_par_left _ _ _ ih => exact ih
  | step_par_right _ _ _ ih => exact ih
  | step_write_true hx _ | step_write_false hx _ =>
    exact Memory.update_mcell_subsumes _ _ _ _ ⟨_, hx⟩
  | step_alloc _ hfresh => exact Memory.extend_mcell_subsumes _ _ _ hfresh
  | step_drop hx => exact Memory.drop_mcell_subsumes _ _ ⟨_, hx⟩
  | step_ctx_letin _ ih | step_ctx_unpack _ ih => exact ih
  | step_lift hv hwf hfresh => exact Memory.extend_subsumes _ _ _ hwf rfl hfresh

/-- A mode-carrying external touch forgets to a plain external touch. -/
theorem Trace.extTouchesFrom_of_mode {A : List Nat} {l : Nat} {cm : CapMode} {t : Trace}
    (h : Trace.extTouchesFromMode A l cm t) : Trace.extTouchesFrom A l t := by
  induction t generalizing A with
  | nil => exact h
  | cons it t ih =>
    cases it with
    | alloc l' => exact ih h
    | access mu l' =>
      rcases h with ⟨h1, h2, _⟩ | h
      · exact Or.inl ⟨h1, h2⟩
      · exact Or.inr (ih h)
    | dealloc l' =>
      rcases h with ⟨h1, h2, _⟩ | h
      · exact Or.inl ⟨h1, h2⟩
      · exact Or.inr (ih h)

/-- An external touch (with mode) is in particular a touch. -/
theorem Trace.touched_of_extTouchesMode {t : Trace} {l : Nat} {cm : CapMode}
    (h : Trace.extTouchesMode t l cm) : Trace.touched t l :=
  Trace.touched_of_extTouches (Trace.extTouchesFrom_of_mode h)

/-- An external touch in a prefix is an external touch of the whole. -/
theorem Trace.extTouchesMode_append_left {ta1 ta2 : Trace} {l : Nat} {cm : CapMode}
    (h : Trace.extTouchesMode ta1 l cm) : Trace.extTouchesMode (ta1 ++ ta2) l cm := by
  have h' : cm ∈ Trace.extSeq l ta1 := Trace.mem_extSeqFrom_iff.mpr h
  refine Trace.mem_extSeqFrom_iff.mp ?_
  show cm ∈ Trace.extSeqFrom [] l (ta1 ++ ta2)
  rw [Trace.extSeqFrom_append]
  exact List.mem_append_left _ h'

/-- An external touch in a suffix, of a cell not allocated by the prefix, is an external
  touch of the whole. -/
theorem Trace.extTouchesMode_append_right {ta1 ta2 : Trace} {l : Nat} {cm : CapMode}
    (hnal : ¬ Trace.allocd ta1 l) (h : Trace.extTouchesMode ta2 l cm) :
    Trace.extTouchesMode (ta1 ++ ta2) l cm := by
  have h' : cm ∈ Trace.extSeq l ta2 := Trace.mem_extSeqFrom_iff.mpr h
  have hnotin : l ∉ Trace.allocList ta1 := fun hin => hnal (Trace.mem_allocList.mp hin)
  refine Trace.mem_extSeqFrom_iff.mp ?_
  show cm ∈ Trace.extSeqFrom [] l (ta1 ++ ta2)
  rw [Trace.extSeqFrom_append]
  refine List.mem_append_right _ ?_
  rw [Trace.extSeqFrom_mem_self (A2 := []) (iff_of_false (by simp [hnotin]) (by simp))]
  exact h'

/-- **Sub-trace non-interference (prefix).** -/
theorem Trace.noninterfere_append_left {ta1 ta2 tb : Trace}
    (h : Trace.Noninterfere (ta1 ++ ta2) tb) : Trace.Noninterfere ta1 tb :=
  fun l cm1 cm2 h1 htb => h l cm1 cm2 (Trace.extTouchesMode_append_left h1) htb

/-- **Sub-trace non-interference (suffix), operational.**  The suffix of a left run still
  does not interfere with the right step `tb`: a cell the suffix externally touches is either
  not allocated by the prefix (lift to the whole, use the full non-interference) or freshly
  allocated by the prefix — in which case it is absent in `mb` (`alloc_fresh`), hence absent
  in `m ⊆ mb`, so the right step (touching only present cells) never touches it. -/
theorem Trace.noninterfere_append_right_step {ta1 ta2 tb : Trace}
    {m mb mb1 : Memory} {eR eR' eL eL1 : Exp {}}
    (h : Trace.Noninterfere (ta1 ++ ta2) tb)
    (hstep : Step tb m eR mb eR') (h1 : SeqStep ta1 mb eL mb1 eL1) :
    Trace.Noninterfere ta2 tb := by
  intro l cm1 cm2 h2 htb
  by_cases hal : Trace.allocd ta1 l
  · exfalso
    have hpres : m.lookup l ≠ none :=
      step_touched_present hstep (Trace.touched_of_extTouchesMode htb)
    have hfreshb : mb.lookup l = none := SeqStep.alloc_fresh h1 hal
    rcases hm : m.lookup l with _ | cc
    · exact hpres hm
    · obtain ⟨c', hc', _⟩ := Step.subsumes hstep l cc hm
      rw [Memory.lookup, hc'] at hfreshb; cases hfreshb
  · exact h l cm1 cm2 (Trace.extTouchesMode_append_right hal h2) htb

/-- **Step-vs-run diamond.**  A right step (`eR : m → mb`) commutes past a separated left
  run (`eL : mb → mLfin`): `eL` runs FIRST from `m` (to some `mc`) and the SAME `eR`-step
  fires from `mc`, reaching the SAME `mLfin`.  A fold of `step_step_swap` over the run,
  threading the operational sub-trace non-interference. -/
theorem step_reduce_swap {tb ta : Trace} {m mb mLfin : Memory} {eR eR' eL eLres : Exp {}}
    (hstep : Step tb m eR mb eR')
    (hrun : SeqReduce ta mb eL mLfin eLres)
    (hsep : Trace.Noninterfere ta tb)
    (hwfL : Exp.WfInHeap eL m.heap)
    (hwfR : Exp.WfInHeap eR m.heap) :
    ∃ mc, SeqReduce ta m eL mc eLres ∧ Step tb mc eR mLfin eR' := by
  induction hrun generalizing m eR' with
  | refl => exact ⟨m, SeqReduce.refl, hstep⟩
  | step h1 hrest ih =>
    obtain ⟨mc1, h1', hstep'⟩ :=
      step_step_swap hstep h1 (Trace.noninterfere_append_left hsep) hwfL hwfR
    obtain ⟨mc, hrest', hstepf⟩ :=
      ih hstep' (Trace.noninterfere_append_right_step hsep hstep h1)
        (step_preserves_wf h1' hwfL)
        (Exp.wf_monotonic (step_memory_monotonic h1') hwfR)
    exact ⟨mc, SeqReduce.step h1' hrest', hstepf⟩

/-! ## Standardization assembly

  With the diamond in hand, standardization reorders an interleaving `Reduce` into the
  canonical left-first `SeqReduce`.  The engine is `absorb`: prepend a single (possibly
  premature) interleaving `Step` to a `SeqReduce` and recover a `SeqReduce` up to
  `Trace.Equiv`.  Because `SeqReduce` is a `Prop` (no length function), the well-founded
  recursion of `absorb` runs on a step-indexed copy `SeqReduceN`. -/

/-- An answer is a normal form: it has no sequential step. -/
theorem SeqStep.not_isAns {t : Trace} {m m' : Memory} {a e' : Exp {}}
    (hstep : SeqStep t m a m' e') (hans : a.IsAns) : False := by
  cases hans with
  | is_val hv => cases hv <;> cases hstep
  | is_var => cases hstep

/-- Step-indexed `SeqReduce`: the index counts the sequential steps, giving a `Nat`
  measure for well-founded recursion (`SeqReduce` itself is a `Prop`, so it admits no
  length function). -/
inductive SeqReduceN : Nat → Trace → Memory → Exp {} → Memory → Exp {} → Prop where
| refl : SeqReduceN 0 [] m e m e
| step : SeqStep t1 m1 e1 m2 e2 → SeqReduceN n t2 m2 e2 m3 e3 →
    SeqReduceN (n + 1) (t1 ++ t2) m1 e1 m3 e3

/-- Forget the step index. -/
theorem SeqReduceN.toSeqReduce {n : Nat} {t : Trace} {m m' : Memory} {e e' : Exp {}}
    (h : SeqReduceN n t m e m' e') : SeqReduce t m e m' e' := by
  induction h with
  | refl => exact SeqReduce.refl
  | step h1 _ ih => exact SeqReduce.step h1 ih

/-- Every `SeqReduce` carries a step index. -/
theorem SeqReduce.toN {t : Trace} {m m' : Memory} {e e' : Exp {}}
    (h : SeqReduce t m e m' e') : ∃ n, SeqReduceN n t m e m' e' := by
  induction h with
  | refl => exact ⟨0, SeqReduceN.refl⟩
  | step h1 _ ih => obtain ⟨n, hn⟩ := ih; exact ⟨n + 1, SeqReduceN.step h1 hn⟩

/-- A step-indexed run from an answer is the trivial one. -/
theorem SeqReduceN.eq_of_isAns {n : Nat} {t : Trace} {m m' : Memory} {a a' : Exp {}}
    (h : SeqReduceN n t m a m' a') (hans : a.IsAns) : n = 0 ∧ t = [] ∧ m' = m ∧ a' = a := by
  cases h with
  | refl => exact ⟨rfl, rfl, rfl, rfl⟩
  | step h1 _ => exact (SeqStep.not_isAns h1 hans).elim

/-- `Trace.Equiv` is a congruence for a common prefix. -/
theorem Trace.Equiv.append_left_congr {t1 t2 t2' : Trace} (h : Trace.Equiv t2 t2') :
    Trace.Equiv (t1 ++ t2) (t1 ++ t2') := by
  intro l
  change Trace.extSeqFrom [] l (t1 ++ t2) = Trace.extSeqFrom [] l (t1 ++ t2')
  rw [Trace.extSeqFrom_append, Trace.extSeqFrom_append]
  congr 1
  rw [Trace.extSeqFrom_eq_ite (A := Trace.allocList t1 ++ []) (t := t2),
      Trace.extSeqFrom_eq_ite (A := Trace.allocList t1 ++ []) (t := t2')]
  by_cases hl : l ∈ Trace.allocList t1 ++ []
  · rw [if_pos hl, if_pos hl]
  · rw [if_neg hl, if_neg hl]; exact h l

/-- **`par` decomposition.**  A sequential run of `par D1 D2 eL eR` to an answer splits into
  a left run (`eL` to an answer `aL`), then a right run (`eR` to an answer `aR`), then the
  join to `.unit` — the left-first schedule `SeqStep` enforces.  Returned with step indices
  summing to strictly less than the whole (the join step is dropped), the measure that drives
  `absorb`. -/
theorem SeqReduceN.par_inv : ∀ {n : Nat} {t : Trace} {m mf : Memory} {D1 D2 : CaptureSet {}}
    {eL eR a : Exp {}},
    SeqReduceN n t m (.par D1 D2 eL eR) mf a → a.IsAns →
    ∃ nL tL mmid aL nR tR aR,
      SeqReduceN nL tL m eL mmid aL ∧ aL.IsAns ∧
      SeqReduceN nR tR mmid eR mf aR ∧ aR.IsAns ∧
      a = .unit ∧ t = tL ++ tR ∧ nL + nR < n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ihn =>
    intro t m mf D1 D2 eL eR a hred hans
    cases hred with
    | refl => cases hans with | is_val hv => cases hv
    | step h1 hrest =>
      cases h1 with
      | step_par_left inner =>
        obtain ⟨nL', tL', mmid, aL, nR, tR, aR, hredL, haL, hredR, haR, hau, ht2, hlt⟩ :=
          ihn _ (Nat.lt_succ_self _) hrest hans
        exact ⟨nL' + 1, _, mmid, aL, nR, tR, aR, SeqReduceN.step inner hredL, haL,
          hredR, haR, hau, by rw [ht2, List.append_assoc], by omega⟩
      | step_par_right haL inner =>
        obtain ⟨nL', tL', mmid, aL, nR', tR', aR, hredL, _, hredR, haR, hau, ht2, hlt⟩ :=
          ihn _ (Nat.lt_succ_self _) hrest hans
        obtain ⟨_, htL0, hmmideq, _⟩ := hredL.eq_of_isAns haL
        subst htL0; subst hmmideq
        exact ⟨0, [], m, eL, nR' + 1, _, aR, SeqReduceN.refl, haL,
          SeqReduceN.step inner hredR, haR, hau, by rw [ht2]; rfl, by omega⟩
      | step_par_join hL hR =>
        obtain ⟨_, ht20, hmfeq, haeq⟩ :=
          hrest.eq_of_isAns (Exp.IsAns.is_val Exp.IsVal.unit)
        subst ht20; subst hmfeq
        exact ⟨0, [], mf, eL, 0, [], eR, SeqReduceN.refl, hL, SeqReduceN.refl, hR,
          haeq, rfl, by omega⟩

/-- **`letin` decomposition.**  A sequential run of `letin eh ek` to an answer runs the head
  `eh` to a simple answer `vh`, then continues (`lift`/`rename` then `ek`).  The head run's
  index is strictly smaller, the measure for `absorb`. -/
theorem SeqReduceN.letin_inv : ∀ {n : Nat} {t : Trace} {m mf : Memory}
    {eh a : Exp {}} {ek : Exp ({},x)},
    SeqReduceN n t m (.letin eh ek) mf a → a.IsAns →
    ∃ nh th mh vh trest, SeqReduceN nh th m eh mh vh ∧ vh.IsSimpleAns ∧
      SeqReduce trest mh (.letin vh ek) mf a ∧ t = th ++ trest ∧ nh < n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ihn =>
    intro t m mf eh ek a hred hans
    cases hred with
    | refl => cases hans with | is_val hv => cases hv
    | step h1 hrest =>
      cases h1 with
      | step_ctx_letin inner =>
        obtain ⟨nh', th', mh, vh, trest, hh, hvh, hrestr, ht2, hlt⟩ :=
          ihn _ (Nat.lt_succ_self _) hrest hans
        exact ⟨nh' + 1, _, mh, vh, trest, SeqReduceN.step inner hh, hvh, hrestr,
          by rw [ht2, List.append_assoc], by omega⟩
      | step_rename =>
        exact ⟨0, [], m, _, _, SeqReduceN.refl, Exp.IsSimpleAns.is_var,
          SeqReduce.step SeqStep.step_rename hrest.toSeqReduce, by simp, by omega⟩
      | step_lift hv hwf_v hfresh =>
        exact ⟨0, [], m, _, _, SeqReduceN.refl, Exp.IsSimpleAns.is_simple_val hv,
          SeqReduce.step (SeqStep.step_lift hv hwf_v hfresh) hrest.toSeqReduce, by simp, by omega⟩

/-- **`unpack` decomposition.**  A sequential run of `unpack eh ek` to an answer runs the head
  `eh` to a `pack`, then continues (`step_unpack` then `ek`). -/
theorem SeqReduceN.unpack_inv : ∀ {n : Nat} {t : Trace} {m mf : Memory}
    {eh a : Exp {}} {ek : Exp ({},C,x)},
    SeqReduceN n t m (.unpack eh ek) mf a → a.IsAns →
    ∃ nh th mh cs x trest, SeqReduceN nh th m eh mh (.pack cs x) ∧
      SeqReduce trest mh (.unpack (.pack cs x) ek) mf a ∧ t = th ++ trest ∧ nh < n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ihn =>
    intro t m mf eh ek a hred hans
    cases hred with
    | refl => cases hans with | is_val hv => cases hv
    | step h1 hrest =>
      cases h1 with
      | step_ctx_unpack inner =>
        obtain ⟨nh', th', mh, cs, x, trest, hh, hrestr, ht2, hlt⟩ :=
          ihn _ (Nat.lt_succ_self _) hrest hans
        exact ⟨nh' + 1, _, mh, cs, x, trest, SeqReduceN.step inner hh, hrestr,
          by rw [ht2, List.append_assoc], by omega⟩
      | step_unpack =>
        exact ⟨0, [], m, _, _, _, SeqReduceN.refl,
          SeqReduce.step SeqStep.step_unpack hrest.toSeqReduce, by simp, by omega⟩

/-- Coverage entails membership (at some mode). -/
theorem CapabilitySet.covers_imp_hasmem {cm : CapMode} {l : Nat} {C : CapabilitySet}
    (h : C.covers cm l) : ∃ mode, C.hasmem mode l := by
  induction h with
  | here _ => exact ⟨_, CapabilitySet.hasmem.here⟩
  | left _ ih => obtain ⟨mode, hm⟩ := ih; exact ⟨mode, CapabilitySet.hasmem.left hm⟩
  | right _ ih => obtain ⟨mode, hm⟩ := ih; exact ⟨mode, CapabilitySet.hasmem.right hm⟩

/-- A reachability-bounded trace does not externally touch a cell fresh in `m`: such a
  cell is outside the reachability's domain. -/
theorem fresh_not_extSeq {t : Trace} {Cs : CaptureSet {}} {m : Memory} {l : Nat}
    (htok : TraceOk t (Cs.reachability m)) (hfresh : m.heap l = none) :
    Trace.extSeq l t = [] := by
  rcases he : Trace.extSeq l t with _ | ⟨cm, rest⟩
  · rfl
  · exfalso
    have hmem : cm ∈ Trace.extSeq l t := he ▸ List.mem_cons_self ..
    have hext : Trace.extTouches t l :=
      Trace.extTouchesFrom_of_mode (Trace.mem_extSeqFrom_iff.mp hmem)
    obtain ⟨mode, hcov⟩ := TraceOk.covers_of_extTouches htok hext
    obtain ⟨mode', hhas⟩ := CapabilitySet.covers_imp_hasmem hcov
    exact CaptureSet.reachability_dom hhas hfresh

/-- A sequential run keeps fresh a cell its trace does not allocate. -/
theorem SeqReduce.alloc_fresh {t : Trace} {m m' : Memory} {e e' : Exp {}} {l : Nat}
    (hred : SeqReduce t m e m' e') (hal : Trace.allocd t l) : m.lookup l = none := by
  induction hred with
  | refl => simp only [Trace.allocd] at hal
  | step h1 hrest ih =>
    rw [Trace.allocd_append] at hal
    rcases hal with hal | hal
    · exact SeqStep.alloc_fresh h1 hal
    · exact Heap.none_of_subsumes_none (step_memory_monotonic h1) (ih hal)

/-- A genuine interleaving step keeps fresh a cell its trace does not allocate. -/
theorem Step.alloc_fresh {t : Trace} {m m' : Memory} {e e' : Exp {}} {l : Nat}
    (h : Step t m e m' e') (hal : Trace.allocd t l) : m.lookup l = none := by
  induction h with
  | step_apply _ | step_invoke _ _ | step_tapply _ | step_capply _ | step_unwrap _
  | step_cond_var_true _ | step_cond_var_false _ | step_read _ _
  | step_write_true _ _ | step_write_false _ _ | step_drop _
  | step_rename | step_unpack | step_par_join _ _ | step_lift _ _ _ =>
    simp only [Trace.allocd] at hal
  | step_alloc _ hfresh =>
    simp only [Trace.allocd, or_false] at hal
    rw [Memory.lookup, hal]; exact hfresh
  | step_ctx_letin _ ih | step_ctx_unpack _ ih
  | step_par_left _ _ _ ih | step_par_right _ _ _ ih => exact ih hal

/-- `Trace.Equiv` is a congruence for a common suffix, PROVIDED the two prefixes allocate
  the same cells (external equivalence alone is insufficient — an allocated cell shadows a
  later external touch).  Allocation equivalence is preserved by the diamond, so this holds
  for every reordering `absorb` produces. -/
theorem Trace.Equiv.append_right_congr {t1 t1' t2 : Trace} (heq : Trace.Equiv t1 t1')
    (hae : ∀ l, Trace.allocd t1 l ↔ Trace.allocd t1' l) :
    Trace.Equiv (t1 ++ t2) (t1' ++ t2) := by
  intro l
  change Trace.extSeqFrom [] l (t1 ++ t2) = Trace.extSeqFrom [] l (t1' ++ t2)
  rw [Trace.extSeqFrom_append, Trace.extSeqFrom_append,
      show Trace.extSeqFrom [] l t1 = Trace.extSeqFrom [] l t1' from heq l]
  congr 1
  apply Trace.extSeqFrom_mem_self
  simp only [List.append_nil]
  rw [Trace.mem_allocList, Trace.mem_allocList]
  exact hae l

/-- The head of a `Safe` `letin` is safe. -/
theorem Safe.letin_inv_left {m : Memory} {eh : Exp {}} {ek : Exp ({},x)}
    (h : Safe m (.letin eh ek)) : Safe m eh := by
  cases h with
  | letin hsa _ _ _ => exact hsa
  | ans hh => cases hh with | is_val hv => cases hv

/-- The head of a `Safe` `unpack` is safe. -/
theorem Safe.unpack_inv_left {m : Memory} {eh : Exp {}} {ek : Exp ({},C,x)}
    (h : Safe m (.unpack eh ek)) : Safe m eh := by
  cases h with
  | unpack hsa _ _ => exact hsa
  | ans hh => cases hh with | is_val hv => cases hv

/-- A simple answer is an answer. -/
theorem Exp.IsSimpleAns.toIsAns {e : Exp {}} (h : e.IsSimpleAns) : e.IsAns := by
  cases h with
  | is_simple_val hv => exact Exp.IsAns.is_val (Exp.isVal_of_isSimpleVal hv)
  | is_var => exact Exp.IsAns.is_var

/-- Trace non-interference is symmetric. -/
theorem Trace.Noninterfere.symm {t s : Trace} (h : Trace.Noninterfere t s) :
    Trace.Noninterfere s t :=
  fun l cm1 cm2 h1 h2 => ⟨(h l cm2 cm1 h2 h1).2, (h l cm2 cm1 h2 h1).1⟩

set_option maxHeartbeats 1000000 in
-- The single monolithic induction has 21 step cases; the `par` cases each thread the diamond
-- plus the 11-field `Safe.par` carrier extraction, so it exceeds the default heartbeat budget.
/-- **Absorb a step into a sequential run.**  Prepending a (possibly premature, interleaving)
  `Step` to a left-first `SeqReduce` recovers a left-first `SeqReduce` reaching the SAME final
  state, up to `Trace.Equiv` (with the same allocations).  The non-structural work is at `par`
  nodes: a premature right step is bubbled past the left branch's run by the small-step diamond
  `step_reduce_swap`, the discharge of whose non-interference comes from the `Safe.par` carrier.
  Well-founded on the run's step index. -/
theorem absorb : ∀ {n : Nat} {t1 t2 : Trace} {m0 m1 mf : Memory} {e e1 a : Exp {}},
    SeqReduceN n t2 m1 e1 mf a → Step t1 m0 e m1 e1 → Safe m0 e → Exp.WfInHeap e m0.heap →
    a.IsAns → ∃ t', SeqReduce t' m0 e mf a ∧ Trace.Equiv (t1 ++ t2) t' ∧
      (∀ l, Trace.allocd (t1 ++ t2) l ↔ Trace.allocd t' l) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ihn =>
    intro t1 t2 m0 m1 mf e e1 a hred hstep hsafe hwf hans
    cases hstep with
    | step_apply hlk =>
      exact ⟨_, SeqReduce.step (SeqStep.step_apply hlk) hred.toSeqReduce,
        Trace.Equiv.refl _, fun l => Iff.rfl⟩
    | step_invoke h1 h2 =>
      exact ⟨_, SeqReduce.step (SeqStep.step_invoke h1 h2) hred.toSeqReduce,
        Trace.Equiv.refl _, fun l => Iff.rfl⟩
    | step_tapply hlk =>
      exact ⟨_, SeqReduce.step (SeqStep.step_tapply hlk) hred.toSeqReduce,
        Trace.Equiv.refl _, fun l => Iff.rfl⟩
    | step_capply hlk =>
      exact ⟨_, SeqReduce.step (SeqStep.step_capply hlk) hred.toSeqReduce,
        Trace.Equiv.refl _, fun l => Iff.rfl⟩
    | step_unwrap hlk =>
      exact ⟨_, SeqReduce.step (SeqStep.step_unwrap hlk) hred.toSeqReduce,
        Trace.Equiv.refl _, fun l => Iff.rfl⟩
    | step_cond_var_true hlk =>
      exact ⟨_, SeqReduce.step (SeqStep.step_cond_var_true hlk) hred.toSeqReduce,
        Trace.Equiv.refl _, fun l => Iff.rfl⟩
    | step_cond_var_false hlk =>
      exact ⟨_, SeqReduce.step (SeqStep.step_cond_var_false hlk) hred.toSeqReduce,
        Trace.Equiv.refl _, fun l => Iff.rfl⟩
    | step_read h1 h2 =>
      exact ⟨_, SeqReduce.step (SeqStep.step_read h1 h2) hred.toSeqReduce,
        Trace.Equiv.refl _, fun l => Iff.rfl⟩
    | step_write_true h1 h2 =>
      exact ⟨_, SeqReduce.step (SeqStep.step_write_true h1 h2) hred.toSeqReduce,
        Trace.Equiv.refl _, fun l => Iff.rfl⟩
    | step_write_false h1 h2 =>
      exact ⟨_, SeqReduce.step (SeqStep.step_write_false h1 h2) hred.toSeqReduce,
        Trace.Equiv.refl _, fun l => Iff.rfl⟩
    | step_alloc h1 h2 =>
      exact ⟨_, SeqReduce.step (SeqStep.step_alloc h1 h2) hred.toSeqReduce,
        Trace.Equiv.refl _, fun l => Iff.rfl⟩
    | step_drop hx =>
      exact ⟨_, SeqReduce.step (SeqStep.step_drop hx) hred.toSeqReduce,
        Trace.Equiv.refl _, fun l => Iff.rfl⟩
    | step_rename =>
      exact ⟨_, SeqReduce.step SeqStep.step_rename hred.toSeqReduce,
        Trace.Equiv.refl _, fun l => Iff.rfl⟩
    | step_lift hv hwf_v hfresh =>
      exact ⟨_, SeqReduce.step (SeqStep.step_lift hv hwf_v hfresh) hred.toSeqReduce,
        Trace.Equiv.refl _, fun l => Iff.rfl⟩
    | step_unpack =>
      exact ⟨_, SeqReduce.step SeqStep.step_unpack hred.toSeqReduce,
        Trace.Equiv.refl _, fun l => Iff.rfl⟩
    | step_par_join h1 h2 =>
      exact ⟨_, SeqReduce.step (SeqStep.step_par_join h1 h2) hred.toSeqReduce,
        Trace.Equiv.refl _, fun l => Iff.rfl⟩
    | step_ctx_letin inner =>
      obtain ⟨nh', th', mh, vh, trest, hh, hvh, hrestr, ht2, hlt⟩ := hred.letin_inv hans
      subst ht2
      obtain ⟨hwf_eh, _⟩ := Exp.wf_inv_letin hwf
      obtain ⟨th'', hehred, heqh, haeh⟩ :=
        ihn nh' (by omega) hh inner (Safe.letin_inv_left hsafe) hwf_eh hvh.toIsAns
      refine ⟨th'' ++ trest, seqreduce_trans (seqreduce_ctx_letin hehred) hrestr, ?_, ?_⟩
      · rw [show t1 ++ (th' ++ trest) = (t1 ++ th') ++ trest from by rw [List.append_assoc]]
        exact Trace.Equiv.append_right_congr heqh haeh
      · intro l
        calc Trace.allocd (t1 ++ (th' ++ trest)) l
            ↔ Trace.allocd (t1 ++ th') l ∨ Trace.allocd trest l := by
              rw [← List.append_assoc]; exact Trace.allocd_append
          _ ↔ Trace.allocd th'' l ∨ Trace.allocd trest l := or_congr_left (haeh l)
          _ ↔ Trace.allocd (th'' ++ trest) l := Trace.allocd_append.symm
    | step_ctx_unpack inner =>
      obtain ⟨nh', th', mh, cs, x, trest, hh, hrestr, ht2, hlt⟩ := hred.unpack_inv hans
      subst ht2
      obtain ⟨hwf_eh, _⟩ := Exp.wf_inv_unpack hwf
      obtain ⟨th'', hehred, heqh, haeh⟩ :=
        ihn nh' (by omega) hh inner (Safe.unpack_inv_left hsafe) hwf_eh
          (Exp.IsAns.is_val Exp.IsVal.pack)
      refine ⟨th'' ++ trest, seqreduce_trans (seqreduce_ctx_unpack hehred) hrestr, ?_, ?_⟩
      · rw [show t1 ++ (th' ++ trest) = (t1 ++ th') ++ trest from by rw [List.append_assoc]]
        exact Trace.Equiv.append_right_congr heqh haeh
      · intro l
        calc Trace.allocd (t1 ++ (th' ++ trest)) l
            ↔ Trace.allocd (t1 ++ th') l ∨ Trace.allocd trest l := by
              rw [← List.append_assoc]; exact Trace.allocd_append
          _ ↔ Trace.allocd th'' l ∨ Trace.allocd trest l := or_congr_left (haeh l)
          _ ↔ Trace.allocd (th'' ++ trest) l := Trace.allocd_append.symm
    | step_par_left inner ht hni_g =>
      obtain ⟨nL', tL', mmid, aL, nR, tR, aR, hredL, haL, hredR, haR, hau, ht2, hlt⟩ :=
        hred.par_inv hans
      subst ht2
      obtain ⟨hwf_eL, _⟩ := Exp.wf_inv_par hwf
      obtain ⟨tL'', hredL'', heqL, haeL⟩ :=
        ihn nL' (by omega) hredL inner (Safe.par_inv_left hsafe) hwf_eL haL
      refine ⟨tL'' ++ tR, ?_, ?_, ?_⟩
      · rw [hau, show (tL'' ++ tR) = (tL'' ++ tR) ++ ([] ++ []) from by simp]
        exact seqreduce_trans (seqreduce_trans (seqreduce_par_left hredL'')
          (seqreduce_par_right haL hredR.toSeqReduce))
          (SeqReduce.step (SeqStep.step_par_join haL haR) SeqReduce.refl)
      · rw [show t1 ++ (tL' ++ tR) = (t1 ++ tL') ++ tR from by rw [List.append_assoc]]
        exact Trace.Equiv.append_right_congr heqL haeL
      · intro l
        calc Trace.allocd (t1 ++ (tL' ++ tR)) l
            ↔ Trace.allocd (t1 ++ tL') l ∨ Trace.allocd tR l := by
              rw [← List.append_assoc]; exact Trace.allocd_append
          _ ↔ Trace.allocd tL'' l ∨ Trace.allocd tR l := or_congr_left (haeL l)
          _ ↔ Trace.allocd (tL'' ++ tR) l := Trace.allocd_append.symm
    | step_par_right ht hni_g inner =>
      obtain ⟨nL, tL, mmid, aL, nR', tR', aR, hredL, haL, hredR, haR, hau, ht2, hlt⟩ :=
        hred.par_inv hans
      subst ht2
      obtain ⟨hwf_eL, hwf_eR⟩ := Exp.wf_inv_par hwf
      cases hsafe with
      | ans hh' => cases hh' with | is_val hv => cases hv
      | par hse_a h2 hb1 hb2 hrs1 hrs2 hpres1 hpres2 hcov1 hcov2 hni =>
        have hsub1 : m1.subsumes m0 := Step.subsumes inner
        have hbsL : BigStep m1 _ tL aL mmid :=
          reduce_to_bigstep hredL.toSeqReduce haL
        have htokL : TraceOk tL _ := hb1 hsub1 (Exp.wf_monotonic hsub1 hwf_eL) hbsL
        have htok1 : TraceOk t1 _ := TraceOk.mono hcov2.2 ht
        have hsep : Trace.Noninterfere tL t1 := traceOk_noninterfere htokL htok1 hni
        obtain ⟨mc, hredL', hstep1'⟩ :=
          step_reduce_swap inner hredL.toSeqReduce hsep hwf_eL hwf_eR
        have hbsL0 : BigStep m0 _ tL aL mc := reduce_to_bigstep hredL' haL
        have hsafe_eR : Safe mc _ := h2 hbsL0
        have hwf_eR_mc : Exp.WfInHeap _ mc.heap :=
          Exp.wf_monotonic (reduce_memory_monotonic hredL') hwf_eR
        obtain ⟨tR'', hredR'', heqR, haeR⟩ :=
          ihn nR' (by omega) hredR hstep1' hsafe_eR hwf_eR_mc haR
        -- freshness for the trace commute
        have hf1 : ∀ l, Trace.allocd tL l → Trace.extSeq l t1 = [] := fun l hal =>
          fresh_not_extSeq ht
            (Heap.none_of_subsumes_none hsub1 (SeqReduce.alloc_fresh hredL.toSeqReduce hal))
        have hf2 : ∀ l, Trace.allocd t1 l → Trace.extSeq l tL = [] := fun l hal =>
          fresh_not_extSeq (TraceOk.mono hcov1.1 htokL) (Step.alloc_fresh inner hal)
        have hcomm : Trace.Equiv (t1 ++ tL) (tL ++ t1) :=
          Trace.equiv_comm_of_noninterfere hsep.symm hf1 hf2
        have hcommAE : ∀ l, Trace.allocd (t1 ++ tL) l ↔ Trace.allocd (tL ++ t1) l := by
          intro l; rw [Trace.allocd_append, Trace.allocd_append]; exact or_comm
        refine ⟨tL ++ tR'', ?_, ?_, ?_⟩
        · rw [hau, show (tL ++ tR'') = (tL ++ tR'') ++ ([] ++ []) from by simp]
          exact seqreduce_trans (seqreduce_trans (seqreduce_par_left hredL')
            (seqreduce_par_right haL hredR''))
            (SeqReduce.step (SeqStep.step_par_join haL haR) SeqReduce.refl)
        · -- Equiv (t1 ++ (tL ++ tR')) (tL ++ tR'')
          have step1 : Trace.Equiv (t1 ++ (tL ++ tR')) (tL ++ (t1 ++ tR')) := by
            rw [← List.append_assoc, ← List.append_assoc]
            exact Trace.Equiv.append_right_congr hcomm hcommAE
          have step2 : Trace.Equiv (tL ++ (t1 ++ tR')) (tL ++ tR'') :=
            Trace.Equiv.append_left_congr heqR
          exact step1.trans step2
        · intro l
          calc Trace.allocd (t1 ++ (tL ++ tR')) l
              ↔ Trace.allocd t1 l ∨ Trace.allocd tL l ∨ Trace.allocd tR' l := by
                rw [Trace.allocd_append, Trace.allocd_append]
            _ ↔ Trace.allocd tL l ∨ Trace.allocd t1 l ∨ Trace.allocd tR' l := or_left_comm
            _ ↔ Trace.allocd tL l ∨ Trace.allocd (t1 ++ tR') l := by rw [Trace.allocd_append]
            _ ↔ Trace.allocd tL l ∨ Trace.allocd tR'' l := or_congr_right (haeR l)
            _ ↔ Trace.allocd (tL ++ tR'') l := Trace.allocd_append.symm

/-- A genuine interleaving step keeps a cell its trace allocates present afterwards. -/
theorem Step.allocd_present {t : Trace} {m1 m2 : Memory} {e1 e2 : Exp {}} {l : Nat}
    (hstep : Step t m1 e1 m2 e2) (hal : Trace.allocd t l) : m2.heap l ≠ none := by
  induction hstep with
  | step_apply _ | step_invoke _ _ | step_tapply _ | step_capply _ | step_unwrap _
  | step_cond_var_true _ | step_cond_var_false _ | step_read _ _
  | step_write_true _ _ | step_write_false _ _ | step_drop _
  | step_rename | step_unpack | step_par_join _ _ | step_lift _ _ _ =>
    simp only [Trace.allocd] at hal
  | step_alloc _ hfresh =>
    simp only [Trace.allocd, or_false] at hal
    subst hal
    simp [Memory.extend_mcell, Heap.extend_mcell]
  | step_ctx_letin _ ih | step_ctx_unpack _ ih
  | step_par_left _ _ _ ih | step_par_right _ _ _ ih => exact ih hal

/-- **Genuine interleaving step preserves well-formedness.**  Well-formedness is structural
  (no separation), so the leaf cases reduce to the sequential `step_preserves_wf` and the
  congruences rebuild via the recursive call. -/
theorem Step.preserves_wf {t : Trace} {m1 m2 : Memory} {e1 e2 : Exp {}}
    (hstep : Step t m1 e1 m2 e2) (hwf : e1.WfInHeap m1.heap) : e2.WfInHeap m2.heap := by
  induction hstep with
  | step_apply hlk => exact step_preserves_wf (SeqStep.step_apply hlk) hwf
  | step_invoke h1 h2 => exact step_preserves_wf (SeqStep.step_invoke h1 h2) hwf
  | step_tapply hlk => exact step_preserves_wf (SeqStep.step_tapply hlk) hwf
  | step_capply hlk => exact step_preserves_wf (SeqStep.step_capply hlk) hwf
  | step_unwrap hlk => exact step_preserves_wf (SeqStep.step_unwrap hlk) hwf
  | step_cond_var_true hlk => exact step_preserves_wf (SeqStep.step_cond_var_true hlk) hwf
  | step_cond_var_false hlk => exact step_preserves_wf (SeqStep.step_cond_var_false hlk) hwf
  | step_read h1 h2 => exact step_preserves_wf (SeqStep.step_read h1 h2) hwf
  | step_write_true h1 h2 => exact step_preserves_wf (SeqStep.step_write_true h1 h2) hwf
  | step_write_false h1 h2 => exact step_preserves_wf (SeqStep.step_write_false h1 h2) hwf
  | step_alloc h1 h2 => exact step_preserves_wf (SeqStep.step_alloc h1 h2) hwf
  | step_drop hx => exact step_preserves_wf (SeqStep.step_drop hx) hwf
  | step_rename => exact step_preserves_wf SeqStep.step_rename hwf
  | step_lift hv hwf_v hfresh => exact step_preserves_wf (SeqStep.step_lift hv hwf_v hfresh) hwf
  | step_unpack => exact step_preserves_wf SeqStep.step_unpack hwf
  | step_par_join h1 h2 => exact step_preserves_wf (SeqStep.step_par_join h1 h2) hwf
  | step_ctx_letin inner ih =>
    obtain ⟨hwf1, hwf2⟩ := Exp.wf_inv_letin hwf
    exact Exp.WfInHeap.wf_letin (ih hwf1) (Exp.wf_monotonic (Step.subsumes inner) hwf2)
  | step_ctx_unpack inner ih =>
    obtain ⟨hwf1, hwf2⟩ := Exp.wf_inv_unpack hwf
    exact Exp.WfInHeap.wf_unpack (ih hwf1) (Exp.wf_monotonic (Step.subsumes inner) hwf2)
  | step_par_left inner _ _ ih =>
    cases hwf with
    | wf_par hwf_C1 hwf_C2 hwf_aL hwf_b =>
      exact Exp.WfInHeap.wf_par
        (CaptureSet.growByAllocs_wf (CaptureSet.wf_monotonic (Step.subsumes inner) hwf_C1)
          (fun l hl => Step.allocd_present inner (Trace.mem_allocList.mp hl)))
        (CaptureSet.wf_monotonic (Step.subsumes inner) hwf_C2)
        (ih hwf_aL)
        (Exp.wf_monotonic (Step.subsumes inner) hwf_b)
  | step_par_right _ _ inner ih =>
    cases hwf with
    | wf_par hwf_C1 hwf_C2 hwf_aL hwf_b =>
      exact Exp.WfInHeap.wf_par
        (CaptureSet.wf_monotonic (Step.subsumes inner) hwf_C1)
        (CaptureSet.growByAllocs_wf (CaptureSet.wf_monotonic (Step.subsumes inner) hwf_C2)
          (fun l hl => Step.allocd_present inner (Trace.mem_allocList.mp hl)))
        (Exp.wf_monotonic (Step.subsumes inner) hwf_aL)
        (ih hwf_b)

/-! ## Step-indexed big-step (`BigStepN`) — the run-size measure for genuine head-expansion

  `BigStep` is a `Prop`, so it admits no derivation-height function (large elimination is
  forbidden).  The genuine head-expansion `Step.head_expand_bigstep` needs to recurse on a
  STRICTLY SMALLER run in the premature-`par_right` case (bubble the step past the left run with
  the BigStep diamond `step_run_commute`, then head-expand the strictly-smaller right run).  A
  step-indexed mirror `BigStepN n` supplies that measure: each rule's premises sit at index `n`
  and its conclusion at `n+1`, so inverting a `BigStepN (n+1)` exposes every sub-run at `n`, and
  the recursion is plain `induction` on the index. -/

/-- Depth-indexed mirror of `BigStep`: `BigStepN n` is derivable with all premise sub-runs at
  index `n` and the conclusion at `n+1` (so `BigStepN 0` is empty, and inversion drops the
  index by one). -/
inductive BigStepN : Nat -> Memory -> Exp {} -> Trace -> Exp {} -> Memory -> Prop where
| bs_pack {n} {m : Memory} :
  BigStepN (n+1) m (.pack cs x) [] (.pack cs x) m
| bs_alloc {n} {m : Memory} {x : Nat} {b : Bool} {hv R} {l : Nat} :
  m.lookup x = some (.val ⟨if b then .btrue else .bfalse, hv, R⟩) ->
  (hfresh : m.heap l = none) ->
  BigStepN (n+1) m (.alloc (.free x)) [.alloc l]
    (.pack (.var (.M .epsilon) (.free l)) (.free l)) (m.extend_mcell l b hfresh)
| bs_val {n} {m : Memory} {v : Exp {}} :
  (hv : Exp.IsSimpleVal v) ->
  BigStepN (n+1) m v [] v m
| bs_var {n} {m : Memory} {x : Var .var {}} :
  BigStepN (n+1) m (.var x) [] (.var x) m
| bs_apply {n} {m : Memory} {x : Nat} :
  m.lookup x = some (.val ⟨.abs cs T e, hv, R⟩) ->
  BigStepN n m (e.subst (Subst.openVar y)) t v m' ->
  BigStepN (n+1) m (.app (.free x) y) t v m'
| bs_invoke {n} {m : Memory} {x : Nat} :
  m.lookup x = some (.capability .basic) ->
  m.lookup y = some (.val ⟨.unit, hv, R⟩) ->
  BigStepN (n+1) m (.app (.free x) (.free y)) [.access .epsilon x] .unit m
| bs_tapply {n} {m : Memory} {x : Nat} :
  m.lookup x = some (.val ⟨.tabs cs T0 e, hv, R⟩) ->
  BigStepN n m (e.subst (Subst.openTVar .top)) t v m' ->
  BigStepN (n+1) m (.tapp (.free x) S) t v m'
| bs_capply {n} {m : Memory} {x : Nat} :
  m.lookup x = some (.val ⟨.cabs cs B0 e, hv, R⟩) ->
  BigStepN n m (e.subst (Subst.openCVar CS)) t v m' ->
  BigStepN (n+1) m (.capp (.free x) CS) t v m'
| bs_wrap {n} {m : Memory} :
  BigStepN (n+1) m (.boxed cs Ψ e) [] (.boxed cs Ψ e) m
| bs_unwrap {n} {m : Memory} {x : Nat} :
  m.lookup x = some (.val ⟨.boxed cs Ψ e, hv, R⟩) ->
  BigStepN n m e t v m' ->
  BigStepN (n+1) m (.unwrap (.free x)) t v m'
| bs_letin_val {n} {m m1 m2 : Memory} {v : Exp {}} {l' : Nat} :
  BigStepN n m e1 t1 v m1 ->
  (hv : Exp.IsSimpleVal v) ->
  (hwf_v : Exp.WfInHeap v m1.heap) ->
  (hfresh : m1.lookup l' = none) ->
  BigStepN n (m1.extend_val l' ⟨v, hv, compute_reachability m1.heap v hv⟩ hwf_v rfl hfresh)
    (e2.subst (Subst.openVar (.free l'))) t2 v2 m2 ->
  BigStepN (n+1) m (.letin e1 e2) (t1 ++ t2) v2 m2
| bs_letin_var {n} {m m1 m2 : Memory} {x : Var .var {}} :
  BigStepN n m e1 t1 (.var x) m1 ->
  BigStepN n m1 (e2.subst (Subst.openVar x)) t2 v2 m2 ->
  BigStepN (n+1) m (.letin e1 e2) (t1 ++ t2) v2 m2
| bs_unpack {n} {m m1 m2 : Memory} {x : Var .var {}} {cs : CaptureSet {}} :
  BigStepN n m e1 t1 (.pack cs x) m1 ->
  BigStepN n m1 (e2.subst (Subst.unpack cs x)) t2 v2 m2 ->
  BigStepN (n+1) m (.unpack e1 e2) (t1 ++ t2) v2 m2
| bs_read {n} {m : Memory} {x : Nat} {b b' : Bool} :
  m.lookup x = some (.val ⟨.reader (.free y), hv, R⟩) ->
  m.lookup y = some (.capability (.mcell b .live)) ->
  BigStepN (n+1) m (.read (.free x)) [.access .ro y] (if b' then .btrue else .bfalse) m
| bs_write_true {n} {m : Memory} {x y : Nat} {b0 : Bool} {hv R} :
  (hx : m.lookup x = some (.capability (.mcell b0 .live))) ->
  m.lookup y = some (.val ⟨.btrue, hv, R⟩) ->
  BigStepN (n+1) m (.write (.free x) (.free y)) [.access .epsilon x] .unit
    (m.update_mcell x true .live ⟨b0, hx⟩)
| bs_write_false {n} {m : Memory} {x y : Nat} {b0 : Bool} {hv R} :
  (hx : m.lookup x = some (.capability (.mcell b0 .live))) ->
  m.lookup y = some (.val ⟨.bfalse, hv, R⟩) ->
  BigStepN (n+1) m (.write (.free x) (.free y)) [.access .epsilon x] .unit
    (m.update_mcell x false .live ⟨b0, hx⟩)
| bs_drop {n} {m : Memory} {x : Nat} {b : Bool} :
  (hx : m.lookup x = some (.capability (.mcell b .live))) ->
  BigStepN (n+1) m (.drop (.free x)) [.dealloc x] .unit (m.drop_mcell x ⟨b, hx⟩)
| bs_cond_true {n} {m : Memory} {x : Var .var {}} :
  resolve m.heap (.var x) = some .btrue ->
  BigStepN n m e2 t v m' ->
  BigStepN (n+1) m (.cond x e2 e3) t v m'
| bs_cond_false {n} {m : Memory} {x : Var .var {}} :
  resolve m.heap (.var x) = some .bfalse ->
  BigStepN n m e3 t v m' ->
  BigStepN (n+1) m (.cond x e2 e3) t v m'
| bs_par {n} {m m1 m2 : Memory} {v1 v2 : Exp {}} :
  BigStepN n m e1 t1 v1 m1 ->
  BigStepN n m1 e2 t2 v2 m2 ->
  BigStepN (n+1) m (.par C1 C2 e1 e2) (t1 ++ t2) .unit m2

/-- Forget the index: every `BigStepN` is a `BigStep`. -/
theorem BigStepN.toBigStep {n : Nat} {m : Memory} {e : Exp {}} {t : Trace} {v : Exp {}}
    {m' : Memory} (h : BigStepN n m e t v m') : BigStep m e t v m' := by
  induction h with
  | bs_pack => exact BigStep.bs_pack
  | bs_alloc hlk hfresh => exact BigStep.bs_alloc hlk hfresh
  | bs_val hv => exact BigStep.bs_val hv
  | bs_var => exact BigStep.bs_var
  | bs_apply hlk _ ih => exact BigStep.bs_apply hlk ih
  | bs_invoke h1 h2 => exact BigStep.bs_invoke h1 h2
  | bs_tapply hlk _ ih => exact BigStep.bs_tapply hlk ih
  | bs_capply hlk _ ih => exact BigStep.bs_capply hlk ih
  | bs_wrap => exact BigStep.bs_wrap
  | bs_unwrap hlk _ ih => exact BigStep.bs_unwrap hlk ih
  | bs_letin_val _ hv hwf_v hfresh _ ih1 ih2 => exact BigStep.bs_letin_val ih1 hv hwf_v hfresh ih2
  | bs_letin_var _ _ ih1 ih2 => exact BigStep.bs_letin_var ih1 ih2
  | bs_unpack _ _ ih1 ih2 => exact BigStep.bs_unpack ih1 ih2
  | bs_read h1 h2 => exact BigStep.bs_read h1 h2
  | bs_write_true hx hy => exact BigStep.bs_write_true hx hy
  | bs_write_false hx hy => exact BigStep.bs_write_false hx hy
  | bs_drop hx => exact BigStep.bs_drop hx
  | bs_cond_true hres _ ih => exact BigStep.bs_cond_true hres ih
  | bs_cond_false hres _ ih => exact BigStep.bs_cond_false hres ih
  | bs_par _ _ ih1 ih2 => exact BigStep.bs_par ih1 ih2

/-- Index weakening by one. -/
theorem BigStepN.mono {n : Nat} {m : Memory} {e : Exp {}} {t : Trace} {v : Exp {}}
    {m' : Memory} (h : BigStepN n m e t v m') : BigStepN (n+1) m e t v m' := by
  induction h with
  | bs_pack => exact BigStepN.bs_pack
  | bs_alloc hlk hfresh => exact BigStepN.bs_alloc hlk hfresh
  | bs_val hv => exact BigStepN.bs_val hv
  | bs_var => exact BigStepN.bs_var
  | bs_apply hlk _ ih => exact BigStepN.bs_apply hlk ih
  | bs_invoke h1 h2 => exact BigStepN.bs_invoke h1 h2
  | bs_tapply hlk _ ih => exact BigStepN.bs_tapply hlk ih
  | bs_capply hlk _ ih => exact BigStepN.bs_capply hlk ih
  | bs_wrap => exact BigStepN.bs_wrap
  | bs_unwrap hlk _ ih => exact BigStepN.bs_unwrap hlk ih
  | bs_letin_val _ hv hwf_v hfresh _ ih1 ih2 => exact BigStepN.bs_letin_val ih1 hv hwf_v hfresh ih2
  | bs_letin_var _ _ ih1 ih2 => exact BigStepN.bs_letin_var ih1 ih2
  | bs_unpack _ _ ih1 ih2 => exact BigStepN.bs_unpack ih1 ih2
  | bs_read h1 h2 => exact BigStepN.bs_read h1 h2
  | bs_write_true hx hy => exact BigStepN.bs_write_true hx hy
  | bs_write_false hx hy => exact BigStepN.bs_write_false hx hy
  | bs_drop hx => exact BigStepN.bs_drop hx
  | bs_cond_true hres _ ih => exact BigStepN.bs_cond_true hres ih
  | bs_cond_false hres _ ih => exact BigStepN.bs_cond_false hres ih
  | bs_par _ _ ih1 ih2 => exact BigStepN.bs_par ih1 ih2

/-- Index weakening (monotone). -/
theorem BigStepN.le_mono {n n' : Nat} {m : Memory} {e : Exp {}} {t : Trace} {v : Exp {}}
    {m' : Memory} (h : BigStepN n m e t v m') (hle : n ≤ n') : BigStepN n' m e t v m' := by
  induction n', hle using Nat.le_induction with
  | base => exact h
  | succ _ _ ih => exact ih.mono

/-- Every `BigStep` is derivable at some index. -/
theorem BigStep.toBigStepN {m : Memory} {e : Exp {}} {t : Trace} {v : Exp {}} {m' : Memory}
    (h : BigStep m e t v m') : ∃ n, BigStepN n m e t v m' := by
  induction h with
  | bs_pack => exact ⟨1, BigStepN.bs_pack⟩
  | bs_alloc hlk hfresh => exact ⟨1, BigStepN.bs_alloc hlk hfresh⟩
  | bs_val hv => exact ⟨1, BigStepN.bs_val hv⟩
  | bs_var => exact ⟨1, BigStepN.bs_var⟩
  | bs_apply hlk _ ih => obtain ⟨n, hn⟩ := ih; exact ⟨n+1, BigStepN.bs_apply hlk hn⟩
  | bs_invoke h1 h2 => exact ⟨1, BigStepN.bs_invoke h1 h2⟩
  | bs_tapply hlk _ ih => obtain ⟨n, hn⟩ := ih; exact ⟨n+1, BigStepN.bs_tapply hlk hn⟩
  | bs_capply hlk _ ih => obtain ⟨n, hn⟩ := ih; exact ⟨n+1, BigStepN.bs_capply hlk hn⟩
  | bs_wrap => exact ⟨1, BigStepN.bs_wrap⟩
  | bs_unwrap hlk _ ih => obtain ⟨n, hn⟩ := ih; exact ⟨n+1, BigStepN.bs_unwrap hlk hn⟩
  | bs_letin_val _ hv hwf_v hfresh _ ih1 ih2 =>
    obtain ⟨n1, hn1⟩ := ih1; obtain ⟨n2, hn2⟩ := ih2
    exact ⟨max n1 n2 + 1, BigStepN.bs_letin_val (hn1.le_mono (Nat.le_max_left ..)) hv hwf_v hfresh
      (hn2.le_mono (Nat.le_max_right ..))⟩
  | bs_letin_var _ _ ih1 ih2 =>
    obtain ⟨n1, hn1⟩ := ih1; obtain ⟨n2, hn2⟩ := ih2
    exact ⟨max n1 n2 + 1, BigStepN.bs_letin_var (hn1.le_mono (Nat.le_max_left ..))
      (hn2.le_mono (Nat.le_max_right ..))⟩
  | bs_unpack _ _ ih1 ih2 =>
    obtain ⟨n1, hn1⟩ := ih1; obtain ⟨n2, hn2⟩ := ih2
    exact ⟨max n1 n2 + 1, BigStepN.bs_unpack (hn1.le_mono (Nat.le_max_left ..))
      (hn2.le_mono (Nat.le_max_right ..))⟩
  | bs_read h1 h2 => exact ⟨1, BigStepN.bs_read h1 h2⟩
  | bs_write_true hx hy => exact ⟨1, BigStepN.bs_write_true hx hy⟩
  | bs_write_false hx hy => exact ⟨1, BigStepN.bs_write_false hx hy⟩
  | bs_drop hx => exact ⟨1, BigStepN.bs_drop hx⟩
  | bs_cond_true hres _ ih => obtain ⟨n, hn⟩ := ih; exact ⟨n+1, BigStepN.bs_cond_true hres hn⟩
  | bs_cond_false hres _ ih => obtain ⟨n, hn⟩ := ih; exact ⟨n+1, BigStepN.bs_cond_false hres hn⟩
  | bs_par _ _ ih1 ih2 =>
    obtain ⟨n1, hn1⟩ := ih1; obtain ⟨n2, hn2⟩ := ih2
    exact ⟨max n1 n2 + 1, BigStepN.bs_par (hn1.le_mono (Nat.le_max_left ..))
      (hn2.le_mono (Nat.le_max_right ..))⟩

/-- Inversion of a `BigStepN` `par` run: both branch sub-runs sit at the predecessor index. -/
theorem BigStepN.par_inv {n : Nat} {m : Memory} {C1 C2 : CaptureSet {}} {e1 e2 : Exp {}}
    {s : Trace} {v : Exp {}} {m' : Memory}
    (h : BigStepN (n + 1) m (.par C1 C2 e1 e2) s v m') :
    ∃ (t1 : Trace) (v1 : Exp {}) (m1 : Memory) (t2 : Trace) (v2 : Exp {}),
      s = t1 ++ t2 ∧ v = .unit ∧
      BigStepN n m e1 t1 v1 m1 ∧ BigStepN n m1 e2 t2 v2 m' := by
  cases h with
  | bs_par hL hR => exact ⟨_, _, _, _, _, rfl, rfl, hL, hR⟩
  | bs_val hv => cases hv

/-- Allocation-equivalence is a congruence for a common suffix. -/
theorem allocd_congr_left_append {ta ta' tb : Trace}
    (h : ∀ l, Trace.allocd ta l ↔ Trace.allocd ta' l) (l : Nat) :
    Trace.allocd (ta ++ tb) l ↔ Trace.allocd (ta' ++ tb) l := by
  rw [Trace.allocd_append, Trace.allocd_append]; exact or_congr_left (h l)

/-- **Converse of `TraceOkFrom.covers_of_extTouchesFromMode`.**  If every external touch of `t`
  (relative to the running allocation set `A`) is covered by `C`, then `t` is `TraceOkFrom C A`:
  every event is either covered or internal (its target already allocated in `A`). -/
theorem TraceOkFrom.of_extTouchesFromMode {C : CapabilitySet} :
    ∀ {A : List Nat} {t : Trace},
      (∀ l cm, Trace.extTouchesFromMode A l cm t → C.covers cm l) → TraceOkFrom C A t := by
  intro A t
  induction t generalizing A with
  | nil => intro _; exact TraceOkFrom.nil
  | cons it t ih =>
    intro h
    cases it with
    | alloc l' =>
      exact TraceOkFrom.alloc (ih (fun l cm hext => h l cm hext))
    | access mu l' =>
      refine TraceOkFrom.access ?_ (ih (fun l cm hext => h l cm (Or.inr hext)))
      by_cases hin : l' ∈ A
      · exact Or.inr hin
      · exact Or.inl (h l' (.access mu) (Or.inl ⟨rfl, hin, rfl⟩))
    | dealloc l' =>
      refine TraceOkFrom.dealloc ?_ (ih (fun l cm hext => h l cm (Or.inr hext)))
      by_cases hin : l' ∈ A
      · exact Or.inr hin
      · exact Or.inl (h l' .drop (Or.inl ⟨rfl, hin, rfl⟩))

/-- `TraceOk` is determined by the external touches it must cover. -/
theorem TraceOk.of_extTouchesMode {C : CapabilitySet} {t : Trace}
    (h : ∀ l cm, Trace.extTouchesMode t l cm → C.covers cm l) : TraceOk t C :=
  TraceOkFrom.of_extTouchesFromMode h

/-- **`TraceOk` is `Trace.Equiv`-invariant.**  Equivalent traces externally touch the same
  locations with the same modes (`Trace.Equiv.extTouchesMode_iff`), and `TraceOk` is exactly
  "every external touch is covered" (`covers_of_extTouchesMode` / `of_extTouchesMode`), so a
  budget bound transports across any Mazurkiewicz reordering. -/
theorem TraceOk.equiv_invariant {C : CapabilitySet} {t t' : Trace}
    (h : TraceOk t C) (heq : Trace.Equiv t t') : TraceOk t' C :=
  TraceOk.of_extTouchesMode (fun _ _ hext =>
    h.covers_of_extTouchesMode ((heq.extTouchesMode_iff).mpr hext))

/-- A cell a genuine step ALLOCATES is a capability in the post-step memory. -/
theorem Step.allocd_mcell {t : Trace} {m1 m2 : Memory} {e1 e2 : Exp {}} {l : Nat}
    (hstep : Step t m1 e1 m2 e2) (hal : Trace.allocd t l) :
    ∃ info, m2.heap l = some (.capability info) := by
  induction hstep with
  | step_apply _ | step_invoke _ _ | step_tapply _ | step_capply _ | step_unwrap _
  | step_cond_var_true _ | step_cond_var_false _ | step_read _ _
  | step_write_true _ _ | step_write_false _ _ | step_drop _
  | step_rename | step_unpack | step_par_join _ _ | step_lift _ _ _ =>
    simp only [Trace.allocd] at hal
  | step_alloc _ hfresh =>
    simp only [Trace.allocd, or_false] at hal; subst hal
    exact ⟨_, Memory.extend_mcell_lookup hfresh⟩
  | step_ctx_letin _ ih | step_ctx_unpack _ ih
  | step_par_left _ _ _ ih | step_par_right _ _ _ ih => exact ih hal

set_option maxHeartbeats 1000000 in
-- The induction has 21 step cases; the premature-`par_right` case threads the BigStep diamond
-- plus the 11-field `Safe.par` carrier and the trace-commutation algebra, exceeding the default.
/-- **Genuine big-step head-expansion (step-indexed).**  If `e1` steps to `e2` (a genuine,
  possibly premature, interleaving step) and `e2` then big-steps to `v` at `m'`, then `e1`
  big-steps to the SAME `v` at the SAME `m'`, on a trace `t'` that is `Trace.Equiv`-equal to
  `t ++ s` (and allocates the same cells).  Proved by `induction` on the run's step index: the
  "aligned" leaf/join/letin/unpack/par_left shapes are head-expanded with the trace EXACTLY
  `t ++ s` (the sequential `BigStep.head_expand`, no reordering); the premature `par_right` case
  bubbles the step past the left branch's run with the diamond `step_run_commute` (non-interference
  off the `Safe.par` carrier) and recurses on the strictly-smaller right run, whence the trace
  reorders only up to `Trace.Equiv`. -/
theorem Step.head_expand_bigstepN :
    ∀ (n : Nat) {t : Trace} {m1 m2 : Memory} {e1 e2 : Exp {}},
      Step t m1 e1 m2 e2 → Safe m1 e1 → Exp.WfInHeap e1 m1.heap →
      ∀ {s : Trace} {v : Exp {}} {m' : Memory},
        BigStepN n m2 e2 s v m' →
        ∃ t', BigStep m1 e1 t' v m' ∧ Trace.Equiv (t ++ s) t' ∧
          (∀ l, Trace.allocd (t ++ s) l ↔ Trace.allocd t' l) := by
  intro n
  induction n with
  | zero =>
    intro _ _ _ _ _ _ _ _ _ _ _ hr; cases hr
  | succ n ihn =>
    intro t m1 m2 e1 e2 hstep hsafe hwf s v m' hr
    cases hstep with
    | step_apply hlk =>
      exact ⟨_, BigStep.head_expand (SeqStep.step_apply hlk) hr.toBigStep,
        Trace.Equiv.refl _, fun _ => Iff.rfl⟩
    | step_invoke h1 h2 =>
      exact ⟨_, BigStep.head_expand (SeqStep.step_invoke h1 h2) hr.toBigStep,
        Trace.Equiv.refl _, fun _ => Iff.rfl⟩
    | step_tapply hlk =>
      exact ⟨_, BigStep.head_expand (SeqStep.step_tapply hlk) hr.toBigStep,
        Trace.Equiv.refl _, fun _ => Iff.rfl⟩
    | step_capply hlk =>
      exact ⟨_, BigStep.head_expand (SeqStep.step_capply hlk) hr.toBigStep,
        Trace.Equiv.refl _, fun _ => Iff.rfl⟩
    | step_unwrap hlk =>
      exact ⟨_, BigStep.head_expand (SeqStep.step_unwrap hlk) hr.toBigStep,
        Trace.Equiv.refl _, fun _ => Iff.rfl⟩
    | step_cond_var_true hlk =>
      exact ⟨_, BigStep.head_expand (SeqStep.step_cond_var_true hlk) hr.toBigStep,
        Trace.Equiv.refl _, fun _ => Iff.rfl⟩
    | step_cond_var_false hlk =>
      exact ⟨_, BigStep.head_expand (SeqStep.step_cond_var_false hlk) hr.toBigStep,
        Trace.Equiv.refl _, fun _ => Iff.rfl⟩
    | step_read h1 h2 =>
      exact ⟨_, BigStep.head_expand (SeqStep.step_read h1 h2) hr.toBigStep,
        Trace.Equiv.refl _, fun _ => Iff.rfl⟩
    | step_write_true h1 h2 =>
      exact ⟨_, BigStep.head_expand (SeqStep.step_write_true h1 h2) hr.toBigStep,
        Trace.Equiv.refl _, fun _ => Iff.rfl⟩
    | step_write_false h1 h2 =>
      exact ⟨_, BigStep.head_expand (SeqStep.step_write_false h1 h2) hr.toBigStep,
        Trace.Equiv.refl _, fun _ => Iff.rfl⟩
    | step_alloc h1 h2 =>
      exact ⟨_, BigStep.head_expand (SeqStep.step_alloc h1 h2) hr.toBigStep,
        Trace.Equiv.refl _, fun _ => Iff.rfl⟩
    | step_drop hx =>
      exact ⟨_, BigStep.head_expand (SeqStep.step_drop hx) hr.toBigStep,
        Trace.Equiv.refl _, fun _ => Iff.rfl⟩
    | step_rename =>
      exact ⟨_, BigStep.head_expand SeqStep.step_rename hr.toBigStep,
        Trace.Equiv.refl _, fun _ => Iff.rfl⟩
    | step_lift hv hwf_v hfresh =>
      exact ⟨_, BigStep.head_expand (SeqStep.step_lift hv hwf_v hfresh) hr.toBigStep,
        Trace.Equiv.refl _, fun _ => Iff.rfl⟩
    | step_unpack =>
      exact ⟨_, BigStep.head_expand SeqStep.step_unpack hr.toBigStep,
        Trace.Equiv.refl _, fun _ => Iff.rfl⟩
    | step_par_join h1 h2 =>
      exact ⟨_, BigStep.head_expand (SeqStep.step_par_join h1 h2) hr.toBigStep,
        Trace.Equiv.refl _, fun _ => Iff.rfl⟩
    | step_ctx_letin inner =>
      have hse := Safe.letin_inv_left hsafe
      have hwfh := (Exp.wf_inv_letin hwf).1
      cases hr with
      | bs_val hv => cases hv
      | bs_letin_val hh hv hwf_v hfresh hc =>
        obtain ⟨th'', hh', heqh, haeh⟩ := ihn inner hse hwfh hh
        refine ⟨th'' ++ _, BigStep.bs_letin_val hh' hv hwf_v hfresh hc.toBigStep, ?_, ?_⟩
        · rw [← List.append_assoc]; exact Trace.Equiv.append_right_congr heqh haeh
        · intro l; rw [← List.append_assoc]; exact allocd_congr_left_append haeh l
      | bs_letin_var hh hc =>
        obtain ⟨th'', hh', heqh, haeh⟩ := ihn inner hse hwfh hh
        refine ⟨th'' ++ _, BigStep.bs_letin_var hh' hc.toBigStep, ?_, ?_⟩
        · rw [← List.append_assoc]; exact Trace.Equiv.append_right_congr heqh haeh
        · intro l; rw [← List.append_assoc]; exact allocd_congr_left_append haeh l
    | step_ctx_unpack inner =>
      have hse := Safe.unpack_inv_left hsafe
      have hwfh := (Exp.wf_inv_unpack hwf).1
      cases hr with
      | bs_val hv => cases hv
      | bs_unpack hh hc =>
        obtain ⟨th'', hh', heqh, haeh⟩ := ihn inner hse hwfh hh
        refine ⟨th'' ++ _, BigStep.bs_unpack hh' hc.toBigStep, ?_, ?_⟩
        · rw [← List.append_assoc]; exact Trace.Equiv.append_right_congr heqh haeh
        · intro l; rw [← List.append_assoc]; exact allocd_congr_left_append haeh l
    | step_par_left inner ht_g hni_g =>
      have hse := Safe.par_inv_left hsafe
      have hwfL := (Exp.wf_inv_par hwf).1
      cases hr with
      | bs_val hv => cases hv
      | bs_par hL hR =>
        obtain ⟨sL'', hL', heqL, haeL⟩ := ihn inner hse hwfL hL
        refine ⟨sL'' ++ _, BigStep.bs_par hL' hR.toBigStep, ?_, ?_⟩
        · rw [← List.append_assoc]; exact Trace.Equiv.append_right_congr heqL haeL
        · intro l; rw [← List.append_assoc]; exact allocd_congr_left_append haeL l
    | step_par_right ht_g hni_g inner =>
      obtain ⟨hwf_eL, hwf_eR⟩ := Exp.wf_inv_par hwf
      obtain ⟨sL, vL, mL, sR, vR, rfl, rfl, hL, hR⟩ := hr.par_inv
      cases hsafe with
      | ans hh' => cases hh' with | is_val hv => cases hv
      | par hse_a h2 hb1 hb2 hrs1 hrs2 hpres1 hpres2 hcov1 hcov2 hni =>
        have hsub1 : m2.subsumes m1 := Step.subsumes inner
        have hbsL_m2 : BigStep m2 _ sL vL mL := hL.toBigStep
        have htokL : TraceOk sL _ := hb1 hsub1 (Exp.wf_monotonic hsub1 hwf_eL) hbsL_m2
        have htok_t : TraceOk t _ := TraceOk.mono hcov2.2 ht_g
        have hsep : Trace.Noninterfere sL t := traceOk_noninterfere htokL htok_t hni
        obtain ⟨mc, hL', inner'⟩ :=
          BigStep.step_run_commute inner hbsL_m2 hsep hwf_eL hwf_eR
        have hsafe_eR : Safe mc _ := h2 hL'
        have hwf_eR_mc : Exp.WfInHeap _ mc.heap := Exp.wf_monotonic (BigStep.subsumes hL') hwf_eR
        obtain ⟨tR'', hR', heqR, haeR⟩ := ihn inner' hsafe_eR hwf_eR_mc hR
        have hf1 : ∀ l, Trace.allocd sL l → Trace.extSeqFrom [] l t = [] := fun l hal =>
          fresh_not_extSeq ht_g
            (Heap.none_of_subsumes_none hsub1 (BigStep.alloc_fresh hbsL_m2 hal))
        have hf2 : ∀ l, Trace.allocd t l → Trace.extSeqFrom [] l sL = [] := fun l hal =>
          fresh_not_extSeq (TraceOk.mono hcov1.1 htokL) (Step.alloc_fresh inner hal)
        have hcomm : Trace.Equiv (t ++ sL) (sL ++ t) :=
          Trace.equiv_comm_of_noninterfere hsep.symm hf1 hf2
        have hcommAE : ∀ l, Trace.allocd (t ++ sL) l ↔ Trace.allocd (sL ++ t) l := by
          intro l; rw [Trace.allocd_append, Trace.allocd_append]; exact or_comm
        refine ⟨sL ++ tR'', BigStep.bs_par hL' hR', ?_, ?_⟩
        · have stepA : Trace.Equiv (t ++ (sL ++ sR)) (sL ++ (t ++ sR)) := by
            rw [← List.append_assoc, ← List.append_assoc]
            exact Trace.Equiv.append_right_congr hcomm hcommAE
          have stepB : Trace.Equiv (sL ++ (t ++ sR)) (sL ++ tR'') :=
            Trace.Equiv.append_left_congr heqR
          exact stepA.trans stepB
        · intro l
          calc Trace.allocd (t ++ (sL ++ sR)) l
              ↔ Trace.allocd t l ∨ Trace.allocd sL l ∨ Trace.allocd sR l := by
                rw [Trace.allocd_append, Trace.allocd_append]
            _ ↔ Trace.allocd sL l ∨ Trace.allocd t l ∨ Trace.allocd sR l := or_left_comm
            _ ↔ Trace.allocd sL l ∨ Trace.allocd (t ++ sR) l := by rw [Trace.allocd_append]
            _ ↔ Trace.allocd sL l ∨ Trace.allocd tR'' l := or_congr_right (haeR l)
            _ ↔ Trace.allocd (sL ++ tR'') l := Trace.allocd_append.symm

/-- **Genuine big-step head-expansion** (wrapper, run-index erased): a genuine step prepended to a
  big-step run of the reduct recovers a run of the original, on a trace `Trace.Equiv` to `t ++ s`
  (same allocations).  See `Step.head_expand_bigstepN`. -/
theorem Step.head_expand_bigstep {t : Trace} {m1 m2 : Memory} {e1 e2 : Exp {}}
    (hstep : Step t m1 e1 m2 e2) (hsafe : Safe m1 e1) (hwf : Exp.WfInHeap e1 m1.heap)
    {s : Trace} {v : Exp {}} {m' : Memory} (hr : BigStep m2 e2 s v m') :
    ∃ t', BigStep m1 e1 t' v m' ∧ Trace.Equiv (t ++ s) t' ∧
      (∀ l, Trace.allocd (t ++ s) l ↔ Trace.allocd t' l) := by
  obtain ⟨n, hrN⟩ := hr.toBigStepN
  exact Step.head_expand_bigstepN n hstep hsafe hwf hrN

set_option maxHeartbeats 1000000 in
-- The 11-field `Safe.par` carrier rebuild, each field threading the diamond/head-expansion, exceeds
-- the default heartbeat budget.
/-- **Premature-`par_left` preservation.**  A genuine left-branch step.  Mirrors the sequential
  `step_preserves_safe` `par_left` case, but every appeal to head-expansion now goes through the
  GENUINE `Step.head_expand_bigstep` (which reorders the recovered trace up to `Trace.Equiv`).  The
  one field this matters for — the reduct's LEFT BUDGET `hb1'` — is closed by `TraceOk`'s
  `Trace.Equiv`-invariance (`TraceOk.equiv_invariant`): the recovered run's trace is `Trace.Equiv`
  to `t ++ s`, so its `hb1` budget bound transports to `t ++ s` and the step's allocations absorb
  into the reduct budget via `split_append`/`absorb_exempt` exactly as in the sequential proof.  The
  continuation `h2'` and robust-safety fields only need the recovered value/memory (trace-free). -/
theorem Step.preserves_safe_par_left {t : Trace} {m1 m2 : Memory}
    {C1 C2 : CaptureSet {}} {eL eL' eR : Exp {}}
    (hstep : Step t m1 eL m2 eL')
    (hsafe : Safe m1 (.par C1 C2 eL eR)) (hwf : Exp.WfInHeap (.par C1 C2 eL eR) m1.heap)
    (ih : Exp.WfInHeap eL m1.heap → Safe m1 eL → Safe m2 eL') :
    Safe m2 (.par (C1.growByAllocs t) C2 eL' eR) := by
  obtain ⟨hwf_a, hwf_b⟩ := Exp.wf_inv_par hwf
  have hwfC1 : C1.WfInHeap m1.heap := by cases hwf with | wf_par h _ _ _ => exact h
  have hwfC2 : C2.WfInHeap m1.heap := by cases hwf with | wf_par _ h _ _ => exact h
  cases hsafe with
  | ans hans => cases hans with | is_val hv => cases hv
  | par hse_a h2 hb1 hb2 _hrs1 hrs2 hpres1 hpres2 hcov1 hcov2 hni =>
    rename_i Cb1 Cb2
    have hsub21 : m2.subsumes m1 := Step.subsumes hstep
    have hse_a2' : Safe m2 eL' := ih hwf_a hse_a
    have hb1_robust : ∀ {m' : Memory} {s : Trace} {v : Exp {}} {m''},
        m'.subsumes m2 → Exp.WfInHeap eL' m'.heap → BigStep m' eL' s v m'' →
        TraceOk s (Cb1 ∪ capsOf (Trace.allocList t)) := by
      intro m' s v m'' hsub' hwf' hbs
      have hwfa' := Step.preserves_wf hstep hwf_a
      obtain ⟨ms, hbs_m2, _, _⟩ := hbs.simulate_down hsub' hwfa'
      obtain ⟨tt, hfull, heq, _⟩ := Step.head_expand_bigstep hstep hse_a hwf_a hbs_m2
      have htok' : TraceOk tt Cb1 := hb1 (Memory.subsumes_refl _) hwf_a hfull
      have htok : TraceOk (t ++ s) Cb1 := TraceOk.equiv_invariant htok' heq.symm
      have := TraceOkFrom.absorb_exempt (TraceOkFrom.split_append htok)
      rwa [List.append_nil] at this
    have hwf_a2' : Exp.WfInHeap eL' m2.heap := Step.preserves_wf hstep hwf_a
    have hcov_of_touch : ∀ {m'' : Memory} {s : Trace} {v : Exp {}} {mf : Memory} {l : Nat}
        {bb : Bool}, m''.subsumes m2 → BigStep m'' eL' s v mf →
        m2.lookup l = some (.capability (.mcell bb .live)) → Trace.extTouches s l →
        ∃ cm, (Cb1 ∪ capsOf (Trace.allocList t)).covers cm l := by
      intro m'' s v mf l bb hsub'' hbs_a' hlive htouch
      have hnal : ¬ Trace.allocd s l := fun ha => by
        have hnone : m''.heap l = none := hbs_a'.alloc_fresh ha
        have : m2.heap l = none := Heap.none_of_subsumes_none hsub'' hnone
        rw [show m2.lookup l = m2.heap l from rfl, this] at hlive; cases hlive
      obtain ⟨cm, hext⟩ :=
        Trace.extTouchesMode_of_touched hnal (Trace.touched_of_extTouches htouch)
      exact ⟨cm, (hb1_robust hsub'' (Exp.wf_monotonic hsub'' hwf_a2') hbs_a')
        |>.covers_of_extTouchesMode hext⟩
    refine Safe.par (C1 := Cb1 ∪ capsOf (Trace.allocList t)) (C2 := Cb2)
      hse_a2' ?h2' (@hb1_robust) ?hb2' ?hrs1' ?hrs2' ?hpres1' ?hpres2' ?hcov1' ?hcov2' ?hni'
    case hcov1' =>
      exact Safe.hcov_step hsub21 hwfC1
        (fun l hl => Step.allocd_mcell hstep (Trace.mem_allocList.mp hl)) hcov1
    case hcov2' =>
      rw [CaptureSet.reachability_monotonic hsub21 C2 hwfC2]; exact hcov2
    case h2' =>
      intro t1 v1 m1' hbs
      obtain ⟨_, hfull, _, _⟩ := Step.head_expand_bigstep hstep hse_a hwf_a hbs
      exact h2 hfull
    case hb2' =>
      intro m' s v m'' hsub' hwf' hbs
      exact hb2 (Memory.subsumes_trans hsub' hsub21) hwf' hbs
    case hrs1' =>
      intro m' hsub' hc
      refine Safe.lift hse_a2' hsub' (Q := fun s val m => BigStep m2 eL' s val m)
        (fun _ _ _ h => h) ?_ hwf_a2'
      intro s v m _ hbs_a' l b hlive htouch
      obtain ⟨cm, hcov⟩ := hcov_of_touch (Memory.subsumes_refl _) hbs_a' hlive htouch
      obtain ⟨mu', hmem', _⟩ := CapabilitySet.covers_imp_exists_hasmem hcov
      obtain ⟨c', hc'', hsubc⟩ := hsub' l (.capability (.mcell b .live)) hlive
      cases c' with
      | val _ => simp [Cell.subsumes] at hsubc
      | masked => simp [Cell.subsumes] at hsubc
      | capability cc =>
        cases cc with
        | mcell b'' ℓ'' =>
          have hℓ := hc mu' l b'' ℓ'' hmem' hc''
          exact ⟨b'', by rw [hℓ] at hc''; exact hc''⟩
        | basic => simp [Cell.subsumes] at hsubc
    case hrs2' =>
      intro m' hsub' hc
      exact hrs2 (Memory.subsumes_trans hsub' hsub21) hc
    case hpres1' =>
      intro mu l hmem
      rcases CapabilitySet.hasmem_union_iff.mp hmem with h1 | hA
      · exact (fun hc => hpres1 mu l h1 (Heap.none_of_subsumes_none hsub21 hc))
      · exact Step.allocd_present hstep (Trace.mem_allocList.mp (capsOf_hasmem hA))
    case hpres2' =>
      intro mu l hmem
      exact (fun hc => hpres2 mu l hmem (Heap.none_of_subsumes_none hsub21 hc))
    case hni' =>
      refine CapabilitySet.Noninterference.ni_union hni
        (CapabilitySet.noninterference_capsOf_fresh ?_)
      intro l hl mu' hm
      exact hpres2 mu' l hm (Step.alloc_fresh hstep (Trace.mem_allocList.mp hl))

/-- **The premature-`par_right` safety gap — the fundamental boundary.**  A `par_right` step whose
  left branch is not yet an answer.  Rebuilding `Safe m₂ (par C₁ C₂ eL eR')` needs the node's
  sequential continuation `h2' : ∀ BigStep m₂ eL → Safe · eR'` and reduct right-budget `hb2'`.  The
  carrier supplies the right branch's safety/bound ONLY conditionally — `h2 : ∀ BigStep m eL →
  Safe · eR` runs eL FIRST — so deriving `h2'`/`hb2'` needs ROBUST preservation of the right step
  at every post-left memory, which the asymmetric `Safe.par` does not provide.  This is the
  dynamic-footprint/ownership fact: the right branch is independently safe at mid-reduction.  The
  principled fix is a SYMMETRIC `Safe.par` (robust right-branch safety) established at
  `sem_typ_par` — a type-system-level change with a large `Fundamental` ripple, hence human design
  intervention.  (`absorb` avoids this by bubbling premature steps past the already-sequential
  left run and reading `h2` at the post-left memory; the gap surfaces only when preserving `Safe`
  along a GENUINE interleaved run.) -/
theorem Step.preserves_safe_par_right {t : Trace} {m1 m2 : Memory}
    {C1 C2 : CaptureSet {}} {eL eR eR' : Exp {}}
    (hstep : Step t m1 eR m2 eR') (hsafe : Safe m1 (.par C1 C2 eL eR))
    (hwf : Exp.WfInHeap (.par C1 C2 eL eR) m1.heap) :
    Safe m2 (.par C1 (C2.growByAllocs t) eL eR') :=
  sorry

/-- **Genuine interleaving step preserves safety.**  The leaf and join steps are `SeqStep`s, so
  they reduce to the sequential `step_preserves_safe`.  The `letin`/`unpack` congruence cases
  rebuild `Safe` via the IH plus genuine head-expansion (`Step.head_expand_bigstep`).  The two
  `par`-congruence cases delegate to `Step.preserves_safe_par_left`/`_par_right`; the latter is
  the documented carrier-asymmetry gap. -/
theorem Step.preserves_safe {t : Trace} {m1 m2 : Memory} {e1 e2 : Exp {}}
    (hstep : Step t m1 e1 m2 e2) (hwf : e1.WfInHeap m1.heap) (hsafe : Safe m1 e1) :
    Safe m2 e2 := by
  induction hstep with
  | step_apply hlk => exact step_preserves_safe (SeqStep.step_apply hlk) hwf hsafe
  | step_invoke h1 h2 => exact step_preserves_safe (SeqStep.step_invoke h1 h2) hwf hsafe
  | step_tapply hlk => exact step_preserves_safe (SeqStep.step_tapply hlk) hwf hsafe
  | step_capply hlk => exact step_preserves_safe (SeqStep.step_capply hlk) hwf hsafe
  | step_unwrap hlk => exact step_preserves_safe (SeqStep.step_unwrap hlk) hwf hsafe
  | step_cond_var_true hlk => exact step_preserves_safe (SeqStep.step_cond_var_true hlk) hwf hsafe
  | step_cond_var_false hlk => exact step_preserves_safe (SeqStep.step_cond_var_false hlk) hwf hsafe
  | step_read h1 h2 => exact step_preserves_safe (SeqStep.step_read h1 h2) hwf hsafe
  | step_write_true h1 h2 => exact step_preserves_safe (SeqStep.step_write_true h1 h2) hwf hsafe
  | step_write_false h1 h2 => exact step_preserves_safe (SeqStep.step_write_false h1 h2) hwf hsafe
  | step_alloc h1 h2 => exact step_preserves_safe (SeqStep.step_alloc h1 h2) hwf hsafe
  | step_drop hx => exact step_preserves_safe (SeqStep.step_drop hx) hwf hsafe
  | step_rename => exact step_preserves_safe SeqStep.step_rename hwf hsafe
  | step_lift hv hwf_v hfresh =>
    exact step_preserves_safe (SeqStep.step_lift hv hwf_v hfresh) hwf hsafe
  | step_unpack => exact step_preserves_safe SeqStep.step_unpack hwf hsafe
  | step_par_join h1 h2 => exact step_preserves_safe (SeqStep.step_par_join h1 h2) hwf hsafe
  | step_ctx_letin inner ih =>
    obtain ⟨hwf1, hwf2⟩ := Exp.wf_inv_letin hwf
    cases hsafe with
    | letin hse1 h_ans h_val h_var =>
      refine Safe.letin (ih hwf1 hse1) ?_ ?_ ?_
      · intro t1 v m1' hbs
        obtain ⟨t', hbs', _, _⟩ := Step.head_expand_bigstep inner hse1 hwf1 hbs
        exact h_ans _ _ _ hbs'
      · intro t1 m1' v hbs hv hwf_v l' hfresh
        obtain ⟨t', hbs', _, _⟩ := Step.head_expand_bigstep inner hse1 hwf1 hbs
        exact h_val hbs' hv hwf_v l' hfresh
      · intro t1 m1' x hbs
        obtain ⟨t', hbs', _, _⟩ := Step.head_expand_bigstep inner hse1 hwf1 hbs
        exact h_var hbs'
    | ans hh => cases hh with | is_val hv => cases hv
  | step_ctx_unpack inner ih =>
    obtain ⟨hwf1, hwf2⟩ := Exp.wf_inv_unpack hwf
    cases hsafe with
    | unpack hse1 h_ans h_val =>
      refine Safe.unpack (ih hwf1 hse1) ?_ ?_
      · intro t1 v m1' hbs
        obtain ⟨t', hbs', _, _⟩ := Step.head_expand_bigstep inner hse1 hwf1 hbs
        exact h_ans _ _ _ hbs'
      · intro t1 m1' x cs hbs
        obtain ⟨t', hbs', _, _⟩ := Step.head_expand_bigstep inner hse1 hwf1 hbs
        exact h_val hbs'
    | ans hh => cases hh with | is_val hv => cases hv
  | step_par_left inner ht hni ih =>
    exact Step.preserves_safe_par_left inner hsafe hwf ih
  | step_par_right ht hni inner ih =>
    exact Step.preserves_safe_par_right inner hsafe hwf

/-- **Standardization (theorem B).**  Every genuine interleaving run to an answer is matched by
  a sequential (left-first) run reaching the IDENTICAL final memory and answer, the traces
  differing only by `Trace.Equiv` (Mazurkiewicz reordering of independent events).  Folds
  `absorb` over the run, threading `Safe`/`WfInHeap` by the genuine-step preservation lemmas. -/
theorem standardization {m mf : Memory} {e a : Exp {}} {t : Trace}
    (hwf : Exp.WfInHeap e m.heap) (hsafe : Safe m e)
    (hred : Reduce t m e mf a) (hans : a.IsAns) :
    ∃ t', SeqReduce t' m e mf a ∧ Trace.Equiv t t' := by
  revert hwf hsafe hans
  induction hred with
  | refl => exact fun _ _ _ => ⟨[], SeqReduce.refl, Trace.Equiv.refl _⟩
  | step h1 hrest ih =>
    intro hwf hsafe hans
    obtain ⟨trest', hsr, heq⟩ :=
      ih (Step.preserves_wf h1 hwf) (Step.preserves_safe h1 hwf hsafe) hans
    obtain ⟨n, hn⟩ := hsr.toN
    obtain ⟨t', hst', heq', _⟩ := absorb hn h1 hsafe hwf hans
    exact ⟨t', hst', (Trace.Equiv.append_left_congr heq).trans heq'⟩

end CoreCapybara
