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

theorem standardization {m mf : Memory} {e a : Exp {}} {t : Trace}
    (hwf : Exp.WfInHeap e m.heap) (hsafe : Safe m e)
    (hred : Reduce t m e mf a) (hans : a.IsAns) :
    ∃ t', SeqReduce t' m e mf a ∧ Trace.Equiv t t' :=
  sorry

end CoreCapybara
