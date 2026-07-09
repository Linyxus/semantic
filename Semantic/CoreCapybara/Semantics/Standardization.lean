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

  This file defines `Trace.Equiv` and proves `standardization`; the separation content
  that licenses the trace reordering is carried by the interleaving `Step`'s own
  `par`-guards, so the theorem needs no `Safe` hypothesis. -/

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

/-! ## The guarded sequential relation

  Standardization reorders runs using only the interleaving `Step`'s own `par`-guards,
  never consulting a separation carrier at intermediate states; the final
  `standardization` theorem needs no `Safe` hypothesis.  A total `Safe` carrier cannot
  be reconstructed after a lone branch step: with the budget-indexed, rely–guarantee
  `Safe.par`, rebuilding the carrier would demand transporting the rely along a
  *partial* branch run, the false operational-monotonicity shape (see the NOTE in
  `Semantics/BigStep.lean`).  The guards suffice on their own: every branch step of a
  given run arrives with its trace bound and the branches' non-interference, which is
  exactly the separation content standardization needs.

  `GSeqStep` is `SeqStep` (the left-first schedule) enriched with `Step`'s `par`
  guards; it projects to a plain `SeqStep` (dropping guards) and to a genuine
  `Step` (dropping the scheduling gate). -/
inductive GSeqStep : Trace -> Memory -> Exp {} -> Memory -> Exp {} -> Prop where
| step_apply :
  m.lookup x = some (.val ⟨.abs cs T e, hv, R⟩) ->
  GSeqStep [] m (.app (.free x) (.free y)) m (e.subst (Subst.openVar (.free y)))
| step_invoke :
  m.lookup x = some (.capability .basic) ->
  m.lookup y = some (.val ⟨.unit, hv, R⟩) ->
  GSeqStep [.access .epsilon x] m (.app (.free x) (.free y)) m .unit
| step_tapply :
  m.lookup x = some (.val ⟨.tabs cs S' e, hv, R⟩) ->
  GSeqStep [] m (.tapp (.free x) S) m (e.subst (Subst.openTVar .top))
| step_capply :
  m.lookup x = some (.val ⟨.cabs cs B e, hv, R⟩) ->
  GSeqStep [] m (.capp (.free x) CS) m (e.subst (Subst.openCVar CS))
| step_consumer_app :
  m.lookup x = some (.val ⟨.consumer cs (.exi 1 T) e, hv, R⟩) ->
  GSeqStep [] m (.consumer_app (.free x) arg) m (.unpack 1 arg e)
| step_unwrap :
  m.lookup x = some (.val ⟨.boxed cs Ψ e, hv, R⟩) ->
  GSeqStep [] m (.unwrap (.free x)) m e
| step_cond_var_true :
  m.lookup x = some (.val ⟨.btrue, hv, R⟩) ->
  GSeqStep [] m (.cond (.free x) e1 e2) m e1
| step_cond_var_false :
  m.lookup x = some (.val ⟨.bfalse, hv, R⟩) ->
  GSeqStep [] m (.cond (.free x) e1 e2) m e2
| step_read :
  m.lookup x = some (.val ⟨.reader (.free y), hv_reader, R_reader⟩) ->
  m.lookup y = some (.capability (.mcell n .live)) ->
  GSeqStep [.access .ro y] m (.read (.free x)) m (.var (.free n))
| step_write :
  (hx : m.lookup x = some (.capability (.mcell n0 .live))) ->
  (hy : m.heap y ≠ none) ->
  GSeqStep [.access .epsilon x] m (.write (.free x) (.free y))
    (m.update_mcell x y .live ⟨n0, hx⟩ (fun _ => hy)) .unit
| step_alloc :
  (hx : m.heap x ≠ none) ->
  (hfresh : m.heap l = none) ->
  GSeqStep [.alloc l] m (.alloc (.free x))
    (m.extend_mcell l x hfresh hx)
    (.pack ⟨[.var (.M .epsilon) (.free l)], rfl⟩ (.free l))
| step_drop :
  (hx : m.lookup x = some (.capability (.mcell n .live))) ->
  GSeqStep [.dealloc x] m (.drop (.free x))
    (m.drop_mcell x ⟨n, hx⟩) .unit
| step_ctx_letin :
  GSeqStep t m e1 m' e1' ->
  GSeqStep t m (.letin e1 e2) m' (.letin e1' e2)
| step_ctx_unpack {n : Nat} {e2 : Exp ((Sig.extendCVars {} n),x)} :
  GSeqStep t m e1 m' e1' ->
  GSeqStep t m (.unpack n e1 e2) m' (.unpack n e1' e2)
| step_par_left {C1 C2 : CaptureSet {}} :
  GSeqStep t m e1 m' e1' ->
  (ht : TraceOk t (C1.reachability m)) ->
  (hni : CapabilitySet.Noninterference (C1.reachability m) (C2.reachability m)) ->
  GSeqStep t m (.par C1 C2 e1 e2) m' (.par (C1.growByAllocs t) C2 e1' e2)
| step_par_right :
  e1.IsAns ->
  (ht : TraceOk t (C2.reachability m)) ->
  (hni : CapabilitySet.Noninterference (C1.reachability m) (C2.reachability m)) ->
  GSeqStep t m e2 m' e2' ->
  GSeqStep t m (.par C1 C2 e1 e2) m' (.par C1 (C2.growByAllocs t) e1 e2')
| step_par_join :
  e1.IsAns -> e2.IsAns ->
  GSeqStep [] m (.par C1 C2 e1 e2) m .unit
| step_rename :
  GSeqStep [] m (.letin (.var (.free y)) e) m (e.subst (Subst.openVar (.free y)))
| step_lift :
  (hv : Exp.IsSimpleVal v) ->
  (hwf : Exp.WfInHeap v m.heap) ->
  (hfresh : m.heap l = none) ->
  GSeqStep
    []
    m (.letin v e)
    (m.extend l ⟨v, hv, compute_reachability m.heap v hv⟩ hwf rfl hfresh)
    (e.subst (Subst.openVar (.free l)))
| step_unpack {n : Nat} {cs : List.Vector (CaptureSet {}) n}
    {e : Exp ((Sig.extendCVars {} n),x)} :
  GSeqStep [] m (.unpack n (.pack cs (.free x)) e) m (e.subst (Subst.unpack cs (.free x)))

/-- Guards are extra: every guarded sequential step is a plain sequential step. -/
theorem GSeqStep.toSeqStep {t : Trace} {m m' : Memory} {e e' : Exp {}}
    (h : GSeqStep t m e m' e') : SeqStep t m e m' e' := by
  induction h with
  | step_apply hlk => exact SeqStep.step_apply hlk
  | step_invoke h1 h2 => exact SeqStep.step_invoke h1 h2
  | step_tapply hlk => exact SeqStep.step_tapply hlk
  | step_capply hlk => exact SeqStep.step_capply hlk
  | step_consumer_app hlk => exact SeqStep.step_consumer_app hlk
  | step_unwrap hlk => exact SeqStep.step_unwrap hlk
  | step_cond_var_true hlk => exact SeqStep.step_cond_var_true hlk
  | step_cond_var_false hlk => exact SeqStep.step_cond_var_false hlk
  | step_read h1 h2 => exact SeqStep.step_read h1 h2
  | step_write h1 h2 => exact SeqStep.step_write h1 h2
  | step_alloc h1 h2 => exact SeqStep.step_alloc h1 h2
  | step_drop hx => exact SeqStep.step_drop hx
  | step_ctx_letin _ ih => exact SeqStep.step_ctx_letin ih
  | step_ctx_unpack _ ih => exact SeqStep.step_ctx_unpack ih
  | step_par_left _ _ _ ih => exact SeqStep.step_par_left ih
  | step_par_right hans _ _ _ ih => exact SeqStep.step_par_right hans ih
  | step_par_join h1 h2 => exact SeqStep.step_par_join h1 h2
  | step_rename => exact SeqStep.step_rename
  | step_lift hv hwf hfresh => exact SeqStep.step_lift hv hwf hfresh
  | step_unpack => exact SeqStep.step_unpack

/-- The gate is extra: every guarded sequential step is a genuine interleaving step. -/
theorem GSeqStep.toStep {t : Trace} {m m' : Memory} {e e' : Exp {}}
    (h : GSeqStep t m e m' e') : Step t m e m' e' := by
  induction h with
  | step_apply hlk => exact Step.step_apply hlk
  | step_invoke h1 h2 => exact Step.step_invoke h1 h2
  | step_tapply hlk => exact Step.step_tapply hlk
  | step_capply hlk => exact Step.step_capply hlk
  | step_consumer_app hlk => exact Step.step_consumer_app hlk
  | step_unwrap hlk => exact Step.step_unwrap hlk
  | step_cond_var_true hlk => exact Step.step_cond_var_true hlk
  | step_cond_var_false hlk => exact Step.step_cond_var_false hlk
  | step_read h1 h2 => exact Step.step_read h1 h2
  | step_write h1 h2 => exact Step.step_write h1 h2
  | step_alloc h1 h2 => exact Step.step_alloc h1 h2
  | step_drop hx => exact Step.step_drop hx
  | step_ctx_letin _ ih => exact Step.step_ctx_letin ih
  | step_ctx_unpack _ ih => exact Step.step_ctx_unpack ih
  | step_par_left _ ht hni ih => exact Step.step_par_left ih ht hni
  | step_par_right _ ht hni _ ih => exact Step.step_par_right ht hni ih
  | step_par_join h1 h2 => exact Step.step_par_join h1 h2
  | step_rename => exact Step.step_rename
  | step_lift hv hwf hfresh => exact Step.step_lift hv hwf hfresh
  | step_unpack => exact Step.step_unpack

/-- Multi-step guarded sequential reduction. -/
inductive GSeqReduce : Trace -> Memory -> Exp {} -> Memory -> Exp {} -> Prop where
| refl :
  GSeqReduce [] m e m e
| step :
  GSeqStep t1 m1 e1 m2 e2 ->
  GSeqReduce t2 m2 e2 m3 e3 ->
  GSeqReduce (t1 ++ t2) m1 e1 m3 e3

theorem gseqreduce_trans {t1 t2 : Trace} {m1 m2 m3 : Memory} {e1 e2 e3 : Exp {}}
    (hred1 : GSeqReduce t1 m1 e1 m2 e2)
    (hred2 : GSeqReduce t2 m2 e2 m3 e3) :
    GSeqReduce (t1 ++ t2) m1 e1 m3 e3 := by
  induction hred1 with
  | refl => exact hred2
  | step h rest ih =>
    rw [List.append_assoc]
    exact GSeqReduce.step h (ih hred2)

theorem GSeqReduce.toSeqReduce {t : Trace} {m m' : Memory} {e e' : Exp {}}
    (h : GSeqReduce t m e m' e') : SeqReduce t m e m' e' := by
  induction h with
  | refl => exact SeqReduce.refl
  | step h _ ih => exact SeqReduce.step h.toSeqStep ih

theorem GSeqReduce.toReduce {t : Trace} {m m' : Memory} {e e' : Exp {}}
    (h : GSeqReduce t m e m' e') : Reduce t m e m' e' := by
  induction h with
  | refl => exact Reduce.refl
  | step h _ ih => exact Reduce.step h.toStep ih

/-- Guarded sequential congruence: a head reduction lifts into `letin`. -/
theorem gseqreduce_ctx_letin {C : Trace} {m m' : Memory} {e1 e1' : Exp {}} {e2 : Exp ({},x)}
    (hred : GSeqReduce C m e1 m' e1') :
    GSeqReduce C m (.letin e1 e2) m' (.letin e1' e2) := by
  induction hred with
  | refl => exact GSeqReduce.refl
  | step h _ ih => exact GSeqReduce.step (GSeqStep.step_ctx_letin h) ih

theorem gseqreduce_ctx_unpack {tt : Trace} {m m' : Memory} {e1 e1' : Exp {}}
    {n : Nat} {e2 : Exp ((Sig.extendCVars {} n),x)}
    (hred : GSeqReduce tt m e1 m' e1') :
    GSeqReduce tt m (.unpack n e1 e2) m' (.unpack n e1' e2) := by
  induction hred with
  | refl => exact GSeqReduce.refl
  | step h _ ih => exact GSeqReduce.step (GSeqStep.step_ctx_unpack h) ih

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
  | step_apply _ | step_invoke _ _ | step_tapply _ | step_capply _ | step_consumer_app _
  | step_unwrap _
  | step_cond_var_true _ | step_cond_var_false _ | step_read _ _
  | step_write _ _ | step_drop _
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
  | step_apply _ | step_invoke _ _ | step_tapply _ | step_capply _ | step_consumer_app _
  | step_unwrap _
  | step_cond_var_true _ | step_cond_var_false _ | step_read _ _
  | step_rename | step_unpack | step_par_join _ _ => rfl
  | step_write hx _ =>
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
  | step_apply _ | step_invoke _ _ | step_tapply _ | step_capply _ | step_consumer_app _
  | step_unwrap _
  | step_cond_var_true _ | step_cond_var_false _ | step_read _ _
  | step_rename | step_unpack | step_par_join _ _ => rfl
  | step_write hx _ =>
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
theorem Memory.update_mcell_lookup_agree {ma mb : Memory} {x c : Nat} {bb : Nat} {ℓ pa pb qa qb}
    (hag : ∀ l, l ≠ c → ma.lookup l = mb.lookup l) :
    ∀ l, l ≠ c →
      (ma.update_mcell x bb ℓ pa qa).lookup l = (mb.update_mcell x bb ℓ pb qb).lookup l := by
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
theorem Memory.extend_mcell_lookup_agree {ma mb : Memory} {l c : Nat} {bb : Nat}
    {pa : ma.heap l = none} {pb : mb.heap l = none} {qa qb}
    (hag : ∀ k, k ≠ c → ma.lookup k = mb.lookup k) :
    ∀ k, k ≠ c → (ma.extend_mcell l bb pa qa).lookup k = (mb.extend_mcell l bb pb qb).lookup k := by
  intro k hkc
  by_cases hkl : k = l
  · subst hkl; rw [Memory.extend_mcell_lookup pa qa, Memory.extend_mcell_lookup pb qb]
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
  | step_consumer_app hlk =>
    obtain ⟨ci, hci⟩ := hc
    exact ⟨mb, SeqStep.step_consumer_app ((hag _ (Memory.val_ne_cap hci hlk)) ▸ hlk),
      hag, rfl⟩
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
  | step_write hx hy =>
    obtain ⟨ci, hci⟩ := hc
    have hxc : _ ≠ c := fun h => hnt (Or.inl h.symm)
    have hyb : mb.heap _ ≠ none := match hwf with
      | .wf_write _ (.wf_free h) => Option.ne_none_iff_exists'.mpr ⟨_, h⟩
    refine ⟨mb.update_mcell _ _ .live ⟨_, (hag _ hxc) ▸ hx⟩ (fun _ => hyb),
      SeqStep.step_write ((hag _ hxc) ▸ hx) hyb,
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
    have hxb : mb.heap _ ≠ none := match hwf with
      | .wf_alloc (.wf_free h) => Option.ne_none_iff_exists'.mpr ⟨_, h⟩
    refine ⟨mb.extend_mcell _ _ hfreshb hxb,
      SeqStep.step_alloc hxb hfreshb,
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
  | step_consumer_app hlk =>
    match hwf with
    | .wf_consumer_app (.wf_free (n := xx) hx1) _ =>
      have hxc : xx ≠ c := fun h => by
        rw [h] at hx1; rw [show mb.heap c = none from hcb] at hx1; cases hx1
      exact ⟨mb, SeqStep.step_consumer_app ((hag xx hxc) ▸ hlk), hag, hcb,
        by simp [Trace.touched]⟩
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
  | step_write hlkx hlky =>
    cases hwf with
    | wf_write hwfx hwfy => cases hwfx with | wf_free hxb => cases hwfy with | wf_free hyb =>
      have hxc := Memory.present_ne_absent hxb hcb
      have hyb' : mb.heap _ ≠ none := Option.ne_none_iff_exists'.mpr ⟨_, hyb⟩
      refine ⟨mb.update_mcell _ _ .live ⟨_, (hag _ hxc) ▸ hlkx⟩ (fun _ => hyb'),
        SeqStep.step_write ((hag _ hxc) ▸ hlkx) hyb',
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
      have hfreshb : mb.heap _ = none := (hag _ hlc).symm.trans hfresh
      have hxb' : mb.heap _ ≠ none := Option.ne_none_iff_exists'.mpr ⟨_, hx1⟩
      refine ⟨mb.extend_mcell _ _ hfreshb hxb',
        SeqStep.step_alloc hxb' hfreshb,
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
  | step_consumer_app hlk =>
    exact ⟨mb, hrun, Step.step_consumer_app (SeqStep.val_preserved hrun hlk)⟩
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
  | step_write hx hy =>
    rename_i x m0 y n0
    have hcx : (m0.update_mcell x y .live ⟨n0, hx⟩ (fun _ => hy)).lookup x =
        some (Cell.capability (.mcell y .live)) := by
      simp only [Memory.lookup, Memory.update_mcell, Heap.update_cell, if_true]
    have hnal : ¬ Trace.allocd s x := fun ha => by
      have hh := SeqStep.alloc_fresh hrun ha
      rw [show (m0.update_mcell x y .live ⟨n0, hx⟩ (fun _ => hy)).lookup x = _
            from hcx] at hh
      cases hh
    have hntsx : ¬ Trace.touched s x :=
      Trace.not_touched_of_noninterfere hsep (Or.inl ⟨rfl, by simp, rfl⟩) (by simp) hnal
    obtain ⟨mc, run, ag, cpres⟩ :=
      hrun.frame_off ⟨_, hcx⟩ ⟨_, hx⟩
        (fun l hl => Memory.update_mcell_lookup_ne hl) hntsx hwf1
    have mcx : mc.lookup x = some (Cell.capability (.mcell n0 .live)) := cpres.trans hx
    have mcy : mc.heap y ≠ none :=
      fun h => hy (Heap.none_of_subsumes_none (step_memory_monotonic run) h)
    have hmb : mc.update_mcell x y .live ⟨n0, mcx⟩ (fun _ => mcy) = mb := by
      apply Memory.ext_lookup; intro l
      by_cases hlx : l = x
      · subst hlx
        rw [show (mc.update_mcell l y .live ⟨n0, mcx⟩ (fun _ => mcy)).lookup l
                = some (Cell.capability (.mcell y .live)) from by
              simp only [Memory.lookup, Memory.update_mcell, Heap.update_cell, if_true],
            SeqStep.untouched_preserved hrun (by rw [hcx]; simp) hntsx, hcx]
      · rw [Memory.update_mcell_lookup_ne hlx, ag l hlx]
    exact ⟨mc, run, hmb ▸ Step.step_write mcx mcy⟩
  | step_alloc hlk hfresh =>
    rename_i l m0 x
    have hcl : (m0.extend_mcell l x hfresh hlk).lookup l =
        some (Cell.capability (.mcell x .live)) := Memory.extend_mcell_lookup hfresh hlk
    obtain ⟨mc, run, ag, cpres, hnt⟩ :=
      hrun.frame_off_fresh ⟨_, hcl⟩ hfresh
        (fun k hk => by
          simp only [Memory.lookup, Memory.extend_mcell, Heap.extend_mcell, if_neg hk]) hwf1
    have mcx : mc.heap x ≠ none :=
      fun h => hlk (Heap.none_of_subsumes_none (step_memory_monotonic run) h)
    have hmb : mc.extend_mcell l x cpres mcx = mb := by
      apply Memory.ext_lookup; intro k
      by_cases hkl : k = l
      · subst hkl
        rw [Memory.extend_mcell_lookup cpres mcx,
            SeqStep.untouched_preserved hrun (by rw [hcl]; simp) hnt, hcl]
      · rw [show (mc.extend_mcell l x cpres mcx).lookup k = mc.lookup k from by
              simp only [Memory.lookup, Memory.extend_mcell, Heap.extend_mcell, if_neg hkl],
            ag k hkl]
    exact ⟨mc, run, hmb ▸ Step.step_alloc mcx cpres⟩
  | step_drop hx =>
    rename_i x m0 b0
    have hcx : (m0.drop_mcell x ⟨_, hx⟩).lookup x =
        some (Cell.capability (.mcell 0 .dead)) := by
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
                = some (Cell.capability (.mcell 0 .dead)) from by
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
  | step_apply _ | step_invoke _ _ | step_tapply _ | step_capply _ | step_consumer_app _
  | step_unwrap _
  | step_cond_var_true _ | step_cond_var_false _ | step_read _ _
  | step_rename | step_unpack | step_par_join _ _ => exact Memory.subsumes_refl _
  | step_par_left _ _ _ ih => exact ih
  | step_par_right _ _ _ ih => exact ih
  | step_write hx hy =>
    exact Memory.update_mcell_subsumes _ _ _ _ ⟨_, hx⟩ (fun _ => hy)
  | step_alloc hx hfresh => exact Memory.extend_mcell_subsumes _ _ _ hfresh hx
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
theorem SeqReduceN.unpack_inv : ∀ {n : Nat} {t : Trace} {m mf : Memory} {nb : Nat}
    {eh a : Exp {}} {ek : Exp ((Sig.extendCVars {} nb),x)},
    SeqReduceN n t m (.unpack nb eh ek) mf a → a.IsAns →
    ∃ (nh : Nat) (th : Trace) (mh : Memory) (cs : List.Vector (CaptureSet {}) nb)
      (x : Var .var {}) (trest : Trace),
      SeqReduceN nh th m eh mh (.pack cs x) ∧
      SeqReduce trest mh (.unpack nb (.pack cs x) ek) mf a ∧ t = th ++ trest ∧ nh < n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ihn =>
    intro t m mf nb eh ek a hred hans
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
  | step_apply _ | step_invoke _ _ | step_tapply _ | step_capply _ | step_consumer_app _
  | step_unwrap _
  | step_cond_var_true _ | step_cond_var_false _ | step_read _ _
  | step_write _ _ | step_drop _
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

/-- A simple answer is an answer. -/
theorem Exp.IsSimpleAns.toIsAns {e : Exp {}} (h : e.IsSimpleAns) : e.IsAns := by
  cases h with
  | is_simple_val hv => exact Exp.IsAns.is_val (Exp.isVal_of_isSimpleVal hv)
  | is_var => exact Exp.IsAns.is_var

/-- Trace non-interference is symmetric. -/
theorem Trace.Noninterfere.symm {t s : Trace} (h : Trace.Noninterfere t s) :
    Trace.Noninterfere s t :=
  fun l cm1 cm2 h1 h2 => ⟨(h l cm2 cm1 h2 h1).2, (h l cm2 cm1 h2 h1).1⟩

/-- A genuine interleaving step keeps a cell its trace allocates present afterwards. -/
theorem Step.allocd_present {t : Trace} {m1 m2 : Memory} {e1 e2 : Exp {}} {l : Nat}
    (hstep : Step t m1 e1 m2 e2) (hal : Trace.allocd t l) : m2.heap l ≠ none := by
  induction hstep with
  | step_apply _ | step_invoke _ _ | step_tapply _ | step_capply _ | step_consumer_app _
  | step_unwrap _
  | step_cond_var_true _ | step_cond_var_false _ | step_read _ _
  | step_write _ _ | step_drop _
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
  | step_consumer_app hlk => exact step_preserves_wf (SeqStep.step_consumer_app hlk) hwf
  | step_unwrap hlk => exact step_preserves_wf (SeqStep.step_unwrap hlk) hwf
  | step_cond_var_true hlk => exact step_preserves_wf (SeqStep.step_cond_var_true hlk) hwf
  | step_cond_var_false hlk => exact step_preserves_wf (SeqStep.step_cond_var_false hlk) hwf
  | step_read h1 h2 => exact step_preserves_wf (SeqStep.step_read h1 h2) hwf
  | step_write h1 h2 => exact step_preserves_wf (SeqStep.step_write h1 h2) hwf
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
  | step_apply _ | step_invoke _ _ | step_tapply _ | step_capply _ | step_consumer_app _
  | step_unwrap _
  | step_cond_var_true _ | step_cond_var_false _ | step_read _ _
  | step_write _ _ | step_drop _
  | step_rename | step_unpack | step_par_join _ _ | step_lift _ _ _ =>
    simp only [Trace.allocd] at hal
  | step_alloc hx hfresh =>
    simp only [Trace.allocd, or_false] at hal; subst hal
    exact ⟨_, Memory.extend_mcell_lookup hfresh hx⟩
  | step_ctx_letin _ ih | step_ctx_unpack _ ih
  | step_par_left _ _ _ ih | step_par_right _ _ _ ih => exact ih hal

/-! ## Guard algebra

  The per-step `par`-guards of a guarded run compose to whole-phase bounds and,
  conversely, whole-phase bounds split back into per-step guards.  The currency is
  `TraceOkFrom`'s exemption set: the annotation's `growByAllocs`-growth corresponds
  exactly to `capsOf` of the trace's allocations (`growByAllocs_reachability_le/ge`),
  which `TraceOkFrom` re-buckets between budget and exemptions
  (`absorb_exempt` / `unabsorb_exempt`). -/

/-- Converse of `TraceOkFrom.absorb_exempt_aux`: re-bucket budget caps over `A`
  back into exemptions. -/
theorem TraceOkFrom.unabsorb_exempt_aux {C : CapabilitySet} {A : List Nat} :
  ∀ {D : List Nat} {t : Trace},
    TraceOkFrom (C ∪ capsOf A) D t -> TraceOkFrom C (D ++ A) t := by
  intro D t
  induction t generalizing D with
  | nil => intro _; exact TraceOkFrom.nil
  | cons it t ih =>
    intro h
    cases it with
    | alloc l =>
      cases h with
      | alloc h =>
        exact TraceOkFrom.alloc (ih (D := l :: D)
          (by simpa only [List.cons_append] using h))
    | access mu l =>
      cases h with
      | access hc h =>
        refine TraceOkFrom.access ?_ (ih h)
        rcases hc with hcov | hin
        · cases hcov with
          | left hc' => exact Or.inl hc'
          | right hc' =>
            obtain ⟨mu', hmem', _⟩ := CapabilitySet.covers_imp_exists_hasmem hc'
            exact Or.inr (List.mem_append.mpr (Or.inr (capsOf_hasmem hmem')))
        · exact Or.inr (List.mem_append.mpr (Or.inl hin))
    | dealloc l =>
      cases h with
      | dealloc hc h =>
        refine TraceOkFrom.dealloc ?_ (ih h)
        rcases hc with hcov | hin
        · cases hcov with
          | left hc' => exact Or.inl hc'
          | right hc' =>
            obtain ⟨mu', hmem', _⟩ := CapabilitySet.covers_imp_exists_hasmem hc'
            exact Or.inr (List.mem_append.mpr (Or.inr (capsOf_hasmem hmem')))
        · exact Or.inr (List.mem_append.mpr (Or.inl hin))

/-- A capability cell survives memory growth as a capability cell
  (`Cell.subsumes` never relates a capability to a value/masked cell). -/
theorem Memory.capability_persists {m1 m2 : Memory} {l : Nat} {info : CapabilityInfo}
    (hsub : m2.subsumes m1) (h : m1.heap l = some (.capability info)) :
    ∃ info', m2.heap l = some (.capability info') := by
  obtain ⟨c', hc', hsubc⟩ := hsub l (.capability info) h
  cases c' with
  | val _ => simp [Cell.subsumes] at hsubc
  | masked => simp [Cell.subsumes] at hsubc
  | capability info' => exact ⟨info', hc'⟩

/-- Cells allocated by a guarded sequential run are capability cells at its end. -/
theorem GSeqReduce.allocd_mcell {t : Trace} {m m' : Memory} {e e' : Exp {}} {l : Nat}
    (hred : GSeqReduce t m e m' e') (hal : Trace.allocd t l) :
    ∃ info, m'.heap l = some (.capability info) := by
  induction hred with
  | refl => simp only [Trace.allocd] at hal
  | step h1 hrest ih =>
    rcases Trace.allocd_append.mp hal with h | h
    · obtain ⟨info, hinfo⟩ := step_allocd_mcell h1.toSeqStep h
      exact Memory.capability_persists
        (reduce_memory_monotonic hrest.toSeqReduce) hinfo
    · exact ih h

/-- **Guard composition.**  A step's guard at the initial annotation composes with the
  continuation's bound at the grown annotation into a whole-trace bound at the
  initial annotation: the growth is exactly `capsOf` of the step's allocations,
  which `TraceOkFrom` re-buckets as exemptions. -/
theorem TraceOk.guard_compose {m m2 : Memory} {C : CaptureSet {}} {t1 t2 : Trace}
    (hsub : m2.subsumes m) (hwfC : C.WfInHeap m.heap)
    (hlive : ∀ l, l ∈ Trace.allocList t1 → ∃ info, m2.heap l = some (.capability info))
    (h1 : TraceOk t1 (C.reachability m))
    (h2 : TraceOk t2 ((C.growByAllocs t1).reachability m2)) :
    TraceOk (t1 ++ t2) (C.reachability m) := by
  have hmono : C.reachability m2 = C.reachability m :=
    CaptureSet.reachability_monotonic hsub C hwfC
  have hle : (C.growByAllocs t1).reachability m2
      ⊆ (C.reachability m) ∪ capsOf (Trace.allocList t1) := by
    have h := growByAllocs_reachability_le (m := m2) (t := t1) (C := C) hlive
    rwa [hmono] at h
  have h2' : TraceOkFrom ((C.reachability m) ∪ capsOf (Trace.allocList t1)) [] t2 :=
    TraceOk.mono hle h2
  have h2'' : TraceOkFrom (C.reachability m) (Trace.allocList t1) t2 := by
    simpa using TraceOkFrom.unabsorb_exempt_aux (D := []) h2'
  refine TraceOkFrom.append_seq h1 ?_
  simpa using h2''

/-- **Guard splitting** (converse of `guard_compose`): a whole-trace bound at the
  initial annotation restricts to the continuation at the grown annotation. -/
theorem TraceOk.guard_split {m m2 : Memory} {C : CaptureSet {}} {t1 t2 : Trace}
    (hsub : m2.subsumes m) (hwfC : C.WfInHeap m.heap)
    (hlive : ∀ l, l ∈ Trace.allocList t1 → ∃ info, m2.heap l = some (.capability info))
    (h : TraceOk (t1 ++ t2) (C.reachability m)) :
    TraceOk t2 ((C.growByAllocs t1).reachability m2) := by
  have hsplit : TraceOkFrom (C.reachability m) (Trace.allocList t1 ++ []) t2 :=
    TraceOkFrom.split_append h
  have habs : TraceOk t2 ((C.reachability m) ∪ capsOf (Trace.allocList t1 ++ [])) :=
    TraceOkFrom.absorb_exempt hsplit
  rw [List.append_nil] at habs
  refine TraceOk.mono ?_ habs
  have hmono : C.reachability m2 = C.reachability m :=
    CaptureSet.reachability_monotonic hsub C hwfC
  refine CapabilitySet.Subset.union_left ?_
    (capsOf_subset_growByAllocs_reachability hlive)
  rw [← hmono]
  exact growByAllocs_reachability_ge

/-- Non-interference survives one side's `growByAllocs`-growth: the added caps sit at
  freshly allocated locations, absent from the other side's (dom-respecting)
  reachability. -/
theorem ni_growByAllocs {m m2 : Memory} {C1 C2 : CaptureSet {}} {t : Trace}
    (hsub : m2.subsumes m) (hwfC1 : C1.WfInHeap m.heap) (hwfC2 : C2.WfInHeap m.heap)
    (hlive : ∀ l, l ∈ Trace.allocList t → ∃ info, m2.heap l = some (.capability info))
    (hfresh : ∀ l, l ∈ Trace.allocList t → m.heap l = none)
    (hni : CapabilitySet.Noninterference (C1.reachability m) (C2.reachability m)) :
    CapabilitySet.Noninterference
      ((C1.growByAllocs t).reachability m2) (C2.reachability m2) := by
  have hmono1 : C1.reachability m2 = C1.reachability m :=
    CaptureSet.reachability_monotonic hsub C1 hwfC1
  have hmono2 : C2.reachability m2 = C2.reachability m :=
    CaptureSet.reachability_monotonic hsub C2 hwfC2
  have hle : (C1.growByAllocs t).reachability m2
      ⊆ (C1.reachability m) ∪ capsOf (Trace.allocList t) := by
    have h := growByAllocs_reachability_le (m := m2) (t := t) (C := C1) hlive
    rwa [hmono1] at h
  rw [hmono2]
  refine CapabilitySet.Noninterference.subset_left ?_ hle
  refine CapabilitySet.Noninterference.ni_union hni
    (CapabilitySet.noninterference_capsOf_fresh ?_)
  intro l hl mu' hm
  exact (CaptureSet.reachability_dom hm) (hfresh l hl)

/-- Annotation well-formedness after a guarded run's growth. -/
theorem gseq_growByAllocs_wf {t : Trace} {m m2 : Memory} {C : CaptureSet {}}
    {e e' : Exp {}}
    (hred : GSeqReduce t m e m2 e') (hwfC : C.WfInHeap m.heap) :
    (C.growByAllocs t).WfInHeap m2.heap := by
  refine CaptureSet.growByAllocs_wf
    (CaptureSet.wf_monotonic (reduce_memory_monotonic hred.toSeqReduce) hwfC) ?_
  intro l hl
  obtain ⟨info, hinfo⟩ := hred.allocd_mcell (Trace.mem_allocList.mp hl)
  simp [hinfo]

/-! ## Guarded `par` congruences and assembly -/

/-- **Guarded `par`-left congruence.**  A guarded branch run whose whole trace is
  bounded at the initial annotation lifts into the `par` with every lifted step
  guarded — per-step guards are recovered by `TraceOk.prefix`/`guard_split`. -/
theorem gseqreduce_par_left {tL : Trace} {m m' : Memory} {C1 C2 : CaptureSet {}}
    {e1 e1' e2 : Exp {}}
    (hred : GSeqReduce tL m e1 m' e1')
    (htok : TraceOk tL (C1.reachability m))
    (hni : CapabilitySet.Noninterference (C1.reachability m) (C2.reachability m))
    (hwfC1 : C1.WfInHeap m.heap) (hwfC2 : C2.WfInHeap m.heap) :
    GSeqReduce tL m (.par C1 C2 e1 e2) m' (.par (C1.growByAllocs tL) C2 e1' e2) := by
  induction hred generalizing C1 with
  | refl => exact GSeqReduce.refl
  | step h1 rest ih =>
    rename_i t1 mA e1a mB e1b trest mC e1c
    have hsub : mB.subsumes mA := step_memory_monotonic h1.toSeqStep
    have hlive : ∀ l, l ∈ Trace.allocList t1 →
        ∃ info, mB.heap l = some (.capability info) :=
      fun l hl => step_allocd_mcell h1.toSeqStep (Trace.mem_allocList.mp hl)
    have hfresh : ∀ l, l ∈ Trace.allocList t1 → mA.heap l = none :=
      fun l hl => step_allocd_fresh h1.toSeqStep (Trace.mem_allocList.mp hl)
    have htok' := TraceOk.guard_split hsub hwfC1 hlive htok
    have hni' := ni_growByAllocs hsub hwfC1 hwfC2 hlive hfresh hni
    have hwfC1' := CaptureSet.growByAllocs_wf (CaptureSet.wf_monotonic hsub hwfC1)
      (fun l hl => step_allocd_present h1.toSeqStep (Trace.mem_allocList.mp hl))
    have hwfC2' := CaptureSet.wf_monotonic hsub hwfC2
    rw [CaptureSet.growByAllocs_append]
    exact GSeqReduce.step (GSeqStep.step_par_left h1 (TraceOk.prefix htok) hni)
      (ih htok' hni' hwfC1' hwfC2')

/-- **Guarded `par`-right congruence** (left branch frozen as an answer). -/
theorem gseqreduce_par_right {tR : Trace} {m m' : Memory} {C1 C2 : CaptureSet {}}
    {a e2 e2' : Exp {}}
    (hans : a.IsAns)
    (hred : GSeqReduce tR m e2 m' e2')
    (htok : TraceOk tR (C2.reachability m))
    (hni : CapabilitySet.Noninterference (C1.reachability m) (C2.reachability m))
    (hwfC1 : C1.WfInHeap m.heap) (hwfC2 : C2.WfInHeap m.heap) :
    GSeqReduce tR m (.par C1 C2 a e2) m' (.par C1 (C2.growByAllocs tR) a e2') := by
  induction hred generalizing C2 with
  | refl => exact GSeqReduce.refl
  | step h1 rest ih =>
    rename_i t1 mA e2a mB e2b trest mC e2c
    have hsub : mB.subsumes mA := step_memory_monotonic h1.toSeqStep
    have hlive : ∀ l, l ∈ Trace.allocList t1 →
        ∃ info, mB.heap l = some (.capability info) :=
      fun l hl => step_allocd_mcell h1.toSeqStep (Trace.mem_allocList.mp hl)
    have hfresh : ∀ l, l ∈ Trace.allocList t1 → mA.heap l = none :=
      fun l hl => step_allocd_fresh h1.toSeqStep (Trace.mem_allocList.mp hl)
    have htok' := TraceOk.guard_split hsub hwfC2 hlive htok
    have hni' := (ni_growByAllocs hsub hwfC2 hwfC1 hlive hfresh
      (CapabilitySet.Noninterference.ni_symm hni)).ni_symm
    have hwfC2' := CaptureSet.growByAllocs_wf (CaptureSet.wf_monotonic hsub hwfC2)
      (fun l hl => step_allocd_present h1.toSeqStep (Trace.mem_allocList.mp hl))
    have hwfC1' := CaptureSet.wf_monotonic hsub hwfC1
    rw [CaptureSet.growByAllocs_append]
    exact GSeqReduce.step (GSeqStep.step_par_right hans (TraceOk.prefix htok) hni h1)
      (ih htok' hni' hwfC1' hwfC2')

/-- **Guarded `par` assembly.**  Rebuild a full guarded `par` run (left phase, right
  phase, join) from guarded phase runs, phase bounds, and the root guards. -/
theorem gseqreduce_par_assemble {tL tR : Trace} {m mmid mf : Memory}
    {C1 C2 : CaptureSet {}} {eL eR aL aR : Exp {}}
    (hredL : GSeqReduce tL m eL mmid aL) (haL : aL.IsAns)
    (hredR : GSeqReduce tR mmid eR mf aR) (haR : aR.IsAns)
    (htokL : TraceOk tL (C1.reachability m))
    (htokR : TraceOk tR (C2.reachability mmid))
    (hni : CapabilitySet.Noninterference (C1.reachability m) (C2.reachability m))
    (hwfC1 : C1.WfInHeap m.heap) (hwfC2 : C2.WfInHeap m.heap) :
    GSeqReduce (tL ++ tR) m (.par C1 C2 eL eR) mf .unit := by
  have hsub : mmid.subsumes m := reduce_memory_monotonic hredL.toSeqReduce
  have hlive : ∀ l, l ∈ Trace.allocList tL →
      ∃ info, mmid.heap l = some (.capability info) :=
    fun l hl => hredL.allocd_mcell (Trace.mem_allocList.mp hl)
  have hfresh : ∀ l, l ∈ Trace.allocList tL → m.heap l = none :=
    fun l hl => SeqReduce.alloc_fresh hredL.toSeqReduce (Trace.mem_allocList.mp hl)
  have hni_mid : CapabilitySet.Noninterference
      ((C1.growByAllocs tL).reachability mmid) (C2.reachability mmid) :=
    ni_growByAllocs hsub hwfC1 hwfC2 hlive hfresh hni
  have hwfC1' : (C1.growByAllocs tL).WfInHeap mmid.heap := gseq_growByAllocs_wf hredL hwfC1
  have hwfC2' : C2.WfInHeap mmid.heap := CaptureSet.wf_monotonic hsub hwfC2
  have hjoin : GSeqReduce [] mf
      (.par (C1.growByAllocs tL) (C2.growByAllocs tR) aL aR) mf .unit :=
    GSeqReduce.step (GSeqStep.step_par_join haL haR) GSeqReduce.refl
  have hphase2 := gseqreduce_par_right (C1 := C1.growByAllocs tL) haL hredR htokR
    hni_mid.ni_symm.ni_symm hwfC1' hwfC2'
  have hphase1 := gseqreduce_par_left (C2 := C2) (e2 := eR) hredL htokL hni hwfC1 hwfC2
  have hcomp := gseqreduce_trans hphase1 (gseqreduce_trans hphase2 hjoin)
  simpa using hcomp

/-! ## Guarded step-indexed runs and inversions -/

/-- Step-indexed guarded sequential runs — the measure driving `absorb`. -/
inductive GSeqReduceN : Nat → Trace → Memory → Exp {} → Memory → Exp {} → Prop where
| refl : GSeqReduceN 0 [] m e m e
| step : GSeqStep t1 m1 e1 m2 e2 → GSeqReduceN n t2 m2 e2 m3 e3 →
    GSeqReduceN (n + 1) (t1 ++ t2) m1 e1 m3 e3

theorem GSeqReduceN.toGSeqReduce {n : Nat} {t : Trace} {m m' : Memory} {e e' : Exp {}}
    (h : GSeqReduceN n t m e m' e') : GSeqReduce t m e m' e' := by
  induction h with
  | refl => exact GSeqReduce.refl
  | step h1 _ ih => exact GSeqReduce.step h1 ih

theorem GSeqReduce.toN {t : Trace} {m m' : Memory} {e e' : Exp {}}
    (h : GSeqReduce t m e m' e') : ∃ n, GSeqReduceN n t m e m' e' := by
  induction h with
  | refl => exact ⟨0, GSeqReduceN.refl⟩
  | step h1 _ ih => obtain ⟨n, hn⟩ := ih; exact ⟨n + 1, GSeqReduceN.step h1 hn⟩

/-- Answers take no guarded sequential step. -/
theorem GSeqStep.not_isAns {t : Trace} {m m' : Memory} {a e' : Exp {}}
    (hstep : GSeqStep t m a m' e') (hans : a.IsAns) : False :=
  seqstep_ans_absurd hans hstep.toSeqStep

/-- A step-indexed guarded run from an answer is the trivial one. -/
theorem GSeqReduceN.eq_of_isAns {n : Nat} {t : Trace} {m m' : Memory} {a a' : Exp {}}
    (h : GSeqReduceN n t m a m' a') (hans : a.IsAns) :
    n = 0 ∧ t = [] ∧ m' = m ∧ a' = a := by
  cases h with
  | refl => exact ⟨rfl, rfl, rfl, rfl⟩
  | step h1 _ => exact (h1.not_isAns hans).elim

set_option maxHeartbeats 1000000 in
-- Large strong-induction case split composing per-step guards into phase bounds.
/-- **Guarded `par` decomposition.**  A guarded sequential run of `par D1 D2 eL eR`
  to an answer splits into a guarded left run, then a guarded right run, then the
  join — AND the per-step guards compose (`TraceOk.guard_compose`) into whole-phase
  bounds at the phase-start annotations. -/
theorem GSeqReduceN.par_inv : ∀ {n : Nat} {t : Trace} {m mf : Memory}
    {D1 D2 : CaptureSet {}} {eL eR a : Exp {}},
    GSeqReduceN n t m (.par D1 D2 eL eR) mf a → a.IsAns →
    Exp.WfInHeap (.par D1 D2 eL eR) m.heap →
    ∃ nL tL mmid aL nR tR aR,
      GSeqReduceN nL tL m eL mmid aL ∧ aL.IsAns ∧
      GSeqReduceN nR tR mmid eR mf aR ∧ aR.IsAns ∧
      a = .unit ∧ t = tL ++ tR ∧ nL + nR < n ∧
      TraceOk tL (D1.reachability m) ∧ TraceOk tR (D2.reachability mmid) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ihn =>
    intro t m mf D1 D2 eL eR a hred hans hwf
    have hwfC1 : D1.WfInHeap m.heap := by cases hwf with | wf_par h _ _ _ => exact h
    have hwfC2 : D2.WfInHeap m.heap := by cases hwf with | wf_par _ h _ _ => exact h
    cases hred with
    | refl => cases hans with | is_val hv => cases hv
    | step h1 hrest =>
      cases h1 with
      | step_par_left inner ht hni =>
        obtain ⟨nL', tL', mmid, aL, nR, tR, aR, hredL, haL, hredR, haR, hau, ht2, hlt,
          htokL', htokR'⟩ := ihn _ (Nat.lt_succ_self _) hrest hans
            (step_preserves_wf (SeqStep.step_par_left inner.toSeqStep) hwf)
        refine ⟨nL' + 1, _, mmid, aL, nR, tR, aR,
          GSeqReduceN.step inner hredL, haL, hredR, haR, hau,
          by rw [ht2, List.append_assoc], by omega,
          TraceOk.guard_compose (step_memory_monotonic inner.toSeqStep) hwfC1
            (fun l hl => step_allocd_mcell inner.toSeqStep (Trace.mem_allocList.mp hl))
            ht htokL', htokR'⟩
      | step_par_right haL ht hni inner =>
        obtain ⟨nL', tL', mmid, aL', nR', tR', aR, hredL, _, hredR, haR, hau, ht2, hlt,
          htokL', htokR'⟩ := ihn _ (Nat.lt_succ_self _) hrest hans
            (step_preserves_wf (SeqStep.step_par_right haL inner.toSeqStep) hwf)
        obtain ⟨_, htL0, hmmideq, haLeq⟩ := hredL.eq_of_isAns haL
        subst htL0; subst hmmideq
        refine ⟨0, [], m, eL, nR' + 1, _, aR, GSeqReduceN.refl, haL,
          GSeqReduceN.step inner hredR, haR, hau, by rw [ht2]; rfl, by omega,
          TraceOk.nil, TraceOk.guard_compose (step_memory_monotonic inner.toSeqStep)
            hwfC2
            (fun l hl => step_allocd_mcell inner.toSeqStep (Trace.mem_allocList.mp hl))
            ht htokR'⟩
      | step_par_join hL hR =>
        obtain ⟨_, ht20, hmfeq, haeq⟩ :=
          hrest.eq_of_isAns (Exp.IsAns.is_val Exp.IsVal.unit)
        subst ht20; subst hmfeq
        exact ⟨0, [], mf, eL, 0, [], eR, GSeqReduceN.refl, hL, GSeqReduceN.refl, hR,
          haeq, rfl, by omega, TraceOk.nil, TraceOk.nil⟩

/-- **Guarded `letin` decomposition** (mirror of `SeqReduceN.letin_inv`). -/
theorem GSeqReduceN.letin_inv : ∀ {n : Nat} {t : Trace} {m mf : Memory}
    {eh a : Exp {}} {ek : Exp ({},x)},
    GSeqReduceN n t m (.letin eh ek) mf a → a.IsAns →
    ∃ nh th mh vh trest, GSeqReduceN nh th m eh mh vh ∧ vh.IsSimpleAns ∧
      GSeqReduce trest mh (.letin vh ek) mf a ∧ t = th ++ trest ∧ nh < n := by
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
        exact ⟨nh' + 1, _, mh, vh, trest, GSeqReduceN.step inner hh, hvh, hrestr,
          by rw [ht2, List.append_assoc], by omega⟩
      | step_rename =>
        exact ⟨0, [], m, _, _, GSeqReduceN.refl, Exp.IsSimpleAns.is_var,
          GSeqReduce.step GSeqStep.step_rename hrest.toGSeqReduce, by simp, by omega⟩
      | step_lift hv hwf_v hfresh =>
        exact ⟨0, [], m, _, _, GSeqReduceN.refl, Exp.IsSimpleAns.is_simple_val hv,
          GSeqReduce.step (GSeqStep.step_lift hv hwf_v hfresh) hrest.toGSeqReduce,
          by simp, by omega⟩

/-- **Guarded `unpack` decomposition** (mirror of `SeqReduceN.unpack_inv`). -/
theorem GSeqReduceN.unpack_inv : ∀ {n : Nat} {t : Trace} {m mf : Memory} {nb : Nat}
    {eh a : Exp {}} {ek : Exp ((Sig.extendCVars {} nb),x)},
    GSeqReduceN n t m (.unpack nb eh ek) mf a → a.IsAns →
    ∃ (nh : Nat) (th : Trace) (mh : Memory) (cs : List.Vector (CaptureSet {}) nb)
      (x : Var .var {}) (trest : Trace),
      GSeqReduceN nh th m eh mh (.pack cs x) ∧
      GSeqReduce trest mh (.unpack nb (.pack cs x) ek) mf a ∧ t = th ++ trest ∧ nh < n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ihn =>
    intro t m mf nb eh ek a hred hans
    cases hred with
    | refl => cases hans with | is_val hv => cases hv
    | step h1 hrest =>
      cases h1 with
      | step_ctx_unpack inner =>
        obtain ⟨nh', th', mh, cs, x, trest, hh, hrestr, ht2, hlt⟩ :=
          ihn _ (Nat.lt_succ_self _) hrest hans
        exact ⟨nh' + 1, _, mh, cs, x, trest, GSeqReduceN.step inner hh, hrestr,
          by rw [ht2, List.append_assoc], by omega⟩
      | step_unpack =>
        exact ⟨0, [], m, _, _, _, GSeqReduceN.refl,
          GSeqReduce.step GSeqStep.step_unpack hrest.toGSeqReduce, by simp, by omega⟩

/-! ## Guard transport across the diamond -/

set_option maxHeartbeats 1000000 in
-- Large parallel case split (every SeqStep constructor against the guarded original).
/-- **Guard transport.**  The bit-exact replay (from a SMALLER memory) of a guarded
  sequential step is itself guarded: leaf steps carry their own data; `par` guards
  transport along `CaptureSet.reachability_monotonic` (reachability is
  `subsumes`-invariant for well-formed annotations). -/
theorem GSeqStep.transport {t : Trace} {m2 m2' m1 m1' : Memory} {e eg' es' : Exp {}}
    (hg : GSeqStep t m2 e m2' eg') (hs : SeqStep t m1 e m1' es')
    (hsub : m2.subsumes m1) (hwf : Exp.WfInHeap e m1.heap) :
    GSeqStep t m1 e m1' es' := by
  induction hs generalizing m2 m2' eg' with
  | step_apply hlk => exact GSeqStep.step_apply hlk
  | step_invoke h1 h2 => exact GSeqStep.step_invoke h1 h2
  | step_tapply hlk => exact GSeqStep.step_tapply hlk
  | step_capply hlk => exact GSeqStep.step_capply hlk
  | step_consumer_app hlk => exact GSeqStep.step_consumer_app hlk
  | step_unwrap hlk => exact GSeqStep.step_unwrap hlk
  | step_cond_var_true hlk => exact GSeqStep.step_cond_var_true hlk
  | step_cond_var_false hlk => exact GSeqStep.step_cond_var_false hlk
  | step_read h1 h2 => exact GSeqStep.step_read h1 h2
  | step_write h1 h2 => exact GSeqStep.step_write h1 h2
  | step_alloc h1 h2 => exact GSeqStep.step_alloc h1 h2
  | step_drop hx => exact GSeqStep.step_drop hx
  | step_rename => exact GSeqStep.step_rename
  | step_lift hv hwf_v hfresh => exact GSeqStep.step_lift hv hwf_v hfresh
  | step_unpack => exact GSeqStep.step_unpack
  | step_par_join h1 h2 => exact GSeqStep.step_par_join h1 h2
  | step_ctx_letin inner ih =>
    cases hg with
    | step_ctx_letin hg1 =>
      exact GSeqStep.step_ctx_letin (ih hg1 hsub (Exp.wf_inv_letin hwf).1)
    | step_rename => cases inner
    | step_lift hv _ _ => cases hv <;> cases inner
  | step_ctx_unpack inner ih =>
    cases hg with
    | step_ctx_unpack hg1 =>
      exact GSeqStep.step_ctx_unpack (ih hg1 hsub (Exp.wf_inv_unpack hwf).1)
    | step_unpack => cases inner
  | step_par_left inner ih =>
    cases hwf with
    | wf_par hwfC1 hwfC2 hwf_e1 hwf_e2 =>
      cases hg with
      | step_par_left hg1 ht hni =>
        rw [CaptureSet.reachability_monotonic hsub _ hwfC1] at ht hni
        rw [CaptureSet.reachability_monotonic hsub _ hwfC2] at hni
        exact GSeqStep.step_par_left (ih hg1 hsub hwf_e1) ht hni
      | step_par_right hansg _ _ _ =>
        exact (seqstep_ans_absurd hansg inner).elim
      | step_par_join hansg _ =>
        exact (seqstep_ans_absurd hansg inner).elim
  | step_par_right hans inner ih =>
    cases hwf with
    | wf_par hwfC1 hwfC2 hwf_e1 hwf_e2 =>
      cases hg with
      | step_par_right _ ht hni hg1 =>
        rw [CaptureSet.reachability_monotonic hsub _ hwfC2] at ht hni
        rw [CaptureSet.reachability_monotonic hsub _ hwfC1] at hni
        exact GSeqStep.step_par_right hans ht hni (ih hg1 hsub hwf_e2)
      | step_par_left hg1 _ _ =>
        exact (GSeqStep.not_isAns hg1 hans).elim
      | step_par_join _ hansg =>
        exact (seqstep_ans_absurd hansg inner).elim

/-- Guarded step-vs-run commute: project, swap with the plain diamond
  (`step_reduce_swap`), and re-guard each replayed step by `GSeqStep.transport`. -/
theorem gstep_reduce_swap {tb ta : Trace} {m mb mLfin : Memory} {eR eR' eL eLres : Exp {}}
    (hstep : Step tb m eR mb eR')
    (hrun : GSeqReduce ta mb eL mLfin eLres)
    (hsep : Trace.Noninterfere ta tb)
    (hwfL : Exp.WfInHeap eL m.heap)
    (hwfR : Exp.WfInHeap eR m.heap) :
    ∃ mc, GSeqReduce ta m eL mc eLres ∧ Step tb mc eR mLfin eR' := by
  induction hrun generalizing m eR' with
  | refl => exact ⟨m, GSeqReduce.refl, hstep⟩
  | step h1 hrest ih =>
    obtain ⟨mc1, h1', hstep'⟩ :=
      step_step_swap hstep h1.toSeqStep (Trace.noninterfere_append_left hsep) hwfL hwfR
    have h1g := h1.transport h1' (Step.subsumes hstep) hwfL
    obtain ⟨mc, hrest', hstepf⟩ :=
      ih hstep' (Trace.noninterfere_append_right_step hsep hstep h1.toSeqStep)
        (step_preserves_wf h1' hwfL)
        (Exp.wf_monotonic (step_memory_monotonic h1') hwfR)
    exact ⟨mc, GSeqReduce.step h1g hrest', hstepf⟩

set_option maxHeartbeats 1000000 in
-- Large case split: the `par` cases thread the diamond, fed by the runs' own guards.
/-- **Absorb a step into a guarded sequential run.**  Prepending a (possibly
  premature, interleaving) `Step` to a left-first GUARDED sequential run recovers a
  guarded left-first run reaching the SAME final state, up to `Trace.Equiv` (with
  the same allocations).  ALL separation content — trace bounds and
  non-interference — comes from the guards of the prepended step and of the given
  run (`GSeqReduceN.par_inv` composes the latter's per-step guards into phase
  bounds); NO safety carrier is consulted, so no carrier needs to be
  (un-reconstructibly) transported across genuine steps.  Well-founded on the
  run's step index. -/
theorem absorb : ∀ {n : Nat} {t1 t2 : Trace} {m0 m1 mf : Memory} {e e1 a : Exp {}},
    GSeqReduceN n t2 m1 e1 mf a → Step t1 m0 e m1 e1 → Exp.WfInHeap e m0.heap →
    a.IsAns → ∃ t', GSeqReduce t' m0 e mf a ∧ Trace.Equiv (t1 ++ t2) t' ∧
      (∀ l, Trace.allocd (t1 ++ t2) l ↔ Trace.allocd t' l) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ihn =>
    intro t1 t2 m0 m1 mf e e1 a hred hstep hwf hans
    cases hstep with
    | step_apply hlk =>
      exact ⟨_, GSeqReduce.step (GSeqStep.step_apply hlk) hred.toGSeqReduce,
        Trace.Equiv.refl _, fun l => Iff.rfl⟩
    | step_invoke h1 h2 =>
      exact ⟨_, GSeqReduce.step (GSeqStep.step_invoke h1 h2) hred.toGSeqReduce,
        Trace.Equiv.refl _, fun l => Iff.rfl⟩
    | step_tapply hlk =>
      exact ⟨_, GSeqReduce.step (GSeqStep.step_tapply hlk) hred.toGSeqReduce,
        Trace.Equiv.refl _, fun l => Iff.rfl⟩
    | step_capply hlk =>
      exact ⟨_, GSeqReduce.step (GSeqStep.step_capply hlk) hred.toGSeqReduce,
        Trace.Equiv.refl _, fun l => Iff.rfl⟩
    | step_consumer_app hlk =>
      exact ⟨_, GSeqReduce.step (GSeqStep.step_consumer_app hlk) hred.toGSeqReduce,
        Trace.Equiv.refl _, fun l => Iff.rfl⟩
    | step_unwrap hlk =>
      exact ⟨_, GSeqReduce.step (GSeqStep.step_unwrap hlk) hred.toGSeqReduce,
        Trace.Equiv.refl _, fun l => Iff.rfl⟩
    | step_cond_var_true hlk =>
      exact ⟨_, GSeqReduce.step (GSeqStep.step_cond_var_true hlk) hred.toGSeqReduce,
        Trace.Equiv.refl _, fun l => Iff.rfl⟩
    | step_cond_var_false hlk =>
      exact ⟨_, GSeqReduce.step (GSeqStep.step_cond_var_false hlk) hred.toGSeqReduce,
        Trace.Equiv.refl _, fun l => Iff.rfl⟩
    | step_read h1 h2 =>
      exact ⟨_, GSeqReduce.step (GSeqStep.step_read h1 h2) hred.toGSeqReduce,
        Trace.Equiv.refl _, fun l => Iff.rfl⟩
    | step_write h1 h2 =>
      exact ⟨_, GSeqReduce.step (GSeqStep.step_write h1 h2) hred.toGSeqReduce,
        Trace.Equiv.refl _, fun l => Iff.rfl⟩
    | step_alloc h1 h2 =>
      exact ⟨_, GSeqReduce.step (GSeqStep.step_alloc h1 h2) hred.toGSeqReduce,
        Trace.Equiv.refl _, fun l => Iff.rfl⟩
    | step_drop hx =>
      exact ⟨_, GSeqReduce.step (GSeqStep.step_drop hx) hred.toGSeqReduce,
        Trace.Equiv.refl _, fun l => Iff.rfl⟩
    | step_rename =>
      exact ⟨_, GSeqReduce.step GSeqStep.step_rename hred.toGSeqReduce,
        Trace.Equiv.refl _, fun l => Iff.rfl⟩
    | step_lift hv hwf_v hfresh =>
      exact ⟨_, GSeqReduce.step (GSeqStep.step_lift hv hwf_v hfresh) hred.toGSeqReduce,
        Trace.Equiv.refl _, fun l => Iff.rfl⟩
    | step_unpack =>
      exact ⟨_, GSeqReduce.step GSeqStep.step_unpack hred.toGSeqReduce,
        Trace.Equiv.refl _, fun l => Iff.rfl⟩
    | step_par_join h1 h2 =>
      exact ⟨_, GSeqReduce.step (GSeqStep.step_par_join h1 h2) hred.toGSeqReduce,
        Trace.Equiv.refl _, fun l => Iff.rfl⟩
    | step_ctx_letin inner =>
      obtain ⟨nh', th', mh, vh, trest, hh, hvh, hrestr, ht2, hlt⟩ := hred.letin_inv hans
      subst ht2
      obtain ⟨hwf_eh, _⟩ := Exp.wf_inv_letin hwf
      obtain ⟨th'', hehred, heqh, haeh⟩ :=
        ihn nh' (by omega) hh inner hwf_eh hvh.toIsAns
      refine ⟨th'' ++ trest,
        gseqreduce_trans (gseqreduce_ctx_letin hehred) hrestr, ?_, ?_⟩
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
        ihn nh' (by omega) hh inner hwf_eh (Exp.IsAns.is_val Exp.IsVal.pack)
      refine ⟨th'' ++ trest,
        gseqreduce_trans (gseqreduce_ctx_unpack hehred) hrestr, ?_, ?_⟩
      · rw [show t1 ++ (th' ++ trest) = (t1 ++ th') ++ trest from by rw [List.append_assoc]]
        exact Trace.Equiv.append_right_congr heqh haeh
      · intro l
        calc Trace.allocd (t1 ++ (th' ++ trest)) l
            ↔ Trace.allocd (t1 ++ th') l ∨ Trace.allocd trest l := by
              rw [← List.append_assoc]; exact Trace.allocd_append
          _ ↔ Trace.allocd th'' l ∨ Trace.allocd trest l := or_congr_left (haeh l)
          _ ↔ Trace.allocd (th'' ++ trest) l := Trace.allocd_append.symm
    | step_par_left inner ht hni_g =>
      obtain ⟨hwf_eL, _⟩ := Exp.wf_inv_par hwf
      cases hwf with
      | wf_par hwfC1 hwfC2 hwf_eL' hwf_eR' =>
      have hwf1 := Step.preserves_wf (Step.step_par_left inner ht hni_g)
        (Exp.WfInHeap.wf_par hwfC1 hwfC2 hwf_eL' hwf_eR')
      obtain ⟨nL', tL', mmid, aL, nR, tR, aR, hredL, haL, hredR, haR, hau, ht2, hlt,
        htokL', htokR'⟩ := hred.par_inv hans hwf1
      subst ht2; subst hau
      obtain ⟨tL'', hredL'', heqL, haeL⟩ :=
        ihn nL' (by omega) hredL inner hwf_eL haL
      have hsub1 : _ := Step.subsumes inner
      have hlive1 : ∀ l, l ∈ Trace.allocList t1 →
          ∃ info, m1.heap l = some (.capability info) :=
        fun l hl => Step.allocd_mcell inner (Trace.mem_allocList.mp hl)
      have htokL0 := TraceOk.guard_compose hsub1 hwfC1 hlive1 ht htokL'
      have htokL'' := TraceOk.equiv_invariant htokL0 heqL
      refine ⟨tL'' ++ tR,
        gseqreduce_par_assemble hredL'' haL hredR.toGSeqReduce haR htokL'' htokR'
          hni_g hwfC1 hwfC2, ?_, ?_⟩
      · rw [show t1 ++ (tL' ++ tR) = (t1 ++ tL') ++ tR from by rw [List.append_assoc]]
        exact Trace.Equiv.append_right_congr heqL haeL
      · intro l
        calc Trace.allocd (t1 ++ (tL' ++ tR)) l
            ↔ Trace.allocd (t1 ++ tL') l ∨ Trace.allocd tR l := by
              rw [← List.append_assoc]; exact Trace.allocd_append
          _ ↔ Trace.allocd tL'' l ∨ Trace.allocd tR l := or_congr_left (haeL l)
          _ ↔ Trace.allocd (tL'' ++ tR) l := Trace.allocd_append.symm
    | step_par_right ht hni_g inner =>
      rename_i eR0 eRs C1 C2 eL0
      cases hwf with
      | wf_par hwfC1 hwfC2 hwf_eL hwf_eR =>
      have hwf1 := Step.preserves_wf (Step.step_par_right ht hni_g inner)
        (Exp.WfInHeap.wf_par hwfC1 hwfC2 hwf_eL hwf_eR)
      obtain ⟨nL, tL, mmid, aL, nR', tR', aR, hredL, haL, hredR, haR, hau, ht2, hlt,
        htokL', htokR'⟩ := hred.par_inv hans hwf1
      subst ht2; subst hau
      have hsub1 := Step.subsumes inner
      have htokL0 : TraceOk tL (C1.reachability m0) := by
        rwa [CaptureSet.reachability_monotonic hsub1 C1 hwfC1] at htokL'
      have hsep : Trace.Noninterfere tL t1 := traceOk_noninterfere htokL0 ht hni_g
      obtain ⟨mc, hredL', hstep1'⟩ :=
        gstep_reduce_swap inner hredL.toGSeqReduce hsep hwf_eL hwf_eR
      have hsubc := reduce_memory_monotonic hredL'.toSeqReduce
      obtain ⟨tR'', hredR'', heqR, haeR⟩ :=
        ihn nR' (by omega) hredR hstep1'
          (Exp.wf_monotonic hsubc hwf_eR) haR
      have hsub_mid1 := reduce_memory_monotonic hredL.toGSeqReduce.toSeqReduce
      have hsub_mid0 := Memory.subsumes_trans hsub_mid1 hsub1
      have hlive1 : ∀ l, l ∈ Trace.allocList t1 →
          ∃ info, mmid.heap l = some (.capability info) := by
        intro l hl
        obtain ⟨info, hinfo⟩ := Step.allocd_mcell inner (Trace.mem_allocList.mp hl)
        exact Memory.capability_persists hsub_mid1 hinfo
      have htokR0 := TraceOk.guard_compose hsub_mid0 hwfC2 hlive1 ht htokR'
      have htokR'' : TraceOk tR'' (C2.reachability mc) := by
        have h0 := TraceOk.equiv_invariant htokR0 heqR
        rw [CaptureSet.reachability_monotonic hsubc C2 hwfC2]
        exact h0
      have hasm := gseqreduce_par_assemble hredL' haL hredR'' haR htokL0 htokR''
        hni_g hwfC1 hwfC2
      have hf1 : ∀ l, Trace.allocd tL l → Trace.extSeq l t1 = [] := fun l hal =>
        fresh_not_extSeq ht
          (Heap.none_of_subsumes_none hsub1
            (SeqReduce.alloc_fresh hredL.toGSeqReduce.toSeqReduce hal))
      have hf2 : ∀ l, Trace.allocd t1 l → Trace.extSeq l tL = [] := fun l hal =>
        fresh_not_extSeq htokL0 (Step.alloc_fresh inner hal)
      have hcomm : Trace.Equiv (t1 ++ tL) (tL ++ t1) :=
        Trace.equiv_comm_of_noninterfere hsep.symm hf1 hf2
      have hcommAE : ∀ l, Trace.allocd (t1 ++ tL) l ↔ Trace.allocd (tL ++ t1) l := by
        intro l; rw [Trace.allocd_append, Trace.allocd_append]; exact or_comm
      refine ⟨tL ++ tR'', hasm, ?_, ?_⟩
      · have stepA : Trace.Equiv (t1 ++ (tL ++ tR')) (tL ++ (t1 ++ tR')) := by
          rw [← List.append_assoc, ← List.append_assoc]
          exact Trace.Equiv.append_right_congr hcomm hcommAE
        have stepB : Trace.Equiv (tL ++ (t1 ++ tR')) (tL ++ tR'') :=
          Trace.Equiv.append_left_congr heqR
        exact stepA.trans stepB
      · intro l
        calc Trace.allocd (t1 ++ (tL ++ tR')) l
            ↔ Trace.allocd t1 l ∨ Trace.allocd tL l ∨ Trace.allocd tR' l := by
              rw [Trace.allocd_append, Trace.allocd_append]
          _ ↔ Trace.allocd tL l ∨ Trace.allocd t1 l ∨ Trace.allocd tR' l := or_left_comm
          _ ↔ Trace.allocd tL l ∨ Trace.allocd (t1 ++ tR') l := by rw [Trace.allocd_append]
          _ ↔ Trace.allocd tL l ∨ Trace.allocd tR'' l := or_congr_right (haeR l)
          _ ↔ Trace.allocd (tL ++ tR'') l := Trace.allocd_append.symm

/-- **Standardization (theorem B) — carrier-free.**  Every genuine interleaving run
  to an answer is matched by a sequential (left-first) run reaching the IDENTICAL
  final memory and answer, the traces differing only by `Trace.Equiv` (Mazurkiewicz
  reordering of independent events).  Folds `absorb` over the run.

  NO safety hypothesis: the separation content that reorders independent steps is
  carried by the interleaving `Step`'s own `par`-guards, composed and re-split by
  the guarded sequential relation `GSeqStep` — never by a carrier that would have
  to be (falsely) transported across genuine steps.  The guarded form of the
  sequential run is also returned. -/
theorem standardization_guarded {m mf : Memory} {e a : Exp {}} {t : Trace}
    (hwf : Exp.WfInHeap e m.heap)
    (hred : Reduce t m e mf a) (hans : a.IsAns) :
    ∃ t', GSeqReduce t' m e mf a ∧ Trace.Equiv t t' := by
  revert hwf hans
  induction hred with
  | refl => exact fun _ _ => ⟨[], GSeqReduce.refl, Trace.Equiv.refl _⟩
  | step h1 hrest ih =>
    intro hwf hans
    obtain ⟨trest', hsr, heq⟩ := ih (Step.preserves_wf h1 hwf) hans
    obtain ⟨n, hn⟩ := hsr.toN
    obtain ⟨t', hst', heq', _⟩ := absorb hn h1 hwf hans
    exact ⟨t', hst', (Trace.Equiv.append_left_congr heq).trans heq'⟩

/-- **Standardization (theorem B).**  Plain-`SeqReduce` corollary of
  `standardization_guarded`. -/
theorem standardization {m mf : Memory} {e a : Exp {}} {t : Trace}
    (hwf : Exp.WfInHeap e m.heap)
    (hred : Reduce t m e mf a) (hans : a.IsAns) :
    ∃ t', SeqReduce t' m e mf a ∧ Trace.Equiv t t' := by
  obtain ⟨t', hg, heq⟩ := standardization_guarded hwf hred hans
  exact ⟨t', hg.toSeqReduce, heq⟩

end CoreCapybara
