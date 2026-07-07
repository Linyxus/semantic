import Semantic.CoreCapybara.Semantics.Standardization

/-! # Prefix trace safety (`PrefixSafe`)

  The mathematical core of interleaving adequacy.  `PrefixSafe k m e R` packages, for
  every WITHIN-BUDGET sequential *prefix* `SeqReduce t m e m' e'`:

  * (i)  a trace bound `TraceOk t R` — the prefix only touches capabilities in `R`;
  * (ii) the *same* run realized in GUARDED form `GSeqReduce t m e m' e'`, whence
         `GSeqReduce.toReduce` embeds it into the genuine interleaving `Reduce`.

  Bundling (ii) into the predicate dissolves the "guardability by induction on `Safe`"
  phase: the composition lemmas below rebuild the guarded run structurally alongside the
  trace bound, mirroring the `Eval.eval_*` family (`BigStep.lean`).  Nothing here mentions
  denotations, so it composes freely into `exp_denot`. -/

namespace CoreCapybara

/-- **Prefix trace safety.**  Every within-budget sequential prefix of `e` from `m` is
  bounded by the capability set `R` and realizable as a guarded sequential run. -/
def PrefixSafe (k : Nat) (m : Memory) (e : Exp {}) (R : CapabilitySet) : Prop :=
  ∀ {t : Trace} {m' : Memory} {e' : Exp {}},
    SeqReduce t m e m' e' → t.readCount < k →
    TraceOk t R ∧ GSeqReduce t m e m' e'

/-! ## Basic lemmas -/

/-- Monotone in the capability set: a larger `R` covers every touch a smaller one does. -/
theorem PrefixSafe.mono {k : Nat} {m : Memory} {e : Exp {}} {R R' : CapabilitySet}
    (hsub : R ⊆ R') (h : PrefixSafe k m e R) : PrefixSafe k m e R' := by
  intro t m' e' hred hbud
  obtain ⟨htok, hg⟩ := h hred hbud
  exact ⟨TraceOk.mono hsub htok, hg⟩

/-- Antitone in the read budget: a run within a smaller budget is within a larger one. -/
theorem PrefixSafe.mono_budget {k j : Nat} {m : Memory} {e : Exp {}} {R : CapabilitySet}
    (hle : j ≤ k) (h : PrefixSafe k m e R) : PrefixSafe j m e R := by
  intro t m' e' hred hbud
  exact h hred (Nat.lt_of_lt_of_le hbud hle)

/-- Answers are prefix-safe: they only reduce reflexively. -/
theorem PrefixSafe.ans {k : Nat} {m : Memory} {e : Exp {}} {R : CapabilitySet}
    (hans : e.IsAns) : PrefixSafe k m e R := by
  intro t m' e' hred _
  obtain ⟨rfl, rfl, rfl⟩ := seqreduce_ans_eq hans hred
  exact ⟨TraceOk.nil, GSeqReduce.refl⟩

/-! ## Annotation-tracking `par` prefix decomposition

  `seqreduce_par_split` (Props) hides the evolved branch annotations existentially; the
  guarded `par` congruences (`gseqreduce_par_left`/`_right`) reach reducts with the
  *specific* `growByAllocs`-grown annotations.  To reconcile the reduct of the given
  prefix with the guarded reconstruction, we re-derive the split tracking exactly those
  grown annotations. -/

/-- **Mid-run `par` decomposition, annotations tracked.**  Like `seqreduce_par_split`, but
  the reduct's branch annotations are pinned to `Cs1.growByAllocs`/`Cs2.growByAllocs` of the
  corresponding phase traces. -/
theorem seqreduce_par_split_ann {t : Trace} {m m' : Memory} {Cs1 Cs2 : CaptureSet {}}
    {e1 e2 X : Exp {}}
    (hred : SeqReduce t m (.par Cs1 Cs2 e1 e2) m' X) :
    (∃ e1', SeqReduce t m e1 m' e1' ∧ X = .par (Cs1.growByAllocs t) Cs2 e1' e2) ∨
    (∃ (t1 t2 : Trace) (m1 : Memory) (a1 e2' : Exp {}),
      SeqReduce t1 m e1 m1 a1 ∧ a1.IsAns ∧ SeqReduce t2 m1 e2 m' e2' ∧
      X = .par (Cs1.growByAllocs t1) (Cs2.growByAllocs t2) a1 e2' ∧ t = t1 ++ t2) ∨
    (∃ (t1 t2 : Trace) (m1 : Memory) (a1 a2 : Exp {}),
      SeqReduce t1 m e1 m1 a1 ∧ a1.IsAns ∧ SeqReduce t2 m1 e2 m' a2 ∧ a2.IsAns ∧
      X = .unit ∧ t = t1 ++ t2) := by
  generalize hgen : Exp.par Cs1 Cs2 e1 e2 = efull at hred
  induction hred generalizing Cs1 Cs2 e1 e2 with
  | refl => exact Or.inl ⟨e1, SeqReduce.refl, hgen.symm⟩
  | step hstep rest ih =>
    rw [←hgen] at hstep
    cases hstep with
    | step_par_left hstep1 =>
      rcases ih rfl with ⟨e1', hr, hX⟩ |
        ⟨t1, t2, m1, a1, e2', hr1, hans1, hr2, hX, ht⟩ |
        ⟨t1, t2, m1, a1, a2, hr1, hans1, hr2, hans2, hX, ht⟩
      · refine Or.inl ⟨e1', SeqReduce.step hstep1 hr, ?_⟩
        rw [hX, CaptureSet.growByAllocs_append]
      · refine Or.inr (Or.inl ⟨_, t2, m1, a1, e2', SeqReduce.step hstep1 hr1, hans1, hr2, ?_,
          by rw [ht, List.append_assoc]⟩)
        rw [hX, CaptureSet.growByAllocs_append]
      · exact Or.inr (Or.inr ⟨_, t2, m1, a1, a2, SeqReduce.step hstep1 hr1, hans1,
          hr2, hans2, hX, by rw [ht, List.append_assoc]⟩)
    | step_par_right hans1 hstep2 =>
      rcases ih rfl with ⟨e1', hr, hX⟩ |
        ⟨t1, t2, m1, a1, e2'', hr1, hans1', hr2, hX, ht⟩ |
        ⟨t1, t2, m1, a1, a2, hr1, hans1', hr2, hans2, hX, ht⟩
      · obtain ⟨rfl, rfl, rfl⟩ := seqreduce_ans_eq hans1 hr
        refine Or.inr (Or.inl ⟨[], _, _, _, _, SeqReduce.refl, hans1,
          SeqReduce.step hstep2 SeqReduce.refl, ?_, by simp⟩)
        rw [hX]; simp
      · obtain ⟨rfl, rfl, rfl⟩ := seqreduce_ans_eq hans1 hr1
        refine Or.inr (Or.inl ⟨[], _, _, _, _, SeqReduce.refl, hans1,
          SeqReduce.step hstep2 hr2, ?_, by simp [ht]⟩)
        rw [hX, CaptureSet.growByAllocs_append]
      · obtain ⟨rfl, rfl, rfl⟩ := seqreduce_ans_eq hans1 hr1
        exact Or.inr (Or.inr ⟨[], _, _, _, _, SeqReduce.refl, hans1,
          SeqReduce.step hstep2 hr2, hans2, hX, by simp [ht]⟩)
    | step_par_join hans1 hans2 =>
      obtain ⟨rfl, rfl, rfl⟩ := seqreduce_ans_eq (Exp.IsAns.is_val Exp.IsVal.unit) rest
      exact Or.inr (Or.inr ⟨[], [], _, _, _, SeqReduce.refl, hans1, SeqReduce.refl,
        hans2, rfl, rfl⟩)

/-- **Covers-based sequential trace composition** (the canonical bind).  A head bound at
  `R` and a continuation bound at `R2` compose into a whole-run bound at `R` when every
  cap the continuation *touches* is either `R`-covered or one of the head's fresh
  allocations (`allocList t1`).  The `touched` guard is load-bearing: it is exactly what
  makes the exemption provable — an accessed cell is a live capability, and the capability
  form is what `appears_allocd_of_cap` needs (see `traceok_bind_run`).  A static
  reachability invariant cannot supply it (reachable cells may be masked). -/
theorem traceok_bind_covers {R R2 : CapabilitySet} {t1 t2 : Trace}
    (htok1 : TraceOk t1 R) (htok2 : TraceOk t2 R2)
    (hbucket : ∀ mode l, Trace.touched t2 l → R2.covers mode l →
      R.covers mode l ∨ l ∈ Trace.allocList t1) :
    TraceOk (t1 ++ t2) R := by
  have h2 : TraceOkFrom R (Trace.allocList t1) t2 := by
    have h := TraceOkFrom.translate (S := Trace.allocList t1) htok2 hbucket
    simpa using h
  exact TraceOkFrom.append_seq htok1 (by simpa using h2)

/-- A guarded sequential *step* only touches (accesses/deallocs) live-capability cells,
  so every touched cell is a capability in the step's RESULT memory (drops leave a dead
  mcell, writes an updated one — both are `.capability`). -/
theorem GSeqStep.touched_cap_result {t : Trace} {m m' : Memory} {e e' : Exp {}}
    (h : GSeqStep t m e m' e') :
    ∀ l, Trace.touched t l → ∃ c, m'.lookup l = some (.capability c) := by
  induction h with
  | step_apply _ | step_tapply _ | step_capply _ | step_consumer_app _ | step_unwrap _
  | step_cond_var_true _ | step_cond_var_false _ | step_alloc _ _ | step_par_join _ _
  | step_rename | step_lift _ _ _ | step_unpack =>
    intro l ht; simp only [Trace.touched] at ht
  | step_invoke hlkx _ =>
    intro l ht; simp only [Trace.touched, or_false] at ht; subst ht; exact ⟨_, hlkx⟩
  | step_read _ hlky =>
    intro l ht; simp only [Trace.touched, or_false] at ht; subst ht; exact ⟨_, hlky⟩
  | step_write hx _ =>
    intro l ht; simp only [Trace.touched, or_false] at ht; subst ht
    simp [Memory.lookup, Memory.update_mcell, Heap.update_cell]
  | step_drop hx =>
    intro l ht; simp only [Trace.touched, or_false] at ht; subst ht
    simp [Memory.lookup, Memory.drop_mcell, Heap.update_cell]
  | step_ctx_letin _ ih | step_ctx_unpack _ ih
  | step_par_left _ _ _ ih | step_par_right _ _ _ _ ih =>
    exact ih

/-- **Touched cells of a guarded sequential run are capabilities** (mirrors
  `BigStep.trace_cells_cap`): the fresh-witness exemption a prefix continuation needs is
  read off the run rather than a static reachability invariant the wf cannot express. -/
theorem GSeqReduce.trace_cells_cap {t : Trace} {m m' : Memory} {e e' : Exp {}}
    (hred : GSeqReduce t m e m' e') :
    ∀ l, Trace.touched t l → ∃ c, m'.lookup l = some (.capability c) := by
  induction hred with
  | refl => intro l ht; simp only [Trace.touched] at ht
  | step h1 hrest ih =>
    intro l ht
    rw [Trace.touched_append] at ht
    rcases ht with h | h
    · obtain ⟨c, hc⟩ := GSeqStep.touched_cap_result h1 l h
      exact Memory.capability_persists (reduce_memory_monotonic hrest.toSeqReduce) hc
    · exact ih l h

/-- A cell present in the smaller memory that is a capability in the larger one is a
  capability in the smaller one too (`Cell.subsumes` never crosses kinds). -/
private theorem Memory.cap_lookup_down {m1 m2 : Memory} {l : Nat} {c0 : Cell}
    {c : CapabilityInfo} (hsub : m2.subsumes m1) (h1 : m1.lookup l = some c0)
    (h2 : m2.lookup l = some (.capability c)) :
    ∃ c', m1.lookup l = some (.capability c') := by
  have h := Memory.lookup_down hsub h1 h2
  cases c0 with
  | val => exact Cell.noConfusion (by simpa only [Cell.subsumes] using h)
  | masked => exact Cell.noConfusion (by simpa only [Cell.subsumes] using h)
  | capability c' => exact ⟨c', h1⟩

/-- **Run-backed bind.**  The continuation's store-fresh exemptions (`m1`-present,
  `m`-absent) become head allocations at *touched* cells: touched ⇒ capability in `mf`
  (`GSeqReduce.trace_cells_cap`), pushed back to a capability in `m1` (present + subsumes),
  which the head run's `appears_allocd_of_cap` places in `allocList t1`.  This is the bind
  the `letin`/`unpack` continuations use. -/
theorem traceok_bind_run {R R2 : CapabilitySet} {m m1 mc mf : Memory}
    {eh vh cont ef : Exp {}} {t1 t2 : Trace}
    (htok1 : TraceOk t1 R) (htok2 : TraceOk t2 R2)
    (hbs1 : BigStep m eh t1 vh m1)
    (hg2 : GSeqReduce t2 mc cont mf ef) (hsub : mf.subsumes m1)
    (hb : ∀ mode l, R2.covers mode l →
      R.covers mode l ∨ (m1.heap l ≠ none ∧ m.lookup l = none)) :
    TraceOk (t1 ++ t2) R := by
  refine traceok_bind_covers htok1 htok2 (fun mode l htouched hcov => ?_)
  rcases hb mode l hcov with hR | ⟨hpres, hfresh⟩
  · exact Or.inl hR
  · right
    rw [Trace.mem_allocList]
    obtain ⟨c, hc_mf⟩ := GSeqReduce.trace_cells_cap hg2 l htouched
    obtain ⟨c0, hc0⟩ := Option.ne_none_iff_exists'.mp hpres
    obtain ⟨c', hc_m1⟩ := Memory.cap_lookup_down hsub hc0 hc_mf
    exact BigStep.appears_allocd_of_cap hbs1 hfresh hc_m1

/-! ## Leaf composition lemmas (mirror `Eval.eval_*`) -/

/-- `app` (β): the reduct is the substituted body; the head step emits `[]`. -/
theorem PrefixSafe.apply {k : Nat} {m : Memory} {x : Nat} {y : Var .var {}}
    {cs T e hv R0} {R : CapabilitySet}
    (hlk : m.lookup x = some (.val ⟨.abs cs T e, hv, R0⟩))
    (hrec : PrefixSafe k m (e.subst (Subst.openVar y)) R) :
    PrefixSafe k m (.app (.free x) y) R := by
  intro t m' e' hred hbud
  cases hred with
  | refl => exact ⟨TraceOk.nil, GSeqReduce.refl⟩
  | step h rest =>
    cases h with
    | step_apply hlk2 =>
      have heq := congrArg HeapVal.unwrap (Memory.lookup_val_eq hlk hlk2)
      simp only at heq
      cases heq
      obtain ⟨htok, hg⟩ := hrec rest (by simpa using hbud)
      exact ⟨by simpa using htok, GSeqReduce.step (GSeqStep.step_apply hlk) hg⟩
    | step_invoke hlkx2 _ => rw [hlk] at hlkx2; exact absurd hlkx2 (by simp)

/-- `invoke`: a basic-capability call to a unit argument; emits `[.access .epsilon x]`. -/
theorem PrefixSafe.invoke {k : Nat} {m : Memory} {x y : Nat} {hv R0} {R : CapabilitySet}
    (hlkx : m.lookup x = some (.capability .basic))
    (hlky : m.lookup y = some (.val ⟨.unit, hv, R0⟩))
    (htok : TraceOk [.access .epsilon x] R) :
    PrefixSafe k m (.app (.free x) (.free y)) R := by
  intro t m' e' hred _
  cases hred with
  | refl => exact ⟨TraceOk.nil, GSeqReduce.refl⟩
  | step h rest =>
    cases h with
    | step_invoke hlkx2 hlky2 =>
      obtain ⟨rfl, rfl, rfl⟩ := seqreduce_ans_eq (Exp.IsAns.is_val Exp.IsVal.unit) rest
      exact ⟨by simpa using htok,
        GSeqReduce.step (GSeqStep.step_invoke hlkx hlky) GSeqReduce.refl⟩
    | step_apply hlk2 => rw [hlkx] at hlk2; exact absurd hlk2 (by simp)

/-- `tapp`: type application; emits `[]`. -/
theorem PrefixSafe.tapply {k : Nat} {m : Memory} {x : Nat} {S} {cs T0 e hv R0}
    {R : CapabilitySet}
    (hlk : m.lookup x = some (.val ⟨.tabs cs T0 e, hv, R0⟩))
    (hrec : PrefixSafe k m (e.subst (Subst.openTVar .top)) R) :
    PrefixSafe k m (.tapp (.free x) S) R := by
  intro t m' e' hred hbud
  cases hred with
  | refl => exact ⟨TraceOk.nil, GSeqReduce.refl⟩
  | step h rest =>
    cases h with
    | step_tapply hlk2 =>
      have heq := congrArg HeapVal.unwrap (Memory.lookup_val_eq hlk hlk2)
      simp only at heq
      cases heq
      obtain ⟨htok, hg⟩ := hrec rest (by simpa using hbud)
      exact ⟨by simpa using htok, GSeqReduce.step (GSeqStep.step_tapply hlk) hg⟩

/-- `capp`: capture application; emits `[]`. -/
theorem PrefixSafe.capply {k : Nat} {m : Memory} {x : Nat} {CS} {cs B0 e hv R0}
    {R : CapabilitySet}
    (hlk : m.lookup x = some (.val ⟨.cabs cs B0 e, hv, R0⟩))
    (hrec : PrefixSafe k m (e.subst (Subst.openCVar CS)) R) :
    PrefixSafe k m (.capp (.free x) CS) R := by
  intro t m' e' hred hbud
  cases hred with
  | refl => exact ⟨TraceOk.nil, GSeqReduce.refl⟩
  | step h rest =>
    cases h with
    | step_capply hlk2 =>
      have heq := congrArg HeapVal.unwrap (Memory.lookup_val_eq hlk hlk2)
      simp only at heq
      cases heq
      obtain ⟨htok, hg⟩ := hrec rest (by simpa using hbud)
      exact ⟨by simpa using htok, GSeqReduce.step (GSeqStep.step_capply hlk) hg⟩

/-- `consumer_app`: the reduct is an `unpack` of the argument against the consumer body. -/
theorem PrefixSafe.consumer_app {k : Nat} {m : Memory} {x : Nat} {arg} {cs T e hv R0}
    {R : CapabilitySet}
    (hlk : m.lookup x = some (.val ⟨.consumer cs (.exi 1 T) e, hv, R0⟩))
    (hrec : PrefixSafe k m (.unpack 1 arg e) R) :
    PrefixSafe k m (.consumer_app (.free x) arg) R := by
  intro t m' e' hred hbud
  cases hred with
  | refl => exact ⟨TraceOk.nil, GSeqReduce.refl⟩
  | step h rest =>
    cases h with
    | step_consumer_app hlk2 =>
      have heq := congrArg HeapVal.unwrap (Memory.lookup_val_eq hlk hlk2)
      simp only at heq
      cases heq
      obtain ⟨htok, hg⟩ := hrec rest (by simpa using hbud)
      exact ⟨by simpa using htok, GSeqReduce.step (GSeqStep.step_consumer_app hlk) hg⟩

/-- `unwrap`: unbox; the reduct is the boxed body; emits `[]`. -/
theorem PrefixSafe.unwrap {k : Nat} {m : Memory} {x : Nat} {cs Ψ e hv R0}
    {R : CapabilitySet}
    (hlk : m.lookup x = some (.val ⟨.boxed cs Ψ e, hv, R0⟩))
    (hrec : PrefixSafe k m e R) :
    PrefixSafe k m (.unwrap (.free x)) R := by
  intro t m' e' hred hbud
  cases hred with
  | refl => exact ⟨TraceOk.nil, GSeqReduce.refl⟩
  | step h rest =>
    cases h with
    | step_unwrap hlk2 =>
      have heq := congrArg HeapVal.unwrap (Memory.lookup_val_eq hlk hlk2)
      simp only at heq
      cases heq
      obtain ⟨htok, hg⟩ := hrec rest (by simpa using hbud)
      exact ⟨by simpa using htok, GSeqReduce.step (GSeqStep.step_unwrap hlk) hg⟩

/-- `cond`: reduces to one branch (resolved from the scrutinee); emits `[]`. -/
theorem PrefixSafe.cond {k : Nat} {m : Memory} {x : Var .var {}} {e2 e3 : Exp {}}
    {R : CapabilitySet}
    (hres : resolve m.heap (.var x) = some .btrue ∨ resolve m.heap (.var x) = some .bfalse)
    (h_true : resolve m.heap (.var x) = some .btrue → PrefixSafe k m e2 R)
    (h_false : resolve m.heap (.var x) = some .bfalse → PrefixSafe k m e3 R) :
    PrefixSafe k m (.cond x e2 e3) R := by
  intro t m' e' hred hbud
  cases hred with
  | refl => exact ⟨TraceOk.nil, GSeqReduce.refl⟩
  | step h rest =>
    cases h with
    | step_cond_var_true hlk2 =>
      obtain ⟨htok, hg⟩ :=
        (h_true (by simp only [resolve, Memory.lookup] at hlk2 ⊢; rw [hlk2])) rest
          (by simpa using hbud)
      exact ⟨by simpa using htok, GSeqReduce.step (GSeqStep.step_cond_var_true hlk2) hg⟩
    | step_cond_var_false hlk2 =>
      obtain ⟨htok, hg⟩ :=
        (h_false (by simp only [resolve, Memory.lookup] at hlk2 ⊢; rw [hlk2])) rest
          (by simpa using hbud)
      exact ⟨by simpa using htok, GSeqReduce.step (GSeqStep.step_cond_var_false hlk2) hg⟩

/-- `read`: dereference a reader cell; emits `[.access .ro y]` and answers a variable. -/
theorem PrefixSafe.read {k : Nat} {m : Memory} {x y n : Nat} {hv R0} {R : CapabilitySet}
    (hlkx : m.lookup x = some (.val ⟨.reader (.free y), hv, R0⟩))
    (hlky : m.lookup y = some (.capability (.mcell n .live)))
    (htok : TraceOk [.access .ro y] R) :
    PrefixSafe k m (.read (.free x)) R := by
  intro t m' e' hred _
  cases hred with
  | refl => exact ⟨TraceOk.nil, GSeqReduce.refl⟩
  | step h rest =>
    cases h with
    | step_read hlkx2 hlky2 =>
      have heq := congrArg HeapVal.unwrap (Memory.lookup_val_eq hlkx hlkx2)
      simp only at heq
      cases heq
      cases hlky.symm.trans hlky2
      obtain ⟨rfl, rfl, rfl⟩ := seqreduce_ans_eq Exp.IsAns.is_var rest
      exact ⟨by simpa using htok,
        GSeqReduce.step (GSeqStep.step_read hlkx hlky) GSeqReduce.refl⟩

/-- `write`: mutate a cell; emits `[.access .epsilon x]` and answers `.unit`. -/
theorem PrefixSafe.write {k : Nat} {m : Memory} {x y : Nat} {n0 : Nat} {R : CapabilitySet}
    (hx : m.lookup x = some (.capability (.mcell n0 .live)))
    (hlky : m.heap y ≠ none)
    (htok : TraceOk [.access .epsilon x] R) :
    PrefixSafe k m (.write (.free x) (.free y)) R := by
  intro t m' e' hred _
  cases hred with
  | refl => exact ⟨TraceOk.nil, GSeqReduce.refl⟩
  | step h rest =>
    cases h with
    | step_write hx2 hy2 =>
      obtain ⟨rfl, rfl, rfl⟩ := seqreduce_ans_eq (Exp.IsAns.is_val Exp.IsVal.unit) rest
      exact ⟨by simpa using htok,
        GSeqReduce.step (GSeqStep.step_write hx hlky) GSeqReduce.refl⟩

/-- `alloc`: allocate a fresh cell; emits `[.alloc l]` (unconditionally `TraceOk`). -/
theorem PrefixSafe.alloc {k : Nat} {m : Memory} {x : Nat} {R : CapabilitySet}
    (hlk : m.heap x ≠ none) :
    PrefixSafe k m (.alloc (.free x)) R := by
  intro t m' e' hred _
  cases hred with
  | refl => exact ⟨TraceOk.nil, GSeqReduce.refl⟩
  | step h rest =>
    cases h with
    | step_alloc hx2 hfresh2 =>
      obtain ⟨rfl, rfl, rfl⟩ := seqreduce_ans_eq (Exp.IsAns.is_val Exp.IsVal.pack) rest
      exact ⟨by simpa using TraceOk.alloc,
        GSeqReduce.step (GSeqStep.step_alloc hlk hfresh2) GSeqReduce.refl⟩

/-- `drop`: deallocate; emits `[.dealloc x]` and answers `.unit`. -/
theorem PrefixSafe.drop {k : Nat} {m : Memory} {x : Nat} {n : Nat} {R : CapabilitySet}
    (hx : m.lookup x = some (.capability (.mcell n .live)))
    (htok : TraceOk [.dealloc x] R) :
    PrefixSafe k m (.drop (.free x)) R := by
  intro t m' e' hred _
  cases hred with
  | refl => exact ⟨TraceOk.nil, GSeqReduce.refl⟩
  | step h rest =>
    cases h with
    | step_drop hx2 =>
      obtain ⟨rfl, rfl, rfl⟩ := seqreduce_ans_eq (Exp.IsAns.is_val Exp.IsVal.unit) rest
      exact ⟨by simpa using htok,
        GSeqReduce.step (GSeqStep.step_drop hx) GSeqReduce.refl⟩

/-! ## Sequencing composition lemmas -/

/-- Every closed term-variable is free: `BVar {} .var` is uninhabited. -/
theorem var_empty_free (y : Var .var {}) : ∃ y0, y = .free y0 := by
  cases y with
  | free y0 => exact ⟨y0, rfl⟩
  | bound b => cases b

/-- `letin`: run the head, then the opened continuation.  The continuation hypotheses are
  conditioned on the head's completed `BigStep` (within budget), at the residual budget. -/
theorem PrefixSafe.letin {k : Nat} {m : Memory} {e1 : Exp {}} {e2 : Exp ({},x)}
    {R : CapabilitySet}
    (hpre1 : PrefixSafe k m e1 R)
    (h_val : ∀ {t1 : Trace} {m1 : Memory} {v : Exp {}},
      BigStep m e1 t1 v m1 → t1.readCount < k →
      (hv : Exp.IsSimpleVal v) → (hwf_v : Exp.WfInHeap v m1.heap) →
      ∀ l' (hfresh : m1.lookup l' = none),
        ∃ R2, (∀ mode l, R2.covers mode l →
              R.covers mode l ∨ (m1.heap l ≠ none ∧ m.lookup l = none)) ∧
          PrefixSafe (k - t1.readCount)
            (m1.extend_val l' ⟨v, hv, compute_reachability m1.heap v hv⟩ hwf_v rfl hfresh)
            (e2.subst (Subst.openVar (.free l'))) R2)
    (h_var : ∀ {t1 : Trace} {m1 : Memory} {x : Var .var {}},
      BigStep m e1 t1 (.var x) m1 → t1.readCount < k →
      ∃ R2, (∀ mode l, R2.covers mode l →
            R.covers mode l ∨ (m1.heap l ≠ none ∧ m.lookup l = none)) ∧
        PrefixSafe (k - t1.readCount) m1 (e2.subst (Subst.openVar x)) R2) :
    PrefixSafe k m (.letin e1 e2) R := by
  intro t m' e' hred hbud
  rcases seqreduce_letin_split hred with
    ⟨e1', hr, hX⟩ |
    ⟨t1, t2, m1, y, hr1, hr2, ht⟩ |
    ⟨t1, t2, m1, v, hv, hwf, l, hfresh, hr1, hr2, ht⟩
  · -- (i) still in head
    subst hX
    obtain ⟨htok1, hg1⟩ := hpre1 hr hbud
    exact ⟨htok1, gseqreduce_ctx_letin hg1⟩
  · -- (ii) head reached a variable, then continuation
    subst ht
    obtain ⟨y0, rfl⟩ := var_empty_free y
    simp only [Trace.readCount_append] at hbud
    have hbud1 : t1.readCount < k := by omega
    obtain ⟨htok1, hg1⟩ := hpre1 hr1 hbud1
    have hbs1 : BigStep m e1 t1 (.var (.free y0)) m1 := reduce_to_bigstep hr1 Exp.IsAns.is_var
    obtain ⟨R2, hbucket, hpre2'⟩ := h_var hbs1 hbud1
    obtain ⟨htok2, hg2⟩ := hpre2' hr2 (by omega)
    refine ⟨traceok_bind_run htok1 htok2 hbs1 hg2
      (reduce_memory_monotonic hg2.toSeqReduce) hbucket, ?_⟩
    exact gseqreduce_trans (gseqreduce_ctx_letin hg1)
      (GSeqReduce.step GSeqStep.step_rename hg2)
  · -- (iii) head reached a simple value, lift, then continuation
    subst ht
    simp only [Trace.readCount_append] at hbud
    have hbud1 : t1.readCount < k := by omega
    obtain ⟨htok1, hg1⟩ := hpre1 hr1 hbud1
    have hbs1 : BigStep m e1 t1 v m1 :=
      reduce_to_bigstep hr1 (Exp.IsAns.is_val (Exp.isVal_of_isSimpleVal hv))
    obtain ⟨R2, hbucket, hpre2'⟩ := h_val hbs1 hbud1 hv hwf l hfresh
    obtain ⟨htok2, hg2⟩ := hpre2' hr2 (by omega)
    refine ⟨traceok_bind_run htok1 htok2 hbs1 hg2
      (Memory.subsumes_trans (reduce_memory_monotonic hg2.toSeqReduce)
        (Memory.extend_val_subsumes m1 l ⟨v, hv, compute_reachability m1.heap v hv⟩ hwf rfl hfresh))
      hbucket, ?_⟩
    exact gseqreduce_trans (gseqreduce_ctx_letin hg1)
      (GSeqReduce.step (GSeqStep.step_lift hv hwf hfresh) hg2)

/-- `unpack`: run the head to a `pack`, then the opened continuation. -/
theorem PrefixSafe.unpack {k : Nat} {m : Memory} {n : Nat} {e1 : Exp {}}
    {e2 : Exp ((Sig.extendCVars {} n),x)} {R : CapabilitySet}
    (hpre1 : PrefixSafe k m e1 R)
    (h_val : ∀ {t1 : Trace} {m1 : Memory} {x : Var .var {}}
        {cs : List.Vector (CaptureSet {}) n},
      BigStep m e1 t1 (.pack cs x) m1 → t1.readCount < k →
      ∃ R2, (∀ mode l, R2.covers mode l →
            R.covers mode l ∨ (m1.heap l ≠ none ∧ m.lookup l = none)) ∧
        PrefixSafe (k - t1.readCount) m1 (e2.subst (Subst.unpack cs x)) R2) :
    PrefixSafe k m (.unpack n e1 e2) R := by
  intro t m' e' hred hbud
  rcases seqreduce_unpack_split hred with
    ⟨e1', hr, hX⟩ |
    ⟨t1, t2, m1, cs, y, hr1, hr2, ht⟩
  · -- (i) still in head
    subst hX
    obtain ⟨htok1, hg1⟩ := hpre1 hr hbud
    exact ⟨htok1, gseqreduce_ctx_unpack hg1⟩
  · -- (ii) head reached a pack, then continuation
    subst ht
    obtain ⟨y0, rfl⟩ := var_empty_free y
    simp only [Trace.readCount_append] at hbud
    have hbud1 : t1.readCount < k := by omega
    obtain ⟨htok1, hg1⟩ := hpre1 hr1 hbud1
    have hbs1 : BigStep m e1 t1 (.pack cs (.free y0)) m1 :=
      reduce_to_bigstep hr1 (Exp.IsAns.is_val Exp.IsVal.pack)
    obtain ⟨R2, hbucket, hpre2'⟩ := h_val hbs1 hbud1
    obtain ⟨htok2, hg2⟩ := hpre2' hr2 (by omega)
    refine ⟨traceok_bind_run htok1 htok2 hbs1 hg2
      (reduce_memory_monotonic hg2.toSeqReduce) hbucket, ?_⟩
    exact gseqreduce_trans (gseqreduce_ctx_unpack hg1)
      (GSeqReduce.step GSeqStep.step_unpack hg2)

/-- **`par` (the crux).**  Left prefix bounded by `Cs1`, right continuation bounded by
  `Cs2` (conditioned on the completed left run), non-interfering — the whole `par` prefix
  is bounded by the union and realizable as a guarded run. -/
theorem PrefixSafe.par {k : Nat} {m : Memory} {Cs1 Cs2 : CaptureSet {}} {e1 e2 : Exp {}}
    (hwf1 : Cs1.WfInHeap m.heap) (hwf2 : Cs2.WfInHeap m.heap)
    (hpre1 : PrefixSafe k m e1 (Cs1.reachability m))
    (hpre2 : ∀ {t1 : Trace} {v1 : Exp {}} {m1 : Memory},
      BigStep m e1 t1 v1 m1 → t1.readCount < k →
      PrefixSafe (k - t1.readCount) m1 e2 (Cs2.reachability m1))
    (hni : CapabilitySet.Noninterference (Cs1.reachability m) (Cs2.reachability m)) :
    PrefixSafe k m (.par Cs1 Cs2 e1 e2)
      (Cs1.reachability m ∪ Cs2.reachability m) := by
  intro t m' e' hred hbud
  rcases seqreduce_par_split_ann hred with
    ⟨e1', hr, hX⟩ |
    ⟨t1, t2, m1, a1, e2', hr1, hans1, hr2, hX, ht⟩ |
    ⟨t1, t2, m1, a1, a2, hr1, hans1, hr2, hans2, hX, ht⟩
  · -- (i) left-only prefix
    subst hX
    obtain ⟨htok1, hg1⟩ := hpre1 hr hbud
    exact ⟨TraceOk.mono CapabilitySet.Subset.union_right_left htok1,
      gseqreduce_par_left hg1 htok1 hni hwf1 hwf2⟩
  · -- (ii) left answered, right in progress
    subst ht; subst hX
    simp only [Trace.readCount_append] at hbud
    have hbud1 : t1.readCount < k := by omega
    obtain ⟨htok1, hg1⟩ := hpre1 hr1 hbud1
    have hbs1 : BigStep m e1 t1 a1 m1 := reduce_to_bigstep hr1 hans1
    obtain ⟨htok2m1, hg2⟩ := hpre2 hbs1 hbud1 hr2 (by omega)
    have hsub : m1.subsumes m := reduce_memory_monotonic hr1
    have hmono2 : Cs2.reachability m1 = Cs2.reachability m :=
      CaptureSet.reachability_monotonic hsub Cs2 hwf2
    have htok2 : TraceOk t2 (Cs2.reachability m) := hmono2 ▸ htok2m1
    have hlive : ∀ l, l ∈ Trace.allocList t1 →
        ∃ info, m1.heap l = some (.capability info) :=
      fun l hl => hg1.allocd_mcell (Trace.mem_allocList.mp hl)
    have hfresh : ∀ l, l ∈ Trace.allocList t1 → m.heap l = none :=
      fun l hl => SeqReduce.alloc_fresh hr1 (Trace.mem_allocList.mp hl)
    have hni_mid : CapabilitySet.Noninterference
        ((Cs1.growByAllocs t1).reachability m1) (Cs2.reachability m1) :=
      ni_growByAllocs hsub hwf1 hwf2 hlive hfresh hni
    have hwfC1' : (Cs1.growByAllocs t1).WfInHeap m1.heap := gseq_growByAllocs_wf hg1 hwf1
    have hwfC2' : Cs2.WfInHeap m1.heap := CaptureSet.wf_monotonic hsub hwf2
    refine ⟨TraceOk.append (TraceOk.mono CapabilitySet.Subset.union_right_left htok1)
      (TraceOk.mono CapabilitySet.Subset.union_right_right htok2), ?_⟩
    exact gseqreduce_trans (gseqreduce_par_left hg1 htok1 hni hwf1 hwf2)
      (gseqreduce_par_right hans1 hg2 htok2m1 hni_mid hwfC1' hwfC2')
  · -- (iii) both answered, joined
    subst ht; subst hX
    simp only [Trace.readCount_append] at hbud
    have hbud1 : t1.readCount < k := by omega
    obtain ⟨htok1, hg1⟩ := hpre1 hr1 hbud1
    have hbs1 : BigStep m e1 t1 a1 m1 := reduce_to_bigstep hr1 hans1
    obtain ⟨htok2m1, hg2⟩ := hpre2 hbs1 hbud1 hr2 (by omega)
    have hsub : m1.subsumes m := reduce_memory_monotonic hr1
    have hmono2 : Cs2.reachability m1 = Cs2.reachability m :=
      CaptureSet.reachability_monotonic hsub Cs2 hwf2
    have htok2 : TraceOk t2 (Cs2.reachability m) := hmono2 ▸ htok2m1
    refine ⟨TraceOk.append (TraceOk.mono CapabilitySet.Subset.union_right_left htok1)
      (TraceOk.mono CapabilitySet.Subset.union_right_right htok2), ?_⟩
    exact gseqreduce_par_assemble hg1 hans1 hg2 hans2 htok1 htok2m1 hni hwf1 hwf2

end CoreCapybara
