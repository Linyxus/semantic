import Semantic.CoreCapybara.Semantics.SmallStep
import Semantic.CoreCapybara.Semantics.BigStep
namespace CoreCapybara

/-- The result of looking up a variable in the heap is deterministic. -/
theorem Heap.lookup_deterministic {H : Heap}
  (hlookup1 : H l = some v1)
  (hlookup2 : H l = some v2) :
  v1 = v2 := Option.some.inj (hlookup1.symm.trans hlookup2)

/-- The result of looking up a variable in the memory is deterministic. -/
theorem Memory.lookup_deterministic {m : Memory}
  (hlookup1 : m.lookup l = some v1)
  (hlookup2 : m.lookup l = some v2) :
  v1 = v2 := by
  cases m
  simp only [Memory.lookup] at hlookup1 hlookup2
  exact Heap.lookup_deterministic hlookup1 hlookup2

/-- Every simple value is a value. -/
theorem Exp.isVal_of_isSimpleVal {v : Exp s} (hv : v.IsSimpleVal) : v.IsVal := by
  cases hv <;> constructor

/-- Helper: Congruence for Reduce in letin context. -/
theorem reduce_ctx_letin
  (hred : Reduce C m e1 m' e1') :
  Reduce C m (.letin e1 e2) m' (.letin e1' e2) := by
  induction hred with
  | refl => exact Reduce.refl
  | step h _ ih => exact Reduce.step (Step.step_ctx_letin h) ih

/-- Helper: Congruence for Reduce in unpack context. -/
theorem reduce_ctx_unpack
  (hred : Reduce C m e1 m' e1') :
  Reduce C m (.unpack e1 e2) m' (.unpack e1' e2) := by
  induction hred with
  | refl => exact Reduce.refl
  | step h _ ih => exact Reduce.step (Step.step_ctx_unpack h) ih

/-- Sequential congruence: a `SeqReduce` of the LEFT branch of `letin` lifts. -/
theorem seqreduce_ctx_letin
  (hred : SeqReduce C m e1 m' e1') :
  SeqReduce C m (.letin e1 e2) m' (.letin e1' e2) := by
  induction hred with
  | refl => exact SeqReduce.refl
  | step h _ ih => exact SeqReduce.step (SeqStep.step_ctx_letin h) ih

theorem seqreduce_ctx_unpack
  (hred : SeqReduce C m e1 m' e1') :
  SeqReduce C m (.unpack e1 e2) m' (.unpack e1' e2) := by
  induction hred with
  | refl => exact SeqReduce.refl
  | step h _ ih => exact SeqReduce.step (SeqStep.step_ctx_unpack h) ih

theorem seqreduce_par_left {C : Trace} {m m' : Memory}
  {Cs1 Cs2 : CaptureSet {}} {e1 e1' e2 : Exp {}}
  (hred : SeqReduce C m e1 m' e1') :
  SeqReduce C m (.par Cs1 Cs2 e1 e2) m' (.par (Cs1.growByAllocs C) Cs2 e1' e2) := by
  induction hred generalizing Cs1 with
  | refl => exact SeqReduce.refl
  | step h _ ih =>
    rw [CaptureSet.growByAllocs_append]
    exact SeqReduce.step (SeqStep.step_par_left h) ih

/-- Sequential congruence for the RIGHT branch: the LEFT branch must be a (frozen)
  answer throughout, as `SeqStep.step_par_right` demands.  The right annotation grows. -/
theorem seqreduce_par_right {C : Trace} {m m' : Memory}
  {Cs1 Cs2 : CaptureSet {}} {a e2 e2' : Exp {}}
  (hans : a.IsAns) (hred : SeqReduce C m e2 m' e2') :
  SeqReduce C m (.par Cs1 Cs2 a e2) m' (.par Cs1 (Cs2.growByAllocs C) a e2') := by
  induction hred generalizing Cs2 with
  | refl => exact SeqReduce.refl
  | step h _ ih =>
    rw [CaptureSet.growByAllocs_append]
    exact SeqReduce.step (SeqStep.step_par_right hans h) ih

/-- Helper: Variables cannot step, so reduction is reflexive. -/
theorem reduce_var_inv
  (hred : Reduce C m (.var x) m' v') :
  m' = m ∧ v' = .var x := by
  generalize he : Exp.var x = e at hred
  induction hred with
  | refl => exact ⟨rfl, he ▸ rfl⟩
  | step hstep _ ih =>
    subst he
    cases hstep

/-- Helper: Single step preserves memory subsumption. -/
theorem step_memory_monotonic
  (hstep : SeqStep C m1 e1 m2 e2) :
  m2.subsumes m1 := by
  induction hstep with
  | step_apply | step_invoke | step_tapply | step_capply | step_unwrap
  | step_cond_var_true _ | step_cond_var_false _ | step_read _ _
  | step_rename | step_unpack | step_par_join _ _ =>
    exact Memory.subsumes_refl _
  | step_par_left _ ih => exact ih
  | step_par_right _ _ ih => exact ih
  | step_write hx hy =>
    exact Memory.update_mcell_subsumes _ _ _ _ ⟨_, hx⟩ (fun _ => hy)
  | step_alloc hlk hfresh => exact Memory.extend_mcell_subsumes _ _ _ hfresh hlk
  | step_drop hx => exact Memory.drop_mcell_subsumes _ _ ⟨_, hx⟩
  | step_ctx_letin _ ih | step_ctx_unpack _ ih => exact ih
  | step_lift hv hwf hfresh => exact Memory.extend_subsumes _ _ _ hwf rfl hfresh

/-- Helper: Reduction preserves memory subsumption. -/
theorem reduce_memory_monotonic
  (hred : SeqReduce C m1 e1 m2 e2) :
  m2.subsumes m1 := by
  induction hred with
  | refl => exact Memory.subsumes_refl _
  | step h rest ih =>
    exact Memory.subsumes_trans ih (step_memory_monotonic h)

theorem step_var_absurd
  (hstep : Step C m (.var x) m' e') : False := by
  cases hstep

theorem step_val_absurd
  (hv : Exp.IsSimpleVal v)
  (hstep : Step C m v m' e') :
  False := by
  cases hv <;> cases hstep

theorem step_ans_absurd
  (hans : e.IsAns)
  (hstep : Step C m e m' e') :
  False := by
  cases hans with
  | is_var => exact step_var_absurd hstep
  | is_val hv => cases hv <;> cases hstep

theorem reduce_ans_eq
  (hans : e.IsAns)
  (hred : Reduce C m e m' e') :
  m = m' ∧ e = e' := by
  induction hred with
  | refl => exact ⟨rfl, rfl⟩
  | step h rest ih =>
    have habsurd : False := step_ans_absurd hans h
    contradiction

theorem reduce_letin_inv
  (hred : Reduce t m (.letin e1 e2) m' a)
  (hans : a.IsAns) :
  (∃ t1 t2 m0 y0, Reduce t1 m e1 m0 (.var (.free y0)) ∧
     Reduce t2 m0 (e2.subst (Subst.openVar (.free y0))) m' a) ∨
  (∃ (t1 t2 : Trace) (m0 : Memory) (v0 : Exp {}) (hv : v0.IsSimpleVal)
     (hwf : Exp.WfInHeap v0 m0.heap) (l0 : Nat) (hfresh : m0.heap l0 = none),
    Reduce t1 m e1 m0 v0 ∧
    Reduce
      t2
      (m0.extend l0 ⟨v0, hv, compute_reachability m0.heap v0 hv⟩ hwf rfl hfresh)
      (e2.subst (Subst.openVar (.free l0)))
      m' a) := by
  generalize hgen : Exp.letin e1 e2 = e_full at hred
  induction hred generalizing e1 e2 with
  | refl =>
    rw [←hgen] at hans
    cases hans with
    | is_val hv => cases hv
  | step hstep rest ih =>
    rw [←hgen] at hstep
    cases hstep with
    | step_ctx_letin hstep_e1 =>
      have ih_result := ih hans rfl
      cases ih_result with
      | inl h_var =>
        obtain ⟨t1, t2, m0, y0, hred_e1', hred_body⟩ := h_var
        exact Or.inl ⟨_, _, m0, y0, Reduce.step hstep_e1 hred_e1', hred_body⟩
      | inr h_val =>
        obtain ⟨t1, t2, m0, v0, hv, hwf, l0, hfresh, hred_e1', hred_body⟩ := h_val
        exact Or.inr ⟨_, _, m0, v0, hv, hwf, l0, hfresh, Reduce.step hstep_e1 hred_e1', hred_body⟩
    | step_rename =>
      exact Or.inl ⟨_, _, _, _, Reduce.refl, rest⟩
    | step_lift hv hwf hfresh =>
      exact Or.inr ⟨_, _, _, _, hv, hwf, _, hfresh, Reduce.refl, rest⟩

theorem step_preserves_wf
  (hstep : SeqStep C m1 e1 m2 e2)
  (hwf : e1.WfInHeap m1.heap) :
  e2.WfInHeap m2.heap := by
  cases hstep with
  | step_apply hlookup =>
    rename_i x y cs T e_body hv R
    cases hwf with
    | wf_app hwf_x hwf_y =>
      have hwf_abs : Exp.WfInHeap (.abs cs T e_body) m1.heap :=
        m1.wf.wf_val _ _ hlookup
      have ⟨_, _, hwf_body⟩ := Exp.wf_inv_abs hwf_abs
      have hwf_subst := Subst.wf_openVar hwf_y
      exact Exp.wf_subst hwf_body hwf_subst
  | step_invoke _ _ =>
    exact Exp.WfInHeap.wf_unit
  | step_tapply hlookup =>
    rename_i x S cs S' e_body hv R
    cases hwf with
    | wf_tapp hwf_x hwf_S =>
      have hwf_tabs : Exp.WfInHeap (.tabs cs S' e_body) m1.heap :=
        m1.wf.wf_val _ _ hlookup
      have ⟨_, _, hwf_body⟩ := Exp.wf_inv_tabs hwf_tabs
      have hwf_top : PureTy.WfInHeap (PureTy.top (s:=∅)) m1.heap :=
        Ty.WfInHeap.wf_top
      have hwf_subst := Subst.wf_openTVar hwf_top
      exact Exp.wf_subst hwf_body hwf_subst
  | step_capply hlookup =>
    rename_i x CS cs B e_body hv R
    cases hwf with
    | wf_capp hwf_x hwf_CS =>
      have hwf_cabs : Exp.WfInHeap (.cabs cs B e_body) m1.heap :=
        m1.wf.wf_val _ _ hlookup
      have ⟨_, _, hwf_body⟩ := Exp.wf_inv_cabs hwf_cabs
      have hwf_subst := Subst.wf_openCVar hwf_CS
      exact Exp.wf_subst hwf_body hwf_subst
  | step_unwrap hlookup =>
    rename_i x cs Ψ R hv
    have hwf_boxed : Exp.WfInHeap (.boxed cs Ψ e2) m1.heap := by
      exact Memory.wf_lookup hlookup
    cases hwf_boxed with
    | wf_boxed _ _ hwf_body =>
      exact hwf_body
  | step_cond_var_true hlookup =>
    have ⟨_, hwf_then, _⟩ := Exp.wf_inv_cond hwf
    exact hwf_then
  | step_cond_var_false hlookup =>
    have ⟨_, _, hwf_else⟩ := Exp.wf_inv_cond hwf
    exact hwf_else
  | step_read hreader hcell =>
    obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.mp (Memory.mcell_content_val hcell)
    exact Exp.WfInHeap.wf_var (Var.WfInHeap.wf_free hv)
  | step_write _ _ =>
    exact Exp.WfInHeap.wf_unit
  | step_alloc hlk hfresh =>
    exact Exp.WfInHeap.wf_pack
      (CaptureSet.WfInHeap.wf_var_free (Memory.extend_mcell_lookup hfresh hlk))
      (Var.WfInHeap.wf_free (Memory.extend_mcell_lookup hfresh hlk))
  | step_drop _ =>
    exact Exp.WfInHeap.wf_unit
  | step_ctx_letin hstep_e1 =>
    have ⟨hwf_e1', hwf_e2'⟩ := Exp.wf_inv_letin hwf
    have hwf_e1'' := step_preserves_wf hstep_e1 hwf_e1'
    have hsub := step_memory_monotonic hstep_e1
    have hwf_e2'' := Exp.wf_monotonic hsub hwf_e2'
    exact Exp.WfInHeap.wf_letin hwf_e1'' hwf_e2''
  | step_ctx_unpack hstep_e1 =>
    have ⟨hwf_e1', hwf_e2'⟩ := Exp.wf_inv_unpack hwf
    have hwf_e1'' := step_preserves_wf hstep_e1 hwf_e1'
    have hsub := step_memory_monotonic hstep_e1
    have hwf_e2'' := Exp.wf_monotonic hsub hwf_e2'
    exact Exp.WfInHeap.wf_unpack hwf_e1'' hwf_e2''
  | step_rename =>
    rename_i y e_body
    have ⟨hwf_var, hwf_body⟩ := Exp.wf_inv_letin hwf
    cases hwf_var with
    | wf_var hwf_y =>
      have hwf_subst := Subst.wf_openVar hwf_y
      exact Exp.wf_subst hwf_body hwf_subst
  | step_lift hv hwf_v hfresh =>
    rename_i v e_body l
    have ⟨hwf_v', hwf_body⟩ := Exp.wf_inv_letin hwf
    let m_ext := m1.extend l ⟨v, hv, compute_reachability m1.heap v hv⟩ hwf_v rfl hfresh
    have hwf_l : Var.WfInHeap (.free l : Var .var ∅) m_ext.heap := by
      have hlookup_l :
          m_ext.heap l = some (.val ⟨v, hv, compute_reachability m1.heap v hv⟩) := by
        unfold m_ext
        simpa only [Memory.lookup] using
          (Memory.extend_lookup_eq m1 l
            ⟨v, hv, compute_reachability m1.heap v hv⟩ hwf_v rfl hfresh)
      exact Var.WfInHeap.wf_free hlookup_l
    have hsub := Memory.extend_subsumes m1 l
      ⟨v, hv, compute_reachability m1.heap v hv⟩ hwf_v rfl hfresh
    have hwf_body_ext := Exp.wf_monotonic hsub hwf_body
    have hwf_subst := Subst.wf_openVar hwf_l
    exact Exp.wf_subst hwf_body_ext hwf_subst
  | step_unpack =>
    rename_i cs x e_body
    have ⟨hwf_pack, hwf_body⟩ := Exp.wf_inv_unpack hwf
    cases hwf_pack with
    | wf_pack hwf_cs hwf_x =>
      have hwf_subst := Subst.wf_unpack hwf_cs hwf_x
      exact Exp.wf_subst hwf_body hwf_subst
  -- Congruence preserves WF: stepped branch via the structural recursive call,
  -- untouched branch via monotonicity; WF is structural so par needs no separation.
  | step_par_left hsub_step =>
    cases hwf with
    | wf_par hwf_C1 hwf_C2 hwf_aL hwf_b =>
      exact Exp.WfInHeap.wf_par
        (CaptureSet.growByAllocs_wf
          (CaptureSet.wf_monotonic (step_memory_monotonic hsub_step) hwf_C1)
          (fun l hl => step_allocd_present hsub_step (Trace.mem_allocList.mp hl)))
        (CaptureSet.wf_monotonic (step_memory_monotonic hsub_step) hwf_C2)
        (step_preserves_wf hsub_step hwf_aL)
        (Exp.wf_monotonic (step_memory_monotonic hsub_step) hwf_b)
  | step_par_right _ hsub_step =>
    cases hwf with
    | wf_par hwf_C1 hwf_C2 hwf_aL hwf_b =>
      exact Exp.WfInHeap.wf_par
        (CaptureSet.wf_monotonic (step_memory_monotonic hsub_step) hwf_C1)
        (CaptureSet.growByAllocs_wf
          (CaptureSet.wf_monotonic (step_memory_monotonic hsub_step) hwf_C2)
          (fun l hl => step_allocd_present hsub_step (Trace.mem_allocList.mp hl)))
        (Exp.wf_monotonic (step_memory_monotonic hsub_step) hwf_aL)
        (step_preserves_wf hsub_step hwf_b)
  | step_par_join _ _ =>
    exact Exp.WfInHeap.wf_unit

theorem reduce_preserves_wf
  (hred : SeqReduce C m1 e1 m2 e2)
  (hwf : e1.WfInHeap m1.heap) :
  e2.WfInHeap m2.heap := by
  induction hred with
  | refl => exact hwf
  | step hstep rest ih =>
    have hwf_mid := step_preserves_wf hstep hwf
    exact ih hwf_mid

/-- Inversion lemma for reduction of unpack expressions -/
theorem reduce_unpack_inv
  (hred : Reduce t m (.unpack e1 e2) m' a)
  (hans : a.IsAns) :
  ∃ (t1 t2 : Trace) (m0 : Memory) (cs : CaptureSet {}) (x : Nat),
    Reduce t1 m e1 m0 (.pack cs (.free x)) ∧
    Reduce t2 m0 (e2.subst (Subst.unpack cs (.free x))) m' a := by
  generalize hgen : Exp.unpack e1 e2 = e_full at hred
  induction hred generalizing e1 e2 with
  | refl =>
    rw [←hgen] at hans
    cases hans; rename_i hv
    cases hv
  | step hstep rest ih =>
    rw [←hgen] at hstep
    cases hstep with
    | step_ctx_unpack hstep_e1 =>
      rename_i e1'
      have ih_result := ih (e1 := e1') (e2 := e2) hans rfl
      obtain ⟨t1, t2, m0, cs, x, hred_e1', hred_body⟩ := ih_result
      exact ⟨_, _, m0, cs, x, Reduce.step hstep_e1 hred_e1', hred_body⟩
    | step_unpack =>
      exact ⟨_, _, _, _, _, Reduce.refl, rest⟩

/-- An expression is *progressive* in memory `m` if it is already an answer, or it
  can take at least one sequential `SeqStep` (the step's trace is hidden
  existentially). -/
inductive IsProgressive : Memory -> Exp {} -> Prop where
| done :
  e.IsAns ->
  IsProgressive m e
| step :
  SeqStep t m e m' e' ->
  IsProgressive m e

/-- If an answer has an evaluation, then the postcondition holds for it with the
    empty trace.  An answer `BigStep`s only to itself emitting no events, so the
    bundled preservation half of `Eval` applies to that trivial run. -/
theorem eval_ans_holds_post {k : Nat} {m : Memory} {e : Exp {}} {Q : Tpost}
  (heval : Eval k m e Q)
  (hans : e.IsAns) :
  Q [] e m :=
  heval.2 _ _ _ (BigStep.of_isAns hans)

/-- A variable in the empty signature is always free (no bound variables exist). -/
theorem Var.free_cases {k : Kind} (x : Var k {}) : ∃ n, x = .free n := by
  cases x with
  | bound b => cases b
  | free n => exact ⟨n, rfl⟩

/-- A simple answer is either a simple value or a free variable. -/
theorem Exp.isSimpleAns_cases {e : Exp {}} (h : e.IsSimpleAns) :
    e.IsSimpleVal ∨ ∃ n, e = .var (.free n) := by
  cases h with
  | is_simple_val hv => exact Or.inl hv
  | is_var =>
    rename_i x
    obtain ⟨n, rfl⟩ := Var.free_cases x
    exact Or.inr ⟨n, rfl⟩

/-- A pack answer in the empty signature has a free witness variable. -/
theorem Exp.isPack_cases {e : Exp {}} (h : e.IsPack) :
    ∃ cs n, e = .pack cs (.free n) := by
  cases h with
  | pack =>
    rename_i cs x
    obtain ⟨n, rfl⟩ := Var.free_cases x
    exact ⟨cs, n, rfl⟩

/-- **Progress (sequential small-step).**  A `Safe` configuration with a LIVE read
    budget (`0 < k`) is *progressive*: already an answer, or it can take a sequential
    `SeqStep`.  The budget positivity is essential: `Safe 0` is the trivial
    `exhausted` bottom and claims nothing.  For `letin`/`unpack`, when the head is an
    answer, `h_ans` on the trivial self-run (whose read count `0 < k` is within
    budget) classifies it as a simple value or variable so that
    `step_lift`/`step_rename`/`step_unpack` fire. -/
theorem safe_implies_progressive {k : Nat} {m : Memory} {e : Exp {}}
  (h : Safe k m e) (hk : 0 < k) :
  IsProgressive m e := by
  revert hk
  induction h with
  | exhausted => intro hk; exact absurd hk (Nat.lt_irrefl 0)
  | ans hans => intro _; exact IsProgressive.done hans
  | alloc hlookup =>
    intro _
    obtain ⟨l, hfresh⟩ := Memory.exists_fresh _
    exact IsProgressive.step (SeqStep.step_alloc (l := l) hlookup hfresh)
  | drop hx =>
    intro _
    exact IsProgressive.step (SeqStep.step_drop hx)
  | @apply cs T e_abs hv R y k m x hlookup _ _ =>
    intro _
    obtain ⟨y', rfl⟩ := Var.free_cases y
    exact IsProgressive.step (SeqStep.step_apply hlookup)
  | invoke hlookup_x hlookup_y =>
    intro _
    exact IsProgressive.step (SeqStep.step_invoke hlookup_x hlookup_y)
  | tapply hlookup _ _ =>
    intro _
    exact IsProgressive.step (SeqStep.step_tapply hlookup)
  | capply hlookup _ _ =>
    intro _
    exact IsProgressive.step (SeqStep.step_capply hlookup)
  | unwrap hlookup _ _ =>
    intro _
    exact IsProgressive.step (SeqStep.step_unwrap hlookup)
  | letin _ h_ans _ _ ih_e1 _ _ =>
    intro hk
    cases ih_e1 hk with
    | done hans =>
      obtain ⟨hsimple_ans, hwf⟩ :=
        h_ans _ _ _ (BigStep.of_isAns hans) (by simpa using hk)
      rcases Exp.isSimpleAns_cases hsimple_ans with hv | ⟨n, rfl⟩
      · obtain ⟨l0, hfresh⟩ := Memory.exists_fresh _
        exact IsProgressive.step (SeqStep.step_lift (l := l0) hv hwf hfresh)
      · exact IsProgressive.step SeqStep.step_rename
    | step hstep =>
      exact IsProgressive.step (SeqStep.step_ctx_letin hstep)
  | unpack _ h_ans _ ih_e1 _ =>
    intro hk
    cases ih_e1 hk with
    | done hans =>
      obtain ⟨hpack, hwf⟩ :=
        h_ans _ _ _ (BigStep.of_isAns hans) (by simpa using hk)
      obtain ⟨cs, n, rfl⟩ := Exp.isPack_cases hpack
      exact IsProgressive.step SeqStep.step_unpack
    | step hstep =>
      exact IsProgressive.step (SeqStep.step_ctx_unpack hstep)
  | @cond e2 e3 k m x hres _ _ _ _ =>
    intro hk
    obtain ⟨fx, rfl⟩ := Var.free_cases x
    cases hres with
    | inl hbtrue =>
      cases hcell : m.heap fx with
      | none => simp [resolve, hcell] at hbtrue
      | some cell =>
        cases cell with
        | val hv =>
          cases hv with
          | mk unwrap hsimple reach =>
            have hunwrap : unwrap = .btrue := by simpa [resolve, hcell] using hbtrue
            cases hunwrap
            exact IsProgressive.step
              (SeqStep.step_cond_var_true (hv := hsimple) (R := reach)
                (by simp [Memory.lookup, hcell]))
        | capability => simp [resolve, hcell] at hbtrue
        | masked => simp [resolve, hcell] at hbtrue
    | inr hbfalse =>
      cases hcell : m.heap fx with
      | none => simp [resolve, hcell] at hbfalse
      | some cell =>
        cases cell with
        | val hv =>
          cases hv with
          | mk unwrap hsimple reach =>
            have hunwrap : unwrap = .bfalse := by simpa [resolve, hcell] using hbfalse
            cases hunwrap
            exact IsProgressive.step
              (SeqStep.step_cond_var_false (hv := hsimple) (R := reach)
                (by simp [Memory.lookup, hcell]))
        | capability => simp [resolve, hcell] at hbfalse
        | masked => simp [resolve, hcell] at hbfalse
  | read hlookup_reader hlookup_cell _ =>
    intro _
    exact IsProgressive.step (SeqStep.step_read hlookup_reader hlookup_cell)
  | write hx hy =>
    intro _
    exact IsProgressive.step (SeqStep.step_write hx hy)
  | par _W _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ih1 _ ihh2 _ _ =>
    -- Sequential `par`: advance the left branch to an answer, then the right
    -- (`step_par_right` needs the left answer), then join. Some step always exists.
    -- The right branch's progress after the left answers comes from the sequential
    -- continuation `h2` on the left's trivial self-run (empty trace, budget intact).
    intro hk
    cases ih1 hk with
    | done hAans =>
      have hprog2 := ihh2 (BigStep.of_isAns hAans)
      simp only [Trace.readCount_nil, Nat.sub_zero] at hprog2
      cases hprog2 hk with
      | done hBans => exact IsProgressive.step (SeqStep.step_par_join hAans hBans)
      | step hstepB => exact IsProgressive.step (SeqStep.step_par_right hAans hstepB)
    | step hstepA => exact IsProgressive.step (SeqStep.step_par_left hstepA)

/-- An `Eval` at a live budget is progressive: its bundled `Safe` half gives
    small-step progress. -/
theorem eval_implies_progressive {k : Nat} {m : Memory} {e : Exp {}} {Q : Tpost}
  (heval : Eval k m e Q) (hk : 0 < k) :
  IsProgressive m e :=
  safe_implies_progressive heval.1 hk

/-! ## Small-step ↔ big-step bridge

`Eval := Safe ∧ preservation` is phrased over the relational `BigStep`.  These
lemmas connect it to the small-step `Step`/`Reduce`, so the small-step
preservation/progress results (consumed by `Safety`) go through.  The keystone is
*head expansion*: prepending a `Step` to a `BigStep` run is again a `BigStep` run. -/

/-- An external touch of a prefix `t` is an external touch of `t ++ t'` (same mode):
    the suffix `t'` is processed after `t`, so it cannot un-do `t`'s external touch. -/
theorem Trace.extTouchesFromMode_append_left {t t' : Trace} {l : Nat} {cm : CapMode}
    {A : List Nat} (h : Trace.extTouchesFromMode A l cm t) :
    Trace.extTouchesFromMode A l cm (t ++ t') := by
  induction t generalizing A with
  | nil => simp only [Trace.extTouchesFromMode] at h
  | cons it t ih =>
    cases it with
    | alloc l' => exact ih h
    | access mu l' =>
      rcases h with hd | hr
      · exact Or.inl hd
      · exact Or.inr (ih hr)
    | dealloc l' =>
      rcases h with hd | hr
      · exact Or.inl hd
      · exact Or.inr (ih hr)

/-- `Noninterfere` is downward-closed in its SECOND argument under prefixing:
    if `t1` does not interfere with `t ++ t'`, it does not interfere with `t`
    (a prefix has fewer external touches). -/
theorem Trace.Noninterfere_of_append_right {t1 t t' : Trace}
    (h : Trace.Noninterfere t1 (t ++ t')) : Trace.Noninterfere t1 t := by
  intro l cm1 cm2 h1 h2
  exact h l cm1 cm2 h1 (Trace.extTouchesFromMode_append_left h2)

/-- **Head expansion (sequential).**  A `SeqStep` prefixed to a `BigStep` run is
    itself a `BigStep` run, with the step's trace prepended.  Read-nondeterminism is
    no obstacle: the `step_read` bit is one admissible `bs_read` outcome (`b' = b`).
    `step_par_right` threads because the sequential schedule fixes the left branch as
    an answer before the right runs, matching `bs_par`'s left-then-right order.  (For
    unrestricted interleaving this holds only up to Mazurkiewicz permutation.) -/
theorem BigStep.head_expand {t : Trace} {m1 e1 m2 e2 : _}
    (hstep : SeqStep t m1 e1 m2 e2) :
    ∀ {t' : Trace} {v : Exp {}} {m' : Memory},
      BigStep m2 e2 t' v m' → BigStep m1 e1 (t ++ t') v m' := by
  induction hstep with
  | step_apply hlk => intro t' v m' hbs; exact BigStep.bs_apply hlk hbs
  | step_invoke hlkx hlky =>
    intro t' v m' hbs
    obtain ⟨rfl, rfl, rfl⟩ := BigStep.simpleVal_eq Exp.IsSimpleVal.unit hbs
    exact BigStep.bs_invoke hlkx hlky
  | step_tapply hlk => intro t' v m' hbs; exact BigStep.bs_tapply hlk hbs
  | step_capply hlk => intro t' v m' hbs; exact BigStep.bs_capply hlk hbs
  | step_unwrap hlk => intro t' v m' hbs; exact BigStep.bs_unwrap hlk hbs
  | step_cond_var_true hlk =>
    intro t' v m' hbs
    simp only [Memory.lookup] at hlk
    exact BigStep.bs_cond_true (by simp only [resolve, hlk]) hbs
  | step_cond_var_false hlk =>
    intro t' v m' hbs
    simp only [Memory.lookup] at hlk
    exact BigStep.bs_cond_false (by simp only [resolve, hlk]) hbs
  | step_read hlkx hlky =>
    intro t' v m' hbs
    cases hbs with
    | bs_var => simpa using BigStep.bs_read hlkx hlky (Memory.mcell_content_val hlky)
    | bs_val hv => cases hv
  | step_write hx hy =>
    intro t' v m' hbs
    obtain ⟨rfl, rfl, rfl⟩ := BigStep.simpleVal_eq Exp.IsSimpleVal.unit hbs
    exact BigStep.bs_write hx hy
  | step_alloc hlk hfresh =>
    intro t' v m' hbs
    cases hbs with
    | bs_pack => exact BigStep.bs_alloc hlk hfresh
    | bs_val hv => cases hv
  | step_drop hx =>
    intro t' v m' hbs
    obtain ⟨rfl, rfl, rfl⟩ := BigStep.simpleVal_eq Exp.IsSimpleVal.unit hbs
    exact BigStep.bs_drop hx
  | step_ctx_letin _ ih =>
    intro t' v m' hbs
    cases hbs with
    | bs_letin_val hrun hv hwf hfresh hrun2 =>
      rw [← List.append_assoc]; exact BigStep.bs_letin_val (ih hrun) hv hwf hfresh hrun2
    | bs_letin_var hrun hrun2 =>
      rw [← List.append_assoc]; exact BigStep.bs_letin_var (ih hrun) hrun2
    | bs_val hv => cases hv
  | step_ctx_unpack _ ih =>
    intro t' v m' hbs
    cases hbs with
    | bs_unpack hrun hrun2 =>
      rw [← List.append_assoc]; exact BigStep.bs_unpack (ih hrun) hrun2
    | bs_val hv => cases hv
  | step_par_left _ ih =>
    intro t' v m' hbs
    cases hbs with
    | bs_par hrunL hrunR =>
      rw [← List.append_assoc]; exact BigStep.bs_par (ih hrunL) hrunR
    | bs_val hv => cases hv
  | step_par_join hans_a hans_b =>
    intro t' v m' hbs
    obtain ⟨rfl, rfl, rfl⟩ := BigStep.simpleVal_eq Exp.IsSimpleVal.unit hbs
    exact BigStep.bs_par (BigStep.of_isAns hans_a) (BigStep.of_isAns hans_b)
  | step_par_right hans_a _ ih =>
    intro t' v m' hbs
    cases hbs with
    | bs_par hrunA hrunB =>
      obtain ⟨rfl, rfl, rfl⟩ := BigStep.isAns_inv hrunA hans_a
      simpa using BigStep.bs_par (BigStep.of_isAns hans_a) (ih hrunB)
    | bs_val hv => cases hv
  | step_rename => intro t' v m' hbs; exact BigStep.bs_letin_var BigStep.bs_var hbs
  | step_unpack => intro t' v m' hbs; exact BigStep.bs_unpack BigStep.bs_pack hbs
  | step_lift hv hwf hfresh =>
    intro t' v' m' hbs
    exact BigStep.bs_letin_val (BigStep.bs_val hv) hv hwf hfresh hbs

/-- Sequential small-step ⇒ big-step (to answers).  A `SeqReduce` to an answer `a`
    is realized by a single `BigStep` emitting the same trace: fold head-expansion
    over the reduction (`refl` is the answer's trivial self-run). -/
theorem reduce_to_bigstep {t : Trace} {m e m' a}
    (hred : SeqReduce t m e m' a) (hans : a.IsAns) : BigStep m e t a m' := by
  induction hred with
  | refl => exact BigStep.of_isAns hans
  | step hstep _ ih => exact BigStep.head_expand hstep (ih hans)

/-! ## Progress along sequential reductions

  With the budget-indexed `Safe`, single-step `Safe`-*preservation* is not the right
  device: rebuilding a `Safe.par` carrier after a lone branch step would require
  transporting the rely `W` along a *partial* branch run, which the rely–guarantee
  fields (quantified over full `BigStep` runs) deliberately do not provide — and
  soundly so, since arbitrary-memory transport is exactly the false
  operational-monotonicity shape this development eliminated.  What adequacy needs
  is weaker and honest: every state reachable *within budget* is progressive.  We
  prove that by consulting the `Safe` derivation in place, decomposing the given
  sequential reduction against the derivation (the `seqreduce_*_split` lemmas), and
  paying budget as the decomposition crosses the head/branch boundary. -/

/-- Answers take no `SeqStep`. -/
theorem seqstep_ans_absurd {t : Trace} {m m' : Memory} {e e' : Exp {}}
    (hans : e.IsAns) (hstep : SeqStep t m e m' e') : False := by
  cases hans with
  | is_var => cases hstep
  | is_val hv => cases hv <;> cases hstep

/-- A `SeqReduce` from an answer is trivial: same memory, same expression, no trace. -/
theorem seqreduce_ans_eq {t : Trace} {m m' : Memory} {e e' : Exp {}}
    (hans : e.IsAns) (hred : SeqReduce t m e m' e') :
    m' = m ∧ e' = e ∧ t = [] := by
  cases hred with
  | refl => exact ⟨rfl, rfl, rfl⟩
  | step hstep _ => exact (seqstep_ans_absurd hans hstep).elim

/-- **Mid-run decomposition of a sequential `letin` reduction.**  A `SeqReduce` from
  `.letin e1 e2` either (i) stays inside the head, or crosses into the opened
  continuation after the head reached (ii) a variable (`step_rename`) or (iii) a
  simple value (`step_lift`). -/
theorem seqreduce_letin_split {t : Trace} {m m' : Memory} {e1 : Exp {}}
    {e2 : Exp ({},x)} {X : Exp {}}
    (hred : SeqReduce t m (.letin e1 e2) m' X) :
    (∃ e1', SeqReduce t m e1 m' e1' ∧ X = .letin e1' e2) ∨
    (∃ (t1 t2 : Trace) (m1 : Memory) (y : Var .var {}),
      SeqReduce t1 m e1 m1 (.var y) ∧
      SeqReduce t2 m1 (e2.subst (Subst.openVar y)) m' X ∧ t = t1 ++ t2) ∨
    (∃ (t1 t2 : Trace) (m1 : Memory) (v : Exp {}) (hv : v.IsSimpleVal)
       (hwf : Exp.WfInHeap v m1.heap) (l : Nat) (hfresh : m1.heap l = none),
      SeqReduce t1 m e1 m1 v ∧
      SeqReduce t2
        (m1.extend l ⟨v, hv, compute_reachability m1.heap v hv⟩ hwf rfl hfresh)
        (e2.subst (Subst.openVar (.free l))) m' X ∧ t = t1 ++ t2) := by
  generalize hgen : Exp.letin e1 e2 = efull at hred
  induction hred generalizing e1 with
  | refl => exact Or.inl ⟨e1, SeqReduce.refl, hgen.symm⟩
  | step hstep rest ih =>
    rw [←hgen] at hstep
    cases hstep with
    | step_ctx_letin hstep1 =>
      rcases ih rfl with ⟨e1', hr, hX⟩ | ⟨t1, t2, m1, y, hr1, hr2, ht⟩ |
        ⟨t1, t2, m1, v, hv, hwf, l, hfresh, hr1, hr2, ht⟩
      · exact Or.inl ⟨e1', SeqReduce.step hstep1 hr, hX⟩
      · exact Or.inr (Or.inl ⟨_, t2, m1, y, SeqReduce.step hstep1 hr1, hr2,
          by rw [ht, List.append_assoc]⟩)
      · exact Or.inr (Or.inr ⟨_, t2, m1, v, hv, hwf, l, hfresh,
          SeqReduce.step hstep1 hr1, hr2, by rw [ht, List.append_assoc]⟩)
    | step_rename =>
      exact Or.inr (Or.inl ⟨[], _, _, _, SeqReduce.refl, rest, rfl⟩)
    | step_lift hv hwf hfresh =>
      exact Or.inr (Or.inr ⟨[], _, _, _, hv, hwf, _, hfresh, SeqReduce.refl, rest, rfl⟩)

/-- `unpack` analogue of `seqreduce_letin_split`. -/
theorem seqreduce_unpack_split {t : Trace} {m m' : Memory} {e1 : Exp {}}
    {e2 : Exp ({},C,x)} {X : Exp {}}
    (hred : SeqReduce t m (.unpack e1 e2) m' X) :
    (∃ e1', SeqReduce t m e1 m' e1' ∧ X = .unpack e1' e2) ∨
    (∃ (t1 t2 : Trace) (m1 : Memory) (cs : CaptureSet {}) (y : Var .var {}),
      SeqReduce t1 m e1 m1 (.pack cs y) ∧
      SeqReduce t2 m1 (e2.subst (Subst.unpack cs y)) m' X ∧ t = t1 ++ t2) := by
  generalize hgen : Exp.unpack e1 e2 = efull at hred
  induction hred generalizing e1 with
  | refl => exact Or.inl ⟨e1, SeqReduce.refl, hgen.symm⟩
  | step hstep rest ih =>
    rw [←hgen] at hstep
    cases hstep with
    | step_ctx_unpack hstep1 =>
      rcases ih rfl with ⟨e1', hr, hX⟩ | ⟨t1, t2, m1, cs, y, hr1, hr2, ht⟩
      · exact Or.inl ⟨e1', SeqReduce.step hstep1 hr, hX⟩
      · exact Or.inr ⟨_, t2, m1, cs, y, SeqReduce.step hstep1 hr1, hr2,
          by rw [ht, List.append_assoc]⟩
    | step_unpack =>
      exact Or.inr ⟨[], _, _, _, _, SeqReduce.refl, rest, rfl⟩

/-- **Mid-run decomposition of a sequential `par` reduction.**  Sequential scheduling
  runs the left branch first (`step_par_right` is gated on the left being an
  answer), so a `SeqReduce` from `.par Cs1 Cs2 e1 e2` is (i) still in the left
  phase, (ii) in the right phase after the left reached an answer, or (iii) joined.
  The evolved annotations are existentially hidden — consumers here need only the
  reduct's shape. -/
theorem seqreduce_par_split {t : Trace} {m m' : Memory} {Cs1 Cs2 : CaptureSet {}}
    {e1 e2 X : Exp {}}
    (hred : SeqReduce t m (.par Cs1 Cs2 e1 e2) m' X) :
    (∃ Cs1' e1', SeqReduce t m e1 m' e1' ∧ X = .par Cs1' Cs2 e1' e2) ∨
    (∃ (t1 t2 : Trace) (m1 : Memory) (a1 e2' : Exp {}) (Cs1' Cs2' : CaptureSet {}),
      SeqReduce t1 m e1 m1 a1 ∧ a1.IsAns ∧ SeqReduce t2 m1 e2 m' e2' ∧
      X = .par Cs1' Cs2' a1 e2' ∧ t = t1 ++ t2) ∨
    (∃ (t1 t2 : Trace) (m1 : Memory) (a1 a2 : Exp {}),
      SeqReduce t1 m e1 m1 a1 ∧ a1.IsAns ∧ SeqReduce t2 m1 e2 m' a2 ∧ a2.IsAns ∧
      X = .unit ∧ t = t1 ++ t2) := by
  generalize hgen : Exp.par Cs1 Cs2 e1 e2 = efull at hred
  induction hred generalizing Cs1 Cs2 e1 e2 with
  | refl => exact Or.inl ⟨Cs1, e1, SeqReduce.refl, hgen.symm⟩
  | step hstep rest ih =>
    rw [←hgen] at hstep
    cases hstep with
    | step_par_left hstep1 =>
      rcases ih rfl with ⟨Cs1', e1', hr, hX⟩ |
        ⟨t1, t2, m1, a1, e2', Cs1', Cs2', hr1, hans1, hr2, hX, ht⟩ |
        ⟨t1, t2, m1, a1, a2, hr1, hans1, hr2, hans2, hX, ht⟩
      · exact Or.inl ⟨Cs1', e1', SeqReduce.step hstep1 hr, hX⟩
      · exact Or.inr (Or.inl ⟨_, t2, m1, a1, e2', Cs1', Cs2',
          SeqReduce.step hstep1 hr1, hans1, hr2, hX, by rw [ht, List.append_assoc]⟩)
      · exact Or.inr (Or.inr ⟨_, t2, m1, a1, a2, SeqReduce.step hstep1 hr1, hans1,
          hr2, hans2, hX, by rw [ht, List.append_assoc]⟩)
    | step_par_right hans1 hstep2 =>
      rcases ih rfl with ⟨Cs1', e1', hr, hX⟩ |
        ⟨t1, t2, m1, a1, e2'', Cs1', Cs2', hr1, hans1', hr2, hX, ht⟩ |
        ⟨t1, t2, m1, a1, a2, hr1, hans1', hr2, hans2, hX, ht⟩
      · obtain ⟨rfl, rfl, rfl⟩ := seqreduce_ans_eq hans1 hr
        exact Or.inr (Or.inl ⟨[], _, _, _, _, Cs1', _, SeqReduce.refl, hans1,
          SeqReduce.step hstep2 SeqReduce.refl, hX, by simp⟩)
      · obtain ⟨rfl, rfl, rfl⟩ := seqreduce_ans_eq hans1 hr1
        exact Or.inr (Or.inl ⟨[], _, _, _, _, Cs1', Cs2', SeqReduce.refl, hans1,
          SeqReduce.step hstep2 hr2, hX, by simp [ht]⟩)
      · obtain ⟨rfl, rfl, rfl⟩ := seqreduce_ans_eq hans1 hr1
        exact Or.inr (Or.inr ⟨[], _, _, _, _, SeqReduce.refl, hans1,
          SeqReduce.step hstep2 hr2, hans2, hX, by simp [ht]⟩)
    | step_par_join hans1 hans2 =>
      obtain ⟨rfl, rfl, rfl⟩ := seqreduce_ans_eq (Exp.IsAns.is_val Exp.IsVal.unit) rest
      exact Or.inr (Or.inr ⟨[], [], _, _, _, SeqReduce.refl, hans1, SeqReduce.refl,
        hans2, rfl, rfl⟩)

set_option maxHeartbeats 1000000 in
-- Large case split: the whole `Safe` derivation, with reduction decomposition per case.
/-- **Progress along sequential reductions (within budget).**  Every state reachable
  from a `Safe` configuration by a sequential reduction performing fewer reads than
  the budget is progressive.  The derivation is consulted in place: the reduction is
  decomposed against it, and the continuation obligations (`h_val`/`h_var`/`h2`) —
  available at the residual budget — carry the recursion.  No `Safe` reconstruction
  at intermediate states is needed. -/
theorem safe_reduce_progressive {k : Nat} {m : Memory} {e : Exp {}}
    (h : Safe k m e) :
    ∀ {t : Trace} {m' : Memory} {e' : Exp {}},
      SeqReduce t m e m' e' -> t.readCount < k -> IsProgressive m' e' := by
  induction h with
  | exhausted =>
    intro t m' e' _ hbud
    exact absurd hbud (Nat.not_lt_zero _)
  | ans hans =>
    intro t m' e' hred _
    obtain ⟨rfl, rfl, rfl⟩ := seqreduce_ans_eq hans hred
    exact IsProgressive.done hans
  | alloc hlk =>
    intro t m' e' hred _
    cases hred with
    | refl =>
      obtain ⟨l, hfresh⟩ := Memory.exists_fresh _
      exact IsProgressive.step (SeqStep.step_alloc (l := l) hlk hfresh)
    | step hstep rest =>
      cases hstep with
      | step_alloc hlk2 hfresh2 =>
        obtain ⟨rfl, rfl, rfl⟩ := seqreduce_ans_eq (Exp.IsAns.is_val Exp.IsVal.pack) rest
        exact IsProgressive.done (Exp.IsAns.is_val Exp.IsVal.pack)
  | @apply cs T e_abs hv R y k m x hlk _ ih =>
    intro t m' e' hred hbud
    cases hred with
    | refl =>
      obtain ⟨y', rfl⟩ := Var.free_cases y
      exact IsProgressive.step (SeqStep.step_apply hlk)
    | step hstep rest =>
      cases hstep with
      | step_apply hlk2 =>
        have heq := congrArg HeapVal.unwrap (Memory.lookup_val_eq hlk hlk2)
        simp only at heq
        cases heq
        exact ih rest (by simpa using hbud)
      | step_invoke hlkx _ =>
        rw [hlk] at hlkx
        exact absurd hlkx (by simp)
  | invoke hlkx hlky =>
    intro t m' e' hred _
    cases hred with
    | refl => exact IsProgressive.step (SeqStep.step_invoke hlkx hlky)
    | step hstep rest =>
      cases hstep with
      | step_apply hlk2 => rw [hlkx] at hlk2; exact absurd hlk2 (by simp)
      | step_invoke _ _ =>
        obtain ⟨rfl, rfl, rfl⟩ := seqreduce_ans_eq (Exp.IsAns.is_val Exp.IsVal.unit) rest
        exact IsProgressive.done (Exp.IsAns.is_val Exp.IsVal.unit)
  | tapply hlk _ ih =>
    intro t m' e' hred hbud
    cases hred with
    | refl => exact IsProgressive.step (SeqStep.step_tapply hlk)
    | step hstep rest =>
      cases hstep with
      | step_tapply hlk2 =>
        have heq := congrArg HeapVal.unwrap (Memory.lookup_val_eq hlk hlk2)
        simp only at heq
        cases heq
        exact ih rest (by simpa using hbud)
  | capply hlk _ ih =>
    intro t m' e' hred hbud
    cases hred with
    | refl => exact IsProgressive.step (SeqStep.step_capply hlk)
    | step hstep rest =>
      cases hstep with
      | step_capply hlk2 =>
        have heq := congrArg HeapVal.unwrap (Memory.lookup_val_eq hlk hlk2)
        simp only at heq
        cases heq
        exact ih rest (by simpa using hbud)
  | unwrap hlk _ ih =>
    intro t m' e' hred hbud
    cases hred with
    | refl => exact IsProgressive.step (SeqStep.step_unwrap hlk)
    | step hstep rest =>
      cases hstep with
      | step_unwrap hlk2 =>
        have heq := congrArg HeapVal.unwrap (Memory.lookup_val_eq hlk hlk2)
        simp only at heq
        cases heq
        exact ih rest (by simpa using hbud)
  | letin hse1 h_ans h_val h_var ih1 ihval ihvar =>
    intro t m' e' hred hbud
    rcases seqreduce_letin_split hred with ⟨e1', hr, rfl⟩ |
      ⟨t1, t2, m1, y, hr1, hr2, rfl⟩ |
      ⟨t1, t2, m1, v, hv, hwf, l, hfresh, hr1, hr2, rfl⟩
    · cases ih1 hr hbud with
      | step hstep => exact IsProgressive.step (SeqStep.step_ctx_letin hstep)
      | done hans1 =>
        obtain ⟨hsa, hwfv⟩ := h_ans _ _ _ (reduce_to_bigstep hr hans1) hbud
        rcases Exp.isSimpleAns_cases hsa with hv | ⟨n, rfl⟩
        · obtain ⟨l0, hfresh⟩ := Memory.exists_fresh _
          exact IsProgressive.step (SeqStep.step_lift (l := l0) hv hwfv hfresh)
        · exact IsProgressive.step SeqStep.step_rename
    · have hbs1 := reduce_to_bigstep hr1 Exp.IsAns.is_var
      rw [Trace.readCount_append] at hbud
      exact ihvar hbs1 hr2 (by omega)
    · have hbs1 := reduce_to_bigstep hr1 (Exp.IsAns.is_val (Exp.isVal_of_isSimpleVal hv))
      rw [Trace.readCount_append] at hbud
      exact ihval hbs1 hv hwf l hfresh hr2 (by omega)
  | unpack hse1 h_ans h_val ih1 ihval =>
    intro t m' e' hred hbud
    rcases seqreduce_unpack_split hred with ⟨e1', hr, rfl⟩ |
      ⟨t1, t2, m1, cs, y, hr1, hr2, rfl⟩
    · cases ih1 hr hbud with
      | step hstep => exact IsProgressive.step (SeqStep.step_ctx_unpack hstep)
      | done hans1 =>
        obtain ⟨hpk, hwfv⟩ := h_ans _ _ _ (reduce_to_bigstep hr hans1) hbud
        obtain ⟨cs', n, rfl⟩ := Exp.isPack_cases hpk
        exact IsProgressive.step SeqStep.step_unpack
    · have hbs1 := reduce_to_bigstep hr1 (Exp.IsAns.is_val Exp.IsVal.pack)
      rw [Trace.readCount_append] at hbud
      exact ihval hbs1 hr2 (by omega)
  | read hlkx hlky hcontent =>
    intro t m' e' hred _
    cases hred with
    | refl => exact IsProgressive.step (SeqStep.step_read hlkx hlky)
    | step hstep rest =>
      cases hstep with
      | step_read _ _ =>
        obtain ⟨rfl, rfl, rfl⟩ := seqreduce_ans_eq Exp.IsAns.is_var rest
        exact IsProgressive.done Exp.IsAns.is_var
  | write hx hy =>
    intro t m' e' hred _
    cases hred with
    | refl => exact IsProgressive.step (SeqStep.step_write hx hy)
    | step hstep rest =>
      cases hstep with
      | step_write _ _ =>
        obtain ⟨rfl, rfl, rfl⟩ := seqreduce_ans_eq (Exp.IsAns.is_val Exp.IsVal.unit) rest
        exact IsProgressive.done (Exp.IsAns.is_val Exp.IsVal.unit)
  | drop hx =>
    intro t m' e' hred _
    cases hred with
    | refl => exact IsProgressive.step (SeqStep.step_drop hx)
    | step hstep rest =>
      cases hstep with
      | step_drop _ =>
        obtain ⟨rfl, rfl, rfl⟩ := seqreduce_ans_eq (Exp.IsAns.is_val Exp.IsVal.unit) rest
        exact IsProgressive.done (Exp.IsAns.is_val Exp.IsVal.unit)
  | cond hres h_true h_false ihtrue ihfalse =>
    intro t m' e' hred hbud
    cases hred with
    | refl =>
      exact safe_implies_progressive (Safe.cond hres h_true h_false) (by simpa using hbud)
    | step hstep rest =>
      cases hstep with
      | step_cond_var_true hlk =>
        simp only [Memory.lookup] at hlk
        exact ihtrue (by simp only [resolve, hlk]) rest (by simpa using hbud)
      | step_cond_var_false hlk =>
        simp only [Memory.lookup] at hlk
        exact ihfalse (by simp only [resolve, hlk]) rest (by simpa using hbud)
  | par _W _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ih1 _ ihh2 _ _ =>
    intro t m' e' hred hbud
    rcases seqreduce_par_split hred with ⟨Cs1', e1', hr, rfl⟩ |
      ⟨t1, t2, m1, a1, e2', Cs1', Cs2', hr1, hans1, hr2, rfl, rfl⟩ |
      ⟨t1, t2, m1, a1, a2, hr1, hans1, hr2, hans2, rfl, rfl⟩
    · cases ih1 hr hbud with
      | step hstepA => exact IsProgressive.step (SeqStep.step_par_left hstepA)
      | done hansA =>
        have hp2 := ihh2 (reduce_to_bigstep hr hansA) SeqReduce.refl
          (by simpa using Nat.sub_pos_of_lt hbud)
        cases hp2 with
        | done hansB => exact IsProgressive.step (SeqStep.step_par_join hansA hansB)
        | step hstepB => exact IsProgressive.step (SeqStep.step_par_right hansA hstepB)
    · rw [Trace.readCount_append] at hbud
      cases ihh2 (reduce_to_bigstep hr1 hans1) hr2 (by omega) with
      | done hansB => exact IsProgressive.step (SeqStep.step_par_join hans1 hansB)
      | step hstepB => exact IsProgressive.step (SeqStep.step_par_right hans1 hstepB)
    · exact IsProgressive.done (Exp.IsAns.is_val Exp.IsVal.unit)

/-- `SeqReduce`-level head expansion: fold `BigStep.head_expand` over a reduction. -/
theorem BigStep.reduce_expand {t : Trace} {m1 e1 m2 e2}
    (hred : SeqReduce t m1 e1 m2 e2) :
    ∀ {t' : Trace} {v : Exp {}} {m' : Memory},
      BigStep m2 e2 t' v m' → BigStep m1 e1 (t ++ t') v m' := by
  induction hred with
  | refl => intro t' v m' hbs; exact hbs
  | step hstep _ ih =>
    intro t' v m' hbs
    rw [List.append_assoc]
    exact BigStep.head_expand hstep (ih hbs)

/-- **Adequacy.**  If `Eval k m e Q` and `e` reduces (sequential small-step) to an
    answer `a` emitting trace `t`, then `Q t a m'`: the reduction is realized as a
    `BigStep` (`reduce_to_bigstep`), to which the preservation half of `Eval`
    applies.  Note NO budget hypothesis: the postcondition half of `Eval`
    quantifies over all runs. -/
theorem eval_to_reduce {k : Nat} {t : Trace} {m e m' a} {Q : Tpost}
    (heval : Eval k m e Q) (hans : a.IsAns) (hred : SeqReduce t m e m' a) : Q t a m' :=
  heval.2 t a m' (reduce_to_bigstep hred hans)

/-- Helper for `Safe.has_reduction`: a single step to an answer satisfies the
  budget disjunction at ANY budget (case on how the step's reads compare). -/
theorem Safe.has_reduction_of_step_ans {k : Nat} {m m2 : Memory} {e a : Exp {}}
    {ts : Trace} (hstep : SeqStep ts m e m2 a) (hans : a.IsAns) :
    ∃ t m' a', SeqReduce t m e m' a' ∧
      ((a'.IsAns ∧ t.readCount < k) ∨ k ≤ t.readCount) := by
  rcases Nat.lt_or_ge (Trace.readCount (ts ++ [])) k with hlt | hge
  · exact ⟨_, _, _, SeqReduce.step hstep SeqReduce.refl, Or.inl ⟨hans, hlt⟩⟩
  · exact ⟨_, _, _, SeqReduce.step hstep SeqReduce.refl, Or.inr hge⟩

/-- Helper for `Safe.has_reduction`: an answer satisfies the budget disjunction
  at ANY budget via its trivial reduction. -/
theorem Safe.has_reduction_of_ans {k : Nat} {m : Memory} {e : Exp {}}
    (hans : e.IsAns) :
    ∃ t m' a', SeqReduce t m e m' a' ∧
      ((a'.IsAns ∧ t.readCount < k) ∨ k ≤ t.readCount) := by
  rcases Nat.lt_or_ge (Trace.readCount []) k with hlt | hge
  · exact ⟨[], _, _, SeqReduce.refl, Or.inl ⟨hans, hlt⟩⟩
  · exact ⟨[], _, _, SeqReduce.refl, Or.inr hge⟩

/-- **Within-budget termination (sequential small-step).**  A `Safe` configuration
  sequentially reduces either to an answer within the read budget, or to a state
  whose reduction has already consumed the whole budget.  This is the honest,
  budget-indexed replacement for the removed total `Safe.has_answer`: a fixed-budget
  derivation cannot promise an answer (`exhausted` carries no run), but it can
  promise the budget is spent before anything gets stuck.  Instantiating the budget
  above a terminating program's read count recovers answer reachability. -/
theorem Safe.has_reduction {k : Nat} {m : Memory} {e : Exp {}} (h : Safe k m e) :
    ∃ t m' a, SeqReduce t m e m' a ∧
      ((a.IsAns ∧ t.readCount < k) ∨ k ≤ t.readCount) := by
  induction h with
  | exhausted => exact ⟨[], _, _, SeqReduce.refl, Or.inr (Nat.zero_le _)⟩
  | ans hans => exact Safe.has_reduction_of_ans hans
  | alloc hlk =>
    obtain ⟨l, hfresh⟩ := Memory.exists_fresh _
    exact Safe.has_reduction_of_step_ans (SeqStep.step_alloc (l := l) hlk hfresh)
      (Exp.IsAns.is_val Exp.IsVal.pack)
  | @apply cs T e_abs hv R y k m x hlk _ ih =>
    obtain ⟨y', rfl⟩ := Var.free_cases y
    obtain ⟨t, m', a, hred, hdisj⟩ := ih
    exact ⟨_, _, _, SeqReduce.step (SeqStep.step_apply hlk) hred, by simpa using hdisj⟩
  | invoke hlkx hlky =>
    exact Safe.has_reduction_of_step_ans (SeqStep.step_invoke hlkx hlky)
      (Exp.IsAns.is_val Exp.IsVal.unit)
  | tapply hlk _ ih =>
    obtain ⟨t, m', a, hred, hdisj⟩ := ih
    exact ⟨_, _, _, SeqReduce.step (SeqStep.step_tapply hlk) hred, by simpa using hdisj⟩
  | capply hlk _ ih =>
    obtain ⟨t, m', a, hred, hdisj⟩ := ih
    exact ⟨_, _, _, SeqReduce.step (SeqStep.step_capply hlk) hred, by simpa using hdisj⟩
  | unwrap hlk _ ih =>
    obtain ⟨t, m', a, hred, hdisj⟩ := ih
    exact ⟨_, _, _, SeqReduce.step (SeqStep.step_unwrap hlk) hred, by simpa using hdisj⟩
  | letin _ h_ans _ _ ih1 ihval ihvar =>
    obtain ⟨t1, m1, a1, hred1, hdisj1⟩ := ih1
    rcases hdisj1 with ⟨hans1, hbud1⟩ | hover1
    · have hbs1 := reduce_to_bigstep hred1 hans1
      obtain ⟨hsa, hwf⟩ := h_ans _ _ _ hbs1 hbud1
      rcases Exp.isSimpleAns_cases hsa with hv | ⟨n, rfl⟩
      · obtain ⟨l, hfresh⟩ := Memory.exists_fresh m1
        obtain ⟨t2, m2, a2, hred2, hdisj2⟩ := ihval hbs1 hv hwf l hfresh
        refine ⟨_, _, _, seqreduce_trans (seqreduce_ctx_letin hred1)
          (SeqReduce.step (SeqStep.step_lift hv hwf hfresh) hred2), ?_⟩
        rcases hdisj2 with ⟨hans2, hbud2⟩ | hover2
        · exact Or.inl ⟨hans2,
            by simp only [Trace.readCount_append, Trace.readCount_nil]; omega⟩
        · exact Or.inr
            (by simp only [Trace.readCount_append, Trace.readCount_nil]; omega)
      · obtain ⟨t2, m2, a2, hred2, hdisj2⟩ := ihvar hbs1
        refine ⟨_, _, _, seqreduce_trans (seqreduce_ctx_letin hred1)
          (SeqReduce.step SeqStep.step_rename hred2), ?_⟩
        rcases hdisj2 with ⟨hans2, hbud2⟩ | hover2
        · exact Or.inl ⟨hans2,
            by simp only [Trace.readCount_append, Trace.readCount_nil]; omega⟩
        · exact Or.inr
            (by simp only [Trace.readCount_append, Trace.readCount_nil]; omega)
    · exact ⟨t1, _, _, seqreduce_ctx_letin hred1, Or.inr hover1⟩
  | unpack _ h_ans _ ih1 ihval =>
    obtain ⟨t1, m1, a1, hred1, hdisj1⟩ := ih1
    rcases hdisj1 with ⟨hans1, hbud1⟩ | hover1
    · have hbs1 := reduce_to_bigstep hred1 hans1
      obtain ⟨hpk, hwf⟩ := h_ans _ _ _ hbs1 hbud1
      obtain ⟨cs, n, rfl⟩ := Exp.isPack_cases hpk
      obtain ⟨t2, m2, a2, hred2, hdisj2⟩ := ihval hbs1
      refine ⟨_, _, _, seqreduce_trans (seqreduce_ctx_unpack hred1)
        (SeqReduce.step SeqStep.step_unpack hred2), ?_⟩
      rcases hdisj2 with ⟨hans2, hbud2⟩ | hover2
      · exact Or.inl ⟨hans2,
          by simp only [Trace.readCount_append, Trace.readCount_nil]; omega⟩
      · exact Or.inr
          (by simp only [Trace.readCount_append, Trace.readCount_nil]; omega)
    · exact ⟨t1, _, _, seqreduce_ctx_unpack hred1, Or.inr hover1⟩
  | read hlkx hlky _ =>
    exact Safe.has_reduction_of_step_ans (SeqStep.step_read hlkx hlky) Exp.IsAns.is_var
  | write hx hy =>
    exact Safe.has_reduction_of_step_ans (SeqStep.step_write hx hy)
      (Exp.IsAns.is_val Exp.IsVal.unit)
  | drop hx =>
    exact Safe.has_reduction_of_step_ans (SeqStep.step_drop hx)
      (Exp.IsAns.is_val Exp.IsVal.unit)
  | @cond e2 e3 k m x hres _ _ ih_true ih_false =>
    obtain ⟨fx, rfl⟩ := Var.free_cases x
    cases hres with
    | inl hbtrue =>
      cases hcell : m.heap fx with
      | none => simp [resolve, hcell] at hbtrue
      | some cell =>
        cases cell with
        | val hv =>
          cases hv with
          | mk unwrap hsimple reach =>
            have hunwrap : unwrap = .btrue := by simpa [resolve, hcell] using hbtrue
            cases hunwrap
            obtain ⟨t, m', a, hred, hdisj⟩ := ih_true hbtrue
            exact ⟨_, _, _, SeqReduce.step
              (SeqStep.step_cond_var_true (hv := hsimple) (R := reach)
                (by simp [Memory.lookup, hcell])) hred, by simpa using hdisj⟩
        | capability => simp [resolve, hcell] at hbtrue
        | masked => simp [resolve, hcell] at hbtrue
    | inr hbfalse =>
      cases hcell : m.heap fx with
      | none => simp [resolve, hcell] at hbfalse
      | some cell =>
        cases cell with
        | val hv =>
          cases hv with
          | mk unwrap hsimple reach =>
            have hunwrap : unwrap = .bfalse := by simpa [resolve, hcell] using hbfalse
            cases hunwrap
            obtain ⟨t, m', a, hred, hdisj⟩ := ih_false hbfalse
            exact ⟨_, _, _, SeqReduce.step
              (SeqStep.step_cond_var_false (hv := hsimple) (R := reach)
                (by simp [Memory.lookup, hcell])) hred, by simpa using hdisj⟩
        | capability => simp [resolve, hcell] at hbfalse
        | masked => simp [resolve, hcell] at hbfalse
  | par _W _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ih1 _ ihh2 _ _ =>
    obtain ⟨t1, m1, a1, hred1, hdisj1⟩ := ih1
    rcases hdisj1 with ⟨hans1, hbud1⟩ | hover1
    · obtain ⟨t2, m2, a2, hred2, hdisj2⟩ := ihh2 (reduce_to_bigstep hred1 hans1)
      rcases hdisj2 with ⟨hans2, hbud2⟩ | hover2
      · refine ⟨_, _, _, seqreduce_trans (seqreduce_par_left hred1)
          (seqreduce_trans (seqreduce_par_right hans1 hred2)
            (SeqReduce.step (SeqStep.step_par_join hans1 hans2) SeqReduce.refl)), ?_⟩
        exact Or.inl ⟨Exp.IsAns.is_val Exp.IsVal.unit,
          by simp only [Trace.readCount_append, Trace.readCount_nil]; omega⟩
      · refine ⟨_, _, _, seqreduce_trans (seqreduce_par_left hred1)
          (seqreduce_par_right hans1 hred2), ?_⟩
        exact Or.inr (by simp only [Trace.readCount_append]; omega)
    · exact ⟨t1, _, _, seqreduce_par_left hred1, Or.inr hover1⟩

/-- Answer existence within budget (sequential small-step): `Eval k m e Q` reduces
    to an answer satisfying `Q` within the budget, or exhausts the budget. -/
theorem eval_reduce_exists_answer {k : Nat} {m : Memory} {e : Exp {}} {Q : Tpost}
    (heval : Eval k m e Q) :
    ∃ t m' a, SeqReduce t m e m' a ∧
      ((a.IsAns ∧ t.readCount < k ∧ Q t a m') ∨ k ≤ t.readCount) := by
  obtain ⟨t, m', a, hred, hdisj⟩ := heval.1.has_reduction
  rcases hdisj with ⟨hans, hbud⟩ | hover
  · exact ⟨t, m', a, hred,
      Or.inl ⟨hans, hbud, heval.2 t a m' (reduce_to_bigstep hred hans)⟩⟩
  · exact ⟨t, m', a, hred, Or.inr hover⟩

theorem not_mutated_refl {m : Memory} : m.not_mutated m := fun _ _ _ hinit => hinit

theorem not_mutated_trans {m1 m2 m3 : Memory}
    (h12 : m1.not_mutated m2) (h23 : m2.not_mutated m3) :
    m1.not_mutated m3 := fun l b ℓ hinit => h23 l b ℓ (h12 l b ℓ hinit)

/-- A single step whose trace contains no write (`access .epsilon`) and no
    deallocation event does not mutate any mutable cell. -/
theorem step_immutable
  (hwr : ∀ l, TraceItem.access .epsilon l ∉ t)
  (hdr : ∀ l, TraceItem.dealloc l ∉ t)
  (hstep : SeqStep t m1 e1 m2 e2) :
  m1.not_mutated m2 := by
  intro l b ℓ hinit
  induction hstep with
  | step_apply | step_invoke | step_tapply | step_capply | step_unwrap
  | step_cond_var_true _ | step_cond_var_false _ | step_read _ _
  | step_rename | step_unpack | step_par_join _ _ =>
    exact hinit
  | step_par_left _ ih => exact ih hwr hdr hinit
  | step_par_right _ _ ih => exact ih hwr hdr hinit
  | step_write _ _ =>
    exact absurd (List.mem_singleton.mpr rfl) (hwr _)
  | step_drop _ =>
    exact absurd (List.mem_singleton.mpr rfl) (hdr _)
  | step_alloc _ hfresh =>
    -- The fresh mcell is at a fresh location, distinct from the queried (allocated) cell.
    simp only [Memory.extend_mcell, Heap.extend_mcell]
    split
    · rename_i heq; rw [heq, hfresh] at hinit; cases hinit
    · exact hinit
  | step_lift hv hwf hfresh =>
    simp only [Memory.extend, Heap.extend]
    split
    · rename_i heq; rw [heq, hfresh] at hinit; cases hinit
    · exact hinit
  | step_ctx_letin _ ih | step_ctx_unpack _ ih => exact ih hwr hdr hinit

/-- A whole reduction whose (accumulated) trace contains no write or deallocation
    event does not mutate memory. -/
theorem reduce_immutable
    (hwr : ∀ l, TraceItem.access .epsilon l ∉ t)
    (hdr : ∀ l, TraceItem.dealloc l ∉ t)
    (hred : SeqReduce t m1 e1 m2 e2) :
    m1.not_mutated m2 := by
  induction hred with
  | refl => exact not_mutated_refl
  | step hstep rest ih =>
    exact not_mutated_trans
      (step_immutable (fun l hm => hwr l (List.mem_append_left _ hm))
        (fun l hm => hdr l (List.mem_append_left _ hm)) hstep)
      (ih (fun l hm => hwr l (List.mem_append_right _ hm))
        (fun l hm => hdr l (List.mem_append_right _ hm)))

/-- **Per-location immutability (single step).**  A step that neither writes
    (`access .epsilon l`) nor drops (`dealloc l`) the specific cell `l` leaves
    that cell unchanged — same bit and liveness.  Fresh allocations land at fresh
    locations (distinct from the queried, already-allocated `l`); writes/drops at
    other locations miss `l`; a write/drop at `l` itself is excluded by the
    hypotheses.  This is the per-cell refinement of `step_immutable`, needed when
    the trace *may* legitimately touch freshly allocated cells. -/
theorem step_preserves_cell {t : Trace} {m1 e1 m2 e2 : _} {l : Nat} {b : Nat} {ℓ : Liveness}
    (hstep : SeqStep t m1 e1 m2 e2) :
    TraceItem.access .epsilon l ∉ t -> TraceItem.dealloc l ∉ t ->
    m1.heap l = some (.capability (.mcell b ℓ)) ->
    m2.heap l = some (.capability (.mcell b ℓ)) := by
  induction hstep with
  | step_apply _ | step_invoke _ _ | step_tapply _ | step_capply _ | step_unwrap _
  | step_cond_var_true _ | step_cond_var_false _ | step_read _ _
  | step_rename | step_unpack | step_par_join _ _ =>
    intro _ _ hinit; exact hinit
  | step_par_left _ ih => intro hwr hdr hinit; exact ih hwr hdr hinit
  | step_par_right _ _ ih => intro hwr hdr hinit; exact ih hwr hdr hinit
  | step_write _ _ =>
    intro hwr _ hinit
    simp only [Memory.update_mcell, Heap.update_cell]
    split
    · rename_i heq; subst heq; exact absurd (List.mem_singleton.mpr rfl) hwr
    · exact hinit
  | step_drop _ =>
    intro _ hdr hinit
    simp only [Memory.drop_mcell, Heap.update_cell]
    split
    · rename_i heq; subst heq; exact absurd (List.mem_singleton.mpr rfl) hdr
    · exact hinit
  | step_alloc _ hfresh =>
    intro _ _ hinit
    simp only [Memory.extend_mcell, Heap.extend_mcell]
    split
    · rename_i heq; rw [heq, hfresh] at hinit; cases hinit
    · exact hinit
  | step_lift hv hwf hfresh =>
    intro _ _ hinit
    simp only [Memory.extend, Heap.extend]
    split
    · rename_i heq; rw [heq, hfresh] at hinit; cases hinit
    · exact hinit
  | step_ctx_letin _ ih | step_ctx_unpack _ ih =>
    intro hwr hdr hinit; exact ih hwr hdr hinit

/-- **Per-location immutability (reduction).**  A whole reduction that never
    writes or drops the specific cell `l` leaves it unchanged. -/
theorem reduce_preserves_cell {t : Trace} {m1 e1 m2 e2 : _} {l : Nat} {b : Nat} {ℓ : Liveness}
    (hred : SeqReduce t m1 e1 m2 e2) :
    TraceItem.access .epsilon l ∉ t -> TraceItem.dealloc l ∉ t ->
    m1.heap l = some (.capability (.mcell b ℓ)) ->
    m2.heap l = some (.capability (.mcell b ℓ)) := by
  induction hred with
  | refl => intro _ _ hinit; exact hinit
  | step hstep _ ih =>
    intro hwr hdr hinit
    refine ih (fun hm => hwr (List.mem_append_right _ hm))
      (fun hm => hdr (List.mem_append_right _ hm)) ?_
    exact step_preserves_cell hstep (fun hm => hwr (List.mem_append_left _ hm))
      (fun hm => hdr (List.mem_append_left _ hm)) hinit

end CoreCapybara
