import Semantic.CoreCapybara.Fundamental
import Semantic.CoreCapybara.Semantics.Props
import Semantic.CoreCapybara.Semantics.Standardization
namespace CoreCapybara

/-! The following defines _platforms_. -/

/-- Context signature of a platform of `n` mutable boolean cells. -/
def Sig.platform_of : Nat -> Sig
| 0 => {}
| n+1 => ((Sig.platform_of n),C),x

/-- A platform context with `n` mutable boolean cells.  The capture variables are
  `.access_only` (the platform grants read/write access to its cells, matching the
  `.access_only` default of `TypeEnv.extend_cvar`). -/
def Ctx.platform_of : (n : Nat) -> Ctx (Sig.platform_of n)
| 0 => .empty
| n+1 => ((Ctx.platform_of n),C[.access_only]<:.unbound),x:(.cell (.cvar (.M .epsilon) .here))

/-- A platform heap with `n` mutable boolean cells (initialized to false, live). -/
def Heap.platform_of (N : Nat) : Heap :=
  fun i =>
    if i < N then
      .some (.capability (.mcell false .live))
    else
      .none

/-- Type environment for a platform with `N` mutable cells.
  Maps each pair `(C, x)` to cell `i` at heap location `i`:
  capture variable `C` maps to singleton ground capture set `{i}`,
  term variable `x` maps to heap location `i`. -/
def TypeEnv.platform_of : (N : Nat) -> TypeEnv (Sig.platform_of N)
| 0 => .empty
| N+1 =>
  let cs : CaptureSet {} := .var (.M .epsilon) (.free N)
  let cap := CapabilitySet.singleton .epsilon N
  let env := (TypeEnv.platform_of N).extend_cvar cs (cap := cap)
  env.extend_var N ⟨.cvar (.M .epsilon) .here, .cvar⟩

/-- The platform heap is well-formed: it contains only mutable cells, no values. -/
theorem Heap.platform_of_wf (N : Nat) : (Heap.platform_of N).WfHeap := by
  constructor
  · intro l hv hlookup
    unfold Heap.platform_of at hlookup
    split at hlookup <;> cases hlookup
  · intro l v hv R hlookup
    unfold Heap.platform_of at hlookup
    split at hlookup <;> cases hlookup
  · intro l v hv R hlookup
    unfold Heap.platform_of at hlookup
    split at hlookup <;> cases hlookup

/-- The platform heap has finite domain {0, 1, ..., N-1}. -/
theorem Heap.platform_of_has_fin_dom (N : Nat) :
  (Heap.platform_of N).HasFinDom (Finset.range N) := by
  intro l
  unfold Heap.platform_of
  constructor
  · intro h
    split at h
    case isTrue hlt =>
      simp [Finset.mem_range, hlt]
    case isFalse =>
      contradiction
  · intro h
    simp [Finset.mem_range] at h
    split
    case isTrue => simp
    case isFalse hf => omega

/-- Platform memory with `N` mutable boolean cells. -/
def Memory.platform_of (N : Nat) : Memory where
  heap := Heap.platform_of N
  wf := Heap.platform_of_wf N
  findom := ⟨Finset.range N, Heap.platform_of_has_fin_dom N⟩

/-- Platform memory M subsumes platform memory N when M ≥ N. -/
theorem platform_memory_subsumes {N M : Nat} (hNM : N ≤ M) :
  (Memory.platform_of M).subsumes (Memory.platform_of N) := by
  intro l v hlookup
  unfold Memory.platform_of Heap.platform_of at hlookup ⊢
  simp only [Option.ite_none_right_eq_some, Option.some.injEq] at hlookup
  obtain ⟨hl, hv⟩ := hlookup
  exists .capability (.mcell false .live)
  simp only [ite_eq_left_iff, not_lt, reduceCtorEq, imp_false, not_le]
  constructor
  · omega
  · rw [← hv]; simp only [Cell.subsumes]; exact Liveness.Le.refl

/-- EnvTyping for platform is monotonic: platform N types in platform M memory when M ≥ N. -/
theorem env_typing_platform_monotonic {Γ : Ctx s} {env : TypeEnv s} {N M : Nat}
  (hNM : N ≤ M)
  (ht : EnvTyping Γ env (Memory.platform_of N)) :
  EnvTyping Γ env (Memory.platform_of M) := by
  exact env_typing_monotonic ht (platform_memory_subsumes hNM)

/-- The platform memory is compatible with any capability set: every location it
  holds is a live mcell, so the liveness obligation of `is_compatible` is met, and
  locations outside its domain are `none` (vacuously fine). -/
theorem platform_is_compatible {N : Nat} (C : CapabilitySet) :
    (Memory.platform_of N).is_compatible C := by
  intro mu l b ℓ _ hheap
  unfold Memory.platform_of Heap.platform_of at hheap
  simp only at hheap
  split at hheap
  · injection hheap with hc
    injection hc with hcell
    injection hcell with _ hℓ
    exact hℓ.symm
  · exact absurd hheap (by simp)

/-- The platform environment is separation-well-formed: all its capture variables
  carry `.access_only` authority, so the `EnvSepWf` obligation (only `.can_drop`
  pairs must be separated) is vacuous. -/
theorem platform_env_sep_wf {N : Nat} : (TypeEnv.platform_of N).EnvSepWf := by
  induction N with
  | zero =>
    intro c1 _ _ _ _
    cases c1
  | succ N ih =>
    unfold TypeEnv.platform_of
    exact (ih.extend_cvar_access_only).extend_var

theorem env_typing_of_platform {N : Nat} :
  EnvTyping
    (Ctx.platform_of N)
    (TypeEnv.platform_of N)
    (Memory.platform_of N) := by
  induction N with
  | zero =>
    unfold Ctx.platform_of TypeEnv.platform_of
    exact True.intro
  | succ N ih =>
    unfold Ctx.platform_of TypeEnv.platform_of EnvTyping
    simp only [List.empty_eq]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · change Ty.val_denot _ (.cell _) _ _
      unfold Ty.val_denot
      refine ⟨?_, N, false, .live, rfl, ?_, ?_⟩
      · simp only [List.empty_eq]
        apply CaptureSet.WfInHeap.wf_var_free
        change (Heap.platform_of (N + 1)) N = some (.capability (.mcell false .live))
        unfold Heap.platform_of
        simp
      · change (Heap.platform_of (N + 1)) N = some (.capability (.mcell false .live))
        unfold Heap.platform_of
        simp
      · simp only [CaptureSet.denot, CaptureSet.subst, Subst.from_TypeEnv,
          CaptureSet.applyAccess_M, CaptureSet.applyMut_epsilon]
        change ((CaptureSet.var (.M .epsilon) (.free N)).ground_denot
          (Memory.platform_of (N + 1))).covers (.access .epsilon) N
        have hg : (CaptureSet.var (.M .epsilon) (.free N)).ground_denot
            (Memory.platform_of (N + 1)) = CapabilitySet.singleton .epsilon N := by
          simp [CaptureSet.ground_denot, reachability_of_loc, Memory.platform_of,
            Heap.platform_of, CapabilitySet.singleton]
        rw [hg]
        exact CapabilitySet.covers.here CapMode.Le.refl
    · simp only [Ty.captureSet, CaptureSet.peakset, CaptureSet.peaks]
    · apply CaptureSet.WfInHeap.wf_var_free
      change (Heap.platform_of (N + 1)) N = some (.capability (.mcell false .live))
      unfold Heap.platform_of
      simp
    · exact CaptureBound.WfInHeap.wf_unbound
    · exact CapabilitySet.BoundedBy.top
    · simp [CaptureSet.ground_denot, reachability_of_loc,
        Memory.platform_of, Heap.platform_of, CapabilitySet.singleton]
    · refine ⟨?_, rfl, ?_⟩
      · intro l hmem
        cases hmem
      · exact env_typing_platform_monotonic (N := N) (M := N + 1) (by omega) ih

/-- An expression `e` is safe with a platform environment of `N` mutable cells iff
    every state reachable from `e` on the platform under the sequential schedule
    `SeqReduce` is progressive (an answer, or able to take another `SeqStep`). -/
def Exp.SafeWithPlatform (e : Exp {}) (N : Nat) : Prop :=
  ∀ t M1 e1,
    SeqReduce t (Memory.platform_of N) e M1 e1 ->
    IsProgressive M1 e1

/-- Adequacy of semantic typing on platform contexts: a semantically well-typed,
    closed program is safe with the platform — every reachable state is
    progressive. The platform memory is compatible with any budget and is
    separation-well-formed, discharging the two extra `SemanticTyping` obligations. -/
theorem adequacy_platform {e : Exp (Sig.platform_of N)}
  (ht : SemanticTyping C (Ctx.platform_of N) e E)
  (hwfe : Exp.WfInHeap e (Heap.platform_of N)) :
  (e.subst (Subst.from_TypeEnv (TypeEnv.platform_of N))).SafeWithPlatform N := by
  unfold Exp.SafeWithPlatform
  intro t M1 e1 hred
  have hdenot := ht (TypeEnv.platform_of N) (Memory.platform_of N)
    env_typing_of_platform platform_env_sep_wf (platform_is_compatible _)
  unfold Ty.exi_exp_denot at hdenot
  have hwf : Exp.WfInHeap (e.subst (Subst.from_TypeEnv (TypeEnv.platform_of N)))
      (Memory.platform_of N).heap :=
    Exp.wf_subst hwfe (from_TypeEnv_wf_in_heap env_typing_of_platform)
  exact eval_implies_progressive
    (reduce_preserves_eval hdenot hwf hred)

/-! ## Adequacy under the genuine interleaving schedule

  `adequacy_platform` carries over from the sequential `SeqReduce` to the GENUINE
  interleaving relation `Reduce` because progress is a consequence of `Safe` alone
  (`safe_implies_progressive`), and `Safe` is preserved under genuine `Step`
  (`Step.preserves_safe`).  No confluence or trace reordering is needed for progress. -/

/-- `Safe` is preserved along a genuine interleaving reduction `Reduce`. -/
theorem Reduce.preserves_safe {t : Trace} {m1 m2 : Memory} {e1 e2 : Exp {}}
    (hred : Reduce t m1 e1 m2 e2) (hwf : e1.WfInHeap m1.heap) :
    Safe m1 e1 → Safe m2 e2 := by
  induction hred with
  | refl => exact fun hs => hs
  | step hstep _ ih =>
    intro hs
    exact ih (Step.preserves_wf hstep hwf) (Step.preserves_safe hstep hwf hs)

/-- An expression is safe with the platform under the GENUINE interleaving schedule
    `Reduce`: every interleaving-reachable state is progressive (an answer, or able to
    take a step). -/
def Exp.SafeWithPlatformReduce (e : Exp {}) (N : Nat) : Prop :=
  ∀ t M1 e1,
    Reduce t (Memory.platform_of N) e M1 e1 ->
    IsProgressive M1 e1

/-- **Adequacy on platform contexts for `Reduce`.**  A semantically well-typed closed
    program is safe with the platform under the genuine interleaving schedule — every
    state reachable by arbitrary interleaving is progressive.  Shares the denotational
    input with the sequential `adequacy_platform`; progress follows from `Safe`,
    preserved under genuine `Step`. -/
theorem adequacy_platform_reduce {e : Exp (Sig.platform_of N)}
    (ht : SemanticTyping C (Ctx.platform_of N) e E)
    (hwfe : Exp.WfInHeap e (Heap.platform_of N)) :
    (e.subst (Subst.from_TypeEnv (TypeEnv.platform_of N))).SafeWithPlatformReduce N := by
  intro t M1 e1 hred
  have hdenot := ht (TypeEnv.platform_of N) (Memory.platform_of N)
    env_typing_of_platform platform_env_sep_wf (platform_is_compatible _)
  unfold Ty.exi_exp_denot at hdenot
  have hwf : Exp.WfInHeap (e.subst (Subst.from_TypeEnv (TypeEnv.platform_of N)))
      (Memory.platform_of N).heap :=
    Exp.wf_subst hwfe (from_TypeEnv_wf_in_heap env_typing_of_platform)
  exact safe_implies_progressive (Reduce.preserves_safe hred hwf hdenot.1)

/-! ## Immutability

  A read-only budget forbids writes (`.access .epsilon`). But the `ro` kind also
  permits `.drop` capabilities (`HasKind.ro_drop`), and a drop deallocates a cell
  (turning it dead and zeroing its bit), which `not_mutated` (tracking bit and
  liveness) counts as a mutation. So immutability needs the budget to be both
  read-only and drop-free. -/

/-- A read-only capability set never covers a write (`.access .epsilon`):
    its caps are `.access .ro` (and `.epsilon ≰ .ro`) or `.drop` (incomparable). -/
theorem haskind_ro_not_covers_eps {C : CapabilitySet} (h : CapabilitySet.HasKind C .ro)
    (l : Nat) : ¬ C.covers (.access .epsilon) l := by
  revert h
  induction C with
  | empty => intro _ hcov; exact CapabilitySet.not_covers_empty hcov
  | cap m' l' =>
    intro h hcov
    cases h with
    | ro_cap => cases hcov with | here hle => cases hle with | access hmu => cases hmu
    | ro_drop => cases hcov with | here hle => cases hle
  | union C1 C2 ih1 ih2 =>
    intro h hcov
    cases h with
    | ro_union h1 h2 =>
      cases hcov with
      | left hc => exact ih1 h1 hc
      | right hc => exact ih2 h2 hc

/-- `covers .drop` is the same as `hasmem .drop` (only a `.drop` cap covers a
    `.drop` request). -/
theorem covers_drop_imp_hasmem {C : CapabilitySet} {l : Nat}
    (h : C.covers .drop l) : C.hasmem .drop l := by
  revert h
  induction C with
  | empty => intro h; exact absurd h CapabilitySet.not_covers_empty
  | cap m' l' => intro h; cases h with | here hle => cases hle; exact CapabilitySet.hasmem.here
  | union C1 C2 ih1 ih2 =>
    intro h
    cases h with
    | left hc => exact CapabilitySet.hasmem.left (ih1 hc)
    | right hc => exact CapabilitySet.hasmem.right (ih2 hc)

/-- A drop-free capability set never covers a drop (`.dealloc`). -/
theorem dropfree_not_covers_drop {C : CapabilitySet} (h : C.drop_free) (l : Nat) :
    ¬ C.covers .drop l := fun hcov => h l (covers_drop_imp_hasmem hcov)

/-- If a trace is `TraceOk` for a budget that does not cover writes at `l`, and
    `l` is neither pre-allocated (`l ∉ A`) nor allocated within the trace, then
    the trace performs no write at `l`. -/
theorem traceok_no_write {C : CapabilitySet} {l : Nat}
    (hcov : ¬ C.covers (.access .epsilon) l) {A : List Nat} {t : Trace}
    (htok : TraceOkFrom C A t) :
    l ∉ A → ¬ Trace.allocd t l → TraceItem.access .epsilon l ∉ t := by
  induction htok with
  | nil => intro _ _ hmem; exact absurd hmem (by simp)
  | @alloc l' A' t' _ ih =>
    intro hA halloc hmem
    simp only [Trace.allocd, not_or] at halloc
    rcases List.mem_cons.mp hmem with heq | hmem'
    · exact absurd heq (by simp)
    · exact ih (by simp only [List.mem_cons, not_or]; exact ⟨halloc.1, hA⟩)
        halloc.2 hmem'
  | @access mu l' A' t' hc _ ih =>
    intro hA halloc hmem
    simp only [Trace.allocd] at halloc
    rcases List.mem_cons.mp hmem with heq | hmem'
    · injection heq with hmu hl'eq; subst hmu; subst hl'eq
      rcases hc with hcov' | hin
      · exact hcov hcov'
      · exact hA hin
    · exact ih hA halloc hmem'
  | @dealloc l' A' t' _ _ ih =>
    intro hA halloc hmem
    simp only [Trace.allocd] at halloc
    rcases List.mem_cons.mp hmem with heq | hmem'
    · exact absurd heq (by simp)
    · exact ih hA halloc hmem'

/-- If a trace is `TraceOk` for a budget that does not cover drops at `l`, and
    `l` is neither pre-allocated nor allocated within the trace, then the trace
    performs no drop at `l`. -/
theorem traceok_no_dealloc {C : CapabilitySet} {l : Nat}
    (hcov : ¬ C.covers .drop l) {A : List Nat} {t : Trace}
    (htok : TraceOkFrom C A t) :
    l ∉ A → ¬ Trace.allocd t l → TraceItem.dealloc l ∉ t := by
  induction htok with
  | nil => intro _ _ hmem; exact absurd hmem (by simp)
  | @alloc l' A' t' _ ih =>
    intro hA halloc hmem
    simp only [Trace.allocd, not_or] at halloc
    rcases List.mem_cons.mp hmem with heq | hmem'
    · exact absurd heq (by simp)
    · exact ih (by simp only [List.mem_cons, not_or]; exact ⟨halloc.1, hA⟩)
        halloc.2 hmem'
  | @access mu l' A' t' _ _ ih =>
    intro hA halloc hmem
    simp only [Trace.allocd] at halloc
    rcases List.mem_cons.mp hmem with heq | hmem'
    · exact absurd heq (by simp)
    · exact ih hA halloc hmem'
  | @dealloc l' A' t' hc _ ih =>
    intro hA halloc hmem
    simp only [Trace.allocd] at halloc
    rcases List.mem_cons.mp hmem with heq | hmem'
    · injection heq with hl'eq; subst hl'eq
      rcases hc with hcov' | hin
      · exact hcov hcov'
      · exact hA hin
    · exact ih hA halloc hmem'

/-- Immutability adequacy: a semantically well-typed program whose budget is
    read-only (`HasKind .ro`) and drop-free does not mutate any platform cell —
    every reachable state agrees with the initial memory on all mutable cells (bit
    and liveness). `ro` rules out writes; drop-freeness rules out deallocations
    (which `ro` would otherwise permit, and which mutate liveness). -/
theorem immutability_adequacy_platform {N : Nat} {e : Exp (Sig.platform_of N)}
    {C : CaptureSet (Sig.platform_of N)} {E : Ty .exi (Sig.platform_of N)}
    (ht : SemanticTyping C (Ctx.platform_of N) e E)
    (hwfe : Exp.WfInHeap e (Heap.platform_of N))
    (hkind : HasKind (Ctx.platform_of N) C .ro)
    (hdf : (C.denot (TypeEnv.platform_of N) (Memory.platform_of N)).drop_free) :
    ∀ t M1 e1,
      SeqReduce t (Memory.platform_of N)
        (e.subst (Subst.from_TypeEnv (TypeEnv.platform_of N))) M1 e1 ->
      (Memory.platform_of N).not_mutated M1 := by
  intro t M1 e1 hred
  have hdenot := ht (TypeEnv.platform_of N) (Memory.platform_of N)
    env_typing_of_platform platform_env_sep_wf (platform_is_compatible _)
  unfold Ty.exi_exp_denot at hdenot
  have hwf : Exp.WfInHeap (e.subst (Subst.from_TypeEnv (TypeEnv.platform_of N)))
      (Memory.platform_of N).heap :=
    Exp.wf_subst hwfe (from_TypeEnv_wf_in_heap env_typing_of_platform)
  have hro : CapabilitySet.HasKind
      (C.denot (TypeEnv.platform_of N) (Memory.platform_of N)) .ro :=
    fundamental_haskind hkind (TypeEnv.platform_of N) (Memory.platform_of N)
      env_typing_of_platform
  -- Extend the partial reduction to a full run, obtaining a `TraceOk` trace.
  obtain ⟨trest, M2, a, hred2, hans⟩ :=
    (reduce_preserves_safe hred hwf hdenot.1).has_reduction
  have hbig := reduce_to_bigstep (seqreduce_trans hred hred2) hans
  have htok : TraceOk (t ++ trest)
      (C.denot (TypeEnv.platform_of N) (Memory.platform_of N)) := (hdenot.2 _ _ _ hbig).1
  intro l b ℓ hinit
  -- `l` is pre-allocated in the platform, so it is never freshly allocated by the run.
  have hl_alloc : ¬ Trace.allocd (t ++ trest) l := by
    intro ha
    have hnone := BigStep.alloc_fresh hbig ha
    simp only [Memory.lookup] at hnone
    rw [hinit] at hnone
    exact absurd hnone (by simp)
  have hwr : TraceItem.access .epsilon l ∉ (t ++ trest) :=
    traceok_no_write (haskind_ro_not_covers_eps hro l) htok (by simp) hl_alloc
  have hdr : TraceItem.dealloc l ∉ (t ++ trest) :=
    traceok_no_dealloc (dropfree_not_covers_drop hdf l) htok (by simp) hl_alloc
  exact reduce_preserves_cell hred
    (fun hm => hwr (List.mem_append_left _ hm))
    (fun hm => hdr (List.mem_append_left _ hm)) hinit

end CoreCapybara
