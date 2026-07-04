import Semantic.CoreCapybara.Fundamental
import Semantic.CoreCapybara.Semantics.Props
namespace CoreCapybara

/-! The following defines _platforms_. -/

/-- Context signature of a platform of `n` mutable boolean cells. -/
def Sig.platform_of : Nat -> Sig
| 0 => {}
| n+1 => ((Sig.platform_of n),C),x

/-- A platform context with `n` mutable cells.  The capture variables are
  `.access_only` (the platform grants read/write access to its cells, matching the
  `.access_only` default of `TypeEnv.extend_cvar`).  Each cell stores a `bool`. -/
def Ctx.platform_of : (n : Nat) -> Ctx (Sig.platform_of n)
| 0 => .empty
| n+1 => ((Ctx.platform_of n),C[.access_only]<:.unbound),x:(.cell (.cvar (.M .epsilon) .here) .bool)

/-- The shared content value held by every platform cell. -/
def platformContent : HeapVal := ⟨.bfalse, Exp.IsSimpleVal.bfalse, {}⟩

/-- A platform heap with `N` mutable cells.  Location `0` holds the shared content value
  (`bfalse`); locations `1..N` are live mutable cells, each pointing at the content value
  at `0`.  Generic cells store the *location* of their content, so the content-closure
  invariant `mcell_wf` requires a real value cell — `0` serves all cells.  The content
  location is fixed (never itself a cell), keeping subsumption uniform across sizes. -/
def Heap.platform_of (N : Nat) : Heap :=
  fun i =>
    if i = 0 then .some (.val platformContent)
    else if i ≤ N then .some (.capability (.mcell 0 .live))
    else .none

/-- Type environment for a platform with `N` mutable cells.
  Maps each pair `(C, x)` to cell `i` at heap location `i+1` (location `0` is reserved
  for the shared content value): capture variable `C` maps to the singleton ground
  capture set `{i+1}`, term variable `x` maps to heap location `i+1`. -/
def TypeEnv.platform_of : (N : Nat) -> TypeEnv (Sig.platform_of N)
| 0 => .empty
| N+1 =>
  let cs : CaptureSet {} := .var (.M .epsilon) (.free (N+1))
  let cap := CapabilitySet.singleton .epsilon (N+1)
  let env := (TypeEnv.platform_of N).extend_cvar cs (cap := cap)
  env.extend_var (N+1) ⟨.cvar (.M .epsilon) .here, .cvar⟩

/-- The only value cell in a platform heap is the shared content value at `0`. -/
theorem Heap.platform_of_val {N l : Nat} {v : Exp {}} {hv R}
    (h : Heap.platform_of N l = some (.val ⟨v, hv, R⟩)) : v = .bfalse ∧ R = {} := by
  unfold Heap.platform_of at h
  split at h
  · injection h with hc
    injection hc with hcv
    refine ⟨?_, ?_⟩
    · have := congrArg HeapVal.unwrap hcv; simpa [platformContent] using this.symm
    · have := congrArg HeapVal.reachability hcv; simpa [platformContent] using this.symm
  · split at h <;> cases h

/-- The live mutable cells of a platform heap are exactly `1..N`, each an mcell whose
  content is location `0` and whose liveness is `.live`. -/
theorem Heap.platform_of_live {M l : Nat} (h1 : 0 < l) (h2 : l ≤ M) :
    Heap.platform_of M l = some (.capability (.mcell 0 .live)) := by
  unfold Heap.platform_of
  rw [if_neg (by omega : ¬ l = 0), if_pos h2]

/-- The platform heap is well-formed. -/
theorem Heap.platform_of_wf (N : Nat) : (Heap.platform_of N).WfHeap := by
  constructor
  · intro l hv hlookup
    obtain ⟨_, _, R⟩ := hv
    obtain ⟨hveq, _⟩ := Heap.platform_of_val hlookup
    subst hveq; exact Exp.WfInHeap.wf_bfalse
  · intro l v hv R hlookup
    obtain ⟨hveq, hReq⟩ := Heap.platform_of_val hlookup
    subst hveq; subst hReq; rfl
  · intro l v hv R hlookup
    obtain ⟨_, hReq⟩ := Heap.platform_of_val hlookup
    subst hReq
    intro mu l' hmem
    exact absurd hmem CapabilitySet.not_hasmem_empty

/-- The platform heap has finite domain {0, 1, ..., N}. -/
theorem Heap.platform_of_has_fin_dom (N : Nat) :
  (Heap.platform_of N).HasFinDom (Finset.range (N + 1)) := by
  intro l
  unfold Heap.platform_of
  constructor
  · intro h
    split at h
    · rename_i hl0; subst hl0; simp
    · split at h
      · rename_i hl0 hlN; simp only [Finset.mem_range]; omega
      · contradiction
  · intro h
    simp only [Finset.mem_range] at h
    split
    · simp
    · split
      · simp
      · rename_i hl0 hlN; omega

/-- Platform memory with `N` mutable cells. -/
def Memory.platform_of (N : Nat) : Memory where
  heap := Heap.platform_of N
  wf := Heap.platform_of_wf N
  findom := ⟨Finset.range (N + 1), Heap.platform_of_has_fin_dom N⟩
  mcell_wf := by
    intro l n hlookup
    unfold Heap.platform_of at hlookup ⊢
    split at hlookup
    · cases hlookup
    · split at hlookup
      · injection hlookup with h
        injection h with hci
        injection hci with hn _
        subst hn; simp
      · cases hlookup

/-- Platform memory M subsumes platform memory N when M ≥ N. -/
theorem platform_memory_subsumes {N M : Nat} (hNM : N ≤ M) :
  (Memory.platform_of M).subsumes (Memory.platform_of N) := by
  intro l v hlookup
  simp only [Memory.platform_of, Heap.platform_of] at hlookup ⊢
  split at hlookup
  · rename_i hl0; subst hl0
    injection hlookup with hv; subst hv
    exact ⟨_, by simp, Cell.subsumes_refl _⟩
  · split at hlookup
    · rename_i hl0 hlN
      injection hlookup with hv; subst hv
      refine ⟨.capability (.mcell 0 .live), ?_, ?_⟩
      · simp only [if_neg hl0, if_pos (by omega : l ≤ M)]
      · exact Liveness.Le.refl
    · cases hlookup

/-- EnvTyping for platform is monotonic in the memory (at a fixed budget/world): platform
  `N` types in platform `M` memory when `M ≥ N`. -/
theorem env_typing_platform_monotonic {Γ : Ctx s} {env : TypeEnv s} {N M k : Nat}
  {st : StoreTyping k}
  (hNM : N ≤ M)
  (ht : EnvTyping Γ env k st (Memory.platform_of N)) :
  EnvTyping Γ env k st (Memory.platform_of M) :=
  env_typing_monotonic ht (platform_memory_subsumes hNM)

/-- The platform memory is compatible with any capability set: every location it
  holds is a live mcell, so the liveness obligation of `is_compatible` is met, and
  locations outside its domain are `none` (vacuously fine). -/
theorem platform_is_compatible {N : Nat} (C : CapabilitySet) :
    (Memory.platform_of N).is_compatible C := by
  intro mu l b ℓ _ hheap
  simp only [Memory.platform_of, Heap.platform_of] at hheap
  split at hheap
  · cases hheap
  · split at hheap
    · injection hheap with hc
      injection hc with hcell
      injection hcell with _ hℓ
      exact hℓ.symm
    · cases hheap

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

/-! ## The platform world (store typing)

  With the world-parametrized step-indexed store, a mutable cell is typed against a
  *stored relation* — a `MonRel k = WP.SemRel k`.  Every platform cell holds a `bool`,
  whose value denotation is index/world-independent (`resolve` to `btrue`/`bfalse`), so
  its stored relation is the constant `platformBoolRel`.  The platform world of size `M`
  types locations `1..M` with this relation (location `0`, the shared content value, and
  everything past `M`, are untyped). -/

/-- Stored relation for a platform (`bool`-content) cell: the value resolves to a boolean.
  This is exactly `Ty.val_denot _ .bool` (which is env/world-independent), so the cell
  agreement biconditional against the content type is definitional. -/
def platformBoolRel (k : Nat) : MonRel k :=
  fun _ _ m e => resolve m.heap e = some .btrue ∨ resolve m.heap e = some .bfalse

/-- The platform store typing of size `N` at budget `k`: locations `1..N` carry the boolean
  relation, all others are untyped. -/
def platformWorld (N k : Nat) : StoreTyping k :=
  WP.World.mk (fun l => if 0 < l ∧ l ≤ N then some (platformBoolRel k) else none)

@[simp] theorem platformWorld_lookup (N k l : Nat) :
    (platformWorld N k).lookup l = if 0 < l ∧ l ≤ N then some (platformBoolRel k) else none := by
  simp only [platformWorld, WP.World.lookup_mk]

/-- Look up a live platform cell (`1..N`): it carries the boolean relation. -/
theorem platformWorld_lookup_pos {N k l : Nat} (h1 : 0 < l) (h2 : l ≤ N) :
    (platformWorld N k).lookup l = some (platformBoolRel k) := by
  simp only [platformWorld_lookup, if_pos (And.intro h1 h2)]

/-- Inversion: a platform-typed location is a live cell `1..N` carrying the boolean
  relation. -/
theorem platformWorld_lookup_eq {N k l : Nat} {R : MonRel k}
    (h : (platformWorld N k).lookup l = some R) :
    R = platformBoolRel k ∧ 0 < l ∧ l ≤ N := by
  simp only [platformWorld_lookup] at h
  split at h
  · rename_i hc; injection h with h; exact ⟨h.symm, hc.1, hc.2⟩
  · cases h

/-- Location `0` (the shared content value) resolves to `bfalse`. -/
theorem resolve_platform_zero (N : Nat) :
    resolve (Heap.platform_of N) (.var (.free 0)) = some .bfalse := by
  simp only [resolve, Heap.platform_of]
  rfl

/-- `reachability_of_loc` of a live platform cell is its singleton `ε`-capability. -/
theorem reachability_platform {M l : Nat} (h1 : 0 < l) (h2 : l ≤ M) :
    reachability_of_loc (Heap.platform_of M) l = CapabilitySet.singleton .epsilon l := by
  simp only [reachability_of_loc, Heap.platform_of_live h1 h2]

/-- `ground_denot` of a `.M .epsilon` capture at a live platform cell is its singleton. -/
theorem ground_denot_platform {M l : Nat} (h1 : 0 < l) (h2 : l ≤ M) :
    (CaptureSet.var (.M .epsilon) (.free l)).ground_denot (Memory.platform_of M)
      = CapabilitySet.singleton .epsilon l := by
  change (reachability_of_loc (Heap.platform_of M) l).applyAccess (.M .epsilon) = _
  simp only [reachability_platform h1 h2, CapabilitySet.applyAccess_M,
    CapabilitySet.applyMut_singleton_epsilon]

/-- **The platform memory is well-typed** for the platform world.  Store consistency: every
  world-typed location `1..N` is a live mcell.  Growth stability: the boolean relation is
  monotone under memory growth (`resolve_monotonic`).  Content typing: every live cell holds
  location `0`, which resolves to `bfalse`. -/
theorem memtyped_platform (N k : Nat) : MemTyped k (platformWorld N k) (Memory.platform_of N) := by
  refine ⟨?_, ?_, ?_⟩
  · -- StoreConsistent
    intro l R hl
    obtain ⟨_, h1, h2⟩ := platformWorld_lookup_eq hl
    exact ⟨0, .live, Heap.platform_of_live h1 h2⟩
  · -- growth-stability of the stored relation
    intro l R hl i w1 w2 m1 m2 hwle e hR
    obtain ⟨hReq, _, _⟩ := platformWorld_lookup_eq hl
    subst hReq
    simp only [platformBoolRel] at hR ⊢
    exact hR.imp (resolve_monotonic hwle.1) (resolve_monotonic hwle.1)
  · -- content typing: every live platform cell holds `bfalse` at location `0`
    intro l n R hl hlkm i
    obtain ⟨hReq, h1, h2⟩ := platformWorld_lookup_eq hl
    subst hReq
    have hn : n = 0 := by
      have hlkm' : Heap.platform_of N l = some (.capability (.mcell n .live)) := hlkm
      rw [Heap.platform_of_live h1 h2] at hlkm'
      injection hlkm' with hlkm'; injection hlkm' with hlkm'
      injection hlkm' with hn _; exact hn.symm
    subst hn
    simp only [platformBoolRel]
    exact Or.inr (resolve_platform_zero N)

/-- **The platform environment types against the platform world** (auxiliary form over a
  larger world `M ≥ N`, so the store typing and memory stay fixed across the induction —
  no world monotonicity for `EnvTyping` is needed). -/
theorem env_typing_of_platform_aux {M k : Nat} :
    ∀ {N : Nat}, N ≤ M →
      EnvTyping (Ctx.platform_of N) (TypeEnv.platform_of N) k (platformWorld M k)
        (Memory.platform_of M) := by
  intro N
  induction N with
  | zero =>
    intro _
    unfold Ctx.platform_of TypeEnv.platform_of
    exact True.intro
  | succ N ih =>
    intro hNM
    unfold Ctx.platform_of TypeEnv.platform_of EnvTyping
    simp only [List.empty_eq]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · -- value denotation of the cell-typed variable at location `N+1`
      simp only [Ty.val_denot]
      refine ⟨?_, N + 1, 0, .live, platformBoolRel k, rfl, ?_, ?_, ?_, ?_⟩
      · exact CaptureSet.WfInHeap.wf_var_free (Heap.platform_of_live (by omega) hNM)
      · exact Heap.platform_of_live (by omega) hNM
      · -- coverage: the cvar `.here` denotes the singleton at `N+1`
        simp only [CaptureSet.denot, CaptureSet.subst, Subst.from_TypeEnv,
          CaptureSet.applyAccess_M, CaptureSet.applyMut_epsilon]
        change ((CaptureSet.var (.M .epsilon) (.free (N + 1))).ground_denot
          (Memory.platform_of M)).covers (.access .epsilon) (N + 1)
        rw [ground_denot_platform (by omega) hNM]
        exact CapabilitySet.covers.here CapMode.Le.refl
      · -- store typing of the fresh cell
        exact platformWorld_lookup_pos (by omega) hNM
      · -- content agreement biconditional (definitional: bool relation vs `val_denot .bool`)
        intro j w' m' e'
        simp only [platformBoolRel]
    · simp only [Ty.captureSet, CaptureSet.peakset, CaptureSet.peaks]
    · exact CaptureSet.WfInHeap.wf_var_free (Heap.platform_of_live (by omega) hNM)
    · exact CaptureBound.WfInHeap.wf_unbound
    · exact CapabilitySet.BoundedBy.top
    · rw [ground_denot_platform (by omega) hNM]
    · refine ⟨?_, rfl, ?_⟩
      · intro l hmem
        cases hmem
      · exact ih (by omega)

/-- The platform environment types against the platform world (the diagonal). -/
theorem env_typing_of_platform {N k : Nat} :
    EnvTyping (Ctx.platform_of N) (TypeEnv.platform_of N) k (platformWorld N k)
      (Memory.platform_of N) :=
  env_typing_of_platform_aux (Nat.le_refl N)

/-- An expression `e` is safe with a platform environment of `N` mutable cells iff
    every state reachable from `e` on the platform under the sequential schedule
    `SeqReduce` is progressive (an answer, or able to take another `SeqStep`). -/
def Exp.SafeWithPlatform (e : Exp {}) (N : Nat) : Prop :=
  ∀ t M1 e1,
    SeqReduce t (Memory.platform_of N) e M1 e1 ->
    IsProgressive M1 e1

/-- Adequacy of semantic typing on platform contexts: a semantically well-typed,
    closed program is safe with the platform — every reachable state is progressive.
    Given a reachable state after a partial run with trace `t`, instantiate the semantic
    typing at read budget `t.readCount + 1`: the run is then strictly within budget, so
    `safe_reduce_progressive` applies.  The platform memory is compatible with any budget
    and separation-well-formed, discharging the two extra `SemanticTyping` obligations. -/
theorem adequacy_platform {e : Exp (Sig.platform_of N)}
  (ht : SemanticTyping C (Ctx.platform_of N) e E) :
  (e.subst (Subst.from_TypeEnv (TypeEnv.platform_of N))).SafeWithPlatform N := by
  intro t M1 e1 hred
  have hdenot := ht (TypeEnv.platform_of N) (t.readCount + 1) (platformWorld N (t.readCount + 1))
    (Memory.platform_of N) env_typing_of_platform platform_env_sep_wf (platform_is_compatible _)
  unfold Ty.exi_exp_denot at hdenot
  have heval := hdenot (memtyped_platform N (t.readCount + 1))
  exact safe_reduce_progressive heval.1 hred (by omega)

/-! ## Adequacy under the genuine interleaving schedule (deferred)

  The genuine-interleaving analogue of `adequacy_platform` (progress along the interleaving
  relation `Reduce`) is NOT available at this layer.  With the budget-indexed `Safe`, there is
  no single-step `Safe`-preservation lemma: reconstructing a `Safe.par` carrier after a lone
  branch `Step` would require transporting the rely `W` along a *partial* branch run, which the
  rely–guarantee fields (quantified over full `BigStep` runs) deliberately do not provide — and
  soundly so, since arbitrary-memory transport is exactly the false operational-monotonicity
  shape this development eliminated.  Interleaving progress therefore needs either carrier
  preservation along genuine steps (impossible here) or a carrier-free standardization result
  (`SeqReduce` covers every `Reduce`-reachable state up to Mazurkiewicz permutation + heap
  iso).  It is deferred to the standardization/confluence rework; the old
  `Reduce.preserves_safe` / `Exp.SafeWithPlatformReduce` / `adequacy_platform_reduce` (which
  rested on the now-removed `Step.preserves_safe`) are removed here. -/

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
    read-only (`HasKind .ro`) and drop-free does not mutate any platform cell along a
    partial run that *extends to an answer* — the state after the prefix agrees with the
    initial memory on all mutable cells (bit and liveness).  The extension to an answer
    is what turns the partial run into a full `BigStep` run, from which the (budget-guarded)
    `TraceOk` postcondition of the semantic typing is read off.  `ro` rules out writes;
    drop-freeness rules out deallocations (which `ro` would otherwise permit, and which
    mutate liveness). -/
theorem immutability_adequacy_platform {N : Nat} {e : Exp (Sig.platform_of N)}
    {C : CaptureSet (Sig.platform_of N)} {E : Ty .exi (Sig.platform_of N)}
    (ht : SemanticTyping C (Ctx.platform_of N) e E)
    (hkind : HasKind (Ctx.platform_of N) C .ro)
    (hdf : (C.denot (TypeEnv.platform_of N) (Memory.platform_of N)).drop_free) :
    ∀ t trest M1 e1 M2 a,
      SeqReduce t (Memory.platform_of N)
        (e.subst (Subst.from_TypeEnv (TypeEnv.platform_of N))) M1 e1 ->
      SeqReduce trest M1 e1 M2 a ->
      a.IsAns ->
      (Memory.platform_of N).not_mutated M1 := by
  intro t trest M1 e1 M2 a hred hrest hans
  have hdenot := ht (TypeEnv.platform_of N) ((t ++ trest).readCount + 1)
    (platformWorld N ((t ++ trest).readCount + 1)) (Memory.platform_of N)
    env_typing_of_platform platform_env_sep_wf (platform_is_compatible _)
  unfold Ty.exi_exp_denot at hdenot
  have heval := hdenot (memtyped_platform N ((t ++ trest).readCount + 1))
  have hro : CapabilitySet.HasKind
      (C.denot (TypeEnv.platform_of N) (Memory.platform_of N)) .ro :=
    fundamental_haskind hkind (TypeEnv.platform_of N) ((t ++ trest).readCount + 1)
      (platformWorld N ((t ++ trest).readCount + 1)) (Memory.platform_of N)
      env_typing_of_platform
  have hbig := reduce_to_bigstep (seqreduce_trans hred hrest) hans
  have htok : TraceOk (t ++ trest)
      (C.denot (TypeEnv.platform_of N) (Memory.platform_of N)) :=
    (heval.2 _ _ _ hbig (by omega)).1
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

/-- Immutability adequacy for a full run to an answer: a read-only, drop-free program that
    reduces to an answer leaves the platform memory unmutated.  Special case of
    `immutability_adequacy_platform` with the answer state itself as the prefix endpoint
    (`trest = refl`). -/
theorem immutability_adequacy_platform_run {N : Nat} {e : Exp (Sig.platform_of N)}
    {C : CaptureSet (Sig.platform_of N)} {E : Ty .exi (Sig.platform_of N)}
    (ht : SemanticTyping C (Ctx.platform_of N) e E)
    (hkind : HasKind (Ctx.platform_of N) C .ro)
    (hdf : (C.denot (TypeEnv.platform_of N) (Memory.platform_of N)).drop_free) :
    ∀ t M2 a,
      SeqReduce t (Memory.platform_of N)
        (e.subst (Subst.from_TypeEnv (TypeEnv.platform_of N))) M2 a ->
      a.IsAns ->
      (Memory.platform_of N).not_mutated M2 :=
  fun t M2 a hred hans =>
    immutability_adequacy_platform ht hkind hdf t [] M2 a M2 a hred SeqReduce.refl hans

end CoreCapybara
