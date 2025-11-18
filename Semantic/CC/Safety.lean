import Semantic.CC.Fundamental
import Semantic.CC.Semantics.Props
namespace CC

/-! The following defines _platforms_. -/

/-- Context signature of a platform of `n` ground capabilities. -/
def Sig.platform_of : Nat -> Sig
| 0 => {}
| n+1 => ((Sig.platform_of n),C),x

/-- A platform context with `n` ground capabilities. -/
def Ctx.platform_of : (n : Nat) -> Ctx (Sig.platform_of n)
| 0 => .empty
| n+1 => ((Ctx.platform_of n),C<:.unbound),x:(.capt (.cvar .here) .cap)

/-- A platform heap with `n` ground capabilities. -/
def Heap.platform_of (N : Nat) : Heap :=
  fun i =>
    if i < N then
      .some .capability
    else
      .none

/-- The size of a signature. -/
def Sig.size : Sig -> Nat :=
  fun s => s.length

/-- Debruijn-level of a bound variable. -/
def BVar.level : BVar s k -> Nat
| .here => s.length
| .there x => x.level

/-- Convert a capture set in a platform context to a concrete capability set.
  Platform contexts have `N` capabilities arranged as pairs `(C, x)` at levels
  `(0,1), (2,3), ..., (2N-2, 2N-1)`, where capability `i` corresponds to
  variables at levels `2i` and `2i+1`. Bound variables map via `level / 2`,
  while free variables directly reference heap locations. -/
def CaptureSet.to_platform_capability_set : CaptureSet (Sig.platform_of N) -> CapabilitySet
| .empty => .empty
| .union cs1 cs2 =>
    (cs1.to_platform_capability_set) ∪ (cs2.to_platform_capability_set)
| .var x =>
    match x with
    | .bound b => .cap (b.level / 2)
    | .free n => .cap n
| .cvar c => .cap (c.level / 2)

/-- Type environment for a platform with `N` ground capabilities.
  Maps each pair `(C, x)` to capability `i` at heap location `i`:
  capture variable `C` maps to singleton ground capture set `{i}`,
  term variable `x` maps to heap location `i`. -/
def TypeEnv.platform_of : (N : Nat) -> TypeEnv (Sig.platform_of N)
| 0 => .empty
| N+1 => ((TypeEnv.platform_of N).extend_cvar (.var (.free N))).extend_var N

/-- The platform heap is well-formed: it contains only capabilities, no values. -/
theorem Heap.platform_of_wf (N : Nat) : (Heap.platform_of N).WfHeap := by
  constructor
  · -- wf_val: no values in the platform heap
    intro l hv hlookup
    unfold Heap.platform_of at hlookup
    split at hlookup <;> cases hlookup
  · -- wf_reach: no values in the platform heap
    intro l v hv R hlookup
    unfold Heap.platform_of at hlookup
    split at hlookup <;> cases hlookup

/-- The platform heap has finite domain {0, 1, ..., N-1}. -/
theorem Heap.platform_of_has_fin_dom (N : Nat) :
  (Heap.platform_of N).HasFinDom (Finset.range N) := by
  intro l
  unfold Heap.platform_of
  constructor
  · -- If heap is not none, then l < N
    intro h
    split at h
    case isTrue hlt =>
      simp [Finset.mem_range, hlt]
    case isFalse =>
      contradiction
  · -- If l ∈ range N, then heap is not none
    intro h
    simp [Finset.mem_range] at h
    split
    case isTrue => simp
    case isFalse hf => omega

/-- Platform memory with `N` ground capabilities. -/
def Memory.platform_of (N : Nat) : Memory where
  heap := Heap.platform_of N
  wf := Heap.platform_of_wf N
  findom := ⟨Finset.range N, Heap.platform_of_has_fin_dom N⟩

/-- Platform memory M subsumes platform memory N when M ≥ N. -/
theorem platform_memory_subsumes {N M : Nat} (hNM : N ≤ M) :
  (Memory.platform_of M).subsumes (Memory.platform_of N) := by
  intro l v hlookup
  unfold Memory.platform_of Heap.platform_of at hlookup ⊢
  simp at hlookup ⊢
  constructor
  · omega
  · exact hlookup.2

/-- EnvTyping for platform is monotonic: platform N types in platform M memory when M ≥ N. -/
theorem env_typing_platform_monotonic {Γ : Ctx s} {env : TypeEnv s} {N M : Nat}
  (hNM : N ≤ M)
  (ht : EnvTyping Γ env (Memory.platform_of N)) :
  EnvTyping Γ env (Memory.platform_of M) := by
  -- Use the existing monotonicity theorem for EnvTyping
  apply env_typing_monotonic
  · exact ht
  · exact platform_memory_subsumes hNM

theorem env_typing_of_platform {N : Nat} :
  EnvTyping
    (Ctx.platform_of N)
    (TypeEnv.platform_of N)
    (Memory.platform_of N) := by
  induction N with
  | zero =>
    -- Base case: empty environment
    unfold Ctx.platform_of TypeEnv.platform_of
    exact True.intro
  | succ N ih =>
    -- Inductive case: add capture variable C and term variable x
    unfold Ctx.platform_of TypeEnv.platform_of EnvTyping
    simp [TypeEnv.extend_cvar, TypeEnv.extend_var]
    constructor
    · -- Term variable x : .capt (.cvar .here) .cap at location N
      unfold Ty.capt_val_denot
      constructor
      · -- Is simple answer
        apply Exp.IsSimpleAns.is_var
      · constructor
        · -- Well-formed in heap
          apply Exp.WfInHeap.wf_var
          apply Var.WfInHeap.wf_free
          show (Heap.platform_of (N + 1)) N = some Cell.capability
          unfold Heap.platform_of
          simp
        · constructor
          · -- Capture set after substitution is well-formed
            simp [CaptureSet.subst, Subst.from_TypeEnv, TypeEnv.lookup_cvar, TypeEnv.lookup]
            apply CaptureSet.WfInHeap.wf_var_free
            show (Heap.platform_of (N + 1)) N = some Cell.capability
            unfold Heap.platform_of
            simp
          · -- Shape typing: N is a capability with reachability {N}
            unfold Ty.shape_val_denot
            constructor
            · -- Well-formed
              apply Exp.WfInHeap.wf_var
              apply Var.WfInHeap.wf_free
              show (Heap.platform_of (N + 1)) N = some Cell.capability
              unfold Heap.platform_of
              simp
            · -- Exists label N that is a capability
              use N
              constructor
              · rfl
              · constructor
                · -- m.lookup N = some .capability
                  unfold Memory.lookup Memory.platform_of Heap.platform_of
                  simp
                · -- N is in the authority set from capture set denot
                  simp [CaptureSet.denot, CaptureSet.subst, Subst.from_TypeEnv,
                    TypeEnv.lookup_cvar, TypeEnv.lookup,
                    CaptureSet.ground_denot, reachability_of_loc,
                    Memory.platform_of]
                  unfold Heap.platform_of
                  simp
                  apply CapabilitySet.mem.here
    · -- Capture variable C with bound .unbound
      constructor
      · -- cs.WfInHeap
        apply CaptureSet.WfInHeap.wf_var_free
        show (Heap.platform_of (N + 1)) N = some Cell.capability
        unfold Heap.platform_of
        simp
      · constructor
        · -- Bound substituted is well-formed
          simp [CaptureBound.subst]
          apply CaptureBound.WfInHeap.wf_unbound
        · constructor
          · -- cs.ground_denot bounded by unbound denot
            apply CapabilitySet.BoundedBy.top
          · -- Recursive: platform N types in platform (N+1) memory
            apply env_typing_platform_monotonic (N := N) (M := N + 1)
            · omega
            · exact ih

/-- An expression `e` is safe with a platform environment of `N` ground
    capabilities under permission `P` iff for any possible reduction state
    starting from `e` on the platform, it is progressive. -/
def Exp.SafeWithPlatform (e : Exp {}) (N : Nat) (P : CapabilitySet) : Prop :=
  ∀ M1 e1,
    Reduce P (Memory.platform_of N) e M1 e1 ->
    IsProgressive P M1 e1

end CC
