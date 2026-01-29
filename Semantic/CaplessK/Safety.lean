import Semantic.CaplessK.Fundamental
import Semantic.CaplessK.Semantics.Props
namespace CaplessK

/-! The following defines _platforms_. -/

/-- Context signature of a platform of `n` ground capabilities. -/
def Sig.platform_of : Nat -> Sig
| 0 => {}
| n+1 => ((Sig.platform_of n),C),x

/-- A platform context with `n` ground capabilities. -/
def Ctx.platform_of : (n : Nat) -> Ctx (Sig.platform_of n)
| 0 => .empty
| n+1 => ((Ctx.platform_of n),C<:(.unbound .top)),x:(.capt (.cvar .here .top) .cap)

/-- A platform heap with `n` ground capabilities (basic capabilities). -/
def Heap.platform_of (N : Nat) : Heap :=
  fun i =>
    if i < N then
      .some (.capability .basic)
    else
      .none

/-- The size of a signature. -/
def Sig.size : Sig -> Nat :=
  fun s => s.length

/-- Debruijn-level of a bound variable. -/
def BVar.level : BVar s k -> Nat
| .here => by
  rename_i s0
  exact s0.size
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
| .var x _ =>
    match x with
    | .bound b => .cap (b.level / 2)
    | .free n => .cap n
| .cvar c _ => .cap (c.level / 2)

/-- A predicate asserting all kind annotations in a capture set are .top. -/
def CaptureSet.AllKindsTop : CaptureSet s -> Prop
| .empty => True
| .union cs1 cs2 => cs1.AllKindsTop ∧ cs2.AllKindsTop
| .var _ K => K = .top
| .cvar _ K => K = .top

/-- Type environment for a platform with `N` ground capabilities.
  Maps each pair `(C, x)` to capability `i` at heap location `i`:
  capture variable `C` maps to singleton ground capture set `{i}`,
  term variable `x` maps to heap location `i`. -/
def TypeEnv.platform_of : (N : Nat) -> TypeEnv (Sig.platform_of N)
| 0 => .empty
| N+1 => ((TypeEnv.platform_of N).extend_cvar (.var (.free N) .top)).extend_var N

def DenotCtx.platform_of (N : Nat) : DenotCtx (Sig.platform_of N) :=
  ⟨TypeEnv.platform_of N⟩

/-- The platform heap is well-formed: it contains only capabilities, no values. -/
theorem Heap.platform_of_wf (N : Nat) : (Heap.platform_of N).WfHeap where
  wf_val := by
    intro l hv hlookup
    unfold Heap.platform_of at hlookup
    split at hlookup <;> cases hlookup
  wf_reach := by
    intro l v hv R hlookup
    unfold Heap.platform_of at hlookup
    split at hlookup <;> cases hlookup
  wf_reachability := by
    intro l hv hlookup
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

/-- Reachability of a location in platform heap is just the singleton set. -/
theorem reachability_of_loc_platform {l : Nat} (hl : l < N) :
  reachability_of_loc (Heap.platform_of N) l = {l} := by
  unfold reachability_of_loc Heap.platform_of
  simp [hl]

/-- Projection of a capability in the platform heap by .top preserves the capability. -/
theorem proj_platform_top {l : Nat} (hl : l < N) :
  (CapabilitySet.cap l).proj (Heap.platform_of N) .top = CapabilitySet.cap l := by
  simp only [CapabilitySet.proj, proj_capability, classifier_of_loc, Heap.platform_of, hl,
    ↓reduceIte, CapabilityInfo.classifier, CapKind.subkind_top']

/-- Projection by any .top kind preserves capability in platform heap. -/
theorem proj_platform_kind_top {l : Nat} (hl : l < N) {K : CapKind} (hK : K = .top) :
  (CapabilitySet.cap l).proj (Heap.platform_of N) K = CapabilitySet.cap l := by
  subst hK
  exact proj_platform_top hl

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
theorem env_typing_platform_monotonic {Γ : Ctx s} {ctx : DenotCtx s} {N M : Nat}
  (hNM : N ≤ M)
  (ht : EnvTyping Γ ctx (Memory.platform_of N)) :
  EnvTyping Γ ctx (Memory.platform_of M) := by
  -- Use the existing monotonicity theorem for EnvTyping
  apply env_typing_monotonic
  · exact ht
  · exact platform_memory_subsumes hNM

theorem env_typing_of_platform {N : Nat} :
  EnvTyping
    (Ctx.platform_of N)
    (DenotCtx.platform_of N)
    (Memory.platform_of N) := by
  induction N with
  | zero =>
    -- Base case: empty environment
    unfold Ctx.platform_of DenotCtx.platform_of TypeEnv.platform_of
    exact True.intro
  | succ N ih =>
    -- Inductive case: add capture variable C and term variable x
    unfold Ctx.platform_of DenotCtx.platform_of TypeEnv.platform_of EnvTyping
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
          show (Heap.platform_of (N + 1)) N = some (.capability .basic)
          unfold Heap.platform_of
          simp
        · constructor
          · -- Capture set after substitution is well-formed
            simp [CaptureSet.subst]
            apply CaptureSet.WfInHeap.wf_var_free
            show (Heap.platform_of (N + 1)) N = some (.capability .basic)
            unfold Heap.platform_of
            simp
          · -- Shape typing: N is a capability with reachability {N}
            unfold Ty.shape_val_denot
            constructor
            · -- Well-formed
              apply Exp.WfInHeap.wf_var
              apply Var.WfInHeap.wf_free
              show (Heap.platform_of (N + 1)) N = some (.capability .basic)
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
                  simp only [CaptureSet.denot, CaptureSet.subst,
                    Memory.platform_of]
                  -- The kind is intersect .top .top = .top
                  change N ∈ (reachability_of_loc (Heap.platform_of (N+1)) N).proj
                    (Heap.platform_of (N+1)) (CapKind.top.intersect CapKind.top)
                  have hN : N < N + 1 := Nat.lt_succ_self N
                  rw [CapKind.intersect.top_l, reachability_of_loc_platform hN]
                  have hwf : (CapabilitySet.cap N).WfInHeap (Heap.platform_of (N + 1)) := by
                    intro l hl; cases hl
                    exact ⟨.capability .basic, by unfold Heap.platform_of; simp [hN]⟩
                  -- Unfold singleton and apply proj_top
                  change N ∈ (CapabilitySet.cap N).proj (Heap.platform_of (N + 1)) .top
                  rw [CapabilitySet.proj_top hwf]
                  exact CapabilitySet.mem.here
    · -- Capture variable C with bound .unbound
      constructor
      · -- cs.WfInHeap
        apply CaptureSet.WfInHeap.wf_var_free
        show (Heap.platform_of (N + 1)) N = some (.capability .basic)
        unfold Heap.platform_of
        simp
      · constructor
        · -- Bound substituted is well-formed
          simp [CaptureBound.subst]
          apply CaptureBound.WfInHeap.wf_unbound
        · constructor
          · -- cs.ground_denot bounded by unbound denot
            apply CapabilitySet.BoundedBy.top
            -- Show HasKind for the ground_denot
            -- First simplify: ground_denot of (var (.free N) .top) is {N}.proj H .top = {N}
            simp only [CaptureSet.ground_denot, Memory.platform_of]
            have hN : N < N + 1 := Nat.lt_succ_self N
            have hwf_cap : (CapabilitySet.cap N).WfInHeap (Heap.platform_of (N + 1)) := by
              intro l hl; cases hl
              exact ⟨.capability .basic, by unfold Heap.platform_of; simp [hN]⟩
            -- Rewrite reachability to get {N}
            rw [reachability_of_loc_platform hN]
            -- The projection of {N} by .top equals {N} (proj_top)
            -- We need to show well-formedness of the projected set
            have heq : (CapabilitySet.cap N).proj (Heap.platform_of (N + 1)) .top =
                CapabilitySet.cap N := CapabilitySet.proj_top hwf_cap
            -- Convert the goal to use cap N directly
            change CapabilitySet.HasKind (Heap.platform_of (N + 1))
              ((CapabilitySet.cap N).proj (Heap.platform_of (N + 1)) .top) .top
            rw [heq]
            exact CapabilitySet.HasKind.of_wf_top hwf_cap
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

/-- The length of a platform signature is 2*N. -/
theorem Sig.platform_of_length : (Sig.platform_of N).length = 2 * N := by
  induction N with
  | zero => rfl
  | succ N ih =>
    unfold Sig.platform_of Sig.extend_cvar Sig.extend_var
    simp only [List.length]
    rw [ih]
    omega

/-- Lookup of term variable in platform environment. -/
theorem TypeEnv.lookup_var_platform {x : BVar (Sig.platform_of N) .var} :
  (TypeEnv.platform_of N).lookup_var x = x.level / 2 := by
  induction N with
  | zero =>
    -- No variables in empty signature
    cases x
  | succ N ih =>
    -- Platform (N+1) extends with C then x
    -- So x is either .here (x_N) or .there (.there x'') (from platform N)
    unfold TypeEnv.platform_of
    cases x with
    | here =>
      -- This is the most recent term variable x_N
      -- x.here : BVar (Sig.platform_of (N+1)) .var
      -- where Sig.platform_of (N+1) = ((platform_of N),C),x
      -- With new BVar.level definition: .here.level = ((platform_of N),C).length = 2*N + 1
      unfold TypeEnv.platform_of TypeEnv.lookup_var TypeEnv.extend_var TypeEnv.extend_cvar
      simp [TypeEnv.lookup, BVar.level, Sig.size]
      -- Goal: N = List.length (Sig.platform_of N,C) / 2
      -- (Sig.platform_of N,C).length = 1 + (Sig.platform_of N).length = 1 + 2*N = 2*N + 1
      unfold Sig.extend_cvar
      simp only [List.length]
      rw [Sig.platform_of_length]
      -- Goal: N = (2 * N + 1) / 2
      omega
    | there x' =>
      cases x' with
      | there x'' =>
        -- x'' : BVar (Sig.platform_of N) .var (skipping over the C)
        unfold TypeEnv.lookup_var TypeEnv.lookup TypeEnv.extend_var TypeEnv.extend_cvar
        simp [TypeEnv.lookup]
        have h := ih (x := x'')
        unfold TypeEnv.lookup_var at h
        rw [h]
        simp only [BVar.level]

/-- Lookup of capture variable in platform environment. -/
theorem TypeEnv.lookup_cvar_platform {c : BVar (Sig.platform_of N) .cvar} :
  (TypeEnv.platform_of N).lookup_cvar c = .var (.free (c.level / 2)) .top := by
  induction N with
  | zero =>
    -- No capture variables in empty signature
    cases c
  | succ N ih =>
    -- Platform (N+1) extends with C then x
    -- So signature is ((Sig.platform_of N),C),x
    unfold TypeEnv.platform_of
    -- c : BVar (((Sig.platform_of N),C),x) .cvar
    -- Must be of form .there c' since outermost is x (a var)
    cases c with
    | there c' =>
      -- c' : BVar ((Sig.platform_of N),C) ?
      -- Could be .here (the C) or .there c'' (from N)
      cases c' with
      | here =>
        -- This is the most recent capture variable C_N
        -- c = .there .here, where .here refers to C in (platform N, C)
        unfold TypeEnv.lookup_cvar TypeEnv.extend_var TypeEnv.extend_cvar
        simp [TypeEnv.lookup]
        -- After simp, goal is: .var (.free N) = .var (.free (BVar.here.there.level / 2))
        -- .there preserves level, so .here.there.level = .here.level
        -- .here.level = length of (platform_of N) = 2*N
        simp only [BVar.level, Sig.size]
        -- Goal: N = List.length (Sig.platform_of N) / 2
        rw [Sig.platform_of_length]
        -- Goal: N = (2 * N) / 2
        omega
      | there c'' =>
        -- c'' : BVar (Sig.platform_of N) .cvar
        -- c = .there (.there c'')
        -- By definition of BVar.level, .there preserves level
        -- So c.level = c''.level
        unfold TypeEnv.lookup_cvar TypeEnv.extend_var TypeEnv.extend_cvar
        simp [TypeEnv.lookup]
        -- Now the lookup simplifies to lookup in the base environment
        have h := ih (c := c'')
        unfold TypeEnv.lookup_cvar at h
        -- The goal now mentions c''.there.there.level which equals c''.level
        simp only [BVar.level] at h ⊢
        exact h

/-- For any bound term variable in a platform signature, its level divided by 2 is less than N. -/
theorem BVar.level_var_bound {b : BVar (Sig.platform_of N) .var} : b.level / 2 < N := by
  induction N with
  | zero => cases b
  | succ N ih =>
    -- Sig.platform_of (N+1) = ((Sig.platform_of N),C),x
    cases b with
    | here =>
      -- b.level = ((Sig.platform_of N),C).length = 2*N + 1
      unfold BVar.level Sig.size Sig.extend_cvar
      simp only [List.length]
      rw [Sig.platform_of_length]
      -- Goal: (2 * N + 1) / 2 < N + 1, which is N < N + 1
      omega
    | there b' =>
      cases b' with
      | there b'' =>
        -- b'': BVar (Sig.platform_of N) .var
        -- b''.there.there.level = b''.there.level = b''.level
        simp only [BVar.level]
        have := ih (b := b'')
        omega

/-- For any bound capture variable in a platform signature,
    its level divided by 2 is less than N. -/
theorem BVar.level_cvar_bound {c : BVar (Sig.platform_of N) .cvar} : c.level / 2 < N := by
  induction N with
  | zero => cases c
  | succ N ih =>
    -- Sig.platform_of (N+1) = ((Sig.platform_of N),C),x
    -- c must be .there c' since outermost is x (a var)
    cases c with
    | there c' =>
      cases c' with
      | here =>
        -- c'.level = (Sig.platform_of N).length = 2*N
        simp only [BVar.level, Sig.size]
        rw [Sig.platform_of_length]
        -- Goal: (2 * N) / 2 < N + 1, which is N < N + 1
        omega
      | there c'' =>
        -- c'': BVar (Sig.platform_of N) .cvar
        -- c''.there.there.level = c''.there.level = c''.level
        simp only [BVar.level]
        have := ih (c := c'')
        omega

/-- The denotation of a capture set in the platform environment equals
    its direct capability set translation, provided the capture set is well-formed
    and all kind annotations are .top. -/
theorem capture_set_denot_eq_platform {C : CaptureSet (Sig.platform_of N)}
  (hwf : C.WfInHeap (Heap.platform_of N))
  (htop : C.AllKindsTop) :
  C.denot (DenotCtx.platform_of N) (Memory.platform_of N) = C.to_platform_capability_set := by
  unfold CaptureSet.denot
  induction C with
  | empty =>
    -- Empty capture set
    unfold CaptureSet.subst CaptureSet.ground_denot CaptureSet.to_platform_capability_set
    rfl
  | union cs1 cs2 ih1 ih2 =>
    -- Union of capture sets
    cases hwf with
    | wf_union hwf1 hwf2 =>
      simp only [CaptureSet.AllKindsTop] at htop
      unfold CaptureSet.subst CaptureSet.to_platform_capability_set CaptureSet.ground_denot
      unfold CaptureSet.denot at ih1 ih2
      rw [ih1 hwf1 htop.1, ih2 hwf2 htop.2]
  | var x K =>
    -- Variable (term variable used as capture)
    simp only [CaptureSet.AllKindsTop] at htop
    unfold CaptureSet.subst CaptureSet.to_platform_capability_set
    cases x with
    | bound b =>
      simp only [Subst.from_DenotCtx, DenotCtx.platform_of]
      unfold Subst.from_TypeEnv Var.subst
      simp only [CaptureSet.ground_denot]
      rw [TypeEnv.lookup_var_platform]
      have hlevel : b.level / 2 < N := BVar.level_var_bound
      unfold Memory.platform_of
      simp only
      rw [reachability_of_loc_platform hlevel]
      -- Now show {l}.proj H K = {l} using K = .top
      have hwf_cap : (CapabilitySet.cap (b.level / 2)).WfInHeap (Heap.platform_of N) := by
        intro l hl; cases hl
        exact ⟨.capability .basic, by unfold Heap.platform_of; simp [hlevel]⟩
      rw [htop]
      change (CapabilitySet.cap (b.level / 2)).proj (Heap.platform_of N) .top =
        CapabilitySet.cap (b.level / 2)
      exact CapabilitySet.proj_top hwf_cap
    | free n =>
      cases hwf with
      | wf_var_free hlookup =>
        simp only [Subst.from_DenotCtx, DenotCtx.platform_of]
        unfold Subst.from_TypeEnv Var.subst
        simp only [CaptureSet.ground_denot]
        unfold Memory.platform_of
        simp only
        have hn : n < N := by
          unfold Heap.platform_of at hlookup
          split at hlookup
          case isTrue h => exact h
          case isFalse => contradiction
        rw [reachability_of_loc_platform hn]
        have hwf_cap : (CapabilitySet.cap n).WfInHeap (Heap.platform_of N) := by
          intro l hl; cases hl
          exact ⟨.capability .basic, by unfold Heap.platform_of; simp [hn]⟩
        rw [htop]
        change (CapabilitySet.cap n).proj (Heap.platform_of N) .top = CapabilitySet.cap n
        exact CapabilitySet.proj_top hwf_cap
  | cvar c K =>
    -- Capture variable
    simp only [CaptureSet.AllKindsTop] at htop
    unfold CaptureSet.subst CaptureSet.to_platform_capability_set
    simp only [Subst.from_DenotCtx, DenotCtx.platform_of, Subst.from_TypeEnv]
    rw [TypeEnv.lookup_cvar_platform]
    rw [CaptureSet.ground_denot_proj_eq]
    unfold CaptureSet.ground_denot Memory.platform_of
    simp only
    have hlevel : c.level / 2 < N := BVar.level_cvar_bound
    rw [reachability_of_loc_platform hlevel]
    have hwf_cap : (CapabilitySet.cap (c.level / 2)).WfInHeap (Heap.platform_of N) := by
      intro l hl; cases hl
      exact ⟨.capability .basic, by unfold Heap.platform_of; simp [hlevel]⟩
    -- Now we have ({l}.proj H .top).proj H K = {l}
    -- Convert goal to use cap directly
    change ((CapabilitySet.cap (c.level / 2)).proj (Heap.platform_of N) .top).proj
        (Heap.platform_of N) K = CapabilitySet.cap (c.level / 2)
    rw [CapabilitySet.proj_top hwf_cap]
    -- Then, {l}.proj H K = {l} using K = .top
    rw [htop, CapabilitySet.proj_top hwf_cap]

/-- Adequacy of semantic typing on platform contexts.
    Requires that the capture set is closed (contains no free variables)
    and all kind annotations are .top. -/
theorem adequacy_platform {e : Exp (Sig.platform_of N)}
  (ht : SemanticTyping C (Ctx.platform_of N) e E)
  (hclosed : C.IsClosed)
  (htop : C.AllKindsTop) :
  (e.subst (Subst.from_DenotCtx (DenotCtx.platform_of N))).SafeWithPlatform
    N
    (C.to_platform_capability_set) := by
  unfold Exp.SafeWithPlatform
  intro M1 e1 hred
  -- Apply semantic typing with platform environment
  have hdenot := ht (DenotCtx.platform_of N) (Memory.platform_of N) env_typing_of_platform
  -- Derive well-formedness from closedness
  have hwf : C.WfInHeap (Heap.platform_of N) := CaptureSet.wf_of_closed hclosed
  -- Rewrite using the equality of capability sets
  rw [capture_set_denot_eq_platform hwf htop] at hdenot
  -- Preservation: Eval is preserved under reduction
  have heval' : Eval C.to_platform_capability_set M1 e1
      (Ty.exi_val_denot (DenotCtx.platform_of N) E).as_mpost := by
    simp only [HasExpDenotation.interp] at hdenot
    unfold Ty.exi_exp_denot at hdenot
    apply reduce_preserves_eval hdenot hred CapabilitySet.subset_refl
  -- Progressive: Eval implies progressive
  exact eval_implies_progressive heval'

end CaplessK
