import Semantic.CC.Soundness
import Semantic.CC.Semantics.BigStep

/-!
# Capture Prediction Theorem

This file contains the capture prediction theorem for the CC system, which states
that if a well-typed term evaluates to a value, then the value's runtime
reachability is bounded by what the type's capture set predicts.

This is a key soundness property: types safely over-approximate the actual
runtime behavior of capture sets.
-/

namespace CC

/-- Capture Prediction Theorem (for simple values):
    If a well-typed term evaluates to a simple value, then the value's runtime
    reachability is bounded by what the capturing type predicts.

    More precisely: Given a well-typed term `C # Γ ⊢ e : T` and an environment
    `ρ` that gives meaning to the free variables in `e`, if the substituted term
    evaluates to a simple value `v` in memory `m'`, then the actual reachability
    computed for `v` is a subset of the capabilities predicted by expanding the
    capture set from the type (after substitution).

    Proof strategy:
    1. Use fundamental theorem to get semantic typing: C # Γ ⊨ e : T
    2. Instantiate semantic typing with the given environment ρ and memory m
    3. From semantic typing of existential type, extract the capturing type witness
    4. Use reachability safety of the denotation to bound actual captures
    5. Connect expand_captures with the denotational semantics
-/
theorem capture_prediction_simple_val
  {C : CaptureSet s}
  {Γ : Ctx s}
  {e : Exp s}
  {T : Ty .exi s}
  {ρ : TypeEnv s}
  {m m' : Memory}
  {v : Exp {}}
  {Q : Mpost}
  (htype : C # Γ ⊢ e : T)
  (henv : EnvTyping Γ ρ m)
  (heval : Eval CapabilitySet.any m (e.subst (Subst.from_TypeEnv ρ)) Q)
  (hpost : Q v m')
  (hval : v.IsSimpleVal) :
  ∃ (CS : CaptureSet s) (S : Ty .shape s),
    -- There exists a capturing type in T
    (∃ (T_capt : Ty .capt s),
      T = .typ T_capt ∧ T_capt = .capt CS S) ∧
    -- The actual reachability is bounded by the predicted captures
    compute_reachability m'.heap v hval ⊆
      expand_captures m'.heap (CS.subst (Subst.from_TypeEnv ρ)) := by
  -- Step 1: Apply fundamental theorem to get semantic typing
  have hsem : C # Γ ⊨ e : T := fundamental htype

  -- Step 2: Instantiate semantic typing with the given environment
  simp [SemanticTyping] at hsem
  have hsem_inst := hsem ρ m henv

  -- Step 4: Case analysis on the existential type T
  cases T with
  | exi T_inner =>
    -- T = .exi T_inner, need to extract witness from evaluation
    sorry -- TODO: Connect evaluation with denotational semantics
  | typ T_capt =>
    -- T = .typ T_capt, this is the simple case
    cases T_capt with
    | capt CS S =>
      -- We have T = .typ (.capt CS S)
      use CS, S
      constructor
      · use .capt CS S
      · -- Prove: compute_reachability m'.heap v hval ⊆ expand_captures m'.heap CS
        -- Strategy: Extract from semantic typing that v satisfies Ty.capt_val_denot,
        -- then use reachability safety
        sorry -- TODO: Need to connect heval + hpost with hsem_inst

/-- Capture Prediction Theorem (general version with existential types):
    If a well-typed term evaluates to any answer (value or pack), then the
    answer's runtime reachability is bounded by what the type predicts.

    This generalizes to existential types by opening the existential witness.
    Works for arbitrary typing contexts by substituting the environment.

    Proof strategy:
    1. Use fundamental theorem for semantic typing
    2. For existential types, the evaluation produces a pack with a witness capture set
    3. Show that the witness capture set bounds the reachability
    4. For simple values, use capture_prediction_simple_val
-/
theorem capture_prediction
  {C : CaptureSet s}
  {Γ : Ctx s}
  {e : Exp s}
  {T : Ty .exi s}
  {ρ : TypeEnv s}
  {m m' : Memory}
  {ans : Exp {}}
  {Q : Mpost}
  (htype : C # Γ ⊢ e : T)
  (henv : EnvTyping Γ ρ m)
  (heval : Eval CapabilitySet.any m (e.subst (Subst.from_TypeEnv ρ)) Q)
  (hpost : Q ans m') :
  -- The answer is either a simple value or a pack
  (∃ (v : Exp {}) (hval : v.IsSimpleVal),
    ans = v ∧
    ∃ (CS : CaptureSet s) (S : Ty .shape s),
      (∃ (T_capt : Ty .capt s),
        T = .typ T_capt ∧ T_capt = .capt CS S) ∧
      compute_reachability m'.heap v hval ⊆
        expand_captures m'.heap (CS.subst (Subst.from_TypeEnv ρ)))
  ∨
  (∃ (cs : CaptureSet {}) (x : Var .var {}),
    ans = .pack cs x ∧
    ∃ (T_inner : Ty .capt (s,C)),
      T = .exi T_inner ∧
      -- The witness capture set cs bounds what the packed value x captures
      (∀ (loc : Nat),
        x = .free loc →
        reachability_of_loc m'.heap loc ⊆ expand_captures m'.heap cs)) := by
  -- Apply fundamental theorem
  have hsem : C # Γ ⊨ e : T := fundamental htype

  -- Case analysis on whether ans is a simple value or a pack
  by_cases hans_val : ans.IsSimpleVal
  case pos =>
    -- ans is a simple value
    left
    use ans, hans_val
    constructor
    · rfl
    · -- Apply the simple value version
      sorry -- Use capture_prediction_simple_val or inline its proof
  case neg =>
    -- ans is not a simple value; check if it's a pack
    by_cases hans_pack : ans.IsPack
    case pos =>
      -- ans is a pack, which means ans = .pack cs x for some cs and x
      right
      -- Since IsPack only has one constructor, ans must be .pack cs x
      cases hans_pack
      -- The goal now knows ans = .pack _ _
      rename_i cs x
      use cs, x
      constructor
      · rfl
      · sorry -- TODO: Extract witness from existential type semantics
    case neg =>
      -- ans is neither a value nor a pack - contradiction with evaluation
      sorry -- TODO: Show that evaluation only produces answers

/-- Helper: resolve_reachability for simple values equals compute_reachability -/
theorem resolve_reachability_eq_compute_reachability
  {m : Memory}
  {v : Exp {}}
  (hval : v.IsSimpleVal) :
  resolve_reachability m.heap v = compute_reachability m.heap v hval :=
  -- This is already proven in Denotation/Core.lean:139
  (compute_reachability_eq_resolve_reachability m.heap v hval).symm

/-- Helper: Semantic typing implies reachability bounds for values.
    This connects the denotational semantics with the operational reachability.
    Works for arbitrary typing contexts via environment substitution. -/
theorem sem_typing_implies_reachability_bound
  {CS : CaptureSet s}
  {S : Ty .shape s}
  {ρ : TypeEnv s}
  {m : Memory}
  {v : Exp {}}
  (hval : v.IsSimpleVal)
  (henv : EnvTyping Γ ρ m)
  (hsem : Ty.capt_val_denot ρ (.capt CS S) m v) :
  compute_reachability m.heap v hval ⊆
    expand_captures m.heap (CS.subst (Subst.from_TypeEnv ρ)) := by
  -- Unfold the semantic typing for capturing types
  simp [Ty.capt_val_denot] at hsem
  obtain ⟨_, _, _, hshape⟩ := hsem

  -- Extract reachability safety from shape denotation
  have henv_safe : TypeEnv.is_reachability_safe ρ :=
    typed_env_is_reachability_safe henv

  have hsafe := shape_val_denot_is_reachability_safe henv_safe S
  have hreach := hsafe (CS.denot ρ m) m v hshape

  -- resolve_reachability v = compute_reachability v for simple values
  rw [resolve_reachability_eq_compute_reachability hval] at hreach

  -- CS.denot ρ m = expand_captures m.heap (CS.subst (Subst.from_TypeEnv ρ))
  have hdenot_eq : CS.denot ρ m = expand_captures m.heap (CS.subst (Subst.from_TypeEnv ρ)) := by
    simp [CaptureSet.denot]
    exact (expand_captures_eq_ground_denot (CS.subst (Subst.from_TypeEnv ρ)) m).symm

  rw [← hdenot_eq]
  exact hreach

end CC
