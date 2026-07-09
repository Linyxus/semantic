import Semantic.CoreCapybara.Safety
import Semantic.CoreCapybara.Semantics.Confluence

/-! # Adequacy under the genuine interleaving schedule

  `Safety.lean` establishes progress and immutability along the *sequential* schedule
  `SeqReduce`.  This file lifts both to the *genuine interleaving* relation `Reduce`
  (built from the interleaving small-step `Step`), closing the gap the old deferral
  comment described.  The bridge is `confluence` (for progress) and `standardization`
  (for immutability): a partial `Reduce` run is joined against a sequential run obtained
  from the semantic typing, and answers are `Step`-normal, so the interleaved state is
  itself progressive. -/

namespace CoreCapybara

/-- A closed platform program stays well-formed after the platform substitution.
    `from_TypeEnv_wf_in_heap` at the platform `EnvTyping` (`env_typing_of_platform`)
    shows the substitution maps every context variable to a live platform cell; source
    closedness then transports through `Exp.wf_subst`.  This is the `WfInHeap` premise
    that `confluence`/`standardization` require at the platform configuration. -/
theorem platform_subst_wfInHeap {N : Nat} {e : Exp (Sig.platform_of N)}
    (hclosed : e.IsClosed) :
    Exp.WfInHeap (e.subst (Subst.from_TypeEnv (TypeEnv.platform_of N)))
      (Memory.platform_of N).heap :=
  Exp.wf_subst (Exp.wf_of_closed hclosed)
    (from_TypeEnv_wf_in_heap (env_typing_of_platform (k := 0)))

/-- The platform context is closed (no heap pointers): each layer binds a capture
    variable at bound `⊤` and a term variable at a `.cell` type over a bound capture
    variable, all syntactically closed. -/
theorem platform_ctx_isClosed (N : Nat) : (Ctx.platform_of N).IsClosed := by
  induction N with
  | zero => exact Ctx.IsClosed.empty
  | succ n ih =>
    refine Ctx.IsClosed.push (Ctx.IsClosed.push ih ?_) ?_
    · exact Binding.IsClosed.cvar CaptureBound.IsClosed.unbound
    · exact Binding.IsClosed.var
        (Ty.IsClosed.cell CaptureSet.IsClosed.cvar Ty.IsClosed.bool)

/-- Progressiveness under the interleaving small-step `Step`: a configuration is either an
    answer, or able to take another `Step`.  The interleaving analogue of the sequential
    `IsProgressive` (over `SeqStep`, Props.lean). -/
inductive IsProgressiveStep : Memory -> Exp {} -> Prop where
  | done : e.IsAns -> IsProgressiveStep m e
  | step : Step t m e m' e' -> IsProgressiveStep m e

/-- An expression `e` is safe with a platform of `N` mutable cells under the *genuine
    interleaving* schedule `Reduce` iff every reachable state is progressive: an answer,
    or able to take another interleaving `Step`. -/
def Exp.SafeWithPlatformReduce (e : Exp {}) (N : Nat) : Prop :=
  ∀ t M1 e1,
    Reduce t (Memory.platform_of N) e M1 e1 ->
    IsProgressiveStep M1 e1

/-- **Adequacy under the genuine interleaving schedule.**  A semantically well-typed,
    source-closed platform program is progressive at every interleaving-reachable state.

    Proof: from a partial run `R : Reduce t1 m e' m1 e1`, instantiate semantic typing at
    `k₁ = t1.readCount + 1` and read a sequential run `S` off the `Eval` (either an answer
    within budget, or a run consuming `≥ k₁` reads).  Re-instantiate the `PrefixSafe`
    companion at `k₂ = S.readCount + 1` to realize `S` as a guarded run and lift it to
    `Reduce`.  `confluence` joins `R` and lifted-`S`; case on `e1`'s joining leg:
    nonempty ⇒ `e1` steps; empty ⇒ either `e1` is (a renaming of) the answer, or — in the
    exhausted case — the threaded readCount equality is contradictory. -/
theorem adequacy_platform_reduce {N : Nat} {e : Exp (Sig.platform_of N)}
    {C : CaptureSet (Sig.platform_of N)} {E : Ty .exi (Sig.platform_of N)}
    (ht : SemanticTyping C (Ctx.platform_of N) e E)
    (hclosed : e.IsClosed) :
    (e.subst (Subst.from_TypeEnv (TypeEnv.platform_of N))).SafeWithPlatformReduce N := by
  intro t M1 e1 hred
  -- Instantiate the semantic typing at read budget `k₁ = t.readCount + 1`.
  have hdenot := ht (TypeEnv.platform_of N) (t.readCount + 1)
    (platformWorld N (t.readCount + 1)) (Memory.platform_of N)
    env_typing_of_platform platform_env_sep_wf (platform_is_compatible _)
  unfold Ty.exi_exp_denot at hdenot
  have heval := hdenot (memtyped_platform N (t.readCount + 1))
  -- Read a sequential run `S` off the `Eval`: an answer within budget, or `≥ k₁` reads.
  obtain ⟨tS, mS, a, hSeq, hcase⟩ := eval_reduce_exists_answer heval.1
  -- Re-instantiate the `PrefixSafe` companion at `k₂ = tS.readCount + 1` and realize `S`
  -- as a guarded run, then lift it to `Reduce`.
  have hdenot2 := ht (TypeEnv.platform_of N) (tS.readCount + 1)
    (platformWorld N (tS.readCount + 1)) (Memory.platform_of N)
    env_typing_of_platform platform_env_sep_wf (platform_is_compatible _)
  unfold Ty.exi_exp_denot at hdenot2
  have heval2 := hdenot2 (memtyped_platform N (tS.readCount + 1))
  have hReduceS : Reduce tS (Memory.platform_of N)
      (e.subst (Subst.from_TypeEnv (TypeEnv.platform_of N))) mS a :=
    (heval2.2 hSeq (Nat.lt_succ_self _)).2.toReduce
  -- Join the given partial run against the lifted sequential run.
  obtain ⟨s1, s2, mf1, mf2, ef1, ef2, π, hleg1, hleg2, hmeq, haeq, htreq, hrc⟩ :=
    confluence (platform_subst_wfInHeap hclosed) hred hReduceS
  cases hleg1 with
  | step hstep _ =>
    -- `e1`'s leg is nonempty, so `e1` takes an interleaving step.
    exact IsProgressiveStep.step hstep
  | refl =>
    -- `e1`'s leg is empty (`e1 = ef1`, `M1 = mf1`).
    rcases hcase with ⟨hans_a, _, _⟩ | hexh
    · -- Answer case: the answer-side leg is empty too, so `e1` is a renaming of the answer.
      obtain ⟨_, hef2⟩ := reduce_ans_eq hans_a hleg2
      subst hef2
      exact IsProgressiveStep.done
        (Exp.IsAns.renameLoc_iff.mp ((Exp.AEq.isAns_iff haeq).mp hans_a))
    · -- Exhausted case: an empty `e1`-leg contradicts the threaded readCount equality.
      exfalso
      simp only [List.append_nil, Trace.readCount_append] at hrc
      omega

/-- **Immutability under the genuine interleaving schedule.**  A read-only
    program that reduces (via the interleaving `Reduce`, to an answer) leaves the platform
    memory unmutated.  `standardization` converts the interleaving run to a sequential run
    with the same endpoints, discharging the sequential `immutability_adequacy_platform_run`. -/
theorem immutability_adequacy_platform_reduce {N : Nat} {e : Exp (Sig.platform_of N)}
    {C : CaptureSet (Sig.platform_of N)} {E : Ty .exi (Sig.platform_of N)}
    (ht : SemanticTyping C (Ctx.platform_of N) e E)
    (hkind : HasKind (Ctx.platform_of N) C .ro)
    (hclosed : e.IsClosed) :
    ∀ t M2 a,
      Reduce t (Memory.platform_of N)
        (e.subst (Subst.from_TypeEnv (TypeEnv.platform_of N))) M2 a ->
      a.IsAns ->
      (Memory.platform_of N).not_mutated M2 := by
  intro t M2 a hred hans
  obtain ⟨t', hseq, _⟩ := standardization (platform_subst_wfInHeap hclosed) hred hans
  exact immutability_adequacy_platform_run ht hkind t' M2 a hseq hans

/-! ## Typed corollaries — interleaving safety with zero side conditions

  For a `HasType`-derived program both the `SemanticTyping` premise (via `fundamental`,
  discharging context closedness with `platform_ctx_isClosed`) and source closedness (via
  `HasType.exp_is_closed`) come for free, so a well-typed platform program is interleaving-safe
  and — when its budget is read-only — interleaving-immutable, with no extra
  hypotheses. -/

/-- **Interleaving adequacy for a typed program.**  Every `Reduce`-reachable state of a
    well-typed platform program is progressive. -/
theorem adequacy_platform_reduce_typed {N : Nat} {e : Exp (Sig.platform_of N)}
    {C : CaptureSet (Sig.platform_of N)} {E : Ty .exi (Sig.platform_of N)}
    (ht : HasType C (Ctx.platform_of N) e E) :
    (e.subst (Subst.from_TypeEnv (TypeEnv.platform_of N))).SafeWithPlatformReduce N :=
  adequacy_platform_reduce (fundamental (platform_ctx_isClosed N) ht)
    (HasType.exp_is_closed ht)

/-- **Interleaving immutability for a typed program.**  A well-typed platform program with a
    read-only budget that reduces to an answer under the interleaving schedule
    leaves the platform memory unmutated. -/
theorem immutability_adequacy_platform_reduce_typed {N : Nat} {e : Exp (Sig.platform_of N)}
    {C : CaptureSet (Sig.platform_of N)} {E : Ty .exi (Sig.platform_of N)}
    (ht : HasType C (Ctx.platform_of N) e E)
    (hkind : HasKind (Ctx.platform_of N) C .ro) :
    ∀ t M2 a,
      Reduce t (Memory.platform_of N)
        (e.subst (Subst.from_TypeEnv (TypeEnv.platform_of N))) M2 a ->
      a.IsAns ->
      (Memory.platform_of N).not_mutated M2 :=
  immutability_adequacy_platform_reduce (fundamental (platform_ctx_isClosed N) ht)
    hkind (HasType.exp_is_closed ht)

end CoreCapybara
