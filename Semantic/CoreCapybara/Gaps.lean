import Semantic.CoreCapybara.Fundamental

/-! # Definition-level counterexamples for the irreducible proof gaps

The development has exactly two `sorry`s left, and each is not merely
unproven but *unprovable*: this file constructs explicit, concrete instances
— contexts, environments, and memories — refuting the exact statement each
`sorry` stands for.

## The closed gaps (for the record)

The subcapture laundering family is gone. `sep_sc` and `seq_sc` carry a
`CaptureSet.EquivP` premise (the shrunken and original budgets' peaks
mutually cover each other, via the mutability-aware `CaptureSet.CoveredBy`),
so separation/sequencing evidence can no longer be moved to a budget whose
peaks hide its droppable anchors: the environment-separation invariant
`DropSepIn` transports across both rules (`CoveredBy.cvar_subset` for
arbitrary atoms, `CoveredBy.cvar_drop_subset` for the mode-exact `.drop`
case), and `fundamental_sepcheck`, `captureSet_seqcomp_denot`, and
`SeqComp.cross_droppable` are fully proven. Likewise
`TypeEnv.DropSepIn.of_subcapt` is proven thanks to the `.access_only`
restriction of `sc_cvar` (droppable peaks are monotone along `Subcapt`).

## The remaining gaps

Both remaining gaps are about the *absence* of any separation invariant at a
program point, not about transporting one:

1. Closure capture (`TypeEnv.DropSepIn.of_envtyping`): the closure-forming
   rules have use-set `{}`, so the creation site receives no invariant about
   the *captured* set, yet the closure body's semantic typing demands one.
   `EnvTyping` records only per-binding facts and admits environments that
   alias two droppable capture variables.
2. Lock-stored `sep_droppable` facts (`fundamental_sepcheck_global`): lock
   facts are consumed at arbitrary later program points (`unwrap`,
   `modal_modal` subtyping) with no budget in scope to relativize an
   invariant to, and `EnvTyping` admits the same aliased environments.

Both counterexamples share one tiny world: a memory `mem1` holding a single
capability cell at location `0`, and an environment binding two droppable
capture variables to the *same* capability `{ε·0}`. Such aliased environments
are well-typed (`EnvTyping` records only per-binding facts), which is the
root of both gaps. What a solution must provide, WITHOUT restricting the type
system: a semantic device carrying cross-variable separation facts to
budget-less program points — e.g. a substitution-stable separation premise
inside the closure/lock cases of `val_denot` (the obstacle: `Retype`/
`openCVar` transport erases capture-variable identity and authority), or an
`EnvTyping`-level invariant compatible with `pack`/`unpack` aliasing (the
obstacle: a global pairwise-disjointness invariant is false — an unpacked
witness may alias its consumed source, which is still bound in the
environment).
-/

namespace CoreCapybara.Gaps

open CoreCapybara

/-! ## The shared world -/

/-- A memory holding a single (basic) capability cell at location `0`. -/
def mem1 : Memory := Memory.extend_cap Memory.empty 0 rfl

/-- The ground capture set `{ε·0}`. -/
def cs0 : CaptureSet {} := .var (.M .epsilon) (.free 0)

/-- The capability `ε·0`. -/
def cap0 : CapabilitySet := .cap (.access .epsilon) 0

theorem cs0_ground : cs0.ground_denot mem1 = cap0 := rfl

theorem cap0_drop_free : cap0.drop_free := by
  intro l h
  cases h

theorem cap0_not_disjoint_self : ¬ CapabilitySet.disjoint cap0 cap0 := by
  intro h
  exact h (.access .epsilon) (.access .epsilon) 0 .here .here

theorem noninterference_cap0_self_false :
    ¬ CapabilitySet.Noninterference cap0 cap0 := by
  intro h
  have key : ∀ (A B : CapabilitySet), CapabilitySet.Noninterference A B →
      A = cap0 → B = cap0 → False := by
    intro A B h
    induction h with
    | ni_symm _ ih => intro h1 h2; exact ih h2 h1
    | ni_empty => intro h1 _; cases h1
    | ni_union _ _ _ _ => intro h1 _; cases h1
    | ni_ro => intro h1 _; cases h1
    | ni_disj hne =>
      intro h1 h2
      cases h1; cases h2
      exact hne rfl
  exact key cap0 cap0 h rfl rfl

/-- The aliased two-droppable context: `∅,C[.can_drop]<:⊤,C[.can_drop]<:⊤`. -/
def Γ2 : Ctx ({},C,C) :=
  ((Ctx.empty).push_cvar .can_drop .unbound).push_cvar .can_drop .unbound

/-- An environment binding *both* droppable capture variables of `Γ2` to the
same capability `cap0`. -/
def env2 : TypeEnv ({},C,C) :=
  ((TypeEnv.empty).extend_cvar cs0 cap0 .can_drop).extend_cvar cs0 cap0 .can_drop

theorem envtyping2 : EnvTyping Γ2 env2 mem1 := by
  refine ⟨?_, ?_, ?_, rfl, ?_, rfl, ?_, ?_, ?_, rfl, ?_, rfl, trivial⟩
  · exact .wf_var_free (val := .capability .basic) rfl
  · exact .wf_unbound
  · exact .top
  · exact cap0_drop_free
  · exact .wf_var_free (val := .capability .basic) rfl
  · exact .wf_unbound
  · exact .top
  · exact cap0_drop_free

/-- The budget peaking both droppable capture variables of `Γ2`. -/
def Cb2 : CaptureSet ({},C,C) :=
  (.cvar (.M .epsilon) (.there .here)) ∪ (.cvar (.M .epsilon) .here)

theorem env2_not_dropsep : ¬ env2.DropSepIn Cb2 := by
  intro h
  exact cap0_not_disjoint_self
    (h (.there .here) .here (.M .epsilon) (.M .epsilon)
      (by intro heq; cases heq) rfl rfl
      (.union_right_left .refl) (.union_right_right .refl))

/-! ## Gap 1: `EnvTyping` does not imply the separation invariant

This refutes the obligation at the closure-forming rules
(`sem_typ_abs`/`tabs`/`cabs`/`wrap`, via `TypeEnv.DropSepIn.of_envtyping`):
their use-set is `{}`, so the only source for the body's `DropSepIn` would be
`EnvTyping` itself — but well-typed environments may alias droppable capture
variables. -/

theorem envtyping_dropsep_false :
    ¬ (∀ {s : Sig} {Γ : Ctx s} {env : TypeEnv s} {m : Memory} (C : CaptureSet s),
        EnvTyping Γ env m → env.DropSepIn C) := by
  intro h
  exact env2_not_dropsep (h Cb2 envtyping2)

/-! ## Gap 2: lock-stored `sep_droppable` facts

This refutes the `sep_droppable` case of `fundamental_sepcheck_global` (the
interpretation of lock-stored `SepCheck` facts, which must hold with no
separation invariant available): two distinct droppable capture variables may
denote overlapping — here, equal — capabilities. -/

theorem sepcheck_global_droppable_false :
    ¬ (∀ {s : Sig} {Γ : Ctx s} {c1 c2 : BVar s .cvar} {m1 m2 : Access},
        Γ.TwoDistinctDroppable c1 c2 →
        Γ.IsClosed →
        ∀ env H, EnvTyping Γ env H →
          CapabilitySet.Noninterference
            ((CaptureSet.cvar m1 c1).denot env H)
            ((CaptureSet.cvar m2 c2).denot env H)) := by
  intro h
  have hni := h (Γ := Γ2) (c1 := .there .here) (c2 := .here)
    (m1 := .M .epsilon) (m2 := .M .epsilon)
    ⟨rfl, rfl, by intro heq; cases heq⟩
    (.push (.push .empty (.cvar .unbound)) (.cvar .unbound))
    env2 mem1 envtyping2
  exact noninterference_cap0_self_false hni

end CoreCapybara.Gaps
