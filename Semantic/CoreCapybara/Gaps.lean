import Semantic.CoreCapybara.Fundamental

/-! # Definition-level counterexamples for the irreducible proof gaps

Every remaining `sorry` of the development is not merely unproven but
*unprovable as stated*: this file constructs explicit, concrete instances —
contexts, environments, and memories — refuting the exact statement each
`sorry` stands for.

## The semantic model (killed-binding form)

Deadness is a *lifecycle state of a binding*: `Authority` has a third tag
`.killed`, the `letin`/`unpack` rules type their continuations in a context
where the consumed peaks of the scrutinee's budget are retagged via
`Ctx.kill_peaks`, and elimination rules guard uses with `accessible`. The one
environment-separation invariant is `TypeEnv.EnvSepWf`: every pair of
distinct `can_drop` capture variables has disjoint capabilities. It is
memory-independent and budget-independent; closure denotations carry *no*
separation premise (closure creation bakes the invariant in), and killing
only removes demanded pairs. This dissolved the former dead-set gaps
(capture-instantiation peak transport, dead-set supply at eliminations) AND
the former subsumption-peak-slack gaps: stored peak sets are denotationally
inert in this model (denotations read the environment only through
`lookup_var.1`/`lookup_tvar`/`lookup_cvar`), so the `Retype` transport needs
no per-variable peak correspondence and `sem_typ_app`/`sem_subtyp_arrow` are
fully proven. The former drop-authority-laundering gap is closed statically:
the `unpack` rule carries the side condition
`((C1.peakset Γ).consumed).droppable Γ` (consumed peaks must be droppable),
which every leaf-generated budget satisfies and which rules out
`sc_elem`-widening a sequenced budget with `drop·c` atoms over `access_only`
variables.

## The remaining gap

1. **Lock-stored separation facts** (`fundamental_sepcheck_global`): lock
   facts are consumed at arbitrary later program points — in particular
   inside `modal_modal` subtyping transports, where no `EnvSepWf` invariant
   is available (`SemSubtyp` cannot carry one: the `exi` rule transports
   under a `can_drop` binder with an arbitrary, possibly aliasing, pack
   witness) — and `EnvTyping` admits aliased droppable capture variables
   (`sepcheck_global_droppable_false`). -/

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

/-- A well-typed environment may alias two droppable capture variables:
`EnvTyping` records no cross-variable disjointness, so the environment
separation invariant `EnvSepWf` is *not* a consequence of `EnvTyping` — it
must be threaded as an invariant (which is exactly what `SemanticTyping`
does). -/
theorem env2_not_envsepwf : ¬ env2.EnvSepWf := by
  intro h
  exact cap0_not_disjoint_self
    (h (.there .here) .here (by intro heq; cases heq) rfl rfl)

/-! ## The gap: lock-stored `sep_droppable` facts

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
