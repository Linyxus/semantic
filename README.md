# Semantic Type Soundness of CoreCapybara

This repository contains the Lean 4 mechanization of the metatheory of
**System CoreCapybara**, the core calculus of the paper *System Capybara:
Tracking Capabilities for Separation and Freshness*. The development proves
semantic type soundness via a step-indexed Kripke logical relation over a
higher-order store: the fundamental theorem yields type safety, memory
safety, immutability, and data-race freedom.

All results are proved in full. The development contains no `sorry`, and
every headline theorem depends only on the standard axioms
`propext`, `Classical.choice`, and `Quot.sound`.

## Building

``` sh
lake exe cache get
lake build
```

The toolchain is pinned by `lean-toolchain`; the only dependency is Mathlib.

## Correspondence with the paper

The paper states its results twice: in the *Metatheory* section of the main
text, and in the metatheory appendix, "in the form in which they are
mechanized". The tables below map both to the Lean declarations, which the
paper designates as ground truth. All declarations live in the
`CoreCapybara` namespace.

### Main theorems

| Paper result | Lean declaration | File |
| --- | --- | --- |
| Fundamental Theorem | `fundamental` | [Fundamental.lean](Semantic/CoreCapybara/Fundamental.lean) |
| Type Soundness | `adequacy_platform_reduce_typed` | [SafetyReduce.lean](Semantic/CoreCapybara/SafetyReduce.lean) |
| Immutability (main text) | `immutability_adequacy_platform_reduce_typed` | [SafetyReduce.lean](Semantic/CoreCapybara/SafetyReduce.lean) |
| Separation | `fundamental_sepcheck` | [Fundamental.lean](Semantic/CoreCapybara/Fundamental.lean) |
| Standardization | `standardization` | [Semantics/Standardization.lean](Semantic/CoreCapybara/Semantics/Standardization.lean) |
| Confluence | `confluence` | [Semantics/Confluence.lean](Semantic/CoreCapybara/Semantics/Confluence.lean) |

- `fundamental` is the paper's statement verbatim: syntactic typing
  `HasType C Γ e E` implies semantic typing `SemanticTyping C Γ e E`
  (for a closed context).
- `adequacy_platform_reduce_typed` is Type Soundness as stated in the main
  text: a well-typed program, run on the platform (see below), reaches only
  progressive configurations — each is an answer or can step — under **any**
  schedule of the interleaving small-step relation `Reduce`. It is the
  composition of `fundamental` with the adequacy theorems below. The Memory
  Safety corollary carries no separate Lean declaration: the stuck
  configurations that adequacy excludes include every use-after-free and
  double-free, since a dead cell matches no reduction rule.
- `immutability_adequacy_platform_reduce_typed`: if the program's use set
  moreover has kind `ro` (`HasKind Γ C .ro`), any interleaved run to an
  answer leaves the initial memory unchanged in content and liveness
  (`Memory.not_mutated`).
- `fundamental_sepcheck`: syntactic separation `SepCheck Γ C1 C2` denotes
  non-interference of the two footprints in every realizing,
  separation-well-formed environment (`SemSepCheck`).
- `standardization`: a well-formed configuration's interleaved run to an
  answer is matched by a sequential run with the same endpoints, up to
  Mazurkiewicz trace equivalence (`Trace.Equiv`). No typing hypothesis.
- `confluence`: any two interleaved runs from a well-formed configuration
  join, with final memories equal up to a location permutation, final
  expressions equal up to the permutation and `Exp.AEq` (reachability
  equivalence of the order-sensitive `par` capture annotations — the
  discrepancy the paper's appendix notes), combined traces
  `Trace.Equiv`-related, and equal read counts. The Schedule Determinism
  corollary is the instance where both runs end in answers: answers are
  `Reduce`-normal, so the joining runs are empty.

### Appendix statements

The appendix states the adequacy chain in its mechanized granularity:

| Paper result | Lean declaration | File |
| --- | --- | --- |
| Subcapturing lemma | `fundamental_subcapt` | [Fundamental.lean](Semantic/CoreCapybara/Fundamental.lean) |
| Separation lemma | `fundamental_sepcheck` | [Fundamental.lean](Semantic/CoreCapybara/Fundamental.lean) |
| Kinding lemma (read-only covers no write) | `fundamental_haskind` | [Fundamental.lean](Semantic/CoreCapybara/Fundamental.lean) |
| Sequential adequacy | `adequacy_platform` | [Safety.lean](Semantic/CoreCapybara/Safety.lean) |
| Adequacy (any schedule) | `adequacy_platform_reduce` | [SafetyReduce.lean](Semantic/CoreCapybara/SafetyReduce.lean) |
| Immutability (semantic premise) | `immutability_adequacy_platform_reduce` | [SafetyReduce.lean](Semantic/CoreCapybara/SafetyReduce.lean) |

The adequacy theorems take a `SemanticTyping` premise and run the program on
the *platform* of `N` pre-allocated boolean cells: `Ctx.platform_of N` binds,
per cell, a capture variable and a term variable of boolean reference type
(`.cell … .bool`), `Memory.platform_of N` allocates the live cells, and
`TypeEnv.platform_of N` maps each variable to its cell
(all in [Safety.lean](Semantic/CoreCapybara/Safety.lean)). `adequacy_platform`
covers sequential runs directly from the model; `adequacy_platform_reduce`
lifts it to arbitrary interleavings by joining, via `confluence`, a partial
interleaved run against the maximal sequential run the model provides. The
`*_typed` corollaries in
[SafetyReduce.lean](Semantic/CoreCapybara/SafetyReduce.lean) discharge the
semantic premises with `fundamental`, giving the zero-side-condition
statements of the main text.

### The model

The logical relation of the paper's metatheory appendix corresponds to the
following definitions, all in
[Denotation/Core.lean](Semantic/CoreCapybara/Denotation/Core.lean) unless
noted otherwise:

| Paper notion | Lean definition |
| --- | --- |
| Footprint of a ground capture set | `CaptureSet.ground_denot` |
| Worlds `(Σ, H)`; stored relations `Rel_k`; truncation | `StoreTyping k` / `MonRel k` / `.trunc`, from the world-parametrized store in [Denotation/StepIndexedWorldParam.lean](Semantic/CoreCapybara/Denotation/StepIndexedWorldParam.lean) |
| World extension | `WorldLe` |
| Well-typed world | `MemTyped` |
| Value denotation of types | `Ty.val_denot` (capturing types), `Ty.exi_val_denot` (existentials) |
| Expression denotation | `Ty.exp_denot`, `Ty.exi_exp_denot` |
| Safety clause (budget-indexed progress; rely–guarantee at `par`) | `Safe`, packaged with the postcondition by `Eval`, in [Semantics/BigStep.lean](Semantic/CoreCapybara/Semantics/BigStep.lean) |
| Prefix safety | `PrefixSafe`, in [Semantics/PrefixTrace.lean](Semantic/CoreCapybara/Semantics/PrefixTrace.lean) |
| Trace authorization | `TraceOk`, in [Semantics/Heap.lean](Semantic/CoreCapybara/Semantics/Heap.lean) |
| Environment realization of a context | `EnvTyping` |
| Separation-well-formedness of the environment | `TypeEnv.EnvSepWf` |
| Semantic typing | `SemanticTyping` |
| Semantic subcapturing / separation / kinding | `SemSubcapt` / `SemSepCheck` / `SemHasKind` |
| Trace equivalence (Mazurkiewicz) | `Trace.Equiv`, in [Semantics/Standardization.lean](Semantic/CoreCapybara/Semantics/Standardization.lean) |

## Repository layout

The calculus itself (syntax, type system, operational semantics) is as in
the paper's CoreCapybara appendix:

- [Syntax/](Semantic/CoreCapybara/Syntax) — expressions (`Exp`), types
  (`Ty`), capture sets (`CaptureSet`), typing contexts (`Ctx`), and the
  separation/mutability contexts of modal types (`SepCtx`, `ModalCtx`);
  [Debruijn.lean](Semantic/CoreCapybara/Debruijn.lean) and
  [Substitution.lean](Semantic/CoreCapybara/Substitution.lean) provide the
  de Bruijn infrastructure.
- [TypeSystem/](Semantic/CoreCapybara/TypeSystem) — the judgments: typing
  (`HasType`), subtyping (`Subtyp`), subcapturing (`Subcapt`), separation
  (`SepCheck`), kinding (`HasKind`), lock satisfaction (`Satisfy`), and
  sequential composition (`SeqComp`), with basic metatheory
  ([BasicProps.lean](Semantic/CoreCapybara/TypeSystem/BasicProps.lean),
  [KillWeakening.lean](Semantic/CoreCapybara/TypeSystem/KillWeakening.lean)).
- [Semantics/](Semantic/CoreCapybara/Semantics) — memory and traces
  ([Heap.lean](Semantic/CoreCapybara/Semantics/Heap.lean)), the big-step
  relation `BigStep` used by the model
  ([BigStep.lean](Semantic/CoreCapybara/Semantics/BigStep.lean)), and the
  small-step relations
  ([SmallStep.lean](Semantic/CoreCapybara/Semantics/SmallStep.lean)):
  `Step`/`Reduce` is the guarded interleaving semantics, `SeqStep`/`SeqReduce`
  its left-first sequential schedule. The schedule theorems live in
  [Standardization.lean](Semantic/CoreCapybara/Semantics/Standardization.lean)
  and [Confluence.lean](Semantic/CoreCapybara/Semantics/Confluence.lean), on
  top of the location-renaming (nominal) layer
  [Equivariance.lean](Semantic/CoreCapybara/Semantics/Equivariance.lean).
- [Denotation/](Semantic/CoreCapybara/Denotation) — the step-indexed Kripke
  model described above, with the environment-manipulation devices
  ([Rebind.lean](Semantic/CoreCapybara/Denotation/Rebind.lean),
  [Retype.lean](Semantic/CoreCapybara/Denotation/Retype.lean),
  [Kill.lean](Semantic/CoreCapybara/Denotation/Kill.lean)).
- [Fundamental.lean](Semantic/CoreCapybara/Fundamental.lean) — one
  compatibility lemma per typing rule, the fundamental lemmas of the
  auxiliary judgments, and the fundamental theorem.
- [Safety.lean](Semantic/CoreCapybara/Safety.lean) /
  [SafetyReduce.lean](Semantic/CoreCapybara/SafetyReduce.lean) — the
  platform and the adequacy theorems, sequential and interleaved.

## Scope

The mechanization covers System CoreCapybara: its type system, semantics,
logical model, and the theorems listed above. The surface calculus
(System Capybara) and its type-preserving compilation into CoreCapybara are
developed on paper, in the paper's translation appendix; they are not part
of this repository.
