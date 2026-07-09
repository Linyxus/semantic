# Semantic Type Soundness of CoreCapybara

This repository contains the Lean 4 mechanization of the metatheory of
**System CoreCapybara**, the core calculus of the paper *System Capybara:
Tracking Capabilities for Separation and Freshness*. The development proves
semantic type soundness via a step-indexed Kripke logical relation over a
higher-order store: the fundamental theorem yields type safety, memory
safety, immutability, and data-race freedom.

## Building

You need the Lean toolchain to build this mechanization.

``` sh
lake exe cache get
lake build
```

The toolchain is pinned by `lean-toolchain`; the only dependency is Mathlib.

## Correspondence with the paper

### Main theorems

| Paper result | Lean declaration | File |
| --- | --- | --- |
| Fundamental Theorem | `fundamental` | [Fundamental.lean](Semantic/CoreCapybara/Fundamental.lean) |
| Type Soundness | `adequacy_platform_reduce_typed` | [SafetyReduce.lean](Semantic/CoreCapybara/SafetyReduce.lean) |
| Immutability (main text) | `immutability_adequacy_platform_reduce_typed` | [SafetyReduce.lean](Semantic/CoreCapybara/SafetyReduce.lean) |
| Separation | `fundamental_sepcheck` | [Fundamental.lean](Semantic/CoreCapybara/Fundamental.lean) |
| Standardization | `standardization` | [Semantics/Standardization.lean](Semantic/CoreCapybara/Semantics/Standardization.lean) |
| Confluence | `confluence` | [Semantics/Confluence.lean](Semantic/CoreCapybara/Semantics/Confluence.lean) |

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
