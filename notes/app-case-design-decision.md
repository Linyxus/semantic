# App-case design decision: the two unprovable separation obligations

> **RESOLVED 2026-07-03** — superseded by `roadmaps/translation.md`.
> Ruling: Gap 1 closed by source-side well-formedness (`DropWf`: drop-moded
> atoms require droppable peaks — rejects zero terms, only phantom
> ascriptions); Gap 2 closed by footprint-granular resolution-free lock
> manufacture (whole-set entries, term vars symbolic — the target's
> `SepCtx`/`sep_mono`/`sep_union` already support consumption at this
> granularity). Target stays intact. Neither option table below was chosen
> as-is; the analysis remains useful history.

*2026-07-03. Status: awaiting a decision. Everything below is machine-verified
against the tree unless marked otherwise.*

## Where things stand

The app case of `CapyHasType.compile` (Preservation.lean) is almost fully
wired. After the current wiring pass finishes, everything reduces to **two
proof obligations that are not provable in the current system** — not for
lack of lemmas, but because the target type system genuinely cannot derive
them. Each is isolated behind a single named, documented `sorry`:

1. **The drop-separation gap** — pinned as `app_capture_self_sep_modepoly`
   (CompileSubstOpenVar.lean:963). Feeds the argument-fit subtyping.
2. **The narrowing self-separation gap** — the `hself` hypothesis of
   `compile_arrowLock_narrow` (CompileNarrow.lean). Blocks the codomain
   bridge's narrowing step (the `hLG` sorry in Preservation).

Both come from **one root fact about the target system**: two *distinct*
capture variables with `access_only` authority are allowed to alias
(read-sharing is deliberately legal — that is what the `sep_ro` rule is
for; the environment invariant `EnvSepWf` guarantees disjointness only for
`can_drop` variables). So "these are two different variables" never implies
"these are separate" in the target, while the *source* rule `sep_distinct`
hands out exactly that implication at every access mode. Since there is no
independent source semantics in this repo (verified: the compilation *is*
the soundness story), the source rule's generosity is exactly what the
compilation must pay for — and at these two spots it can't.

## Gap 1: drop-separation (the pinned lemma at CompileSubstOpenVar.lean:963)

**When it fires.** Apply a function whose *declared domain type* contains a
nested `drop`-mode latent of its capture parameter, e.g.

```
T1 = (z : Unit) →{} ([·] →{drop c} Unit)
```

to a capture argument with two distinct access-only atoms, `D = {ε c1} ∪ {ε c2}`.
The compiled subtyping must then prove `⟦c1⟧` and `⟦c2⟧` separate **at drop
mode**. Droppability can't pay (D is access-only); the ambient covering
can't pay (it only carries ε-mode uses, and the covering pipeline is
mode-preserving — it transports separations, never strengthens their mode).

**Why it's worse than "hard".** Such drop-latents can be *phantoms*: a
function that never drops anything can be upcast into the drop-latent type
by subsumption (`{} <: {drop w}`). The source program is then perfectly
sound — yet the demanded target fact is **false** in the target's semantic
model whenever `c1, c2` alias. So no sound in-system device can close this
case; any fix either changes the system or rejects the program.

**Options.**

| Option | What it is | Verdict |
|---|---|---|
| **B — droppability premise** | Add to the source app rule: "if the callee's latent may drop its capture parameter, the argument must be droppable." Reuses the existing (green) droppability route verbatim. | Sound, **small**. But it *rejects* the phantom programs, which are semantically sound — a type-system restriction. |
| **C — latent-composed captures** (the option previously chosen, before these findings) | Make use-sets/locks record that applying a drop-latent function drop-uses the argument, so the covering carries drop-mode atoms. | Sound, but requires changing the source rule's capture accounting anyway, has a large blast radius (AppSatisfy/AppFinalCapture/AppChain), and **still rejects the phantom case** (compilation gets stuck instead of closing). Same power as B at strictly more cost. |
| **O1 — fix the denotation** | Make "drop-mode of an `access_only` variable" denote the **empty** capability set — arguably the *correct* denotation, since such a variable can never be dropped (the target `drop` requires droppability). Then the demanded separations become vacuously true; a small new rule (`sep_drop_accessOnly`) makes them derivable. Closes everything, **rejects nothing**. | Semantically right, **architecturally blocked as a local change**: the denotation provably ignores authority (`from_TypeEnv_extend_cvar_cap_irrelevant`, Denotation/Core.lean:250, is a theorem), so this means abandoning the `denot = subst ∘ ground_denot` factoring and re-proving the semantic core (~300+ use sites, the whole Fundamental). Weeks-scale, high risk. |
| **Pin** | Keep the one documented `sorry`. | Honest; the compiled programs are safe, the proof just can't certify this corner. |

(An earlier idea — a target rule "distinct compiled variables are separate"
— is **refuted**: distinct access-only variables really can alias; such a
rule would be unsound. Likewise "filter drop atoms out of locks" is refuted:
the fresh case's green proof consumes exactly those drop-mode grants.)

## Gap 2: narrowing self-separation (`hself` in CompileNarrow.lean)

**When it fires.** The codomain bridge must relate the codomain compiled
with the parameter at its *declared* type `T1` versus at the argument's
*actual* type `T0y` (with `T0y <: T1[D]`). Locks inside a compiled type
resolve the parameter through its stored type's top-level capture set, so
the `T1`-side locks mention **surplus** resources the `T0y` side lacks.
Most surplus separations are paid by the ambient covering. One pair is not:
**a nested function's own (fresh, future-quantified) argument variable
versus a surplus resource**. Fresh bound variable — the covering can't
speak for it; the smaller lock doesn't contain the surplus; there is no
pushed lock to read the pair from in this direction (`modal_modal` pushes
the right-hand lock and satisfies the left-hand one — verified at
TypeSystem/Core.lean:175-181).

This gap is at ordinary ε/ro modes and is **provably independent of Gap 1**
(drop never enters parameter resolution: `peaksVarBound` resolves only the
top-level capture set, Context.lean:224-225).

**Options.**

| Option | What it is | Verdict |
|---|---|---|
| **O3 — intensional locks** | Stop resolving the parameter through its stored type when *building lock footprints* (a new `lockPeaks` used only by `peakSepCtx`; the ordinary `peaks` must stay — it is load-bearing for the source system). Then the `T1`-side and `T0y`-side locks become syntactically identical and the entire surplus problem — including `hself` — dissolves. | The only known full closer. Large: ~15 files of lock-stack reproof, including reworking `app_satisfy_bridge` and the `appPeaks` inventory. |
| **Surgical O3** | Opacity only in *codomain-body* locks, keeping the wrap-lock's parameter entry that existing proofs need. | Plausibly much cheaper. **Unverified** — risk that it just displaces the gap into the body's own covering. One focused probe would settle it. |
| **Pin** | Keep `hself` as a documented hypothesis/sorry. | Honest; true for real programs, uncertifiable in-system. |

## The decision (two independent choices)

Because the gaps are orthogonal, pick one per row:

- **Gap 1 (drop):** B (small, restricts) · C (bigger B, restricts) · O1 (no restriction, weeks) · pin.
- **Gap 2 (narrowing):** O3 full (large) · surgical-O3 probe first · pin.

Cost-ordered combinations, as assessed:
1. **B + pin** — cheapest path to a mostly-green stack, two honest residuals
   (one closed by a premise that rejects phantom programs, one pinned).
2. **B + surgical O3** — fully green if the surgical probe pans out; still
   carries B's restriction.
3. **O1 + full O3** — the zero-pin, zero-restriction ideal; maximal effort
   (semantic-core rework + lock-stack rework).

Note: your standing rule ("never restrict the type system to make proofs
work") weighs against B and C, since the phantom programs they reject are
semantically sound. If that rule is absolute, the honest choices are
pins now (with O1/O3 as the eventual closers) or committing to the deep work.

## What is NOT blocked on this decision

- The argFit wiring (in progress — 4 premises from done) and the readonly
  replay: after them the app case is green **modulo the two pins above**
  plus the pre-existing accepted baselines (`app_use_covered`,
  `Coherent.srcAligned`).
- All banked lemmas (covering cores, peak inventory, narrowing node/heart)
  survive every option.
- The ~900-line narrowing recursion is on hold: under O3 it mostly
  dissolves, so building it first would be wasted under that choice.
