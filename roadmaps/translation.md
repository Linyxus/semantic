# Roadmap: Capybara → CoreCapybara translation — fresh-start edition

*Finalized 2026-07-04, rev. 2 (same day). **Fresh-start ruling (user)**: the
existing source module and its compilation are renamed to `Legacy*` and
frozen as reference; after the rebase, a NEW Capybara is designed and built
from scratch, from first principles, with every ruling of the 2026-07-03/04
discussions baked in from day one instead of retrofitted. Rev. 1's retrofit
phases (W/U/F/F2/F3/A/L) are superseded as *work plans* but their content
survives as design inputs — see the phase map. Adversarial-review archive:
`notes/roadmap-critique-2026-07-03.md`. Supersedes
`notes/app-case-design-decision.md`. File:line anchors were machine-verified
2026-07-03/04; anchors into the legacy module cite pre-rename paths (after
Phase R they live under `LegacyCapybara/`/`LegacyCompilation/`, checkable at
the reference tag).*

*Decision status: the entry-grouping device is **ruled** (compute once,
transport thereafter — P3). ONE design decision remains open — the
alignment device (P7, ex-srcAligned), now a Phase D design-time choice
rather than a retrofit; the fresh start makes the subcapture-shaped
coherence design (β) natural.*

## Phase map (rev. 1 → rev. 2)

| Rev. 1 (retrofit) | Rev. 2 (fresh start) |
|---|---|
| R — rebase | **R** — rebase + legacy quarantine (revised: no legacy repair) |
| W — DropWf retrofit | principle **P1**, designed in **D**, built in **S** |
| U — unified parameters retrofit | principle **P2**, designed in **D**, built in **S** |
| F — lock rebuild (incl. F.0) | principle **P3**, designed in **D**, built in **C** |
| F2 — contravariant domains | principle **P4**, designed in **D**, built in **S**/**C** |
| F3 — source sep_mono | principle **P5**, designed in **D**, built in **S**/**C** |
| L — surface consumers | principle **P6**, designed in **D**, built last in **S**/**C** |
| A — app-case endgame | **E** — endgame; legacy sorries become the **cliffs checklist** |

**Order: R → D → S → C → E.**

## The ruling

One constraint, two design changes (the intellectual core, unchanged from
rev. 1 — now founding principles of the new module rather than retrofits):

**Constraint — the target stays intact** (conservative extensions only,
each proven sound in the existing model; no new obligations imposed on
target clients). The translation's target delta today: **141 insertions in
3 files** — TypeSystem/Core.lean +25 (`SepCheck.sep_mono` plus four
`Subtyp` capture-covariance rules `cell`/`reader`/`cap`/`poly_cap`),
BasicProps.lean +9, Fundamental.lean +107 (the semantic cases for all five
additions, already proven in the old model). These live in CORE files, not
the legacy directories — they survive quarantine, are re-proven in Phase R,
and are load-bearing for the new design too (`sep_mono` pays footprint
consumption; the covariance rules receive source capture-covariance).
Phase D re-validates the exact set; it stays at this scale. Rationale: the
target's green semantic stack is the fixed ground truth; "the
(conservatively extended) core hosts the surface calculus" is strictly
stronger than a result where the core was bent to receive it.

**Change 1 (→ P1) — `DropWf`: drop-qualified captures must be
exercisable.** A `.drop`-moded atom is well-formed only when its peaks have
`can_drop` authority. Kills the phantom drop-separation obligation (legacy
963 pin) at the *formation* level. Evidence this is the right frame
(verified in the legacy system; the new design inherits the argument):
- The invariant already holds for terms and use-sets: `drop` requires
  `droppable` (legacy Capybara/TypeSystem/Core.lean:399), `fresh` requires
  `droppable Γ D` (:252), `letin_unpack` binds its witness `C[.can_drop]`
  (:377). The **only** leak is types-via-subsumption: `subtyp` (:429)
  checks only `IsClosed`, and `sc_elem`'s `{} ⊑ {drop c}` flows into
  nested arrow latents through covariant cs-widening, below the reach of
  top-level `AccessOnly` premises.
- Arrow binders are access-only and `capp` instantiation is
  access-only-valid, so **no term can exercise a drop-latent over a
  parameter** — every such latent is a phantom. `DropWf` rejects *zero
  terms*, only self-contradictory ascriptions. Consistent with the
  no-restriction rule.

**Change 2 (→ P3) — footprint-granular, resolution-free locks.** Lock
manufacture stops atomizing and stops resolving through stored types:
entries are whole footprints as written (term-var atoms stay symbolic
`{x}`; cvar atoms already are symbols), and the entry *grouping* is
computed once at the introduction context and transported thereafter
(the ruled device, below). Declared-side and actual-side locks are then
syntactically identical under narrowing — the legacy hLG/hself problem is
unstatable — and the manufactured within-footprint obligations (the demand
side of the 963 gap) never exist. Evidence the target already consumes at
this granularity (verified; **unchanged on core-capybara**):
- `SepCtx` = list of capture sets "meant to be pairwise separated"
  (Syntax/SepCtx.lean:8) — entries are already whole sets.
- Entailment rules exist in-target: `sep_union`, `sep_mono` (full left
  anti-monotonicity under `Subcapt`; ours), `sep_symm`, `sep_lock`,
  `sep_droppable` (TypeSystem/Core.lean:80-125). Cross-footprint demands
  below footprint entries are payable via `sep_lock + sep_mono + sc_elem`
  (`sep_mono` shrinks the left side only — upward-resolved peak-level
  demands are NOT payable this way; the new compile must ground
  `sep_distinct`-shaped leaves at footprint entries *before* any
  source-side peak resolution). Within-footprint demands are never
  stated — which matches what the source ever grants usably.

**Endgame:** the phantom gap dies at formation (P1), the narrowing gap and
the atomization debt are never born (P3), the target never reopens beyond
the five proven conservative extensions. Pin target for the new module:
**zero, with no legacy baseline to inherit** — the eight legacy sorries are
quarantined with the legacy module and become the cliffs checklist (Phase E)
that the new design must avoid by construction.

## Phase R — Rebase + legacy quarantine (FIRST)

> **✅ COMPLETED 2026-07-04.** Commit chain: notes checkpoint + backup
> branch `capybara-translation-pre-rebase-2` at `ff84c9f`; dangling
> `import Semantic.Capybara` removed `410143d`; quarantine `16cb8d4`
> (39 files → `LegacyCapybara/`/`LegacyCompilation/`, unimported, frozen
> notices); merge `f1cfc6f` (core taken wholesale; Debruijn kept both
> additive families; five extensions restated in the merge — `cell`/
> `reader` reshaped for element-typed cells, element invariant; `sep_mono`
> Fundamental cases ported verbatim and proven); R.5 `335cf07`
> (`sem_subtyp_cell`/`reader`/`cap`/`poly_cap` re-proven in the Kripke
> model — old skeleton transferred: element payloads carried verbatim,
> wf/covers fields rebuilt via `SemSubcapt` monotonicity). **Acceptance
> held: whole tree green AND sorryAx-free** — `#print axioms` sweep over
> `fundamental`, `adequacy_platform`, `immutability_adequacy_platform`
> (+`_run`), `fundamental_subtyp`/`_sepcheck`/`_sepcheck_global`,
> `SepCheck.left_mono`, and the four `sem_subtyp_*` = only
> `[propext, Classical.choice, Quot.sound]`. Model note for D/C: `.cell`
> denot uniquely lacks the leading `e.WfInHeap` conjunct; `SemSubcapt` now
> yields `CapabilitySet.Subset` on the MEMORY's denotations; cells store a
> step-indexed `MonRel` whose defining iff is what the rigid-element-type
> choice carries verbatim.

The core has evolved: 28 commits since the merge base `f6b793e`, tip
`af26a66` ("consume-lambda elimination; module green", 0-sorry). The
translation branch carries 89 commits on the old base. Under the fresh
start, **none of the legacy translation is repaired against the new core**
— that was the bulk of rev. 1's R and it is deleted work.

### Steps

1. **Backup/reference point**: branch or tag
   `capybara-translation-pre-rebase-2` — the last commit where the legacy
   module is green against the OLD core. This, not the in-tree copy, is
   the *checkable* legacy reference.
2. **Quarantine** (before the merge, so the tree is green at every step):
   - `git mv Semantic/CoreCapybara/Capybara Semantic/CoreCapybara/LegacyCapybara`
     (+ `Capybara.lean` → `LegacyCapybara.lean`),
     `git mv Semantic/CoreCapybara/Compilation Semantic/CoreCapybara/LegacyCompilation`
     (+ aggregator likewise); fix internal `import` lines mechanically
     (37 files).
   - Drop the two imports from `Semantic/CoreCapybara.lean` (the de facto
     root aggregator — the lakefile has no explicit glob, and the working
     discipline is per-file lean4check, so unimported = out of the build).
   - Names inside legacy stay `Capy*` (they sit in `namespace
     CoreCapybara`); the new module will reuse those natural names.
     Clashes are impossible while legacy is never co-imported; an optional
     `namespace Legacy` wrap is hygiene, not a requirement, and can wait
     until a co-import is actually wanted.
   - Note in `LegacyCapybara.lean`'s docstring: frozen 2026-07-04,
     reference tag, superseded by the fresh module.
3. **Merge `core-capybara` into `capybara-translation`** (merge, not a
   89-commit replay). The one non-trivial conflict is **Fundamental.lean**
   (our +107 lines × the core's ~4,900-line Kripke rework): take the core
   side wholesale, re-add the five extensions (`sep_mono` + four `Subtyp`
   covariance rules), and **re-prove their semantic cases in the new
   Kripke model**, reshaped for element-typed cells/readers, using the
   old-model proofs (`git show <reference-tag>:...`) as guides. Budget as
   a real proof task, not merge mechanics. (The old-model cases are
   already proven on this branch — `fundamental_sepcheck`/`_global`
   sep_mono cases, `sem_subtyp_cell/reader/cap/poly_cap` — so this is
   re-proof, not proof-from-nothing.)
4. Do **not** base on `core-capybara-relax-droppability` — discarded
   experiment (user ruled it the wrong direction).

### What the new core provides (design targets for D)

| New since old base `f6b793e` | Relevance to the fresh module |
|---|---|
| **Generic cells/readers**: `Ty.cell`/`Ty.reader` gain an element-type argument (Ty.lean:63-65) | D decides whether source cells go generic too (natural) or stay bool; compiled shapes `.cell ⟦C⟧ _`; the four covariance rules reshape for the element argument (R re-proof) |
| **n-ary existentials**: `Ty.exi : (n : Nat) → …` (Ty.lean:72), `pack` over `List.Vector` + `PairwiseSep`, `unpack` binds `extendCVars n` | D decides source existential arity (fresh/unpack at n = 1 vs native n-ary); `Sig.extend`-vs-`extendCVars 1` defeq friction has known repair idioms (memory) |
| **`DisjCheck` judgment** (Core.lean:170) | feeds `PairwiseSep` (pack); `seq_sep` takes a **SepCheck** — a small **DisjCheck→SepCheck embedding** is needed by consumer compilation (P6) |
| **Consumer lambdas**: `consumer`/`consumer_app` | the receiver for P6 |
| Kripke Denotation/Fundamental rework | the R merge cost (step 3) |

Verifiably stable (design analysis carries over): `Syntax/CaptureSet.lean`
and `Syntax/SepCtx.lean` byte-identical since the fork; `SepCheck`,
`Satisfy`, `modal_modal`, `sep_lock`, `Subcapt`, lock/ModalCtx structure
unchanged. Also already in the core: kill-based `letin`/`unpack`,
`accessible` premises, `seq_sep`, PeakSet/kill_peaks +
`Ctx.kill_peaks_accessOnly` (legacy Compilation/AppSupport.lean:85-107 —
quarry item).

### Acceptance

**Whole tree green AND sorryAx-free** — for the first time on this branch:
with legacy unimported, the build is exactly core-capybara + the five
re-proven extensions; there is no sorry baseline to inherit. `#print
axioms` sweep on the headline core theorems + the five extension cases.
Legacy directories present, renamed, unimported; reference tag recorded.

## Phase D — First-principles design (paper, before code)

One design document (`roadmaps/capybara-design.md` or `notes/`), covering
the whole new module — source calculus AND compilation scheme together,
since the compiled-type scheme is where past debt accumulated. Exit
criterion: the document is complete enough that S and C are execution, not
discovery. Optionally re-run the fresh-context adversarial review on it
(the rev. 1 critique caught real errors; cheap insurance before building).

**D.1 — Feature inventory.** Type formers (arrow, cpoly, consumer — P6 —
cells/readers: generic or bool, existentials: arity), expression forms,
mode/authority lattice. Decide what legacy features are NOT carried (e.g.
anything that existed only to serve atomization).

**D.2 — Well-formedness (P1, ex-W).** `DropWf` designed into a single
`CapyTy.Wf` bundle (with `PureBounds`, `AccessOnly`-domain) from day one —
premised once at binder-introduction points + `subtyp`'s E2, regularity
proven once; no scattered per-rule premises (the legacy app:334-339
re-requiring pattern is the anti-pattern). Per-binder authority table
(load-bearing for zero-rejection): `exi` binders extend at `.can_drop`
(witness drop-latents are legitimately exercisable — `letin_unpack`'s own
body use is `{drop C}`); `arrow`/`cpoly` binders at `.access_only`.
Substitution case is nearly free: access-only cvars never drop-occur in WF
types, so `{drop c}[c ↦ D]` never fires; remaining `applyDrop` sites are
droppability-guarded.

**D.3 — Unified capture parameters (P2, ex-U).** No roots/views species —
any capture parameter, however bounded, means separation. Four ingredients,
born in the rules (no `pseudo_peak` branch ever exists):
1. `sep_distinct` guarded by an **is-cvar-atom shape guard** (any two
   mode-erased-distinct cvar *atoms* separate; `{ε c} # {ro c}`
   underivable; the guard keeps overlapping sets and term-var alias pairs
   out — both unsound).
2. `bound_unbound`: `CapySubbound Γ (.bound D) (.unbound m)` with premise
   `CapyHasKind Γ D m` (free for `m = ε`; ro-kinding for `m = ro`) — every
   cpoly is instantiable.
3. Separation check at `capp`: `CapySepCheck Γ D (interfere_set …)`,
   mirroring app's premise.
4. Top-level hypothesis: primordial pairwise separation over all env cvars.
Soundness architecture (verified 2026-07-03): payment covers consumption —
fiat consumptions reach sites through capture annotations = what
`interfere_set` collects; eliminations check POST-substitution types;
aliasing is rejected exactly where observable. ro-sharing survives
(`sep_ro`; capability-based model); dissolution only goes UP into bounds —
no sibling-parameter path. **Target needs nothing** (`Subbound.top` is the
compiled image; `Satisfy.hkind` pays m-kinding via the wrap lock's
`MutabilityCtx`). Language consequence (accepted): distinct capture
parameters are a separation contract; sharing = merge parameters or ro.

**D.4 — Lock design (P3, incl. the ruled F.0 device).** Locks are
footprint-granular and resolution-free from day one; `pseudo_peak`,
`resourcePeaks`-vs-`peaks` view splits, stability filters, and the
atomizing `peakSepCtx` are **never built**. The entry-grouping device
(RULED 2026-07-04): a flat `SepCtx` claims all pairs, so which entries may
be pair-claimed must be decided — any use-site peak-disjointness test is a
resolution (narrowing flips it; legacy hLG resurrects), and purely
syntactic grouping makes false claims (`{y}` vs `{c}` with `c ∈ ann(y)` ⇒
unsatisfiable wrap for a harmless program). **Grouping is computed ONCE at
the type's introduction context and transported** — threaded G-style or
materialized in the compiled modal's Ψ (which is syntax) — never
recomputed. Residual obligation: substitution-compatibility
(instantiation preserves the grouping's disjointness BECAUSE of the D.3
checks). Rejected alternatives, recorded: (b) cvar-only entries +
payment-time descent — REFUTED (body derivations ground at peak-closure
cvar pairs outside the written footprint; closure = resolution); (c)
canonical-footprint WF — rejected under the no-restriction rule (`sc_elem`
widening legitimately creates redundant spellings). **The one-page
transport design (where the grouping lives, behavior under
rename/subst/narrowing, checked against the hLG and substitution
scenarios) is D's hardest deliverable.**

**D.5 — Subtyping (P4 + P5, ex-F2/F3).** Contravariant arrow domains from
day one (the target has had them all along, TypeSystem/Core.lean:153;
legacy disabled them because term-parameter stored types leaked into lock
manufacture via `peaksVarBound` — under P3 that leak never exists; cvar
bounds never leaked, which is why legacy cpoly kept bound-contravariance
via `consCVar_boundIrrel`). Source `sep_mono` (left-monotonicity under
`CapySubcapt`) from day one — semantically unimpeachable
(`C' ⊑ C ∧ C # X ⟹ C' # X`), covers separation facts against arbitrary
footprints that the D.3 fiat does not, compiles by a one-rule mirror to
target `sep_mono`; legacy couldn't afford it only because the frozen
atomized pipeline couldn't pay transported claims (`EquivP` was the
fence). Write the **P2×P4 interaction argument** here: does
payment-covers-consumption survive contravariant shrinking of
interfere-relevant annotations? (No counterexample found 2026-07-03;
argument never written — a D exit criterion.)

**D.6 — Consumer lambdas (P6, ex-L; designed now, built last).** Surface
type `.consumer T1 cs E` (T1 under the implicit ∃-witness binder, dual to
the arrow's ∀ self-cvar; `E` at OUTER scope — the witness must not leak);
expression `.consume_abs T1 e`; elimination reuses `.app x y`
(type-directed dispatch on disjoint constructors), compilation
synthesizing `pack ⟦D⟧ ⟦y⟧`. Un-phantomable by construction: consumption
is a CONSTRUCTOR, not a mode annotation — subsumption cannot conjure it;
complements P1. Intro rule = `letin_unpack`'s binder block as a lambda
(`(Γ,C[.can_drop]<:.unbound ε), x:T1` context, `cs↑↑ ∪ {εC} ∪ {drop C}`
use, `implicit_cvar` rename) + witness-WF premises. Elim premises = pack
evidence (D closed, access-only, droppable) + `CapyDisjCheck Γ D {εx}` +
argFit `y : T1[openCVar D]`; NO interfere_set check (the core consumer is
kill-based: witness-vs-closure is the DisjCheck; the rest is dead by the
kill clause). Conclusion use-set fresh-style `{εx} ∪ D ∪ D.applyDrop`
(var-style can't match the compiled pack's concrete use; the explicit
`D.applyDrop` lets the enclosing letin's SeqComp protect the
continuation). Compilation: intro → core `consumer` with
`X := ambient droppables \ cs`; elim → `consumer_app` + `pack` (n = 1,
`PairwiseSep` trivial); SeqComp discharge = `seq_access_only` (D leg) +
`seq_sep` via the DisjCheck→SepCheck embedding (drop leg), assembled by
`seq_union`. Known v1 limit (accepted, document in the rule): the
DisjCheck premise needs all closure peaks droppable (`disj_droppable` is
its only base pair rule) — consumers closing over non-droppable roots
can't be applied; upgrade path = premise becomes `CapySepCheck` compiled
straight into `seq_sep`. Main risk: kill-context transport (body TYPES
may statically mention killed cvars — core treatment unverified).
Deferred: direct-package application, n > 1 witnesses, dependent results.

**D.7 — Alignment by design (P7, ex-srcAligned; THE open decision, made
here).** The legacy anatomy (established 2026-07-04, verified at legacy
TypeCompiler.lean:218-253): the compiled arrow is the two-cpoly tower
`[c][cx <: ⟦ann⟧](x : S^{cx}) → …` — the source arrow's own binder maps to
the OUTER *unbounded* cpoly (app's first capp instantiates it with `⟦D⟧`);
`cx` is the inner bounded one, absent from source signatures, whose
source-level identity is **x-used-as-a-capture-atom** (the compiler
compiles the self-refined domain `(T↑)^{εx}` under `x ↦ {εcx}`; the second
capp `cx := {εy}` is the capture half of term substitution, which the
source does monolithically via `openVar`). `cx` exists because a stored
type cannot mention its own binder. The legacy gap: the body context
stores `x` at the RAW annotation while the compiled image is `{εcx}` —
stored-type-READING forms on a parameter (`fresh x`, `drop x`,
pack-over-x) compile to obligations false for access-only `cx`.
Prohibition is not a fix: widening `{εcx}` to cx's bound and
letin-rebinding is sound and compiles (`sc_cvar` dissolution) — the fix is
**alignment**. Fresh-start candidates (α death-by-F and δ pin from rev. 1
are moot — there is no legacy pipeline to observe and no reason to be born
pinned):
- **(β) subcapture-shaped coherence from birth** (natural default): the
  new `SrcAligned`/`Coherent.varLookup` interface is stated with
  `image ⊑ ⟦T.captureSet⟧` from day one — both legacy disjuncts already
  delivered exactly that — and every consumer is *designed against* `⊑`
  instead of audited for it. Companion requirement: the widening route
  rides source capture covariance, which legacy had for arrows only —
  the new source gets covariance at cell/reader/cap formers too (their
  target twins are the four proven extension rules).
- **(γ) the `S^{εc}` annotation idiom**: domains whose top-level capture
  is the arrow's own binder make the direct forms fail already (the
  binder is access-only AND unbounded — nothing to widen to), shrinking
  the residual misalignment to `{εcx}` vs `{εc'}` (trivial subcapture).
  Could be the default style, or a WF'd idiom — but forcing it is in
  tension with the no-restriction rule; as an *idiom* it composes with β.
- **(novel)**: with the rules unowned by history, the arrow rule's body
  context can be designed outright around the view question (e.g. what
  view of the parameter the body types against, and what the compiled
  Coherent invariant asserts) — D.7 is where that gets one honest pass.
Recommendation: β as the backbone, γ as idiom, novel-design pass during
D.7; user confirms here.

**D.8 — Example programs.** Write the worked examples FIRST (none exist in
the tree today): fresh + abs + app + letin_unpack + a consumer + a capp on
a bounded parameter. They are D's test of expressiveness (the
zero-rejection claims), then live as green regression programs through S/C.

## Phase S — Build: the new source calculus

`Semantic/CoreCapybara/Capybara/` recreated from scratch per D: syntax,
substitution/rename infrastructure, type system (all of P1/P2/P4/P5/P6 in
the rules from day one), then ONE metatheory pass — regularity (Wf
threading), inversion, narrowing, substitution lemmas. No `pseudo_peak`,
no `resourcePeaks` split, no per-rule WF premise scatter. The D.8 example
programs typecheck at the end of S. Zero sorries at phase acceptance
(named interim sorries allowed only mid-phase).

Quarry consciously (statement shapes and idioms, not wholesale ports):
legacy Substitution/rename lemma inventory, `Sig.extend` defeq repair
idioms, the two-peak-view lessons (the new system has ONE `peaks`).

## Phase C — Build: the new compilation

`Semantic/CoreCapybara/Compilation/` recreated per D. Staging:

1. **TypeCompiler + compiled-form lemmas**: the compiled arrow/cpoly/
   consumer schemes with footprint locks and the D.4 transported grouping
   from the first line. The legacy tower (reference tag
   TypeCompiler.lean:218-253) is the starting sketch, re-derived under
   D.7's alignment choice.
2. **Coherence layer**: the β-shaped (subcapture) invariant; context
   morphisms; substitution lemmas. The substitution-compatibility lemma
   for the transported grouping (D.4's residual obligation) lands here —
   the single riskiest proof of the phase.
3. **Rule families in order**: fresh/abs/subtyp first (legacy had these
   green — regression reference), then app + capp through **ONE
   parameterized checked-instantiation device** (bound-fit /
   satisfy-bridge / final-capture serving app, capp, and consumer-app —
   design once, the legacy var-origin/readonly-origin replay split is not
   repeated: the app compile is parametric in head origin), then
   consumer_app + pack synthesis (P6), then letin/letin_unpack over
   consuming heads — which needs the **kill-weakening lemma** (see E).
4. `CapySepCheck.compile` grounds `sep_distinct` leaves at footprint
   entries before any peak resolution; body-side payments go through
   enclosing entries via `sep_lock + sep_mono`; no covering pipeline
   unless a residual transport genuinely needs one.

NOT ported, by design: `peakSepCtx` (atomizing), the stability filter,
`pseudo_peak` machinery, CompileNarrow (node lemma, 9-lemma peak
inventory, `compile_arrowLock_narrow`), the ~900-line narrowing recursion
plan, `SepCovered`/`TgtSplitCoveredOn` (unless a small residual transport
survives), the 963 pinned lemma and its mode-poly premise.

## Phase E — Endgame

- Headline preservation theorem over the full rule set; adequacy of the
  compiled programs via the core's green stack.
- **Kill-weakening lemma** (target-side, syntactic; research-grade,
  latent since the old base): "`HasType` survives killing `can_drop`
  peaks the use-set avoids" — needed to compile `letin`/`letin_unpack`
  over consuming heads (their core rules kill the continuation context;
  the source continuation is typed unkilled). Does not exist on
  core-capybara (only denotational transport, Denotation/Kill.lean).
  Plausible shape: kill flips authority to `.killed` with the bound
  intact; `sc_cvar` requires `.access_only`, so killed cvars never fed
  subcapture; the avoidance hypothesis is exactly `seq_drop`'s DisjCheck.
  This is a LEMMA about the target, not a rule change — consistent with
  the target-intact constraint.
- **Cliffs checklist** — each legacy sorry, with its by-construction
  killer, verified dead in the new module:
  | Legacy sorry (at reference tag) | Killer |
  |---|---|
  | 963 pin `app_capture_self_sep_modepoly` (CompileSubstOpenVar:977) | P1: phantom drop-latents unformable |
  | hLG (Preservation:1351) + hself/CompileNarrow | P3: locks transported, never recomputed — narrowing preserves them syntactically |
  | hcompat (:753), hcompatAl (:811) | footprint entries + `sep_mono` absorb the `Cy ⊑ latent` slack; if a residue survives, the app-case context discipline chosen in D decides (G-style actual-typed intermediate context) |
  | readonly replay (:449) | C.3: app compile parametric in head origin — no replay |
  | non-app stub (:1438) | C covers all rule families; prerequisite = the kill-weakening lemma above |
  | `Coherent.srcAligned` (CoherenceMorphism:588) | P7/D.7: alignment designed in (β backbone) |
  | `app_use_covered` (UseCovered:161) | use accounting designed at footprint granularity; D must check it dissolves with atomization (flag in D.4 if not) |
- Hygiene: sweep bare `sorry` AND `#print axioms` for `sorryAx` across the
  new module before declaring green; zero tolerance — there is no
  inherited baseline.
- Docs/memory updates; legacy directories may be deleted once the new
  module strictly dominates (user call at the time).

## Deferred (explicitly out of scope)

- The one-rule target extension (`drop×ε` mode-lowering separation) — moot
  under P1; recorded as considered-and-unnecessary.
- `core-capybara-relax-droppability` — discarded experiment; do not
  resurrect.
- Repairing the legacy module against the new core — explicitly not done;
  the checkable legacy reference is the pre-merge tag.
- Consumer extensions: direct-package application, n > 1 witnesses,
  dependent results (D.6 lists the upgrade paths).

## Sequencing and risk

**R → D → S → C → E.** R first (user directive; everything builds on the
new core). D before any code: the entire value of the fresh start is that
S and C execute a settled design — if D wobbles mid-build, stop and re-run
D, don't patch forward (that is how the legacy debt accumulated). Within
C, the transported-grouping substitution lemma (C.2) should be attacked
early — it is the load-bearing novelty; if it fails, the F.0 device needs
redesign while nothing downstream exists yet.

Gates: D's exit criteria — the transport one-pager (D.4), the P2×P4
interaction argument (D.5), the alignment decision (D.7, user
confirmation), example programs (D.8); optional adversarial review of the
design doc. E's acceptance = cliffs checklist fully verified + hygiene
sweep.

Biggest risks, ranked: (1) rebuild scale — S+C re-prove everything the
legacy module took months to accumulate; mitigation: the quarry (all
design analyses survive, legacy proofs remain readable at the tag, and
the new pipeline is structurally smaller — most legacy Compilation volume
served atomization); (2) the transported-grouping substitution lemma
(C.2); (3) R's Fundamental merge + five re-proofs in the new Kripke model;
(4) the kill-weakening lemma (E; research-grade, plausible shape); (5)
D.7 alignment choice turning out to constrain the arrow rule in ways D
didn't foresee — mitigated by the D.8 examples and the optional design
review.

Working discipline: lean4check (never `lake build` as a check), no axioms
(theorem + sorry), `#print axioms` sweeps before any "done" claim, opus
subagents with single-file ownership when parallelizing, zero-sorry phase
acceptance (named interim sorries only mid-phase).
