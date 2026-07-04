# Roadmap: Capybara → CoreCapybara translation

*Finalized 2026-07-04. Agreed in discussion 2026-07-03; adversarially
reviewed by an independent fresh-context reviewer and the findings folded
in (verbatim critique preserved at `notes/roadmap-critique-2026-07-03.md`).
File:line anchors were machine-verified on those dates; core-capybara
anchors against commit `af26a66`. Supersedes
`notes/app-case-design-decision.md`.*

*Decision status: every phase is ruled and actionable. The Phase F
entry-grouping device is **ruled** (F.0: compute once, transport
thereafter — 2026-07-04). ONE design item remains open: the
`Coherent.srcAligned` device (candidates enumerated in Phase A; Phase F
runs a check that may moot it).*

## The ruling

One constraint and two design changes:

**Constraint — the target stays intact** (conservative extensions only,
each proven sound in the existing model; no new obligations imposed on
target clients). The translation's actual target delta today: **141
insertions in 3 files** — TypeSystem/Core.lean +25 (`SepCheck.sep_mono`
plus four `Subtyp` capture-covariance rules `cell`/`reader`/`cap`/
`poly_cap`), BasicProps.lean +9, Fundamental.lean +107 (the semantic cases
for all five additions, already proven in the old model). It stays at that
scale. Rationale: the target's green semantic stack (Fundamental, adequacy)
is the fixed ground truth; the result "the (conservatively extended) core
hosts the surface calculus" is strictly stronger than one where the core
was bent to receive it.

**Change 1 — `DropWf`: drop-qualified captures must be exercisable
(source-side well-formedness).** A `.drop`-moded atom is well-formed only
when its peaks have `can_drop` authority. This kills Gap 1 (the phantom
drop-separation obligation, pinned at `app_capture_self_sep_modepoly`,
CompileSubstOpenVar.lean:963) at the *formation* level. Evidence this is
the right frame:
- The invariant already holds for terms and use-sets: `drop` requires
  `droppable` (Capybara/TypeSystem/Core.lean:399), `fresh` requires
  `droppable Γ D` (:252), `letin_unpack` binds its witness `C[.can_drop]`
  (:377). The **only** leak is types-via-subsumption: `subtyp` (:429)
  checks only `IsClosed`, and `sc_elem`'s `{} ⊑ {drop c}` flows into
  nested arrow latents through covariant cs-widening (:177), below the
  reach of the top-level `AccessOnly` premises (abs:274, app:340).
- Arrow binders are access-only (`C<:.unbound .epsilon`, :180) and `capp`
  instantiation is access-only-valid (:358), so **no term can exercise a
  drop-latent over a parameter** — every such latent is a phantom.
  `DropWf` therefore rejects *zero terms*, only self-contradictory
  ascriptions. Consistent with the no-restriction rule.
- The comment at app:334-339 ("subsumption at the use-site is what loses
  it, so it is re-required here") documents the per-rule-premise pattern
  this replaces.

**Change 2 — footprint-granular, resolution-free locks (translation-side;
"N′").** Lock manufacture (`peakSepCtx`, Compilation/TypeCompiler.lean:172)
stops atomizing and stops resolving through stored types: entries become
whole footprints as written (term-var atoms stay symbolic `{x}`; cvar atoms
already are symbols), and the entry *grouping* is computed once at the
introduction context and transported thereafter (F.0). This kills Gap 2
(narrowing self-separation, the `hself` hypothesis in CompileNarrow.lean /
the `hLG` sorry in Preservation) by construction — declared-side and
actual-side locks become syntactically identical, since nothing in a lock
mentions a context resolution that narrowing could change. It also deletes
the manufactured within-footprint obligations (the demand side of Gap 1)
and the `pseudo_peak` graft. Evidence the target already supports
consumption at this granularity (all verified, and **unchanged on
core-capybara**):
- `SepCtx` = list of capture sets "meant to be pairwise separated"
  (Syntax/SepCtx.lean:8) — entries are already whole sets.
- Entailment rules exist in-target: `sep_union`, `sep_mono` (full left
  anti-monotonicity under `Subcapt`; ours), `sep_symm`, `sep_lock`,
  `sep_droppable` (TypeSystem/Core.lean:80-125). Cross-footprint demands
  **below** footprint entries are payable via `sep_lock + sep_mono +
  sc_elem` (`sep_mono` shrinks the left side only — upward-resolved
  peak-level demands are NOT payable this way; that is why Phase F.3's
  `sep_distinct`-leaf re-targeting must intercept compiled proofs *before*
  source-side peak resolution, not after). Within-footprint demands are
  never stated — which matches what the source ever grants usably.

**Endgame:** Gap 1 dies at formation (W), Gap 2 and the atomization debt
die at manufacture (F), the target never reopens beyond the five proven
conservative extensions. Pin target: zero *modulo* the `Coherent.srcAligned`
ruling (Phase A).

## Phase R — Rebase onto latest core-capybara (FIRST)

The core has evolved: 28 commits since the merge base `f6b793e`, tip
`af26a66` ("consume-lambda elimination; module green", 0-sorry). The
translation branch carries 89 commits on the old base.

### What is genuinely new on the core (verified against base `f6b793e`)

| New since base | Impact on translation |
|---|---|
| **Generic cells/readers**: `Ty.cell`/`Ty.reader` gain an element-type argument (Ty.lean:63-65) | `TypeCompiler` cell/reader cases + compiled-form lemmas; source bool-cells map to `.cell ⟦C⟧ bool`-shaped targets; our four `Subtyp` covariance rules reshape for the element argument |
| **n-ary existentials**: `Ty.exi : (n : Nat) → Ty .capt (s.extendCVars n) → Ty .exi s` (Ty.lean:72), `pack` over `List.Vector` + `PairwiseSep` premise, `unpack` binds `extendCVars n` | fresh/unpack compilation re-targets at `n = 1`; expect `Sig.extend`-vs-`extendCVars 1` defeq friction (known repair idioms in memory) |
| **`DisjCheck` judgment** (Core.lean:170) mirroring source `CapyDisjCheck` | `seq_sep` (already in base) takes a **SepCheck**, not DisjCheck; `DisjCheck` feeds only `PairwiseSep` (pack). Reaching `SeqComp` from source `seq_drop` needs a small **DisjCheck→SepCheck embedding** (constructor-wise straightforward; new work item) |
| **Consumer lambdas**: `consumer`/`consumer_app` rules | No obligation now (nothing compiles to them yet); receiver for Phase L |
| **Denotation/Fundamental Kripke rework** (~4,900 changed lines in Fundamental.lean; new KripkeModel/StepIndexed* files) | The real merge cost — see Mechanics 2 |
| `capp` gained a vestigial unused `{I : CaptureSet s}` implicit | Cosmetic |

Already in the base (no R work): kill-based `letin`/`unpack` (+droppable
premise), `accessible` premises with `{}`-use head vars (`unwrap` has no
`accessible` premise on the new core), `seq_sep`, PeakSet/kill_peaks
infrastructure — and the `kill_peaks`-is-noop lemmas for access-only heads
already exist (`Ctx.kill_peaks_accessOnly`, Compilation/AppSupport.lean:85-107).

### What is verifiably stable (design analysis carries over)

`Syntax/CaptureSet.lean` and `Syntax/SepCtx.lean` are **byte-identical**
since the fork; `SepCheck`, `Satisfy`, `modal_modal`, `sep_lock`, the
`Subcapt` rules, and lock/ModalCtx structure are unchanged. Everything the
ruling above relies on survives the rebase untouched.

### Mechanics

1. Back up: branch `capybara-translation-pre-rebase-2` (precedent exists).
2. **Merge `core-capybara` into `capybara-translation`** rather than
   replaying 89 commits: `Capybara/` and `Compilation/` don't exist on the
   core side, and the Syntax/TypeSystem deltas are small. The one
   **non-trivial conflict is Fundamental.lean** (our +107 lines × the
   core's ~4,900-line Kripke rework): resolve by taking the core side
   wholesale, then re-adding our five extensions (`sep_mono` + the four
   `Subtyp` covariance rules) and **re-proving their semantic cases in the
   new Kripke model**, reshaped for element-typed cells/readers, using the
   old-model proofs (`git show capybara-translation-pre-rebase-2:...`) as
   guides. Budget this as a real proof task, not merge mechanics.
3. Do **not** base on `core-capybara-relax-droppability` — that is the
   discarded (PACK)/(DROP)-premise experiment (user ruled it the wrong
   direction).
4. Repair order: Syntax/type-level first (`TypeCompiler`), then
   `Substitution`/compiled-form lemmas, then the big Compilation files,
   Preservation last.
5. The Fundamental cases for all five target extensions are **already
   proven on this branch in the old model**
   (`fundamental_sepcheck`/`_global` sep_mono cases;
   `sem_subtyp_cell/reader/cap/poly_cap`), and everything imports together
   via `Semantic/CoreCapybara.lean`. The rebase work item is purely the
   re-proof under the new model (Mechanics 2), old proofs as guides.

### Acceptance

Whole tree green under lean4check; sorry inventory unchanged from the
pre-merge baseline of **eight**: the 963 pin (CompileSubstOpenVar:977),
hLG (Preservation:1351), hcompat (:753), hcompatAl (:811), readonly
(:449), the non-app stub (:1438), `Coherent.srcAligned`
(CoherenceMorphism.lean:588 — the open design item, Phase A), and
`app_use_covered` (UseCovered.lean:161). `#print axioms` sweep on the
headline lemmas shows no NEW taint (pre-existing taint: srcAligned and
app_use_covered sit on the live app spine, so headline lemmas are
sorryAx-tainted by them today — R does not change that).

## Phase W — DropWf (source-side)

1. **Predicate**: `CapyCaptureSet.DropWf Γ C` — every `.drop`-moded atom's
   peaks are droppable (reuse `CapyCaptureSet.droppable`,
   Capybara/Syntax/Context.lean:497, which is already peak-derived) — and
   recursive `CapyTy.DropWf Γ T`, extending Γ under binders **with this
   per-binder authority table** (load-bearing for the zero-rejection
   claim): `exi` binders extend at **`.can_drop`** (drop-latents over
   existential witnesses are legitimately exercisable — `letin_unpack`'s
   own body use is `{drop C}`; extending at `.access_only` would reject
   them and break "zero rejections"); `arrow`/`cpoly` binders extend at
   `.access_only`.
2. **Enforcement points** (not inside `CapySubcapt`/`CapySubtyp`
   constructors — subcapture is shared with legitimate droppable-set
   reasoning like `sc_drop_mono`/`seq_drop`, and premises inside subtyping
   poison its metatheory): the `subtyp` rule (on `E2` — the single choke
   point for phantom creation) + written annotations (`abs`'s `T1`,
   `cabs`'s bound).
3. **Regularity**: every type in a derivation is DropWf. Preservation
   lemmas under rename/subst/narrowing. The substitution case is nearly
   free: `capp`'s `D` is access-only and DropWf says access-only cvars
   never drop-occur, so `{drop c}[c ↦ D] = D.applyDrop` never fires on WF
   types; remaining `applyDrop` sites are droppability-guarded already.
4. **Optional consolidation**: bundle DropWf with `PureBounds` and
   `AccessOnly`-domain into one `CapyTy.Wf`, premised once, regularity
   once; the scattered per-rule premises (the app:339 pattern) become
   corollaries. (`NoPseudoPeak` is only transitional — Phase F deletes the
   `pseudo_peak` device and those premises with it; don't design the
   bundle around it.) Recommended if the premise-threading cost repeats.
5. **Immediate harvest (minimal)**: add the WF hypothesis to the 963
   lemma's statement and note the scenario is unreachable; the *full*
   deletion of the mode-poly premise waits for Phase F (no point doing
   `compile_subst_subtyp` interface surgery twice).

Acceptance: WF threaded + regularity proven; zero-rejection sanity check —
no example programs exist in the tree today, so **write one**: a small
typed source example exercising fresh + abs + app + letin_unpack, kept
green across W and all later phases.

## Phase U — Unified capture parameters (source-side)

*Ruling (2026-07-03, user decision): the roots/views species distinction is
DISSOLVED — any capture parameter, however bounded, means separation. The
earlier "keep the distinction" finding was a theorem about unification
under FREE instantiation; Phase U changes the instantiation rules,
supplying the payment that makes the unified fiat sound. It also fixes a
genuine wart: `[c <: m]` cpolys are uncallable today (`capp` demands
`.bound D`, `bound_unbound` removed).*

Four ingredients:

1. **Extended fiat**: `sep_distinct`'s `CapyIsPeak` guard is **replaced by
   an is-cvar-atom shape guard** — any two mode-erased-distinct cvar
   *atoms* are separate (`{ε c} # {ro c}` stays underivable). The shape
   guard is load-bearing: it keeps arbitrary sets (`{x} # {x,y}` —
   overlapping) and term-var pairs (`{x} # {y}` with `y := x` — aliases)
   out; both would be unsound. The `pseudo_peak` branch of the guard
   survives until Phase F deletes the device (U runs before F).
2. **Restored `bound_unbound`**: `CapySubbound Γ (.bound D) (.unbound m)`
   with premise `CapyHasKind Γ D m` (free for `m = ε` via `rw`; ro-kinding
   for `m = ro`). Root-cpolys become instantiable via bound-narrowing.
3. **Separation check at `capp`**:
   `CapySepCheck Γ D (CapyTy.interfere_set (.cpoly cb {εx} T))` — the
   exact mirror of app's premise (Core.lean:345); `interfere_set` is
   already defined for cpoly (Substitution.lean:233).
4. **Widened top-level hypothesis**: primordial pairwise separation covers
   all env cvars.

Soundness architecture (analysis 2026-07-03): payment covers consumption —
every fiat consumption reaches its site through capture annotations, which
is what `interfere_set` collects; eliminations check against
POST-substitution types, so earlier instantiations appear concretely in
later checks; aliasing is rejected exactly where the aliased things could
meet (if the body cannot observe `c1`, no check fires and none is needed).
Corner cases verified: ro-sharing survives (`sep_ro` pays; the model is
capability-based, so mode-poly grants on ro instantiations are true); no
self-separation (dissolution only goes UP into bounds — no path between
sibling parameters); drop modes policed by DropWf/droppability as before;
the old `bound_unbound` removal was protecting fiat-without-payment, which
ingredient 3 answers. **Target needs nothing** (verified: `Subbound.top`
is the compiled image of the restored rule; `Satisfy.hkind` pays the
`m`-kinding via the wrap lock's `MutabilityCtx`; no fiat exists
target-side; two cvars denoting disjoint subsets of a shared bound is
model-realizable).

Language consequence (accepted): distinct capture parameters are a
separation contract. Mutable aliasing across distinct parameters is
unwritable at any instantiation; sharing is expressed by merging
parameters or via the ro tier.

Compilation cost: compiled capp becomes structurally identical to compiled
app — Phase F builds ONE parameterized checked-instantiation device
(bound-fit / satisfy-bridge / final-capture) consumed by both rules. The
lock manufacture rule simplifies further: every cvar atom heads an entry —
no species case-split.

Metatheory repair inventory: `CapySubbound` inversion lemmas (restored
`bound_unbound` gives `.unbound` targets a second constructor), subtyping
transitivity/narrowing through the new rule, `capp` inversion updates for
the new premise, and a regularity re-thread over the edited rules.

Sequencing: source-rule edits + metatheory here, **bundled with W's
regularity pass** (do the rule surgery of W+U first, then ONE combined
regularity pass — threading W's regularity before U's rule edits would
rework it); the compilation payment lands in F.

Acceptance (interim state — U is honest-with-sorries until F): source
rules edited + metatheory green; `CapySepCheck.compile` gains **one named,
documented sorry** for the extended-fiat case (bound-cvar pairs have no
lock item under the still-atomized manufacture — TypeCompiler.lean:172-176
filters unstable cvars; the payment is F's job); no other new sorries;
the W example program still typechecks.

## Phase F — Footprint locks (translation-side)

### F.0 — Entry-grouping device (RULED 2026-07-04: compute once, transport thereafter)

The tension this resolves: "locks are resolution-free, hence identical
under narrowing" conflicts with any manufacture-time pairing test.
Deciding which entries a flat target `SepCtx` may pair-claim requires a
peak-disjointness check; that check *is* a resolution (`peaksVarBound`
reads stored types, Capybara/Syntax/Context.lean:223-236), and narrowing
can flip its verdict overlap→disjoint (shrink `ann(y)` past a shared
atom) — the two sides of hLG would then group differently and hLG
resurrects. Purely syntactic grouping fails the other way: `{y}` vs `{c}`
with `c ∈ ann(y)` are syntactically disjoint, so the lock makes a false
claim and the wrap becomes unsatisfiable for a harmless program (today's
atomize-then-dedup hid this silently).

**Ruled device**: the grouping is computed ONCE, at the type's
introduction context, and thereafter *transported* — threaded G-style, or
materialized in the compiled modal's Ψ (which is syntax) — never
recomputed at use sites. Narrowing then preserves locks trivially; the
residual obligation is **substitution-compatibility**: instantiation
preserves the grouping's disjointness *because of* the U-checks (the
`interfere_set` payments at app/capp are what license the substituted
grouping).

Rejected alternatives (recorded so they are not re-proposed):
- (b) cvar-only entries + payment-time descent — REFUTED: body-side
  separation derivations ground at peak-closure cvar pairs *outside* the
  written footprint (source term-var separations have no fiat; every
  route descends to peak-level `sep_distinct` leaves), so a lock without
  closure-resolved entries cannot pay the body; closure = resolution,
  full circle.
- (c) canonical-footprint WF (forbid redundant spellings like `{εy, εc}`
  with `c ∈ ann(y)`) — rejected under the no-restriction rule:
  subsumption legitimately creates such spellings (`sc_elem` widening),
  and widened types may be needed for interface matching.

**Entry criterion for F's code work**: a one-page transport design —
where the grouping lives (threaded vs Ψ-materialized), how it moves under
rename/subst/narrowing — written and checked on paper against the hLG
scenario and the substitution scenario.

### Work items

1. **Manufacture**: `peakSepCtx′` — entries are footprints as written; no
   `peaks`-resolution of term vars, no per-atom fan-out; entry grouping
   comes from F.0's transported computation, never recomputed. The
   stability filter retires, and **`pseudo_peak` is DELETED** (verified
   2026-07-03: it is the atomized representation's hand-rolled footprint
   entry — `openCVar` freezes substituted sets so locks keep them as one
   atom; ordinary positions compile it transparently,
   TypeCompiler.lean:12-18 — under native footprint entries with
   positional identity it has no job). Deletion inventory: the
   constructor + `CapyIsPeak.peak_pseudo` + `openCVar` freezing + the
   `resourcePeaks`/`peaks` view split collapses (resourcePeaks existed
   only to dissolve pseudo for AccessOnly/droppable, Context.lean:396-408)
   + the `NoPseudoPeak`/`PeaksOnly` lemma families + every `NoPseudoPeak`
   premise in fresh(:260)/abs(:273)/app(:323-325) (they only refute pseudo
   branches in `CapySepCheck.compile`) + pseudo cases across ~15
   Compilation files (rebuilt here anyway). Source-side `peaks` stays —
   it is load-bearing for `disj_peaks`. Under Phase U the entry rule is
   uniform: every cvar atom and every term-var atom heads an entry.
2. **Consumption reorganization**: body-side part-of-footprint payments go
   through enclosing footprint entries via `sep_lock + sep_mono` instead of
   atomized entries; the covering pipeline (`SepCovered`,
   `TgtSplitCoveredOn`) shrinks to whatever transports remain — its main
   job (shepherding atoms through substitution) disappears because entry
   substitution is wholesale.
3. **Rebuilds** (the big item): `compile_subst_subtyp`'s interface —
   premise #5 (the ∀-modes atom-pair demand) disappears;
   `app_satisfy_bridge`; the `appPeaks` inventory; `CapySepCheck.compile`'s
   `sep_distinct` leaf re-targeted at footprint entries.
4. **Casualties/salvage**: sep-core lemmas (`Subcapt.cvar_of_le`, the
   SepCovered cores) survive; `CompileNarrow.lean` (node lemma, 9-lemma
   peak inventory, `compile_arrowLock_narrow`) retires *with its problem*
   — keep as reference until the new route is green, then delete.
5. **Effect on Preservation's app case**: `hLG` closes by construction
   (locks are transported, not recomputed — F.0's device delivers exactly
   identical-locks-under-narrowing); the 963 pin is deleted or
   trivialized; re-examine `hcompat`/`hcompatAl` (the ctxSub
   `Cy`-vs-latent exactness tension) — expected to relax, since footprint
   entries + `sep_mono` absorb exactly the `Cy ⊑ latent` slack; if not,
   fall back to a G-style actual-typed intermediate context.
6. **`Coherent.srcAligned`**: during this phase's design pass, run the
   death-by-F check — does the rebuilt pipeline stop emitting the
   `pack {cx} x` whose droppability obligation is false? If yes, the open
   ruling in Phase A moots; if no, Phase A decides the device.

Acceptance: fresh/abs/subtyp compilation green on the new manufacture;
`hLG`, 963, and the U-interim `CapySepCheck.compile` sorry gone; no new
sorries; srcAligned either dead or explicitly decided in Phase A.

### Phase F2 — Restoration: contravariant arrow domains

Today the source arrow subtyping rule is domain-invariant (same `T` both
sides, Capybara/TypeSystem/Core.lean:177-183) while the target has had full
contravariance all along (TypeSystem/Core.lean:153). It was disabled
because term-parameter stored types leak into lock manufacture
(`peaksVarBound` resolves them; cvar *bounds* never leak — which is why
`cpoly` kept full bound-contravariance via `consCVar_boundIrrel`). Phase F
removes exactly that leak, so contravariance becomes restorable:

- **cpoly layer**: bounds `⟦T2.cs⟧ ⊑ ⟦T1.cs⟧` match the target `Subbound`
  direction; body-under-changed-bound already solved (`consCVar_boundIrrel`).
- **arrow layer**: target rule already contravariant; `CapySubtyp.compile`
  recurses on domains.
- **lock layer**: parameter entries are symbolic ⇒ identical both sides
  (exact `sep_lock`); cs-entries differ by subcapture ⇒ `modal_modal` +
  `sep_mono` — machinery needed for latent widening regardless of domains.
  No new obligation *kind*.

Plan: state Phase F's interfaces domain-generically from the start, but
**land F green on invariant domains first**, then flip the source rule
here. Costs: source rule + inversion/transitivity repairs; watch whether
the compile invokes a source term-var *narrowing* lemma (`sep_sc`'s
peak-equivalence premise is the sensitive spot — source `peaks` stays
stored-type-resolving). DropWf covers the new domain premise automatically.
Target: unchanged.

### Phase F3 — Restoration: separation inheritance (source `sep_mono`)

*(The roots-vs-views species question that once lived here is dissolved by
Phase U; what remains is the inheritance restoration — independent and
still wanted.)*

Bound-cvar transparency (`sc_cvar : {εc} ⊑ D`) is retained under U, but
capture sets today cannot *inherit* separations along subcapture at all
(verified: `sep_sc` is peak-rigid via `EquivP`; no source
left-monotonicity). Semantically `C' ⊑ C ∧ C # X ⟹ C' # X` is
unimpeachable — and it covers what the U-fiat does not: facts against
arbitrary footprints `X` (term-var footprints, unions), not just sibling
cvars. Fix: add source `sep_mono` (left-monotonicity under `CapySubcapt`),
compiled by a one-rule mirror to target `sep_mono` + compiled subcapture.
The old design could not afford this (transported claims the frozen
atomized pipeline couldn't pay — `EquivP` was the fence); under footprint
locks it is nearly free. Safety: only shrinks the left side (cannot
conjure the `{ε c} # {ro c}` same-root pair from `sep_distinct`'s
mode-erasure note; cannot create drop atoms — DropWf polices those).

Sequencing: after F lands; independent of F2; the `CapySepCheck.compile`
induction gains one trivial case (do it while that proof is open).

## Phase A — App-case endgame

- Close the remaining app-case sorries under the new regime:
  `hcompat`/`hcompatAl`, the readonly replay (Preservation:449), and
  `app_use_covered` (UseCovered.lean:161).
- **`Coherent.srcAligned` (CoherenceMorphism.lean:588) — the ONE open
  design item (user ruling pending; F.6 may moot it).** It sits on the
  live app spine (Preservation.lean:122-124/:1236/:1287,
  SubtypCompile.lean:1187), so it sorryAx-taints the headline lemmas
  today.

  Anatomy (established 2026-07-04): the compiled arrow
  (TypeCompiler.lean:218-253) is the two-cpoly tower
  `[c][cx <: ⟦ann⟧](x : S^{cx}) → …`. The source arrow's own binder maps
  to the OUTER, *unbounded* cpoly (app instantiates it with `⟦D⟧`); `cx`
  is the inner, bounded one, absent from the source signatures — its
  source-level identity is **x-used-as-a-capture-atom** (the compiler
  compiles the self-refined domain `(T↑)^{εx}` under `x ↦ {εcx}`). It
  exists as a separate target binder because a stored type cannot mention
  its own binder (`x : S^{x}` is inexpressible in stored position) and
  because the target splits term substitution into capture instantiation
  (second `capp`, `cx := {εy}`) plus application. The gap: the body
  context stores `x` at the RAW annotation source-side while the compiled
  image is `{εcx}`, so stored-type-READING forms over a parameter —
  `fresh x`, `drop x`, pack-over-x — compile to obligations that are
  false for `cx` (access_only). Prohibition is NOT a fix: widening
  `{εcx}` to cx's bound and re-binding through a `letin` is sound and
  compiles green (`sc_cvar` dissolution), so the direct forms must be
  *aligned*, not banned.

  Candidate devices for the ruling:
  - **(α) death-by-F**: the F.6 check — the rebuilt footprint pipeline may
    stop emitting the false obligation altogether.
  - **(β) interface relaxation**: weaken `SrcAligned`
    (SubstLemmas.lean:410) from image-equality to subcapture
    (`image ⊑ ⟦T.captureSet⟧` — exactly what `Coherent.varLookup` already
    delivers for BOTH disjuncts); audit the consumers
    (Preservation.lean:122-124/:1236/:1287, SubtypCompile.lean:1187,
    OpenCVarSubtyp.lean:6842) for whether `⊑` suffices where `=` was
    used. Companion fact: the widening route rides source capture
    covariance, which exists for arrows only
    (Capybara/TypeSystem/Core.lean:177) — cells/readers/caps would need
    source twins of our four target covariance rules.
  - **(γ) the `S^{εc}` annotation idiom**: domains whose top-level capture
    is the arrow's own binder already make the direct forms fail (the
    binder is access-only AND `.unbound` — no bound to widen to, so even
    laundering is impossible), and the residual misalignment shrinks to
    `{εcx}` vs `{εc'}` — a trivial subcapture. Concretely-annotated
    domains remain the misaligned species, handled by (β) or by idiom/WF.
  - **(δ) honest pin**: true for real programs, uncertifiable in-system.
- Decide the non-app stub's status (out of the app-case scope; either close
  or mark as the next milestone). **The non-app milestone has a known
  research-grade prerequisite** (latent since the base): compiling
  `letin`/`letin_unpack` over consuming heads (`fresh`'s use is
  `D ∪ D.applyDrop`) targets rules that **kill** the continuation context,
  while the source continuation is typed unkilled. Needs a *syntactic*
  target kill-weakening lemma — "`HasType` survives killing `can_drop`
  peaks the use-set avoids" — which does not exist on core-capybara (only
  denotational transport, Denotation/Kill.lean). Plausible proof shape:
  kill flips authority to `.killed` with the bound intact; `sc_cvar`
  requires `.access_only`, so killed cvars never fed subcapture; the
  avoidance hypothesis is exactly source `seq_drop`'s DisjCheck.
- Hygiene: sweep bare `sorry` AND `#print axioms` for `sorryAx` across
  `Compilation/` + `Capybara/` before declaring green.
- Update `notes/` + memory; retire `notes/app-case-design-decision.md`
  (already banner-marked resolved).

## Phase L — Surface consumer lambdas

*Design agreed 2026-07-03 (user proposal, rules drafted).*

Surface forms: type `.consumer T1 cs E` (`T1 : CapyTy .capt (s,C)` under
the implicit **witness** binder; `E : CapyTy .exi s` at the OUTER scope —
the witness must not leak into the result); expression `.consume_abs T1 e`;
elimination **reuses `.app x y`** (type-directed dispatch on disjoint
constructors `.arrow`/`.consumer` — no ambiguity), with the compilation
**synthesizing the pack** and its evidence.

Design highlights:
- **Quantifier duality**: arrow = implicit ∀ self-cvar (app instantiates);
  consumer = implicit ∃ witness cvar (app packs; body sees it abstract).
  Same domain shape, dual elimination.
- **Un-phantomable consumption**: the drop-right is conveyed by the type
  CONSTRUCTOR, not a mode annotation — subsumption cannot conjure a
  `.consumer` from an `.arrow`. Complements DropWf (which bans the unsound
  drop-latent route); the body's `{drop C}` use is DropWf-valid because
  the witness binder is `can_drop`.
- **Intro rule = `letin_unpack`'s binder block as a lambda**
  (Core.lean:374-377 pattern verbatim: `(Γ,C[.can_drop]<:.unbound ε),x:T1`
  context, `cs↑↑ ∪ {ε C} ∪ {drop C}` use-set, `implicit_cvar` rename,
  double-lifted result) + the `fresh`/`abs` witness-WF premise family.
- **Elim rule premises** = pack evidence (D closed, access-only,
  `droppable Γ D`) + `CapyDisjCheck Γ D {εx}` (consumed footprint vs the
  consumer's own captures) + the app-style argFit premise
  `y : T1[openCVar D]`. NO `NoPseudoPeak` premises (L lands after F,
  which deletes the device). **No `interfere_set` SepCheck** — the core
  consumer is kill-based, not lock-based: witness-vs-closure is the
  DisjCheck ({εx} resolves to cs), everything else is dead by the kill
  clause. Conclusion use-set is **fresh-style** `{εx} ∪ D ∪ D.applyDrop`
  (var-style `{εy}` cannot match the compiled pack's concrete use; the
  explicit `D.applyDrop` is what lets the enclosing letin's SeqComp
  protect the continuation).
- **Compilation**: intro → core `consumer` with kill set
  `X := ambient droppables \ cs` (kill-clause true by construction);
  elim → `consumer_app ⟦x⟧ (pack ⟦D⟧ ⟦y⟧)` (n = 1, `PairwiseSep`
  trivial; `accessible` rides Phase R's liveness repair). The SeqComp
  discharge is more than one step: the `D` leg via `seq_access_only`, the
  `D.applyDrop` leg via `seq_sep` — which takes a **SepCheck**, so it
  needs the DisjCheck→SepCheck embedding (Phase R work item) + drop-mode
  adaptation — assembled by `seq_union`. The argFit premise reuses Phase
  F's checked-instantiation device — one device serves app, U-capp, and
  consume-app.
- **Known v1 expressiveness limit** (accepted — state it in the rule's
  doc): the `CapyDisjCheck Γ D {εx}` premise is derivable only when *all*
  the closure's peaks are droppable (`disj_droppable` is DisjCheck's only
  base pair rule), so a consumer whose closure captures a non-droppable
  root or an ro capability can never be applied — while the target
  receiver (`seq_sep` = full SepCheck incl. `sep_lock`) is strictly more
  permissive. If it bites, the premise upgrades to a `CapySepCheck`
  compiled straight into `seq_sep`.
- Mechanical extensions: `CapySubtyp.consumer` (covariant cs/E, E with no
  binder gymnastics; domain invariant until F2), `interfere_set` case
  (`cs ∪ dropCVar T1.captureSet ∪ E.interfere_set`), DropWf/Wf cases,
  `tySize`.

Risks/deferred: kill-context transport (body TYPES may statically mention
killed cvars — how the core treats static references to killed entries is
unverified; main compilation risk); non-dependent results (E independence)
accepted for now; extensions that fit smoothly later: direct-package
application (`y` already `.exi`-typed), multi-witness consumers (n > 1,
`PairwiseSep` = the U-flavored pairwise check), dependent results.

Sequencing: after the green baseline (Phase A); needs R (core consumer
exists on the new base) and benefits from W (DropWf validates the witness
pattern) and F (the shared argFit device); independent of F2/F3.

## Deferred (explicitly out of scope)

- The one-rule target extension (`drop×ε` mode-lowering separation) — moot
  once DropWf lands; recorded as considered-and-unnecessary.
- `core-capybara-relax-droppability` — discarded experiment; do not
  resurrect.

## Sequencing and risk

**Order: R → W+U (bundled) → F → A → L.** R first (user directive;
everything else builds on the new core). W and U are **bundled**: do both
phases' rule surgery first, then ONE combined regularity pass (threading
W's regularity before U's rule edits would rework it). W+U before F
because F's rebuilt interfaces should be stated once, with the WF
hypotheses and the unified-parameter semantics available — though they are
logically independent of F's design-level work, which can start in
parallel after R if bandwidth allows. Cross-checked: U's checks do NOT
need F3's source `sep_mono` (`sep_sc` + `EquivP` suffices — resolution is
peak-preserving); R depends on nothing scheduled later.

Gates before F's code work: the F.0 transport design written on paper
(the device is ruled; the write-up is the entry criterion), and the
U-vs-F2 interaction argument (does payment-covers-consumption survive
contravariant shrinking of interfere-relevant annotations? no
counterexample found; argument not yet written) recorded as part of F2's
entry criteria. The srcAligned device (Phase A) needs a user ruling
unless F.6's death-by-F check moots it — run that check early in F.

Biggest risks: R's Fundamental.lean merge + five re-proofs in the new
Kripke model (real proof work, not mechanics); F's `compile_subst_subtyp`
rebuild (the single biggest mechanical item, but it *replaces* the hardest
existing debt rather than adding to it); F.0's substitution-compatibility
lemma (the transported grouping's residual obligation); the non-app
milestone's kill-weakening lemma (Phase A; research-grade, plausible proof
shape); the srcAligned ruling (design risk, not proof risk). W+U
regularity is standard infrastructure.

Working discipline: lean4check (never `lake build` as a check), no axioms
(theorem + sorry), `#print axioms` sweeps before any "done" claim, opus
subagents with single-file ownership when parallelizing.
