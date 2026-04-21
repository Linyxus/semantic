# Build Warnings Checklist

Snapshot taken 2026-04-21 from `lake build`. Total: **6752 warnings**, zero errors.

Tick a file off once `lake build` produces no warnings for it. Run `lean4check` during work; finish a module with a fresh `lake build` to confirm the count dropped.

## Category totals

| Count | Category | Fix recipe |
|---:|---|---|
| ~6100 | **flex_simp** — `simp [...]` / `simp [...] at h` modifying goal flexibly | Replace with `simp only [...]` (use `simp?` suggestion) or `suffices`. Most are mechanical. |
| 302 | **empty_line** — blank line inside a `theorem`/`def` command | Delete the empty line or add a `--` comment. |
| 129 | **show_tactic** — `show` used to rewrite goal form, not state it | Replace with `change` or `conv` when doing definitional rewriting; keep `show` only for human-readable intermediate states. |
| 83 | **unused_simp_arg** — lemma in `simp [...]` that never fires | Drop it. |
| 43 | **line_too_long** — >100 chars | Wrap. |
| 22 | **unreachable_tactic** — tactic after the goal closes | Remove. |
| 22 | **try_this** — linter offers a replacement (usually `intro`) | Apply the suggestion. |
| 16 | **no_op_tactic** — `constructor` / `assumption` that does nothing | Remove. |
| ~8 | **chain_semicolon** — `tac1 <;> tac2` where `(tac1; tac2)` suffices | Rewrite. |

The `flex_simp` warnings dominate. The cheapest win is to sweep one file at a time with `simp?` hints (Lean already emits them as `info` messages next to each warning).

## Strategy

- Work bottom-up per module: Syntax → Substitution → Semantics → Denotation → TypeSystem → Fundamental → Safety.
- **CC and CCPrec are near-mirror copies.** Counts match file-for-file. Fix CC first, then replay in CCPrec.
- Do `show` → `change` sweeps alongside `simp only` conversions in the same file.
- Verify with `lean4check` per file; `lake build` for a module at the end.
- **FORBIDDEN shortcut:** `set_option linter.flexible false` (or any file/section-scoped linter opt-out). Previous run tried this; it was rejected. Every warning must be fixed mechanically.

## Run log

- 2026-04-21: Pass 1. Stlc cleaned properly (96 → 0). Other 5 modules had agents that took the `set_option linter.flexible false` shortcut across ~40 files; all reverted.
- 2026-04-21: Pass 1b. Codex per-module (gpt-5.4 xhigh, write). Results: Fsub 253 → 0 ✅. CC 1774 → 699 (6/11 files clean). CCPrec 1765 → 1723 (2/11 — budget exhausted early). Consume 1338 → 1098 (5/13). ModalCapybara 1526 → 1156 (9/14).
- 2026-04-21: Pass 2. Per-file Codex on 5 biggest files. Results: CCPrec/Fundamental 563 → 0 ✅. ModalCapybara/Fundamental 419 → 0 ✅. CCPrec/Denotation/Core 456 → 128. Consume/Fundamental 369 → 106. CC/Fundamental 488 → 192 (Codex dropped `intro m' hsubsumes` in `sem_subtyp_trans` capt/exi cases; manually restored). Total warnings 4676 → 2938.
- 2026-04-21: Pass 3. Per-file Codex on 5 next biggest. Results: CCPrec/Semantics/Heap 231 → 0 ✅. Consume/Semantics/Heap 243 → 0 ✅. ModalCapybara/Semantics/Heap 280 → 0 ✅. Consume/Denotation/Core 294 → 0 ✅. ModalCapybara/Denotation/Core 349 → "31" but Codex introduced 103 errors and falsely reported `errors_introduced: 0` — fully reverted. Total warnings 2938 → 2009.
- 2026-04-21: Pass 4 dispatched with strict error-check contract (5 parallel).
  - Consume/Fundamental: 106 → 82, 0 errors.
  - ModalCapybara/Denotation/Core: 349 → 149, 0 errors (strict prompt worked; no regression).
  - CCPrec/Substitution: 149 → 23, 0 errors.
  - CC/Fundamental: 192 → 120, 0 errors.
  - CCPrec/Denotation/Core: in-flight (last report: 2 warnings left).
  - Audit revealed pass 3's Consume/Denotation/Core "clean" claim was false — file actually has 119 warnings; status reverted to incomplete in checklist.
  - Total warnings 2009 → 1330 (80% reduction from original 6752).

---

## Stlc (96 warnings) — ✅ DONE

- [x] `Semantic/Stlc/Syntax.lean` — 5 (flex_simp ×5)
- [x] `Semantic/Stlc/Substitution.lean` — 5 (flex_simp ×5) — non-mechanical: `Exp.weaken_subst_comm` and `Exp.subst_comp` abs cases needed `congrArg`/`rw` rewrites because `simp only` couldn't strip outer congruence.
- [x] `Semantic/Stlc/SmallStep/Eval.lean` — 4 (empty_line ×4)
- [x] `Semantic/Stlc/SmallStep/Soundness.lean` — 36 (flex_simp ×34, no_op ×1, unreachable ×1) — `first | assumption | constructor` → `assumption`; one long line wrapped.
- [x] `Semantic/Stlc/BigStep/Soundness.lean` — 46 (flex_simp ×44, no_op ×1, unreachable ×1) — same `first | ...` fix.

## Fsub (253 warnings) — ✅ DONE (Codex, 2026-04-21)

- [x] `Semantic/Fsub/Heap.lean` — 1
- [x] `Semantic/Fsub/Syntax.lean` — 14 — non-mechanical: `Ty.rename_id`, `Exp.rename_id`, `Ty.rename_comp`, `Exp.rename_comp` — wildcard simp branches expanded to explicit `congrArg`/`rw` branch proofs.
- [x] `Semantic/Fsub/Substitution.lean` — 20
- [x] `Semantic/Fsub/Eval/BigStep.lean` — 2
- [x] `Semantic/Fsub/Denotation/Core.lean` — 74 — non-mechanical: `val_denot_is_transparent` singleton case restructured with direct case analysis.
- [x] `Semantic/Fsub/Denotation/Rebind.lean` — 12 — non-mechanical: `rebind_val_denot` tvar and singleton cases rewritten to direct equality proofs.
- [x] `Semantic/Fsub/Denotation/Retype.lean` — 15
- [x] `Semantic/Fsub/Soundness.lean` — 115 — non-mechanical: `sem_typ_app` replaced broad `simp at *` with an explicit equality-on-substituted-argument rewrite.

Verified: `lake build Semantic.Fsub` → 0 warnings, 0 errors.

## CC (1774 warnings; 390 remaining)

- [x] `Semantic/CC/Syntax/Ty.lean` — 16
- [x] `Semantic/CC/Substitution.lean` — 149
- [x] `Semantic/CC/Semantics/BigStep.lean` — 47
- [x] `Semantic/CC/Semantics/Props.lean` — 43
- [x] `Semantic/CC/Semantics/Heap.lean` — 231 — non-mechanical: `Cell.subsumes_trans`, `resolve_monotonic` restructured.
- [ ] `Semantic/CC/Denotation/Core.lean` — 9 left
- [ ] `Semantic/CC/Denotation/Rebind.lean` — 80 left (Codex reverted; direct `simp only` swap needs proof-shape change)
- [ ] `Semantic/CC/Denotation/Retype.lean` — 109 left (not yet attacked in pass 2)
- [x] `Semantic/CC/TypeSystem/BasicProps.lean` — 26
- [ ] `Semantic/CC/Fundamental.lean` — 120 left (pass 4 reduced 192 → 120; multiple restructures in `sem_typ_*` / `sem_subtyp_arrow`)
- [ ] `Semantic/CC/Safety.lean` — 13 left

## CCPrec (1765 warnings; 832 remaining)

- [x] `Semantic/CCPrec/Syntax/Ty.lean` — 16
- [ ] `Semantic/CCPrec/Substitution.lean` — 23 left (pass 4 reduced 149 → 23; `Ty.subst_id`, `Exp.subst_id`, `Ty/Exp.subst_asSubst`, closedness lemmas restructured with `congrArg`/`suffices`)
- [ ] `Semantic/CCPrec/Semantics/BigStep.lean` — 47 (pass 1 reverted own edits)
- [ ] `Semantic/CCPrec/Semantics/Props.lean` — 43
- [x] `Semantic/CCPrec/Semantics/Heap.lean` — 231 → 0 ✅ (pass 3; 4 restructures incl. `Cell.subsumes_trans`, `resolve_monotonic`, `reachability_of_loc_monotonic`, `update_mcell_subsumes_compat`)
- [ ] `Semantic/CCPrec/Denotation/Core.lean` — 2 left (pass 4 in-flight almost done, reduced 128 → 2)
- [ ] `Semantic/CCPrec/Denotation/Rebind.lean` — 80
- [ ] `Semantic/CCPrec/Denotation/Retype.lean` — 107
- [x] `Semantic/CCPrec/TypeSystem/BasicProps.lean` — 26
- [x] `Semantic/CCPrec/Fundamental.lean` — 563 → 0 ✅ (pass 2; 7 non-mechanical restructures)
- [ ] `Semantic/CCPrec/Safety.lean` — 47

## Consume (1338 warnings; 966 remaining)

- [x] `Semantic/Consume/Syntax/Context.lean` — 5
- [x] `Semantic/Consume/Syntax/Ty.lean` — 8
- [x] `Semantic/Consume/Syntax/Exp.lean` — 9
- [x] `Semantic/Consume/Substitution.lean` — 170
- [x] `Semantic/Consume/Semantics/BigStep.lean` — 48
- [ ] `Semantic/Consume/Semantics/Props.lean` — 35
- [x] `Semantic/Consume/Semantics/Heap.lean` — 243 → 0 ✅ (pass 3; 4 restructures)
- [ ] `Semantic/Consume/Denotation/Core.lean` — 119 left (pass 3 Codex falsely reported "clean" — likely stale cache; real count is 119. File was edited: 310+/163- diff. Needs a follow-up pass.)
- [ ] `Semantic/Consume/Denotation/Rebind.lean` — 28
- [ ] `Semantic/Consume/Denotation/Retype.lean` — 59
- [ ] `Semantic/Consume/TypeSystem/BasicProps.lean` — 30
- [ ] `Semantic/Consume/Fundamental.lean` — 82 left (pass 4 reduced 106 → 82; no extra restructures)
- [ ] `Semantic/Consume/Safety.lean` — 40

## ModalCapybara (1526 warnings; 737 remaining)

- [x] `Semantic/ModalCapybara/Syntax/Context.lean` — 6
- [x] `Semantic/ModalCapybara/Syntax/Ty.lean` — 8
- [x] `Semantic/ModalCapybara/Syntax/Exp.lean` — 11
- [x] `Semantic/ModalCapybara/Syntax/SepCtx.lean` — 9 — non-mechanical: `SepCtx.HasTwoDistinct.rename_inv` needed explicit `cases`/`injection` in place of `simp only`.
- [x] `Semantic/ModalCapybara/Substitution.lean` — 182 — non-mechanical: several sites needed `congrArg` / direct `rw [ih1, ih2]` and no-op removals.
- [x] `Semantic/ModalCapybara/Semantics/BigStep.lean` — 52 — non-mechanical: boolean/subsumption case splits.
- [x] `Semantic/ModalCapybara/Semantics/Props.lean` — 35 — non-mechanical: `Memory.extend_heapval_reachability_irrel` rewritten with `cases`; `step_lift` needed `change` steps after narrowing `simp`.
- [x] `Semantic/ModalCapybara/Semantics/Heap.lean` — 280 → 0 ✅ (pass 3; 3 restructures)
- [ ] `Semantic/ModalCapybara/Denotation/Core.lean` — 149 left (pass 4 re-attempt reduced 349 → 149 with 0 errors; 8 non-mechanical restructures)
- [x] `Semantic/ModalCapybara/Denotation/Rebind.lean` — 33
- [ ] `Semantic/ModalCapybara/Denotation/Retype.lean` — 68
- [x] `Semantic/ModalCapybara/TypeSystem/BasicProps.lean` — 34
- [x] `Semantic/ModalCapybara/Fundamental.lean` — 419 → 0 ✅ (pass 2; 3 non-mechanical restructures: `sem_subtyp_exi`, `sem_typ_unpack`, `sem_typ_unwrap`)
- [ ] `Semantic/ModalCapybara/Safety.lean` — 40

---

## Verification

After finishing a module, confirm with:

```sh
lake build 2>&1 | grep -c "^warning:"
```

The number should drop by the sum of the ticked files. A non-matching delta usually means:
- downstream files re-emitted warnings from the edited one (unlikely for these linters),
- or a `simp only` fix removed a lemma that another file relied on — rebuild will surface it as an error.
