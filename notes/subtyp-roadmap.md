# Roadmap — `CapySubtyp.compile` (subtyping preservation)

**Goal.** Prove `CapySubtyp.compile` (`SubtypCompile.lean`): source subtyping ⟹ target subtyping.
**Status:** `top refl trans tvar typ exi` ✅ (closedness threaded).  `arrow poly cpoly` = 3 sorries
= **K1**, a FUNDAMENTAL design gap (NOT missing infrastructure).  Independent of `fresh`.

---

## ★ K1 — the injected separation lock (needs a HUMAN DESIGN decision)

**The obligation reduces cleanly.**  Compiling `CapySubtyp (∀cs1…) (∀cs2…)` gives, via
`Subtyp.{poly,cpoly}` (bound) + `Subtyp.typ` + `trans` through `.modal cs2 Ψ1 E2` + `Subtyp.modal`,
a single premise:  `Satisfy (Γt.push_lock Ψ2) (Ψ1.rename succ)`
where `Ψ1 = peakSepCtx(peaks cs1)`, `Ψ2 = peakSepCtx(peaks cs2)`.

**Why it's underivable.**  `Ψ1` demands *every two distinct peaks of `cs1` are separate*.
`CapySubcapt cs1 cs2` does NOT give this — subcapture can MERGE distinct peaks.
**Counterexample** (in the `SubtypCompile.lean` K1 comment):
`c₁,c₂ : [access_only] <: .bound{d}`, `cs1={c₁,c₂}`, `cs2={d}` — `CapySubcapt` derivable, but the
target needs `SepCheck (push {⟦d⟧}) ⟦c₁⟧ ⟦c₂⟧`, which **no rule produces** (`sep_lock` needs 2 lock
items; `sep_droppable` needs `can_drop`, they're `access_only`; `sep_ro` needs `ro`; `sep_mono` →
`d⊥d`).

**Root cause.**  The compiler **injects** the lock: target `wrap` *pushes* `Ψ` for the body with no
check (discharged at `unwrap`), but source `abs`/`tabs`/`cabs` do NOT sep-check captures (Capybara
separation is a USE-site check: `app`/`par`).  So there is no source well-formedness to thread.

## Decision (pick one) — reshapes the lock; settle BEFORE finishing B2c (reasons about same lock)
- (a) **Weaken the function-type lock** to only subcapture-stable separations.
- (b) **Sep-check captures at source `abs`/`tabs`/`cabs`** (definition-site separation).
- (c) **Change the modal-lock subtyping rule** (`Subtyp.modal_modal`) — e.g. allow `modal Ψ1 E <:
  modal Ψ2 E` when `Ψ1` is *unsatisfiable* (so the body is dead), which is exactly the merged
  case below.

## ★ K1′ — B2c BACKWARD is the SAME gap, under substitution-MERGING (confirmed 2026-06-28)
`CapyTy.compile_subst_subtyp` (`OpenCVarSubtyp.lean`) was thought K1-independent.  It is NOT.
- **Forward** `⟦T[σ]⟧ <: ⟦T⟧[σt]` goes *weak-lock → strong-lock* (`modal_modal` needs the strong
  context to satisfy the weak requirement — **HOLDS**).  `cpoly` forward is **fully proven** (the
  ~270-line hsep dispatch: split→`sep_droppable`, distinct→`sep_lock`).  cpoly avoids contravariance
  because its capture bound compiles to an EQUALITY (`Subbound.refl`).
- **Backward** `⟦T⟧[σt] <: ⟦T[σ]⟧` goes *strong → weak* and **FAILS** when `σ` MERGES two distinct
  origin peaks `d1≠d2` into overlapping target captures (sharing cvar `x`).  `Ψ_R.HasTwoDistinct`
  is POSITIONAL (`SepCtx.lean:40`, no `C1≠C2` premise), so it still yields the pair `⟦d1⟧[σt],
  ⟦d2⟧[σt]` — both ∋ `x` — and `SepCheck _ (…x…) (…x…)` is unsatisfiable.  Located at
  `OpenCVarSubtyp.lean` `cpoly` `case satB`.
- **Merging is realizable at `openCVar`**: `∃c. (X ->{c,w} Y)` packed with `Df = {w}` opens to
  `X ->{w} Y`; the substituted original lock asserts the impossible `w ⊥ w`.  Semantically the
  original modal is then UNINHABITABLE (`<:` anything), but `modal_modal` can't see that — pure
  syntactic incompleteness ⇒ option (c).
- **Cascade**: `poly` forward needs `ihS.2` (type-bound contravariance), `arrow` forward needs
  `ihT1.2` (domain contravariance) — both pull the merging-backward into the forward recursion.  So
  `poly`/`arrow` (either direction) and the `fresh` `var` wiring are ALL gated on this decision.
  Only the cpoly/leaf fragment (no contravariant capture-polymorphism) has a sorry-free forward.
- This is precisely the codebase's known **"function-typed-variable refinement"** gap
  (`Preservation.lean:18`).

## Bug flag (independent)
`sep_distinct` (`Capybara/TypeSystem/Core.lean:112`): both `LookupCVar` premises (114–115)
reference `c1`; the 2nd should be `c2`.

## Deferred (same model mismatch)
Source `CapySepCheck → SepCheck` bridge: source separates on `.unbound` bounds; target separates
on `can_drop` authority or a lock.  Blocked until the lock model is decided.
