# Roadmap — closing `fresh`

**Goal.** Discharge the `var` sorry in the `fresh` case (`Compilation/Preservation.lean:253`).
Path: **B2c** (`CapyTy.compile_subst_subtyp`, `OpenCVarSubtyp.lean`) → **var wiring**.

> **⚠ CORRECTION (2026-06-28): NOT independent of K1.**  B2c's FORWARD direction is provable
> (`cpoly` forward DONE — the full hsep crux).  But its BACKWARD direction has the SAME injected-lock
> instability as K1, now under substitution-MERGING (see `subtyp-roadmap.md` ★ K1′).  `poly`/`arrow`
> FORWARD need the contravariant backward (`ihS.2`/`ihT1.2`), so the `var` wiring for any opened type
> containing capture-polymorphic functions in contravariant position is gated on the K1 lock-design
> decision.  The cpoly/leaf fragment is unblocked.  STATUS: `cpoly` forward 0-sorry; `cpoly` backward
> structured (1 sorry = the gap `satB`); `poly`/`arrow` documented-blocked.

**Legend:** ✅ done · 🔨 to build · ⬜ not started.

---

## B2c — `compile_subst_subtyp` (`⟦T[σ]⟧ <: ⟦T⟧[σt]`, both directions)

Signature now threads (after `T.PureBounds`): `TgtPairDroppable` · `SrcAligned ×2` ·
`capyCtx.IsClosed ×2` · `Subst.IsClosed σt` · `srcCtx.VarsClosed ×2` · `coreCtx.IsClosed` ·
`CapySubst.IsClosed σ`.  (Discharge all of these at the `fresh` site — see wiring.)

- ✅ Leaf/structural cases: `top unit bool cap cell typ exi tvar` (8/11).
- ✅ **cpoly forward — all but hsep:**
  - structure: `Subtyp.cpoly Subbound.refl Subcapt.refl (Subtyp.typ (trans through .modal Cf_R Ψ_L E_R))`.
    Absorb `Cf_L=Cf_R` with `Subtyp.modal (hCf ▸ Subcapt.refl)` (NOT `rw [hCf]`).
  - 4 closedness sub-goals (`Ty.IsClosed.modal`/`peakSepCtx_isClosed`/`*.is_closed_subst`).
  - body: `ihE` at RAW lock-pushed `succ`-renamed ctxs + `convert hle using 2` +
    `compile_rename` + `Ty.weaken_subst_comm_base`.
  - hkind (mutability): `mutabilityCtx_subst_here` + `cases cb`/`cases m`.
- 🔨 **hsep (cpoly fwd) — THE CRUX.** See below.
- ⬜ cpoly **backward** — mirror of forward (body via same option-(b); hsep dispatch reversed).
- ⬜ **poly** — like cpoly w/o the cb; `SrcAligned.consTVar` ready; reuses body + hsep dispatch.
- ⬜ **arrow** — body via option-(b) **+ domain contravariance** (both IH dirs) **+** build
  `SrcAligned.consVar` **+** `compile_eq_of` for the `consVar .top`-vs-real-type body-ctx bound.

### 🔨 hsep — cross-context peak tracing (the one genuinely-new lemma, ~150 lines)
Entry (✅, in source): `simp only [ModalCtx.rename]; rw [← peakSepCtx_rename];
obtain ⟨⟨c1,hc1,hC1⟩,⟨c2,hc2,hC2⟩⟩ := peakSepCtx_HasTwoDistinct hdist`.
Goal: `SepCheck (push_lock Ψ_R) C1 C2` for distinct peaks `c1,c2` of `cs[σ]`, where
`Cᵢ = ⟦peakItem(peaks Γsub (cs[σ])) cᵢ⟧ sc'` and `Ψ_R = peakSepCtx(peaks Γorig cs)[σt]`.

**Build a tracing lemma**: each peak `c ∈ peakCvars(peaks Γsub (cs[σ]))` traces to an origin
`d ∈ peakCvars(peaks Γorig cs)` under `σ` (subst can SPLIT one `d` into many `c`).  Then dispatch:
- **distinct origins** `d1≠d2` → `sep_lock` via `peakSepCtx_subst_HasTwoDistinct_of` (+ `sep_mono`
  /`sep_symm` to absorb per-peak access modes).
- **same origin** (split: both from one `D = σ.cvar d`) → `sep_droppable` from `hdrop : TgtPairDroppable`.

Have: `peaks_subst_mem` (single-ctx atom classifier), `compile_peaks_subst` (whole-SET keystone),
`peakSepCtx_subst`/`_HasTwoDistinct_of` (substituted-lock converse).  Missing: the per-individual-peak
cross-context correspondence + split classification.

---

## var wiring 🔨  (after B2c is green)
- Instantiate B2c (LE direction) at `openCVar`: `SubstCompat.openCVar`✅, `SubstTvarCompat.openCVar`✅,
  `TgtPairDroppable` from `droppable Γ Df`, and the closedness/`CapySubst.IsClosed` premises from
  `Df` closed (`fresh` carries `D.IsClosed`).  Still need `Tbody.IsClosed`/`PureBounds`
  (regularity lemma "looked-up types in a closed ctx are closed/pure-bounded", or a source premise).
- Assemble: `HasType.var ∘ HasType.subtyp ∘ Subtyp.self_refine ∘ B2c`.

## Reusable builders (all ✅ green)
`compile_eq_of` · `compile_rename`/`compile_mapsTo` · `compile_subst`/`compile_peaks`/`compile_peaks_subst`
· `SrcAligned.{weakenTarget,consCVar,consTVar}` (consVar ⬜) · `SubstCompat/SubstTvarCompat.{openCVar,
weakenConsCVar,weakenConsTVar,weakenTarget}` · `TgtPairDroppable.{lift,liftTVar,liftLock}` ·
`mutabilityCtx_subst_here` · `peakSepCtx_isClosed`/`compile_isClosed`/`*.is_closed_subst`.
