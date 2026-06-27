import Semantic.CoreCapybara.Compilation.Coherence
import Semantic.CoreCapybara.Compilation.SubstLemmas
import Semantic.CoreCapybara.Compilation.SubtypCompile
open CoreCapybara
namespace Compilation

/-!
# Type-preserving term compilation

The central theorem of the translation: every well-typed Capybara term compiles
to a well-typed CoreCapybara term.  It is phrased as an existence statement
(`∃ e', HasType …`) proven by induction on the source typing derivation
`CapyHasType`; the witness `e'` is the compiled term, built case by case.

This is a WORK IN PROGRESS scaffold: the trivial cases (`unit`/`btrue`/`bfalse`)
are discharged; the remaining cases are left as `sorry` and filled in
incrementally.  See [[project_capybara_translation]] for the per-case plan and
the one genuine design gap (function-typed-variable refinement).
-/

/-- **A variable refined to its own singleton subtypes its declared type.**  For
    `bv : T'` in the target, `T'` with its top capture set narrowed to `{bv}` is a
    subtype of `T'`.  Holds uniformly: `{bv} <: T'.captureSet` by `sc_var`, lifted
    through each former's covariant capture rule (`arrow`/`poly`/`cpoly`/`modal`
    structural; `cell`/`reader`/`cap` via the dedicated covariance rules). -/
theorem Subtyp.self_refine {s : Sig} {Γ : Ctx s} {bv : BVar s .var} {T' : Ty .capt s}
    (h : Γ.LookupVar bv T') :
    Subtyp Γ (T'.refineCaptureSet (.var (.M .epsilon) (.bound bv))) T' := by
  have hsc : Subcapt Γ (.var (.M .epsilon) (.bound bv)) T'.captureSet := Subcapt.sc_var h
  cases T' with
  | top => exact Subtyp.refl
  | tvar X => exact Subtyp.refl
  | unit => exact Subtyp.refl
  | bool => exact Subtyp.refl
  | cap cs => exact Subtyp.cap hsc
  | cell cs => exact Subtyp.cell hsc
  | reader cs => exact Subtyp.reader hsc
  | arrow A cs B => exact Subtyp.arrow Subtyp.refl hsc Subtyp.refl
  | poly S cs B => exact Subtyp.poly_cap hsc
  | cpoly cb cs B =>
    refine Subtyp.cpoly ?_ hsc Subtyp.refl
    cases cb with
    | unbound => exact Subbound.top
    | bound C => exact Subbound.capset (Subcapt.sc_elem CaptureSet.Subset.refl)
  | modal cs Ψ E => exact Subtyp.modal hsc Subtyp.refl

/-- **Self-capture refinement vanishes under compilation.**

    With the `Coherent` invariant `⟦xv⟧ = ⟦T.captureSet⟧`, the var rule's refined
    type `T^{xv}` compiles to *exactly* `⟦T⟧`: the refined capture field `{xv}`
    compiles back to `⟦T.captureSet⟧`, the value it replaced.  For functions this
    keeps the body lock faithful (the latent requirement `⟦cs⟧`, never understated)
    — which is what dissolves the old function-typed-variable design gap.

    The `arrow`/`poly`/`cpoly` cases additionally need the compiled lock `W` and
    its separation context `Ψ` to coincide between `{xv}` and `cs`; both follow
    from `compile`/`peaks` commuting with the capture image (the latter from
    `peaks Γ {xv} = peaks Γ T.captureSet`).  This is now a MECHANICAL commutation
    — the design gap is resolved — left as a scoped TODO. -/
theorem CapyTy.compile_refine_self {s1 s2 : Sig} {T : CapyTy .capt s1}
    {ctx : CompilerCtx s1 s2} {xv : BVar s1 .var}
    (hsrc : ctx.srcCtx.lookupVar xv = CaptureSet.compile T.captureSet ctx.srcCtx)
    (hcapy : ctx.capyCtx.LookupVar xv T) :
    CapyTy.compile (T.refineCaptureSet (.var (.M .epsilon) (.bound xv))) ctx
      = CapyTy.compile T ctx := by
  -- the var's capture image `⟦{xv}⟧` is its declared latent `⟦T.captureSet⟧`
  have hxv : CaptureSet.compile (.var (.M .epsilon) (.bound xv)) ctx.srcCtx
      = CaptureSet.compile T.captureSet ctx.srcCtx := by
    simp only [CaptureSet.compile, hsrc, CaptureSet.applyAccess_M, CaptureSet.applyMut_epsilon]
  -- `peaks {xv} = peaks T.captureSet` (faithful separation context)
  have hpk : CapyCaptureSet.peakset ctx.capyCtx (.var (.M .epsilon) (.bound xv))
      = CapyCaptureSet.peakset ctx.capyCtx T.captureSet := by
    apply CapyCaptureSet.peakset_congr
    rw [CapyCaptureSet.peaks, CapyCaptureSet.peaksVarBound_eq_captureSet hcapy]
  cases T with
  | top => simp only [CapyTy.refineCaptureSet]
  | tvar X => simp only [CapyTy.refineCaptureSet]
  | unit => simp only [CapyTy.refineCaptureSet]
  | bool => simp only [CapyTy.refineCaptureSet]
  | cap cs =>
    simp only [CapyTy.captureSet] at hxv
    simp only [CapyTy.refineCaptureSet, CapyTy.compile, hxv]
  | cell cs m =>
    simp only [CapyTy.captureSet] at hxv
    cases m <;> simp only [CapyTy.refineCaptureSet, CapyTy.compile, hxv]
  | poly S cs E =>
    simp only [CapyTy.captureSet] at hxv hpk
    have hCf : CaptureSet.compile (.var (.M .epsilon) (.bound xv))
          (SrcCtx.weaken (k := Kind.tvar) ctx.srcCtx)
        = CaptureSet.compile cs (SrcCtx.weaken (k := Kind.tvar) ctx.srcCtx) := by
      unfold SrcCtx.weaken
      rw [CaptureSet.compile_rename, CaptureSet.compile_rename, hxv]
    -- only the modal lock `W` and (via `hpk`) the separation `Ψ` differ; `congr`
    -- discharges the residual lock equality with `hCf` from context.
    simp only [CapyTy.refineCaptureSet, CapyTy.compile, hpk]
    repeat' congr 1
  | cpoly cb cs E =>
    simp only [CapyTy.captureSet] at hxv hpk
    have hCf : CaptureSet.compile (.var (.M .epsilon) (.bound xv))
          (SrcCtx.weaken (k := Kind.cvar) ctx.srcCtx)
        = CaptureSet.compile cs (SrcCtx.weaken (k := Kind.cvar) ctx.srcCtx) := by
      unfold SrcCtx.weaken
      rw [CaptureSet.compile_rename, CaptureSet.compile_rename, hxv]
    -- only the modal lock `W` and (via `hpk`) the separation `Ψ` differ; `congr`
    -- discharges the residual lock equality with `hCf` from context.
    simp only [CapyTy.refineCaptureSet, CapyTy.compile, hpk]
    repeat' congr 1
  | arrow T1 cs E =>
    simp only [CapyTy.captureSet] at hxv hpk
    simp only [CapyTy.refineCaptureSet, CapyTy.compile]
    set ctxL := (ctx.weakenTarget.weakenTarget.weakenTarget.consCVar (.unbound .epsilon)
      (.there (.there .here))).consVar T1 (some .here)
      (.cvar (.M .epsilon) (.there .here)) with hctxL
    -- the modal lock `W` agrees between `{xv}` and `cs`.  The two source
    -- weakenings of the lock field peel through the lock's `var`/`cvar` `cons`es
    -- via `compile_lock_field_congr`; its hypothesis is `hxv` transported under
    -- the three target weakenings (`compile_rename` ×3).
    have hCfW : CaptureSet.compile
          (((CaptureSet.var (.M .epsilon) (.bound xv)).rename Rename.succ).rename Rename.succ
            ∪ .var (.M .epsilon) (.bound .here)) ctxL.srcCtx
        = CaptureSet.compile ((cs.rename Rename.succ).rename Rename.succ
            ∪ .var (.M .epsilon) (.bound .here)) ctxL.srcCtx := by
      rw [hctxL]
      simp only [CompilerCtx.consVar_srcCtx, CompilerCtx.consCVar_srcCtx,
        CompilerCtx.weakenTarget_srcCtx]
      apply CaptureSet.compile_lock_field_congr
      simp only [CaptureSet.compile_rename, hxv]
    -- the lock's separation context `Ψ` agrees between `{xv}` and `cs`.  Mirror of
    -- `hCfW` for `peaks`: project the underlying `peaks` equality off `hpk`, then
    -- peel the two `peaks`-weakenings via `peaks_lock_field_congr`.
    have hpk' : CapyCaptureSet.peaks ctx.capyCtx (.var (.M .epsilon) (.bound xv))
        = CapyCaptureSet.peaks ctx.capyCtx cs := congrArg PeakSet.cs hpk
    have hpkW : CapyCaptureSet.peakset ctxL.capyCtx
          (((CaptureSet.var (.M .epsilon) (.bound xv)).rename Rename.succ).rename Rename.succ
            ∪ .var (.M .epsilon) (.bound .here))
        = CapyCaptureSet.peakset ctxL.capyCtx ((cs.rename Rename.succ).rename Rename.succ
            ∪ .var (.M .epsilon) (.bound .here)) := by
      apply CapyCaptureSet.peakset_congr
      rw [hctxL]
      simp only [CompilerCtx.consVar_capyCtx, CompilerCtx.consCVar_capyCtx,
        CompilerCtx.weakenTarget_capyCtx]
      exact CapyCaptureSet.peaks_lock_field_congr hpk'
    repeat' congr 1


/-- **Type-preservation of term compilation.**  A well-typed source term, in any
    coherent compiler context whose source typing context matches the
    derivation's, compiles to a well-typed target term at the compiled capture
    set, context, and type. -/
theorem CapyHasType.compile {s1 : Sig} {Cs : CaptureSet s1} {Γ : CapyCtx s1}
    {e : CapyExp s1} {E : CapyTy .exi s1} (hty : CapyHasType Cs Γ e E) :
    ∀ {s2 : Sig} (ctx : CompilerCtx s1 s2), ctx.capyCtx = Γ → ctx.Coherent →
    ∃ e' : Exp s2, HasType (CaptureSet.compile Cs ctx.srcCtx) ctx.coreCtx e'
      (CapyTy.compile E ctx) := by
  induction hty
  case unit =>
    intro s2 ctx hΓ hcoh
    refine ⟨.unit, ?_⟩
    simp only [CaptureSet.compile, CapyTy.compile]
    exact HasType.unit
  case btrue =>
    intro s2 ctx hΓ hcoh
    refine ⟨.btrue, ?_⟩
    simp only [CaptureSet.compile, CapyTy.compile]
    exact HasType.btrue
  case bfalse =>
    intro s2 ctx hΓ hcoh
    refine ⟨.bfalse, ?_⟩
    simp only [CaptureSet.compile, CapyTy.compile]
    exact HasType.bfalse
  case var =>
    intro s2 ctx hΓ hcoh
    rename_i xv Γv Tv hclosed hlook
    obtain ⟨bv, _, hsrcvar, hcorelk⟩ := hcoh.varLookup (hΓ ▸ hlook)
    refine ⟨.var (.bound bv), ?_⟩
    have hTvclosed : Tv.IsClosed := CapyCtx.lookupVar_isClosed (hΓ ▸ hlook) (hΓ ▸ hclosed)
    have hbase : HasType {} ctx.coreCtx (.var (.bound bv))
        (.typ ((CapyTy.compile Tv ctx).refineCaptureSet (.var (.M .epsilon) (.bound bv)))) :=
      HasType.var hcoh.closed hcorelk
    -- the var's compiled capture is its declared latent `⟦Tv.captureSet⟧`
    have hcs : CaptureSet.compile (.var (.M .epsilon) (.bound xv)) ctx.srcCtx
        = CaptureSet.compile Tv.captureSet ctx.srcCtx := by
      simp only [CaptureSet.compile, hsrcvar, CaptureSet.applyAccess_M, CaptureSet.applyMut_epsilon]
    rw [hcs]
    -- the refinement vanishes: `⟦E⟧ = .typ ⟦Tv⟧`
    simp only [CapyTy.compile]
    rw [CapyTy.compile_refine_self hsrcvar (hΓ ▸ hlook)]
    exact HasType.subtyp hbase (Subcapt.sc_elem CaptureSet.Subset.empty)
      (Subtyp.typ (Subtyp.self_refine hcorelk))
      (CaptureSet.compile_isClosed (CapyTy.IsClosed.captureSet hTvclosed) hcoh.srcClosed)
      (Ty.IsClosed.typ (CapyTy.compile_isClosed _ _ hTvclosed hcoh.srcClosed))
  case readonly =>
    intro s2 ctx hΓ hcoh
    rename_i xv Γv Cc hclosed hlook
    obtain ⟨bv, _, hsrcvar, hcorelk⟩ := hcoh.varLookup (hΓ ▸ hlook)
    simp only [CapyTy.captureSet] at hsrcvar
    simp only [CapyTy.compile] at hcorelk
    refine ⟨.reader (.bound bv), ?_⟩
    have hCcclosed : Cc.IsClosed := by
      have h := CapyCtx.lookupVar_isClosed (hΓ ▸ hlook) (hΓ ▸ hclosed)
      cases h with | cell h => exact h
    have hbase : HasType {} ctx.coreCtx (.reader (.bound bv))
        (.typ (.reader (.var (.M .ro) (.bound bv)))) := HasType.reader hcoh.closed hcorelk
    have hcsclosed : (CaptureSet.compile Cc ctx.srcCtx).applyRO.IsClosed :=
      CaptureSet.applyRO_isClosed (CaptureSet.compile_isClosed hCcclosed hcoh.srcClosed)
    -- the readonly view's compiled capture is `(⟦Cc⟧).applyRO`
    have hcs : CaptureSet.compile (.var (.M .ro) (.bound xv)) ctx.srcCtx
        = (CaptureSet.compile Cc ctx.srcCtx).applyRO := by
      simp only [CaptureSet.compile, hsrcvar, CaptureSet.applyAccess_M, CaptureSet.applyMut_ro]
    have hEtype : CapyTy.compile (CapyTy.cell (.var (.M .ro) (.bound xv)) .ro).typ ctx
        = .typ (.reader ((CaptureSet.compile Cc ctx.srcCtx).applyRO)) := by
      simp only [CapyTy.compile, hcs]
    rw [hcs, hEtype]
    refine HasType.subtyp hbase (Subcapt.sc_elem CaptureSet.Subset.empty)
      (Subtyp.typ (Subtyp.reader (Subcapt.sc_ro_mono (Subcapt.sc_var hcorelk))))
      hcsclosed (Ty.IsClosed.typ (Ty.IsClosed.reader hcsclosed))
  case fresh =>
    intro s2 ctx hΓ hcoh
    -- **`fresh` ↦ `letin ⟦premise⟧ (pack (⟦D⟧.rename succ) (.bound .here))`,
    --   with the premise witness bound at effect `C1 = {}`.**
    --
    -- An MNF let-binding rebinds the compiled premise (a *value*) to a genuine
    -- variable `.bound .here` typed `{}`, which `pack` consumes.  The `letin` is
    -- REQUIRED: a source `.var x` compiles to `.var bv` (via `var`) OR to `.reader bv`
    -- (via `readonly`), and `pack` only accepts a `.var` argument — so the let must
    -- rebind either value to a fresh `.var here`.
    --
    -- **Bind the premise at `C1 = {}` (the SECONDARY-FINDING fix).**  Both `.var bv`
    -- and `.reader bv` are values the target types at effect `{}` (the `var`/`reader`
    -- rules conclude `{}`); `Cprem` enters only via source subsumption, so the witness
    -- is ALWAYS obtainable at `C1 = {}` (lemma `compile_var_typ_empty`).  Binding at
    -- `{}` makes the `letin`'s continuation context CLEAN — `({}.peakset).consumed = ∅`
    -- ⇒ `kill_peaks` is a no-op ⇒ `Γ2 = (⟦Γ⟧, x:⟦T[D/c]⟧)` with NO killed cvars — and
    -- makes `seq` trivial (`seq_access_only` on `{}`).  The final `letin` effect
    -- `{} ∪ (⟦D⟧ ∪ ⟦D⟧.applyDrop)` is subsumed up to `⟦C ∪ D ∪ D.applyDrop⟧`.
    --   (WHY `{}` and not `Cc`: if `C1 = Cc`, `kill_peaks` kills `Cc`'s drop-mode peak
    --    cvars; a spurious `.cvar .drop k` injected into `Cprem` by `sc_elem`
    --    subsumption with `k ∈ peaks(D)` would then be `.killed` in `Γ2`, breaking
    --    `pack`'s `drp` and the lock `Satisfy`.  Binding at `{}` removes the kill.)
    --
    -- `pack`'s body must line up with the let-bound `here`'s type, which needs the
    -- type-level opening commutation up to **subtyping**:
    --     `⟦T[D/c]⟧  <:  ⟦T⟧[⟦D⟧/c]`.
    -- A compiled function lock is `peakSepCtx (peakset Γ W) …` (one item per distinct
    -- peak cvar).  Source-substitute-then-compile (`⟦T[D/c]⟧`) re-groups `c` into
    -- `D`'s peaks (SEPARATED lock `Ψsep`); compile-then-target-substitute
    -- (`⟦T⟧[⟦D⟧/c]`) keeps `c`'s single item, now holding `⟦D⟧` (MERGED lock
    -- `Ψmerged`).  Per the trusted `Subtyp.modal_modal`, `Ψsep <: Ψmerged` reduces to
    -- `Satisfy (Γ.push_lock Ψmerged) Ψsep`: discharge every `HasTwoDistinct` pair of
    -- `Ψsep`.  Three kinds of pair:
    --   • within-`D` (peak_i ⊥ peak_j):  ✓ `sep_droppable` from `droppable Γ D`.
    --   • other-other (cs-peak ⊥ cs-peak): ✓ `sep_lock` (both are items of `Ψmerged`).
    --   • CROSS (D-peak_i ⊥ cs-peak f):   ✓ `SepCheck.sep_mono` (below).
    --
    -- **The cross pair — resolved by `SepCheck.sep_mono`.**  We have `⟦D⟧ ⊥ f` from
    -- `Ψmerged` (via `sep_lock`, where `⟦D⟧ = peak_1 ∪ … ∪ peak_n` is a SINGLE merged
    -- lock item) and need `peak_i ⊥ f` with `peak_i ⊆ ⟦D⟧` and `f` an arbitrary
    -- (possibly NON-droppable) capability.  This is LEFT-DOWNWARD-MONOTONICITY of
    -- `SepCheck`: `SepCheck Γ A B → Subcapt Γ A' A → SepCheck Γ A' B`.  It is NOT
    -- admissible from the other constructors (induction on the `⟦D⟧ ⊥ f` derivation
    -- blocks at `sep_lock`: `peak_i ⊊ ⟦D⟧` is not itself a lock item), so it was
    -- ADDED as the primitive `SepCheck.sep_mono` (Core.lean), discharged in
    -- `fundamental_sepcheck`/`_global` via `Noninterference.subset_left` — sound
    -- because `SemSepCheck = Noninterference` is downward-closed (`peak_i.denot ⊆
    -- ⟦D⟧.denot` by `fundamental_subcapt`).  Convenience wrapper: `SepCheck.left_mono`.
    --
    -- With the lock `Satisfy` now fully dischargeable, NO design gap remains.  The
    -- rest is mechanical assembly: the type-level subtyping lift `⟦T[D/c]⟧ <:
    -- ⟦T⟧[⟦D⟧/c]` (leaves = `compile_subst_openCVar` equality → refl; locks =
    -- `modal_modal` + the `Satisfy` above), the `letin`/`pack` term wiring, the
    -- capture arithmetic, and the `pack` droppability/access-only side-conditions.
    -- Foundations PROVEN: `SubstCompat`, (★)`compile_peaks`, `sep_mono`.
    -- [[project_capybara_translation]]
    --
    -- ⚠️ NOTE (skeleton below is PRE-FIX): the `have key` still binds the premise at
    -- `C1 := Cc` (`hePrem` at effect `Cc`), the FLAWED choice.  On resume this is to
    -- be revised to `C1 := {}` per the fix above — emit `compile_var_typ_empty` to
    -- get the premise witness at `{}`, set `C1 := {}` (⇒ clean `Γ2`, trivial `seq`),
    -- then subsume the final effect up to `⟦C ∪ D ∪ D.applyDrop⟧`.  Kept as-is for now
    -- (build paused); `seq`/`ao`/`drp`/`var` remain `sorry`.
    rename_i s0 Cprem Γ0 xv Dpack Tbody hprem hDcl hDvalid hdrop ih
    obtain ⟨ePrem, hePrem⟩ := ih ctx hΓ hcoh
    simp only [CapyTy.compile] at hePrem ⊢
    refine ⟨.letin ePrem (.pack ((CaptureSet.compile Dpack ctx.srcCtx).rename Rename.succ)
      (.bound .here)), ?_⟩
    -- abbreviations
    set Cc := CaptureSet.compile Cprem ctx.srcCtx with hCc
    set Dc := CaptureSet.compile Dpack ctx.srcCtx with hDc
    set exiCtx := ctx.weakenTarget.consCVar (CapyCaptureBound.unbound .epsilon) BVar.here with hexi
    -- the `letin` at the right-nested capture; coerced to the goal capture afterwards.
    have key : HasType (Cc ∪ (Dc ∪ Dc.applyDrop)) ctx.coreCtx
        (ePrem.letin (Exp.pack (Dc.rename Rename.succ) (Var.bound BVar.here)))
        (Ty.exi (CapyTy.compile Tbody exiCtx)) := by
      refine HasType.letin (C1 := Cc) (C2 := Dc ∪ Dc.applyDrop)
        (T := CapyTy.compile (Tbody.subst (CapySubst.openCVar Dpack)) ctx)
        (U := Ty.exi (CapyTy.compile Tbody exiCtx)) ?seq hePrem ?e2
      case seq => sorry
      case e2 =>
        -- normalize the pack capture `(Dc ∪ Dc.applyDrop).rename succ`
        simp only [CaptureSet.rename, CaptureSet.applyDrop_rename]
        refine HasType.pack ?cl ?ao ?drp ?var
        case cl =>
          -- `⟦D⟧.rename succ` closed: `D.IsClosed` (new `fresh` premise) compiled + renamed.
          exact CaptureSet.rename_isClosed
            (CaptureSet.compile_isClosed hDcl hcoh.srcClosed)
        case ao => sorry
        case drp => sorry
        case var =>
          -- the let-bound `x` (typed `⟦T[D/c]⟧.rename succ`) subsumes to `pack`'s
          -- required body `(⟦T⟧_exiCtx.rename succ.lift).subst (openCVar (Dc.rename succ))`.
          -- = (★★) renamed: `⟦T[D/c]⟧ <: ⟦T⟧_exiCtx[⟦D⟧/c]`, via `var`+`self_refine`+
          -- `compile_openCVar_subtyp` (the type-level commutation; locks via `sep_mono`).
          sorry
    -- coerce: reassoc the (left-nested) goal capture to `key`'s (right-nested);
    -- the goal type already matches `key`'s (both `.exi (compile Tbody exiCtx)`).
    refine HasType.subtyp key ?_ Subtyp.refl ?_ ?_
    · -- Subcapt (Cc ∪ (Dc ∪ Dc.applyDrop)) ⟦Cprem ∪ Dpack ∪ Dpack.applyDrop⟧
      simp only [CaptureSet.compile, CaptureSet.compile_applyDrop, ← hCc, ← hDc]
      exact Subcapt.sc_union
        (Subcapt.sc_elem (.union_right_left (.union_right_left .refl)))
        (Subcapt.sc_union
          (Subcapt.sc_elem (.union_right_left (.union_right_right .refl)))
          (Subcapt.sc_elem (.union_right_right .refl)))
    · -- goal capture closed: from `key`'s regularity + reassoc
      have hk := key.use_set_is_closed
      simp only [CaptureSet.compile, CaptureSet.compile_applyDrop, ← hCc, ← hDc]
      cases hk with
      | union hCcCl hrest =>
        cases hrest with
        | union hDcCl hDcdCl => exact .union (.union hCcCl hDcCl) hDcdCl
    · -- goal type closed: identical to `key`'s type
      exact key.type_is_closed
  -- Remaining cases (abs, tabs, cabs, app, tapp, capp,
  -- letin, letin_unpack, alloc, drop, read, write, cond, par, invoke, subtyp)
  -- are WIP: discharged incrementally.
  all_goals (intro s2 ctx hΓ hcoh; sorry)

end Compilation
