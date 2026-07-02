import Semantic.CoreCapybara.Compilation.Coherence
import Semantic.CoreCapybara.Compilation.SubstLemmas
import Semantic.CoreCapybara.Compilation.SubtypCompile
import Semantic.CoreCapybara.Compilation.OpenCVarSubtyp
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
    (hsrc : ctx.srcCtx.lookupVar xv = CapyCaptureSet.compile T.captureSet ctx.srcCtx)
    (hcapy : ctx.capyCtx.LookupVar xv T) :
    CapyTy.compile (T.refineCaptureSet (.var (.M .epsilon) (.bound xv))) ctx
      = CapyTy.compile T ctx := by
  -- the var's capture image `⟦{xv}⟧` is its declared latent `⟦T.captureSet⟧`
  have hxv : CapyCaptureSet.compile (.var (.M .epsilon) (.bound xv)) ctx.srcCtx
      = CapyCaptureSet.compile T.captureSet ctx.srcCtx := by
    simp only [CapyCaptureSet.compile, hsrc, CaptureSet.applyAccess_M, CaptureSet.applyMut_epsilon]
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
    have hCf : CapyCaptureSet.compile (.var (.M .epsilon) (.bound xv))
          (SrcCtx.weaken (k := Kind.tvar) ctx.srcCtx)
        = CapyCaptureSet.compile cs (SrcCtx.weaken (k := Kind.tvar) ctx.srcCtx) := by
      unfold SrcCtx.weaken
      rw [CapyCaptureSet.compile_rename, CapyCaptureSet.compile_rename, hxv]
    -- only the modal lock `W` and (via `hpk`) the separation `Ψ` differ; `congr`
    -- discharges the residual lock equality with `hCf` from context.
    simp only [CapyTy.refineCaptureSet, CapyTy.compile, hpk]
    repeat' congr 1
  | cpoly cb cs E =>
    simp only [CapyTy.captureSet] at hxv hpk
    have hCf : CapyCaptureSet.compile (.var (.M .epsilon) (.bound xv))
          (SrcCtx.weaken (k := Kind.cvar) ctx.srcCtx)
        = CapyCaptureSet.compile cs (SrcCtx.weaken (k := Kind.cvar) ctx.srcCtx) := by
      unfold SrcCtx.weaken
      rw [CapyCaptureSet.compile_rename, CapyCaptureSet.compile_rename, hxv]
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
    have hCfW : CapyCaptureSet.compile
          (((CapyCaptureSet.var (.M .epsilon) (.bound xv)).rename Rename.succ).rename Rename.succ
            ∪ .var (.M .epsilon) (.bound .here)) ctxL.srcCtx
        = CapyCaptureSet.compile ((cs.rename Rename.succ).rename Rename.succ
            ∪ .var (.M .epsilon) (.bound .here)) ctxL.srcCtx := by
      rw [hctxL]
      simp only [CompilerCtx.consVar_srcCtx, CompilerCtx.consCVar_srcCtx,
        CompilerCtx.weakenTarget_srcCtx]
      apply CapyCaptureSet.compile_lock_field_congr
      simp only [CapyCaptureSet.compile_rename, hxv]
    -- the lock's separation context `Ψ` agrees between `{xv}` and `cs`.  Mirror of
    -- `hCfW` for `peaks`: project the underlying `peaks` equality off `hpk`, then
    -- peel the two `peaks`-weakenings via `peaks_lock_field_congr`.
    have hpk' : CapyCaptureSet.peaks ctx.capyCtx (.var (.M .epsilon) (.bound xv))
        = CapyCaptureSet.peaks ctx.capyCtx cs := congrArg CapyPeakSet.cs hpk
    have hpkW : CapyCaptureSet.peakset ctxL.capyCtx
          (((CapyCaptureSet.var (.M .epsilon) (.bound xv)).rename Rename.succ).rename Rename.succ
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
    set, context, and type.

    Beyond `Coherent`, two context-regularity invariants are threaded (both
    trivial at the closed top-level context and preserved by every context
    extension): `CVarInjective` (distinct source cvars have distinct target
    images) and `capyCtx.NoPseudoPeak` (stored capture annotations carry no
    frozen peaks) — the `fresh` case's `compile_subst_subtyp` instantiation
    consumes them. -/
theorem CapyHasType.compile {s1 : Sig} {Cs : CapyCaptureSet s1} {Γ : CapyCtx s1}
    {e : CapyExp s1} {E : CapyTy .exi s1} (hty : CapyHasType Cs Γ e E) :
    ∀ {s2 : Sig} (ctx : CompilerCtx s1 s2), ctx.capyCtx = Γ → ctx.Coherent →
    ctx.srcCtx.CVarInjective → ctx.capyCtx.NoPseudoPeak →
    ∃ e' : Exp s2, HasType (CapyCaptureSet.compile Cs ctx.srcCtx) ctx.coreCtx e'
      (CapyTy.compile E ctx) := by
  induction hty
  case unit =>
    intro s2 ctx hΓ hcoh hinj hnpp
    refine ⟨.unit, ?_⟩
    simp only [CapyCaptureSet.compile, CapyTy.compile]
    exact HasType.unit
  case btrue =>
    intro s2 ctx hΓ hcoh hinj hnpp
    refine ⟨.btrue, ?_⟩
    simp only [CapyCaptureSet.compile, CapyTy.compile]
    exact HasType.btrue
  case bfalse =>
    intro s2 ctx hΓ hcoh hinj hnpp
    refine ⟨.bfalse, ?_⟩
    simp only [CapyCaptureSet.compile, CapyTy.compile]
    exact HasType.bfalse
  case var =>
    intro s2 ctx hΓ hcoh hinj hnpp
    rename_i xv Γv Tv hclosed hlook
    obtain ⟨bv, _, hsrcvar, hcorelk⟩ := hcoh.varLookup (hΓ ▸ hlook)
    refine ⟨.var (.bound bv), ?_⟩
    have hTvclosed : Tv.IsClosed := CapyCtx.lookupVar_isClosed (hΓ ▸ hlook) (hΓ ▸ hclosed)
    have hbase : HasType {} ctx.coreCtx (.var (.bound bv))
        (.typ ((CapyTy.compile Tv ctx).refineCaptureSet (.var (.M .epsilon) (.bound bv)))) :=
      HasType.var hcoh.closed hcorelk
    -- the var's compiled capture is its declared latent `⟦Tv.captureSet⟧`
    have hcs : CapyCaptureSet.compile (.var (.M .epsilon) (.bound xv)) ctx.srcCtx
        = CapyCaptureSet.compile Tv.captureSet ctx.srcCtx := by
      simp only [CapyCaptureSet.compile, hsrcvar, CaptureSet.applyAccess_M,
        CaptureSet.applyMut_epsilon]
    rw [hcs]
    -- the refinement vanishes: `⟦E⟧ = .typ ⟦Tv⟧`
    simp only [CapyTy.compile]
    rw [CapyTy.compile_refine_self hsrcvar (hΓ ▸ hlook)]
    exact HasType.subtyp hbase (Subcapt.sc_elem CaptureSet.Subset.empty)
      (Subtyp.typ (Subtyp.self_refine hcorelk))
      (CapyCaptureSet.compile_isClosed (CapyTy.IsClosed.captureSet hTvclosed) hcoh.srcClosed)
      (Ty.IsClosed.typ (CapyTy.compile_isClosed _ _ hTvclosed hcoh.srcClosed))
  case readonly =>
    intro s2 ctx hΓ hcoh hinj hnpp
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
    have hcsclosed : (CapyCaptureSet.compile Cc ctx.srcCtx).applyRO.IsClosed :=
      CaptureSet.applyRO_isClosed (CapyCaptureSet.compile_isClosed hCcclosed hcoh.srcClosed)
    -- the readonly view's compiled capture is `(⟦Cc⟧).applyRO`
    have hcs : CapyCaptureSet.compile (.var (.M .ro) (.bound xv)) ctx.srcCtx
        = (CapyCaptureSet.compile Cc ctx.srcCtx).applyRO := by
      simp only [CapyCaptureSet.compile, hsrcvar, CaptureSet.applyAccess_M, CaptureSet.applyMut_ro]
    have hEtype : CapyTy.compile (CapyTy.cell (.var (.M .ro) (.bound xv)) .ro).typ ctx
        = .typ (.reader ((CapyCaptureSet.compile Cc ctx.srcCtx).applyRO)) := by
      simp only [CapyTy.compile, hcs]
    rw [hcs, hEtype]
    refine HasType.subtyp hbase (Subcapt.sc_elem CaptureSet.Subset.empty)
      (Subtyp.typ (Subtyp.reader (Subcapt.sc_ro_mono (Subcapt.sc_var hcorelk))))
      hcsclosed (Ty.IsClosed.typ (Ty.IsClosed.reader hcsclosed))
  case fresh =>
    intro s2 ctx hΓ hcoh hinj hnpp
    rename_i s0 Γ0 Df xv Tbody hDcl hao hlook hdrop hpb hnp
    -- The refactored `fresh` rule reads `x` straight from the context
    -- (`Γ.LookupVar x (T[D/c])`) and re-packs it.  The subject `.var (.bound x)`
    -- compiles to the target variable `bv`, so we emit `.pack ⟦D⟧ bv` DIRECTLY —
    -- no `letin`, since `bv` is already a genuine `.var` that `pack` accepts.  With
    -- `C` dropped from the conclusion, compilation is EXACT: `pack`'s native capture
    -- `⟦D⟧ ∪ ⟦D⟧.applyAccess .drop` IS the goal capture `⟦D ∪ D.applyDrop⟧` (modulo
    -- `applyAccess .drop ≡ applyDrop`), so no subsumption is needed.
    -- [[project_capybara_translation]]
    obtain ⟨bv, _, _, hcorelk⟩ := hcoh.varLookup (hΓ ▸ hlook)
    -- the `.exi`-compiler's extended body context
    set exiCtx := ctx.weakenTarget.consCVar (CapyCaptureBound.unbound .epsilon) BVar.here
      with hexi
    refine ⟨.pack (CapyCaptureSet.compile Df ctx.srcCtx) (.bound bv), ?_⟩
    -- `⟦.exi T⟧` is definitionally `.exi ⟦T⟧_exiCtx`; distribute `⟦D ∪ D.applyDrop⟧`.
    have hty : CapyTy.compile (CapyTy.exi Tbody) ctx = Ty.exi (CapyTy.compile Tbody exiCtx) := by
      simp only [CapyTy.compile, ← hexi]
    rw [hty]
    simp only [CapyCaptureSet.compile, CapyCaptureSet.compile_applyDrop]
    refine HasType.pack ?cl ?ao ?drp ?var
    case cl => exact CapyCaptureSet.compile_isClosed hDcl hcoh.srcClosed
    case ao =>
      -- `⟦D⟧.AccessOnly ⟦Γ⟧` from source `AccessOnly Γ D` (`hao`), via the
      -- compile-preserves-AccessOnly transport (Workstream A).
      exact CapyCaptureSet.compile_accessOnly hcoh hDcl (hΓ ▸ hao)
    case drp =>
      -- `⟦D⟧.droppable ⟦Γ⟧` from source `droppable Γ D` (`hdrop`), via the
      -- compile-preserves-droppable transport (Workstream A).
      exact CapyCaptureSet.compile_droppable hcoh hDcl (hΓ ▸ hdrop)
    case var =>
      -- `HasType.var` types `bv` at `{}` and `⟦T[D/c]⟧^{bv}`; `pack` wants it at
      -- `(⟦T⟧_exiCtx).subst (openCVar ⟦D⟧)`.  Bridge = self-refinement vanishing
      -- (`Subtyp.self_refine`) ∘ the type-level openCVar commutation up to
      -- subtyping `⟦T[D/c]⟧ <: ⟦T⟧_exiCtx[⟦D⟧/c]` — `compile_subst_subtyp`'s
      -- forward direction, instantiated at the base `openCVar` package
      -- (`OpenCVarSubtyp.lean`'s `openCVar` instances).
      have hstoredCl : (Tbody.subst (CapySubst.openCVar Df)).IsClosed :=
        CapyCtx.lookupVar_isClosed (hΓ ▸ hlook) hcoh.capyClosed
      have hTcl : Tbody.IsClosed := CapyTy.isClosed_of_subst hstoredCl
      have hnppExi : exiCtx.capyCtx.NoPseudoPeak := hnpp
      have hclOrig : exiCtx.capyCtx.IsClosed :=
        CapyCtx.IsClosed.push hcoh.capyClosed
          (CapyBinding.IsClosed.cvar CapyCaptureBound.IsClosed.unbound)
      have hvcOrig : exiCtx.srcCtx.VarsClosed := hcoh.srcClosed.weaken.consCVar
      have hscl : (Subst.openCVar (CapyCaptureSet.compile Df ctx.srcCtx)).IsClosed :=
        Subst.IsClosed.openCVar (CapyCaptureSet.compile_isClosed hDcl hcoh.srcClosed)
      have hdropT : CaptureSet.droppable ctx.coreCtx
          (CapyCaptureSet.compile Df ctx.srcCtx) :=
        CapyCaptureSet.compile_droppable hcoh hDcl (hΓ ▸ hdrop)
      have hB2c := (CapyTy.compile_subst_subtyp Tbody
        (ctxOrig := exiCtx) (ctxSub := ctx)
        (σt := Subst.openCVar (CapyCaptureSet.compile Df ctx.srcCtx))
        SubstCompat.openCVar SubstTvarCompat.openCVar hTcl hpb
        (TgtPairDroppable.openCVar hdropT)
        (SubstCompat.realign_openCVar hcoh)
        hcoh.capyClosed hclOrig hscl hcoh.srcClosed hvcOrig hcoh.closed
        (CapySubst.IsClosed.openCVar hDcl)
        hinj (PeakSubstIso.openCVar Df) hnppExi hnp
        CapyCtx.SubstsTo.openCVar PeakSubstIso.StablePreserving.openCVar).1
      have hmidCl : (CapyTy.compile (Tbody.subst (CapySubst.openCVar Df)) ctx).IsClosed :=
        CapyTy.compile_isClosed _ _ hstoredCl hcoh.srcClosed
      have hbase : HasType {} ctx.coreCtx (.var (.bound bv))
          (.typ ((CapyTy.compile (Tbody.subst (CapySubst.openCVar Df)) ctx).refineCaptureSet
            (.var (.M .epsilon) (.bound bv)))) :=
        HasType.var hcoh.closed hcorelk
      have hE2cl : Ty.IsClosed ((CapyTy.compile Tbody exiCtx).subst
          (Subst.openCVar (CapyCaptureSet.compile Df ctx.srcCtx))) :=
        Ty.is_closed_subst (CapyTy.compile_isClosed Tbody exiCtx hTcl hvcOrig) hscl
      exact HasType.subtyp hbase Subcapt.refl
        (Subtyp.typ (Subtyp.trans hmidCl (Subtyp.self_refine hcorelk) hB2c))
        CaptureSet.IsClosed.empty (Ty.IsClosed.typ hE2cl)
  -- Remaining cases (abs, tabs, cabs, app, tapp, capp,
  -- letin, letin_unpack, alloc, drop, read, write, cond, par, invoke, subtyp)
  -- are WIP: discharged incrementally.
  all_goals (intro s2 ctx hΓ hcoh hinj hnpp; sorry)

end Compilation
