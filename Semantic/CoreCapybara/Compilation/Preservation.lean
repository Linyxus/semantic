import Semantic.CoreCapybara.Compilation.Coherence
import Semantic.CoreCapybara.Compilation.SubstLemmas
import Semantic.CoreCapybara.Compilation.SubtypCompile
import Semantic.CoreCapybara.Compilation.OpenCVarSubtyp
import Semantic.CoreCapybara.Compilation.TargetRename
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
    obtain ⟨bv, _, _, hcorelk⟩ := hcoh.varLookup (hΓ ▸ hlook)
    refine ⟨.var (.bound bv), ?_⟩
    have hTvclosed : Tv.IsClosed := CapyCtx.lookupVar_isClosed (hΓ ▸ hlook) (hΓ ▸ hclosed)
    -- `HasType.var` at the invariant's SELF-REFINED binding `⟦Tv^{xv}⟧` gives the
    -- goal type directly; erase the extra `{bv}`-refinement by `Subtyp.self_refine`
    -- and bridge the capture `{} <: ⟦{ε xv}⟧`.  (No capture-image fact needed — the
    -- proof is uniform over aligned and re-abstracted binders.)
    have hbase := HasType.var hcoh.closed hcorelk
    simp only [CapyTy.compile]
    exact HasType.subtyp hbase (Subcapt.sc_elem CaptureSet.Subset.empty)
      (Subtyp.typ (Subtyp.self_refine hcorelk))
      (CapyCaptureSet.compile_isClosed CapyCaptureSet.IsClosed.var_bound hcoh.srcClosed)
      (Ty.IsClosed.typ (CapyTy.compile_isClosed _ _
        (CapyTy.IsClosed.refineCaptureSet hTvclosed CapyCaptureSet.IsClosed.var_bound)
        hcoh.srcClosed))
  case readonly =>
    intro s2 ctx hΓ hcoh hinj hnpp
    rename_i xv Γv Cc hclosed hlook
    obtain ⟨bv, _, _, hcorelk⟩ := hcoh.varLookup (hΓ ▸ hlook)
    -- the invariant's SELF-REFINED binding at a `cell` is `.cell ⟦{ε xv}⟧`, whose
    -- capture set the target `reader` rule + `sc_var`/`sc_ro_mono` narrow to the
    -- readonly view — uniformly over aligned and re-abstracted binders.
    simp only [CapyTy.refineCaptureSet, CapyTy.compile] at hcorelk
    refine ⟨.reader (.bound bv), ?_⟩
    have hbase : HasType {} ctx.coreCtx (.reader (.bound bv))
        (.typ (.reader (.var (.M .ro) (.bound bv)))) := HasType.reader hcoh.closed hcorelk
    have hcsclosed : (CapyCaptureSet.compile
        (.var (.M .ro) (.bound xv)) ctx.srcCtx).IsClosed :=
      CapyCaptureSet.compile_isClosed CapyCaptureSet.IsClosed.var_bound hcoh.srcClosed
    have hsub : Subcapt ctx.coreCtx (.var (.M .ro) (.bound bv))
        (CapyCaptureSet.compile (.var (.M .ro) (.bound xv)) ctx.srcCtx) := by
      have h0 := Subcapt.sc_ro_mono (Subcapt.sc_var hcorelk)
      simp only [Ty.captureSet, CaptureSet.applyRO_var, Access.applyRO] at h0
      simp only [CapyCaptureSet.compile, CaptureSet.applyAccess_M, CaptureSet.applyMut_ro]
      exact h0
    simp only [CapyTy.compile]
    exact HasType.subtyp hbase (Subcapt.sc_elem CaptureSet.Subset.empty)
      (Subtyp.typ (Subtyp.reader hsub))
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
    -- collapse the invariant's self-refined binding to `⟦T[D/c]⟧` — via the
    -- ALIGNED image (`hcoh.srcAligned`; at a re-abstracted parameter this rides
    -- the documented fresh-under-abs gap recorded there).
    rw [CapyTy.compile_refine_self (hcoh.srcAligned (hΓ ▸ hlook)) (hΓ ▸ hlook)] at hcorelk
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
  case abs =>
    intro s2 ctx hΓ hcoh hinj hnpp
    rename_i Γ0 e0 cs0 T1 T2 hT1cl hT1np hT1ao hbody ih
    simp only [CapyTy.compile]
    -- ── The real-binding tower over the target context, mirroring the compiled
    -- type's placeholder-built contexts (`compile` reads only `srcCtx`/`capyCtx`;
    -- the payloads are written in the goal's own placeholder-context form so the
    -- constructed derivation's indices match the goal syntactically).
    set b2 : Binding (s2,C) .cvar := Binding.cvar Authority.access_only
      (CaptureBound.bound (CapyCaptureSet.compile T1.captureSet
        (ctx.weakenTarget.consCVar (CapyCaptureBound.unbound Mutability.epsilon)
          BVar.here).srcCtx)) with hb2
    set b3 : Binding (s2,C,C) .var := Binding.var (CapyTy.compile
      ((T1.rename Rename.succ).refineCaptureSet
        (CapyCaptureSet.var (.M .epsilon) (.bound .here)))
      ((ctx.weakenTarget.weakenTarget.consCVar
          (CapyCaptureBound.unbound Mutability.epsilon)
          (BVar.there BVar.here)).consVar T1 none
        (CaptureSet.cvar (Access.M Mutability.epsilon) BVar.here))) with hb3
    set ctxW3 := ((ctx.weakenTarget
      (Binding.cvar Authority.access_only CaptureBound.unbound)).weakenTarget b2
      ).weakenTarget b3 with hctxW3
    set ctxC4 := ctxW3.consCVar (.unbound .epsilon) (BVar.there (BVar.there BVar.here))
      with hctxC4
    set ctxLockR := ctxC4.consVar T1 (some BVar.here)
      (CaptureSet.cvar (Access.M Mutability.epsilon) (BVar.there BVar.here)) with hctxLockR
    -- ── Coherence chain up the tower.
    have hcoh1 := hcoh.weakenTarget
      (b := Binding.cvar Authority.access_only CaptureBound.unbound)
      (Binding.IsClosed.cvar CaptureBound.IsClosed.unbound)
    have hcoh2 := hcoh1.weakenTarget (b := b2) (Binding.IsClosed.cvar
      (CaptureBound.IsClosed.bound
        (CapyCaptureSet.compile_isClosed (CapyTy.IsClosed.captureSet hT1cl)
          hcoh.srcClosed.weaken.consCVar)))
    have hcoh3 := hcoh2.weakenTarget (b := b3) (Binding.IsClosed.var
      (CapyTy.compile_isClosed _ _
        (CapyTy.IsClosed.refineCaptureSet (CapyTy.IsClosed.rename hT1cl Rename.succ)
          CapyCaptureSet.IsClosed.var_bound)
        ((hcoh.srcClosed.weaken.weaken.consCVar).consVar CaptureSet.IsClosed.cvar)))
    have hcoh4 := hcoh3.consCVar (cb := CapyCaptureBound.unbound Mutability.epsilon)
      (c := BVar.there (BVar.there BVar.here)) CapyCaptureBound.IsClosed.unbound
      (Ctx.LookupCVar.there (Ctx.LookupCVar.there Ctx.LookupCVar.here))
    -- ── `x ↦ {cx}`: the re-abstracted parameter binder (`Coherent.consVarCVar`).
    -- `cx`'s declared bound realigns by `compile_rename` ×2 …
    have hcx : ctxC4.coreCtx.LookupCVar (BVar.there BVar.here) Authority.access_only
        (.bound (CapyCaptureSet.compile T1.captureSet ctxC4.srcCtx)) := by
      have hlkx : ctxW3.coreCtx.LookupCVar (BVar.there BVar.here) Authority.access_only
          (((CaptureBound.bound (CapyCaptureSet.compile T1.captureSet
            (ctx.weakenTarget.consCVar (CapyCaptureBound.unbound Mutability.epsilon)
              BVar.here).srcCtx)).rename Rename.succ).rename Rename.succ) :=
        Ctx.LookupCVar.there Ctx.LookupCVar.here
      simp only [CaptureBound.rename] at hlkx
      rw [← CapyCaptureSet.compile_rename, ← CapyCaptureSet.compile_rename] at hlkx
      exact hlkx
    -- … and the target binder's payload (the goal's arrow DOMAIN, compiled at the
    -- `bv = none` domain context) realigns to the lock context by
    -- `compile_rename` (rename past the target `x`-push) + `compile_eq_of`
    -- (`bv`-irrelevance: `compile` never reads the stored target-var image).
    have hlkdom : ctxC4.coreCtx.LookupVar BVar.here
        (CapyTy.compile ((T1.rename Rename.succ).refineCaptureSet
            (.var (.M .epsilon) (.bound .here)))
          (ctxC4.consVar T1 (some BVar.here)
            (.cvar (.M .epsilon) (BVar.there BVar.here)))) := by
      have hraw : ctxC4.coreCtx.LookupVar BVar.here
          ((CapyTy.compile ((T1.rename Rename.succ).refineCaptureSet
              (CapyCaptureSet.var (.M .epsilon) (.bound .here)))
            ((ctx.weakenTarget.weakenTarget.consCVar
                (CapyCaptureBound.unbound Mutability.epsilon)
                (BVar.there BVar.here)).consVar T1 none
              (CaptureSet.cvar (Access.M Mutability.epsilon) BVar.here))).rename
            Rename.succ) := Ctx.LookupVar.here
      have heqPayload : (CapyTy.compile ((T1.rename Rename.succ).refineCaptureSet
            (CapyCaptureSet.var (.M .epsilon) (.bound .here)))
          ((ctx.weakenTarget.weakenTarget.consCVar
              (CapyCaptureBound.unbound Mutability.epsilon)
              (BVar.there BVar.here)).consVar T1 none
            (CaptureSet.cvar (Access.M Mutability.epsilon) BVar.here))).rename Rename.succ
          = CapyTy.compile ((T1.rename Rename.succ).refineCaptureSet
              (CapyCaptureSet.var (.M .epsilon) (.bound .here))) ctxLockR :=
        (CapyTy.compile_rename _
          ((ctx.weakenTarget.weakenTarget.consCVar
              (CapyCaptureBound.unbound Mutability.epsilon)
              (BVar.there BVar.here)).consVar T1 none
            (CaptureSet.cvar (Access.M Mutability.epsilon) BVar.here))
          (((ctx.weakenTarget.weakenTarget.consCVar
              (CapyCaptureBound.unbound Mutability.epsilon)
              (BVar.there BVar.here)).consVar T1 none
            (CaptureSet.cvar (Access.M Mutability.epsilon) BVar.here)).weakenTarget b3)
          Rename.succ rfl rfl).symm.trans
        (CapyTy.compile_eq_of _ _ _
          ⟨⟨fun x => by cases x with | here => rfl | there x' => rfl,
            fun c => by cases c with | there c' => rfl,
            fun X => by cases X with | there X' => rfl⟩,
           fun _ => rfl, fun _ => Iff.rfl⟩)
      exact heqPayload ▸ hraw
    have hcohLock : ctxLockR.Coherent := hcoh4.consVarCVar hT1cl hcx hlkdom
    -- ── The IH at the real-binding lock context.
    have hΓL : ctxLockR.capyCtx = Γ0,C<:.unbound .epsilon,x:T1 := by
      simp only [hctxLockR, hctxC4, hctxW3, CompilerCtx.consVar_capyCtx,
        CompilerCtx.consCVar_capyCtx, CompilerCtx.weakenTarget_capyCtx, hΓ]
    have hinjL : ctxLockR.srcCtx.CVarInjective :=
      SrcCtx.CVarInjective.consVar hinj.consCVarThereThereHere
    have hnppL : ctxLockR.capyCtx.NoPseudoPeak := by
      rw [hΓL]
      exact ⟨hΓ ▸ hnpp, hT1np.captureSet⟩
    obtain ⟨eb, heb⟩ := ih ctxLockR hΓL hcohLock hinjL hnppL
    -- bridge the body type to the goal's placeholder-built lock context
    -- (same `capyCtx`/`srcCtx`, different `coreCtx` payloads).
    have heqT2 : CapyTy.compile (T2.rename Rename.implicit_cvar) ctxLockR
        = CapyTy.compile (T2.rename Rename.implicit_cvar)
          ((ctx.weakenTarget.weakenTarget.weakenTarget.consCVar
              (CapyCaptureBound.unbound Mutability.epsilon)
              (BVar.there (BVar.there BVar.here))).consVar
            T1 (some BVar.here)
            (CaptureSet.cvar (Access.M Mutability.epsilon) (BVar.there BVar.here))) :=
      CapyTy.compile_eq_of _ _ _
        ⟨⟨fun _ => rfl, fun _ => rfl, fun _ => rfl⟩, fun _ => rfl, fun _ => Iff.rfl⟩
    rw [heqT2] at heb
    -- ── Assembly: weaken past the lock, then wrap / abs / cabs / cabs.
    have hvcLock : ctxLockR.srcCtx.VarsClosed :=
      ((hcoh.srcClosed.weaken.weaken.weaken).consCVar).consVar CaptureSet.IsClosed.cvar
    have hΨcl : (⟨peakSepCtx ctxLockR.capyCtx
        (CapyCaptureSet.peakset ctxLockR.capyCtx
          ((cs0.rename Rename.succ).rename Rename.succ
            ∪ CapyCaptureSet.var (.M .epsilon) (.bound .here)))
        ctxLockR.srcCtx, MutabilityCtx.empty⟩ : ModalCtx (s2,C,C,x)).IsClosed :=
      ⟨peakSepCtx_isClosed (CapyCaptureSet.peaks_isClosed _ _) hvcLock,
        MutabilityCtx.IsClosed.empty⟩
    have hwk := HasType.weaken heb
      (Binding.lock ⟨peakSepCtx ctxLockR.capyCtx
        (CapyCaptureSet.peakset ctxLockR.capyCtx
          ((cs0.rename Rename.succ).rename Rename.succ
            ∪ CapyCaptureSet.var (.M .epsilon) (.bound .here)))
        ctxLockR.srcCtx, MutabilityCtx.empty⟩)
      (Binding.IsClosed.lock hΨcl)
    have hwrap := HasType.wrap hΨcl hwk
    have hdomCl : (CapyTy.compile ((T1.rename Rename.succ).refineCaptureSet
        (CapyCaptureSet.var (.M .epsilon) (.bound .here)))
        ((ctx.weakenTarget.weakenTarget.consCVar
            (CapyCaptureBound.unbound Mutability.epsilon)
            (BVar.there BVar.here)).consVar T1 none
          (CaptureSet.cvar (Access.M Mutability.epsilon) BVar.here))).IsClosed :=
      CapyTy.compile_isClosed _ _
        (CapyTy.IsClosed.refineCaptureSet (CapyTy.IsClosed.rename hT1cl Rename.succ)
          CapyCaptureSet.IsClosed.var_bound)
        ((hcoh.srcClosed.weaken.weaken.consCVar).consVar CaptureSet.IsClosed.cvar)
    have habs := HasType.abs (cs := {}) hdomCl hwrap
    -- the middle cpoly binder's bound is valid: `⟦T1.captureSet⟧` is access-only,
    -- transported from the new source premise `hT1ao` by `compile_accessOnly` at
    -- the (coherent) `ctxB`-level context.
    have hcohB : ((ctx.weakenTarget (Binding.cvar Authority.access_only
        CaptureBound.unbound)).consCVar (.unbound .epsilon) BVar.here).Coherent :=
      hcoh1.consCVar CapyCaptureBound.IsClosed.unbound Ctx.LookupCVar.here
    have hb2AO : CaptureSet.AccessOnly
        ((ctx.weakenTarget (Binding.cvar Authority.access_only
          CaptureBound.unbound)).consCVar (.unbound .epsilon) BVar.here).coreCtx
        (CapyCaptureSet.compile T1.captureSet
          ((ctx.weakenTarget (Binding.cvar Authority.access_only
            CaptureBound.unbound)).consCVar (.unbound .epsilon) BVar.here).srcCtx) :=
      CapyCaptureSet.compile_accessOnly hcohB (CapyTy.IsClosed.captureSet hT1cl)
        (by simp only [CompilerCtx.consCVar_capyCtx, CompilerCtx.weakenTarget_capyCtx, hΓ]
            exact hT1ao)
    have hcabs1 := HasType.cabs (cs := {})
      (CaptureBound.IsClosed.bound
        (CapyCaptureSet.compile_isClosed (CapyTy.IsClosed.captureSet hT1cl)
          hcoh.srcClosed.weaken.consCVar))
      hb2AO habs
    have hcabs2 := HasType.cabs (cs := {}) CaptureBound.IsClosed.unbound trivial hcabs1
    exact ⟨_, hcabs2⟩
  case app =>
    intro s2 ctx hΓ hcoh hinj hnpp
    rename_i Γ0 xv D yv T1 T2 hxao hDcl hDao hyao hx hy hsep ihx ihy
    subst hΓ
    -- ── PLAN (2026-07-02; see [[project_capybara_translation]]).  Both premises
    -- are variable-typed, so NO η-expansion `letin`s for the subjects: invert
    -- them source-side (`CapyHasType.var_typ_inversion`, AppSupport.lean) to a
    -- context lookup + source subtyping, compile the lookup through
    -- `Coherent.varLookup` + `HasType.var` + `Subtyp.self_refine`, and transport
    -- the source subtyping by K1 (`CapySubtyp.compile`).  The application itself
    -- is a 4-step ANF chain (all heads access-only, so `HasType.letin_ao`):
    --   letin (capp bvx ⟦D⟧)                                    -- c  ↦ ⟦D⟧
    --     (letin (capp #0 ⟦{ε y}⟧↑)                             -- cx ↦ ⟦{ε y}⟧
    --       (letin (app #0 bvy↑↑)                               -- β
    --         (unwrap #0)))                                     -- open the modal
    -- `cx` is instantiated with the ARGUMENT's image (not the domain's full
    -- latent!) so the codomain modal's `W = ⟦{ε x}⟧↑↑ ∪ {ε cx}` instantiates to
    -- `⟦{ε x}⟧ ∪ ⟦{ε y}⟧` — exactly the conclusion capture.  The `HasType.var`
    -- self-refinement supplies each rule's self-capture subject shape for free.
    obtain ⟨x, T0x, rfl, hlookx, hsubx, hArrCl⟩ :
        ∃ (x : BVar _ .var) (T0 : CapyTy .capt _), xv = .bound x ∧
          ctx.capyCtx.LookupVar x T0 ∧
          CapySubtyp ctx.capyCtx
            (.typ (T0.refineCaptureSet (.var (.M .epsilon) (.bound x))))
            (.typ (.arrow T1 (.var (.M .epsilon) xv) T2)) ∧
          (CapyTy.typ (.arrow T1 (.var (.M .epsilon) xv) T2)).IsClosed := by
      sorry -- TOOLKIT (in flight): CapyHasType.var_typ_inversion hx
    obtain ⟨y, T0y, rfl, hlooky, hsuby, hT1DCl⟩ :
        ∃ (y : BVar _ .var) (T0 : CapyTy .capt _), yv = .bound y ∧
          ctx.capyCtx.LookupVar y T0 ∧
          CapySubtyp ctx.capyCtx
            (.typ (T0.refineCaptureSet (.var (.M .epsilon) (.bound y))))
            (.typ (T1.subst (CapySubst.openCVar D))) ∧
          (CapyTy.typ (T1.subst (CapySubst.openCVar D))).IsClosed := by
      sorry -- TOOLKIT (in flight): CapyHasType.var_typ_inversion hy
    obtain ⟨bvx, _, _, hcorelkx⟩ := hcoh.varLookup hlookx
    obtain ⟨bvy, _, _, hcorelky⟩ := hcoh.varLookup hlooky
    have hT0xCl : T0x.IsClosed := CapyCtx.lookupVar_isClosed hlookx hcoh.capyClosed
    -- read-only provenance for K1 (`SubCoherent.roLookup`): every source cvar
    -- declared `.unbound .ro` carries a target `HasKind _ _ .ro` witness from its
    -- enclosing lock's `MutabilityCtx`.  `Coherent` does not track this yet — it
    -- needs its own threading (a `Coherent` field or a compile hypothesis),
    -- mirroring how `CapyCaptureBound.mutabilityCtx` records `({c}, ro)`.
    have hro : ∀ {c : BVar _ .cvar} {a : CapyAuthority} {cb : CapyCaptureBound _},
        ctx.capyCtx.LookupCVar c a cb → cb = .unbound .ro →
        HasKind ctx.coreCtx (.cvar (.M .epsilon) (ctx.srcCtx.lookupCVar c)) .ro := by
      sorry -- FOLLOW-UP: ro-provenance threading
    -- the function subject, at its compiled source-ASSIGNED arrow type (the K1
    -- transport of the inverted source subtyping), compile-normalized
    have hK1x := CapySubtyp.compile hsubx ctx rfl (hcoh.toSubCoherent hro)
      (CapyTy.IsClosed.typ (CapyTy.IsClosed.refineCaptureSet hT0xCl
        CapyCaptureSet.IsClosed.var_bound))
      hArrCl
    simp only [CapyTy.compile] at hK1x
    have hArrTgtCl : (CapyTy.compile
        (.typ (.arrow T1 (.var (.M .epsilon) (.bound x)) T2)) ctx).IsClosed :=
      CapyTy.compile_isClosed _ _ hArrCl hcoh.srcClosed
    simp only [CapyTy.compile] at hArrTgtCl
    have hfun := HasType.subtyp (HasType.var hcoh.closed hcorelkx) Subcapt.refl
      (Subtyp.trans
        (Ty.IsClosed.typ (CapyTy.compile_isClosed _ _
          (CapyTy.IsClosed.refineCaptureSet hT0xCl CapyCaptureSet.IsClosed.var_bound)
          hcoh.srcClosed))
        (Subtyp.typ (Subtyp.self_refine hcorelkx))
        hK1x)
      CaptureSet.IsClosed.empty
      hArrTgtCl
    -- ── step 1: instantiate the self cvar `c ↦ ⟦D⟧` (re-bound the outer cpoly
    -- contravariantly by `Subbound.top`, enlarge the capture to the self form).
    have hDtCl : (CapyCaptureSet.compile D ctx.srcCtx).IsClosed :=
      CapyCaptureSet.compile_isClosed hDcl hcoh.srcClosed
    have hDtVal : CaptureBound.IsValid ctx.coreCtx
        (.bound (CapyCaptureSet.compile D ctx.srcCtx)) :=
      CapyCaptureSet.compile_accessOnly hcoh hDcl hDao
    have haccx : (CaptureSet.var (.M .epsilon) (.bound bvx)).accessible ctx.coreCtx := by
      sorry -- FOLLOW-UP: `Ctx.AllAlive` threading (AppSupport.lean toolkit)
    have hfun2 := HasType.subtyp hfun Subcapt.refl
      (Subtyp.typ (Subtyp.cpoly
        (Subbound.top (B := .bound (CapyCaptureSet.compile D ctx.srcCtx)))
        (Subcapt.sc_elem
          (CaptureSet.Subset.empty (C := .var (.M .epsilon) (.bound bvx))))
        Subtyp.refl))
      CaptureSet.IsClosed.empty
      (by sorry) -- re-bounded tower closedness (mechanical)
    have hstep1 := HasType.capp (I := {}) haccx hDtCl hDtVal hfun2
    -- ── steps 2–4 + the letin fold (WIP): capp₂ needs the subject re-bounded to
    -- `⟦{ε y}⟧↑` (`Subbound.capset` from `CapySubtyp.captureSet_subcapt hsuby`,
    -- compiled by `CapySubcapt.compile`); the `app` step fits the argument via
    -- the B2c domain bridge at `[c ↦ D]` + the `{cx}`-realign (an `openVar`
    -- instance package for OpenCVarSubtyp does NOT exist yet); `unwrap` needs
    -- `Satisfy` from the source `CapySepCheck` premise (compile transport via
    -- the `compile_peakSepCtx_subcapt_sep` family); the three `letin_ao` folds
    -- need the heads' `AccessOnly` (peaksVarBound-unfold through the stored
    -- types to `⟦{ε x}⟧`, then `compile_accessOnly hxao`) and per-level capture
    -- re-expression by `sc_var`; the innermost body finally bridges the opened
    -- codomain to `⟦T2[openVar y]⟧` (B2c composite at `[C ↦ D, x ↦ y]`).
    sorry
  -- Remaining cases (tabs, cabs, tapp, capp,
  -- letin, letin_unpack, alloc, drop, read, write, cond, par, invoke, subtyp)
  -- are WIP: discharged incrementally.
  all_goals (intro s2 ctx hΓ hcoh hinj hnpp; sorry)

end Compilation
