import Semantic.CoreCapybara.Compilation.Coherence
import Semantic.CoreCapybara.Compilation.SubstLemmas
import Semantic.CoreCapybara.Compilation.SubtypCompile
import Semantic.CoreCapybara.Compilation.OpenCVarSubtyp
import Semantic.CoreCapybara.Compilation.TargetRename
import Semantic.CoreCapybara.Compilation.SepCheckCompile
import Semantic.CoreCapybara.Compilation.AppSupport
import Semantic.CoreCapybara.Compilation.UnshiftLock
import Semantic.CoreCapybara.Compilation.AppChain
import Semantic.CoreCapybara.Compilation.AppFinalCapture
import Semantic.CoreCapybara.Compilation.AppSatisfy
import Semantic.CoreCapybara.Compilation.SepRestrict
import Semantic.CoreCapybara.Compilation.ArgFitTopPure
import Semantic.CoreCapybara.Capybara.TypeSystem.UseCovered
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
    ctx.coreCtx.AllAlive → ctx.SepCovered Cs →
    ∃ e' : Exp s2, HasType (CapyCaptureSet.compile Cs ctx.srcCtx) ctx.coreCtx e'
      (CapyTy.compile E ctx) := by
  induction hty
  case unit =>
    intro s2 ctx hΓ hcoh hinj hnpp halive hcov
    refine ⟨.unit, ?_⟩
    simp only [CapyCaptureSet.compile, CapyTy.compile]
    exact HasType.unit
  case btrue =>
    intro s2 ctx hΓ hcoh hinj hnpp halive hcov
    refine ⟨.btrue, ?_⟩
    simp only [CapyCaptureSet.compile, CapyTy.compile]
    exact HasType.btrue
  case bfalse =>
    intro s2 ctx hΓ hcoh hinj hnpp halive hcov
    refine ⟨.bfalse, ?_⟩
    simp only [CapyCaptureSet.compile, CapyTy.compile]
    exact HasType.bfalse
  case var =>
    intro s2 ctx hΓ hcoh hinj hnpp halive hcov
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
    intro s2 ctx hΓ hcoh hinj hnpp halive hcov
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
    intro s2 ctx hΓ hcoh hinj hnpp halive hcov
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
    intro s2 ctx hΓ hcoh hinj hnpp halive hcov
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
      (fun h => Mutability.noConfusion (CapyCaptureBound.unbound.inj h))
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
    -- ── The wrap lock, built BEFORE the IH: the body compiles UNDER it — this is
    -- what establishes the body's ambient covering (`SepCovered.of_lock`), the
    -- target-side payment for the source's `sep_distinct` axiom.
    have hvcLock : ctxLockR.srcCtx.VarsClosed :=
      ((hcoh.srcClosed.weaken.weaken.weaken).consCVar).consVar CaptureSet.IsClosed.cvar
    set Ψc : ModalCtx (s2,C,C,x) := ⟨peakSepCtx ctxLockR.capyCtx
      (CapyCaptureSet.peakset ctxLockR.capyCtx
        ((cs0.rename Rename.succ).rename Rename.succ
          ∪ CapyCaptureSet.var (.M .epsilon) (.bound .here)))
      ctxLockR.srcCtx, MutabilityCtx.empty⟩ with hΨc
    have hΨcl : Ψc.IsClosed :=
      ⟨peakSepCtx_isClosed (CapyCaptureSet.peaks_isClosed _ _) hvcLock,
        MutabilityCtx.IsClosed.empty⟩
    set ctxLock5 := ctxLockR.weakenTarget (Binding.lock Ψc) with hctxLock5
    have hcohLock5 : ctxLock5.Coherent :=
      hcohLock.weakenTarget (Binding.IsClosed.lock hΨcl)
    have hinjL5 : ctxLock5.srcCtx.CVarInjective :=
      SrcCtx.CVarInjective.rename hinjL Rename.injective_succ
    have halive5 : ctxLock5.coreCtx.AllAlive :=
      ((((halive.push_cvar (fun h => Authority.noConfusion h)).push_cvar
        (fun h => Authority.noConfusion h)).push_var).push_lock)
    have hlkΨ : Ctx.LookupLock ctxLock5.coreCtx BVar.here
        ⟨peakSepCtx ctxLock5.capyCtx (CapyCaptureSet.peakset ctxLock5.capyCtx
          ((cs0.rename Rename.succ).rename Rename.succ
            ∪ CapyCaptureSet.var (.M .epsilon) (.bound .here))) ctxLock5.srcCtx,
         MutabilityCtx.empty.rename Rename.succ⟩ := by
      have hΨeq : Ψc.rename (Rename.succ (k := Kind.lock))
          = (⟨peakSepCtx ctxLock5.capyCtx (CapyCaptureSet.peakset ctxLock5.capyCtx
              ((cs0.rename Rename.succ).rename Rename.succ
                ∪ CapyCaptureSet.var (.M .epsilon) (.bound .here))) ctxLock5.srcCtx,
             MutabilityCtx.empty.rename Rename.succ⟩ : ModalCtx _) := by
        rw [hΨc]
        simp only [ModalCtx.rename]
        congr 1
        exact peakSepCtx_rename.symm
      exact hΨeq ▸ Ctx.LookupLock.here (Γ := ctxLockR.coreCtx) (Ψ := Ψc)
    have hcov5 := CompilerCtx.SepCovered.of_lock hlkΨ
    -- ── The IH under the lock.
    obtain ⟨eb5, heb5⟩ := ih ctxLock5 hΓL hcohLock5 hinjL5 hnppL halive5 hcov5
    -- the lock binder is invisible to expression syntax: unshift the body witness
    obtain ⟨eb, rfl⟩ := Exp.unshift_lock eb5
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
    -- realign the capture/type compiles down to `ctxLockR` + `.rename succ`
    have heqCap : CapyCaptureSet.compile
        ((cs0.rename Rename.succ).rename Rename.succ
          ∪ CapyCaptureSet.var (.M .epsilon) (.bound .here)) ctxLock5.srcCtx
        = (CapyCaptureSet.compile
            ((cs0.rename Rename.succ).rename Rename.succ
              ∪ CapyCaptureSet.var (.M .epsilon) (.bound .here))
            ctxLockR.srcCtx).rename Rename.succ :=
      CapyCaptureSet.compile_rename
    have heqBody : CapyTy.compile (T2.rename Rename.implicit_cvar) ctxLock5
        = (CapyTy.compile (T2.rename Rename.implicit_cvar)
            ((ctx.weakenTarget.weakenTarget.weakenTarget.consCVar
                (CapyCaptureBound.unbound Mutability.epsilon)
                (BVar.there (BVar.there BVar.here))).consVar
              T1 (some BVar.here)
              (CaptureSet.cvar (Access.M Mutability.epsilon)
                (BVar.there BVar.here)))).rename Rename.succ :=
      (CapyTy.compile_rename _ ctxLockR ctxLock5 Rename.succ rfl rfl).trans
        (congrArg (fun T => T.rename (Rename.succ (k := Kind.lock))) heqT2)
    have hwk : HasType
        ((CapyCaptureSet.compile
            ((cs0.rename Rename.succ).rename Rename.succ
              ∪ CapyCaptureSet.var (.M .epsilon) (.bound .here))
            ctxLockR.srcCtx).rename Rename.succ)
        ctxLock5.coreCtx (eb.rename Rename.succ)
        ((CapyTy.compile (T2.rename Rename.implicit_cvar)
            ((ctx.weakenTarget.weakenTarget.weakenTarget.consCVar
                (CapyCaptureBound.unbound Mutability.epsilon)
                (BVar.there (BVar.there BVar.here))).consVar
              T1 (some BVar.here)
              (CaptureSet.cvar (Access.M Mutability.epsilon)
                (BVar.there BVar.here)))).rename Rename.succ) := by
      rw [← heqCap, ← heqBody]
      exact heb5
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
        (fun h => Mutability.noConfusion (CapyCaptureBound.unbound.inj h))
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
    intro s2 ctx hΓ hcoh hinj hnpp halive hcov
    rename_i Γ0 xv D yv T1 T2 hxao hDcl hDao hyao hDnpp hT1npp hT2npp hT1ao hx hy hsep ihx ihy
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
    obtain ⟨x, rfl, hxorig, hArrCl⟩ := CapyHasType.var_typ_inversion hx
    -- a cell never subtypes an arrow, so the FUNCTION's readonly origin refutes
    obtain ⟨T0x, hlookx, hsubx⟩ :
        ∃ T0 : CapyTy .capt _, ctx.capyCtx.LookupVar x T0 ∧
          CapySubtyp ctx.capyCtx
            (.typ (T0.refineCaptureSet (.var (.M .epsilon) (.bound x))))
            (.typ (.arrow T1 (.var (.M .epsilon) (.bound x)) T2)) := by
      rcases hxorig with h | ⟨Cc, _, hcell⟩
      · exact h
      · exact (CapySubtyp.cell_not_arrow hcell).elim
    obtain ⟨y, rfl, hyorig, hT1DCl⟩ := CapyHasType.var_typ_inversion hy
    cases hyorig with
    | inr hcellOrig =>
      -- ARGUMENT READ-ONLY ORIGIN (`y` is a cell read through its readonly
      -- view): the same ANF chain with an extra `reader`-head `letin` supplying
      -- the argument value.  Deferred until the var-origin main line closes.
      sorry
    | inl hvarOrig =>
    obtain ⟨T0y, hlooky, hsuby⟩ := hvarOrig
    obtain ⟨bvx, _, _, hcorelkx⟩ := hcoh.varLookup hlookx
    obtain ⟨bvy, _, _, hcorelky⟩ := hcoh.varLookup hlooky
    have hT0xCl : T0x.IsClosed := CapyCtx.lookupVar_isClosed hlookx hcoh.capyClosed
    -- the function subject, at its compiled source-ASSIGNED arrow type (the K1
    -- transport of the inverted source subtyping), compile-normalized
    have hK1x := CapySubtyp.compile hsubx ctx rfl hcoh.toSubCoherent
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
    have haccx : (CaptureSet.var (.M .epsilon) (.bound bvx)).accessible ctx.coreCtx :=
      CaptureSet.accessible_of_allAlive halive _
    have hfun2 := HasType.subtyp hfun Subcapt.refl
      (Subtyp.typ (Subtyp.cpoly
        (Subbound.top (B := .bound (CapyCaptureSet.compile D ctx.srcCtx)))
        (Subcapt.sc_elem
          (CaptureSet.Subset.empty (C := .var (.M .epsilon) (.bound bvx))))
        Subtyp.refl))
      CaptureSet.IsClosed.empty
      (by -- re-bounded tower closedness: rebuild `hArrTgtCl` with the new bound
          -- `⟦D⟧` (closed by `hDtCl`) and self capture `{ε bvx}` (a bound var)
        cases hArrTgtCl with
        | typ h1 =>
          cases h1 with
          | cpoly hb hcs hin =>
            exact Ty.IsClosed.typ (Ty.IsClosed.cpoly (CaptureBound.IsClosed.bound hDtCl)
              CaptureSet.IsClosed.var_bound hin))
    have hstep1 := HasType.capp (I := {}) haccx hDtCl hDtVal hfun2
    simp only [Ty.subst, CaptureSet.subst, CaptureBound.subst] at hstep1
    -- ── step 2: bind `x1` (the `c ↦ ⟦D⟧`-instantiated tower) and instantiate the
    -- re-abstraction cvar `cx ↦ ⟦{ε y}⟧↑`.  `x1`'s `HasType.var` self-refinement
    -- puts the self capture `{ε x1}` in the cpoly's cs slot; the outer bound is
    -- re-bounded contravariantly to the ARGUMENT's image (`Subbound.capset` on the
    -- compiled `captureSet_subcapt hsuby`, bridged by `compile_subst_openCVar`).
    -- The level-1 compiler context (target-only push of `x1`):
    set B2D : CaptureSet s2 := (CapyCaptureSet.compile T1.captureSet
        (ctx.weakenTarget.consCVar (CapyCaptureBound.unbound Mutability.epsilon)
          BVar.here).srcCtx).subst
      (Subst.openCVar (CapyCaptureSet.compile D ctx.srcCtx)) with hB2D
    -- the compiled argument image and its subcapture below the instantiated bound
    have hsubY : Subcapt ctx.coreCtx
        (CapyCaptureSet.compile (.var (.M .epsilon) (.bound y)) ctx.srcCtx) B2D := by
      -- source chain: `{ε y} ⊑ (T0y^{εy}).captureSet ⊑ (T1[D/c]).captureSet`
      -- (for non-capturing heads the refined capture set IS the stored `∅`,
      -- reached by `sc_var` instead)
      have hyAtom : CapySubcapt ctx.capyCtx (.var (.M .epsilon) (.bound y))
          ((T0y.refineCaptureSet (.var (.M .epsilon) (.bound y))).captureSet) := by
        cases T0y <;>
          first
            | exact CapySubcapt.sc_elem CapyCaptureSet.Subset.refl
            | exact CapySubcapt.sc_var hlooky
      have hsc := CapySubcapt.sc_trans hyAtom
        (CapySubtyp.captureSet_subcapt hsuby.typ_typ_dest)
      rw [CapyTy.captureSet_subst_openCVar] at hsc
      have hc := CapySubcapt.compile hsc ctx rfl hcoh.toSubCoherent
      have heq : CapyCaptureSet.compile
          (T1.captureSet.subst (CapySubst.openCVar D)) ctx.srcCtx = B2D := by
        rw [hB2D]
        exact CapyCaptureSet.compile_subst_openCVar
      exact heq ▸ hc
    set Cy : CaptureSet s2 :=
      CapyCaptureSet.compile (.var (.M .epsilon) (.bound y)) ctx.srcCtx with hCy_def
    -- ── The compiled arrow's lock ingredients: `CapyTy.compile`'s arrow-case
    -- `ctxDomain`/`ctxLock`/`W`/`Ψ` at THIS arrow (capture `{ε x}`, domain `T1`),
    -- named so the payload-defining conjuncts below can state the concrete forms.
    set ctxDomA := ((ctx.weakenTarget.weakenTarget).consCVar
        (CapyCaptureBound.unbound Mutability.epsilon) (BVar.there BVar.here)).consVar T1 none
        (CaptureSet.cvar (Access.M Mutability.epsilon) BVar.here) with hctxDomA
    set ctxLockA := ((ctx.weakenTarget.weakenTarget.weakenTarget).consCVar
        (CapyCaptureBound.unbound Mutability.epsilon)
        (BVar.there (BVar.there BVar.here))).consVar T1 (some BVar.here)
        (CaptureSet.cvar (Access.M Mutability.epsilon) (BVar.there BVar.here)) with hctxLockA
    set WsrcA := (((CapyCaptureSet.var (.M .epsilon) (.bound x)).rename
        Rename.succ).rename Rename.succ) ∪
        (CapyCaptureSet.var (.M .epsilon) (.bound .here)) with hWsrcA
    set ΨaA : ModalCtx _ := ⟨peakSepCtx ctxLockA.capyCtx
        (CapyCaptureSet.peakset ctxLockA.capyCtx WsrcA) ctxLockA.srcCtx,
        MutabilityCtx.empty⟩ with hΨaA
    -- ── Abstract hstep1's compiled leaf payloads (arrow domain `M`, codomain lock
    -- capture `W`, lock record `Ψ`, codomain `E`) to opaque names so the ANF chain
    -- reasons over the cpoly/arrow/modal SKELETON, not the raw compiled terms —
    -- WITH defining-equation conjuncts (each `rfl` at instantiation: the spine's
    -- `simp only` normalizations are definitional) so the bridge proofs can
    -- recover the concrete compiled forms.
    obtain ⟨M, W, Ψ, E, hst1, hMeq, hWeq, hΨeq, hEeq⟩ :
        ∃ (M : Ty .capt (s2,C)) (W : CaptureSet (s2,C,x))
          (Ψ : ModalCtx (s2,C,x)) (E : Ty .exi (s2,C,x)),
          HasType (.var (.M .epsilon) (.bound bvx)) ctx.coreCtx
            (.capp (.bound bvx) (CapyCaptureSet.compile D ctx.srcCtx))
            (.typ (.cpoly (.bound B2D) ∅
              (.typ (.arrow M ∅ (.typ (.modal W Ψ E)))))) ∧
          M = (CapyTy.compile ((T1.rename Rename.succ).refineCaptureSet
                (.var (.M .epsilon) (.bound .here))) ctxDomA).subst
              ((Subst.openCVar (CapyCaptureSet.compile D ctx.srcCtx)).lift) ∧
          W = (CapyCaptureSet.compile WsrcA ctxLockA.srcCtx).subst
              (((Subst.openCVar (CapyCaptureSet.compile D ctx.srcCtx)).lift).lift) ∧
          Ψ = ΨaA.subst
              (((Subst.openCVar (CapyCaptureSet.compile D ctx.srcCtx)).lift).lift) ∧
          E = (CapyTy.compile (T2.rename Rename.implicit_cvar) ctxLockA).subst
              (((Subst.openCVar (CapyCaptureSet.compile D ctx.srcCtx)).lift).lift) :=
      ⟨_, _, _, _, hstep1, rfl, rfl, rfl, rfl⟩
    set T1sub : Ty .capt s2 :=
      .cpoly (.bound B2D) ∅ (.typ (.arrow M ∅ (.typ (.modal W Ψ E)))) with hT1sub_def
    have hT1subCl : T1sub.IsClosed := by
      have h := hst1.type_is_closed; cases h with | typ h => exact h
    -- ── Level 1: push `x1 : T1sub`.  Self-refined lookup, then re-bound the outer
    -- cpoly CONTRAVARIANTLY to the argument image `⟦{ε y}⟧↑` (`Subbound.capset` on
    -- `hsubY` weakened past the binder), and instantiate `cx ↦ ⟦{ε y}⟧↑`.
    have hΓ1cl : (ctx.coreCtx.push (Binding.var T1sub)).IsClosed :=
      Ctx.IsClosed.push hcoh.closed (Binding.IsClosed.var hT1subCl)
    have hx1 := HasType.var hΓ1cl (Ctx.LookupVar.here (Γ := ctx.coreCtx) (T := T1sub))
    have hT1subCl' : (Ty.cpoly (CaptureBound.bound B2D) ∅
        (M.arrow ∅ (Ty.modal W Ψ E).typ).typ).IsClosed := hT1sub_def ▸ hT1subCl
    obtain ⟨hB2Dcl, -, hBody1cl⟩ :
        (CaptureBound.bound B2D).IsClosed ∧ (∅ : CaptureSet s2).IsClosed ∧
          (Ty.arrow M ∅ (Ty.modal W Ψ E).typ).typ.IsClosed := by
      cases hT1subCl' with | cpoly hb hcs hbody => exact ⟨hb, hcs, hbody⟩
    have hyt_cl : Cy.IsClosed :=
      CapyCaptureSet.compile_isClosed CapyCaptureSet.IsClosed.var_bound hcoh.srcClosed
    -- re-bound the outer cpoly CONTRAVARIANTLY to the argument image `⟦{ε y}⟧↑`
    have hx1' := HasType.subtyp hx1 (Subcapt.sc_elem CaptureSet.Subset.refl)
      (Subtyp.typ (Subtyp.cpoly
        (Subbound.capset (Subcapt.weaken hsubY (Binding.var T1sub)))
        (Subcapt.sc_elem CaptureSet.Subset.refl)
        Subtyp.refl))
      CaptureSet.IsClosed.empty
      (Ty.IsClosed.typ (Ty.IsClosed.cpoly
        (CaptureBound.IsClosed.bound (CaptureSet.rename_closed hyt_cl))
        CaptureSet.IsClosed.var_bound (Ty.rename_closed hBody1cl)))
    -- capp₂: instantiate `cx ↦ ⟦{ε y}⟧↑`
    have haccx1 : (CaptureSet.var (.M .epsilon) (.bound .here)).accessible
        (ctx.coreCtx.push (Binding.var T1sub)) :=
      CaptureSet.accessible_of_allAlive halive.push_var _
    have hval2 : CaptureBound.IsValid (ctx.coreCtx.push (Binding.var T1sub))
        (.bound (Cy.rename Rename.succ)) :=
      (CapyCaptureSet.compile_accessOnly hcoh CapyCaptureSet.IsClosed.var_bound hyao).renamesTo
        (Ctx.RenamesTo.weaken (Binding.var T1sub))
    have hstep2 := HasType.capp (I := {}) haccx1 (CaptureSet.rename_closed hyt_cl) hval2 hx1'
    -- Abstract hstep2's arrow-domain / codomain-modal payloads.
    -- Abstract capp₂'s arrow; keep the DEFINING EQUATIONS (`hM2eq` etc.) so the
    -- arg-fit bridge (over `M2`) and the `hst3` equations chain to compiled forms.
    obtain ⟨M2, W2, Ψ2, E2, hst2, hM2eq, hW2eq, hΨ2eq, hE2eq⟩ :
        ∃ (M2 : Ty .capt (s2,x)) (W2 : CaptureSet (s2,x,x))
          (Ψ2 : ModalCtx (s2,x,x)) (E2 : Ty .exi (s2,x,x)),
          HasType (.var (.M .epsilon) (.bound .here)) (ctx.coreCtx.push (Binding.var T1sub))
            (.capp (.bound .here) (Cy.rename Rename.succ))
            (.typ (.arrow M2 ∅ (.typ (.modal W2 Ψ2 E2)))) ∧
          M2 = (M.rename Rename.succ.lift).subst (Subst.openCVar (Cy.rename Rename.succ)) ∧
          W2 = (W.rename Rename.succ.lift.lift).subst
            (Subst.openCVar (Cy.rename Rename.succ)).lift ∧
          Ψ2 = (Ψ.rename Rename.succ.lift.lift).subst
            (Subst.openCVar (Cy.rename Rename.succ)).lift ∧
          E2 = (E.rename Rename.succ.lift.lift).subst
            (Subst.openCVar (Cy.rename Rename.succ)).lift :=
      ⟨_, _, _, _, hstep2, rfl, rfl, rfl, rfl⟩
    -- ── Level 2: push `x2 : A2` (the substituted arrow).  Self-refine (arrow cs
    -- slot → `{ε x2}`), then apply to the twice-weakened compiled argument `bvy`
    -- via the domain-fit bridge.
    have hA2Cl : (M2.arrow ∅ (Ty.modal W2 Ψ2 E2).typ).IsClosed := by
      have h := hst2.type_is_closed; cases h with | typ h => exact h
    obtain ⟨hM2cl, -, -⟩ :
        M2.IsClosed ∧ (∅ : CaptureSet (s2,x)).IsClosed ∧ (Ty.modal W2 Ψ2 E2).typ.IsClosed := by
      cases hA2Cl with | arrow hm hc hcod => exact ⟨hm, hc, hcod⟩
    have hΓ2cl : ((ctx.coreCtx.push (Binding.var T1sub)).push
        (Binding.var (M2.arrow ∅ (Ty.modal W2 Ψ2 E2).typ))).IsClosed :=
      Ctx.IsClosed.push hΓ1cl (Binding.IsClosed.var hA2Cl)
    have hx2 := HasType.var hΓ2cl (Ctx.LookupVar.here
      (Γ := ctx.coreCtx.push (Binding.var T1sub)) (T := M2.arrow ∅ (Ty.modal W2 Ψ2 E2).typ))
    have haccx2 : (CaptureSet.var (.M .epsilon) (.bound .here)).accessible
        ((ctx.coreCtx.push (Binding.var T1sub)).push
          (Binding.var (M2.arrow ∅ (Ty.modal W2 Ψ2 E2).typ))) :=
      CaptureSet.accessible_of_allAlive halive.push_var.push_var _
    have hyarg0 := HasType.var hΓ2cl (Ctx.LookupVar.there
      (b := Binding.var (M2.arrow ∅ (Ty.modal W2 Ψ2 E2).typ))
      (Ctx.LookupVar.there (b := Binding.var T1sub) hcorelky))
    have hargBridge :
        Subtyp ((ctx.coreCtx.push (Binding.var T1sub)).push
            (Binding.var (M2.arrow ∅ (Ty.modal W2 Ψ2 E2).typ)))
          ((((CapyTy.compile (T0y.refineCaptureSet (.var (.M .epsilon) (.bound y))) ctx).rename
              Rename.succ).rename Rename.succ).refineCaptureSet
            (.var (.M .epsilon) (.bound (.there (.there bvy)))))
          (M2.rename Rename.succ) := by
      -- ARG-FIT (app-chain recipe #4): the argument's compiled type fits the
      -- instantiated domain.  K1 (`CapySubtyp.compile hsuby`) gives the SOURCE
      -- subtyping `⟦T0y^{εy}⟧ <: ⟦T1[D]⟧` compiled; weaken it ↑↑ up the tower; then
      -- (a) refine both sides to the argument atom `{ε bvy↑↑}` and (b) ALIGN the
      -- RHS `⟦T1[D]⟧↑↑` with the re-abstracted compiled domain `M2.rename succ`
      -- (the openCVar-family commutation, no slack — hK1ALIGN below).
      have hT0yCl : T0y.IsClosed := CapyCtx.lookupVar_isClosed hlooky hcoh.capyClosed
      have hclT0y : (T0y.refineCaptureSet (.var (.M .epsilon) (.bound y))).IsClosed :=
        CapyTy.IsClosed.refineCaptureSet hT0yCl CapyCaptureSet.IsClosed.var_bound
      have hclT1D : (T1.subst (CapySubst.openCVar D)).IsClosed := by
        cases hT1DCl with | typ h => exact h
      have hK1 : Subtyp ctx.coreCtx
          (CapyTy.compile (T0y.refineCaptureSet (.var (.M .epsilon) (.bound y))) ctx)
          (CapyTy.compile (T1.subst (CapySubst.openCVar D)) ctx) :=
        CapySubtyp.compile hsuby.typ_typ_dest ctx rfl hcoh.toSubCoherent hclT0y hclT1D
      have hK1w := (hK1.renamesTo (Ctx.RenamesTo.weaken (Binding.var T1sub))
          Rename.injective_succ
          (fun hc => Ctx.IsClosed.push hc (Binding.IsClosed.var hT1subCl))).renamesTo
          (Ctx.RenamesTo.weaken (Binding.var (M2.arrow ∅ (Ty.modal W2 Ψ2 E2).typ)))
          Rename.injective_succ
          (fun hc => Ctx.IsClosed.push hc (Binding.IsClosed.var hA2Cl))
      -- hK1w : Subtyp Γ2c (⟦T0y.refine{εy}⟧↑↑) (⟦T1[D]⟧↑↑)
      -- ── Wrapper (mine): refine BOTH sides of hK1w by the argument atom `{ε bvy↑↑}`
      -- (`refine_widen`, TargetRename.lean:1071 — total up to a `B = .top` escape),
      -- then ALIGN the refined RHS `⟦T1[D]⟧↑↑.refine{ε bvy↑↑}` with `M2.rename succ`
      -- via the unconditional openCVar-commutation equation `argFit_align` (app-chain).
      -- The `B = .top` corner (a `Top`-headed source domain fed a pure argument) is
      -- discharged by `argFit_top_pure` (app-chain): `{εy}` is provably non-empty, so
      -- `B = .top` forces `T0y` pure-headed, whence `A.refine{ε bvy↑↑}` is pure and the
      -- goal collapses to `A.refine <: .top` via `Subtyp.top`.
      have hclT1Dc : (CapyTy.compile (T1.subst (CapySubst.openCVar D)) ctx).IsClosed :=
        CapyTy.compile_isClosed _ _ hclT1D hcoh.srcClosed
      -- (1) app-chain: the arg-fit FORWARD subtyping — `compile_subst_subtyp.1`
      -- direction, exactly as fresh's `hB2c` (compile-subst on the LEFT `<:`
      -- compile-then-subst on the RIGHT).  NOT an equation: for a higher-order `T1`
      -- the nested lock records resolve through different contexts (`ctxDomA`'s
      -- param-at-`T1` vs the D-instantiated `ctx`), so they match only up to
      -- subtyping.  Soundness fixes the direction: argument `<:` domain.
      have argFit_align :
          Subtyp ((ctx.coreCtx.push (Binding.var T1sub)).push
              (Binding.var (M2.arrow ∅ (Ty.modal W2 Ψ2 E2).typ)))
            ((((CapyTy.compile (T1.subst (CapySubst.openCVar D)) ctx).rename Rename.succ).rename
              Rename.succ).refineCaptureSet (.var (.M .epsilon) (.bound (.there (.there bvy)))))
            (M2.rename Rename.succ) := sorry
      -- Chain `A.refine{ε bvy↑↑} <: B.refine{ε bvy↑↑}` (refine_widen of hK1w; top corner
      -- via `refine_top_preserved`) THROUGH the domain-fit subtyping `argFit_align`.
      refine Subtyp.trans ?_ ?_ argFit_align
      · exact Ty.refineCaptureSet_closed (Ty.rename_closed (Ty.rename_closed hclT1Dc))
          CaptureSet.IsClosed.var_bound
      · rcases Subtyp.refine_widen hK1w (Subcapt.sc_elem CaptureSet.Subset.refl)
            CaptureSet.IsClosed.var_bound (Ty.rename_closed (Ty.rename_closed hclT1Dc))
            with hsub | hBtop
        · exact hsub
        · -- top corner: B = .top ⇒ goal RHS `B.refine{ε bvy↑↑} = .top`.  Discharge via
          -- `refine_top_preserved`: A <: .top (hK1w↾B=.top); the argument atom `{ε bvy↑↑}`
          -- is `sc_var`-below A's capture (bvy↑↑'s lookup); A is closed.
          exact hBtop ▸ Subtyp.refine_top_preserved (hBtop ▸ hK1w)
            (Subcapt.sc_var (Ctx.LookupVar.there (Ctx.LookupVar.there hcorelky)))
            (Ty.rename_closed (Ty.rename_closed
              (CapyTy.compile_isClosed _ _ hclT0y hcoh.srcClosed)))
    have hyarg := HasType.subtyp hyarg0 (Subcapt.sc_elem CaptureSet.Subset.refl)
      (Subtyp.typ hargBridge) CaptureSet.IsClosed.empty
      (Ty.IsClosed.typ (Ty.rename_closed hM2cl))
    have hstep3 := HasType.app haccx2 hx2 hyarg
    -- Abstract the app-result modal; keep the DEFINING EQUATIONS (`hW3eq`/`hΨ3eq`/
    -- `hE3eq`) so the downstream bridges over `W3`/`Ψ3`/`E3` can recover the
    -- concrete (openVar-substituted) forms.  (`hstep3` also stays in scope.)
    obtain ⟨W3, Ψ3, E3, hst3, hW3eq, hΨ3eq, hE3eq⟩ :
        ∃ (W3 : CaptureSet (s2,x,x)) (Ψ3 : ModalCtx (s2,x,x)) (E3 : Ty .exi (s2,x,x)),
          HasType (.var (.M .epsilon) (.bound .here))
            ((ctx.coreCtx.push (Binding.var T1sub)).push
              (Binding.var (M2.arrow ∅ (Ty.modal W2 Ψ2 E2).typ)))
            (.app (.bound .here) (.bound (.there (.there bvy))))
            (.typ (.modal W3 Ψ3 E3)) ∧
          W3 = (W2.rename Rename.succ.lift).subst
            (Subst.openVar (Var.bound (.there (.there bvy)))) ∧
          Ψ3 = (Ψ2.rename Rename.succ.lift).subst
            (Subst.openVar (Var.bound (.there (.there bvy)))) ∧
          E3 = (E2.rename Rename.succ.lift).subst
            (Subst.openVar (Var.bound (.there (.there bvy)))) :=
      ⟨_, _, _, hstep3, rfl, rfl, rfl⟩
    -- ── goal type/capture abbreviations (`F`, `Cg`), telescoped up the tower.
    set F : Ty .exi s2 :=
      CapyTy.compile (T2.subst (CapySubst.openVar (Var.bound y))) ctx with hF_def
    set Cg : CaptureSet s2 := CapyCaptureSet.compile
      (.var (.M .epsilon) (.bound x) ∪ .var (.M .epsilon) (.bound y)) ctx.srcCtx with hCg_def
    -- an empty capture set is access-only in any context (no peaks to drop)
    have hEmptyAO : ∀ {s' : Sig} {Γ' : Ctx s'},
        (CaptureSet.empty : CaptureSet s').AccessOnly Γ' := by
      intro s' Γ' c hsub
      simp only [CaptureSet.peakset, CaptureSet.peaks] at hsub
      exact absurd hsub (by rintro ⟨⟩)
    -- ── Level 3: push `x3 : modal`.  Self-refine (modal cs slot → `{ε x3}`), then
    -- `unwrap` (Satisfy bridge).
    have hMod3Cl : (Ty.modal W3 Ψ3 E3).IsClosed := by
      have h := hst3.type_is_closed; cases h with | typ h => exact h
    have hΓ3cl : (((ctx.coreCtx.push (Binding.var T1sub)).push
        (Binding.var (M2.arrow ∅ (Ty.modal W2 Ψ2 E2).typ))).push
        (Binding.var (Ty.modal W3 Ψ3 E3))).IsClosed :=
      Ctx.IsClosed.push hΓ2cl (Binding.IsClosed.var hMod3Cl)
    have hx3 := HasType.var hΓ3cl (Ctx.LookupVar.here
      (Γ := (ctx.coreCtx.push (Binding.var T1sub)).push
        (Binding.var (M2.arrow ∅ (Ty.modal W2 Ψ2 E2).typ))) (T := Ty.modal W3 Ψ3 E3))
    have hSat : Satisfy (((ctx.coreCtx.push (Binding.var T1sub)).push
        (Binding.var (M2.arrow ∅ (Ty.modal W2 Ψ2 E2).typ))).push
        (Binding.var (Ty.modal W3 Ψ3 E3))) (Ψ3.rename Rename.succ) := by
      -- the ambient covering + the source `hsep` discharge the collapsed lock
      -- `ΨaA.subst appOpen` at `ctx.coreCtx`; lift it three times up the ANF tower
      -- (`Satisfy.renamesTo` ×3) and match `Ψ3.rename succ` to `(ΨaA.subst appOpen)↑↑↑`
      -- via the payload equations + `ModalCtx.appChain_collapse`.
      have hsat0 := app_satisfy_bridge (yv := Var.bound bvy) hcoh hcoh.toSubCoherent
        hnpp hDnpp hT1npp hT2npp hT1ao hsep hcov (CapyHasType.app_use_covered hx hy)
      have hsat3 := (((hsat0.renamesTo (Ctx.RenamesTo.weaken (Binding.var T1sub))
          Rename.injective_succ).renamesTo
          (Ctx.RenamesTo.weaken (Binding.var (M2.arrow ∅ (Ty.modal W2 Ψ2 E2).typ)))
          Rename.injective_succ).renamesTo
          (Ctx.RenamesTo.weaken (Binding.var (Ty.modal W3 Ψ3 E3))) Rename.injective_succ)
      have heqΨ : Ψ3.rename Rename.succ
          = (((ΨaA.subst (appOpen (CapyCaptureSet.compile D ctx.srcCtx) Cy
              (Var.bound bvy))).rename (Rename.succ (k := Kind.var))).rename
              (Rename.succ (k := Kind.var))).rename (Rename.succ (k := Kind.var)) := by
        rw [hΨ3eq, hΨ2eq, hΨeq]
        exact ModalCtx.appChain_collapse (Dt := CapyCaptureSet.compile D ctx.srcCtx)
          (Cy := Cy) (yv := Var.bound bvy) ΨaA
      exact heqΨ ▸ hsat3
    have hstep4 := HasType.unwrap hx3 hSat
    -- ── name the tower contexts
    set Γ1c := ctx.coreCtx.push (Binding.var T1sub) with hΓ1c
    set Γ2c := Γ1c.push (Binding.var (M2.arrow ∅ (Ty.modal W2 Ψ2 E2).typ)) with hΓ2c
    set Γ3c := Γ2c.push (Binding.var (Ty.modal W3 Ψ3 E3)) with hΓ3c
    -- ── closedness of the telescoped goal type/capture
    have hCgcl : Cg.IsClosed :=
      CapyCaptureSet.compile_isClosed
        (CapyCaptureSet.IsClosed.union CapyCaptureSet.IsClosed.var_bound
          CapyCaptureSet.IsClosed.var_bound) hcoh.srcClosed
    have hT2cl : T2.IsClosed := by
      cases hArrCl with | typ h => cases h with | arrow _ _ ht2 => exact ht2
    have hFcl : F.IsClosed :=
      CapyTy.compile_isClosed _ _
        (CapyTy.is_closed_subst hT2cl (CapySubst.openVar_is_closed Var.IsClosed.bound))
        hcoh.srcClosed
    -- ── head access-only facts (all heads are `{ε _}` self-captures)
    have hao_x1 : (CaptureSet.var (.M .epsilon) (.bound .here)).AccessOnly Γ1c :=
      CaptureSet.var_eps_accessOnly Ctx.LookupVar.here hEmptyAO
    have hao_x2 : (CaptureSet.var (.M .epsilon) (.bound .here)).AccessOnly Γ2c :=
      CaptureSet.var_eps_accessOnly Ctx.LookupVar.here hEmptyAO
    have hTxAO : (CapyTy.compile (T0x.refineCaptureSet (.var (.M .epsilon) (.bound x)))
        ctx).captureSet.AccessOnly ctx.coreCtx := by
      cases T0x with
      | cap cs =>
        simp only [CapyTy.refineCaptureSet, CapyTy.compile, Ty.captureSet]
        exact CapyCaptureSet.compile_accessOnly hcoh CapyCaptureSet.IsClosed.var_bound hxao
      | cell cs m =>
        cases m <;>
          (simp only [CapyTy.refineCaptureSet, CapyTy.compile, Ty.captureSet]
           exact CapyCaptureSet.compile_accessOnly hcoh CapyCaptureSet.IsClosed.var_bound hxao)
      | _ =>
        simp only [CapyTy.refineCaptureSet, CapyTy.compile, Ty.captureSet]
        exact hEmptyAO
    have hao_bvx : (CaptureSet.var (.M .epsilon) (.bound bvx)).AccessOnly ctx.coreCtx :=
      CaptureSet.var_eps_accessOnly hcorelkx hTxAO
    -- ── the codomain / final-capture bridges at the innermost body
    have hCapBridge : Subcapt Γ3c (CaptureSet.var (.M .epsilon) (.bound .here))
        (((Cg.rename Rename.succ).rename Rename.succ).rename Rename.succ) := by
      -- `x3`'s self atom `{ε .here}` lowers (`sc_var`) to its stored modal type's
      -- capture `W3.rename succ`; the ANF chain's payload equations + the σ-chain
      -- collapse (`AppChain`) rewrite `W3.rename succ` to `(Wc.subst appOpen)↑↑↑`,
      -- and `appWc_subst_appOpen` computes `Wc.subst appOpen = ⟦{εx}⟧ ∪ Cy = Cg`.
      have hWcAO : (CapyCaptureSet.compile WsrcA ctxLockA.srcCtx).subst
          (appOpen (CapyCaptureSet.compile D ctx.srcCtx) Cy (Var.bound bvy)) = Cg :=
        appWc_subst_appOpen (ctx := ctx) (x := x) (T1 := T1)
          (Dt := CapyCaptureSet.compile D ctx.srcCtx) (Cy := Cy) (yv := Var.bound bvy)
      have hlk : Subcapt Γ3c (CaptureSet.var (.M .epsilon) (.bound .here))
          ((Ty.modal W3 Ψ3 E3).rename Rename.succ).captureSet :=
        Subcapt.sc_var Ctx.LookupVar.here
      simp only [Ty.rename, Ty.captureSet] at hlk
      -- hlk : Subcapt Γ3c {ε .here} (W3.rename succ)
      -- the σ-chain collapse (with `yv` explicit so its rename-image is a concrete
      -- term) then `hWcAO` (`Wc.subst appOpen = Cg`); `exact` bridges the defeq
      -- between the collapse's `(yv.rename succ).rename succ` and the reduced form.
      have hcollapse := CaptureSet.appChain_collapse
        (X := CapyCaptureSet.compile WsrcA ctxLockA.srcCtx)
        (Dt := CapyCaptureSet.compile D ctx.srcCtx) (Cy := Cy) (yv := Var.bound bvy)
      have heq : W3.rename (Rename.succ (k := Kind.var))
          = (((Cg.rename (Rename.succ (k := Kind.var))).rename (Rename.succ (k := Kind.var))).rename
              (Rename.succ (k := Kind.var))) := by
        rw [hW3eq, hW2eq, hWeq]
        exact hcollapse.trans (congrArg
          (fun z => ((z.rename (Rename.succ (k := Kind.var))).rename
            (Rename.succ (k := Kind.var))).rename (Rename.succ (k := Kind.var))) hWcAO)
      rw [heq] at hlk
      exact hlk
    have hCodBridge : Subtyp Γ3c (E3.rename Rename.succ)
        (((F.rename Rename.succ).rename Rename.succ).rename Rename.succ) := by
      sorry -- BRIDGE(codomain)
    have hbodyC := HasType.subtyp hstep4 hCapBridge hCodBridge
      (CaptureSet.rename_closed (CaptureSet.rename_closed (CaptureSet.rename_closed hCgcl)))
      (Ty.rename_closed (Ty.rename_closed (Ty.rename_closed hFcl)))
    -- ── innermost fold: `letin (app x2 bvy) (unwrap x3)`
    have hinner := HasType.letin_ao CaptureSet.IsClosed.var_bound hao_x2 hst3 hbodyC
    -- massage to the middle letin's body shape
    have hbodyB := HasType.subtyp hinner
      (Subcapt.sc_union
        (Subcapt.sc_trans (Subcapt.sc_var Ctx.LookupVar.here)
          (Subcapt.sc_elem CaptureSet.Subset.empty))
        (Subcapt.sc_elem CaptureSet.Subset.refl))
      Subtyp.refl (CaptureSet.rename_closed (CaptureSet.rename_closed hCgcl))
      (Ty.rename_closed (Ty.rename_closed hFcl))
    -- ── middle fold: `letin (capp x1 ⟦{ε y}⟧↑) inner`
    have hmid := HasType.letin_ao CaptureSet.IsClosed.var_bound hao_x1 hst2 hbodyB
    have hbodyA := HasType.subtyp hmid
      (Subcapt.sc_union
        (Subcapt.sc_trans (Subcapt.sc_var Ctx.LookupVar.here)
          (Subcapt.sc_elem CaptureSet.Subset.empty))
        (Subcapt.sc_elem CaptureSet.Subset.refl))
      Subtyp.refl (CaptureSet.rename_closed hCgcl) (Ty.rename_closed hFcl)
    -- ── outer fold: `letin (capp bvx ⟦D⟧) mid`
    have houter := HasType.letin_ao CaptureSet.IsClosed.var_bound hao_bvx hst1 hbodyA
    -- ── final: bridge the outer capture `{ε bvx} ∪ Cg ⊑ Cg` (the function's
    -- self-capture lowers to `⟦{ε x}⟧ ⊆ Cg`).
    have hTxSub : Subcapt ctx.coreCtx
        (CapyTy.compile (T0x.refineCaptureSet (.var (.M .epsilon) (.bound x))) ctx).captureSet
        (CapyCaptureSet.compile (.var (.M .epsilon) (.bound x)) ctx.srcCtx) := by
      cases T0x with
      | cap cs =>
        simp only [CapyTy.refineCaptureSet, CapyTy.compile, Ty.captureSet]
        exact Subcapt.sc_elem CaptureSet.Subset.refl
      | cell cs m =>
        cases m <;>
          (simp only [CapyTy.refineCaptureSet, CapyTy.compile, Ty.captureSet]
           exact Subcapt.sc_elem CaptureSet.Subset.refl)
      | _ =>
        simp only [CapyTy.refineCaptureSet, CapyTy.compile, Ty.captureSet]
        exact Subcapt.sc_elem CaptureSet.Subset.empty
    have hfinal := HasType.subtyp houter
      (Subcapt.sc_union
        (Subcapt.sc_trans (Subcapt.sc_var hcorelkx)
          (Subcapt.sc_trans hTxSub (Subcapt.sc_elem
            (CaptureSet.Subset.union_right_left CaptureSet.Subset.refl))))
        (Subcapt.sc_elem CaptureSet.Subset.refl))
      Subtyp.refl hCgcl hFcl
    exact ⟨_, hfinal⟩
  -- Remaining cases (tabs, cabs, tapp, capp,
  -- letin, letin_unpack, alloc, drop, read, write, cond, par, invoke, subtyp)
  -- are WIP: discharged incrementally.
  all_goals (intro s2 ctx hΓ hcoh hinj hnpp halive hcov; sorry)

end Compilation
