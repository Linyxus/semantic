import Semantic.CoreCapybara.Compilation.OpenCVarSubtyp
import Semantic.CoreCapybara.Compilation.SepCovered
import Semantic.CoreCapybara.Compilation.AppSatisfy

/-! # `CompileSubstOpenVar`: the covered backward lock-`Satisfy` dispatch.

The codomain bridge of the compiled application needs the backward direction of
`CapyTy.compile_subst_subtyp` (`(compile T ctxOrig).subst σt <: compile (T.subst σ) ctxSub`)
at `σ = openVar y`, where the redirected value parameter `p ↦ y` carries only the
subsumption slack `T0y <: T1[openCVar D]` (not the exact `SubstsTo.var` capture equation
`compile_subst_subtyp` demands).

The K1 lock-*merge* instability that the old `compile_peakSepCtx_sep_backward` comment
warns about is RESOLVED (stable-peak locks ⇒ `subPeakOf_inj`, no merge).  The genuine
residue is a peak *surplus*: the ORIGIN lock is keyed by the faithful (`Γorig`) parameter
type `T1` (the EXPECTED, larger peak set), while the SUB lock is keyed by the argument's
ACTUAL smaller type `T0y`, so a `HasTwoDistinct` of the substituted-origin lock can name an
expected peak with no sub-image.  The ambient covering `SepCovered U` (over `U ⊇` the
expected peaks — the same covering `app_satisfy_bridge` uses) supplies the missing
separations.

`compile_peakSepCtx_sep_backward_covered` is the DISPATCH core: it reduces the
substituted-origin lock's `HasTwoDistinct` to a distinct *stable origin peak* pair and
discharges it from a per-pair covering premise (already transported to `coreCtxW` through
`σtW`).  Establishing that premise from a literal `SepCovered` is the `app_satisfy_bridge`-
style transport, done at the wiring site. -/

open CoreCapybara

namespace Compilation

set_option linter.style.longLine false

/-- **Covered backward lock-`Satisfy` separation half (dispatch core).**
    From a `HasTwoDistinct` of the substituted-origin lock (renamed under the pushed lock
    binder), derive the required `SepCheck` in the SUB-lock context — using a per-pair
    covering premise `hcover` that separates the compiled, `σtW`-substituted key items of
    any two distinct stable ORIGIN peaks.  The peak surplus (expected-vs-actual) is
    invisible here: `peakSepCtx_subst_rename_HasTwoDistinct_ne` already names a distinct
    stable origin pair, and `hcover` covers *all* such pairs (the covering ranges over the
    expected/larger peak set). -/
theorem compile_peakSepCtx_sep_backward_covered {s1 s2w s1' s2w' : Sig}
    {Γorig : CapyCtx s1} {Γsub : CapyCtx s1'}
    {scOrig : SrcCtx s1 s2w} {scSub : SrcCtx s1' s2w'}
    {σ : CapySubst s1 s1'} {σtW : Subst s2w s2w'}
    {cs : CapyCaptureSet s1} {coreCtxW : Ctx s2w'} {ΨmutSub : MutabilityCtx s2w'}
    (hcover : ∀ (p1 p2 : Peak s1),
        p1 ∈ (peakList (CapyCaptureSet.peakset Γorig cs)).filter
          (fun p => decide (Peak.IsStable Γorig p)) →
        p2 ∈ (peakList (CapyCaptureSet.peakset Γorig cs)).filter
          (fun p => decide (Peak.IsStable Γorig p)) →
        p1 ≠ p2 →
        SepCheck coreCtxW
          ((CapyCaptureSet.compile (peakKeyItem (CapyCaptureSet.peakset Γorig cs) p1) scOrig).subst σtW)
          ((CapyCaptureSet.compile (peakKeyItem (CapyCaptureSet.peakset Γorig cs) p2) scOrig).subst σtW)) :
    ∀ (C1 C2 : CaptureSet (s2w',,Kind.lock)),
      (((peakSepCtx Γorig (CapyCaptureSet.peakset Γorig cs) scOrig).subst σtW).rename
        Rename.succ).HasTwoDistinct C1 C2 →
      SepCheck
        (coreCtxW.push_lock
          ({ sep := peakSepCtx Γsub (CapyCaptureSet.peakset Γsub (cs.subst σ)) scSub,
             mutability := ΨmutSub } : ModalCtx s2w'))
        C1 C2 := by
  intro C1 C2 hdist
  obtain ⟨p1, hp1, p2, hp2, hpne, hPdisj⟩ := peakSepCtx_subst_rename_HasTwoDistinct_ne hdist
  rcases hPdisj with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact (hcover p1 p2 hp1 hp2 hpne).renamesTo
      (Ctx.RenamesTo.weaken (Binding.lock _)) Rename.injective_succ
  · exact (hcover p2 p1 hp2 hp1 (Ne.symm hpne)).renamesTo
      (Ctx.RenamesTo.weaken (Binding.lock _)) Rename.injective_succ

end Compilation
