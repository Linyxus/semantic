import Semantic.CoreCapybara.Compilation.AppChain
import Semantic.CoreCapybara.Compilation.CompileLemmas

open CoreCapybara

namespace Compilation

set_option linter.style.longLine false

private theorem compile_cup {s1 s2 : Sig} {A B : CapyCaptureSet s1} {sc : SrcCtx s1 s2} :
    CapyCaptureSet.compile (A ∪ B) sc
      = CapyCaptureSet.compile A sc ∪ CapyCaptureSet.compile B sc := rfl
private theorem subst_cup {s1 s2 : Sig} {P Q : CaptureSet s1} {σ : Subst s1 s2} :
    (P ∪ Q).subst σ = P.subst σ ∪ Q.subst σ := rfl
private theorem rename_succ_var {s : Sig} {k k' : Kind} {y : BVar s k'} :
    (Rename.succ (k := k)).var y = y.there := rfl

theorem appWc_subst_appOpen {s1 s2 : Sig} {ctx : CompilerCtx s1 s2} {x : BVar s1 .var}
    {T1 : CapyTy .capt (s1,C)} {Dt Cy : CaptureSet s2} {yv : Var .var s2} :
    let ctxLockA := ((ctx.weakenTarget.weakenTarget.weakenTarget).consCVar
        (.unbound .epsilon) (.there (.there .here))).consVar T1 (some .here)
        (.cvar (.M .epsilon) (.there .here))
    let WsrcA := (((CapyCaptureSet.var (.M .epsilon) (.bound x)).rename Rename.succ).rename
        Rename.succ) ∪ (CapyCaptureSet.var (.M .epsilon) (.bound .here))
    (CapyCaptureSet.compile WsrcA ctxLockA.srcCtx).subst (appOpen Dt Cy yv)
      = (CapyCaptureSet.compile (.var (.M .epsilon) (.bound x)) ctx.srcCtx) ∪ Cy := by
  intro ctxLockA WsrcA
  simp only [ctxLockA, WsrcA, CompilerCtx.consVar, CompilerCtx.consCVar,
    CompilerCtx.weakenTarget, SrcCtx.weaken]
  rw [compile_cup, subst_cup]
  congr 1
  simp only [CapyCaptureSet.compile, CapyCaptureSet.rename, Var.rename, rename_succ_var]
  rw [CaptureSet.applyAccess_subst]
  congr 1
  change ((((ctx.srcCtx.rename Rename.succ).rename Rename.succ).rename Rename.succ).lookupVar x).subst
      (appOpen Dt Cy yv) = ctx.srcCtx.lookupVar x
  rw [SrcCtx.lookupVar_rename, SrcCtx.lookupVar_rename, SrcCtx.lookupVar_rename,
    CaptureSet.appOpen_weaken_cancel]

end Compilation
