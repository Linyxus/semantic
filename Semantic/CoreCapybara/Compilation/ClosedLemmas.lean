import Semantic.CoreCapybara.Compilation.CompileLemmas
open CoreCapybara
namespace Compilation

/-!
# Closedness preservation for compilation

The target subsumption rule (`HasType.subtyp`) demands that the *widened* capture
set and type be closed (`IsClosed`).  Term compilation widens through subsumption
constantly, so we need: compiling a closed source capture set / type yields a
closed target one.  Capture-set compilation reads variable images out of the
source→target map; those images must themselves be closed, captured by the
predicate `SrcCtx.VarsClosed`, which every context builder preserves.
-/

/-- A source→target map is *closed-valued* when every term-variable image is a
    closed capture set.  This is the only non-structural ingredient of
    `CapyCaptureSet.compile`'s closedness (capture- and type-variable images compile
    to closed `.cvar`/`.tvar` atoms unconditionally). -/
def SrcCtx.VarsClosed (ctx : SrcCtx s1 s2) : Prop :=
  ∀ (x : BVar s1 .var), (ctx.lookupVar x).IsClosed

theorem SrcCtx.VarsClosed.weaken {ctx : SrcCtx s1 s2} (h : ctx.VarsClosed)
    {ρ : Rename s2 s2'} : (ctx.rename ρ).VarsClosed := by
  intro x
  rw [SrcCtx.lookupVar_rename]
  exact CaptureSet.rename_isClosed (h x)

theorem SrcCtx.VarsClosed.consVar {ctx : SrcCtx s1 s2} (h : ctx.VarsClosed)
    {bv : Option (BVar s2 .var)} {cs : CaptureSet s2} (hcs : cs.IsClosed) :
    (SrcCtx.cons (.var bv cs) ctx).VarsClosed := by
  intro x
  cases x with
  | here => exact hcs
  | there x => exact h x

theorem SrcCtx.VarsClosed.consCVar {ctx : SrcCtx s1 s2} (h : ctx.VarsClosed)
    {c : BVar s2 .cvar} : (SrcCtx.cons (.cvar c) ctx).VarsClosed := by
  intro x
  cases x with
  | there x => exact h x

theorem SrcCtx.VarsClosed.consTVar {ctx : SrcCtx s1 s2} (h : ctx.VarsClosed)
    {X : BVar s2 .tvar} : (SrcCtx.cons (.tvar X) ctx).VarsClosed := by
  intro x
  cases x with
  | there x => exact h x

/-- Compiling a closed source capture set in a closed-valued map yields a closed
    target capture set. -/
theorem CapyCaptureSet.compile_isClosed {cs : CapyCaptureSet s1} {ctx : SrcCtx s1 s2}
    (hc : cs.IsClosed) (hctx : ctx.VarsClosed) : (CapyCaptureSet.compile cs ctx).IsClosed := by
  induction cs with
  | empty => exact CaptureSet.IsClosed.empty
  | union cs1 cs2 ih1 ih2 =>
    cases hc with | union h1 h2 => exact CaptureSet.IsClosed.union (ih1 h1) (ih2 h2)
  | cvar a c => exact CaptureSet.IsClosed.cvar
  | var a x =>
    cases hc with
    | var_bound =>
      simp only [CapyCaptureSet.compile]
      exact CaptureSet.applyAccess_isClosed (hctx _)
  | pseudo_peak _ _ =>
    simp only [CapyCaptureSet.compile]
    exact CaptureSet.IsClosed.empty

/-- Compiling a closed source capture bound in a closed-valued map yields a closed
    target capture bound. -/
theorem CapyCaptureBound.compile_isClosed {cb : CapyCaptureBound s1} {ctx : SrcCtx s1 s2}
    (hc : cb.IsClosed) (hctx : ctx.VarsClosed) :
    (CapyCaptureBound.compile cb ctx).IsClosed := by
  cases cb with
  | unbound m => exact CaptureBound.IsClosed.unbound
  | bound cs =>
    cases hc with | bound hcs =>
    exact CaptureBound.IsClosed.bound (CapyCaptureSet.compile_isClosed hcs hctx)

/-- A peak item is built solely from capture-variable atoms, hence closed. -/
theorem peakItem_isClosed {P : CapyPeakSet s} {c : BVar s .cvar} : (peakItem P c).IsClosed := by
  simp only [peakItem]
  induction (accessedAt P c) with
  | nil => exact CapyCaptureSet.IsClosed.empty
  | cons a as ih => exact CapyCaptureSet.IsClosed.union CapyCaptureSet.IsClosed.cvar ih

/-- The peak-separation context of a peak set is closed when the source→target map
    is closed-valued.  (Each item compiles a peak item, which is closed.) -/
theorem peakSepCtx_isClosed {P : CapyPeakSet s1} {ctx : SrcCtx s1 s2}
    (hctx : ctx.VarsClosed) : (peakSepCtx P ctx).IsClosed := by
  simp only [peakSepCtx]
  suffices h : ∀ (l : List (BVar s1 .cvar)) (acc : SepCtx s2), acc.IsClosed →
      (l.foldl (fun K c => .cons K (CapyCaptureSet.compile (peakItem P c) ctx)) acc).IsClosed by
    exact h _ .empty SepCtx.IsClosed.empty
  intro l
  induction l with
  | nil => intro acc hacc; exact hacc
  | cons c cs ih =>
    intro acc hacc
    simp only [List.foldl_cons]
    exact ih _ (SepCtx.IsClosed.cons hacc (CapyCaptureSet.compile_isClosed peakItem_isClosed hctx))

/-- The mutability obligation of a capture bound is closed. -/
theorem CapyCaptureBound.mutabilityCtx_isClosed {cb : CapyCaptureBound s1}
    {c : BVar s2 .cvar} : (CapyCaptureBound.mutabilityCtx cb c).IsClosed := by
  cases cb with
  | unbound m =>
    exact MutabilityCtx.IsClosed.cons MutabilityCtx.IsClosed.empty CaptureSet.IsClosed.cvar
  | bound cs => exact MutabilityCtx.IsClosed.empty

/-- A closed source type has a closed capture set. -/
theorem CapyTy.IsClosed.captureSet {T : CapyTy .capt s} (h : T.IsClosed) :
    T.captureSet.IsClosed := by
  cases h <;>
    first
    | exact CapyCaptureSet.IsClosed.empty
    | assumption

/-- Refining the capture set of a closed type with a closed capture set keeps it
    closed. -/
theorem CapyTy.IsClosed.refineCaptureSet {T : CapyTy .capt s} {cs : CapyCaptureSet s}
    (h : T.IsClosed) (hcs : cs.IsClosed) : (T.refineCaptureSet cs).IsClosed := by
  cases h with
  | top => exact .top
  | tvar => exact .tvar
  | arrow h1 _ h2 => exact .arrow h1 hcs h2
  | poly h1 _ h2 => exact .poly h1 hcs h2
  | cpoly hcb _ hT => exact .cpoly hcb hcs hT
  | unit => exact .unit
  | cap _ => exact .cap hcs
  | bool => exact .bool
  | cell _ => exact .cell hcs

/-- Renaming a closed source capture bound keeps it closed. -/
theorem CapyCaptureBound.IsClosed.rename {cb : CapyCaptureBound s1} (h : cb.IsClosed)
    {f : Rename s1 s2} : (cb.rename f).IsClosed := by
  cases h with
  | unbound => exact .unbound
  | bound hcs => exact .bound (CapyCaptureSet.rename_isClosed hcs)

/-- Renaming a closed source type keeps it closed. -/
theorem CapyTy.IsClosed.rename {sort : CapyTySort} {s1 : Sig} {T : CapyTy sort s1}
    (h : T.IsClosed) : ∀ {s2 : Sig} (f : Rename s1 s2), (T.rename f).IsClosed := by
  induction h with
  | top => intro _ _; exact .top
  | tvar => intro _ _; exact .tvar
  | arrow _ hcs _ ih1 ih2 =>
    intro _ f; exact .arrow (ih1 f.lift) (CapyCaptureSet.rename_isClosed hcs) (ih2 f.lift)
  | poly _ hcs _ ih1 ih2 =>
    intro _ f; exact .poly (ih1 f) (CapyCaptureSet.rename_isClosed hcs) (ih2 f.lift)
  | cpoly hcb hcs _ ih =>
    intro _ f
    exact .cpoly (CapyCaptureBound.IsClosed.rename hcb) (CapyCaptureSet.rename_isClosed hcs)
      (ih f.lift)
  | unit => intro _ _; exact .unit
  | cap hcs => intro _ _; exact .cap (CapyCaptureSet.rename_isClosed hcs)
  | bool => intro _ _; exact .bool
  | cell hcs => intro _ _; exact .cell (CapyCaptureSet.rename_isClosed hcs)
  | exi _ ih => intro _ f; exact .exi (ih f.lift)
  | typ _ ih => intro _ f; exact .typ (ih f)

/-- A term variable looked up in a closed source context has a closed type. -/
theorem CapyCtx.lookupVar_isClosed {Γ : CapyCtx s} {x : BVar s .var} {T : CapyTy .capt s}
    (h : Γ.LookupVar x T) : Γ.IsClosed → T.IsClosed := by
  induction h with
  | here =>
    intro hΓ; cases hΓ with | push _ hb => cases hb with
    | var hT => exact CapyTy.IsClosed.rename hT _
  | there _ ih =>
    intro hΓ; cases hΓ with | push hΓ' _ => exact CapyTy.IsClosed.rename (ih hΓ') _

/-! ### `VarsClosed` preservation, phrased on compiler-context builders. -/

theorem CompilerCtx.weakenTarget_VarsClosed {ctx : CompilerCtx s1 s2} {k : Kind}
    {b : Binding s2 k} (h : ctx.srcCtx.VarsClosed) : (ctx.weakenTarget b).srcCtx.VarsClosed := by
  simp only [CompilerCtx.weakenTarget_srcCtx]; exact h.weaken

theorem CompilerCtx.consVar_VarsClosed {ctx : CompilerCtx s1 s2} {T : CapyTy .capt s1}
    {bv : Option (BVar s2 .var)} {cs : CaptureSet s2}
    (h : ctx.srcCtx.VarsClosed) (hcs : cs.IsClosed) :
    (ctx.consVar T bv cs).srcCtx.VarsClosed := by
  simp only [CompilerCtx.consVar_srcCtx]; exact h.consVar hcs

theorem CompilerCtx.consCVar_VarsClosed {ctx : CompilerCtx s1 s2} {cb : CapyCaptureBound s1}
    {c : BVar s2 .cvar} (h : ctx.srcCtx.VarsClosed) :
    (ctx.consCVar cb c).srcCtx.VarsClosed := by
  simp only [CompilerCtx.consCVar_srcCtx]; exact h.consCVar

theorem CompilerCtx.consTVar_VarsClosed {ctx : CompilerCtx s1 s2} {S : CapyPureTy s1}
    {X : BVar s2 .tvar} (h : ctx.srcCtx.VarsClosed) :
    (ctx.consTVar S X).srcCtx.VarsClosed := by
  simp only [CompilerCtx.consTVar_srcCtx]; exact h.consTVar

/-- **Closedness preservation for type compilation.**  Compiling a closed source
    type in a closed-valued compiler context yields a closed target type. -/
theorem CapyTy.compile_isClosed {sort : CapyTySort} {s1 s2 : Sig}
    (T : CapyTy sort s1) (ctx : CompilerCtx s1 s2) :
    T.IsClosed → ctx.srcCtx.VarsClosed → (CapyTy.compile T ctx).IsClosed := by
  fun_induction CapyTy.compile T ctx
  case case1 => intro _ _; exact Ty.IsClosed.top
  case case2 => intro _ _; exact Ty.IsClosed.unit
  case case3 => intro _ _; exact Ty.IsClosed.bool
  case case4 =>
    intro hT hctx; cases hT with | cap hcs =>
    exact Ty.IsClosed.cap (CapyCaptureSet.compile_isClosed hcs hctx)
  case case5 =>
    intro hT hctx; cases hT with | cell hcs =>
    exact Ty.IsClosed.cell (CapyCaptureSet.compile_isClosed hcs hctx)
  case case6 =>
    intro hT hctx; cases hT with | cell hcs =>
    exact Ty.IsClosed.reader (CapyCaptureSet.compile_isClosed hcs hctx)
  case case7 =>
    intro hT hctx; rename_i ih; cases hT with | typ hT =>
    exact Ty.IsClosed.typ (ih hT hctx)
  case case8 => intro _ _; exact Ty.IsClosed.tvar
  case case9 =>
    intro hT hctx
    rename_i Tdom csarr Earr ctx0 ctxB ctxDomain ctxE ctxLock Wv Psiv ih2 ih1
    cases hT with | arrow hTdom hcs hEcl =>
    have hB : ctxB.srcCtx.VarsClosed :=
      CompilerCtx.consCVar_VarsClosed (CompilerCtx.weakenTarget_VarsClosed hctx)
    have hDom : ctxDomain.srcCtx.VarsClosed :=
      CompilerCtx.consVar_VarsClosed
        (CompilerCtx.consCVar_VarsClosed
          (CompilerCtx.weakenTarget_VarsClosed (CompilerCtx.weakenTarget_VarsClosed hctx)))
        CaptureSet.IsClosed.cvar
    have hLock : ctxLock.srcCtx.VarsClosed :=
      CompilerCtx.consVar_VarsClosed
        (CompilerCtx.consCVar_VarsClosed
          (CompilerCtx.weakenTarget_VarsClosed
            (CompilerCtx.weakenTarget_VarsClosed (CompilerCtx.weakenTarget_VarsClosed hctx))))
        CaptureSet.IsClosed.cvar
    have hctxE : ctxE.srcCtx.VarsClosed :=
      CompilerCtx.consVar_VarsClosed
        (CompilerCtx.weakenTarget_VarsClosed
          (CompilerCtx.weakenTarget_VarsClosed (CompilerCtx.weakenTarget_VarsClosed hctx)))
        CaptureSet.IsClosed.cvar
    exact Ty.IsClosed.cpoly CaptureBound.IsClosed.unbound CaptureSet.IsClosed.empty
      (Ty.IsClosed.typ
        (Ty.IsClosed.cpoly
          (CaptureBound.IsClosed.bound
            (CapyCaptureSet.compile_isClosed (CapyTy.IsClosed.captureSet hTdom) hB))
          CaptureSet.IsClosed.empty
          (Ty.IsClosed.typ
            (Ty.IsClosed.arrow
              (ih2 (CapyTy.IsClosed.refineCaptureSet (CapyTy.IsClosed.rename hTdom Rename.succ)
                      CapyCaptureSet.IsClosed.var_bound) hDom)
              CaptureSet.IsClosed.empty
              (Ty.IsClosed.typ
                (Ty.IsClosed.modal
                  (CapyCaptureSet.compile_isClosed
                    (CapyCaptureSet.IsClosed.union
                      (CapyCaptureSet.rename_isClosed (CapyCaptureSet.rename_isClosed hcs))
                      CapyCaptureSet.IsClosed.var_bound)
                    hLock)
                  ⟨peakSepCtx_isClosed hLock, MutabilityCtx.IsClosed.empty⟩
                  (ih1 hEcl hctxE)))))))
  case case10 =>
    intro hT hctx
    rename_i Sv csv Ev ctx0 ctxE Cfv Psiv ihS ihE
    cases hT with | poly hS hcs hE =>
    exact Ty.IsClosed.poly
      (ihS hS hctx)
      CaptureSet.IsClosed.empty
      (Ty.IsClosed.typ
        (Ty.IsClosed.modal
          (CapyCaptureSet.compile_isClosed hcs hctx.weaken)
          ⟨peakSepCtx_isClosed hctx.weaken, MutabilityCtx.IsClosed.empty⟩
          (ihE hE (CompilerCtx.consTVar_VarsClosed (CompilerCtx.weakenTarget_VarsClosed hctx)))))
  case case11 =>
    intro hT hctx
    rename_i cbv csv Ev ctx0 ctxE Cfv Psiv ih
    cases hT with | cpoly hcb hcs hE =>
    exact Ty.IsClosed.cpoly
      (CapyCaptureBound.compile_isClosed hcb hctx)
      CaptureSet.IsClosed.empty
      (Ty.IsClosed.typ
        (Ty.IsClosed.modal
          (CapyCaptureSet.compile_isClosed hcs hctx.weaken)
          ⟨peakSepCtx_isClosed hctx.weaken, CapyCaptureBound.mutabilityCtx_isClosed⟩
          (ih hE (CompilerCtx.consCVar_VarsClosed (CompilerCtx.weakenTarget_VarsClosed hctx)))))
  case case12 =>
    intro hT hctx; rename_i ih; cases hT with | exi hTinner =>
    exact Ty.IsClosed.exi
      (ih hTinner (CompilerCtx.consCVar_VarsClosed (CompilerCtx.weakenTarget_VarsClosed hctx)))

end Compilation
