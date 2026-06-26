import Semantic.CoreCapybara.Compilation.TypeCompiler
open CoreCapybara
namespace Compilation

/-!
# Infrastructure for term compilation

Foundational lemmas about how the compilation functions (`CaptureSet.compile`,
`CapyCaptureBound.compile`, `CapyTy.compile`) interact with *target* renaming.
These underpin the context-coherence invariant and the lookup-transport lemmas
used by the term-compilation preservation theorem.
-/

/-- Looking up a capture variable in a target-renamed source context renames the
    looked-up image. -/
theorem SrcCtx.lookupCVar_rename {ctx : SrcCtx s1 s2} {ρ : Rename s2 s2'}
    {c : BVar s1 .cvar} :
    (ctx.rename ρ).lookupCVar c = ρ.var (ctx.lookupCVar c) := by
  induction ctx generalizing s2' with
  | empty => nomatch c
  | cons info rest ih =>
    cases c with
    | here => cases info; rfl
    | there c => simp only [SrcCtx.rename, SrcCtx.lookupCVar]; exact ih

/-- Looking up the capture-set image of a term variable in a target-renamed
    source context renames the image. -/
theorem SrcCtx.lookupVar_rename {ctx : SrcCtx s1 s2} {ρ : Rename s2 s2'}
    {x : BVar s1 .var} :
    (ctx.rename ρ).lookupVar x = (ctx.lookupVar x).rename ρ := by
  induction ctx generalizing s2' with
  | empty => nomatch x
  | cons info rest ih =>
    cases x with
    | here => cases info; rfl
    | there x => simp only [SrcCtx.rename, SrcCtx.lookupVar]; exact ih

/-- `CaptureSet.compile` commutes with target renaming of the source context. -/
theorem CaptureSet.compile_rename {cs : CaptureSet s1} {ctx : SrcCtx s1 s2}
    {ρ : Rename s2 s2'} :
    CaptureSet.compile cs (ctx.rename ρ) = (CaptureSet.compile cs ctx).rename ρ := by
  induction cs with
  | empty => rfl
  | union cs1 cs2 ih1 ih2 =>
    simp only [CaptureSet.compile, CaptureSet.rename, ih1, ih2]
  | cvar a c =>
    simp only [CaptureSet.compile, CaptureSet.rename, SrcCtx.lookupCVar_rename]
  | var a x =>
    cases x with
    | bound x =>
      simp only [CaptureSet.compile, SrcCtx.lookupVar_rename,
        CaptureSet.applyAccess_rename]
    | free n => rfl

/-- `CapyCaptureBound.compile` commutes with target renaming of the source
    context. -/
theorem CapyCaptureBound.compile_rename {cb : CapyCaptureBound s1}
    {ctx : SrcCtx s1 s2} {ρ : Rename s2 s2'} :
    CapyCaptureBound.compile cb (ctx.rename ρ)
      = (CapyCaptureBound.compile cb ctx).rename ρ := by
  cases cb with
  | unbound m => rfl
  | bound cs =>
    simp only [CapyCaptureBound.compile, CaptureBound.rename, CaptureSet.compile_rename]

/-- Looking up a type variable in a target-renamed source context renames the
    looked-up image. -/
theorem SrcCtx.lookupTVar_rename {ctx : SrcCtx s1 s2} {ρ : Rename s2 s2'}
    {X : BVar s1 .tvar} :
    (ctx.rename ρ).lookupTVar X = ρ.var (ctx.lookupTVar X) := by
  induction ctx generalizing s2' with
  | empty => nomatch X
  | cons info rest ih =>
    cases X with
    | here => cases info; rfl
    | there X => simp only [SrcCtx.rename, SrcCtx.lookupTVar]; exact ih

/-- Foldl/rename fusion underlying `peakSepCtx_rename`: renaming the result of the
    `peakSepCtx` fold equals folding with the renamed source context, starting
    from the renamed accumulator. -/
private theorem peakSepCtx_foldl_rename {P : PeakSet s1} {ctx : SrcCtx s1 s2}
    {ρ : Rename s2 s2'} :
    ∀ (l : List (BVar s1 .cvar)) (acc : SepCtx s2),
    (l.foldl (fun K c => .cons K (CaptureSet.compile (peakItem P c) ctx)) acc).rename ρ
      = l.foldl (fun K c => .cons K (CaptureSet.compile (peakItem P c) (ctx.rename ρ)))
          (acc.rename ρ)
  | [], acc => rfl
  | c :: cs, acc => by
    simp only [List.foldl_cons]
    rw [peakSepCtx_foldl_rename cs]
    simp only [SepCtx.rename, CaptureSet.compile_rename]

/-- The peak-separation context commutes with target renaming of the source
    context (the peak set itself lives in the source signature and is unchanged). -/
theorem peakSepCtx_rename {P : PeakSet s1} {ctx : SrcCtx s1 s2} {ρ : Rename s2 s2'} :
    peakSepCtx P (ctx.rename ρ) = (peakSepCtx P ctx).rename ρ := by
  simp only [peakSepCtx]
  rw [peakSepCtx_foldl_rename]
  rfl

/-! ### Renaming of source-context maps commutes with composition. -/

theorem SrcBinderInfo.rename_comp {info : SrcBinderInfo k s2} {f : Rename s2 s3}
    {g : Rename s3 s4} :
    (info.rename f).rename g = info.rename (f.comp g) := by
  cases info with
  | var bv cs =>
    simp only [SrcBinderInfo.rename, CaptureSet.rename_comp, Option.map_map]
    rfl
  | cvar c => rfl
  | tvar X => rfl

theorem SrcCtx.rename_comp {ctx : SrcCtx s1 s2} {f : Rename s2 s3} {g : Rename s3 s4} :
    (ctx.rename f).rename g = ctx.rename (f.comp g) := by
  induction ctx generalizing s3 s4 with
  | empty => rfl
  | cons info rest ih =>
    simp only [SrcCtx.rename, SrcBinderInfo.rename_comp, ih]

/-! ### Builder field projections (definitional; exposed as simp lemmas). -/

@[simp] theorem CompilerCtx.weakenTarget_capyCtx {ctx : CompilerCtx s1 s2}
    {b : Binding s2 k} : (ctx.weakenTarget b).capyCtx = ctx.capyCtx := rfl
@[simp] theorem CompilerCtx.weakenTarget_srcCtx {ctx : CompilerCtx s1 s2}
    {b : Binding s2 k} :
    (ctx.weakenTarget b).srcCtx = ctx.srcCtx.rename Rename.succ := rfl
@[simp] theorem CompilerCtx.consCVar_capyCtx {ctx : CompilerCtx s1 s2}
    {cb : CapyCaptureBound s1} {c : BVar s2 .cvar} :
    (ctx.consCVar cb c).capyCtx = ctx.capyCtx.push_cvar_default cb := rfl
@[simp] theorem CompilerCtx.consCVar_srcCtx {ctx : CompilerCtx s1 s2}
    {cb : CapyCaptureBound s1} {c : BVar s2 .cvar} :
    (ctx.consCVar cb c).srcCtx = .cons (.cvar c) ctx.srcCtx := rfl
@[simp] theorem CompilerCtx.consVar_capyCtx {ctx : CompilerCtx s1 s2}
    {T : CapyTy .capt s1} {bv : Option (BVar s2 .var)} {cs : CaptureSet s2} :
    (ctx.consVar T bv cs).capyCtx = ctx.capyCtx.push_var T := rfl
@[simp] theorem CompilerCtx.consVar_srcCtx {ctx : CompilerCtx s1 s2}
    {T : CapyTy .capt s1} {bv : Option (BVar s2 .var)} {cs : CaptureSet s2} :
    (ctx.consVar T bv cs).srcCtx = .cons (.var bv cs) ctx.srcCtx := rfl
@[simp] theorem CompilerCtx.consTVar_capyCtx {ctx : CompilerCtx s1 s2}
    {S : CapyPureTy s1} {X : BVar s2 .tvar} :
    (ctx.consTVar S X).capyCtx = ctx.capyCtx.push_tvar S := rfl
@[simp] theorem CompilerCtx.consTVar_srcCtx {ctx : CompilerCtx s1 s2}
    {S : CapyPureTy s1} {X : BVar s2 .tvar} :
    (ctx.consTVar S X).srcCtx = .cons (.tvar X) ctx.srcCtx := rfl

/-! ### Source-context map renaming commutes with `Rename.succ` weakening. -/

theorem SrcCtx.rename_succ_comm {sc : SrcCtx s1 s2} {ρ : Rename s2 s2'} :
    (sc.rename ρ).rename (Rename.succ (k:=k)) = (sc.rename Rename.succ).rename ρ.lift := by
  simp only [SrcCtx.rename_comp, Rename.succ_lift_comm]

/-! ### The `RenamesTo` relation: two compiler contexts agreeing on the source
typing context, with `ρ`-related source→target maps.  Each builder preserves it
(lifting `ρ` when the target signature grows), which is exactly the data
`CapyTy.compile_rename` threads through its recursive calls. -/

/-- `ctx.RenamesTo ctx' ρ` holds when `ctx'` agrees with `ctx` on the source
    typing context and its source→target map is the `ρ`-renaming of `ctx`'s.
    Only the two fields `CapyTy.compile` actually reads are constrained. -/
structure CompilerCtx.RenamesTo (ctx : CompilerCtx s1 s2) (ctx' : CompilerCtx s1 s2')
    (ρ : Rename s2 s2') : Prop where
  capy : ctx'.capyCtx = ctx.capyCtx
  src : ctx'.srcCtx = ctx.srcCtx.rename ρ

theorem CompilerCtx.RenamesTo.weakenTarget {ctx : CompilerCtx s1 s2}
    {ctx' : CompilerCtx s1 s2'} {ρ : Rename s2 s2'} (h : ctx.RenamesTo ctx' ρ)
    (b : Binding s2 k := placeholderBinding k) (b' : Binding s2' k := placeholderBinding k) :
    (ctx.weakenTarget b).RenamesTo (ctx'.weakenTarget b') ρ.lift where
  capy := by simp only [CompilerCtx.weakenTarget_capyCtx, h.capy]
  src := by
    simp only [CompilerCtx.weakenTarget_srcCtx, h.src]
    exact SrcCtx.rename_succ_comm

theorem CompilerCtx.RenamesTo.consCVar {ctx : CompilerCtx s1 s2}
    {ctx' : CompilerCtx s1 s2'} {ρ : Rename s2 s2'} (h : ctx.RenamesTo ctx' ρ)
    {cb : CapyCaptureBound s1} {c : BVar s2 .cvar} :
    (ctx.consCVar cb c).RenamesTo (ctx'.consCVar cb (ρ.var c)) ρ where
  capy := by simp only [CompilerCtx.consCVar_capyCtx, h.capy]
  src := by
    simp only [CompilerCtx.consCVar_srcCtx, h.src, SrcCtx.rename, SrcBinderInfo.rename]

theorem CompilerCtx.RenamesTo.consVar {ctx : CompilerCtx s1 s2}
    {ctx' : CompilerCtx s1 s2'} {ρ : Rename s2 s2'} (h : ctx.RenamesTo ctx' ρ)
    {T : CapyTy .capt s1} {bv : Option (BVar s2 .var)} {cs : CaptureSet s2} :
    (ctx.consVar T bv cs).RenamesTo (ctx'.consVar T (bv.map ρ.var) (cs.rename ρ)) ρ where
  capy := by simp only [CompilerCtx.consVar_capyCtx, h.capy]
  src := by
    simp only [CompilerCtx.consVar_srcCtx, h.src, SrcCtx.rename, SrcBinderInfo.rename]

theorem CompilerCtx.RenamesTo.consTVar {ctx : CompilerCtx s1 s2}
    {ctx' : CompilerCtx s1 s2'} {ρ : Rename s2 s2'} (h : ctx.RenamesTo ctx' ρ)
    {S : CapyPureTy s1} {X : BVar s2 .tvar} :
    (ctx.consTVar S X).RenamesTo (ctx'.consTVar S (ρ.var X)) ρ where
  capy := by simp only [CompilerCtx.consTVar_capyCtx, h.capy]
  src := by
    simp only [CompilerCtx.consTVar_srcCtx, h.src, SrcCtx.rename, SrcBinderInfo.rename]

/-- The mutability obligation a capture bound imposes on the freshly bound `c`
    (`.here`) is invariant under renaming that fixes `.here` (a lift). -/
theorem CapyCaptureBound.mutabilityCtx_rename_here {cb : CapyCaptureBound s1}
    {ρ : Rename s2 s2'} :
    (CapyCaptureBound.mutabilityCtx cb (.here : BVar (s2,,Kind.cvar) .cvar)).rename ρ.lift
      = CapyCaptureBound.mutabilityCtx cb (.here : BVar (s2',,Kind.cvar) .cvar) := by
  cases cb with
  | unbound m =>
    simp only [CapyCaptureBound.mutabilityCtx, MutabilityCtx.rename, CaptureSet.rename, Rename.lift]
  | bound cs => rfl

/-- `CapyTy.compile` commutes with target renaming: compiling a type in a
    compiler context whose source→target map is the `ρ`-renaming of another's
    (and which agrees on the source typing context) yields the `ρ`-renamed
    compilation.  This is the type-level analogue of `CaptureSet.compile_rename`,
    and the device that lets compilation be threaded through context extensions.
    Proved by functional induction on `CapyTy.compile`; the recursive
    (arrow/poly/cpoly/exi) cases use `CompilerCtx.RenamesTo` to transport the
    hypotheses through the builders. -/
theorem CapyTy.compile_rename {sort : CapyTySort} {s1 s2 : Sig}
    (T : CapyTy sort s1) (ctx : CompilerCtx s1 s2) :
    ∀ {s2' : Sig} (ctx' : CompilerCtx s1 s2') (ρ : Rename s2 s2'),
    ctx'.capyCtx = ctx.capyCtx →
    ctx'.srcCtx = ctx.srcCtx.rename ρ →
    CapyTy.compile T ctx' = (CapyTy.compile T ctx).rename ρ := by
  fun_induction CapyTy.compile T ctx
  case case1 => intro _ _ _ _ _; simp only [CapyTy.compile, Ty.rename]
  case case2 => intro _ _ _ _ _; simp only [CapyTy.compile, Ty.rename]
  case case3 => intro _ _ _ _ _; simp only [CapyTy.compile, Ty.rename]
  case case4 => intro _ _ _ _ h; simp only [CapyTy.compile, Ty.rename, h, CaptureSet.compile_rename]
  case case5 => intro _ _ _ _ h; simp only [CapyTy.compile, Ty.rename, h, CaptureSet.compile_rename]
  case case6 => intro _ _ _ _ h; simp only [CapyTy.compile, Ty.rename, h, CaptureSet.compile_rename]
  case case7 =>
    intro s2' ctx' ρ hcapy hsrc; rename_i ih
    simp only [CapyTy.compile, Ty.rename]; exact congrArg Ty.typ (ih ctx' ρ hcapy hsrc)
  case case8 => intro _ _ _ _ h; simp only [CapyTy.compile, Ty.rename, h, SrcCtx.lookupTVar_rename]
  case case9 =>
    intro s2' ctx' ρ hcapy hsrc
    rename_i _ _ Tdom _ _ _ _ _ _ _ _ _ ihDom ihE
    have h0 : CompilerCtx.RenamesTo _ ctx' ρ := ⟨hcapy, hsrc⟩
    have hB : CompilerCtx.RenamesTo _
        (ctx'.weakenTarget.consCVar (.unbound .epsilon) .here) ρ.lift :=
      h0.weakenTarget.consCVar (c := .here)
    have hDom : CompilerCtx.RenamesTo _
        ((ctx'.weakenTarget.weakenTarget.consCVar (.unbound .epsilon) (.there .here)).consVar
          Tdom none (.cvar (.M .epsilon) .here)) ρ.lift.lift :=
      (h0.weakenTarget.weakenTarget.consCVar (c := .there .here)).consVar
        (T := Tdom) (bv := none) (cs := .cvar (.M .epsilon) .here)
    have hLock : CompilerCtx.RenamesTo _
        ((ctx'.weakenTarget.weakenTarget.weakenTarget.consCVar (.unbound .epsilon)
            (.there (.there .here))).consVar Tdom (some .here)
          (.cvar (.M .epsilon) (.there .here))) ρ.lift.lift.lift :=
      (h0.weakenTarget.weakenTarget.weakenTarget.consCVar (c := .there (.there .here))).consVar
        (T := Tdom) (bv := some .here) (cs := .cvar (.M .epsilon) (.there .here))
    have hE : CompilerCtx.RenamesTo _
        (ctx'.weakenTarget.weakenTarget.weakenTarget.consVar .top (some .here)
          (.cvar (.M .epsilon) (.there .here))) ρ.lift.lift.lift :=
      (((h0.weakenTarget (b := placeholderBinding .cvar)).weakenTarget
        (b := placeholderBinding .cvar)).weakenTarget (b := placeholderBinding .var)).consVar
        (T := .top) (bv := some .here) (cs := .cvar (.M .epsilon) (.there .here))
    simp (config := { zetaDelta := true }) only [CapyTy.compile, Ty.rename]
    congr 1
    congr 1
    congr 1
    · congr 1
      rw [hB.src]
      exact CaptureSet.compile_rename
    · congr 1
      congr 1
      · exact ihDom _ _ hDom.capy hDom.src
      · congr 1
        congr 1
        · rw [hLock.src]
          exact CaptureSet.compile_rename
        · simp only [ModalCtx.rename, MutabilityCtx.rename, hLock.capy]
          congr 1
          rw [hLock.src]
          exact peakSepCtx_rename
        · exact ihE _ _ hE.capy hE.src
  case case10 =>
    intro s2' ctx' ρ hcapy hsrc
    rename_i s1v s2v Sv csv Ev ctxv ctxEv Cfv Psiv ihS ihE
    have hE : CompilerCtx.RenamesTo (ctxv.weakenTarget.consTVar .top .here)
        (ctx'.weakenTarget.consTVar .top .here) ρ.lift :=
      (CompilerCtx.RenamesTo.mk hcapy hsrc).weakenTarget.consTVar (X := .here)
    simp (config := { zetaDelta := true }) only [CapyTy.compile, Ty.rename]
    congr 1
    · exact ihS _ _ hcapy hsrc
    · congr 1
      congr 1
      · rw [SrcCtx.weaken, SrcCtx.weaken, hsrc, SrcCtx.rename_succ_comm]
        exact CaptureSet.compile_rename
      · simp only [ModalCtx.rename, MutabilityCtx.rename, hcapy]
        congr 1
        rw [SrcCtx.weaken, SrcCtx.weaken, hsrc, SrcCtx.rename_succ_comm]
        exact peakSepCtx_rename
      · exact ihE _ _ hE.capy hE.src
  case case11 =>
    intro s2' ctx' ρ hcapy hsrc
    rename_i s1v s2v cbv csv Ev ctxv ctxEv Cfv Psiv ih
    have hE : CompilerCtx.RenamesTo (ctxv.weakenTarget.consCVar cbv .here)
        (ctx'.weakenTarget.consCVar cbv .here) ρ.lift :=
      (CompilerCtx.RenamesTo.mk hcapy hsrc).weakenTarget.consCVar (cb := cbv) (c := .here)
    simp (config := { zetaDelta := true }) only [CapyTy.compile, Ty.rename]
    congr 1
    · rw [hsrc]; exact CapyCaptureBound.compile_rename
    · congr 1
      congr 1
      · rw [SrcCtx.weaken, SrcCtx.weaken, hsrc, SrcCtx.rename_succ_comm]
        exact CaptureSet.compile_rename
      · simp only [ModalCtx.rename, hcapy]
        congr 1
        · rw [SrcCtx.weaken, SrcCtx.weaken, hsrc, SrcCtx.rename_succ_comm]
          exact peakSepCtx_rename
        · exact CapyCaptureBound.mutabilityCtx_rename_here.symm
      · exact ih _ _ hE.capy hE.src
  case case12 =>
    intro s2' ctx' ρ hcapy hsrc; rename_i ih
    have hE : CompilerCtx.RenamesTo _
        (ctx'.weakenTarget.consCVar (.unbound .epsilon) .here) ρ.lift :=
      (CompilerCtx.RenamesTo.mk hcapy hsrc).weakenTarget.consCVar (c := .here)
    have eE := ih _ _ hE.capy hE.src
    simp only [CapyTy.compile, Ty.rename]; exact congrArg Ty.exi eE

end Compilation
