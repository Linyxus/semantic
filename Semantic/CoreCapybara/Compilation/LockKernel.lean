import Semantic.CoreCapybara.Compilation.SubstLemmas
import Semantic.CoreCapybara.Compilation.ContextMorphism
open CoreCapybara
namespace Compilation

/-!
# Shared infrastructure for the function-lock subtyping kernel (K1 / B2c)

Target-level weakening of `Subcapt`/`SepCheck`/`Satisfy` (needed to lift compiled
subcaptures and separations into a `push_lock` context), plus the lock `Satisfy`
assembly used by both `CapySubtyp.compile` (K1) and `compile_subst_subtyp` (B2c).
-/

/-- Renaming preserves capture-set subset (it is structural). -/
theorem CaptureSet.Subset.rename {s1 s2 : Sig} {C1 C2 : CaptureSet s1} {f : Rename s1 s2}
    (h : C1.Subset C2) : (C1.rename f).Subset (C2.rename f) := by
  induction h with
  | refl => exact .refl
  | empty => exact .empty
  | union_left _ _ ih1 ih2 => exact .union_left ih1 ih2
  | union_right_left _ ih => exact .union_right_left ih
  | union_right_right _ ih => exact .union_right_right ih

/-- **`Subcapt` weakening by one binder.**  A subcapture in `Γ` lifts to one in
    `Γ.push b` with both sides `succ`-renamed.  Each `Subcapt` rule transports: the
    lookup rules use `LookupVar.there`/`LookupCVar.there` (which `succ`-rename the
    looked-up type/bound), the mode rules use the `applyMut`/`applyRO`/`applyAccess`
    rename commutations. -/
theorem Subcapt.weaken {s : Sig} {Γ : Ctx s} {C1 C2 : CaptureSet s} {k : Kind}
    (h : Subcapt Γ C1 C2) (b : Binding s k) :
    Subcapt (Γ.push b) (C1.rename Rename.succ) (C2.rename Rename.succ) := by
  induction h with
  | sc_trans _ _ ih1 ih2 => exact Subcapt.sc_trans ih1 ih2
  | sc_elem hsub => exact Subcapt.sc_elem (CaptureSet.Subset.rename hsub)
  | sc_mode hle =>
    simp only [CaptureSet.applyMut_rename]
    exact Subcapt.sc_mode hle
  | sc_union _ _ ih1 ih2 =>
    simp only [CaptureSet.rename]
    exact Subcapt.sc_union ih1 ih2
  | sc_var hlk =>
    simp only [CaptureSet.rename, Var.rename, Rename.succ, ← Ty.captureSet_rename]
    exact Subcapt.sc_var (Ctx.LookupVar.there hlk)
  | sc_cvar hlk =>
    simp only [CaptureSet.rename, Rename.succ]
    exact Subcapt.sc_cvar (Ctx.LookupCVar.there hlk)
  | sc_ro =>
    simp only [CaptureSet.applyRO_rename]
    exact Subcapt.sc_ro
  | sc_ro_mono _ ih =>
    simp only [CaptureSet.applyRO_rename]
    exact Subcapt.sc_ro_mono ih
  | sc_drop_mono _ ih =>
    simp only [CaptureSet.applyAccess_rename]
    exact Subcapt.sc_drop_mono ih

/-! ## `compile` bound-insensitivity congruence

`compile` reads `capyCtx` only through `peaks` (in the lock cases) and `srcCtx`
(lookups), never `coreCtx`/`dstCtx` nor the tvar/cvar bounds of `capyCtx`.  So two
compiler contexts with equal `srcCtx` and pointwise-equal `peaks` compile every
type identically.  This bridges the compiler's placeholder body-context bounds
(`consTVar .top`) and the IH context's real bounds. -/

/-- `peaks` over a pushed context ignores the pushed binder's *bound*: if two
    contexts have the same `peaks` everywhere, so do their extensions by the same
    binder (a var binder reads only its declared type's captures, which agree). -/
theorem CapyCaptureSet.peaks_push_cong {s : Sig} {Γ1 Γ2 : CapyCtx s} {k : Kind}
    (b : CapyBinding s k)
    (h : ∀ W₀ : CapyCaptureSet s,
      CapyCaptureSet.peaks Γ1 W₀ = CapyCaptureSet.peaks Γ2 W₀) :
    ∀ W : CapyCaptureSet (s,,k),
      CapyCaptureSet.peaks (Γ1.push b) W = CapyCaptureSet.peaks (Γ2.push b) W := by
  intro W
  induction W with
  | empty => simp only [CapyCaptureSet.peaks]
  | union W1 W2 ih1 ih2 => simp only [CapyCaptureSet.peaks]; rw [ih1, ih2]
  | cvar m c => simp only [CapyCaptureSet.peaks]
  | pseudo_peak _ ih => simp only [CapyCaptureSet.peaks]; rw [ih]
  | var m x =>
    cases x with
    | free n => simp only [CapyCaptureSet.peaks]
    | bound x0 =>
      simp only [CapyCaptureSet.peaks]
      cases x0 with
      | here =>
        cases b with
        | var T =>
          simp only [CapyCaptureSet.peaksVarBound]
          rw [h T.captureSet]
      | there x1 =>
        simp only [CapyCaptureSet.peaksVarBound]
        have hx := h (.var m (.bound x1))
        simp only [CapyCaptureSet.peaks] at hx
        rw [hx]

/-- `peaks` ignores a pushed *tvar* bound (it adds no term-variable binding). -/
theorem CapyCaptureSet.peaks_push_tvar_irrel {s : Sig} {Γ : CapyCtx s}
    {S1 S2 : CapyPureTy s} :
    ∀ W : CapyCaptureSet (s,X),
      CapyCaptureSet.peaks (Γ.push_tvar S1) W = CapyCaptureSet.peaks (Γ.push_tvar S2) W := by
  intro W
  induction W with
  | empty => simp only [CapyCaptureSet.peaks]
  | union W1 W2 ih1 ih2 => simp only [CapyCaptureSet.peaks]; rw [ih1, ih2]
  | cvar m c => simp only [CapyCaptureSet.peaks]
  | pseudo_peak _ ih => simp only [CapyCaptureSet.peaks]; rw [ih]
  | var m x =>
    cases x with
    | free n => simp only [CapyCaptureSet.peaks]
    | bound x0 =>
      simp only [CapyCaptureSet.peaks, CapyCtx.push_tvar]
      cases x0 with
      | there x1 =>
        conv_lhs => rw [CapyCaptureSet.peaksVarBound.eq_def]
        conv_rhs => rw [CapyCaptureSet.peaksVarBound.eq_def]
        rfl

/-- `peaks` ignores a pushed *cvar* authority/bound (it adds no term-variable binding). -/
theorem CapyCaptureSet.peaks_push_cvar_irrel {s : Sig} {Γ : CapyCtx s}
    {a1 a2 : CapyAuthority} {cb1 cb2 : CapyCaptureBound s} :
    ∀ W : CapyCaptureSet (s,C),
      CapyCaptureSet.peaks (Γ.push_cvar a1 cb1) W
        = CapyCaptureSet.peaks (Γ.push_cvar a2 cb2) W := by
  intro W
  induction W with
  | empty => simp only [CapyCaptureSet.peaks]
  | union W1 W2 ih1 ih2 => simp only [CapyCaptureSet.peaks]; rw [ih1, ih2]
  | cvar m c => simp only [CapyCaptureSet.peaks]
  | pseudo_peak _ ih => simp only [CapyCaptureSet.peaks]; rw [ih]
  | var m x =>
    cases x with
    | free n => simp only [CapyCaptureSet.peaks]
    | bound x0 =>
      simp only [CapyCaptureSet.peaks, CapyCtx.push_cvar]
      cases x0 with
      | there x1 =>
        conv_lhs => rw [CapyCaptureSet.peaksVarBound.eq_def]
        conv_rhs => rw [CapyCaptureSet.peaksVarBound.eq_def]
        rfl

/-- Two compiler contexts agree for `compile`: equal `srcCtx`, pointwise-equal `peaks`,
    and pointwise-agreeing cvar stability (the last is what the peak-separation lock's
    stability filter additionally reads from `capyCtx`, beyond bare `peaks`-behavior). -/
def CompilerCtx.CompileCong {s1 s2 : Sig} (ctx1 ctx2 : CompilerCtx s1 s2) : Prop :=
  ctx1.srcCtx = ctx2.srcCtx ∧
  (∀ W : CapyCaptureSet s1,
    CapyCaptureSet.peaks ctx1.capyCtx W = CapyCaptureSet.peaks ctx2.capyCtx W) ∧
  (∀ c : BVar s1 .cvar, ctx1.capyCtx.IsStableCVar c ↔ ctx2.capyCtx.IsStableCVar c)

/-- Pushing the *same* binding onto both sides of a `CompileCong` context preserves
    cvar-stability agreement: a `.there`-cvar defers to the tail (the pushed binding
    doesn't affect it, by `hstab`), and a fresh `.here` cvar (only reachable through
    `consCVar`, at kind `.cvar`) computes identically on both sides since the *same*
    `b` was pushed on both. -/
theorem CapyCtx.IsStableCVar.push_cong {s : Sig} {Γ1 Γ2 : CapyCtx s} {k : Kind}
    (b : CapyBinding s k) (hstab : ∀ c : BVar s .cvar, Γ1.IsStableCVar c ↔ Γ2.IsStableCVar c) :
    ∀ c : BVar (s,,k) .cvar, (Γ1.push b).IsStableCVar c ↔ (Γ2.push b).IsStableCVar c := by
  intro c
  cases k with
  | cvar =>
    cases b with
    | cvar a cb =>
      cases c with
      | here =>
        unfold CapyCtx.IsStableCVar CapyCtx.lookup_authority CapyCtx.lookup_cvar
        exact Iff.rfl
      | there c' =>
        unfold CapyCtx.IsStableCVar CapyCtx.lookup_authority CapyCtx.lookup_cvar
        simp only [CapyCaptureBound.rename_eq_unbound_iff]
        exact hstab c'
  | var =>
    cases c with
    | there c' =>
      unfold CapyCtx.IsStableCVar CapyCtx.lookup_authority CapyCtx.lookup_cvar
      simp only [CapyCaptureBound.rename_eq_unbound_iff]
      exact hstab c'
  | tvar =>
    cases c with
    | there c' =>
      unfold CapyCtx.IsStableCVar CapyCtx.lookup_authority CapyCtx.lookup_cvar
      simp only [CapyCaptureBound.rename_eq_unbound_iff]
      exact hstab c'
  | lock =>
    cases c with
    | there c' =>
      unfold CapyCtx.IsStableCVar CapyCtx.lookup_authority CapyCtx.lookup_cvar
      simp only [CapyCaptureBound.rename_eq_unbound_iff]
      exact hstab c'

theorem CompilerCtx.CompileCong.weakenTarget {s1 s2 : Sig} {k : Kind}
    {ctx1 ctx2 : CompilerCtx s1 s2} (h : ctx1.CompileCong ctx2)
    (b1 : Binding s2 k := placeholderBinding k) (b2 : Binding s2 k := placeholderBinding k) :
    (ctx1.weakenTarget b1).CompileCong (ctx2.weakenTarget b2) :=
  ⟨by simp only [CompilerCtx.weakenTarget_srcCtx, h.1],
   fun W => by simp only [CompilerCtx.weakenTarget_capyCtx]; exact h.2.1 W,
   fun c => by simp only [CompilerCtx.weakenTarget_capyCtx]; exact h.2.2 c⟩

theorem CompilerCtx.CompileCong.consCVar {s1 s2 : Sig} {ctx1 ctx2 : CompilerCtx s1 s2}
    (h : ctx1.CompileCong ctx2) (cb : CapyCaptureBound s1) (c : BVar s2 .cvar) :
    (ctx1.consCVar cb c).CompileCong (ctx2.consCVar cb c) :=
  ⟨by simp only [CompilerCtx.consCVar_srcCtx, h.1],
   fun W => by
     simp only [CompilerCtx.consCVar_capyCtx, CapyCtx.push_cvar_default, CapyCtx.push_cvar]
     exact CapyCaptureSet.peaks_push_cong (.cvar .access_only cb) h.2.1 W,
   fun c0 => by
     simp only [CompilerCtx.consCVar_capyCtx, CapyCtx.push_cvar_default]
     exact CapyCtx.IsStableCVar.push_cong (.cvar .access_only cb) h.2.2 c0⟩

theorem CompilerCtx.CompileCong.consVar {s1 s2 : Sig} {ctx1 ctx2 : CompilerCtx s1 s2}
    (h : ctx1.CompileCong ctx2) (T : CapyTy .capt s1) (bv : Option (BVar s2 .var))
    (cs : CaptureSet s2) :
    (ctx1.consVar T bv cs).CompileCong (ctx2.consVar T bv cs) :=
  ⟨by simp only [CompilerCtx.consVar_srcCtx, h.1],
   fun W => by
     simp only [CompilerCtx.consVar_capyCtx, CapyCtx.push_var]
     exact CapyCaptureSet.peaks_push_cong (.var T) h.2.1 W,
   fun c => by
     simp only [CompilerCtx.consVar_capyCtx, CapyCtx.push_var]
     exact CapyCtx.IsStableCVar.push_cong (.var T) h.2.2 c⟩

theorem CompilerCtx.CompileCong.consTVar {s1 s2 : Sig} {ctx1 ctx2 : CompilerCtx s1 s2}
    (h : ctx1.CompileCong ctx2) (S : CapyPureTy s1) (X : BVar s2 .tvar) :
    (ctx1.consTVar S X).CompileCong (ctx2.consTVar S X) :=
  ⟨by simp only [CompilerCtx.consTVar_srcCtx, h.1],
   fun W => by
     simp only [CompilerCtx.consTVar_capyCtx, CapyCtx.push_tvar]
     exact CapyCaptureSet.peaks_push_cong (.tvar S) h.2.1 W,
   fun c => by
     simp only [CompilerCtx.consTVar_capyCtx, CapyCtx.push_tvar]
     exact CapyCtx.IsStableCVar.push_cong (.tvar S) h.2.2 c⟩

/-- Pushing a `tvar` binder is `CompileCong`-irrelevant to its OWN declared bound: the
    same base context extended with two different tvar bounds `S1`/`S2` compiles
    identically (a tvar push adds no cvar slot, and `peaks`/`IsStableCVar` never
    inspect a tvar's bound — `CapyCaptureSet.peaks_push_tvar_irrel`). Needed to bridge
    a `CapySubtyp.poly`-derived tvar push (the REAL declared bound `S`) against
    `CapyTy.compile`'s own placeholder-bound tvar push (`.top`, `TypeCompiler.lean`'s
    `.poly` case), which compile identically. -/
theorem CompilerCtx.CompileCong.consTVar_boundIrrel {s1 s2 : Sig} {ctx : CompilerCtx s1 s2}
    (S1 S2 : CapyPureTy s1) (X : BVar s2 .tvar) :
    (ctx.consTVar S1 X).CompileCong (ctx.consTVar S2 X) :=
  ⟨by simp only [CompilerCtx.consTVar_srcCtx],
   fun W => by
     simp only [CompilerCtx.consTVar_capyCtx, CapyCtx.push_tvar]
     exact CapyCaptureSet.peaks_push_tvar_irrel W,
   fun c => by
     simp only [CompilerCtx.consTVar_capyCtx, CapyCtx.push_tvar]
     cases c with
     | there c' =>
       unfold CapyCtx.IsStableCVar CapyCtx.lookup_authority CapyCtx.lookup_cvar
       exact Iff.rfl⟩

/-- A compiled lock's `peakSepCtx` depends on the context only through `peaks` +
    cvar-stability agreement. -/
theorem CapyCaptureSet.peakset_eq {s : Sig} {Γ1 Γ2 : CapyCtx s} {W : CapyCaptureSet s}
    (h : CapyCaptureSet.peaks Γ1 W = CapyCaptureSet.peaks Γ2 W) :
    CapyCaptureSet.peakset Γ1 W = CapyCaptureSet.peakset Γ2 W := by
  simp only [CapyCaptureSet.peakset, h]

/-- `peakSepCtx` at a *fixed* peak set `P` depends on the context only through
    cvar-stability agreement (the filter predicate). -/
theorem peakSepCtx_eq_of_cong {s1 s2 : Sig} {Γ1 Γ2 : CapyCtx s1} {P : CapyPeakSet s1}
    {sc : SrcCtx s1 s2} (hstab : ∀ c, Γ1.IsStableCVar c ↔ Γ2.IsStableCVar c) :
    peakSepCtx Γ1 P sc = peakSepCtx Γ2 P sc := by
  have hfilt : (peakList P).filter (fun p => decide (Peak.IsStable Γ1 p))
      = (peakList P).filter (fun p => decide (Peak.IsStable Γ2 p)) := by
    induction (peakList P) with
    | nil => rfl
    | cons p ps ih =>
      simp only [List.filter_cons]
      have hp : Peak.IsStable Γ1 p ↔ Peak.IsStable Γ2 p := by
        cases p with
        | cvar c => exact hstab c
        | pseudo _ => exact Iff.rfl
      by_cases h : Peak.IsStable Γ1 p
      · rw [if_pos (decide_eq_true_iff.mpr h), if_pos (decide_eq_true_iff.mpr (hp.mp h)), ih]
      · rw [if_neg (fun hc => h (decide_eq_true_iff.mp hc)),
          if_neg (fun hc => h (hp.mpr (decide_eq_true_iff.mp hc))), ih]
  simp only [peakSepCtx, hfilt]

/-- The actual `peakSepCtx (peakset Γ W)` pattern that `CapyTy.compile` uses: both
    the underlying peak set (via `peaks`-agreement) and the stability filter (via
    `IsStableCVar`-agreement) need to line up between `Γ1`/`Γ2`. -/
theorem peakSepCtx_peakset_eq_of_cong {s1 s2 : Sig} {Γ1 Γ2 : CapyCtx s1} {W : CapyCaptureSet s1}
    {sc : SrcCtx s1 s2}
    (hpeaks : CapyCaptureSet.peaks Γ1 W = CapyCaptureSet.peaks Γ2 W)
    (hstab : ∀ c, Γ1.IsStableCVar c ↔ Γ2.IsStableCVar c) :
    peakSepCtx Γ1 (CapyCaptureSet.peakset Γ1 W) sc
      = peakSepCtx Γ2 (CapyCaptureSet.peakset Γ2 W) sc := by
  rw [CapyCaptureSet.peakset_eq hpeaks]
  exact peakSepCtx_eq_of_cong hstab

/-- **`compile` bound-insensitivity.**  `compile` reads `capyCtx` only through `peaks`
    and `srcCtx`; two `CompileCong` contexts compile every type identically.  (Recursion
    re-establishes `CompileCong` via the same builder applied on both sides.) -/
theorem CapyTy.compile_eq_of {sort : CapyTySort} {s1 s2 : Sig}
    (T : CapyTy sort s1) (ctx1 : CompilerCtx s1 s2) :
    ∀ (ctx2 : CompilerCtx s1 s2), ctx1.CompileCong ctx2 →
    CapyTy.compile T ctx1 = CapyTy.compile T ctx2 := by
  fun_induction CapyTy.compile T ctx1 with
  | case1 => intro ctx2 h; simp only [CapyTy.compile]
  | case2 => intro ctx2 h; simp only [CapyTy.compile]
  | case3 => intro ctx2 h; simp only [CapyTy.compile]
  | case4 => intro ctx2 h; simp only [CapyTy.compile, h.1]
  | case5 => intro ctx2 h; simp only [CapyTy.compile, h.1]
  | case6 => intro ctx2 h; simp only [CapyTy.compile, h.1]
  | case7 => rename_i ih; intro ctx2 h; simp only [CapyTy.compile]; rw [ih ctx2 h]
  | case8 => intro ctx2 h; simp only [CapyTy.compile, h.1]
  | case9 =>
    rename_i ihDom ihE
    rename_i Tdom _ _ _ _ _ _ _ _ _
    intro ctx2 h
    have hB := (h.weakenTarget (placeholderBinding .cvar)).consCVar
      (CapyCaptureBound.unbound .epsilon) BVar.here
    have hDom := (((h.weakenTarget (placeholderBinding .cvar)).weakenTarget
      (placeholderBinding .cvar)).consCVar (CapyCaptureBound.unbound .epsilon)
      (.there .here)).consVar Tdom none (.cvar (.M .epsilon) .here)
    have hLock := ((((h.weakenTarget (placeholderBinding .cvar)).weakenTarget
      (placeholderBinding .cvar)).weakenTarget (placeholderBinding .var)).consCVar
      (CapyCaptureBound.unbound .epsilon) (.there (.there .here))).consVar Tdom (some .here)
      (.cvar (.M .epsilon) (.there .here))
    have hE := (((h.weakenTarget (placeholderBinding .cvar)).weakenTarget
      (placeholderBinding .cvar)).weakenTarget (placeholderBinding .var)).consVar
      CapyTy.top (some .here) (.cvar (.M .epsilon) (.there .here))
    simp (config := { zetaDelta := true }) only [CapyTy.compile]
    congr 1
    congr 1
    congr 1
    · congr 1
      exact congrArg _ hB.1
    · congr 1
      congr 1
      · exact ihDom _ hDom
      · congr 1
        congr 1
        · exact congrArg _ hLock.1
        · rw [hLock.1, peakSepCtx_peakset_eq_of_cong (hLock.2.1 _) hLock.2.2]
        · exact ihE _ hE
  | case10 =>
    rename_i ihS ihE; intro ctx2 h
    simp (config := { zetaDelta := true }) only [CapyTy.compile]
    rw [ihS ctx2 h,
      ihE (ctx2.weakenTarget.consTVar CapyPureTy.top BVar.here)
        (h.weakenTarget.consTVar CapyPureTy.top BVar.here),
      h.1, peakSepCtx_peakset_eq_of_cong (h.2.1 _) h.2.2]
  | case11 =>
    rename_i ihE; intro ctx2 h
    simp (config := { zetaDelta := true }) only [CapyTy.compile]
    rw [ihE (ctx2.weakenTarget.consCVar _ BVar.here)
        (h.weakenTarget.consCVar _ BVar.here),
      h.1, peakSepCtx_peakset_eq_of_cong (h.2.1 _) h.2.2]
  | case12 =>
    rename_i ih; intro ctx2 h
    simp only [CapyTy.compile]
    rw [ih (ctx2.weakenTarget.consCVar (CapyCaptureBound.unbound .epsilon) BVar.here)
      (h.weakenTarget.consCVar (CapyCaptureBound.unbound .epsilon) BVar.here)]

end Compilation
