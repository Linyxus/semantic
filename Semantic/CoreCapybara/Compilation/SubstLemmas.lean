import Semantic.CoreCapybara.Compilation.ClosedLemmas
open CoreCapybara
namespace Compilation

/-!
# Compilation commutes with capture-variable opening

The `fresh` (existential-introduction) case of term compilation packs a variable
whose source type is `T.subst (openCVar D)` into the target existential `.exi T`,
via the target `pack`.  `pack`'s premise demands the variable at the *opened*
compiled body `⟦T⟧.subst (openCVar ⟦D⟧)`, so type-preservation needs

  `⟦T.subst (openCVar D)⟧ = ⟦T⟧.subst (openCVar ⟦D⟧)`

— compilation commutes with capture opening.  This file develops that suite,
starting at the capture-set level.
-/

/-- Compilation distributes over `applyMut` (it only relabels atom access modes,
    which `compile` carries through). -/
theorem CapyCaptureSet.compile_applyMut {cs : CapyCaptureSet s1} {sc : SrcCtx s1 s2}
    {m : Mutability} :
    CapyCaptureSet.compile (cs.applyMut m) sc = (CapyCaptureSet.compile cs sc).applyMut m := by
  cases m with
  | epsilon => simp only [CapyCaptureSet.applyMut_epsilon, CaptureSet.applyMut_epsilon]
  | ro =>
    simp only [CapyCaptureSet.applyMut_ro, CaptureSet.applyMut_ro]
    induction cs with
    | empty => simp only [CapyCaptureSet.applyRO, CaptureSet.applyRO, CapyCaptureSet.compile]
    | union cs1 cs2 ih1 ih2 =>
      simp only [CapyCaptureSet.applyRO_union, CaptureSet.applyRO_union, CapyCaptureSet.compile,
        ih1, ih2]
    | cvar a c =>
      simp only [CapyCaptureSet.applyRO_cvar, CaptureSet.applyRO_cvar, CapyCaptureSet.compile]
    | var a x =>
      cases x with
      | bound x =>
        simp only [CapyCaptureSet.applyRO_var, CapyCaptureSet.compile,
          CaptureSet.applyAccess_applyRO]
      | free n =>
        simp only [CapyCaptureSet.applyRO_var, CaptureSet.applyRO_var, CapyCaptureSet.compile]
    | pseudo_peak _ ih =>
      simp only [CapyCaptureSet.applyRO, CapyCaptureSet.compile, ih]

/-- Compilation distributes over `applyDrop`. -/
theorem CapyCaptureSet.compile_applyDrop {cs : CapyCaptureSet s1} {sc : SrcCtx s1 s2} :
    CapyCaptureSet.compile cs.applyDrop sc = (CapyCaptureSet.compile cs sc).applyDrop := by
  induction cs with
  | empty => simp only [CapyCaptureSet.applyDrop, CaptureSet.applyDrop, CapyCaptureSet.compile]
  | union cs1 cs2 ih1 ih2 =>
    simp only [CapyCaptureSet.applyDrop, CaptureSet.applyDrop, CapyCaptureSet.compile, ih1, ih2]
  | cvar a c => simp only [CapyCaptureSet.applyDrop, CaptureSet.applyDrop, CapyCaptureSet.compile]
  | var a x =>
    cases x with
    | bound x =>
      simp only [CapyCaptureSet.applyDrop, CapyCaptureSet.compile, CaptureSet.applyAccess_drop,
        CaptureSet.applyAccess_applyDrop]
    | free n => simp only [CapyCaptureSet.applyDrop, CaptureSet.applyDrop, CapyCaptureSet.compile]
  | pseudo_peak _ ih =>
    simp only [CapyCaptureSet.applyDrop, CapyCaptureSet.compile, ih]

/-- Compilation distributes over `applyAccess`. -/
theorem CapyCaptureSet.compile_applyAccess {cs : CapyCaptureSet s1} {sc : SrcCtx s1 s2}
    {a : Access} :
    CapyCaptureSet.compile (cs.applyAccess a) sc
      = (CapyCaptureSet.compile cs sc).applyAccess a := by
  cases a with
  | M m =>
    simp only [CapyCaptureSet.applyAccess_M, CaptureSet.applyAccess_M,
      CapyCaptureSet.compile_applyMut]
  | drop =>
    simp only [CapyCaptureSet.applyAccess_drop, CaptureSet.applyAccess_drop,
      CapyCaptureSet.compile_applyDrop]

/-- **Capture-set compilation commutes with capture-variable opening.**  For a
    capture set `cs` under a fresh source cvar binder, compiling its source-opening
    `cs[D/c]` equals compiling `cs` through the cvar-extended source map and then
    target-opening the compiled witness `⟦D⟧`.  This is the capture-set base of the
    type-level commutation `CapyTy.compile_openCVar`.  The cvar-`.here` atom maps to
    `D`/`⟦D⟧` on both sides; every other atom is weakened past the binder, so
    `weaken_openCVar` cancels the introduced shift. -/
theorem CapyCaptureSet.compile_subst_openCVar {s1 s2 : Sig}
    {cs : CapyCaptureSet (s1,,Kind.cvar)} {sc : SrcCtx s1 s2} {D : CapyCaptureSet s1} :
    CapyCaptureSet.compile (CapyCaptureSet.subst cs (CapySubst.openCVar D)) sc
      = (CapyCaptureSet.compile cs (.cons (.cvar .here) (sc.rename Rename.succ))).subst
          (Subst.openCVar (CapyCaptureSet.compile D sc)) := by
  induction cs with
  | empty => simp only [CapyCaptureSet.subst, CapyCaptureSet.compile, CaptureSet.subst]
  | union cs1 cs2 ih1 ih2 =>
    simp only [CapyCaptureSet.subst, CapyCaptureSet.compile, CaptureSet.subst, ih1, ih2]
  | cvar a c =>
    cases c with
    | here =>
      simp only [CapyCaptureSet.subst, CapySubst.openCVar, CapyCaptureSet.compile_applyAccess,
        CapyCaptureSet.compile, SrcCtx.lookupCVar, CaptureSet.subst, Subst.openCVar]
    | there c0 =>
      simp only [CapyCaptureSet.subst, CapySubst.openCVar, CapyCaptureSet.compile_applyAccess,
        CapyCaptureSet.compile, SrcCtx.lookupCVar, SrcCtx.lookupCVar_rename, Rename.succ,
        CaptureSet.subst, Subst.openCVar]
  | var a x =>
    cases x with
    | bound x =>
      cases x with
      | there x0 =>
        simp only [CapyCaptureSet.subst, CapyVar.subst, CapySubst.openCVar, CapyCaptureSet.compile,
          SrcCtx.lookupVar, SrcCtx.lookupVar_rename, CaptureSet.applyAccess_subst,
          CaptureSet.weaken_openCVar]
    | free n =>
      simp only [CapyCaptureSet.subst, CapyVar.subst, CapyCaptureSet.compile, CaptureSet.subst,
        Var.subst, Subst.openCVar]
  | pseudo_peak _ ih =>
    simp only [CapyCaptureSet.subst, CapyCaptureSet.compile, ih]

/-- The access mode on a compiled variable atom factors out. -/
theorem CapyCaptureSet.compile_var_access {y : Var .var s1} {sc : SrcCtx s1 s2} {m : Access} :
    CapyCaptureSet.compile (.var m y) sc
      = (CapyCaptureSet.compile (.var (.M .epsilon) y) sc).applyAccess m := by
  cases y with
  | bound x =>
    simp only [CapyCaptureSet.compile, CaptureSet.applyAccess_M, CaptureSet.applyMut_epsilon]
  | free n =>
    cases m with
    | M m' =>
      cases m' with
      | epsilon =>
        simp only [CapyCaptureSet.compile, CaptureSet.applyAccess_M, CaptureSet.applyMut_epsilon]
      | ro =>
        simp only [CapyCaptureSet.compile, CaptureSet.applyAccess_M, CaptureSet.applyMut_ro,
          CaptureSet.applyRO_var, Access.applyRO]
    | drop =>
      simp only [CapyCaptureSet.compile, CaptureSet.applyAccess_drop, CaptureSet.applyDrop]

/-- **Substitution-compatibility** of a source→target map `scSub`, a "base" map
    `scOrig`, a source substitution `σ`, and a target substitution `σt`: each source
    capture/term variable's `σ`-image compiles (through `scSub`) to its `scOrig`-image
    `σt`-substituted.  This is exactly the per-atom data that makes
    `CapyCaptureSet.compile` commute with `σ` (below). -/
structure SubstCompat {s1 s1' s2 s2' : Sig} (scSub : SrcCtx s1' s2')
    (scOrig : SrcCtx s1 s2) (σ : CapySubst s1 s1') (σt : Subst s2 s2') : Prop where
  cvar : ∀ c, CapyCaptureSet.compile (σ.cvar c) scSub = σt.cvar (scOrig.lookupCVar c)
  var : ∀ x, CapyCaptureSet.compile (.var (.M .epsilon) (σ.var x)) scSub
      = (scOrig.lookupVar x).subst σt

/-- **Capture-set compilation commutes with a compatible substitution.**  The
    generalization of `compile_subst_openCVar` to any `SubstCompat` data — needed
    because the type-level recursion meets `openCVar` *lifted* under binders. -/
theorem CapyCaptureSet.compile_subst {s1 s1' s2 s2' : Sig} {scSub : SrcCtx s1' s2'}
    {scOrig : SrcCtx s1 s2} {σ : CapySubst s1 s1'} {σt : Subst s2 s2'}
    (h : SubstCompat scSub scOrig σ σt) {cs : CapyCaptureSet s1} (hcs : cs.IsClosed) :
    CapyCaptureSet.compile (CapyCaptureSet.subst cs σ) scSub
      = (CapyCaptureSet.compile cs scOrig).subst σt := by
  induction cs with
  | empty => simp only [CapyCaptureSet.subst, CapyCaptureSet.compile, CaptureSet.subst]
  | union cs1 cs2 ih1 ih2 =>
    cases hcs with | union hcs1 hcs2 =>
    simp only [CapyCaptureSet.subst, CapyCaptureSet.compile, CaptureSet.subst, ih1 hcs1, ih2 hcs2]
  | cvar m c =>
    simp only [CapyCaptureSet.subst, CapyCaptureSet.compile_applyAccess, h.cvar,
      CapyCaptureSet.compile, CaptureSet.subst]
  | var m x =>
    cases x with
    | bound x =>
      simp only [CapyCaptureSet.subst, CapyVar.subst, CapyCaptureSet.compile_var_access, h.var,
        CapyCaptureSet.compile, CaptureSet.applyAccess_subst]
    | free n => nomatch hcs
  | pseudo_peak _ ih =>
    cases hcs with | pseudo_peak h =>
    simp only [CapyCaptureSet.subst, CapyCaptureSet.compile, ih h]

/-- The base substitution-compatibility: opening a fresh cvar.  `scOrig` carries the
    cvar binder (mapped to target `.here`); `σ`/`σt` open it with `T`/`⟦T⟧`. -/
theorem SubstCompat.openCVar {s1 s2 : Sig} {sc : SrcCtx s1 s2} {T : CapyCaptureSet s1} :
    SubstCompat sc (.cons (.cvar .here) (sc.rename Rename.succ))
      (CapySubst.openCVar T) (Subst.openCVar (CapyCaptureSet.compile T sc)) where
  cvar := by
    intro c
    cases c with
    | here =>
      simp only [CapySubst.openCVar, CapyCaptureSet.compile, SrcCtx.lookupCVar, Subst.openCVar]
    | there c0 =>
      simp only [CapySubst.openCVar, CapyCaptureSet.compile, SrcCtx.lookupCVar,
        SrcCtx.lookupCVar_rename, Rename.succ, Subst.openCVar]
  var := by
    intro x
    cases x with
    | there x0 =>
      simp only [CapySubst.openCVar, CapyCaptureSet.compile, CaptureSet.applyAccess_M,
        CaptureSet.applyMut_epsilon, SrcCtx.lookupVar, SrcCtx.lookupVar_rename,
        CaptureSet.weaken_openCVar]

/-- `SubstCompat` is preserved by a fresh *target* binder (the compiler's
    `weakenTarget`): both maps are `succ`-renamed and `σt` lifts. -/
theorem SubstCompat.weakenTarget {s1 s1' s2 s2' : Sig} {scSub : SrcCtx s1' s2'}
    {scOrig : SrcCtx s1 s2} {σ : CapySubst s1 s1'} {σt : Subst s2 s2'}
    (h : SubstCompat scSub scOrig σ σt) :
    SubstCompat (scSub.rename Rename.succ) (scOrig.rename Rename.succ) σ (σt.lift (k := k)) where
  cvar := by
    intro c
    simp only [CapyCaptureSet.compile_rename, h.cvar, SrcCtx.lookupCVar_rename, Rename.succ,
      Subst.lift_there_cvar_eq]
  var := by
    intro x
    simp only [CapyCaptureSet.compile_rename, h.var, SrcCtx.lookupVar_rename]
    exact CaptureSet.weaken_subst_comm_liftMany (K := [])

/-- `SubstCompat` is preserved by the compiler's `weakenTarget.consCVar … .here`
    (recursing under a source capture binder mapped to a fresh target cvar). -/
theorem SubstCompat.weakenConsCVar {s1 s1' s2 s2' : Sig} {scSub : SrcCtx s1' s2'}
    {scOrig : SrcCtx s1 s2} {σ : CapySubst s1 s1'} {σt : Subst s2 s2'}
    (h : SubstCompat scSub scOrig σ σt) :
    SubstCompat (.cons (.cvar .here) (scSub.rename Rename.succ))
      (.cons (.cvar .here) (scOrig.rename Rename.succ)) σ.lift (σt.lift (k := Kind.cvar)) where
  cvar := by
    intro c
    cases c with
    | here =>
      have h1 : (σ.lift (k := Kind.cvar)).cvar .here
          = CapyCaptureSet.cvar (.M .epsilon) .here := rfl
      have h2 : (σt.lift (k := Kind.cvar)).cvar .here = CaptureSet.cvar (.M .epsilon) .here := rfl
      simp only [h1, CapyCaptureSet.compile, SrcCtx.lookupCVar, h2]
    | there c0 =>
      have hY : (CapySubst.lift σ (k := Kind.cvar)).cvar (.there c0)
          = (σ.cvar c0).rename Rename.succ := CapySubst.lift_there_cvar_eq
      rw [hY, CapyCaptureSet.compile_rename_succ_cons, CapyCaptureSet.compile_rename, h.cvar]
      simp only [SrcCtx.lookupCVar, SrcCtx.lookupCVar_rename, Rename.succ, Subst.lift_there_cvar_eq]
  var := by
    intro x
    cases x with
    | there x0 =>
      have hY : (CapySubst.lift σ (k := Kind.cvar)).var (.there x0)
          = (σ.var x0).rename Rename.succ := CapySubst.lift_there_var_eq
      rw [hY, show (CapyCaptureSet.var (.M .epsilon) ((σ.var x0).rename Rename.succ))
            = (CapyCaptureSet.var (.M .epsilon) (σ.var x0)).rename Rename.succ from rfl,
        CapyCaptureSet.compile_rename_succ_cons, CapyCaptureSet.compile_rename, h.var]
      simp only [SrcCtx.lookupVar, SrcCtx.lookupVar_rename]
      exact CaptureSet.weaken_subst_comm_liftMany (K := [])

/-- `SubstCompat` preserved by a source capture binder, mapped to target cvar `cS`
    (sub-world) / `cO` (orig-world) related by `σt` (`consCVar`; target unchanged). -/
theorem SubstCompat.consCVar {s1 s1' s2 s2' : Sig} {sc : SrcCtx s1' s2'}
    {scO : SrcCtx s1 s2} {σ : CapySubst s1 s1'} {σt : Subst s2 s2'}
    {cS : BVar s2' .cvar} {cO : BVar s2 .cvar}
    (h : SubstCompat sc scO σ σt) (hc : σt.cvar cO = CaptureSet.cvar (.M .epsilon) cS) :
    SubstCompat (.cons (.cvar cS) sc) (.cons (.cvar cO) scO) σ.lift σt where
  cvar := by
    intro cc
    cases cc with
    | here =>
      have h1 : (σ.lift (k := Kind.cvar)).cvar .here
          = CapyCaptureSet.cvar (.M .epsilon) .here := rfl
      simp only [h1, CapyCaptureSet.compile, SrcCtx.lookupCVar, hc]
    | there c0 =>
      rw [CapySubst.lift_there_cvar_eq, CapyCaptureSet.compile_rename_succ_cons, h.cvar]
      simp only [SrcCtx.lookupCVar]
  var := by
    intro x
    cases x with
    | there x0 =>
      rw [CapySubst.lift_there_var_eq,
        show (CapyCaptureSet.var (.M .epsilon) ((σ.var x0).rename Rename.succ))
          = (CapyCaptureSet.var (.M .epsilon) (σ.var x0)).rename Rename.succ from rfl,
        CapyCaptureSet.compile_rename_succ_cons, h.var]
      simp only [SrcCtx.lookupVar]

/-- `SubstCompat` preserved by a source value binder, with capture images `csS`
    (sub-world) / `csO` (orig-world) related by `σt` (`consVar`). -/
theorem SubstCompat.consVar {s1 s1' s2 s2' : Sig} {sc : SrcCtx s1' s2'}
    {scO : SrcCtx s1 s2} {σ : CapySubst s1 s1'} {σt : Subst s2 s2'}
    {bvS : Option (BVar s2' .var)} {bvO : Option (BVar s2 .var)}
    {csS : CaptureSet s2'} {csO : CaptureSet s2}
    (h : SubstCompat sc scO σ σt) (hinv : csO.subst σt = csS) :
    SubstCompat (.cons (.var bvS csS) sc) (.cons (.var bvO csO) scO) σ.lift σt where
  cvar := by
    intro cc
    cases cc with
    | there c0 =>
      rw [CapySubst.lift_there_cvar_eq, CapyCaptureSet.compile_rename_succ_cons, h.cvar]
      simp only [SrcCtx.lookupCVar]
  var := by
    intro x
    cases x with
    | here =>
      have h1 : (σ.lift (k := Kind.var)).var .here = Var.bound .here := rfl
      simp only [h1, CapyCaptureSet.compile, SrcCtx.lookupVar, CaptureSet.applyAccess_M,
        CaptureSet.applyMut_epsilon, hinv]
    | there x0 =>
      rw [CapySubst.lift_there_var_eq,
        show (CapyCaptureSet.var (.M .epsilon) ((σ.var x0).rename Rename.succ))
          = (CapyCaptureSet.var (.M .epsilon) (σ.var x0)).rename Rename.succ from rfl,
        CapyCaptureSet.compile_rename_succ_cons, h.var]
      simp only [SrcCtx.lookupVar]

/-- `SubstCompat` preserved by a source type binder (the compiler's `consTVar`). -/
theorem SubstCompat.consTVar {s1 s1' s2 s2' : Sig} {sc : SrcCtx s1' s2'}
    {scO : SrcCtx s1 s2} {σ : CapySubst s1 s1'} {σt : Subst s2 s2'}
    {XS : BVar s2' .tvar} {XO : BVar s2 .tvar}
    (h : SubstCompat sc scO σ σt) :
    SubstCompat (.cons (.tvar XS) sc) (.cons (.tvar XO) scO) σ.lift σt where
  cvar := by
    intro cc
    cases cc with
    | there c0 =>
      rw [CapySubst.lift_there_cvar_eq, CapyCaptureSet.compile_rename_succ_cons, h.cvar]
      simp only [SrcCtx.lookupCVar]
  var := by
    intro x
    cases x with
    | there x0 =>
      rw [CapySubst.lift_there_var_eq,
        show (CapyCaptureSet.var (.M .epsilon) ((σ.var x0).rename Rename.succ))
          = (CapyCaptureSet.var (.M .epsilon) (σ.var x0)).rename Rename.succ from rfl,
        CapyCaptureSet.compile_rename_succ_cons, h.var]
      simp only [SrcCtx.lookupVar]

/-- The leaf cases of the type-level commutation are an *equality* (the lock cases
    are where subtyping enters).  This proves the equality for the non-recursive,
    lock-free formers `cap`/`cell` (and the trivial `top`/`unit`/`bool`), via the
    capture-level `compile_subst`. -/
theorem CapyTy.compile_subst_cap {s1 s1' s2 s2' : Sig} {cs : CapyCaptureSet s1}
    {ctxSub : CompilerCtx s1' s2'} {ctxOrig : CompilerCtx s1 s2}
    {σ : CapySubst s1 s1'} {σt : Subst s2 s2'}
    (h : SubstCompat ctxSub.srcCtx ctxOrig.srcCtx σ σt) (hcs : cs.IsClosed) :
    CapyTy.compile ((CapyTy.cap cs).subst σ) ctxSub
      = (CapyTy.compile (CapyTy.cap cs) ctxOrig).subst σt := by
  simp only [CapyTy.subst, CapyTy.compile, Ty.subst, CapyCaptureSet.compile_subst h hcs]

theorem CapyTy.compile_subst_cell {s1 s1' s2 s2' : Sig} {cs : CapyCaptureSet s1} {m : Mutability}
    {ctxSub : CompilerCtx s1' s2'} {ctxOrig : CompilerCtx s1 s2}
    {σ : CapySubst s1 s1'} {σt : Subst s2 s2'}
    (h : SubstCompat ctxSub.srcCtx ctxOrig.srcCtx σ σt) (hcs : cs.IsClosed) :
    CapyTy.compile ((CapyTy.cell cs m).subst σ) ctxSub
      = (CapyTy.compile (CapyTy.cell cs m) ctxOrig).subst σt := by
  cases m <;>
    simp only [CapyTy.subst, CapyTy.compile, Ty.subst, CapyCaptureSet.compile_subst h hcs]

/-- **Capture-bound compilation commutes with a compatible substitution.**  Mirrors
    `compile_subst_cap`/`cell` at the bound level: `unbound` is trivial, `bound` reduces
    to the capture-set `compile_subst`.  Needed by the lock-kernel `cpoly`/`arrow` cases
    (the `Subbound` premise relates the two compiled bounds). -/
theorem CapyCaptureBound.compile_subst {s1 s1' s2 s2' : Sig} {scSub : SrcCtx s1' s2'}
    {scOrig : SrcCtx s1 s2} {σ : CapySubst s1 s1'} {σt : Subst s2 s2'}
    (h : SubstCompat scSub scOrig σ σt) {cb : CapyCaptureBound s1} (hcb : cb.IsClosed) :
    CapyCaptureBound.compile (cb.subst σ) scSub
      = (CapyCaptureBound.compile cb scOrig).subst σt := by
  cases cb with
  | unbound m => simp only [CapyCaptureBound.subst, CapyCaptureBound.compile, CaptureBound.subst]
  | bound cs =>
    cases hcb with | bound hcs =>
    simp only [CapyCaptureBound.subst, CapyCaptureBound.compile, CaptureBound.subst,
      CapyCaptureSet.compile_subst h hcs]

/-! ### Structure of the compiled separation lock `peakSepCtx`

Toward the lock `Satisfy` sub-proof of the type-level commutation: an item of the
folded separation context comes from exactly one peak cvar. -/

/-- Membership in a `foldl`-built separation context: an item is either in the
    accumulator or is `g c` for some list element `c`. -/
theorem SepCtx.Has_foldl_cons {α : Type} {s2 : Sig} {g : α → CaptureSet s2}
    {C : CaptureSet s2} (l : List α) (acc : SepCtx s2)
    (h : SepCtx.Has (l.foldl (fun K c => .cons K (g c)) acc) C) :
    (∃ c ∈ l, C = g c) ∨ SepCtx.Has acc C := by
  induction l generalizing acc with
  | nil => exact Or.inr h
  | cons c0 l' ih =>
    simp only [List.foldl_cons] at h
    rcases ih _ h with ⟨c, hc, hC⟩ | hacc
    · exact Or.inl ⟨c, List.mem_cons_of_mem _ hc, hC⟩
    · cases hacc with
      | here => exact Or.inl ⟨c0, List.mem_cons_self, rfl⟩
      | there hacc' => exact Or.inr hacc'

/-- Every separation item of a compiled lock is the compiled `peakItem` of some
    distinct peak cvar. -/
theorem peakSepCtx_Has {s1 s2 : Sig} {Γ : CapyCtx s1} {P : CapyPeakSet s1} {sc : SrcCtx s1 s2}
    {C : CaptureSet s2} (h : SepCtx.Has (peakSepCtx Γ P sc) C) :
    ∃ p ∈ peakList P, C = CapyCaptureSet.compile (peakKeyItem P p) sc := by
  simp only [peakSepCtx] at h
  rcases SepCtx.Has_foldl_cons _ _ h with ⟨p, hp, hC⟩ | hempty
  · exact ⟨p, List.mem_of_mem_filter hp, hC⟩
  · cases hempty

/-- `HasTwoDistinct` entails `Has` on both components (public re-proof). -/
theorem SepCtx.HasTwoDistinct.has_both {s : Sig} {K : SepCtx s} {C1 C2 : CaptureSet s}
    (h : SepCtx.HasTwoDistinct K C1 C2) : SepCtx.Has K C1 ∧ SepCtx.Has K C2 := by
  induction h with
  | here_there hhas => exact ⟨.here, .there hhas⟩
  | there _ ih => exact ⟨.there ih.1, .there ih.2⟩
  | symm _ ih => exact ⟨ih.2, ih.1⟩

/-- Both members of a `HasTwoDistinct` pair of a compiled lock are compiled
    `peakKeyItem`s of peaks. -/
theorem peakSepCtx_HasTwoDistinct {s1 s2 : Sig} {Γ : CapyCtx s1} {P : CapyPeakSet s1}
    {sc : SrcCtx s1 s2}
    {C1 C2 : CaptureSet s2} (h : SepCtx.HasTwoDistinct (peakSepCtx Γ P sc) C1 C2) :
    (∃ p1 ∈ peakList P, C1 = CapyCaptureSet.compile (peakKeyItem P p1) sc) ∧
    (∃ p2 ∈ peakList P, C2 = CapyCaptureSet.compile (peakKeyItem P p2) sc) := by
  obtain ⟨h1, h2⟩ := SepCtx.HasTwoDistinct.has_both h
  exact ⟨peakSepCtx_Has h1, peakSepCtx_Has h2⟩

/-! ### (★) Compilation is invariant under peak-resolution (under alignment)

`SrcAligned Γ sc` is the part of `Coherent` that (★) needs: every source variable's
stored target image is the *compiled capture set of its declared type*.  It peels
through a binder (the new image is the tail's compiled captureSet, recovered with
`compile_rename_succ_cons`). -/

/-- A source typing context and a source→target map agree: each term variable's
    image is the compilation of its declared type's capture set. -/
def SrcAligned (Γ : CapyCtx s) (sc : SrcCtx s s2) : Prop :=
  ∀ {x : BVar s .var} {T : CapyTy .capt s},
    Γ.LookupVar x T → sc.lookupVar x = CapyCaptureSet.compile T.captureSet sc

/-- Alignment peels through one binder. -/
theorem SrcAligned.peel {Γ' : CapyCtx s} {b : CapyBinding s k}
    {info : SrcBinderInfo k s2} {sc' : SrcCtx s s2}
    (h : SrcAligned (Γ'.push b) (.cons info sc')) : SrcAligned Γ' sc' := by
  intro x' T' hlook
  have hx := h (CapyCtx.LookupVar.there hlook)
  simp only [SrcCtx.lookupVar, CapyTy.captureSet_rename,
    CapyCaptureSet.compile_rename_succ_cons] at hx
  exact hx

/-! **(★) compilation factors through peak-resolution.**  Under alignment (and
    closedness — `peaks` drops *free* atoms to `{}` while `compile` keeps them, so
    `(★)` needs no free atoms), compiling a capture set equals compiling its
    `peaks`.  Mutual with the variable-bound version; the recursion mirrors
    `peaks`/`peaksVarBound` (decreasing on the context). -/
mutual
theorem CapyCaptureSet.compile_peaksVarBound {Γ : CapyCtx s} {sc : SrcCtx s s2}
    (hΓ : Γ.IsClosed) (h : SrcAligned Γ sc) {m : Access} {x : BVar s .var} :
    CapyCaptureSet.compile (CapyCaptureSet.peaksVarBound Γ m x) sc
      = (sc.lookupVar x).applyAccess m := by
  match Γ, x, sc, hΓ with
  | .push Γ' (.var T), .here, .cons info sc', .push hΓ' (.var hT) =>
    rw [CapyCaptureSet.peaksVarBound, CapyCaptureSet.compile_applyAccess,
      CapyCaptureSet.compile_rename_succ_cons,
      CapyCaptureSet.compile_peaks hΓ' (h.peel) (CapyTy.IsClosed.captureSet hT)]
    have hx := h CapyCtx.LookupVar.here
    simp only [CapyTy.captureSet_rename,
      CapyCaptureSet.compile_rename_succ_cons] at hx ⊢
    rw [hx]
  | .push Γ' b, .there x', .cons info sc', .push hΓ' _ =>
    rw [CapyCaptureSet.peaksVarBound, CapyCaptureSet.compile_rename_succ_cons,
      CapyCaptureSet.compile_peaksVarBound hΓ' (h.peel)]
    simp only [SrcCtx.lookupVar]
termination_by (sizeOf Γ, sizeOf x + 1)

theorem CapyCaptureSet.compile_peaks {Γ : CapyCtx s} {sc : SrcCtx s s2}
    (hΓ : Γ.IsClosed) (h : SrcAligned Γ sc) {cs : CapyCaptureSet s} (hcs : cs.IsClosed) :
    CapyCaptureSet.compile (CapyCaptureSet.peaks Γ cs) sc = CapyCaptureSet.compile cs sc := by
  match cs, hcs with
  | .empty, _ => simp only [CapyCaptureSet.peaks]
  | .union cs1 cs2, .union hcs1 hcs2 =>
    simp only [CapyCaptureSet.peaks, CapyCaptureSet.compile,
      CapyCaptureSet.compile_peaks hΓ h hcs1, CapyCaptureSet.compile_peaks hΓ h hcs2]
  | .cvar a c, _ => simp only [CapyCaptureSet.peaks]
  | .pseudo_peak C, .pseudo_peak hC =>
    simp only [CapyCaptureSet.peaks, CapyCaptureSet.compile, CapyCaptureSet.compile_peaks hΓ h hC]
  | .var a (.bound x), _ =>
    rw [CapyCaptureSet.peaks, CapyCaptureSet.compile_peaksVarBound hΓ h]
    simp only [CapyCaptureSet.compile]
termination_by (sizeOf Γ, sizeOf cs)
end

/- **(★, resource view)** Like `compile_peaks`, but for `resourcePeaks`, which
   RESOLVES frozen peaks.  Since `compile` is transparent on `pseudo_peak`
   (`⟦pseudo_peak C⟧ = ⟦C⟧`), resolving the content leaves the compiled image
   unchanged, so `⟦resourcePeaks Γ cs⟧ = ⟦cs⟧` exactly as for `peaks`. -/
mutual
theorem CapyCaptureSet.compile_resourcePeaksVarBound {Γ : CapyCtx s} {sc : SrcCtx s s2}
    (hΓ : Γ.IsClosed) (h : SrcAligned Γ sc) {m : Access} {x : BVar s .var} :
    CapyCaptureSet.compile (CapyCaptureSet.resourcePeaksVarBound Γ m x) sc
      = (sc.lookupVar x).applyAccess m := by
  match Γ, x, sc, hΓ with
  | .push Γ' (.var T), .here, .cons info sc', .push hΓ' (.var hT) =>
    rw [CapyCaptureSet.resourcePeaksVarBound, CapyCaptureSet.compile_applyAccess,
      CapyCaptureSet.compile_rename_succ_cons,
      CapyCaptureSet.compile_resourcePeaks hΓ' (h.peel) (CapyTy.IsClosed.captureSet hT)]
    have hx := h CapyCtx.LookupVar.here
    simp only [CapyTy.captureSet_rename,
      CapyCaptureSet.compile_rename_succ_cons] at hx ⊢
    rw [hx]
  | .push Γ' b, .there x', .cons info sc', .push hΓ' _ =>
    rw [CapyCaptureSet.resourcePeaksVarBound, CapyCaptureSet.compile_rename_succ_cons,
      CapyCaptureSet.compile_resourcePeaksVarBound hΓ' (h.peel)]
    simp only [SrcCtx.lookupVar]
termination_by (sizeOf Γ, sizeOf x + 1)

theorem CapyCaptureSet.compile_resourcePeaks {Γ : CapyCtx s} {sc : SrcCtx s s2}
    (hΓ : Γ.IsClosed) (h : SrcAligned Γ sc) {cs : CapyCaptureSet s} (hcs : cs.IsClosed) :
    CapyCaptureSet.compile (CapyCaptureSet.resourcePeaks Γ cs) sc
      = CapyCaptureSet.compile cs sc := by
  match cs, hcs with
  | .empty, _ => simp only [CapyCaptureSet.resourcePeaks]
  | .union cs1 cs2, .union hcs1 hcs2 =>
    simp only [CapyCaptureSet.resourcePeaks, CapyCaptureSet.compile,
      CapyCaptureSet.compile_resourcePeaks hΓ h hcs1,
      CapyCaptureSet.compile_resourcePeaks hΓ h hcs2]
  | .cvar a c, _ => simp only [CapyCaptureSet.resourcePeaks]
  | .pseudo_peak C, .pseudo_peak hC =>
    rw [CapyCaptureSet.resourcePeaks, CapyCaptureSet.compile_resourcePeaks hΓ h hC]
    simp only [CapyCaptureSet.compile]
  | .var a (.bound x), _ =>
    rw [CapyCaptureSet.resourcePeaks, CapyCaptureSet.compile_resourcePeaksVarBound hΓ h]
    simp only [CapyCaptureSet.compile]
termination_by (sizeOf Γ, sizeOf cs)
end

/-! ### Type-level commutation (next layer) — and a subtlety it exposes

The `fresh` case needs the *type*-level analogue,

  `⟦T[D/c]⟧_ctx = ⟦T⟧_{exiCtx ctx} [⟦D⟧/c]`     (`CapyTy.compile_openCVar`)

with `exiCtx ctx := ctx.weakenTarget.consCVar (.unbound .epsilon) .here` (the
`.exi`-compiler's extended context).  Its structural cases (`cap`/`cell`/`typ`/…)
reduce directly to `CapyCaptureSet.compile_subst_openCVar` above.

The `arrow`/`poly`/`cpoly` cases are where the story gets interesting.  A compiled
function carries a separation lock `Ψ = peakSepCtx (peakset Γ W) …`, and `peakset`
**expands** each capture to its *peaks* (resolving term variables to their declared
type's capture, `peaksVarBound`).  Two layers result:

1. The peak-content agrees only if compilation is invariant under peak-resolution,
   `⟦cs⟧ = ⟦peaks Γ cs⟧` (★).  This is NOT a type-compiler identity — it holds via
   alignment (`SrcAligned`, the `Coherent` field) + `peaksVarBound_eq_captureSet`.
   It is now PROVEN: `CapyCaptureSet.compile_peaks` above (mutual, closedness-guarded).

2. The lock's *grouping* does not commute as an equality, but it commutes up to
   SUBTYPING — which is all `fresh` needs.  `peakSepCtx` emits one item per distinct
   peak cvar.  Opening `c ↦ D = {c₁,c₂}`: `⟦T[D/c]⟧` re-groups by `D`'s peaks (two
   items ⇒ demands `c₁ ⊥ c₂`); `⟦T⟧[⟦D⟧/c]` keeps `c`'s single item (merged ⇒
   demands nothing).  A modal lock is *contravariant* in its demand, so the
   separated modal is a SUBTYPE of the merged one: `Subtyp.modal_modal` needs
   `Satisfy (Γ.push_lock Ψmerged) Ψsep`, i.e. `D`'s peaks pairwise-separate in `Γ` —
   delivered by `fresh`'s `droppable Γ D` premise (`sep_droppable`).  So the
   type-level statement is `⟦T[D/c]⟧ <: ⟦T⟧[⟦D⟧/c]`, and the let-bound value
   subsumes to `pack`'s argument.  Routine (given the foundations above), not a
   design gap.  See the `fresh` case of `CapyHasType.compile`. -/

end Compilation
