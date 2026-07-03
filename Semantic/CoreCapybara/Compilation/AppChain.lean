import Semantic.CoreCapybara.Substitution

open CoreCapybara

namespace Compilation

set_option linter.style.longLine false

theorem Subst.comp_var {s1 s2 s3 : Sig} {σ1 : Subst s1 s2} {σ2 : Subst s2 s3}
    {x : BVar s1 .var} : (σ1.comp σ2).var x = (σ1.var x).subst σ2 := rfl
theorem Subst.comp_cvar {s1 s2 s3 : Sig} {σ1 : Subst s1 s2} {σ2 : Subst s2 s3}
    {c : BVar s1 .cvar} : (σ1.comp σ2).cvar c = (σ1.cvar c).subst σ2 := rfl
theorem Subst.comp_tvar {s1 s2 s3 : Sig} {σ1 : Subst s1 s2} {σ2 : Subst s2 s3}
    {X : BVar s1 .tvar} : (σ1.comp σ2).tvar X = (σ1.tvar X).subst σ2 := rfl

theorem CaptureSet.subst_cvar {s1 s2 : Sig} {a : Access} {c : BVar s1 .cvar} {σ : Subst s1 s2} :
    (CaptureSet.cvar a c).subst σ = (σ.cvar c).applyAccess a := rfl
theorem CaptureSet.rename_cvar {s1 s2 : Sig} {a : Access} {c : BVar s1 .cvar} {f : Rename s1 s2} :
    (CaptureSet.cvar a c).rename f = .cvar a (f.var c) := rfl
theorem Subst.openCVar_here {s : Sig} {w : CaptureSet s} :
    (Subst.openCVar w).cvar .here = w := rfl
theorem Subst.openCVar_there {s : Sig} {w : CaptureSet s} {c : BVar s .cvar} :
    (Subst.openCVar w).cvar (.there c) = .cvar (.M .epsilon) c := rfl
theorem Subst.openVar_cvar_there {s : Sig} {z : Var .var s} {c : BVar s .cvar} :
    (Subst.openVar z).cvar (.there c) = .cvar (.M .epsilon) c := rfl

theorem Subst.lift_here_var {s1 s2 : Sig} {σ : Subst s1 s2} :
    (σ.lift (k := .var)).var .here = .bound .here := rfl
theorem Subst.lift_here_cvar {s1 s2 : Sig} {σ : Subst s1 s2} :
    (σ.lift (k := .cvar)).cvar .here = .cvar (.M .epsilon) .here := rfl
theorem Subst.lift_here_tvar {s1 s2 : Sig} {σ : Subst s1 s2} :
    (σ.lift (k := .tvar)).tvar .here = PureTy.tvar .here := rfl

/-- The everything-at-once opening of the compiled-application tower's three
    binders (c ↦ Dt, cx ↦ Cy, param ↦ yv): the collapse of the ANF chain's
    interleaved capp/app instantiations and let-pushes. -/
def appOpen {s : Sig} (Dt Cy : CaptureSet s) (yv : Var .var s) :
    Subst (s,C,C,x) s where
  var := fun
    | .here => yv
    | .there (.there (.there x0)) => .bound x0
  tvar := fun
    | .there (.there (.there X0)) => PureTy.tvar X0
  cvar := fun
    | .there .here => Cy
    | .there (.there .here) => Dt
    | .there (.there (.there c0)) => .cvar (.M .epsilon) c0

theorem appOpen_cvar_c {s : Sig} {Dt Cy : CaptureSet s} {yv : Var .var s} :
    (appOpen Dt Cy yv).cvar (.there (.there .here)) = Dt := rfl
theorem appOpen_cvar_cx {s : Sig} {Dt Cy : CaptureSet s} {yv : Var .var s} :
    (appOpen Dt Cy yv).cvar (.there .here) = Cy := rfl

/-- The composite `appOpen` substitution is closed when its three payloads are:
    the value image `yv`, the redirected-parameter capture `Cy`, and the compiled
    argument `Dt`.  (The remaining slots are shifts to closed atoms.)  Needed for the
    `Subtyp.trans` middle-type closedness of the codomain G-decomposition. -/
theorem appOpen_is_closed {s : Sig} {Dt Cy : CaptureSet s} {yv : Var .var s}
    (hDt : Dt.IsClosed) (hCy : Cy.IsClosed) (hyv : yv.IsClosed) :
    (appOpen Dt Cy yv).IsClosed where
  var_closed := fun x => by
    match x with
    | .here => exact hyv
    | .there (.there (.there _)) => exact Var.IsClosed.bound
  tvar_closed := fun X => by
    match X with
    | .there (.there (.there _)) => exact Ty.IsClosed.tvar
  cvar_closed := fun C => by
    match C with
    | .there .here => exact hCy
    | .there (.there .here) => exact hDt
    | .there (.there (.there _)) => exact CaptureSet.IsClosed.cvar

theorem CaptureSet.appChain_collapse {s : Sig} {Dt Cy : CaptureSet s} {yv : Var .var s}
    (X : CaptureSet (s,C,C,x)) :
    ((((((X.subst (((Subst.openCVar Dt).lift (k := .cvar)).lift (k := .var))).rename
        (((Rename.succ (k := .var)).lift (k := .cvar)).lift (k := .var))).subst
        ((Subst.openCVar (Cy.rename (Rename.succ (k := .var)))).lift (k := .var))).rename
        ((Rename.succ (k := .var)).lift (k := .var))).subst
        (Subst.openVar ((yv.rename (Rename.succ (k := .var))).rename (Rename.succ (k := .var))))).rename
        (Rename.succ (k := .var)))
      = (((X.subst (appOpen Dt Cy yv)).rename (Rename.succ (k := .var))).rename
          (Rename.succ (k := .var))).rename (Rename.succ (k := .var)) := by
  simp only [← CaptureSet.subst_asSubst, CaptureSet.subst_comp]
  congr 1
  apply Subst.funext
  · intro x
    match x with
    | .here => cases yv <;> rfl
    | .there (.there (.there x0)) => rfl
  · intro X
    match X with
    | .there (.there (.there X0)) => rfl
  · intro C
    match C with
    | .there .here =>
      rw [Subst.comp_cvar, Subst.comp_cvar, Subst.comp_cvar, Subst.comp_cvar, Subst.comp_cvar,
        Subst.comp_cvar, Subst.comp_cvar, Subst.comp_cvar, appOpen_cvar_cx]
      change (((((CaptureSet.cvar (.M .epsilon) (.there .here)).subst
          Rename.succ.lift.lift.asSubst).subst
          (Subst.openCVar (Cy.subst Rename.succ.asSubst)).lift).subst
          Rename.succ.lift.asSubst).subst
          (Subst.openVar ((yv.rename Rename.succ).rename Rename.succ))).subst Rename.succ.asSubst
        = ((Cy.subst Rename.succ.asSubst).subst Rename.succ.asSubst).subst Rename.succ.asSubst
      simp only [CaptureSet.subst_asSubst, CaptureSet.subst_cvar, CaptureSet.rename_cvar]
      change ((((Cy.rename Rename.succ).rename Rename.succ).rename Rename.succ.lift).subst
          (Subst.openVar ((yv.rename Rename.succ).rename Rename.succ))).rename Rename.succ
        = ((Cy.rename Rename.succ).rename Rename.succ).rename Rename.succ
      simp only [CaptureSet.weaken_rename_comm, CaptureSet.weaken_openVar]
    | .there (.there .here) =>
      rw [Subst.comp_cvar, Subst.comp_cvar, Subst.comp_cvar, Subst.comp_cvar, Subst.comp_cvar,
        Subst.comp_cvar, Subst.comp_cvar, Subst.comp_cvar, appOpen_cvar_c]
      change (((((((Dt.rename (Rename.succ (k := .cvar))).rename (Rename.succ (k := .var)))).subst
          Rename.succ.lift.lift.asSubst).subst
          (Subst.openCVar (Cy.subst Rename.succ.asSubst)).lift).subst
          Rename.succ.lift.asSubst).subst
          (Subst.openVar ((yv.rename Rename.succ).rename Rename.succ))).subst Rename.succ.asSubst
        = ((Dt.subst Rename.succ.asSubst).subst Rename.succ.asSubst).subst Rename.succ.asSubst
      simp only [← CaptureSet.subst_asSubst, CaptureSet.subst_comp]
      congr 1
    | .there (.there (.there c0)) => rfl

/-- The `SepCtx` lifting of the ANF application-chain collapse: structural over the
    context, reusing the capture-set collapse on each stored capture. -/
theorem SepCtx.appChain_collapse {s : Sig} {Dt Cy : CaptureSet s} {yv : Var .var s}
    (Ψ : SepCtx (s,C,C,x)) :
    ((((((Ψ.subst (((Subst.openCVar Dt).lift (k := .cvar)).lift (k := .var))).rename
        (((Rename.succ (k := .var)).lift (k := .cvar)).lift (k := .var))).subst
        ((Subst.openCVar (Cy.rename (Rename.succ (k := .var)))).lift (k := .var))).rename
        ((Rename.succ (k := .var)).lift (k := .var))).subst
        (Subst.openVar ((yv.rename (Rename.succ (k := .var))).rename (Rename.succ (k := .var))))).rename
        (Rename.succ (k := .var)))
      = (((Ψ.subst (appOpen Dt Cy yv)).rename (Rename.succ (k := .var))).rename
          (Rename.succ (k := .var))).rename (Rename.succ (k := .var)) := by
  induction Ψ with
  | empty => rfl
  | cons K Cc ih =>
    simp only [SepCtx.subst, SepCtx.rename, ih, CaptureSet.appChain_collapse]

/-- The `MutabilityCtx` lifting of the ANF application-chain collapse. -/
theorem MutabilityCtx.appChain_collapse {s : Sig} {Dt Cy : CaptureSet s} {yv : Var .var s}
    (Ψ : MutabilityCtx (s,C,C,x)) :
    ((((((Ψ.subst (((Subst.openCVar Dt).lift (k := .cvar)).lift (k := .var))).rename
        (((Rename.succ (k := .var)).lift (k := .cvar)).lift (k := .var))).subst
        ((Subst.openCVar (Cy.rename (Rename.succ (k := .var)))).lift (k := .var))).rename
        ((Rename.succ (k := .var)).lift (k := .var))).subst
        (Subst.openVar ((yv.rename (Rename.succ (k := .var))).rename (Rename.succ (k := .var))))).rename
        (Rename.succ (k := .var)))
      = (((Ψ.subst (appOpen Dt Cy yv)).rename (Rename.succ (k := .var))).rename
          (Rename.succ (k := .var))).rename (Rename.succ (k := .var)) := by
  induction Ψ with
  | empty => rfl
  | cons K Cc m ih =>
    simp only [MutabilityCtx.subst, MutabilityCtx.rename, ih, CaptureSet.appChain_collapse]

/-- The `ModalCtx` lifting of the ANF application-chain collapse: componentwise from
    the separation and mutability liftings. -/
theorem ModalCtx.appChain_collapse {s : Sig} {Dt Cy : CaptureSet s} {yv : Var .var s}
    (Ψ : ModalCtx (s,C,C,x)) :
    ((((((Ψ.subst (((Subst.openCVar Dt).lift (k := .cvar)).lift (k := .var))).rename
        (((Rename.succ (k := .var)).lift (k := .cvar)).lift (k := .var))).subst
        ((Subst.openCVar (Cy.rename (Rename.succ (k := .var)))).lift (k := .var))).rename
        ((Rename.succ (k := .var)).lift (k := .var))).subst
        (Subst.openVar ((yv.rename (Rename.succ (k := .var))).rename (Rename.succ (k := .var))))).rename
        (Rename.succ (k := .var)))
      = (((Ψ.subst (appOpen Dt Cy yv)).rename (Rename.succ (k := .var))).rename
          (Rename.succ (k := .var))).rename (Rename.succ (k := .var)) := by
  cases Ψ with
  | mk sep mu =>
    simp only [ModalCtx.subst, ModalCtx.rename, SepCtx.appChain_collapse,
      MutabilityCtx.appChain_collapse]

/-- The `CaptureBound` lifting of the ANF application-chain collapse. -/
theorem CaptureBound.appChain_collapse {s : Sig} {Dt Cy : CaptureSet s} {yv : Var .var s}
    (cb : CaptureBound (s,C,C,x)) :
    ((((((cb.subst (((Subst.openCVar Dt).lift (k := .cvar)).lift (k := .var))).rename
        (((Rename.succ (k := .var)).lift (k := .cvar)).lift (k := .var))).subst
        ((Subst.openCVar (Cy.rename (Rename.succ (k := .var)))).lift (k := .var))).rename
        ((Rename.succ (k := .var)).lift (k := .var))).subst
        (Subst.openVar ((yv.rename (Rename.succ (k := .var))).rename (Rename.succ (k := .var))))).rename
        (Rename.succ (k := .var)))
      = (((cb.subst (appOpen Dt Cy yv)).rename (Rename.succ (k := .var))).rename
          (Rename.succ (k := .var))).rename (Rename.succ (k := .var)) := by
  cases cb with
  | unbound => rfl
  | bound cs =>
    simp only [CaptureBound.subst, CaptureBound.rename, CaptureSet.appChain_collapse]

/-- The `Ty` lifting of the ANF application-chain collapse.  The three nested
    ANF substitutions (`c ↦ ⟦D⟧`, `cx ↦ Cy`, `p ↦ y`, each interleaved with a
    tower weakening) compose into the single `appOpen` substitution on the raw
    compiled codomain, up to the three ambient weakenings — exactly as for the
    `ModalCtx`/`CaptureSet` payloads.  Generic over `Ty.subst_comp`, so it needs
    no structural case analysis: after `subst_asSubst`+`subst_comp`+`congr 1` the
    residual `Subst` equality is category-agnostic (identical to the `CaptureSet`
    collapse's `funext`). -/
theorem Ty.appChain_collapse {s : Sig} {Dt Cy : CaptureSet s} {yv : Var .var s}
    {sort : TySort} (T : Ty sort (s,C,C,x)) :
    ((((((T.subst (((Subst.openCVar Dt).lift (k := .cvar)).lift (k := .var))).rename
        (((Rename.succ (k := .var)).lift (k := .cvar)).lift (k := .var))).subst
        ((Subst.openCVar (Cy.rename (Rename.succ (k := .var)))).lift (k := .var))).rename
        ((Rename.succ (k := .var)).lift (k := .var))).subst
        (Subst.openVar ((yv.rename (Rename.succ (k := .var))).rename (Rename.succ (k := .var))))).rename
        (Rename.succ (k := .var)))
      = (((T.subst (appOpen Dt Cy yv)).rename (Rename.succ (k := .var))).rename
          (Rename.succ (k := .var))).rename (Rename.succ (k := .var)) := by
  simp only [← Ty.subst_asSubst, ← CaptureSet.subst_asSubst, Ty.subst_comp]
  congr 1
  apply Subst.funext
  · intro x
    match x with
    | .here => cases yv <;> rfl
    | .there (.there (.there x0)) => rfl
  · intro X
    match X with
    | .there (.there (.there X0)) => rfl
  · intro C
    match C with
    | .there .here =>
      rw [Subst.comp_cvar, Subst.comp_cvar, Subst.comp_cvar, Subst.comp_cvar, Subst.comp_cvar,
        Subst.comp_cvar, Subst.comp_cvar, Subst.comp_cvar, appOpen_cvar_cx]
      change (((((CaptureSet.cvar (.M .epsilon) (.there .here)).subst
          Rename.succ.lift.lift.asSubst).subst
          (Subst.openCVar (Cy.subst Rename.succ.asSubst)).lift).subst
          Rename.succ.lift.asSubst).subst
          (Subst.openVar ((yv.rename Rename.succ).rename Rename.succ))).subst Rename.succ.asSubst
        = ((Cy.subst Rename.succ.asSubst).subst Rename.succ.asSubst).subst Rename.succ.asSubst
      simp only [CaptureSet.subst_asSubst, CaptureSet.subst_cvar, CaptureSet.rename_cvar]
      change ((((Cy.rename Rename.succ).rename Rename.succ).rename Rename.succ.lift).subst
          (Subst.openVar ((yv.rename Rename.succ).rename Rename.succ))).rename Rename.succ
        = ((Cy.rename Rename.succ).rename Rename.succ).rename Rename.succ
      simp only [CaptureSet.weaken_rename_comm, CaptureSet.weaken_openVar]
    | .there (.there .here) =>
      rw [Subst.comp_cvar, Subst.comp_cvar, Subst.comp_cvar, Subst.comp_cvar, Subst.comp_cvar,
        Subst.comp_cvar, Subst.comp_cvar, Subst.comp_cvar, appOpen_cvar_c]
      change (((((((Dt.rename (Rename.succ (k := .cvar))).rename (Rename.succ (k := .var)))).subst
          Rename.succ.lift.lift.asSubst).subst
          (Subst.openCVar (Cy.subst Rename.succ.asSubst)).lift).subst
          Rename.succ.lift.asSubst).subst
          (Subst.openVar ((yv.rename Rename.succ).rename Rename.succ))).subst Rename.succ.asSubst
        = ((Dt.subst Rename.succ.asSubst).subst Rename.succ.asSubst).subst Rename.succ.asSubst
      simp only [← CaptureSet.subst_asSubst, CaptureSet.subst_comp]
      congr 1
    | .there (.there (.there c0)) => rfl

/-- The everything-at-once opening of the compiled arg-fit tower's TWO cpoly
    binders (c ↦ Dt, cx ↦ Cy): the 2-capp analog of `appOpen`, without the
    value-parameter slot.  Instantiates the outer cpoly `c` (`.there .here`) to the
    compiled argument `Dt` and the inner cpoly `cx` (`.here`) to the redirected
    parameter capture `Cy`; the remaining slots are shifts to closed atoms. -/
def argOpen {s : Sig} (Dt Cy : CaptureSet s) :
    Subst (s,C,C) s where
  var := fun
    | .there (.there x0) => .bound x0
  tvar := fun
    | .there (.there X0) => PureTy.tvar X0
  cvar := fun
    | .here => Cy
    | .there .here => Dt
    | .there (.there c0) => .cvar (.M .epsilon) c0

theorem argOpen_cvar_c {s : Sig} {Dt Cy : CaptureSet s} :
    (argOpen Dt Cy).cvar (.there .here) = Dt := rfl
theorem argOpen_cvar_cx {s : Sig} {Dt Cy : CaptureSet s} :
    (argOpen Dt Cy).cvar .here = Cy := rfl

/-- The arg-fit `argOpen` substitution is closed when its two payloads are: the
    redirected-parameter capture `Cy` and the compiled argument `Dt`.  (The remaining
    slots are shifts to closed atoms.)  The 2-cpoly (no value-param) analogue of
    `appOpen_is_closed`. -/
theorem argOpen_is_closed {s : Sig} {Dt Cy : CaptureSet s}
    (hDt : Dt.IsClosed) (hCy : Cy.IsClosed) :
    (argOpen Dt Cy).IsClosed where
  var_closed := fun x => by
    match x with
    | .there (.there _) => exact Var.IsClosed.bound
  tvar_closed := fun X => by
    match X with
    | .there (.there _) => exact Ty.IsClosed.tvar
  cvar_closed := fun C => by
    match C with
    | .here => exact hCy
    | .there .here => exact hDt
    | .there (.there _) => exact CaptureSet.IsClosed.cvar

/-- The `Ty` lifting of the ANF ARG-FIT chain collapse (2-capp, no value param).
    The two nested ANF cpoly substitutions (`c ↦ ⟦D⟧`, `cx ↦ Cy`, each interleaved
    with a tower weakening) compose into the single `argOpen` substitution on the raw
    compiled domain, up to the two ambient var-weakenings.  This is the arg-fit analog
    of `Ty.appChain_collapse`, targeting `M2.rename succ` where
    `M = A.subst (openCVar Dt).lift` and `M2 = (M.rename succ.lift).subst (openCVar (Cy.rename succ))`.
    Generic over `Ty.subst_comp`, so after `subst_asSubst`+`subst_comp`+`congr 1` the
    residual `Subst` equality is category-agnostic. -/
theorem Ty.argChain_collapse {s : Sig} {Dt Cy : CaptureSet s}
    {sort : TySort} (E : Ty sort (s,C,C)) :
    (((E.subst ((Subst.openCVar Dt).lift (k := .cvar))).rename
        ((Rename.succ (k := .var)).lift (k := .cvar))).subst
        (Subst.openCVar (Cy.rename (Rename.succ (k := .var))))).rename
        (Rename.succ (k := .var))
      = ((E.subst (argOpen Dt Cy)).rename (Rename.succ (k := .var))).rename
          (Rename.succ (k := .var)) := by
  simp only [← Ty.subst_asSubst, ← CaptureSet.subst_asSubst, Ty.subst_comp]
  congr 1
  apply Subst.funext
  · intro x
    match x with
    | .there (.there x0) => rfl
  · intro X
    match X with
    | .there (.there X0) => rfl
  · intro C
    match C with
    | .here =>
      simp only [Subst.comp_cvar, argOpen_cvar_cx]
      change ((((CaptureSet.cvar (.M .epsilon) BVar.here).subst Rename.succ.lift.asSubst).subst
          (Subst.openCVar (Cy.subst Rename.succ.asSubst))).subst Rename.succ.asSubst)
        = (Cy.subst Rename.succ.asSubst).subst Rename.succ.asSubst
      simp only [CaptureSet.subst_asSubst, CaptureSet.subst_cvar, CaptureSet.rename_cvar]
      rfl
    | .there .here =>
      simp only [Subst.comp_cvar, argOpen_cvar_c]
      change ((((Dt.rename (Rename.succ (k := .cvar))).subst Rename.succ.lift.asSubst).subst
          (Subst.openCVar (Cy.subst Rename.succ.asSubst))).subst Rename.succ.asSubst)
        = (Dt.subst Rename.succ.asSubst).subst Rename.succ.asSubst
      simp only [← CaptureSet.subst_asSubst, CaptureSet.subst_comp]
      congr 1
    | .there (.there c0) => rfl

/-- The weakened-image cancellation used to compute chain images of items that do not
    mention the three tower binders: an item weakened past the two cvar binders and the
    param binder is mapped straight back by `appOpen`. -/
theorem CaptureSet.appOpen_weaken_cancel {s : Sig} {Dt Cy : CaptureSet s} {yv : Var .var s}
    (Z : CaptureSet s) :
    (((Z.rename (Rename.succ (k := .cvar))).rename (Rename.succ (k := .cvar))).rename
        (Rename.succ (k := .var))).subst (appOpen Dt Cy yv) = Z := by
  simp only [← CaptureSet.subst_asSubst, CaptureSet.subst_comp]
  conv_rhs => rw [← CaptureSet.subst_id (cs := Z)]
  congr 1

end Compilation
