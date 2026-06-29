import Semantic.CoreCapybara.Compilation.CompileLemmas

/-!
# Context morphisms

A renaming `f : Rename s1 s2` acts on a typing context as a *morphism*: it sends
every lookup to its `f`-renamed image.  We record this as a relation
`Γ1.RenamesTo Γ2 f` per context type — the natural "`Γ2` is the `f`-renaming of
`Γ1`" — stated on the lookup *judgments* (so authority and lock data ride along
with no special-casing).  There is deliberately no total `CapyCtx.rename`/`Ctx.rename`:
the contexts are telescopes, so a general renaming has no well-typed *action*, only
this *relation*.

On top of the two calculus-level relations sits the compiler-context morphism
`CompilerCtx.MapsTo ctx1 ctx2 fs ft`, which additionally relates the source→target
map `srcCtx`.  The single theorem

  `compile (T.rename fs) ctx2 = (compile T ctx1).rename ft`

then commutes compilation with the morphism, subsuming both `CapyTy.compile_rename`
(the `fs = id` slice — `RenamesTo` is that special case) and the source-weakening
alignment `compile (T.rename succ) (ctx.cons b) = (compile T ctx).rename succ` that
coherence-preservation needs (the `fs = succ` slice).
-/

namespace CoreCapybara

/-- **`Γ2` is the `f`-renaming of the source typing context `Γ1`.**  Equivalently,
    `f` is a morphism `Γ1 ⟶ Γ2`: it transports every lookup to its renamed image.
    The defining property of context renaming; the operational facts (e.g. that
    `peaks` commutes with `f`, below) are consequences. -/
structure CapyCtx.RenamesTo {s1 s2 : Sig}
    (Γ1 : CapyCtx s1) (Γ2 : CapyCtx s2) (f : Rename s1 s2) : Prop where
  var  : ∀ {x : BVar s1 .var} {T : CapyTy .capt s1},
    Γ1.LookupVar x T → Γ2.LookupVar (f.var x) (T.rename f)
  cvar : ∀ {c : BVar s1 .cvar} {a : CapyAuthority} {cb : CapyCaptureBound s1},
    Γ1.LookupCVar c a cb → Γ2.LookupCVar (f.var c) a (cb.rename f)
  tvar : ∀ {X : BVar s1 .tvar} {S : CapyPureTy s1},
    Γ1.LookupTVar X S → Γ2.LookupTVar (f.var X) (S.rename f)

/-- **`Γ2` is the `f`-renaming of the target typing context `Γ1`.**  Same shape as
    `CapyCtx.RenamesTo`, with the extra lock lookup the Core calculus carries. -/
structure Ctx.RenamesTo {s1 s2 : Sig}
    (Γ1 : Ctx s1) (Γ2 : Ctx s2) (f : Rename s1 s2) : Prop where
  var  : ∀ {x : BVar s1 .var} {T : Ty .capt s1},
    Γ1.LookupVar x T → Γ2.LookupVar (f.var x) (T.rename f)
  cvar : ∀ {c : BVar s1 .cvar} {a : Authority} {cb : CaptureBound s1},
    Γ1.LookupCVar c a cb → Γ2.LookupCVar (f.var c) a (cb.rename f)
  tvar : ∀ {X : BVar s1 .tvar} {S : PureTy s1},
    Γ1.LookupTVar X S → Γ2.LookupTVar (f.var X) (S.rename f)
  lock : ∀ {ℓ : BVar s1 .lock} {Ψ : ModalCtx s1},
    Γ1.LookupLock ℓ Ψ → Γ2.LookupLock (f.var ℓ) (Ψ.rename f)

/-- A morphism out of an *extended* source context restricts to one out of the
    tail, precomposed with the weakening `succ`.  This is the structural engine
    behind peak-resolution naturality: `peaks` peels the context one binder at a
    time, and at each peel the morphism follows.  Note `Γ2` is *not* peeled — the
    morphism is purely lookup-based, so the tail still maps into the whole `Γ2`. -/
theorem CapyCtx.RenamesTo.unpush {s1 s2 : Sig} {k : Kind} {Γ1 : CapyCtx s1}
    {b : CapyBinding s1 k} {Γ2 : CapyCtx s2} {f : Rename (s1,,k) s2}
    (h : (Γ1.push b).RenamesTo Γ2 f) : Γ1.RenamesTo Γ2 (Rename.succ.comp f) where
  var hl := by
    have := h.var (CapyCtx.LookupVar.there (b := b) hl)
    rwa [CapyTy.rename_comp] at this
  cvar hl := by
    have := h.cvar (CapyCtx.LookupCVar.there (b := b) hl)
    rwa [CapyCaptureBound.rename_comp] at this
  tvar hl := by
    have := h.tvar (CapyCtx.LookupTVar.there (b := b) hl)
    rwa [CapyPureTy.rename_comp] at this

/-! ### Weakening commutes with renaming under a binder (payload-type instances).

The `…weaken_rename_comm` family says `(X.rename succ).rename f.lift = (X.rename f).rename succ`
— exactly what realigns a `there`-lookup's `rename succ` after the morphism `f` lifts past a
fresh binder.  `CapyTy`/`Ty`/`CapyPureTy`/`PureTy` already have theirs; the rest follow. -/

theorem CapyCaptureBound.weaken_rename_comm {cb : CapyCaptureBound s1} {f : Rename s1 s2} :
    (cb.rename Rename.succ).rename (f.lift (k:=k0)) = (cb.rename f).rename Rename.succ := by
  rw [CapyCaptureBound.rename_comp, Rename.succ_lift_comm, ← CapyCaptureBound.rename_comp]

theorem CaptureBound.weaken_rename_comm {cb : CaptureBound s1} {f : Rename s1 s2} :
    (cb.rename Rename.succ).rename (f.lift (k:=k0)) = (cb.rename f).rename Rename.succ := by
  rw [CaptureBound.rename_comp, Rename.succ_lift_comm, ← CaptureBound.rename_comp]

theorem ModalCtx.weaken_rename_comm {Ψ : ModalCtx s1} {f : Rename s1 s2} :
    (Ψ.rename Rename.succ).rename (f.lift (k:=k0)) = (Ψ.rename f).rename Rename.succ := by
  rw [ModalCtx.rename_comp, Rename.succ_lift_comm, ← ModalCtx.rename_comp]

/-- Capture-set refinement commutes with renaming. -/
theorem CapyTy.refineCaptureSet_rename {T : CapyTy .capt s1} {cs : CapyCaptureSet s1}
    {f : Rename s1 s2} :
    (T.refineCaptureSet cs).rename f = (T.rename f).refineCaptureSet (cs.rename f) := by
  cases T <;> simp only [CapyTy.refineCaptureSet, CapyTy.rename]

/-! ### Injective renamings

`peakSepCtx` deduplicates peaks, so it commutes with a source renaming only when the
renaming keeps distinct peaks distinct — i.e. is injective.  Every concretely built
renaming (`id`, `succ`, `lift`, `comp`) is; non-injective maps are substitutions,
handled elsewhere. -/

/-- A renaming whose variable action is injective at every kind.  `k` is explicit
    (not `{k}`) so that an `Injective` value passes cleanly to a parameter of the
    same type without triggering Lean's implicit-lambda elaboration. -/
def Rename.Injective {s1 s2 : Sig} (f : Rename s1 s2) : Prop :=
  ∀ (k : Kind), Function.Injective (f.var (k := k))

theorem Rename.injective_id {s : Sig} : (Rename.id (s := s)).Injective := by
  intro _ a b h; exact h

theorem Rename.injective_succ {s : Sig} {k : Kind} :
    (Rename.succ (s := s) (k := k)).Injective := by
  intro _ a b h; exact BVar.there.inj h

theorem Rename.Injective.lift {s1 s2 : Sig} {k0 : Kind} {f : Rename s1 s2}
    (hf : f.Injective) : (f.lift (k := k0)).Injective := by
  intro k a b h
  cases a with
  | here =>
    cases b with
    | here => rfl
    | there b' => simp [Rename.lift] at h
  | there a' =>
    cases b with
    | here => simp [Rename.lift] at h
    | there b' =>
      simp only [Rename.lift, BVar.there.injEq] at h
      exact congrArg BVar.there (hf k h)

/-- A morphism extends under a fresh source binder: pushing `b` (resp. its `f`-image)
    on both sides keeps the contexts related over `f.lift`.  Dual to `unpush`.  The
    payload's `rename succ` realigns via `weaken_rename_comm`; the variable image
    (`f.lift.var .here = .here`, `f.lift.var (.there x) = .there (f.var x)`) is defeq
    so `exact` closes it without unfolding `Rename.lift`. -/
theorem CapyCtx.RenamesTo.push {s1 s2 : Sig} {k : Kind} {Γ1 : CapyCtx s1} {Γ2 : CapyCtx s2}
    {f : Rename s1 s2} (h : Γ1.RenamesTo Γ2 f) (b : CapyBinding s1 k) :
    (Γ1.push b).RenamesTo (Γ2.push (b.rename f)) f.lift where
  var hl := by
    cases hl with
    | here => rw [CapyTy.weaken_rename_comm]; exact CapyCtx.LookupVar.here
    | there hl' => rw [CapyTy.weaken_rename_comm]; exact CapyCtx.LookupVar.there (h.var hl')
  cvar hl := by
    cases hl with
    | here => rw [CapyCaptureBound.weaken_rename_comm]; exact CapyCtx.LookupCVar.here
    | there hl' =>
      rw [CapyCaptureBound.weaken_rename_comm]; exact CapyCtx.LookupCVar.there (h.cvar hl')
  tvar hl := by
    cases hl with
    | here => rw [CapyPureTy.weaken_rename_comm]; exact CapyCtx.LookupTVar.here
    | there hl' =>
      rw [CapyPureTy.weaken_rename_comm]; exact CapyCtx.LookupTVar.there (h.tvar hl')

/-- Target-context analogue of `CapyCtx.RenamesTo.push` (carries the lock field). -/
theorem Ctx.RenamesTo.push {s1 s2 : Sig} {k : Kind} {Γ1 : Ctx s1} {Γ2 : Ctx s2}
    {f : Rename s1 s2} (h : Γ1.RenamesTo Γ2 f) (b : Binding s1 k) :
    (Γ1.push b).RenamesTo (Γ2.push (b.rename f)) f.lift where
  var hl := by
    cases hl with
    | here => rw [Ty.weaken_rename_comm]; exact Ctx.LookupVar.here
    | there hl' => rw [Ty.weaken_rename_comm]; exact Ctx.LookupVar.there (h.var hl')
  cvar hl := by
    cases hl with
    | here => rw [CaptureBound.weaken_rename_comm]; exact Ctx.LookupCVar.here
    | there hl' =>
      rw [CaptureBound.weaken_rename_comm]; exact Ctx.LookupCVar.there (h.cvar hl')
  tvar hl := by
    cases hl with
    | here => rw [PureTy.weaken_rename_comm]; exact Ctx.LookupTVar.here
    | there hl' => rw [PureTy.weaken_rename_comm]; exact Ctx.LookupTVar.there (h.tvar hl')
  lock hl := by
    cases hl with
    | here => rw [ModalCtx.weaken_rename_comm]; exact Ctx.LookupLock.here
    | there hl' => rw [ModalCtx.weaken_rename_comm]; exact Ctx.LookupLock.there (h.lock hl')

/-- Source peak-resolution commutes with a context renaming — the one operational
    consequence the compiled lock needs, *derived* from the morphism (not assumed).
    Generalizes `CapyCaptureSet.peaks_rename_succ_eq` from `succ` to any `f`.

    By well-founded recursion peeling `Γ1` (`unpush`); the only non-structural
    step is the bound-var leaf, where `var_peaks` resolves the `Γ2` side through
    the transported lookup so no structural knowledge of `Γ2` is needed. -/
theorem CapyCaptureSet.peaks_renamesTo {s1 s2 : Sig}
    {Γ1 : CapyCtx s1} {Γ2 : CapyCtx s2} {f : Rename s1 s2}
    (h : Γ1.RenamesTo Γ2 f) (W : CapyCaptureSet s1) :
    CapyCaptureSet.peaks Γ2 (W.rename f) = (CapyCaptureSet.peaks Γ1 W).rename f := by
  match Γ1, W, h with
  | _, .empty, _ => simp only [CapyCaptureSet.rename, CapyCaptureSet.peaks]
  | _, .pseudo_peak W0, _ => simp only [CapyCaptureSet.rename, CapyCaptureSet.peaks]
  | _, .union W1 W2, h =>
    simp only [CapyCaptureSet.rename, CapyCaptureSet.peaks]
    rw [peaks_renamesTo h W1, peaks_renamesTo h W2]
    rfl
  | _, .cvar m c, _ => simp only [CapyCaptureSet.rename, CapyCaptureSet.peaks]
  | _, .var m (.free n), _ =>
    simp only [CapyCaptureSet.rename, Var.rename, CapyCaptureSet.peaks]
    rfl
  | .push Γ1' (.var T0), .var m (.bound .here), h =>
    have hl2 := h.var (CapyCtx.LookupVar.here (Γ := Γ1') (T := T0))
    have key := CapyCaptureSet.peaks_renamesTo (h.unpush) (T0.captureSet.applyAccess m)
    simp only [CapyCaptureSet.rename, Var.rename]
    rw [CapyCaptureSet.var_peaks hl2]
    simp only [CapyTy.captureSet_rename, CapyCaptureSet.rename_comp,
      ← CapyCaptureSet.applyAccess_rename]
    rw [key]
    simp only [CapyCaptureSet.peaks, CapyCaptureSet.peaksVarBound,
      CapyCaptureSet.peaks_applyAccess_comm, CapyCaptureSet.applyAccess_rename,
      CapyCaptureSet.rename_comp]
  | .push Γ1' b, .var m (.bound (.there x')), h =>
    have key := CapyCaptureSet.peaks_renamesTo (h.unpush) (CapyCaptureSet.var m (.bound x'))
    simp only [CapyCaptureSet.rename, Var.rename, Rename.comp, Rename.succ,
      CapyCaptureSet.peaks, CapyCaptureSet.peaksVarBound, CapyCaptureSet.rename_comp] at key ⊢
    exact key
  termination_by (sizeOf Γ1, sizeOf W)

/-- Source peak-resolution commutes with a context renaming.  Thin wrapper over
    `CapyCaptureSet.peaks_renamesTo` with the capture set implicit. -/
theorem CapyCtx.RenamesTo.peaks {s1 s2 : Sig} {Γ1 : CapyCtx s1} {Γ2 : CapyCtx s2}
    {f : Rename s1 s2} (h : Γ1.RenamesTo Γ2 f) {W : CapyCaptureSet s1} :
    CapyCaptureSet.peaks Γ2 (W.rename f) = (CapyCaptureSet.peaks Γ1 W).rename f :=
  CapyCaptureSet.peaks_renamesTo h W

/-- The whole *peak set* (peaks + its `PeaksOnly` witness) commutes with a context
    renaming; the witness is proof-irrelevant, so this is just `RenamesTo.peaks`. -/
theorem CapyCtx.RenamesTo.peakset {s1 s2 : Sig} {Γ1 : CapyCtx s1} {Γ2 : CapyCtx s2}
    {f : Rename s1 s2} (h : Γ1.RenamesTo Γ2 f) (W : CapyCaptureSet s1) :
    CapyCaptureSet.peakset Γ2 (W.rename f) = (CapyCaptureSet.peakset Γ1 W).rename f := by
  simp only [CapyCaptureSet.peakset, CapyPeakSet.rename, h.peaks]

end CoreCapybara

open CoreCapybara
namespace Compilation

/-- A **compiler-context morphism** `ctx1 ⟶ ctx2` over a source renaming `fs` and a
    target renaming `ft`: the two typing contexts are renaming-related (`capy`/`core`),
    and the source→target map `srcCtx` commutes with `(fs, ft)` on each lookup.
    `CompilerCtx.RenamesTo` (in `CompileLemmas`) is the `fs = id` special case. -/
structure CompilerCtx.MapsTo {s1 s1' s2 s2' : Sig}
    (ctx1 : CompilerCtx s1 s2) (ctx2 : CompilerCtx s1' s2')
    (fs : Rename s1 s1') (ft : Rename s2 s2') : Prop where
  /-- The source typing contexts are `fs`-renaming-related. -/
  capy : ctx1.capyCtx.RenamesTo ctx2.capyCtx fs
  /-- The target typing contexts are `ft`-renaming-related. -/
  core : ctx1.coreCtx.RenamesTo ctx2.coreCtx ft
  /-- Capture-variable images commute with `(fs, ft)`. -/
  cvar : ∀ (c : BVar s1 .cvar),
    ctx2.srcCtx.lookupCVar (fs.var c) = ft.var (ctx1.srcCtx.lookupCVar c)
  /-- Term-variable capture images commute with `(fs, ft)`. -/
  var : ∀ (x : BVar s1 .var),
    ctx2.srcCtx.lookupVar (fs.var x) = (ctx1.srcCtx.lookupVar x).rename ft
  /-- Term-variable target images commute with `(fs, ft)`. -/
  varBVar : ∀ (x : BVar s1 .var),
    ctx2.srcCtx.lookupVarBVar (fs.var x) = (ctx1.srcCtx.lookupVarBVar x).map ft.var
  /-- Type-variable images commute with `(fs, ft)`. -/
  tvar : ∀ (X : BVar s1 .tvar),
    ctx2.srcCtx.lookupTVar (fs.var X) = ft.var (ctx1.srcCtx.lookupTVar X)

/-! ### Builder-preservation (the morphism threads through the compiler's binders)

`weakenTarget` adds a *target* binder (lift `ft`, `fs` fixed); `consTVar`/`consCVar`/
`consVar` add a *source* binder (lift `fs`, `ft` fixed) whose `ctx2`-image renames
its payload.  Each reduces to a `push`-preservation of `capy`/`core` plus the
`srcCtx` field equations. -/

/-- Preserved by a fresh target binder: `ft` lifts, `fs` fixed.  The fresh binding
    on the `ctx2` side is the `ft`-image of `b`, so the `core` field holds (and the
    placeholder default is rename-stable, so `compile` sees no difference). -/
theorem CompilerCtx.MapsTo.weakenTarget {s1 s1' s2 s2' : Sig} {k : Kind}
    {ctx1 : CompilerCtx s1 s2} {ctx2 : CompilerCtx s1' s2'}
    {fs : Rename s1 s1'} {ft : Rename s2 s2'} (h : ctx1.MapsTo ctx2 fs ft)
    (b : Binding s2 k := placeholderBinding k) :
    (ctx1.weakenTarget b).MapsTo (ctx2.weakenTarget (b.rename ft)) fs ft.lift where
  capy := h.capy
  core := h.core.push b
  cvar := by
    intro c
    simp only [CompilerCtx.weakenTarget_srcCtx, SrcCtx.lookupCVar_rename, h.cvar,
      Rename.succ, Rename.lift]
  var := by
    intro x
    simp only [CompilerCtx.weakenTarget_srcCtx, SrcCtx.lookupVar_rename, h.var,
      CaptureSet.rename_comp, Rename.succ_lift_comm]
  varBVar := by
    intro x
    simp only [CompilerCtx.weakenTarget_srcCtx, SrcCtx.lookupVarBVar_rename, h.varBVar,
      Option.map_map]
    congr 1
  tvar := by
    intro X
    simp only [CompilerCtx.weakenTarget_srcCtx, SrcCtx.lookupTVar_rename, h.tvar,
      Rename.succ, Rename.lift]

/-- Preserved by a fresh source type binder: `fs` lifts, `ft` fixed. -/
theorem CompilerCtx.MapsTo.consTVar {s1 s1' s2 s2' : Sig}
    {ctx1 : CompilerCtx s1 s2} {ctx2 : CompilerCtx s1' s2'}
    {fs : Rename s1 s1'} {ft : Rename s2 s2'} (h : ctx1.MapsTo ctx2 fs ft)
    {S : CapyPureTy s1} {X : BVar s2 .tvar} :
    (ctx1.consTVar S X).MapsTo (ctx2.consTVar (S.rename fs) (ft.var X)) fs.lift ft where
  capy := by
    simp only [CompilerCtx.consTVar_capyCtx, CapyCtx.push_tvar]
    exact h.capy.push (.tvar S)
  core := h.core
  cvar := by intro c; cases c with | there c' => exact h.cvar c'
  var := by intro x; cases x with | there x' => exact h.var x'
  varBVar := by intro x; cases x with | there x' => exact h.varBVar x'
  tvar := by intro X0; cases X0 with
    | here => rfl
    | there X' => exact h.tvar X'

/-- Preserved by a fresh source capture binder: `fs` lifts, `ft` fixed. -/
theorem CompilerCtx.MapsTo.consCVar {s1 s1' s2 s2' : Sig}
    {ctx1 : CompilerCtx s1 s2} {ctx2 : CompilerCtx s1' s2'}
    {fs : Rename s1 s1'} {ft : Rename s2 s2'} (h : ctx1.MapsTo ctx2 fs ft)
    {cb : CapyCaptureBound s1} {c : BVar s2 .cvar} :
    (ctx1.consCVar cb c).MapsTo (ctx2.consCVar (cb.rename fs) (ft.var c)) fs.lift ft where
  capy := by
    simp only [CompilerCtx.consCVar_capyCtx, CapyCtx.push_cvar_default, CapyCtx.push_cvar]
    exact h.capy.push (.cvar .access_only cb)
  core := h.core
  cvar := by intro c0; cases c0 with
    | here => rfl
    | there c' => exact h.cvar c'
  var := by intro x; cases x with | there x' => exact h.var x'
  varBVar := by intro x; cases x with | there x' => exact h.varBVar x'
  tvar := by intro X; cases X with | there X' => exact h.tvar X'

/-- Preserved by a fresh source term binder: `fs` lifts, `ft` fixed; the stored
    capture image and optional target var rename by `ft`. -/
theorem CompilerCtx.MapsTo.consVar {s1 s1' s2 s2' : Sig}
    {ctx1 : CompilerCtx s1 s2} {ctx2 : CompilerCtx s1' s2'}
    {fs : Rename s1 s1'} {ft : Rename s2 s2'} (h : ctx1.MapsTo ctx2 fs ft)
    {T : CapyTy .capt s1} {bv : Option (BVar s2 .var)} {cs : CaptureSet s2} :
    (ctx1.consVar T bv cs).MapsTo
      (ctx2.consVar (T.rename fs) (bv.map ft.var) (cs.rename ft)) fs.lift ft where
  capy := by
    simp only [CompilerCtx.consVar_capyCtx, CapyCtx.push_var]
    exact h.capy.push (.var T)
  core := h.core
  cvar := by intro c; cases c with | there c' => exact h.cvar c'
  var := by intro x; cases x with
    | here => rfl
    | there x' => exact h.var x'
  varBVar := by intro x; cases x with
    | here => rfl
    | there x' => exact h.varBVar x'
  tvar := by intro X; cases X with | there X' => exact h.tvar X'

/-! ### Capture-set / capture-bound compilation under a `srcCtx` morphism

These read only the `srcCtx` field equations (`cvar`/`var`), so they are stated on
those directly (reusable inside the lock's `peakSepCtx` below). -/

theorem CapyCaptureSet.compile_mapsTo {s1 s1' t1 t2 : Sig} {sctx1 : SrcCtx s1 t1}
    {sctx2 : SrcCtx s1' t2} {fs : Rename s1 s1'} {ft : Rename t1 t2}
    (hcvar : ∀ c, sctx2.lookupCVar (fs.var c) = ft.var (sctx1.lookupCVar c))
    (hvar : ∀ x, sctx2.lookupVar (fs.var x) = (sctx1.lookupVar x).rename ft)
    (cs : CapyCaptureSet s1) :
    CapyCaptureSet.compile (cs.rename fs) sctx2 = (CapyCaptureSet.compile cs sctx1).rename ft := by
  induction cs with
  | empty => rfl
  | union cs1 cs2 ih1 ih2 =>
    simp only [CapyCaptureSet.rename, CaptureSet.rename, CapyCaptureSet.compile, ih1, ih2]
  | cvar a c =>
    simp only [CapyCaptureSet.rename, CaptureSet.rename, CapyCaptureSet.compile, hcvar c]
  | var a x =>
    cases x with
    | bound x =>
      simp only [CapyCaptureSet.rename, Var.rename, CapyCaptureSet.compile,
        hvar x, CaptureSet.applyAccess_rename]
    | free n =>
      simp only [CapyCaptureSet.rename, CaptureSet.rename, Var.rename, CapyCaptureSet.compile]
  | pseudo_peak _ ih => simp only [CapyCaptureSet.rename, CapyCaptureSet.compile, ih]

theorem CapyCaptureBound.compile_mapsTo {s1 s1' t1 t2 : Sig} {sctx1 : SrcCtx s1 t1}
    {sctx2 : SrcCtx s1' t2} {fs : Rename s1 s1'} {ft : Rename t1 t2}
    (hcvar : ∀ c, sctx2.lookupCVar (fs.var c) = ft.var (sctx1.lookupCVar c))
    (hvar : ∀ x, sctx2.lookupVar (fs.var x) = (sctx1.lookupVar x).rename ft)
    (cb : CapyCaptureBound s1) :
    CapyCaptureBound.compile (cb.rename fs) sctx2
      = (CapyCaptureBound.compile cb sctx1).rename ft := by
  cases cb with
  | unbound m => rfl
  | bound cs =>
    simp only [CapyCaptureBound.rename, CapyCaptureBound.compile, CaptureBound.rename,
      CapyCaptureSet.compile_mapsTo hcvar hvar cs]

/-- The lock's mutability field commutes with the morphism.  `mutabilityCtx` reads
    only the bound's *constructor* and mutability tag (not its capture set), so it is
    invariant under the source rename; the target `.here` realigns via `…rename_here`. -/
theorem CapyCaptureBound.mutabilityCtx_mapsTo {s1 s1' s2 s2' : Sig} {cb : CapyCaptureBound s1}
    {fs : Rename s1 s1'} {ft : Rename s2 s2'} :
    CapyCaptureBound.mutabilityCtx (cb.rename fs) (.here : BVar (s2',C) .cvar)
      = (CapyCaptureBound.mutabilityCtx cb (.here : BVar (s2,C) .cvar)).rename ft.lift := by
  rw [CapyCaptureBound.mutabilityCtx_rename_here]
  cases cb <;> rfl

/-! ### Lock separation context under an (injective) source morphism

`peakSepCtx` is a *deduplicated* fold of compiled `peakItem`s.  Under an injective
source renaming `fs` (with a `srcCtx` morphism on the target side) it commutes:
`peakCvars`/`peakItem` are natural (the injectivity makes `dedup` and the access
filter commute with `fs`), and the fold fuses with `SepCtx.rename`. -/

private theorem dedup_map_injective {α β : Type _} [DecidableEq α] [DecidableEq β]
    {f : α → β} (hf : Function.Injective f) (l : List α) :
    dedup (l.map f) = (dedup l).map f := by
  induction l with
  | nil => rfl
  | cons a as ih =>
    have hcond : (f a ∈ (dedup as).map f) ↔ (a ∈ dedup as) := by
      simp only [List.mem_map, hf.eq_iff, exists_eq_right]
    simp only [List.map_cons, dedup, ih, apply_ite (List.map f), List.map_cons, hcond]

theorem peakCvars.go_rename {s1 s2 : Sig} {fs : Rename s1 s2} (cs : CapyCaptureSet s1) :
    peakCvars.go (cs.rename fs) = (peakCvars.go cs).map fs.var := by
  induction cs with
  | empty => rfl
  | union c1 c2 ih1 ih2 =>
    simp only [CapyCaptureSet.rename, peakCvars.go, List.map_append, ih1, ih2]
  | cvar a c => simp only [CapyCaptureSet.rename, peakCvars.go, List.map_cons, List.map_nil]
  | var a x => cases x <;> simp only [CapyCaptureSet.rename, Var.rename, peakCvars.go, List.map_nil]
  | pseudo_peak _ _ => simp only [CapyCaptureSet.rename, peakCvars.go, List.map_nil]

theorem peakCvars_rename {s1 s2 : Sig} {fs : Rename s1 s2}
    (hfs : Function.Injective (fs.var (k := .cvar))) (P : CapyPeakSet s1) :
    peakCvars (P.rename fs) = (peakCvars P).map fs.var := by
  simp only [peakCvars, CapyPeakSet.rename, peakCvars.go_rename]
  exact dedup_map_injective hfs _

theorem accessedAt.go_rename {s1 s2 : Sig} {fs : Rename s1 s2}
    (hfs : Function.Injective (fs.var (k := .cvar))) {c : BVar s1 .cvar} (cs : CapyCaptureSet s1) :
    accessedAt.go (fs.var c) (cs.rename fs) = accessedAt.go c cs := by
  induction cs with
  | empty => rfl
  | union c1 c2 ih1 ih2 => simp only [CapyCaptureSet.rename, accessedAt.go, ih1, ih2]
  | cvar a c' => simp only [CapyCaptureSet.rename, accessedAt.go, hfs.eq_iff]
  | var a x => cases x <;> simp only [CapyCaptureSet.rename, Var.rename, accessedAt.go]
  | pseudo_peak _ _ => simp only [CapyCaptureSet.rename, accessedAt.go]

theorem accessedAt_rename {s1 s2 : Sig} {fs : Rename s1 s2}
    (hfs : Function.Injective (fs.var (k := .cvar))) (P : CapyPeakSet s1) (c : BVar s1 .cvar) :
    accessedAt (P.rename fs) (fs.var c) = accessedAt P c := by
  simp only [accessedAt, CapyPeakSet.rename, accessedAt.go_rename hfs]

theorem peakItem_rename {s1 s2 : Sig} {fs : Rename s1 s2}
    (hfs : Function.Injective (fs.var (k := .cvar))) (P : CapyPeakSet s1) (c : BVar s1 .cvar) :
    peakItem (P.rename fs) (fs.var c) = (peakItem P c).rename fs := by
  simp only [peakItem, accessedAt_rename hfs]
  generalize accessedAt P c = l
  induction l with
  | nil => rfl
  | cons a as ih => simp only [List.foldr_cons, CapyCaptureSet.rename, ih]; rfl

/-- The `peakSepCtx` fold fuses with `SepCtx.rename` through the injective source
    renaming and the `srcCtx` morphism (`peakItem_rename` + `compile_mapsTo`). -/
theorem peakSepCtx_foldl_mapsTo {s1 s1' t1 t2 : Sig} {sctx1 : SrcCtx s1 t1}
    {sctx2 : SrcCtx s1' t2} {fs : Rename s1 s1'} {ft : Rename t1 t2}
    (hfs : Function.Injective (fs.var (k := .cvar)))
    (hcvar : ∀ c, sctx2.lookupCVar (fs.var c) = ft.var (sctx1.lookupCVar c))
    (hvar : ∀ x, sctx2.lookupVar (fs.var x) = (sctx1.lookupVar x).rename ft)
    (P : CapyPeakSet s1) :
    ∀ (l : List (BVar s1 .cvar)) (acc1 : SepCtx t1) (acc2 : SepCtx t2), acc2 = acc1.rename ft →
      (l.map fs.var).foldl
          (fun K c => .cons K (CapyCaptureSet.compile (peakItem (P.rename fs) c) sctx2)) acc2
        = ((l.foldl (fun K c => .cons K (CapyCaptureSet.compile (peakItem P c) sctx1))
            acc1).rename ft)
  | [], _, _, hacc => by simpa using hacc
  | c :: cs, acc1, acc2, hacc => by
    simp only [List.map_cons, List.foldl_cons]
    apply peakSepCtx_foldl_mapsTo hfs hcvar hvar P cs
    simp only [SepCtx.rename, hacc]
    congr 1
    rw [peakItem_rename hfs]
    exact CapyCaptureSet.compile_mapsTo hcvar hvar (peakItem P c)

theorem peakSepCtx_mapsTo {s1 s1' t1 t2 : Sig} {sctx1 : SrcCtx s1 t1} {sctx2 : SrcCtx s1' t2}
    {fs : Rename s1 s1'} {ft : Rename t1 t2}
    (hfs : Function.Injective (fs.var (k := .cvar)))
    (hcvar : ∀ c, sctx2.lookupCVar (fs.var c) = ft.var (sctx1.lookupCVar c))
    (hvar : ∀ x, sctx2.lookupVar (fs.var x) = (sctx1.lookupVar x).rename ft)
    (P : CapyPeakSet s1) :
    peakSepCtx (P.rename fs) sctx2 = (peakSepCtx P sctx1).rename ft := by
  simp only [peakSepCtx, peakCvars_rename hfs]
  exact peakSepCtx_foldl_mapsTo hfs hcvar hvar P (peakCvars P) .empty .empty rfl

/-- The whole *lock separation context* `peakSepCtx (peaks Γ W) sctx` commutes with a
    context morphism: the peaks naturality (`hcapy.peakset`) feeds the peak-set into
    `peakSepCtx_mapsTo`.  Stated over abstract `Γ1`/`Γ2`/`sctx1`/`sctx2` so the internal
    peaks rewrite matches syntactically; at use sites the contexts are matched up to
    defeq by `exact`. -/
theorem peakSepCtx_peakset_mapsTo {s1 s1' t1 t2 : Sig}
    {Γ1 : CapyCtx s1} {Γ2 : CapyCtx s1'} {sctx1 : SrcCtx s1 t1} {sctx2 : SrcCtx s1' t2}
    {fs : Rename s1 s1'} {ft : Rename t1 t2}
    (hcapy : Γ1.RenamesTo Γ2 fs)
    (hfs : Function.Injective (fs.var (k := .cvar)))
    (hcvar : ∀ c, sctx2.lookupCVar (fs.var c) = ft.var (sctx1.lookupCVar c))
    (hvar : ∀ x, sctx2.lookupVar (fs.var x) = (sctx1.lookupVar x).rename ft)
    (W : CapyCaptureSet s1) :
    peakSepCtx (CapyCaptureSet.peakset Γ2 (W.rename fs)) sctx2
      = (peakSepCtx (CapyCaptureSet.peakset Γ1 W) sctx1).rename ft := by
  rw [hcapy.peakset]
  exact peakSepCtx_mapsTo hfs hcvar hvar _

/-! ### The renaming theorem

Compilation commutes with a context morphism.  Proved by induction on `T` (same
shape as `CapyTy.compile_rename`): the `cap`/`cell`/`tvar` leaves read the `srcCtx`
field equations; the lock cases read `h.capy.peaks`; the recursive cases
re-instantiate at the builder-extended morphisms above. -/
theorem CapyTy.compile_mapsTo {sort : CapyTySort} {s1 s2 : Sig}
    (T : CapyTy sort s1) (ctx1 : CompilerCtx s1 s2) :
    ∀ {s1' s2' : Sig} {ctx2 : CompilerCtx s1' s2'} {fs : Rename s1 s1'} {ft : Rename s2 s2'},
      fs.Injective → ctx1.MapsTo ctx2 fs ft →
      CapyTy.compile (T.rename fs) ctx2 = (CapyTy.compile T ctx1).rename ft := by
  fun_induction CapyTy.compile T ctx1
  case case1 => intro _ _ _ _ _ _ _; simp only [CapyTy.rename, CapyTy.compile, Ty.rename]
  case case2 => intro _ _ _ _ _ _ _; simp only [CapyTy.rename, CapyTy.compile, Ty.rename]
  case case3 => intro _ _ _ _ _ _ _; simp only [CapyTy.rename, CapyTy.compile, Ty.rename]
  case case4 =>
    intro _ _ _ _ _ _ hm
    simp only [CapyTy.rename, CapyTy.compile, Ty.rename,
      CapyCaptureSet.compile_mapsTo hm.cvar hm.var]
  case case5 =>
    intro _ _ _ _ _ _ hm
    simp only [CapyTy.rename, CapyTy.compile, Ty.rename,
      CapyCaptureSet.compile_mapsTo hm.cvar hm.var]
  case case6 =>
    intro _ _ _ _ _ _ hm
    simp only [CapyTy.rename, CapyTy.compile, Ty.rename,
      CapyCaptureSet.compile_mapsTo hm.cvar hm.var]
  case case7 =>
    rename_i ih; intro s1' s2' ctx2 fs ft hinj hm
    simp only [CapyTy.rename, CapyTy.compile, Ty.rename]
    exact congrArg Ty.typ (ih hinj hm)
  case case8 =>
    intro _ _ _ _ _ _ hm
    simp only [CapyTy.rename, CapyTy.compile, Ty.rename, hm.tvar]
  case case9 =>
    rename_i ihDom ihE
    rename_i Tdom csv _ _ _ _ _ _ _ _
    intro s1' s2' ctx2 fs ft hinj hm
    have hmB := hm.weakenTarget.consCVar (cb := .unbound .epsilon) (c := .here)
    have hmDom := (hm.weakenTarget.weakenTarget.consCVar
        (cb := .unbound .epsilon) (c := .there .here)).consVar
        (T := Tdom) (bv := none) (cs := .cvar (.M .epsilon) .here)
    have hmLock := (hm.weakenTarget.weakenTarget.weakenTarget.consCVar
        (cb := .unbound .epsilon) (c := .there (.there .here))).consVar
        (T := Tdom) (bv := some .here) (cs := .cvar (.M .epsilon) (.there .here))
    simp only [CapyCaptureBound.rename] at hmLock
    have hmE := (((hm.weakenTarget (b := placeholderBinding .cvar)).weakenTarget
        (b := placeholderBinding .cvar)).weakenTarget (b := placeholderBinding .var)).consVar
        (T := .top) (bv := some .here) (cs := .cvar (.M .epsilon) (.there .here))
    have hW : (((csv.rename fs).rename (Rename.succ (k := .cvar))).rename (Rename.succ (k := .var))
          ∪ CapyCaptureSet.var (.M .epsilon) (.bound .here) : CapyCaptureSet (s1',C,x))
        = ((((csv.rename (Rename.succ (k := .cvar))).rename (Rename.succ (k := .var)))
          ∪ CapyCaptureSet.var (.M .epsilon) (.bound .here)).rename fs.lift.lift) := by
      simp only [CapyCaptureSet.rename, Var.rename]
      rw [CapyCaptureSet.weaken_rename_comm, CapyCaptureSet.weaken_rename_comm]
      rfl
    have hcore : (Tdom.rename fs.lift).rename (Rename.succ (k := .var))
        = (Tdom.rename (Rename.succ (k := .var))).rename fs.lift.lift :=
      CapyTy.weaken_rename_comm.symm
    have hAdom : (((Tdom.rename fs.lift : CapyTy .capt (s1',C)).rename
          (Rename.succ (k := .var))).refineCaptureSet
          (CapyCaptureSet.var (.M .epsilon) (.bound .here)) : CapyTy .capt (s1',C,x))
        = (((Tdom.rename (Rename.succ (k := .var))).refineCaptureSet
          (CapyCaptureSet.var (.M .epsilon) (.bound .here))).rename fs.lift.lift) := by
      rw [CapyTy.refineCaptureSet_rename, ← hcore]
      rfl
    simp (config := { zetaDelta := true }) only [CapyTy.rename, CapyTy.compile, Ty.rename]
    simp only [hW, hAdom]
    congr 1
    congr 1
    congr 1
    · congr 1
      rw [CapyTy.captureSet_rename]
      exact CapyCaptureSet.compile_mapsTo hmB.cvar hmB.var _
    · congr 1
      congr 1
      · exact ihDom hinj.lift.lift hmDom
      · congr 1
        congr 1
        · exact CapyCaptureSet.compile_mapsTo hmLock.cvar hmLock.var _
        · simp only [ModalCtx.rename, MutabilityCtx.rename]
          congr 1
          exact peakSepCtx_peakset_mapsTo hmLock.capy (hinj.lift.lift .cvar)
            hmLock.cvar hmLock.var _
        · exact ihE hinj.lift hmE
  case case10 =>
    rename_i ihS ihE; intro s1' s2' ctx2 fs ft hinj hm
    simp (config := { zetaDelta := true }) only [CapyTy.rename, CapyTy.compile, Ty.rename]
    congr 1
    · exact ihS hinj hm
    · congr 1
      congr 1
      · exact CapyCaptureSet.compile_mapsTo hm.weakenTarget.cvar hm.weakenTarget.var _
      · simp only [ModalCtx.rename, MutabilityCtx.rename]
        congr 1
        rw [hm.capy.peakset]
        exact peakSepCtx_mapsTo (hinj .cvar) hm.weakenTarget.cvar hm.weakenTarget.var _
      · exact ihE hinj.lift (hm.weakenTarget.consTVar (S := .top) (X := .here))
  case case11 =>
    rename_i ih; intro s1' s2' ctx2 fs ft hinj hm
    simp (config := { zetaDelta := true }) only [CapyTy.rename, CapyTy.compile, Ty.rename]
    congr 1
    · exact CapyCaptureBound.compile_mapsTo hm.cvar hm.var _
    · congr 1
      congr 1
      · exact CapyCaptureSet.compile_mapsTo hm.weakenTarget.cvar hm.weakenTarget.var _
      · simp only [ModalCtx.rename]
        congr 1
        · rw [hm.capy.peakset]
          exact peakSepCtx_mapsTo (hinj .cvar) hm.weakenTarget.cvar hm.weakenTarget.var _
        · exact CapyCaptureBound.mutabilityCtx_mapsTo
      · exact ih hinj.lift (hm.weakenTarget.consCVar (c := .here))
  case case12 =>
    rename_i ih; intro s1' s2' ctx2 fs ft hinj hm
    simp only [CapyTy.rename, CapyTy.compile, Ty.rename]
    exact congrArg Ty.exi
      (ih hinj.lift (hm.weakenTarget.consCVar (cb := .unbound .epsilon) (c := .here)))

end Compilation
