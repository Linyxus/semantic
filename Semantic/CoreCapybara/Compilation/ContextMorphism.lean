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

/-- Source peak-resolution commutes with a context renaming — the one operational
    consequence the compiled lock needs, *derived* from the morphism (not assumed).
    Generalizes `CapyCaptureSet.peaks_rename_succ_eq` from `succ` to any `f`. -/
theorem CapyCtx.RenamesTo.peaks {s1 s2 : Sig} {Γ1 : CapyCtx s1} {Γ2 : CapyCtx s2}
    {f : Rename s1 s2} (h : Γ1.RenamesTo Γ2 f) {W : CaptureSet s1} :
    CapyCaptureSet.peaks Γ2 (W.rename f) = (CapyCaptureSet.peaks Γ1 W).rename f := by
  sorry

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

/-- Preserved by a fresh target binder: `ft` lifts, `fs` fixed. -/
theorem CompilerCtx.MapsTo.weakenTarget {s1 s1' s2 s2' : Sig}
    {ctx1 : CompilerCtx s1 s2} {ctx2 : CompilerCtx s1' s2'}
    {fs : Rename s1 s1'} {ft : Rename s2 s2'} (h : ctx1.MapsTo ctx2 fs ft)
    (b1 : Binding s2 k := placeholderBinding k) (b2 : Binding s2' k := placeholderBinding k) :
    (ctx1.weakenTarget b1).MapsTo (ctx2.weakenTarget b2) fs ft.lift := by
  sorry

/-- Preserved by a fresh source type binder: `fs` lifts, `ft` fixed. -/
theorem CompilerCtx.MapsTo.consTVar {s1 s1' s2 s2' : Sig}
    {ctx1 : CompilerCtx s1 s2} {ctx2 : CompilerCtx s1' s2'}
    {fs : Rename s1 s1'} {ft : Rename s2 s2'} (h : ctx1.MapsTo ctx2 fs ft)
    {S : CapyPureTy s1} {X : BVar s2 .tvar} :
    (ctx1.consTVar S X).MapsTo (ctx2.consTVar (S.rename fs) (ft.var X)) fs.lift ft := by
  sorry

/-- Preserved by a fresh source capture binder: `fs` lifts, `ft` fixed. -/
theorem CompilerCtx.MapsTo.consCVar {s1 s1' s2 s2' : Sig}
    {ctx1 : CompilerCtx s1 s2} {ctx2 : CompilerCtx s1' s2'}
    {fs : Rename s1 s1'} {ft : Rename s2 s2'} (h : ctx1.MapsTo ctx2 fs ft)
    {cb : CapyCaptureBound s1} {c : BVar s2 .cvar} :
    (ctx1.consCVar cb c).MapsTo (ctx2.consCVar (cb.rename fs) (ft.var c)) fs.lift ft := by
  sorry

/-- Preserved by a fresh source term binder: `fs` lifts, `ft` fixed; the stored
    capture image and optional target var rename by `ft`. -/
theorem CompilerCtx.MapsTo.consVar {s1 s1' s2 s2' : Sig}
    {ctx1 : CompilerCtx s1 s2} {ctx2 : CompilerCtx s1' s2'}
    {fs : Rename s1 s1'} {ft : Rename s2 s2'} (h : ctx1.MapsTo ctx2 fs ft)
    {T : CapyTy .capt s1} {bv : Option (BVar s2 .var)} {cs : CaptureSet s2} :
    (ctx1.consVar T bv cs).MapsTo
      (ctx2.consVar (T.rename fs) (bv.map ft.var) (cs.rename ft)) fs.lift ft := by
  sorry

/-! ### The renaming theorem

Compilation commutes with a context morphism.  Proved by induction on `T` (same
shape as `CapyTy.compile_rename`): the `cap`/`cell`/`tvar` leaves read the `srcCtx`
field equations; the lock cases read `h.capy.peaks`; the recursive cases
re-instantiate at the builder-extended morphisms above. -/
theorem CapyTy.compile_mapsTo {sort : CapyTySort} {s1 : Sig} (T : CapyTy sort s1) :
    ∀ {s1' s2 s2' : Sig} {ctx1 : CompilerCtx s1 s2} {ctx2 : CompilerCtx s1' s2'}
      {fs : Rename s1 s1'} {ft : Rename s2 s2'},
      ctx1.MapsTo ctx2 fs ft →
      CapyTy.compile (T.rename fs) ctx2 = (CapyTy.compile T ctx1).rename ft := by
  sorry

end Compilation
