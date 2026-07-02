import Semantic.CoreCapybara.Compilation.ClosedLemmas
open CoreCapybara
namespace Compilation

/-!
# Binding compilation and the context-coherence invariant

This module compiles source bindings (`CapyBinding`) into target bindings, and
develops the `Coherent` invariant relating a compiler context's source typing
context, source→target map, and target Core context.  It underpins the
lookup-transport lemmas that the term-compilation preservation theorem needs.
-/

/-- Compilation of capture sets preserves emptiness. -/
theorem CapyCaptureSet.compile_isEmpty {cs : CapyCaptureSet s1} (h : cs.IsEmpty)
    {ctx : SrcCtx s1 s2} : (CapyCaptureSet.compile cs ctx).IsEmpty := by
  induction h with
  | empty => exact CaptureSet.IsEmpty.empty
  | union _ _ ih1 ih2 => exact CaptureSet.IsEmpty.union ih1 ih2

/-- Compilation preserves purity of types (an empty outer capture set stays
    empty; functions get an empty outer capture set anyway). -/
theorem CapyTy.compile_isPure {T : CapyTy .capt s1} (h : T.IsPureType)
    {ctx : CompilerCtx s1 s2} : (CapyTy.compile T ctx).IsPureType := by
  unfold CapyTy.IsPureType Ty.IsPureType at *
  simp only [CapyTy.captureSet] at h
  cases T with
  | top => simp only [CapyTy.compile, Ty.captureSet]; exact CaptureSet.IsEmpty.empty
  | tvar => simp only [CapyTy.compile, Ty.captureSet]; exact CaptureSet.IsEmpty.empty
  | unit => simp only [CapyTy.compile, Ty.captureSet]; exact CaptureSet.IsEmpty.empty
  | bool => simp only [CapyTy.compile, Ty.captureSet]; exact CaptureSet.IsEmpty.empty
  | cap cs => simp only [CapyTy.compile, Ty.captureSet]; exact CapyCaptureSet.compile_isEmpty h
  | cell cs m =>
    cases m <;> (simp only [CapyTy.compile, Ty.captureSet]; exact CapyCaptureSet.compile_isEmpty h)
  | arrow => simp only [CapyTy.compile, Ty.captureSet]; exact CaptureSet.IsEmpty.empty
  | poly => simp only [CapyTy.compile, Ty.captureSet]; exact CaptureSet.IsEmpty.empty
  | cpoly => simp only [CapyTy.compile, Ty.captureSet]; exact CaptureSet.IsEmpty.empty

/-- Compiles a source pure type into the target. -/
def CapyPureTy.compile (S : CapyPureTy s1) (ctx : CompilerCtx s1 s2) : PureTy s2 :=
  ⟨CapyTy.compile S.core ctx, CapyTy.compile_isPure S.p⟩

/-- Compiles a source authority into the target (identity on the two shared
    cases). -/
def CapyAuthority.compile : CapyAuthority -> Authority
| .can_drop => .can_drop
| .access_only => .access_only

/-- Compiles a source binding into the target binding of the same kind. -/
def CapyBinding.compile : CapyBinding s1 k -> CompilerCtx s1 s2 -> Binding s2 k
| .var T, ctx => .var (CapyTy.compile T ctx)
| .tvar S, ctx => .tvar (CapyPureTy.compile S ctx)
| .cvar a cb, ctx => .cvar (CapyAuthority.compile a) (CapyCaptureBound.compile cb ctx.srcCtx)

/-- The context-coherence invariant: the target Core context `coreCtx` is a
    faithful compilation of the source typing context `capyCtx` along the
    source→target map `srcCtx`.  Concretely, it is closed and every source
    term-variable's image is bound in `coreCtx` at the compiled type.  (Capture-
    and type-variable lookup facts will be added alongside the `capp`/`tapp`
    cases.)  Lookup transport is then a projection out of this structure;
    `CapyTy.compile_rename` is what makes the stored compiled types line up with
    the shifts the lookup judgements apply. -/
structure CompilerCtx.Coherent (ctx : CompilerCtx s1 s2) : Prop where
  closed : ctx.coreCtx.IsClosed
  capyClosed : ctx.capyCtx.IsClosed
  srcClosed : ctx.srcCtx.VarsClosed
  varLookup : ∀ {x : BVar s1 .var} {T : CapyTy .capt s1},
    ctx.capyCtx.LookupVar x T →
    ∃ bv, ctx.srcCtx.lookupVarBVar x = some bv ∧
          -- A source variable's capture IMAGE is EITHER its declared type's
          -- compiled capture set `⟦T.captureSet⟧` — the *latent requirement*, the
          -- shape every `letin`-introduced binder has — OR (a function parameter,
          -- introduced by the `abs` compilation) the singleton `{cx}` of a target
          -- capture variable whose declared bound is that latent.  The second
          -- disjunct is what the `arrow` compiler's re-abstraction (`x ↦ {cx}`,
          -- `cx <: ⟦T.captureSet⟧`) demands of the abs-body context; the first is
          -- what keeps the aligned-context devices (`SrcAligned`, the A1 resource
          -- keystone) available.  Both give `Subcapt image ⟦T.captureSet⟧`.
          (ctx.srcCtx.lookupVar x = CapyCaptureSet.compile T.captureSet ctx.srcCtx ∨
           ∃ cx, ctx.srcCtx.lookupVar x = .cvar (.M .epsilon) cx ∧
             ctx.coreCtx.LookupCVar cx .access_only
               (.bound (CapyCaptureSet.compile T.captureSet ctx.srcCtx))) ∧
          -- The target binder holds the compiled SELF-REFINED type `⟦T^{x}⟧`.
          -- At an aligned binder this is `⟦T⟧` (`CapyTy.compile_refine_self`); at a
          -- re-abstracted parameter it is the compiled arrow DOMAIN (`⟦T⟧` with
          -- outer capture `{cx}`) — exactly what the target `abs` rule binds.
          ctx.coreCtx.LookupVar bv
            (CapyTy.compile (T.refineCaptureSet (.var (.M .epsilon) (.bound x))) ctx)
  -- Capture-variable lookup coherence: a source cvar's image is bound in `coreCtx`
  -- at the compiled authority + capture bound.  Needed by `Subtyp.tvar`/`cpoly`
  -- compilation, droppability transport (`compile_droppable`), and the lock
  -- separation machinery (`sep_droppable` from a source `droppable`).
  cvarLookup : ∀ {c : BVar s1 .cvar} {a : CapyAuthority} {cb : CapyCaptureBound s1},
    ctx.capyCtx.LookupCVar c a cb →
    ctx.coreCtx.LookupCVar (ctx.srcCtx.lookupCVar c)
      (CapyAuthority.compile a) (CapyCaptureBound.compile cb ctx.srcCtx)
  -- Type-variable lookup coherence: a source tvar's image is bound at the compiled
  -- pure type.  Needed by `Subtyp.tvar` compilation.
  tvarLookup : ∀ {X : BVar s1 .tvar} {S : CapyPureTy s1},
    ctx.capyCtx.LookupTVar X S →
    ctx.coreCtx.LookupTVar (ctx.srcCtx.lookupTVar X) (CapyPureTy.compile S ctx)
  /-- Read-only provenance: every source cvar declared `.unbound .ro` has a target
      `HasKind _ _ .ro` witness (in practice via an enclosing lock's `MutabilityCtx`,
      `HasKind.imm` — a compiled `cpoly [c <: unbound ro]` records `({c}, ro)` in its
      body lock, `CapyCaptureBound.mutabilityCtx`).  This is what compiles source
      `CapyHasKind.imm`, whose premise reads `c`'s declared mutability with no
      structural (`applyRO`) witness on the set itself.  Shared verbatim with
      `SubCoherent.roLookup`, so `toSubCoherent` needs no extra argument. -/
  roLookup : ∀ {c : BVar s1 .cvar} {a : CapyAuthority} {cb : CapyCaptureBound s1},
    ctx.capyCtx.LookupCVar c a cb → cb = .unbound .ro →
    HasKind ctx.coreCtx (.cvar (.M .epsilon) (ctx.srcCtx.lookupCVar c)) .ro

end Compilation
