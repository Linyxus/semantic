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
theorem CaptureSet.compile_isEmpty {cs : CaptureSet s1} (h : cs.IsEmpty)
    {ctx : SrcCtx s1 s2} : (CaptureSet.compile cs ctx).IsEmpty := by
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
  | cap cs => simp only [CapyTy.compile, Ty.captureSet]; exact CaptureSet.compile_isEmpty h
  | cell cs m =>
    cases m <;> (simp only [CapyTy.compile, Ty.captureSet]; exact CaptureSet.compile_isEmpty h)
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
  srcClosed : ctx.srcCtx.VarsClosed
  varLookup : ∀ {x : BVar s1 .var} {T : CapyTy .capt s1},
    ctx.capyCtx.LookupVar x T →
    ∃ bv, ctx.srcCtx.lookupVarBVar x = some bv ∧
          -- A source variable's capture IMAGE is its declared type's compiled
          -- capture set `⟦T.captureSet⟧` — the function's *latent requirement* —
          -- NOT the singleton `{bv}`.  This keeps the compiled lock faithful, so
          -- the var rule's self-capture refinement vanishes under compilation
          -- (see `Subtyp.self_refine`).  The target variable `bv` is used only for
          -- the compiled *expression* `.var bv`.
          ctx.srcCtx.lookupVar x = CaptureSet.compile T.captureSet ctx.srcCtx ∧
          ctx.coreCtx.LookupVar bv (CapyTy.compile T ctx)

end Compilation
