import Semantic.CoreCapybara.Compilation.Coherence
open CoreCapybara
namespace Compilation

/-!
# Type-preserving term compilation

The central theorem of the translation: every well-typed Capybara term compiles
to a well-typed CoreCapybara term.  It is phrased as an existence statement
(`∃ e', HasType …`) proven by induction on the source typing derivation
`CapyHasType`; the witness `e'` is the compiled term, built case by case.

This is a WORK IN PROGRESS scaffold: the trivial cases (`unit`/`btrue`/`bfalse`)
are discharged; the remaining cases are left as `sorry` and filled in
incrementally.  See [[project_capybara_translation]] for the per-case plan and
the one genuine design gap (function-typed-variable refinement).
-/

/-- **Type-preservation of term compilation.**  A well-typed source term, in any
    coherent compiler context whose source typing context matches the
    derivation's, compiles to a well-typed target term at the compiled capture
    set, context, and type. -/
theorem CapyHasType.compile {s1 : Sig} {Cs : CaptureSet s1} {Γ : CapyCtx s1}
    {e : CapyExp s1} {E : CapyTy .exi s1} (hty : CapyHasType Cs Γ e E) :
    ∀ {s2 : Sig} (ctx : CompilerCtx s1 s2), ctx.capyCtx = Γ → ctx.Coherent →
    ∃ e' : Exp s2, HasType (CaptureSet.compile Cs ctx.srcCtx) ctx.coreCtx e'
      (CapyTy.compile E ctx) := by
  induction hty
  case unit =>
    intro s2 ctx hΓ hcoh
    refine ⟨.unit, ?_⟩
    simp only [CaptureSet.compile, CapyTy.compile]
    exact HasType.unit
  case btrue =>
    intro s2 ctx hΓ hcoh
    refine ⟨.btrue, ?_⟩
    simp only [CaptureSet.compile, CapyTy.compile]
    exact HasType.btrue
  case bfalse =>
    intro s2 ctx hΓ hcoh
    refine ⟨.bfalse, ?_⟩
    simp only [CaptureSet.compile, CapyTy.compile]
    exact HasType.bfalse
  -- Remaining cases (var, readonly, fresh, abs, tabs, cabs, app, tapp, capp,
  -- letin, letin_unpack, alloc, drop, read, write, cond, par, invoke, subtyp)
  -- are WIP: discharged incrementally.
  all_goals (intro s2 ctx hΓ hcoh; sorry)

end Compilation
