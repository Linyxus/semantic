import Semantic.CoreCapybara.Compilation.Coherence
import Semantic.CoreCapybara.Compilation.SubstLemmas
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

/-- **A variable refined to its own singleton subtypes its declared type.**  For
    `bv : T'` in the target, `T'` with its top capture set narrowed to `{bv}` is a
    subtype of `T'`.  Holds uniformly: `{bv} <: T'.captureSet` by `sc_var`, lifted
    through each former's covariant capture rule (`arrow`/`poly`/`cpoly`/`modal`
    structural; `cell`/`reader`/`cap` via the dedicated covariance rules). -/
theorem Subtyp.self_refine {s : Sig} {Γ : Ctx s} {bv : BVar s .var} {T' : Ty .capt s}
    (h : Γ.LookupVar bv T') :
    Subtyp Γ (T'.refineCaptureSet (.var (.M .epsilon) (.bound bv))) T' := by
  have hsc : Subcapt Γ (.var (.M .epsilon) (.bound bv)) T'.captureSet := Subcapt.sc_var h
  cases T' with
  | top => exact Subtyp.refl
  | tvar X => exact Subtyp.refl
  | unit => exact Subtyp.refl
  | bool => exact Subtyp.refl
  | cap cs => exact Subtyp.cap hsc
  | cell cs => exact Subtyp.cell hsc
  | reader cs => exact Subtyp.reader hsc
  | arrow A cs B => exact Subtyp.arrow Subtyp.refl hsc Subtyp.refl
  | poly S cs B => exact Subtyp.poly_cap hsc
  | cpoly cb cs B =>
    refine Subtyp.cpoly ?_ hsc Subtyp.refl
    cases cb with
    | unbound => exact Subbound.top
    | bound C => exact Subbound.capset (Subcapt.sc_elem CaptureSet.Subset.refl)
  | modal cs Ψ E => exact Subtyp.modal hsc Subtyp.refl

/-- **Self-capture refinement vanishes under compilation.**

    With the `Coherent` invariant `⟦xv⟧ = ⟦T.captureSet⟧`, the var rule's refined
    type `T^{xv}` compiles to *exactly* `⟦T⟧`: the refined capture field `{xv}`
    compiles back to `⟦T.captureSet⟧`, the value it replaced.  For functions this
    keeps the body lock faithful (the latent requirement `⟦cs⟧`, never understated)
    — which is what dissolves the old function-typed-variable design gap.

    The `arrow`/`poly`/`cpoly` cases additionally need the compiled lock `W` and
    its separation context `Ψ` to coincide between `{xv}` and `cs`; both follow
    from `compile`/`peaks` commuting with the capture image (the latter from
    `peaks Γ {xv} = peaks Γ T.captureSet`).  This is now a MECHANICAL commutation
    — the design gap is resolved — left as a scoped TODO. -/
theorem CapyTy.compile_refine_self {s1 s2 : Sig} {T : CapyTy .capt s1}
    {ctx : CompilerCtx s1 s2} {xv : BVar s1 .var}
    (hsrc : ctx.srcCtx.lookupVar xv = CaptureSet.compile T.captureSet ctx.srcCtx)
    (hcapy : ctx.capyCtx.LookupVar xv T) :
    CapyTy.compile (T.refineCaptureSet (.var (.M .epsilon) (.bound xv))) ctx
      = CapyTy.compile T ctx := by
  -- the var's capture image `⟦{xv}⟧` is its declared latent `⟦T.captureSet⟧`
  have hxv : CaptureSet.compile (.var (.M .epsilon) (.bound xv)) ctx.srcCtx
      = CaptureSet.compile T.captureSet ctx.srcCtx := by
    simp only [CaptureSet.compile, hsrc, CaptureSet.applyAccess_M, CaptureSet.applyMut_epsilon]
  -- `peaks {xv} = peaks T.captureSet` (faithful separation context)
  have hpk : CapyCaptureSet.peakset ctx.capyCtx (.var (.M .epsilon) (.bound xv))
      = CapyCaptureSet.peakset ctx.capyCtx T.captureSet := by
    apply CapyCaptureSet.peakset_congr
    rw [CapyCaptureSet.peaks, CapyCaptureSet.peaksVarBound_eq_captureSet hcapy]
  cases T with
  | top => simp only [CapyTy.refineCaptureSet]
  | tvar X => simp only [CapyTy.refineCaptureSet]
  | unit => simp only [CapyTy.refineCaptureSet]
  | bool => simp only [CapyTy.refineCaptureSet]
  | cap cs =>
    simp only [CapyTy.captureSet] at hxv
    simp only [CapyTy.refineCaptureSet, CapyTy.compile, hxv]
  | cell cs m =>
    simp only [CapyTy.captureSet] at hxv
    cases m <;> simp only [CapyTy.refineCaptureSet, CapyTy.compile, hxv]
  | poly S cs E =>
    simp only [CapyTy.captureSet] at hxv hpk
    have hCf : CaptureSet.compile (.var (.M .epsilon) (.bound xv))
          (SrcCtx.weaken (k := Kind.tvar) ctx.srcCtx)
        = CaptureSet.compile cs (SrcCtx.weaken (k := Kind.tvar) ctx.srcCtx) := by
      unfold SrcCtx.weaken
      rw [CaptureSet.compile_rename, CaptureSet.compile_rename, hxv]
    -- only the modal lock `W` and (via `hpk`) the separation `Ψ` differ; `congr`
    -- discharges the residual lock equality with `hCf` from context.
    simp only [CapyTy.refineCaptureSet, CapyTy.compile, hpk]
    repeat' congr 1
  | cpoly cb cs E =>
    simp only [CapyTy.captureSet] at hxv hpk
    have hCf : CaptureSet.compile (.var (.M .epsilon) (.bound xv))
          (SrcCtx.weaken (k := Kind.cvar) ctx.srcCtx)
        = CaptureSet.compile cs (SrcCtx.weaken (k := Kind.cvar) ctx.srcCtx) := by
      unfold SrcCtx.weaken
      rw [CaptureSet.compile_rename, CaptureSet.compile_rename, hxv]
    -- only the modal lock `W` and (via `hpk`) the separation `Ψ` differ; `congr`
    -- discharges the residual lock equality with `hCf` from context.
    simp only [CapyTy.refineCaptureSet, CapyTy.compile, hpk]
    repeat' congr 1
  | arrow T1 cs E =>
    simp only [CapyTy.captureSet] at hxv hpk
    simp only [CapyTy.refineCaptureSet, CapyTy.compile]
    set ctxL := (ctx.weakenTarget.weakenTarget.weakenTarget.consCVar (.unbound .epsilon)
      (.there (.there .here))).consVar T1 (some .here)
      (.cvar (.M .epsilon) (.there .here)) with hctxL
    -- the modal lock `W` agrees between `{xv}` and `cs`.  The two source
    -- weakenings of the lock field peel through the lock's `var`/`cvar` `cons`es
    -- via `compile_lock_field_congr`; its hypothesis is `hxv` transported under
    -- the three target weakenings (`compile_rename` ×3).
    have hCfW : CaptureSet.compile
          (((CaptureSet.var (.M .epsilon) (.bound xv)).rename Rename.succ).rename Rename.succ
            ∪ .var (.M .epsilon) (.bound .here)) ctxL.srcCtx
        = CaptureSet.compile ((cs.rename Rename.succ).rename Rename.succ
            ∪ .var (.M .epsilon) (.bound .here)) ctxL.srcCtx := by
      rw [hctxL]
      simp only [CompilerCtx.consVar_srcCtx, CompilerCtx.consCVar_srcCtx,
        CompilerCtx.weakenTarget_srcCtx]
      apply CaptureSet.compile_lock_field_congr
      simp only [CaptureSet.compile_rename, hxv]
    -- the lock's separation context `Ψ` agrees between `{xv}` and `cs`.  Mirror of
    -- `hCfW` for `peaks`: project the underlying `peaks` equality off `hpk`, then
    -- peel the two `peaks`-weakenings via `peaks_lock_field_congr`.
    have hpk' : CapyCaptureSet.peaks ctx.capyCtx (.var (.M .epsilon) (.bound xv))
        = CapyCaptureSet.peaks ctx.capyCtx cs := congrArg PeakSet.cs hpk
    have hpkW : CapyCaptureSet.peakset ctxL.capyCtx
          (((CaptureSet.var (.M .epsilon) (.bound xv)).rename Rename.succ).rename Rename.succ
            ∪ .var (.M .epsilon) (.bound .here))
        = CapyCaptureSet.peakset ctxL.capyCtx ((cs.rename Rename.succ).rename Rename.succ
            ∪ .var (.M .epsilon) (.bound .here)) := by
      apply CapyCaptureSet.peakset_congr
      rw [hctxL]
      simp only [CompilerCtx.consVar_capyCtx, CompilerCtx.consCVar_capyCtx,
        CompilerCtx.weakenTarget_capyCtx]
      exact CapyCaptureSet.peaks_lock_field_congr hpk'
    repeat' congr 1


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
  case var =>
    intro s2 ctx hΓ hcoh
    rename_i xv Γv Tv hclosed hlook
    obtain ⟨bv, _, hsrcvar, hcorelk⟩ := hcoh.varLookup (hΓ ▸ hlook)
    refine ⟨.var (.bound bv), ?_⟩
    have hTvclosed : Tv.IsClosed := CapyCtx.lookupVar_isClosed (hΓ ▸ hlook) (hΓ ▸ hclosed)
    have hbase : HasType {} ctx.coreCtx (.var (.bound bv))
        (.typ ((CapyTy.compile Tv ctx).refineCaptureSet (.var (.M .epsilon) (.bound bv)))) :=
      HasType.var hcoh.closed hcorelk
    -- the var's compiled capture is its declared latent `⟦Tv.captureSet⟧`
    have hcs : CaptureSet.compile (.var (.M .epsilon) (.bound xv)) ctx.srcCtx
        = CaptureSet.compile Tv.captureSet ctx.srcCtx := by
      simp only [CaptureSet.compile, hsrcvar, CaptureSet.applyAccess_M, CaptureSet.applyMut_epsilon]
    rw [hcs]
    -- the refinement vanishes: `⟦E⟧ = .typ ⟦Tv⟧`
    simp only [CapyTy.compile]
    rw [CapyTy.compile_refine_self hsrcvar (hΓ ▸ hlook)]
    exact HasType.subtyp hbase (Subcapt.sc_elem CaptureSet.Subset.empty)
      (Subtyp.typ (Subtyp.self_refine hcorelk))
      (CaptureSet.compile_isClosed (CapyTy.IsClosed.captureSet hTvclosed) hcoh.srcClosed)
      (Ty.IsClosed.typ (CapyTy.compile_isClosed _ _ hTvclosed hcoh.srcClosed))
  case readonly =>
    intro s2 ctx hΓ hcoh
    rename_i xv Γv Cc hclosed hlook
    obtain ⟨bv, _, hsrcvar, hcorelk⟩ := hcoh.varLookup (hΓ ▸ hlook)
    simp only [CapyTy.captureSet] at hsrcvar
    simp only [CapyTy.compile] at hcorelk
    refine ⟨.reader (.bound bv), ?_⟩
    have hCcclosed : Cc.IsClosed := by
      have h := CapyCtx.lookupVar_isClosed (hΓ ▸ hlook) (hΓ ▸ hclosed)
      cases h with | cell h => exact h
    have hbase : HasType {} ctx.coreCtx (.reader (.bound bv))
        (.typ (.reader (.var (.M .ro) (.bound bv)))) := HasType.reader hcoh.closed hcorelk
    have hcsclosed : (CaptureSet.compile Cc ctx.srcCtx).applyRO.IsClosed :=
      CaptureSet.applyRO_isClosed (CaptureSet.compile_isClosed hCcclosed hcoh.srcClosed)
    -- the readonly view's compiled capture is `(⟦Cc⟧).applyRO`
    have hcs : CaptureSet.compile (.var (.M .ro) (.bound xv)) ctx.srcCtx
        = (CaptureSet.compile Cc ctx.srcCtx).applyRO := by
      simp only [CaptureSet.compile, hsrcvar, CaptureSet.applyAccess_M, CaptureSet.applyMut_ro]
    have hEtype : CapyTy.compile (CapyTy.cell (.var (.M .ro) (.bound xv)) .ro).typ ctx
        = .typ (.reader ((CaptureSet.compile Cc ctx.srcCtx).applyRO)) := by
      simp only [CapyTy.compile, hcs]
    rw [hcs, hEtype]
    refine HasType.subtyp hbase (Subcapt.sc_elem CaptureSet.Subset.empty)
      (Subtyp.typ (Subtyp.reader (Subcapt.sc_ro_mono (Subcapt.sc_var hcorelk))))
      hcsclosed (Ty.IsClosed.typ (Ty.IsClosed.reader hcsclosed))
  case fresh =>
    intro s2 ctx hΓ hcoh
    -- **DESIGN GAP RESOLVED — `fresh` ↦ `let v = ⟦premise⟧ in pack ⟦D⟧ v`.**
    --
    -- The earlier obstruction ("`pack` needs a *syntactic variable* typed at `{}`,
    -- but the IH delivers an opaque `∃ e'` at `⟦C⟧`, and a read-only-cell var
    -- compiles to a non-variable `.reader`") is dissolved by an MNF **let-binding**:
    -- the compiler may emit target glue, so `fresh` compiles to
    --   `letin ⟦premise⟧ (pack (⟦D⟧.rename succ) (.bound .here))`.
    -- The let-bound `v` is a genuine variable (handles the opaque/`.reader` witness),
    -- re-derived at capture `{}` by the target `var` rule (handles the `{}` demand),
    -- and `pack`'s body type lines up with `v`'s via the now-proven capture-opening
    -- commutation (`CaptureSet.compile_subst_openCVar`) lifted to types, plus
    -- `Subtyp.self_refine` for the var rule's refinement.  This is NOT a design gap.
    --
    -- The opening does NOT commute as a syntactic equality at the function lock, but
    -- it commutes up to **subtyping**, which is all `pack` needs:
    --     `⟦T[D/c]⟧  <:  ⟦T⟧[⟦D⟧/c]`.
    -- A compiled function lock is `peakSepCtx (peakset Γ W) …`, one separation item
    -- per distinct peak cvar.  Opening `c ↦ D` makes the let-bound `v`'s type
    -- `⟦T[D/c]⟧` re-group by `D`'s peaks (more items ⇒ demands `D`'s peaks pairwise
    -- separate), whereas `pack`'s required body `⟦T⟧[⟦D⟧/c]` keeps `c`'s single item
    -- (merged ⇒ demands nothing).  A lock is *contravariant* in its demand, so the
    -- more-demanding (separated) modal is a SUBTYPE of the less-demanding (merged)
    -- one — `Subtyp.modal_modal` requires `Satisfy (Γ.push_lock Ψmerged) Ψsep`, i.e.
    -- proving `D`'s peaks pairwise-separate in `Γ`, which is EXACTLY what the rule's
    -- `droppable Γ D` premise delivers (distinct droppable peaks ⇒ `sep_droppable`).
    -- So `v` subsumes to `pack`'s argument type.  Foundations PROVEN
    -- (`compile_subst_openCVar`, (★) `compile_peaks`); the remaining work is the
    -- type-level subtyping lift of these + the `letin` glue.  [[project_capybara_translation]]
    sorry
  -- Remaining cases (abs, tabs, cabs, app, tapp, capp,
  -- letin, letin_unpack, alloc, drop, read, write, cond, par, invoke, subtyp)
  -- are WIP: discharged incrementally.
  all_goals (intro s2 ctx hΓ hcoh; sorry)

end Compilation
