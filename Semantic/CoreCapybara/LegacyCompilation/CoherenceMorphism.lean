import Semantic.CoreCapybara.LegacyCompilation.Coherence
import Semantic.CoreCapybara.LegacyCompilation.ContextMorphism
import Semantic.CoreCapybara.LegacyCompilation.SubstLemmas
import Semantic.CoreCapybara.LegacyCompilation.LockKernel

/-!
# Coherence preservation under the context builders

The term-compilation preservation proof threads the context-coherence invariant
`CompilerCtx.Coherent` through every binder it descends under.  This module proves
that each compiler-context builder preserves `Coherent`:

* `Coherent.weakenTarget` — a fresh *target* Core binder (`coreCtx` grows by a
  closed binding); the stored compiled types realign by `CapyTy.compile_rename`
  (target weakening).
* `Coherent.consTVar`/`consCVar`/`consVar` — a fresh *source* binder; the *old*
  lookups realign by `CapyTy.compile_mapsTo` at the source-weakening morphism
  `fs = succ`, `ft = id` (the keystone P delivered), and the *new* `.here` lookup
  is supplied as a hypothesis (the freshly bound target image).

The source-weakening morphisms `ctx ⟶ ctx.cons* …` over `(succ, id)` are the
asymmetric "left-unit" extensions that the symmetric P2 builders do not give, so
they are built directly here.
-/

open CoreCapybara

namespace CoreCapybara

/-- The reflexive (identity) context renaming. -/
theorem Ctx.RenamesTo.refl {s : Sig} {Γ : Ctx s} : Γ.RenamesTo Γ Rename.id where
  var hl := by rw [Ty.rename_id]; exact hl
  cvar hl := by rw [CaptureBound.rename_id]; exact hl
  tvar hl := by rw [PureTy.rename_id]; exact hl
  lock hl := by rw [ModalCtx.rename_id]; exact hl

/-- A source typing context renames into its own one-binder extension by the
    weakening `succ` (the `.there` lookups). -/
theorem CapyCtx.RenamesTo.weaken {s : Sig} {k : Kind} {Γ : CapyCtx s}
    (b : CapyBinding s k) : Γ.RenamesTo (Γ.push b) Rename.succ where
  var hl := CapyCtx.LookupVar.there hl
  cvar hl := CapyCtx.LookupCVar.there hl
  tvar hl := CapyCtx.LookupTVar.there hl

end CoreCapybara

open CoreCapybara
namespace Compilation

/-! ### Source-weakening morphisms (`ctx ⟶ ctx.cons* …` over `(succ, id)`)

The `srcCtx` field equations all peel a `.there` lookup against the fresh `cons`,
leaving the tail lookup; `ft = id` contributes a `rename id`/`map id` that the
identity lemmas erase. -/

theorem CompilerCtx.MapsTo.consCVar_weaken {s1 s2 : Sig} {ctx : CompilerCtx s1 s2}
    {cb : CapyCaptureBound s1} {c : BVar s2 .cvar} :
    ctx.MapsTo (ctx.consCVar cb c) Rename.succ Rename.id where
  capy := by
    simp only [CompilerCtx.consCVar_capyCtx, CapyCtx.push_cvar_default, CapyCtx.push_cvar]
    exact CapyCtx.RenamesTo.weaken (.cvar .access_only cb)
  core := Ctx.RenamesTo.refl
  cvar c0 := rfl
  var x := by rw [CaptureSet.rename_id]; rfl
  varBVar x := by simp [Rename.id]; rfl
  tvar X := rfl

theorem CompilerCtx.MapsTo.consVar_weaken {s1 s2 : Sig} {ctx : CompilerCtx s1 s2}
    {T : CapyTy .capt s1} {bv : Option (BVar s2 .var)} {cs : CaptureSet s2} :
    ctx.MapsTo (ctx.consVar T bv cs) Rename.succ Rename.id where
  capy := by
    simp only [CompilerCtx.consVar_capyCtx, CapyCtx.push_var]
    exact CapyCtx.RenamesTo.weaken (.var T)
  core := Ctx.RenamesTo.refl
  cvar c0 := rfl
  var x := by rw [CaptureSet.rename_id]; rfl
  varBVar x := by simp [Rename.id]; rfl
  tvar X := rfl

theorem CompilerCtx.MapsTo.consTVar_weaken {s1 s2 : Sig} {ctx : CompilerCtx s1 s2}
    {S : CapyPureTy s1} {X : BVar s2 .tvar} :
    ctx.MapsTo (ctx.consTVar S X) Rename.succ Rename.id where
  capy := by
    simp only [CompilerCtx.consTVar_capyCtx, CapyCtx.push_tvar]
    exact CapyCtx.RenamesTo.weaken (.tvar S)
  core := Ctx.RenamesTo.refl
  cvar c0 := rfl
  var x := by rw [CaptureSet.rename_id]; rfl
  varBVar x := by simp [Rename.id]; rfl
  tvar X0 := rfl

/-! ### Payload realignment helpers

A capture bound / pure type weakened by a fresh *source* binder peels against the
matching `cons` (capture bounds directly; pure types reduce to `CapyTy`). -/

theorem CapyCaptureBound.compile_rename_succ_cons {s1 s2 : Sig} {cb : CapyCaptureBound s1}
    {rest : SrcCtx s1 s2} {info : SrcBinderInfo k s2} :
    CapyCaptureBound.compile (cb.rename (Rename.succ (k := k))) (.cons info rest)
      = CapyCaptureBound.compile cb rest := by
  cases cb with
  | unbound m => rfl
  | bound cs =>
    simp only [CapyCaptureBound.rename, CapyCaptureBound.compile,
      CapyCaptureSet.compile_rename_succ_cons]

/-- A pure type's compilation commutes with target renaming (reduces to `CapyTy`). -/
theorem CapyPureTy.compile_rename {s1 s2 s2' : Sig} {S : CapyPureTy s1}
    {ctx : CompilerCtx s1 s2} {ctx' : CompilerCtx s1 s2'} {ρ : Rename s2 s2'}
    (hcapy : ctx'.capyCtx = ctx.capyCtx) (hsrc : ctx'.srcCtx = ctx.srcCtx.rename ρ) :
    CapyPureTy.compile S ctx' = (CapyPureTy.compile S ctx).rename ρ := by
  simp only [CapyPureTy.compile, PureTy.rename]
  congr 1
  exact CapyTy.compile_rename S.core ctx ctx' ρ hcapy hsrc

/-- A pure type's compilation commutes with a context morphism (reduces to `CapyTy`). -/
theorem CapyPureTy.compile_mapsTo {s1 s2 s1' s2' : Sig} {S : CapyPureTy s1}
    {ctx1 : CompilerCtx s1 s2} {ctx2 : CompilerCtx s1' s2'}
    {fs : Rename s1 s1'} {ft : Rename s2 s2'}
    (hinj : fs.Injective) (hm : ctx1.MapsTo ctx2 fs ft) :
    CapyPureTy.compile (S.rename fs) ctx2 = (CapyPureTy.compile S ctx1).rename ft := by
  simp only [CapyPureTy.compile, CapyPureTy.rename, PureTy.rename]
  congr 1
  exact CapyTy.compile_mapsTo S.core ctx1 hinj hm

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
    (hsrc : ctx.srcCtx.lookupVar xv = CapyCaptureSet.compile T.captureSet ctx.srcCtx)
    (hcapy : ctx.capyCtx.LookupVar xv T) :
    CapyTy.compile (T.refineCaptureSet (.var (.M .epsilon) (.bound xv))) ctx
      = CapyTy.compile T ctx := by
  -- the var's capture image `⟦{xv}⟧` is its declared latent `⟦T.captureSet⟧`
  have hxv : CapyCaptureSet.compile (.var (.M .epsilon) (.bound xv)) ctx.srcCtx
      = CapyCaptureSet.compile T.captureSet ctx.srcCtx := by
    simp only [CapyCaptureSet.compile, hsrc, CaptureSet.applyAccess_M, CaptureSet.applyMut_epsilon]
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
    have hCf : CapyCaptureSet.compile (.var (.M .epsilon) (.bound xv))
          (SrcCtx.weaken (k := Kind.tvar) ctx.srcCtx)
        = CapyCaptureSet.compile cs (SrcCtx.weaken (k := Kind.tvar) ctx.srcCtx) := by
      unfold SrcCtx.weaken
      rw [CapyCaptureSet.compile_rename, CapyCaptureSet.compile_rename, hxv]
    -- only the modal lock `W` and (via `hpk`) the separation `Ψ` differ; `congr`
    -- discharges the residual lock equality with `hCf` from context.
    simp only [CapyTy.refineCaptureSet, CapyTy.compile, hpk]
    repeat' congr 1
  | cpoly cb cs E =>
    simp only [CapyTy.captureSet] at hxv hpk
    have hCf : CapyCaptureSet.compile (.var (.M .epsilon) (.bound xv))
          (SrcCtx.weaken (k := Kind.cvar) ctx.srcCtx)
        = CapyCaptureSet.compile cs (SrcCtx.weaken (k := Kind.cvar) ctx.srcCtx) := by
      unfold SrcCtx.weaken
      rw [CapyCaptureSet.compile_rename, CapyCaptureSet.compile_rename, hxv]
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
    have hCfW : CapyCaptureSet.compile
          (((CapyCaptureSet.var (.M .epsilon) (.bound xv)).rename Rename.succ).rename Rename.succ
            ∪ .var (.M .epsilon) (.bound .here)) ctxL.srcCtx
        = CapyCaptureSet.compile ((cs.rename Rename.succ).rename Rename.succ
            ∪ .var (.M .epsilon) (.bound .here)) ctxL.srcCtx := by
      rw [hctxL]
      simp only [CompilerCtx.consVar_srcCtx, CompilerCtx.consCVar_srcCtx,
        CompilerCtx.weakenTarget_srcCtx]
      apply CapyCaptureSet.compile_lock_field_congr
      simp only [CapyCaptureSet.compile_rename, hxv]
    -- the lock's separation context `Ψ` agrees between `{xv}` and `cs`.  Mirror of
    -- `hCfW` for `peaks`: project the underlying `peaks` equality off `hpk`, then
    -- peel the two `peaks`-weakenings via `peaks_lock_field_congr`.
    have hpk' : CapyCaptureSet.peaks ctx.capyCtx (.var (.M .epsilon) (.bound xv))
        = CapyCaptureSet.peaks ctx.capyCtx cs := congrArg CapyPeakSet.cs hpk
    have hpkW : CapyCaptureSet.peakset ctxL.capyCtx
          (((CapyCaptureSet.var (.M .epsilon) (.bound xv)).rename Rename.succ).rename Rename.succ
            ∪ .var (.M .epsilon) (.bound .here))
        = CapyCaptureSet.peakset ctxL.capyCtx ((cs.rename Rename.succ).rename Rename.succ
            ∪ .var (.M .epsilon) (.bound .here)) := by
      apply CapyCaptureSet.peakset_congr
      rw [hctxL]
      simp only [CompilerCtx.consVar_capyCtx, CompilerCtx.consCVar_capyCtx,
        CompilerCtx.weakenTarget_capyCtx]
      exact CapyCaptureSet.peaks_lock_field_congr hpk'
    repeat' congr 1


/-! ### `Coherent` builder-preservation (K2) -/

/-- A fresh *target* Core binder preserves coherence: the stored compiled types
    realign by `CapyTy.compile_rename` (target weakening), and the lookups shift by
    one Core binder.  `b` must be closed (the Core context stays closed). -/
theorem CompilerCtx.Coherent.weakenTarget {s1 s2 : Sig} {ctx : CompilerCtx s1 s2}
    {k : Kind} {b : Binding s2 k} (hcoh : ctx.Coherent) (hb : b.IsClosed) :
    (ctx.weakenTarget b).Coherent where
  closed := hcoh.closed.push hb
  capyClosed := hcoh.capyClosed
  srcClosed := CompilerCtx.weakenTarget_VarsClosed hcoh.srcClosed
  varLookup := by
    intro x T hl
    obtain ⟨bv0, hbv0, himg0, hcore0⟩ := hcoh.varLookup hl
    refine ⟨Rename.succ.var bv0, ?_, ?_, ?_⟩
    · simp only [CompilerCtx.weakenTarget_srcCtx,
        SrcCtx.lookupVarBVar_rename, hbv0, Option.map_some]
    · cases himg0 with
      | inl h =>
        left
        simp only [CompilerCtx.weakenTarget_srcCtx,
          SrcCtx.lookupVar_rename, h, CapyCaptureSet.compile_rename]
      | inr h =>
        obtain ⟨cx, hlv, hcx⟩ := h
        right
        refine ⟨Rename.succ.var cx, ?_, ?_⟩
        · simp only [CompilerCtx.weakenTarget_srcCtx, SrcCtx.lookupVar_rename, hlv,
            CaptureSet.rename]
        · have h2 := Ctx.LookupCVar.there (b := b) hcx
          simp only [CaptureBound.rename] at h2
          simp only [CompilerCtx.weakenTarget_srcCtx, CapyCaptureSet.compile_rename]
          exact h2
    · rw [CapyTy.compile_rename (T.refineCaptureSet (.var (.M .epsilon) (.bound x)))
        ctx (ctx.weakenTarget b) Rename.succ rfl rfl]
      exact Ctx.LookupVar.there hcore0
  cvarLookup := by
    intro c0 a cb0 hl
    have h := hcoh.cvarLookup hl
    simp only [CompilerCtx.weakenTarget_srcCtx, SrcCtx.lookupCVar_rename]
    rw [CapyCaptureBound.compile_rename]
    exact Ctx.LookupCVar.there h
  tvarLookup := by
    intro X S hl
    have h := hcoh.tvarLookup hl
    simp only [CompilerCtx.weakenTarget_srcCtx, SrcCtx.lookupTVar_rename]
    rw [CapyPureTy.compile_rename (ctx := ctx) (ctx' := ctx.weakenTarget b) (ρ := Rename.succ)
      rfl rfl]
    exact Ctx.LookupTVar.there h
  roLookup := by
    intro c0 a0 cb0 hl heq
    have h := hcoh.roLookup hl heq
    simp only [CompilerCtx.weakenTarget_srcCtx, SrcCtx.lookupCVar_rename]
    exact HasKind.weaken h b


/-! ### Source-weakening payload realignment (`ft = id`)

The old lookups of a `cons*`-extended context realign by `compile_mapsTo` at the
source-weakening morphism, whose `ft = id` leaves a `rename id` that the identity
lemma erases.  Stated in *compiler-context* form (`ctx2.srcCtx`, not the unfolded
`cons`) so they match the goal without re-introducing the `extend`/`extend_cvar`
representation gap, and with implicit payloads so `rw` infers them. -/

/-- A type's compilation is invariant under a source-weakening morphism (`ft = id`). -/
theorem CapyTy.compile_weaken_eq {sort : CapyTySort} {s1 s2 : Sig} {k : Kind}
    {T : CapyTy sort s1} {ctx : CompilerCtx s1 s2} {ctx2 : CompilerCtx (s1,,k) s2}
    (hm : ctx.MapsTo ctx2 (Rename.succ (k := k)) Rename.id) :
    CapyTy.compile (T.rename (Rename.succ (k := k))) ctx2 = CapyTy.compile T ctx := by
  rw [CapyTy.compile_mapsTo T ctx Rename.injective_succ hm, Ty.rename_id]

/-- A pure type's compilation is invariant under a source-weakening morphism. -/
theorem CapyPureTy.compile_weaken_eq {s1 s2 : Sig} {k : Kind}
    {S : CapyPureTy s1} {ctx : CompilerCtx s1 s2} {ctx2 : CompilerCtx (s1,,k) s2}
    (hm : ctx.MapsTo ctx2 (Rename.succ (k := k)) Rename.id) :
    CapyPureTy.compile (S.rename (Rename.succ (k := k))) ctx2 = CapyPureTy.compile S ctx := by
  rw [CapyPureTy.compile_mapsTo Rename.injective_succ hm, PureTy.rename_id]

/-- A capture bound's compilation is invariant under a source-weakening morphism. -/
theorem CapyCaptureBound.compile_weaken_eq {s1 s2 : Sig} {k : Kind}
    {cb : CapyCaptureBound s1} {ctx : CompilerCtx s1 s2} {ctx2 : CompilerCtx (s1,,k) s2}
    (hm : ctx.MapsTo ctx2 (Rename.succ (k := k)) Rename.id) :
    CapyCaptureBound.compile (cb.rename (Rename.succ (k := k))) ctx2.srcCtx
      = CapyCaptureBound.compile cb ctx.srcCtx := by
  rw [CapyCaptureBound.compile_mapsTo hm.cvar hm.var, CaptureBound.rename_id]

/-- A type's *capture set* compilation peels under a source-weakening morphism. -/
theorem CapyCaptureSet.compile_captureSet_weaken_eq {s1 s2 : Sig} {k : Kind} {T : CapyTy .capt s1}
    {ctx : CompilerCtx s1 s2} {ctx2 : CompilerCtx (s1,,k) s2}
    (hm : ctx.MapsTo ctx2 (Rename.succ (k := k)) Rename.id) :
    CapyCaptureSet.compile (T.rename (Rename.succ (k := k))).captureSet ctx2.srcCtx
      = CapyCaptureSet.compile T.captureSet ctx.srcCtx := by
  rw [CapyTy.captureSet_rename, CapyCaptureSet.compile_mapsTo hm.cvar hm.var, CaptureSet.rename_id]

/-- The coherence invariant's self-refined-binding payload realigns under a
    source-weakening morphism: refinement commutes with the weakening rename
    (`refineCaptureSet_rename`), whose compile then peels (`compile_weaken_eq`). -/
theorem CapyTy.compile_refine_weaken_eq {s1 s2 : Sig} {k : Kind}
    {T : CapyTy .capt s1} {x : BVar s1 .var}
    {ctx : CompilerCtx s1 s2} {ctx2 : CompilerCtx (s1,,k) s2}
    (hm : ctx.MapsTo ctx2 (Rename.succ (k := k)) Rename.id) :
    CapyTy.compile ((T.rename (Rename.succ (k := k))).refineCaptureSet
        (.var (.M .epsilon) (.bound (.there x)))) ctx2
      = CapyTy.compile (T.refineCaptureSet (.var (.M .epsilon) (.bound x))) ctx := by
  have h : ((T.refineCaptureSet (.var (.M .epsilon) (.bound x))).rename
        (Rename.succ (k := k)))
      = (T.rename (Rename.succ (k := k))).refineCaptureSet
          (.var (.M .epsilon) (.bound (.there x))) :=
    CapyTy.refineCaptureSet_rename
  rw [← h]
  exact CapyTy.compile_weaken_eq hm

/-! ### `Coherent` builder-preservation under source binders

`cases hl` unfolds the source `push_cvar_default`/`push_var`/`push_tvar` to the
general `push` (`,,k`), so the looked-up payload lands in the `extend` rep while the
builder context keeps the `extend_cvar`/`_var`/`_tvar` rep — defeq but syntactically
distinct.  We therefore realign the *clean* (rename-free) hypothesis side with the
weaken lemmas and discharge by `exact`, whose defeq check bridges the rep gap. -/

/-- A fresh *source* capture binder `c <: cb` preserves coherence; the new `.here`
    capture lookup is supplied by `hlk`.  `hro` is the read-only provenance for the
    NEW binder: vacuous unless `cb = .unbound .ro`, in which case the caller must
    exhibit a target `HasKind {c} .ro` witness (at the `cpoly` compile site:
    `HasKind.imm` on the compiled body lock, pushed BEFORE this `consCVar`). -/
theorem CompilerCtx.Coherent.consCVar {s1 s2 : Sig} {ctx : CompilerCtx s1 s2}
    {cb : CapyCaptureBound s1} {c : BVar s2 .cvar}
    (hcoh : ctx.Coherent) (hcb : cb.IsClosed)
    (hlk : ctx.coreCtx.LookupCVar c .access_only (CapyCaptureBound.compile cb ctx.srcCtx))
    (hro : cb = .unbound .ro → HasKind ctx.coreCtx (.cvar (.M .epsilon) c) .ro) :
    (ctx.consCVar cb c).Coherent where
  closed := hcoh.closed
  capyClosed := by
    simp only [CompilerCtx.consCVar_capyCtx, CapyCtx.push_cvar_default, CapyCtx.push_cvar]
    exact CapyCtx.IsClosed.push hcoh.capyClosed (CapyBinding.IsClosed.cvar hcb)
  srcClosed := CompilerCtx.consCVar_VarsClosed hcoh.srcClosed
  varLookup := by
    intro x T hl
    simp only [CompilerCtx.consCVar_capyCtx, CapyCtx.push_cvar_default, CapyCtx.push_cvar] at hl
    cases hl with
    | there hl0 =>
      obtain ⟨bv0, hbv0, himg0, hcore0⟩ := hcoh.varLookup hl0
      refine ⟨bv0, hbv0, ?_, ?_⟩
      · cases himg0 with
        | inl h =>
          left
          exact h.trans
            (CapyCaptureSet.compile_captureSet_weaken_eq CompilerCtx.MapsTo.consCVar_weaken).symm
        | inr h =>
          obtain ⟨cx, hlv, hcx⟩ := h
          right
          refine ⟨cx, hlv, ?_⟩
          exact (CapyCaptureSet.compile_captureSet_weaken_eq
            CompilerCtx.MapsTo.consCVar_weaken).symm ▸ hcx
      · exact (CapyTy.compile_refine_weaken_eq
          CompilerCtx.MapsTo.consCVar_weaken).symm ▸ hcore0
  cvarLookup := by
    intro c0 a cb0 hl
    simp only [CompilerCtx.consCVar_capyCtx, CapyCtx.push_cvar_default, CapyCtx.push_cvar] at hl
    cases hl with
    | here =>
      rw [(CapyCaptureBound.compile_weaken_eq CompilerCtx.MapsTo.consCVar_weaken).symm] at hlk
      exact hlk
    | there hl0 =>
      have h := hcoh.cvarLookup hl0
      rw [(CapyCaptureBound.compile_weaken_eq CompilerCtx.MapsTo.consCVar_weaken).symm] at h
      exact h
  tvarLookup := by
    intro X S hl
    simp only [CompilerCtx.consCVar_capyCtx, CapyCtx.push_cvar_default, CapyCtx.push_cvar] at hl
    cases hl with
    | there hl0 =>
      have h := hcoh.tvarLookup hl0
      rw [(CapyPureTy.compile_weaken_eq CompilerCtx.MapsTo.consCVar_weaken).symm] at h
      exact h
  roLookup := by
    intro c0 a0 cb0 hl heq
    simp only [CompilerCtx.consCVar_capyCtx, CapyCtx.push_cvar_default, CapyCtx.push_cvar] at hl
    cases hl with
    | here =>
      exact hro (CapyCaptureBound.rename_eq_unbound_iff.mp heq)
    | there hl0 =>
      exact hcoh.roLookup hl0 (CapyCaptureBound.rename_eq_unbound_iff.mp heq)

/-- A fresh *source* type binder `X <: S` preserves coherence; the new `.here`
    type-variable lookup is supplied by `hlk`. -/
theorem CompilerCtx.Coherent.consTVar {s1 s2 : Sig} {ctx : CompilerCtx s1 s2}
    {S : CapyPureTy s1} {X : BVar s2 .tvar}
    (hcoh : ctx.Coherent) (hS : S.core.IsClosed)
    (hlk : ctx.coreCtx.LookupTVar X (CapyPureTy.compile S ctx)) :
    (ctx.consTVar S X).Coherent where
  closed := hcoh.closed
  capyClosed := by
    simp only [CompilerCtx.consTVar_capyCtx, CapyCtx.push_tvar]
    exact CapyCtx.IsClosed.push hcoh.capyClosed (CapyBinding.IsClosed.tvar hS)
  srcClosed := CompilerCtx.consTVar_VarsClosed hcoh.srcClosed
  varLookup := by
    intro x T hl
    simp only [CompilerCtx.consTVar_capyCtx, CapyCtx.push_tvar] at hl
    cases hl with
    | there hl0 =>
      obtain ⟨bv0, hbv0, himg0, hcore0⟩ := hcoh.varLookup hl0
      refine ⟨bv0, hbv0, ?_, ?_⟩
      · cases himg0 with
        | inl h =>
          left
          exact h.trans
            (CapyCaptureSet.compile_captureSet_weaken_eq CompilerCtx.MapsTo.consTVar_weaken).symm
        | inr h =>
          obtain ⟨cx, hlv, hcx⟩ := h
          right
          refine ⟨cx, hlv, ?_⟩
          exact (CapyCaptureSet.compile_captureSet_weaken_eq
            CompilerCtx.MapsTo.consTVar_weaken).symm ▸ hcx
      · exact (CapyTy.compile_refine_weaken_eq
          CompilerCtx.MapsTo.consTVar_weaken).symm ▸ hcore0
  cvarLookup := by
    intro c0 a cb0 hl
    simp only [CompilerCtx.consTVar_capyCtx, CapyCtx.push_tvar] at hl
    cases hl with
    | there hl0 =>
      have h := hcoh.cvarLookup hl0
      rw [(CapyCaptureBound.compile_weaken_eq CompilerCtx.MapsTo.consTVar_weaken).symm] at h
      exact h
  tvarLookup := by
    intro X0 S0 hl
    simp only [CompilerCtx.consTVar_capyCtx, CapyCtx.push_tvar] at hl
    cases hl with
    | here =>
      rw [(CapyPureTy.compile_weaken_eq CompilerCtx.MapsTo.consTVar_weaken).symm] at hlk
      exact hlk
    | there hl0 =>
      have h := hcoh.tvarLookup hl0
      rw [(CapyPureTy.compile_weaken_eq CompilerCtx.MapsTo.consTVar_weaken).symm] at h
      exact h
  roLookup := by
    intro c0 a0 cb0 hl heq
    simp only [CompilerCtx.consTVar_capyCtx, CapyCtx.push_tvar] at hl
    cases hl with
    | there hl0 =>
      exact hcoh.roLookup hl0 (CapyCaptureBound.rename_eq_unbound_iff.mp heq)

/-- A fresh *source* term binder `x : T` (a real Core binder, mapped to target var
    `bv` with capture image `⟦T.captureSet⟧`) preserves coherence.  `bv` is required
    to be bound in `coreCtx` at `⟦T⟧` (`hlk`). -/
theorem CompilerCtx.Coherent.consVar {s1 s2 : Sig} {ctx : CompilerCtx s1 s2}
    {T : CapyTy .capt s1} {bv : BVar s2 .var}
    (hcoh : ctx.Coherent) (hT : T.IsClosed)
    (hlk : ctx.coreCtx.LookupVar bv (CapyTy.compile T ctx)) :
    (ctx.consVar T (some bv) (CapyCaptureSet.compile T.captureSet ctx.srcCtx)).Coherent where
  closed := hcoh.closed
  capyClosed := by
    simp only [CompilerCtx.consVar_capyCtx, CapyCtx.push_var]
    exact CapyCtx.IsClosed.push hcoh.capyClosed (CapyBinding.IsClosed.var hT)
  srcClosed := CompilerCtx.consVar_VarsClosed hcoh.srcClosed
    (CapyCaptureSet.compile_isClosed (CapyTy.IsClosed.captureSet hT) hcoh.srcClosed)
  varLookup := by
    intro x T0 hl
    simp only [CompilerCtx.consVar_capyCtx, CapyCtx.push_var] at hl
    cases hl with
    | here =>
      refine ⟨bv, rfl, ?_, ?_⟩
      · left
        exact (CapyCaptureSet.compile_captureSet_weaken_eq CompilerCtx.MapsTo.consVar_weaken).symm
      · -- the fresh binder is ALIGNED (image = `⟦T.captureSet⟧`), so the compiled
        -- self-refined type collapses to `⟦T⟧` (`compile_refine_self`), which peels
        -- to the supplied binding.
        have hsrc : (ctx.consVar T (some bv)
              (CapyCaptureSet.compile T.captureSet ctx.srcCtx)).srcCtx.lookupVar .here
            = CapyCaptureSet.compile (T.rename Rename.succ).captureSet
                (ctx.consVar T (some bv)
                  (CapyCaptureSet.compile T.captureSet ctx.srcCtx)).srcCtx :=
          (CapyCaptureSet.compile_captureSet_weaken_eq CompilerCtx.MapsTo.consVar_weaken).symm
        have hcapy : (ctx.consVar T (some bv)
              (CapyCaptureSet.compile T.captureSet ctx.srcCtx)).capyCtx.LookupVar .here
            (T.rename Rename.succ) := CapyCtx.LookupVar.here
        rw [CapyTy.compile_refine_self hsrc hcapy]
        exact (CapyTy.compile_weaken_eq CompilerCtx.MapsTo.consVar_weaken).symm ▸ hlk
    | there hl0 =>
      obtain ⟨bv0, hbv0, himg0, hcore0⟩ := hcoh.varLookup hl0
      refine ⟨bv0, hbv0, ?_, ?_⟩
      · cases himg0 with
        | inl h =>
          left
          exact h.trans
            (CapyCaptureSet.compile_captureSet_weaken_eq CompilerCtx.MapsTo.consVar_weaken).symm
        | inr h =>
          obtain ⟨cx, hlv, hcx⟩ := h
          right
          refine ⟨cx, hlv, ?_⟩
          exact (CapyCaptureSet.compile_captureSet_weaken_eq
            CompilerCtx.MapsTo.consVar_weaken).symm ▸ hcx
      · exact (CapyTy.compile_refine_weaken_eq
          CompilerCtx.MapsTo.consVar_weaken).symm ▸ hcore0
  cvarLookup := by
    intro c0 a cb0 hl
    simp only [CompilerCtx.consVar_capyCtx, CapyCtx.push_var] at hl
    cases hl with
    | there hl0 =>
      have h := hcoh.cvarLookup hl0
      rw [(CapyCaptureBound.compile_weaken_eq CompilerCtx.MapsTo.consVar_weaken).symm] at h
      exact h
  tvarLookup := by
    intro X S hl
    simp only [CompilerCtx.consVar_capyCtx, CapyCtx.push_var] at hl
    cases hl with
    | there hl0 =>
      have h := hcoh.tvarLookup hl0
      rw [(CapyPureTy.compile_weaken_eq CompilerCtx.MapsTo.consVar_weaken).symm] at h
      exact h
  roLookup := by
    intro c0 a0 cb0 hl heq
    simp only [CompilerCtx.consVar_capyCtx, CapyCtx.push_var] at hl
    cases hl with
    | there hl0 =>
      exact hcoh.roLookup hl0 (CapyCaptureBound.rename_eq_unbound_iff.mp heq)

/-- `Coherent`'s capture-image component, in `SrcAligned` form (every var's image
    IS its latent `⟦T.captureSet⟧`).

    ⚠ GENUINE DESIGN GAP (fresh-under-abs family): at a RE-ABSTRACTED parameter
    binder (`x ↦ {cx}`, the second `varLookup` disjunct — present in every
    abs-body compiler context) alignment is FALSE: `{cx}` is a bare target cvar
    while the aligned image is the compiled latent `⟦T.captureSet⟧`.  The
    aligned-context devices that consume this (`compile_resourcePeaks` / the A1
    resource keystone behind the `AccessOnly`/`droppable` transports, and the
    `fresh` case's `realign`-identity `SubstCompat`) are equalities that genuinely
    FAIL there — e.g. `fresh`-packing a parameter emits `pack {cx} x`, whose
    target `droppable` obligation is false (`cx` is bound `.access_only`).
    Resolving this needs a design decision (can-drop-bounded `cx`, a
    `Subcapt`-relaxed B2c for the lock keystones, or a source-level device);
    until then the second disjunct is a documented `sorry`. -/
theorem CompilerCtx.Coherent.srcAligned {s1 s2 : Sig} {ctx : CompilerCtx s1 s2}
    (hcoh : ctx.Coherent) : SrcAligned ctx.capyCtx ctx.srcCtx := by
  intro x T hlook
  obtain ⟨bv, _, himg, _⟩ := hcoh.varLookup hlook
  cases himg with
  | inl h => exact h
  | inr h => sorry

/-- A fresh *source* term binder mapped to a RE-ABSTRACTED capture image `{cx}` —
    the `abs` compilation's function parameter.  `cx` must be bound in `coreCtx` at
    authority `.access_only` with bound `⟦T.captureSet⟧` (the middle `cpoly` binder
    of the compiled arrow), and `bv` at the compiled self-refined domain type
    (which resolves `x ↦ {cx}` — exactly the compiled arrow's domain). -/
theorem CompilerCtx.Coherent.consVarCVar {s1 s2 : Sig} {ctx : CompilerCtx s1 s2}
    {T : CapyTy .capt s1} {bv : BVar s2 .var} {cx : BVar s2 .cvar}
    (hcoh : ctx.Coherent) (hT : T.IsClosed)
    (hcx : ctx.coreCtx.LookupCVar cx .access_only
      (.bound (CapyCaptureSet.compile T.captureSet ctx.srcCtx)))
    (hlk : ctx.coreCtx.LookupVar bv
      (CapyTy.compile ((T.rename Rename.succ).refineCaptureSet
          (.var (.M .epsilon) (.bound .here)))
        (ctx.consVar T (some bv) (.cvar (.M .epsilon) cx)))) :
    (ctx.consVar T (some bv) (.cvar (.M .epsilon) cx)).Coherent where
  closed := hcoh.closed
  capyClosed := by
    simp only [CompilerCtx.consVar_capyCtx, CapyCtx.push_var]
    exact CapyCtx.IsClosed.push hcoh.capyClosed (CapyBinding.IsClosed.var hT)
  srcClosed := CompilerCtx.consVar_VarsClosed hcoh.srcClosed CaptureSet.IsClosed.cvar
  varLookup := by
    intro x T0 hl
    simp only [CompilerCtx.consVar_capyCtx, CapyCtx.push_var] at hl
    cases hl with
    | here =>
      refine ⟨bv, rfl, ?_, hlk⟩
      right
      refine ⟨cx, rfl, ?_⟩
      exact (CapyCaptureSet.compile_captureSet_weaken_eq
        CompilerCtx.MapsTo.consVar_weaken).symm ▸ hcx
    | there hl0 =>
      obtain ⟨bv0, hbv0, himg0, hcore0⟩ := hcoh.varLookup hl0
      refine ⟨bv0, hbv0, ?_, ?_⟩
      · cases himg0 with
        | inl h =>
          left
          exact h.trans
            (CapyCaptureSet.compile_captureSet_weaken_eq CompilerCtx.MapsTo.consVar_weaken).symm
        | inr h =>
          obtain ⟨cx0, hlv, hcx0⟩ := h
          right
          refine ⟨cx0, hlv, ?_⟩
          exact (CapyCaptureSet.compile_captureSet_weaken_eq
            CompilerCtx.MapsTo.consVar_weaken).symm ▸ hcx0
      · exact (CapyTy.compile_refine_weaken_eq
          CompilerCtx.MapsTo.consVar_weaken).symm ▸ hcore0
  cvarLookup := by
    intro c0 a cb0 hl
    simp only [CompilerCtx.consVar_capyCtx, CapyCtx.push_var] at hl
    cases hl with
    | there hl0 =>
      have h := hcoh.cvarLookup hl0
      rw [(CapyCaptureBound.compile_weaken_eq CompilerCtx.MapsTo.consVar_weaken).symm] at h
      exact h
  tvarLookup := by
    intro X S hl
    simp only [CompilerCtx.consVar_capyCtx, CapyCtx.push_var] at hl
    cases hl with
    | there hl0 =>
      have h := hcoh.tvarLookup hl0
      rw [(CapyPureTy.compile_weaken_eq CompilerCtx.MapsTo.consVar_weaken).symm] at h
      exact h
  roLookup := by
    intro c0 a0 cb0 hl heq
    simp only [CompilerCtx.consVar_capyCtx, CapyCtx.push_var] at hl
    cases hl with
    | there hl0 =>
      exact hcoh.roLookup hl0 (CapyCaptureBound.rename_eq_unbound_iff.mp heq)

end Compilation
