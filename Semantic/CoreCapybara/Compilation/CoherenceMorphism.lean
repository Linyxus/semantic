import Semantic.CoreCapybara.Compilation.Coherence
import Semantic.CoreCapybara.Compilation.ContextMorphism

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
      CaptureSet.compile_rename_succ_cons]

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
    obtain ⟨bv0, hbv0, hlv0, hcore0⟩ := hcoh.varLookup hl
    refine ⟨Rename.succ.var bv0, ?_, ?_, ?_⟩
    · simp only [CompilerCtx.weakenTarget_srcCtx,
        SrcCtx.lookupVarBVar_rename, hbv0, Option.map_some]
    · simp only [CompilerCtx.weakenTarget_srcCtx,
        SrcCtx.lookupVar_rename, hlv0, CaptureSet.compile_rename]
    · rw [CapyTy.compile_rename T ctx (ctx.weakenTarget b) Rename.succ rfl rfl]
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
theorem CaptureSet.compile_captureSet_weaken_eq {s1 s2 : Sig} {k : Kind} {T : CapyTy .capt s1}
    {ctx : CompilerCtx s1 s2} {ctx2 : CompilerCtx (s1,,k) s2}
    (hm : ctx.MapsTo ctx2 (Rename.succ (k := k)) Rename.id) :
    CaptureSet.compile (T.rename (Rename.succ (k := k))).captureSet ctx2.srcCtx
      = CaptureSet.compile T.captureSet ctx.srcCtx := by
  rw [CapyTy.captureSet_rename, CaptureSet.compile_mapsTo hm.cvar hm.var, CaptureSet.rename_id]

/-! ### `Coherent` builder-preservation under source binders

`cases hl` unfolds the source `push_cvar_default`/`push_var`/`push_tvar` to the
general `push` (`,,k`), so the looked-up payload lands in the `extend` rep while the
builder context keeps the `extend_cvar`/`_var`/`_tvar` rep — defeq but syntactically
distinct.  We therefore realign the *clean* (rename-free) hypothesis side with the
weaken lemmas and discharge by `exact`, whose defeq check bridges the rep gap. -/

/-- A fresh *source* capture binder `c <: cb` preserves coherence; the new `.here`
    capture lookup is supplied by `hlk`. -/
theorem CompilerCtx.Coherent.consCVar {s1 s2 : Sig} {ctx : CompilerCtx s1 s2}
    {cb : CapyCaptureBound s1} {c : BVar s2 .cvar}
    (hcoh : ctx.Coherent) (hcb : cb.IsClosed)
    (hlk : ctx.coreCtx.LookupCVar c .access_only (CapyCaptureBound.compile cb ctx.srcCtx)) :
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
      obtain ⟨bv0, hbv0, hlv0, hcore0⟩ := hcoh.varLookup hl0
      refine ⟨bv0, hbv0, ?_, ?_⟩
      · exact hlv0.trans
          (CaptureSet.compile_captureSet_weaken_eq CompilerCtx.MapsTo.consCVar_weaken).symm
      · rw [(CapyTy.compile_weaken_eq CompilerCtx.MapsTo.consCVar_weaken).symm] at hcore0
        exact hcore0
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
      obtain ⟨bv0, hbv0, hlv0, hcore0⟩ := hcoh.varLookup hl0
      refine ⟨bv0, hbv0, ?_, ?_⟩
      · exact hlv0.trans
          (CaptureSet.compile_captureSet_weaken_eq CompilerCtx.MapsTo.consTVar_weaken).symm
      · rw [(CapyTy.compile_weaken_eq CompilerCtx.MapsTo.consTVar_weaken).symm] at hcore0
        exact hcore0
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

/-- A fresh *source* term binder `x : T` (a real Core binder, mapped to target var
    `bv` with capture image `⟦T.captureSet⟧`) preserves coherence.  `bv` is required
    to be bound in `coreCtx` at `⟦T⟧` (`hlk`). -/
theorem CompilerCtx.Coherent.consVar {s1 s2 : Sig} {ctx : CompilerCtx s1 s2}
    {T : CapyTy .capt s1} {bv : BVar s2 .var}
    (hcoh : ctx.Coherent) (hT : T.IsClosed)
    (hlk : ctx.coreCtx.LookupVar bv (CapyTy.compile T ctx)) :
    (ctx.consVar T (some bv) (CaptureSet.compile T.captureSet ctx.srcCtx)).Coherent where
  closed := hcoh.closed
  capyClosed := by
    simp only [CompilerCtx.consVar_capyCtx, CapyCtx.push_var]
    exact CapyCtx.IsClosed.push hcoh.capyClosed (CapyBinding.IsClosed.var hT)
  srcClosed := CompilerCtx.consVar_VarsClosed hcoh.srcClosed
    (CaptureSet.compile_isClosed (CapyTy.IsClosed.captureSet hT) hcoh.srcClosed)
  varLookup := by
    intro x T0 hl
    simp only [CompilerCtx.consVar_capyCtx, CapyCtx.push_var] at hl
    cases hl with
    | here =>
      refine ⟨bv, rfl, ?_, ?_⟩
      · exact (CaptureSet.compile_captureSet_weaken_eq CompilerCtx.MapsTo.consVar_weaken).symm
      · rw [(CapyTy.compile_weaken_eq CompilerCtx.MapsTo.consVar_weaken).symm] at hlk
        exact hlk
    | there hl0 =>
      obtain ⟨bv0, hbv0, hlv0, hcore0⟩ := hcoh.varLookup hl0
      refine ⟨bv0, hbv0, ?_, ?_⟩
      · exact hlv0.trans
          (CaptureSet.compile_captureSet_weaken_eq CompilerCtx.MapsTo.consVar_weaken).symm
      · rw [(CapyTy.compile_weaken_eq CompilerCtx.MapsTo.consVar_weaken).symm] at hcore0
        exact hcore0
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

end Compilation
