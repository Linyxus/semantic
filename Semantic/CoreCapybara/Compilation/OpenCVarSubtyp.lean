import Semantic.CoreCapybara.Compilation.SubtypCompile
open CoreCapybara
namespace Compilation

/-!
# Type-level capture-opening commutes up to subtyping  (Workstream B / K1)

`fresh`'s `var` obligation needs `⟦T[D/c]⟧ <: (⟦T⟧_exiCtx).subst (openCVar ⟦D⟧)`.
At leaves this is the *equality* `⟦T[D/c]⟧ = ⟦T⟧[⟦D⟧/c]` (capture-level
`compile_subst`); at function types the compiled lock `peakSepCtx` re-groups —
opening `c ↦ D = {c₁,c₂}` SPLITS `c`'s single lock item into one per peak of `D`
(SEPARATED), vs. keeping `c`'s single item now holding `⟦D⟧` (MERGED).  A modal
lock is contravariant in its demand, so SEPARATED `<:` MERGED (the extra
separations discharged from `D`'s droppability).  The function *domain* is itself
contravariant, so we prove BOTH directions.

**Design (avoids the K2 coherence keystone):** the only context-sensitive fact
the lock `Satisfy` needs is that the split peaks are pairwise *droppable-separate*
in the TARGET.  We thread that as a target-side hypothesis (`TgtPairDroppable`)
which transports through binders by cheap target weakening — establishing it once
at the top in `fresh` via Workstream A's `compile_droppable`.  No `Coherent`
threading through the recursion.
-/

/-- A target substitution `σt` is *pairwise-droppable* in `Γt` when any two
    distinct peaks of an image `σt.cvar Y` separate (`TwoDistinctDroppable`).
    Vacuous for single-cvar images; for the genuinely-substituted cvar it is
    `⟦D⟧.droppable`.  Stable under lifting. -/
def TgtPairDroppable {s2 s2' : Sig} (Γt : Ctx s2') (σt : Subst s2 s2') : Prop :=
  ∀ (Y : BVar s2 .cvar) (a1 a2 : Access) (c1 c2 : BVar s2' .cvar), c1 ≠ c2 →
    (CaptureSet.cvar a1 c1) ⊆ CaptureSet.peaks Γt (σt.cvar Y) →
    (CaptureSet.cvar a2 c2) ⊆ CaptureSet.peaks Γt (σt.cvar Y) →
    Γt.TwoDistinctDroppable c1 c2

/-- A target cvar atom of a `succ`-renamed capture set comes from a `.there`
    atom of the original (same access mode). -/
theorem CaptureSet.cvar_subset_rename_succ {s : Sig} {a : Access}
    {c : BVar (s,,k) .cvar} {cs : CaptureSet s}
    (h : CaptureSet.Subset (.cvar a c) (cs.rename (Rename.succ (k := k)))) :
    ∃ c0, c = .there c0 ∧ CaptureSet.Subset (.cvar a c0) cs := by
  induction cs with
  | empty => simp only [CaptureSet.rename] at h; cases h
  | union cs1 cs2 ih1 ih2 =>
    simp only [CaptureSet.rename] at h
    cases h with
    | union_right_left h1 =>
      obtain ⟨c0, hc, hsub⟩ := ih1 h1; exact ⟨c0, hc, .union_right_left hsub⟩
    | union_right_right h2 =>
      obtain ⟨c0, hc, hsub⟩ := ih2 h2; exact ⟨c0, hc, .union_right_right hsub⟩
  | cvar a' c' =>
    simp only [CaptureSet.rename, Rename.succ] at h
    cases h
    exact ⟨c', rfl, CaptureSet.Subset.refl⟩
  | var a' x =>
    simp only [CaptureSet.rename, Var.rename] at h
    cases x <;> cases h

/-- `TgtPairDroppable` is preserved by a target binder + a cvar lift. -/
theorem TgtPairDroppable.lift {s2 s2' : Sig} {Γt : Ctx s2'} {σt : Subst s2 s2'}
    {b : Binding s2' .cvar} (h : TgtPairDroppable Γt σt) :
    TgtPairDroppable (Γt.push b) (σt.lift (k := Kind.cvar)) := by
  intro Y a1 a2 c1 c2 hne hmem1 hmem2
  cases Y with
  | here =>
    -- `σt.lift.cvar .here = .cvar ε .here`: a single peak, so no distinct pair.
    have h1 : (σt.lift (k := Kind.cvar)).cvar .here = CaptureSet.cvar (.M .epsilon) .here := rfl
    rw [h1] at hmem1 hmem2
    simp only [CaptureSet.peaks] at hmem1 hmem2
    cases hmem1; cases hmem2
    exact absurd rfl hne
  | there Y0 =>
    have hYeq : (σt.lift (k := Kind.cvar)).cvar (.there Y0)
        = (σt.cvar Y0).rename Rename.succ := Subst.lift_there_cvar_eq
    rw [hYeq, CaptureSet.peaks_rename_succ_eq] at hmem1 hmem2
    obtain ⟨d1, hd1, hsub1⟩ := CaptureSet.cvar_subset_rename_succ hmem1
    obtain ⟨d2, hd2, hsub2⟩ := CaptureSet.cvar_subset_rename_succ hmem2
    subst hd1; subst hd2
    have hne0 : d1 ≠ d2 := fun heq => hne (by rw [heq])
    obtain ⟨ha_d1, ha_d2, _⟩ := h Y0 a1 a2 d1 d2 hne0 hsub1 hsub2
    refine ⟨?_, ?_, hne⟩
    · simp only [Ctx.lookup_authority]; exact ha_d1
    · simp only [Ctx.lookup_authority]; exact ha_d2

/-- `TgtPairDroppable` is preserved by a target binder + a TVAR lift (the
    `poly`-body builder).  The lifted cvar var is always `.there` (the binder is a
    tvar), so only the shift case arises — identical to `.lift`'s `.there` case. -/
theorem TgtPairDroppable.liftTVar {s2 s2' : Sig} {Γt : Ctx s2'} {σt : Subst s2 s2'}
    {b : Binding s2' .tvar} (h : TgtPairDroppable Γt σt) :
    TgtPairDroppable (Γt.push b) (σt.lift (k := Kind.tvar)) := by
  intro Y a1 a2 c1 c2 hne hmem1 hmem2
  cases Y with
  | there Y0 =>
    have hYeq : (σt.lift (k := Kind.tvar)).cvar (.there Y0)
        = (σt.cvar Y0).rename Rename.succ := Subst.lift_there_cvar_eq
    rw [hYeq, CaptureSet.peaks_rename_succ_eq] at hmem1 hmem2
    obtain ⟨d1, hd1, hsub1⟩ := CaptureSet.cvar_subset_rename_succ hmem1
    obtain ⟨d2, hd2, hsub2⟩ := CaptureSet.cvar_subset_rename_succ hmem2
    subst hd1; subst hd2
    have hne0 : d1 ≠ d2 := fun heq => hne (by rw [heq])
    obtain ⟨ha_d1, ha_d2, _⟩ := h Y0 a1 a2 d1 d2 hne0 hsub1 hsub2
    refine ⟨?_, ?_, hne⟩
    · simp only [Ctx.lookup_authority]; exact ha_d1
    · simp only [Ctx.lookup_authority]; exact ha_d2

/-- **Peaks-after-substitution decomposition.**  A peak cvar of `cs.subst σ`
    traces back to a peak of an atom-image of `cs`: either `(σ.cvar c0).applyAccess m`
    for a cvar-atom `.cvar m c0` of `cs`, or `.var m (σ.var x)` for a var-atom.
    The keystone for classifying the separated lock's peaks (split vs. other). -/
theorem CapyCaptureSet.peaks_subst_mem {s1 s2 : Sig} {Γ : CapyCtx s2}
    {σ : CapySubst s1 s2} {cs : CaptureSet s1} {a : Access} {c : BVar s2 .cvar}
    (h : (CaptureSet.cvar a c) ⊆ CapyCaptureSet.peaks Γ (CapyCaptureSet.subst cs σ)) :
    (∃ (c0 : BVar s1 .cvar) (m : Access),
        (CaptureSet.cvar a c) ⊆ CapyCaptureSet.peaks Γ ((σ.cvar c0).applyAccess m)) ∨
    (∃ (x : Var .var s1) (m : Access),
        (CaptureSet.cvar a c) ⊆ CapyCaptureSet.peaks Γ (.var m (CapyVar.subst x σ))) := by
  induction cs with
  | empty => simp only [CapyCaptureSet.subst, CapyCaptureSet.peaks] at h; cases h
  | union cs1 cs2 ih1 ih2 =>
    simp only [CapyCaptureSet.subst, CapyCaptureSet.peaks] at h
    cases h with
    | union_right_left h1 => exact ih1 h1
    | union_right_right h2 => exact ih2 h2
  | cvar m c0 =>
    simp only [CapyCaptureSet.subst] at h
    exact Or.inl ⟨c0, m, h⟩
  | var m x =>
    simp only [CapyCaptureSet.subst] at h
    exact Or.inr ⟨x, m, h⟩

/-! ### Pure bounds

`Subtyp.poly`/`tabs` retype a polymorphic bound only when it is a *shape* (pure)
type — the target `poly` bound is reconstructed as a `PureTy`.  A merely *closed*
type may have an impure poly bound, which the target subtyping cannot change, so
the type-level commutation needs the bound purity that well-formed source types
always carry (source `poly`/`tabs` bind `CapyPureTy`).  `PureBounds` records
exactly that, recursively. -/

/-- Every polymorphic (`poly`/`tabs`) bound occurring in `T`, at any depth, is a
    pure shape type.  Function domains need not be pure, but their own bounds must
    be (so the recursion can re-enter them). -/
def CapyTy.PureBounds : CapyTy sort s → Prop
  | .top | .tvar _ | .unit | .bool | .cap _ | .cell _ _ => True
  | .arrow T1 _ E => CapyTy.PureBounds T1 ∧ CapyTy.PureBounds E
  | .poly S _ E => S.IsPureType ∧ CapyTy.PureBounds S ∧ CapyTy.PureBounds E
  | .cpoly _ _ E => CapyTy.PureBounds E
  | .exi T => CapyTy.PureBounds T
  | .typ T => CapyTy.PureBounds T

/-! ### Type-variable compatibility (the `tvar` leaf)

`SubstCompat` (in `SubstLemmas`) records the capture/term-variable compatibility
that makes `CaptureSet.compile` commute with `σ`.  The type-level commutation
additionally meets the `tvar` leaf, which `SubstCompat` says nothing about.  We
carry a companion predicate: every source type variable's `σ`-image is itself a
*type variable* whose compiled target image agrees with `σt` post-composed with
the original lookup.  This holds for the only substitutions `fresh` instantiates
(capture-variable openings, which never replace a tvar by a compound), and it is
exactly what makes the `tvar` case a reflexivity. -/

/-- The `σ`-image of each source tvar is a tvar `Z`, and the two target images
    (`σt ∘ lookupTVar` in the orig world vs. `lookupTVar Z` in the sub world)
    coincide.  Threaded alongside `SubstCompat` through the commutation recursion. -/
def SubstTvarCompat {s1 s1' s2 s2' : Sig} (scSub : SrcCtx s1' s2')
    (scOrig : SrcCtx s1 s2) (σ : CapySubst s1 s1') (σt : Subst s2 s2') : Prop :=
  ∀ (X : BVar s1 .tvar), ∃ (Z : BVar s1' .tvar),
    σ.tvar X = CapyPureTy.tvar Z ∧
    σt.tvar (scOrig.lookupTVar X) = PureTy.tvar (scSub.lookupTVar Z)

/-- The base case: opening a fresh cvar maps every tvar to its shift, so its image
    is the same tvar, and the target opening leaves tvars untouched. -/
theorem SubstTvarCompat.openCVar {s1 s2 : Sig} {sc : SrcCtx s1 s2} {T : CaptureSet s1} :
    SubstTvarCompat sc (.cons (.cvar .here) (sc.rename Rename.succ))
      (CapySubst.openCVar T) (Subst.openCVar (CaptureSet.compile T sc)) := by
  intro X
  cases X with
  | there X0 =>
    refine ⟨X0, ?_, ?_⟩
    · simp only [CapySubst.openCVar]
    · simp only [SrcCtx.lookupTVar, SrcCtx.lookupTVar_rename, Rename.succ, Subst.openCVar]

/-- `SubstTvarCompat` is preserved by the compiler's `weakenTarget.consCVar … .here`
    (recursing under a source capture binder mapped to a fresh target cvar). -/
theorem SubstTvarCompat.weakenConsCVar {s1 s1' s2 s2' : Sig} {scSub : SrcCtx s1' s2'}
    {scOrig : SrcCtx s1 s2} {σ : CapySubst s1 s1'} {σt : Subst s2 s2'}
    (h : SubstTvarCompat scSub scOrig σ σt) :
    SubstTvarCompat (.cons (.cvar .here) (scSub.rename Rename.succ))
      (.cons (.cvar .here) (scOrig.rename Rename.succ)) σ.lift (σt.lift (k := Kind.cvar)) := by
  intro X
  cases X with
  | there X0 =>
    obtain ⟨Z0, hZ, hlk⟩ := h X0
    refine ⟨.there Z0, ?_, ?_⟩
    · rw [CapySubst.lift_there_tvar_eq, hZ]; rfl
    · simp only [SrcCtx.lookupTVar, SrcCtx.lookupTVar_rename, Rename.succ,
        Subst.lift_there_tvar_eq, hlk]; rfl

/-- `SubstCompat` preserved by the compiler's `weakenTarget.consTVar … .here`
    (recursing under a source TYPE binder mapped to a fresh target tvar) — the
    `poly`-body builder.  Mirrors `SubstCompat.weakenConsCVar`, but the binder is a
    tvar so the capture/term variables only ever appear as `.there`. -/
theorem SubstCompat.weakenConsTVar {s1 s1' s2 s2' : Sig} {scSub : SrcCtx s1' s2'}
    {scOrig : SrcCtx s1 s2} {σ : CapySubst s1 s1'} {σt : Subst s2 s2'}
    (h : SubstCompat scSub scOrig σ σt) :
    SubstCompat (.cons (.tvar .here) (scSub.rename Rename.succ))
      (.cons (.tvar .here) (scOrig.rename Rename.succ)) σ.lift (σt.lift (k := Kind.tvar)) where
  cvar := by
    intro c
    cases c with
    | there c0 =>
      rw [CapySubst.lift_there_cvar_eq, CaptureSet.compile_rename_succ_cons,
        CaptureSet.compile_rename, h.cvar]
      simp only [SrcCtx.lookupCVar, SrcCtx.lookupCVar_rename, Rename.succ, Subst.lift_there_cvar_eq]
  var := by
    intro x
    cases x with
    | there x0 =>
      have hY : (CapySubst.lift σ (k := Kind.tvar)).var (.there x0)
          = (σ.var x0).rename Rename.succ := CapySubst.lift_there_var_eq
      rw [hY, show (CaptureSet.var (.M .epsilon) ((σ.var x0).rename Rename.succ))
            = (CaptureSet.var (.M .epsilon) (σ.var x0)).rename Rename.succ from rfl,
        CaptureSet.compile_rename_succ_cons, CaptureSet.compile_rename, h.var]
      simp only [SrcCtx.lookupVar, SrcCtx.lookupVar_rename]
      exact CaptureSet.weaken_subst_comm_liftMany (K := [])

/-- `SubstTvarCompat` preserved by `weakenTarget.consTVar … .here` (the `poly`-body
    builder).  The freshly-bound tvar `.here` maps to itself; deeper tvars shift. -/
theorem SubstTvarCompat.weakenConsTVar {s1 s1' s2 s2' : Sig} {scSub : SrcCtx s1' s2'}
    {scOrig : SrcCtx s1 s2} {σ : CapySubst s1 s1'} {σt : Subst s2 s2'}
    (h : SubstTvarCompat scSub scOrig σ σt) :
    SubstTvarCompat (.cons (.tvar .here) (scSub.rename Rename.succ))
      (.cons (.tvar .here) (scOrig.rename Rename.succ)) σ.lift (σt.lift (k := Kind.tvar)) := by
  intro X
  cases X with
  | here =>
    exact ⟨.here, rfl, rfl⟩
  | there X0 =>
    obtain ⟨Z0, hZ, hlk⟩ := h X0
    refine ⟨.there Z0, ?_, ?_⟩
    · rw [CapySubst.lift_there_tvar_eq, hZ]; rfl
    · simp only [SrcCtx.lookupTVar, SrcCtx.lookupTVar_rename, Rename.succ,
        Subst.lift_there_tvar_eq, hlk]; rfl

/-- **Type-level capture-opening commutes up to subtyping, both directions.**
    Stated `∀`-after-`T` (over the substitution data + contexts) so the recursive
    cases re-instantiate at lifted substitutions / extended contexts. -/
theorem CapyTy.compile_subst_subtyp {sort : CapyTySort} (T : CapyTy sort s1) :
    ∀ {s2 s1' s2' : Sig} {ctxOrig : CompilerCtx s1 s2} {ctxSub : CompilerCtx s1' s2'}
      {σ : CapySubst s1 s1'} {σt : Subst s2 s2'},
      SubstCompat ctxSub.srcCtx ctxOrig.srcCtx σ σt →
      SubstTvarCompat ctxSub.srcCtx ctxOrig.srcCtx σ σt → T.IsClosed → CapyTy.PureBounds T →
      TgtPairDroppable ctxSub.coreCtx σt →
      Subtyp ctxSub.coreCtx (CapyTy.compile (T.subst σ) ctxSub)
        ((CapyTy.compile T ctxOrig).subst σt) ∧
      Subtyp ctxSub.coreCtx ((CapyTy.compile T ctxOrig).subst σt)
        (CapyTy.compile (T.subst σ) ctxSub) := by
  induction T with
  | top =>
    intro s2 s1' s2' ctxOrig ctxSub σ σt hcompat htvar hcl hpb hdrop
    simp only [CapyTy.subst, CapyTy.compile, Ty.subst]
    exact ⟨Subtyp.refl, Subtyp.refl⟩
  | unit =>
    intro s2 s1' s2' ctxOrig ctxSub σ σt hcompat htvar hcl hpb hdrop
    simp only [CapyTy.subst, CapyTy.compile, Ty.subst]
    exact ⟨Subtyp.refl, Subtyp.refl⟩
  | bool =>
    intro s2 s1' s2' ctxOrig ctxSub σ σt hcompat htvar hcl hpb hdrop
    simp only [CapyTy.subst, CapyTy.compile, Ty.subst]
    exact ⟨Subtyp.refl, Subtyp.refl⟩
  | cap cs =>
    intro s2 s1' s2' ctxOrig ctxSub σ σt hcompat htvar hcl hpb hdrop
    cases hcl with | cap hcs =>
    rw [CapyTy.compile_subst_cap hcompat hcs]
    exact ⟨Subtyp.refl, Subtyp.refl⟩
  | cell cs m =>
    intro s2 s1' s2' ctxOrig ctxSub σ σt hcompat htvar hcl hpb hdrop
    cases hcl with | cell hcs =>
    rw [CapyTy.compile_subst_cell hcompat hcs]
    exact ⟨Subtyp.refl, Subtyp.refl⟩
  | typ T1 ih =>
    intro s2 s1' s2' ctxOrig ctxSub σ σt hcompat htvar hcl hpb hdrop
    cases hcl with | typ hcl1 =>
    simp only [CapyTy.subst, CapyTy.compile, Ty.subst]
    obtain ⟨hle, hge⟩ := ih hcompat htvar hcl1 hpb hdrop
    exact ⟨Subtyp.typ hle, Subtyp.typ hge⟩
  | exi T1 ih =>
    intro s2 s1' s2' ctxOrig ctxSub σ σt hcompat htvar hcl hpb hdrop
    cases hcl with | exi hcl1 =>
    simp only [CapyTy.subst, CapyTy.compile, Ty.subst]
    obtain ⟨hle, hge⟩ := ih (ctxOrig := ctxOrig.weakenTarget.consCVar (.unbound .epsilon) .here)
      (ctxSub := ctxSub.weakenTarget.consCVar (.unbound .epsilon) .here)
      (SubstCompat.weakenConsCVar hcompat) (SubstTvarCompat.weakenConsCVar htvar) hcl1 hpb
      (TgtPairDroppable.lift hdrop)
    exact ⟨Subtyp.exi hle, Subtyp.exi hge⟩
  | tvar X =>
    intro s2 s1' s2' ctxOrig ctxSub σ σt hcompat htvar hcl hpb hdrop
    obtain ⟨Z, hZ, hlk⟩ := htvar X
    simp only [CapyTy.subst, hZ, CapyPureTy.tvar, CapyTy.compile, Ty.subst, hlk, PureTy.tvar]
    exact ⟨Subtyp.refl, Subtyp.refl⟩
  | arrow T1 cs E ihT1 ihE =>
    intro s2 s1' s2' ctxOrig ctxSub σ σt hcompat htvar hcl hpb hdrop
    sorry
  | poly S cs E ihS ihE =>
    intro s2 s1' s2' ctxOrig ctxSub σ σt hcompat htvar hcl hpb hdrop
    sorry
  | cpoly cb cs E ihE =>
    intro s2 s1' s2' ctxOrig ctxSub σ σt hcompat htvar hcl hpb hdrop
    sorry

end Compilation
