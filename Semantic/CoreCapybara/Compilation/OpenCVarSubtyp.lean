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

/-- `TgtPairDroppable` preserved by a target binder + a LOCK lift (the modal-body
    builder).  The lifted cvar var is always `.there` (the binder is a lock), so
    only the shift case arises — identical to `.liftTVar`. -/
theorem TgtPairDroppable.liftLock {s2 s2' : Sig} {Γt : Ctx s2'} {σt : Subst s2 s2'}
    {b : Binding s2' .lock} (h : TgtPairDroppable Γt σt) :
    TgtPairDroppable (Γt.push b) (σt.lift (k := Kind.lock)) := by
  intro Y a1 a2 c1 c2 hne hmem1 hmem2
  cases Y with
  | there Y0 =>
    have hYeq : (σt.lift (k := Kind.lock)).cvar (.there Y0)
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
    {σ : CapySubst s1 s2} {cs : CapyCaptureSet s1} {a : Access} {c : BVar s2 .cvar}
    (h : (CapyCaptureSet.cvar a c) ⊆ CapyCaptureSet.peaks Γ (CapyCaptureSet.subst cs σ)) :
    (∃ (c0 : BVar s1 .cvar) (m : Access),
        (CapyCaptureSet.cvar a c) ⊆ CapyCaptureSet.peaks Γ ((σ.cvar c0).applyAccess m)) ∨
    (∃ (x : Var .var s1) (m : Access),
        (CapyCaptureSet.cvar a c) ⊆ CapyCaptureSet.peaks Γ (.var m (CapyVar.subst x σ))) := by
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
that makes `CapyCaptureSet.compile` commute with `σ`.  The type-level commutation
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
theorem SubstTvarCompat.openCVar {s1 s2 : Sig} {sc : SrcCtx s1 s2} {T : CapyCaptureSet s1} :
    SubstTvarCompat sc (.cons (.cvar .here) (sc.rename Rename.succ))
      (CapySubst.openCVar T) (Subst.openCVar (CapyCaptureSet.compile T sc)) := by
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
      rw [CapySubst.lift_there_cvar_eq, CapyCaptureSet.compile_rename_succ_cons,
        CapyCaptureSet.compile_rename, h.cvar]
      simp only [SrcCtx.lookupCVar, SrcCtx.lookupCVar_rename, Rename.succ, Subst.lift_there_cvar_eq]
  var := by
    intro x
    cases x with
    | there x0 =>
      have hY : (CapySubst.lift σ (k := Kind.tvar)).var (.there x0)
          = (σ.var x0).rename Rename.succ := CapySubst.lift_there_var_eq
      rw [hY, show (CapyCaptureSet.var (.M .epsilon) ((σ.var x0).rename Rename.succ))
            = (CapyCaptureSet.var (.M .epsilon) (σ.var x0)).rename Rename.succ from rfl,
        CapyCaptureSet.compile_rename_succ_cons, CapyCaptureSet.compile_rename, h.var]
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

/-- `SubstTvarCompat` preserved by a fresh *target* binder (`weakenTarget`): both
    `srcCtx`s rename by `succ`, `σ` is unchanged, `σt` lifts.  Mirrors
    `SubstCompat.weakenTarget`; the lock body's tvar leaf. -/
theorem SubstTvarCompat.weakenTarget {s1 s1' s2 s2' : Sig} {scSub : SrcCtx s1' s2'}
    {scOrig : SrcCtx s1 s2} {σ : CapySubst s1 s1'} {σt : Subst s2 s2'}
    (h : SubstTvarCompat scSub scOrig σ σt) :
    SubstTvarCompat (scSub.rename Rename.succ) (scOrig.rename Rename.succ) σ
      (σt.lift (k := k)) := by
  intro X
  obtain ⟨Z, hZ, hlk⟩ := h X
  refine ⟨Z, hZ, ?_⟩
  simp only [SrcCtx.lookupTVar_rename, Rename.succ, Subst.lift_there_tvar_eq, hlk]; rfl

/-- Alignment is preserved by a fresh *target* binder (`SrcCtx.weaken = rename succ`):
    both the looked-up image and the compiled capture set rename by `succ`. -/
theorem SrcAligned.weakenTarget {s s2 : Sig} {Γ : CapyCtx s} {sc : SrcCtx s s2} {k : Kind}
    (h : SrcAligned Γ sc) : SrcAligned Γ (sc.weaken (k := k)) := by
  intro x T hlook
  change (sc.rename Rename.succ).lookupVar x
    = CapyCaptureSet.compile T.captureSet (sc.rename Rename.succ)
  rw [SrcCtx.lookupVar_rename, CapyCaptureSet.compile_rename, h hlook]

/-- Compiling a source-weakened type's capture set through a matching `cons` peels the
    weakening (abstract kind `k`, so the rewrite's kind metavar absorbs the goal's). -/
theorem CapyCaptureSet.compile_captureSet_weaken {s s2 : Sig} {k : Kind} {T : CapyTy .capt s}
    {info : SrcBinderInfo k s2} {sc : SrcCtx s s2} :
    CapyCaptureSet.compile (T.rename (Rename.succ (k := k))).captureSet (.cons info sc)
      = CapyCaptureSet.compile T.captureSet sc := by
  rw [CapyTy.captureSet_rename]
  exact CapyCaptureSet.compile_rename_succ_cons

/-- Alignment is preserved by a fresh source capture binder (`consCVar`). -/
theorem SrcAligned.consCVar {s s2 : Sig} {Γ : CapyCtx s} {sc : SrcCtx s s2}
    {cb : CapyCaptureBound s} {c : BVar s2 .cvar}
    (h : SrcAligned Γ sc) : SrcAligned (Γ.push_cvar_default cb) (.cons (.cvar c) sc) := by
  intro x T hlook
  simp only [CapyCtx.push_cvar_default, CapyCtx.push_cvar] at hlook
  cases hlook with
  | there hlook0 => exact (h hlook0).trans CapyCaptureSet.compile_captureSet_weaken.symm

/-- Alignment is preserved by a fresh source type binder (`consTVar`). -/
theorem SrcAligned.consTVar {s s2 : Sig} {Γ : CapyCtx s} {sc : SrcCtx s s2}
    {S : CapyPureTy s} {X : BVar s2 .tvar}
    (h : SrcAligned Γ sc) : SrcAligned (Γ.push_tvar S) (.cons (.tvar X) sc) := by
  intro x T hlook
  simp only [CapyCtx.push_tvar] at hlook
  cases hlook with
  | there hlook0 => exact (h hlook0).trans CapyCaptureSet.compile_captureSet_weaken.symm

/-- **(★-keystone) Compiled peaks commute with a compatible substitution.**  Combines
    (★) `compile_peaks` (compilation factors through peak-resolution, under alignment)
    on both sides with the capture-level `compile_subst`:
    `⟦peaks (cs[σ])⟧ = ⟦peaks cs⟧[σt]`.  This is the union-level correspondence that
    lets the lock-`Satisfy` cross pairs relate `Ψ_L`'s items to `Ψ_R`'s (the
    SEPARATED-vs-MERGED split is then purely combinatorial on top of this). -/
theorem CapyCaptureSet.compile_peaks_subst {s1 s2 s1' s2' : Sig}
    {Γorig : CapyCtx s1} {Γsub : CapyCtx s1'} {scOrig : SrcCtx s1 s2} {scSub : SrcCtx s1' s2'}
    {σ : CapySubst s1 s1'} {σt : Subst s2 s2'}
    (hΓO : Γorig.IsClosed) (hΓS : Γsub.IsClosed)
    (haO : SrcAligned Γorig scOrig) (haS : SrcAligned Γsub scSub)
    (h : SubstCompat scSub scOrig σ σt)
    {cs : CapyCaptureSet s1} (hcs : cs.IsClosed) (hsub : (CapyCaptureSet.subst cs σ).IsClosed) :
    CapyCaptureSet.compile (CapyCaptureSet.peaks Γsub (CapyCaptureSet.subst cs σ)) scSub
      = (CapyCaptureSet.compile (CapyCaptureSet.peaks Γorig cs) scOrig).subst σt := by
  rw [CapyCaptureSet.compile_peaks hΓS haS hsub, CapyCaptureSet.compile_subst h hcs,
      ← CapyCaptureSet.compile_peaks hΓO haO hcs]

/-! ### Converse of `peakSepCtx_HasTwoDistinct` — distinct peak cvars are separable

The lock `Satisfy`'s cross pairs separate via `sep_lock`, which needs
`HasTwoDistinct` of the in-context lock's items.  These foldl-position lemmas
show that two items at *distinct list positions* of a `peakSepCtx` fold are
`HasTwoDistinct`; for `peakCvars` (a `dedup`) distinct cvars give distinct
positions. -/

/-- `HasTwoDistinct` survives extending the accumulator by more folded items. -/
theorem SepCtx.HasTwoDistinct.foldl_mono {α : Type} {s : Sig} {g : α → CaptureSet s}
    {C1 C2 : CaptureSet s} (L : List α) :
    ∀ {acc : SepCtx s}, SepCtx.HasTwoDistinct acc C1 C2 →
      SepCtx.HasTwoDistinct (L.foldl (fun K c => .cons K (g c)) acc) C1 C2 := by
  induction L with
  | nil => intro acc h; exact h
  | cons c L' ih => intro acc h; exact ih h.there

/-- `Has` survives extending the accumulator by more folded items. -/
theorem SepCtx.Has.foldl_mono {α : Type} {s : Sig} {g : α → CaptureSet s} {C : CaptureSet s}
    (L : List α) :
    ∀ {acc : SepCtx s}, SepCtx.Has acc C →
      SepCtx.Has (L.foldl (fun K c => .cons K (g c)) acc) C := by
  induction L with
  | nil => intro acc h; exact h
  | cons c L' ih => intro acc h; exact ih h.there

/-- Every list element's image is `Has` in the fold. -/
theorem SepCtx.Has.foldl_mem {α : Type} {s : Sig} {g : α → CaptureSet s} {a : α}
    (L : List α) :
    a ∈ L → ∀ {acc : SepCtx s}, SepCtx.Has (L.foldl (fun K c => .cons K (g c)) acc) (g a) := by
  induction L with
  | nil => intro ha; simp at ha
  | cons c L' ih =>
    intro ha acc
    rcases List.mem_cons.mp ha with rfl | hmem
    · exact SepCtx.Has.foldl_mono L' SepCtx.Has.here
    · exact ih hmem

/-- An accumulator member and a later list element are `HasTwoDistinct`. -/
theorem SepCtx.HasTwoDistinct.foldl_acc {α : Type} {s : Sig} {g : α → CaptureSet s}
    {C1 : CaptureSet s} {a : α} (L : List α) :
    a ∈ L → ∀ {acc : SepCtx s}, SepCtx.Has acc C1 →
      SepCtx.HasTwoDistinct (L.foldl (fun K c => .cons K (g c)) acc) C1 (g a) := by
  induction L with
  | nil => intro ha; simp at ha
  | cons c L' ih =>
    intro ha acc hC1
    rcases List.mem_cons.mp ha with rfl | hmem
    · exact SepCtx.HasTwoDistinct.foldl_mono L' (SepCtx.HasTwoDistinct.here_there hC1).symm
    · exact ih hmem hC1.there

/-- Two distinct list elements give `HasTwoDistinct` images in the fold. -/
theorem SepCtx.HasTwoDistinct.foldl {α : Type} {s : Sig} {g : α → CaptureSet s} {a b : α}
    (L : List α) :
    a ∈ L → b ∈ L → a ≠ b →
    ∀ {acc : SepCtx s},
      SepCtx.HasTwoDistinct (L.foldl (fun K c => .cons K (g c)) acc) (g a) (g b) := by
  induction L with
  | nil => intro ha _ _; simp at ha
  | cons c L' ih =>
    intro ha hb hab acc
    rcases List.mem_cons.mp ha with rfl | haL'
    · rcases List.mem_cons.mp hb with rfl | hbL'
      · exact absurd rfl hab
      · exact SepCtx.HasTwoDistinct.foldl_acc L' hbL' SepCtx.Has.here
    · rcases List.mem_cons.mp hb with rfl | hbL'
      · exact (SepCtx.HasTwoDistinct.foldl_acc L' haL' SepCtx.Has.here).symm
      · exact ih haL' hbL' hab

/-- **Converse of `peakSepCtx_HasTwoDistinct`.**  Two distinct peak cvars give
    `HasTwoDistinct` compiled `peakItem`s — the `sep_lock` premise for cross pairs. -/
theorem peakSepCtx_HasTwoDistinct_of {s1 s2 : Sig} {P : CapyPeakSet s1} {sc : SrcCtx s1 s2}
    {c1 c2 : BVar s1 .cvar} (hc1 : c1 ∈ peakCvars P) (hc2 : c2 ∈ peakCvars P) (hne : c1 ≠ c2) :
    SepCtx.HasTwoDistinct (peakSepCtx P sc)
      (CapyCaptureSet.compile (peakItem P c1) sc) (CapyCaptureSet.compile (peakItem P c2) sc) := by
  simp only [peakSepCtx]
  exact SepCtx.HasTwoDistinct.foldl
    (g := fun c => CapyCaptureSet.compile (peakItem P c) sc) (peakCvars P) hc1 hc2 hne

/-- `SepCtx.subst` distributes over a `foldl`-built context (push the subst inside). -/
theorem SepCtx.subst_foldl {α : Type} {s1 s2 : Sig} {g : α → CaptureSet s1} {σt : Subst s1 s2}
    (L : List α) :
    ∀ {acc : SepCtx s1}, (L.foldl (fun K c => SepCtx.cons K (g c)) acc).subst σt
      = L.foldl (fun K c => SepCtx.cons K ((g c).subst σt)) (acc.subst σt) := by
  induction L with
  | nil => intro acc; rfl
  | cons c L' ih => intro acc; exact ih

/-- The substituted compiled lock is itself a `peakSepCtx`-style fold with the items
    substituted — so the foldl `HasTwoDistinct` machinery applies to `Ψ_R`. -/
theorem peakSepCtx_subst {s1 s2 s2' : Sig} {P : CapyPeakSet s1} {sc : SrcCtx s1 s2}
    {σt : Subst s2 s2'} :
    (peakSepCtx P sc).subst σt
      = (peakCvars P).foldl
          (fun K c => SepCtx.cons K ((CapyCaptureSet.compile (peakItem P c) sc).subst σt))
          SepCtx.empty := by
  simp only [peakSepCtx]
  rw [SepCtx.subst_foldl]
  rfl

/-- **Converse for the substituted lock `Ψ_R`.**  Distinct peak cvars give
    `HasTwoDistinct` *substituted* items — the `sep_lock` premise against the
    in-context merged lock. -/
theorem peakSepCtx_subst_HasTwoDistinct_of {s1 s2 s2' : Sig} {P : CapyPeakSet s1}
    {sc : SrcCtx s1 s2} {σt : Subst s2 s2'} {c1 c2 : BVar s1 .cvar}
    (hc1 : c1 ∈ peakCvars P) (hc2 : c2 ∈ peakCvars P) (hne : c1 ≠ c2) :
    SepCtx.HasTwoDistinct ((peakSepCtx P sc).subst σt)
      ((CapyCaptureSet.compile (peakItem P c1) sc).subst σt)
      ((CapyCaptureSet.compile (peakItem P c2) sc).subst σt) := by
  rw [peakSepCtx_subst]
  exact SepCtx.HasTwoDistinct.foldl
    (g := fun c => (CapyCaptureSet.compile (peakItem P c) sc).subst σt) (peakCvars P) hc1 hc2 hne

/-! ### Capture-variable injectivity of a source→target map

The compiled function-lock separation discipline (`sep_droppable`) requires that
distinct source capture peaks map to *distinct* target capture variables — i.e.
the source→target map is injective on cvars.  Every compiler-built `srcCtx` is
(fresh cvars are introduced 1:1); this records the invariant and its preservation
under the relevant context builders. -/

/-- A source→target map is injective on capture variables. -/
def SrcCtx.CVarInjective {s1 s2 : Sig} (sc : SrcCtx s1 s2) : Prop :=
  ∀ {c1 c2 : BVar s1 .cvar}, sc.lookupCVar c1 = sc.lookupCVar c2 → c1 = c2

/-- Injectivity is preserved by an injective target renaming. -/
theorem SrcCtx.CVarInjective.rename {s1 s2 s2' : Sig} {sc : SrcCtx s1 s2}
    (h : sc.CVarInjective) {ρ : Rename s2 s2'} (hρ : ρ.Injective) :
    (sc.rename ρ).CVarInjective := by
  intro c1 c2 he
  rw [SrcCtx.lookupCVar_rename, SrcCtx.lookupCVar_rename] at he
  exact h (hρ .cvar he)

/-- Injectivity is preserved by a fresh `.here` cvar binder over a `succ`-renamed
    (hence all-`.there`-image) tail — the compiler's source-cvar-binder pattern. -/
theorem SrcCtx.CVarInjective.consCVarHere {s1 s2 : Sig} {sc : SrcCtx s1 s2}
    (h : sc.CVarInjective) :
    (SrcCtx.cons (.cvar (BVar.here)) (sc.rename Rename.succ)).CVarInjective := by
  intro c1 c2 he
  cases c1 with
  | here =>
    cases c2 with
    | here => rfl
    | there c2' =>
      simp only [SrcCtx.lookupCVar, SrcCtx.lookupCVar_rename, Rename.succ] at he; cases he
  | there c1' =>
    cases c2 with
    | here =>
      simp only [SrcCtx.lookupCVar, SrcCtx.lookupCVar_rename, Rename.succ] at he; cases he
    | there c2' =>
      simp only [SrcCtx.lookupCVar, SrcCtx.lookupCVar_rename, Rename.succ] at he
      exact congrArg BVar.there (h (BVar.there.inj he))

/-- Injectivity is preserved by a fresh *type*-variable binder (cvars stay `.there`). -/
theorem SrcCtx.CVarInjective.consTVar {s1 s2 : Sig} {sc : SrcCtx s1 s2}
    (h : sc.CVarInjective) {X : BVar s2 .tvar} :
    (SrcCtx.cons (.tvar X) sc).CVarInjective := by
  intro c1 c2 he
  cases c1 with
  | there c1' =>
    cases c2 with
    | there c2' => simp only [SrcCtx.lookupCVar] at he; exact congrArg BVar.there (h he)

/-- Injectivity is preserved by a fresh *term*-variable binder (cvars stay `.there`). -/
theorem SrcCtx.CVarInjective.consVar {s1 s2 : Sig} {sc : SrcCtx s1 s2}
    (h : sc.CVarInjective) {bv : Option (BVar s2 .var)} {cs : CaptureSet s2} :
    (SrcCtx.cons (.var bv cs) sc).CVarInjective := by
  intro c1 c2 he
  cases c1 with
  | there c1' =>
    cases c2 with
    | there c2' => simp only [SrcCtx.lookupCVar] at he; exact congrArg BVar.there (h he)

/-! ### Inversion: distinct `HasTwoDistinct` items of a `peakSepCtx` are distinct peaks

The `sep_droppable` dispatch needs the two lock items `C1, C2` (which
`peakSepCtx_HasTwoDistinct` already identifies as `g c1, g c2`) to come from
*distinct* peak cvars `c1 ≠ c2`.  Since `peakCvars` is a `dedup` (NoDup), distinct
fold positions give distinct elements; this is the position-tracking inverse of
`SepCtx.HasTwoDistinct.foldl`. -/

/-- The local `dedup` produces a `Nodup` list. -/
theorem dedup_nodup {α : Type} [DecidableEq α] (l : List α) : (dedup l).Nodup := by
  induction l with
  | nil => exact List.nodup_nil
  | cons a as ih =>
    simp only [dedup]
    split
    · exact ih
    · rename_i hnotin; exact List.nodup_cons.mpr ⟨hnotin, ih⟩

/-- `peakCvars` is `Nodup`. -/
theorem peakCvars_nodup {s : Sig} (P : CapyPeakSet s) : (peakCvars P).Nodup :=
  dedup_nodup _

/-- A member of a `g`-fold over `L` (from `.empty`) is the `g`-image of some `c ∈ L`. -/
theorem SepCtx.Has.foldl_empty_inv {α : Type} {s : Sig} {g : α → CaptureSet s} (L : List α) :
    ∀ {acc : SepCtx s} {C : CaptureSet s},
      SepCtx.Has (L.foldl (fun K c => SepCtx.cons K (g c)) acc) C →
      SepCtx.Has acc C ∨ ∃ c ∈ L, C = g c := by
  induction L with
  | nil => intro acc C h; exact Or.inl h
  | cons c L' ih =>
    intro acc C h
    rw [List.foldl_cons] at h
    rcases ih h with h' | ⟨c', hc', he⟩
    · cases h' with
      | here => exact Or.inr ⟨c, List.mem_cons_self, rfl⟩
      | there h'' => exact Or.inl h''
    · exact Or.inr ⟨c', List.mem_cons_of_mem _ hc', he⟩

/-- A `g`-fold over `L` (from `.empty`) that equals `.cons K0 C` exhibits `L` as a
    snoc `L0 ++ [c']` with `K0` the fold of `L0` and `C = g c'`. -/
theorem foldl_empty_eq_cons_inv {α : Type} {s : Sig} {g : α → CaptureSet s} {L : List α}
    {K0 : SepCtx s} {C : CaptureSet s}
    (h : L.foldl (fun K c => SepCtx.cons K (g c)) SepCtx.empty = SepCtx.cons K0 C) :
    ∃ (L0 : List α) (c' : α), L = L0 ++ [c'] ∧
      K0 = L0.foldl (fun K c => SepCtx.cons K (g c)) SepCtx.empty ∧ C = g c' := by
  rcases List.eq_nil_or_concat L with rfl | ⟨L0, c', rfl⟩
  · rw [List.foldl_nil] at h; cases h
  · rw [List.concat_eq_append, List.foldl_append, List.foldl_cons, List.foldl_nil] at h
    injection h with hK hC
    refine ⟨L0, c', ?_, hK.symm, hC.symm⟩
    rw [List.concat_eq_append]

/-- **Position-tracking inverse of `HasTwoDistinct.foldl`.**  Two `HasTwoDistinct`
    items of a `g`-fold over a `Nodup` list are the `g`-images of two *distinct*
    list elements (up to swapping). -/
theorem SepCtx.HasTwoDistinct.foldl_nodup {α : Type} {s : Sig} {g : α → CaptureSet s}
    {K : SepCtx s} {C1 C2 : CaptureSet s} (h : SepCtx.HasTwoDistinct K C1 C2) :
    ∀ (L : List α), L.Nodup → K = L.foldl (fun K c => SepCtx.cons K (g c)) SepCtx.empty →
      ∃ c1 ∈ L, ∃ c2 ∈ L, c1 ≠ c2 ∧
        ((C1 = g c1 ∧ C2 = g c2) ∨ (C1 = g c2 ∧ C2 = g c1)) := by
  induction h with
  | @here_there K0 C2v C1v hHas =>
    intro L hnd hK
    obtain ⟨L0, c', hL, hK0, hC1⟩ := foldl_empty_eq_cons_inv hK.symm
    subst hL
    have hnotin : c' ∉ L0 := by
      have hdisj := (List.nodup_append.mp hnd).2.2
      intro hc; exact hdisj c' hc c' (by simp) rfl
    rcases SepCtx.Has.foldl_empty_inv L0 (hK0 ▸ hHas) with hemp | ⟨c2, hc2, he2⟩
    · cases hemp
    · refine ⟨c', List.mem_append_right _ (by simp), c2, List.mem_append_left _ hc2, ?_,
        Or.inl ⟨hC1, he2⟩⟩
      intro heq; subst heq; exact hnotin hc2
  | @there K0 C1v C2v Cv _ ih =>
    intro L hnd hK
    obtain ⟨L0, c', hL, hK0, _⟩ := foldl_empty_eq_cons_inv hK.symm
    subst hL
    have hnd0 : L0.Nodup := (List.nodup_append.mp hnd).1
    obtain ⟨c1, hc1, c2, hc2, hne, hdisj⟩ := ih L0 hnd0 hK0
    exact ⟨c1, List.mem_append_left _ hc1, c2, List.mem_append_left _ hc2, hne, hdisj⟩
  | @symm K0 C1v C2v _ ih =>
    intro L hnd hK
    obtain ⟨c1, hc1, c2, hc2, hne, hdisj⟩ := ih L hnd hK
    refine ⟨c1, hc1, c2, hc2, hne, ?_⟩
    rcases hdisj with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · exact Or.inr ⟨hb, ha⟩
    · exact Or.inl ⟨hb, ha⟩

/-- **Distinct lock items come from distinct peaks.**  Strengthens
    `peakSepCtx_HasTwoDistinct` with `c1 ≠ c2` (needed for the `sep_droppable`
    dispatch), via the `Nodup`ness of `peakCvars`. -/
theorem peakSepCtx_HasTwoDistinct_ne {s1 s2 : Sig} {P : CapyPeakSet s1} {sc : SrcCtx s1 s2}
    {C1 C2 : CaptureSet s2} (h : SepCtx.HasTwoDistinct (peakSepCtx P sc) C1 C2) :
    ∃ c1 ∈ peakCvars P, ∃ c2 ∈ peakCvars P, c1 ≠ c2 ∧
      ((C1 = CapyCaptureSet.compile (peakItem P c1) sc ∧
          C2 = CapyCaptureSet.compile (peakItem P c2) sc) ∨
       (C1 = CapyCaptureSet.compile (peakItem P c2) sc ∧
          C2 = CapyCaptureSet.compile (peakItem P c1) sc)) :=
  SepCtx.HasTwoDistinct.foldl_nodup (g := fun c => CapyCaptureSet.compile (peakItem P c) sc) h
    (peakCvars P) (peakCvars_nodup P) rfl

/-! ### Target-level atom-tracing (the `hsep` dispatch's plumbing)

The lock `Satisfy`'s separation half traces a peak of the *substituted* compiled
set back through the target substitution `σt` to an origin cvar of the
*un-substituted* compiled set.  Three structural membership lemmas underlie this. -/

/-- Substitution is monotone with respect to the syntactic subset relation.
    (Local copy; the `Denotation`-layer version is not in this import closure.) -/
theorem CaptureSet.Subset.subst {s1 s2 : Sig} {C1 C2 : CaptureSet s1}
    {σ : Subst s1 s2} (h : C1 ⊆ C2) : C1.subst σ ⊆ C2.subst σ := by
  induction h with
  | refl => exact .refl
  | empty => exact .empty
  | union_left _ _ ih1 ih2 => exact .union_left ih1 ih2
  | union_right_left _ ih => exact .union_right_left ih
  | union_right_right _ ih => exact .union_right_right ih

/-- **(L1) A target cvar atom of `X.subst σt` traces to a cvar atom of `X`** plus
    its `applyAccess`-image membership.  (A var atom of `X` substitutes to a var
    atom, never a cvar, so the source atom is always a cvar.) -/
theorem CaptureSet.subst_cvar_subset_inv {s1 s2 : Sig} {X : CaptureSet s1}
    {σt : Subst s1 s2} {a : Access} {Y : BVar s2 .cvar}
    (h : (CaptureSet.cvar a Y) ⊆ X.subst σt) :
    ∃ (Z : BVar s1 .cvar) (m : Access),
      (CaptureSet.cvar m Z) ⊆ X ∧
      (CaptureSet.cvar a Y) ⊆ (σt.cvar Z).applyAccess m := by
  induction X with
  | empty => simp only [CaptureSet.subst] at h; cases h
  | union X1 X2 ih1 ih2 =>
    simp only [CaptureSet.subst] at h
    cases h with
    | union_right_left h1 =>
      obtain ⟨Z, m, hZ, hsub⟩ := ih1 h1; exact ⟨Z, m, .union_right_left hZ, hsub⟩
    | union_right_right h2 =>
      obtain ⟨Z, m, hZ, hsub⟩ := ih2 h2; exact ⟨Z, m, .union_right_right hZ, hsub⟩
  | cvar m Z => exact ⟨Z, m, CaptureSet.Subset.refl, h⟩
  | var m x => simp only [CaptureSet.subst] at h; cases h

/-- A cvar atom of `D.applyRO` comes from a cvar atom of `D` (same cvar). -/
theorem CaptureSet.cvar_mem_applyRO_inv {s : Sig} {a : Access} {c : BVar s .cvar}
    {D : CaptureSet s} (hsub : (CaptureSet.cvar a c) ⊆ D.applyRO) :
    ∃ a0, (CaptureSet.cvar a0 c) ⊆ D := by
  induction D with
  | empty => simp only [CaptureSet.applyRO] at hsub; cases hsub
  | union D1 D2 ih1 ih2 =>
    simp only [CaptureSet.applyRO] at hsub
    cases hsub with
    | union_right_left h => obtain ⟨a0, hm⟩ := ih1 h; exact ⟨a0, .union_right_left hm⟩
    | union_right_right h => obtain ⟨a0, hm⟩ := ih2 h; exact ⟨a0, .union_right_right hm⟩
  | var m' x => simp only [CaptureSet.applyRO] at hsub; cases hsub
  | cvar m' c' => simp only [CaptureSet.applyRO] at hsub; cases hsub; exact ⟨m', .refl⟩

/-- A cvar atom of `D.applyDrop` comes from a cvar atom of `D` (same cvar). -/
theorem CaptureSet.cvar_mem_applyDrop_inv {s : Sig} {a : Access} {c : BVar s .cvar}
    {D : CaptureSet s} (hsub : (CaptureSet.cvar a c) ⊆ D.applyDrop) :
    ∃ a0, (CaptureSet.cvar a0 c) ⊆ D := by
  induction D with
  | empty => simp only [CaptureSet.applyDrop] at hsub; cases hsub
  | union D1 D2 ih1 ih2 =>
    simp only [CaptureSet.applyDrop] at hsub
    cases hsub with
    | union_right_left h => obtain ⟨a0, hm⟩ := ih1 h; exact ⟨a0, .union_right_left hm⟩
    | union_right_right h => obtain ⟨a0, hm⟩ := ih2 h; exact ⟨a0, .union_right_right hm⟩
  | var m' x => simp only [CaptureSet.applyDrop] at hsub; cases hsub
  | cvar m' c' => simp only [CaptureSet.applyDrop] at hsub; cases hsub; exact ⟨m', .refl⟩

/-- **(L2) `applyAccess` preserves cvar membership.**  A cvar atom of `D.applyAccess m`
    occurs (at some access mode) in `D` itself — both `applyMut` and `applyDrop`
    keep the cvar, changing only the access annotation. -/
theorem CaptureSet.cvar_subset_applyAccess_inv {s : Sig} {D : CaptureSet s} {a m : Access}
    {Y : BVar s .cvar} (h : (CaptureSet.cvar a Y) ⊆ D.applyAccess m) :
    ∃ a', (CaptureSet.cvar a' Y) ⊆ D := by
  cases m with
  | M m0 =>
    cases m0 with
    | epsilon =>
      simp only [CaptureSet.applyAccess_M, CaptureSet.applyMut_epsilon] at h; exact ⟨a, h⟩
    | ro =>
      simp only [CaptureSet.applyAccess_M, CaptureSet.applyMut_ro] at h
      exact CaptureSet.cvar_mem_applyRO_inv h
  | drop =>
    simp only [CaptureSet.applyAccess_drop] at h
    exact CaptureSet.cvar_mem_applyDrop_inv h

/-- **(L3) A cvar atom of `cs` is a peak.**  The target `peaks` keeps cvar atoms
    verbatim, so any cvar atom of `cs` occurs in `peaks Γ cs`. -/
theorem CaptureSet.cvar_subset_peaks {s : Sig} {Γ : Ctx s} {cs : CaptureSet s}
    {a : Access} {Y : BVar s .cvar} (h : (CaptureSet.cvar a Y) ⊆ cs) :
    (CaptureSet.cvar a Y) ⊆ CaptureSet.peaks Γ cs := by
  induction cs with
  | empty => cases h
  | union cs1 cs2 ih1 ih2 =>
    have hpk : CaptureSet.peaks Γ (cs1.union cs2)
        = CaptureSet.peaks Γ cs1 ∪ CaptureSet.peaks Γ cs2 := by
      conv_lhs => unfold CaptureSet.peaks
    rw [hpk]
    cases h with
    | union_right_left h1 => exact .union_right_left (ih1 h1)
    | union_right_right h2 => exact .union_right_right (ih2 h2)
  | cvar m c =>
    have hpk : CaptureSet.peaks Γ (CaptureSet.cvar m c) = CaptureSet.cvar m c := by
      conv_lhs => unfold CaptureSet.peaks
    rw [hpk]; exact h
  | var m x => cases h

/-! ### `peakItem` internals + droppability weakening

Atom-level facts about `peakItem`/`accessedAt` (a peak item is exactly the
`P.cs`-occurrences of one cvar) plus the transport of `TwoDistinctDroppable`
through a binder, used by the `hsep` atom dispatch. -/

/-- A peak item consists only of capture-variable atoms. -/
theorem peakItem_peaksOnly {s : Sig} {P : CapyPeakSet s} {c : BVar s .cvar} :
    (peakItem P c).PeaksOnly := by
  simp only [peakItem]
  generalize accessedAt P c = l
  induction l with
  | nil => exact CapyCaptureSet.PeaksOnly.empty
  | cons a as ih =>
    simp only [List.foldr_cons]
    exact CapyCaptureSet.PeaksOnly.union CapyCaptureSet.PeaksOnly.cvar ih

/-- An access mode recorded in `accessedAt.go c cs` witnesses a `.cvar`-occurrence
    of `c` in `cs`. -/
theorem accessedAt_go_subset {s : Sig} {c : BVar s .cvar} {a : Access} (cs : CapyCaptureSet s)
    (h : a ∈ accessedAt.go c cs) : (CapyCaptureSet.cvar a c) ⊆ cs := by
  induction cs with
  | empty => simp only [accessedAt.go] at h; cases h
  | union cs1 cs2 ih1 ih2 =>
    simp only [accessedAt.go, List.mem_append] at h
    rcases h with h1 | h2
    · exact .union_right_left (ih1 h1)
    · exact .union_right_right (ih2 h2)
  | cvar a' c' =>
    simp only [accessedAt.go] at h
    split at h
    · rename_i hcc; subst hcc; simp only [List.mem_singleton] at h; subst h; exact .refl
    · simp only [List.not_mem_nil] at h
  | var a' x => simp only [accessedAt.go] at h; cases h

/-- Conversely, a `.cvar`-occurrence of `c` in `cs` records its mode in
    `accessedAt.go c cs`. -/
theorem accessedAt_go_mem {s : Sig} {c : BVar s .cvar} {a : Access} (cs : CapyCaptureSet s)
    (h : (CapyCaptureSet.cvar a c) ⊆ cs) : a ∈ accessedAt.go c cs := by
  induction cs with
  | empty => cases h
  | union cs1 cs2 ih1 ih2 =>
    simp only [accessedAt.go, List.mem_append]
    cases h with
    | union_right_left h1 => exact Or.inl (ih1 h1)
    | union_right_right h2 => exact Or.inr (ih2 h2)
  | cvar a' c' =>
    cases h
    simp [accessedAt.go]
  | var a' x => cases h

/-- Every atom of a peak item is at the indexed cvar, and witnesses an occurrence
    in `P.cs`. -/
theorem peakItem_atom {s : Sig} {P : CapyPeakSet s} {d e : BVar s .cvar} {a : Access}
    (h : (CapyCaptureSet.cvar a e) ⊆ peakItem P d) :
    e = d ∧ (CapyCaptureSet.cvar a d) ⊆ P.cs := by
  simp only [peakItem] at h
  have hfold : ∀ (l : List Access),
      (CapyCaptureSet.cvar a e) ⊆ l.foldr (fun a' acc => CapyCaptureSet.cvar a' d ∪ acc) .empty →
      e = d ∧ a ∈ l := by
    intro l
    induction l with
    | nil => intro hh; cases hh
    | cons a' l' ih =>
      intro hh
      simp only [List.foldr_cons] at hh
      cases hh with
      | union_right_left h1 => cases h1; exact ⟨rfl, List.mem_cons_self⟩
      | union_right_right h2 => obtain ⟨he, hmem⟩ := ih h2; exact ⟨he, List.mem_cons_of_mem _ hmem⟩
  obtain ⟨he, hmem⟩ := hfold _ h
  subst he
  exact ⟨rfl, accessedAt_go_subset _ (by simpa only [accessedAt] using hmem)⟩

/-- A `.cvar`-occurrence of `c` in `P.cs` belongs to the peak item of `c`. -/
theorem cvar_subset_peakItem {s : Sig} {P : CapyPeakSet s} {c : BVar s .cvar} {a : Access}
    (h : (CapyCaptureSet.cvar a c) ⊆ P.cs) : (CapyCaptureSet.cvar a c) ⊆ peakItem P c := by
  simp only [peakItem]
  have hmem : a ∈ accessedAt P c := by simpa only [accessedAt] using accessedAt_go_mem _ h
  simp only [accessedAt] at hmem ⊢
  generalize accessedAt.go c P.cs = l at hmem
  induction l with
  | nil => cases hmem
  | cons a' l' ih =>
    simp only [List.foldr_cons]
    rcases List.mem_cons.mp hmem with rfl | hmem'
    · exact .union_right_left .refl
    · exact .union_right_right (ih hmem')

/-- The local `dedup` keeps membership. -/
theorem mem_dedup {α : Type} [DecidableEq α] {a : α} {l : List α} (h : a ∈ l) : a ∈ dedup l := by
  induction l with
  | nil => cases h
  | cons b bs ih =>
    simp only [dedup]
    rcases List.mem_cons.mp h with rfl | hmem
    · split
      · rename_i hb; exact hb
      · exact List.mem_cons_self
    · have hd := ih hmem
      split
      · exact hd
      · exact List.mem_cons_of_mem _ hd

/-- A `.cvar`-occurrence of `c` records `c` in `peakCvars.go cs`. -/
theorem cvar_subset_peakCvars_go {s : Sig} {c : BVar s .cvar} {a : Access} (cs : CapyCaptureSet s)
    (h : (CapyCaptureSet.cvar a c) ⊆ cs) : c ∈ peakCvars.go cs := by
  induction cs with
  | empty => cases h
  | union cs1 cs2 ih1 ih2 =>
    simp only [peakCvars.go, List.mem_append]
    cases h with
    | union_right_left h1 => exact Or.inl (ih1 h1)
    | union_right_right h2 => exact Or.inr (ih2 h2)
  | cvar a' c' => cases h; simp [peakCvars.go]
  | var a' x => cases h

/-- A `.cvar`-occurrence of `c` puts `c` among the (deduplicated) peak cvars. -/
theorem cvar_mem_peakCvars {s : Sig} {P : CapyPeakSet s} {c : BVar s .cvar} {a : Access}
    (h : (CapyCaptureSet.cvar a c) ⊆ P.cs) : c ∈ peakCvars P := by
  simp only [peakCvars]
  exact mem_dedup (cvar_subset_peakCvars_go P.cs h)

/-- `TwoDistinctDroppable` transports through a fresh binder (`succ`-shift). -/
theorem Ctx.TwoDistinctDroppable.push {s : Sig} {Γ : Ctx s} {c1 c2 : BVar s .cvar} {k : Kind}
    (h : Γ.TwoDistinctDroppable c1 c2) (b : Binding s k) :
    (Γ.push b).TwoDistinctDroppable (.there c1) (.there c2) := by
  obtain ⟨h1, h2, hne⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · simp only [Ctx.lookup_authority]; exact h1
  · simp only [Ctx.lookup_authority]; exact h2
  · intro he; exact hne (BVar.there.inj he)

/-! ### Union-lift: atom-wise separation entails set separation

`sep_droppable`/`sep_lock` produce separation of single cvar *atoms*; the lock
items `C1, C2` are whole compiled `peakItem`s (unions of same-cvar atoms).  These
two lemmas lift atom-wise `SepCheck` to `SepCheck` of the whole (peaks-only) sets
via `sep_union`/`sep_symm`/`sep_empty`. -/

/-- A `PeaksOnly` right operand separates from a fixed left cvar atom as soon as
    every right atom does. -/
theorem SepCheck.of_cvar_atoms_left {s : Sig} {Γ : Ctx s} {a1 : Access} {c1 : BVar s .cvar}
    {C2 : CaptureSet s} (hpo2 : C2.PeaksOnly)
    (hatom : ∀ (a2 : Access) (c2 : BVar s .cvar), (CaptureSet.cvar a2 c2) ⊆ C2 →
      SepCheck Γ (CaptureSet.cvar a1 c1) (CaptureSet.cvar a2 c2)) :
    SepCheck Γ (CaptureSet.cvar a1 c1) C2 := by
  induction hpo2 with
  | empty => exact SepCheck.sep_symm SepCheck.sep_empty
  | @cvar m c => exact hatom m c CaptureSet.Subset.refl
  | union _ _ iha ihb =>
    refine SepCheck.sep_symm (SepCheck.sep_union ?_ ?_)
    · exact SepCheck.sep_symm (iha (fun a2 c2 h => hatom a2 c2 (.union_right_left h)))
    · exact SepCheck.sep_symm (ihb (fun a2 c2 h => hatom a2 c2 (.union_right_right h)))

/-- **Union-lift.**  Two `PeaksOnly` capture sets separate as soon as every pair of
    their cvar atoms separates. -/
theorem SepCheck.of_cvar_atoms {s : Sig} {Γ : Ctx s} {C1 C2 : CaptureSet s}
    (hpo1 : C1.PeaksOnly) (hpo2 : C2.PeaksOnly)
    (hatom : ∀ (a1 : Access) (c1 : BVar s .cvar) (a2 : Access) (c2 : BVar s .cvar),
      (CaptureSet.cvar a1 c1) ⊆ C1 → (CaptureSet.cvar a2 c2) ⊆ C2 →
      SepCheck Γ (CaptureSet.cvar a1 c1) (CaptureSet.cvar a2 c2)) :
    SepCheck Γ C1 C2 := by
  induction hpo1 with
  | empty => exact SepCheck.sep_empty
  | @cvar m c =>
    exact SepCheck.of_cvar_atoms_left hpo2 (fun a2 c2 h => hatom m c a2 c2 CaptureSet.Subset.refl h)
  | union _ _ iha ihb =>
    refine SepCheck.sep_union ?_ ?_
    · exact iha (fun a1 c1' a2 c2 h1 h2 => hatom a1 c1' a2 c2 (.union_right_left h1) h2)
    · exact ihb (fun a1 c1' a2 c2 h1 h2 => hatom a1 c1' a2 c2 (.union_right_right h1) h2)

/-- Reflexivity of target capture-bound subtyping (`.bound` via `Subcapt.refl`,
    `.unbound` via `top`).  The `cpoly`/`modal` bound premises reduce to this once
    the two compiled bounds are identified by `CapyCaptureBound.compile_subst`. -/
theorem Subbound.refl {s : Sig} {Γ : Ctx s} {cb : CaptureBound s} : Subbound Γ cb cb := by
  cases cb with
  | unbound => exact Subbound.top
  | bound C => exact Subbound.capset Subcapt.refl

/-- **`mutabilityCtx` at `.here` commutes with substitution.**  The mutability
    lock reads only the bound's *kind* (unbound vs bound) and, for `.unbound m`,
    its mutability label `m` — both preserved by `cb.subst σ` — and the freshly
    bound cvar `.here`, which `σt.lift` fixes.  So `σ` is irrelevant to the result
    and the equation holds for ANY `σt`.  The subst analogue of
    `CapyCaptureBound.mutabilityCtx_rename_here`; the `cpoly` lock's mutability
    half of `Satisfy`. -/
theorem CapyCaptureBound.mutabilityCtx_subst_here {s1 s1' s2 s2' : Sig}
    {cb : CapyCaptureBound s1} {σ : CapySubst s1 s1'} {σt : Subst s2 s2'} :
    CapyCaptureBound.mutabilityCtx (cb.subst σ) (.here : BVar (s2',,Kind.cvar) .cvar)
      = (CapyCaptureBound.mutabilityCtx cb (.here : BVar (s2,,Kind.cvar) .cvar)).subst σt.lift := by
  cases cb with
  | unbound m => rfl
  | bound cs => rfl

/-- **Type-level capture-opening commutes up to subtyping, both directions.**
    Stated `∀`-after-`T` (over the substitution data + contexts) so the recursive
    cases re-instantiate at lifted substitutions / extended contexts. -/
theorem CapyTy.compile_subst_subtyp {sort : CapyTySort} (T : CapyTy sort s1) :
    ∀ {s2 s1' s2' : Sig} {ctxOrig : CompilerCtx s1 s2} {ctxSub : CompilerCtx s1' s2'}
      {σ : CapySubst s1 s1'} {σt : Subst s2 s2'},
      SubstCompat ctxSub.srcCtx ctxOrig.srcCtx σ σt →
      SubstTvarCompat ctxSub.srcCtx ctxOrig.srcCtx σ σt → T.IsClosed → CapyTy.PureBounds T →
      TgtPairDroppable ctxSub.coreCtx σt →
      SrcAligned ctxSub.capyCtx ctxSub.srcCtx → SrcAligned ctxOrig.capyCtx ctxOrig.srcCtx →
      ctxSub.capyCtx.IsClosed → ctxOrig.capyCtx.IsClosed →
      Subst.IsClosed σt →
      ctxSub.srcCtx.VarsClosed → ctxOrig.srcCtx.VarsClosed →
      ctxSub.coreCtx.IsClosed →
      CapySubst.IsClosed σ →
      ctxSub.srcCtx.CVarInjective →
      Subtyp ctxSub.coreCtx (CapyTy.compile (T.subst σ) ctxSub)
        ((CapyTy.compile T ctxOrig).subst σt) ∧
      Subtyp ctxSub.coreCtx ((CapyTy.compile T ctxOrig).subst σt)
        (CapyTy.compile (T.subst σ) ctxSub) := by
  induction T with
  | top =>
    intro s2 s1' s2' ctxOrig ctxSub σ σt hcompat htvar hcl hpb hdrop haSub haOrig hclSub hclOrig
      hscl hvcSub hvcOrig hcoreSub hscS hinj
    simp only [CapyTy.subst, CapyTy.compile, Ty.subst]
    exact ⟨Subtyp.refl, Subtyp.refl⟩
  | unit =>
    intro s2 s1' s2' ctxOrig ctxSub σ σt hcompat htvar hcl hpb hdrop haSub haOrig hclSub hclOrig
      hscl hvcSub hvcOrig hcoreSub hscS hinj
    simp only [CapyTy.subst, CapyTy.compile, Ty.subst]
    exact ⟨Subtyp.refl, Subtyp.refl⟩
  | bool =>
    intro s2 s1' s2' ctxOrig ctxSub σ σt hcompat htvar hcl hpb hdrop haSub haOrig hclSub hclOrig
      hscl hvcSub hvcOrig hcoreSub hscS hinj
    simp only [CapyTy.subst, CapyTy.compile, Ty.subst]
    exact ⟨Subtyp.refl, Subtyp.refl⟩
  | cap cs =>
    intro s2 s1' s2' ctxOrig ctxSub σ σt hcompat htvar hcl hpb hdrop haSub haOrig hclSub hclOrig
      hscl hvcSub hvcOrig hcoreSub hscS hinj
    cases hcl with | cap hcs =>
    rw [CapyTy.compile_subst_cap hcompat hcs]
    exact ⟨Subtyp.refl, Subtyp.refl⟩
  | cell cs m =>
    intro s2 s1' s2' ctxOrig ctxSub σ σt hcompat htvar hcl hpb hdrop haSub haOrig hclSub hclOrig
      hscl hvcSub hvcOrig hcoreSub hscS hinj
    cases hcl with | cell hcs =>
    rw [CapyTy.compile_subst_cell hcompat hcs]
    exact ⟨Subtyp.refl, Subtyp.refl⟩
  | typ T1 ih =>
    intro s2 s1' s2' ctxOrig ctxSub σ σt hcompat htvar hcl hpb hdrop haSub haOrig hclSub hclOrig
      hscl hvcSub hvcOrig hcoreSub hscS hinj
    cases hcl with | typ hcl1 =>
    simp only [CapyTy.subst, CapyTy.compile, Ty.subst]
    obtain ⟨hle, hge⟩ := ih hcompat htvar hcl1 hpb hdrop haSub haOrig hclSub hclOrig
      hscl hvcSub hvcOrig hcoreSub hscS hinj
    exact ⟨Subtyp.typ hle, Subtyp.typ hge⟩
  | exi T1 ih =>
    intro s2 s1' s2' ctxOrig ctxSub σ σt hcompat htvar hcl hpb hdrop haSub haOrig hclSub hclOrig
      hscl hvcSub hvcOrig hcoreSub hscS hinj
    cases hcl with | exi hcl1 =>
    simp only [CapyTy.subst, CapyTy.compile, Ty.subst]
    obtain ⟨hle, hge⟩ := ih (ctxOrig := ctxOrig.weakenTarget.consCVar (.unbound .epsilon) .here)
      (ctxSub := ctxSub.weakenTarget.consCVar (.unbound .epsilon) .here)
      (SubstCompat.weakenConsCVar hcompat) (SubstTvarCompat.weakenConsCVar htvar) hcl1 hpb
      (TgtPairDroppable.lift hdrop)
      (SrcAligned.consCVar haSub.weakenTarget) (SrcAligned.consCVar haOrig.weakenTarget)
      (CapyCtx.IsClosed.push hclSub (CapyBinding.IsClosed.cvar CapyCaptureBound.IsClosed.unbound))
      (CapyCtx.IsClosed.push hclOrig (CapyBinding.IsClosed.cvar CapyCaptureBound.IsClosed.unbound))
      (Subst.lift_closed hscl) hvcSub.weaken.consCVar hvcOrig.weaken.consCVar
      (Ctx.IsClosed.push hcoreSub (Binding.IsClosed.cvar CaptureBound.IsClosed.unbound))
      (CapySubst.lift_closed hscS) (SrcCtx.CVarInjective.consCVarHere hinj)
    exact ⟨Subtyp.exi hle, Subtyp.exi hge⟩
  | tvar X =>
    intro s2 s1' s2' ctxOrig ctxSub σ σt hcompat htvar hcl hpb hdrop haSub haOrig hclSub hclOrig
      hscl hvcSub hvcOrig hcoreSub hscS hinj
    obtain ⟨Z, hZ, hlk⟩ := htvar X
    simp only [CapyTy.subst, hZ, CapyPureTy.tvar, CapyTy.compile, Ty.subst, hlk, PureTy.tvar]
    exact ⟨Subtyp.refl, Subtyp.refl⟩
  | arrow T1 cs E ihT1 ihE =>
    intro s2 s1' s2' ctxOrig ctxSub σ σt hcompat htvar hcl hpb hdrop haSub haOrig hclSub hclOrig
      hscl hvcSub hvcOrig hcoreSub hscS hinj
    -- ★ BLOCKED BY THE SAME GAP AS `cpoly` `satB`.  An arrow compiles to a `cpoly`/`cpoly`/
    -- `arrow`/`modal` nest; relating two such nests by `Subtyp` reaches `Subtyp.arrow`, whose
    -- DOMAIN premise is CONTRAVARIANT: the *forward* arrow obligation needs `ihT1.2` (the
    -- BACKWARD direction of the domain type).  That backward direction is exactly the
    -- merging-unstable lock subtyping documented at `cpoly`'s `satB` — so neither direction of
    -- `arrow` is dischargeable until the K1 lock-design decision is made.  (The structural
    -- scaffold mirrors `cpoly`: `Subtyp.cpoly`×2 / `Subtyp.arrow` / `Subtyp.modal` with the
    -- codomain `modal_modal` Satisfy being the load-bearing obligation.)
    sorry
  | poly S cs E ihS ihE =>
    intro s2 s1' s2' ctxOrig ctxSub σ σt hcompat htvar hcl hpb hdrop haSub haOrig hclSub hclOrig
      hscl hvcSub hvcOrig hcoreSub hscS hinj
    -- ★ BLOCKED BY THE SAME GAP AS `cpoly` `satB`.  Unlike `cpoly` (whose capture bound is an
    -- EQUALITY, `Subbound.refl`, so no contravariance), `poly`'s type bound `S` is genuinely
    -- CONTRAVARIANT: `Subtyp.poly` needs `Subtyp Γ S2.core S1.core`, i.e. `ihS.2` (the BACKWARD
    -- direction of `S`).  That backward direction is the merging-unstable lock subtyping
    -- (`cpoly`'s `satB`).  The forward Satisfy here is provable (a mirror of `cpoly` forward's
    -- hsep dispatch), but the case as a whole is gated on the K1 lock-design decision.
    sorry
  | cpoly cb cs E ihE =>
    intro s2 s1' s2' ctxOrig ctxSub σ σt hcompat htvar hcl hpb hdrop haSub haOrig hclSub hclOrig
      hscl hvcSub hvcOrig hcoreSub hscS hinj
    cases hcl with | cpoly hcb hcsCl hECl =>
    simp only [CapyTy.subst, CapyTy.compile, Ty.subst]
    rw [CapyCaptureBound.compile_subst hcompat hcb]
    refine ⟨?_, ?_⟩
    · -- forward: ⟦(cpoly cb cs E)[σ]⟧ <: ⟦cpoly cb cs E⟧[σt]
      refine Subtyp.cpoly Subbound.refl ?_ (Subtyp.typ ?_)
      · simp only [CaptureSet.subst]; exact Subcapt.refl
      · -- MODAL subtyping (forward).  `Cf_L = Cf_R` by `compile_subst`; then `trans`
        -- through `.modal Cf_R Ψ_L E_R`: `Subtyp.modal` (body `E_L<:E_R` via `ihE` at the
        -- real-bound lock-weakened ctx, bridged by `compile_eq_of`+`compile_rename`) then
        -- `Subtyp.modal_modal` (`Satisfy (push Ψ_R) (Ψ_L.rename succ)` via the Cover
        -- dispatch: split→`sep_droppable`, cross→`sep_lock`+`sep_mono`+`sep_symm` on the
        -- `compile_peaks_subst` keystone).  [B2c in-progress; structure + bound + Cf done.]
        have hCf :
            CapyCaptureSet.compile (CapyCaptureSet.subst cs σ)
                  (ctxSub.srcCtx.weaken (k := .cvar)) =
              (CapyCaptureSet.compile cs (ctxOrig.srcCtx.weaken (k := .cvar))).subst
                (σt.lift (k := .cvar)) :=
          CapyCaptureSet.compile_subst (SubstCompat.weakenTarget hcompat) hcsCl
        -- `Subtyp.modal` absorbs the `Cf_L = Cf_R` difference via its `Subcapt` premise
        -- (no `rw`, which trips on the projection-kind of `.weaken`).
        refine Subtyp.trans ?_ (Subtyp.modal (hCf ▸ Subcapt.refl) ?body)
          (Subtyp.modal_modal ?_ ?_ ?_ ?sat)
        -- (1) CLOSEDNESS of the intermediate `.modal Cf_R Ψ_L E_R`, (3) of `Γt`, (4) `Ψ_L`,
        -- (5) `Ψ_R`.  All four need the new premise `Subst.IsClosed σt` threaded through
        -- `compile_subst_subtyp` (dischargeable at the `fresh` use-site: `σt = openCVar ⟦Df⟧`
        -- with `Df` closed).  Then: `Ty.IsClosed.modal`/`compile_isClosed`/`peakSepCtx_isClosed`
        -- for the un-substituted shells + `*.is_closed_subst` (Substitution.lean) to push `σt`
        -- through.  `Γt.IsClosed` additionally needs `ctxSub.coreCtx.IsClosed` (a second new
        -- premise, or recovered from a coherence invariant on `CompilerCtx`).
        · exact Ty.IsClosed.modal
            (CaptureSet.is_closed_subst (CapyCaptureSet.compile_isClosed hcsCl hvcOrig.weaken)
              (Subst.lift_closed hscl))
            ⟨peakSepCtx_isClosed hvcSub.weaken, CapyCaptureBound.mutabilityCtx_isClosed⟩
            (Ty.is_closed_subst
              (CapyTy.compile_isClosed E (ctxOrig.weakenTarget.consCVar cb BVar.here) hECl
                hvcOrig.weaken.consCVar)
              (Subst.lift_closed hscl))
        -- (2) BODY `Subtyp (Γt.push_lock Ψ_L) (E_L.rename succ) (E_R.rename succ)`.
        -- PLAN (option b): no `Subtyp` renaming lemma exists, so instantiate `ihE` at RAW
        -- lock-pushed `succ`-renamed contexts (compile ignores coreCtx/dstCtx → real-bound
        -- `Γt.push_lock Ψ_L` coreCtx used directly); σ''=σ.lift, σt''=σt.lift.lift.  Premises
        -- compose from built builders (`.weakenConsCVar._.weakenTarget`, `hdrop.lift.lift`,
        -- Γlock-closed, `SrcAligned.consCVar._.weakenTarget`); conclusion→goal via `compile_rename`
        -- ×2 + `Ty.weaken_subst_comm`.
        -- ⚠ SNAG (premise-creep): ihE's `ctxSub''.capyCtx.IsClosed` needs `(cb.subst σ).IsClosed`
        -- (`push_cvar_default` keeps the REAL bound; `.bound C` needs SOURCE subst σ closed).  Fix
        -- (a) thread a 5th source-σ-closedness premise (dischargeable at fresh, σ=openCVar⟦Df⟧) →
        -- real capyCtx + compile_rename; or (b) placeholder `.unbound` capyCtx + `compile_eq_of`∘
        -- `compile_rename` bridge (cvar bounds don't affect peaks).  Either ~100 lines.
        case body =>
          set ΨL : ModalCtx (s2',,Kind.cvar) :=
            { sep := peakSepCtx (CapyCaptureSet.peakset ctxSub.capyCtx (CapyCaptureSet.subst cs σ))
                       ctxSub.srcCtx.weaken,
              mutability := CapyCaptureBound.mutabilityCtx (cb.subst σ) BVar.here } with hΨL
          set csub' := ctxSub.weakenTarget.consCVar (cb.subst σ) (BVar.here) with hcsub'
          set corig' := ctxOrig.weakenTarget.consCVar cb (BVar.here) with hcorig'
          -- The two lock-weakened compile contexts (explicit 4-field, so `.coreCtx`/`.srcCtx`
          -- reduce): ctxSub'' keeps the REAL-bound lock coreCtx (= the goal's context); ctxOrig''’s
          -- coreCtx is irrelevant to ihE's conclusion.
          set ctxSub'' : CompilerCtx (s1',C) ((s2',,Kind.cvar),,Kind.lock) :=
            ⟨csub'.capyCtx, csub'.srcCtx.rename Rename.succ,
             (csub'.weakenTarget (Binding.lock ΨL)).dstCtx,
             (ctxSub.coreCtx,C[Authority.access_only]<:(CapyCaptureBound.compile cb
               ctxOrig.srcCtx).subst σt).push_lock ΨL⟩ with hctxSub''
          set ctxOrig'' : CompilerCtx _ ((s2,,Kind.cvar),,Kind.lock) :=
            ⟨corig'.capyCtx, corig'.srcCtx.rename Rename.succ,
             (corig'.weakenTarget
               (Binding.lock (⟨SepCtx.empty, MutabilityCtx.empty⟩ : ModalCtx _))).dstCtx,
             corig'.coreCtx.push_lock (⟨SepCtx.empty, MutabilityCtx.empty⟩ : ModalCtx _)⟩
            with hctxOrig''
          have hle := (ihE (ctxSub := ctxSub'') (ctxOrig := ctxOrig'') (σ := σ.lift)
            (σt := σt.lift.lift)
            ((SubstCompat.weakenConsCVar hcompat).weakenTarget)
            ((SubstTvarCompat.weakenConsCVar htvar).weakenTarget)
            hECl hpb
            (TgtPairDroppable.liftLock (b := Binding.lock ΨL)
              (TgtPairDroppable.lift (b := Binding.cvar Authority.access_only
                ((CapyCaptureBound.compile cb ctxOrig.srcCtx).subst σt)) hdrop))
            (SrcAligned.weakenTarget (SrcAligned.consCVar (SrcAligned.weakenTarget haSub)))
            (SrcAligned.weakenTarget (SrcAligned.consCVar (SrcAligned.weakenTarget haOrig)))
            (CapyCtx.IsClosed.push hclSub (CapyBinding.IsClosed.cvar
              (CapyCaptureBound.is_closed_subst hcb hscS)))
            (CapyCtx.IsClosed.push hclOrig (CapyBinding.IsClosed.cvar hcb))
            (Subst.lift_closed (Subst.lift_closed hscl))
            hvcSub.weaken.consCVar.weaken hvcOrig.weaken.consCVar.weaken
            (Ctx.IsClosed.push
              (Ctx.IsClosed.push hcoreSub (Binding.IsClosed.cvar
                (CaptureBound.is_closed_subst
                  (CapyCaptureBound.compile_isClosed hcb hvcOrig) hscl)))
              (Binding.IsClosed.lock ⟨peakSepCtx_isClosed hvcSub.weaken,
                CapyCaptureBound.mutabilityCtx_isClosed⟩))
            (CapySubst.lift_closed hscS)
            (SrcCtx.CVarInjective.rename
              (SrcCtx.CVarInjective.consCVarHere hinj) Rename.injective_succ)).1
          -- Bridge the two compiled bodies to the goal forms.
          have heq1 : CapyTy.compile (E.subst σ.lift) ctxSub''
              = (CapyTy.compile (E.subst σ.lift) csub').rename Rename.succ :=
            CapyTy.compile_rename (E.subst σ.lift) csub' ctxSub'' Rename.succ rfl rfl
          have heq2 : CapyTy.compile E ctxOrig''
              = (CapyTy.compile E corig').rename Rename.succ :=
            CapyTy.compile_rename E corig' ctxOrig'' Rename.succ rfl rfl
          convert hle using 2
          · exact heq1.symm
          · rw [heq2]; exact Ty.weaken_subst_comm_base
        · exact Ctx.IsClosed.push hcoreSub (Binding.IsClosed.cvar
            (CaptureBound.is_closed_subst (CapyCaptureBound.compile_isClosed hcb hvcOrig) hscl))
        · exact ⟨peakSepCtx_isClosed hvcSub.weaken, CapyCaptureBound.mutabilityCtx_isClosed⟩
        · exact ModalCtx.is_closed_subst
            ⟨peakSepCtx_isClosed hvcOrig.weaken, CapyCaptureBound.mutabilityCtx_isClosed⟩
            (Subst.lift_closed hscl)
        case sat =>
          apply Satisfy.satisfy
          · -- (6a) hkind (MUTABILITY half) — DONE.  `mutabilityCtx_subst_here` makes
            -- `Ψ_L.mutability = Ψ_R.mutability`, so `hmem : (Ψ_R.mut.rename succ).Has C m`.  Split
            -- on `m`: `.epsilon` is universal (`HasKind.rw`); `.ro` reads the pushed lock
            -- (`HasKind.imm` + `LookupLock.here`, whose `Ψ_R.rename succ` matches `hmem`).
            intro C m hmem
            simp only [ModalCtx.rename] at hmem
            cases cb with
            | bound cs0 =>
              simp only [CapyCaptureBound.subst, CapyCaptureBound.mutabilityCtx,
                MutabilityCtx.rename] at hmem
              cases hmem
            | unbound m0 =>
              cases m with
              | epsilon => exact HasKind.rw
              | ro => exact HasKind.imm Ctx.LookupLock.here hmem
          · -- (6b) hsep (SEPARATION half — the DISPATCH, the real content).  Destructor below
            -- extracts `c1,c2 ∈ peakCvars (peaks Γsub (cs[σ]))` with `Cᵢ = ⟦peakItem _ cᵢ⟧ sc'`.
            -- REMAINING: trace each `cᵢ` (a peak of `cs[σ]`) to its origin peak `dᵢ` of `cs`
            -- (a NEW individual-peak, cross-context tracing lemma — `compile_peaks_subst` is the
            -- whole-SET keystone, too coarse; subst may SPLIT one peak of `cs` into many of
            -- `cs[σ]`, so no item-wise equality holds).  Then dispatch on `d1 =?= d2`:
            --   • distinct origins → `sep_lock` (pushed `Ψ_R` has `⟦d1⟧[σt],⟦d2⟧[σt]` distinct via
            --     `peakSepCtx_subst_HasTwoDistinct_of`) + `sep_mono`/`sep_symm` to shrink `Cᵢ` to
            --     its `dᵢ`-image piece;
            --   • same origin (split) → `sep_droppable` from `hdrop : TgtPairDroppable`.
            intro C1 C2 hdist
            simp only [ModalCtx.rename] at hdist
            rw [← peakSepCtx_rename] at hdist
            obtain ⟨c1, hc1, c2, hc2, hcne, hCdisj⟩ := peakSepCtx_HasTwoDistinct_ne hdist
            -- E1: the whole compiled peak-set commutes with `σt.lift` (inner level).
            have hE1 :
                CapyCaptureSet.compile
                    (CapyCaptureSet.peaks ctxSub.capyCtx (CapyCaptureSet.subst cs σ))
                    (ctxSub.srcCtx.weaken (k := Kind.cvar))
                  = (CapyCaptureSet.compile (CapyCaptureSet.peaks ctxOrig.capyCtx cs)
                      (ctxOrig.srcCtx.weaken (k := Kind.cvar))).subst (σt.lift (k := Kind.cvar)) :=
              CapyCaptureSet.compile_peaks_subst hclOrig hclSub
                (SrcAligned.weakenTarget (k := Kind.cvar) haOrig)
                (SrcAligned.weakenTarget (k := Kind.cvar) haSub)
                (SubstCompat.weakenTarget (k := Kind.cvar) hcompat) hcsCl
                (CapyCaptureSet.is_closed_subst hcsCl hscS)
            -- `scSub_w` is cvar-injective (the base map shifted once for the `C`-binder).
            have hinjW : (ctxSub.srcCtx.weaken (k := Kind.cvar)).CVarInjective :=
              SrcCtx.CVarInjective.rename hinj Rename.injective_succ
            -- Per-atom tracing: an atom of a compiled sub-peak-item factors back through
            -- `σt.lift` to an atom of the compiled orig peak-set, recording the target image.
            have traceAtom : ∀ (d : BVar s1' Kind.cvar)
                (Y : BVar ((s2',C),,Kind.lock) Kind.cvar) (a : Access),
                (CaptureSet.cvar a Y) ⊆ CapyCaptureSet.compile
                  (peakItem (CapyCaptureSet.peakset ctxSub.capyCtx (CapyCaptureSet.subst cs σ)) d)
                  ((ctxSub.srcCtx.weaken (k := Kind.cvar)).rename Rename.succ) →
                ∃ (Y' : BVar (s2',C) Kind.cvar) (Z : BVar (s2,C) Kind.cvar) (m : Access),
                  Y = BVar.there Y' ∧ (ctxSub.srcCtx.weaken (k := Kind.cvar)).lookupCVar d = Y' ∧
                  (CaptureSet.cvar m Z) ⊆ CapyCaptureSet.compile
                    (CapyCaptureSet.peaks ctxOrig.capyCtx cs)
                    (ctxOrig.srcCtx.weaken (k := Kind.cvar)) ∧
                  (CaptureSet.cvar a Y') ⊆ ((σt.lift (k := Kind.cvar)).cvar Z).applyAccess m := by
              intro d Y a hsub
              rw [CapyCaptureSet.compile_rename] at hsub
              obtain ⟨Y', hYeq, hsub'⟩ := CaptureSet.cvar_subset_rename_succ hsub
              obtain ⟨e, hlke, hsube⟩ :=
                CapyCaptureSet.compile_cvar_subset_inv peakItem_peaksOnly hsub'
              obtain ⟨hed, hsubP⟩ := peakItem_atom hsube
              subst hed
              have hmono :=
                CapyCaptureSet.compile_subset (sc := ctxSub.srcCtx.weaken (k := Kind.cvar)) hsubP
              have hcompc : CapyCaptureSet.compile (CapyCaptureSet.cvar a e)
                  (ctxSub.srcCtx.weaken (k := Kind.cvar)) = CaptureSet.cvar a Y' :=
                congrArg (CaptureSet.cvar a) hlke
              have hpcs : (CapyCaptureSet.peakset ctxSub.capyCtx (CapyCaptureSet.subst cs σ)).cs
                  = CapyCaptureSet.peaks ctxSub.capyCtx (CapyCaptureSet.subst cs σ) := rfl
              rw [hcompc, hpcs, hE1] at hmono
              obtain ⟨Z, m, hmZ, happ⟩ := CaptureSet.subst_cvar_subset_inv hmono
              exact ⟨Y', Z, m, hYeq, hlke, hmZ, happ⟩
            -- The key separation claim for two distinct sub-peaks.
            have key : ∀ (d1 d2 : BVar s1' Kind.cvar), d1 ≠ d2 →
                d1 ∈ peakCvars (CapyCaptureSet.peakset ctxSub.capyCtx (CapyCaptureSet.subst cs σ)) →
                d2 ∈ peakCvars (CapyCaptureSet.peakset ctxSub.capyCtx (CapyCaptureSet.subst cs σ)) →
                SepCheck
                  ((ctxSub.coreCtx,C[Authority.access_only]<:(CapyCaptureBound.compile cb
                      ctxOrig.srcCtx).subst σt).push_lock
                    (({ sep := peakSepCtx (CapyCaptureSet.peakset ctxOrig.capyCtx cs)
                          (ctxOrig.srcCtx.weaken (k := Kind.cvar)),
                        mutability := CapyCaptureBound.mutabilityCtx cb BVar.here } :
                      ModalCtx (s2,C)).subst σt.lift))
                  (CapyCaptureSet.compile
                    (peakItem (CapyCaptureSet.peakset ctxSub.capyCtx
                      (CapyCaptureSet.subst cs σ)) d1)
                    ((ctxSub.srcCtx.weaken (k := Kind.cvar)).rename Rename.succ))
                  (CapyCaptureSet.compile
                    (peakItem (CapyCaptureSet.peakset ctxSub.capyCtx
                      (CapyCaptureSet.subst cs σ)) d2)
                    ((ctxSub.srcCtx.weaken (k := Kind.cvar)).rename Rename.succ)) := by
              intro d1 d2 hne hd1 hd2
              refine SepCheck.of_cvar_atoms (CapyCaptureSet.compile_peaksOnly peakItem_peaksOnly)
                (CapyCaptureSet.compile_peaksOnly peakItem_peaksOnly) ?_
              intro a1 Y1 a2 Y2 hY1 hY2
              obtain ⟨Y1', Z1, m1, hY1eq, hlk1, hmZ1, happ1⟩ := traceAtom d1 Y1 a1 hY1
              obtain ⟨Y2', Z2, m2, hY2eq, hlk2, hmZ2, happ2⟩ := traceAtom d2 Y2 a2 hY2
              -- Y1 ≠ Y2 always: distinct sub-peaks map to distinct target cvars (injectivity).
              have hYne : Y1 ≠ Y2 := by
                subst hY1eq; subst hY2eq
                intro he
                exact hne (hinjW (by rw [hlk1, hlk2]; exact BVar.there.inj he))
              by_cases hZ : Z1 = Z2
              · -- SPLIT: both atoms come from the same `σt.lift`-image `Z`; `hdrop` separates.
                subst hZ
                obtain ⟨a1', hmem1⟩ := CaptureSet.cvar_subset_applyAccess_inv happ1
                obtain ⟨a2', hmem2⟩ := CaptureSet.cvar_subset_applyAccess_inv happ2
                have hY'ne : Y1' ≠ Y2' := by
                  intro he; exact hYne (by rw [hY1eq, hY2eq, he])
                have hdd := (hdrop.lift (b := Binding.cvar Authority.access_only
                    ((CapyCaptureBound.compile cb ctxOrig.srcCtx).subst σt)))
                    Z1 a1' a2' Y1' Y2' hY'ne
                    (CaptureSet.cvar_subset_peaks hmem1) (CaptureSet.cvar_subset_peaks hmem2)
                subst hY1eq; subst hY2eq
                exact SepCheck.sep_droppable (Ctx.TwoDistinctDroppable.push hdd (Binding.lock
                  (({ sep := peakSepCtx (CapyCaptureSet.peakset ctxOrig.capyCtx cs)
                        (ctxOrig.srcCtx.weaken (k := Kind.cvar)),
                      mutability := CapyCaptureBound.mutabilityCtx cb BVar.here } :
                    ModalCtx (s2,C)).subst σt.lift)))
              · -- DISTINCT ORIGIN: the two atoms trace to distinct lock items, which the
                -- pushed `Ψ_R` separates (`sep_lock`); shrink to the atoms via `sep_mono`.
                obtain ⟨d1', hd1lk, hd1mem⟩ := CapyCaptureSet.compile_cvar_subset_inv
                  (CapyCaptureSet.peaks_peaksOnly ctxOrig.capyCtx cs) hmZ1
                obtain ⟨d2', hd2lk, hd2mem⟩ := CapyCaptureSet.compile_cvar_subset_inv
                  (CapyCaptureSet.peaks_peaksOnly ctxOrig.capyCtx cs) hmZ2
                have hd1pc : d1' ∈ peakCvars (CapyCaptureSet.peakset ctxOrig.capyCtx cs) :=
                  cvar_mem_peakCvars hd1mem
                have hd2pc : d2' ∈ peakCvars (CapyCaptureSet.peakset ctxOrig.capyCtx cs) :=
                  cvar_mem_peakCvars hd2mem
                have hd12ne : d1' ≠ d2' := fun he => hZ (by rw [← hd1lk, ← hd2lk, he])
                -- the lock's two items separate (substituted + lock-shifted)
                have htd := (peakSepCtx_subst_HasTwoDistinct_of
                  (sc := ctxOrig.srcCtx.weaken (k := Kind.cvar))
                  (σt := σt.lift (k := Kind.cvar)) hd1pc hd2pc hd12ne).rename
                  (f := Rename.succ (k := Kind.lock))
                -- shrink each lock item down to the atom (inner subcapture, then weaken to lock)
                have mkSub : ∀ (a : Access) (Y' : BVar (s2',C) Kind.cvar)
                    (Z : BVar (s2,C) Kind.cvar) (m : Access) (d' : BVar _ Kind.cvar),
                    (CaptureSet.cvar a Y') ⊆ ((σt.lift (k := Kind.cvar)).cvar Z).applyAccess m →
                    (CapyCaptureSet.cvar m d') ⊆ CapyCaptureSet.peaks ctxOrig.capyCtx cs →
                    (ctxOrig.srcCtx.weaken (k := Kind.cvar)).lookupCVar d' = Z →
                    Subcapt (ctxSub.coreCtx,C[Authority.access_only]<:(CapyCaptureBound.compile cb
                        ctxOrig.srcCtx).subst σt)
                      (CaptureSet.cvar a Y')
                      ((CapyCaptureSet.compile
                        (peakItem (CapyCaptureSet.peakset ctxOrig.capyCtx cs) d')
                        (ctxOrig.srcCtx.weaken (k := Kind.cvar))).subst σt.lift) := by
                  intro a Y' Z m d' happ hmem hdlk
                  refine Subcapt.sc_trans (Subcapt.sc_elem happ) (Subcapt.sc_elem ?_)
                  have h1 : (CapyCaptureSet.cvar m d') ⊆
                      peakItem (CapyCaptureSet.peakset ctxOrig.capyCtx cs) d' :=
                    cvar_subset_peakItem hmem
                  have h2 := CapyCaptureSet.compile_subset
                    (sc := ctxOrig.srcCtx.weaken (k := Kind.cvar)) h1
                  have h3 := CaptureSet.Subset.subst (σ := σt.lift) h2
                  have heqc : CapyCaptureSet.compile (CapyCaptureSet.cvar m d')
                      (ctxOrig.srcCtx.weaken (k := Kind.cvar)) = CaptureSet.cvar m Z :=
                    congrArg (CaptureSet.cvar m) hdlk
                  rw [heqc] at h3
                  exact h3
                subst hY1eq; subst hY2eq
                -- Assemble as one `exact`: the goal context `Γ0` flows through every
                -- `sep_symm`/`sep_mono` down to `sep_lock`, pinning the looked-up lock `Ψ`
                -- and the `.weaken` bindings (`_`) automatically.
                exact SepCheck.sep_symm
                  (SepCheck.sep_mono
                    (SepCheck.sep_symm
                      (SepCheck.sep_mono
                        (SepCheck.sep_lock (ℓ := BVar.here) Ctx.LookupLock.here htd)
                        (Subcapt.weaken (mkSub a1 Y1' Z1 m1 d1' happ1 hd1mem hd1lk) _)))
                    (Subcapt.weaken (mkSub a2 Y2' Z2 m2 d2' happ2 hd2mem hd2lk) _))
            -- Discharge the goal from `key` (either ordering of the `HasTwoDistinct` pair).
            rcases hCdisj with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
            · exact key c1 c2 hcne hc1 hc2
            · exact key c2 c1 (Ne.symm hcne) hc2 hc1
    · -- backward: ⟦cpoly cb cs E⟧[σt] <: ⟦(cpoly cb cs E)[σ]⟧.  Structural mirror of the
      -- forward; the capture bound is again an EQUALITY (`Subbound.refl`, no contravariance),
      -- so the ONLY non-mechanical obligation is the `modal_modal` lock-change Satisfy — and
      -- THAT is the genuine gap (see `?satB` below).
      refine Subtyp.cpoly Subbound.refl ?_ (Subtyp.typ ?_)
      · simp only [CaptureSet.subst]; exact Subcapt.refl
      · have hCf :
            CapyCaptureSet.compile (CapyCaptureSet.subst cs σ)
                  (ctxSub.srcCtx.weaken (k := .cvar)) =
              (CapyCaptureSet.compile cs (ctxOrig.srcCtx.weaken (k := .cvar))).subst
                (σt.lift (k := .cvar)) :=
          CapyCaptureSet.compile_subst (SubstCompat.weakenTarget hcompat) hcsCl
        -- Intermediate `.modal Cf_R Ψ_L E_R`: lock-change `Ψ_R → Ψ_L` (`modal_modal`) then the
        -- `Cf`/body step (`modal`).  Mirror of forward with the two `trans` arms swapped.
        refine Subtyp.trans ?_
          (Subtyp.modal_modal ?_ ?_ ?_ ?satB)
          (Subtyp.modal (hCf ▸ Subcapt.refl) ?bodyB)
        -- (1) closedness of the intermediate `.modal Cf_R Ψ_L E_R` (identical to forward).
        · exact Ty.IsClosed.modal
            (CaptureSet.is_closed_subst (CapyCaptureSet.compile_isClosed hcsCl hvcOrig.weaken)
              (Subst.lift_closed hscl))
            ⟨peakSepCtx_isClosed hvcSub.weaken, CapyCaptureBound.mutabilityCtx_isClosed⟩
            (Ty.is_closed_subst
              (CapyTy.compile_isClosed E (ctxOrig.weakenTarget.consCVar cb BVar.here) hECl
                hvcOrig.weaken.consCVar)
              (Subst.lift_closed hscl))
        -- modal_modal closedness: Γ, Ψ1 = Ψ_R (substituted), Ψ2 = Ψ_L (sub-peaks).
        · exact Ctx.IsClosed.push hcoreSub (Binding.IsClosed.cvar
            (CaptureBound.is_closed_subst (CapyCaptureBound.compile_isClosed hcb hvcOrig) hscl))
        · exact ModalCtx.is_closed_subst
            ⟨peakSepCtx_isClosed hvcOrig.weaken, CapyCaptureBound.mutabilityCtx_isClosed⟩
            (Subst.lift_closed hscl)
        · exact ⟨peakSepCtx_isClosed hvcSub.weaken, CapyCaptureBound.mutabilityCtx_isClosed⟩
        -- (2) ★ THE GAP ★  `Satisfy (push_lock Ψ_L) (Ψ_R.rename succ)`: the un-substituted lock
        -- `Ψ_R` (one separation per ORIGIN peak of `cs`) must hold in the context whose lock is
        -- `Ψ_L` (one per SUB-peak of `cs[σ]`).  When `σ` MERGES two distinct origin peaks
        -- `d1≠d2` into the same sub-peak (their `σt`-images share a target cvar `x`),
        -- `Ψ_R.HasTwoDistinct` still yields the (positional!) pair `⟦d1⟧[σt], ⟦d2⟧[σt]`, which
        -- BOTH contain `x` — and `SepCheck _ (…x…) (…x…)` is unsatisfiable (no rule separates a
        -- cvar from itself; `Ψ_L` has fewer peaks and cannot help).  This is the K1 injected-lock
        -- instability under substitution-merging: the forward dispatch went weak→strong lock
        -- (provable), this backward one goes strong→weak.  Needs the HUMAN lock-design decision
        -- (subtyp-roadmap.md K1); independent of the `var`/`fresh` USE (which needs only `.1`).
        case satB => sorry
        case bodyB =>
          set ΨL : ModalCtx (s2',,Kind.cvar) :=
            { sep := peakSepCtx (CapyCaptureSet.peakset ctxSub.capyCtx (CapyCaptureSet.subst cs σ))
                       ctxSub.srcCtx.weaken,
              mutability := CapyCaptureBound.mutabilityCtx (cb.subst σ) BVar.here } with hΨL
          set csub' := ctxSub.weakenTarget.consCVar (cb.subst σ) (BVar.here) with hcsub'
          set corig' := ctxOrig.weakenTarget.consCVar cb (BVar.here) with hcorig'
          set ctxSub'' : CompilerCtx (s1',C) ((s2',,Kind.cvar),,Kind.lock) :=
            ⟨csub'.capyCtx, csub'.srcCtx.rename Rename.succ,
             (csub'.weakenTarget (Binding.lock ΨL)).dstCtx,
             (ctxSub.coreCtx,C[Authority.access_only]<:(CapyCaptureBound.compile cb
               ctxOrig.srcCtx).subst σt).push_lock ΨL⟩ with hctxSub''
          set ctxOrig'' : CompilerCtx _ ((s2,,Kind.cvar),,Kind.lock) :=
            ⟨corig'.capyCtx, corig'.srcCtx.rename Rename.succ,
             (corig'.weakenTarget
               (Binding.lock (⟨SepCtx.empty, MutabilityCtx.empty⟩ : ModalCtx _))).dstCtx,
             corig'.coreCtx.push_lock (⟨SepCtx.empty, MutabilityCtx.empty⟩ : ModalCtx _)⟩
            with hctxOrig''
          -- backward body: the SECOND conjunct of `ihE` (`.2`).
          have hge := (ihE (ctxSub := ctxSub'') (ctxOrig := ctxOrig'') (σ := σ.lift)
            (σt := σt.lift.lift)
            ((SubstCompat.weakenConsCVar hcompat).weakenTarget)
            ((SubstTvarCompat.weakenConsCVar htvar).weakenTarget)
            hECl hpb
            (TgtPairDroppable.liftLock (b := Binding.lock ΨL)
              (TgtPairDroppable.lift (b := Binding.cvar Authority.access_only
                ((CapyCaptureBound.compile cb ctxOrig.srcCtx).subst σt)) hdrop))
            (SrcAligned.weakenTarget (SrcAligned.consCVar (SrcAligned.weakenTarget haSub)))
            (SrcAligned.weakenTarget (SrcAligned.consCVar (SrcAligned.weakenTarget haOrig)))
            (CapyCtx.IsClosed.push hclSub (CapyBinding.IsClosed.cvar
              (CapyCaptureBound.is_closed_subst hcb hscS)))
            (CapyCtx.IsClosed.push hclOrig (CapyBinding.IsClosed.cvar hcb))
            (Subst.lift_closed (Subst.lift_closed hscl))
            hvcSub.weaken.consCVar.weaken hvcOrig.weaken.consCVar.weaken
            (Ctx.IsClosed.push
              (Ctx.IsClosed.push hcoreSub (Binding.IsClosed.cvar
                (CaptureBound.is_closed_subst
                  (CapyCaptureBound.compile_isClosed hcb hvcOrig) hscl)))
              (Binding.IsClosed.lock ⟨peakSepCtx_isClosed hvcSub.weaken,
                CapyCaptureBound.mutabilityCtx_isClosed⟩))
            (CapySubst.lift_closed hscS)
            (SrcCtx.CVarInjective.rename
              (SrcCtx.CVarInjective.consCVarHere hinj) Rename.injective_succ)).2
          have heq1 : CapyTy.compile (E.subst σ.lift) ctxSub''
              = (CapyTy.compile (E.subst σ.lift) csub').rename Rename.succ :=
            CapyTy.compile_rename (E.subst σ.lift) csub' ctxSub'' Rename.succ rfl rfl
          have heq2 : CapyTy.compile E ctxOrig''
              = (CapyTy.compile E corig').rename Rename.succ :=
            CapyTy.compile_rename E corig' ctxOrig'' Rename.succ rfl rfl
          convert hge using 2
          · rw [heq2]; exact Ty.weaken_subst_comm_base
          · exact heq1.symm

end Compilation
