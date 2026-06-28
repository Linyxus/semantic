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
    = CaptureSet.compile T.captureSet (sc.rename Rename.succ)
  rw [SrcCtx.lookupVar_rename, CaptureSet.compile_rename, h hlook]

/-- Compiling a source-weakened type's capture set through a matching `cons` peels the
    weakening (abstract kind `k`, so the rewrite's kind metavar absorbs the goal's). -/
theorem CaptureSet.compile_captureSet_weaken {s s2 : Sig} {k : Kind} {T : CapyTy .capt s}
    {info : SrcBinderInfo k s2} {sc : SrcCtx s s2} :
    CaptureSet.compile (T.rename (Rename.succ (k := k))).captureSet (.cons info sc)
      = CaptureSet.compile T.captureSet sc := by
  rw [CapyTy.captureSet_rename]
  exact CaptureSet.compile_rename_succ_cons

/-- Alignment is preserved by a fresh source capture binder (`consCVar`). -/
theorem SrcAligned.consCVar {s s2 : Sig} {Γ : CapyCtx s} {sc : SrcCtx s s2}
    {cb : CapyCaptureBound s} {c : BVar s2 .cvar}
    (h : SrcAligned Γ sc) : SrcAligned (Γ.push_cvar_default cb) (.cons (.cvar c) sc) := by
  intro x T hlook
  simp only [CapyCtx.push_cvar_default, CapyCtx.push_cvar] at hlook
  cases hlook with
  | there hlook0 => exact (h hlook0).trans CaptureSet.compile_captureSet_weaken.symm

/-- Alignment is preserved by a fresh source type binder (`consTVar`). -/
theorem SrcAligned.consTVar {s s2 : Sig} {Γ : CapyCtx s} {sc : SrcCtx s s2}
    {S : CapyPureTy s} {X : BVar s2 .tvar}
    (h : SrcAligned Γ sc) : SrcAligned (Γ.push_tvar S) (.cons (.tvar X) sc) := by
  intro x T hlook
  simp only [CapyCtx.push_tvar] at hlook
  cases hlook with
  | there hlook0 => exact (h hlook0).trans CaptureSet.compile_captureSet_weaken.symm

/-- **(★-keystone) Compiled peaks commute with a compatible substitution.**  Combines
    (★) `compile_peaks` (compilation factors through peak-resolution, under alignment)
    on both sides with the capture-level `compile_subst`:
    `⟦peaks (cs[σ])⟧ = ⟦peaks cs⟧[σt]`.  This is the union-level correspondence that
    lets the lock-`Satisfy` cross pairs relate `Ψ_L`'s items to `Ψ_R`'s (the
    SEPARATED-vs-MERGED split is then purely combinatorial on top of this). -/
theorem CaptureSet.compile_peaks_subst {s1 s2 s1' s2' : Sig}
    {Γorig : CapyCtx s1} {Γsub : CapyCtx s1'} {scOrig : SrcCtx s1 s2} {scSub : SrcCtx s1' s2'}
    {σ : CapySubst s1 s1'} {σt : Subst s2 s2'}
    (hΓO : Γorig.IsClosed) (hΓS : Γsub.IsClosed)
    (haO : SrcAligned Γorig scOrig) (haS : SrcAligned Γsub scSub)
    (h : SubstCompat scSub scOrig σ σt)
    {cs : CaptureSet s1} (hcs : cs.IsClosed) (hsub : (CapyCaptureSet.subst cs σ).IsClosed) :
    CaptureSet.compile (CapyCaptureSet.peaks Γsub (CapyCaptureSet.subst cs σ)) scSub
      = (CaptureSet.compile (CapyCaptureSet.peaks Γorig cs) scOrig).subst σt := by
  rw [CaptureSet.compile_peaks hΓS haS hsub, CaptureSet.compile_subst h hcs,
      ← CaptureSet.compile_peaks hΓO haO hcs]

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
theorem peakSepCtx_HasTwoDistinct_of {s1 s2 : Sig} {P : PeakSet s1} {sc : SrcCtx s1 s2}
    {c1 c2 : BVar s1 .cvar} (hc1 : c1 ∈ peakCvars P) (hc2 : c2 ∈ peakCvars P) (hne : c1 ≠ c2) :
    SepCtx.HasTwoDistinct (peakSepCtx P sc)
      (CaptureSet.compile (peakItem P c1) sc) (CaptureSet.compile (peakItem P c2) sc) := by
  simp only [peakSepCtx]
  exact SepCtx.HasTwoDistinct.foldl
    (g := fun c => CaptureSet.compile (peakItem P c) sc) (peakCvars P) hc1 hc2 hne

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
theorem peakSepCtx_subst {s1 s2 s2' : Sig} {P : PeakSet s1} {sc : SrcCtx s1 s2}
    {σt : Subst s2 s2'} :
    (peakSepCtx P sc).subst σt
      = (peakCvars P).foldl
          (fun K c => SepCtx.cons K ((CaptureSet.compile (peakItem P c) sc).subst σt))
          SepCtx.empty := by
  simp only [peakSepCtx]
  rw [SepCtx.subst_foldl]
  rfl

/-- **Converse for the substituted lock `Ψ_R`.**  Distinct peak cvars give
    `HasTwoDistinct` *substituted* items — the `sep_lock` premise against the
    in-context merged lock. -/
theorem peakSepCtx_subst_HasTwoDistinct_of {s1 s2 s2' : Sig} {P : PeakSet s1}
    {sc : SrcCtx s1 s2} {σt : Subst s2 s2'} {c1 c2 : BVar s1 .cvar}
    (hc1 : c1 ∈ peakCvars P) (hc2 : c2 ∈ peakCvars P) (hne : c1 ≠ c2) :
    SepCtx.HasTwoDistinct ((peakSepCtx P sc).subst σt)
      ((CaptureSet.compile (peakItem P c1) sc).subst σt)
      ((CaptureSet.compile (peakItem P c2) sc).subst σt) := by
  rw [peakSepCtx_subst]
  exact SepCtx.HasTwoDistinct.foldl
    (g := fun c => (CaptureSet.compile (peakItem P c) sc).subst σt) (peakCvars P) hc1 hc2 hne

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
      Subtyp ctxSub.coreCtx (CapyTy.compile (T.subst σ) ctxSub)
        ((CapyTy.compile T ctxOrig).subst σt) ∧
      Subtyp ctxSub.coreCtx ((CapyTy.compile T ctxOrig).subst σt)
        (CapyTy.compile (T.subst σ) ctxSub) := by
  induction T with
  | top =>
    intro s2 s1' s2' ctxOrig ctxSub σ σt hcompat htvar hcl hpb hdrop haSub haOrig hclSub hclOrig
      hscl hvcSub hvcOrig hcoreSub hscS
    simp only [CapyTy.subst, CapyTy.compile, Ty.subst]
    exact ⟨Subtyp.refl, Subtyp.refl⟩
  | unit =>
    intro s2 s1' s2' ctxOrig ctxSub σ σt hcompat htvar hcl hpb hdrop haSub haOrig hclSub hclOrig
      hscl hvcSub hvcOrig hcoreSub hscS
    simp only [CapyTy.subst, CapyTy.compile, Ty.subst]
    exact ⟨Subtyp.refl, Subtyp.refl⟩
  | bool =>
    intro s2 s1' s2' ctxOrig ctxSub σ σt hcompat htvar hcl hpb hdrop haSub haOrig hclSub hclOrig
      hscl hvcSub hvcOrig hcoreSub hscS
    simp only [CapyTy.subst, CapyTy.compile, Ty.subst]
    exact ⟨Subtyp.refl, Subtyp.refl⟩
  | cap cs =>
    intro s2 s1' s2' ctxOrig ctxSub σ σt hcompat htvar hcl hpb hdrop haSub haOrig hclSub hclOrig
      hscl hvcSub hvcOrig hcoreSub hscS
    cases hcl with | cap hcs =>
    rw [CapyTy.compile_subst_cap hcompat hcs]
    exact ⟨Subtyp.refl, Subtyp.refl⟩
  | cell cs m =>
    intro s2 s1' s2' ctxOrig ctxSub σ σt hcompat htvar hcl hpb hdrop haSub haOrig hclSub hclOrig
      hscl hvcSub hvcOrig hcoreSub hscS
    cases hcl with | cell hcs =>
    rw [CapyTy.compile_subst_cell hcompat hcs]
    exact ⟨Subtyp.refl, Subtyp.refl⟩
  | typ T1 ih =>
    intro s2 s1' s2' ctxOrig ctxSub σ σt hcompat htvar hcl hpb hdrop haSub haOrig hclSub hclOrig
      hscl hvcSub hvcOrig hcoreSub hscS
    cases hcl with | typ hcl1 =>
    simp only [CapyTy.subst, CapyTy.compile, Ty.subst]
    obtain ⟨hle, hge⟩ := ih hcompat htvar hcl1 hpb hdrop haSub haOrig hclSub hclOrig
      hscl hvcSub hvcOrig hcoreSub hscS
    exact ⟨Subtyp.typ hle, Subtyp.typ hge⟩
  | exi T1 ih =>
    intro s2 s1' s2' ctxOrig ctxSub σ σt hcompat htvar hcl hpb hdrop haSub haOrig hclSub hclOrig
      hscl hvcSub hvcOrig hcoreSub hscS
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
      (CapySubst.lift_closed hscS)
    exact ⟨Subtyp.exi hle, Subtyp.exi hge⟩
  | tvar X =>
    intro s2 s1' s2' ctxOrig ctxSub σ σt hcompat htvar hcl hpb hdrop haSub haOrig hclSub hclOrig
      hscl hvcSub hvcOrig hcoreSub hscS
    obtain ⟨Z, hZ, hlk⟩ := htvar X
    simp only [CapyTy.subst, hZ, CapyPureTy.tvar, CapyTy.compile, Ty.subst, hlk, PureTy.tvar]
    exact ⟨Subtyp.refl, Subtyp.refl⟩
  | arrow T1 cs E ihT1 ihE =>
    intro s2 s1' s2' ctxOrig ctxSub σ σt hcompat htvar hcl hpb hdrop haSub haOrig hclSub hclOrig
      hscl hvcSub hvcOrig hcoreSub hscS
    sorry
  | poly S cs E ihS ihE =>
    intro s2 s1' s2' ctxOrig ctxSub σ σt hcompat htvar hcl hpb hdrop haSub haOrig hclSub hclOrig
      hscl hvcSub hvcOrig hcoreSub hscS
    sorry
  | cpoly cb cs E ihE =>
    intro s2 s1' s2' ctxOrig ctxSub σ σt hcompat htvar hcl hpb hdrop haSub haOrig hclSub hclOrig
      hscl hvcSub hvcOrig hcoreSub hscS
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
            CaptureSet.compile (CapyCaptureSet.subst cs σ)
                  (ctxSub.srcCtx.weaken (k := .cvar)) =
              (CaptureSet.compile cs (ctxOrig.srcCtx.weaken (k := .cvar))).subst
                (σt.lift (k := .cvar)) :=
          CaptureSet.compile_subst (SubstCompat.weakenTarget hcompat) hcsCl
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
            (CaptureSet.is_closed_subst (CaptureSet.compile_isClosed hcsCl hvcOrig.weaken)
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
            (CapySubst.lift_closed hscS)).1
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
            obtain ⟨⟨c1, hc1, hC1⟩, ⟨c2, hc2, hC2⟩⟩ := peakSepCtx_HasTwoDistinct hdist
            sorry
    · -- backward
      refine Subtyp.cpoly Subbound.refl ?_ (Subtyp.typ ?_)
      · simp only [CaptureSet.subst]; exact Subcapt.refl
      · sorry  -- modal subtyping (backward)

end Compilation
