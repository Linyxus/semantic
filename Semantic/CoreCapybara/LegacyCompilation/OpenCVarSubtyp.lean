import Semantic.CoreCapybara.LegacyCompilation.SubtypCompile
import Semantic.CoreCapybara.LegacyCompilation.TargetRename
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

/-- `TgtPairDroppable` preserved by a target binder + a VAR lift (the arrow-body
    builder).  The lifted cvar var is always `.there` (the binder is a var), so
    only the shift case arises — identical to `.liftLock`. -/
theorem TgtPairDroppable.liftVar {s2 s2' : Sig} {Γt : Ctx s2'} {σt : Subst s2 s2'}
    {b : Binding s2' .var} (h : TgtPairDroppable Γt σt) :
    TgtPairDroppable (Γt.push b) (σt.lift (k := Kind.var)) := by
  intro Y a1 a2 c1 c2 hne hmem1 hmem2
  cases Y with
  | there Y0 =>
    have hYeq : (σt.lift (k := Kind.var)).cvar (.there Y0)
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

/-- **Scoped pairwise-droppability.**  Like `TgtPairDroppable`, but only the target
    cvars `Y` satisfying a scope predicate `P` are required to be pairwise-droppable.
    Antitone in `P` (`.mono`).  The blanket form is the case `P = fun _ => True`
    (`TgtPairDroppable.toOn`).  Lifts through binders adjust `P` on the `.there`
    slot only — the freshly-bound cvar image is single-peak, hence vacuous. -/
def TgtPairDroppableOn {s2 s2' : Sig} (P : BVar s2 .cvar → Prop)
    (Γt : Ctx s2') (σt : Subst s2 s2') : Prop :=
  ∀ (Y : BVar s2 .cvar), P Y → ∀ (a1 a2 : Access) (c1 c2 : BVar s2' .cvar), c1 ≠ c2 →
    (CaptureSet.cvar a1 c1) ⊆ CaptureSet.peaks Γt (σt.cvar Y) →
    (CaptureSet.cvar a2 c2) ⊆ CaptureSet.peaks Γt (σt.cvar Y) →
    Γt.TwoDistinctDroppable c1 c2

/-- `TgtPairDroppableOn` is antitone in its scope: a smaller scope is easier. -/
theorem TgtPairDroppableOn.mono {s2 s2' : Sig} {Γt : Ctx s2'} {σt : Subst s2 s2'}
    {P P' : BVar s2 .cvar → Prop} (hPP : ∀ Y, P' Y → P Y)
    (h : TgtPairDroppableOn P Γt σt) : TgtPairDroppableOn P' Γt σt :=
  fun Y hY => h Y (hPP Y hY)

/-- The blanket `TgtPairDroppable` gives the scoped form for any scope. -/
theorem TgtPairDroppable.toOn {s2 s2' : Sig} {Γt : Ctx s2'} {σt : Subst s2 s2'}
    {P : BVar s2 .cvar → Prop} (h : TgtPairDroppable Γt σt) : TgtPairDroppableOn P Γt σt :=
  fun Y _ => h Y

/-- `TgtPairDroppableOn` preserved by a target binder + a cvar lift.  The freshly-bound
    `.here` cvar is single-peak (vacuous); the scope on the `.there` slot is adjusted by
    `hP`. -/
theorem TgtPairDroppableOn.lift {s2 s2' : Sig} {Γt : Ctx s2'} {σt : Subst s2 s2'}
    {P : BVar s2 .cvar → Prop} {P' : BVar (s2,,Kind.cvar) .cvar → Prop}
    {b : Binding s2' .cvar} (hP : ∀ Y0, P' (.there Y0) → P Y0)
    (h : TgtPairDroppableOn P Γt σt) :
    TgtPairDroppableOn P' (Γt.push b) (σt.lift (k := Kind.cvar)) := by
  intro Y hY a1 a2 c1 c2 hne hmem1 hmem2
  cases Y with
  | here =>
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
    obtain ⟨ha_d1, ha_d2, _⟩ := h Y0 (hP Y0 hY) a1 a2 d1 d2 hne0 hsub1 hsub2
    refine ⟨?_, ?_, hne⟩
    · simp only [Ctx.lookup_authority]; exact ha_d1
    · simp only [Ctx.lookup_authority]; exact ha_d2

/-- `TgtPairDroppableOn` preserved by a target binder + a TVAR lift. -/
theorem TgtPairDroppableOn.liftTVar {s2 s2' : Sig} {Γt : Ctx s2'} {σt : Subst s2 s2'}
    {P : BVar s2 .cvar → Prop} {P' : BVar (s2,,Kind.tvar) .cvar → Prop}
    {b : Binding s2' .tvar} (hP : ∀ Y0, P' (.there Y0) → P Y0)
    (h : TgtPairDroppableOn P Γt σt) :
    TgtPairDroppableOn P' (Γt.push b) (σt.lift (k := Kind.tvar)) := by
  intro Y hY a1 a2 c1 c2 hne hmem1 hmem2
  cases Y with
  | there Y0 =>
    have hYeq : (σt.lift (k := Kind.tvar)).cvar (.there Y0)
        = (σt.cvar Y0).rename Rename.succ := Subst.lift_there_cvar_eq
    rw [hYeq, CaptureSet.peaks_rename_succ_eq] at hmem1 hmem2
    obtain ⟨d1, hd1, hsub1⟩ := CaptureSet.cvar_subset_rename_succ hmem1
    obtain ⟨d2, hd2, hsub2⟩ := CaptureSet.cvar_subset_rename_succ hmem2
    subst hd1; subst hd2
    have hne0 : d1 ≠ d2 := fun heq => hne (by rw [heq])
    obtain ⟨ha_d1, ha_d2, _⟩ := h Y0 (hP Y0 hY) a1 a2 d1 d2 hne0 hsub1 hsub2
    refine ⟨?_, ?_, hne⟩
    · simp only [Ctx.lookup_authority]; exact ha_d1
    · simp only [Ctx.lookup_authority]; exact ha_d2

/-- `TgtPairDroppableOn` preserved by a target binder + a LOCK lift. -/
theorem TgtPairDroppableOn.liftLock {s2 s2' : Sig} {Γt : Ctx s2'} {σt : Subst s2 s2'}
    {P : BVar s2 .cvar → Prop} {P' : BVar (s2,,Kind.lock) .cvar → Prop}
    {b : Binding s2' .lock} (hP : ∀ Y0, P' (.there Y0) → P Y0)
    (h : TgtPairDroppableOn P Γt σt) :
    TgtPairDroppableOn P' (Γt.push b) (σt.lift (k := Kind.lock)) := by
  intro Y hY a1 a2 c1 c2 hne hmem1 hmem2
  cases Y with
  | there Y0 =>
    have hYeq : (σt.lift (k := Kind.lock)).cvar (.there Y0)
        = (σt.cvar Y0).rename Rename.succ := Subst.lift_there_cvar_eq
    rw [hYeq, CaptureSet.peaks_rename_succ_eq] at hmem1 hmem2
    obtain ⟨d1, hd1, hsub1⟩ := CaptureSet.cvar_subset_rename_succ hmem1
    obtain ⟨d2, hd2, hsub2⟩ := CaptureSet.cvar_subset_rename_succ hmem2
    subst hd1; subst hd2
    have hne0 : d1 ≠ d2 := fun heq => hne (by rw [heq])
    obtain ⟨ha_d1, ha_d2, _⟩ := h Y0 (hP Y0 hY) a1 a2 d1 d2 hne0 hsub1 hsub2
    refine ⟨?_, ?_, hne⟩
    · simp only [Ctx.lookup_authority]; exact ha_d1
    · simp only [Ctx.lookup_authority]; exact ha_d2

/-- `TgtPairDroppableOn` preserved by a target binder + a VAR lift. -/
theorem TgtPairDroppableOn.liftVar {s2 s2' : Sig} {Γt : Ctx s2'} {σt : Subst s2 s2'}
    {P : BVar s2 .cvar → Prop} {P' : BVar (s2,,Kind.var) .cvar → Prop}
    {b : Binding s2' .var} (hP : ∀ Y0, P' (.there Y0) → P Y0)
    (h : TgtPairDroppableOn P Γt σt) :
    TgtPairDroppableOn P' (Γt.push b) (σt.lift (k := Kind.var)) := by
  intro Y hY a1 a2 c1 c2 hne hmem1 hmem2
  cases Y with
  | there Y0 =>
    have hYeq : (σt.lift (k := Kind.var)).cvar (.there Y0)
        = (σt.cvar Y0).rename Rename.succ := Subst.lift_there_cvar_eq
    rw [hYeq, CaptureSet.peaks_rename_succ_eq] at hmem1 hmem2
    obtain ⟨d1, hd1, hsub1⟩ := CaptureSet.cvar_subset_rename_succ hmem1
    obtain ⟨d2, hd2, hsub2⟩ := CaptureSet.cvar_subset_rename_succ hmem2
    subst hd1; subst hd2
    have hne0 : d1 ≠ d2 := fun heq => hne (by rw [heq])
    obtain ⟨ha_d1, ha_d2, _⟩ := h Y0 (hP Y0 hY) a1 a2 d1 d2 hne0 hsub1 hsub2
    refine ⟨?_, ?_, hne⟩
    · simp only [Ctx.lookup_authority]; exact ha_d1
    · simp only [Ctx.lookup_authority]; exact ha_d2

/-- `TgtPairDroppableOn` preserved by a target binder + a lift of ANY kind (generic over
    the binder kind — the freshly-bound cvar image, only possible when the kind is `cvar`,
    is single-peak hence vacuous). -/
theorem TgtPairDroppableOn.liftGen {s2 s2' : Sig} {Γt : Ctx s2'} {σt : Subst s2 s2'}
    {k : Kind} {P : BVar s2 .cvar → Prop} {P' : BVar (s2,,k) .cvar → Prop}
    {b : Binding s2' k} (hP : ∀ Y0, P' (.there Y0) → P Y0)
    (h : TgtPairDroppableOn P Γt σt) :
    TgtPairDroppableOn P' (Γt.push b) (σt.lift (k := k)) := by
  intro Y hY a1 a2 c1 c2 hne hmem1 hmem2
  cases Y with
  | here =>
    have h1 : (σt.lift (k := Kind.cvar)).cvar .here = CaptureSet.cvar (.M .epsilon) .here := rfl
    rw [h1] at hmem1 hmem2
    simp only [CaptureSet.peaks] at hmem1 hmem2
    cases hmem1; cases hmem2
    exact absurd rfl hne
  | there Y0 =>
    have hYeq : (σt.lift (k := k)).cvar (.there Y0) = (σt.cvar Y0).rename Rename.succ :=
      Subst.lift_there_cvar_eq
    rw [hYeq, CaptureSet.peaks_rename_succ_eq] at hmem1 hmem2
    obtain ⟨d1, hd1, hsub1⟩ := CaptureSet.cvar_subset_rename_succ hmem1
    obtain ⟨d2, hd2, hsub2⟩ := CaptureSet.cvar_subset_rename_succ hmem2
    subst hd1; subst hd2
    have hne0 : d1 ≠ d2 := fun heq => hne (by rw [heq])
    obtain ⟨ha_d1, ha_d2, _⟩ := h Y0 (hP Y0 hY) a1 a2 d1 d2 hne0 hsub1 hsub2
    refine ⟨?_, ?_, hne⟩
    · simp only [Ctx.lookup_authority]; exact ha_d1
    · simp only [Ctx.lookup_authority]; exact ha_d2

/-- Two-binder lift with a 2-level scope transport (`.there (.there ·)`). -/
theorem TgtPairDroppableOn.liftShift2 {s2 s2' : Sig} {Γt : Ctx s2'} {σt : Subst s2 s2'}
    {k1 k2 : Kind} {b1 : Binding s2' k1} {b2 : Binding (s2',,k1) k2}
    {P : BVar s2 .cvar → Prop} {P2 : BVar ((s2,,k1),,k2) .cvar → Prop}
    (hP : ∀ Y0, P2 (BVar.there (BVar.there Y0)) → P Y0)
    (h : TgtPairDroppableOn P Γt σt) :
    TgtPairDroppableOn P2 ((Γt.push b1).push b2)
      ((σt.lift (k := k1)).lift (k := k2)) :=
  TgtPairDroppableOn.liftGen (fun _ hh => hh)
    (TgtPairDroppableOn.liftGen (P' := fun Z => P2 (BVar.there Z)) hP h)

/-- Three-binder lift with a 3-level scope transport (`.there (.there (.there ·))`). -/
theorem TgtPairDroppableOn.liftShift3 {s2 s2' : Sig} {Γt : Ctx s2'} {σt : Subst s2 s2'}
    {k1 k2 k3 : Kind} {b1 : Binding s2' k1} {b2 : Binding (s2',,k1) k2}
    {b3 : Binding ((s2',,k1),,k2) k3}
    {P : BVar s2 .cvar → Prop} {P3 : BVar (((s2,,k1),,k2),,k3) .cvar → Prop}
    (hP : ∀ Y0, P3 (BVar.there (BVar.there (BVar.there Y0))) → P Y0)
    (h : TgtPairDroppableOn P Γt σt) :
    TgtPairDroppableOn P3 (((Γt.push b1).push b2).push b3)
      (((σt.lift (k := k1)).lift (k := k2)).lift (k := k3)) :=
  TgtPairDroppableOn.liftGen (fun _ hh => hh)
    (TgtPairDroppableOn.liftGen (P' := fun Z => P3 (BVar.there Z)) (fun _ hh => hh)
      (TgtPairDroppableOn.liftGen (P' := fun Z => P3 (BVar.there (BVar.there Z))) hP h))

/-- Four-binder lift with a 4-level scope transport. -/
theorem TgtPairDroppableOn.liftShift4 {s2 s2' : Sig} {Γt : Ctx s2'} {σt : Subst s2 s2'}
    {k1 k2 k3 k4 : Kind} {b1 : Binding s2' k1} {b2 : Binding (s2',,k1) k2}
    {b3 : Binding ((s2',,k1),,k2) k3} {b4 : Binding (((s2',,k1),,k2),,k3) k4}
    {P : BVar s2 .cvar → Prop} {P4 : BVar ((((s2,,k1),,k2),,k3),,k4) .cvar → Prop}
    (hP : ∀ Y0, P4 (BVar.there (BVar.there (BVar.there (BVar.there Y0)))) → P Y0)
    (h : TgtPairDroppableOn P Γt σt) :
    TgtPairDroppableOn P4 ((((Γt.push b1).push b2).push b3).push b4)
      ((((σt.lift (k := k1)).lift (k := k2)).lift (k := k3)).lift (k := k4)) :=
  TgtPairDroppableOn.liftGen (fun _ hh => hh)
    (TgtPairDroppableOn.liftGen (P' := fun Z => P4 (BVar.there Z)) (fun _ hh => hh)
      (TgtPairDroppableOn.liftGen (P' := fun Z => P4 (BVar.there (BVar.there Z))) (fun _ hh => hh)
        (TgtPairDroppableOn.liftGen
          (P' := fun Z => P4 (BVar.there (BVar.there (BVar.there Z)))) hP h)))

/-! ### Split-covering scoped separation (`TgtSplitCoveredOn`)

The split-covering analog of `TgtPairDroppableOn`: same scope/quantifier structure,
but the per-pair conclusion is a mode-polymorphic `SepCheck` (the covering analog of
`sep_droppable`'s own access-mode polymorphism) instead of `TwoDistinctDroppable`.
This is the ADDITIVE foundation for re-routing `compile_subst_subtyp`'s forward peak
separation from droppability to a split-covering premise (`hsplitW`); the split-covering
forward dispatch `compile_peakSepCtx_sep_forward_splitcov` consumes exactly this shape.

The lifts mirror `TgtPairDroppableOn`'s verbatim in their scope/peaks transport; only the
conclusion transport changes: `TwoDistinctDroppable`-under-weaken becomes `SepCheck`-under-
weaken, via `SepCheck.weaken` (a thin single-binder wrapper around the imported
`SepCheck.renamesTo` — the same lock-weakening `compile_peakSepCtx_sep_forward_splitcov`
performs at its split dispatch).  The scope-transport dispatch bridges
(`tgtCvarOccurs_bridge_poly/_cpoly/_arrow`) conclude `TgtCvarOccurs` and are conclusion-
agnostic, so they are SHARED with the droppability route (no split-covering port needed). -/

/-- Single-binder `SepCheck` weakening: `SepCheck Γ` transports to `SepCheck (Γ.push b)`
    under `Rename.succ`.  A thin specialization of `SepCheck.renamesTo` to the
    weaken-morphism `Ctx.RenamesTo.weaken b`; the exact conclusion transport the
    split-covering lifts (and the `_splitcov` dispatch's split case) perform. -/
theorem SepCheck.weaken {s : Sig} {Γ : Ctx s} {C1 C2 : CaptureSet s} {k : Kind}
    (h : SepCheck Γ C1 C2) (b : Binding s k) :
    SepCheck (Γ.push b) (C1.rename Rename.succ) (C2.rename Rename.succ) :=
  h.renamesTo (Ctx.RenamesTo.weaken b) Rename.injective_succ

/-- **Scoped split-covering separation.**  Like `TgtPairDroppableOn`, but only the target
    cvars `Y` satisfying a scope predicate `P` are required to have their distinct target-peak
    cvars pairwise-`SepCheck`-separated (mode-polymorphically).  Matches `hsplitW`'s exact
    shape.  Antitone in `P` (`.mono`).  Lifts through binders adjust `P` on the `.there`
    slot only — the freshly-bound cvar image is single-peak, hence vacuous. -/
def TgtSplitCoveredOn {s2 s2' : Sig} (P : BVar s2 .cvar → Prop)
    (Γt : Ctx s2') (σt : Subst s2 s2') : Prop :=
  ∀ (Y : BVar s2 .cvar), P Y → ∀ (a1 a2 : Access) (c1 c2 : BVar s2' .cvar), c1 ≠ c2 →
    (CaptureSet.cvar a1 c1) ⊆ CaptureSet.peaks Γt (σt.cvar Y) →
    (CaptureSet.cvar a2 c2) ⊆ CaptureSet.peaks Γt (σt.cvar Y) →
    ∀ (m1 m2 : Access), SepCheck Γt (CaptureSet.cvar m1 c1) (CaptureSet.cvar m2 c2)

/-- `TgtSplitCoveredOn` is antitone in its scope: a smaller scope is easier. -/
theorem TgtSplitCoveredOn.mono {s2 s2' : Sig} {Γt : Ctx s2'} {σt : Subst s2 s2'}
    {P P' : BVar s2 .cvar → Prop} (hPP : ∀ Y, P' Y → P Y)
    (h : TgtSplitCoveredOn P Γt σt) : TgtSplitCoveredOn P' Γt σt :=
  fun Y hY => h Y (hPP Y hY)

/-- `TgtSplitCoveredOn` preserved by a target binder + a cvar lift.  The freshly-bound
    `.here` cvar is single-peak (vacuous); the scope on the `.there` slot is adjusted by
    `hP`. -/
theorem TgtSplitCoveredOn.lift {s2 s2' : Sig} {Γt : Ctx s2'} {σt : Subst s2 s2'}
    {P : BVar s2 .cvar → Prop} {P' : BVar (s2,,Kind.cvar) .cvar → Prop}
    {b : Binding s2' .cvar} (hP : ∀ Y0, P' (.there Y0) → P Y0)
    (h : TgtSplitCoveredOn P Γt σt) :
    TgtSplitCoveredOn P' (Γt.push b) (σt.lift (k := Kind.cvar)) := by
  intro Y hY a1 a2 c1 c2 hne hmem1 hmem2
  cases Y with
  | here =>
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
    intro m1 m2
    exact SepCheck.weaken (h Y0 (hP Y0 hY) a1 a2 d1 d2 hne0 hsub1 hsub2 m1 m2) b

/-- `TgtSplitCoveredOn` preserved by a target binder + a TVAR lift. -/
theorem TgtSplitCoveredOn.liftTVar {s2 s2' : Sig} {Γt : Ctx s2'} {σt : Subst s2 s2'}
    {P : BVar s2 .cvar → Prop} {P' : BVar (s2,,Kind.tvar) .cvar → Prop}
    {b : Binding s2' .tvar} (hP : ∀ Y0, P' (.there Y0) → P Y0)
    (h : TgtSplitCoveredOn P Γt σt) :
    TgtSplitCoveredOn P' (Γt.push b) (σt.lift (k := Kind.tvar)) := by
  intro Y hY a1 a2 c1 c2 hne hmem1 hmem2
  cases Y with
  | there Y0 =>
    have hYeq : (σt.lift (k := Kind.tvar)).cvar (.there Y0)
        = (σt.cvar Y0).rename Rename.succ := Subst.lift_there_cvar_eq
    rw [hYeq, CaptureSet.peaks_rename_succ_eq] at hmem1 hmem2
    obtain ⟨d1, hd1, hsub1⟩ := CaptureSet.cvar_subset_rename_succ hmem1
    obtain ⟨d2, hd2, hsub2⟩ := CaptureSet.cvar_subset_rename_succ hmem2
    subst hd1; subst hd2
    have hne0 : d1 ≠ d2 := fun heq => hne (by rw [heq])
    intro m1 m2
    exact SepCheck.weaken (h Y0 (hP Y0 hY) a1 a2 d1 d2 hne0 hsub1 hsub2 m1 m2) b

/-- `TgtSplitCoveredOn` preserved by a target binder + a LOCK lift. -/
theorem TgtSplitCoveredOn.liftLock {s2 s2' : Sig} {Γt : Ctx s2'} {σt : Subst s2 s2'}
    {P : BVar s2 .cvar → Prop} {P' : BVar (s2,,Kind.lock) .cvar → Prop}
    {b : Binding s2' .lock} (hP : ∀ Y0, P' (.there Y0) → P Y0)
    (h : TgtSplitCoveredOn P Γt σt) :
    TgtSplitCoveredOn P' (Γt.push b) (σt.lift (k := Kind.lock)) := by
  intro Y hY a1 a2 c1 c2 hne hmem1 hmem2
  cases Y with
  | there Y0 =>
    have hYeq : (σt.lift (k := Kind.lock)).cvar (.there Y0)
        = (σt.cvar Y0).rename Rename.succ := Subst.lift_there_cvar_eq
    rw [hYeq, CaptureSet.peaks_rename_succ_eq] at hmem1 hmem2
    obtain ⟨d1, hd1, hsub1⟩ := CaptureSet.cvar_subset_rename_succ hmem1
    obtain ⟨d2, hd2, hsub2⟩ := CaptureSet.cvar_subset_rename_succ hmem2
    subst hd1; subst hd2
    have hne0 : d1 ≠ d2 := fun heq => hne (by rw [heq])
    intro m1 m2
    exact SepCheck.weaken (h Y0 (hP Y0 hY) a1 a2 d1 d2 hne0 hsub1 hsub2 m1 m2) b

/-- `TgtSplitCoveredOn` preserved by a target binder + a VAR lift. -/
theorem TgtSplitCoveredOn.liftVar {s2 s2' : Sig} {Γt : Ctx s2'} {σt : Subst s2 s2'}
    {P : BVar s2 .cvar → Prop} {P' : BVar (s2,,Kind.var) .cvar → Prop}
    {b : Binding s2' .var} (hP : ∀ Y0, P' (.there Y0) → P Y0)
    (h : TgtSplitCoveredOn P Γt σt) :
    TgtSplitCoveredOn P' (Γt.push b) (σt.lift (k := Kind.var)) := by
  intro Y hY a1 a2 c1 c2 hne hmem1 hmem2
  cases Y with
  | there Y0 =>
    have hYeq : (σt.lift (k := Kind.var)).cvar (.there Y0)
        = (σt.cvar Y0).rename Rename.succ := Subst.lift_there_cvar_eq
    rw [hYeq, CaptureSet.peaks_rename_succ_eq] at hmem1 hmem2
    obtain ⟨d1, hd1, hsub1⟩ := CaptureSet.cvar_subset_rename_succ hmem1
    obtain ⟨d2, hd2, hsub2⟩ := CaptureSet.cvar_subset_rename_succ hmem2
    subst hd1; subst hd2
    have hne0 : d1 ≠ d2 := fun heq => hne (by rw [heq])
    intro m1 m2
    exact SepCheck.weaken (h Y0 (hP Y0 hY) a1 a2 d1 d2 hne0 hsub1 hsub2 m1 m2) b

/-- `TgtSplitCoveredOn` preserved by a target binder + a lift of ANY kind (generic over
    the binder kind — the freshly-bound cvar image, only possible when the kind is `cvar`,
    is single-peak hence vacuous). -/
theorem TgtSplitCoveredOn.liftGen {s2 s2' : Sig} {Γt : Ctx s2'} {σt : Subst s2 s2'}
    {k : Kind} {P : BVar s2 .cvar → Prop} {P' : BVar (s2,,k) .cvar → Prop}
    {b : Binding s2' k} (hP : ∀ Y0, P' (.there Y0) → P Y0)
    (h : TgtSplitCoveredOn P Γt σt) :
    TgtSplitCoveredOn P' (Γt.push b) (σt.lift (k := k)) := by
  intro Y hY a1 a2 c1 c2 hne hmem1 hmem2
  cases Y with
  | here =>
    have h1 : (σt.lift (k := Kind.cvar)).cvar .here = CaptureSet.cvar (.M .epsilon) .here := rfl
    rw [h1] at hmem1 hmem2
    simp only [CaptureSet.peaks] at hmem1 hmem2
    cases hmem1; cases hmem2
    exact absurd rfl hne
  | there Y0 =>
    have hYeq : (σt.lift (k := k)).cvar (.there Y0) = (σt.cvar Y0).rename Rename.succ :=
      Subst.lift_there_cvar_eq
    rw [hYeq, CaptureSet.peaks_rename_succ_eq] at hmem1 hmem2
    obtain ⟨d1, hd1, hsub1⟩ := CaptureSet.cvar_subset_rename_succ hmem1
    obtain ⟨d2, hd2, hsub2⟩ := CaptureSet.cvar_subset_rename_succ hmem2
    subst hd1; subst hd2
    have hne0 : d1 ≠ d2 := fun heq => hne (by rw [heq])
    intro m1 m2
    exact SepCheck.weaken (h Y0 (hP Y0 hY) a1 a2 d1 d2 hne0 hsub1 hsub2 m1 m2) b

/-- Two-binder lift with a 2-level scope transport (`.there (.there ·)`). -/
theorem TgtSplitCoveredOn.liftShift2 {s2 s2' : Sig} {Γt : Ctx s2'} {σt : Subst s2 s2'}
    {k1 k2 : Kind} {b1 : Binding s2' k1} {b2 : Binding (s2',,k1) k2}
    {P : BVar s2 .cvar → Prop} {P2 : BVar ((s2,,k1),,k2) .cvar → Prop}
    (hP : ∀ Y0, P2 (BVar.there (BVar.there Y0)) → P Y0)
    (h : TgtSplitCoveredOn P Γt σt) :
    TgtSplitCoveredOn P2 ((Γt.push b1).push b2)
      ((σt.lift (k := k1)).lift (k := k2)) :=
  TgtSplitCoveredOn.liftGen (fun _ hh => hh)
    (TgtSplitCoveredOn.liftGen (P' := fun Z => P2 (BVar.there Z)) hP h)

/-- Three-binder lift with a 3-level scope transport (`.there (.there (.there ·))`). -/
theorem TgtSplitCoveredOn.liftShift3 {s2 s2' : Sig} {Γt : Ctx s2'} {σt : Subst s2 s2'}
    {k1 k2 k3 : Kind} {b1 : Binding s2' k1} {b2 : Binding (s2',,k1) k2}
    {b3 : Binding ((s2',,k1),,k2) k3}
    {P : BVar s2 .cvar → Prop} {P3 : BVar (((s2,,k1),,k2),,k3) .cvar → Prop}
    (hP : ∀ Y0, P3 (BVar.there (BVar.there (BVar.there Y0))) → P Y0)
    (h : TgtSplitCoveredOn P Γt σt) :
    TgtSplitCoveredOn P3 (((Γt.push b1).push b2).push b3)
      (((σt.lift (k := k1)).lift (k := k2)).lift (k := k3)) :=
  TgtSplitCoveredOn.liftGen (fun _ hh => hh)
    (TgtSplitCoveredOn.liftGen (P' := fun Z => P3 (BVar.there Z)) (fun _ hh => hh)
      (TgtSplitCoveredOn.liftGen (P' := fun Z => P3 (BVar.there (BVar.there Z))) hP h))

/-- Four-binder lift with a 4-level scope transport. -/
theorem TgtSplitCoveredOn.liftShift4 {s2 s2' : Sig} {Γt : Ctx s2'} {σt : Subst s2 s2'}
    {k1 k2 k3 k4 : Kind} {b1 : Binding s2' k1} {b2 : Binding (s2',,k1) k2}
    {b3 : Binding ((s2',,k1),,k2) k3} {b4 : Binding (((s2',,k1),,k2),,k3) k4}
    {P : BVar s2 .cvar → Prop} {P4 : BVar ((((s2,,k1),,k2),,k3),,k4) .cvar → Prop}
    (hP : ∀ Y0, P4 (BVar.there (BVar.there (BVar.there (BVar.there Y0)))) → P Y0)
    (h : TgtSplitCoveredOn P Γt σt) :
    TgtSplitCoveredOn P4 ((((Γt.push b1).push b2).push b3).push b4)
      ((((σt.lift (k := k1)).lift (k := k2)).lift (k := k3)).lift (k := k4)) :=
  TgtSplitCoveredOn.liftGen (fun _ hh => hh)
    (TgtSplitCoveredOn.liftGen (P' := fun Z => P4 (BVar.there Z)) (fun _ hh => hh)
      (TgtSplitCoveredOn.liftGen (P' := fun Z => P4 (BVar.there (BVar.there Z))) (fun _ hh => hh)
        (TgtSplitCoveredOn.liftGen
          (P' := fun Z => P4 (BVar.there (BVar.there (BVar.there Z)))) hP h)))

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
  -- `subst`/`peaks` keep the pseudo-peak frozen; a `.cvar` atom cannot be `⊆` it.
  | pseudo_peak _ _ => simp only [CapyCaptureSet.subst, CapyCaptureSet.peaks] at h; cases h

/-- **Frozen-peak-after-substitution decomposition.**  A *frozen* peak of
    `cs.subst σ` traces back to a frozen peak of a cvar-atom image `(σ.cvar c0).applyAccess m`
    of `cs`.  Origin (`cs`) and context (`Γ`) are pseudo-peak free, so the only
    `pseudo_peak` introduced is by `σ` at a cvar atom — the keystone for routing a
    sub *frozen* peak back to the origin cvar that `σ` froze. -/
theorem CapyCaptureSet.peaks_subst_pseudo_mem {s1 s2 : Sig} {Γ : CapyCtx s2}
    {σ : CapySubst s1 s2} (hΓ : Γ.NoPseudoPeak) {C' : CapyCaptureSet s2} :
    ∀ {cs : CapyCaptureSet s1}, cs.NoPseudoPeak →
      (CapyCaptureSet.pseudo_peak C' ⊆ CapyCaptureSet.peaks Γ (CapyCaptureSet.subst cs σ)) →
      ∃ (c0 : BVar s1 .cvar) (m : Access),
        (CapyCaptureSet.pseudo_peak C') ⊆
          CapyCaptureSet.peaks Γ ((σ.cvar c0).applyAccess m) := by
  intro cs
  induction cs with
  | empty => intro _ h; simp only [CapyCaptureSet.subst, CapyCaptureSet.peaks] at h; cases h
  | union cs1 cs2 ih1 ih2 =>
    intro hcs h
    simp only [CapyCaptureSet.subst, CapyCaptureSet.peaks] at h
    cases hcs with
    | union hcs1 hcs2 =>
      cases h with
      | union_right_left h1 => exact ih1 hcs1 h1
      | union_right_right h2 => exact ih2 hcs2 h2
  | cvar m c0 => intro _ h; simp only [CapyCaptureSet.subst] at h; exact ⟨c0, m, h⟩
  | var m x =>
    intro _ h
    simp only [CapyCaptureSet.subst] at h
    exact absurd h
      (CapyCaptureSet.peaks_noPseudoPeak hΓ CapyCaptureSet.NoPseudoPeak.var).not_pseudo_subset
  | pseudo_peak C0 _ => intro hcs _; cases hcs

/-- Strengthening of `peaks_subst_pseudo_mem` that also exposes the *origin cvar
    occurrence* `{m c0} ⊆ cs` whose `σ`-image carries the frozen peak.  (Needed by the
    reverse frozen-item containment to place the content into `c0`'s origin lock item.) -/
theorem CapyCaptureSet.peaks_subst_pseudo_mem' {s1 s2 : Sig} {Γ : CapyCtx s2}
    {σ : CapySubst s1 s2} (hΓ : Γ.NoPseudoPeak) {C' : CapyCaptureSet s2} :
    ∀ {cs : CapyCaptureSet s1}, cs.NoPseudoPeak →
      (CapyCaptureSet.pseudo_peak C' ⊆ CapyCaptureSet.peaks Γ (CapyCaptureSet.subst cs σ)) →
      ∃ (c0 : BVar s1 .cvar) (m : Access),
        (CapyCaptureSet.cvar m c0) ⊆ cs ∧
        (CapyCaptureSet.pseudo_peak C') ⊆
          CapyCaptureSet.peaks Γ ((σ.cvar c0).applyAccess m) := by
  intro cs
  induction cs with
  | empty => intro _ h; simp only [CapyCaptureSet.subst, CapyCaptureSet.peaks] at h; cases h
  | union cs1 cs2 ih1 ih2 =>
    intro hcs h
    simp only [CapyCaptureSet.subst, CapyCaptureSet.peaks] at h
    cases hcs with
    | union hcs1 hcs2 =>
      cases h with
      | union_right_left h1 =>
        obtain ⟨c0, m, hocc, hp⟩ := ih1 hcs1 h1
        exact ⟨c0, m, CapyCaptureSet.Subset.union_right_left hocc, hp⟩
      | union_right_right h2 =>
        obtain ⟨c0, m, hocc, hp⟩ := ih2 hcs2 h2
        exact ⟨c0, m, CapyCaptureSet.Subset.union_right_right hocc, hp⟩
  | cvar m c0 =>
    intro _ h; simp only [CapyCaptureSet.subst] at h
    exact ⟨c0, m, CapyCaptureSet.Subset.refl, h⟩
  | var m x =>
    intro _ h
    simp only [CapyCaptureSet.subst] at h
    exact absurd h
      (CapyCaptureSet.peaks_noPseudoPeak hΓ CapyCaptureSet.NoPseudoPeak.var).not_pseudo_subset
  | pseudo_peak C0 _ => intro hcs _; cases hcs

/-! ### Pure bounds

`Subtyp.poly`/`tabs` retype a polymorphic bound only when it is a *shape* (pure)
type — the target `poly` bound is reconstructed as a `PureTy`.  A merely *closed*
type may have an impure poly bound, which the target subtyping cannot change, so
the type-level commutation needs the bound purity that well-formed source types
always carry (source `poly`/`tabs` bind `CapyPureTy`).  `PureBounds` records
exactly that, recursively. -/

/-- `PureBounds` (now defined at the source syntax layer, `Capybara/Syntax/Ty.lean`,
    so the `fresh` typing rule can carry it as a witness well-formedness premise)
    is preserved by renaming (it constrains only type-bound positions, which
    rename structurally). -/
theorem CapyTy.PureBounds.rename {sort : CapyTySort} {s1 : Sig} {T : CapyTy sort s1} :
    ∀ {s2 : Sig} (ρ : Rename s1 s2), CapyTy.PureBounds T → CapyTy.PureBounds (T.rename ρ) := by
  induction T with
  | arrow T1 cs E ih1 ih2 => intro _ ρ h; exact ⟨ih1 ρ.lift h.1, ih2 ρ.lift h.2⟩
  | poly S cs E ihS ihE => intro _ ρ h; exact ⟨h.1.rename ρ, ihS ρ h.2.1, ihE ρ.lift h.2.2⟩
  | cpoly cb cs E ihE => intro _ ρ h; exact ihE ρ.lift h
  | exi T ih => intro _ ρ h; exact ih ρ.lift h
  | typ T ih => intro _ ρ h; exact ih ρ h
  | top | tvar _ | unit | bool | cap _ | cell _ _ => intro _ _ _; exact trivial

/-- `PureBounds` is preserved by `refineCaptureSet` (it overwrites only the latent capture,
    not the type-bound positions). -/
theorem CapyTy.PureBounds.refineCaptureSet {s : Sig} {T : CapyTy .capt s}
    {cs : CapyCaptureSet s} (h : CapyTy.PureBounds T) :
    CapyTy.PureBounds (T.refineCaptureSet cs) := by
  cases T <;> exact h

/-- `CapyTy.NoPseudoPeak` is preserved by renaming. -/
theorem CapyTy.NoPseudoPeak.rename {sort : CapyTySort} {s1 : Sig} {T : CapyTy sort s1} :
    ∀ {s2 : Sig} (ρ : Rename s1 s2), T.NoPseudoPeak → (T.rename ρ).NoPseudoPeak := by
  induction T with
  | arrow T1 cs E ih1 ih2 => intro _ ρ h; exact ⟨ih1 ρ.lift h.1, h.2.1.rename ρ, ih2 ρ.lift h.2.2⟩
  | poly S cs E ihS ihE => intro _ ρ h; exact ⟨ihS ρ h.1, h.2.1.rename ρ, ihE ρ.lift h.2.2⟩
  | cpoly cb cs E ihE =>
    intro _ ρ h; cases cb with
    | unbound m => exact ⟨True.intro, h.2.1.rename ρ, ihE ρ.lift h.2.2⟩
    | bound csb => exact ⟨h.1.rename ρ, h.2.1.rename ρ, ihE ρ.lift h.2.2⟩
  | cap cs => intro _ ρ h; exact h.rename ρ
  | cell cs m => intro _ ρ h; exact h.rename ρ
  | exi T ih => intro _ ρ h; exact ih ρ.lift h
  | typ T ih => intro _ ρ h; exact ih ρ h
  | top | tvar _ | unit | bool => intro _ _ _; exact True.intro

/-- `CapyTy.NoPseudoPeak` is preserved by `refineCaptureSet` (the new latent capture must be
    pseudo-peak-free). -/
theorem CapyTy.NoPseudoPeak.refineCaptureSet {s : Sig} {T : CapyTy .capt s}
    {cs : CapyCaptureSet s} (h : T.NoPseudoPeak) (hcs : cs.NoPseudoPeak) :
    (T.refineCaptureSet cs).NoPseudoPeak := by
  cases T with
  | arrow T1 cs0 E => exact ⟨h.1, hcs, h.2.2⟩
  | poly S cs0 E => exact ⟨h.1, hcs, h.2.2⟩
  | cpoly cb cs0 E => exact ⟨h.1, hcs, h.2.2⟩
  | cap cs0 => exact hcs
  | cell cs0 m => exact hcs
  | top | tvar _ | unit | bool => exact True.intro

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

/-- `SubstTvarCompat` preserved by a source *term*-variable binder (`consVar`): the binder
    adds no target tvar, so every source tvar is `.there` and the target map is unchanged. -/
theorem SubstTvarCompat.consVar {s1 s1' s2 s2' : Sig} {scSub : SrcCtx s1' s2'}
    {scOrig : SrcCtx s1 s2} {σ : CapySubst s1 s1'} {σt : Subst s2 s2'}
    {bvS : Option (BVar s2' .var)} {bvO : Option (BVar s2 .var)}
    {csS : CaptureSet s2'} {csO : CaptureSet s2}
    (h : SubstTvarCompat scSub scOrig σ σt) :
    SubstTvarCompat (.cons (.var bvS csS) scSub) (.cons (.var bvO csO) scOrig) σ.lift σt := by
  intro X
  cases X with
  | there X0 =>
    obtain ⟨Z0, hZ, hlk⟩ := h X0
    refine ⟨.there Z0, ?_, ?_⟩
    · rw [CapySubst.lift_there_tvar_eq, hZ]; rfl
    · simp only [SrcCtx.lookupTVar]; exact hlk

/-- `SubstTvarCompat` preserved by a source *capture*-variable binder (`consCVar`, any target
    cvar): the binder adds no target tvar, so every source tvar is `.there`. -/
theorem SubstTvarCompat.consCVar {s1 s1' s2 s2' : Sig} {scSub : SrcCtx s1' s2'}
    {scOrig : SrcCtx s1 s2} {σ : CapySubst s1 s1'} {σt : Subst s2 s2'}
    {cS : BVar s2' .cvar} {cO : BVar s2 .cvar}
    (h : SubstTvarCompat scSub scOrig σ σt) :
    SubstTvarCompat (.cons (.cvar cS) scSub) (.cons (.cvar cO) scOrig) σ.lift σt := by
  intro X
  cases X with
  | there X0 =>
    obtain ⟨Z0, hZ, hlk⟩ := h X0
    refine ⟨.there Z0, ?_, ?_⟩
    · rw [CapySubst.lift_there_tvar_eq, hZ]; rfl
    · simp only [SrcCtx.lookupTVar]; exact hlk

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

/-- Alignment is preserved by a fresh source term binder whose capture image is the
    binder's own declared latent capture `⟦T.captureSet⟧` (the *aligned* surrogate of
    the `arrow` compiler's `ctxLock`/`ctxDomain`, which instead store the self-capture
    `{cx}`). -/
theorem SrcAligned.consVar {s s2 : Sig} {Γ : CapyCtx s} {sc : SrcCtx s s2}
    {T : CapyTy .capt s} {bv : Option (BVar s2 .var)}
    (h : SrcAligned Γ sc) :
    SrcAligned (Γ.push_var T)
      (.cons (.var bv (CapyCaptureSet.compile T.captureSet sc)) sc) := by
  intro x U hlook
  cases hlook with
  | here => exact CapyCaptureSet.compile_captureSet_weaken.symm
  | there hlook0 =>
    exact (h hlook0).trans CapyCaptureSet.compile_captureSet_weaken.symm

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

/-- **Converse of `peakSepCtx_HasTwoDistinct`.**  Two distinct *stable* peaks give
    `HasTwoDistinct` compiled `peakKeyItem`s — the `sep_lock` premise for cross pairs.
    (Only stable peaks survive into `peakSepCtx`'s filtered fold; an unstable peak's
    item is simply not in the lock.) -/
theorem peakSepCtx_HasTwoDistinct_of {s1 s2 : Sig} {Γ : CapyCtx s1} {P : CapyPeakSet s1}
    {sc : SrcCtx s1 s2} {p1 p2 : Peak s1}
    (hc1 : p1 ∈ (peakList P).filter (fun p => decide (Peak.IsStable Γ p)))
    (hc2 : p2 ∈ (peakList P).filter (fun p => decide (Peak.IsStable Γ p)))
    (hne : p1 ≠ p2) :
    SepCtx.HasTwoDistinct (peakSepCtx Γ P sc)
      (CapyCaptureSet.compile (peakKeyItem P p1) sc)
      (CapyCaptureSet.compile (peakKeyItem P p2) sc) := by
  simp only [peakSepCtx]
  exact SepCtx.HasTwoDistinct.foldl
    (g := fun p => CapyCaptureSet.compile (peakKeyItem P p) sc)
    ((peakList P).filter (fun p => decide (Peak.IsStable Γ p))) hc1 hc2 hne

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
theorem peakSepCtx_subst {s1 s2 s2' : Sig} {Γ : CapyCtx s1} {P : CapyPeakSet s1}
    {sc : SrcCtx s1 s2} {σt : Subst s2 s2'} :
    (peakSepCtx Γ P sc).subst σt
      = ((peakList P).filter (fun p => decide (Peak.IsStable Γ p))).foldl
          (fun K p => SepCtx.cons K ((CapyCaptureSet.compile (peakKeyItem P p) sc).subst σt))
          SepCtx.empty := by
  simp only [peakSepCtx]
  rw [SepCtx.subst_foldl]
  rfl

/-- **Converse for the substituted lock `Ψ_R`.**  Distinct *stable* peaks give
    `HasTwoDistinct` *substituted* items — the `sep_lock` premise against the
    in-context merged lock. -/
theorem peakSepCtx_subst_HasTwoDistinct_of {s1 s2 s2' : Sig} {Γ : CapyCtx s1} {P : CapyPeakSet s1}
    {sc : SrcCtx s1 s2} {σt : Subst s2 s2'} {p1 p2 : Peak s1}
    (hc1 : p1 ∈ (peakList P).filter (fun p => decide (Peak.IsStable Γ p)))
    (hc2 : p2 ∈ (peakList P).filter (fun p => decide (Peak.IsStable Γ p)))
    (hne : p1 ≠ p2) :
    SepCtx.HasTwoDistinct ((peakSepCtx Γ P sc).subst σt)
      ((CapyCaptureSet.compile (peakKeyItem P p1) sc).subst σt)
      ((CapyCaptureSet.compile (peakKeyItem P p2) sc).subst σt) := by
  rw [peakSepCtx_subst]
  exact SepCtx.HasTwoDistinct.foldl
    (g := fun p => (CapyCaptureSet.compile (peakKeyItem P p) sc).subst σt)
    ((peakList P).filter (fun p => decide (Peak.IsStable Γ p))) hc1 hc2 hne

/-- `SepCtx.rename` distributes over a `foldl`-built context (push the rename inside). -/
theorem SepCtx.rename_foldl {α : Type} {s1 s2 : Sig} {g : α → CaptureSet s1} {ρ : Rename s1 s2}
    (L : List α) :
    ∀ {acc : SepCtx s1}, (L.foldl (fun K c => SepCtx.cons K (g c)) acc).rename ρ
      = L.foldl (fun K c => SepCtx.cons K ((g c).rename ρ)) (acc.rename ρ) := by
  induction L with
  | nil => intro acc; rfl
  | cons c L' ih => intro acc; exact ih

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

/-- Injectivity for a fresh source cvar mapped to the *second-newest* target cvar
    `.there .here` over a doubly-`succ`-renamed context (the `arrow`-domain `[c]` binder, which
    sits below the freshly-bound `[cx]`). -/
theorem SrcCtx.CVarInjective.consCVarThereHere {s1 s2 : Sig} {sc : SrcCtx s1 s2}
    (h : sc.CVarInjective) :
    (SrcCtx.cons (.cvar (BVar.there BVar.here))
      ((sc.rename (Rename.succ (k := Kind.cvar))).rename
        (Rename.succ (k := Kind.cvar)))).CVarInjective := by
  intro c1 c2 he
  cases c1 with
  | here =>
    cases c2 with
    | here => rfl
    | there c2' =>
      simp only [SrcCtx.lookupCVar, SrcCtx.lookupCVar_rename, Rename.succ] at he
      exact absurd he (by simp)
  | there c1' =>
    cases c2 with
    | here =>
      simp only [SrcCtx.lookupCVar, SrcCtx.lookupCVar_rename, Rename.succ] at he
      exact absurd he (by simp)
    | there c2' =>
      simp only [SrcCtx.lookupCVar, SrcCtx.lookupCVar_rename, Rename.succ] at he
      exact congrArg BVar.there (h (BVar.there.inj (BVar.there.inj he)))

/-- Injectivity for a fresh source cvar mapped to the *third-newest* target cvar
    `.there (.there .here)` over a triply-`succ`-renamed context — the `abs`
    compilation's body tower, where two target cvars (`[c]`, `[cx]`) and the
    target term binder (`x`) sit above the base. -/
theorem SrcCtx.CVarInjective.consCVarThereThereHere {s1 s2 : Sig} {sc : SrcCtx s1 s2}
    (h : sc.CVarInjective) :
    (SrcCtx.cons (.cvar (BVar.there (BVar.there BVar.here)))
      (((sc.rename (Rename.succ (k := Kind.cvar))).rename
          (Rename.succ (k := Kind.cvar))).rename
        (Rename.succ (k := Kind.var)))).CVarInjective := by
  intro c1 c2 he
  cases c1 with
  | here =>
    cases c2 with
    | here => rfl
    | there c2' =>
      simp only [SrcCtx.lookupCVar, SrcCtx.lookupCVar_rename, Rename.succ] at he
      exact absurd he (by simp)
  | there c1' =>
    cases c2 with
    | here =>
      simp only [SrcCtx.lookupCVar, SrcCtx.lookupCVar_rename, Rename.succ] at he
      exact absurd he (by simp)
    | there c2' =>
      simp only [SrcCtx.lookupCVar, SrcCtx.lookupCVar_rename, Rename.succ] at he
      exact congrArg BVar.there
        (h (BVar.there.inj (BVar.there.inj (BVar.there.inj he))))

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

/-- `peakPseudos` is `Nodup`. -/
theorem peakPseudos_nodup {s : Sig} (P : CapyPeakSet s) : (peakPseudos P).Nodup :=
  dedup_nodup _

/-- `peakList` is `Nodup`: each track is `Nodup` (dedup'd, mapped by an injective
    constructor) and the two tracks are disjoint (cvar peaks vs pseudo peaks). -/
theorem peakList_nodup {s : Sig} (P : CapyPeakSet s) : (peakList P).Nodup := by
  refine List.nodup_append.mpr ⟨(peakCvars_nodup P).map (fun _ _ h => Peak.cvar.inj h),
    (peakPseudos_nodup P).map (fun _ _ h => Peak.pseudo.inj h), ?_⟩
  intro p hpc
  obtain ⟨c, _, hc⟩ := List.mem_map.mp hpc
  subst hc
  simp [List.mem_map]

/-- A cvar peak in `peakList` comes from `peakCvars`. -/
theorem mem_peakCvars_of_cvar_mem {s : Sig} {P : CapyPeakSet s} {d : BVar s .cvar}
    (h : Peak.cvar d ∈ peakList P) : d ∈ peakCvars P := by
  simp only [peakList, List.mem_append, List.mem_map] at h
  rcases h with ⟨d', hd', he⟩ | ⟨D, _, he⟩
  · exact Peak.cvar.inj he ▸ hd'
  · exact absurd he (by simp)

/-- A pseudo peak in `peakList` comes from `peakPseudos`. -/
theorem mem_peakPseudos_of_pseudo_mem {s : Sig} {P : CapyPeakSet s} {D : CapyCaptureSet s}
    (h : Peak.pseudo D ∈ peakList P) : D ∈ peakPseudos P := by
  simp only [peakList, List.mem_append, List.mem_map] at h
  rcases h with ⟨d', _, he⟩ | ⟨D', hD', he⟩
  · exact absurd he (by simp)
  · exact Peak.pseudo.inj he ▸ hD'

/-- A `peakCvars` member is a cvar peak of `peakList`. -/
theorem cvar_mem_peakList {s : Sig} {P : CapyPeakSet s} {d : BVar s .cvar}
    (h : d ∈ peakCvars P) : Peak.cvar d ∈ peakList P :=
  List.mem_append_left _ (List.mem_map_of_mem h)

/-- A `peakPseudos` member is a pseudo peak of `peakList`. -/
theorem pseudo_mem_peakList {s : Sig} {P : CapyPeakSet s} {D : CapyCaptureSet s}
    (h : D ∈ peakPseudos P) : Peak.pseudo D ∈ peakList P :=
  List.mem_append_right _ (List.mem_map_of_mem h)

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

/-- **Distinct lock items come from distinct *stable* peaks.**  Strengthens
    `peakSepCtx_HasTwoDistinct` with `c1 ≠ c2` (needed for the `sep_droppable`
    dispatch), via the `Nodup`ness of `peakCvars` (preserved under `List.filter`). -/
theorem peakSepCtx_HasTwoDistinct_ne {s1 s2 : Sig} {Γ : CapyCtx s1} {P : CapyPeakSet s1}
    {sc : SrcCtx s1 s2} {C1 C2 : CaptureSet s2}
    (h : SepCtx.HasTwoDistinct (peakSepCtx Γ P sc) C1 C2) :
    ∃ p1 ∈ (peakList P).filter (fun p => decide (Peak.IsStable Γ p)),
      ∃ p2 ∈ (peakList P).filter (fun p => decide (Peak.IsStable Γ p)), p1 ≠ p2 ∧
      ((C1 = CapyCaptureSet.compile (peakKeyItem P p1) sc ∧
          C2 = CapyCaptureSet.compile (peakKeyItem P p2) sc) ∨
       (C1 = CapyCaptureSet.compile (peakKeyItem P p2) sc ∧
          C2 = CapyCaptureSet.compile (peakKeyItem P p1) sc)) :=
  SepCtx.HasTwoDistinct.foldl_nodup (g := fun p => CapyCaptureSet.compile (peakKeyItem P p) sc) h
    ((peakList P).filter (fun p => decide (Peak.IsStable Γ p)))
    ((peakList_nodup P).filter _) rfl

/-- **Inversion for the substituted + lock-renamed lock `Ψ_R`** (the backward `satB`
    direction): two `HasTwoDistinct` items of `((peakSepCtx Γ P sc).subst σt).rename ρ` come
    from two *distinct stable* peaks of `P`.  No item-injectivity needed — `peakList` is
    `Nodup` (hence so is its filter). -/
theorem peakSepCtx_subst_rename_HasTwoDistinct_ne {s1 s2 s2' s2'' : Sig} {Γ : CapyCtx s1}
    {P : CapyPeakSet s1} {sc : SrcCtx s1 s2} {σt : Subst s2 s2'} {ρ : Rename s2' s2''}
    {C1 C2 : CaptureSet s2''}
    (h : SepCtx.HasTwoDistinct (((peakSepCtx Γ P sc).subst σt).rename ρ) C1 C2) :
    ∃ p1 ∈ (peakList P).filter (fun p => decide (Peak.IsStable Γ p)),
      ∃ p2 ∈ (peakList P).filter (fun p => decide (Peak.IsStable Γ p)), p1 ≠ p2 ∧
      ((C1 = ((CapyCaptureSet.compile (peakKeyItem P p1) sc).subst σt).rename ρ ∧
          C2 = ((CapyCaptureSet.compile (peakKeyItem P p2) sc).subst σt).rename ρ) ∨
       (C1 = ((CapyCaptureSet.compile (peakKeyItem P p2) sc).subst σt).rename ρ ∧
          C2 = ((CapyCaptureSet.compile (peakKeyItem P p1) sc).subst σt).rename ρ)) := by
  rw [peakSepCtx_subst, SepCtx.rename_foldl] at h
  exact SepCtx.HasTwoDistinct.foldl_nodup
    (g := fun p => ((CapyCaptureSet.compile (peakKeyItem P p) sc).subst σt).rename ρ) h
    ((peakList P).filter (fun p => decide (Peak.IsStable Γ p)))
    ((peakList_nodup P).filter _) (by simp only [SepCtx.rename])

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

/-- A peak item is `NoPseudoPeak` (it is built purely from `.cvar` atoms). -/
theorem peakItem_noPseudoPeak {s : Sig} {P : CapyPeakSet s} {c : BVar s .cvar} :
    (peakItem P c).NoPseudoPeak := by
  simp only [peakItem]
  generalize accessedAt P c = l
  induction l with
  | nil => exact CapyCaptureSet.NoPseudoPeak.empty
  | cons a as ih =>
    simp only [List.foldr_cons]
    exact CapyCaptureSet.NoPseudoPeak.union CapyCaptureSet.NoPseudoPeak.cvar ih

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
  | pseudo_peak _ _ => simp only [accessedAt.go] at h; cases h

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
  | pseudo_peak _ _ => cases h

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

/-- The local `dedup` only contains original members. -/
theorem mem_dedup_inv {α : Type} [DecidableEq α] {a : α} {l : List α} (h : a ∈ dedup l) :
    a ∈ l := by
  induction l with
  | nil => exact h
  | cons b bs ih =>
    simp only [dedup] at h
    split at h
    · exact List.mem_cons_of_mem _ (ih h)
    · rcases List.mem_cons.mp h with rfl | hm
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (ih hm)

/-- A member of `peakCvars.go cs` has a `.cvar`-occurrence in `cs`. -/
theorem peakCvars_go_occ {s : Sig} {c : BVar s .cvar} :
    ∀ {cs : CapyCaptureSet s}, c ∈ peakCvars.go cs → ∃ a, (CapyCaptureSet.cvar a c) ⊆ cs := by
  intro cs
  induction cs with
  | empty => intro h; simp only [peakCvars.go, List.not_mem_nil] at h
  | union cs1 cs2 ih1 ih2 =>
    intro h
    simp only [peakCvars.go, List.mem_append] at h
    rcases h with h1 | h2
    · obtain ⟨a, ha⟩ := ih1 h1; exact ⟨a, CapyCaptureSet.Subset.union_right_left ha⟩
    · obtain ⟨a, ha⟩ := ih2 h2; exact ⟨a, CapyCaptureSet.Subset.union_right_right ha⟩
  | cvar a' c' =>
    intro h; simp only [peakCvars.go, List.mem_singleton] at h
    subst h; exact ⟨a', CapyCaptureSet.Subset.refl⟩
  | var a' x => intro h; simp only [peakCvars.go, List.not_mem_nil] at h
  | pseudo_peak _ _ => intro h; simp only [peakCvars.go, List.not_mem_nil] at h

/-- A peak cvar has an access-mode occurrence in the peak set. -/
theorem peakCvars_occ {s : Sig} {P : CapyPeakSet s} {c : BVar s .cvar}
    (h : c ∈ peakCvars P) : ∃ a, (CapyCaptureSet.cvar a c) ⊆ P.cs :=
  peakCvars_go_occ (mem_dedup_inv (by simpa only [peakCvars] using h))

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
  | pseudo_peak _ _ => cases h

/-- A `.cvar`-occurrence of `c` puts `c` among the (deduplicated) peak cvars. -/
theorem cvar_mem_peakCvars {s : Sig} {P : CapyPeakSet s} {c : BVar s .cvar} {a : Access}
    (h : (CapyCaptureSet.cvar a c) ⊆ P.cs) : c ∈ peakCvars P := by
  simp only [peakCvars]
  exact mem_dedup (cvar_subset_peakCvars_go P.cs h)

/-- A `pseudo_peak C` occurrence records its mode-erased base in `peakPseudos.go`. -/
theorem pseudo_subset_peakPseudos_go {s : Sig} {C : CapyCaptureSet s} (cs : CapyCaptureSet s)
    (h : (CapyCaptureSet.pseudo_peak C) ⊆ cs) : C.modeErase ∈ peakPseudos.go cs := by
  induction cs with
  | empty => cases h
  | union cs1 cs2 ih1 ih2 =>
    simp only [peakPseudos.go, List.mem_append]
    cases h with
    | union_right_left h1 => exact Or.inl (ih1 h1)
    | union_right_right h2 => exact Or.inr (ih2 h2)
  | cvar a c => cases h
  | var a x => cases h
  | pseudo_peak C' ih => cases h; simp [peakPseudos.go]

/-- A `pseudo_peak C` occurrence puts its mode-erased base among the peak pseudos. -/
theorem pseudoBase_mem_peakPseudos {s : Sig} {P : CapyPeakSet s} {C : CapyCaptureSet s}
    (h : (CapyCaptureSet.pseudo_peak C) ⊆ P.cs) : C.modeErase ∈ peakPseudos P :=
  mem_dedup (pseudo_subset_peakPseudos_go P.cs h)

/-- A member of `peakPseudos.go cs` has a `pseudo_peak`-occurrence in `cs` whose
    mode-erased base it is. -/
theorem peakPseudos_go_occ {s : Sig} {D : CapyCaptureSet s} :
    ∀ {cs : CapyCaptureSet s}, D ∈ peakPseudos.go cs →
      ∃ C, (CapyCaptureSet.pseudo_peak C) ⊆ cs ∧ C.modeErase = D := by
  intro cs
  induction cs with
  | empty => intro h; simp only [peakPseudos.go, List.not_mem_nil] at h
  | union cs1 cs2 ih1 ih2 =>
    intro h
    simp only [peakPseudos.go, List.mem_append] at h
    rcases h with h1 | h2
    · obtain ⟨C, hC, hCm⟩ := ih1 h1; exact ⟨C, CapyCaptureSet.Subset.union_right_left hC, hCm⟩
    · obtain ⟨C, hC, hCm⟩ := ih2 h2; exact ⟨C, CapyCaptureSet.Subset.union_right_right hC, hCm⟩
  | cvar a c => intro h; simp only [peakPseudos.go, List.not_mem_nil] at h
  | var a x => intro h; simp only [peakPseudos.go, List.not_mem_nil] at h
  | pseudo_peak C _ =>
    intro h; simp only [peakPseudos.go, List.mem_singleton] at h
    exact ⟨C, CapyCaptureSet.Subset.refl, h.symm⟩

/-- A peak pseudo base has a `pseudo_peak`-occurrence in the peak set. -/
theorem peakPseudos_occ {s : Sig} {P : CapyPeakSet s} {D : CapyCaptureSet s}
    (h : D ∈ peakPseudos P) : ∃ C, (CapyCaptureSet.pseudo_peak C) ⊆ P.cs ∧ C.modeErase = D :=
  peakPseudos_go_occ (mem_dedup_inv (by simpa only [peakPseudos] using h))

/-- A pseudo-peak-free capture set collects no frozen bases. -/
theorem peakPseudos_go_nil_of_noPseudoPeak {s : Sig} {cs : CapyCaptureSet s}
    (h : cs.NoPseudoPeak) : peakPseudos.go cs = [] := by
  induction h with
  | empty => rfl
  | cvar => rfl
  | var => rfl
  | union _ _ ih1 ih2 => simp only [peakPseudos.go, ih1, ih2, List.append_nil]

/-- A peak set whose underlying capture set is pseudo-peak-free has no frozen peaks in its
    `peakList` — so every peak it lists is a `cvar`. -/
theorem pseudo_not_mem_peakList_of_noPseudoPeak {s : Sig} {P : CapyPeakSet s}
    {D : CapyCaptureSet s} (hnp : P.cs.NoPseudoPeak)
    (h : Peak.pseudo D ∈ peakList P) : False := by
  have hD := mem_peakPseudos_of_pseudo_mem h
  simp only [peakPseudos] at hD
  rw [peakPseudos_go_nil_of_noPseudoPeak hnp] at hD
  simp [dedup] at hD

/-- A `pseudo_peak C` occurrence belongs to the pseudo item of its mode-erased base. -/
theorem pseudo_subset_pseudoItem_go {s : Sig} {C D : CapyCaptureSet s} (hD : C.modeErase = D)
    (cs : CapyCaptureSet s) (h : (CapyCaptureSet.pseudo_peak C) ⊆ cs) :
    (CapyCaptureSet.pseudo_peak C) ⊆ pseudoItem.go D cs := by
  induction cs with
  | empty => cases h
  | union cs1 cs2 ih1 ih2 =>
    simp only [pseudoItem.go]
    cases h with
    | union_right_left h1 => exact .union_right_left (ih1 h1)
    | union_right_right h2 => exact .union_right_right (ih2 h2)
  | cvar a c => cases h
  | var a x => cases h
  | pseudo_peak C' ih =>
    cases h
    simp only [pseudoItem.go]
    rw [if_pos hD]
    exact CapyCaptureSet.Subset.refl

/-- A `pseudo_peak C` occurrence in `P.cs` belongs to the pseudo item of its base. -/
theorem pseudo_subset_pseudoItem {s : Sig} {P : CapyPeakSet s} {C : CapyCaptureSet s}
    (h : (CapyCaptureSet.pseudo_peak C) ⊆ P.cs) :
    (CapyCaptureSet.pseudo_peak C) ⊆ pseudoItem P (C.modeErase) := by
  simp only [pseudoItem]
  exact pseudo_subset_pseudoItem_go rfl P.cs h

/-- **The PEAK TRACER (sorry-free).**  A target cvar atom of the compiled peak set
    `⟦P.cs⟧` belongs to the compiled item of SOME peak `p ∈ peakList P` (a cvar peak
    when the atom is a source cvar, a frozen peak when it sits inside a frozen
    content).  This is the lock-side source tracer that finally handles frozen peaks —
    built on the local `compile_atom_source`. -/
theorem compile_atom_peak {s1 s2 : Sig} {P : CapyPeakSet s1} {sc : SrcCtx s1 s2}
    {m : Access} {Z : BVar s2 .cvar}
    (h : (CaptureSet.cvar m Z) ⊆ CapyCaptureSet.compile P.cs sc) :
    ∃ p ∈ peakList P, (CaptureSet.cvar m Z) ⊆ CapyCaptureSet.compile (peakKeyItem P p) sc := by
  rcases CapyCaptureSet.compile_atom_source P.h h with ⟨c, hlk, hsub⟩ | ⟨C, hCsub, hZsub⟩
  · refine ⟨Peak.cvar c, cvar_mem_peakList (cvar_mem_peakCvars hsub), ?_⟩
    have h2 := CapyCaptureSet.compile_subset (sc := sc) (cvar_subset_peakItem hsub)
    have heq : CapyCaptureSet.compile (CapyCaptureSet.cvar m c) sc = CaptureSet.cvar m Z := by
      simp only [CapyCaptureSet.compile, hlk]
    rw [heq] at h2
    exact h2
  · refine ⟨Peak.pseudo C.modeErase, pseudo_mem_peakList (pseudoBase_mem_peakPseudos hCsub), ?_⟩
    have h2 := CapyCaptureSet.compile_subset (sc := sc) (pseudo_subset_pseudoItem hCsub)
    simp only [CapyCaptureSet.compile] at h2
    exact CaptureSet.Subset.trans hZsub h2

/-- A cvar peak item sits inside the peak set (each occurrence is in `P.cs`). -/
theorem peakItem_subset {s : Sig} {P : CapyPeakSet s} {c : BVar s .cvar} :
    peakItem P c ⊆ P.cs := by
  simp only [peakItem]
  have key : ∀ (l : List Access), (∀ a ∈ l, (CapyCaptureSet.cvar a c) ⊆ P.cs) →
      l.foldr (fun a acc => CapyCaptureSet.cvar a c ∪ acc) .empty ⊆ P.cs := by
    intro l
    induction l with
    | nil => intro _; exact CapyCaptureSet.Subset.empty
    | cons a' l' ih =>
      intro hl
      exact CapyCaptureSet.Subset.union_left (hl a' List.mem_cons_self)
        (ih (fun a ha => hl a (List.mem_cons_of_mem _ ha)))
  exact key _ (fun a ha => accessedAt_go_subset _ (by simpa only [accessedAt] using ha))

/-- A pseudo item sits inside the peak set. -/
theorem pseudoItem_go_subset {s : Sig} {D : CapyCaptureSet s} (cs : CapyCaptureSet s) :
    pseudoItem.go D cs ⊆ cs := by
  induction cs with
  | empty => exact CapyCaptureSet.Subset.refl
  | union cs1 cs2 ih1 ih2 =>
    simp only [pseudoItem.go]
    exact CapyCaptureSet.Subset.union_left
      (CapyCaptureSet.Subset.union_right_left ih1)
      (CapyCaptureSet.Subset.union_right_right ih2)
  | cvar a c => exact CapyCaptureSet.Subset.empty
  | var a x => exact CapyCaptureSet.Subset.empty
  | pseudo_peak C ih =>
    simp only [pseudoItem.go]
    split
    · exact CapyCaptureSet.Subset.refl
    · exact CapyCaptureSet.Subset.empty

theorem pseudoItem_subset {s : Sig} {P : CapyPeakSet s} {D : CapyCaptureSet s} :
    pseudoItem P D ⊆ P.cs := pseudoItem_go_subset P.cs

/-- Every peak's item sits inside the peak set. -/
theorem peakKeyItem_subset {s : Sig} {P : CapyPeakSet s} (p : Peak s) :
    peakKeyItem P p ⊆ P.cs := by
  cases p with
  | cvar c => exact peakItem_subset
  | pseudo D => exact pseudoItem_subset

/-! ### `PeakSubstIso`: the non-merging per-peak correspondence

`compile_subst_subtyp` is only TRUE for substitutions that do not *merge* two
distinct origin peaks into one sub-peak (the backward lock-change Satisfy is false
under merging, and the forward pseudo cases would collide).  `openCVar` — the only
real caller — is non-merging: it sends the opened cvar to a frozen `pseudo_peak`
(a fresh, distinct separation item) and every other cvar to itself.  We capture
exactly this as an *injective* map `toPeak` sending each origin cvar to the single
sub-peak (cvar or frozen) that `σ` substitutes for it. -/

/-- The single-atom capture set a peak stands for: a cvar peak is the `ε`-mode cvar
    atom (the identity image), a frozen peak is its `pseudo_peak`. -/
def Peak.asCaptureSet : Peak s → CapyCaptureSet s
| .cvar c => CapyCaptureSet.cvar (.M .epsilon) c
| .pseudo C => CapyCaptureSet.pseudo_peak C

theorem Peak.asCaptureSet_rename {s1 s2 : Sig} (p : Peak s1) (f : Rename s1 s2) :
    p.asCaptureSet.rename f = (p.rename f).asCaptureSet := by
  cases p with
  | cvar c => rfl
  | pseudo C => rfl

theorem Peak.rename_inj {s1 s2 : Sig} {f : Rename s1 s2} (hinj : f.Injective) :
    Function.Injective (fun p : Peak s1 => p.rename f) := by
  intro p1 p2 h
  cases p1 with
  | cvar c1 =>
    cases p2 with
    | cvar c2 =>
      simp only [Peak.rename, Peak.cvar.injEq] at h
      exact congrArg Peak.cvar (hinj .cvar h)
    | pseudo C2 => simp only [Peak.rename] at h; exact absurd h (by simp)
  | pseudo C1 =>
    cases p2 with
    | cvar c2 => simp only [Peak.rename] at h; exact absurd h (by simp)
    | pseudo C2 =>
      simp only [Peak.rename, Peak.pseudo.injEq] at h
      exact congrArg Peak.pseudo (CapyCaptureSet.rename_inj hinj h)

/-- A renamed peak is frozen only if the original was. -/
theorem Peak.rename_eq_pseudo_inv {s1 s2 : Sig} {p : Peak s1} {f : Rename s1 s2}
    {D : CapyCaptureSet s2} (h : p.rename f = Peak.pseudo D) : ∃ D0, p = Peak.pseudo D0 := by
  cases p with
  | cvar c => simp only [Peak.rename] at h; exact absurd h (by simp)
  | pseudo C0 => exact ⟨C0, rfl⟩

/-- The induced peak correspondence of a non-merging substitution.  `uniqueFrozen`
    records that at most one origin cvar is frozen (`openCVar` freezes only the opened
    binder; `.lift` shifts that single frozen source) — it makes the pseudo–pseudo peak
    pairs vacuous. -/
structure PeakSubstIso {s1 s2 : Sig} (σ : CapySubst s1 s2) where
  toPeak : BVar s1 .cvar → Peak s2
  image : ∀ c, σ.cvar c = (toPeak c).asCaptureSet
  inj : Function.Injective toPeak
  uniqueFrozen : ∀ {c1 c2 : BVar s1 .cvar} {D1 D2 : CapyCaptureSet s2},
    toPeak c1 = Peak.pseudo D1 → toPeak c2 = Peak.pseudo D2 → c1 = c2

/-- The lifted peak map: the new head cvar (present only for a cvar binder) maps to
    itself; everything else shifts through `succ`.  A standalone `def` so its equation
    lemmas reduce by `rfl`. -/
def liftToPeak {s1 s2 : Sig} : {k : Kind} → (g : BVar s1 .cvar → Peak s2) →
    BVar (s1,,k) .cvar → Peak (s2,,k)
| .cvar, _, .here => Peak.cvar .here
| _, g, .there x => (g x).rename Rename.succ

/-- The `openCVar` peak map: the opened cvar becomes the frozen base, the rest are
    identity cvars. -/
def openCVarToPeak {s : Sig} (C : CapyCaptureSet s) : BVar (s,C) .cvar → Peak s
| .here => Peak.pseudo C
| .there x => Peak.cvar x

/-- Lifting under any binder preserves the correspondence. -/
def PeakSubstIso.lift {s1 s2 : Sig} {σ : CapySubst s1 s2} (h : PeakSubstIso σ) (k : Kind) :
    PeakSubstIso (σ.lift (k := k)) where
  toPeak := liftToPeak h.toPeak
  image := by
    intro c
    cases c with
    | here => simp only [liftToPeak, Peak.asCaptureSet]; rfl
    | there x =>
      rw [CapySubst.lift_there_cvar_eq, h.image x, Peak.asCaptureSet_rename]
      simp only [liftToPeak]
  inj := by
    intro c1 c2 h12
    cases c1 with
    | here =>
      cases c2 with
      | here => rfl
      | there x2 =>
        simp only [liftToPeak] at h12
        cases hp : h.toPeak x2 <;> rw [hp] at h12 <;> simp [Peak.rename, Rename.succ] at h12
    | there x1 =>
      cases c2 with
      | here =>
        simp only [liftToPeak] at h12
        cases hp : h.toPeak x1 <;> rw [hp] at h12 <;> simp [Peak.rename, Rename.succ] at h12
      | there x2 =>
        simp only [liftToPeak] at h12
        exact congrArg BVar.there (h.inj (Peak.rename_inj Rename.injective_succ h12))
  uniqueFrozen := by
    intro c1 c2 D1 D2 h1 h2
    cases c1 with
    | here => simp only [liftToPeak] at h1; exact absurd h1 (by simp)
    | there x1 =>
      cases c2 with
      | here => simp only [liftToPeak] at h2; exact absurd h2 (by simp)
      | there x2 =>
        simp only [liftToPeak] at h1 h2
        obtain ⟨D1', hx1⟩ := Peak.rename_eq_pseudo_inv h1
        obtain ⟨D2', hx2⟩ := Peak.rename_eq_pseudo_inv h2
        exact congrArg BVar.there (h.uniqueFrozen hx1 hx2)

/-- The image of a peak under a substitution iso `hiso2`: a `cvar` peak follows
    `hiso2.toPeak` (which may itself be a `cvar` or a frozen peak), a frozen peak's
    base is simply substituted (`hiso2` never dissolves an already-frozen peak). -/
def Peak.substByIso {s2 s3 : Sig} {σ2 : CapySubst s2 s3} (hiso2 : PeakSubstIso σ2) :
    Peak s2 → Peak s3
| .cvar c => hiso2.toPeak c
| .pseudo D => Peak.pseudo (CapyCaptureSet.subst D σ2)

/-- `asCaptureSet` commutes with `substByIso`: substituting (via `σ2`) the single atom a
    peak stands for equals the atom of its `substByIso` image.  The `cvar` case uses
    `hiso2.image` after noting `applyAccess (.M .epsilon)` is the identity; the frozen
    case is the `pseudo_peak` substitution equation. -/
theorem Peak.asCaptureSet_substByIso {s2 s3 : Sig} {σ2 : CapySubst s2 s3}
    (hiso2 : PeakSubstIso σ2) (p : Peak s2) :
    CapyCaptureSet.subst p.asCaptureSet σ2 = (p.substByIso hiso2).asCaptureSet := by
  cases p with
  | cvar c =>
    simp only [Peak.asCaptureSet, Peak.substByIso, CapyCaptureSet.subst,
      CapyCaptureSet.applyAccess_M, CapyCaptureSet.applyMut_epsilon]
    exact hiso2.image c
  | pseudo D =>
    simp only [Peak.asCaptureSet, Peak.substByIso, CapyCaptureSet.subst]

/-- The composite peak map: run `g` (an origin→mid map), then `substByIso hiso2`
    (a mid→sub map).  A standalone `def` so the `.toPeak` projection of
    `PeakSubstIso.comp` reduces cleanly, mirroring `liftToPeak`. -/
def compToPeak {s1 s2 s3 : Sig} {σ2 : CapySubst s2 s3}
    (g : BVar s1 .cvar → Peak s2) (hiso2 : PeakSubstIso σ2) : BVar s1 .cvar → Peak s3 :=
  fun c => (g c).substByIso hiso2

/-- A peak correspondence is **cvar-only** when it never freezes any origin cvar: every
    origin cvar maps to a `cvar` peak.  The `openVar`/`openTVar` openings (identity on
    cvars) are `CvarOnly`. -/
def PeakSubstIso.CvarOnly {s1 s2 : Sig} {σ : CapySubst s1 s2} (hiso : PeakSubstIso σ) : Prop :=
  ∀ c : BVar s1 .cvar, ∃ d : BVar s2 .cvar, hiso.toPeak c = Peak.cvar d

/-- **Composition of peak correspondences** along `σ1.comp σ2`, provided the RIGHT factor
    `hiso2` is `CvarOnly`.

    The `CvarOnly` hypothesis is ESSENTIAL and cannot be dropped: without it composition
    can MERGE two distinct origin cvars.  Concretely, if `hiso1` sends `c1` to a `cvar d`
    that `hiso2` then FREEZES (`hiso2.toPeak d = pseudo E`) while `hiso1` already freezes a
    different `c2` to `pseudo D2` with `D2.subst σ2 = E`, then `(σ1.comp σ2).cvar c1 =
    (σ1.comp σ2).cvar c2 = pseudo_peak E` — a merge that the `image`+`inj` fields of ANY
    `PeakSubstIso` for the composite would contradict.  Requiring `hiso2` never to freeze
    (which every `openVar`/`openTVar` right-factor in this development satisfies) rules the
    scenario out: `substByIso` of a `cvar` then stays a `cvar`, so the mixed cases below are
    vacuous. -/
def PeakSubstIso.comp {s1 s2 s3 : Sig} {σ1 : CapySubst s1 s2} {σ2 : CapySubst s2 s3}
    (hiso1 : PeakSubstIso σ1) (hiso2 : PeakSubstIso σ2) (h2 : hiso2.CvarOnly) :
    PeakSubstIso (σ1.comp σ2) where
  toPeak := compToPeak hiso1.toPeak hiso2
  image := by
    intro c
    simp only [compToPeak, CapySubst.comp]
    rw [hiso1.image c]
    exact Peak.asCaptureSet_substByIso hiso2 (hiso1.toPeak c)
  inj := by
    intro c1 c2 h12
    simp only [compToPeak] at h12
    cases h1c : hiso1.toPeak c1 with
    | cvar c1' =>
      cases h2c : hiso1.toPeak c2 with
      | cvar c2' =>
        rw [h1c, h2c] at h12
        simp only [Peak.substByIso] at h12
        apply hiso1.inj
        rw [h1c, h2c]
        exact congrArg Peak.cvar (hiso2.inj h12)
      | pseudo D2 =>
        exfalso
        rw [h1c, h2c] at h12
        simp only [Peak.substByIso] at h12
        obtain ⟨d, hd⟩ := h2 c1'
        rw [hd] at h12
        exact absurd h12 (by simp)
    | pseudo D1 =>
      cases h2c : hiso1.toPeak c2 with
      | cvar c2' =>
        exfalso
        rw [h1c, h2c] at h12
        simp only [Peak.substByIso] at h12
        obtain ⟨d, hd⟩ := h2 c2'
        rw [hd] at h12
        exact absurd h12 (by simp)
      | pseudo D2 =>
        exact hiso1.uniqueFrozen h1c h2c
  uniqueFrozen := by
    intro c1 c2 E1 E2 hf1 hf2
    simp only [compToPeak] at hf1 hf2
    cases h1c : hiso1.toPeak c1 with
    | cvar c1' =>
      exfalso
      rw [h1c] at hf1
      simp only [Peak.substByIso] at hf1
      obtain ⟨d, hd⟩ := h2 c1'
      rw [hd] at hf1
      exact absurd hf1 (by simp)
    | pseudo D1 =>
      cases h2c : hiso1.toPeak c2 with
      | cvar c2' =>
        exfalso
        rw [h2c] at hf2
        simp only [Peak.substByIso] at hf2
        obtain ⟨d, hd⟩ := h2 c2'
        rw [hd] at hf2
        exact absurd hf2 (by simp)
      | pseudo D2 =>
        exact hiso1.uniqueFrozen h1c h2c

/-- **Stability-preservation of a peak correspondence.**  A cvar is ORIGIN-stable iff
    its image (via `hiso.toPeak`) is stable in `Γsub` — an *exact* correspondence, not
    just one direction, since both directions are needed: forward, to re-derive a stable
    SUB peak's separation from the origin lock; backward, to show a sub-peak traced BACK
    to an origin cvar (e.g. via `sub_cvar_peak_origin`) is itself origin-stable, so the
    origin-side stability-filtered `peakSepCtx` lemmas remain applicable.
    `CapyCtx.SubstsTo` alone (a `var`-lookup-only morphism) supplies none of this. -/
def PeakSubstIso.StablePreserving {s1 s2 : Sig} {σ : CapySubst s1 s2} (hiso : PeakSubstIso σ)
    (Γorig : CapyCtx s1) (Γsub : CapyCtx s2) : Prop :=
  ∀ c : BVar s1 .cvar, Γorig.IsStableCVar c ↔ Peak.IsStable Γsub (hiso.toPeak c)

/-- Substituting an `.unbound` bound leaves it `.unbound` at the *same* mode (mode-only,
    substitution-invariant) — the substitution-level analogue of
    `CapyCaptureBound.rename_eq_unbound_iff`. -/
theorem CapyCaptureBound.subst_eq_unbound_iff {s1 s2 : Sig} {X : CapyCaptureBound s1}
    {σ : CapySubst s1 s2} {m : Mutability} :
    X.subst σ = .unbound m ↔ X = .unbound m := by
  cases X with
  | unbound m' => simp only [CapyCaptureBound.subst, CapyCaptureBound.unbound.injEq]
  | bound cs =>
    constructor
    · intro h; simp only [CapyCaptureBound.subst] at h; cases h
    · intro h; cases h

/-- Stability-preservation lifts through a shared `consCVar`-style push — `Γorig` gains
    `.access_only cb`, `Γsub` gains `.access_only (cb.subst σ)` (exactly how every
    `compile_subst_subtyp` cvar-binder recursive call extends its two contexts; every
    `consCVar` in this codebase fixes authority `.access_only`, so `.here`'s stability
    reduces to "the bound is `.unbound`", which `subst` preserves at the *same* mode). -/
theorem PeakSubstIso.StablePreserving.pushCVar {s1 s2 : Sig} {σ : CapySubst s1 s2}
    {hiso : PeakSubstIso σ} {Γorig : CapyCtx s1} {Γsub : CapyCtx s2}
    (h : hiso.StablePreserving Γorig Γsub) (cb : CapyCaptureBound s1) :
    (hiso.lift Kind.cvar).StablePreserving
      (Γorig.push_cvar .access_only cb) (Γsub.push_cvar .access_only (cb.subst σ)) := by
  intro c
  cases c with
  | here =>
    simp only [PeakSubstIso.lift, liftToPeak, Peak.IsStable, CapyCtx.IsStableCVar,
      CapyCtx.lookup_authority, CapyCtx.lookup_cvar, CapyCtx.push_cvar,
      CapyCaptureBound.rename_eq_unbound_iff]
    exact or_congr Iff.rfl (exists_congr (fun m => CapyCaptureBound.subst_eq_unbound_iff.symm))
  | there c' =>
    simp only [PeakSubstIso.lift, liftToPeak, CapyCtx.push_cvar]
    rw [Peak.IsStable.renamesTo_iff (CapyCtx.RenamesTo.weaken (.cvar .access_only (cb.subst σ))),
      ← h c']
    simp only [CapyCtx.IsStableCVar, CapyCtx.lookup_authority, CapyCtx.lookup_cvar,
      CapyCaptureBound.rename_eq_unbound_iff]

/-- Stability-preservation lifts through a shared `consVar`-style push — the pushed
    *term*-variable's declared type is irrelevant to cvar stability (only the `.there`
    recursion into the tail matters), so `Γorig`/`Γsub` may gain unrelated types `T1`/`T2`. -/
theorem PeakSubstIso.StablePreserving.pushVar {s1 s2 : Sig} {σ : CapySubst s1 s2}
    {hiso : PeakSubstIso σ} {Γorig : CapyCtx s1} {Γsub : CapyCtx s2}
    (h : hiso.StablePreserving Γorig Γsub) (T1 : CapyTy .capt s1) (T2 : CapyTy .capt s2) :
    (hiso.lift Kind.var).StablePreserving (Γorig.push_var T1) (Γsub.push_var T2) := by
  intro c
  cases c with
  | there c' =>
    simp only [PeakSubstIso.lift, liftToPeak, CapyCtx.push_var]
    rw [Peak.IsStable.renamesTo_iff (CapyCtx.RenamesTo.weaken (.var T2)), ← h c']
    simp only [CapyCtx.IsStableCVar, CapyCtx.lookup_authority, CapyCtx.lookup_cvar,
      CapyCaptureBound.rename_eq_unbound_iff]

/-- Stability-preservation lifts through a shared `consTVar`-style push — the pushed
    *type*-variable's bound is irrelevant to cvar stability. -/
theorem PeakSubstIso.StablePreserving.pushTVar {s1 s2 : Sig} {σ : CapySubst s1 s2}
    {hiso : PeakSubstIso σ} {Γorig : CapyCtx s1} {Γsub : CapyCtx s2}
    (h : hiso.StablePreserving Γorig Γsub) (S1 : CapyPureTy s1) (S2 : CapyPureTy s2) :
    (hiso.lift Kind.tvar).StablePreserving (Γorig.push_tvar S1) (Γsub.push_tvar S2) := by
  intro c
  cases c with
  | there c' =>
    simp only [PeakSubstIso.lift, liftToPeak, CapyCtx.push_tvar]
    rw [Peak.IsStable.renamesTo_iff (CapyCtx.RenamesTo.weaken (.tvar S2)), ← h c']
    simp only [CapyCtx.IsStableCVar, CapyCtx.lookup_authority, CapyCtx.lookup_cvar,
      CapyCaptureBound.rename_eq_unbound_iff]

/-- Stability-preservation composes along `hiso1.comp hiso2 h2cvar`: an origin cvar is
    `Γ1`-stable iff its composite image is `Γ3`-stable.  Independent of `inj`/`uniqueFrozen`
    — only the `toPeak` equation is used — so the `CvarOnly` witness `h2cvar` enters solely
    to name the composite iso.  Chases through `h1` (origin→mid) then a peak-wise bridge:
    a `cvar` peak uses `h2` (mid→sub); a frozen peak is stable on both sides (`True`). -/
theorem PeakSubstIso.StablePreserving.comp {s1 s2 s3 : Sig} {σ1 : CapySubst s1 s2}
    {σ2 : CapySubst s2 s3} {hiso1 : PeakSubstIso σ1} {hiso2 : PeakSubstIso σ2}
    {h2cvar : hiso2.CvarOnly}
    {Γ1 : CapyCtx s1} {Γmid : CapyCtx s2} {Γ3 : CapyCtx s3}
    (h1 : hiso1.StablePreserving Γ1 Γmid) (h2 : hiso2.StablePreserving Γmid Γ3) :
    (hiso1.comp hiso2 h2cvar).StablePreserving Γ1 Γ3 := by
  have key : ∀ p : Peak s2,
      Peak.IsStable Γmid p ↔ Peak.IsStable Γ3 (p.substByIso hiso2) := by
    intro p
    cases p with
    | cvar c' => simp only [Peak.IsStable, Peak.substByIso]; exact h2 c'
    | pseudo D => simp only [Peak.IsStable, Peak.substByIso]
  intro c
  simp only [PeakSubstIso.comp, compToPeak]
  rw [h1 c]
  exact key (hiso1.toPeak c)

/-- `openCVar` is non-merging: the opened cvar becomes the frozen `pseudo_peak C`,
    every other cvar maps to itself. -/
def PeakSubstIso.openCVar {s : Sig} (C : CapyCaptureSet s) :
    PeakSubstIso (CapySubst.openCVar C) where
  toPeak := openCVarToPeak C
  image := by intro c; cases c with | here => rfl | there x => rfl
  inj := by
    intro c1 c2 h12
    cases c1 with
    | here =>
      cases c2 with
      | here => rfl
      | there x2 => exact absurd h12 (by simp [openCVarToPeak])
    | there x1 =>
      cases c2 with
      | here => exact absurd h12 (by simp [openCVarToPeak])
      | there x2 =>
        simp only [openCVarToPeak, Peak.cvar.injEq] at h12
        exact congrArg BVar.there h12
  uniqueFrozen := by
    intro c1 c2 D1 D2 h1 h2
    cases c1 with
    | here =>
      cases c2 with
      | here => rfl
      | there x2 => simp only [openCVarToPeak] at h2; exact absurd h2 (by simp)
    | there x1 => simp only [openCVarToPeak] at h1; exact absurd h1 (by simp)

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

/-- **Per-atom cvar→FROZEN containment.**  When `σ` FREEZES the origin cvar peak `d`
    (`σ.cvar d = pseudo_peak D`), each occurrence lands, after `σt`, inside the sub
    *frozen* item keyed by `(peaks Γsub D).modeErase`.  The membership premise `hmem`
    (the `D`-frozen peak is among the sub peaks) is the structural fact discharged at
    the use site; no non-collision needed (frozen items match by their mode-erased
    base, and `modeErase` absorbs the folded access). -/
theorem peakItem_subst_atom_pseudo {s1 s2 s1' s2' : Sig}
    {Γsub : CapyCtx s1'} {scOrig : SrcCtx s1 s2} {scSub : SrcCtx s1' s2'}
    {σ : CapySubst s1 s1'} {σt : Subst s2 s2'} {cs : CapyCaptureSet s1}
    (hΓS : Γsub.IsClosed) (haS : SrcAligned Γsub scSub)
    (hcompat : SubstCompat scSub scOrig σ σt)
    {a : Access} {d : BVar s1 .cvar} {D : CapyCaptureSet s1'} (hDcl : D.IsClosed)
    (hdD : σ.cvar d = CapyCaptureSet.pseudo_peak D)
    (hmem : (CapyCaptureSet.pseudo_peak ((CapyCaptureSet.peaks Γsub D).applyAccess a))
       ⊆ CapyCaptureSet.peaks Γsub (cs.subst σ)) :
    ((CaptureSet.cvar a (scOrig.lookupCVar d)).subst σt) ⊆
      CapyCaptureSet.compile (pseudoItem (CapyCaptureSet.peakset Γsub (cs.subst σ))
        ((CapyCaptureSet.peaks Γsub D).modeErase)) scSub := by
  have hZD : σt.cvar (scOrig.lookupCVar d) = CapyCaptureSet.compile D scSub := by
    rw [← hcompat.cvar d, hdD]; rfl
  have hatomeq : (CaptureSet.cvar a (scOrig.lookupCVar d)).subst σt
      = (CapyCaptureSet.compile D scSub).applyAccess a := by
    simp only [CaptureSet.subst, hZD]
  rw [hatomeq]
  have hsub1 : (CapyCaptureSet.pseudo_peak ((CapyCaptureSet.peaks Γsub D).applyAccess a))
      ⊆ pseudoItem (CapyCaptureSet.peakset Γsub (cs.subst σ))
          ((CapyCaptureSet.peaks Γsub D).modeErase) := by
    have h0 := pseudo_subset_pseudoItem (P := CapyCaptureSet.peakset Γsub (cs.subst σ))
      (C := (CapyCaptureSet.peaks Γsub D).applyAccess a) hmem
    rwa [CapyCaptureSet.modeErase_applyAccess] at h0
  have h2 := CapyCaptureSet.compile_subset (sc := scSub) hsub1
  have heq : CapyCaptureSet.compile
        (CapyCaptureSet.pseudo_peak ((CapyCaptureSet.peaks Γsub D).applyAccess a)) scSub
      = (CapyCaptureSet.compile D scSub).applyAccess a := by
    simp only [CapyCaptureSet.compile, CapyCaptureSet.compile_applyAccess,
      CapyCaptureSet.compile_peaks hΓS haS hDcl]
  rw [← heq]; exact h2

/-- **The full cvar→FROZEN containment** (union over the occurrences). -/
theorem peakItem_subst_subset_pseudo {s1 s2 s1' s2' : Sig}
    {Γorig : CapyCtx s1} {Γsub : CapyCtx s1'} {scOrig : SrcCtx s1 s2} {scSub : SrcCtx s1' s2'}
    {σ : CapySubst s1 s1'} {σt : Subst s2 s2'} {cs : CapyCaptureSet s1}
    (hΓS : Γsub.IsClosed) (haS : SrcAligned Γsub scSub)
    (hcompat : SubstCompat scSub scOrig σ σt)
    {d : BVar s1 .cvar} {D : CapyCaptureSet s1'} (hDcl : D.IsClosed)
    (hdD : σ.cvar d = CapyCaptureSet.pseudo_peak D)
    (hmem : ∀ a, (CapyCaptureSet.cvar a d) ⊆ CapyCaptureSet.peaks Γorig cs →
       (CapyCaptureSet.pseudo_peak ((CapyCaptureSet.peaks Γsub D).applyAccess a))
       ⊆ CapyCaptureSet.peaks Γsub (cs.subst σ)) :
    (CapyCaptureSet.compile (peakItem (CapyCaptureSet.peakset Γorig cs) d) scOrig).subst σt ⊆
      CapyCaptureSet.compile (pseudoItem (CapyCaptureSet.peakset Γsub (cs.subst σ))
        ((CapyCaptureSet.peaks Γsub D).modeErase)) scSub := by
  have key : ∀ (L : List Access),
      (∀ b ∈ L, (CapyCaptureSet.cvar b d) ⊆ CapyCaptureSet.peaks Γorig cs) →
      (CapyCaptureSet.compile
          (L.foldr (fun b acc => CapyCaptureSet.cvar b d ∪ acc) .empty) scOrig).subst σt ⊆
        CapyCaptureSet.compile (pseudoItem (CapyCaptureSet.peakset Γsub (cs.subst σ))
          ((CapyCaptureSet.peaks Γsub D).modeErase)) scSub := by
    intro L
    induction L with
    | nil =>
      intro _
      simp only [List.foldr_nil, CapyCaptureSet.compile, CaptureSet.subst]
      exact CaptureSet.Subset.empty
    | cons b L' ih =>
      intro hL
      rw [List.foldr_cons]
      simp only [CapyCaptureSet.compile]
      exact CaptureSet.Subset.union_left
        (peakItem_subst_atom_pseudo hΓS haS hcompat hDcl hdD
          (hmem b (hL b List.mem_cons_self)))
        (ih (fun b' hb' => hL b' (List.mem_cons_of_mem _ hb')))
  exact key (accessedAt (CapyCaptureSet.peakset Γorig cs) d)
    (fun b hb => accessedAt_go_subset _ (by simpa only [accessedAt] using hb))

/-- The actual sub-peak an origin cvar peak `d` maps to under a non-merging `σ`: its
    identity-image cvar, or the resolved + mode-erased frozen base. -/
def subPeakOf {s1 s1' : Sig} {σ : CapySubst s1 s1'} (hiso : PeakSubstIso σ)
    (Γsub : CapyCtx s1') (d : BVar s1 .cvar) : Peak s1' :=
  match hiso.toPeak d with
  | .cvar e => Peak.cvar e
  | .pseudo D => Peak.pseudo ((CapyCaptureSet.peaks Γsub D).modeErase)

/-- Distinct origin peaks map to distinct sub-peaks (`inj` for cvar images,
    `uniqueFrozen` for frozen images, kind-clash for mixed). -/
theorem subPeakOf_inj {s1 s1' : Sig} {σ : CapySubst s1 s1'} (hiso : PeakSubstIso σ)
    {Γsub : CapyCtx s1'} {d1 d2 : BVar s1 .cvar}
    (he : subPeakOf hiso Γsub d1 = subPeakOf hiso Γsub d2) : d1 = d2 := by
  cases h1 : hiso.toPeak d1 with
  | cvar e1 =>
    cases h2 : hiso.toPeak d2 with
    | cvar e2 =>
      simp only [subPeakOf, h1, h2, Peak.cvar.injEq] at he
      exact hiso.inj (by rw [h1, h2, he])
    | pseudo D2 => simp only [subPeakOf, h1, h2] at he; exact absurd he (by simp)
  | pseudo D1 =>
    cases h2 : hiso.toPeak d2 with
    | cvar e2 => simp only [subPeakOf, h1, h2] at he; exact absurd he (by simp)
    | pseudo D2 => exact hiso.uniqueFrozen h1 h2

/-! ### Source-level context-substitution morphism (`CapyCtx.SubstsTo`)

The substitution analogue of `CapyCtx.RenamesTo`: `Γ2` is the `σ`-substitution of `Γ1`.
Its sole operational consequence we need is that source peak-resolution sends a frozen
origin source to its resolved frozen image in the substituted peaks (`peaks_subst_frozen`),
which discharges `frozen_sub_peak_present` outright. -/

end Compilation
namespace CoreCapybara

/-- Drop the head binder slot of a lifted-capable substitution.  `σ.tail.cvar c = σ.cvar
    (.there c)` etc. — the restriction of `σ` to the tail of an extended source signature. -/
def CapySubst.tail {s1 s2 : Sig} {k : Kind} (σ : CapySubst (s1,,k) s2) : CapySubst s1 s2 where
  var := fun x => σ.var (.there x)
  tvar := fun X => σ.tvar (.there X)
  cvar := fun c => σ.cvar (.there c)

/-- Renaming by `succ` then substituting by `σ` equals substituting by the tail of `σ`. -/
theorem CapyCaptureSet.rename_succ_subst {s1 s2 : Sig} {k : Kind}
    {W : CapyCaptureSet s1} {σ : CapySubst (s1,,k) s2} :
    (W.rename Rename.succ).subst σ = W.subst σ.tail := by
  induction W with
  | empty => rfl
  | union W1 W2 ih1 ih2 => simp only [CapyCaptureSet.rename, CapyCaptureSet.subst, ih1, ih2]
  | pseudo_peak W0 ih => simp only [CapyCaptureSet.rename, CapyCaptureSet.subst, ih]
  | var m x => cases x <;> rfl
  | cvar m c => rfl

/-- `captureSet` commutes with substitution when the substitution keeps type variables
    as type variables (`SubstTvarCompat`): both sides are then `.empty` at the `tvar`
    leaf, and a direct projection elsewhere. -/
theorem CapyTy.captureSet_subst {s1 s2 : Sig} {T : CapyTy .capt s1} {σ : CapySubst s1 s2}
    (htv : ∀ X, ∃ Y, σ.tvar X = CapyPureTy.tvar Y) :
    (T.subst σ).captureSet = T.captureSet.subst σ := by
  cases T with
  | tvar X =>
    obtain ⟨Y, hY⟩ := htv X
    simp only [CapyTy.subst, hY, CapyPureTy.tvar, CapyTy.captureSet, CapyCaptureSet.subst]
  | top => rfl
  | unit => rfl
  | bool => rfl
  | arrow T1 cs T2 => rfl
  | poly T1 cs T2 => rfl
  | cpoly cb cs T => rfl
  | cap cs => rfl
  | cell cs m => rfl

/-- `refineCaptureSet` commutes with substitution when `σ` keeps type variables as type
    variables (so the `tvar` head — which substitution may turn into a compound — still has
    `refineCaptureSet` as the identity on both sides). -/
theorem CapyTy.refineCaptureSet_subst {s1 s2 : Sig} {T : CapyTy .capt s1}
    {cs : CapyCaptureSet s1} {σ : CapySubst s1 s2}
    (htv : ∀ X, ∃ Y, σ.tvar X = CapyPureTy.tvar Y) :
    (T.refineCaptureSet cs).subst σ = (T.subst σ).refineCaptureSet (cs.subst σ) := by
  cases T with
  | tvar X =>
    obtain ⟨Y, hY⟩ := htv X
    simp only [CapyTy.refineCaptureSet, CapyTy.subst, hY, CapyPureTy.tvar, CapyTy.refineCaptureSet]
  | top | unit | bool => rfl
  | cap cs0 | cell cs0 m => rfl
  | arrow T1 cs0 T2 | poly T1 cs0 T2 | cpoly T1 cs0 T2 => rfl

/-- **`Γ2` is the `σ`-substitution of the source typing context `Γ1`.**  A morphism
    `Γ1 ⟶ Γ2`: every term-variable lookup transports to a *bound* lookup whose bound's
    capture set is the `σ`-substitution of the original's (`σ` keeps term variables
    bound — true for capture-openings).  Only this `var` clause is needed: peak-resolution
    only consults the *capture sets* of term-var bounds. -/
structure CapyCtx.SubstsTo {s1 s2 : Sig}
    (Γ1 : CapyCtx s1) (Γ2 : CapyCtx s2) (σ : CapySubst s1 s2) : Prop where
  var : ∀ {x : BVar s1 .var} {T : CapyTy .capt s1},
    Γ1.LookupVar x T → ∃ (x' : BVar s2 .var) (T' : CapyTy .capt s2),
      σ.var x = .bound x' ∧ Γ2.LookupVar x' T' ∧ T'.captureSet = T.captureSet.subst σ

/-- A morphism out of an extended source context restricts to one out of the tail,
    `σ`-tail-precomposed.  (Mirror of `CapyCtx.RenamesTo.unpush`.) -/
theorem CapyCtx.SubstsTo.unpush {s1 s2 : Sig} {k : Kind} {Γ1 : CapyCtx s1}
    {b : CapyBinding s1 k} {Γ2 : CapyCtx s2} {σ : CapySubst (s1,,k) s2}
    (h : (Γ1.push b).SubstsTo Γ2 σ) : Γ1.SubstsTo Γ2 σ.tail where
  var {x} {T} hl := by
    obtain ⟨x', T', hx', hlk, hcs⟩ := h.var (CapyCtx.LookupVar.there (b := b) hl)
    refine ⟨x', T', hx', hlk, ?_⟩
    rw [hcs, CapyTy.captureSet_rename, CapyCaptureSet.rename_succ_subst]

/-- Composition of substitution morphisms: `Γ1 ⟶ Γmid ⟶ Γ2` gives `Γ1 ⟶ Γ2` along the
    composite `σ1.comp σ2`.  Chases the two `var` witnesses and fuses the capture
    equations via `CapyCaptureSet.subst_comp`. -/
theorem CapyCtx.SubstsTo.comp {s1 s2 s3 : Sig} {Γ1 : CapyCtx s1} {Γmid : CapyCtx s2}
    {Γ2 : CapyCtx s3} {σ1 : CapySubst s1 s2} {σ2 : CapySubst s2 s3}
    (h1 : Γ1.SubstsTo Γmid σ1) (h2 : Γmid.SubstsTo Γ2 σ2) :
    Γ1.SubstsTo Γ2 (σ1.comp σ2) where
  var {x} {T} hl := by
    obtain ⟨x', T', hx', hlk', hcs'⟩ := h1.var hl
    obtain ⟨x'', T'', hx'', hlk'', hcs''⟩ := h2.var hlk'
    refine ⟨x'', T'', ?_, hlk'', ?_⟩
    · simp only [CapySubst.comp, hx', CapyVar.subst]; exact hx''
    · rw [hcs'', hcs', CapyCaptureSet.subst_comp]

/-- Opening a value-variable binder is a substitution morphism onto the base, provided
    the substituted variable `y` is looked up there at the SAME type `T` the binder
    stored.  The redirected-parameter case: the pushed param at the argument's actual
    type `T0y` maps to `y : T0y`, and `T0y`'s capture is `openVar`-invariant
    (`weaken_openVar`) — exactly the EXACT `SubstsTo.var` the `.2` device demands. -/
theorem CapyCtx.SubstsTo.openVar {Γ : CapyCtx s} {y : BVar s .var} {T : CapyTy .capt s}
    (hlk : Γ.LookupVar y T) :
    (Γ.push (.var T)).SubstsTo Γ (CapySubst.openVar (.bound y)) where
  var {x} {T'} hl := by
    cases hl with
    | here =>
      exact ⟨y, T, rfl, hlk, by
        rw [CapyTy.captureSet_rename, CapyCaptureSet.weaken_openVar]⟩
    | there hl0 =>
      exact ⟨_, _, rfl, hl0, by
        rw [CapyTy.captureSet_rename, CapyCaptureSet.weaken_openVar]⟩

/-- A substitution morphism extends through a `cvar` binder, lifting `σ`.
    (Mirror of `CapyCtx.RenamesTo.push` for the `cvar` case.) -/
theorem CapyCtx.SubstsTo.consCVar {s1 s2 : Sig} {Γ1 : CapyCtx s1} {Γ2 : CapyCtx s2}
    {σ : CapySubst s1 s2} (h : Γ1.SubstsTo Γ2 σ)
    {a : CapyAuthority} {cb : CapyCaptureBound s1} :
    (Γ1.push_cvar a cb).SubstsTo (Γ2.push_cvar a (cb.subst σ)) (σ.lift (k := Kind.cvar)) where
  var {x} {T} hl := by
    cases hl with
    | there hl0 =>
      rename_i x0 T0
      obtain ⟨x', T', hx', hlk, hcs⟩ := h.var hl0
      refine ⟨BVar.there x', T'.rename Rename.succ, ?_, ?_, ?_⟩
      · rw [CapySubst.lift_there_var_eq, hx']; rfl
      · exact CapyCtx.LookupVar.there hlk
      · calc (T'.rename Rename.succ).captureSet
            = T'.captureSet.rename Rename.succ := CapyTy.captureSet_rename
          _ = (T0.captureSet.subst σ).rename Rename.succ := by rw [hcs]
          _ = (T0.captureSet.rename Rename.succ).subst σ.lift :=
              CapyCaptureSet.weaken_subst_comm_base
          _ = (T0.rename Rename.succ).captureSet.subst σ.lift := by
              rw [CapyTy.captureSet_rename]

/-- A substitution morphism extends through a `tvar` binder, lifting `σ`.
    (Mirror of `consCVar` for the `tvar` case — a tvar binder adds no term variable, so
    only the `there` lookups transport.) -/
theorem CapyCtx.SubstsTo.consTVar {s1 s2 : Sig} {Γ1 : CapyCtx s1} {Γ2 : CapyCtx s2}
    {σ : CapySubst s1 s2} (h : Γ1.SubstsTo Γ2 σ) {S1 : CapyPureTy s1} {S2 : CapyPureTy s2} :
    (Γ1.push_tvar S1).SubstsTo (Γ2.push_tvar S2) (σ.lift (k := Kind.tvar)) where
  var {x} {T} hl := by
    cases hl with
    | there hl0 =>
      rename_i x0 T0
      obtain ⟨x', T', hx', hlk, hcs⟩ := h.var hl0
      refine ⟨BVar.there x', T'.rename Rename.succ, ?_, ?_, ?_⟩
      · rw [CapySubst.lift_there_var_eq, hx']; rfl
      · exact CapyCtx.LookupVar.there hlk
      · calc (T'.rename Rename.succ).captureSet
            = T'.captureSet.rename Rename.succ := CapyTy.captureSet_rename
          _ = (T0.captureSet.subst σ).rename Rename.succ := by rw [hcs]
          _ = (T0.captureSet.rename Rename.succ).subst σ.lift :=
              CapyCaptureSet.weaken_subst_comm_base
          _ = (T0.rename Rename.succ).captureSet.subst σ.lift := by
              rw [CapyTy.captureSet_rename]

/-- A substitution morphism extends through a *term*-variable binder, lifting `σ`.  The freshly
    bound `x : T` maps to `x : T[σ]`; deeper lookups transport via `h`. -/
theorem CapyCtx.SubstsTo.consVar {s1 s2 : Sig} {Γ1 : CapyCtx s1} {Γ2 : CapyCtx s2}
    {σ : CapySubst s1 s2} (h : Γ1.SubstsTo Γ2 σ) {T : CapyTy .capt s1}
    (htv : ∀ X, ∃ Y, σ.tvar X = CapyPureTy.tvar Y) :
    (Γ1.push_var T).SubstsTo (Γ2.push_var (T.subst σ)) (σ.lift (k := Kind.var)) where
  var {x} {U} hl := by
    cases hl with
    | here =>
      refine ⟨BVar.here, (T.subst σ).rename Rename.succ, rfl, CapyCtx.LookupVar.here, ?_⟩
      calc ((T.subst σ).rename Rename.succ).captureSet
          = (T.subst σ).captureSet.rename Rename.succ := CapyTy.captureSet_rename
        _ = (T.captureSet.subst σ).rename Rename.succ := by rw [CapyTy.captureSet_subst htv]
        _ = (T.captureSet.rename Rename.succ).subst σ.lift :=
            CapyCaptureSet.weaken_subst_comm_base
        _ = (T.rename Rename.succ).captureSet.subst σ.lift := by rw [CapyTy.captureSet_rename]
    | there hl0 =>
      rename_i x0 T0
      obtain ⟨x', T', hx', hlk, hcs⟩ := h.var hl0
      refine ⟨BVar.there x', T'.rename Rename.succ, ?_, ?_, ?_⟩
      · rw [CapySubst.lift_there_var_eq, hx']; rfl
      · exact CapyCtx.LookupVar.there hlk
      · calc (T'.rename Rename.succ).captureSet
            = T'.captureSet.rename Rename.succ := CapyTy.captureSet_rename
          _ = (T0.captureSet.subst σ).rename Rename.succ := by rw [hcs]
          _ = (T0.captureSet.rename Rename.succ).subst σ.lift :=
              CapyCaptureSet.weaken_subst_comm_base
          _ = (T0.rename Rename.succ).captureSet.subst σ.lift := by
              rw [CapyTy.captureSet_rename]

/-- `applyAccess` distributes over the frozen wrapper. -/
theorem CapyCaptureSet.applyAccess_pseudo_peak {s : Sig} {C : CapyCaptureSet s} {m : Access} :
    (CapyCaptureSet.pseudo_peak C).applyAccess m
      = CapyCaptureSet.pseudo_peak (C.applyAccess m) := by
  cases m with
  | M mm => cases mm <;> rfl
  | drop => rfl

/-- A target cvar atom of a `succ`-renamed source capture set comes from a `there`-cvar
    of the original. -/
theorem CapyCaptureSet.cvar_subset_rename_succ {s : Sig} {k : Kind} {a : Access}
    {c : BVar (s,,k) .cvar} {C : CapyCaptureSet s}
    (h : (CapyCaptureSet.cvar a c) ⊆ C.rename Rename.succ) :
    ∃ c', c = BVar.there c' ∧ (CapyCaptureSet.cvar a c') ⊆ C := by
  induction C with
  | empty => simp only [CapyCaptureSet.rename] at h; cases h
  | union C1 C2 ih1 ih2 =>
    simp only [CapyCaptureSet.rename] at h
    cases h with
    | union_right_left h1 =>
      obtain ⟨c', hc', hsub⟩ := ih1 h1
      exact ⟨c', hc', CapyCaptureSet.Subset.union_right_left hsub⟩
    | union_right_right h2 =>
      obtain ⟨c', hc', hsub⟩ := ih2 h2
      exact ⟨c', hc', CapyCaptureSet.Subset.union_right_right hsub⟩
  | cvar a0 c0 =>
    simp only [CapyCaptureSet.rename] at h
    cases h
    exact ⟨c0, by simp only [Rename.succ], CapyCaptureSet.Subset.refl⟩
  | var a0 x0 => simp only [CapyCaptureSet.rename] at h; cases h
  | pseudo_peak C0 _ => simp only [CapyCaptureSet.rename] at h; cases h

/-- **Source-level frozen-peak presence (the discharge of `frozen_sub_peak_present`).**
    Given a substitution morphism `Γ1 ⟶ Γ2` (`SubstsTo`, with the `tvar` images staying
    type variables), a frozen origin source `d` (`σ.cvar d = pseudo_peak D`) occurring at
    access `a` in `peaks Γ1 W` has its `Γ2`-resolved, access-folded frozen image present
    in `peaks Γ2 (W[σ])`.  By well-founded recursion peeling `Γ1` (mirror of
    `peaks_renamesTo`); the var-resolution case absorbs the bound's `applyAccess`/`rename`
    into the recursion argument so the access `a` is preserved verbatim. -/
theorem CapyCaptureSet.peaks_subst_frozen {s1 s2 : Sig}
    {Γ1 : CapyCtx s1} {Γ2 : CapyCtx s2} {σ : CapySubst s1 s2}
    (htv : ∀ X, ∃ Y, σ.tvar X = CapyPureTy.tvar Y) (h : Γ1.SubstsTo Γ2 σ)
    {d : BVar s1 .cvar} {D : CapyCaptureSet s2} (hdD : σ.cvar d = CapyCaptureSet.pseudo_peak D)
    (W : CapyCaptureSet s1) {a : Access}
    (hsub : (CapyCaptureSet.cvar a d) ⊆ CapyCaptureSet.peaks Γ1 W) :
    (CapyCaptureSet.pseudo_peak ((CapyCaptureSet.peaks Γ2 D).applyAccess a))
      ⊆ CapyCaptureSet.peaks Γ2 (W.subst σ) := by
  match Γ1, W, h, hsub with
  | _, .empty, _, hsub => simp only [CapyCaptureSet.peaks] at hsub; cases hsub
  | _, .pseudo_peak W0, _, hsub => simp only [CapyCaptureSet.peaks] at hsub; cases hsub
  | _, .var m (.free n), _, hsub => simp only [CapyCaptureSet.peaks] at hsub; cases hsub
  | _, .union W1 W2, h, hsub =>
    simp only [CapyCaptureSet.peaks] at hsub
    simp only [CapyCaptureSet.subst, CapyCaptureSet.peaks]
    cases hsub with
    | union_right_left h1 =>
      exact CapyCaptureSet.Subset.union_right_left
        (CapyCaptureSet.peaks_subst_frozen htv h hdD W1 h1)
    | union_right_right h2 =>
      exact CapyCaptureSet.Subset.union_right_right
        (CapyCaptureSet.peaks_subst_frozen htv h hdD W2 h2)
  | _, .cvar m c, _, hsub =>
    simp only [CapyCaptureSet.peaks] at hsub
    cases hsub
    simp only [CapyCaptureSet.subst, hdD, CapyCaptureSet.applyAccess_pseudo_peak,
      CapyCaptureSet.peaks, CapyCaptureSet.peaks_applyAccess_comm]
    exact CapyCaptureSet.Subset.refl
  | .push Γ1' (.var T0), .var m (.bound .here), h, hsub =>
    have hpeq : CapyCaptureSet.peaks (Γ1'.push (.var T0)) (.var m (.bound .here))
        = (CapyCaptureSet.peaks Γ1' (T0.captureSet.applyAccess m)).rename Rename.succ := by
      simp only [CapyCaptureSet.peaks, CapyCaptureSet.peaksVarBound]
      rw [← CapyCaptureSet.applyAccess_rename, ← CapyCaptureSet.peaks_applyAccess_comm]
    rw [hpeq] at hsub
    obtain ⟨d', hdeq, hsub'⟩ := CapyCaptureSet.cvar_subset_rename_succ hsub
    subst hdeq
    have hdD' : (σ.tail).cvar d' = CapyCaptureSet.pseudo_peak D := hdD
    have htv' : ∀ X, ∃ Y, (σ.tail).tvar X = CapyPureTy.tvar Y := fun X => htv (.there X)
    have hrec := CapyCaptureSet.peaks_subst_frozen htv' h.unpush hdD'
      (T0.captureSet.applyAccess m) hsub'
    obtain ⟨x', T', hx', hlk, hcseq⟩ := h.var (CapyCtx.LookupVar.here (Γ := Γ1') (T := T0))
    have hrhs : CapyCaptureSet.peaks Γ2 ((CapyCaptureSet.var m (.bound .here)).subst σ)
        = CapyCaptureSet.peaks Γ2 ((T0.captureSet.applyAccess m).subst σ.tail) := by
      simp only [CapyCaptureSet.subst, CapyVar.subst, hx']
      rw [CapyCaptureSet.var_peaks hlk, hcseq, CapyTy.captureSet_rename,
        CapyCaptureSet.rename_succ_subst, ← CapyCaptureSet.applyAccess_subst]
    rw [hrhs]; exact hrec
  | .push Γ1' b, .var m (.bound (.there x')), h, hsub =>
    have hpeq : CapyCaptureSet.peaks (Γ1'.push b) (.var m (.bound (.there x')))
        = (CapyCaptureSet.peaks Γ1' (.var m (.bound x'))).rename Rename.succ := by
      simp only [CapyCaptureSet.peaks, CapyCaptureSet.peaksVarBound]
    rw [hpeq] at hsub
    obtain ⟨d', hdeq, hsub'⟩ := CapyCaptureSet.cvar_subset_rename_succ hsub
    subst hdeq
    have hdD' : (σ.tail).cvar d' = CapyCaptureSet.pseudo_peak D := hdD
    have htv' : ∀ X, ∃ Y, (σ.tail).tvar X = CapyPureTy.tvar Y := fun X => htv (.there X)
    have hrec := CapyCaptureSet.peaks_subst_frozen htv' h.unpush hdD'
      (CapyCaptureSet.var m (.bound x')) hsub'
    have hrhs : CapyCaptureSet.peaks Γ2 ((CapyCaptureSet.var m (.bound (.there x'))).subst σ)
        = CapyCaptureSet.peaks Γ2 ((CapyCaptureSet.var m (.bound x')).subst σ.tail) := rfl
    rw [hrhs]; exact hrec
  termination_by (sizeOf Γ1, sizeOf W)

/-- **Forward identity-image membership** (mirror of `peaks_subst_frozen` for identity
    cvar images): an occurrence `{a d} ⊆ peaks Γ1 W` of an origin cvar peak whose
    `σ`-image is the identity cvar `e` (`σ.cvar d = {ε e}`) yields the same-mode
    occurrence `{a e} ⊆ peaks Γ2 (W[σ])`.  Replaces the compiled-keystone atom trace
    (whose spurious frozen branch demanded a blanket non-collision precondition —
    at the SOURCE level, frozen wrappers stay opaque, so no collision case arises
    at all). -/
theorem CapyCaptureSet.peaks_subst_cvar_fwd {s1 s2 : Sig}
    {Γ1 : CapyCtx s1} {Γ2 : CapyCtx s2} {σ : CapySubst s1 s2}
    (htv : ∀ X, ∃ Y, σ.tvar X = CapyPureTy.tvar Y) (h : Γ1.SubstsTo Γ2 σ)
    {d : BVar s1 .cvar} {e : BVar s2 .cvar}
    (hde : σ.cvar d = CapyCaptureSet.cvar (.M .epsilon) e)
    (W : CapyCaptureSet s1) {a : Access}
    (hsub : (CapyCaptureSet.cvar a d) ⊆ CapyCaptureSet.peaks Γ1 W) :
    (CapyCaptureSet.cvar a e) ⊆ CapyCaptureSet.peaks Γ2 (W.subst σ) := by
  match Γ1, W, h, hsub with
  | _, .empty, _, hsub => simp only [CapyCaptureSet.peaks] at hsub; cases hsub
  | _, .pseudo_peak W0, _, hsub => simp only [CapyCaptureSet.peaks] at hsub; cases hsub
  | _, .var m (.free n), _, hsub => simp only [CapyCaptureSet.peaks] at hsub; cases hsub
  | _, .union W1 W2, h, hsub =>
    simp only [CapyCaptureSet.peaks] at hsub
    simp only [CapyCaptureSet.subst, CapyCaptureSet.peaks]
    cases hsub with
    | union_right_left h1 =>
      exact CapyCaptureSet.Subset.union_right_left
        (CapyCaptureSet.peaks_subst_cvar_fwd htv h hde W1 h1)
    | union_right_right h2 =>
      exact CapyCaptureSet.Subset.union_right_right
        (CapyCaptureSet.peaks_subst_cvar_fwd htv h hde W2 h2)
  | _, .cvar m c, _, hsub =>
    simp only [CapyCaptureSet.peaks] at hsub
    cases hsub
    have himg : (CapyCaptureSet.cvar a d).subst σ = CapyCaptureSet.cvar a e := by
      simp only [CapyCaptureSet.subst, hde]
      cases a with
      | M mu => cases mu <;> rfl
      | drop => rfl
    rw [himg]
    simp only [CapyCaptureSet.peaks]
    exact CapyCaptureSet.Subset.refl
  | .push Γ1' (.var T0), .var m (.bound .here), h, hsub =>
    have hpeq : CapyCaptureSet.peaks (Γ1'.push (.var T0)) (.var m (.bound .here))
        = (CapyCaptureSet.peaks Γ1' (T0.captureSet.applyAccess m)).rename Rename.succ := by
      simp only [CapyCaptureSet.peaks, CapyCaptureSet.peaksVarBound]
      rw [← CapyCaptureSet.applyAccess_rename, ← CapyCaptureSet.peaks_applyAccess_comm]
    rw [hpeq] at hsub
    obtain ⟨d', hdeq, hsub'⟩ := CapyCaptureSet.cvar_subset_rename_succ hsub
    subst hdeq
    have hde' : (σ.tail).cvar d' = CapyCaptureSet.cvar (.M .epsilon) e := hde
    have htv' : ∀ X, ∃ Y, (σ.tail).tvar X = CapyPureTy.tvar Y := fun X => htv (.there X)
    have hrec := CapyCaptureSet.peaks_subst_cvar_fwd htv' h.unpush hde'
      (T0.captureSet.applyAccess m) hsub'
    obtain ⟨x', T', hx', hlk, hcseq⟩ := h.var (CapyCtx.LookupVar.here (Γ := Γ1') (T := T0))
    have hrhs : CapyCaptureSet.peaks Γ2 ((CapyCaptureSet.var m (.bound .here)).subst σ)
        = CapyCaptureSet.peaks Γ2 ((T0.captureSet.applyAccess m).subst σ.tail) := by
      simp only [CapyCaptureSet.subst, CapyVar.subst, hx']
      rw [CapyCaptureSet.var_peaks hlk, hcseq, CapyTy.captureSet_rename,
        CapyCaptureSet.rename_succ_subst, ← CapyCaptureSet.applyAccess_subst]
    rw [hrhs]; exact hrec
  | .push Γ1' b, .var m (.bound (.there x')), h, hsub =>
    have hpeq : CapyCaptureSet.peaks (Γ1'.push b) (.var m (.bound (.there x')))
        = (CapyCaptureSet.peaks Γ1' (.var m (.bound x'))).rename Rename.succ := by
      simp only [CapyCaptureSet.peaks, CapyCaptureSet.peaksVarBound]
    rw [hpeq] at hsub
    obtain ⟨d', hdeq, hsub'⟩ := CapyCaptureSet.cvar_subset_rename_succ hsub
    subst hdeq
    have hde' : (σ.tail).cvar d' = CapyCaptureSet.cvar (.M .epsilon) e := hde
    have htv' : ∀ X, ∃ Y, (σ.tail).tvar X = CapyPureTy.tvar Y := fun X => htv (.there X)
    have hrec := CapyCaptureSet.peaks_subst_cvar_fwd htv' h.unpush hde'
      (CapyCaptureSet.var m (.bound x')) hsub'
    have hrhs : CapyCaptureSet.peaks Γ2 ((CapyCaptureSet.var m (.bound (.there x'))).subst σ)
        = CapyCaptureSet.peaks Γ2 ((CapyCaptureSet.var m (.bound x')).subst σ.tail) := rfl
    rw [hrhs]; exact hrec
  termination_by (sizeOf Γ1, sizeOf W)

/-- Capture-set subset is preserved by renaming. -/
theorem CapyCaptureSet.Subset.rename {s1 s2 : Sig} {C1 C2 : CapyCaptureSet s1} {f : Rename s1 s2}
    (h : C1.Subset C2) : (C1.rename f).Subset (C2.rename f) := by
  induction h with
  | refl => exact CapyCaptureSet.Subset.refl
  | empty => exact CapyCaptureSet.Subset.empty
  | union_left _ _ ih1 ih2 => exact CapyCaptureSet.Subset.union_left ih1 ih2
  | union_right_left _ ih => exact CapyCaptureSet.Subset.union_right_left ih
  | union_right_right _ ih => exact CapyCaptureSet.Subset.union_right_right ih

/-- A cvar atom contained in a single cvar atom equals it (mode and resource). -/
theorem CapyCaptureSet.cvar_subset_cvar_inv {s : Sig} {a a' : Access} {c c' : BVar s .cvar}
    (h : (CapyCaptureSet.cvar a c) ⊆ (CapyCaptureSet.cvar a' c')) : a = a' ∧ c = c' := by
  cases h; exact ⟨rfl, rfl⟩

/-- A cvar atom contained in `{m0 c0}` access-folded has the same resource `c0`. -/
theorem CapyCaptureSet.cvar_subset_cvar_applyAccess {s : Sig} {a mm m0 : Access}
    {d1 c0 : BVar s .cvar}
    (h : (CapyCaptureSet.cvar a d1) ⊆ (CapyCaptureSet.cvar m0 c0).applyAccess mm) : d1 = c0 := by
  cases mm with
  | M mu =>
    cases mu with
    | epsilon =>
      simp only [CapyCaptureSet.applyAccess_M, CapyCaptureSet.applyMut] at h
      exact (CapyCaptureSet.cvar_subset_cvar_inv h).2
    | ro =>
      simp only [CapyCaptureSet.applyAccess_M, CapyCaptureSet.applyMut, CapyCaptureSet.applyRO] at h
      exact (CapyCaptureSet.cvar_subset_cvar_inv h).2
  | drop =>
    simp only [CapyCaptureSet.applyAccess_drop, CapyCaptureSet.applyDrop] at h
    exact (CapyCaptureSet.cvar_subset_cvar_inv h).2

/-- **Source-level cvar reverse-trace through `SubstsTo`.**  A cvar atom `{a d1}` of the
    substituted, peaks-resolved set traces back to an origin cvar `c01` (with an occurrence
    `{m c01} ⊆ peaks Γ1 W`) whose `σ`-image, access-folded, carries it.  The structural dual
    of `peaks_subst_frozen`: var-bound atoms recurse through the context morphism `h.var`.
    No peak-iso needed here — the image identification (`σ.cvar c01 = {ε d1}`) is read off at
    the use site. -/
theorem CapyCaptureSet.peaks_subst_cvar {s1 s2 : Sig}
    {Γ1 : CapyCtx s1} {Γ2 : CapyCtx s2} {σ : CapySubst s1 s2}
    (h : Γ1.SubstsTo Γ2 σ) (htv : ∀ X, ∃ Y, σ.tvar X = CapyPureTy.tvar Y)
    {d1 : BVar s2 .cvar} {a : Access}
    (W : CapyCaptureSet s1)
    (hsub : (CapyCaptureSet.cvar a d1) ⊆ CapyCaptureSet.peaks Γ2 (W.subst σ)) :
    ∃ (c01 : BVar s1 .cvar) (m : Access),
      (CapyCaptureSet.cvar m c01) ⊆ CapyCaptureSet.peaks Γ1 W ∧
      (CapyCaptureSet.cvar a d1)
        ⊆ CapyCaptureSet.peaks Γ2 ((σ.cvar c01).applyAccess m) := by
  match Γ1, W, h, hsub with
  | _, .empty, _, hsub =>
    simp only [CapyCaptureSet.subst, CapyCaptureSet.peaks] at hsub; cases hsub
  | _, .pseudo_peak W0, _, hsub =>
    simp only [CapyCaptureSet.subst, CapyCaptureSet.peaks] at hsub; cases hsub
  | _, .var m (.free n), _, hsub =>
    simp only [CapyCaptureSet.subst, CapyVar.subst, CapyCaptureSet.peaks] at hsub; cases hsub
  | _, .union W1 W2, h, hsub =>
    simp only [CapyCaptureSet.subst, CapyCaptureSet.peaks] at hsub
    cases hsub with
    | union_right_left h1 =>
      obtain ⟨c01, m, hocc, hatom⟩ := CapyCaptureSet.peaks_subst_cvar h htv W1 h1
      exact ⟨c01, m, by
        simp only [CapyCaptureSet.peaks]; exact CapyCaptureSet.Subset.union_right_left hocc, hatom⟩
    | union_right_right h2 =>
      obtain ⟨c01, m, hocc, hatom⟩ := CapyCaptureSet.peaks_subst_cvar h htv W2 h2
      exact ⟨c01, m, by
        simp only [CapyCaptureSet.peaks]
        exact CapyCaptureSet.Subset.union_right_right hocc, hatom⟩
  | _, .cvar m c, _, hsub =>
    refine ⟨c, m, by simp only [CapyCaptureSet.peaks]; exact CapyCaptureSet.Subset.refl, ?_⟩
    simpa only [CapyCaptureSet.subst] using hsub
  | .push Γ1' (.var T0), .var m (.bound .here), h, hsub =>
    have hrhs : CapyCaptureSet.peaks Γ2 ((CapyCaptureSet.var m (.bound .here)).subst σ)
        = CapyCaptureSet.peaks Γ2 ((T0.captureSet.applyAccess m).subst σ.tail) := by
      obtain ⟨x', T', hx', hlk, hcseq⟩ := h.var (CapyCtx.LookupVar.here (Γ := Γ1') (T := T0))
      simp only [CapyCaptureSet.subst, CapyVar.subst, hx']
      rw [CapyCaptureSet.var_peaks hlk, hcseq, CapyTy.captureSet_rename,
        CapyCaptureSet.rename_succ_subst, ← CapyCaptureSet.applyAccess_subst]
    rw [hrhs] at hsub
    have htv' : ∀ X, ∃ Y, (σ.tail).tvar X = CapyPureTy.tvar Y := fun X => htv (.there X)
    obtain ⟨c01', m', hocc', hatom'⟩ :=
      CapyCaptureSet.peaks_subst_cvar h.unpush htv' (T0.captureSet.applyAccess m) hsub
    have hpeq : CapyCaptureSet.peaks (Γ1'.push (.var T0)) (.var m (.bound .here))
        = (CapyCaptureSet.peaks Γ1' (T0.captureSet.applyAccess m)).rename Rename.succ := by
      simp only [CapyCaptureSet.peaks, CapyCaptureSet.peaksVarBound]
      rw [← CapyCaptureSet.applyAccess_rename, ← CapyCaptureSet.peaks_applyAccess_comm]
    refine ⟨BVar.there c01', m', ?_, hatom'⟩
    rw [hpeq]
    change (CapyCaptureSet.cvar m' c01').rename Rename.succ ⊆ _
    exact CapyCaptureSet.Subset.rename hocc'
  | .push Γ1' b, .var m (.bound (.there x')), h, hsub =>
    have hpeq2 : CapyCaptureSet.peaks Γ2 ((CapyCaptureSet.var m (.bound (.there x'))).subst σ)
        = CapyCaptureSet.peaks Γ2 ((CapyCaptureSet.var m (.bound x')).subst σ.tail) := rfl
    rw [hpeq2] at hsub
    have htv' : ∀ X, ∃ Y, (σ.tail).tvar X = CapyPureTy.tvar Y := fun X => htv (.there X)
    obtain ⟨c01', m', hocc', hatom'⟩ :=
      CapyCaptureSet.peaks_subst_cvar h.unpush htv' (CapyCaptureSet.var m (.bound x')) hsub
    have hpeq : CapyCaptureSet.peaks (Γ1'.push b) (.var m (.bound (.there x')))
        = (CapyCaptureSet.peaks Γ1' (.var m (.bound x'))).rename Rename.succ := by
      simp only [CapyCaptureSet.peaks, CapyCaptureSet.peaksVarBound]
    refine ⟨BVar.there c01', m', ?_, hatom'⟩
    rw [hpeq]
    change (CapyCaptureSet.cvar m' c01').rename Rename.succ ⊆ _
    exact CapyCaptureSet.Subset.rename hocc'
  termination_by (sizeOf Γ1, sizeOf W)

/-- **Source-level frozen-peak reverse-trace through `SubstsTo`.**  The pseudo-peak dual of
    `peaks_subst_cvar`: a *frozen* peak `pseudo_peak C'` of the substituted, peaks-resolved set
    `peaks Γ2 (W[σ])` traces back to an origin cvar `c01` (occurring in `peaks Γ1 W`) that `σ`
    froze — routed through the context morphism `h` and the *origin* pseudo-freeness `hΓ1`,
    NOT through any pseudo-freeness of the *sub* context `Γ2`.  This is the device that makes
    the sub-context `NoPseudoPeak` premise (`hsubPure`) unnecessary: frozen-peak attribution
    goes via the genuinely pseudo-free origin (`hΓ1`) + `h`, even when `σ` freezes captured
    cvars so that `Γ2`'s var bounds carry frozen peaks. -/
theorem CapyCaptureSet.peaks_subst_pseudo_cvar {s1 s2 : Sig}
    {Γ1 : CapyCtx s1} {Γ2 : CapyCtx s2} {σ : CapySubst s1 s2}
    (h : Γ1.SubstsTo Γ2 σ) (hΓ1 : Γ1.NoPseudoPeak) {C' : CapyCaptureSet s2}
    (W : CapyCaptureSet s1) (hW : W.NoPseudoPeak)
    (hsub : (CapyCaptureSet.pseudo_peak C') ⊆ CapyCaptureSet.peaks Γ2 (W.subst σ)) :
    ∃ (c01 : BVar s1 .cvar) (m : Access),
      (CapyCaptureSet.cvar m c01) ⊆ CapyCaptureSet.peaks Γ1 W ∧
      (CapyCaptureSet.pseudo_peak C')
        ⊆ CapyCaptureSet.peaks Γ2 ((σ.cvar c01).applyAccess m) := by
  match Γ1, W, h, hΓ1, hW, hsub with
  | _, .empty, _, _, _, hsub =>
    simp only [CapyCaptureSet.subst, CapyCaptureSet.peaks] at hsub; cases hsub
  | _, .pseudo_peak W0, _, _, hW, _ => nomatch hW
  | _, .var m (.free n), _, _, _, hsub =>
    simp only [CapyCaptureSet.subst, CapyVar.subst, CapyCaptureSet.peaks] at hsub; cases hsub
  | _, .union W1 W2, h, hΓ1, hW, hsub =>
    simp only [CapyCaptureSet.subst, CapyCaptureSet.peaks] at hsub
    cases hW with
    | union hW1 hW2 =>
      cases hsub with
      | union_right_left h1 =>
        obtain ⟨c01, m, hocc, hatom⟩ :=
          CapyCaptureSet.peaks_subst_pseudo_cvar h hΓ1 W1 hW1 h1
        exact ⟨c01, m, by
          simp only [CapyCaptureSet.peaks]
          exact CapyCaptureSet.Subset.union_right_left hocc, hatom⟩
      | union_right_right h2 =>
        obtain ⟨c01, m, hocc, hatom⟩ :=
          CapyCaptureSet.peaks_subst_pseudo_cvar h hΓ1 W2 hW2 h2
        exact ⟨c01, m, by
          simp only [CapyCaptureSet.peaks]
          exact CapyCaptureSet.Subset.union_right_right hocc, hatom⟩
  | _, .cvar m c, _, _, _, hsub =>
    refine ⟨c, m, by simp only [CapyCaptureSet.peaks]; exact CapyCaptureSet.Subset.refl, ?_⟩
    simpa only [CapyCaptureSet.subst] using hsub
  | .push Γ1' (.var T0), .var m (.bound .here), h, hΓ1, _, hsub =>
    have hrhs : CapyCaptureSet.peaks Γ2 ((CapyCaptureSet.var m (.bound .here)).subst σ)
        = CapyCaptureSet.peaks Γ2 ((T0.captureSet.applyAccess m).subst σ.tail) := by
      obtain ⟨x', T', hx', hlk, hcseq⟩ := h.var (CapyCtx.LookupVar.here (Γ := Γ1') (T := T0))
      simp only [CapyCaptureSet.subst, CapyVar.subst, hx']
      rw [CapyCaptureSet.var_peaks hlk, hcseq, CapyTy.captureSet_rename,
        CapyCaptureSet.rename_succ_subst, ← CapyCaptureSet.applyAccess_subst]
    rw [hrhs] at hsub
    obtain ⟨c01', m', hocc', hatom'⟩ :=
      CapyCaptureSet.peaks_subst_pseudo_cvar h.unpush hΓ1.1
        (T0.captureSet.applyAccess m) hΓ1.2.applyAccess hsub
    have hpeq : CapyCaptureSet.peaks (Γ1'.push (.var T0)) (.var m (.bound .here))
        = (CapyCaptureSet.peaks Γ1' (T0.captureSet.applyAccess m)).rename Rename.succ := by
      simp only [CapyCaptureSet.peaks, CapyCaptureSet.peaksVarBound]
      rw [← CapyCaptureSet.applyAccess_rename, ← CapyCaptureSet.peaks_applyAccess_comm]
    refine ⟨BVar.there c01', m', ?_, hatom'⟩
    rw [hpeq]
    change (CapyCaptureSet.cvar m' c01').rename Rename.succ ⊆ _
    exact CapyCaptureSet.Subset.rename hocc'
  | .push Γ1' b, .var m (.bound (.there x')), h, hΓ1, _, hsub =>
    have hpeq2 : CapyCaptureSet.peaks Γ2 ((CapyCaptureSet.var m (.bound (.there x'))).subst σ)
        = CapyCaptureSet.peaks Γ2 ((CapyCaptureSet.var m (.bound x')).subst σ.tail) := rfl
    rw [hpeq2] at hsub
    obtain ⟨c01', m', hocc', hatom'⟩ :=
      CapyCaptureSet.peaks_subst_pseudo_cvar h.unpush hΓ1.tail
        (CapyCaptureSet.var m (.bound x')) CapyCaptureSet.NoPseudoPeak.var hsub
    have hpeq : CapyCaptureSet.peaks (Γ1'.push b) (.var m (.bound (.there x')))
        = (CapyCaptureSet.peaks Γ1' (.var m (.bound x'))).rename Rename.succ := by
      simp only [CapyCaptureSet.peaks, CapyCaptureSet.peaksVarBound]
    refine ⟨BVar.there c01', m', ?_, hatom'⟩
    rw [hpeq]
    change (CapyCaptureSet.cvar m' c01').rename Rename.succ ⊆ _
    exact CapyCaptureSet.Subset.rename hocc'
  termination_by (sizeOf Γ1, sizeOf W)

/-- `peaks` of a cvar atom (access-folded) carries no frozen peak — independent of the
    context, since `peaks` never resolves a cvar atom through `Γ`.  The `hsubPure`-free
    discharge of the identity-image contradiction in the frozen reverse-trace lemmas. -/
theorem CapyCaptureSet.peaks_cvar_applyAccess_noPseudoPeak {s : Sig} {Γ : CapyCtx s}
    {a m : Access} {c : BVar s .cvar} :
    (CapyCaptureSet.peaks Γ ((CapyCaptureSet.cvar a c).applyAccess m)).NoPseudoPeak := by
  rw [CapyCaptureSet.peaks_applyAccess_comm]
  simp only [CapyCaptureSet.peaks]
  exact CapyCaptureSet.NoPseudoPeak.cvar.applyAccess

end CoreCapybara
namespace Compilation

/-- **Per-atom cvar containment (the canonical-correspondence linchpin).**  An
    access-mode occurrence `a` of an origin cvar peak `d` whose `σ`-image is the
    *identity* cvar `e` (`σ.cvar d = {ε e}`) lands, after `σt`-substitution, inside
    `e`'s sub-peak item.  Proof: the SOURCE-level forward membership
    (`peaks_subst_cvar_fwd`, through the `SubstsTo` morphism) places `{a e}` among
    the sub peaks directly — no compiled-keystone atom trace, hence no frozen-branch
    ambiguity and NO non-collision precondition. -/
theorem peakItem_subst_atom {s1 s2 s1' s2' : Sig}
    {Γorig : CapyCtx s1} {Γsub : CapyCtx s1'} {scOrig : SrcCtx s1 s2} {scSub : SrcCtx s1' s2'}
    {σ : CapySubst s1 s1'} {σt : Subst s2 s2'} {cs : CapyCaptureSet s1}
    (hcompat : SubstCompat scSub scOrig σ σt)
    (htv : ∀ X, ∃ Y, σ.tvar X = CapyPureTy.tvar Y)
    (hsubsto : Γorig.SubstsTo Γsub σ)
    {a : Access} {d : BVar s1 .cvar} {e : BVar s1' .cvar}
    (hde : σ.cvar d = CapyCaptureSet.cvar (.M .epsilon) e)
    (ha : (CapyCaptureSet.cvar a d) ⊆ CapyCaptureSet.peaks Γorig cs) :
    ((CaptureSet.cvar a (scOrig.lookupCVar d)).subst σt) ⊆
      CapyCaptureSet.compile (peakItem (CapyCaptureSet.peakset Γsub (cs.subst σ)) e) scSub := by
  -- the substituted atom is exactly `{a W}` (W = ⟦e⟧) — applying access `a` to the
  -- full-access image `{ε W}` re-imposes `a`.
  have hatomeq : (CaptureSet.cvar a (scOrig.lookupCVar d)).subst σt
      = CaptureSet.cvar a (scSub.lookupCVar e) := by
    have hZW : σt.cvar (scOrig.lookupCVar d)
        = CaptureSet.cvar (.M .epsilon) (scSub.lookupCVar e) := by
      rw [← hcompat.cvar d, hde]; rfl
    simp only [CaptureSet.subst, hZW]
    cases a with
    | M m => cases m <;> rfl
    | drop => rfl
  rw [hatomeq]
  have hesub : (CapyCaptureSet.cvar a e) ⊆ CapyCaptureSet.peaks Γsub (cs.subst σ) :=
    CapyCaptureSet.peaks_subst_cvar_fwd htv hsubsto hde cs ha
  have h3 := CapyCaptureSet.compile_subset (sc := scSub)
    (cvar_subset_peakItem (P := CapyCaptureSet.peakset Γsub (cs.subst σ)) hesub)
  simpa only [CapyCaptureSet.compile] using h3

/-- **The full cvar-peak containment** (union of `peakItem_subst_atom` over the
    access-mode occurrences): an identity-image origin cvar peak `d` (`σ.cvar d = {ε e}`)
    has its whole compiled item, `σt`-substituted, inside `e`'s sub-peak item. -/
theorem peakItem_subst_subset {s1 s2 s1' s2' : Sig}
    {Γorig : CapyCtx s1} {Γsub : CapyCtx s1'} {scOrig : SrcCtx s1 s2} {scSub : SrcCtx s1' s2'}
    {σ : CapySubst s1 s1'} {σt : Subst s2 s2'} {cs : CapyCaptureSet s1}
    (hcompat : SubstCompat scSub scOrig σ σt)
    (htv : ∀ X, ∃ Y, σ.tvar X = CapyPureTy.tvar Y)
    (hsubsto : Γorig.SubstsTo Γsub σ)
    {d : BVar s1 .cvar} {e : BVar s1' .cvar}
    (hde : σ.cvar d = CapyCaptureSet.cvar (.M .epsilon) e) :
    (CapyCaptureSet.compile (peakItem (CapyCaptureSet.peakset Γorig cs) d) scOrig).subst σt ⊆
      CapyCaptureSet.compile (peakItem (CapyCaptureSet.peakset Γsub (cs.subst σ)) e) scSub := by
  have key : ∀ (L : List Access),
      (∀ b ∈ L, (CapyCaptureSet.cvar b d) ⊆ CapyCaptureSet.peaks Γorig cs) →
      (CapyCaptureSet.compile
          (L.foldr (fun b acc => CapyCaptureSet.cvar b d ∪ acc) .empty) scOrig).subst σt ⊆
        CapyCaptureSet.compile (peakItem (CapyCaptureSet.peakset Γsub (cs.subst σ)) e) scSub := by
    intro L
    induction L with
    | nil =>
      intro _
      simp only [List.foldr_nil, CapyCaptureSet.compile, CaptureSet.subst]
      exact CaptureSet.Subset.empty
    | cons b L' ih =>
      intro hL
      rw [List.foldr_cons]
      simp only [CapyCaptureSet.compile]
      refine CaptureSet.Subset.union_left ?_
        (ih (fun b' hb' => hL b' (List.mem_cons_of_mem _ hb')))
      exact peakItem_subst_atom hcompat htv hsubsto hde (hL b List.mem_cons_self)
  exact key (accessedAt (CapyCaptureSet.peakset Γorig cs) d)
    (fun b hb => accessedAt_go_subset _ (by simpa only [accessedAt] using hb))

/-- **A sub frozen-peak comes from a frozen source cvar.**  Under a non-merging
    `PeakSubstIso` σ with pseudo-free origin `cs` and a substitution morphism `Γorig ⟶ Γsub`,
    every frozen sub-peak `pseudo_peak C'` of `peaks Γsub (cs.subst σ)` is exactly the
    resolved, access-folded content `(peaks Γsub D).applyAccess m` of some origin cvar `c0`
    that σ freezes (`σ.cvar c0 = pseudo_peak D`).  Routed through the genuinely pseudo-free
    *origin* (`horig`) + the morphism (`hsubsto`) via `peaks_subst_pseudo_cvar`, so it holds
    even when σ freezes captured cvars (making `Γsub`'s var bounds carry frozen peaks). -/
theorem pseudo_sub_peak_frozen_source {s1 s1' : Sig}
    {Γorig : CapyCtx s1} {Γsub : CapyCtx s1'} {σ : CapySubst s1 s1'} {cs : CapyCaptureSet s1}
    {C' : CapyCaptureSet s1'}
    (hiso : PeakSubstIso σ) (hsubsto : Γorig.SubstsTo Γsub σ) (horig : Γorig.NoPseudoPeak)
    (hcs : cs.NoPseudoPeak)
    (h : (CapyCaptureSet.pseudo_peak C') ⊆ CapyCaptureSet.peaks Γsub (cs.subst σ)) :
    ∃ (c0 : BVar s1 .cvar) (D : CapyCaptureSet s1') (m : Access),
      σ.cvar c0 = CapyCaptureSet.pseudo_peak D ∧
      C' = (CapyCaptureSet.peaks Γsub D).applyAccess m := by
  obtain ⟨c0, m, _, hsub⟩ := CapyCaptureSet.peaks_subst_pseudo_cvar hsubsto horig cs hcs h
  have himg := hiso.image c0
  cases hp : hiso.toPeak c0 with
  | cvar e =>
    rw [hp] at himg
    simp only [Peak.asCaptureSet] at himg
    rw [himg] at hsub
    exact absurd hsub CapyCaptureSet.peaks_cvar_applyAccess_noPseudoPeak.not_pseudo_subset
  | pseudo D =>
    rw [hp] at himg
    simp only [Peak.asCaptureSet] at himg
    refine ⟨c0, D, m, himg, ?_⟩
    rw [himg] at hsub
    have happ : (CapyCaptureSet.pseudo_peak D).applyAccess m
        = CapyCaptureSet.pseudo_peak (D.applyAccess m) := by
      cases m with
      | M mm => cases mm <;> rfl
      | drop => rfl
    rw [happ] at hsub
    simp only [CapyCaptureSet.peaks] at hsub
    rw [CapyCaptureSet.pseudo_subset_pseudo_eq hsub, CapyCaptureSet.peaks_applyAccess_comm]

/-- **(★ Source-level frozen-peak presence — now DISCHARGED via `peaks_subst_frozen`.)**
    When `σ` FREEZES an origin cvar peak `d` (`σ.cvar d = pseudo_peak D`) that occurs at
    access `a` in the origin peaks `peaks Γorig cs`, its access-folded, `Γsub`-resolved
    frozen image `pseudo_peak ((peaks Γsub D).applyAccess a)` is present among the sub
    peaks `peaks Γsub (cs[σ])`.

    A frozen peak is erased by `compile` (`⟦pseudo_peak C⟧ = ⟦C⟧`), so the compiled
    keystone `compile_peaks_subst` cannot witness the frozen *wrapper's* presence — only
    its content's atoms.  The genuine device is the SOURCE-level context-substitution
    morphism `Γorig.SubstsTo Γsub σ` (the substitution analogue of `CapyCtx.RenamesTo`),
    threaded through `peaks_subst_frozen`; the `tvar`-as-`tvar` premise is exactly what
    the already-carried `SubstTvarCompat` supplies. -/
theorem frozen_sub_peak_present {s1 s1' : Sig}
    {Γorig : CapyCtx s1} {Γsub : CapyCtx s1'} {σ : CapySubst s1 s1'}
    (hsubsto : Γorig.SubstsTo Γsub σ) (htv : ∀ X, ∃ Y, σ.tvar X = CapyPureTy.tvar Y)
    {cs : CapyCaptureSet s1} {d : BVar s1 .cvar} {D : CapyCaptureSet s1'}
    (hdD : σ.cvar d = CapyCaptureSet.pseudo_peak D) :
    ∀ (a : Access), (CapyCaptureSet.cvar a d) ⊆ CapyCaptureSet.peaks Γorig cs →
      (CapyCaptureSet.pseudo_peak ((CapyCaptureSet.peaks Γsub D).applyAccess a))
        ⊆ CapyCaptureSet.peaks Γsub (CapyCaptureSet.subst cs σ) :=
  fun _ ha => CapyCaptureSet.peaks_subst_frozen htv hsubsto hdD cs ha

/-- **Identity-image sub-peak membership (sorry-free).**  When `σ` maps an origin cvar
    peak `d` to an identity-image cvar (`σ.cvar d = {ε e}`) that occurs in the origin
    peaks, `e` is a peak cvar of the sub peaks — directly by the SOURCE-level forward
    trace `peaks_subst_cvar_fwd`. -/
theorem identity_sub_peak_mem {s1 s1' : Sig}
    {Γorig : CapyCtx s1} {Γsub : CapyCtx s1'}
    {σ : CapySubst s1 s1'} {cs : CapyCaptureSet s1}
    (htv : ∀ X, ∃ Y, σ.tvar X = CapyPureTy.tvar Y)
    (hsubsto : Γorig.SubstsTo Γsub σ)
    {d : BVar s1 .cvar} {e : BVar s1' .cvar} {a0 : Access}
    (hde : σ.cvar d = CapyCaptureSet.cvar (.M .epsilon) e)
    (hd : (CapyCaptureSet.cvar a0 d) ⊆ CapyCaptureSet.peaks Γorig cs) :
    e ∈ peakCvars (CapyCaptureSet.peakset Γsub (cs.subst σ)) :=
  cvar_mem_peakCvars (CapyCaptureSet.peaks_subst_cvar_fwd htv hsubsto hde cs hd)

/-- **Reverse cvar-item containment (sorry-free).**  Dual of `peakItem_subst_subset`: the
    SUB cvar item for an identity image `e` (σ.cvar d = {ε e}) is contained in the
    σt-substituted ORIGIN cvar item for `d`.  Every occurrence of `e` in `peaks(cs[σ])`
    traces back SOURCE-level (`peaks_subst_cvar`) to a unique origin cvar `c0`; `c0 = d`
    because a frozen image keeps its opaque wrapper source-side (a bare cvar atom has no
    `Subset` path into `pseudo_peak _`) and the identity image fixes the peak via
    `hiso.inj`.  No compiled keystone, no `CVarInjective`, no non-collision. -/
theorem peakItem_subst_supset {s1 s2 s1' s2' : Sig}
    {Γorig : CapyCtx s1} {Γsub : CapyCtx s1'} {scOrig : SrcCtx s1 s2} {scSub : SrcCtx s1' s2'}
    {σ : CapySubst s1 s1'} {σt : Subst s2 s2'} {cs : CapyCaptureSet s1}
    (hcompat : SubstCompat scSub scOrig σ σt)
    (hiso : PeakSubstIso σ)
    (htv : ∀ X, ∃ Y, σ.tvar X = CapyPureTy.tvar Y)
    (hsubsto : Γorig.SubstsTo Γsub σ)
    {d : BVar s1 .cvar} {e : BVar s1' .cvar}
    (hde : σ.cvar d = CapyCaptureSet.cvar (.M .epsilon) e) :
    CapyCaptureSet.compile (peakItem (CapyCaptureSet.peakset Γsub (cs.subst σ)) e) scSub ⊆
      (CapyCaptureSet.compile (peakItem (CapyCaptureSet.peakset Γorig cs) d) scOrig).subst σt := by
  -- Per-atom: a `b`-occurrence of `e` lands inside the σt-image of `d`'s origin item.
  have atom : ∀ (b : Access),
      (CapyCaptureSet.cvar b e) ⊆ CapyCaptureSet.peaks Γsub (cs.subst σ) →
      (CaptureSet.cvar b (scSub.lookupCVar e)) ⊆ ((CapyCaptureSet.compile
        (peakItem (CapyCaptureSet.peakset Γorig cs) d) scOrig).subst σt) := by
    intro b hb
    obtain ⟨c0, m, hc0cs, htrace⟩ := CapyCaptureSet.peaks_subst_cvar hsubsto htv cs hb
    -- Identify the origin: the image analysis pins `b = m` and `c0 = d`.
    have hkey : b = m ∧ c0 = d := by
      cases htc : hiso.toPeak c0 with
      | pseudo C0 =>
        exfalso
        have himg := hiso.image c0
        rw [htc] at himg; simp only [Peak.asCaptureSet] at himg
        rw [himg] at htrace
        -- the frozen wrapper survives `applyAccess` and `peaks` — no cvar atom inside.
        obtain ⟨C1, hC1⟩ : ∃ C1, (CapyCaptureSet.pseudo_peak C0).applyAccess m
            = CapyCaptureSet.pseudo_peak C1 := by
          cases m with
          | M mu => cases mu with
            | epsilon => exact ⟨C0, rfl⟩
            | ro => exact ⟨C0.applyRO, rfl⟩
          | drop => exact ⟨C0.applyDrop, rfl⟩
        rw [hC1] at htrace
        simp only [CapyCaptureSet.peaks] at htrace
        cases htrace
      | cvar f =>
        have himg := hiso.image c0
        rw [htc] at himg; simp only [Peak.asCaptureSet] at himg
        rw [himg] at htrace
        have hacc : (CapyCaptureSet.cvar (.M .epsilon) f).applyAccess m
            = CapyCaptureSet.cvar m f := by
          cases m with
          | M mu => cases mu <;> rfl
          | drop => rfl
        rw [hacc] at htrace
        simp only [CapyCaptureSet.peaks] at htrace
        obtain ⟨hbm, hef⟩ := CapyCaptureSet.cvar_subset_cvar_inv htrace
        subst hef
        have htd : hiso.toPeak d = Peak.cvar e := by
          have himgd := hiso.image d
          rw [hde] at himgd
          cases htcd : hiso.toPeak d with
          | cvar g =>
            rw [htcd] at himgd
            simp only [Peak.asCaptureSet, CapyCaptureSet.cvar.injEq] at himgd
            exact congrArg Peak.cvar himgd.2.symm
          | pseudo D'' => rw [htcd] at himgd; simp [Peak.asCaptureSet] at himgd
        exact ⟨hbm, hiso.inj (by rw [htc, htd])⟩
    obtain ⟨hbm, hc0d⟩ := hkey
    rw [hc0d] at hc0cs
    rw [hbm]
    have hmem : (CapyCaptureSet.cvar m d) ⊆ peakItem (CapyCaptureSet.peakset Γorig cs) d :=
      cvar_subset_peakItem hc0cs
    have hcm : (CaptureSet.cvar m (scOrig.lookupCVar d))
        ⊆ CapyCaptureSet.compile (peakItem (CapyCaptureSet.peakset Γorig cs) d) scOrig := by
      have h0 := CapyCaptureSet.compile_subset (sc := scOrig) hmem
      simpa only [CapyCaptureSet.compile] using h0
    have hsm := CaptureSet.Subset.subst (σ := σt) hcm
    have hatomeq : (CaptureSet.cvar m (scOrig.lookupCVar d)).subst σt
        = CaptureSet.cvar m (scSub.lookupCVar e) := by
      have hZW : σt.cvar (scOrig.lookupCVar d)
          = CaptureSet.cvar (.M .epsilon) (scSub.lookupCVar e) := by
        rw [← hcompat.cvar d, hde]; rfl
      simp only [CaptureSet.subst, hZW]
      cases m with
      | M mu => cases mu <;> rfl
      | drop => rfl
    rw [hatomeq] at hsm
    exact hsm
  -- Fold the atom lemma over the access-mode occurrences of `e`.
  have key : ∀ (L : List Access),
      (∀ b ∈ L, (CapyCaptureSet.cvar b e) ⊆ CapyCaptureSet.peaks Γsub (cs.subst σ)) →
      CapyCaptureSet.compile (L.foldr (fun b acc => CapyCaptureSet.cvar b e ∪ acc) .empty) scSub ⊆
        ((CapyCaptureSet.compile
          (peakItem (CapyCaptureSet.peakset Γorig cs) d) scOrig).subst σt) := by
    intro L
    induction L with
    | nil =>
      intro _
      simp only [List.foldr_nil, CapyCaptureSet.compile]
      exact CaptureSet.Subset.empty
    | cons b L' ih =>
      intro hL
      rw [List.foldr_cons]
      simp only [CapyCaptureSet.compile]
      exact CaptureSet.Subset.union_left (atom b (hL b List.mem_cons_self))
        (ih (fun b' hb' => hL b' (List.mem_cons_of_mem _ hb')))
  exact key (accessedAt (CapyCaptureSet.peakset Γsub (cs.subst σ)) e)
    (fun b hb => accessedAt_go_subset _ (by simpa only [accessedAt] using hb))

/-- A cvar atom of `cs` is preserved by `peaks` (which keeps cvar atoms verbatim). -/
theorem CapyCaptureSet.cvar_subset_peaks_self {s : Sig} {Γ : CapyCtx s} {m : Access}
    {c : BVar s .cvar} {cs : CapyCaptureSet s} (h : (CapyCaptureSet.cvar m c) ⊆ cs) :
    (CapyCaptureSet.cvar m c) ⊆ CapyCaptureSet.peaks Γ cs := by
  induction cs with
  | empty => cases h
  | union cs1 cs2 ih1 ih2 =>
    simp only [CapyCaptureSet.peaks]
    cases h with
    | union_right_left h1 => exact CapyCaptureSet.Subset.union_right_left (ih1 h1)
    | union_right_right h2 => exact CapyCaptureSet.Subset.union_right_right (ih2 h2)
  | cvar m' c' => cases h; simp only [CapyCaptureSet.peaks]; exact CapyCaptureSet.Subset.refl
  | var m' x => cases h
  | pseudo_peak C _ => cases h

/-- **Reverse FROZEN-item containment (sorry-free).**  Dual of `peakItem_subst_atom_pseudo`
    (union form): the SUB frozen item keyed by `(peaks Γsub D02).modeErase` is contained in
    the σt-substituted ORIGIN cvar item for `c02` (the unique cvar `σ` freezes,
    `σ.cvar c02 = pseudo_peak D02`).  Every frozen sub-peak traces back (via
    `peaks_subst_pseudo_mem'`) to a frozen origin cvar; `uniqueFrozen` forces it to be
    `c02`, so its compiled content `⟦D02⟧[a]` is exactly the `σt`-image of `c02`'s item. -/
theorem pseudoItem_subst_supset {s1 s2 s1' s2' : Sig}
    {Γorig : CapyCtx s1} {Γsub : CapyCtx s1'} {scOrig : SrcCtx s1 s2} {scSub : SrcCtx s1' s2'}
    {σ : CapySubst s1 s1'} {σt : Subst s2 s2'} {cs : CapyCaptureSet s1}
    (hΓS : Γsub.IsClosed) (haS : SrcAligned Γsub scSub)
    (hcompat : SubstCompat scSub scOrig σ σt)
    (hcsnp : cs.NoPseudoPeak) (hsubsto : Γorig.SubstsTo Γsub σ) (hΓOnp : Γorig.NoPseudoPeak)
    (hiso : PeakSubstIso σ) (hscS : CapySubst.IsClosed σ)
    {c02 : BVar s1 .cvar} {D02 : CapyCaptureSet s1'}
    (hc02 : σ.cvar c02 = CapyCaptureSet.pseudo_peak D02) :
    CapyCaptureSet.compile (pseudoItem (CapyCaptureSet.peakset Γsub (cs.subst σ))
        ((CapyCaptureSet.peaks Γsub D02).modeErase)) scSub ⊆
      ((CapyCaptureSet.compile
        (peakItem (CapyCaptureSet.peakset Γorig cs) c02) scOrig).subst σt) := by
  have hD02cl : D02.IsClosed := by
    have h0 := hscS.cvar_closed c02; rw [hc02] at h0
    cases h0 with | pseudo_peak h => exact h
  have ht02 : hiso.toPeak c02 = Peak.pseudo D02 := by
    have h2 := hiso.image c02; rw [hc02] at h2
    cases ht : hiso.toPeak c02 with
    | cvar g => rw [ht] at h2; simp [Peak.asCaptureSet] at h2
    | pseudo D' =>
      rw [ht] at h2
      simp only [Peak.asCaptureSet, CapyCaptureSet.pseudo_peak.injEq] at h2
      exact congrArg Peak.pseudo h2.symm
  -- Each frozen sub-peak's compiled content lands in `c02`'s σt-substituted origin item.
  have atom : ∀ C'', (CapyCaptureSet.pseudo_peak C'') ⊆ CapyCaptureSet.peaks Γsub (cs.subst σ) →
      CapyCaptureSet.compile C'' scSub ⊆
        ((CapyCaptureSet.compile
          (peakItem (CapyCaptureSet.peakset Γorig cs) c02) scOrig).subst σt) := by
    intro C'' hsub
    obtain ⟨c0, m, hocc, hp⟩ :=
      CapyCaptureSet.peaks_subst_pseudo_cvar hsubsto hΓOnp cs hcsnp hsub
    have himg := hiso.image c0
    cases htc : hiso.toPeak c0 with
    | cvar f =>
      exfalso
      rw [htc] at himg; simp only [Peak.asCaptureSet] at himg
      rw [himg] at hp
      exact absurd hp CapyCaptureSet.peaks_cvar_applyAccess_noPseudoPeak.not_pseudo_subset
    | pseudo D0' =>
      rw [htc] at himg; simp only [Peak.asCaptureSet] at himg
      have hc0eq : c0 = c02 := hiso.uniqueFrozen htc ht02
      subst c0
      have hD : D0' = D02 :=
        CapyCaptureSet.pseudo_peak.inj (himg.symm.trans hc02)
      subst D0'
      rw [hc02, CapyCaptureSet.applyAccess_pseudo_peak, CapyCaptureSet.peaks] at hp
      have hC'' : C'' = (CapyCaptureSet.peaks Γsub D02).applyAccess m := by
        rw [CapyCaptureSet.pseudo_subset_pseudo_eq hp, CapyCaptureSet.peaks_applyAccess_comm]
      subst hC''
      have hmem : (CapyCaptureSet.cvar m c02) ⊆ peakItem (CapyCaptureSet.peakset Γorig cs) c02 :=
        cvar_subset_peakItem hocc
      have hcm : (CaptureSet.cvar m (scOrig.lookupCVar c02))
          ⊆ CapyCaptureSet.compile (peakItem (CapyCaptureSet.peakset Γorig cs) c02) scOrig := by
        have h0 := CapyCaptureSet.compile_subset (sc := scOrig) hmem
        simpa only [CapyCaptureSet.compile] using h0
      have hsm := CaptureSet.Subset.subst (σ := σt) hcm
      refine CaptureSet.Subset.trans ?_ hsm
      rw [CapyCaptureSet.compile_applyAccess, CapyCaptureSet.compile_peaks hΓS haS hD02cl]
      simp only [CaptureSet.subst, ← hcompat.cvar c02, hc02, CapyCaptureSet.compile]
      exact CaptureSet.Subset.refl
  -- Fold the atom over the frozen-peak occurrences collected by `pseudoItem.go`.
  have key : ∀ (S : CapyCaptureSet s1'),
      (∀ C, (CapyCaptureSet.pseudo_peak C) ⊆ S →
        CapyCaptureSet.compile C scSub ⊆
          ((CapyCaptureSet.compile
            (peakItem (CapyCaptureSet.peakset Γorig cs) c02) scOrig).subst σt)) →
      CapyCaptureSet.compile (pseudoItem.go ((CapyCaptureSet.peaks Γsub D02).modeErase) S) scSub ⊆
        ((CapyCaptureSet.compile
          (peakItem (CapyCaptureSet.peakset Γorig cs) c02) scOrig).subst σt) := by
    intro S
    induction S with
    | empty =>
      intro _; simp only [pseudoItem.go, CapyCaptureSet.compile]; exact CaptureSet.Subset.empty
    | union S1 S2 ih1 ih2 =>
      intro hS
      simp only [pseudoItem.go, CapyCaptureSet.compile]
      exact CaptureSet.Subset.union_left
        (ih1 (fun C h => hS C (CapyCaptureSet.Subset.union_right_left h)))
        (ih2 (fun C h => hS C (CapyCaptureSet.Subset.union_right_right h)))
    | cvar m' c' =>
      intro _; simp only [pseudoItem.go, CapyCaptureSet.compile]; exact CaptureSet.Subset.empty
    | var m' x =>
      intro _; simp only [pseudoItem.go, CapyCaptureSet.compile]; exact CaptureSet.Subset.empty
    | pseudo_peak C _ =>
      intro hS
      simp only [pseudoItem.go]
      split
      · simp only [CapyCaptureSet.compile]; exact hS C CapyCaptureSet.Subset.refl
      · simp only [CapyCaptureSet.compile]; exact CaptureSet.Subset.empty
  simpa only [pseudoItem] using key (CapyCaptureSet.peaks Γsub (cs.subst σ)) atom

/-- **Sub cvar peak ⟶ origin identity image (sorry-free).**  A cvar peak `d1` of the
    substituted set is the identity `σ`-image of a unique origin cvar peak `c01`.  The atom
    reverse-traces (`peaks_subst_cvar`) to `c01`; `hiso` then reads off `σ.cvar c01 = {ε d1}`
    (the frozen alternative is impossible — a bare cvar cannot sit in a `pseudo_peak`). -/
theorem sub_cvar_peak_origin {s1 s1' : Sig}
    {Γorig : CapyCtx s1} {Γsub : CapyCtx s1'} {σ : CapySubst s1 s1'}
    (hiso : PeakSubstIso σ) (hsubsto : Γorig.SubstsTo Γsub σ)
    (htv : ∀ X, ∃ Y, σ.tvar X = CapyPureTy.tvar Y)
    {cs : CapyCaptureSet s1} {d1 : BVar s1' .cvar}
    (hmem : d1 ∈ peakCvars (CapyCaptureSet.peakset Γsub (cs.subst σ))) :
    ∃ (c01 : BVar s1 .cvar),
      σ.cvar c01 = CapyCaptureSet.cvar (.M .epsilon) d1 ∧
      c01 ∈ peakCvars (CapyCaptureSet.peakset Γorig cs) := by
  obtain ⟨a1, hocc⟩ := peakCvars_occ hmem
  obtain ⟨c01, m, hocc01, hatom⟩ := CapyCaptureSet.peaks_subst_cvar hsubsto htv cs hocc
  have himg := hiso.image c01
  cases htc : hiso.toPeak c01 with
  | cvar f =>
    rw [htc] at himg; simp only [Peak.asCaptureSet] at himg
    rw [himg, CapyCaptureSet.peaks_applyAccess_comm] at hatom
    simp only [CapyCaptureSet.peaks] at hatom
    have hd1f : d1 = f := CapyCaptureSet.cvar_subset_cvar_applyAccess hatom
    refine ⟨c01, ?_, cvar_mem_peakCvars hocc01⟩
    rw [himg, hd1f]
  | pseudo D =>
    exfalso
    rw [htc] at himg; simp only [Peak.asCaptureSet] at himg
    rw [himg, CapyCaptureSet.applyAccess_pseudo_peak, CapyCaptureSet.peaks] at hatom
    cases hatom

/-- **Sub frozen peak ⟶ origin frozen cvar (sorry-free).**  A frozen peak `D2` of the
    substituted set comes from a frozen origin cvar peak `c02` (`σ.cvar c02 = pseudo_peak D02`,
    `D2 = ⌊peaks D02⌋`).  Routes the occurrence through `peaks_subst_pseudo_mem'`; `hiso`
    identifies the image (the cvar-image alternative is impossible — a `pseudo_peak` cannot
    sit in a resolved cvar atom). -/
theorem sub_pseudo_peak_origin {s1 s1' : Sig}
    {Γorig : CapyCtx s1} {Γsub : CapyCtx s1'} {σ : CapySubst s1 s1'}
    (hiso : PeakSubstIso σ) (hsubsto : Γorig.SubstsTo Γsub σ) (horig : Γorig.NoPseudoPeak)
    {cs : CapyCaptureSet s1} (hcsnp : cs.NoPseudoPeak)
    {D2 : CapyCaptureSet s1'}
    (hmem : D2 ∈ peakPseudos (CapyCaptureSet.peakset Γsub (cs.subst σ))) :
    ∃ (c02 : BVar s1 .cvar) (D02 : CapyCaptureSet s1'),
      σ.cvar c02 = CapyCaptureSet.pseudo_peak D02 ∧
      D2 = (CapyCaptureSet.peaks Γsub D02).modeErase ∧
      c02 ∈ peakCvars (CapyCaptureSet.peakset Γorig cs) := by
  obtain ⟨C', hC'sub, hC'm⟩ := peakPseudos_occ hmem
  obtain ⟨c0, m, hocc, hp⟩ :=
    CapyCaptureSet.peaks_subst_pseudo_cvar hsubsto horig cs hcsnp hC'sub
  have himg := hiso.image c0
  cases htc : hiso.toPeak c0 with
  | cvar f =>
    exfalso
    rw [htc] at himg; simp only [Peak.asCaptureSet] at himg
    rw [himg] at hp
    exact absurd hp CapyCaptureSet.peaks_cvar_applyAccess_noPseudoPeak.not_pseudo_subset
  | pseudo D0 =>
    rw [htc] at himg; simp only [Peak.asCaptureSet] at himg
    refine ⟨c0, D0, himg, ?_, cvar_mem_peakCvars hocc⟩
    rw [← hC'm]
    rw [himg, CapyCaptureSet.applyAccess_pseudo_peak, CapyCaptureSet.peaks] at hp
    have hC' : C' = (CapyCaptureSet.peaks Γsub D0).applyAccess m := by
      rw [CapyCaptureSet.pseudo_subset_pseudo_eq hp, CapyCaptureSet.peaks_applyAccess_comm]
    rw [hC', CapyCaptureSet.modeErase_applyAccess]

/-! ### `srcCtx`-realignment for re-abstracted locks (the `arrow` device)

The `arrow` compiler binds the value parameter `x` to its self-capture `{cx}`
(`lookupVar x = {cx}`), which makes `SrcAligned` FAIL for `ctxLock`/`ctxDomain`
(alignment would demand `{cx} = ⟦T.captureSet⟧`).  But the compiled lock reads the
`srcCtx` only through `lookupCVar`: `peaks Γ W` resolves every bound var into the
context (`peaksVarBound`), so its output has NO bound-var atom, and `compile` of a
bound-var-free set never consults `lookupVar`.  Hence the lock is invariant under
changing the `x`-entry's capture image — we may realign it to `⟦T.captureSet⟧` and
reuse the SrcAligned-based dispatch. -/

end Compilation
namespace CoreCapybara

/-- A capture set with no *bound* term-variable atom anywhere (incl. inside frozen
    wrappers).  `compile` of such a set never consults `lookupVar`, only `lookupCVar`. -/
def CapyCaptureSet.NoBoundVar {s : Sig} : CapyCaptureSet s → Prop
| .empty => True
| .union c1 c2 => NoBoundVar c1 ∧ NoBoundVar c2
| .cvar _ _ => True
| .var _ (.bound _) => False
| .var _ (.free _) => True
| .pseudo_peak C => NoBoundVar C

theorem CapyCaptureSet.NoBoundVar.applyRO {s : Sig} {cs : CapyCaptureSet s}
    (h : cs.NoBoundVar) : cs.applyRO.NoBoundVar := by
  induction cs with
  | empty => exact True.intro
  | union c1 c2 ih1 ih2 => exact ⟨ih1 h.1, ih2 h.2⟩
  | cvar a c => exact True.intro
  | var a x => cases x with
    | bound x' => exact h.elim
    | free n => exact True.intro
  | pseudo_peak C ih => exact ih h

theorem CapyCaptureSet.NoBoundVar.applyDrop {s : Sig} {cs : CapyCaptureSet s}
    (h : cs.NoBoundVar) : cs.applyDrop.NoBoundVar := by
  induction cs with
  | empty => exact True.intro
  | union c1 c2 ih1 ih2 => exact ⟨ih1 h.1, ih2 h.2⟩
  | cvar a c => exact True.intro
  | var a x => cases x with
    | bound x' => exact h.elim
    | free n => exact True.intro
  | pseudo_peak C ih => exact ih h

theorem CapyCaptureSet.NoBoundVar.applyAccess {s : Sig} {cs : CapyCaptureSet s} {a : Access}
    (h : cs.NoBoundVar) : (cs.applyAccess a).NoBoundVar := by
  cases a with
  | M m => cases m with
    | epsilon => exact h
    | ro => exact h.applyRO
  | drop => exact h.applyDrop

theorem CapyCaptureSet.NoBoundVar.rename {s1 s2 : Sig} {cs : CapyCaptureSet s1} {f : Rename s1 s2}
    (h : cs.NoBoundVar) : (cs.rename f).NoBoundVar := by
  induction cs with
  | empty => exact True.intro
  | union c1 c2 ih1 ih2 => exact ⟨ih1 h.1, ih2 h.2⟩
  | cvar a c => exact True.intro
  | var a x => cases x with
    | bound x' => exact h.elim
    | free n => exact True.intro
  | pseudo_peak C ih => exact ih h

mutual
theorem CapyCaptureSet.peaksVarBound_noBoundVar {s : Sig} (Γ : CapyCtx s) (m : Access)
    (x : BVar s .var) : (CapyCaptureSet.peaksVarBound Γ m x).NoBoundVar := by
  match Γ, x with
  | .push Γ' (.var T), .here =>
    rw [CapyCaptureSet.peaksVarBound]
    exact ((CapyCaptureSet.peaks_noBoundVar Γ' T.captureSet).rename).applyAccess
  | .push Γ' b, .there x' =>
    rw [CapyCaptureSet.peaksVarBound]
    exact (CapyCaptureSet.peaksVarBound_noBoundVar Γ' m x').rename
termination_by (sizeOf Γ, sizeOf x + 1)

theorem CapyCaptureSet.peaks_noBoundVar {s : Sig} (Γ : CapyCtx s) (cs : CapyCaptureSet s) :
    (CapyCaptureSet.peaks Γ cs).NoBoundVar := by
  match cs with
  | .empty => rw [CapyCaptureSet.peaks]; exact True.intro
  | .union c1 c2 =>
    rw [CapyCaptureSet.peaks]
    exact ⟨CapyCaptureSet.peaks_noBoundVar Γ c1, CapyCaptureSet.peaks_noBoundVar Γ c2⟩
  | .cvar m c => rw [CapyCaptureSet.peaks]; exact True.intro
  | .var m (.free n) => rw [CapyCaptureSet.peaks]; exact True.intro
  | .var m (.bound x) =>
    rw [CapyCaptureSet.peaks]; exact CapyCaptureSet.peaksVarBound_noBoundVar Γ m x
  | .pseudo_peak C =>
    rw [CapyCaptureSet.peaks]; exact CapyCaptureSet.peaks_noBoundVar Γ C
termination_by (sizeOf Γ, sizeOf cs)
end

end CoreCapybara
namespace Compilation

/-- **`compile` is `lookupVar`-insensitive on bound-var-free sets.**  Two source
    contexts agreeing on every `lookupCVar` compile such a set identically. -/
theorem CapyCaptureSet.compile_eq_of_lookupCVar {s1 s2 : Sig} {cs : CapyCaptureSet s1}
    {sc1 sc2 : SrcCtx s1 s2} (h : cs.NoBoundVar)
    (hcv : ∀ (c : BVar s1 .cvar), sc1.lookupCVar c = sc2.lookupCVar c) :
    CapyCaptureSet.compile cs sc1 = CapyCaptureSet.compile cs sc2 := by
  induction cs with
  | empty => rfl
  | union c1 c2 ih1 ih2 =>
    simp only [CapyCaptureSet.compile, ih1 h.1, ih2 h.2]
  | cvar a c => simp only [CapyCaptureSet.compile, hcv c]
  | var a x => cases x with
    | bound x' => exact h.elim
    | free n => simp only [CapyCaptureSet.compile]
  | pseudo_peak C ih => simp only [CapyCaptureSet.compile, ih h]

/-- The compiled key item of any peak is bound-var-free: `cvar` peaks build pure
    `cvar` unions; `pseudo` peaks freeze a (bound-var-free) base from `P.cs`. -/
theorem peakKeyItem_noBoundVar {s : Sig} {P : CapyPeakSet s} (hP : P.cs.NoBoundVar)
    (p : Peak s) : (peakKeyItem P p).NoBoundVar := by
  cases p with
  | cvar c =>
    simp only [peakKeyItem, peakItem]
    induction (accessedAt P c) with
    | nil => exact True.intro
    | cons a as ih => exact ⟨True.intro, ih⟩
  | pseudo D =>
    simp only [peakKeyItem, pseudoItem]
    have aux : ∀ (cs : CapyCaptureSet s),
        cs.NoBoundVar → (pseudoItem.go D cs).NoBoundVar := by
      intro cs
      induction cs with
      | empty => intro _; exact True.intro
      | union c1 c2 ih1 ih2 =>
        intro hcs; simp only [pseudoItem.go]; exact ⟨ih1 hcs.1, ih2 hcs.2⟩
      | cvar a c => intro _; exact True.intro
      | var a x => intro _; exact True.intro
      | pseudo_peak C ih =>
        intro hcs; simp only [pseudoItem.go]
        split
        · exact hcs
        · exact True.intro
    exact aux P.cs hP

/-- **The compiled lock is `lookupVar`-insensitive.**  `peakSepCtx (peakset Γ W)`
    reads `srcCtx` only through `lookupCVar` (its items are bound-var-free), so two
    contexts agreeing on `lookupCVar` build the same separation context. -/
theorem peakSepCtx_eq_of_lookupCVar {s1 s2 : Sig} {Γ : CapyCtx s1} {P : CapyPeakSet s1}
    {sc1 sc2 : SrcCtx s1 s2} (hP : P.cs.NoBoundVar)
    (hcv : ∀ (c : BVar s1 .cvar), sc1.lookupCVar c = sc2.lookupCVar c) :
    peakSepCtx Γ P sc1 = peakSepCtx Γ P sc2 := by
  simp only [peakSepCtx]
  generalize (SepCtx.empty : SepCtx s2) = acc
  induction (peakList P).filter (fun p => decide (Peak.IsStable Γ p)) generalizing acc with
  | nil => rfl
  | cons p ps ih =>
    simp only [List.foldl]
    rw [CapyCaptureSet.compile_eq_of_lookupCVar (peakKeyItem_noBoundVar hP p) hcv]
    exact ih _

/-! ### `realign`: the always-available aligned surrogate

`realign Γ sc` rewrites each term-binder's capture image in `sc` to its declared latent
`⟦T.captureSet⟧` (keeping `cvar`/`tvar` images), producing an *aligned* source context that
agrees with `sc` on every `lookupCVar`/`lookupTVar`.  Compiled LOCKS (bound-var-free) are
insensitive to the difference, so the SrcAligned-based dispatch can run at `realign Γ sc`
and transport back — this is what lets `compile_subst_subtyp` drop its `SrcAligned` premise
and so recurse through the `arrow`'s re-abstracted (`x ↦ {cx}`) domain/lock/body contexts. -/
def SrcCtx.realign : {s1 : Sig} → CapyCtx s1 → SrcCtx s1 s2 → SrcCtx s1 s2
  | _, .empty, .empty => .empty
  | _, .push Γ' (.var T), .cons (.var bv _) sc' =>
      .cons (.var bv (CapyCaptureSet.compile T.captureSet (SrcCtx.realign Γ' sc')))
        (SrcCtx.realign Γ' sc')
  | _, .push Γ' (.cvar _ _), .cons info sc' => .cons info (SrcCtx.realign Γ' sc')
  | _, .push Γ' (.tvar _), .cons info sc' => .cons info (SrcCtx.realign Γ' sc')

@[simp] theorem SrcCtx.realign_lookupCVar {s1 s2 : Sig} (Γ : CapyCtx s1) (sc : SrcCtx s1 s2)
    (c : BVar s1 .cvar) : (SrcCtx.realign Γ sc).lookupCVar c = sc.lookupCVar c := by
  match Γ, sc, c with
  | .push Γ' (.var _), .cons (.var _ _) sc', .there c' =>
      simp only [SrcCtx.realign, SrcCtx.lookupCVar]; exact SrcCtx.realign_lookupCVar Γ' sc' c'
  | .push Γ' (.cvar _ _), .cons (.cvar _) sc', .here =>
      simp only [SrcCtx.realign, SrcCtx.lookupCVar]
  | .push Γ' (.cvar _ _), .cons (.cvar _) sc', .there c' =>
      simp only [SrcCtx.realign, SrcCtx.lookupCVar]; exact SrcCtx.realign_lookupCVar Γ' sc' c'
  | .push Γ' (.tvar _), .cons (.tvar _) sc', .there c' =>
      simp only [SrcCtx.realign, SrcCtx.lookupCVar]; exact SrcCtx.realign_lookupCVar Γ' sc' c'

@[simp] theorem SrcCtx.realign_lookupTVar {s1 s2 : Sig} (Γ : CapyCtx s1) (sc : SrcCtx s1 s2)
    (X : BVar s1 .tvar) : (SrcCtx.realign Γ sc).lookupTVar X = sc.lookupTVar X := by
  match Γ, sc, X with
  | .push Γ' (.var _), .cons (.var _ _) sc', .there X' =>
      simp only [SrcCtx.realign, SrcCtx.lookupTVar]; exact SrcCtx.realign_lookupTVar Γ' sc' X'
  | .push Γ' (.cvar _ _), .cons (.cvar _) sc', .there X' =>
      simp only [SrcCtx.realign, SrcCtx.lookupTVar]; exact SrcCtx.realign_lookupTVar Γ' sc' X'
  | .push Γ' (.tvar _), .cons (.tvar _) sc', .here =>
      simp only [SrcCtx.realign, SrcCtx.lookupTVar]
  | .push Γ' (.tvar _), .cons (.tvar _) sc', .there X' =>
      simp only [SrcCtx.realign, SrcCtx.lookupTVar]; exact SrcCtx.realign_lookupTVar Γ' sc' X'

/-- `realign` always yields a `SrcAligned` context. -/
theorem SrcCtx.realign_aligned {s1 s2 : Sig} (Γ : CapyCtx s1) (sc : SrcCtx s1 s2) :
    SrcAligned Γ (SrcCtx.realign Γ sc) := by
  intro x U hlook
  induction hlook generalizing s2 with
  | here =>
    cases sc with
    | cons info sc' =>
      cases info with
      | var bv cs =>
        simp only [SrcCtx.realign, SrcCtx.lookupVar]
        exact CapyCaptureSet.compile_captureSet_weaken.symm
  | there hlook0 ih =>
    cases sc with
    | cons info sc' =>
      rename_i b
      cases b with
      | var T1 =>
        cases info with
        | var bv cs =>
          simp only [SrcCtx.realign, SrcCtx.lookupVar]
          exact (ih sc').trans CapyCaptureSet.compile_captureSet_weaken.symm
      | cvar a cb =>
        cases info with
        | cvar c =>
          simp only [SrcCtx.realign, SrcCtx.lookupVar]
          exact (ih sc').trans CapyCaptureSet.compile_captureSet_weaken.symm
      | tvar S =>
        cases info with
        | tvar X =>
          simp only [SrcCtx.realign, SrcCtx.lookupVar]
          exact (ih sc').trans CapyCaptureSet.compile_captureSet_weaken.symm

/-- On an already-`SrcAligned` context, `realign` is the identity (var images already
    equal `⟦T.captureSet⟧`).  Lets the base call sites supply the real `srcCtx`. -/
theorem SrcCtx.realign_eq_self {s1 s2 : Sig} (Γ : CapyCtx s1) (sc : SrcCtx s1 s2)
    (h : SrcAligned Γ sc) : SrcCtx.realign Γ sc = sc := by
  match Γ, sc with
  | .empty, .empty => rfl
  | .push Γ' (.var T), .cons (.var bv cs) sc' =>
      have hrest : SrcCtx.realign Γ' sc' = sc' := SrcCtx.realign_eq_self Γ' sc' h.peel
      have hh := h (CapyCtx.LookupVar.here (Γ := Γ') (T := T))
      simp only [SrcCtx.lookupVar] at hh
      have hcs : cs = CapyCaptureSet.compile T.captureSet sc' :=
        hh.trans CapyCaptureSet.compile_captureSet_weaken
      simp only [SrcCtx.realign, hrest, hcs]
  | .push Γ' (.cvar a cb), .cons (.cvar c) sc' =>
      have hrest : SrcCtx.realign Γ' sc' = sc' := SrcCtx.realign_eq_self Γ' sc' h.peel
      simp only [SrcCtx.realign, hrest]
  | .push Γ' (.tvar S), .cons (.tvar X) sc' =>
      have hrest : SrcCtx.realign Γ' sc' = sc' := SrcCtx.realign_eq_self Γ' sc' h.peel
      simp only [SrcCtx.realign, hrest]

/-- `realign` commutes with a target renaming (it only rewrites capture *images*, which
    rename pointwise).  Lets the surrogate `SubstCompat` thread through `weakenTarget`. -/
theorem SrcCtx.realign_rename {s1 s2 s2' : Sig} (Γ : CapyCtx s1) (sc : SrcCtx s1 s2)
    (ρ : Rename s2 s2') :
    SrcCtx.realign Γ (sc.rename ρ) = (SrcCtx.realign Γ sc).rename ρ := by
  match Γ, sc with
  | .empty, .empty => rfl
  | .push Γ' (.var T), .cons (.var bv cs) sc' =>
      simp only [SrcCtx.rename, SrcBinderInfo.rename, SrcCtx.realign]
      rw [SrcCtx.realign_rename Γ' sc' ρ, CapyCaptureSet.compile_rename]
  | .push Γ' (.cvar a cb), .cons (.cvar c) sc' =>
      simp only [SrcCtx.rename, SrcBinderInfo.rename, SrcCtx.realign,
        SrcCtx.realign_rename Γ' sc' ρ]
  | .push Γ' (.tvar S), .cons (.tvar X) sc' =>
      simp only [SrcCtx.rename, SrcBinderInfo.rename, SrcCtx.realign,
        SrcCtx.realign_rename Γ' sc' ρ]

/-- **`compile_peaks_subst` without the `SrcAligned` premise.**  Both peak-sets are
    bound-var-free, so compiling them is `lookupVar`-insensitive: transport to the
    aligned `realign` surrogate, apply the SrcAligned-based keystone there (its only
    substitution input is `SubstCompat` *at* `realign`), and transport back. -/
theorem CapyCaptureSet.compile_peaks_subst' {s1 s2 s1' s2' : Sig}
    {Γorig : CapyCtx s1} {Γsub : CapyCtx s1'}
    {scOrig : SrcCtx s1 s2} {scSub : SrcCtx s1' s2'}
    {σ : CapySubst s1 s1'} {σt : Subst s2 s2'} {cs : CapyCaptureSet s1}
    (hΓO : Γorig.IsClosed) (hΓS : Γsub.IsClosed)
    (hcompatAl : SubstCompat (SrcCtx.realign Γsub scSub) (SrcCtx.realign Γorig scOrig) σ σt)
    (hcs : cs.IsClosed) (hsub : (cs.subst σ).IsClosed) :
    CapyCaptureSet.compile (CapyCaptureSet.peaks Γsub (cs.subst σ)) scSub
      = (CapyCaptureSet.compile (CapyCaptureSet.peaks Γorig cs) scOrig).subst σt := by
  rw [CapyCaptureSet.compile_eq_of_lookupCVar (CapyCaptureSet.peaks_noBoundVar Γsub (cs.subst σ))
        (fun c => (SrcCtx.realign_lookupCVar Γsub scSub c).symm),
      CapyCaptureSet.compile_peaks_subst hΓO hΓS (SrcCtx.realign_aligned Γorig scOrig)
        (SrcCtx.realign_aligned Γsub scSub) hcompatAl hcs hsub,
      CapyCaptureSet.compile_eq_of_lookupCVar (CapyCaptureSet.peaks_noBoundVar Γorig cs)
        (fun c => SrcCtx.realign_lookupCVar Γorig scOrig c)]

/-- The `realign` surrogate-`SubstCompat` threads through a fresh *target* binder
    (`weakenTarget`): `realign` commutes with the `succ`-rename (`realign_rename`), so this
    reduces to the ordinary `SubstCompat.weakenTarget`. -/
theorem SubstCompat.realign_weakenTarget {s1 s2 s1' s2' : Sig}
    {Γsub : CapyCtx s1'} {Γorig : CapyCtx s1} {scSub : SrcCtx s1' s2'} {scOrig : SrcCtx s1 s2}
    {σ : CapySubst s1 s1'} {σt : Subst s2 s2'}
    (h : SubstCompat (SrcCtx.realign Γsub scSub) (SrcCtx.realign Γorig scOrig) σ σt) :
    SubstCompat (SrcCtx.realign Γsub (scSub.rename Rename.succ))
      (SrcCtx.realign Γorig (scOrig.rename Rename.succ)) σ (σt.lift (k := k)) := by
  rw [SrcCtx.realign_rename, SrcCtx.realign_rename]
  exact SubstCompat.weakenTarget h

/-- The `realign` surrogate-`SubstCompat` threads through the compiler's
    `weakenTarget.consCVar … .here` (recursing under a source capture binder): `realign` of the
    `push_cvar_default`/`.cons (.cvar .here)` shape unfolds (the cvar bound is irrelevant to
    `realign`) and `realign_rename` matches `SubstCompat.weakenConsCVar`. -/
theorem SubstCompat.realign_weakenConsCVar {s1 s2 s1' s2' : Sig}
    {Γsub : CapyCtx s1'} {Γorig : CapyCtx s1} {scSub : SrcCtx s1' s2'} {scOrig : SrcCtx s1 s2}
    {σ : CapySubst s1 s1'} {σt : Subst s2 s2'}
    {cbS : CapyCaptureBound s1'} {cbO : CapyCaptureBound s1}
    (h : SubstCompat (SrcCtx.realign Γsub scSub) (SrcCtx.realign Γorig scOrig) σ σt) :
    SubstCompat
      (SrcCtx.realign (Γsub.push_cvar_default cbS)
        (.cons (.cvar BVar.here) (scSub.rename Rename.succ)))
      (SrcCtx.realign (Γorig.push_cvar_default cbO)
        (.cons (.cvar BVar.here) (scOrig.rename Rename.succ)))
      σ.lift (σt.lift (k := Kind.cvar)) := by
  have e1 : SrcCtx.realign (Γsub.push_cvar_default cbS)
        (.cons (.cvar BVar.here) (scSub.rename Rename.succ))
      = .cons (.cvar BVar.here) (SrcCtx.realign Γsub (scSub.rename Rename.succ)) := rfl
  have e2 : SrcCtx.realign (Γorig.push_cvar_default cbO)
        (.cons (.cvar BVar.here) (scOrig.rename Rename.succ))
      = .cons (.cvar BVar.here) (SrcCtx.realign Γorig (scOrig.rename Rename.succ)) := rfl
  rw [e1, e2, SrcCtx.realign_rename, SrcCtx.realign_rename]
  exact SubstCompat.weakenConsCVar h

/-- The `realign` surrogate-`SubstCompat` threads through the compiler's
    `weakenTarget.consTVar … .here` (the `poly`-body builder). -/
theorem SubstCompat.realign_weakenConsTVar {s1 s2 s1' s2' : Sig}
    {Γsub : CapyCtx s1'} {Γorig : CapyCtx s1} {scSub : SrcCtx s1' s2'} {scOrig : SrcCtx s1 s2}
    {σ : CapySubst s1 s1'} {σt : Subst s2 s2'}
    {SS : CapyPureTy s1'} {SO : CapyPureTy s1}
    (h : SubstCompat (SrcCtx.realign Γsub scSub) (SrcCtx.realign Γorig scOrig) σ σt) :
    SubstCompat
      (SrcCtx.realign (Γsub.push_tvar SS)
        (.cons (.tvar BVar.here) (scSub.rename Rename.succ)))
      (SrcCtx.realign (Γorig.push_tvar SO)
        (.cons (.tvar BVar.here) (scOrig.rename Rename.succ)))
      σ.lift (σt.lift (k := Kind.tvar)) := by
  have e1 : SrcCtx.realign (Γsub.push_tvar SS)
        (.cons (.tvar BVar.here) (scSub.rename Rename.succ))
      = .cons (.tvar BVar.here) (SrcCtx.realign Γsub (scSub.rename Rename.succ)) := rfl
  have e2 : SrcCtx.realign (Γorig.push_tvar SO)
        (.cons (.tvar BVar.here) (scOrig.rename Rename.succ))
      = .cons (.tvar BVar.here) (SrcCtx.realign Γorig (scOrig.rename Rename.succ)) := rfl
  rw [e1, e2, SrcCtx.realign_rename, SrcCtx.realign_rename]
  exact SubstCompat.weakenConsTVar h

/-- The `realign` surrogate-`SubstCompat` threads through a source capture binder mapped to an
    arbitrary target cvar (`consCVar`).  `realign` keeps the cvar image, so it reduces to the
    plain `SubstCompat.consCVar`. -/
theorem SubstCompat.realign_consCVar {s1 s2 s1' s2' : Sig}
    {Γsub : CapyCtx s1'} {Γorig : CapyCtx s1} {scSub : SrcCtx s1' s2'} {scOrig : SrcCtx s1 s2}
    {σ : CapySubst s1 s1'} {σt : Subst s2 s2'}
    {cS : BVar s2' .cvar} {cO : BVar s2 .cvar}
    {cbS : CapyCaptureBound s1'} {cbO : CapyCaptureBound s1}
    (h : SubstCompat (SrcCtx.realign Γsub scSub) (SrcCtx.realign Γorig scOrig) σ σt)
    (hc : σt.cvar cO = CaptureSet.cvar (.M .epsilon) cS) :
    SubstCompat
      (SrcCtx.realign (Γsub.push_cvar_default cbS) (.cons (.cvar cS) scSub))
      (SrcCtx.realign (Γorig.push_cvar_default cbO) (.cons (.cvar cO) scOrig))
      σ.lift σt := by
  have e1 : SrcCtx.realign (Γsub.push_cvar_default cbS) (.cons (.cvar cS) scSub)
      = .cons (.cvar cS) (SrcCtx.realign Γsub scSub) := rfl
  have e2 : SrcCtx.realign (Γorig.push_cvar_default cbO) (.cons (.cvar cO) scOrig)
      = .cons (.cvar cO) (SrcCtx.realign Γorig scOrig) := rfl
  rw [e1, e2]
  exact SubstCompat.consCVar h hc

/-- The `realign` surrogate-`SubstCompat` threads through a source term binder (`consVar`).
    `realign` rewrites *both* var images to the declared latent `⟦T.captureSet⟧`, so the
    `consVar` invariant `csO.subst σt = csS` is exactly `compile_subst` on `To.captureSet`. -/
theorem SubstCompat.realign_consVar {s1 s2 s1' s2' : Sig}
    {Γsub : CapyCtx s1'} {Γorig : CapyCtx s1} {scSub : SrcCtx s1' s2'} {scOrig : SrcCtx s1 s2}
    {σ : CapySubst s1 s1'} {σt : Subst s2 s2'} {To : CapyTy .capt s1}
    {bvS : Option (BVar s2' .var)} {bvO : Option (BVar s2 .var)}
    {csS : CaptureSet s2'} {csO : CaptureSet s2}
    (h : SubstCompat (SrcCtx.realign Γsub scSub) (SrcCtx.realign Γorig scOrig) σ σt)
    (htv : ∀ X, ∃ Y, σ.tvar X = CapyPureTy.tvar Y) (hTo : To.IsClosed) :
    SubstCompat
      (SrcCtx.realign (Γsub.push_var (To.subst σ)) (.cons (.var bvS csS) scSub))
      (SrcCtx.realign (Γorig.push_var To) (.cons (.var bvO csO) scOrig))
      σ.lift σt := by
  have e1 : SrcCtx.realign (Γsub.push_var (To.subst σ)) (.cons (.var bvS csS) scSub)
      = .cons (.var bvS
          (CapyCaptureSet.compile (To.subst σ).captureSet (SrcCtx.realign Γsub scSub)))
          (SrcCtx.realign Γsub scSub) := rfl
  have e2 : SrcCtx.realign (Γorig.push_var To) (.cons (.var bvO csO) scOrig)
      = .cons (.var bvO (CapyCaptureSet.compile To.captureSet (SrcCtx.realign Γorig scOrig)))
          (SrcCtx.realign Γorig scOrig) := rfl
  rw [e1, e2]
  refine SubstCompat.consVar h ?_
  rw [show (To.subst σ).captureSet = (To.captureSet).subst σ from CapyTy.captureSet_subst htv]
  exact (CapyCaptureSet.compile_subst h (CapyTy.IsClosed.captureSet hTo)).symm

/-- `CVarInjective` survives `realign` — it only constrains `lookupCVar`, which `realign`
    preserves. -/
theorem SrcCtx.CVarInjective.realign {s1 s2 : Sig} {Γ : CapyCtx s1} {sc : SrcCtx s1 s2}
    (h : sc.CVarInjective) : (SrcCtx.realign Γ sc).CVarInjective := by
  intro c1 c2 he
  rw [SrcCtx.realign_lookupCVar, SrcCtx.realign_lookupCVar] at he
  exact h he

/-- An identity-mode image forces `hiso.toPeak` to land on the matching cvar peak — the
    only alternative, `.pseudo`, would give a `pseudo_peak` image, never a bare `cvar`
    atom. -/
theorem PeakSubstIso.toPeak_eq_cvar_of_image {s1 s2 : Sig} {σ : CapySubst s1 s2}
    (hiso : PeakSubstIso σ) {c : BVar s1 .cvar} {d : BVar s2 .cvar}
    (h : σ.cvar c = CapyCaptureSet.cvar (.M .epsilon) d) : hiso.toPeak c = Peak.cvar d := by
  have him := hiso.image c
  rw [h] at him
  cases htc : hiso.toPeak c with
  | cvar f =>
    rw [htc] at him
    simp only [Peak.asCaptureSet, CapyCaptureSet.cvar.injEq] at him
    rw [him.2]
  | pseudo D =>
    exfalso
    rw [htc] at him
    simp [Peak.asCaptureSet] at him

/-- A frozen image forces `hiso.toPeak` to land on some frozen peak — the only
    alternative, `.cvar`, would give a bare `cvar` atom image, never a `pseudo_peak`. -/
theorem PeakSubstIso.toPeak_eq_pseudo_of_image {s1 s2 : Sig} {σ : CapySubst s1 s2}
    (hiso : PeakSubstIso σ) {c : BVar s1 .cvar} {D : CapyCaptureSet s2}
    (h : σ.cvar c = CapyCaptureSet.pseudo_peak D) : ∃ D', hiso.toPeak c = Peak.pseudo D' := by
  have him := hiso.image c
  rw [h] at him
  cases htc : hiso.toPeak c with
  | cvar f =>
    exfalso
    rw [htc] at him
    simp [Peak.asCaptureSet] at him
  | pseudo D' => exact ⟨D', rfl⟩

/-- **Origin-stability from a traced target atom.**  When an origin cvar `d1'`
    (identified via `compile_cvar_subset_inv_resource` on a resolved target atom `Z`)
    is the source of the SAME atom a stable SUB cvar `d1` traces to (the
    `compile_peakSepCtx_sep_forward` "distinct origin" scenario), `d1'` is itself
    origin-stable.  Case on `hiso.toPeak d1'`: if frozen, `Peak.IsStable` is trivially
    `True` and `hstab` forces origin-stability directly (freezing only ever happens to
    origin-stable cvars); if a cvar `e`, the `SubstCompat` commuting square + injectivity
    on `scSub` identify `e = d1`, so `d1`'s (assumed) stability transports via `hstab`. -/
theorem origin_cvar_stable_of_target_atom {s1 s2 s1' s2' : Sig}
    {Γorig : CapyCtx s1} {Γsub : CapyCtx s1'} {σ : CapySubst s1 s1'}
    {scOrig : SrcCtx s1 s2} {scSub : SrcCtx s1' s2'} {σt : Subst s2 s2'}
    (hcompat : SubstCompat scSub scOrig σ σt) (hiso : PeakSubstIso σ)
    (hinj : scSub.CVarInjective) (hstab : hiso.StablePreserving Γorig Γsub)
    {d1 : BVar s1' .cvar} {d1' : BVar s1 .cvar} {Z : BVar s2 .cvar}
    {Y : BVar s2' .cvar} {a m : Access}
    (hd1lk : scOrig.lookupCVar d1' = Z) (hlk1 : scSub.lookupCVar d1 = Y)
    (happ1 : (CaptureSet.cvar a Y) ⊆ (σt.cvar Z).applyAccess m)
    (hd1stab : Γsub.IsStableCVar d1) :
    Γorig.IsStableCVar d1' := by
  refine (hstab d1').mpr ?_
  have hsq := hcompat.cvar d1'
  rw [hiso.image d1', hd1lk] at hsq
  cases htc : hiso.toPeak d1' with
  | pseudo D => exact trivial
  | cvar e =>
    rw [htc] at hsq
    simp only [Peak.asCaptureSet, CapyCaptureSet.compile] at hsq
    rw [← hsq] at happ1
    obtain ⟨a', hcv⟩ := CaptureSet.cvar_subset_applyAccess_inv happ1
    obtain ⟨-, hYe⟩ := CaptureSet.cvar_subset_cvar_inv hcv
    simp only [Peak.IsStable]
    rw [← hinj (hlk1.trans hYe)]
    exact hd1stab

/-- **Forward lock-`Satisfy` separation half (extracted, generic over the binder).**
    The separation dispatch of `cpoly`/`poly`/`arrow`'s `modal_modal` codomain in the
    FORWARD direction (`⟦T[σ]⟧ <: ⟦T⟧[σt]`): from `HasTwoDistinct` of two SUB peaks of
    `cs[σ]`, derive a `SepCheck` in the context whose pushed lock is the SUBSTITUTED ORIGIN
    lock `Ψ_R[σt]`.  Distinct sub-cvars trace (via `traceAtom`) to lock items separated by
    `sep_lock`; a `σ`-merge of two origin peaks is separated by `hdropW`; the cvar–frozen and
    frozen–frozen cases route through the reverse containments / `uniqueFrozen`.  Generic over
    the binder-extended target sigs `s2w/s2w'`, so it serves the `cvar` (cpoly), `tvar` (poly),
    and nested (arrow) binders uniformly. -/
theorem compile_peakSepCtx_sep_forward {s1 s2w s1' s2w' : Sig}
    {Γorig : CapyCtx s1} {Γsub : CapyCtx s1'}
    {scOrig : SrcCtx s1 s2w} {scSub : SrcCtx s1' s2w'}
    {σ : CapySubst s1 s1'} {σtW : Subst s2w s2w'}
    {cs : CapyCaptureSet s1} {coreCtxW : Ctx s2w'} {ΨmutR : MutabilityCtx s2w}
    (hΓO : Γorig.IsClosed) (hΓS : Γsub.IsClosed)
    (haOrigW : SrcAligned Γorig scOrig) (haSubW : SrcAligned Γsub scSub)
    (hcompatW : SubstCompat scSub scOrig σ σtW)
    (hcsCl : cs.IsClosed) (hsubcl : (cs.subst σ).IsClosed)
    (hΓOnp : Γorig.NoPseudoPeak) (hcsnp : cs.NoPseudoPeak)
    (hinjW : scSub.CVarInjective)
    (hiso : PeakSubstIso σ)
    (hscS : CapySubst.IsClosed σ)
    (htv' : ∀ X, ∃ Y, σ.tvar X = CapyPureTy.tvar Y)
    (hsubsto : Γorig.SubstsTo Γsub σ)
    (hdropW : TgtPairDroppableOn
      (fun Z => ∃ m, CaptureSet.cvar m Z ⊆
        CapyCaptureSet.compile (CapyCaptureSet.peaks Γorig cs) scOrig) coreCtxW σtW)
    (hstab : hiso.StablePreserving Γorig Γsub) :
    ∀ (C1 C2 : CaptureSet (s2w',,Kind.lock)),
      (peakSepCtx Γsub (CapyCaptureSet.peakset Γsub (cs.subst σ))
        (scSub.rename Rename.succ)).HasTwoDistinct C1 C2 →
      SepCheck
        (coreCtxW.push_lock
          (({ sep := peakSepCtx Γorig (CapyCaptureSet.peakset Γorig cs) scOrig,
              mutability := ΨmutR } : ModalCtx s2w).subst σtW))
        C1 C2 := by
  intro C1 C2 hdist
  obtain ⟨c1, hc1, c2, hc2, hcne, hCdisj⟩ := peakSepCtx_HasTwoDistinct_ne hdist
  -- E1: the whole compiled peak-set commutes with `σtW`.
  have hE1 :
      CapyCaptureSet.compile (CapyCaptureSet.peaks Γsub (cs.subst σ)) scSub
        = (CapyCaptureSet.compile (CapyCaptureSet.peaks Γorig cs) scOrig).subst σtW :=
    CapyCaptureSet.compile_peaks_subst hΓO hΓS haOrigW haSubW hcompatW hcsCl hsubcl
  -- Per-atom tracing: an atom of a compiled sub-peak-item factors back through `σtW` to an
  -- atom of the compiled orig peak-set, recording the target image.
  have traceAtom : ∀ (d : BVar s1' Kind.cvar)
      (Y : BVar (s2w',,Kind.lock) Kind.cvar) (a : Access),
      (CaptureSet.cvar a Y) ⊆ CapyCaptureSet.compile
        (peakItem (CapyCaptureSet.peakset Γsub (cs.subst σ)) d)
        (scSub.rename Rename.succ) →
      ∃ (Y' : BVar s2w' Kind.cvar) (Z : BVar s2w Kind.cvar) (m : Access),
        Y = BVar.there Y' ∧ scSub.lookupCVar d = Y' ∧
        (CaptureSet.cvar m Z) ⊆ CapyCaptureSet.compile
          (CapyCaptureSet.peaks Γorig cs) scOrig ∧
        (CaptureSet.cvar a Y') ⊆ (σtW.cvar Z).applyAccess m := by
    intro d Y a hsub
    rw [CapyCaptureSet.compile_rename] at hsub
    obtain ⟨Y', hYeq, hsub'⟩ := CaptureSet.cvar_subset_rename_succ hsub
    obtain ⟨e, hlke, hsube⟩ :=
      CapyCaptureSet.compile_cvar_subset_inv_resource peakItem_peaksOnly
        peakItem_noPseudoPeak hsub'
    obtain ⟨hed, hsubP⟩ := peakItem_atom hsube
    subst hed
    have hmono := CapyCaptureSet.compile_subset (sc := scSub) hsubP
    have hcompc : CapyCaptureSet.compile (CapyCaptureSet.cvar a e) scSub = CaptureSet.cvar a Y' :=
      congrArg (CaptureSet.cvar a) hlke
    have hpcs : (CapyCaptureSet.peakset Γsub (cs.subst σ)).cs
        = CapyCaptureSet.peaks Γsub (cs.subst σ) := rfl
    rw [hcompc, hpcs, hE1] at hmono
    obtain ⟨Z, m, hmZ, happ⟩ := CaptureSet.subst_cvar_subset_inv hmono
    exact ⟨Y', Z, m, hYeq, hlke, hmZ, happ⟩
  -- The key separation claim for two distinct STABLE CVAR sub-peaks.
  have keyCC : ∀ (d1 d2 : BVar s1' Kind.cvar), d1 ≠ d2 →
      Γsub.IsStableCVar d1 → Γsub.IsStableCVar d2 →
      d1 ∈ peakCvars (CapyCaptureSet.peakset Γsub (cs.subst σ)) →
      d2 ∈ peakCvars (CapyCaptureSet.peakset Γsub (cs.subst σ)) →
      SepCheck
        (coreCtxW.push_lock
          (({ sep := peakSepCtx Γorig (CapyCaptureSet.peakset Γorig cs) scOrig,
              mutability := ΨmutR } : ModalCtx s2w).subst σtW))
        (CapyCaptureSet.compile
          (peakItem (CapyCaptureSet.peakset Γsub (cs.subst σ)) d1)
          (scSub.rename Rename.succ))
        (CapyCaptureSet.compile
          (peakItem (CapyCaptureSet.peakset Γsub (cs.subst σ)) d2)
          (scSub.rename Rename.succ)) := by
    intro d1 d2 hne hd1stab hd2stab hd1 hd2
    refine SepCheck.of_cvar_atoms
      (CapyCaptureSet.compile_peaksOnly peakItem_peaksOnly peakItem_noPseudoPeak)
      (CapyCaptureSet.compile_peaksOnly peakItem_peaksOnly peakItem_noPseudoPeak) ?_
    intro a1 Y1 a2 Y2 hY1 hY2
    obtain ⟨Y1', Z1, m1, hY1eq, hlk1, hmZ1, happ1⟩ := traceAtom d1 Y1 a1 hY1
    obtain ⟨Y2', Z2, m2, hY2eq, hlk2, hmZ2, happ2⟩ := traceAtom d2 Y2 a2 hY2
    have hYne : Y1 ≠ Y2 := by
      subst hY1eq; subst hY2eq
      intro he
      exact hne (hinjW (by rw [hlk1, hlk2]; exact BVar.there.inj he))
    by_cases hZ : Z1 = Z2
    · -- SPLIT: both atoms come from the same `σtW`-image `Z`; `hdropW` separates.
      subst hZ
      obtain ⟨a1', hmem1⟩ := CaptureSet.cvar_subset_applyAccess_inv happ1
      obtain ⟨a2', hmem2⟩ := CaptureSet.cvar_subset_applyAccess_inv happ2
      have hY'ne : Y1' ≠ Y2' := by
        intro he; exact hYne (by rw [hY1eq, hY2eq, he])
      have hdd := hdropW Z1 ⟨m1, hmZ1⟩ a1' a2' Y1' Y2' hY'ne
        (CaptureSet.cvar_subset_peaks hmem1) (CaptureSet.cvar_subset_peaks hmem2)
      subst hY1eq; subst hY2eq
      exact SepCheck.sep_droppable (Ctx.TwoDistinctDroppable.push hdd (Binding.lock
        (({ sep := peakSepCtx Γorig (CapyCaptureSet.peakset Γorig cs) scOrig,
            mutability := ΨmutR } : ModalCtx s2w).subst σtW)))
    · -- DISTINCT ORIGIN: trace to distinct lock items separated by the pushed `Ψ_R[σtW]`.
      obtain ⟨d1', hd1lk, hd1mem⟩ := CapyCaptureSet.compile_cvar_subset_inv_resource
        (CapyCaptureSet.peaks_peaksOnly Γorig cs)
        (CapyCaptureSet.peaks_noPseudoPeak hΓOnp hcsnp) hmZ1
      obtain ⟨d2', hd2lk, hd2mem⟩ := CapyCaptureSet.compile_cvar_subset_inv_resource
        (CapyCaptureSet.peaks_peaksOnly Γorig cs)
        (CapyCaptureSet.peaks_noPseudoPeak hΓOnp hcsnp) hmZ2
      have hd1pc : d1' ∈ peakCvars (CapyCaptureSet.peakset Γorig cs) := cvar_mem_peakCvars hd1mem
      have hd2pc : d2' ∈ peakCvars (CapyCaptureSet.peakset Γorig cs) := cvar_mem_peakCvars hd2mem
      have hd12ne : d1' ≠ d2' := fun he => hZ (by rw [← hd1lk, ← hd2lk, he])
      have hd1'stab : Γorig.IsStableCVar d1' :=
        origin_cvar_stable_of_target_atom hcompatW hiso hinjW hstab hd1lk hlk1 happ1 hd1stab
      have hd2'stab : Γorig.IsStableCVar d2' :=
        origin_cvar_stable_of_target_atom hcompatW hiso hinjW hstab hd2lk hlk2 happ2 hd2stab
      have htd := (peakSepCtx_subst_HasTwoDistinct_of
        (sc := scOrig) (σt := σtW)
        (List.mem_filter.mpr ⟨cvar_mem_peakList hd1pc, decide_eq_true_iff.mpr hd1'stab⟩)
        (List.mem_filter.mpr ⟨cvar_mem_peakList hd2pc, decide_eq_true_iff.mpr hd2'stab⟩)
        (fun h => hd12ne (Peak.cvar.inj h))).rename
        (f := Rename.succ (k := Kind.lock))
      have mkSub : ∀ (a : Access) (Y' : BVar s2w' Kind.cvar)
          (Z : BVar s2w Kind.cvar) (m : Access) (d' : BVar _ Kind.cvar),
          (CaptureSet.cvar a Y') ⊆ (σtW.cvar Z).applyAccess m →
          (CapyCaptureSet.cvar m d') ⊆ CapyCaptureSet.peaks Γorig cs →
          scOrig.lookupCVar d' = Z →
          Subcapt coreCtxW
            (CaptureSet.cvar a Y')
            ((CapyCaptureSet.compile
              (peakItem (CapyCaptureSet.peakset Γorig cs) d') scOrig).subst σtW) := by
        intro a Y' Z m d' happ hmem hdlk
        refine Subcapt.sc_trans (Subcapt.sc_elem happ) (Subcapt.sc_elem ?_)
        have h1 : (CapyCaptureSet.cvar m d') ⊆ peakItem (CapyCaptureSet.peakset Γorig cs) d' :=
          cvar_subset_peakItem hmem
        have h2 := CapyCaptureSet.compile_subset (sc := scOrig) h1
        have h3 := CaptureSet.Subset.subst (σ := σtW) h2
        have heqc : CapyCaptureSet.compile (CapyCaptureSet.cvar m d') scOrig
            = CaptureSet.cvar m Z :=
          congrArg (CaptureSet.cvar m) hdlk
        rw [heqc] at h3
        exact h3
      subst hY1eq; subst hY2eq
      exact SepCheck.sep_symm
        (SepCheck.sep_mono
          (SepCheck.sep_symm
            (SepCheck.sep_mono
              (SepCheck.sep_lock (ℓ := BVar.here) Ctx.LookupLock.here htd)
              (Subcapt.weaken (mkSub a1 Y1' Z1 m1 d1' happ1 hd1mem hd1lk) _)))
          (Subcapt.weaken (mkSub a2 Y2' Z2 m2 d2' happ2 hd2mem hd2lk) _))
  -- the CVAR–FROZEN key: distinct origin cvar peaks separate; shrink via reverse containments.
  have keyCP : ∀ (d1 : BVar s1' Kind.cvar) (D2 : CapyCaptureSet s1'),
      Γsub.IsStableCVar d1 →
      d1 ∈ peakCvars (CapyCaptureSet.peakset Γsub (cs.subst σ)) →
      D2 ∈ peakPseudos (CapyCaptureSet.peakset Γsub (cs.subst σ)) →
      SepCheck
        (coreCtxW.push_lock
          (({ sep := peakSepCtx Γorig (CapyCaptureSet.peakset Γorig cs) scOrig,
              mutability := ΨmutR } : ModalCtx s2w).subst σtW))
        (CapyCaptureSet.compile
          (peakItem (CapyCaptureSet.peakset Γsub (cs.subst σ)) d1)
          (scSub.rename Rename.succ))
        (CapyCaptureSet.compile
          (pseudoItem (CapyCaptureSet.peakset Γsub (cs.subst σ)) D2)
          (scSub.rename Rename.succ)) := by
    intro d1 D2 hd1stab hd1m hD2m
    obtain ⟨c01, hc01, hc01pc⟩ := sub_cvar_peak_origin hiso hsubsto htv' hd1m
    obtain ⟨c02, D02, hc02, hD2eq, hc02pc⟩ :=
      sub_pseudo_peak_origin hiso hsubsto hΓOnp hcsnp hD2m
    have hne01 : c01 ≠ c02 := by
      intro he; rw [he, hc02] at hc01; simp at hc01
    have hc01stab : Γorig.IsStableCVar c01 :=
      (hstab c01).mpr (by rw [hiso.toPeak_eq_cvar_of_image hc01]; exact hd1stab)
    have hc02stab : Γorig.IsStableCVar c02 := by
      obtain ⟨D02', hc02eq⟩ := hiso.toPeak_eq_pseudo_of_image hc02
      exact (hstab c02).mpr (by rw [hc02eq]; trivial)
    have htd := (peakSepCtx_subst_HasTwoDistinct_of
      (sc := scOrig) (σt := σtW)
      (List.mem_filter.mpr ⟨cvar_mem_peakList hc01pc, decide_eq_true_iff.mpr hc01stab⟩)
      (List.mem_filter.mpr ⟨cvar_mem_peakList hc02pc, decide_eq_true_iff.mpr hc02stab⟩)
      (fun h => hne01 (Peak.cvar.inj h))).rename
      (f := Rename.succ (k := Kind.lock))
    refine SepCheck.sep_symm (SepCheck.sep_mono (SepCheck.sep_symm (SepCheck.sep_mono
      (SepCheck.sep_lock (ℓ := BVar.here) Ctx.LookupLock.here htd) ?_)) ?_)
    · apply Subcapt.sc_elem
      rw [CapyCaptureSet.compile_rename]
      exact CaptureSet.Subset.rename (f := Rename.succ)
        (peakItem_subst_supset hcompatW hiso htv' hsubsto hc01)
    · apply Subcapt.sc_elem
      rw [hD2eq, CapyCaptureSet.compile_rename]
      exact CaptureSet.Subset.rename (f := Rename.succ)
        (pseudoItem_subst_supset hΓS haSubW hcompatW hcsnp hsubsto hΓOnp hiso hscS hc02)
  -- Peak-level dispatch: cvar–cvar via `keyCC`; mixed via `keyCP` (+ `sep_symm`);
  -- pseudo–pseudo is vacuous (`uniqueFrozen`).
  have key' : ∀ (p1 p2 : Peak s1'), p1 ≠ p2 →
      p1 ∈ (peakList (CapyCaptureSet.peakset Γsub (cs.subst σ))).filter
        (fun p => decide (Peak.IsStable Γsub p)) →
      p2 ∈ (peakList (CapyCaptureSet.peakset Γsub (cs.subst σ))).filter
        (fun p => decide (Peak.IsStable Γsub p)) →
      SepCheck
        (coreCtxW.push_lock
          (({ sep := peakSepCtx Γorig (CapyCaptureSet.peakset Γorig cs) scOrig,
              mutability := ΨmutR } : ModalCtx s2w).subst σtW))
        (CapyCaptureSet.compile
          (peakKeyItem (CapyCaptureSet.peakset Γsub (cs.subst σ)) p1)
          (scSub.rename Rename.succ))
        (CapyCaptureSet.compile
          (peakKeyItem (CapyCaptureSet.peakset Γsub (cs.subst σ)) p2)
          (scSub.rename Rename.succ)) := by
    intro p1 p2 hne hp1f hp2f
    obtain ⟨hp1, hp1s⟩ := List.mem_filter.mp hp1f
    obtain ⟨hp2, hp2s⟩ := List.mem_filter.mp hp2f
    cases p1 with
    | cvar d1 =>
      cases p2 with
      | cvar d2 =>
        have h1 := mem_peakCvars_of_cvar_mem hp1
        have h2 := mem_peakCvars_of_cvar_mem hp2
        exact keyCC d1 d2 (fun h => hne (congrArg Peak.cvar h))
          (decide_eq_true_iff.mp hp1s) (decide_eq_true_iff.mp hp2s) h1 h2
      | pseudo D2 =>
        exact keyCP d1 D2 (decide_eq_true_iff.mp hp1s) (mem_peakCvars_of_cvar_mem hp1)
          (mem_peakPseudos_of_pseudo_mem hp2)
    | pseudo D1 =>
      cases p2 with
      | cvar d2 =>
        exact SepCheck.sep_symm (keyCP d2 D1 (decide_eq_true_iff.mp hp2s)
          (mem_peakCvars_of_cvar_mem hp2) (mem_peakPseudos_of_pseudo_mem hp1))
      | pseudo D2 =>
        -- VACUOUS: distinct frozen SUB peaks trace to frozen ORIGIN sources forced equal.
        exfalso
        obtain ⟨C1', hC1, hC1m⟩ := peakPseudos_occ (mem_peakPseudos_of_pseudo_mem hp1)
        obtain ⟨C2', hC2, hC2m⟩ := peakPseudos_occ (mem_peakPseudos_of_pseudo_mem hp2)
        obtain ⟨c01, D01, m1, hc01, hC1eq⟩ :=
          pseudo_sub_peak_frozen_source hiso hsubsto hΓOnp hcsnp hC1
        obtain ⟨c02, D02, m2, hc02, hC2eq⟩ :=
          pseudo_sub_peak_frozen_source hiso hsubsto hΓOnp hcsnp hC2
        have ht1 : hiso.toPeak c01 = Peak.pseudo D01 := by
          have him := hiso.image c01; rw [hc01] at him
          cases htc : hiso.toPeak c01 with
          | cvar e => rw [htc] at him; simp [Peak.asCaptureSet] at him
          | pseudo D'' =>
            rw [htc] at him
            simp only [Peak.asCaptureSet, CapyCaptureSet.pseudo_peak.injEq] at him
            rw [him]
        have ht2 : hiso.toPeak c02 = Peak.pseudo D02 := by
          have him := hiso.image c02; rw [hc02] at him
          cases htc : hiso.toPeak c02 with
          | cvar e => rw [htc] at him; simp [Peak.asCaptureSet] at him
          | pseudo D'' =>
            rw [htc] at him
            simp only [Peak.asCaptureSet, CapyCaptureSet.pseudo_peak.injEq] at him
            rw [him]
        have hc12 : c01 = c02 := hiso.uniqueFrozen ht1 ht2
        subst hc12
        have hD : D01 = D02 := by
          rw [hc01] at hc02; exact CapyCaptureSet.pseudo_peak.inj hc02
        apply hne
        have e1 : D1 = (CapyCaptureSet.peaks Γsub D01).modeErase := by
          rw [← hC1m, hC1eq, CapyCaptureSet.modeErase_applyAccess]
        have e2 : D2 = (CapyCaptureSet.peaks Γsub D02).modeErase := by
          rw [← hC2m, hC2eq, CapyCaptureSet.modeErase_applyAccess]
        rw [e1, e2, hD]
  -- Discharge the goal (either ordering of the `HasTwoDistinct` pair).
  rcases hCdisj with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact key' c1 c2 hcne hc1 hc2
  · exact key' c2 c1 (Ne.symm hcne) hc2 hc1

/-- **Forward dispatch without the `SrcAligned` premise** (the `realign` surrogate route).  Run
    the SrcAligned-based forward dispatch at the always-aligned `realign Γ sc`, then transport the
    compiled locks back to the real `sc` (peaks are bound-var-free, so the lock is
    `lookupCVar`-insensitive).  `CVarInjective` carries over by `.realign`. -/
theorem compile_peakSepCtx_sep_forward_realign {s1 s2w s1' s2w' : Sig}
    {Γorig : CapyCtx s1} {Γsub : CapyCtx s1'}
    {scOrig : SrcCtx s1 s2w} {scSub : SrcCtx s1' s2w'}
    {σ : CapySubst s1 s1'} {σtW : Subst s2w s2w'}
    {cs : CapyCaptureSet s1} {coreCtxW : Ctx s2w'} {ΨmutR : MutabilityCtx s2w}
    (hΓO : Γorig.IsClosed) (hΓS : Γsub.IsClosed)
    (hcompatAlW : SubstCompat (SrcCtx.realign Γsub scSub) (SrcCtx.realign Γorig scOrig) σ σtW)
    (hcsCl : cs.IsClosed) (hsubcl : (cs.subst σ).IsClosed)
    (hΓOnp : Γorig.NoPseudoPeak) (hcsnp : cs.NoPseudoPeak)
    (hinjW : scSub.CVarInjective)
    (hiso : PeakSubstIso σ)
    (hscS : CapySubst.IsClosed σ)
    (htv' : ∀ X, ∃ Y, σ.tvar X = CapyPureTy.tvar Y)
    (hsubsto : Γorig.SubstsTo Γsub σ)
    (hdropW : TgtPairDroppableOn
      (fun Z => ∃ m, CaptureSet.cvar m Z ⊆
        CapyCaptureSet.compile (CapyCaptureSet.peaks Γorig cs) scOrig) coreCtxW σtW)
    (hstab : hiso.StablePreserving Γorig Γsub) :
    ∀ (C1 C2 : CaptureSet (s2w',,Kind.lock)),
      (peakSepCtx Γsub (CapyCaptureSet.peakset Γsub (cs.subst σ))
        (scSub.rename Rename.succ)).HasTwoDistinct C1 C2 →
      SepCheck
        (coreCtxW.push_lock
          (({ sep := peakSepCtx Γorig (CapyCaptureSet.peakset Γorig cs) scOrig,
              mutability := ΨmutR } : ModalCtx s2w).subst σtW))
        C1 C2 := by
  have hInEq : peakSepCtx Γsub (CapyCaptureSet.peakset Γsub (cs.subst σ))
        ((SrcCtx.realign Γsub scSub).rename (Rename.succ (k := Kind.lock)))
      = peakSepCtx Γsub (CapyCaptureSet.peakset Γsub (cs.subst σ))
        (scSub.rename (Rename.succ (k := Kind.lock))) :=
    peakSepCtx_eq_of_lookupCVar (CapyCaptureSet.peaks_noBoundVar Γsub (cs.subst σ)) (fun c => by
      rw [SrcCtx.lookupCVar_rename, SrcCtx.lookupCVar_rename, SrcCtx.realign_lookupCVar])
  have hOutEq : peakSepCtx Γorig (CapyCaptureSet.peakset Γorig cs) (SrcCtx.realign Γorig scOrig)
      = peakSepCtx Γorig (CapyCaptureSet.peakset Γorig cs) scOrig :=
    peakSepCtx_eq_of_lookupCVar (CapyCaptureSet.peaks_noBoundVar Γorig cs)
      (fun c => SrcCtx.realign_lookupCVar Γorig scOrig c)
  have hbridge : CapyCaptureSet.compile (CapyCaptureSet.peaks Γorig cs)
        (SrcCtx.realign Γorig scOrig)
      = CapyCaptureSet.compile (CapyCaptureSet.peaks Γorig cs) scOrig :=
    CapyCaptureSet.compile_eq_of_lookupCVar (CapyCaptureSet.peaks_noBoundVar Γorig cs)
      (fun c => SrcCtx.realign_lookupCVar Γorig scOrig c)
  intro C1 C2 hdist
  rw [← hInEq] at hdist
  rw [← hOutEq]
  exact compile_peakSepCtx_sep_forward (scOrig := SrcCtx.realign Γorig scOrig)
    (scSub := SrcCtx.realign Γsub scSub) hΓO hΓS
    (SrcCtx.realign_aligned Γorig scOrig) (SrcCtx.realign_aligned Γsub scSub) hcompatAlW
    hcsCl hsubcl hΓOnp hcsnp hinjW.realign hiso hscS htv' hsubsto
    (hdropW.mono (fun Z hZ => hbridge ▸ hZ)) hstab
    C1 C2 hdist

/-- **Split-covering forward dispatch** (UPSTREAM copy of `compile_peakSepCtx_sep_forward`
    with EXACTLY ONE change: the same-origin SPLIT case is discharged by a COVERING
    (`SepCheck`) premise `hsplitW : TgtSplitCoveredOn …` instead of the droppability
    `hdropW : TgtPairDroppableOn …`.  `hsplitW` separates the two distinct target cvars
    directly (mode-polymorphically, the covering analog of `sep_droppable`'s own access-mode
    polymorphism), then `renamesTo`/`SepCheck.weaken` weakens along the pushed origin lock.
    ALL other cases — in particular the distinct-origin cvar peaks read via `sep_lock` —
    are VERBATIM identical to `compile_peakSepCtx_sep_forward`. -/
theorem compile_peakSepCtx_sep_forward_splitcov {s1 s2w s1' s2w' : Sig}
    {Γorig : CapyCtx s1} {Γsub : CapyCtx s1'}
    {scOrig : SrcCtx s1 s2w} {scSub : SrcCtx s1' s2w'}
    {σ : CapySubst s1 s1'} {σtW : Subst s2w s2w'}
    {cs : CapyCaptureSet s1} {coreCtxW : Ctx s2w'} {ΨmutR : MutabilityCtx s2w}
    (hΓO : Γorig.IsClosed) (hΓS : Γsub.IsClosed)
    (haOrigW : SrcAligned Γorig scOrig) (haSubW : SrcAligned Γsub scSub)
    (hcompatW : SubstCompat scSub scOrig σ σtW)
    (hcsCl : cs.IsClosed) (hsubcl : (cs.subst σ).IsClosed)
    (hΓOnp : Γorig.NoPseudoPeak) (hcsnp : cs.NoPseudoPeak)
    (hinjW : scSub.CVarInjective)
    (hiso : PeakSubstIso σ)
    (hscS : CapySubst.IsClosed σ)
    (htv' : ∀ X, ∃ Y, σ.tvar X = CapyPureTy.tvar Y)
    (hsubsto : Γorig.SubstsTo Γsub σ)
    (hsplitW : TgtSplitCoveredOn
      (fun Z => ∃ m, CaptureSet.cvar m Z ⊆
        CapyCaptureSet.compile (CapyCaptureSet.peaks Γorig cs) scOrig) coreCtxW σtW)
    (hstab : hiso.StablePreserving Γorig Γsub) :
    ∀ (C1 C2 : CaptureSet (s2w',,Kind.lock)),
      (peakSepCtx Γsub (CapyCaptureSet.peakset Γsub (cs.subst σ))
        (scSub.rename Rename.succ)).HasTwoDistinct C1 C2 →
      SepCheck
        (coreCtxW.push_lock
          (({ sep := peakSepCtx Γorig (CapyCaptureSet.peakset Γorig cs) scOrig,
              mutability := ΨmutR } : ModalCtx s2w).subst σtW))
        C1 C2 := by
  intro C1 C2 hdist
  obtain ⟨c1, hc1, c2, hc2, hcne, hCdisj⟩ := peakSepCtx_HasTwoDistinct_ne hdist
  -- E1: the whole compiled peak-set commutes with `σtW`.
  have hE1 :
      CapyCaptureSet.compile (CapyCaptureSet.peaks Γsub (cs.subst σ)) scSub
        = (CapyCaptureSet.compile (CapyCaptureSet.peaks Γorig cs) scOrig).subst σtW :=
    CapyCaptureSet.compile_peaks_subst hΓO hΓS haOrigW haSubW hcompatW hcsCl hsubcl
  -- Per-atom tracing: an atom of a compiled sub-peak-item factors back through `σtW` to an
  -- atom of the compiled orig peak-set, recording the target image.
  have traceAtom : ∀ (d : BVar s1' Kind.cvar)
      (Y : BVar (s2w',,Kind.lock) Kind.cvar) (a : Access),
      (CaptureSet.cvar a Y) ⊆ CapyCaptureSet.compile
        (peakItem (CapyCaptureSet.peakset Γsub (cs.subst σ)) d)
        (scSub.rename Rename.succ) →
      ∃ (Y' : BVar s2w' Kind.cvar) (Z : BVar s2w Kind.cvar) (m : Access),
        Y = BVar.there Y' ∧ scSub.lookupCVar d = Y' ∧
        (CaptureSet.cvar m Z) ⊆ CapyCaptureSet.compile
          (CapyCaptureSet.peaks Γorig cs) scOrig ∧
        (CaptureSet.cvar a Y') ⊆ (σtW.cvar Z).applyAccess m := by
    intro d Y a hsub
    rw [CapyCaptureSet.compile_rename] at hsub
    obtain ⟨Y', hYeq, hsub'⟩ := CaptureSet.cvar_subset_rename_succ hsub
    obtain ⟨e, hlke, hsube⟩ :=
      CapyCaptureSet.compile_cvar_subset_inv_resource peakItem_peaksOnly
        peakItem_noPseudoPeak hsub'
    obtain ⟨hed, hsubP⟩ := peakItem_atom hsube
    subst hed
    have hmono := CapyCaptureSet.compile_subset (sc := scSub) hsubP
    have hcompc : CapyCaptureSet.compile (CapyCaptureSet.cvar a e) scSub = CaptureSet.cvar a Y' :=
      congrArg (CaptureSet.cvar a) hlke
    have hpcs : (CapyCaptureSet.peakset Γsub (cs.subst σ)).cs
        = CapyCaptureSet.peaks Γsub (cs.subst σ) := rfl
    rw [hcompc, hpcs, hE1] at hmono
    obtain ⟨Z, m, hmZ, happ⟩ := CaptureSet.subst_cvar_subset_inv hmono
    exact ⟨Y', Z, m, hYeq, hlke, hmZ, happ⟩
  -- The key separation claim for two distinct STABLE CVAR sub-peaks.
  have keyCC : ∀ (d1 d2 : BVar s1' Kind.cvar), d1 ≠ d2 →
      Γsub.IsStableCVar d1 → Γsub.IsStableCVar d2 →
      d1 ∈ peakCvars (CapyCaptureSet.peakset Γsub (cs.subst σ)) →
      d2 ∈ peakCvars (CapyCaptureSet.peakset Γsub (cs.subst σ)) →
      SepCheck
        (coreCtxW.push_lock
          (({ sep := peakSepCtx Γorig (CapyCaptureSet.peakset Γorig cs) scOrig,
              mutability := ΨmutR } : ModalCtx s2w).subst σtW))
        (CapyCaptureSet.compile
          (peakItem (CapyCaptureSet.peakset Γsub (cs.subst σ)) d1)
          (scSub.rename Rename.succ))
        (CapyCaptureSet.compile
          (peakItem (CapyCaptureSet.peakset Γsub (cs.subst σ)) d2)
          (scSub.rename Rename.succ)) := by
    intro d1 d2 hne hd1stab hd2stab hd1 hd2
    refine SepCheck.of_cvar_atoms
      (CapyCaptureSet.compile_peaksOnly peakItem_peaksOnly peakItem_noPseudoPeak)
      (CapyCaptureSet.compile_peaksOnly peakItem_peaksOnly peakItem_noPseudoPeak) ?_
    intro a1 Y1 a2 Y2 hY1 hY2
    obtain ⟨Y1', Z1, m1, hY1eq, hlk1, hmZ1, happ1⟩ := traceAtom d1 Y1 a1 hY1
    obtain ⟨Y2', Z2, m2, hY2eq, hlk2, hmZ2, happ2⟩ := traceAtom d2 Y2 a2 hY2
    have hYne : Y1 ≠ Y2 := by
      subst hY1eq; subst hY2eq
      intro he
      exact hne (hinjW (by rw [hlk1, hlk2]; exact BVar.there.inj he))
    by_cases hZ : Z1 = Z2
    · -- SPLIT: both atoms come from the same `σtW`-image `Z`.  The COVERING premise
      -- `hsplitW` separates the two distinct target cvars directly, re-moded to the
      -- goal's accesses `a1`/`a2` (mirroring `sep_droppable`'s own mode-polymorphism),
      -- then weakened along the pushed origin lock.  (Distinct-origin case unchanged.)
      subst hZ
      obtain ⟨a1', hmem1⟩ := CaptureSet.cvar_subset_applyAccess_inv happ1
      obtain ⟨a2', hmem2⟩ := CaptureSet.cvar_subset_applyAccess_inv happ2
      have hY'ne : Y1' ≠ Y2' := by
        intro he; exact hYne (by rw [hY1eq, hY2eq, he])
      have hsep := hsplitW Z1 ⟨m1, hmZ1⟩ a1' a2' Y1' Y2' hY'ne
        (CaptureSet.cvar_subset_peaks hmem1) (CaptureSet.cvar_subset_peaks hmem2) a1 a2
      subst hY1eq; subst hY2eq
      exact hsep.renamesTo (Ctx.RenamesTo.weaken (Binding.lock
        (({ sep := peakSepCtx Γorig (CapyCaptureSet.peakset Γorig cs) scOrig,
            mutability := ΨmutR } : ModalCtx s2w).subst σtW))) Rename.injective_succ
    · -- DISTINCT ORIGIN: trace to distinct lock items separated by the pushed `Ψ_R[σtW]`.
      obtain ⟨d1', hd1lk, hd1mem⟩ := CapyCaptureSet.compile_cvar_subset_inv_resource
        (CapyCaptureSet.peaks_peaksOnly Γorig cs)
        (CapyCaptureSet.peaks_noPseudoPeak hΓOnp hcsnp) hmZ1
      obtain ⟨d2', hd2lk, hd2mem⟩ := CapyCaptureSet.compile_cvar_subset_inv_resource
        (CapyCaptureSet.peaks_peaksOnly Γorig cs)
        (CapyCaptureSet.peaks_noPseudoPeak hΓOnp hcsnp) hmZ2
      have hd1pc : d1' ∈ peakCvars (CapyCaptureSet.peakset Γorig cs) := cvar_mem_peakCvars hd1mem
      have hd2pc : d2' ∈ peakCvars (CapyCaptureSet.peakset Γorig cs) := cvar_mem_peakCvars hd2mem
      have hd12ne : d1' ≠ d2' := fun he => hZ (by rw [← hd1lk, ← hd2lk, he])
      have hd1'stab : Γorig.IsStableCVar d1' :=
        origin_cvar_stable_of_target_atom hcompatW hiso hinjW hstab hd1lk hlk1 happ1 hd1stab
      have hd2'stab : Γorig.IsStableCVar d2' :=
        origin_cvar_stable_of_target_atom hcompatW hiso hinjW hstab hd2lk hlk2 happ2 hd2stab
      have htd := (peakSepCtx_subst_HasTwoDistinct_of
        (sc := scOrig) (σt := σtW)
        (List.mem_filter.mpr ⟨cvar_mem_peakList hd1pc, decide_eq_true_iff.mpr hd1'stab⟩)
        (List.mem_filter.mpr ⟨cvar_mem_peakList hd2pc, decide_eq_true_iff.mpr hd2'stab⟩)
        (fun h => hd12ne (Peak.cvar.inj h))).rename
        (f := Rename.succ (k := Kind.lock))
      have mkSub : ∀ (a : Access) (Y' : BVar s2w' Kind.cvar)
          (Z : BVar s2w Kind.cvar) (m : Access) (d' : BVar _ Kind.cvar),
          (CaptureSet.cvar a Y') ⊆ (σtW.cvar Z).applyAccess m →
          (CapyCaptureSet.cvar m d') ⊆ CapyCaptureSet.peaks Γorig cs →
          scOrig.lookupCVar d' = Z →
          Subcapt coreCtxW
            (CaptureSet.cvar a Y')
            ((CapyCaptureSet.compile
              (peakItem (CapyCaptureSet.peakset Γorig cs) d') scOrig).subst σtW) := by
        intro a Y' Z m d' happ hmem hdlk
        refine Subcapt.sc_trans (Subcapt.sc_elem happ) (Subcapt.sc_elem ?_)
        have h1 : (CapyCaptureSet.cvar m d') ⊆ peakItem (CapyCaptureSet.peakset Γorig cs) d' :=
          cvar_subset_peakItem hmem
        have h2 := CapyCaptureSet.compile_subset (sc := scOrig) h1
        have h3 := CaptureSet.Subset.subst (σ := σtW) h2
        have heqc : CapyCaptureSet.compile (CapyCaptureSet.cvar m d') scOrig
            = CaptureSet.cvar m Z :=
          congrArg (CaptureSet.cvar m) hdlk
        rw [heqc] at h3
        exact h3
      subst hY1eq; subst hY2eq
      exact SepCheck.sep_symm
        (SepCheck.sep_mono
          (SepCheck.sep_symm
            (SepCheck.sep_mono
              (SepCheck.sep_lock (ℓ := BVar.here) Ctx.LookupLock.here htd)
              (Subcapt.weaken (mkSub a1 Y1' Z1 m1 d1' happ1 hd1mem hd1lk) _)))
          (Subcapt.weaken (mkSub a2 Y2' Z2 m2 d2' happ2 hd2mem hd2lk) _))
  -- the CVAR–FROZEN key: distinct origin cvar peaks separate; shrink via reverse containments.
  have keyCP : ∀ (d1 : BVar s1' Kind.cvar) (D2 : CapyCaptureSet s1'),
      Γsub.IsStableCVar d1 →
      d1 ∈ peakCvars (CapyCaptureSet.peakset Γsub (cs.subst σ)) →
      D2 ∈ peakPseudos (CapyCaptureSet.peakset Γsub (cs.subst σ)) →
      SepCheck
        (coreCtxW.push_lock
          (({ sep := peakSepCtx Γorig (CapyCaptureSet.peakset Γorig cs) scOrig,
              mutability := ΨmutR } : ModalCtx s2w).subst σtW))
        (CapyCaptureSet.compile
          (peakItem (CapyCaptureSet.peakset Γsub (cs.subst σ)) d1)
          (scSub.rename Rename.succ))
        (CapyCaptureSet.compile
          (pseudoItem (CapyCaptureSet.peakset Γsub (cs.subst σ)) D2)
          (scSub.rename Rename.succ)) := by
    intro d1 D2 hd1stab hd1m hD2m
    obtain ⟨c01, hc01, hc01pc⟩ := sub_cvar_peak_origin hiso hsubsto htv' hd1m
    obtain ⟨c02, D02, hc02, hD2eq, hc02pc⟩ :=
      sub_pseudo_peak_origin hiso hsubsto hΓOnp hcsnp hD2m
    have hne01 : c01 ≠ c02 := by
      intro he; rw [he, hc02] at hc01; simp at hc01
    have hc01stab : Γorig.IsStableCVar c01 :=
      (hstab c01).mpr (by rw [hiso.toPeak_eq_cvar_of_image hc01]; exact hd1stab)
    have hc02stab : Γorig.IsStableCVar c02 := by
      obtain ⟨D02', hc02eq⟩ := hiso.toPeak_eq_pseudo_of_image hc02
      exact (hstab c02).mpr (by rw [hc02eq]; trivial)
    have htd := (peakSepCtx_subst_HasTwoDistinct_of
      (sc := scOrig) (σt := σtW)
      (List.mem_filter.mpr ⟨cvar_mem_peakList hc01pc, decide_eq_true_iff.mpr hc01stab⟩)
      (List.mem_filter.mpr ⟨cvar_mem_peakList hc02pc, decide_eq_true_iff.mpr hc02stab⟩)
      (fun h => hne01 (Peak.cvar.inj h))).rename
      (f := Rename.succ (k := Kind.lock))
    refine SepCheck.sep_symm (SepCheck.sep_mono (SepCheck.sep_symm (SepCheck.sep_mono
      (SepCheck.sep_lock (ℓ := BVar.here) Ctx.LookupLock.here htd) ?_)) ?_)
    · apply Subcapt.sc_elem
      rw [CapyCaptureSet.compile_rename]
      exact CaptureSet.Subset.rename (f := Rename.succ)
        (peakItem_subst_supset hcompatW hiso htv' hsubsto hc01)
    · apply Subcapt.sc_elem
      rw [hD2eq, CapyCaptureSet.compile_rename]
      exact CaptureSet.Subset.rename (f := Rename.succ)
        (pseudoItem_subst_supset hΓS haSubW hcompatW hcsnp hsubsto hΓOnp hiso hscS hc02)
  -- Peak-level dispatch: cvar–cvar via `keyCC`; mixed via `keyCP` (+ `sep_symm`);
  -- pseudo–pseudo is vacuous (`uniqueFrozen`).
  have key' : ∀ (p1 p2 : Peak s1'), p1 ≠ p2 →
      p1 ∈ (peakList (CapyCaptureSet.peakset Γsub (cs.subst σ))).filter
        (fun p => decide (Peak.IsStable Γsub p)) →
      p2 ∈ (peakList (CapyCaptureSet.peakset Γsub (cs.subst σ))).filter
        (fun p => decide (Peak.IsStable Γsub p)) →
      SepCheck
        (coreCtxW.push_lock
          (({ sep := peakSepCtx Γorig (CapyCaptureSet.peakset Γorig cs) scOrig,
              mutability := ΨmutR } : ModalCtx s2w).subst σtW))
        (CapyCaptureSet.compile
          (peakKeyItem (CapyCaptureSet.peakset Γsub (cs.subst σ)) p1)
          (scSub.rename Rename.succ))
        (CapyCaptureSet.compile
          (peakKeyItem (CapyCaptureSet.peakset Γsub (cs.subst σ)) p2)
          (scSub.rename Rename.succ)) := by
    intro p1 p2 hne hp1f hp2f
    obtain ⟨hp1, hp1s⟩ := List.mem_filter.mp hp1f
    obtain ⟨hp2, hp2s⟩ := List.mem_filter.mp hp2f
    cases p1 with
    | cvar d1 =>
      cases p2 with
      | cvar d2 =>
        have h1 := mem_peakCvars_of_cvar_mem hp1
        have h2 := mem_peakCvars_of_cvar_mem hp2
        exact keyCC d1 d2 (fun h => hne (congrArg Peak.cvar h))
          (decide_eq_true_iff.mp hp1s) (decide_eq_true_iff.mp hp2s) h1 h2
      | pseudo D2 =>
        exact keyCP d1 D2 (decide_eq_true_iff.mp hp1s) (mem_peakCvars_of_cvar_mem hp1)
          (mem_peakPseudos_of_pseudo_mem hp2)
    | pseudo D1 =>
      cases p2 with
      | cvar d2 =>
        exact SepCheck.sep_symm (keyCP d2 D1 (decide_eq_true_iff.mp hp2s)
          (mem_peakCvars_of_cvar_mem hp2) (mem_peakPseudos_of_pseudo_mem hp1))
      | pseudo D2 =>
        -- VACUOUS: distinct frozen SUB peaks trace to frozen ORIGIN sources forced equal.
        exfalso
        obtain ⟨C1', hC1, hC1m⟩ := peakPseudos_occ (mem_peakPseudos_of_pseudo_mem hp1)
        obtain ⟨C2', hC2, hC2m⟩ := peakPseudos_occ (mem_peakPseudos_of_pseudo_mem hp2)
        obtain ⟨c01, D01, m1, hc01, hC1eq⟩ :=
          pseudo_sub_peak_frozen_source hiso hsubsto hΓOnp hcsnp hC1
        obtain ⟨c02, D02, m2, hc02, hC2eq⟩ :=
          pseudo_sub_peak_frozen_source hiso hsubsto hΓOnp hcsnp hC2
        have ht1 : hiso.toPeak c01 = Peak.pseudo D01 := by
          have him := hiso.image c01; rw [hc01] at him
          cases htc : hiso.toPeak c01 with
          | cvar e => rw [htc] at him; simp [Peak.asCaptureSet] at him
          | pseudo D'' =>
            rw [htc] at him
            simp only [Peak.asCaptureSet, CapyCaptureSet.pseudo_peak.injEq] at him
            rw [him]
        have ht2 : hiso.toPeak c02 = Peak.pseudo D02 := by
          have him := hiso.image c02; rw [hc02] at him
          cases htc : hiso.toPeak c02 with
          | cvar e => rw [htc] at him; simp [Peak.asCaptureSet] at him
          | pseudo D'' =>
            rw [htc] at him
            simp only [Peak.asCaptureSet, CapyCaptureSet.pseudo_peak.injEq] at him
            rw [him]
        have hc12 : c01 = c02 := hiso.uniqueFrozen ht1 ht2
        subst hc12
        have hD : D01 = D02 := by
          rw [hc01] at hc02; exact CapyCaptureSet.pseudo_peak.inj hc02
        apply hne
        have e1 : D1 = (CapyCaptureSet.peaks Γsub D01).modeErase := by
          rw [← hC1m, hC1eq, CapyCaptureSet.modeErase_applyAccess]
        have e2 : D2 = (CapyCaptureSet.peaks Γsub D02).modeErase := by
          rw [← hC2m, hC2eq, CapyCaptureSet.modeErase_applyAccess]
        rw [e1, e2, hD]
  -- Discharge the goal (either ordering of the `HasTwoDistinct` pair).
  rcases hCdisj with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact key' c1 c2 hcne hc1 hc2
  · exact key' c2 c1 (Ne.symm hcne) hc2 hc1

/-- **Split-covering forward dispatch without `SrcAligned`** (the `realign` surrogate route) —
    the split-covering twin of `compile_peakSepCtx_sep_forward_realign`.  Runs the
    `SrcAligned`-based split-covering dispatch at the always-aligned `realign Γ sc`,
    transporting the covering premise `hsplitW`'s scope from the real `scOrig` to
    `realign Γorig scOrig` via `hbridge` (the compiled peak-set is bound-var-free, hence
    `lookupCVar`-insensitive), exactly as `_forward_realign` transports `hdropW`. -/
theorem compile_peakSepCtx_sep_forward_splitcov_realign {s1 s2w s1' s2w' : Sig}
    {Γorig : CapyCtx s1} {Γsub : CapyCtx s1'}
    {scOrig : SrcCtx s1 s2w} {scSub : SrcCtx s1' s2w'}
    {σ : CapySubst s1 s1'} {σtW : Subst s2w s2w'}
    {cs : CapyCaptureSet s1} {coreCtxW : Ctx s2w'} {ΨmutR : MutabilityCtx s2w}
    (hΓO : Γorig.IsClosed) (hΓS : Γsub.IsClosed)
    (hcompatAlW : SubstCompat (SrcCtx.realign Γsub scSub) (SrcCtx.realign Γorig scOrig) σ σtW)
    (hcsCl : cs.IsClosed) (hsubcl : (cs.subst σ).IsClosed)
    (hΓOnp : Γorig.NoPseudoPeak) (hcsnp : cs.NoPseudoPeak)
    (hinjW : scSub.CVarInjective)
    (hiso : PeakSubstIso σ)
    (hscS : CapySubst.IsClosed σ)
    (htv' : ∀ X, ∃ Y, σ.tvar X = CapyPureTy.tvar Y)
    (hsubsto : Γorig.SubstsTo Γsub σ)
    (hsplitW : TgtSplitCoveredOn
      (fun Z => ∃ m, CaptureSet.cvar m Z ⊆
        CapyCaptureSet.compile (CapyCaptureSet.peaks Γorig cs) scOrig) coreCtxW σtW)
    (hstab : hiso.StablePreserving Γorig Γsub) :
    ∀ (C1 C2 : CaptureSet (s2w',,Kind.lock)),
      (peakSepCtx Γsub (CapyCaptureSet.peakset Γsub (cs.subst σ))
        (scSub.rename Rename.succ)).HasTwoDistinct C1 C2 →
      SepCheck
        (coreCtxW.push_lock
          (({ sep := peakSepCtx Γorig (CapyCaptureSet.peakset Γorig cs) scOrig,
              mutability := ΨmutR } : ModalCtx s2w).subst σtW))
        C1 C2 := by
  have hInEq : peakSepCtx Γsub (CapyCaptureSet.peakset Γsub (cs.subst σ))
        ((SrcCtx.realign Γsub scSub).rename (Rename.succ (k := Kind.lock)))
      = peakSepCtx Γsub (CapyCaptureSet.peakset Γsub (cs.subst σ))
        (scSub.rename (Rename.succ (k := Kind.lock))) :=
    peakSepCtx_eq_of_lookupCVar (CapyCaptureSet.peaks_noBoundVar Γsub (cs.subst σ)) (fun c => by
      rw [SrcCtx.lookupCVar_rename, SrcCtx.lookupCVar_rename, SrcCtx.realign_lookupCVar])
  have hOutEq : peakSepCtx Γorig (CapyCaptureSet.peakset Γorig cs) (SrcCtx.realign Γorig scOrig)
      = peakSepCtx Γorig (CapyCaptureSet.peakset Γorig cs) scOrig :=
    peakSepCtx_eq_of_lookupCVar (CapyCaptureSet.peaks_noBoundVar Γorig cs)
      (fun c => SrcCtx.realign_lookupCVar Γorig scOrig c)
  have hbridge : CapyCaptureSet.compile (CapyCaptureSet.peaks Γorig cs)
        (SrcCtx.realign Γorig scOrig)
      = CapyCaptureSet.compile (CapyCaptureSet.peaks Γorig cs) scOrig :=
    CapyCaptureSet.compile_eq_of_lookupCVar (CapyCaptureSet.peaks_noBoundVar Γorig cs)
      (fun c => SrcCtx.realign_lookupCVar Γorig scOrig c)
  intro C1 C2 hdist
  rw [← hInEq] at hdist
  rw [← hOutEq]
  exact compile_peakSepCtx_sep_forward_splitcov (scOrig := SrcCtx.realign Γorig scOrig)
    (scSub := SrcCtx.realign Γsub scSub) hΓO hΓS
    (SrcCtx.realign_aligned Γorig scOrig) (SrcCtx.realign_aligned Γsub scSub) hcompatAlW
    hcsCl hsubcl hΓOnp hcsnp hinjW.realign hiso hscS htv' hsubsto
    (hsplitW.mono (fun Z hZ => hbridge ▸ hZ)) hstab
    C1 C2 hdist


/-- `subPeakOf`'s stability only depends on `hiso.toPeak d`'s shape (a `.pseudo` case is
    always stable regardless of the mode-erased content `subPeakOf` substitutes in). -/
theorem Peak.IsStable_subPeakOf {s1 s1' : Sig} {σ : CapySubst s1 s1'} (hiso : PeakSubstIso σ)
    (Γsub : CapyCtx s1') (d : BVar s1 .cvar) :
    Peak.IsStable Γsub (subPeakOf hiso Γsub d) ↔ Peak.IsStable Γsub (hiso.toPeak d) := by
  unfold subPeakOf
  cases hiso.toPeak d with
  | cvar e => rfl
  | pseudo D => simp only [Peak.IsStable]

/-- **Backward lock-`Satisfy` separation half (extracted, generic over the binder).**
    The separation dispatch of `cpoly`/`poly`/`arrow`'s `modal_modal` codomain in the
    BACKWARD direction (`⟦T⟧[σt] <: ⟦T[σ]⟧`): from `HasTwoDistinct` of two SUBSTITUTED ORIGIN
    items, derive a `SepCheck` in the context whose pushed lock is the SUB lock `Ψ_L`.  The
    origin peaks are all cvars (origin is pseudo-free); each maps via `subPeakOf` to a distinct
    SUB peak (`traceItem`: identity images → `identity_sub_peak_mem`/`peakItem_subst_subset`,
    frozen images → `frozen_sub_peak_present`/`peakItem_subst_subset_pseudo`), and the two
    distinct sub-peaks separate by `sep_lock` shrinking each origin item into its sub item. -/
theorem compile_peakSepCtx_sep_backward {s1 s2w s1' s2w' : Sig}
    {Γorig : CapyCtx s1} {Γsub : CapyCtx s1'}
    {scOrig : SrcCtx s1 s2w} {scSub : SrcCtx s1' s2w'}
    {σ : CapySubst s1 s1'} {σtW : Subst s2w s2w'}
    {cs : CapyCaptureSet s1} {coreCtxW : Ctx s2w'} {ΨmutSub : MutabilityCtx s2w'}
    (hΓS : Γsub.IsClosed) (haSubW : SrcAligned Γsub scSub)
    (hcompatW : SubstCompat scSub scOrig σ σtW)
    (hΓOnp : Γorig.NoPseudoPeak) (hcsnp : cs.NoPseudoPeak)
    (hiso : PeakSubstIso σ)
    (hscS : CapySubst.IsClosed σ)
    (htv' : ∀ X, ∃ Y, σ.tvar X = CapyPureTy.tvar Y)
    (hsubsto : Γorig.SubstsTo Γsub σ)
    (hstab : hiso.StablePreserving Γorig Γsub) :
    ∀ (C1 C2 : CaptureSet (s2w',,Kind.lock)),
      (((peakSepCtx Γorig (CapyCaptureSet.peakset Γorig cs) scOrig).subst σtW).rename
        Rename.succ).HasTwoDistinct C1 C2 →
      SepCheck
        (coreCtxW.push_lock
          ({ sep := peakSepCtx Γsub (CapyCaptureSet.peakset Γsub (cs.subst σ)) scSub,
             mutability := ΨmutSub } : ModalCtx s2w'))
        C1 C2 := by
  intro C1 C2 hdist
  obtain ⟨p1, hp1f, p2, hp2f, hpne, hPdisj⟩ := peakSepCtx_subst_rename_HasTwoDistinct_ne hdist
  obtain ⟨hp1, hp1s⟩ := List.mem_filter.mp hp1f
  obtain ⟨hp2, hp2s⟩ := List.mem_filter.mp hp2f
  -- Per ORIGIN cvar peak `d`: its sub-peak `subPeakOf d` is a peak of the sub peaks, and the
  -- substituted compiled origin item sits inside the compiled sub item.
  have traceItem : ∀ (d : BVar _ Kind.cvar),
      d ∈ peakCvars (CapyCaptureSet.peakset Γorig cs) →
      subPeakOf hiso Γsub d ∈ peakList (CapyCaptureSet.peakset Γsub (cs.subst σ)) ∧
        ((CapyCaptureSet.compile
            (peakItem (CapyCaptureSet.peakset Γorig cs) d) scOrig).subst σtW) ⊆
          CapyCaptureSet.compile
            (peakKeyItem (CapyCaptureSet.peakset Γsub (cs.subst σ)) (subPeakOf hiso Γsub d))
            scSub := by
    intro d hd
    obtain ⟨a0, hocc⟩ := peakCvars_occ hd
    cases htp : hiso.toPeak d with
    | cvar e =>
      have hde : σ.cvar d = CapyCaptureSet.cvar (.M .epsilon) e := by
        rw [hiso.image d, htp]; rfl
      have hmem := identity_sub_peak_mem htv' hsubsto hde hocc
      have hcont := peakItem_subst_subset (cs := cs) hcompatW htv' hsubsto hde
      refine ⟨?_, ?_⟩
      · simp only [subPeakOf, htp]; exact cvar_mem_peakList hmem
      · simp only [subPeakOf, htp, peakKeyItem]; exact hcont
    | pseudo D =>
      have hdD : σ.cvar d = CapyCaptureSet.pseudo_peak D := by
        rw [hiso.image d, htp]; rfl
      have hDcl : D.IsClosed := by
        have hcl := hscS.cvar_closed d; rw [hdD] at hcl
        cases hcl with | pseudo_peak hD => exact hD
      have hmem := frozen_sub_peak_present (cs := cs) hsubsto htv' hdD
      have hcont := peakItem_subst_subset_pseudo
        (Γorig := Γorig) (scOrig := scOrig) hΓS haSubW hcompatW hDcl hdD hmem
      refine ⟨?_, ?_⟩
      · simp only [subPeakOf, htp]
        apply pseudo_mem_peakList
        have h0 := pseudoBase_mem_peakPseudos
          (P := CapyCaptureSet.peakset Γsub (cs.subst σ)) (hmem a0 hocc)
        rwa [CapyCaptureSet.modeErase_applyAccess] at h0
      · simp only [subPeakOf, htp, peakKeyItem]; exact hcont
  -- Dispatch: origin peaks are all cvars; separate the two distinct sub-peaks in `Ψ_L`.
  have hnpOcs : (CapyCaptureSet.peakset Γorig cs).cs.NoPseudoPeak :=
    CapyCaptureSet.peaks_noPseudoPeak hΓOnp hcsnp
  cases p1 with
  | pseudo D1 => exact absurd hp1 (pseudo_not_mem_peakList_of_noPseudoPeak hnpOcs)
  | cvar d1 =>
    cases p2 with
    | pseudo D2 => exact absurd hp2 (pseudo_not_mem_peakList_of_noPseudoPeak hnpOcs)
    | cvar d2 =>
      have hd1 := mem_peakCvars_of_cvar_mem hp1
      have hd2 := mem_peakCvars_of_cvar_mem hp2
      have hne : d1 ≠ d2 := fun h => hpne (congrArg Peak.cvar h)
      obtain ⟨mem1, cont1⟩ := traceItem d1 hd1
      obtain ⟨mem2, cont2⟩ := traceItem d2 hd2
      have hne' : subPeakOf hiso Γsub d1 ≠ subPeakOf hiso Γsub d2 :=
        fun h => hne (subPeakOf_inj hiso h)
      have hsub1stab : Peak.IsStable Γsub (subPeakOf hiso Γsub d1) :=
        (Peak.IsStable_subPeakOf hiso Γsub d1).mpr ((hstab d1).mp (decide_eq_true_iff.mp hp1s))
      have hsub2stab : Peak.IsStable Γsub (subPeakOf hiso Γsub d2) :=
        (Peak.IsStable_subPeakOf hiso Γsub d2).mpr ((hstab d2).mp (decide_eq_true_iff.mp hp2s))
      have mem1' : subPeakOf hiso Γsub d1 ∈
          (peakList (CapyCaptureSet.peakset Γsub (cs.subst σ))).filter
            (fun p => decide (Peak.IsStable Γsub p)) :=
        List.mem_filter.mpr ⟨mem1, decide_eq_true_iff.mpr hsub1stab⟩
      have mem2' : subPeakOf hiso Γsub d2 ∈
          (peakList (CapyCaptureSet.peakset Γsub (cs.subst σ))).filter
            (fun p => decide (Peak.IsStable Γsub p)) :=
        List.mem_filter.mpr ⟨mem2, decide_eq_true_iff.mpr hsub2stab⟩
      have htd := (peakSepCtx_HasTwoDistinct_of (sc := scSub) mem1' mem2' hne').rename
        (f := Rename.succ (k := Kind.lock))
      have htd' := (peakSepCtx_HasTwoDistinct_of (sc := scSub) mem2' mem1' (Ne.symm hne')).rename
        (f := Rename.succ (k := Kind.lock))
      simp only [peakKeyItem] at hPdisj
      rcases hPdisj with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact SepCheck.sep_symm (SepCheck.sep_mono (SepCheck.sep_symm (SepCheck.sep_mono
          (SepCheck.sep_lock (ℓ := BVar.here) Ctx.LookupLock.here htd)
          (Subcapt.weaken (Subcapt.sc_elem cont1) _)))
          (Subcapt.weaken (Subcapt.sc_elem cont2) _))
      · exact SepCheck.sep_symm (SepCheck.sep_mono (SepCheck.sep_symm (SepCheck.sep_mono
          (SepCheck.sep_lock (ℓ := BVar.here) Ctx.LookupLock.here htd')
          (Subcapt.weaken (Subcapt.sc_elem cont2) _)))
          (Subcapt.weaken (Subcapt.sc_elem cont1) _))

/-- **Backward dispatch without the `SrcAligned` premise** (the `realign` surrogate route). -/
theorem compile_peakSepCtx_sep_backward_realign {s1 s2w s1' s2w' : Sig}
    {Γorig : CapyCtx s1} {Γsub : CapyCtx s1'}
    {scOrig : SrcCtx s1 s2w} {scSub : SrcCtx s1' s2w'}
    {σ : CapySubst s1 s1'} {σtW : Subst s2w s2w'}
    {cs : CapyCaptureSet s1} {coreCtxW : Ctx s2w'} {ΨmutSub : MutabilityCtx s2w'}
    (hΓS : Γsub.IsClosed)
    (hcompatAlW : SubstCompat (SrcCtx.realign Γsub scSub) (SrcCtx.realign Γorig scOrig) σ σtW)
    (hΓOnp : Γorig.NoPseudoPeak) (hcsnp : cs.NoPseudoPeak)
    (hiso : PeakSubstIso σ)
    (hscS : CapySubst.IsClosed σ)
    (htv' : ∀ X, ∃ Y, σ.tvar X = CapyPureTy.tvar Y)
    (hsubsto : Γorig.SubstsTo Γsub σ)
    (hstab : hiso.StablePreserving Γorig Γsub) :
    ∀ (C1 C2 : CaptureSet (s2w',,Kind.lock)),
      (((peakSepCtx Γorig (CapyCaptureSet.peakset Γorig cs) scOrig).subst σtW).rename
        Rename.succ).HasTwoDistinct C1 C2 →
      SepCheck
        (coreCtxW.push_lock
          ({ sep := peakSepCtx Γsub (CapyCaptureSet.peakset Γsub (cs.subst σ)) scSub,
             mutability := ΨmutSub } : ModalCtx s2w'))
        C1 C2 := by
  have hInEq : peakSepCtx Γorig (CapyCaptureSet.peakset Γorig cs) (SrcCtx.realign Γorig scOrig)
      = peakSepCtx Γorig (CapyCaptureSet.peakset Γorig cs) scOrig :=
    peakSepCtx_eq_of_lookupCVar (CapyCaptureSet.peaks_noBoundVar Γorig cs)
      (fun c => SrcCtx.realign_lookupCVar Γorig scOrig c)
  have hOutEq :
      peakSepCtx Γsub (CapyCaptureSet.peakset Γsub (cs.subst σ)) (SrcCtx.realign Γsub scSub)
      = peakSepCtx Γsub (CapyCaptureSet.peakset Γsub (cs.subst σ)) scSub :=
    peakSepCtx_eq_of_lookupCVar (CapyCaptureSet.peaks_noBoundVar Γsub (cs.subst σ))
      (fun c => SrcCtx.realign_lookupCVar Γsub scSub c)
  intro C1 C2 hdist
  rw [← hInEq] at hdist
  rw [← hOutEq]
  exact compile_peakSepCtx_sep_backward (scOrig := SrcCtx.realign Γorig scOrig)
    (scSub := SrcCtx.realign Γsub scSub) hΓS
    (SrcCtx.realign_aligned Γsub scSub) hcompatAlW
    hΓOnp hcsnp hiso hscS htv' hsubsto hstab
    C1 C2 hdist

/-!
# Target-cvar occurrence and the codomain crux  (Option B)

A *source-side* occurrence predicate `CapyTy.TgtCvarOccurs` that scopes the
droppability the SPLIT case of `compile_peakSepCtx_sep_forward` actually reads,
plus the **codomain crux** (the c-slot inserted by `Rename.implicit_cvar` never
occurs, so a lock-scoped `TgtPairDroppableOn` is vacuous there).  These live here
(rather than a downstream file) so `compile_subst_subtyp`'s premise can be scoped
by `TgtCvarOccurs T ctxOrig`.
-/

/-! ### Source cvar membership in capture sets / bounds -/

/-- `c` occurs as a capture-variable atom of the source capture set `cs`. -/
def CapyCaptureSet.CvarMem : BVar s .cvar → CapyCaptureSet s → Prop
| _, .empty => False
| c, .union cs1 cs2 => CvarMem c cs1 ∨ CvarMem c cs2
| _, .var _ _ => False
| c, .cvar _ c' => c = c'
| c, .pseudo_peak C => CvarMem c C

theorem CapyCaptureSet.CvarMem.rename_inv {cs : CapyCaptureSet s1} {ρ : Rename s1 s2}
    {c' : BVar s2 .cvar} (h : CapyCaptureSet.CvarMem c' (cs.rename ρ)) :
    ∃ c, ρ.var c = c' ∧ CapyCaptureSet.CvarMem c cs := by
  induction cs with
  | empty => exact absurd h (by simp [CapyCaptureSet.rename, CapyCaptureSet.CvarMem])
  | union cs1 cs2 ih1 ih2 =>
    simp only [CapyCaptureSet.rename, CapyCaptureSet.CvarMem] at h
    cases h with
    | inl h => obtain ⟨c, hc, hm⟩ := ih1 h; exact ⟨c, hc, Or.inl hm⟩
    | inr h => obtain ⟨c, hc, hm⟩ := ih2 h; exact ⟨c, hc, Or.inr hm⟩
  | var a x => exact absurd h (by simp [CapyCaptureSet.rename, CapyCaptureSet.CvarMem])
  | cvar a c0 =>
    simp only [CapyCaptureSet.rename, CapyCaptureSet.CvarMem] at h
    exact ⟨c0, h.symm, rfl⟩
  | pseudo_peak C ih =>
    simp only [CapyCaptureSet.rename, CapyCaptureSet.CvarMem] at h
    obtain ⟨c, hc, hm⟩ := ih h
    exact ⟨c, hc, hm⟩

/-- `c` occurs in a source capture bound (only `.bound` carries a set). -/
def CapyCaptureBound.CvarMem : BVar s .cvar → CapyCaptureBound s → Prop
| _, .unbound _ => False
| c, .bound cs => CapyCaptureSet.CvarMem c cs

theorem CapyCaptureBound.CvarMem.rename_inv {cb : CapyCaptureBound s1} {ρ : Rename s1 s2}
    {c' : BVar s2 .cvar} (h : CapyCaptureBound.CvarMem c' (cb.rename ρ)) :
    ∃ c, ρ.var c = c' ∧ CapyCaptureBound.CvarMem c cb := by
  cases cb with
  | unbound m => exact absurd h (by simp [CapyCaptureBound.rename, CapyCaptureBound.CvarMem])
  | bound cs =>
    simp only [CapyCaptureBound.rename, CapyCaptureBound.CvarMem] at h
    obtain ⟨c, hc, hm⟩ := CapyCaptureSet.CvarMem.rename_inv h
    exact ⟨c, hc, hm⟩

/-- Inverting `Rename.lift` on a `.there` target. -/
theorem Rename.lift_var_eq_there_inv {ρ : Rename s1 s2} {k : Kind}
    {c0 : BVar (s1,,k) .cvar} {c' : BVar s2 .cvar}
    (h : (ρ.lift (k := k)).var c0 = BVar.there c') :
    ∃ c, c0 = BVar.there c ∧ ρ.var c = c' := by
  cases c0 with
  | here => simp only [Rename.lift] at h; cases h
  | there c => simp only [Rename.lift] at h; exact ⟨c, rfl, BVar.there.inj h⟩

/-! ### Source cvar freeness in types -/

/-- `c` occurs free (as a capture-variable atom, de-Bruijn adjusted under binders)
    in the source type `T`. -/
def CapyTy.SrcCvarFree : {sort : CapyTySort} → {s : Sig} → BVar s .cvar → CapyTy sort s → Prop
| _, _, _, .top => False
| _, _, _, .tvar _ => False
| _, _, _, .unit => False
| _, _, _, .bool => False
| _, _, c, .cap cs => CapyCaptureSet.CvarMem c cs
| _, _, c, .cell cs _ => CapyCaptureSet.CvarMem c cs
| _, _, c, .arrow T1 cs E =>
    CapyTy.SrcCvarFree (.there c) T1 ∨ CapyCaptureSet.CvarMem c cs
      ∨ CapyTy.SrcCvarFree (.there c) E
| _, _, c, .poly S cs E =>
    CapyTy.SrcCvarFree c S ∨ CapyCaptureSet.CvarMem c cs ∨ CapyTy.SrcCvarFree (.there c) E
| _, _, c, .cpoly cb cs E =>
    CapyCaptureBound.CvarMem c cb ∨ CapyCaptureSet.CvarMem c cs ∨ CapyTy.SrcCvarFree (.there c) E
| _, _, c, .exi T => CapyTy.SrcCvarFree (.there c) T
| _, _, c, .typ T => CapyTy.SrcCvarFree c T

theorem CapyTy.SrcCvarFree.rename_inv {sort : CapyTySort} {s1 : Sig} (T : CapyTy sort s1) :
    ∀ {s2 : Sig} {ρ : Rename s1 s2} {c' : BVar s2 .cvar},
      CapyTy.SrcCvarFree c' (T.rename ρ) → ∃ c, ρ.var c = c' ∧ CapyTy.SrcCvarFree c T := by
  induction T with
  | top => intro s2 ρ c' h; exact absurd h (by simp [CapyTy.rename, CapyTy.SrcCvarFree])
  | tvar x => intro s2 ρ c' h; exact absurd h (by simp [CapyTy.rename, CapyTy.SrcCvarFree])
  | unit => intro s2 ρ c' h; exact absurd h (by simp [CapyTy.rename, CapyTy.SrcCvarFree])
  | bool => intro s2 ρ c' h; exact absurd h (by simp [CapyTy.rename, CapyTy.SrcCvarFree])
  | cap cs =>
    intro s2 ρ c' h
    simp only [CapyTy.rename, CapyTy.SrcCvarFree] at h
    obtain ⟨c, hc, hm⟩ := CapyCaptureSet.CvarMem.rename_inv h
    exact ⟨c, hc, hm⟩
  | cell cs m =>
    intro s2 ρ c' h
    simp only [CapyTy.rename, CapyTy.SrcCvarFree] at h
    obtain ⟨c, hc, hm⟩ := CapyCaptureSet.CvarMem.rename_inv h
    exact ⟨c, hc, hm⟩
  | arrow T1 cs E ih1 ihE =>
    intro s2 ρ c' h
    simp only [CapyTy.rename, CapyTy.SrcCvarFree] at h
    rcases h with h | h | h
    · obtain ⟨c0, hc0, hm⟩ := ih1 h
      obtain ⟨c, hce, hcρ⟩ := Rename.lift_var_eq_there_inv hc0
      subst hce
      exact ⟨c, hcρ, Or.inl hm⟩
    · obtain ⟨c, hc, hm⟩ := CapyCaptureSet.CvarMem.rename_inv h
      exact ⟨c, hc, Or.inr (Or.inl hm)⟩
    · obtain ⟨c0, hc0, hm⟩ := ihE h
      obtain ⟨c, hce, hcρ⟩ := Rename.lift_var_eq_there_inv hc0
      subst hce
      exact ⟨c, hcρ, Or.inr (Or.inr hm)⟩
  | poly S cs E ihS ihE =>
    intro s2 ρ c' h
    simp only [CapyTy.rename, CapyTy.SrcCvarFree] at h
    rcases h with h | h | h
    · obtain ⟨c, hc, hm⟩ := ihS h
      exact ⟨c, hc, Or.inl hm⟩
    · obtain ⟨c, hc, hm⟩ := CapyCaptureSet.CvarMem.rename_inv h
      exact ⟨c, hc, Or.inr (Or.inl hm)⟩
    · obtain ⟨c0, hc0, hm⟩ := ihE h
      obtain ⟨c, hce, hcρ⟩ := Rename.lift_var_eq_there_inv hc0
      subst hce
      exact ⟨c, hcρ, Or.inr (Or.inr hm)⟩
  | cpoly cb cs E ihE =>
    intro s2 ρ c' h
    simp only [CapyTy.rename, CapyTy.SrcCvarFree] at h
    rcases h with h | h | h
    · obtain ⟨c, hc, hm⟩ := CapyCaptureBound.CvarMem.rename_inv h
      exact ⟨c, hc, Or.inl hm⟩
    · obtain ⟨c, hc, hm⟩ := CapyCaptureSet.CvarMem.rename_inv h
      exact ⟨c, hc, Or.inr (Or.inl hm)⟩
    · obtain ⟨c0, hc0, hm⟩ := ihE h
      obtain ⟨c, hce, hcρ⟩ := Rename.lift_var_eq_there_inv hc0
      subst hce
      exact ⟨c, hcρ, Or.inr (Or.inr hm)⟩
  | exi T ih =>
    intro s2 ρ c' h
    simp only [CapyTy.rename, CapyTy.SrcCvarFree] at h
    obtain ⟨c0, hc0, hm⟩ := ih h
    obtain ⟨c, hce, hcρ⟩ := Rename.lift_var_eq_there_inv hc0
    subst hce
    exact ⟨c, hcρ, hm⟩
  | typ T ih =>
    intro s2 ρ c' h
    simp only [CapyTy.rename, CapyTy.SrcCvarFree] at h
    obtain ⟨c, hc, hm⟩ := ih h
    exact ⟨c, hc, hm⟩

/-- The capture slot inserted by `Rename.implicit_cvar` (`.there .here`) is never
    referenced by the renamed type. -/
theorem CapyTy.not_SrcCvarFree_implicit_cvar {sort : CapyTySort} {s : Sig} {k : Kind}
    {T : CapyTy sort (s,,k)} :
    ¬ CapyTy.SrcCvarFree (BVar.there BVar.here)
        (T.rename (Rename.implicit_cvar (s := s) (k := k))) := by
  intro h
  obtain ⟨c, hc, _⟩ := CapyTy.SrcCvarFree.rename_inv T h
  cases c with
  | here => simp only [Rename.implicit_cvar] at hc; cases hc
  | there y => simp only [Rename.implicit_cvar] at hc; cases hc

/-! ### Source cvar freeness in the compiler's source typing context -/

/-- `c` occurs free in a source-context binder's stored type / bound. -/
def CapyBinding.SrcCvarFree : BVar s .cvar → CapyBinding s k → Prop
| c, .var T => CapyTy.SrcCvarFree c T
| c, .tvar S => CapyTy.SrcCvarFree c S.core
| c, .cvar _ cb => CapyCaptureBound.CvarMem c cb

/-- `c` occurs free in some binder of the source typing context `Γ`. -/
def CapyCtx.SrcCvarFree : {s : Sig} → BVar s .cvar → CapyCtx s → Prop
| _, _, .empty => False
| _, .here, .push _ _ => False
| _, .there c0, .push Γ b => CapyBinding.SrcCvarFree c0 b ∨ CapyCtx.SrcCvarFree c0 Γ

/-! ### The target-cvar occurrence predicate and the codomain crux -/

/-- A target cvar `Y` *occurs* for `(T, ctx)` when it is the `lookupCVar` image of a
    source cvar free in `T` or in `ctx`'s source typing context. -/
def CapyTy.TgtCvarOccurs (T : CapyTy sort s1) (ctx : CompilerCtx s1 s2)
    (Y : BVar s2 .cvar) : Prop :=
  ∃ c : BVar s1 .cvar, ctx.srcCtx.lookupCVar c = Y ∧
    (CapyTy.SrcCvarFree c T ∨ CapyCtx.SrcCvarFree c ctx.capyCtx)

/-- A source cvar free in neither `T` nor the context has a non-occurring target
    image. -/
theorem CapyTy.TgtCvarOccurs.absent {T : CapyTy sort s1} {ctx : CompilerCtx s1 s2}
    {c : BVar s1 .cvar} (hinj : ctx.srcCtx.CVarInjective)
    (hT : ¬ CapyTy.SrcCvarFree c T)
    (hΓ : ¬ CapyCtx.SrcCvarFree c ctx.capyCtx) :
    ¬ CapyTy.TgtCvarOccurs T ctx (ctx.srcCtx.lookupCVar c) := by
  rintro ⟨c', hlk, hfree⟩
  have hcc : c' = c := hinj hlk
  subst hcc
  rcases hfree with h | h
  · exact hT h
  · exact hΓ h

/-- **The codomain crux.**  For a codomain type `T2` under a binder `k0`, lifted by
    `Rename.implicit_cvar`, the c-slot's target image does NOT occur (given
    injectivity and a c-slot-free context). -/
theorem CapyTy.tgtCvarOccurs_implicit_cvar_absent {sort : CapyTySort} {s1 : Sig}
    {k0 : Kind} {s2 : Sig} {T2 : CapyTy sort (s1,,k0)}
    {ctx : CompilerCtx (s1,C,,k0) s2}
    (hinj : ctx.srcCtx.CVarInjective)
    (hΓ : ¬ CapyCtx.SrcCvarFree (BVar.there BVar.here) ctx.capyCtx) :
    ¬ CapyTy.TgtCvarOccurs (T2.rename Rename.implicit_cvar) ctx
        (ctx.srcCtx.lookupCVar (BVar.there BVar.here)) :=
  CapyTy.TgtCvarOccurs.absent hinj CapyTy.not_SrcCvarFree_implicit_cvar hΓ

/-! ### Step-1 bridge: dispatch scope traces to source cvar freeness -/

/-- A `Subset` cvar-atom of a capture set is a `CvarMem` of it (access modes ignored). -/
theorem CapyCaptureSet.cvarMem_of_subset_cvar {s : Sig} {cs : CapyCaptureSet s}
    {a : Access} {c : BVar s .cvar}
    (h : CapyCaptureSet.Subset (.cvar a c) cs) : CapyCaptureSet.CvarMem c cs := by
  generalize hcv : CapyCaptureSet.cvar a c = cvatom at h
  induction h with
  | refl => cases hcv; exact rfl
  | empty => cases hcv
  | union_left _ _ => cases hcv
  | union_right_left _ ih => exact Or.inl (ih hcv)
  | union_right_right _ ih => exact Or.inr (ih hcv)

/-- `CvarMem` is preserved by stripping `applyRO` (it rewrites only access modes). -/
theorem CapyCaptureSet.CvarMem.applyRO {s : Sig} {cs : CapyCaptureSet s} {d : BVar s .cvar}
    (h : CapyCaptureSet.CvarMem d cs.applyRO) : CapyCaptureSet.CvarMem d cs := by
  induction cs with
  | empty => exact h
  | union cs1 cs2 ih1 ih2 =>
    simp only [CapyCaptureSet.applyRO_union, CapyCaptureSet.CvarMem] at h ⊢
    exact h.imp ih1 ih2
  | var a x => exact h
  | cvar a x => exact h
  | pseudo_peak C ih =>
    simp only [CapyCaptureSet.applyRO, CapyCaptureSet.CvarMem] at h ⊢; exact ih h

/-- `CvarMem` is preserved by stripping `applyDrop`. -/
theorem CapyCaptureSet.CvarMem.applyDrop {s : Sig} {cs : CapyCaptureSet s} {d : BVar s .cvar}
    (h : CapyCaptureSet.CvarMem d cs.applyDrop) : CapyCaptureSet.CvarMem d cs := by
  induction cs with
  | empty => exact h
  | union cs1 cs2 ih1 ih2 =>
    simp only [CapyCaptureSet.applyDrop, CapyCaptureSet.CvarMem] at h ⊢
    exact h.imp ih1 ih2
  | var a x => exact h
  | cvar a x => exact h
  | pseudo_peak C ih =>
    simp only [CapyCaptureSet.applyDrop, CapyCaptureSet.CvarMem] at h ⊢; exact ih h

/-- `CvarMem` is preserved by stripping `applyAccess`. -/
theorem CapyCaptureSet.CvarMem.applyAccess {s : Sig} {cs : CapyCaptureSet s} {d : BVar s .cvar}
    {a : Access} (h : CapyCaptureSet.CvarMem d (cs.applyAccess a)) :
    CapyCaptureSet.CvarMem d cs := by
  cases a with
  | M m =>
    cases m with
    | epsilon => exact h
    | ro => exact CapyCaptureSet.CvarMem.applyRO h
  | drop => exact CapyCaptureSet.CvarMem.applyDrop h

/-- A cvar of a `.capt`-type's top capture set is free in the type. -/
theorem CapyTy.cvarMem_captureSet_srcCvarFree {s : Sig} {T : CapyTy .capt s} {d : BVar s .cvar}
    (h : CapyCaptureSet.CvarMem d T.captureSet) : CapyTy.SrcCvarFree d T := by
  cases T with
  | top => exact absurd h (by simp [CapyTy.captureSet, CapyCaptureSet.CvarMem])
  | tvar x => exact absurd h (by simp [CapyTy.captureSet, CapyCaptureSet.CvarMem])
  | unit => exact absurd h (by simp [CapyTy.captureSet, CapyCaptureSet.CvarMem])
  | bool => exact absurd h (by simp [CapyTy.captureSet, CapyCaptureSet.CvarMem])
  | cap cs => exact h
  | cell cs m => exact h
  | arrow T1 cs E => exact Or.inr (Or.inl h)
  | poly S cs E => exact Or.inr (Or.inl h)
  | cpoly cb cs E => exact Or.inr (Or.inl h)

/-- Equation for `CapyCtx.SrcCvarFree` on a `.there`/`.push` (unfolds even when the
    pushed binder's kind is abstract — the raw `match` won't iota-reduce there). -/
theorem CapyCtx.srcCvarFree_there_push {s : Sig} {k : Kind} {Γ : CapyCtx s}
    {b : CapyBinding s k} {c0 : BVar s .cvar} :
    CapyCtx.SrcCvarFree (BVar.there c0) (Γ.push b)
      ↔ (CapyBinding.SrcCvarFree c0 b ∨ CapyCtx.SrcCvarFree c0 Γ) := by
  cases b <;> exact Iff.rfl

mutual
/-- **Step-1 foundation.**  A cvar occurring in `peaks Γ cs` is free in `cs` or in the
    source typing context `Γ` (via `peaksVarBound` resolving a term-var through its
    binder's stored type). -/
theorem CapyCaptureSet.cvarMem_peaks {s : Sig} (Γ : CapyCtx s) (cs : CapyCaptureSet s) :
    ∀ {d : BVar s .cvar}, CapyCaptureSet.CvarMem d (CapyCaptureSet.peaks Γ cs) →
      CapyCaptureSet.CvarMem d cs ∨ CapyCtx.SrcCvarFree d Γ := by
  match cs with
  | .empty => intro d h; rw [CapyCaptureSet.peaks] at h; exact absurd h id
  | .union cs1 cs2 =>
    intro d h
    rw [CapyCaptureSet.peaks] at h
    simp only [CapyCaptureSet.CvarMem] at h ⊢
    cases h with
    | inl h => exact (CapyCaptureSet.cvarMem_peaks Γ cs1 h).imp Or.inl id
    | inr h => exact (CapyCaptureSet.cvarMem_peaks Γ cs2 h).imp Or.inr id
  | .cvar m c => intro d h; rw [CapyCaptureSet.peaks] at h; exact Or.inl h
  | .var _ (.free _) => intro d h; rw [CapyCaptureSet.peaks] at h; exact absurd h id
  | .var m (.bound x) =>
    intro d h
    rw [CapyCaptureSet.peaks] at h
    exact Or.inr (CapyCaptureSet.cvarMem_peaksVarBound Γ m x h)
  | .pseudo_peak C =>
    intro d h
    rw [CapyCaptureSet.peaks] at h
    simp only [CapyCaptureSet.CvarMem] at h ⊢
    exact CapyCaptureSet.cvarMem_peaks Γ C h
termination_by (sizeOf Γ, sizeOf cs)

/-- **Step-1 foundation (mutual).**  A cvar of `peaksVarBound Γ m x` is free in a binder
    of `Γ` (the binder's stored type's capture set, resolved through the context). -/
theorem CapyCaptureSet.cvarMem_peaksVarBound {s : Sig} (Γ : CapyCtx s) (m : Access)
    (x : BVar s .var) :
    ∀ {d : BVar s .cvar}, CapyCaptureSet.CvarMem d (CapyCaptureSet.peaksVarBound Γ m x) →
      CapyCtx.SrcCvarFree d Γ := by
  match Γ, x with
  | .push Γ' (.var T), .here =>
    intro d h
    rw [CapyCaptureSet.peaksVarBound] at h
    have h1 := CapyCaptureSet.CvarMem.applyAccess h
    obtain ⟨d0, hd0, hm⟩ := CapyCaptureSet.CvarMem.rename_inv h1
    have hthere : d = BVar.there d0 := by rw [← hd0]; rfl
    subst hthere
    exact (CapyCaptureSet.cvarMem_peaks Γ' T.captureSet hm).imp
      CapyTy.cvarMem_captureSet_srcCvarFree id
  | .push Γ' b, .there x' =>
    intro d h
    rw [CapyCaptureSet.peaksVarBound] at h
    obtain ⟨d0, hd0, hm⟩ := CapyCaptureSet.CvarMem.rename_inv h
    have hthere : d = BVar.there d0 := by rw [← hd0]; rfl
    subst hthere
    exact CapyCtx.srcCvarFree_there_push.mpr
      (Or.inr (CapyCaptureSet.cvarMem_peaksVarBound Γ' m x' hm))
termination_by (sizeOf Γ, sizeOf x + 1)
end

/-! ### Occurrence transport through the recursive-call binders -/

/-- Occurrence transports through a target weakening: the target sig grows by a fresh
    binder (source & typing context unchanged), so an occurrence at `.there Y0`
    descends to `Y0`. -/
theorem CapyTy.tgtCvarOccurs_weakenTarget {sort : CapyTySort} {s1 s2 : Sig} {k : Kind}
    {T : CapyTy sort s1} {ctx : CompilerCtx s1 s2} {b : Binding s2 k} {Y0 : BVar s2 .cvar}
    (h : CapyTy.TgtCvarOccurs T (ctx.weakenTarget b) (BVar.there Y0)) :
    CapyTy.TgtCvarOccurs T ctx Y0 := by
  obtain ⟨c, hlk, hfree⟩ := h
  refine ⟨c, ?_, hfree⟩
  have hlk' : (ctx.srcCtx.rename Rename.succ).lookupCVar c = BVar.there Y0 := hlk
  rw [SrcCtx.lookupCVar_rename] at hlk'
  exact BVar.there.inj hlk'

/-- Occurrence transport for the `exi` recursion (`ctxOrig.weakenTarget.consCVar`): a
    child occurrence at `.there Y0` traces to a parent occurrence of `exi T1` at `Y0`. -/
theorem CapyTy.tgtCvarOccurs_exi {s1 s2 : Sig} {T1 : CapyTy .capt (s1,C)}
    {ctx : CompilerCtx s1 s2} {Y0 : BVar s2 .cvar}
    (h : CapyTy.TgtCvarOccurs T1
      (ctx.weakenTarget.consCVar (CapyCaptureBound.unbound Mutability.epsilon) BVar.here)
      (BVar.there Y0)) :
    CapyTy.TgtCvarOccurs (CapyTy.exi T1) ctx Y0 := by
  obtain ⟨c, hlk, hfree⟩ := h
  cases c with
  | here =>
    -- source `.here` maps to target `.here`, contradicting `.there Y0`
    rw [show (ctx.weakenTarget.consCVar
        (CapyCaptureBound.unbound Mutability.epsilon) BVar.here).srcCtx.lookupCVar BVar.here
        = BVar.here from rfl] at hlk
    simp at hlk
  | there c0 =>
    refine ⟨c0, ?_, ?_⟩
    · have hlk' : (ctx.srcCtx.rename Rename.succ).lookupCVar c0 = BVar.there Y0 := hlk
      rw [SrcCtx.lookupCVar_rename] at hlk'
      exact BVar.there.inj hlk'
    · rcases hfree with hT | hΓ
      · exact Or.inl hT
      · -- capyCtx = ctx.capyCtx.push (.cvar .access_only (.unbound ε)); the binder is cvar-free
        refine Or.inr ?_
        have := (CapyCtx.srcCvarFree_there_push (b :=
          CapyBinding.cvar CapyAuthority.access_only
            (CapyCaptureBound.unbound Mutability.epsilon))).mp hΓ
        rcases this with hb | hrest
        · exact absurd hb id
        · exact hrest

/-- Freeness through `refineCaptureSet`: a cvar free in a capture-refined type is either
    free in the replacement set or free in the original type (the refine only rewrites the
    TOP capture set). -/
theorem CapyTy.srcCvarFree_refineCaptureSet {s : Sig} {T : CapyTy .capt s}
    {cs : CapyCaptureSet s} {c : BVar s .cvar}
    (h : CapyTy.SrcCvarFree c (T.refineCaptureSet cs)) :
    CapyCaptureSet.CvarMem c cs ∨ CapyTy.SrcCvarFree c T := by
  cases T with
  | top => exact absurd h (by simp [CapyTy.refineCaptureSet, CapyTy.SrcCvarFree])
  | tvar x => exact absurd h (by simp [CapyTy.refineCaptureSet, CapyTy.SrcCvarFree])
  | unit => exact absurd h (by simp [CapyTy.refineCaptureSet, CapyTy.SrcCvarFree])
  | bool => exact absurd h (by simp [CapyTy.refineCaptureSet, CapyTy.SrcCvarFree])
  | cap cs0 => exact Or.inl h
  | cell cs0 m => exact Or.inl h
  | arrow T1 cs0 E =>
    simp only [CapyTy.refineCaptureSet, CapyTy.SrcCvarFree] at h
    rcases h with h | h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inr h))
  | poly S cs0 E =>
    simp only [CapyTy.refineCaptureSet, CapyTy.SrcCvarFree] at h
    rcases h with h | h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inr h))
  | cpoly cb cs0 E =>
    simp only [CapyTy.refineCaptureSet, CapyTy.SrcCvarFree] at h
    rcases h with h | h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inr h))

/-- Occurrence transport for the `poly` BOUND recursion (`compile_subst_subtyp S`, same
    context, same target cvar): a child occurrence of `S` lifts to a parent occurrence of
    `poly S cs E`.  Used with `.mono` (no target-binder peel). -/
theorem CapyTy.tgtCvarOccurs_poly_bound {s1 s2 : Sig} {S : CapyTy .capt s1}
    {cs : CapyCaptureSet s1} {E : CapyTy .exi (s1,X)} {ctx : CompilerCtx s1 s2}
    {Y : BVar s2 .cvar} (h : CapyTy.TgtCvarOccurs S ctx Y) :
    CapyTy.TgtCvarOccurs (CapyTy.poly S cs E) ctx Y := by
  obtain ⟨c, hlk, hfree⟩ := h
  refine ⟨c, hlk, ?_⟩
  rcases hfree with hS | hΓ
  · exact Or.inl (Or.inl hS)
  · exact Or.inr hΓ

/-- Occurrence transport for the `poly` BODY recursion.  The body `E` lives under a source
    tvar binder (`consTVar`), a target tvar weakening and a target lock weakening; a child
    occurrence at `.there (.there Y0)` traces to a parent occurrence of `poly S cs E` at `Y0`. -/
theorem CapyTy.tgtCvarOccurs_poly_body {s1 s2 : Sig} {S : CapyTy .capt s1}
    {cs : CapyCaptureSet s1} {E : CapyTy .exi (s1,X)} {ctx : CompilerCtx s1 s2}
    {bl : Binding (s2,,Kind.tvar) Kind.lock} {Y0 : BVar s2 .cvar}
    (h : CapyTy.TgtCvarOccurs E
      ((ctx.weakenTarget.consTVar CapyPureTy.top BVar.here).weakenTarget bl)
      (BVar.there (BVar.there Y0))) :
    CapyTy.TgtCvarOccurs (CapyTy.poly S cs E) ctx Y0 := by
  obtain ⟨c, hlk, hfree⟩ := h
  cases c with
  | there c0 =>
    refine ⟨c0, ?_, ?_⟩
    · have hlk' : (((ctx.srcCtx.rename Rename.succ).rename Rename.succ).lookupCVar c0)
          = BVar.there (BVar.there Y0) := hlk
      rw [SrcCtx.lookupCVar_rename, SrcCtx.lookupCVar_rename] at hlk'
      exact BVar.there.inj (BVar.there.inj hlk')
    · rcases hfree with hE | hΓ
      · exact Or.inl (Or.inr (Or.inr hE))
      · refine Or.inr ?_
        rcases (CapyCtx.srcCvarFree_there_push (b := CapyBinding.tvar CapyPureTy.top)).mp hΓ
          with hb | hrest
        · exact absurd hb id
        · exact hrest

/-- Occurrence transport for the `cpoly` BODY recursion.  The body `E` lives under a source
    cvar binder (`consCVar cb`), a target cvar weakening and a target lock weakening; a child
    occurrence at `.there (.there Y0)` traces to a parent occurrence of `cpoly cb cs E` at `Y0`. -/
theorem CapyTy.tgtCvarOccurs_cpoly_body {s1 s2 : Sig} {cb : CapyCaptureBound s1}
    {cs : CapyCaptureSet s1} {E : CapyTy .exi (s1,C)} {ctx : CompilerCtx s1 s2}
    {bl : Binding (s2,,Kind.cvar) Kind.lock} {Y0 : BVar s2 .cvar}
    (h : CapyTy.TgtCvarOccurs E
      ((ctx.weakenTarget.consCVar cb BVar.here).weakenTarget bl)
      (BVar.there (BVar.there Y0))) :
    CapyTy.TgtCvarOccurs (CapyTy.cpoly cb cs E) ctx Y0 := by
  obtain ⟨c, hlk, hfree⟩ := h
  cases c with
  | here =>
    rw [show ((ctx.weakenTarget.consCVar cb BVar.here).weakenTarget bl).srcCtx.lookupCVar
        BVar.here = BVar.there BVar.here from rfl] at hlk
    simp at hlk
  | there c0 =>
    refine ⟨c0, ?_, ?_⟩
    · have hlk' : (((ctx.srcCtx.rename Rename.succ).rename Rename.succ).lookupCVar c0)
          = BVar.there (BVar.there Y0) := hlk
      rw [SrcCtx.lookupCVar_rename, SrcCtx.lookupCVar_rename] at hlk'
      exact BVar.there.inj (BVar.there.inj hlk')
    · rcases hfree with hE | hΓ
      · exact Or.inl (Or.inr (Or.inr hE))
      · rcases (CapyCtx.srcCvarFree_there_push (b :=
          CapyBinding.cvar CapyAuthority.access_only cb)).mp hΓ with hb | hrest
        · exact Or.inl (Or.inl hb)
        · exact Or.inr hrest

/-- Occurrence transport for the `arrow` DOMAIN recursion.  The re-abstracted domain type
    `(T1.rename succ).refineCaptureSet {param}` lives under two target cvar weakenings, a source
    cvar binder (`consCVar`) and a source term binder (`consVar T1`); a child occurrence at
    `.there (.there Y0)` traces to a parent occurrence of `arrow T1 cs E` at `Y0`. -/
theorem CapyTy.tgtCvarOccurs_arrow_dom {s1 s2 : Sig} {T1 : CapyTy .capt (s1,C)}
    {cs : CapyCaptureSet s1} {E : CapyTy .exi (s1,x)} {ctx : CompilerCtx s1 s2}
    {Y0 : BVar s2 .cvar}
    (h : CapyTy.TgtCvarOccurs
      ((T1.rename Rename.succ).refineCaptureSet
        (CapyCaptureSet.var (.M .epsilon) (.bound BVar.here)))
      ((ctx.weakenTarget.weakenTarget.consCVar
          (CapyCaptureBound.unbound Mutability.epsilon) (BVar.there BVar.here)).consVar T1 none
        (CaptureSet.cvar (.M .epsilon) BVar.here))
      (BVar.there (BVar.there Y0))) :
    CapyTy.TgtCvarOccurs (CapyTy.arrow T1 cs E) ctx Y0 := by
  obtain ⟨c, hlk, hfree⟩ := h
  cases c with
  | there c1 =>
    cases c1 with
    | here =>
      have hlk2 : (BVar.there BVar.here : BVar ((s2,,Kind.cvar),,Kind.cvar) .cvar)
          = BVar.there (BVar.there Y0) := hlk
      simp at hlk2
    | there c0 =>
      refine ⟨c0, ?_, ?_⟩
      · have hlk' : (((ctx.srcCtx.rename Rename.succ).rename Rename.succ).lookupCVar c0)
            = BVar.there (BVar.there Y0) := hlk
        rw [SrcCtx.lookupCVar_rename, SrcCtx.lookupCVar_rename] at hlk'
        exact BVar.there.inj (BVar.there.inj hlk')
      · rcases hfree with hT | hΓ
        · rcases CapyTy.srcCvarFree_refineCaptureSet hT with hv | hren
          · exact absurd hv (by intro hc; cases hc)
          · obtain ⟨c', hc'eq, hc'free⟩ := CapyTy.SrcCvarFree.rename_inv T1 hren
            have hc'eq' : BVar.there c' = BVar.there (BVar.there c0) := hc'eq
            have : c' = BVar.there c0 := BVar.there.inj hc'eq'
            subst this
            exact Or.inl (Or.inl hc'free)
        · refine ?_
          rcases (CapyCtx.srcCvarFree_there_push (b := CapyBinding.var T1)).mp hΓ with hb | hrest
          · exact Or.inl (Or.inl hb)
          · rcases (CapyCtx.srcCvarFree_there_push (b :=
              CapyBinding.cvar CapyAuthority.access_only
                (CapyCaptureBound.unbound Mutability.epsilon))).mp hrest with hb2 | hrest2
            · exact absurd hb2 id
            · exact Or.inr hrest2

/-- Occurrence transport for the `arrow` CODOMAIN recursion.  The codomain `E.rename implicit_cvar`
    lives under three target weakenings (cvar, cvar, var), a source cvar binder, a source term
    binder and a target lock weakening; a child occurrence at `.there⁴ Y0` traces to a parent
    occurrence of `arrow T1 cs E` at `Y0`. -/
theorem CapyTy.tgtCvarOccurs_arrow_cod {s1 s2 : Sig} {T1 : CapyTy .capt (s1,C)}
    {cs : CapyCaptureSet s1} {E : CapyTy .exi (s1,x)} {ctx : CompilerCtx s1 s2}
    {bl : Binding (((s2,,Kind.cvar),,Kind.cvar),,Kind.var) Kind.lock} {Y0 : BVar s2 .cvar}
    (h : CapyTy.TgtCvarOccurs (E.rename Rename.implicit_cvar)
      (((ctx.weakenTarget.weakenTarget.weakenTarget.consCVar
          (CapyCaptureBound.unbound Mutability.epsilon)
          (BVar.there (BVar.there BVar.here))).consVar T1 (some BVar.here)
        (CaptureSet.cvar (.M .epsilon) (BVar.there BVar.here))).weakenTarget bl)
      (BVar.there (BVar.there (BVar.there (BVar.there Y0))))) :
    CapyTy.TgtCvarOccurs (CapyTy.arrow T1 cs E) ctx Y0 := by
  obtain ⟨c, hlk, hfree⟩ := h
  cases c with
  | there c1 =>
    cases c1 with
    | here =>
      have hlk2 : (BVar.there (BVar.there (BVar.there BVar.here)) :
          BVar ((((s2,,Kind.cvar),,Kind.cvar),,Kind.var),,Kind.lock) .cvar)
          = BVar.there (BVar.there (BVar.there (BVar.there Y0))) := hlk
      simp at hlk2
    | there c0 =>
      refine ⟨c0, ?_, ?_⟩
      · have hlk' : ((((((ctx.srcCtx.rename Rename.succ).rename Rename.succ).rename
              Rename.succ).rename Rename.succ).lookupCVar c0))
            = BVar.there (BVar.there (BVar.there (BVar.there Y0))) := hlk
        rw [SrcCtx.lookupCVar_rename, SrcCtx.lookupCVar_rename, SrcCtx.lookupCVar_rename,
          SrcCtx.lookupCVar_rename] at hlk'
        exact BVar.there.inj (BVar.there.inj (BVar.there.inj (BVar.there.inj hlk')))
      · rcases hfree with hE | hΓ
        · obtain ⟨c', hc'eq, hc'free⟩ := CapyTy.SrcCvarFree.rename_inv E hE
          cases c' with
          | there c'' =>
            have hc'eq' : BVar.there (BVar.there c'')
                = BVar.there (BVar.there c0) := hc'eq
            have : c'' = c0 := BVar.there.inj (BVar.there.inj hc'eq')
            subst this
            exact Or.inl (Or.inr (Or.inr hc'free))
        · refine ?_
          rcases (CapyCtx.srcCvarFree_there_push (b := CapyBinding.var T1)).mp hΓ with hb | hrest
          · exact Or.inl (Or.inl hb)
          · rcases (CapyCtx.srcCvarFree_there_push (b :=
              CapyBinding.cvar CapyAuthority.access_only
                (CapyCaptureBound.unbound Mutability.epsilon))).mp hrest with hb2 | hrest2
            · exact absurd hb2 id
            · exact Or.inr hrest2

/-- **Forward-dispatch bridge (`poly`).**  A stable cvar-atom `.there Y0` of the compiled
    lock peak-set traces (`compile_cvar_subset_inv_resource` → `cvarMem_peaks`) to a source
    cvar `d` free in `cs` or the context, whose target image is `Y0`; hence it occurs for
    `poly S cs E`.  Serves as the `hP` for `.liftTVar` at the `poly` `sat`-case feed. -/
theorem CapyTy.tgtCvarOccurs_bridge_poly {s1 s2 : Sig} {S : CapyTy .capt s1}
    {cs : CapyCaptureSet s1} {E : CapyTy .exi (s1,X)} {ctx : CompilerCtx s1 s2}
    (hΓnp : ctx.capyCtx.NoPseudoPeak) (hcsnp : cs.NoPseudoPeak) (Y0 : BVar s2 .cvar)
    (h : ∃ m, CaptureSet.Subset (CaptureSet.cvar m (BVar.there Y0))
      (CapyCaptureSet.compile (CapyCaptureSet.peaks ctx.capyCtx cs)
        (ctx.srcCtx.weaken (k := Kind.tvar)))) :
    CapyTy.TgtCvarOccurs (CapyTy.poly S cs E) ctx Y0 := by
  obtain ⟨m, hsub⟩ := h
  obtain ⟨d, hlkd, hsubd⟩ := CapyCaptureSet.compile_cvar_subset_inv_resource
    (CapyCaptureSet.peaks_peaksOnly _ _) (CapyCaptureSet.peaks_noPseudoPeak hΓnp hcsnp) hsub
  have hlkeq : ctx.srcCtx.lookupCVar d = Y0 := by
    have hlkd' : (ctx.srcCtx.rename Rename.succ).lookupCVar d = BVar.there Y0 := hlkd
    rw [SrcCtx.lookupCVar_rename] at hlkd'
    exact BVar.there.inj hlkd'
  have hmem := CapyCaptureSet.cvarMem_of_subset_cvar hsubd
  rcases CapyCaptureSet.cvarMem_peaks ctx.capyCtx cs hmem with hcs | hΓ
  · exact ⟨d, hlkeq, Or.inl (Or.inr (Or.inl hcs))⟩
  · exact ⟨d, hlkeq, Or.inr hΓ⟩

/-- **Forward-dispatch bridge (`cpoly`).**  As `tgtCvarOccurs_bridge_poly`, for `cpoly cb cs E`
    (lock feed via `.lift` at a cvar binder). -/
theorem CapyTy.tgtCvarOccurs_bridge_cpoly {s1 s2 : Sig} {cb : CapyCaptureBound s1}
    {cs : CapyCaptureSet s1} {E : CapyTy .exi (s1,C)} {ctx : CompilerCtx s1 s2}
    (hΓnp : ctx.capyCtx.NoPseudoPeak) (hcsnp : cs.NoPseudoPeak) (Y0 : BVar s2 .cvar)
    (h : ∃ m, CaptureSet.Subset (CaptureSet.cvar m (BVar.there Y0))
      (CapyCaptureSet.compile (CapyCaptureSet.peaks ctx.capyCtx cs)
        (ctx.srcCtx.weaken (k := Kind.cvar)))) :
    CapyTy.TgtCvarOccurs (CapyTy.cpoly cb cs E) ctx Y0 := by
  obtain ⟨m, hsub⟩ := h
  obtain ⟨d, hlkd, hsubd⟩ := CapyCaptureSet.compile_cvar_subset_inv_resource
    (CapyCaptureSet.peaks_peaksOnly _ _) (CapyCaptureSet.peaks_noPseudoPeak hΓnp hcsnp) hsub
  have hlkeq : ctx.srcCtx.lookupCVar d = Y0 := by
    have hlkd' : (ctx.srcCtx.rename Rename.succ).lookupCVar d = BVar.there Y0 := hlkd
    rw [SrcCtx.lookupCVar_rename] at hlkd'
    exact BVar.there.inj hlkd'
  have hmem := CapyCaptureSet.cvarMem_of_subset_cvar hsubd
  rcases CapyCaptureSet.cvarMem_peaks ctx.capyCtx cs hmem with hcs | hΓ
  · exact ⟨d, hlkeq, Or.inl (Or.inr (Or.inl hcs))⟩
  · exact ⟨d, hlkeq, Or.inr hΓ⟩

/-- **Forward-dispatch bridge (`arrow`).**  The arrow modal body's lock separates over the
    domain-lock capture set `W = (cs.rename succ).rename succ ∪ {param}` in the lock context
    `ctxLockOrig`.  A stable cvar-atom `.there³ Y0` of `compile (peaks Γ_L W) sc_L` traces to a
    source cvar `d = .there (.there d0)`, whose `cs`-membership (or lock-context freeness through
    the domain-param binder `T1`) makes it occur for `arrow T1 cs E` at `Y0`.  The genuine
    lock-shape arithmetic.  Serves as the innermost `.lift` `hP` at the arrow `sat`-case feed. -/
theorem CapyTy.tgtCvarOccurs_bridge_arrow {s1 s2 : Sig} {T1 : CapyTy .capt (s1,C)}
    {cs : CapyCaptureSet s1} {E : CapyTy .exi (s1,x)} {ctx : CompilerCtx s1 s2}
    (hΓnp : ctx.capyCtx.NoPseudoPeak) (hT1csnp : T1.captureSet.NoPseudoPeak)
    (hWnp : (((cs.rename (Rename.succ (k := Kind.cvar))).rename (Rename.succ (k := Kind.var)))
        ∪ CapyCaptureSet.var (.M .epsilon) (.bound BVar.here)).NoPseudoPeak)
    (Y0 : BVar s2 .cvar)
    (h : ∃ m, CaptureSet.Subset
      (CaptureSet.cvar m (BVar.there (BVar.there (BVar.there Y0))))
      (CapyCaptureSet.compile
        (CapyCaptureSet.peaks
          ((ctx.weakenTarget.weakenTarget.weakenTarget.consCVar
              (CapyCaptureBound.unbound Mutability.epsilon)
              (BVar.there (BVar.there BVar.here))).consVar T1 (some BVar.here)
            (CaptureSet.cvar (.M .epsilon) (BVar.there BVar.here))).capyCtx
          (((cs.rename Rename.succ).rename Rename.succ)
            ∪ CapyCaptureSet.var (.M .epsilon) (.bound BVar.here)))
        ((ctx.weakenTarget.weakenTarget.weakenTarget.consCVar
            (CapyCaptureBound.unbound Mutability.epsilon)
            (BVar.there (BVar.there BVar.here))).consVar T1 (some BVar.here)
          (CaptureSet.cvar (.M .epsilon) (BVar.there BVar.here))).srcCtx)) :
    CapyTy.TgtCvarOccurs (CapyTy.arrow T1 cs E) ctx Y0 := by
  obtain ⟨m, hsub⟩ := h
  have hΓLnp : ((ctx.capyCtx.push_cvar_default
      (CapyCaptureBound.unbound Mutability.epsilon)).push_var T1).NoPseudoPeak :=
    ⟨hΓnp, hT1csnp⟩
  obtain ⟨d, hlkd, hsubd⟩ := CapyCaptureSet.compile_cvar_subset_inv_resource
    (CapyCaptureSet.peaks_peaksOnly _ _) (CapyCaptureSet.peaks_noPseudoPeak hΓLnp hWnp) hsub
  have hmem := CapyCaptureSet.cvarMem_of_subset_cvar hsubd
  cases d with
  | there d1 =>
    cases d1 with
    | here =>
      have hlk2 : (BVar.there (BVar.there BVar.here) :
          BVar (((s2,,Kind.cvar),,Kind.cvar),,Kind.var) .cvar)
          = BVar.there (BVar.there (BVar.there Y0)) := hlkd
      simp at hlk2
    | there d0 =>
      have hlkeq : ctx.srcCtx.lookupCVar d0 = Y0 := by
        have hlkd' : (((ctx.srcCtx.rename Rename.succ).rename Rename.succ).rename
            Rename.succ).lookupCVar d0 = BVar.there (BVar.there (BVar.there Y0)) := hlkd
        rw [SrcCtx.lookupCVar_rename, SrcCtx.lookupCVar_rename, SrcCtx.lookupCVar_rename] at hlkd'
        exact BVar.there.inj (BVar.there.inj (BVar.there.inj hlkd'))
      rcases CapyCaptureSet.cvarMem_peaks _ _ hmem with hW | hΓ
      · simp only [CapyCaptureSet.CvarMem, or_false] at hW
        obtain ⟨d', hd'eq, hd'mem⟩ := CapyCaptureSet.CvarMem.rename_inv hW
        have hd'eq2 : BVar.there d' = BVar.there (BVar.there d0) := hd'eq
        have hd'e : d' = BVar.there d0 := BVar.there.inj hd'eq2
        subst hd'e
        obtain ⟨d'', hd''eq, hd''mem⟩ := CapyCaptureSet.CvarMem.rename_inv hd'mem
        have hd''eq2 : BVar.there d'' = BVar.there d0 := hd''eq
        have hd''e : d'' = d0 := BVar.there.inj hd''eq2
        exact ⟨d0, hlkeq, Or.inl (Or.inr (Or.inl (hd''e ▸ hd''mem)))⟩
      · rcases (CapyCtx.srcCvarFree_there_push (b := CapyBinding.var T1)).mp hΓ with hb | hrest
        · exact ⟨d0, hlkeq, Or.inl (Or.inl hb)⟩
        · rcases (CapyCtx.srcCvarFree_there_push (b :=
            CapyBinding.cvar CapyAuthority.access_only
              (CapyCaptureBound.unbound Mutability.epsilon))).mp hrest with hb2 | hrest2
          · exact absurd hb2 id
          · exact ⟨d0, hlkeq, Or.inr hrest2⟩

/-- **Type-level capture-opening commutes up to subtyping, both directions.**
    Stated `∀`-after-`T` (over the substitution data + contexts) so the recursive
    cases re-instantiate at lifted substitutions / extended contexts. -/
theorem CapyTy.compile_subst_subtyp {sort : CapyTySort} (T : CapyTy sort s1) :
    ∀ {s2 s1' s2' : Sig} {ctxOrig : CompilerCtx s1 s2} {ctxSub : CompilerCtx s1' s2'}
      {σ : CapySubst s1 s1'} {σt : Subst s2 s2'},
      SubstCompat ctxSub.srcCtx ctxOrig.srcCtx σ σt →
      SubstTvarCompat ctxSub.srcCtx ctxOrig.srcCtx σ σt → T.IsClosed → CapyTy.PureBounds T →
      TgtSplitCoveredOn (CapyTy.TgtCvarOccurs T ctxOrig) ctxSub.coreCtx σt →
      SubstCompat (SrcCtx.realign ctxSub.capyCtx ctxSub.srcCtx)
        (SrcCtx.realign ctxOrig.capyCtx ctxOrig.srcCtx) σ σt →
      ctxSub.capyCtx.IsClosed → ctxOrig.capyCtx.IsClosed →
      Subst.IsClosed σt →
      ctxSub.srcCtx.VarsClosed → ctxOrig.srcCtx.VarsClosed →
      ctxSub.coreCtx.IsClosed →
      CapySubst.IsClosed σ →
      ctxSub.srcCtx.CVarInjective →
      (hiso : PeakSubstIso σ) →
      ctxOrig.capyCtx.NoPseudoPeak →
      T.NoPseudoPeak →
      ctxOrig.capyCtx.SubstsTo ctxSub.capyCtx σ →
      hiso.StablePreserving ctxOrig.capyCtx ctxSub.capyCtx →
      Subtyp ctxSub.coreCtx (CapyTy.compile (T.subst σ) ctxSub)
        ((CapyTy.compile T ctxOrig).subst σt) ∧
      Subtyp ctxSub.coreCtx ((CapyTy.compile T ctxOrig).subst σt)
        (CapyTy.compile (T.subst σ) ctxSub) := by
  match T with
  | .top =>
    intro s2 s1' s2' ctxOrig ctxSub σ σt hcompat htvar hcl hpb hdrop hcompatAl hclSub hclOrig
      hscl hvcSub hvcOrig hcoreSub hscS hinj hiso horig hTnp hsubsto hstab
    simp only [CapyTy.subst, CapyTy.compile, Ty.subst]
    exact ⟨Subtyp.refl, Subtyp.refl⟩
  | .unit =>
    intro s2 s1' s2' ctxOrig ctxSub σ σt hcompat htvar hcl hpb hdrop hcompatAl hclSub hclOrig
      hscl hvcSub hvcOrig hcoreSub hscS hinj hiso horig hTnp hsubsto hstab
    simp only [CapyTy.subst, CapyTy.compile, Ty.subst]
    exact ⟨Subtyp.refl, Subtyp.refl⟩
  | .bool =>
    intro s2 s1' s2' ctxOrig ctxSub σ σt hcompat htvar hcl hpb hdrop hcompatAl hclSub hclOrig
      hscl hvcSub hvcOrig hcoreSub hscS hinj hiso horig hTnp hsubsto hstab
    simp only [CapyTy.subst, CapyTy.compile, Ty.subst]
    exact ⟨Subtyp.refl, Subtyp.refl⟩
  | .cap cs =>
    intro s2 s1' s2' ctxOrig ctxSub σ σt hcompat htvar hcl hpb hdrop hcompatAl hclSub hclOrig
      hscl hvcSub hvcOrig hcoreSub hscS hinj hiso horig hTnp hsubsto hstab
    cases hcl with | cap hcs =>
    rw [CapyTy.compile_subst_cap hcompat hcs]
    exact ⟨Subtyp.refl, Subtyp.refl⟩
  | .cell cs m =>
    intro s2 s1' s2' ctxOrig ctxSub σ σt hcompat htvar hcl hpb hdrop hcompatAl hclSub hclOrig
      hscl hvcSub hvcOrig hcoreSub hscS hinj hiso horig hTnp hsubsto hstab
    cases hcl with | cell hcs =>
    rw [CapyTy.compile_subst_cell hcompat hcs]
    exact ⟨Subtyp.refl, Subtyp.refl⟩
  | .typ T1 =>
    intro s2 s1' s2' ctxOrig ctxSub σ σt hcompat htvar hcl hpb hdrop hcompatAl hclSub hclOrig
      hscl hvcSub hvcOrig hcoreSub hscS hinj hiso horig hTnp hsubsto hstab
    cases hcl with | typ hcl1 =>
    simp only [CapyTy.subst, CapyTy.compile, Ty.subst]
    obtain ⟨hle, hge⟩ := CapyTy.compile_subst_subtyp T1 hcompat htvar hcl1 hpb hdrop hcompatAl
      hclSub hclOrig
      hscl hvcSub hvcOrig hcoreSub hscS hinj hiso horig hTnp hsubsto hstab
    exact ⟨Subtyp.typ hle, Subtyp.typ hge⟩
  | .exi T1 =>
    intro s2 s1' s2' ctxOrig ctxSub σ σt hcompat htvar hcl hpb hdrop hcompatAl hclSub hclOrig
      hscl hvcSub hvcOrig hcoreSub hscS hinj hiso horig hTnp hsubsto hstab
    cases hcl with | exi hcl1 =>
    simp only [CapyTy.subst, CapyTy.compile, Ty.subst]
    obtain ⟨hle, hge⟩ := CapyTy.compile_subst_subtyp T1
      (ctxOrig := ctxOrig.weakenTarget.consCVar (.unbound .epsilon) .here)
      (ctxSub := ctxSub.weakenTarget.consCVar (.unbound .epsilon) .here)
      (SubstCompat.weakenConsCVar hcompat) (SubstTvarCompat.weakenConsCVar htvar) hcl1 hpb
      (hdrop.lift (fun _ hh => CapyTy.tgtCvarOccurs_exi hh))
      (SubstCompat.realign_weakenConsCVar hcompatAl)
      (CapyCtx.IsClosed.push hclSub (CapyBinding.IsClosed.cvar CapyCaptureBound.IsClosed.unbound))
      (CapyCtx.IsClosed.push hclOrig (CapyBinding.IsClosed.cvar CapyCaptureBound.IsClosed.unbound))
      (Subst.lift_closed hscl) hvcSub.weaken.consCVar hvcOrig.weaken.consCVar
      (Ctx.IsClosed.push hcoreSub (Binding.IsClosed.cvar CaptureBound.IsClosed.unbound))
      (CapySubst.lift_closed hscS) (SrcCtx.CVarInjective.consCVarHere hinj) (hiso.lift Kind.cvar)
      horig hTnp hsubsto.consCVar (hstab.pushCVar (.unbound .epsilon))
    exact ⟨Subtyp.exi hle, Subtyp.exi hge⟩
  | .tvar X =>
    intro s2 s1' s2' ctxOrig ctxSub σ σt hcompat htvar hcl hpb hdrop hcompatAl hclSub hclOrig
      hscl hvcSub hvcOrig hcoreSub hscS hinj hiso horig hTnp hsubsto hstab
    obtain ⟨Z, hZ, hlk⟩ := htvar X
    simp only [CapyTy.subst, hZ, CapyPureTy.tvar, CapyTy.compile, Ty.subst, hlk, PureTy.tvar]
    exact ⟨Subtyp.refl, Subtyp.refl⟩
  | .arrow T1 cs E =>
    intro s2 s1' s2' ctxOrig ctxSub σ σt hcompat htvar hcl hpb hdrop hcompatAl hclSub hclOrig
      hscl hvcSub hvcOrig hcoreSub hscS hinj hiso horig hTnp hsubsto hstab
    -- ★ REMAINING — large MECHANICAL assembly, NO design gap (the K1/merging-lock blocker is
    -- gone; the dispatch machinery `compile_peakSepCtx_sep_forward`/`_backward` + the `cpoly`/
    -- `poly` cases prove there is no obstruction).  `arrow T cs E` compiles to a
    -- `cpoly .unbound {} (typ (cpoly (bound ⟦T.captureSet⟧) {} (typ (arrow ⟦Tdom⟧ {}
    --   (typ (modal ⟦W⟧ Ψ ⟦E⟧))))))` nest with `Tdom = (T.rename succ).refineCaptureSet {x}`,
    -- `W = (cs.rename succ).rename succ ∪ {param}`.  Forward = `Subtyp.cpoly Subbound.refl` (outer)
    -- / inner `Subtyp.cpoly (Subbound.capset (heq ▸ Subcapt.refl))` with `heq` via
    -- `captureSet_subst hlifttv` + `compile_subst (SubstCompat.weakenConsCVar hcompat)` / then
    -- `Subtyp.arrow ?dom {} ?body`.  `?dom` (contravariant) is now a RECURSIVE SELF-CALL
    -- `(CapyTy.compile_subst_subtyp Tdom …).2` — REACHABLE because `tySize Tdom = tySize T <
    -- tySize (arrow …)` under the well-founded recursion (this whole proof was converted from
    -- `induction T` to `match T` + `termination_by tySize T` specifically to unlock this).  The
    -- naturality `Tdom.subst σ.lift.lift = ((T.subst σ.lift).rename succ).refineCaptureSet {x}`
    -- holds via `CapyTy.refineCaptureSet_subst hlift2tv` + `weaken_subst_comm_base`.  `?body` is
    -- the `W`-based modal lock, discharged by the SAME extracted dispatch at `cs := W`.  Backward
    -- mirrors.  The ONLY thing still to BUILD is a handful of context-premise lemmas for the
    -- `arrow`-domain shape `consVar ∘ consCVar(.there .here) ∘ weakenTarget²` — mirrors of the
    -- existing cvar/tvar builders: `SubstTvarCompat.consVar`/`.consCVar`, `SrcAligned.consVar`,
    -- `CapyCtx.SubstsTo.consVar`.  All other premises compose
    -- from `SubstCompat.consVar`/`.consCVar` (general, already exist) + `weakenTarget`.
    cases hcl with | arrow hT1Cl hcsCl hECl =>
    obtain ⟨hpbT1, hpbE⟩ := hpb
    obtain ⟨hT1np, hcsnp, hEnp⟩ := hTnp
    simp only [CapyTy.subst, CapyTy.compile, Ty.subst]
    refine ⟨?_, ?_⟩
    · -- forward: ⟦(arrow T1 cs E)[σ]⟧ <: ⟦arrow T1 cs E⟧[σt]
      refine Subtyp.cpoly Subbound.refl ?_ (Subtyp.typ ?_)
      · simp only [CaptureSet.subst]; exact Subcapt.refl
      · refine Subtyp.cpoly (Subbound.capset ?_) ?_ (Subtyp.typ ?_)
        · -- inner bound: ⟦T1.cap⟧[σt.lift] <: ⟦(T1[σ.lift]).cap⟧  (an equality)
          have htv0 : ∀ X, ∃ Y, σ.tvar X = CapyPureTy.tvar Y :=
            fun X => let ⟨Z, hZ, _⟩ := htvar X; ⟨Z, hZ⟩
          have hlifttv : ∀ X, ∃ Y, (σ.lift (k := Kind.cvar)).tvar X = CapyPureTy.tvar Y := by
            intro X
            cases X with
            | there X0 =>
              obtain ⟨Y0, hY0⟩ := htv0 X0
              exact ⟨_, by rw [CapySubst.lift_there_tvar_eq, hY0]; rfl⟩
          have heq : CapyCaptureSet.compile (T1.subst σ.lift).captureSet
                (ctxSub.weakenTarget.consCVar (CapyCaptureBound.unbound Mutability.epsilon)
                  BVar.here).srcCtx
              = (CapyCaptureSet.compile T1.captureSet
                  (ctxOrig.weakenTarget.consCVar (CapyCaptureBound.unbound Mutability.epsilon)
                    BVar.here).srcCtx).subst (σt.lift (k := Kind.cvar)) := by
            rw [show (T1.subst σ.lift).captureSet = (T1.captureSet).subst σ.lift from
              CapyTy.captureSet_subst hlifttv]
            exact CapyCaptureSet.compile_subst (SubstCompat.weakenConsCVar hcompat)
              (CapyTy.IsClosed.captureSet hT1Cl)
          exact heq ▸ Subcapt.refl
        · simp only [CaptureSet.subst]; exact Subcapt.refl
        · refine Subtyp.arrow ?_ ?_ (Subtyp.typ ?_)
          · -- contravariant DOMAIN: the `.2` (backward) of a recursion on
            -- `Tdom = (T1.rename succ).refineCaptureSet {x}` at the re-abstracted `ctxDomain`,
            -- modulo naturality `Tdom.subst σ.lift.lift = ((T1.subst σ.lift).rename succ)
            -- .refineCaptureSet {x}` (`refineCaptureSet_subst` + `weaken_subst_comm_base`).
            -- ★ The former NoPseudoPeak blocker is GONE: the sub-side `hsubPure` premise was
            -- removed from `compile_subst_subtyp` (frozen-peak attribution now routes through the
            -- pseudo-free ORIGIN via `peaks_subst_pseudo_cvar`), so the recursion's only
            -- pseudo-freeness obligation is `ctxOrig_domain.capyCtx.NoPseudoPeak` — SATISFIABLE,
            -- `= ⟨horig (cvar push adds nothing), hT1np⟩` for the value-param var push.  What
            -- remains is the cpoly-style explicit-coreCtx CompilerCtx assembly + premise threading
            -- through the `consVar ∘ consCVar(.there .here) ∘ weakenTarget²` domain builders (all
            -- of which exist).  Purely mechanical.  See memory `project_capybara_arrow_resolution`.
            have htv0 : ∀ X, ∃ Y, σ.tvar X = CapyPureTy.tvar Y :=
              fun X => let ⟨Z, hZ, _⟩ := htvar X; ⟨Z, hZ⟩
            have hlift1tv : ∀ X, ∃ Y,
                (σ.lift (k := Kind.cvar)).tvar X = CapyPureTy.tvar Y := by
              intro X
              cases X with
              | there X0 =>
                obtain ⟨Y, hY⟩ := htv0 X0
                exact ⟨_, by rw [CapySubst.lift_there_tvar_eq, hY]; rfl⟩
            have hlift2tv : ∀ X, ∃ Y,
                ((σ.lift (k := Kind.cvar)).lift (k := Kind.var)).tvar X = CapyPureTy.tvar Y := by
              intro X
              cases X with
              | there X0 =>
                cases X0 with
                | there X1 =>
                  obtain ⟨Y, hY⟩ := htv0 X1
                  exact ⟨_, by
                    rw [CapySubst.lift_there_tvar_eq, CapySubst.lift_there_tvar_eq, hY]; rfl⟩
            have ha : (T1.rename Rename.succ).subst
                  ((σ.lift (k := Kind.cvar)).lift (k := Kind.var))
                = (T1.subst σ.lift).rename Rename.succ :=
              CapyTy.weaken_subst_comm_base.symm
            have hnat : ((T1.rename Rename.succ).refineCaptureSet
                  (CapyCaptureSet.var (.M .epsilon) (.bound .here))).subst
                  ((σ.lift (k := Kind.cvar)).lift (k := Kind.var))
                = ((T1.subst σ.lift).rename Rename.succ).refineCaptureSet
                  (CapyCaptureSet.var (.M .epsilon) (.bound .here)) := by
              have hrcs := CapyTy.refineCaptureSet_subst (T := T1.rename Rename.succ)
                (cs := CapyCaptureSet.var (.M .epsilon) (.bound .here))
                (σ := (σ.lift (k := Kind.cvar)).lift (k := Kind.var)) hlift2tv
              rw [hrcs, ha]
              rfl
            set rDsub :=
              (ctxSub.weakenTarget.weakenTarget.consCVar
                  (CapyCaptureBound.unbound Mutability.epsilon)
                  (BVar.there BVar.here)).consVar (T1.subst σ.lift) none
                  (CaptureSet.cvar (.M .epsilon) BVar.here) with hrDsub
            set ctxDsub : CompilerCtx _ _ := ⟨rDsub.capyCtx, rDsub.srcCtx, rDsub.dstCtx,
                Ctx.push_cvar
                  (Ctx.push_cvar ctxSub.coreCtx Authority.access_only
                    (CaptureBound.unbound.subst σt))
                  Authority.access_only
                  ((CaptureBound.bound (CapyCaptureSet.compile T1.captureSet
                    (ctxOrig.weakenTarget.consCVar (CapyCaptureBound.unbound Mutability.epsilon)
                      BVar.here).srcCtx)).subst (σt.lift (k := Kind.cvar)))⟩ with hctxDsub
            have hrec := (CapyTy.compile_subst_subtyp
              ((T1.rename Rename.succ).refineCaptureSet
                (CapyCaptureSet.var (.M .epsilon) (.bound .here)))
              (ctxSub := ctxDsub)
              (ctxOrig := (ctxOrig.weakenTarget.weakenTarget.consCVar
                  (CapyCaptureBound.unbound Mutability.epsilon)
                  (BVar.there BVar.here)).consVar T1 none
                  (CaptureSet.cvar (.M .epsilon) BVar.here))
              (σ := (σ.lift (k := Kind.cvar)).lift (k := Kind.var))
              (σt := (σt.lift (k := Kind.cvar)).lift (k := Kind.cvar))
              (((hcompat.weakenTarget.weakenTarget).consCVar rfl).consVar rfl)
              ((htvar.weakenTarget.weakenTarget).consCVar).consVar
              (CapyTy.IsClosed.refineCaptureSet (CapyTy.IsClosed.rename hT1Cl Rename.succ)
                CapyCaptureSet.IsClosed.var_bound)
              (CapyTy.PureBounds.refineCaptureSet (CapyTy.PureBounds.rename Rename.succ hpbT1))
              (hdrop.liftShift2 (fun _ hh => CapyTy.tgtCvarOccurs_arrow_dom hh))
              ((hcompatAl.realign_weakenConsCVar.realign_weakenTarget).realign_consVar
                hlift1tv hT1Cl)
              (CapyCtx.IsClosed.push
                (CapyCtx.IsClosed.push hclSub
                  (CapyBinding.IsClosed.cvar CapyCaptureBound.IsClosed.unbound))
                (CapyBinding.IsClosed.var
                  (CapyTy.is_closed_subst hT1Cl (CapySubst.lift_closed hscS))))
              (CapyCtx.IsClosed.push
                (CapyCtx.IsClosed.push hclOrig
                  (CapyBinding.IsClosed.cvar CapyCaptureBound.IsClosed.unbound))
                (CapyBinding.IsClosed.var hT1Cl))
              (Subst.lift_closed (Subst.lift_closed hscl))
              (((hvcSub.weaken).weaken).consCVar.consVar CaptureSet.IsClosed.cvar)
              (((hvcOrig.weaken).weaken).consCVar.consVar CaptureSet.IsClosed.cvar)
              (Ctx.IsClosed.push
                (Ctx.IsClosed.push hcoreSub
                  (Binding.IsClosed.cvar CaptureBound.IsClosed.unbound))
                (Binding.IsClosed.cvar
                  (CaptureBound.IsClosed.bound
                    (CaptureSet.is_closed_subst
                      (CapyCaptureSet.compile_isClosed (CapyTy.IsClosed.captureSet hT1Cl)
                        hvcOrig.weaken.consCVar)
                      (Subst.lift_closed hscl)))))
              (CapySubst.lift_closed (CapySubst.lift_closed hscS))
              (SrcCtx.CVarInjective.consVar (SrcCtx.CVarInjective.consCVarThereHere hinj))
              ((hiso.lift Kind.cvar).lift Kind.var)
              ⟨horig, hT1np.captureSet⟩
              (CapyTy.NoPseudoPeak.refineCaptureSet (CapyTy.NoPseudoPeak.rename Rename.succ hT1np)
                CapyCaptureSet.NoPseudoPeak.var)
              ((hsubsto.consCVar).consVar hlift1tv)
              ((hstab.pushCVar (.unbound .epsilon)).pushVar T1 (T1.subst σ.lift))).2
            have hbridge : CapyTy.compile
                  (((T1.rename Rename.succ).refineCaptureSet
                      (CapyCaptureSet.var (.M .epsilon) (.bound .here))).subst
                    ((σ.lift (k := Kind.cvar)).lift (k := Kind.var))) ctxDsub
                = CapyTy.compile
                  (((T1.subst σ.lift).rename Rename.succ).refineCaptureSet
                    (CapyCaptureSet.var (.M .epsilon) (.bound .here))) rDsub :=
              (CapyTy.compile_eq_of _ ctxDsub rDsub
                ⟨⟨fun _ => rfl, fun _ => rfl, fun _ => rfl⟩,
                 fun _ => rfl, fun _ => Iff.rfl⟩).trans
                (congrArg (fun Z => CapyTy.compile Z rDsub) hnat)
            exact hbridge ▸ hrec
          · simp only [CaptureSet.subst]; exact Subcapt.refl
          · -- modal BODY (W-lock): mirrors the `cpoly` `case body`/`sat` at `ctxLock`/`ctxE` with
            -- `cs := W`.  No design gap (NoPseudoPeak blocker gone); mechanical.
            -- The source W capture (over the domain sig `(s1,C,x)`).
            set Wsrc : CapyCaptureSet (s1,C,x) :=
              (cs.rename Rename.succ).rename Rename.succ
                ∪ CapyCaptureSet.var (.M .epsilon) (.bound .here) with hWsrc
            -- the `cs`-part subst/rename commutation (applied twice).
            have hcomm : ((cs.rename Rename.succ).rename Rename.succ).subst
                  ((σ.lift (k := Kind.cvar)).lift (k := Kind.var))
                = ((cs.subst σ).rename Rename.succ).rename Rename.succ := by
              have e1 : (cs.rename Rename.succ).subst (σ.lift (k := Kind.cvar))
                  = (cs.subst σ).rename Rename.succ :=
                (CapyCaptureSet.weaken_subst_comm_base (cs := cs) (σ := σ) (k := Kind.cvar)).symm
              have e2 : ((cs.rename Rename.succ).rename Rename.succ).subst
                    ((σ.lift (k := Kind.cvar)).lift (k := Kind.var))
                  = ((cs.rename Rename.succ).subst (σ.lift (k := Kind.cvar))).rename Rename.succ :=
                (CapyCaptureSet.weaken_subst_comm_base (cs := cs.rename Rename.succ)
                  (σ := σ.lift (k := Kind.cvar)) (k := Kind.var)).symm
              rw [e2, e1]
            -- naturality: `Wsrc[σ_lock]` is the goal's distributed sub-W.
            have hWnat : Wsrc.subst ((σ.lift (k := Kind.cvar)).lift (k := Kind.var))
                = ((cs.subst σ).rename Rename.succ).rename Rename.succ
                  ∪ CapyCaptureSet.var (.M .epsilon) (.bound .here) := by
              rw [hWsrc]; simp only [CapyCaptureSet.subst]; congr 1
            -- the lock-level compiler contexts (sub / orig).
            set ctxLockSub :=
              (ctxSub.weakenTarget.weakenTarget.weakenTarget.consCVar
                  (CapyCaptureBound.unbound Mutability.epsilon)
                  (BVar.there (BVar.there BVar.here))).consVar (T1.subst σ.lift) (some BVar.here)
                (CaptureSet.cvar (Access.M Mutability.epsilon) (BVar.there BVar.here))
              with hctxLockSub
            set ctxLockOrig :=
              (ctxOrig.weakenTarget.weakenTarget.weakenTarget.consCVar
                  (CapyCaptureBound.unbound Mutability.epsilon)
                  (BVar.there (BVar.there BVar.here))).consVar T1 (some BVar.here)
                (CaptureSet.cvar (Access.M Mutability.epsilon) (BVar.there BVar.here))
              with hctxLockOrig
            have hcLock : (((σt.lift (k := Kind.cvar)).lift (k := Kind.cvar)).lift
                  (k := Kind.var)).cvar (BVar.there (BVar.there BVar.here))
                = CaptureSet.cvar (.M .epsilon) (BVar.there (BVar.there BVar.here)) := rfl
            have hinvLock : (CaptureSet.cvar (.M .epsilon) (BVar.there BVar.here)).subst
                  (((σt.lift (k := Kind.cvar)).lift (k := Kind.cvar)).lift (k := Kind.var))
                = CaptureSet.cvar (.M .epsilon) (BVar.there BVar.here) := rfl
            have hcompatLock :=
              (((hcompat.weakenTarget (k := Kind.cvar)).weakenTarget (k := Kind.cvar)).weakenTarget
                  (k := Kind.var)).consCVar hcLock |>.consVar
                (bvS := some BVar.here) (bvO := some BVar.here) hinvLock
            have hWcl : Wsrc.IsClosed := by
              rw [hWsrc]
              exact CapyCaptureSet.IsClosed.union
                (CapyCaptureSet.rename_isClosed (CapyCaptureSet.rename_isClosed hcsCl))
                CapyCaptureSet.IsClosed.var_bound
            have hWf : CapyCaptureSet.compile
                  (((cs.subst σ).rename Rename.succ).rename Rename.succ
                    ∪ CapyCaptureSet.var (.M .epsilon) (.bound .here)) ctxLockSub.srcCtx
                = (CapyCaptureSet.compile Wsrc ctxLockOrig.srcCtx).subst
                  (((σt.lift (k := Kind.cvar)).lift (k := Kind.cvar)).lift (k := Kind.var)) := by
              rw [← hWnat]
              exact CapyCaptureSet.compile_subst hcompatLock hWcl
            have hvcLockSub : ctxLockSub.srcCtx.VarsClosed :=
              ((hvcSub.weaken.weaken.weaken).consCVar).consVar CaptureSet.IsClosed.cvar
            have hvcLockOrig : ctxLockOrig.srcCtx.VarsClosed :=
              ((hvcOrig.weaken.weaken.weaken).consCVar).consVar CaptureSet.IsClosed.cvar
            have hσt3 : Subst.IsClosed
                (((σt.lift (k := Kind.cvar)).lift (k := Kind.cvar)).lift (k := Kind.var)) :=
              Subst.lift_closed (Subst.lift_closed (Subst.lift_closed hscl))
            refine Subtyp.trans ?_ (Subtyp.modal (hWf ▸ Subcapt.refl) ?body)
              (Subtyp.modal_modal ?_ ?_ ?_ ?sat)
            · exact Ty.IsClosed.modal
                (CaptureSet.is_closed_subst
                  (CapyCaptureSet.compile_isClosed hWcl hvcLockOrig) hσt3)
                ⟨peakSepCtx_isClosed (CapyCaptureSet.peaks_isClosed _ _) hvcLockSub,
                  MutabilityCtx.IsClosed.empty⟩
                (Ty.is_closed_subst
                  (CapyTy.compile_isClosed (E.rename Rename.implicit_cvar) ctxLockOrig
                    (CapyTy.IsClosed.rename hECl Rename.implicit_cvar) hvcLockOrig)
                  hσt3)
            case body =>
              have htv0 : ∀ X, ∃ Y, σ.tvar X = CapyPureTy.tvar Y :=
                fun X => let ⟨Z, hZ, _⟩ := htvar X; ⟨Z, hZ⟩
              have hlift1tv : ∀ X, ∃ Y,
                  (σ.lift (k := Kind.cvar)).tvar X = CapyPureTy.tvar Y := by
                intro X
                cases X with
                | there X0 =>
                  obtain ⟨Y, hY⟩ := htv0 X0
                  exact ⟨_, by rw [CapySubst.lift_there_tvar_eq, hY]; rfl⟩
              have hclOrigW : ctxLockOrig.capyCtx.IsClosed :=
                CapyCtx.IsClosed.push (CapyCtx.IsClosed.push hclOrig
                  (CapyBinding.IsClosed.cvar CapyCaptureBound.IsClosed.unbound))
                  (CapyBinding.IsClosed.var hT1Cl)
              have hclSubW : ctxLockSub.capyCtx.IsClosed :=
                CapyCtx.IsClosed.push (CapyCtx.IsClosed.push hclSub
                  (CapyBinding.IsClosed.cvar CapyCaptureBound.IsClosed.unbound))
                  (CapyBinding.IsClosed.var
                    (CapyTy.is_closed_subst hT1Cl (CapySubst.lift_closed hscS)))
              have hinjW : ctxLockSub.srcCtx.CVarInjective :=
                SrcCtx.CVarInjective.consVar
                  (SrcCtx.CVarInjective.rename (SrcCtx.CVarInjective.rename
                    (SrcCtx.CVarInjective.consCVarHere hinj) Rename.injective_succ)
                    Rename.injective_succ)
              set ΨL : ModalCtx (s2',,Kind.cvar,,Kind.cvar,,Kind.var) :=
                { sep := peakSepCtx ctxLockSub.capyCtx (CapyCaptureSet.peakset ctxLockSub.capyCtx
                           (((cs.subst σ).rename Rename.succ).rename Rename.succ
                             ∪ CapyCaptureSet.var (.M .epsilon) (.bound .here)))
                         ctxLockSub.srcCtx,
                  mutability := MutabilityCtx.empty } with hΨL
              have hGbcl : ((ctxSub.coreCtx.push_cvar Authority.access_only
                    (CaptureBound.unbound.subst σt)).push_cvar Authority.access_only
                    ((CaptureBound.bound (CapyCaptureSet.compile T1.captureSet
                      (ctxOrig.weakenTarget.consCVar (CapyCaptureBound.unbound Mutability.epsilon)
                        BVar.here).srcCtx)).subst (σt.lift (k := Kind.cvar)))).push_var
                    ((CapyTy.compile ((T1.rename Rename.succ).refineCaptureSet
                        (CapyCaptureSet.var (.M .epsilon) (.bound .here)))
                      ((ctxOrig.weakenTarget.weakenTarget.consCVar
                          (CapyCaptureBound.unbound Mutability.epsilon)
                          (BVar.there BVar.here)).consVar T1 none
                        (CaptureSet.cvar (.M .epsilon) BVar.here))).subst
                      ((σt.lift (k := Kind.cvar)).lift (k := Kind.cvar))) |>.IsClosed :=
                Ctx.IsClosed.push
                  (Ctx.IsClosed.push
                    (Ctx.IsClosed.push hcoreSub
                      (Binding.IsClosed.cvar CaptureBound.IsClosed.unbound))
                    (Binding.IsClosed.cvar
                      (CaptureBound.IsClosed.bound
                        (CaptureSet.is_closed_subst
                          (CapyCaptureSet.compile_isClosed (CapyTy.IsClosed.captureSet hT1Cl)
                            hvcOrig.weaken.consCVar)
                          (Subst.lift_closed hscl)))))
                  (Binding.IsClosed.var
                    (Ty.is_closed_subst
                      (CapyTy.compile_isClosed
                        ((T1.rename Rename.succ).refineCaptureSet
                          (CapyCaptureSet.var (.M .epsilon) (.bound .here)))
                        ((ctxOrig.weakenTarget.weakenTarget.consCVar
                            (CapyCaptureBound.unbound Mutability.epsilon)
                            (BVar.there BVar.here)).consVar T1 none
                          (CaptureSet.cvar (.M .epsilon) BVar.here))
                        (CapyTy.IsClosed.refineCaptureSet
                          (CapyTy.IsClosed.rename hT1Cl Rename.succ)
                          CapyCaptureSet.IsClosed.var_bound)
                        ((hvcOrig.weaken.weaken.consCVar).consVar CaptureSet.IsClosed.cvar))
                      (Subst.lift_closed (Subst.lift_closed hscl))))
              set ctxSub'' : CompilerCtx (s1',C,,Kind.var)
                  ((s2',,Kind.cvar,,Kind.cvar,,Kind.var),,Kind.lock) :=
                ⟨ctxLockSub.capyCtx, ctxLockSub.srcCtx.rename Rename.succ,
                 (ctxLockSub.weakenTarget (Binding.lock ΨL)).dstCtx,
                 ((ctxSub.coreCtx.push_cvar Authority.access_only
                      (CaptureBound.unbound.subst σt)).push_cvar Authority.access_only
                      ((CaptureBound.bound (CapyCaptureSet.compile T1.captureSet
                        (ctxOrig.weakenTarget.consCVar (CapyCaptureBound.unbound Mutability.epsilon)
                          BVar.here).srcCtx)).subst (σt.lift (k := Kind.cvar)))).push_var
                      ((CapyTy.compile ((T1.rename Rename.succ).refineCaptureSet
                          (CapyCaptureSet.var (.M .epsilon) (.bound .here)))
                        ((ctxOrig.weakenTarget.weakenTarget.consCVar
                            (CapyCaptureBound.unbound Mutability.epsilon)
                            (BVar.there BVar.here)).consVar T1 none
                          (CaptureSet.cvar (.M .epsilon) BVar.here))).subst
                        ((σt.lift (k := Kind.cvar)).lift (k := Kind.cvar)))
                      |>.push_lock ΨL⟩ with hctxSub''
              set ctxOrig'' : CompilerCtx (s1,C,,Kind.var)
                  ((s2,,Kind.cvar,,Kind.cvar,,Kind.var),,Kind.lock) :=
                ⟨ctxLockOrig.capyCtx, ctxLockOrig.srcCtx.rename Rename.succ,
                 (ctxLockOrig.weakenTarget
                   (Binding.lock (⟨SepCtx.empty, MutabilityCtx.empty⟩ : ModalCtx _))).dstCtx,
                 ctxLockOrig.coreCtx.push_lock
                   (⟨SepCtx.empty, MutabilityCtx.empty⟩ : ModalCtx _)⟩ with hctxOrig''
              have hle := (CapyTy.compile_subst_subtyp (E.rename Rename.implicit_cvar)
                (ctxSub := ctxSub'') (ctxOrig := ctxOrig'')
                (σ := (σ.lift (k := Kind.cvar)).lift (k := Kind.var))
                (σt := (((σt.lift (k := Kind.cvar)).lift (k := Kind.cvar)).lift
                  (k := Kind.var)).lift (k := Kind.lock))
                hcompatLock.weakenTarget
                ((((htvar.weakenTarget.weakenTarget.weakenTarget).consCVar).consVar).weakenTarget)
                (CapyTy.IsClosed.rename hECl Rename.implicit_cvar)
                (CapyTy.PureBounds.rename Rename.implicit_cvar hpbE)
                (hdrop.liftShift4 (fun _ hh => CapyTy.tgtCvarOccurs_arrow_cod hh))
                ((((hcompatAl.realign_weakenTarget.realign_weakenTarget.realign_weakenTarget
                    ).realign_consCVar hcLock).realign_consVar hlift1tv
                    hT1Cl).realign_weakenTarget)
                hclSubW hclOrigW
                (Subst.lift_closed (Subst.lift_closed (Subst.lift_closed (Subst.lift_closed hscl))))
                hvcLockSub.weaken hvcLockOrig.weaken
                (Ctx.IsClosed.push hGbcl
                  (Binding.IsClosed.lock ⟨peakSepCtx_isClosed
                    (CapyCaptureSet.peaks_isClosed _ _) hvcLockSub,
                    MutabilityCtx.IsClosed.empty⟩))
                (CapySubst.lift_closed (CapySubst.lift_closed hscS))
                (SrcCtx.CVarInjective.rename hinjW Rename.injective_succ)
                ((hiso.lift Kind.cvar).lift Kind.var)
                ⟨horig, hT1np.captureSet⟩
                (CapyTy.NoPseudoPeak.rename Rename.implicit_cvar hEnp)
                ((hsubsto.consCVar).consVar hlift1tv)
                ((hstab.pushCVar (.unbound .epsilon)).pushVar T1 (T1.subst σ.lift))).1
              have heq1 : CapyTy.compile ((E.subst σ.lift).rename Rename.implicit_cvar) ctxSub''
                  = (CapyTy.compile ((E.subst σ.lift).rename Rename.implicit_cvar)
                      ctxLockSub).rename Rename.succ :=
                CapyTy.compile_rename ((E.subst σ.lift).rename Rename.implicit_cvar)
                  ctxLockSub ctxSub'' Rename.succ rfl rfl
              have heq2 : CapyTy.compile (E.rename Rename.implicit_cvar) ctxOrig''
                  = (CapyTy.compile (E.rename Rename.implicit_cvar) ctxLockOrig).rename
                      Rename.succ :=
                CapyTy.compile_rename (E.rename Rename.implicit_cvar) ctxLockOrig ctxOrig''
                  Rename.succ rfl rfl
              convert hle using 2
              · exact heq1.symm.trans
                  (congrArg (fun Z => CapyTy.compile Z ctxSub'')
                    CapyTy.implicit_cvar_subst_comm)
              · rw [heq2]; exact Ty.weaken_subst_comm_base
            · exact Ctx.IsClosed.push
                (Ctx.IsClosed.push
                  (Ctx.IsClosed.push hcoreSub
                    (Binding.IsClosed.cvar CaptureBound.IsClosed.unbound))
                  (Binding.IsClosed.cvar
                    (CaptureBound.IsClosed.bound
                      (CaptureSet.is_closed_subst
                        (CapyCaptureSet.compile_isClosed (CapyTy.IsClosed.captureSet hT1Cl)
                          hvcOrig.weaken.consCVar)
                        (Subst.lift_closed hscl)))))
                (Binding.IsClosed.var
                  (Ty.is_closed_subst
                    (CapyTy.compile_isClosed
                      ((T1.rename Rename.succ).refineCaptureSet
                        (CapyCaptureSet.var (.M .epsilon) (.bound .here)))
                      ((ctxOrig.weakenTarget.weakenTarget.consCVar
                          (CapyCaptureBound.unbound Mutability.epsilon)
                          (BVar.there BVar.here)).consVar T1 none
                        (CaptureSet.cvar (.M .epsilon) BVar.here))
                      (CapyTy.IsClosed.refineCaptureSet
                        (CapyTy.IsClosed.rename hT1Cl Rename.succ)
                        CapyCaptureSet.IsClosed.var_bound)
                      ((hvcOrig.weaken.weaken.consCVar).consVar CaptureSet.IsClosed.cvar))
                    (Subst.lift_closed (Subst.lift_closed hscl))))
            · exact ⟨peakSepCtx_isClosed (CapyCaptureSet.peaks_isClosed _ _) hvcLockSub,
                MutabilityCtx.IsClosed.empty⟩
            · exact ModalCtx.is_closed_subst
                ⟨peakSepCtx_isClosed (CapyCaptureSet.peaks_isClosed _ _) hvcLockOrig,
                  MutabilityCtx.IsClosed.empty⟩ hσt3
            case sat =>
              have htv0 : ∀ X, ∃ Y, σ.tvar X = CapyPureTy.tvar Y :=
                fun X => let ⟨Z, hZ, _⟩ := htvar X; ⟨Z, hZ⟩
              have hlift1tv : ∀ X, ∃ Y,
                  (σ.lift (k := Kind.cvar)).tvar X = CapyPureTy.tvar Y := by
                intro X
                cases X with
                | there X0 =>
                  obtain ⟨Y, hY⟩ := htv0 X0
                  exact ⟨_, by rw [CapySubst.lift_there_tvar_eq, hY]; rfl⟩
              have hlift2tv : ∀ X, ∃ Y,
                  ((σ.lift (k := Kind.cvar)).lift (k := Kind.var)).tvar X = CapyPureTy.tvar Y := by
                intro X
                cases X with
                | there X0 =>
                  obtain ⟨Y, hY⟩ := hlift1tv X0
                  exact ⟨_, by rw [CapySubst.lift_there_tvar_eq, hY]; rfl⟩
              have hclOrigW : ctxLockOrig.capyCtx.IsClosed :=
                CapyCtx.IsClosed.push (CapyCtx.IsClosed.push hclOrig
                  (CapyBinding.IsClosed.cvar CapyCaptureBound.IsClosed.unbound))
                  (CapyBinding.IsClosed.var hT1Cl)
              have hclSubW : ctxLockSub.capyCtx.IsClosed :=
                CapyCtx.IsClosed.push (CapyCtx.IsClosed.push hclSub
                  (CapyBinding.IsClosed.cvar CapyCaptureBound.IsClosed.unbound))
                  (CapyBinding.IsClosed.var
                    (CapyTy.is_closed_subst hT1Cl (CapySubst.lift_closed hscS)))
              have hWsubcl :
                  (Wsrc.subst ((σ.lift (k := Kind.cvar)).lift (k := Kind.var))).IsClosed :=
                CapyCaptureSet.is_closed_subst hWcl
                  (CapySubst.lift_closed (CapySubst.lift_closed hscS))
              have hWnp : Wsrc.NoPseudoPeak :=
                CapyCaptureSet.NoPseudoPeak.union
                  ((hcsnp.rename Rename.succ).rename Rename.succ)
                  CapyCaptureSet.NoPseudoPeak.var
              have hinjW : ctxLockSub.srcCtx.CVarInjective :=
                SrcCtx.CVarInjective.consVar
                  (SrcCtx.CVarInjective.rename (SrcCtx.CVarInjective.rename
                    (SrcCtx.CVarInjective.consCVarHere hinj) Rename.injective_succ)
                    Rename.injective_succ)
              apply Satisfy.satisfy
              · intro C m hmem
                simp only [ModalCtx.rename] at hmem
                simp only [MutabilityCtx.rename] at hmem
                cases hmem
              · intro C1 C2 hdist
                simp only [ModalCtx.rename] at hdist
                rw [← peakSepCtx_rename] at hdist
                have hdist2 : (peakSepCtx ctxLockSub.capyCtx
                      (CapyCaptureSet.peakset ctxLockSub.capyCtx
                        (Wsrc.subst ((σ.lift (k := Kind.cvar)).lift (k := Kind.var))))
                    (ctxLockSub.srcCtx.rename Rename.succ)).HasTwoDistinct C1 C2 :=
                  hWnat ▸ hdist
                exact compile_peakSepCtx_sep_forward_splitcov_realign hclOrigW hclSubW
                  ((hcompatAl.realign_weakenTarget.realign_weakenTarget.realign_weakenTarget
                      ).realign_consCVar hcLock |>.realign_consVar hlift1tv hT1Cl)
                  hWcl hWsubcl ⟨horig, hT1np.captureSet⟩ hWnp hinjW
                  ((hiso.lift Kind.cvar).lift Kind.var)
                  (CapySubst.lift_closed (CapySubst.lift_closed hscS))
                  hlift2tv
                  ((hsubsto.consCVar).consVar hlift1tv)
                  (hdrop.liftShift3 (fun _ hh =>
                    CapyTy.tgtCvarOccurs_bridge_arrow horig hT1np.captureSet hWnp _ hh))
                  ((hstab.pushCVar (.unbound .epsilon)).pushVar T1 (T1.subst σ.lift))
                  C1 C2 hdist2
    · -- backward: ⟦arrow T1 cs E⟧[σt] <: ⟦(arrow T1 cs E)[σ]⟧.  Structural mirror of forward.
      refine Subtyp.cpoly Subbound.refl ?_ (Subtyp.typ ?_)
      · simp only [CaptureSet.subst]; exact Subcapt.refl
      · refine Subtyp.cpoly (Subbound.capset ?_) ?_ (Subtyp.typ ?_)
        · -- inner bound (reversed): ⟦(T1[σ.lift]).cap⟧ <: ⟦T1.cap⟧[σt.lift]
          have htv0 : ∀ X, ∃ Y, σ.tvar X = CapyPureTy.tvar Y :=
            fun X => let ⟨Z, hZ, _⟩ := htvar X; ⟨Z, hZ⟩
          have hlifttv : ∀ X, ∃ Y, (σ.lift (k := Kind.cvar)).tvar X = CapyPureTy.tvar Y := by
            intro X
            cases X with
            | there X0 =>
              obtain ⟨Y0, hY0⟩ := htv0 X0
              exact ⟨_, by rw [CapySubst.lift_there_tvar_eq, hY0]; rfl⟩
          have heq : CapyCaptureSet.compile (T1.subst σ.lift).captureSet
                (ctxSub.weakenTarget.consCVar (CapyCaptureBound.unbound Mutability.epsilon)
                  BVar.here).srcCtx
              = (CapyCaptureSet.compile T1.captureSet
                  (ctxOrig.weakenTarget.consCVar (CapyCaptureBound.unbound Mutability.epsilon)
                    BVar.here).srcCtx).subst (σt.lift (k := Kind.cvar)) := by
            rw [show (T1.subst σ.lift).captureSet = (T1.captureSet).subst σ.lift from
              CapyTy.captureSet_subst hlifttv]
            exact CapyCaptureSet.compile_subst (SubstCompat.weakenConsCVar hcompat)
              (CapyTy.IsClosed.captureSet hT1Cl)
          exact heq ▸ Subcapt.refl
        · simp only [CaptureSet.subst]; exact Subcapt.refl
        · refine Subtyp.arrow ?_ ?_ (Subtyp.typ ?_)
          · -- contravariant DOMAIN: the `.1` (forward) of the `Tdom` recursion.
            have htv0 : ∀ X, ∃ Y, σ.tvar X = CapyPureTy.tvar Y :=
              fun X => let ⟨Z, hZ, _⟩ := htvar X; ⟨Z, hZ⟩
            have hlift1tv : ∀ X, ∃ Y,
                (σ.lift (k := Kind.cvar)).tvar X = CapyPureTy.tvar Y := by
              intro X
              cases X with
              | there X0 =>
                obtain ⟨Y, hY⟩ := htv0 X0
                exact ⟨_, by rw [CapySubst.lift_there_tvar_eq, hY]; rfl⟩
            have hlift2tv : ∀ X, ∃ Y,
                ((σ.lift (k := Kind.cvar)).lift (k := Kind.var)).tvar X = CapyPureTy.tvar Y := by
              intro X
              cases X with
              | there X0 =>
                cases X0 with
                | there X1 =>
                  obtain ⟨Y, hY⟩ := htv0 X1
                  exact ⟨_, by
                    rw [CapySubst.lift_there_tvar_eq, CapySubst.lift_there_tvar_eq, hY]; rfl⟩
            have ha : (T1.rename Rename.succ).subst
                  ((σ.lift (k := Kind.cvar)).lift (k := Kind.var))
                = (T1.subst σ.lift).rename Rename.succ :=
              CapyTy.weaken_subst_comm_base.symm
            have hnat : ((T1.rename Rename.succ).refineCaptureSet
                  (CapyCaptureSet.var (.M .epsilon) (.bound .here))).subst
                  ((σ.lift (k := Kind.cvar)).lift (k := Kind.var))
                = ((T1.subst σ.lift).rename Rename.succ).refineCaptureSet
                  (CapyCaptureSet.var (.M .epsilon) (.bound .here)) := by
              have hrcs := CapyTy.refineCaptureSet_subst (T := T1.rename Rename.succ)
                (cs := CapyCaptureSet.var (.M .epsilon) (.bound .here))
                (σ := (σ.lift (k := Kind.cvar)).lift (k := Kind.var)) hlift2tv
              rw [hrcs, ha]
              rfl
            set rDsub :=
              (ctxSub.weakenTarget.weakenTarget.consCVar
                  (CapyCaptureBound.unbound Mutability.epsilon)
                  (BVar.there BVar.here)).consVar (T1.subst σ.lift) none
                  (CaptureSet.cvar (.M .epsilon) BVar.here) with hrDsub
            set ctxDsub : CompilerCtx _ _ := ⟨rDsub.capyCtx, rDsub.srcCtx, rDsub.dstCtx,
                Ctx.push_cvar
                  (Ctx.push_cvar ctxSub.coreCtx Authority.access_only
                    CaptureBound.unbound)
                  Authority.access_only
                  (CaptureBound.bound (CapyCaptureSet.compile (T1.subst σ.lift).captureSet
                    (ctxSub.weakenTarget.consCVar (CapyCaptureBound.unbound Mutability.epsilon)
                      BVar.here).srcCtx))⟩ with hctxDsub
            have hrec := (CapyTy.compile_subst_subtyp
              ((T1.rename Rename.succ).refineCaptureSet
                (CapyCaptureSet.var (.M .epsilon) (.bound .here)))
              (ctxSub := ctxDsub)
              (ctxOrig := (ctxOrig.weakenTarget.weakenTarget.consCVar
                  (CapyCaptureBound.unbound Mutability.epsilon)
                  (BVar.there BVar.here)).consVar T1 none
                  (CaptureSet.cvar (.M .epsilon) BVar.here))
              (σ := (σ.lift (k := Kind.cvar)).lift (k := Kind.var))
              (σt := (σt.lift (k := Kind.cvar)).lift (k := Kind.cvar))
              (((hcompat.weakenTarget.weakenTarget).consCVar rfl).consVar rfl)
              ((htvar.weakenTarget.weakenTarget).consCVar).consVar
              (CapyTy.IsClosed.refineCaptureSet (CapyTy.IsClosed.rename hT1Cl Rename.succ)
                CapyCaptureSet.IsClosed.var_bound)
              (CapyTy.PureBounds.refineCaptureSet (CapyTy.PureBounds.rename Rename.succ hpbT1))
              (hdrop.liftShift2 (fun _ hh => CapyTy.tgtCvarOccurs_arrow_dom hh))
              ((hcompatAl.realign_weakenConsCVar.realign_weakenTarget).realign_consVar
                hlift1tv hT1Cl)
              (CapyCtx.IsClosed.push
                (CapyCtx.IsClosed.push hclSub
                  (CapyBinding.IsClosed.cvar CapyCaptureBound.IsClosed.unbound))
                (CapyBinding.IsClosed.var
                  (CapyTy.is_closed_subst hT1Cl (CapySubst.lift_closed hscS))))
              (CapyCtx.IsClosed.push
                (CapyCtx.IsClosed.push hclOrig
                  (CapyBinding.IsClosed.cvar CapyCaptureBound.IsClosed.unbound))
                (CapyBinding.IsClosed.var hT1Cl))
              (Subst.lift_closed (Subst.lift_closed hscl))
              (((hvcSub.weaken).weaken).consCVar.consVar CaptureSet.IsClosed.cvar)
              (((hvcOrig.weaken).weaken).consCVar.consVar CaptureSet.IsClosed.cvar)
              (Ctx.IsClosed.push
                (Ctx.IsClosed.push hcoreSub
                  (Binding.IsClosed.cvar CaptureBound.IsClosed.unbound))
                (Binding.IsClosed.cvar
                  (CaptureBound.IsClosed.bound
                    (CapyCaptureSet.compile_isClosed
                      (CapyTy.IsClosed.captureSet
                        (CapyTy.is_closed_subst hT1Cl (CapySubst.lift_closed hscS)))
                      hvcSub.weaken.consCVar))))
              (CapySubst.lift_closed (CapySubst.lift_closed hscS))
              (SrcCtx.CVarInjective.consVar (SrcCtx.CVarInjective.consCVarThereHere hinj))
              ((hiso.lift Kind.cvar).lift Kind.var)
              ⟨horig, hT1np.captureSet⟩
              (CapyTy.NoPseudoPeak.refineCaptureSet (CapyTy.NoPseudoPeak.rename Rename.succ hT1np)
                CapyCaptureSet.NoPseudoPeak.var)
              ((hsubsto.consCVar).consVar hlift1tv)
              ((hstab.pushCVar (.unbound .epsilon)).pushVar T1 (T1.subst σ.lift))).1
            have hbridge : CapyTy.compile
                  (((T1.rename Rename.succ).refineCaptureSet
                      (CapyCaptureSet.var (.M .epsilon) (.bound .here))).subst
                    ((σ.lift (k := Kind.cvar)).lift (k := Kind.var))) ctxDsub
                = CapyTy.compile
                  (((T1.subst σ.lift).rename Rename.succ).refineCaptureSet
                    (CapyCaptureSet.var (.M .epsilon) (.bound .here))) rDsub :=
              (CapyTy.compile_eq_of _ ctxDsub rDsub
                ⟨⟨fun _ => rfl, fun _ => rfl, fun _ => rfl⟩,
                 fun _ => rfl, fun _ => Iff.rfl⟩).trans
                (congrArg (fun Z => CapyTy.compile Z rDsub) hnat)
            exact hbridge ▸ hrec
          · simp only [CaptureSet.subst]; exact Subcapt.refl
          · -- backward modal BODY (W-lock).
            set Wsrc : CapyCaptureSet (s1,C,x) :=
              (cs.rename Rename.succ).rename Rename.succ
                ∪ CapyCaptureSet.var (.M .epsilon) (.bound .here) with hWsrc
            have hcomm : ((cs.rename Rename.succ).rename Rename.succ).subst
                  ((σ.lift (k := Kind.cvar)).lift (k := Kind.var))
                = ((cs.subst σ).rename Rename.succ).rename Rename.succ := by
              have e1 : (cs.rename Rename.succ).subst (σ.lift (k := Kind.cvar))
                  = (cs.subst σ).rename Rename.succ :=
                (CapyCaptureSet.weaken_subst_comm_base (cs := cs) (σ := σ) (k := Kind.cvar)).symm
              have e2 : ((cs.rename Rename.succ).rename Rename.succ).subst
                    ((σ.lift (k := Kind.cvar)).lift (k := Kind.var))
                  = ((cs.rename Rename.succ).subst (σ.lift (k := Kind.cvar))).rename Rename.succ :=
                (CapyCaptureSet.weaken_subst_comm_base (cs := cs.rename Rename.succ)
                  (σ := σ.lift (k := Kind.cvar)) (k := Kind.var)).symm
              rw [e2, e1]
            have hWnat : Wsrc.subst ((σ.lift (k := Kind.cvar)).lift (k := Kind.var))
                = ((cs.subst σ).rename Rename.succ).rename Rename.succ
                  ∪ CapyCaptureSet.var (.M .epsilon) (.bound .here) := by
              rw [hWsrc]; simp only [CapyCaptureSet.subst]; congr 1
            set ctxLockSub :=
              (ctxSub.weakenTarget.weakenTarget.weakenTarget.consCVar
                  (CapyCaptureBound.unbound Mutability.epsilon)
                  (BVar.there (BVar.there BVar.here))).consVar (T1.subst σ.lift) (some BVar.here)
                (CaptureSet.cvar (Access.M Mutability.epsilon) (BVar.there BVar.here))
              with hctxLockSub
            set ctxLockOrig :=
              (ctxOrig.weakenTarget.weakenTarget.weakenTarget.consCVar
                  (CapyCaptureBound.unbound Mutability.epsilon)
                  (BVar.there (BVar.there BVar.here))).consVar T1 (some BVar.here)
                (CaptureSet.cvar (Access.M Mutability.epsilon) (BVar.there BVar.here))
              with hctxLockOrig
            have hcLock : (((σt.lift (k := Kind.cvar)).lift (k := Kind.cvar)).lift
                  (k := Kind.var)).cvar (BVar.there (BVar.there BVar.here))
                = CaptureSet.cvar (.M .epsilon) (BVar.there (BVar.there BVar.here)) := rfl
            have hinvLock : (CaptureSet.cvar (.M .epsilon) (BVar.there BVar.here)).subst
                  (((σt.lift (k := Kind.cvar)).lift (k := Kind.cvar)).lift (k := Kind.var))
                = CaptureSet.cvar (.M .epsilon) (BVar.there BVar.here) := rfl
            have hcompatLock :=
              (((hcompat.weakenTarget (k := Kind.cvar)).weakenTarget (k := Kind.cvar)).weakenTarget
                  (k := Kind.var)).consCVar hcLock |>.consVar
                (bvS := some BVar.here) (bvO := some BVar.here) hinvLock
            have hWcl : Wsrc.IsClosed := by
              rw [hWsrc]
              exact CapyCaptureSet.IsClosed.union
                (CapyCaptureSet.rename_isClosed (CapyCaptureSet.rename_isClosed hcsCl))
                CapyCaptureSet.IsClosed.var_bound
            have hWf : CapyCaptureSet.compile
                  (((cs.subst σ).rename Rename.succ).rename Rename.succ
                    ∪ CapyCaptureSet.var (.M .epsilon) (.bound .here)) ctxLockSub.srcCtx
                = (CapyCaptureSet.compile Wsrc ctxLockOrig.srcCtx).subst
                  (((σt.lift (k := Kind.cvar)).lift (k := Kind.cvar)).lift (k := Kind.var)) := by
              rw [← hWnat]
              exact CapyCaptureSet.compile_subst hcompatLock hWcl
            have hvcLockSub : ctxLockSub.srcCtx.VarsClosed :=
              ((hvcSub.weaken.weaken.weaken).consCVar).consVar CaptureSet.IsClosed.cvar
            have hvcLockOrig : ctxLockOrig.srcCtx.VarsClosed :=
              ((hvcOrig.weaken.weaken.weaken).consCVar).consVar CaptureSet.IsClosed.cvar
            have hσt3 : Subst.IsClosed
                (((σt.lift (k := Kind.cvar)).lift (k := Kind.cvar)).lift (k := Kind.var)) :=
              Subst.lift_closed (Subst.lift_closed (Subst.lift_closed hscl))
            refine Subtyp.trans ?_ (Subtyp.modal_modal ?_ ?_ ?_ ?satB)
              (Subtyp.modal (hWf ▸ Subcapt.refl) ?bodyB)
            · exact Ty.IsClosed.modal
                (CaptureSet.is_closed_subst
                  (CapyCaptureSet.compile_isClosed hWcl hvcLockOrig) hσt3)
                ⟨peakSepCtx_isClosed (CapyCaptureSet.peaks_isClosed _ _) hvcLockSub,
                  MutabilityCtx.IsClosed.empty⟩
                (Ty.is_closed_subst
                  (CapyTy.compile_isClosed (E.rename Rename.implicit_cvar) ctxLockOrig
                    (CapyTy.IsClosed.rename hECl Rename.implicit_cvar) hvcLockOrig)
                  hσt3)
            · exact Ctx.IsClosed.push
                (Ctx.IsClosed.push
                  (Ctx.IsClosed.push hcoreSub
                    (Binding.IsClosed.cvar CaptureBound.IsClosed.unbound))
                  (Binding.IsClosed.cvar
                    (CaptureBound.IsClosed.bound
                      (CapyCaptureSet.compile_isClosed
                        (CapyTy.IsClosed.captureSet
                          (CapyTy.is_closed_subst hT1Cl (CapySubst.lift_closed hscS)))
                        hvcSub.weaken.consCVar))))
                (Binding.IsClosed.var
                  (CapyTy.compile_isClosed
                    (((T1.subst σ.lift).rename Rename.succ).refineCaptureSet
                      (CapyCaptureSet.var (.M .epsilon) (.bound .here)))
                    ((ctxSub.weakenTarget.weakenTarget.consCVar
                        (CapyCaptureBound.unbound Mutability.epsilon)
                        (BVar.there BVar.here)).consVar (T1.subst σ.lift) none
                      (CaptureSet.cvar (.M .epsilon) BVar.here))
                    (CapyTy.IsClosed.refineCaptureSet
                      (CapyTy.IsClosed.rename
                        (CapyTy.is_closed_subst hT1Cl (CapySubst.lift_closed hscS)) Rename.succ)
                      CapyCaptureSet.IsClosed.var_bound)
                    ((hvcSub.weaken.weaken.consCVar).consVar CaptureSet.IsClosed.cvar)))
            · exact ModalCtx.is_closed_subst
                ⟨peakSepCtx_isClosed (CapyCaptureSet.peaks_isClosed _ _) hvcLockOrig,
                  MutabilityCtx.IsClosed.empty⟩ hσt3
            · exact ⟨peakSepCtx_isClosed (CapyCaptureSet.peaks_isClosed _ _) hvcLockSub,
                MutabilityCtx.IsClosed.empty⟩
            case satB =>
              have htv0 : ∀ X, ∃ Y, σ.tvar X = CapyPureTy.tvar Y :=
                fun X => let ⟨Z, hZ, _⟩ := htvar X; ⟨Z, hZ⟩
              have hlift1tv : ∀ X, ∃ Y,
                  (σ.lift (k := Kind.cvar)).tvar X = CapyPureTy.tvar Y := by
                intro X
                cases X with
                | there X0 =>
                  obtain ⟨Y, hY⟩ := htv0 X0
                  exact ⟨_, by rw [CapySubst.lift_there_tvar_eq, hY]; rfl⟩
              have hlift2tv : ∀ X, ∃ Y,
                  ((σ.lift (k := Kind.cvar)).lift (k := Kind.var)).tvar X = CapyPureTy.tvar Y := by
                intro X
                cases X with
                | there X0 =>
                  obtain ⟨Y, hY⟩ := hlift1tv X0
                  exact ⟨_, by rw [CapySubst.lift_there_tvar_eq, hY]; rfl⟩
              have hclOrigW : ctxLockOrig.capyCtx.IsClosed :=
                CapyCtx.IsClosed.push (CapyCtx.IsClosed.push hclOrig
                  (CapyBinding.IsClosed.cvar CapyCaptureBound.IsClosed.unbound))
                  (CapyBinding.IsClosed.var hT1Cl)
              have hclSubW : ctxLockSub.capyCtx.IsClosed :=
                CapyCtx.IsClosed.push (CapyCtx.IsClosed.push hclSub
                  (CapyBinding.IsClosed.cvar CapyCaptureBound.IsClosed.unbound))
                  (CapyBinding.IsClosed.var
                    (CapyTy.is_closed_subst hT1Cl (CapySubst.lift_closed hscS)))
              have hWsubcl :
                  (Wsrc.subst ((σ.lift (k := Kind.cvar)).lift (k := Kind.var))).IsClosed :=
                CapyCaptureSet.is_closed_subst hWcl
                  (CapySubst.lift_closed (CapySubst.lift_closed hscS))
              have hWnp : Wsrc.NoPseudoPeak :=
                CapyCaptureSet.NoPseudoPeak.union
                  ((hcsnp.rename Rename.succ).rename Rename.succ)
                  CapyCaptureSet.NoPseudoPeak.var
              have hinjW : ctxLockSub.srcCtx.CVarInjective :=
                SrcCtx.CVarInjective.consVar
                  (SrcCtx.CVarInjective.rename (SrcCtx.CVarInjective.rename
                    (SrcCtx.CVarInjective.consCVarHere hinj) Rename.injective_succ)
                    Rename.injective_succ)
              apply Satisfy.satisfy
              · intro C m hmem
                simp only [ModalCtx.rename, ModalCtx.subst] at hmem
                simp only [MutabilityCtx.subst, MutabilityCtx.rename] at hmem
                cases hmem
              · intro C1 C2 hdist
                simp only [ModalCtx.rename, ModalCtx.subst] at hdist
                exact hWnat ▸ compile_peakSepCtx_sep_backward_realign hclSubW
                  ((hcompatAl.realign_weakenTarget.realign_weakenTarget.realign_weakenTarget
                      ).realign_consCVar hcLock |>.realign_consVar hlift1tv hT1Cl)
                  (by exact ⟨horig, hT1np.captureSet⟩) hWnp
                  ((hiso.lift Kind.cvar).lift Kind.var)
                  (CapySubst.lift_closed (CapySubst.lift_closed hscS))
                  hlift2tv
                  (by exact (hsubsto.consCVar).consVar hlift1tv)
                  ((hstab.pushCVar (.unbound .epsilon)).pushVar T1 (T1.subst σ.lift))
                  C1 C2 hdist
            case bodyB =>
              have htv0 : ∀ X, ∃ Y, σ.tvar X = CapyPureTy.tvar Y :=
                fun X => let ⟨Z, hZ, _⟩ := htvar X; ⟨Z, hZ⟩
              have hlift1tv : ∀ X, ∃ Y,
                  (σ.lift (k := Kind.cvar)).tvar X = CapyPureTy.tvar Y := by
                intro X
                cases X with
                | there X0 =>
                  obtain ⟨Y, hY⟩ := htv0 X0
                  exact ⟨_, by rw [CapySubst.lift_there_tvar_eq, hY]; rfl⟩
              have hclOrigW : ctxLockOrig.capyCtx.IsClosed :=
                CapyCtx.IsClosed.push (CapyCtx.IsClosed.push hclOrig
                  (CapyBinding.IsClosed.cvar CapyCaptureBound.IsClosed.unbound))
                  (CapyBinding.IsClosed.var hT1Cl)
              have hclSubW : ctxLockSub.capyCtx.IsClosed :=
                CapyCtx.IsClosed.push (CapyCtx.IsClosed.push hclSub
                  (CapyBinding.IsClosed.cvar CapyCaptureBound.IsClosed.unbound))
                  (CapyBinding.IsClosed.var
                    (CapyTy.is_closed_subst hT1Cl (CapySubst.lift_closed hscS)))
              have hinjW : ctxLockSub.srcCtx.CVarInjective :=
                SrcCtx.CVarInjective.consVar
                  (SrcCtx.CVarInjective.rename (SrcCtx.CVarInjective.rename
                    (SrcCtx.CVarInjective.consCVarHere hinj) Rename.injective_succ)
                    Rename.injective_succ)
              set ΨL : ModalCtx (s2',,Kind.cvar,,Kind.cvar,,Kind.var) :=
                { sep := peakSepCtx ctxLockSub.capyCtx (CapyCaptureSet.peakset ctxLockSub.capyCtx
                           (((cs.subst σ).rename Rename.succ).rename Rename.succ
                             ∪ CapyCaptureSet.var (.M .epsilon) (.bound .here)))
                         ctxLockSub.srcCtx,
                  mutability := MutabilityCtx.empty } with hΨL
              have hGbcl : ((ctxSub.coreCtx.push_cvar Authority.access_only
                    CaptureBound.unbound).push_cvar Authority.access_only
                    (CaptureBound.bound (CapyCaptureSet.compile (T1.subst σ.lift).captureSet
                      (ctxSub.weakenTarget.consCVar (CapyCaptureBound.unbound Mutability.epsilon)
                        BVar.here).srcCtx))).push_var
                    (CapyTy.compile (((T1.subst σ.lift).rename Rename.succ).refineCaptureSet
                        (CapyCaptureSet.var (.M .epsilon) (.bound .here)))
                      ((ctxSub.weakenTarget.weakenTarget.consCVar
                          (CapyCaptureBound.unbound Mutability.epsilon)
                          (BVar.there BVar.here)).consVar (T1.subst σ.lift) none
                        (CaptureSet.cvar (.M .epsilon) BVar.here))) |>.IsClosed :=
                Ctx.IsClosed.push
                  (Ctx.IsClosed.push
                    (Ctx.IsClosed.push hcoreSub
                      (Binding.IsClosed.cvar CaptureBound.IsClosed.unbound))
                    (Binding.IsClosed.cvar
                      (CaptureBound.IsClosed.bound
                        (CapyCaptureSet.compile_isClosed
                          (CapyTy.IsClosed.captureSet
                            (CapyTy.is_closed_subst hT1Cl (CapySubst.lift_closed hscS)))
                          hvcSub.weaken.consCVar))))
                  (Binding.IsClosed.var
                    (CapyTy.compile_isClosed
                      (((T1.subst σ.lift).rename Rename.succ).refineCaptureSet
                        (CapyCaptureSet.var (.M .epsilon) (.bound .here)))
                      ((ctxSub.weakenTarget.weakenTarget.consCVar
                          (CapyCaptureBound.unbound Mutability.epsilon)
                          (BVar.there BVar.here)).consVar (T1.subst σ.lift) none
                        (CaptureSet.cvar (.M .epsilon) BVar.here))
                      (CapyTy.IsClosed.refineCaptureSet
                        (CapyTy.IsClosed.rename
                          (CapyTy.is_closed_subst hT1Cl (CapySubst.lift_closed hscS)) Rename.succ)
                        CapyCaptureSet.IsClosed.var_bound)
                      ((hvcSub.weaken.weaken.consCVar).consVar CaptureSet.IsClosed.cvar)))
              set ctxSub'' : CompilerCtx (s1',C,,Kind.var)
                  ((s2',,Kind.cvar,,Kind.cvar,,Kind.var),,Kind.lock) :=
                ⟨ctxLockSub.capyCtx, ctxLockSub.srcCtx.rename Rename.succ,
                 (ctxLockSub.weakenTarget (Binding.lock ΨL)).dstCtx,
                 ((ctxSub.coreCtx.push_cvar Authority.access_only
                      CaptureBound.unbound).push_cvar Authority.access_only
                      (CaptureBound.bound (CapyCaptureSet.compile (T1.subst σ.lift).captureSet
                        (ctxSub.weakenTarget.consCVar (CapyCaptureBound.unbound Mutability.epsilon)
                          BVar.here).srcCtx))).push_var
                      (CapyTy.compile (((T1.subst σ.lift).rename Rename.succ).refineCaptureSet
                          (CapyCaptureSet.var (.M .epsilon) (.bound .here)))
                        ((ctxSub.weakenTarget.weakenTarget.consCVar
                            (CapyCaptureBound.unbound Mutability.epsilon)
                            (BVar.there BVar.here)).consVar (T1.subst σ.lift) none
                          (CaptureSet.cvar (.M .epsilon) BVar.here)))
                      |>.push_lock ΨL⟩ with hctxSub''
              set ctxOrig'' : CompilerCtx (s1,C,,Kind.var)
                  ((s2,,Kind.cvar,,Kind.cvar,,Kind.var),,Kind.lock) :=
                ⟨ctxLockOrig.capyCtx, ctxLockOrig.srcCtx.rename Rename.succ,
                 (ctxLockOrig.weakenTarget
                   (Binding.lock (⟨SepCtx.empty, MutabilityCtx.empty⟩ : ModalCtx _))).dstCtx,
                 ctxLockOrig.coreCtx.push_lock
                   (⟨SepCtx.empty, MutabilityCtx.empty⟩ : ModalCtx _)⟩ with hctxOrig''
              have hge := (CapyTy.compile_subst_subtyp (E.rename Rename.implicit_cvar)
                (ctxSub := ctxSub'') (ctxOrig := ctxOrig'')
                (σ := (σ.lift (k := Kind.cvar)).lift (k := Kind.var))
                (σt := (((σt.lift (k := Kind.cvar)).lift (k := Kind.cvar)).lift
                  (k := Kind.var)).lift (k := Kind.lock))
                hcompatLock.weakenTarget
                ((((htvar.weakenTarget.weakenTarget.weakenTarget).consCVar).consVar).weakenTarget)
                (CapyTy.IsClosed.rename hECl Rename.implicit_cvar)
                (CapyTy.PureBounds.rename Rename.implicit_cvar hpbE)
                (hdrop.liftShift4 (fun _ hh => CapyTy.tgtCvarOccurs_arrow_cod hh))
                ((((hcompatAl.realign_weakenTarget.realign_weakenTarget.realign_weakenTarget
                    ).realign_consCVar hcLock).realign_consVar hlift1tv
                    hT1Cl).realign_weakenTarget)
                hclSubW hclOrigW
                (Subst.lift_closed (Subst.lift_closed (Subst.lift_closed (Subst.lift_closed hscl))))
                hvcLockSub.weaken hvcLockOrig.weaken
                (Ctx.IsClosed.push hGbcl
                  (Binding.IsClosed.lock ⟨peakSepCtx_isClosed
                    (CapyCaptureSet.peaks_isClosed _ _) hvcLockSub,
                    MutabilityCtx.IsClosed.empty⟩))
                (CapySubst.lift_closed (CapySubst.lift_closed hscS))
                (SrcCtx.CVarInjective.rename hinjW Rename.injective_succ)
                ((hiso.lift Kind.cvar).lift Kind.var)
                ⟨horig, hT1np.captureSet⟩
                (CapyTy.NoPseudoPeak.rename Rename.implicit_cvar hEnp)
                ((hsubsto.consCVar).consVar hlift1tv)
                ((hstab.pushCVar (.unbound .epsilon)).pushVar T1 (T1.subst σ.lift))).2
              have heq1 : CapyTy.compile ((E.subst σ.lift).rename Rename.implicit_cvar) ctxSub''
                  = (CapyTy.compile ((E.subst σ.lift).rename Rename.implicit_cvar)
                      ctxLockSub).rename Rename.succ :=
                CapyTy.compile_rename ((E.subst σ.lift).rename Rename.implicit_cvar)
                  ctxLockSub ctxSub'' Rename.succ rfl rfl
              have heq2 : CapyTy.compile (E.rename Rename.implicit_cvar) ctxOrig''
                  = (CapyTy.compile (E.rename Rename.implicit_cvar) ctxLockOrig).rename
                      Rename.succ :=
                CapyTy.compile_rename (E.rename Rename.implicit_cvar) ctxLockOrig ctxOrig''
                  Rename.succ rfl rfl
              convert hge using 2
              · rw [heq2]; exact Ty.weaken_subst_comm_base
              · exact heq1.symm.trans
                  (congrArg (fun Z => CapyTy.compile Z ctxSub'')
                    CapyTy.implicit_cvar_subst_comm)
  | .poly S cs E =>
    intro s2 s1' s2' ctxOrig ctxSub σ σt hcompat htvar hcl hpb hdrop hcompatAl hclSub hclOrig
      hscl hvcSub hvcOrig hcoreSub hscS hinj hiso horig hTnp hsubsto hstab
    cases hcl with | poly hSCl hcsCl hECl =>
    obtain ⟨hSiPure, hpbS, hpbE⟩ := hpb
    obtain ⟨hSnp, hcsnp, hEnp⟩ := hTnp
    simp only [CapyTy.subst, CapyTy.compile, Ty.subst]
    refine ⟨?_, ?_⟩
    · -- forward: ⟦(poly S cs E)[σ]⟧ <: ⟦poly S cs E⟧[σt]
      have hS2p : Ty.IsPureType ((CapyTy.compile S ctxOrig).subst σt) :=
        Ty.IsPureType.subst (CapyTy.compile_isPure hSiPure) σt
      have hS2cl : Ty.IsClosed ((CapyTy.compile S ctxOrig).subst σt) :=
        Ty.is_closed_subst (CapyTy.compile_isClosed S ctxOrig hSCl hvcOrig) hscl
      refine Subtyp.poly
        (S1 := ⟨CapyTy.compile (S.subst σ) ctxSub, CapyTy.compile_isPure (hSiPure.subst σ)⟩)
        (S2 := ⟨(CapyTy.compile S ctxOrig).subst σt, hS2p⟩)
        ((CapyTy.compile_subst_subtyp S hcompat htvar hSCl hpbS
            (hdrop.mono (fun _ hh => CapyTy.tgtCvarOccurs_poly_bound hh)) hcompatAl hclSub hclOrig
            hscl hvcSub hvcOrig hcoreSub hscS hinj hiso horig hSnp hsubsto hstab).2)
        ?_ (Subtyp.typ ?_)
      · simp only [CaptureSet.subst]; exact Subcapt.refl
      · have hCf :
            CapyCaptureSet.compile (CapyCaptureSet.subst cs σ)
                  (ctxSub.srcCtx.weaken (k := .tvar)) =
              (CapyCaptureSet.compile cs (ctxOrig.srcCtx.weaken (k := .tvar))).subst
                (σt.lift (k := .tvar)) :=
          CapyCaptureSet.compile_subst (SubstCompat.weakenTarget hcompat) hcsCl
        refine Subtyp.trans ?_ (Subtyp.modal (hCf ▸ Subcapt.refl) ?body)
          (Subtyp.modal_modal ?_ ?_ ?_ ?sat)
        · exact Ty.IsClosed.modal
            (CaptureSet.is_closed_subst (CapyCaptureSet.compile_isClosed hcsCl hvcOrig.weaken)
              (Subst.lift_closed hscl))
            ⟨peakSepCtx_isClosed (CapyCaptureSet.peaks_isClosed _ _)
              hvcSub.weaken, MutabilityCtx.IsClosed.empty⟩
            (Ty.is_closed_subst
              (CapyTy.compile_isClosed E (ctxOrig.weakenTarget.consTVar CapyPureTy.top BVar.here)
                hECl hvcOrig.weaken.consTVar)
              (Subst.lift_closed hscl))
        case body =>
          set ΨL : ModalCtx (s2',,Kind.tvar) :=
            { sep := peakSepCtx ctxSub.capyCtx
                (CapyCaptureSet.peakset ctxSub.capyCtx (CapyCaptureSet.subst cs σ))
                ctxSub.srcCtx.weaken,
              mutability := MutabilityCtx.empty } with hΨL
          set csub' := ctxSub.weakenTarget.consTVar CapyPureTy.top (BVar.here) with hcsub'
          set corig' := ctxOrig.weakenTarget.consTVar CapyPureTy.top (BVar.here) with hcorig'
          set S2bnd : PureTy s2' := ⟨(CapyTy.compile S ctxOrig).subst σt, hS2p⟩ with hS2bnd
          set ctxSub'' : CompilerCtx (s1',X) ((s2',,Kind.tvar),,Kind.lock) :=
            ⟨csub'.capyCtx, csub'.srcCtx.rename Rename.succ,
             (csub'.weakenTarget (Binding.lock ΨL)).dstCtx,
             (ctxSub.coreCtx,X<:S2bnd).push_lock ΨL⟩ with hctxSub''
          set ctxOrig'' : CompilerCtx _ ((s2,,Kind.tvar),,Kind.lock) :=
            ⟨corig'.capyCtx, corig'.srcCtx.rename Rename.succ,
             (corig'.weakenTarget
               (Binding.lock (⟨SepCtx.empty, MutabilityCtx.empty⟩ : ModalCtx _))).dstCtx,
             corig'.coreCtx.push_lock (⟨SepCtx.empty, MutabilityCtx.empty⟩ : ModalCtx _)⟩
            with hctxOrig''
          have hle := (CapyTy.compile_subst_subtyp E (ctxSub := ctxSub'') (ctxOrig := ctxOrig'')
            (σ := σ.lift)
            (σt := σt.lift.lift)
            ((SubstCompat.weakenConsTVar hcompat).weakenTarget)
            ((SubstTvarCompat.weakenConsTVar htvar).weakenTarget)
            hECl hpbE
            (hdrop.liftShift2 (fun _ hh => CapyTy.tgtCvarOccurs_poly_body hh))
            (SubstCompat.realign_weakenConsTVar hcompatAl).realign_weakenTarget
            (CapyCtx.IsClosed.push hclSub (CapyBinding.IsClosed.tvar CapyTy.IsClosed.top))
            (CapyCtx.IsClosed.push hclOrig (CapyBinding.IsClosed.tvar CapyTy.IsClosed.top))
            (Subst.lift_closed (Subst.lift_closed hscl))
            hvcSub.weaken.consTVar.weaken hvcOrig.weaken.consTVar.weaken
            (Ctx.IsClosed.push
              (Ctx.IsClosed.push hcoreSub (Binding.IsClosed.tvar hS2cl))
              (Binding.IsClosed.lock ⟨peakSepCtx_isClosed
                (CapyCaptureSet.peaks_isClosed _ _) hvcSub.weaken,
                MutabilityCtx.IsClosed.empty⟩))
            (CapySubst.lift_closed hscS)
            (SrcCtx.CVarInjective.rename
              (SrcCtx.CVarInjective.consTVar
                (SrcCtx.CVarInjective.rename hinj Rename.injective_succ)) Rename.injective_succ)
            (hiso.lift Kind.tvar) horig hEnp
            hsubsto.consTVar (hstab.pushTVar CapyPureTy.top CapyPureTy.top)).1
          have heq1 : CapyTy.compile (E.subst σ.lift) ctxSub''
              = (CapyTy.compile (E.subst σ.lift) csub').rename Rename.succ :=
            CapyTy.compile_rename (E.subst σ.lift) csub' ctxSub'' Rename.succ rfl rfl
          have heq2 : CapyTy.compile E ctxOrig''
              = (CapyTy.compile E corig').rename Rename.succ :=
            CapyTy.compile_rename E corig' ctxOrig'' Rename.succ rfl rfl
          convert hle using 2
          · exact heq1.symm
          · rw [heq2]; exact Ty.weaken_subst_comm_base
        · exact Ctx.IsClosed.push hcoreSub (Binding.IsClosed.tvar hS2cl)
        · exact ⟨peakSepCtx_isClosed (CapyCaptureSet.peaks_isClosed _ _)
              hvcSub.weaken, MutabilityCtx.IsClosed.empty⟩
        · exact ModalCtx.is_closed_subst
            ⟨peakSepCtx_isClosed (CapyCaptureSet.peaks_isClosed _ _)
              hvcOrig.weaken, MutabilityCtx.IsClosed.empty⟩
            (Subst.lift_closed hscl)
        case sat =>
          apply Satisfy.satisfy
          · intro C m hmem
            simp only [ModalCtx.rename] at hmem
            simp only [MutabilityCtx.rename] at hmem
            cases hmem
          · intro C1 C2 hdist
            simp only [ModalCtx.rename] at hdist
            rw [← peakSepCtx_rename] at hdist
            exact compile_peakSepCtx_sep_forward_splitcov_realign hclOrig hclSub
              (SubstCompat.realign_weakenTarget (k := Kind.tvar) hcompatAl) hcsCl
              (CapyCaptureSet.is_closed_subst hcsCl hscS) horig hcsnp
              (SrcCtx.CVarInjective.rename hinj Rename.injective_succ)
              hiso hscS (fun X => let ⟨Z, hZ, _⟩ := htvar X; ⟨Z, hZ⟩)
              hsubsto
              (hdrop.liftTVar (fun _ hh => CapyTy.tgtCvarOccurs_bridge_poly horig hcsnp _ hh))
              hstab C1 C2 hdist
    · -- backward: ⟦poly S cs E⟧[σt] <: ⟦(poly S cs E)[σ]⟧
      have hS2p : Ty.IsPureType ((CapyTy.compile S ctxOrig).subst σt) :=
        Ty.IsPureType.subst (CapyTy.compile_isPure hSiPure) σt
      have hSsubcl : (S.subst σ).IsClosed := CapyTy.is_closed_subst hSCl hscS
      have hS1cl : Ty.IsClosed (CapyTy.compile (S.subst σ) ctxSub) :=
        CapyTy.compile_isClosed (S.subst σ) ctxSub hSsubcl hvcSub
      refine Subtyp.poly
        (S1 := ⟨(CapyTy.compile S ctxOrig).subst σt, hS2p⟩)
        (S2 := ⟨CapyTy.compile (S.subst σ) ctxSub, CapyTy.compile_isPure (hSiPure.subst σ)⟩)
        ((CapyTy.compile_subst_subtyp S hcompat htvar hSCl hpbS
            (hdrop.mono (fun _ hh => CapyTy.tgtCvarOccurs_poly_bound hh)) hcompatAl hclSub hclOrig
            hscl hvcSub hvcOrig hcoreSub hscS hinj hiso horig hSnp hsubsto hstab).1)
        ?_ (Subtyp.typ ?_)
      · simp only [CaptureSet.subst]; exact Subcapt.refl
      · have hCf :
            CapyCaptureSet.compile (CapyCaptureSet.subst cs σ)
                  (ctxSub.srcCtx.weaken (k := .tvar)) =
              (CapyCaptureSet.compile cs (ctxOrig.srcCtx.weaken (k := .tvar))).subst
                (σt.lift (k := .tvar)) :=
          CapyCaptureSet.compile_subst (SubstCompat.weakenTarget hcompat) hcsCl
        refine Subtyp.trans ?_
          (Subtyp.modal_modal ?_ ?_ ?_ ?satB)
          (Subtyp.modal (hCf ▸ Subcapt.refl) ?bodyB)
        · exact Ty.IsClosed.modal
            (CaptureSet.is_closed_subst (CapyCaptureSet.compile_isClosed hcsCl hvcOrig.weaken)
              (Subst.lift_closed hscl))
            ⟨peakSepCtx_isClosed (CapyCaptureSet.peaks_isClosed _ _)
              hvcSub.weaken, MutabilityCtx.IsClosed.empty⟩
            (Ty.is_closed_subst
              (CapyTy.compile_isClosed E (ctxOrig.weakenTarget.consTVar CapyPureTy.top BVar.here)
                hECl hvcOrig.weaken.consTVar)
              (Subst.lift_closed hscl))
        · exact Ctx.IsClosed.push hcoreSub (Binding.IsClosed.tvar hS1cl)
        · exact ModalCtx.is_closed_subst
            ⟨peakSepCtx_isClosed (CapyCaptureSet.peaks_isClosed _ _)
              hvcOrig.weaken, MutabilityCtx.IsClosed.empty⟩
            (Subst.lift_closed hscl)
        · exact ⟨peakSepCtx_isClosed (CapyCaptureSet.peaks_isClosed _ _)
              hvcSub.weaken, MutabilityCtx.IsClosed.empty⟩
        case satB =>
          apply Satisfy.satisfy
          · intro C m hmem
            simp only [ModalCtx.rename, ModalCtx.subst, MutabilityCtx.subst,
              MutabilityCtx.rename] at hmem
            cases hmem
          · intro C1 C2 hdist
            simp only [ModalCtx.rename, ModalCtx.subst] at hdist
            exact compile_peakSepCtx_sep_backward_realign hclSub
              (SubstCompat.realign_weakenTarget (k := Kind.tvar) hcompatAl) horig hcsnp
              hiso hscS (fun X => let ⟨Z, hZ, _⟩ := htvar X; ⟨Z, hZ⟩)
              hsubsto hstab C1 C2 hdist
        case bodyB =>
          set ΨL : ModalCtx (s2',,Kind.tvar) :=
            { sep := peakSepCtx ctxSub.capyCtx
                (CapyCaptureSet.peakset ctxSub.capyCtx (CapyCaptureSet.subst cs σ))
                ctxSub.srcCtx.weaken,
              mutability := MutabilityCtx.empty } with hΨL
          set csub' := ctxSub.weakenTarget.consTVar CapyPureTy.top (BVar.here) with hcsub'
          set corig' := ctxOrig.weakenTarget.consTVar CapyPureTy.top (BVar.here) with hcorig'
          set S2bnd : PureTy s2' :=
            ⟨CapyTy.compile (S.subst σ) ctxSub, CapyTy.compile_isPure (hSiPure.subst σ)⟩ with hS2bnd
          set ctxSub'' : CompilerCtx (s1',X) ((s2',,Kind.tvar),,Kind.lock) :=
            ⟨csub'.capyCtx, csub'.srcCtx.rename Rename.succ,
             (csub'.weakenTarget (Binding.lock ΨL)).dstCtx,
             (ctxSub.coreCtx,X<:S2bnd).push_lock ΨL⟩ with hctxSub''
          set ctxOrig'' : CompilerCtx _ ((s2,,Kind.tvar),,Kind.lock) :=
            ⟨corig'.capyCtx, corig'.srcCtx.rename Rename.succ,
             (corig'.weakenTarget
               (Binding.lock (⟨SepCtx.empty, MutabilityCtx.empty⟩ : ModalCtx _))).dstCtx,
             corig'.coreCtx.push_lock (⟨SepCtx.empty, MutabilityCtx.empty⟩ : ModalCtx _)⟩
            with hctxOrig''
          have hge := (CapyTy.compile_subst_subtyp E (ctxSub := ctxSub'') (ctxOrig := ctxOrig'')
            (σ := σ.lift)
            (σt := σt.lift.lift)
            ((SubstCompat.weakenConsTVar hcompat).weakenTarget)
            ((SubstTvarCompat.weakenConsTVar htvar).weakenTarget)
            hECl hpbE
            (hdrop.liftShift2 (fun _ hh => CapyTy.tgtCvarOccurs_poly_body hh))
            (SubstCompat.realign_weakenConsTVar hcompatAl).realign_weakenTarget
            (CapyCtx.IsClosed.push hclSub (CapyBinding.IsClosed.tvar CapyTy.IsClosed.top))
            (CapyCtx.IsClosed.push hclOrig (CapyBinding.IsClosed.tvar CapyTy.IsClosed.top))
            (Subst.lift_closed (Subst.lift_closed hscl))
            hvcSub.weaken.consTVar.weaken hvcOrig.weaken.consTVar.weaken
            (Ctx.IsClosed.push
              (Ctx.IsClosed.push hcoreSub (Binding.IsClosed.tvar hS1cl))
              (Binding.IsClosed.lock ⟨peakSepCtx_isClosed
                (CapyCaptureSet.peaks_isClosed _ _) hvcSub.weaken,
                MutabilityCtx.IsClosed.empty⟩))
            (CapySubst.lift_closed hscS)
            (SrcCtx.CVarInjective.rename
              (SrcCtx.CVarInjective.consTVar
                (SrcCtx.CVarInjective.rename hinj Rename.injective_succ)) Rename.injective_succ)
            (hiso.lift Kind.tvar) horig hEnp
            hsubsto.consTVar (hstab.pushTVar CapyPureTy.top CapyPureTy.top)).2
          have heq1 : CapyTy.compile (E.subst σ.lift) ctxSub''
              = (CapyTy.compile (E.subst σ.lift) csub').rename Rename.succ :=
            CapyTy.compile_rename (E.subst σ.lift) csub' ctxSub'' Rename.succ rfl rfl
          have heq2 : CapyTy.compile E ctxOrig''
              = (CapyTy.compile E corig').rename Rename.succ :=
            CapyTy.compile_rename E corig' ctxOrig'' Rename.succ rfl rfl
          convert hge using 2
          · rw [heq2]; exact Ty.weaken_subst_comm_base
          · exact heq1.symm
  | .cpoly cb cs E =>
    intro s2 s1' s2' ctxOrig ctxSub σ σt hcompat htvar hcl hpb hdrop hcompatAl hclSub hclOrig
      hscl hvcSub hvcOrig hcoreSub hscS hinj hiso horig hTnp hsubsto hstab
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
            ⟨peakSepCtx_isClosed (CapyCaptureSet.peaks_isClosed _ _)
              hvcSub.weaken, CapyCaptureBound.mutabilityCtx_isClosed⟩
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
            { sep := peakSepCtx ctxSub.capyCtx
                (CapyCaptureSet.peakset ctxSub.capyCtx (CapyCaptureSet.subst cs σ))
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
          have hle := (CapyTy.compile_subst_subtyp E (ctxSub := ctxSub'') (ctxOrig := ctxOrig'')
            (σ := σ.lift)
            (σt := σt.lift.lift)
            ((SubstCompat.weakenConsCVar hcompat).weakenTarget)
            ((SubstTvarCompat.weakenConsCVar htvar).weakenTarget)
            hECl hpb
            (hdrop.liftShift2 (fun _ hh => CapyTy.tgtCvarOccurs_cpoly_body hh))
            (SubstCompat.realign_weakenConsCVar hcompatAl).realign_weakenTarget
            (CapyCtx.IsClosed.push hclSub (CapyBinding.IsClosed.cvar
              (CapyCaptureBound.is_closed_subst hcb hscS)))
            (CapyCtx.IsClosed.push hclOrig (CapyBinding.IsClosed.cvar hcb))
            (Subst.lift_closed (Subst.lift_closed hscl))
            hvcSub.weaken.consCVar.weaken hvcOrig.weaken.consCVar.weaken
            (Ctx.IsClosed.push
              (Ctx.IsClosed.push hcoreSub (Binding.IsClosed.cvar
                (CaptureBound.is_closed_subst
                  (CapyCaptureBound.compile_isClosed hcb hvcOrig) hscl)))
              (Binding.IsClosed.lock ⟨peakSepCtx_isClosed
                (CapyCaptureSet.peaks_isClosed _ _) hvcSub.weaken,
                CapyCaptureBound.mutabilityCtx_isClosed⟩))
            (CapySubst.lift_closed hscS)
            (SrcCtx.CVarInjective.rename
              (SrcCtx.CVarInjective.consCVarHere hinj) Rename.injective_succ)
            (hiso.lift Kind.cvar) horig hTnp.2.2
            hsubsto.consCVar (hstab.pushCVar cb)).1
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
        · exact ⟨peakSepCtx_isClosed (CapyCaptureSet.peaks_isClosed _ _)
              hvcSub.weaken, CapyCaptureBound.mutabilityCtx_isClosed⟩
        · exact ModalCtx.is_closed_subst
            ⟨peakSepCtx_isClosed (CapyCaptureSet.peaks_isClosed _ _)
              hvcOrig.weaken, CapyCaptureBound.mutabilityCtx_isClosed⟩
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
            exact compile_peakSepCtx_sep_forward_splitcov_realign hclOrig hclSub
              (SubstCompat.realign_weakenTarget (k := Kind.cvar) hcompatAl) hcsCl
              (CapyCaptureSet.is_closed_subst hcsCl hscS) horig hTnp.2.1
              (SrcCtx.CVarInjective.rename hinj Rename.injective_succ)
              hiso hscS (fun X => let ⟨Z, hZ, _⟩ := htvar X; ⟨Z, hZ⟩)
              hsubsto
              (hdrop.lift (fun _ hh => CapyTy.tgtCvarOccurs_bridge_cpoly horig hTnp.2.1 _ hh))
              hstab C1 C2 hdist
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
            ⟨peakSepCtx_isClosed (CapyCaptureSet.peaks_isClosed _ _)
              hvcSub.weaken, CapyCaptureBound.mutabilityCtx_isClosed⟩
            (Ty.is_closed_subst
              (CapyTy.compile_isClosed E (ctxOrig.weakenTarget.consCVar cb BVar.here) hECl
                hvcOrig.weaken.consCVar)
              (Subst.lift_closed hscl))
        -- modal_modal closedness: Γ, Ψ1 = Ψ_R (substituted), Ψ2 = Ψ_L (sub-peaks).
        · exact Ctx.IsClosed.push hcoreSub (Binding.IsClosed.cvar
            (CaptureBound.is_closed_subst (CapyCaptureBound.compile_isClosed hcb hvcOrig) hscl))
        · exact ModalCtx.is_closed_subst
            ⟨peakSepCtx_isClosed (CapyCaptureSet.peaks_isClosed _ _)
              hvcOrig.weaken, CapyCaptureBound.mutabilityCtx_isClosed⟩
            (Subst.lift_closed hscl)
        · exact ⟨peakSepCtx_isClosed (CapyCaptureSet.peaks_isClosed _ _)
              hvcSub.weaken, CapyCaptureBound.mutabilityCtx_isClosed⟩
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
        case satB =>
          apply Satisfy.satisfy
          · -- hkind (mutability), mirror of the forward `sat` but `Ψ_R` is substituted.
            intro C m hmem
            simp only [ModalCtx.rename, ModalCtx.subst] at hmem
            cases cb with
            | bound cs0 =>
              simp only [CapyCaptureBound.mutabilityCtx, MutabilityCtx.subst,
                MutabilityCtx.rename] at hmem
              cases hmem
            | unbound m0 =>
              cases m with
              | epsilon => exact HasKind.rw
              | ro => exact HasKind.imm Ctx.LookupLock.here hmem
          · -- hsep: invert the substituted + lock-renamed origin lock to ORIGIN peaks
            -- (all cvars, since origin is pseudo-free), then separate them in `Ψ_L`.
            intro C1 C2 hdist
            simp only [ModalCtx.rename, ModalCtx.subst] at hdist
            exact compile_peakSepCtx_sep_backward_realign hclSub
              (SubstCompat.realign_weakenTarget (k := Kind.cvar) hcompatAl) horig hTnp.2.1
              hiso hscS (fun X => let ⟨Z, hZ, _⟩ := htvar X; ⟨Z, hZ⟩)
              hsubsto hstab C1 C2 hdist
        case bodyB =>
          set ΨL : ModalCtx (s2',,Kind.cvar) :=
            { sep := peakSepCtx ctxSub.capyCtx
                (CapyCaptureSet.peakset ctxSub.capyCtx (CapyCaptureSet.subst cs σ))
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
          have hge := (CapyTy.compile_subst_subtyp E (ctxSub := ctxSub'') (ctxOrig := ctxOrig'')
            (σ := σ.lift)
            (σt := σt.lift.lift)
            ((SubstCompat.weakenConsCVar hcompat).weakenTarget)
            ((SubstTvarCompat.weakenConsCVar htvar).weakenTarget)
            hECl hpb
            (hdrop.liftShift2 (fun _ hh => CapyTy.tgtCvarOccurs_cpoly_body hh))
            (SubstCompat.realign_weakenConsCVar hcompatAl).realign_weakenTarget
            (CapyCtx.IsClosed.push hclSub (CapyBinding.IsClosed.cvar
              (CapyCaptureBound.is_closed_subst hcb hscS)))
            (CapyCtx.IsClosed.push hclOrig (CapyBinding.IsClosed.cvar hcb))
            (Subst.lift_closed (Subst.lift_closed hscl))
            hvcSub.weaken.consCVar.weaken hvcOrig.weaken.consCVar.weaken
            (Ctx.IsClosed.push
              (Ctx.IsClosed.push hcoreSub (Binding.IsClosed.cvar
                (CaptureBound.is_closed_subst
                  (CapyCaptureBound.compile_isClosed hcb hvcOrig) hscl)))
              (Binding.IsClosed.lock ⟨peakSepCtx_isClosed
                (CapyCaptureSet.peaks_isClosed _ _) hvcSub.weaken,
                CapyCaptureBound.mutabilityCtx_isClosed⟩))
            (CapySubst.lift_closed hscS)
            (SrcCtx.CVarInjective.rename
              (SrcCtx.CVarInjective.consCVarHere hinj) Rename.injective_succ)
            (hiso.lift Kind.cvar) horig hTnp.2.2
            hsubsto.consCVar (hstab.pushCVar cb)).2
          have heq1 : CapyTy.compile (E.subst σ.lift) ctxSub''
              = (CapyTy.compile (E.subst σ.lift) csub').rename Rename.succ :=
            CapyTy.compile_rename (E.subst σ.lift) csub' ctxSub'' Rename.succ rfl rfl
          have heq2 : CapyTy.compile E ctxOrig''
              = (CapyTy.compile E corig').rename Rename.succ :=
            CapyTy.compile_rename E corig' ctxOrig'' Rename.succ rfl rfl
          convert hge using 2
          · rw [heq2]; exact Ty.weaken_subst_comm_base
          · exact heq1.symm
termination_by tySize T
decreasing_by
  all_goals first
    | (simp only [tySize]; omega)
    | (simp only [tySize, tySize_rename, tySize_refineCaptureSet]; omega)

/-! ### Base `openCVar` instances — the `fresh` wiring (`CapyHasType.compile`)

`compile_subst_subtyp`, instantiated at the existential opening
`σ = CapySubst.openCVar D` / `σt = Subst.openCVar ⟦D⟧`,
`ctxOrig = ctx.weakenTarget.consCVar cb .here` (the `.exi` compiler context),
`ctxSub = ctx`.  Each lemma below discharges one hypothesis of that instantiation
from the `fresh` rule's premises and the `Coherent` invariant. -/

/-- Closedness of the opened-cvar substitution (source side). -/
theorem CapySubst.IsClosed.openCVar {s : Sig} {D : CapyCaptureSet s} (h : D.IsClosed) :
    (CapySubst.openCVar D).IsClosed where
  var_closed := by
    intro x
    cases x with
    | there x0 => exact Var.IsClosed.bound
  tvar_closed := by
    intro X
    cases X with
    | there X0 => exact CapyTy.IsClosed.tvar
  cvar_closed := by
    intro c
    cases c with
    | here => exact CapyCaptureSet.IsClosed.pseudo_peak h
    | there c0 => exact CapyCaptureSet.IsClosed.cvar

/-- Closedness of the opened-cvar substitution (target side). -/
theorem Subst.IsClosed.openCVar {s : Sig} {C : CaptureSet s} (h : C.IsClosed) :
    (Subst.openCVar C).IsClosed where
  var_closed := by
    intro x
    cases x with
    | there x0 => exact Var.IsClosed.bound
  tvar_closed := by
    intro X
    cases X with
    | there X0 => exact Ty.IsClosed.tvar
  cvar_closed := by
    intro c
    cases c with
    | here => exact h
    | there c0 => exact CaptureSet.IsClosed.cvar

/-- Opening a fresh cvar is a source-context morphism `(Γ,C<:cb) ⇒σ Γ`: every var's
    declared type loses its vacuous weakening (`weaken_openCVar`). -/
theorem CapyCtx.SubstsTo.openCVar {s : Sig} {Γ : CapyCtx s} {cb : CapyCaptureBound s}
    {D : CapyCaptureSet s} :
    (Γ,C<:cb).SubstsTo Γ (CapySubst.openCVar D) where
  var := by
    intro x T hlook
    simp only [CapyCtx.push_cvar_default, CapyCtx.push_cvar] at hlook
    cases hlook with
    | there hlook0 =>
      exact ⟨_, _, rfl, hlook0,
        ((congrArg (fun z => CapyCaptureSet.subst z (CapySubst.openCVar D))
          CapyTy.captureSet_rename).trans CapyCaptureSet.weaken_openCVar).symm⟩

/-- Opening an `.unbound`-bounded cvar preserves per-peak stability: the opened cvar
    (stable) freezes to an always-stable `pseudo` peak; every other cvar maps to
    itself, with its binding untouched. -/
theorem PeakSubstIso.StablePreserving.openCVar {s : Sig} {Γ : CapyCtx s} {m : Mutability}
    {D : CapyCaptureSet s} :
    (PeakSubstIso.openCVar D).StablePreserving (Γ,C<:.unbound m) Γ := by
  intro c
  cases c with
  | here =>
    constructor
    · intro _
      exact trivial
    · intro _
      exact Or.inr ⟨m, rfl⟩
  | there c0 =>
    change Peak.IsStable (Γ,C<:.unbound m) ((Peak.cvar c0).rename Rename.succ)
      ↔ Peak.IsStable Γ (Peak.cvar c0)
    exact Peak.IsStable.renamesTo_iff
      (CapyCtx.RenamesTo.weaken (CapyBinding.cvar .access_only (.unbound m)))

/-- `TgtPairDroppable` at the target opening of a DROPPABLE compiled set: distinct
    cvars among `⟦D⟧`'s peaks are pairwise droppable (`CaptureSet.droppable` is
    exactly per-peak droppability), and a non-opened cvar's image is a singleton
    (no two distinct cvars fit). -/
theorem TgtPairDroppable.openCVar {s : Sig} {Γt : Ctx s} {C : CaptureSet s}
    (hdrop : CaptureSet.droppable Γt C) :
    TgtPairDroppable Γt (Subst.openCVar C) := by
  intro Y a1 a2 c1 c2 hne h1 h2
  cases Y with
  | here => exact ⟨hdrop a1 c1 h1, hdrop a2 c2 h2, hne⟩
  | there y =>
    simp only [Subst.openCVar, CaptureSet.peaks] at h1 h2
    cases h1
    cases h2
    exact absurd rfl hne

/-- **Split-covering analog of `TgtPairDroppable.openCVar` (fresh-site premise #5).**
    At the target opening of a DROPPABLE compiled set, distinct cvars among `⟦D⟧`'s peaks
    are pairwise-`SepCheck`-separated (via `sep_droppable`, the covering analog of
    `CaptureSet.droppable`'s per-peak droppability); a non-opened cvar's image is a
    singleton, so no two distinct cvars fit (vacuous).  Directly scoped by any `P`. -/
theorem TgtSplitCoveredOn.openCVar {s : Sig} {Γt : Ctx s} {C : CaptureSet s}
    {P : BVar (s,,Kind.cvar) .cvar → Prop} (hdrop : CaptureSet.droppable Γt C) :
    TgtSplitCoveredOn P Γt (Subst.openCVar C) := by
  intro Y _ a1 a2 c1 c2 hne h1 h2 m1 m2
  cases Y with
  | here => exact SepCheck.sep_droppable ⟨hdrop a1 c1 h1, hdrop a2 c2 h2, hne⟩
  | there y =>
    simp only [Subst.openCVar, CaptureSet.peaks] at h1 h2
    cases h1
    cases h2
    exact absurd rfl hne

/-- **Covering analog of `TgtSplitCoveredOn.openCVar` (app-site premise #5).**  Whereas
    `TgtSplitCoveredOn.openCVar` discharges the opened-cvar's distinct-peak separations from
    per-peak DROPPABILITY (a fresh-rule premise `⟦D⟧.droppable`), the application site has NO
    droppability for its capture argument `D`; instead the ambient covering `SepCovered U`
    (restricted through `app_use_covered`'s `SubP D ⊑ U`) supplies the very target-peak
    self-separations of `⟦D⟧` as the hypothesis `hsep`.  The non-opened cvar image is a
    singleton (vacuous), identical to the droppability twin. -/
theorem TgtSplitCoveredOn.openCVar_covered {s : Sig} {Γt : Ctx s} {C : CaptureSet s}
    {P : BVar (s,,Kind.cvar) .cvar → Prop}
    (hsep : ∀ (a1 a2 : Access) (c1 c2 : BVar s .cvar), c1 ≠ c2 →
        (CaptureSet.cvar a1 c1) ⊆ CaptureSet.peaks Γt C →
        (CaptureSet.cvar a2 c2) ⊆ CaptureSet.peaks Γt C →
        ∀ (m1 m2 : Access), SepCheck Γt (CaptureSet.cvar m1 c1) (CaptureSet.cvar m2 c2)) :
    TgtSplitCoveredOn P Γt (Subst.openCVar C) := by
  intro Y _ a1 a2 c1 c2 hne h1 h2 m1 m2
  cases Y with
  | here => exact hsep a1 a2 c1 c2 hne h1 h2 m1 m2
  | there y =>
    simp only [Subst.openCVar, CaptureSet.peaks] at h1 h2
    cases h1
    cases h2
    exact absurd rfl hne

/-- The realign-surrogate `SubstCompat` at the fresh site: on a `Coherent` base
    context `realign` is the identity (`SrcAligned` via `Coherent.srcAligned`), so
    this is `SubstCompat.openCVar` after rewriting both surrogates away. -/
theorem SubstCompat.realign_openCVar {s1 s2 : Sig} {ctx : CompilerCtx s1 s2}
    (hcoh : ctx.Coherent) {cb : CapyCaptureBound s1} {D : CapyCaptureSet s1} :
    SubstCompat (SrcCtx.realign ctx.capyCtx ctx.srcCtx)
      (SrcCtx.realign (ctx.capyCtx,C<:cb)
        (.cons (.cvar .here) (ctx.srcCtx.rename Rename.succ)))
      (CapySubst.openCVar D)
      (Subst.openCVar (CapyCaptureSet.compile D ctx.srcCtx)) := by
  have hself : SrcCtx.realign ctx.capyCtx ctx.srcCtx = ctx.srcCtx :=
    SrcCtx.realign_eq_self _ _ hcoh.srcAligned
  have horig : SrcCtx.realign (ctx.capyCtx,C<:cb)
      (.cons (.cvar .here) (ctx.srcCtx.rename Rename.succ))
      = .cons (.cvar .here) (ctx.srcCtx.rename Rename.succ) := by
    change SrcCtx.cons (SrcBinderInfo.cvar BVar.here)
        (SrcCtx.realign ctx.capyCtx (ctx.srcCtx.rename Rename.succ))
      = SrcCtx.cons (SrcBinderInfo.cvar BVar.here) (ctx.srcCtx.rename Rename.succ)
    rw [SrcCtx.realign_rename, hself]
  rw [hself, horig]
  exact SubstCompat.openCVar

/-! ### Closedness reflects along substitution

Free heap atoms survive ANY substitution (`CapyVar.subst` keeps `.free`), so a
closed substitution-image forces a closed pre-image.  Recovers the `fresh` rule's
existential witness `T`'s closedness from the looked-up `T[openCVar D]`'s. -/

theorem CapyCaptureSet.isClosed_of_subst {s1 s2 : Sig} {cs : CapyCaptureSet s1}
    {σ : CapySubst s1 s2} (h : (cs.subst σ).IsClosed) : cs.IsClosed := by
  induction cs with
  | empty => exact CapyCaptureSet.IsClosed.empty
  | union cs1 cs2 ih1 ih2 =>
    simp only [CapyCaptureSet.subst] at h
    cases h with | union h1 h2 => exact CapyCaptureSet.IsClosed.union (ih1 h1) (ih2 h2)
  | cvar a c => exact CapyCaptureSet.IsClosed.cvar
  | var a x =>
    cases x with
    | bound x0 => exact CapyCaptureSet.IsClosed.var_bound
    | free n =>
      simp only [CapyCaptureSet.subst, CapyVar.subst] at h
      nomatch h
  | pseudo_peak C ih =>
    simp only [CapyCaptureSet.subst] at h
    cases h with | pseudo_peak h0 => exact CapyCaptureSet.IsClosed.pseudo_peak (ih h0)

theorem CapyCaptureBound.isClosed_of_subst {s1 s2 : Sig} {cb : CapyCaptureBound s1}
    {σ : CapySubst s1 s2} (h : (cb.subst σ).IsClosed) : cb.IsClosed := by
  cases cb with
  | unbound m => exact CapyCaptureBound.IsClosed.unbound
  | bound cs =>
    simp only [CapyCaptureBound.subst] at h
    cases h with
    | bound h0 => exact CapyCaptureBound.IsClosed.bound (CapyCaptureSet.isClosed_of_subst h0)

theorem CapyTy.isClosed_of_subst {sort : CapyTySort} {s1 : Sig} {T : CapyTy sort s1} :
    ∀ {s2 : Sig} {σ : CapySubst s1 s2}, (T.subst σ).IsClosed → T.IsClosed := by
  induction T with
  | top => intro _ _ _; exact CapyTy.IsClosed.top
  | tvar X => intro _ _ _; exact CapyTy.IsClosed.tvar
  | unit => intro _ _ _; exact CapyTy.IsClosed.unit
  | bool => intro _ _ _; exact CapyTy.IsClosed.bool
  | cap cs =>
    intro _ _ h
    simp only [CapyTy.subst] at h
    cases h with | cap h0 => exact CapyTy.IsClosed.cap (CapyCaptureSet.isClosed_of_subst h0)
  | cell cs m =>
    intro _ _ h
    simp only [CapyTy.subst] at h
    cases h with | cell h0 => exact CapyTy.IsClosed.cell (CapyCaptureSet.isClosed_of_subst h0)
  | arrow T1 cs T2 ih1 ih2 =>
    intro _ _ h
    simp only [CapyTy.subst] at h
    cases h with
    | arrow h1 hcs h2 =>
      exact CapyTy.IsClosed.arrow (ih1 h1) (CapyCaptureSet.isClosed_of_subst hcs) (ih2 h2)
  | poly T1 cs T2 ih1 ih2 =>
    intro _ _ h
    simp only [CapyTy.subst] at h
    cases h with
    | poly h1 hcs h2 =>
      exact CapyTy.IsClosed.poly (ih1 h1) (CapyCaptureSet.isClosed_of_subst hcs) (ih2 h2)
  | cpoly cb cs T0 ih =>
    intro _ _ h
    simp only [CapyTy.subst] at h
    cases h with
    | cpoly hcb hcs h0 =>
      exact CapyTy.IsClosed.cpoly (CapyCaptureBound.isClosed_of_subst hcb)
        (CapyCaptureSet.isClosed_of_subst hcs) (ih h0)
  | exi T0 ih =>
    intro _ _ h
    simp only [CapyTy.subst] at h
    cases h with | exi h0 => exact CapyTy.IsClosed.exi (ih h0)
  | typ T0 ih =>
    intro _ _ h
    simp only [CapyTy.subst] at h
    cases h with | typ h0 => exact CapyTy.IsClosed.typ (ih h0)

end Compilation
