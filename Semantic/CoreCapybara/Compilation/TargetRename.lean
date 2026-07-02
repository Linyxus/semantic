import Semantic.CoreCapybara.Compilation.ContextMorphism
open CoreCapybara
namespace CoreCapybara

/-!
# Renaming (weakening) for the target (CoreCapybara) typing judgments

Given a context morphism `Γ.RenamesTo Γ' f` (from `ContextMorphism.lean`) together
with `f.Injective`, every target-calculus typing judgment renames.  The headline
result is `HasType.renamesTo`, from which `HasType.weaken` (push one closed binding)
follows.

Everything here is a *pure target-calculus* fact, so it lives in the `CoreCapybara`
namespace; the file is under `Compilation/` only because `Ctx.RenamesTo` is defined
there.
-/

/-! ## Small syntactic helpers -/

/-- A closed binding renames to a closed binding. -/
theorem Binding.IsClosed.rename {s1 s2 : Sig} {k : Kind} {b : Binding s1 k}
    {f : Rename s1 s2} (h : b.IsClosed) : (b.rename f).IsClosed := by
  cases h with
  | var hT => exact .var (Ty.rename_closed hT)
  | tvar hT => exact .tvar (Ty.rename_closed hT)
  | cvar hcb => exact .cvar (CaptureBound.rename_closed hcb)
  | lock hΨ => exact .lock (ModalCtx.rename_closed hΨ)

/-- Weakening commutes with renaming under a binder, for expressions. -/
theorem Exp.weaken_rename_comm {s1 s2 : Sig} {k0 : Kind} {e : Exp s1} {f : Rename s1 s2} :
    (e.rename Rename.succ).rename (f.lift (k := k0)) = (e.rename f).rename Rename.succ := by
  rw [Exp.rename_comp, Rename.succ_lift_comm, ← Exp.rename_comp]

/-! ## Context morphism builders -/

/-- A target typing context renames into its own one-binder extension by `succ`. -/
theorem Ctx.RenamesTo.weaken {s : Sig} {k : Kind} {Γ : Ctx s}
    (b : Binding s k) : Γ.RenamesTo (Γ.push b) Rename.succ where
  var hl := Ctx.LookupVar.there hl
  cvar hl := Ctx.LookupCVar.there hl
  tvar hl := Ctx.LookupTVar.there hl
  lock hl := Ctx.LookupLock.there hl

/-- A morphism out of an *extended* source context restricts to one out of the tail,
    precomposed with `succ` (target analogue of `CapyCtx.RenamesTo.unpush`). -/
theorem Ctx.RenamesTo.unpush {s1 s2 : Sig} {k : Kind} {Γ1 : Ctx s1}
    {b : Binding s1 k} {Γ2 : Ctx s2} {f : Rename (s1,,k) s2}
    (h : (Γ1.push b).RenamesTo Γ2 f) : Γ1.RenamesTo Γ2 (Rename.succ.comp f) where
  var hl := by
    have := h.var (Ctx.LookupVar.there (b := b) hl)
    rwa [Ty.rename_comp] at this
  cvar hl := by
    have := h.cvar (Ctx.LookupCVar.there (b := b) hl)
    rwa [CaptureBound.rename_comp] at this
  tvar hl := by
    have := h.tvar (Ctx.LookupTVar.there (b := b) hl)
    rwa [PureTy.rename_comp] at this
  lock hl := by
    have := h.lock (Ctx.LookupLock.there (b := b) hl)
    rwa [ModalCtx.rename_comp] at this

/-- Given `hclimp : Γ.IsClosed → Γ'.IsClosed`, closedness threads through a binder
    push: `(Γ.push b).IsClosed → (Γ'.push (b.rename f)).IsClosed`. -/
theorem Ctx.RenamesTo.hclimp_push {s1 s2 : Sig} {k : Kind} {Γ : Ctx s1} {Γ' : Ctx s2}
    {f : Rename s1 s2} {b : Binding s1 k} (hclimp : Γ.IsClosed → Γ'.IsClosed) :
    (Γ.push b).IsClosed → (Γ'.push (b.rename f)).IsClosed := by
  intro hc
  cases hc with
  | push hΓ hb => exact Ctx.IsClosed.push (hclimp hΓ) (Binding.IsClosed.rename hb)

/-! ## Peak resolution commutes with a context morphism -/

/-- Target peak-resolution commutes with a context renaming (mirror of
    `CapyCaptureSet.peaks_renamesTo`; no pseudo-peak constructor). -/
theorem CaptureSet.peaks_renamesTo {s1 s2 : Sig}
    {Γ1 : Ctx s1} {Γ2 : Ctx s2} {f : Rename s1 s2}
    (h : Γ1.RenamesTo Γ2 f) (W : CaptureSet s1) :
    CaptureSet.peaks Γ2 (W.rename f) = (CaptureSet.peaks Γ1 W).rename f := by
  match Γ1, W, h with
  | _, .empty, _ => simp only [CaptureSet.rename, CaptureSet.peaks]
  | _, .union W1 W2, h =>
    simp only [CaptureSet.rename, CaptureSet.peaks]
    rw [peaks_renamesTo h W1, peaks_renamesTo h W2]
    rfl
  | _, .cvar m c, _ => simp only [CaptureSet.rename, CaptureSet.peaks]
  | _, .var m (.free n), _ =>
    simp only [CaptureSet.rename, Var.rename, CaptureSet.peaks]
    rfl
  | .push Γ1' (.var T0), .var m (.bound .here), h =>
    have hl2 := h.var (Ctx.LookupVar.here (Γ := Γ1') (T := T0))
    have key := CaptureSet.peaks_renamesTo (h.unpush) (T0.captureSet.applyAccess m)
    simp only [CaptureSet.rename, Var.rename]
    rw [CaptureSet.var_peaks hl2]
    simp only [Ty.captureSet_rename, CaptureSet.rename_comp,
      ← CaptureSet.applyAccess_rename]
    rw [key]
    simp only [CaptureSet.peaks, CaptureSet.peaksVarBound,
      CaptureSet.peaks_applyAccess_comm, CaptureSet.applyAccess_rename,
      CaptureSet.rename_comp]
  | .push Γ1' b, .var m (.bound (.there x')), h =>
    have key := CaptureSet.peaks_renamesTo (h.unpush) (CaptureSet.var m (.bound x'))
    simp only [CaptureSet.rename, Var.rename, Rename.comp, Rename.succ,
      CaptureSet.peaks, CaptureSet.peaksVarBound, CaptureSet.rename_comp] at key ⊢
    exact key
  termination_by (sizeOf Γ1, sizeOf W)

/-- Thin wrapper: peak-resolution commutes with a context morphism. -/
theorem Ctx.RenamesTo.peaks {s1 s2 : Sig} {Γ1 : Ctx s1} {Γ2 : Ctx s2}
    {f : Rename s1 s2} (h : Γ1.RenamesTo Γ2 f) {W : CaptureSet s1} :
    CaptureSet.peaks Γ2 (W.rename f) = (CaptureSet.peaks Γ1 W).rename f :=
  CaptureSet.peaks_renamesTo h W

/-- The whole peak set commutes with a context morphism. -/
theorem Ctx.RenamesTo.peakset {s1 s2 : Sig} {Γ1 : Ctx s1} {Γ2 : Ctx s2}
    {f : Rename s1 s2} (h : Γ1.RenamesTo Γ2 f) (W : CaptureSet s1) :
    CaptureSet.peakset Γ2 (W.rename f) = (CaptureSet.peakset Γ1 W).rename f := by
  simp only [CaptureSet.peakset, PeakSet.rename, h.peaks]

/-! ## Copied structural lemmas (kept file-local to avoid import weight/clashes) -/

/-- Renaming preserves capture-set subset (copy of `CaptureSet.Subset.rename` under a
    fresh name, to avoid importing the heavy `LockKernel`). -/
theorem CaptureSet.Subset.renameF {s1 s2 : Sig} {C1 C2 : CaptureSet s1} {f : Rename s1 s2}
    (h : C1.Subset C2) : (C1.rename f).Subset (C2.rename f) := by
  induction h with
  | refl => exact .refl
  | empty => exact .empty
  | union_left _ _ ih1 ih2 => exact .union_left ih1 ih2
  | union_right_left _ ih => exact .union_right_left ih
  | union_right_right _ ih => exact .union_right_right ih

/-- Inversion of a `cvar` subset through a renaming (file-local copy of the Rebind
    lemma of the same name; `private` avoids a clash when both are co-imported). -/
private theorem CaptureSet.PeaksOnly.cvar_subset_rename_inv
  {s1 s2 : Sig} {cs : CaptureSet s1} (hpo : cs.PeaksOnly) {f : Rename s1 s2}
  {m : Access} {c : BVar s2 .cvar}
  (hsub : (.cvar m c) ⊆ cs.rename f) :
  ∃ c', f.var c' = c ∧ (.cvar m c') ⊆ cs := by
  induction hpo with
  | empty =>
    simp only [CaptureSet.rename] at hsub
    cases hsub
  | cvar =>
    simp only [CaptureSet.rename] at hsub
    cases hsub
    exact ⟨_, rfl, .refl⟩
  | union _ _ ih1 ih2 =>
    simp only [CaptureSet.rename] at hsub
    cases hsub with
    | union_right_left hsub1 =>
      obtain ⟨c', hfc, hsub'⟩ := ih1 hsub1
      exact ⟨c', hfc, .union_right_left hsub'⟩
    | union_right_right hsub2 =>
      obtain ⟨c', hfc, hsub'⟩ := ih2 hsub2
      exact ⟨c', hfc, .union_right_right hsub'⟩

/-- `consumed` commutes with renaming. -/
theorem CaptureSet.consumed_rename {s1 s2 : Sig} {cs : CaptureSet s1} {f : Rename s1 s2} :
    (cs.rename f).consumed = cs.consumed.rename f := by
  induction cs with
  | empty => rfl
  | union cs1 cs2 ih1 ih2 =>
    simp only [CaptureSet.rename, CaptureSet.consumed, ih1, ih2]
  | var m x => cases x <;> rfl
  | cvar m c =>
    cases m with
    | M mu => simp only [CaptureSet.rename, CaptureSet.consumed]
    | drop => simp only [CaptureSet.rename, CaptureSet.consumed]

/-- The consumed peak set commutes with renaming. -/
theorem PeakSet.consumed_rename {s1 s2 : Sig} {P : PeakSet s1} {f : Rename s1 s2} :
    (P.rename f).consumed = P.consumed.rename f := by
  cases P with
  | mk cs h =>
    simp only [PeakSet.rename, PeakSet.consumed]
    congr 1
    exact CaptureSet.consumed_rename

/-! ## Authority and peak-predicate transports -/

/-- A cvar's authority is transported exactly along a context morphism. -/
theorem Ctx.RenamesTo.lookup_authority_eq {s1 s2 : Sig} {Γ : Ctx s1} {Γ' : Ctx s2}
    {f : Rename s1 s2} (h : Γ.RenamesTo Γ' f) (c : BVar s1 .cvar) :
    Γ'.lookup_authority (f.var c) = Γ.lookup_authority c :=
  (h.cvar (Ctx.lookup_cvar_spec Γ c)).eq_authority.symm

/-- `AccessOnly` transports along a context morphism. -/
theorem CaptureSet.AccessOnly.renamesTo {s1 s2 : Sig} {Γ : Ctx s1} {Γ' : Ctx s2}
    {f : Rename s1 s2} {C : CaptureSet s1}
    (hAO : C.AccessOnly Γ) (h : Γ.RenamesTo Γ' f) : (C.rename f).AccessOnly Γ' := by
  intro c' hsub
  change (CaptureSet.cvar .drop c') ⊆ CaptureSet.peaks Γ' (C.rename f) at hsub
  rw [CaptureSet.peaks_renamesTo h C] at hsub
  obtain ⟨c0, _, hsub0⟩ := (CaptureSet.peaks_peaksOnly Γ C).cvar_subset_rename_inv hsub
  exact hAO c0 hsub0

/-- `accessible` transports along a context morphism. -/
theorem CaptureSet.accessible.renamesTo {s1 s2 : Sig} {Γ : Ctx s1} {Γ' : Ctx s2}
    {f : Rename s1 s2} {C : CaptureSet s1}
    (hacc : C.accessible Γ) (h : Γ.RenamesTo Γ' f) : (C.rename f).accessible Γ' := by
  intro a c' hsub
  change (CaptureSet.cvar a c') ⊆ CaptureSet.peaks Γ' (C.rename f) at hsub
  rw [CaptureSet.peaks_renamesTo h C] at hsub
  obtain ⟨c0, rfl, hsub0⟩ := (CaptureSet.peaks_peaksOnly Γ C).cvar_subset_rename_inv hsub
  rw [h.lookup_authority_eq c0]
  exact hacc a c0 hsub0

/-- `PeakSet.droppable` transports along a context morphism. -/
theorem PeakSet.droppable.renamesTo {s1 s2 : Sig} {Γ : Ctx s1} {Γ' : Ctx s2}
    {f : Rename s1 s2} {P : PeakSet s1}
    (hdrop : P.droppable Γ) (h : Γ.RenamesTo Γ' f) : (P.rename f).droppable Γ' := by
  intro a c' hsub
  change (CaptureSet.cvar a c') ⊆ P.cs.rename f at hsub
  obtain ⟨c0, rfl, hsub0⟩ := P.h.cvar_subset_rename_inv hsub
  rw [h.lookup_authority_eq c0]
  exact hdrop a c0 hsub0

/-- `CaptureSet.droppable` transports along a context morphism. -/
theorem CaptureSet.droppable.renamesTo {s1 s2 : Sig} {Γ : Ctx s1} {Γ' : Ctx s2}
    {f : Rename s1 s2} {C : CaptureSet s1}
    (hdrop : C.droppable Γ) (h : Γ.RenamesTo Γ' f) : (C.rename f).droppable Γ' := by
  intro a c' hsub
  change (CaptureSet.cvar a c') ⊆ CaptureSet.peaks Γ' (C.rename f) at hsub
  rw [CaptureSet.peaks_renamesTo h C] at hsub
  obtain ⟨c0, rfl, hsub0⟩ := (CaptureSet.peaks_peaksOnly Γ C).cvar_subset_rename_inv hsub
  rw [h.lookup_authority_eq c0]
  exact hdrop a c0 hsub0

/-- Peak-level subset transports along a context morphism. -/
theorem CaptureSet.SubP.renamesTo {s1 s2 : Sig} {Γ : Ctx s1} {Γ' : Ctx s2}
    {f : Rename s1 s2} {C1 C2 : CaptureSet s1}
    (hsub : CaptureSet.SubP Γ C1 C2) (h : Γ.RenamesTo Γ' f) :
    CaptureSet.SubP Γ' (C1.rename f) (C2.rename f) := by
  unfold CaptureSet.SubP at hsub ⊢
  rw [h.peaks, h.peaks]
  exact hsub.rename

/-- Peak-level equivalence transports along a context morphism. -/
theorem CaptureSet.EquivP.renamesTo {s1 s2 : Sig} {Γ : Ctx s1} {Γ' : Ctx s2}
    {f : Rename s1 s2} {C1 C2 : CaptureSet s1}
    (heq : CaptureSet.EquivP Γ C1 C2) (h : Γ.RenamesTo Γ' f) :
    CaptureSet.EquivP Γ' (C1.rename f) (C2.rename f) :=
  ⟨heq.1.renamesTo h, heq.2.renamesTo h⟩

/-! ## `Subcapt`, `HasKind`, `Subbound` -/

/-- `Subcapt` transports along a context morphism. -/
theorem Subcapt.renamesTo {s1 s2 : Sig} {Γ : Ctx s1} {C1 C2 : CaptureSet s1}
    (hsc : Subcapt Γ C1 C2) {Γ' : Ctx s2} {f : Rename s1 s2} (h : Γ.RenamesTo Γ' f) :
    Subcapt Γ' (C1.rename f) (C2.rename f) := by
  induction hsc with
  | sc_trans _ _ ih1 ih2 => exact Subcapt.sc_trans (ih1 h) (ih2 h)
  | sc_elem hsub => exact Subcapt.sc_elem hsub.renameF
  | sc_mode hle =>
    simp only [CaptureSet.applyMut_rename]
    exact Subcapt.sc_mode hle
  | sc_union _ _ ih1 ih2 =>
    simp only [CaptureSet.rename]
    exact Subcapt.sc_union (ih1 h) (ih2 h)
  | sc_var hlk =>
    simp only [CaptureSet.rename, Var.rename, ← Ty.captureSet_rename]
    exact Subcapt.sc_var (h.var hlk)
  | sc_cvar hlk =>
    simp only [CaptureSet.rename]
    exact Subcapt.sc_cvar (h.cvar hlk)
  | sc_ro =>
    simp only [CaptureSet.applyRO_rename]
    exact Subcapt.sc_ro
  | sc_ro_mono _ ih =>
    simp only [CaptureSet.applyRO_rename]
    exact Subcapt.sc_ro_mono (ih h)
  | sc_drop_mono _ ih =>
    simp only [CaptureSet.applyAccess_rename]
    exact Subcapt.sc_drop_mono (ih h)

/-- `HasKind` transports along a context morphism. -/
theorem HasKind.renamesTo {s1 s2 : Sig} {Γ : Ctx s1} {C : CaptureSet s1} {m : Mutability}
    (hk : HasKind Γ C m) {Γ' : Ctx s2} {f : Rename s1 s2} (h : Γ.RenamesTo Γ' f) :
    HasKind Γ' (C.rename f) m := by
  induction hk with
  | empty => exact HasKind.empty
  | union _ _ ih1 ih2 =>
    simp only [CaptureSet.rename]
    exact HasKind.union ih1 ih2
  | sc hsub _ ih => exact HasKind.sc (hsub.renamesTo h) ih
  | rw => exact HasKind.rw
  | imm hlk hmem =>
    exact HasKind.imm (h.lock hlk) (by
      simp only [ModalCtx.rename_mutability] at *
      exact hmem.rename)
  | ro =>
    simp only [CaptureSet.applyRO_rename]
    exact HasKind.ro

/-- `Subbound` transports along a context morphism. -/
theorem Subbound.renamesTo {s1 s2 : Sig} {Γ : Ctx s1} {cb1 cb2 : CaptureBound s1}
    (hsb : Subbound Γ cb1 cb2) {Γ' : Ctx s2} {f : Rename s1 s2} (h : Γ.RenamesTo Γ' f) :
    Subbound Γ' (cb1.rename f) (cb2.rename f) := by
  cases hsb with
  | capset hsc => exact Subbound.capset (hsc.renamesTo h)
  | top => exact Subbound.top

/-! ## `SepCheck`, `Satisfy`, `SeqComp` -/

/-- `SepCheck` transports along an injective context morphism. -/
theorem SepCheck.renamesTo {s1 s2 : Sig} {Γ : Ctx s1} {C1 C2 : CaptureSet s1}
    (hsep : SepCheck Γ C1 C2) {Γ' : Ctx s2} {f : Rename s1 s2}
    (h : Γ.RenamesTo Γ' f) (hinj : f.Injective) :
    SepCheck Γ' (C1.rename f) (C2.rename f) := by
  induction hsep with
  | sep_symm _ ih => exact SepCheck.sep_symm ih
  | sep_union _ _ ih1 ih2 =>
    simp only [CaptureSet.rename]
    exact SepCheck.sep_union ih1 ih2
  | sep_empty => exact SepCheck.sep_empty
  | sep_ro hc1 hc2 hao1 hao2 hk1 hk2 =>
    exact SepCheck.sep_ro (CaptureSet.rename_closed hc1) (CaptureSet.rename_closed hc2)
      (hao1.renamesTo h) (hao2.renamesTo h) (hk1.renamesTo h) (hk2.renamesTo h)
  | sep_sc _ hsc heq ih =>
    exact SepCheck.sep_sc ih (hsc.renamesTo h) (heq.renamesTo h)
  | sep_mono _ hsc ih =>
    exact SepCheck.sep_mono ih (hsc.renamesTo h)
  | sep_lock hlk htwo =>
    refine SepCheck.sep_lock (h.lock hlk) ?_
    simp only [ModalCtx.rename_sep]
    exact htwo.rename
  | sep_droppable hdist =>
    obtain ⟨ha1, ha2, hne⟩ := hdist
    simp only [CaptureSet.rename]
    exact SepCheck.sep_droppable
      ⟨(h.lookup_authority_eq _).trans ha1, (h.lookup_authority_eq _).trans ha2,
       fun he => hne (hinj .cvar he)⟩

/-- `Satisfy` transports along an injective context morphism. -/
theorem Satisfy.renamesTo {s1 s2 : Sig} {Γ : Ctx s1} {Ψ : ModalCtx s1}
    (hsat : Satisfy Γ Ψ) {Γ' : Ctx s2} {f : Rename s1 s2}
    (h : Γ.RenamesTo Γ' f) (hinj : f.Injective) :
    Satisfy Γ' (Ψ.rename f) := by
  cases hsat with
  | satisfy hkind hsep =>
    apply Satisfy.satisfy
    · intro C m hhas
      simp only [ModalCtx.rename_mutability] at hhas
      obtain ⟨C0, rfl, hhas0⟩ := MutabilityCtx.Has.rename_inv hhas
      exact (hkind C0 m hhas0).renamesTo h
    · intro C1 C2 hhas
      simp only [ModalCtx.rename_sep] at hhas
      obtain ⟨D1, D2, rfl, rfl, hh0⟩ := SepCtx.HasTwoDistinct.rename_inv hhas
      exact (hsep D1 D2 hh0).renamesTo h hinj

/-- `SeqComp` transports along an injective context morphism. -/
theorem SeqComp.renamesTo {s1 s2 : Sig} {Γ : Ctx s1} {C1 C2 : CaptureSet s1}
    (hseq : SeqComp Γ C1 C2) {Γ' : Ctx s2} {f : Rename s1 s2}
    (h : Γ.RenamesTo Γ' f) (hinj : f.Injective) :
    SeqComp Γ' (C1.rename f) (C2.rename f) := by
  induction hseq with
  | seq_sc hsc heq _ ih =>
    exact SeqComp.seq_sc (hsc.renamesTo h) (heq.renamesTo h) ih
  | seq_union _ _ ih1 ih2 =>
    simp only [CaptureSet.rename]
    exact SeqComp.seq_union ih1 ih2
  | seq_access_only hc hao =>
    exact SeqComp.seq_access_only (CaptureSet.rename_closed hc) (hao.renamesTo h)
  | seq_sep hsep =>
    exact SeqComp.seq_sep (hsep.renamesTo h hinj)

/-! ## `Subtyp` -/

/-- `Subtyp` transports along an injective context morphism.  Threaded with the
    implication `Γ.IsClosed → Γ'.IsClosed` (`hclimp`) so `modal_modal` — whose only
    obligation over `Γ'` is `Γ'.IsClosed` — is dischargeable, while binder cases
    re-establish `hclimp` for the pushed (renamed, still-closed) binding. -/
theorem Subtyp.renamesTo {s : Sig} {Γ : Ctx s} {sort : TySort} {T1 T2 : Ty sort s}
    (hsub : Subtyp Γ T1 T2) :
    ∀ {s' : Sig} {Γ' : Ctx s'} {f : Rename s s'}, Γ.RenamesTo Γ' f → f.Injective →
      (Γ.IsClosed → Γ'.IsClosed) → Subtyp Γ' (T1.rename f) (T2.rename f) := by
  induction hsub with
  | top hpure => intro _ _ f h _ _; exact Subtyp.top (hpure.rename f)
  | refl => intro _ _ _ _ _ _; exact Subtyp.refl
  | trans hT2 _ _ ih1 ih2 =>
    intro _ _ _ h hinj hclimp
    exact Subtyp.trans (Ty.rename_closed hT2) (ih1 h hinj hclimp) (ih2 h hinj hclimp)
  | tvar hlk => intro _ _ _ h _ _; exact Subtyp.tvar (h.tvar hlk)
  | arrow _ hsc _ ihdom ihbody =>
    intro _ _ _ h hinj hclimp
    exact Subtyp.arrow (ihdom h hinj hclimp) (hsc.renamesTo h)
      (ihbody (h.push (.var _)) hinj.lift (Ctx.RenamesTo.hclimp_push hclimp))
  | poly _ hsc _ ihdom ihbody =>
    intro _ _ f h hinj hclimp
    simp only [Ty.rename,
      show ∀ (S : PureTy _), S.core.rename f = (S.rename f).core from fun _ => rfl]
    exact Subtyp.poly (ihdom h hinj hclimp) (hsc.renamesTo h)
      (ihbody (h.push (.tvar _)) hinj.lift (Ctx.RenamesTo.hclimp_push hclimp))
  | cpoly hsb hsc _ ihbody =>
    intro _ _ _ h hinj hclimp
    exact Subtyp.cpoly (hsb.renamesTo h) (hsc.renamesTo h)
      (ihbody (h.push (.cvar .access_only _)) hinj.lift (Ctx.RenamesTo.hclimp_push hclimp))
  | modal hsc _ ihbody =>
    intro _ _ _ h hinj hclimp
    have hb := ihbody (h.push (.lock _)) hinj.lift (Ctx.RenamesTo.hclimp_push hclimp)
    rw [Ty.weaken_rename_comm, Ty.weaken_rename_comm] at hb
    exact Subtyp.modal (hsc.renamesTo h) hb
  | modal_modal hΓcl hΨ1 hΨ2 hsat =>
    intro _ _ _ h hinj hclimp
    have hs := hsat.renamesTo (h.push (.lock _)) hinj.lift
    rw [ModalCtx.weaken_rename_comm] at hs
    exact Subtyp.modal_modal (hclimp hΓcl) (ModalCtx.rename_closed hΨ1)
      (ModalCtx.rename_closed hΨ2) hs
  | exi _ ihbody =>
    intro _ _ f h hinj hclimp
    exact Subtyp.exi
      (ihbody (h.push (.cvar .access_only .unbound)) hinj.lift
        (Ctx.RenamesTo.hclimp_push (f := f) hclimp))
  | typ _ ihbody => intro _ _ _ h hinj hclimp; exact Subtyp.typ (ihbody h hinj hclimp)
  | cell hsc => intro _ _ _ h _ _; exact Subtyp.cell (hsc.renamesTo h)
  | reader hsc => intro _ _ _ h _ _; exact Subtyp.reader (hsc.renamesTo h)
  | cap hsc => intro _ _ _ h _ _; exact Subtyp.cap (hsc.renamesTo h)
  | poly_cap hsc => intro _ _ _ h _ _; exact Subtyp.poly_cap (hsc.renamesTo h)

/-! ## Renaming commutes with the opening substitutions

These are the `subst`-level composition equalities behind `pack`/`app`/`tapp`/`capp`:
opening then renaming equals renaming (under `f.lift`) then opening the renamed
payload. -/

theorem Subst.openCVar_comp_asSubst {s1 s2 : Sig} {C : CaptureSet s1} {f : Rename s1 s2} :
    (Subst.openCVar C).comp (Rename.asSubst f)
      = (Rename.asSubst (f.lift (k := .cvar))).comp (Subst.openCVar (C.rename f)) := by
  apply Subst.funext
  · intro x; cases x with | there x0 => rfl
  · intro X; cases X with | there X0 => rfl
  · intro c
    cases c with
    | here =>
      change C.subst (Rename.asSubst f) = (C.rename f).applyAccess (.M .epsilon)
      rw [CaptureSet.subst_asSubst, CaptureSet.applyAccess_M, CaptureSet.applyMut_epsilon]
    | there c0 => rfl

theorem Subst.openVar_comp_asSubst {s1 s2 : Sig} {y : Var .var s1} {f : Rename s1 s2} :
    (Subst.openVar y).comp (Rename.asSubst f)
      = (Rename.asSubst (f.lift (k := .var))).comp (Subst.openVar (y.rename f)) := by
  apply Subst.funext
  · intro x
    cases x with
    | here =>
      change y.subst (Rename.asSubst f) = y.rename f
      exact Var.subst_asSubst
    | there x0 => rfl
  · intro X; cases X with | there X0 => rfl
  · intro c; cases c with | there c0 => rfl

theorem Subst.openTVar_comp_asSubst {s1 s2 : Sig} {S : PureTy s1} {f : Rename s1 s2} :
    (Subst.openTVar S).comp (Rename.asSubst f)
      = (Rename.asSubst (f.lift (k := .tvar))).comp (Subst.openTVar (S.rename f)) := by
  apply Subst.funext
  · intro x; cases x with | there x0 => rfl
  · intro X
    cases X with
    | here =>
      change S.subst (Rename.asSubst f) = S.rename f
      exact PureTy.subst_asSubst
    | there X0 => rfl
  · intro c; cases c with | there c0 => rfl

theorem Ty.rename_subst_openCVar {sort : TySort} {s1 s2 : Sig} {T : Ty sort (s1,C)}
    {C : CaptureSet s1} {f : Rename s1 s2} :
    (T.subst (Subst.openCVar C)).rename f
      = (T.rename f.lift).subst (Subst.openCVar (C.rename f)) :=
  calc (T.subst (Subst.openCVar C)).rename f
      = (T.subst (Subst.openCVar C)).subst (Rename.asSubst f) := Ty.subst_asSubst.symm
    _ = T.subst ((Subst.openCVar C).comp (Rename.asSubst f)) := Ty.subst_comp
    _ = T.subst ((Rename.asSubst f.lift).comp (Subst.openCVar (C.rename f))) := by
        rw [Subst.openCVar_comp_asSubst]
    _ = (T.subst (Rename.asSubst f.lift)).subst (Subst.openCVar (C.rename f)) := Ty.subst_comp.symm
    _ = (T.rename f.lift).subst (Subst.openCVar (C.rename f)) := by rw [Ty.subst_asSubst]

theorem Ty.rename_subst_openVar {sort : TySort} {s1 s2 : Sig} {T : Ty sort (s1,x)}
    {y : Var .var s1} {f : Rename s1 s2} :
    (T.subst (Subst.openVar y)).rename f
      = (T.rename f.lift).subst (Subst.openVar (y.rename f)) :=
  calc (T.subst (Subst.openVar y)).rename f
      = (T.subst (Subst.openVar y)).subst (Rename.asSubst f) := Ty.subst_asSubst.symm
    _ = T.subst ((Subst.openVar y).comp (Rename.asSubst f)) := Ty.subst_comp
    _ = T.subst ((Rename.asSubst f.lift).comp (Subst.openVar (y.rename f))) := by
        rw [Subst.openVar_comp_asSubst]
    _ = (T.subst (Rename.asSubst f.lift)).subst (Subst.openVar (y.rename f)) := Ty.subst_comp.symm
    _ = (T.rename f.lift).subst (Subst.openVar (y.rename f)) := by rw [Ty.subst_asSubst]

theorem Ty.rename_subst_openTVar {sort : TySort} {s1 s2 : Sig} {T : Ty sort (s1,X)}
    {S : PureTy s1} {f : Rename s1 s2} :
    (T.subst (Subst.openTVar S)).rename f
      = (T.rename f.lift).subst (Subst.openTVar (S.rename f)) :=
  calc (T.subst (Subst.openTVar S)).rename f
      = (T.subst (Subst.openTVar S)).subst (Rename.asSubst f) := Ty.subst_asSubst.symm
    _ = T.subst ((Subst.openTVar S).comp (Rename.asSubst f)) := Ty.subst_comp
    _ = T.subst ((Rename.asSubst f.lift).comp (Subst.openTVar (S.rename f))) := by
        rw [Subst.openTVar_comp_asSubst]
    _ = (T.subst (Rename.asSubst f.lift)).subst (Subst.openTVar (S.rename f)) := Ty.subst_comp.symm
    _ = (T.rename f.lift).subst (Subst.openTVar (S.rename f)) := by rw [Ty.subst_asSubst]

/-! ## The `kill_peaks` context morphism

`kill_peaks`/`kill_cvar` change only cvar *authorities*, never the var/tvar/lock/cvar
*data*, so lookups (and closedness) transport.  The functional-lookup lemmas below
are file-local copies (distinct names + `private`) of the context-side lemmas in
`Denotation/Kill.lean`, kept here to avoid importing the denotation layer. -/

private theorem Ctx.killcvar_lookup_var {s : Sig} (Γ : Ctx s) (c : BVar s .cvar)
    (x : BVar s .var) : (Γ.kill_cvar c).lookup_var x = Γ.lookup_var x := by
  match Γ, c, x with
  | .push Γ (.cvar a cb), .here, .there x => rfl
  | .push Γ (.var T), .there c, .here => rfl
  | .push Γ b, .there c, .there x =>
    simp only [Ctx.kill_cvar, Ctx.lookup_var]
    rw [Ctx.killcvar_lookup_var Γ c x]

private theorem Ctx.killcvar_lookup_tvar {s : Sig} (Γ : Ctx s) (c : BVar s .cvar)
    (X : BVar s .tvar) : (Γ.kill_cvar c).lookup_tvar X = Γ.lookup_tvar X := by
  match Γ, c, X with
  | .push Γ (.cvar a cb), .here, .there X => rfl
  | .push Γ (.tvar S), .there c, .here => rfl
  | .push Γ b, .there c, .there X =>
    simp only [Ctx.kill_cvar, Ctx.lookup_tvar]
    rw [Ctx.killcvar_lookup_tvar Γ c X]

private theorem Ctx.killcvar_lookup_cvar {s : Sig} (Γ : Ctx s) (c : BVar s .cvar)
    (c' : BVar s .cvar) : (Γ.kill_cvar c).lookup_cvar c' = Γ.lookup_cvar c' := by
  match Γ, c, c' with
  | .push Γ (.cvar a cb), .here, .here => rfl
  | .push Γ (.cvar a cb), .here, .there c' => rfl
  | .push Γ (.cvar a cb), .there c, .here => rfl
  | .push Γ b, .there c, .there c' =>
    simp only [Ctx.kill_cvar, Ctx.lookup_cvar]
    rw [Ctx.killcvar_lookup_cvar Γ c c']

private theorem Ctx.killcvar_lookup_lock {s : Sig} (Γ : Ctx s) (c : BVar s .cvar)
    (ℓ : BVar s .lock) : (Γ.kill_cvar c).lookup_lock ℓ = Γ.lookup_lock ℓ := by
  match Γ, c, ℓ with
  | .push Γ (.cvar a cb), .here, .there ℓ => rfl
  | .push Γ (.lock Ψ), .there c, .here => rfl
  | .push Γ b, .there c, .there ℓ =>
    simp only [Ctx.kill_cvar, Ctx.lookup_lock]
    rw [Ctx.killcvar_lookup_lock Γ c ℓ]

private theorem Ctx.killcvar_authority_self {s : Sig} (Γ : Ctx s) (c : BVar s .cvar) :
    (Γ.kill_cvar c).lookup_authority c = .killed := by
  match Γ, c with
  | .push Γ (.cvar a cb), .here => rfl
  | .push Γ b, .there c =>
    simp only [Ctx.kill_cvar, Ctx.lookup_authority]
    exact Ctx.killcvar_authority_self Γ c

private theorem Ctx.killcvar_authority_ne {s : Sig} (Γ : Ctx s)
    {c c' : BVar s .cvar} (hne : c' ≠ c) :
    (Γ.kill_cvar c).lookup_authority c' = Γ.lookup_authority c' := by
  match Γ, c, c' with
  | .push Γ (.cvar a cb), .here, .here => exact absurd rfl hne
  | .push Γ (.cvar a cb), .here, .there c' => rfl
  | .push Γ (.cvar a cb), .there c, .here => rfl
  | .push Γ b, .there c, .there c' =>
    simp only [Ctx.kill_cvar, Ctx.lookup_authority]
    exact Ctx.killcvar_authority_ne Γ (fun h => hne (congrArg BVar.there h))

private theorem Ctx.killcvar_isClosed {s : Sig} {Γ : Ctx s} {c : BVar s .cvar}
    (h : Γ.IsClosed) : (Γ.kill_cvar c).IsClosed := by
  match Γ, c with
  | .push Γ (.cvar a cb), .here =>
    cases h with
    | push hΓ hb =>
      cases hb with
      | cvar hcb => exact Ctx.IsClosed.push hΓ (Binding.IsClosed.cvar hcb)
  | .push Γ b, .there c =>
    cases h with
    | push hΓ hb =>
      simp only [Ctx.kill_cvar]
      exact Ctx.IsClosed.push (Ctx.killcvar_isClosed hΓ) hb

private theorem Ctx.killcvar_isClosed_inv {s : Sig} {Γ : Ctx s} {c : BVar s .cvar}
    (h : (Γ.kill_cvar c).IsClosed) : Γ.IsClosed := by
  match Γ, c with
  | .push Γ (.cvar a cb), .here =>
    simp only [Ctx.kill_cvar] at h
    cases h with
    | push hΓ hb =>
      cases hb with
      | cvar hcb => exact Ctx.IsClosed.push hΓ (Binding.IsClosed.cvar hcb)
  | .push Γ b, .there c =>
    simp only [Ctx.kill_cvar] at h
    cases h with
    | push hΓ hb => exact Ctx.IsClosed.push (Ctx.killcvar_isClosed_inv hΓ) hb

/-- Single-`kill_cvar` context morphism (needs injectivity so the killed target cvar
    is distinguished from every other). -/
theorem Ctx.RenamesTo.kill_cvar {s1 s2 : Sig} {Γ : Ctx s1} {Γ' : Ctx s2} {f : Rename s1 s2}
    (h : Γ.RenamesTo Γ' f) (hinj : f.Injective) (c0 : BVar s1 .cvar) :
    (Γ.kill_cvar c0).RenamesTo (Γ'.kill_cvar (f.var c0)) f where
  var hl := by
    rename_i x _
    have hT := hl.eq_lookup.trans (Ctx.killcvar_lookup_var Γ c0 x)
    subst hT
    have h2 := h.var (Ctx.lookup_var_spec Γ x)
    have hspec := Ctx.lookup_var_spec (Γ'.kill_cvar (f.var c0)) (f.var x)
    rw [Ctx.killcvar_lookup_var Γ' (f.var c0), ← h2.eq_lookup] at hspec
    exact hspec
  tvar hl := by
    rename_i X _
    have hT := hl.eq_lookup.trans (Ctx.killcvar_lookup_tvar Γ c0 X)
    subst hT
    have h2 := h.tvar (Ctx.lookup_tvar_spec Γ X)
    have hspec := Ctx.lookup_tvar_spec (Γ'.kill_cvar (f.var c0)) (f.var X)
    rw [Ctx.killcvar_lookup_tvar Γ' (f.var c0), ← h2.eq_lookup] at hspec
    exact hspec
  lock hl := by
    rename_i ℓ _
    have hT := hl.eq_lookup.trans (Ctx.killcvar_lookup_lock Γ c0 ℓ)
    subst hT
    have h2 := h.lock (Ctx.lookup_lock_spec Γ ℓ)
    have hspec := Ctx.lookup_lock_spec (Γ'.kill_cvar (f.var c0)) (f.var ℓ)
    rw [Ctx.killcvar_lookup_lock Γ' (f.var c0), ← h2.eq_lookup] at hspec
    exact hspec
  cvar hl := by
    rename_i c a cb
    have hb := hl.eq_lookup.trans (Ctx.killcvar_lookup_cvar Γ c0 c)
    have ha := hl.eq_authority
    subst hb ha
    have hbound : (Γ.lookup_cvar c).rename f = Γ'.lookup_cvar (f.var c) :=
      (h.cvar (Ctx.lookup_cvar_spec Γ c)).eq_lookup
    have hauth : (Γ.kill_cvar c0).lookup_authority c
        = (Γ'.kill_cvar (f.var c0)).lookup_authority (f.var c) := by
      by_cases hcc : c = c0
      · subst hcc
        rw [Ctx.killcvar_authority_self, Ctx.killcvar_authority_self]
      · rw [Ctx.killcvar_authority_ne Γ hcc,
            Ctx.killcvar_authority_ne Γ' (fun he => hcc (hinj .cvar he)),
            h.lookup_authority_eq c]
    rw [hauth, hbound, ← Ctx.killcvar_lookup_cvar Γ' (f.var c0) (f.var c)]
    exact Ctx.lookup_cvar_spec (Γ'.kill_cvar (f.var c0)) (f.var c)

/-- `kill_peaks_cs` context morphism (lift of the single-`kill_cvar` one over the
    structure of the killed capture set). -/
theorem Ctx.RenamesTo.kill_peaks_cs {s1 s2 : Sig} {f : Rename s1 s2}
    (hinj : f.Injective) (K : CaptureSet s1) :
    ∀ {Γ : Ctx s1} {Γ' : Ctx s2}, Γ.RenamesTo Γ' f →
      (Γ.kill_peaks_cs K).RenamesTo (Γ'.kill_peaks_cs (K.rename f)) f := by
  induction K with
  | empty => intro _ _ h; exact h
  | union K1 K2 ih1 ih2 => intro _ _ h; exact ih2 (ih1 h)
  | cvar a c => intro _ _ h; exact h.kill_cvar hinj c
  | var a v => intro _ _ h; exact h

/-- `kill_peaks` context morphism. -/
theorem Ctx.RenamesTo.kill_peaks {s1 s2 : Sig} {Γ : Ctx s1} {Γ' : Ctx s2} {f : Rename s1 s2}
    (h : Γ.RenamesTo Γ' f) (hinj : f.Injective) (P : PeakSet s1) :
    (Γ.kill_peaks P).RenamesTo (Γ'.kill_peaks (P.rename f)) f :=
  Ctx.RenamesTo.kill_peaks_cs hinj P.cs h

private theorem Ctx.killpeakscs_isClosed {s : Sig} {Γ : Ctx s} {K : CaptureSet s}
    (h : Γ.IsClosed) : (Γ.kill_peaks_cs K).IsClosed := by
  induction K generalizing Γ with
  | empty => exact h
  | union K1 K2 ih1 ih2 => exact ih2 (ih1 h)
  | cvar a c => exact Ctx.killcvar_isClosed h
  | var a v => exact h

private theorem Ctx.killpeakscs_isClosed_inv {s : Sig} {Γ : Ctx s} {K : CaptureSet s}
    (h : (Γ.kill_peaks_cs K).IsClosed) : Γ.IsClosed := by
  induction K generalizing Γ with
  | empty => exact h
  | union K1 K2 ih1 ih2 => exact ih1 (ih2 h)
  | cvar a c => exact Ctx.killcvar_isClosed_inv h
  | var a v => exact h

/-- `hclimp` threads through `kill_peaks` (killing preserves closedness both ways). -/
theorem Ctx.RenamesTo.hclimp_kill {s1 s2 : Sig} {Γ : Ctx s1} {Γ' : Ctx s2} {f : Rename s1 s2}
    (hclimp : Γ.IsClosed → Γ'.IsClosed) (P : PeakSet s1) :
    (Γ.kill_peaks P).IsClosed → (Γ'.kill_peaks (P.rename f)).IsClosed :=
  fun hc => Ctx.killpeakscs_isClosed (hclimp (Ctx.killpeakscs_isClosed_inv hc))

/-! ## `HasType` -/

/-- Capture-set refinement commutes with renaming (target analogue of
    `CapyTy.refineCaptureSet_rename`). -/
theorem Ty.refineCaptureSet_rename {s1 s2 : Sig} {T : Ty .capt s1} {cs : CaptureSet s1}
    {f : Rename s1 s2} :
    (T.refineCaptureSet cs).rename f = (T.rename f).refineCaptureSet (cs.rename f) := by
  cases T <;> simp only [Ty.refineCaptureSet, Ty.rename]

/-- A valid capture bound stays valid along a context morphism. -/
theorem CaptureBound.IsValid.renamesTo {s1 s2 : Sig} {Γ : Ctx s1} {Γ' : Ctx s2}
    {f : Rename s1 s2} {cb : CaptureBound s1}
    (hv : cb.IsValid Γ) (h : Γ.RenamesTo Γ' f) : (cb.rename f).IsValid Γ' := by
  cases cb with
  | unbound => exact trivial
  | bound C => exact CaptureSet.AccessOnly.renamesTo hv h

/-- `HasType` transports along an injective context morphism (weakening), threading
    `hclimp : Γ.IsClosed → Γ'.IsClosed`. -/
theorem HasType.renamesTo {s : Sig} {C : CaptureSet s} {Γ : Ctx s} {e : Exp s} {E : Ty .exi s}
    (ht : HasType C Γ e E) :
    ∀ {s' : Sig} {Γ' : Ctx s'} {f : Rename s s'}, Γ.RenamesTo Γ' f → f.Injective →
      (Γ.IsClosed → Γ'.IsClosed) →
      HasType (C.rename f) Γ' (e.rename f) (E.rename f) := by
  induction ht with
  | var hΓcl hlk =>
    intro _ _ f h hinj hclimp
    simp only [CaptureSet.rename, Exp.rename, Var.rename, Ty.rename, Ty.refineCaptureSet_rename]
    exact HasType.var (hclimp hΓcl) (h.var hlk)
  | reader hΓcl hlk =>
    intro _ _ f h hinj hclimp
    simp only [CaptureSet.rename, Exp.rename, Var.rename, Ty.rename]
    exact HasType.reader (hclimp hΓcl) (h.var hlk)
  | abs hT1cl _ ihbody =>
    intro _ _ f h hinj hclimp
    have hb := ihbody (h.push (.var _)) hinj.lift (Ctx.RenamesTo.hclimp_push hclimp)
    exact HasType.abs (Ty.rename_closed hT1cl) (CaptureSet.weaken_rename_comm ▸ hb)
  | tabs hScl _ ihbody =>
    intro _ _ f h hinj hclimp
    have hb := ihbody (h.push (.tvar _)) hinj.lift (Ctx.RenamesTo.hclimp_push hclimp)
    exact HasType.tabs (Ty.rename_closed hScl) (CaptureSet.weaken_rename_comm ▸ hb)
  | cabs hcbcl hcbvalid _ ihbody =>
    intro _ _ f h hinj hclimp
    have hb := ihbody (h.push (.cvar .access_only _)) hinj.lift (Ctx.RenamesTo.hclimp_push hclimp)
    exact HasType.cabs (CaptureBound.rename_closed hcbcl) (hcbvalid.renamesTo h)
      (CaptureSet.weaken_rename_comm ▸ hb)
  | wrap hΨcl _ ihbody =>
    intro _ _ f h hinj hclimp
    have hb := ihbody (h.push (.lock _)) hinj.lift (Ctx.RenamesTo.hclimp_push hclimp)
    rw [CaptureSet.weaken_rename_comm, Exp.weaken_rename_comm, Ty.weaken_rename_comm] at hb
    exact HasType.wrap (ModalCtx.rename_closed hΨcl) hb
  | pack hCcl hCao hCdrop _ ihbody =>
    intro _ _ f h hinj hclimp
    have hb := ihbody h hinj hclimp
    simp only [Exp.rename, Ty.rename, Ty.rename_subst_openCVar] at hb
    simpa only [CaptureSet.rename, CaptureSet.applyAccess_rename, Exp.rename, Var.rename, Ty.rename]
      using HasType.pack (CaptureSet.rename_closed hCcl) (hCao.renamesTo h)
        (hCdrop.renamesTo h) hb
  | app haccess _ _ ihfun iharg =>
    intro _ _ f h hinj hclimp
    have hfun := ihfun h hinj hclimp
    have harg := iharg h hinj hclimp
    simp only [Exp.rename, Ty.rename, CaptureSet.rename, Var.rename] at hfun harg
    simp only [CaptureSet.rename, Var.rename, Exp.rename, Ty.rename_subst_openVar]
    exact HasType.app (haccess.renamesTo h) hfun harg
  | tapp haccess hScl _ ihfun =>
    intro _ _ f h hinj hclimp
    have hfun := ihfun h hinj hclimp
    simp only [Exp.rename, Ty.rename, CaptureSet.rename, Var.rename] at hfun
    simp only [CaptureSet.rename, Var.rename, Exp.rename, Ty.rename_subst_openTVar]
    exact HasType.tapp (haccess.renamesTo h) (Ty.rename_closed hScl) hfun
  | capp haccess hDcl hDvalid _ ihfun =>
    intro _ _ f h hinj hclimp
    have hfun := ihfun h hinj hclimp
    simp only [Exp.rename, Ty.rename, CaptureSet.rename, Var.rename, CaptureBound.rename] at hfun
    simp only [CaptureSet.rename, Var.rename, Exp.rename, Ty.rename_subst_openCVar]
    exact HasType.capp (I := .empty) (haccess.renamesTo h) (CaptureSet.rename_closed hDcl)
      (hDvalid.renamesTo h) hfun
  | unwrap _ hsat ihfun =>
    intro _ _ f h hinj hclimp
    have hfun := ihfun h hinj hclimp
    simp only [Exp.rename, Ty.rename, CaptureSet.rename, Var.rename] at hfun
    simp only [CaptureSet.rename, Var.rename, Exp.rename]
    exact HasType.unwrap hfun (hsat.renamesTo h hinj)
  | letin hseq _ _ ihe1 ihe2 =>
    intro _ _ f h hinj hclimp
    have hb := ihe2 ((h.kill_peaks hinj _).push (.var _)) hinj.lift
      (Ctx.RenamesTo.hclimp_push (Ctx.RenamesTo.hclimp_kill (f := f) hclimp _))
    rw [CaptureSet.weaken_rename_comm, Ty.weaken_rename_comm,
      ← PeakSet.consumed_rename, ← h.peakset] at hb
    simp only [CaptureSet.rename, Exp.rename]
    exact HasType.letin (hseq.renamesTo h hinj) (ihe1 h hinj hclimp) hb
  | unpack hseq hdrop _ _ iht ihu =>
    intro _ _ f h hinj hclimp
    have hb := ihu (((h.kill_peaks hinj _).push (.cvar .can_drop .unbound)).push (.var _))
      hinj.lift.lift
      (Ctx.RenamesTo.hclimp_push (Ctx.RenamesTo.hclimp_push
        (Ctx.RenamesTo.hclimp_kill (f := f) hclimp _)))
    simp only [CaptureSet.rename, CaptureSet.weaken_rename_comm, Ty.weaken_rename_comm] at hb
    rw [← PeakSet.consumed_rename, ← h.peakset] at hb
    simp only [CaptureSet.rename, Exp.rename]
    exact HasType.unpack (hseq.renamesTo h hinj)
      (by rw [h.peakset, PeakSet.consumed_rename]; exact hdrop.renamesTo h)
      (iht h hinj hclimp) hb
  | unit => intro _ _ f h hinj hclimp; exact HasType.unit
  | btrue => intro _ _ f h hinj hclimp; exact HasType.btrue
  | bfalse => intro _ _ f h hinj hclimp; exact HasType.bfalse
  | alloc _ ihbody =>
    intro _ _ f h hinj hclimp
    exact HasType.alloc (ihbody h hinj hclimp)
  | drop hΓcl hdrop _ ihbody =>
    intro _ _ f h hinj hclimp
    have hb := ihbody h hinj hclimp
    simp only [Exp.rename, Ty.rename, CaptureSet.rename, Var.rename] at hb
    simp only [CaptureSet.rename, Var.rename, Exp.rename]
    exact HasType.drop (hclimp hΓcl) (hdrop.renamesTo h) hb
  | read haccess _ ihbody =>
    intro _ _ f h hinj hclimp
    have hb := ihbody h hinj hclimp
    simp only [Exp.rename, Ty.rename, CaptureSet.rename, Var.rename] at hb
    simp only [CaptureSet.rename, Var.rename, Exp.rename, Ty.rename]
    exact HasType.read (haccess.renamesTo h) hb
  | write haccess _ _ ihx ihy =>
    intro _ _ f h hinj hclimp
    have hbx := ihx h hinj hclimp
    have hby := ihy h hinj hclimp
    simp only [Exp.rename, Ty.rename, CaptureSet.rename, Var.rename] at hbx hby
    simp only [CaptureSet.rename, Var.rename, Exp.rename, Ty.rename]
    exact HasType.write (haccess.renamesTo h) hbx hby
  | cond _ _ _ ihx ih2 ih3 =>
    intro _ _ f h hinj hclimp
    have hbx := ihx h hinj hclimp
    simp only [Exp.rename, Ty.rename, Var.rename] at hbx
    simp only [CaptureSet.rename, Exp.rename]
    exact HasType.cond hbx (ih2 h hinj hclimp) (ih3 h hinj hclimp)
  | par _ _ hsep ih1 ih2 =>
    intro _ _ f h hinj hclimp
    simp only [CaptureSet.rename, Exp.rename, Ty.rename]
    exact HasType.par (ih1 h hinj hclimp) (ih2 h hinj hclimp) (hsep.renamesTo h hinj)
  | invoke haccess _ _ ihx ihy =>
    intro _ _ f h hinj hclimp
    have hbx := ihx h hinj hclimp
    have hby := ihy h hinj hclimp
    simp only [Exp.rename, Ty.rename, CaptureSet.rename, Var.rename] at hbx hby
    simp only [CaptureSet.rename, Var.rename, Exp.rename, Ty.rename]
    exact HasType.invoke (haccess.renamesTo h) hbx hby
  | subtyp _ hsc hst hC2cl hE2cl ihe =>
    intro _ _ f h hinj hclimp
    exact HasType.subtyp (ihe h hinj hclimp) (hsc.renamesTo h)
      (hst.renamesTo h hinj hclimp) (CaptureSet.rename_closed hC2cl) (Ty.rename_closed hE2cl)

/-- **Weakening**: push one closed binding. -/
theorem HasType.weaken {s : Sig} {C : CaptureSet s} {Γ : Ctx s} {e : Exp s} {E : Ty .exi s}
    (h : HasType C Γ e E) {k : Kind} (b : Binding s k) (hb : b.IsClosed) :
    HasType (C.rename Rename.succ) (Γ.push b) (e.rename Rename.succ) (E.rename Rename.succ) :=
  HasType.renamesTo h (Ctx.RenamesTo.weaken b) Rename.injective_succ (fun hc => hc.push hb)

/-! ## Self-capture unfolds through the stored type

A bound variable's self-capture `{ε x}` resolves (peaks) to exactly its declared
type's capture set, so the `AccessOnly`/`droppable`/`accessible` side conditions on a
self-capture reduce to the same conditions on the stored type — the shape the
`app`-compiled `letin` chain needs. -/

/-- Peaks of a variable's `{ε x}` self-capture equal the peaks of its stored type's
    capture set. -/
theorem CaptureSet.peaks_var_eps {s : Sig} {Γ : Ctx s} {x : BVar s .var} {T : Ty .capt s}
    (hlk : Γ.LookupVar x T) :
    CaptureSet.peaks Γ (.var (.M .epsilon) (.bound x)) = CaptureSet.peaks Γ T.captureSet := by
  rw [CaptureSet.var_peaks hlk]
  simp only [CaptureSet.applyAccess_M, CaptureSet.applyMut_epsilon]

/-- `AccessOnly` of a `{ε x}` self-capture, from `AccessOnly` of the stored type. -/
theorem CaptureSet.var_eps_accessOnly {s : Sig} {Γ : Ctx s} {x : BVar s .var}
    {T : Ty .capt s} (hlk : Γ.LookupVar x T) (hT : T.captureSet.AccessOnly Γ) :
    (CaptureSet.var (.M .epsilon) (.bound x)).AccessOnly Γ := by
  intro c hsub
  change (CaptureSet.cvar .drop c) ⊆ CaptureSet.peaks Γ (.var (.M .epsilon) (.bound x)) at hsub
  rw [CaptureSet.peaks_var_eps hlk] at hsub
  exact hT c hsub

/-- `droppable` of a `{ε x}` self-capture, from `droppable` of the stored type. -/
theorem CaptureSet.var_eps_droppable {s : Sig} {Γ : Ctx s} {x : BVar s .var}
    {T : Ty .capt s} (hlk : Γ.LookupVar x T) (hT : T.captureSet.droppable Γ) :
    (CaptureSet.var (.M .epsilon) (.bound x)).droppable Γ := by
  intro a c hsub
  change (CaptureSet.cvar a c) ⊆ CaptureSet.peaks Γ (.var (.M .epsilon) (.bound x)) at hsub
  rw [CaptureSet.peaks_var_eps hlk] at hsub
  exact hT a c hsub

/-- `accessible` of a `{ε x}` self-capture, from `accessible` of the stored type. -/
theorem CaptureSet.var_eps_accessible {s : Sig} {Γ : Ctx s} {x : BVar s .var}
    {T : Ty .capt s} (hlk : Γ.LookupVar x T) (hT : T.captureSet.accessible Γ) :
    (CaptureSet.var (.M .epsilon) (.bound x)).accessible Γ := by
  intro a c hsub
  change (CaptureSet.cvar a c) ⊆ CaptureSet.peaks Γ (.var (.M .epsilon) (.bound x)) at hsub
  rw [CaptureSet.peaks_var_eps hlk] at hsub
  exact hT a c hsub

/-! ## Left-refinement strengthening for `Subtyp` (`refine_widen`)

The `app`-case fitting must relate two `refineCaptureSet` instances of a
subtyping: from `Subtyp Γ A B` and a capture widening `Subcapt Γ c1 c2` conclude
`Subtyp Γ (A.refineCaptureSet c1) (B.refineCaptureSet c2)`.  Refinement only
replaces a former's *outer* capture slot, so every structural rule survives with
its capture premise swapped for the widening `hc : Subcapt Γ c1 c2`.  Two corners
resist a blanket statement:

* The `top` rule is purity-gated (`Subtyp Γ T .top` needs `T.IsPureType`) and
  `A.refineCaptureSet c1` is impure for nonempty `c1`, so `A.refine c1 <: .top`
  is *genuinely false*.  The honest conclusion therefore carries a `B = .top`
  escape disjunct.  The use site discharges it by source reasoning: a variable
  self-capture argument `{ε bv}` is impure, so the source never fits it to a
  `Top` domain — see `refine_widen_of_ne_top` and the recipe below.
* The `tvar` rule's bound `S.core` may itself be a (pure) capturing former, so
  refining the *right* side to `c2` widens its empty slot.  This chains
  `Subtyp.tvar` with `Subtyp.widen_capture` via `trans`, whose middle closedness
  forces `c2.IsClosed` and `B.IsClosed` (the latter closes the looked-up bound).
  `B.IsClosed` also supplies the `modal_modal` corner's payload closedness, and
  propagates cleanly through `trans` (the intermediate closedness comes from the
  `trans` rule's own `T2.IsClosed` premise).

### Use-site recipe (Preservation `app`)

`hbase : ... (.typ (X.refineCaptureSet {ε bv}))`, `hK1 : Subtyp Γ (.typ X) (.typ Y)`
(invert `.typ` to `Subtyp Γ X Y`), and `Subcapt Γ {ε bv} c`.  With `Y ≠ .top`
(guaranteed since the impure self-capture argument could not source-fit a `Top`
domain), `refine_widen_of_ne_top` yields `Subtyp Γ (X.refine {ε bv}) (Y.refine c)`;
re-wrap with `Subtyp.typ`.  Should `Y = .top` ever be forced, the source
application would have rejected the impure argument, so that branch is vacuous. -/

/-- An empty capture set is a subset of any capture set. -/
theorem CaptureSet.IsEmpty.subset {s : Sig} {cs : CaptureSet s} (h : cs.IsEmpty)
    {C : CaptureSet s} : cs.Subset C := by
  induction h with
  | empty => exact CaptureSet.Subset.empty
  | union _ _ ih1 ih2 => exact CaptureSet.Subset.union_left ih1 ih2

/-- A pure type's capture set is empty. -/
theorem PureTy.captureSet_isEmpty {s : Sig} (S : PureTy s) : S.core.captureSet.IsEmpty :=
  S.p

/-- Refining a capturing type with its own capture set is the identity. -/
theorem Ty.refine_captureSet_self {s : Sig} {T : Ty .capt s} :
    T.refineCaptureSet T.captureSet = T := by
  cases T <;> rfl

/-- **Refinement is monotone in the capture slot.**  Replacing a former's outer
    capture by `c1 ≤ c2` yields a subtype: atomic shapes are unchanged (`refl`),
    capturing shapes reuse their covariant capture rule with `hc`. -/
theorem Subtyp.refine_mono {s : Sig} {Γ : Ctx s} {T : Ty .capt s} {c1 c2 : CaptureSet s}
    (hc : Subcapt Γ c1 c2) :
    Subtyp Γ (T.refineCaptureSet c1) (T.refineCaptureSet c2) := by
  cases T with
  | top => exact Subtyp.refl
  | tvar X => exact Subtyp.refl
  | unit => exact Subtyp.refl
  | bool => exact Subtyp.refl
  | cap cs => exact Subtyp.cap hc
  | cell cs => exact Subtyp.cell hc
  | reader cs => exact Subtyp.reader hc
  | arrow A cs B => exact Subtyp.arrow Subtyp.refl hc Subtyp.refl
  | poly S cs B => exact Subtyp.poly_cap hc
  | cpoly cb cs B =>
    refine Subtyp.cpoly ?_ hc Subtyp.refl
    cases cb with
    | unbound => exact Subbound.top
    | bound C => exact Subbound.capset (Subcapt.sc_elem CaptureSet.Subset.refl)
  | modal cs Ψ E => exact Subtyp.modal hc Subtyp.refl

/-- **Widening a type's own capture set is a supertype.**  From `T.captureSet ≤ c`
    conclude `T <: T.refineCaptureSet c`.  Special case of `refine_mono` using
    `Ty.refine_captureSet_self`. -/
theorem Subtyp.widen_capture {s : Sig} {Γ : Ctx s} {T : Ty .capt s} {c : CaptureSet s}
    (hsc : Subcapt Γ T.captureSet c) : Subtyp Γ T (T.refineCaptureSet c) := by
  have h := Subtyp.refine_mono (T := T) hsc
  rwa [Ty.refine_captureSet_self] at h

/-! ### Sort-guarded motives

`Subtyp` is indexed by `TySort` (`.capt`/`.exi`), and `refineCaptureSet` is
`.capt`-only, so `induction` over a `Subtyp` at the *fixed* sort `.capt` is
rejected ("index is not a variable").  We induct at a *general* sort against a
motive that is the intended `.capt` statement on `.capt` and trivially `True`
on `.exi`; the `.capt`-headed constructors reduce it to the real goal, `exi`/`typ`
to `True`, and the sort-polymorphic `refl`/`trans` are handled by `cases` on the
sort in dedicated helpers. -/

/-- Sort-guarded motive for `eq_top_of_top`. -/
def Subtyp.EqTopMotive {s : Sig} {k : TySort} (A B : Ty k s) : Prop :=
  match k, A, B with
  | .capt, A, B => A = .top → B = .top
  | .exi, _, _ => True

/-- `refl` discharges the `EqTopMotive` at either sort. -/
theorem Subtyp.EqTopMotive.refl {s : Sig} {k : TySort} {A : Ty k s} :
    Subtyp.EqTopMotive A A := by
  cases k with
  | capt => exact id
  | exi => trivial

/-- `trans` composes the `EqTopMotive` at either sort. -/
theorem Subtyp.EqTopMotive.trans {s : Sig} {k : TySort} {A M B : Ty k s}
    (ih1 : Subtyp.EqTopMotive A M) (ih2 : Subtyp.EqTopMotive M B) :
    Subtyp.EqTopMotive A B := by
  cases k with
  | capt => exact fun hA => ih2 (ih1 hA)
  | exi => trivial

/-- General-sort core of `eq_top_of_top` (see `EqTopMotive`). -/
theorem Subtyp.eq_top_of_top_gen {s : Sig} {Γ : Ctx s} {k : TySort} {A B : Ty k s}
    (h : Subtyp Γ A B) : Subtyp.EqTopMotive A B := by
  induction h with
  | top => intro _; rfl
  | refl => exact Subtyp.EqTopMotive.refl
  | trans _ _ _ ih1 ih2 => exact Subtyp.EqTopMotive.trans ih1 ih2
  | exi => trivial
  | typ => trivial
  | _ => intro hA; nomatch hA

/-- Only `.top` is a subtype-of-`.top` on its left: if `A <: B` and `A = .top`
    then `B = .top`.  Closes the `M = .top` corner of `refine_widen`'s `trans`. -/
theorem Subtyp.eq_top_of_top {s : Sig} {Γ : Ctx s} {A B : Ty .capt s}
    (h : Subtyp Γ A B) : A = .top → B = .top :=
  Subtyp.eq_top_of_top_gen h

/-- Sort-guarded motive for `refine_widen`. -/
def Subtyp.RefineWidenMotive {s : Sig} {k : TySort} (Γ : Ctx s) (A B : Ty k s) : Prop :=
  match k, A, B with
  | .capt, A, B => ∀ {c1 c2 : CaptureSet s}, Subcapt Γ c1 c2 → c2.IsClosed → B.IsClosed →
      Subtyp Γ (A.refineCaptureSet c1) (B.refineCaptureSet c2) ∨ B = .top
  | .exi, _, _ => True

/-- `refl` discharges the `RefineWidenMotive` at either sort. -/
theorem Subtyp.RefineWidenMotive.refl {s : Sig} {k : TySort} {Γ : Ctx s} {A : Ty k s} :
    Subtyp.RefineWidenMotive Γ A A := by
  cases k with
  | capt => intro _ _ hc _ _; exact Or.inl (Subtyp.refine_mono hc)
  | exi => trivial

/-- `trans` composes the `RefineWidenMotive` at either sort.  On `.capt`: fit
    through the intermediate `M.refineCaptureSet c2` (closed by `M.IsClosed`
    and `c2.IsClosed`), or — when the left half reveals `M = .top` — conclude
    `B = .top` from the original `Subtyp Γ M B` via `eq_top_of_top`. -/
theorem Subtyp.RefineWidenMotive.trans {s : Sig} {k : TySort} {Γ : Ctx s} {A M B : Ty k s}
    (hM : M.IsClosed) (h2 : Subtyp Γ M B)
    (ih1 : Subtyp.RefineWidenMotive Γ A M) (ih2 : Subtyp.RefineWidenMotive Γ M B) :
    Subtyp.RefineWidenMotive Γ A B := by
  cases k with
  | capt =>
    intro _ c2 hc hc2 hBcl
    rcases ih1 hc hc2 hM with h1' | hMtop
    · rcases ih2 (Subcapt.sc_elem CaptureSet.Subset.refl) hc2 hBcl with h2' | hBtop
      · exact Or.inl (Subtyp.trans (Ty.refineCaptureSet_closed hM hc2) h1' h2')
      · exact Or.inr hBtop
    · exact Or.inr (Subtyp.eq_top_of_top h2 hMtop)
  | exi => trivial

/-- General-sort core of `refine_widen` (see `RefineWidenMotive`). -/
theorem Subtyp.refine_widen_gen {s : Sig} {Γ : Ctx s} {k : TySort} {A B : Ty k s}
    (h : Subtyp Γ A B) : Subtyp.RefineWidenMotive Γ A B := by
  induction h with
  | top => intro _ _ _ _ _; exact Or.inr rfl
  | refl => exact Subtyp.RefineWidenMotive.refl
  | trans hM _ h2 ih1 ih2 => exact Subtyp.RefineWidenMotive.trans hM h2 ih1 ih2
  | tvar hlk =>
    intro _ _ _ _ hBcl
    left
    rename_i X S _ _ _ _
    refine Subtyp.trans hBcl (Subtyp.tvar hlk) (Subtyp.widen_capture ?_)
    exact Subcapt.sc_elem (CaptureSet.IsEmpty.subset S.p)
  | arrow h1 _ h3 _ _ => intro _ _ hc _ _; exact Or.inl (Subtyp.arrow h1 hc h3)
  | poly h1 _ h3 _ _ => intro _ _ hc _ _; exact Or.inl (Subtyp.poly h1 hc h3)
  | cpoly hsb _ h3 _ => intro _ _ hc _ _; exact Or.inl (Subtyp.cpoly hsb hc h3)
  | modal _ hbody _ => intro _ _ hc _ _; exact Or.inl (Subtyp.modal hc hbody)
  | modal_modal hΓcl hΨ1 hΨ2 hsat =>
    intro _ _ hc hc2 hBcl
    cases hBcl with | modal _ _ hE =>
    exact Or.inl (Subtyp.trans (Ty.IsClosed.modal hc2 hΨ1 hE)
      (Subtyp.modal hc Subtyp.refl) (Subtyp.modal_modal hΓcl hΨ1 hΨ2 hsat))
  | exi => trivial
  | typ => trivial
  | cell _ => intro _ _ hc _ _; exact Or.inl (Subtyp.cell hc)
  | reader _ => intro _ _ hc _ _; exact Or.inl (Subtyp.reader hc)
  | cap _ => intro _ _ hc _ _; exact Or.inl (Subtyp.cap hc)
  | poly_cap _ => intro _ _ hc _ _; exact Or.inl (Subtyp.poly_cap hc)

/-- **Left-refinement strengthening (disjunctive form).**  From `Subtyp Γ A B`
    and a capture widening `Subcapt Γ c1 c2`, refining both former slots preserves
    the subtyping — unless `B = .top`, the one genuinely-false corner (an impure
    `A.refine c1` is never a subtype of the pure `.top`).  `c2.IsClosed` and
    `B.IsClosed` feed the `trans`/`tvar`/`modal_modal` intermediate closedness. -/
theorem Subtyp.refine_widen {s : Sig} {Γ : Ctx s} {A B : Ty .capt s}
    (h : Subtyp Γ A B) :
    ∀ {c1 c2 : CaptureSet s}, Subcapt Γ c1 c2 → c2.IsClosed → B.IsClosed →
      Subtyp Γ (A.refineCaptureSet c1) (B.refineCaptureSet c2) ∨ B = .top :=
  Subtyp.refine_widen_gen h

/-- **Left-refinement strengthening (`B ≠ .top` form).**  The clean fitting the
    `app` case uses: with the top corner excluded, refining both slots of a
    subtyping under `Subcapt Γ c1 c2` yields the refined subtyping directly. -/
theorem Subtyp.refine_widen_of_ne_top {s : Sig} {Γ : Ctx s} {A B : Ty .capt s}
    {c1 c2 : CaptureSet s} (h : Subtyp Γ A B) (hc : Subcapt Γ c1 c2)
    (hc2 : c2.IsClosed) (hBcl : B.IsClosed) (hB : B ≠ .top) :
    Subtyp Γ (A.refineCaptureSet c1) (B.refineCaptureSet c2) :=
  (Subtyp.refine_widen h hc hc2 hBcl).resolve_right hB

end CoreCapybara
