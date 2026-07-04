import Semantic.CoreCapybara.LegacyCompilation.PeakCombinatorics
import Semantic.CoreCapybara.LegacyCompilation.AppPeaks
import Semantic.CoreCapybara.LegacyCompilation.AppChain
import Semantic.CoreCapybara.LegacyCompilation.SepRestrict
import Semantic.CoreCapybara.LegacyCompilation.SepCheckCompile
import Semantic.CoreCapybara.LegacyCompilation.AppSupport
import Semantic.CoreCapybara.LegacyCapybara.TypeSystem.UseCovered

/-! # AppSatisfy: the unwrap `Satisfy` bridge for the compiled application. -/

open CoreCapybara

namespace Compilation

set_option linter.style.longLine false

/-- Separation against a `PeaksOnly` right operand reduces to its `cvar` atoms
    (generalizes `SepCheck.of_cvar_atoms_left` to an arbitrary left operand). -/
theorem SepCheck.of_atoms_right {s : Sig} {Γ : Ctx s} {C1 C2 : CaptureSet s}
    (hpo : C2.PeaksOnly)
    (hatom : ∀ (a2 : Access) (c2 : BVar s .cvar), (CaptureSet.cvar a2 c2) ⊆ C2 →
      SepCheck Γ C1 (CaptureSet.cvar a2 c2)) :
    SepCheck Γ C1 C2 := by
  induction hpo with
  | empty => exact SepCheck.sep_symm SepCheck.sep_empty
  | @cvar m c => exact hatom m c CaptureSet.Subset.refl
  | union _ _ iha ihb =>
    refine SepCheck.sep_symm (SepCheck.sep_union ?_ ?_)
    · exact SepCheck.sep_symm (iha (fun a2 c2 h => hatom a2 c2 (.union_right_left h)))
    · exact SepCheck.sep_symm (ihb (fun a2 c2 h => hatom a2 c2 (.union_right_right h)))

theorem app_satisfy_bridge {s1 s2 : Sig} {ctx : CompilerCtx s1 s2}
    {x y : BVar s1 .var} {yv : Var .var s2} {D : CapyCaptureSet s1}
    {T1 : CapyTy .capt (s1,C)} {T2 : CapyTy .exi (s1,x)}
    (hcoh : ctx.Coherent) (hsub : ctx.SubCoherent)
    (hnpp : ctx.capyCtx.NoPseudoPeak) (hDnpp : D.NoPseudoPeak)
    (hT1npp : T1.NoPseudoPeak) (_hT2npp : T2.NoPseudoPeak)
    (hT1ao : CapyCaptureSet.AccessOnly (ctx.capyCtx.push_cvar_default (.unbound .epsilon)) T1.captureSet)
    (hsep : CapySepCheck ctx.capyCtx D
        (CapyTy.interfere_set (.arrow T1 (.var (.M .epsilon) (.bound x)) T2)))
    (hcov : ctx.SepCovered (.var (.M .epsilon) (.bound x) ∪ .var (.M .epsilon) (.bound y)))
    (huc : CapyCaptureSet.SubP ctx.capyCtx
        (D ∪ CapyTy.interfere_set (.arrow T1 (.var (.M .epsilon) (.bound x)) T2))
        (.var (.M .epsilon) (.bound x) ∪ .var (.M .epsilon) (.bound y))) :
    let ctxLockA := ((ctx.weakenTarget.weakenTarget.weakenTarget).consCVar
        (.unbound .epsilon) (.there (.there .here))).consVar T1 (some .here)
        (.cvar (.M .epsilon) (.there .here))
    let WsrcA := (((CapyCaptureSet.var (.M .epsilon) (.bound x)).rename Rename.succ).rename
        Rename.succ) ∪ (CapyCaptureSet.var (.M .epsilon) (.bound .here))
    Satisfy ctx.coreCtx
      (ModalCtx.subst ⟨peakSepCtx ctxLockA.capyCtx
          (CapyCaptureSet.peakset ctxLockA.capyCtx WsrcA) ctxLockA.srcCtx,
        MutabilityCtx.empty⟩
        (appOpen (CapyCaptureSet.compile D ctx.srcCtx)
          (CapyCaptureSet.compile (.var (.M .epsilon) (.bound y)) ctx.srcCtx)
          yv)) := by
  intro ctxLockA WsrcA
  set Dt := CapyCaptureSet.compile D ctx.srcCtx with hDt
  set Cy := CapyCaptureSet.compile (CapyCaptureSet.var (.M .epsilon) (.bound y)) ctx.srcCtx with hCy
  set σ : Subst (s2,C,C,x) s2 := appOpen Dt Cy yv with hσ
  set ΓL := ctxLockA.capyCtx with hΓL
  set PW := CapyCaptureSet.peakset ΓL WsrcA with hPW
  set srcCtxL := ctxLockA.srcCtx with hsrcL
  refine Satisfy.satisfy (fun C m hm => ?_) (fun C1 C2 hd => ?_)
  · -- mutability half: the substituted mutability context is empty
    simp only [ModalCtx.subst, MutabilityCtx.subst] at hm
    cases hm
  · -- separation half
    simp only [ModalCtx.subst] at hd
    rw [peakSepCtx_subst] at hd
    -- the filtered stable-peak list is nodup, so `HasTwoDistinct` picks two distinct entries
    have hnodup : ((peakList PW).filter (fun p => decide (Peak.IsStable ΓL p))).Nodup :=
      (PC.peakList_nodup PW).filter _
    obtain ⟨p1, hp1, p2, hp2, hne, hdisj⟩ :=
      PC.hasTwoDistinct_foldl_nodup hd _ hnodup rfl
    -- the footprint slice `U0` is covered (restrict the ambient covering twice)
    have hU0sub : appU0 x T1
        ⊆ D ∪ CapyTy.interfere_set (.arrow T1 (.var (.M .epsilon) (.bound x)) T2) := by
      rw [CapyTy.interfere_set]
      exact CapyCaptureSet.Subset.union_right_right
        (CapyCaptureSet.Subset.union_right_left CapyCaptureSet.Subset.refl)
    have hcovU0 : ctx.SepCovered (appU0 x T1) :=
      (hcov.of_subP hsub huc).of_subP hsub
        (CapyCaptureSet.Subset.coveredBy (CapyCaptureSet.peaks_subset_mono hU0sub))
    -- (Step 4b) the self-capture peak's compiled, appOpen-substituted item is `⊑ ⟦D⟧`
    have foldC : ∀ (L : List Access), (∀ a ∈ L, a ≠ Access.drop) →
        Subcapt ctx.coreCtx
          ((CapyCaptureSet.compile
            (L.foldr (fun a acc => CapyCaptureSet.cvar a (BVar.there BVar.here) ∪ acc) .empty)
            srcCtxL).subst σ) Dt := by
      intro L hL
      induction L with
      | nil => exact Subcapt.sc_elem CaptureSet.Subset.empty
      | cons a L' ih =>
        have hane : a ≠ Access.drop := hL a List.mem_cons_self
        have ihL' := ih (fun b hb => hL b (List.mem_cons_of_mem _ hb))
        have hstep : (CapyCaptureSet.compile
              ((a :: L').foldr (fun a acc => CapyCaptureSet.cvar a (BVar.there BVar.here) ∪ acc) .empty)
              srcCtxL).subst σ
            = (Dt.applyAccess a) ∪ (CapyCaptureSet.compile
              (L'.foldr (fun a acc => CapyCaptureSet.cvar a (BVar.there BVar.here) ∪ acc) .empty)
              srcCtxL).subst σ := by
          simp only [List.foldr_cons]; rfl
        rw [hstep]
        cases a with
        | drop => exact absurd rfl hane
        | M m => exact Subcapt.sc_union Subcapt.applyAccess_nondrop ihL'
    have itemC : Subcapt ctx.coreCtx
        ((CapyCaptureSet.compile (peakItem PW (.there .here)) srcCtxL).subst σ) Dt :=
      foldC (accessedAt PW (.there .here)) (by
        intro a ha
        have hocc : (CapyCaptureSet.cvar a (BVar.there BVar.here)) ⊆ PW.cs :=
          PC.accessedAt_go_subset PW.cs (by simpa only [accessedAt] using ha)
        exact appPeaks_c_no_drop ctx.capyCtx T1 hT1ao (appPeaks_occ_c ctx.capyCtx x T1 hocc))
    -- (Step 4a) a Γ-peak's compiled, appOpen-substituted item is contained in the
    -- underlying cvar's compiled footprint item
    have itemT : ∀ (c' : BVar s1 .cvar),
        CaptureSet.Subset
          ((CapyCaptureSet.compile (peakItem PW (.there (.there c'))) srcCtxL).subst σ)
          (CapyCaptureSet.compile
            (peakItem (CapyCaptureSet.peakset ctx.capyCtx (appU0 x T1)) c') ctx.srcCtx) := by
      intro c'
      have hsrc := appPeaks_item_there ctx.capyCtx x T1 (c' := c')
      have hRHS : CapyCaptureSet.compile
            (((peakItem (CapyCaptureSet.peakset ctx.capyCtx (appU0 x T1)) c').rename Rename.succ).rename
              Rename.succ) srcCtxL
          = (((CapyCaptureSet.compile
              (peakItem (CapyCaptureSet.peakset ctx.capyCtx (appU0 x T1)) c') ctx.srcCtx).rename
              Rename.succ).rename Rename.succ).rename Rename.succ := by
        change CapyCaptureSet.compile
            (((peakItem (CapyCaptureSet.peakset ctx.capyCtx (appU0 x T1)) c').rename Rename.succ).rename
              Rename.succ)
            (SrcCtx.cons _ (SrcCtx.cons _ (ctx.srcCtx.weaken.weaken.weaken))) = _
        rw [CapyCaptureSet.compile_rename_succ_cons, CapyCaptureSet.compile_rename_succ_cons]
        change CapyCaptureSet.compile
            (peakItem (CapyCaptureSet.peakset ctx.capyCtx (appU0 x T1)) c')
            (((ctx.srcCtx.rename Rename.succ).rename Rename.succ).rename Rename.succ) = _
        rw [CapyCaptureSet.compile_rename, CapyCaptureSet.compile_rename, CapyCaptureSet.compile_rename]
      have hcomp := hRHS ▸ CapyCaptureSet.compile_subset (sc := srcCtxL) hsrc
      have hs := CaptureSet.Subset.subst (σ := σ) hcomp
      have hcancel : ((((CapyCaptureSet.compile
            (peakItem (CapyCaptureSet.peakset ctx.capyCtx (appU0 x T1)) c') ctx.srcCtx).rename
              Rename.succ).rename Rename.succ).rename Rename.succ).subst σ
          = CapyCaptureSet.compile
              (peakItem (CapyCaptureSet.peakset ctx.capyCtx (appU0 x T1)) c') ctx.srcCtx := by
        rw [hσ]; exact CaptureSet.appOpen_weaken_cancel _
      exact hcancel ▸ hs
    -- `⟦D⟧` separates from a stable Γ-peak's compiled footprint item (per-atom
    -- `CapySepCheck` right-restriction of `hsep`, then compiled)
    have sepDpeak : ∀ (c' : BVar s1 .cvar), ctx.capyCtx.IsStableCVar c' →
        SepCheck ctx.coreCtx Dt
          (CapyCaptureSet.compile
            (peakItem (CapyCaptureSet.peakset ctx.capyCtx (appU0 x T1)) c') ctx.srcCtx) := by
      intro c' hc'stab
      have hU0subI : appU0 x T1
          ⊆ CapyTy.interfere_set (.arrow T1 (.var (.M .epsilon) (.bound x)) T2) := by
        rw [CapyTy.interfere_set]
        exact CapyCaptureSet.Subset.union_right_left CapyCaptureSet.Subset.refl
      have foldSep : ∀ (L : List Access),
          (∀ a ∈ L, (CapyCaptureSet.cvar a c') ⊆ CapyCaptureSet.peaks ctx.capyCtx (appU0 x T1)) →
          SepCheck ctx.coreCtx Dt
            (CapyCaptureSet.compile
              (L.foldr (fun a acc => CapyCaptureSet.cvar a c' ∪ acc) .empty) ctx.srcCtx) := by
        intro L hL
        induction L with
        | nil => exact SepCheck.sep_symm SepCheck.sep_empty
        | cons a L' ih =>
          have hoccI := CapyCaptureSet.atom_subset_trans
            (CapyCaptureSet.peaks_subset_mono hU0subI) (hL a List.mem_cons_self)
          have hatom : SepCheck ctx.coreCtx Dt
              (CapyCaptureSet.compile (CapyCaptureSet.cvar a c') ctx.srcCtx) :=
            CapySepCheck.compile (CapySepCheck.restrict_right hsep hoccI hc'stab)
              ctx rfl hcoh hsub hnpp hDnpp CapyCaptureSet.NoPseudoPeak.cvar
              ((hcov.of_subP hsub huc).of_subP hsub
                (CapyCaptureSet.SubP.union_peak_atom hoccI))
          have hstep : CapyCaptureSet.compile
                ((a :: L').foldr (fun a acc => CapyCaptureSet.cvar a c' ∪ acc) .empty) ctx.srcCtx
              = CapyCaptureSet.compile (CapyCaptureSet.cvar a c') ctx.srcCtx
                ∪ CapyCaptureSet.compile
                  (L'.foldr (fun a acc => CapyCaptureSet.cvar a c' ∪ acc) .empty) ctx.srcCtx := by
            simp only [List.foldr_cons]; rfl
          rw [hstep]
          exact SepCheck.sep_symm (SepCheck.sep_union (SepCheck.sep_symm hatom)
            (SepCheck.sep_symm (ih (fun b hb => hL b (List.mem_cons_of_mem _ hb)))))
      exact foldSep (accessedAt (CapyCaptureSet.peakset ctx.capyCtx (appU0 x T1)) c')
        (fun a ha => PC.accessedAt_go_subset _ (by simpa only [accessedAt] using ha))
    -- symmetric key: distinct stable peaks of `PW` give a `SepCheck` of their compiled,
    -- appOpen-substituted lock items
    have key : ∀ (q1 q2 : Peak ((s1,C),x)),
        q1 ∈ (peakList PW).filter (fun p => decide (Peak.IsStable ΓL p)) →
        q2 ∈ (peakList PW).filter (fun p => decide (Peak.IsStable ΓL p)) → q1 ≠ q2 →
        SepCheck ctx.coreCtx
          ((CapyCaptureSet.compile (peakKeyItem PW q1) srcCtxL).subst σ)
          ((CapyCaptureSet.compile (peakKeyItem PW q2) srcCtxL).subst σ) := by
      intro q1 q2 hq1 hq2 hqne
      rcases appPeaks_mem_inventory ctx.capyCtx x T1 hnpp hT1npp hq1 with hc1 | ⟨c1', hc1shape, hc1stab, hc1mem⟩
      · rcases appPeaks_mem_inventory ctx.capyCtx x T1 hnpp hT1npp hq2 with hc2 | ⟨c2', hc2shape, hc2stab, hc2mem⟩
        · -- both are the self-capture peak c: contradiction with q1 ≠ q2
          exact absurd (hc1.trans hc2.symm) hqne
        · -- q1 = c-peak, q2 = Γ-peak c2'
          subst hc1; subst hc2shape
          exact SepCheck.sep_symm (SepCheck.sep_mono
            (SepCheck.sep_symm (SepCheck.sep_mono (sepDpeak c2' hc2stab) itemC))
            (Subcapt.sc_elem (itemT c2')))
      · rcases appPeaks_mem_inventory ctx.capyCtx x T1 hnpp hT1npp hq2 with hc2 | ⟨c2', hc2shape, hc2stab, hc2mem⟩
        · -- q1 = Γ-peak c1', q2 = c-peak
          subst hc1shape; subst hc2
          exact SepCheck.sep_symm (SepCheck.sep_symm (SepCheck.sep_mono
            (SepCheck.sep_symm (SepCheck.sep_mono (sepDpeak c1' hc1stab) itemC))
            (Subcapt.sc_elem (itemT c1'))))
        · -- both Γ-peaks c1', c2'
          subst hc1shape; subst hc2shape
          have hcne : Peak.cvar c1' ≠ Peak.cvar c2' := by
            intro h
            exact hqne (by rw [Peak.cvar.inj h])
          have base := hcovU0 (Peak.cvar c1') (Peak.cvar c2') hc1mem hc2mem hcne
          exact SepCheck.sep_symm (SepCheck.sep_mono
            (SepCheck.sep_symm (SepCheck.sep_mono base (Subcapt.sc_elem (itemT c1'))))
            (Subcapt.sc_elem (itemT c2')))
    rcases hdisj with ⟨hC1, hC2⟩ | ⟨hC1, hC2⟩
    · rw [hC1, hC2]; exact key p1 p2 hp1 hp2 hne
    · rw [hC1, hC2]; exact SepCheck.sep_symm (key p1 p2 hp1 hp2 hne)

end Compilation
