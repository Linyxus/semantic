import Semantic.CoreCapybara.Compilation.Coherence
import Semantic.CoreCapybara.Compilation.SubstLemmas
open CoreCapybara
namespace Compilation

/-!
# Subtyping compilation

`CapySubtyp Γ A B ⟹ Subtyp ⟦Γ⟧ ⟦A⟧ ⟦B⟧` — source subtyping compiles to target
subtyping.  This is BOTH the `subtyp` case of the main term-compilation theorem
AND the bridge used by `fresh`'s variable re-derivation (`compile_var_typ_empty`).

Structural/leaf cases (`top`/`refl`/`trans`/`tvar`/`typ`) are discharged here.
The `exi` case needs the `consCVar` coherence-preservation lemma (K2); the
`arrow`/`poly`/`cpoly` cases need the function-lock subtyping kernel (K1) — both
tracked in `notes/fresh-roadmap.md`.
-/

/-- Compilation distributes over `applyRO` (`applyRO = applyMut .ro`). -/
theorem CaptureSet.compile_applyRO {cs : CaptureSet s1} {sc : SrcCtx s1 s2} :
    CaptureSet.compile cs.applyRO sc = (CaptureSet.compile cs sc).applyRO := by
  rw [← CaptureSet.applyMut_ro, CaptureSet.compile_applyMut, CaptureSet.applyMut_ro]

/-- Compilation preserves capture-set subset (it is a homomorphism on the
    union/empty structure that `Subset` is defined over). -/
theorem CaptureSet.compile_subset {C1 C2 : CaptureSet s1} {sc : SrcCtx s1 s2}
    (h : CaptureSet.Subset C1 C2) :
    CaptureSet.Subset (CaptureSet.compile C1 sc) (CaptureSet.compile C2 sc) := by
  induction h with
  | refl => exact .refl
  | empty => simp only [CaptureSet.compile]; exact .empty
  | union_left _ _ ih1 ih2 => simp only [CaptureSet.compile]; exact .union_left ih1 ih2
  | union_right_left _ ih => simp only [CaptureSet.compile]; exact .union_right_left ih
  | union_right_right _ ih => simp only [CaptureSet.compile]; exact .union_right_right ih

/-- **Subcapturing compiles to subcapturing.**  Source and target `Subcapt` share
    the same constructor structure, so this is a clean structural induction (the
    `sc_var`/`sc_cvar` cases use the `varLookup`/`cvarLookup` coherence fields). -/
theorem CapySubcapt.compile {s1 : Sig} {Γ : CapyCtx s1} {C1 C2 : CaptureSet s1}
    (h : CapySubcapt Γ C1 C2) :
    ∀ {s2 : Sig} (ctx : CompilerCtx s1 s2), ctx.capyCtx = Γ → ctx.Coherent →
    Subcapt ctx.coreCtx (CaptureSet.compile C1 ctx.srcCtx)
      (CaptureSet.compile C2 ctx.srcCtx) := by
  induction h with
  | sc_trans _ _ ih1 ih2 =>
    intro s2 ctx hΓ hcoh
    exact Subcapt.sc_trans (ih1 ctx hΓ hcoh) (ih2 ctx hΓ hcoh)
  | sc_elem hsub =>
    intro s2 ctx hΓ hcoh
    exact Subcapt.sc_elem (CaptureSet.compile_subset hsub)
  | sc_mode hle =>
    intro s2 ctx hΓ hcoh
    simp only [CaptureSet.compile_applyMut]
    exact Subcapt.sc_mode hle
  | sc_union _ _ ih1 ih2 =>
    intro s2 ctx hΓ hcoh
    simp only [CaptureSet.compile]
    exact Subcapt.sc_union (ih1 ctx hΓ hcoh) (ih2 ctx hΓ hcoh)
  | sc_var hlk =>
    intro s2 ctx hΓ hcoh
    obtain ⟨bv, _, hlv, _⟩ := hcoh.varLookup (hΓ ▸ hlk)
    simp only [CaptureSet.compile, CaptureSet.applyAccess_M, CaptureSet.applyMut_epsilon, hlv]
    exact Subcapt.sc_elem CaptureSet.Subset.refl
  | sc_cvar hlk =>
    intro s2 ctx hΓ hcoh
    simp only [CaptureSet.compile]
    exact Subcapt.sc_cvar (hcoh.cvarLookup (hΓ ▸ hlk))
  | sc_ro =>
    intro s2 ctx hΓ hcoh
    simp only [CaptureSet.compile_applyRO]
    exact Subcapt.sc_ro
  | sc_ro_mono _ ih =>
    intro s2 ctx hΓ hcoh
    simp only [CaptureSet.compile_applyRO]
    exact Subcapt.sc_ro_mono (ih ctx hΓ hcoh)
  | sc_drop_mono _ ih =>
    intro s2 ctx hΓ hcoh
    simp only [CaptureSet.compile_applyAccess]
    exact Subcapt.sc_drop_mono (ih ctx hΓ hcoh)

/-- Source subtyping compiles to target subtyping. -/
theorem CapySubtyp.compile {s1 : Sig} {Γ : CapyCtx s1} {sort : CapyTySort}
    {A B : CapyTy sort s1} (h : CapySubtyp Γ A B) :
    ∀ {s2 : Sig} (ctx : CompilerCtx s1 s2), ctx.capyCtx = Γ → ctx.Coherent →
    Subtyp ctx.coreCtx (CapyTy.compile A ctx) (CapyTy.compile B ctx) := by
  induction h with
  | top hpure =>
    intro s2 ctx hΓ hcoh
    simp only [CapyTy.compile]
    exact Subtyp.top (CapyTy.compile_isPure hpure)
  | refl =>
    intro s2 ctx hΓ hcoh
    exact Subtyp.refl
  | trans hT2 _ _ ih1 ih2 =>
    intro s2 ctx hΓ hcoh
    exact Subtyp.trans (CapyTy.compile_isClosed _ _ hT2 hcoh.srcClosed)
      (ih1 ctx hΓ hcoh) (ih2 ctx hΓ hcoh)
  | tvar hlk =>
    intro s2 ctx hΓ hcoh
    simp only [CapyTy.compile]
    exact Subtyp.tvar (hcoh.tvarLookup (hΓ ▸ hlk))
  | typ _ ih =>
    intro s2 ctx hΓ hcoh
    simp only [CapyTy.compile]
    exact Subtyp.typ (ih ctx hΓ hcoh)
  | exi _ ih =>
    intro s2 ctx hΓ hcoh
    -- K2: needs `consCVar` coherence preservation to feed `ih` the extended ctx.
    sorry
  | arrow _ _ _ ih1 ih3 =>
    intro s2 ctx hΓ hcoh
    -- K1: function-lock subtyping kernel.
    sorry
  | poly _ _ _ ih1 ih3 =>
    intro s2 ctx hΓ hcoh
    -- K1: function-lock subtyping kernel.
    sorry
  | cpoly _ _ _ ih3 =>
    intro s2 ctx hΓ hcoh
    -- K1: function-lock subtyping kernel.
    sorry

end Compilation
