import Semantic.CoreCapybara.LegacyCompilation.TypeCompiler
import Semantic.CoreCapybara.LegacyCompilation.TargetRename

open CoreCapybara

namespace Compilation

set_option linter.style.longLine false

/-- **Renaming reflects `top`.**  Only `.top` renames to `.top` — every other head
    constructor is preserved by `rename`, so a renamed non-`top` type is never `.top`. -/
theorem Ty.rename_eq_top {s1 s2 : Sig} {T : Ty .capt s1} {ρ : Rename s1 s2}
    (h : T.rename ρ = .top) : T = .top := by
  cases T <;> simp_all [Ty.rename]

/-- **Compilation reflects `top`.**  Only the source `.top` compiles to the target
    `.top`; every other source head compiles to a non-`top` target head. -/
theorem CapyTy.compile_eq_top {s1 s2 : Sig} {T : CapyTy .capt s1}
    {ctx : CompilerCtx s1 s2} (h : CapyTy.compile T ctx = .top) : T = .top := by
  cases T with
  | cell cs m => cases m <;> simp_all [CapyTy.compile]
  | _ => simp_all [CapyTy.compile]

/-! ### Capture-set monotonicity of `Subtyp`

`A <: B` implies `A.captureSet <: B.captureSet` — every structural rule either
carries the capture `Subcapt` (arrow/poly/cpoly/modal/cap/cell/reader/poly_cap) or
supplies it trivially (`top`: `A` pure ⊑ `∅`; `tvar`: `∅ ⊑ _`; `modal_modal`:
identical captures; `refl`/`trans`: reflexivity/transitivity).  Sort-guarded motive
(`.exi` ↦ `True`) mirrors `Subtyp.eq_top_of_top_gen`. -/

/-- Sort-guarded motive for capture-set monotonicity. -/
def Subtyp.CapMonoMotive {s : Sig} {k : TySort} (Γ : Ctx s) (A B : Ty k s) : Prop :=
  match k, A, B with
  | .capt, A, B => Subcapt Γ A.captureSet B.captureSet
  | .exi, _, _ => True

theorem Subtyp.CapMonoMotive.refl {s : Sig} {k : TySort} {Γ : Ctx s} {A : Ty k s} :
    Subtyp.CapMonoMotive Γ A A := by
  cases k with
  | capt => exact Subcapt.sc_elem CaptureSet.Subset.refl
  | exi => trivial

theorem Subtyp.CapMonoMotive.trans {s : Sig} {k : TySort} {Γ : Ctx s} {A M B : Ty k s}
    (ih1 : Subtyp.CapMonoMotive Γ A M) (ih2 : Subtyp.CapMonoMotive Γ M B) :
    Subtyp.CapMonoMotive Γ A B := by
  cases k with
  | capt => exact Subcapt.sc_trans ih1 ih2
  | exi => trivial

/-- General-sort core of capture monotonicity. -/
theorem Subtyp.captureSet_subcapt_gen {s : Sig} {Γ : Ctx s} {k : TySort} {A B : Ty k s}
    (h : Subtyp Γ A B) : Subtyp.CapMonoMotive Γ A B := by
  induction h with
  | top hpure => exact Subcapt.sc_elem (CaptureSet.IsEmpty.subset hpure)
  | refl => exact Subtyp.CapMonoMotive.refl
  | trans _ _ _ ih1 ih2 => exact Subtyp.CapMonoMotive.trans ih1 ih2
  | tvar _ => exact Subcapt.sc_elem CaptureSet.Subset.empty
  | arrow _ hcs _ _ _ => exact hcs
  | poly _ hcs _ _ _ => exact hcs
  | cpoly _ hcs _ _ => exact hcs
  | modal hcs _ _ => exact hcs
  | modal_modal _ _ _ _ => exact Subcapt.sc_elem CaptureSet.Subset.refl
  | cell hcs => exact hcs
  | reader hcs => exact hcs
  | cap hcs => exact hcs
  | poly_cap hcs => exact hcs
  | exi _ _ => trivial
  | typ _ _ => trivial

/-- **Capture-set monotonicity of `Subtyp`.**  `A <: B ⟹ A.captureSet <: B.captureSet`. -/
theorem Subtyp.captureSet_subcapt {s : Sig} {Γ : Ctx s} {A B : Ty .capt s}
    (h : Subtyp Γ A B) : Subcapt Γ A.captureSet B.captureSet :=
  Subtyp.captureSet_subcapt_gen h

/-! ### `top`-preservation under bounded refinement

The `app`-case top corner: an argument whose (refined) type is a subtype of `.top`
stays so after re-refining by a capture `c` that is **bounded by the type's own
capture** — the reachable case, since `A`'s self-capture atom is `sc_var`-below its
stored type.  Unconditional refinement is UNSOUND (`cap ∅ <: .top` but
`(cap ∅).refine c = cap c ⊄ .top` for nonempty `c`); the `Subcapt c A.captureSet`
premise is exactly what rules that out. -/

/-- **`.top`-preservation under bounded refinement.**  If `A <: .top` and the refine
    atom `c` is below `A`'s capture, then `A.refineCaptureSet c <: .top`.  (Refining to
    `∅` via `refine_mono`, then `.top` since every head refined at `∅` is pure.) -/
theorem Subtyp.refine_top_preserved {s : Sig} {Γ : Ctx s} {A : Ty .capt s} {c : CaptureSet s}
    (h : Subtyp Γ A .top) (hc : Subcapt Γ c A.captureSet) (hAcl : A.IsClosed) :
    Subtyp Γ (A.refineCaptureSet c) .top := by
  have hcm : Subcapt Γ A.captureSet (CaptureSet.empty) := Subtyp.captureSet_subcapt h
  have hc0 : Subcapt Γ c (CaptureSet.empty) := Subcapt.sc_trans hc hcm
  have hstep : Subtyp Γ (A.refineCaptureSet c) (A.refineCaptureSet CaptureSet.empty) :=
    Subtyp.refine_mono hc0
  have hpure : (A.refineCaptureSet CaptureSet.empty).IsPureType := by
    cases A <;> exact CaptureSet.IsEmpty.empty
  have hcl2 : (A.refineCaptureSet CaptureSet.empty).IsClosed :=
    Ty.refineCaptureSet_closed hAcl CaptureSet.IsClosed.empty
  exact Subtyp.trans hcl2 hstep (Subtyp.top hpure)

end Compilation
