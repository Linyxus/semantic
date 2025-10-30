import Semantic.CC.TypeSystem.Core

/-!
Basic properties of the type system.

This module contains fundamental properties about:
- Context operations and lookups
- Subtyping and subsumption
- Typing judgments
-/

namespace CC

-- Context lookup properties

theorem Ctx.lookup_var_det {Γ : Ctx s} {x : BVar s .var} {T1 T2 : Ty .capt s} :
    Γ.LookupVar x T1 -> Γ.LookupVar x T2 -> T1 = T2 := by
  intro h1 h2
  induction h1
  case here =>
    cases h2
    case here => rfl
  case there ih =>
    cases h2
    case there h2' =>
      have eq := ih h2'
      rw [eq]

theorem Ctx.lookup_tvar_det {Γ : Ctx s} {X : BVar s .tvar} {T1 T2 : Ty .shape s} :
    Γ.LookupTVar X T1 -> Γ.LookupTVar X T2 -> T1 = T2 := by
  intro h1 h2
  induction h1
  case here =>
    cases h2
    case here => rfl
  case there ih =>
    cases h2
    case there h2' =>
      have eq := ih h2'
      rw [eq]

theorem Ctx.lookup_cvar_det {Γ : Ctx s} {c : BVar s .cvar} {cb1 cb2 : CaptureBound s} :
    Γ.LookupCVar c cb1 -> Γ.LookupCVar c cb2 -> cb1 = cb2 := by
  intro h1 h2
  induction h1
  case here =>
    cases h2
    case here => rfl
  case there ih =>
    cases h2
    case there h2' =>
      have eq := ih h2'
      rw [eq]

-- Subsumption reflexivity

theorem Subcapt.refl {Γ : Ctx s} {C : CaptureSet s} :
    Subcapt Γ C C := by
  apply Subcapt.sc_elem
  apply CaptureSet.Subset.refl

theorem Subbound.refl {Γ : Ctx s} {cb : CaptureBound s} :
    Subbound Γ cb cb := by
  cases cb
  case unbound =>
    apply Subbound.top
  case bound C =>
    apply Subbound.capset
    apply Subcapt.refl

/-- Renaming preserves closedness of capture sets. -/
theorem CaptureSet.rename_closed {cs : CaptureSet s1} {f : Rename s1 s2} :
    cs.IsClosed -> (cs.rename f).IsClosed := by
  intro h
  induction h
  case empty => exact IsClosed.empty
  case union ih1 ih2 => exact IsClosed.union ih1 ih2
  case cvar => exact IsClosed.cvar
  case var_bound => exact IsClosed.var_bound

/-- Renaming preserves closedness of capture bounds. -/
theorem CaptureBound.rename_closed {cb : CaptureBound s1} {f : Rename s1 s2} :
    cb.IsClosed -> (cb.rename f).IsClosed := by
  intro h
  cases h
  case unbound => exact IsClosed.unbound
  case bound ih => exact IsClosed.bound (CaptureSet.rename_closed ih)

theorem HasType.use_set_is_closed
  (ht : C # Γ ⊢ e : T) :
  C.IsClosed := by
  induction ht <;> try (solve | constructor | grind only [CaptureSet.IsClosed])

theorem HasType.exp_is_closed
  (ht : C # Γ ⊢ e : T) :
  e.IsClosed := by
  induction ht <;> try (solve | constructor | grind only [Exp.IsClosed])
  case var => sorry
  case abs T1 ih => sorry
  case tabs S ih => sorry
  case cabs cb ih => sorry
  case pack C x T => sorry
  case app => sorry
  case tapp => sorry
  case letin ih1 ih2 => sorry
  case unpack ih1 ih2 => sorry
  case invoke => sorry

/-- The output type of typing is closed. -/
theorem HasType.result_is_closed
  (ht : C # Γ ⊢ t : E) :
  E.IsClosed := by
  induction ht
  case var =>
    sorry
  case abs T1 =>
    sorry
  case tabs S =>
    sorry
  case cabs cb =>
    sorry
  case pack C x T =>
    sorry
  case app =>
    sorry
  case tapp =>
    sorry
  case letin ih1 ih2 =>
    sorry
  case unpack ih1 ih2 =>
    sorry
  case unit =>
    apply Ty.IsClosed.typ
    apply Ty.IsClosed.capt
    · apply CaptureSet.IsClosed.empty
    · apply Ty.IsClosed.unit
  case invoke =>
    apply Ty.IsClosed.typ
    apply Ty.IsClosed.capt
    · apply CaptureSet.IsClosed.empty
    · apply Ty.IsClosed.unit
  case subtyp _ _ _ _ he_closed => sorry

end CC
