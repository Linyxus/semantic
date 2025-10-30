import Semantic.CC.TypeSystem.Core

/-!
Basic properties of the type system.
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

end CC
