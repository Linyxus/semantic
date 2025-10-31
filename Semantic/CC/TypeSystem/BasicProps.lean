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

/-- If a renamed capture set is closed, the original is also closed. -/
theorem CaptureSet.rename_closed_inv {cs : CaptureSet s1} {f : Rename s1 s2} :
    (cs.rename f).IsClosed -> cs.IsClosed := by
  intro h
  induction cs
  case empty => exact IsClosed.empty
  case union cs1 cs2 ih1 ih2 =>
    simp [CaptureSet.rename] at h
    cases h
    rename_i h1 h2
    exact IsClosed.union (ih1 h1) (ih2 h2)
  case cvar => exact IsClosed.cvar
  case var v =>
    cases v
    case bound => exact IsClosed.var_bound
    case free =>
      -- If cs = .var (.free h), then cs.rename f = .var (.free h)
      -- But h says (cs.rename f).IsClosed, which means no free heap variables
      -- This is a contradiction
      simp [CaptureSet.rename, Var.rename] at h
      cases h

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
  case app ih_x ih_y =>
    exact CaptureSet.IsClosed.union ih_x ih_y

theorem HasType.exp_is_closed
  (ht : C # Γ ⊢ e : T) :
  e.IsClosed := by
  induction ht <;> try (solve | constructor | grind only [Exp.IsClosed])
  case var => constructor; constructor
  case abs T1 ih =>
    rename_i T1_closed
    constructor
    · -- cs✝.IsClosed
      have h_use := HasType.use_set_is_closed T1
      cases h_use with
      | union h_cs_renamed h_var =>
        exact CaptureSet.rename_closed_inv h_cs_renamed
    · -- T1✝.IsClosed
      exact T1_closed
    · -- e✝.IsClosed
      exact ih
  case tabs S ih =>
    rename_i S_closed
    constructor
    · -- cs✝.IsClosed
      have h_use := HasType.use_set_is_closed S
      exact CaptureSet.rename_closed_inv h_use
    · -- S✝.IsClosed (the shape type bound)
      exact S_closed
    · -- e✝.IsClosed
      exact ih
  case cabs cb ih =>
    rename_i cb_closed
    constructor
    · -- cs✝.IsClosed
      have h_use := HasType.use_set_is_closed cb
      exact CaptureSet.rename_closed_inv h_use
    · -- cb✝.IsClosed
      exact cb_closed
    · -- e✝.IsClosed
      exact ih
  case pack C x T =>
    constructor
    · -- C✝.IsClosed
      assumption
    · -- Var.IsClosed x✝
      cases T
      assumption
  case app =>
    rename_i ih_x ih_y
    constructor
    · -- Var.IsClosed x✝
      cases ih_x; assumption
    · -- Var.IsClosed y✝
      cases ih_y; assumption
  case tapp =>
    constructor
    · -- Var.IsClosed x✝
      rename_i _ ih_x
      cases ih_x; assumption
    · -- Ty.IsClosed S✝
      assumption
  case capp =>
    constructor
    · -- Var.IsClosed x✝
      rename_i _ ih_x
      cases ih_x; assumption
    · -- CaptureSet.IsClosed D✝
      assumption
  case letin ih1 ih2 => constructor <;> assumption
  case unpack ih1 ih2 => constructor <;> assumption
  case invoke =>
    rename_i ih_x ih_y
    constructor
    · -- Var.IsClosed x✝
      cases ih_x; assumption
    · -- Var.IsClosed y✝
      cases ih_y; assumption

-- More context lookup properties

theorem Ctx.lookup_var_exists {Γ : Ctx s} {x : BVar s .var} :
  ∃ T, Γ.LookupVar x T := by
  cases x with
  | here =>
    -- x = here, so s = s₀,,var for some s₀
    -- Γ : Ctx (s₀,,var), so Γ = push Γ₀ b where b : Binding s₀ .var
    cases Γ with
    | push Γ₀ b =>
      -- Since b : Binding s₀ .var, we have b = .var T₀
      cases b with
      | var T₀ =>
        use T₀.rename Rename.succ
        apply Ctx.LookupVar.here
  | there x' =>
    -- x = there x', so s = s₀,,k for some s₀, k
    -- Γ : Ctx (s₀,,k), so Γ = push Γ₀ b where b : Binding s₀ k
    cases Γ with
    | push Γ₀ b =>
      -- Recursively apply the theorem to get T₀ such that Γ₀.LookupVar x' T₀
      obtain ⟨T₀, h⟩ := lookup_var_exists (Γ := Γ₀) (x := x')
      use T₀.rename Rename.succ
      apply Ctx.LookupVar.there
      exact h

end CC
