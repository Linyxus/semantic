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

/-- If a renamed capture bound is closed, the original is also closed. -/
theorem CaptureBound.rename_closed_inv {cb : CaptureBound s1} {f : Rename s1 s2} :
    (cb.rename f).IsClosed -> cb.IsClosed := by
  intro h
  cases cb
  case unbound => exact IsClosed.unbound
  case bound cs =>
    simp [CaptureBound.rename] at h
    cases h
    exact IsClosed.bound (CaptureSet.rename_closed_inv ‹_›)

theorem Ty.rename_closed {T : Ty sort s1} {f : Rename s1 s2} :
    T.IsClosed -> (T.rename f).IsClosed := by
  intro h
  induction T generalizing s2
  case top => exact IsClosed.top
  case tvar => exact IsClosed.tvar
  case arrow T1 T2 ih1 ih2 =>
    cases h with | arrow h1 h2 =>
    exact IsClosed.arrow (ih1 h1) (ih2 h2)
  case poly S T ih1 ih2 =>
    cases h with | poly h1 h2 =>
    exact IsClosed.poly (ih1 h1) (ih2 h2)
  case cpoly cb T ihcb ihT =>
    cases h with | cpoly hcb hT =>
    exact IsClosed.cpoly (CaptureBound.rename_closed hcb) (ihT hT)
  case unit => exact IsClosed.unit
  case cap => exact IsClosed.cap
  case bool => exact IsClosed.bool
  case cell => exact IsClosed.cell
  case capt C S ihC ihS =>
    cases h with | capt hC hS =>
    exact IsClosed.capt (CaptureSet.rename_closed hC) (ihS hS)
  case typ T ih =>
    cases h with | typ hT =>
    exact IsClosed.typ (ih hT)
  case exi T ih =>
    cases h with | exi hT =>
    exact IsClosed.exi (ih hT)

/-- If a renamed type is closed, the original is also closed. -/
theorem Ty.rename_closed_inv {T : Ty sort s1} {f : Rename s1 s2} :
    (T.rename f).IsClosed -> T.IsClosed := by
  intro h
  induction T generalizing s2
  case top => exact IsClosed.top
  case tvar => exact IsClosed.tvar
  case arrow T1 T2 ih1 ih2 =>
    simp [Ty.rename] at h
    cases h; rename_i h1 h2
    exact IsClosed.arrow (ih1 h1) (ih2 h2)
  case poly S T ih1 ih2 =>
    simp [Ty.rename] at h
    cases h; rename_i h1 h2
    exact IsClosed.poly (ih1 h1) (ih2 h2)
  case cpoly cb T ihcb ihT =>
    simp [Ty.rename] at h
    cases h; rename_i hcb hT
    constructor
    · exact CaptureBound.rename_closed_inv hcb
    · exact ihT hT
  case unit => exact IsClosed.unit
  case cap => exact IsClosed.cap
  case bool => exact IsClosed.bool
  case cell => exact IsClosed.cell
  case capt C S ihC ihS =>
    simp [Ty.rename] at h
    cases h; rename_i hC hS
    exact IsClosed.capt (CaptureSet.rename_closed_inv hC) (ihS hS)
  case typ T ih =>
    simp [Ty.rename] at h
    cases h; rename_i hT
    exact IsClosed.typ (ih hT)
  case exi T ih =>
    simp [Ty.rename] at h
    cases h; rename_i hT
    exact IsClosed.exi (ih hT)

theorem Ctx.lookup_var_gives_closed {Γ : Ctx s} {x : BVar s .var} {T : Ty .capt s}
  (hΓ : Γ.IsClosed) (hlookup : Γ.LookupVar x T) :
  T.IsClosed := by
  induction hlookup with
  | here =>
    cases hΓ with | push hΓ_prev hb =>
    cases hb with | var hT =>
    exact Ty.rename_closed hT
  | there _ ih =>
    cases hΓ with | push hΓ_prev _ =>
    have hT := ih hΓ_prev
    exact Ty.rename_closed hT

theorem HasType.use_set_is_closed
  (ht : C # Γ ⊢ e : T) :
  C.IsClosed := by
  induction ht <;> try (solve | constructor | grind only [CaptureSet.IsClosed])
  case app ih_x ih_y =>
    exact CaptureSet.IsClosed.union ih_x ih_y
  case invoke ih_x ih_y =>
    exact CaptureSet.IsClosed.union ih_x ih_y
  case write ih_x ih_y =>
    exact CaptureSet.IsClosed.union ih_x ih_y
  case cond ih1 ih2 ih3 =>
    exact CaptureSet.IsClosed.union (CaptureSet.IsClosed.union ih1 ih2) ih3

theorem HasType.exp_is_closed
  (ht : C # Γ ⊢ e : T) :
  e.IsClosed := by
  induction ht <;> try (solve | constructor | grind only [Exp.IsClosed])
  case var => constructor; constructor
  case read ih_x =>
    -- ih_x : (.var x).IsClosed, need to extract x.IsClosed
    cases ih_x with
    | var hx_closed =>
      constructor
      exact hx_closed
  case write ih_x ih_y =>
    -- Need to extract variable closedness from both IHs
    cases ih_x with
    | var hx_closed =>
      cases ih_y with
      | var hy_closed =>
        constructor
        · exact hx_closed
        · exact hy_closed
  case cond ih_var ih2 ih3 =>
    -- ih_var : (.var x).IsClosed, need to extract x.IsClosed
    cases ih_var with
    | var hx_closed =>
      constructor
      · exact hx_closed
      · exact ih2
      · exact ih3
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

theorem HasType.type_is_closed
  (ht : C # Γ ⊢ e : E) :
  E.IsClosed := by
  induction ht <;> try (solve | constructor | grind only [Ty.IsClosed])
  case var hΓ_closed hlookup =>
    constructor
    -- Need to prove: (.capt (.var (.bound x)) S).IsClosed
    -- We have: hlookup : Γ.LookupVar x (.capt C S)
    -- Extract S.IsClosed from the lookup
    have hT_closed := Ctx.lookup_var_gives_closed hΓ_closed hlookup
    cases hT_closed with | capt _ hS =>
    constructor
    · -- (.var (.bound x)).IsClosed
      constructor
    · -- S.IsClosed
      exact hS
  case abs T1_closed ht_body ih =>
    constructor
    constructor
    · -- cs.IsClosed where cs.rename Rename.succ ∪ ... typed the body
      have h_use := HasType.use_set_is_closed ht_body
      cases h_use with | union h_cs_renamed h_var =>
      exact CaptureSet.rename_closed_inv h_cs_renamed
    · constructor <;> assumption
  case tabs S_closed ht_body ih =>
    constructor
    constructor
    · -- cs.IsClosed where cs.rename Rename.succ typed the body
      have h_use := HasType.use_set_is_closed ht_body
      exact CaptureSet.rename_closed_inv h_use
    · constructor <;> assumption
  case cabs cb_closed ht_body ih =>
    constructor
    constructor
    · -- cs.IsClosed where cs.rename Rename.succ typed the body
      have h_use := HasType.use_set_is_closed ht_body
      exact CaptureSet.rename_closed_inv h_use
    · constructor <;> assumption
  case pack hC ih =>
    constructor
    -- ih : (T✝.subst (Subst.openCVar C✝)).typ.IsClosed
    -- Goal: T✝.IsClosed
    -- Extract closedness from .typ wrapper
    cases ih with | typ hT =>
    -- hT : (T✝.subst (Subst.openCVar C✝)).IsClosed
    -- Apply Ty.subst_closed_inv to get T✝.IsClosed
    exact Ty.subst_closed_inv hT
  case read ih_x =>
    -- Goal: (Ty.capt ∅ Ty.bool).typ.IsClosed
    constructor
    constructor
    · constructor
    · constructor
  case write ih_x ih_y =>
    -- Goal: (Ty.capt ∅ Ty.unit).typ.IsClosed
    constructor
    constructor
    · constructor
    · constructor
  case app ht_x ht_y ih_x ih_y =>
    -- Goal: (T2✝.subst (Subst.openVar y✝)).IsClosed
    -- After rename_i, variables get renamed in order: s✝ x✝ Γ✝ T1✝ T2✝ y✝
    -- So we name them: sig_s func_x ctx_gamma arg_type result_type arg_y
    rename_i sig_s func_x ctx_gamma arg_type result_type arg_y
    -- Extract result_type.IsClosed from ih_x
    cases ih_x with | typ h =>
    cases h with | capt _ h =>
    cases h with | arrow _ hT2 =>
    -- hT2 : result_type.IsClosed
    -- Get arg_y.IsClosed from the closed expression
    have hy_closed : arg_y.IsClosed := by
      have h_exp := HasType.exp_is_closed ht_y
      cases h_exp; assumption
    exact Ty.is_closed_subst hT2 (Subst.openVar_is_closed hy_closed)
  case tapp hS_closed ht_x ih =>
    rename_i x S T
    -- ih : (Ty.capt (CaptureSet.var x) (S.poly T)).typ.IsClosed
    -- hS_closed : S.IsClosed
    -- Extract: T.IsClosed
    cases ih with | typ h =>
    cases h with | capt _ h =>
    cases h with | poly _ hT =>
    -- hT : T.IsClosed
    -- Need: (T.subst (Subst.openTVar S)).IsClosed
    exact Ty.is_closed_subst hT (Subst.openTVar_is_closed hS_closed)
  case capp hD_closed ht_x ih =>
    rename_i x D T
    -- ih : (Ty.capt (CaptureSet.var x) (Ty.cpoly (CaptureBound.bound D) T)).typ.IsClosed
    -- hD_closed : D.IsClosed
    -- Extract: T.IsClosed
    cases ih with | typ h =>
    cases h with | capt _ h =>
    cases h with | cpoly _ hT =>
    -- hT : T.IsClosed
    -- Need: (T.subst (Subst.openCVar D)).IsClosed
    exact Ty.is_closed_subst hT (Subst.openCVar_is_closed hD_closed)
  case letin ih1 ih2 =>
    -- ih2 : (U.rename Rename.succ).IsClosed
    -- Need: U.IsClosed
    exact Ty.rename_closed_inv ih2
  case unpack ih1 ih2 =>
    -- ih2 : ((U.rename Rename.succ).rename Rename.succ).IsClosed
    -- Need: U.IsClosed
    apply Ty.rename_closed_inv
    exact Ty.rename_closed_inv ih2
  case unit =>
    constructor
    constructor
    · constructor
    · constructor
  case invoke =>
    constructor
    constructor
    · constructor
    · constructor
  case btrue =>
    exact Ty.IsClosed.typ (Ty.IsClosed.capt CaptureSet.IsClosed.empty Ty.IsClosed.bool)
  case bfalse =>
    exact Ty.IsClosed.typ (Ty.IsClosed.capt CaptureSet.IsClosed.empty Ty.IsClosed.bool)

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
