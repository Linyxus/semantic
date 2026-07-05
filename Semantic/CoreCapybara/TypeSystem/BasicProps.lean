import Semantic.CoreCapybara.TypeSystem.Core

/-!
Basic properties of the type system.

This module contains fundamental properties about:
- Context operations and lookups
- Subtyping and subsumption
- Typing judgments
-/

namespace CoreCapybara

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

theorem Ctx.lookup_tvar_det {Γ : Ctx s} {X : BVar s .tvar} {T1 T2 : PureTy s} :
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

theorem Ctx.lookup_cvar_det {Γ : Ctx s} {c : BVar s .cvar}
    {a1 a2 : Authority} {cb1 cb2 : CaptureBound s} :
    Γ.LookupCVar c a1 cb1 -> Γ.LookupCVar c a2 cb2 -> cb1 = cb2 := by
  intro h1 h2
  induction h1 generalizing a2
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
  exact Subcapt.sc_elem CaptureSet.Subset.refl

/-- Renaming preserves closedness of capture sets. -/
theorem CaptureSet.rename_closed {cs : CaptureSet s1} {f : Rename s1 s2} :
    cs.IsClosed -> (cs.rename f).IsClosed := by
  intro h
  induction h
  case empty => exact IsClosed.empty
  case union ih1 ih2 => exact IsClosed.union ih1 ih2
  case cvar => exact IsClosed.cvar
  case var_bound => exact IsClosed.var_bound

/-- The `n` fresh capture-variable atoms of an `n`-ary existential are closed:
they are all bound `.cvar` atoms. Used to establish the manufactured lock's
well-formedness in the `unpack_own` semantic case. -/
theorem CaptureSet.freshCVars_isClosed {s : Sig} (n : Nat) :
    (CaptureSet.freshCVars (s := s) n).IsClosed := by
  induction n with
  | zero => exact CaptureSet.IsClosed.empty
  | succ n ih =>
    exact CaptureSet.IsClosed.union CaptureSet.IsClosed.cvar (CaptureSet.rename_closed ih)

/-- If a renamed capture set is closed, the original is also closed. -/
theorem CaptureSet.rename_closed_inv {cs : CaptureSet s1} {f : Rename s1 s2} :
    (cs.rename f).IsClosed -> cs.IsClosed := by
  intro h
  induction cs
  case empty => exact IsClosed.empty
  case union cs1 cs2 ih1 ih2 =>
    simp only [CaptureSet.rename] at h
    cases h
    rename_i h1 h2
    exact IsClosed.union (ih1 h1) (ih2 h2)
  case cvar => exact IsClosed.cvar
  case var v =>
    cases v
    case bound => exact IsClosed.var_bound
    case free =>
      simp only [CaptureSet.rename, Var.rename] at h
      cases h

theorem CaptureBound.rename_closed {cb : CaptureBound s1} {f : Rename s1 s2} :
    cb.IsClosed -> (cb.rename f).IsClosed := by
  intro h
  cases h with
  | unbound => exact CaptureBound.IsClosed.unbound
  | bound hcs => exact CaptureBound.IsClosed.bound (CaptureSet.rename_closed hcs)

theorem CaptureBound.rename_closed_inv {cb : CaptureBound s1} {f : Rename s1 s2} :
    (cb.rename f).IsClosed -> cb.IsClosed := by
  intro h
  cases cb with
  | unbound => exact CaptureBound.IsClosed.unbound
  | bound cs =>
    simp only [CaptureBound.rename] at h
    cases h with
    | bound hcs =>
      exact CaptureBound.IsClosed.bound (CaptureSet.rename_closed_inv hcs)

/-- Renaming preserves closedness of separation contexts. -/
theorem SepCtx.rename_closed {Ψ : SepCtx s1} {f : Rename s1 s2} :
    Ψ.IsClosed -> (Ψ.rename f).IsClosed := by
  intro h
  induction h with
  | empty => exact SepCtx.IsClosed.empty
  | cons hΨ hC ih =>
    exact SepCtx.IsClosed.cons ih (CaptureSet.rename_closed hC)

/-- If a renamed separation context is closed, the original is also closed. -/
theorem SepCtx.rename_closed_inv {Ψ : SepCtx s1} {f : Rename s1 s2} :
    (Ψ.rename f).IsClosed -> Ψ.IsClosed := by
  intro h
  induction Ψ with
  | empty => exact SepCtx.IsClosed.empty
  | cons Ψ C ih =>
    simp only [SepCtx.rename] at h
    cases h with
    | cons hΨ hC =>
      exact SepCtx.IsClosed.cons (ih hΨ) (CaptureSet.rename_closed_inv hC)

/-- Renaming preserves closedness of mutability contexts. -/
theorem MutabilityCtx.rename_closed {Ψ : MutabilityCtx s1} {f : Rename s1 s2} :
    Ψ.IsClosed -> (Ψ.rename f).IsClosed := by
  intro h
  induction h with
  | empty => exact MutabilityCtx.IsClosed.empty
  | cons hΨ hC ih =>
    exact MutabilityCtx.IsClosed.cons ih (CaptureSet.rename_closed hC)

theorem MutabilityCtx.rename_closed_inv {Ψ : MutabilityCtx s1} {f : Rename s1 s2} :
    (Ψ.rename f).IsClosed -> Ψ.IsClosed := by
  intro h
  induction Ψ with
  | empty => exact MutabilityCtx.IsClosed.empty
  | cons Ψ C m ih =>
    simp only [MutabilityCtx.rename] at h
    cases h with
    | cons hΨ hC =>
      exact MutabilityCtx.IsClosed.cons (ih hΨ) (CaptureSet.rename_closed_inv hC)

/-- Renaming preserves closedness of modal contexts. -/
theorem ModalCtx.rename_closed {Ψ : ModalCtx s1} {f : Rename s1 s2} :
    Ψ.IsClosed -> (Ψ.rename f).IsClosed := fun h =>
  ⟨SepCtx.rename_closed h.sep, MutabilityCtx.rename_closed h.mutability⟩

theorem ModalCtx.rename_closed_inv {Ψ : ModalCtx s1} {f : Rename s1 s2} :
    (Ψ.rename f).IsClosed -> Ψ.IsClosed := fun h =>
  ⟨SepCtx.rename_closed_inv h.sep, MutabilityCtx.rename_closed_inv h.mutability⟩

/-- Refining a closed type with a closed capture set yields a closed type. -/
theorem Ty.refineCaptureSet_closed {T : Ty .capt s} {cs : CaptureSet s} :
    T.IsClosed -> cs.IsClosed -> (T.refineCaptureSet cs).IsClosed := by
  intro hT hcs
  cases hT with
  | top => exact IsClosed.top
  | tvar => exact IsClosed.tvar
  | arrow h1 _ h2 => exact IsClosed.arrow h1 hcs h2
  | poly h1 _ h2 => exact IsClosed.poly h1 hcs h2
  | cpoly hcb _ hT' => exact IsClosed.cpoly hcb hcs hT'
  | consumer h1 _ h2 => exact IsClosed.consumer h1 hcs h2
  | modal _ hΨ hT' => exact IsClosed.modal hcs hΨ hT'
  | unit => exact IsClosed.unit
  | cap _ => exact IsClosed.cap hcs
  | bool => exact IsClosed.bool
  | cell _ hT => exact IsClosed.cell hcs hT
  | reader _ hT => exact IsClosed.reader hcs hT

theorem Ty.rename_closed {T : Ty sort s1} {f : Rename s1 s2} :
    T.IsClosed -> (T.rename f).IsClosed := by
  intro h
  induction T generalizing s2
  case top => exact IsClosed.top
  case tvar => exact IsClosed.tvar
  case arrow T1 cs T2 ih1 ih2 =>
    cases h with | arrow h1 hcs h2 =>
    exact IsClosed.arrow (ih1 h1)
      (CaptureSet.rename_closed hcs) (ih2 h2)
  case poly S cs T ih1 ih2 =>
    cases h with | poly h1 hcs h2 =>
    exact IsClosed.poly (ih1 h1)
      (CaptureSet.rename_closed hcs) (ih2 h2)
  case cpoly cb cs T ihT =>
    cases h with | cpoly hcb hcs hT =>
    exact IsClosed.cpoly (CaptureBound.rename_closed hcb)
      (CaptureSet.rename_closed hcs) (ihT hT)
  case consumer T1 cs T2 ih1 ih2 =>
    cases h with | consumer h1 hcs h2 =>
    exact IsClosed.consumer (ih1 h1)
      (CaptureSet.rename_closed hcs) (ih2 h2)
  case modal cs Ψ T ihT =>
    cases h with | modal hcs hΨ hT =>
    exact IsClosed.modal (CaptureSet.rename_closed hcs)
      (ModalCtx.rename_closed hΨ) (ihT hT)
  case unit => exact IsClosed.unit
  case cap cs =>
    cases h with | cap hcs =>
    exact IsClosed.cap (CaptureSet.rename_closed hcs)
  case bool => exact IsClosed.bool
  case cell cs T ihT =>
    cases h with | cell hcs hT =>
    exact IsClosed.cell (CaptureSet.rename_closed hcs) (ihT hT)
  case reader cs T ihT =>
    cases h with | reader hcs hT =>
    exact IsClosed.reader (CaptureSet.rename_closed hcs) (ihT hT)
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
  case arrow T1 cs T2 ih1 ih2 =>
    simp only [Ty.rename] at h
    cases h with | arrow h1 hcs h2 =>
    exact IsClosed.arrow (ih1 h1)
      (CaptureSet.rename_closed_inv hcs) (ih2 h2)
  case poly S cs T ih1 ih2 =>
    simp only [Ty.rename] at h
    cases h with | poly h1 hcs h2 =>
    exact IsClosed.poly (ih1 h1)
      (CaptureSet.rename_closed_inv hcs) (ih2 h2)
  case cpoly cb cs T ihT =>
    simp only [Ty.rename] at h
    cases h with | cpoly hcb hcs hT =>
    exact IsClosed.cpoly (CaptureBound.rename_closed_inv hcb)
      (CaptureSet.rename_closed_inv hcs) (ihT hT)
  case consumer T1 cs T2 ih1 ih2 =>
    simp only [Ty.rename] at h
    cases h with | consumer h1 hcs h2 =>
    exact IsClosed.consumer (ih1 h1)
      (CaptureSet.rename_closed_inv hcs) (ih2 h2)
  case modal cs Ψ T ihT =>
    simp only [Ty.rename] at h
    cases h with | modal hcs hΨ hT =>
    exact IsClosed.modal (CaptureSet.rename_closed_inv hcs)
      (ModalCtx.rename_closed_inv hΨ) (ihT hT)
  case unit => exact IsClosed.unit
  case cap cs =>
    simp only [Ty.rename] at h
    cases h; rename_i hcs
    exact IsClosed.cap (CaptureSet.rename_closed_inv hcs)
  case bool => exact IsClosed.bool
  case cell cs T ihT =>
    simp only [Ty.rename] at h
    cases h with | cell hcs hT =>
    exact IsClosed.cell (CaptureSet.rename_closed_inv hcs) (ihT hT)
  case reader cs T ihT =>
    simp only [Ty.rename] at h
    cases h with | reader hcs hT =>
    exact IsClosed.reader (CaptureSet.rename_closed_inv hcs) (ihT hT)
  case typ T ih =>
    simp only [Ty.rename] at h
    cases h; rename_i hT
    exact IsClosed.typ (ih hT)
  case exi T ih =>
    simp only [Ty.rename] at h
    cases h; rename_i hT
    exact IsClosed.exi (ih hT)

theorem Exp.rename_closed_inv {e : Exp s1} {f : Rename s1 s2} :
    (e.rename f).IsClosed -> e.IsClosed := by
  intro h
  rw [← Exp.subst_asSubst] at h
  exact Exp.subst_closed_inv h

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

/-- A typed variable expression has a closed variable. -/
theorem HasType.typed_var_closed
  {x : Var Kind.var s}
  (ht : HasType C Γ (Exp.var x) T) :
  x.IsClosed := by
  generalize he : Exp.var x = e at ht
  induction ht with
  | var => cases he; exact Var.IsClosed.bound
  | subtyp _ _ _ _ _ ih => exact ih he
  | _ => cases he

/-- The capture set `{m x}` is closed when `x` is a typed variable. -/
theorem HasType.typed_var_capture_closed
  {x : Var Kind.var s} {a : Access}
  (ht : HasType C Γ (Exp.var x) T) :
  (CaptureSet.var a x).IsClosed := by
  have hx := typed_var_closed ht
  cases x with
  | bound => exact CaptureSet.IsClosed.var_bound
  | free => cases hx

theorem HasType.use_set_is_closed
  (ht : HasType C Γ e T) :
  C.IsClosed := by
  induction ht with
  | var => exact CaptureSet.IsClosed.empty
  | reader => exact CaptureSet.IsClosed.empty
  | abs => exact CaptureSet.IsClosed.empty
  | tabs => exact CaptureSet.IsClosed.empty
  | cabs => exact CaptureSet.IsClosed.empty
  | consumer => exact CaptureSet.IsClosed.empty
  | wrap => exact CaptureSet.IsClosed.empty
  | pack hC _ _ _ =>
    exact CaptureSet.IsClosed.union hC (CaptureSet.applyAccess_isClosed hC)
  | app _ ht_x _ _ _ => exact HasType.typed_var_capture_closed ht_x
  | consumer_app _ _ _ ht_x _ _ ih_e =>
    exact CaptureSet.IsClosed.union ih_e (HasType.typed_var_capture_closed ht_x)
  | tapp _ _ ht_x _ => exact HasType.typed_var_capture_closed ht_x
  | capp _ _ _ ht_x _ => exact HasType.typed_var_capture_closed ht_x
  | unwrap ht_x _ _ => exact HasType.typed_var_capture_closed ht_x
  | letin _ _ _ ih1 ih2 =>
    exact CaptureSet.IsClosed.union ih1 (CaptureSet.rename_closed_inv ih2)
  | unpack _ _ _ _ ih1 ih2 =>
    cases ih2 with
    | union hleft _ =>
      cases hleft with
      | union hC2 _ =>
        exact CaptureSet.IsClosed.union ih1
          (CaptureSet.rename_closed_inv (CaptureSet.rename_closed_inv hC2))
  | unpack_own _ _ _ _ ih1 ih2 =>
    -- Same as `unpack`, but the `C2` summand of the continuation budget carries
    -- one extra `.lock`-succ rename layer, so peel THREE renames off `hC2`.
    cases ih2 with
    | union hleft _ =>
      cases hleft with
      | union hC2 _ =>
        exact CaptureSet.IsClosed.union ih1
          (CaptureSet.rename_closed_inv (CaptureSet.rename_closed_inv
            (CaptureSet.rename_closed_inv hC2)))
  | unit => exact CaptureSet.IsClosed.empty
  | btrue => exact CaptureSet.IsClosed.empty
  | bfalse => exact CaptureSet.IsClosed.empty
  | alloc => exact CaptureSet.IsClosed.empty
  | drop _ _ ht_x _ => exact HasType.typed_var_capture_closed ht_x
  | read _ ht_x _ => exact HasType.typed_var_capture_closed ht_x
  | write _ ht_x _ _ _ => exact HasType.typed_var_capture_closed ht_x
  | cond _ _ _ ih1 ih2 ih3 =>
    exact CaptureSet.IsClosed.union (CaptureSet.IsClosed.union ih1 ih2) ih3
  | par _ _ _ ih1 ih2 => exact CaptureSet.IsClosed.union ih1 ih2
  | invoke _ ht_x _ _ _ => exact HasType.typed_var_capture_closed ht_x
  | subtyp _ _ _ hC _ _ => exact hC

theorem HasType.exp_is_closed
  (ht : HasType C Γ e T) :
  e.IsClosed := by
  induction ht <;>
    try
      (solve
        | assumption
        | constructor
        | (constructor <;> assumption)
        | (constructor <;> (first | assumption | constructor)))
  case read ih_x =>
    cases ih_x with
    | var hx_closed =>
      constructor
      exact hx_closed
  case write ih_x ih_y =>
    cases ih_x with
    | var hx_closed =>
      cases ih_y with
      | var hy_closed =>
        constructor
        · exact hx_closed
        · exact hy_closed
  case cond ih_var ih2 ih3 =>
    cases ih_var with
    | var hx_closed =>
      constructor
      · exact hx_closed
      · exact ih2
      · exact ih3
  case par ht1 ht2 _ ih1 ih2 =>
    -- `C1`/`C2` are closed because they are the use-sets of the well-typed branches.
    exact Exp.IsClosed.par (HasType.use_set_is_closed ht1)
      (HasType.use_set_is_closed ht2) ih1 ih2
  case abs T1 ih =>
    rename_i T1_closed
    constructor
    · exact CaptureSet.rename_closed_inv (HasType.use_set_is_closed T1)
    · exact T1_closed
    · exact ih
  case tabs S ih =>
    rename_i S_closed
    constructor
    · have h_use := HasType.use_set_is_closed S
      exact CaptureSet.rename_closed_inv h_use
    · exact S_closed
    · exact ih
  case cabs cb ih =>
    constructor
    · have h_use := HasType.use_set_is_closed cb
      exact CaptureSet.rename_closed_inv h_use
    · assumption
    · exact ih
  case consumer hT1 _hX ht_body ih =>
    constructor
    · have h_use := HasType.use_set_is_closed ht_body
      cases h_use with
      | union hleft _ =>
        cases hleft with
        | union hcs _ =>
          exact CaptureSet.rename_closed_inv (CaptureSet.rename_closed_inv hcs)
    · exact Ty.IsClosed.exi hT1
    · exact ih
  case wrap hΨ_closed ht_body ih =>
    constructor
    · have h_use := HasType.use_set_is_closed ht_body
      exact CaptureSet.rename_closed_inv h_use
    · exact hΨ_closed
    · exact Exp.rename_closed_inv ih
  case pack hCs_closed _ _ _ _ ih =>
    constructor
    · exact CaptureSet.unionAll_closed_inv hCs_closed
    · cases ih
      assumption
  case app =>
    rename_i ih_x ih_y
    constructor
    · cases ih_x; assumption
    · cases ih_y; assumption
  case tapp =>
    constructor
    · rename_i _ ih_x
      cases ih_x; assumption
    · assumption
  case capp =>
    constructor
    · rename_i _ ih_x
      cases ih_x; assumption
    · assumption
  case consumer_app _ _ _ _ _ ih_x ih_e =>
    constructor
    · cases ih_x; assumption
    · exact ih_e
  case unwrap _ _ ih_x =>
    cases ih_x with
    | var hx_closed =>
      exact Exp.IsClosed.unwrap hx_closed
  case alloc ih_x =>
    cases ih_x with
    | var hx_closed =>
      exact Exp.IsClosed.alloc hx_closed
  case drop ih_x =>
    cases ih_x with
    | var hx_closed =>
      exact Exp.IsClosed.drop hx_closed
  case invoke =>
    rename_i ih_x ih_y
    constructor
    · cases ih_x; assumption
    · cases ih_y; assumption
  case unpack_own =>
    -- The continuation IH is over `u.rename ((Rename.succ (k := .lock)).lift)`
    -- (the manufactured-lock slot), so peel that weakening back off before
    -- concluding closedness of the bare `u` under `Exp.IsClosed.unpack`.
    apply Exp.IsClosed.unpack
    · assumption
    · apply Exp.rename_closed_inv
      assumption

theorem HasType.type_is_closed
  (ht : HasType C Γ e E) :
  E.IsClosed := by
  induction ht <;>
    try (solve | assumption | constructor | grind only [Ty.IsClosed])
  case var hΓ_closed hlookup =>
    constructor
    have hT_closed := Ctx.lookup_var_gives_closed hΓ_closed hlookup
    exact Ty.refineCaptureSet_closed hT_closed CaptureSet.IsClosed.var_bound
  case reader hΓ hlk =>
    constructor
    cases Ctx.lookup_var_gives_closed hΓ hlk with | cell _ hT =>
    exact Ty.IsClosed.reader CaptureSet.IsClosed.var_bound hT
  case abs T1_closed ht_body ih =>
    constructor
    have h_use := HasType.use_set_is_closed ht_body
    exact Ty.IsClosed.arrow T1_closed
      (CaptureSet.rename_closed_inv h_use) ih
  case tabs S_closed ht_body ih =>
    constructor
    have h_use := HasType.use_set_is_closed ht_body
    exact Ty.IsClosed.poly S_closed
      (CaptureSet.rename_closed_inv h_use) ih
  case cabs ht_body ih =>
    constructor
    have h_use := HasType.use_set_is_closed ht_body
    rename_i hcb_closed _
    exact Ty.IsClosed.cpoly hcb_closed
      (CaptureSet.rename_closed_inv h_use) ih
  case consumer hT1 _hX ht_body ih =>
    constructor
    have h_use := HasType.use_set_is_closed ht_body
    cases h_use with
    | union hleft _ =>
      cases hleft with
      | union hcs _ =>
        exact Ty.IsClosed.consumer
          (Ty.IsClosed.exi hT1)
          (CaptureSet.rename_closed_inv (CaptureSet.rename_closed_inv hcs))
          (Ty.rename_closed_inv (Ty.rename_closed_inv ih))
  case wrap hΨ_closed ht_body ih =>
    constructor
    have h_use := HasType.use_set_is_closed ht_body
    exact Ty.IsClosed.modal
      (CaptureSet.rename_closed_inv h_use)
      hΨ_closed
      (Ty.rename_closed_inv ih)
  case pack hC ih =>
    constructor
    cases ih with | typ hT =>
    exact Ty.subst_closed_inv hT
  case app ht_x ht_y ih_x ih_y =>
    cases ih_x with | typ h =>
    cases h with | arrow _ _ hT2 =>
    have hy_closed := HasType.exp_is_closed ht_y
    cases hy_closed with | var hy =>
    exact Ty.is_closed_subst hT2 (Subst.openVar_is_closed hy)
  case tapp hS_closed ht_x ih =>
    cases ih with | typ h =>
    cases h with | poly _ _ hT =>
    exact Ty.is_closed_subst hT (Subst.openTVar_is_closed hS_closed)
  case capp hD_closed _ _ ih =>
    cases ih with | typ h =>
    cases h with | cpoly _ _ hT =>
    exact Ty.is_closed_subst hT (Subst.openCVar_is_closed hD_closed)
  case letin ih1 ih2 =>
    exact Ty.rename_closed_inv ih2
  case unpack ih1 ih2 =>
    exact Ty.rename_closed_inv (Ty.rename_closed_inv ih2)
  case unpack_own ih1 ih2 =>
    -- Result type carries one extra `.lock`-succ rename layer over `unpack`.
    exact Ty.rename_closed_inv (Ty.rename_closed_inv (Ty.rename_closed_inv ih2))
  case alloc ih =>
    cases ih with | typ hT =>
    exact Ty.IsClosed.exi (Ty.IsClosed.cell CaptureSet.IsClosed.cvar (Ty.rename_closed hT))
-- More context lookup properties

theorem Ctx.lookup_var_exists {Γ : Ctx s} {x : BVar s .var} :
  ∃ T, Γ.LookupVar x T := by
  cases x with
  | here =>
    cases Γ with
    | push Γ₀ b =>
      cases b with
      | var T₀ =>
        use T₀.rename Rename.succ
        apply Ctx.LookupVar.here
  | there x' =>
    cases Γ with
    | push Γ₀ b =>
      obtain ⟨T₀, h⟩ := lookup_var_exists (Γ := Γ₀) (x := x')
      use T₀.rename Rename.succ
      apply Ctx.LookupVar.there
      exact h

/-! ## Syntactic subset infrastructure

Inversion and transport lemmas for `CaptureSet.Subset`, tracing
capture-variable peak membership through the separation judgments. -/

/-- Inversion: a union on the left of `Subset` splits. -/
theorem CaptureSet.union_subset_inv {C1 C2 C : CaptureSet s}
    (h : (C1.union C2) ⊆ C) : C1 ⊆ C ∧ C2 ⊆ C := by
  generalize hu : C1.union C2 = U at h
  induction h with
  | refl =>
    subst hu
    exact ⟨.union_right_left .refl, .union_right_right .refl⟩
  | empty => cases hu
  | union_left h1 h2 =>
    cases hu
    exact ⟨h1, h2⟩
  | union_right_left _ ih =>
    obtain ⟨ha, hb⟩ := ih hu
    exact ⟨.union_right_left ha, .union_right_left hb⟩
  | union_right_right _ ih =>
    obtain ⟨ha, hb⟩ := ih hu
    exact ⟨.union_right_right ha, .union_right_right hb⟩

/-- `CaptureSet.Subset` is transitive. -/
theorem CaptureSet.Subset.trans {C1 C2 C3 : CaptureSet s}
    (h1 : C1 ⊆ C2) (h2 : C2 ⊆ C3) : C1 ⊆ C3 := by
  induction h1 generalizing C3 with
  | refl => exact h2
  | empty => exact .empty
  | union_left _ _ ih1 ih2 => exact .union_left (ih1 h2) (ih2 h2)
  | union_right_left _ ih => exact ih (CaptureSet.union_subset_inv h2).1
  | union_right_right _ ih => exact ih (CaptureSet.union_subset_inv h2).2

/-- Inversion: a `cvar` element of a union is in one of the components. -/
theorem CaptureSet.cvar_subset_union_inv {a : Access} {c : BVar s .cvar}
    {C1 C2 : CaptureSet s}
    (h : (CaptureSet.cvar a c) ⊆ C1.union C2) :
    (CaptureSet.cvar a c) ⊆ C1 ∨ (CaptureSet.cvar a c) ⊆ C2 := by
  cases h with
  | union_right_left h => exact .inl h
  | union_right_right h => exact .inr h

/-- Inversion: a `cvar` element of a singleton `cvar` set matches it. -/
theorem CaptureSet.cvar_subset_cvar_inv {a a' : Access} {c c' : BVar s .cvar}
    (h : (CaptureSet.cvar a c) ⊆ (CaptureSet.cvar a' c')) :
    a = a' ∧ c = c' := by
  cases h with
  | refl => exact ⟨rfl, rfl⟩

theorem CaptureSet.cvar_not_subset_empty {a : Access} {c : BVar s .cvar}
    (h : (CaptureSet.cvar a c) ⊆ (.empty : CaptureSet s)) : False := by
  cases h

theorem CaptureSet.cvar_not_subset_var {a m : Access} {c : BVar s .cvar} {x : Var .var s}
    (h : (CaptureSet.cvar a c) ⊆ (CaptureSet.var m x)) : False := by
  cases h

/-- Inversion for `consumed`: an atom of the consumed part of a capture set is
a `.drop`-mode atom of the set itself. -/
theorem CaptureSet.cvar_subset_consumed_inv {a : Access} {c : BVar s .cvar}
    {C : CaptureSet s}
    (h : (CaptureSet.cvar a c) ⊆ C.consumed) : (CaptureSet.cvar .drop c) ⊆ C := by
  induction C with
  | empty => exact absurd h CaptureSet.cvar_not_subset_empty
  | union C1 C2 ih1 ih2 =>
    cases CaptureSet.cvar_subset_union_inv h with
    | inl h' => exact .union_right_left (ih1 h')
    | inr h' => exact .union_right_right (ih2 h')
  | cvar m c' =>
    cases m with
    | M _ => exact absurd h CaptureSet.cvar_not_subset_empty
    | drop =>
      obtain ⟨_, rfl⟩ := CaptureSet.cvar_subset_cvar_inv h
      exact .refl
  | var _ _ => exact absurd h CaptureSet.cvar_not_subset_empty

/-- Raw-constructor version of `peaks_union`. -/
theorem CaptureSet.peaks_union_raw (Γ : Ctx s) (cs1 cs2 : CaptureSet s) :
    CaptureSet.peaks Γ (cs1.union cs2)
      = (CaptureSet.peaks Γ cs1).union (CaptureSet.peaks Γ cs2) := by
  conv_lhs => unfold CaptureSet.peaks
  rfl

theorem CaptureSet.peaks_empty (Γ : Ctx s) :
    CaptureSet.peaks Γ (.empty : CaptureSet s) = .empty := by
  unfold CaptureSet.peaks
  rfl

/-- A `cvar` element of the peaks of a union is in one of the components'
peaks. Stated through defeq so it applies to both `∪`- and `.union`-shaped
goals. -/
theorem CaptureSet.cvar_subset_peaks_union_inv {Γ : Ctx s} {a : Access}
    {c : BVar s .cvar} {A B : CaptureSet s}
    (h : (CaptureSet.cvar a c) ⊆ (A.union B).peaks Γ) :
    (CaptureSet.cvar a c) ⊆ A.peaks Γ ∨ (CaptureSet.cvar a c) ⊆ B.peaks Γ := by
  rw [CaptureSet.peaks_union_raw] at h
  exact CaptureSet.cvar_subset_union_inv h

theorem CaptureSet.cvar_not_subset_peaks_empty {Γ : Ctx s} {a : Access}
    {c : BVar s .cvar}
    (h : (CaptureSet.cvar a c) ⊆ (CaptureSet.empty : CaptureSet s).peaks Γ) : False := by
  rw [CaptureSet.peaks_empty] at h
  exact CaptureSet.cvar_not_subset_empty h

/-- `peaks` is monotone with respect to the syntactic subset relation. -/
theorem CaptureSet.peaks_subset_monotone {Γ : Ctx s} {C1 C2 : CaptureSet s}
    (h : C1 ⊆ C2) : C1.peaks Γ ⊆ C2.peaks Γ := by
  induction h with
  | refl => exact .refl
  | empty =>
    rw [CaptureSet.peaks_empty]
    exact .empty
  | union_left _ _ ih1 ih2 =>
    rw [CaptureSet.peaks_union_raw]
    exact .union_left ih1 ih2
  | union_right_left _ ih =>
    rw [CaptureSet.peaks_union_raw]
    exact .union_right_left ih
  | union_right_right _ ih =>
    rw [CaptureSet.peaks_union_raw]
    exact .union_right_right ih

/-- Inversion: a `cvar` element of `C.applyDrop` is at `.drop` access and stems
from a `cvar` element of `C` at some access. -/
theorem CaptureSet.cvar_subset_applyDrop_inv {a : Access} {c : BVar s .cvar}
    {C : CaptureSet s}
    (h : (CaptureSet.cvar a c) ⊆ C.applyDrop) :
    a = .drop ∧ ∃ a0, (CaptureSet.cvar a0 c) ⊆ C := by
  induction C with
  | empty => exact absurd h CaptureSet.cvar_not_subset_empty
  | union C1 C2 ih1 ih2 =>
    cases CaptureSet.cvar_subset_union_inv h with
    | inl h1 =>
      obtain ⟨ha, a0, hsub⟩ := ih1 h1
      exact ⟨ha, a0, .union_right_left hsub⟩
    | inr h2 =>
      obtain ⟨ha, a0, hsub⟩ := ih2 h2
      exact ⟨ha, a0, .union_right_right hsub⟩
  | var a' x => exact absurd h CaptureSet.cvar_not_subset_var
  | cvar a' c' =>
    obtain ⟨ha, hc⟩ := CaptureSet.cvar_subset_cvar_inv h
    subst hc
    exact ⟨ha, a', .refl⟩

/-- Inversion: a `cvar` element of `C.applyRO` stems from a `cvar` element of
`C` whose read-only image is the given access. -/
theorem CaptureSet.cvar_subset_applyRO_inv {a : Access} {c : BVar s .cvar}
    {C : CaptureSet s}
    (h : (CaptureSet.cvar a c) ⊆ C.applyRO) :
    ∃ a0, a = a0.applyRO ∧ (CaptureSet.cvar a0 c) ⊆ C := by
  induction C with
  | empty => exact absurd h CaptureSet.cvar_not_subset_empty
  | union C1 C2 ih1 ih2 =>
    cases CaptureSet.cvar_subset_union_inv h with
    | inl h1 =>
      obtain ⟨a0, ha, hsub⟩ := ih1 h1
      exact ⟨a0, ha, .union_right_left hsub⟩
    | inr h2 =>
      obtain ⟨a0, ha, hsub⟩ := ih2 h2
      exact ⟨a0, ha, .union_right_right hsub⟩
  | var a' x => exact absurd h CaptureSet.cvar_not_subset_var
  | cvar a' c' =>
    obtain ⟨ha, hc⟩ := CaptureSet.cvar_subset_cvar_inv h
    subst hc
    exact ⟨a', ha, .refl⟩

/-- Inversion: a `cvar` element of `C.applyMut m` stems from a `cvar` element
of `C` at some access. -/
theorem CaptureSet.cvar_subset_applyMut_inv {a : Access} {c : BVar s .cvar}
    {C : CaptureSet s} {m : Mutability}
    (h : (CaptureSet.cvar a c) ⊆ C.applyMut m) :
    ∃ a0, (CaptureSet.cvar a0 c) ⊆ C := by
  cases m with
  | epsilon => exact ⟨a, h⟩
  | ro =>
    obtain ⟨a0, _, hsub⟩ := CaptureSet.cvar_subset_applyRO_inv h
    exact ⟨a0, hsub⟩

/-- Inversion: a `cvar` element of `C.applyAccess a'` stems from a `cvar`
element of `C` at some access. -/
theorem CaptureSet.cvar_subset_applyAccess_inv {a a' : Access} {c : BVar s .cvar}
    {C : CaptureSet s}
    (h : (CaptureSet.cvar a c) ⊆ C.applyAccess a') :
    ∃ a0, (CaptureSet.cvar a0 c) ⊆ C := by
  cases a' with
  | M m => exact CaptureSet.cvar_subset_applyMut_inv h
  | drop =>
    obtain ⟨_, a0, hsub⟩ := CaptureSet.cvar_subset_applyDrop_inv h
    exact ⟨a0, hsub⟩

/-- Forward transport: a `cvar` element survives `applyRO` (at its read-only
image). -/
theorem CaptureSet.cvar_subset_applyRO_fwd {a : Access} {c : BVar s .cvar}
    {C : CaptureSet s}
    (h : (CaptureSet.cvar a c) ⊆ C) :
    (CaptureSet.cvar a.applyRO c) ⊆ C.applyRO := by
  generalize he : CaptureSet.cvar a c = E at h
  induction h with
  | refl => subst he; exact .refl
  | empty => cases he
  | union_left _ _ _ _ => cases he
  | union_right_left _ ih => exact .union_right_left (ih he)
  | union_right_right _ ih => exact .union_right_right (ih he)

/-- Forward transport: a `cvar` element survives `applyDrop` (at `.drop`). -/
theorem CaptureSet.cvar_subset_applyDrop_fwd {a : Access} {c : BVar s .cvar}
    {C : CaptureSet s}
    (h : (CaptureSet.cvar a c) ⊆ C) :
    (CaptureSet.cvar .drop c) ⊆ C.applyDrop := by
  generalize he : CaptureSet.cvar a c = E at h
  induction h with
  | refl => subst he; exact .refl
  | empty => cases he
  | union_left _ _ _ _ => cases he
  | union_right_left _ ih => exact .union_right_left (ih he)
  | union_right_right _ ih => exact .union_right_right (ih he)

/-- Forward transport: a `cvar` element survives `applyMut` at some access. -/
theorem CaptureSet.cvar_subset_applyMut_fwd {a : Access} {c : BVar s .cvar}
    {C : CaptureSet s} (m : Mutability)
    (h : (CaptureSet.cvar a c) ⊆ C) :
    ∃ a', (CaptureSet.cvar a' c) ⊆ C.applyMut m := by
  cases m with
  | epsilon => exact ⟨a, h⟩
  | ro => exact ⟨a.applyRO, CaptureSet.cvar_subset_applyRO_fwd h⟩

/-- A peaks-only capture set is a fixed point of `peaks`. -/
theorem CaptureSet.PeaksOnly.peaks_fixed {Γ : Ctx s} {P : CaptureSet s}
    (hP : P.PeaksOnly) : P.peaks Γ = P := by
  induction hP with
  | empty => exact CaptureSet.peaks_empty Γ
  | union _ _ ih1 ih2 =>
    rename_i C1 C2 _ _
    show CaptureSet.peaks Γ (C1.union C2) = _
    rw [CaptureSet.peaks_union_raw, ih1, ih2]
  | cvar => rw [CaptureSet.peaks]

/-- `TwoDistinctDroppable` is symmetric. -/
theorem Ctx.TwoDistinctDroppable.symm {Γ : Ctx s} {c1 c2 : BVar s .cvar}
    (h : Γ.TwoDistinctDroppable c1 c2) : Γ.TwoDistinctDroppable c2 c1 :=
  ⟨h.2.1, h.1, fun he => h.2.2 he.symm⟩

/-- `CoveredBy` transports capture-variable atoms: every capture-variable
atom of the covered set occurs, at some access, in the covering set (peaks
cannot be hidden across budget shrinking). -/
theorem CaptureSet.CoveredBy.cvar_subset {A B : CaptureSet s}
    {a : Access} {c : BVar s .cvar}
    (hcov : A.CoveredBy B)
    (h : (CaptureSet.cvar a c) ⊆ A) :
    ∃ a', (CaptureSet.cvar a' c) ⊆ B := by
  induction hcov generalizing a with
  | refl hm =>
    obtain ⟨a0, h0⟩ := CaptureSet.cvar_subset_applyMut_inv h
    exact CaptureSet.cvar_subset_applyMut_fwd _ h0
  | empty => exact absurd h CaptureSet.cvar_not_subset_empty
  | union_left _ _ ih1 ih2 =>
    cases CaptureSet.cvar_subset_union_inv h with
    | inl h' => exact ih1 h'
    | inr h' => exact ih2 h'
  | union_right_left _ ih =>
    obtain ⟨a', h'⟩ := ih h
    exact ⟨a', .union_right_left h'⟩
  | union_right_right _ ih =>
    obtain ⟨a', h'⟩ := ih h
    exact ⟨a', .union_right_right h'⟩

/-- `CoveredBy` transports `.drop`-mode capture-variable atoms exactly:
mutability application leaves `.drop` untouched (`Access.applyRO .drop =
.drop`), so a consuming atom of the covered set is a consuming atom of the
covering set. -/
theorem CaptureSet.CoveredBy.cvar_drop_subset {A B : CaptureSet s}
    {c : BVar s .cvar}
    (hcov : A.CoveredBy B)
    (h : (CaptureSet.cvar .drop c) ⊆ A) :
    (CaptureSet.cvar .drop c) ⊆ B := by
  induction hcov with
  | refl hm =>
    rename_i C m1 m2
    have h0 : (CaptureSet.cvar .drop c) ⊆ C := by
      cases m1 with
      | epsilon => simpa only [CaptureSet.applyMut_epsilon] using h
      | ro =>
        simp only [CaptureSet.applyMut_ro] at h
        obtain ⟨a0, heq, h0⟩ := CaptureSet.cvar_subset_applyRO_inv h
        cases a0 with
        | M m => cases heq
        | drop => exact h0
    cases m2 with
    | epsilon => simpa only [CaptureSet.applyMut_epsilon] using h0
    | ro =>
      simp only [CaptureSet.applyMut_ro]
      have := CaptureSet.cvar_subset_applyRO_fwd (a := .drop) h0
      simpa only [Access.applyRO] using this
  | empty => exact absurd h CaptureSet.cvar_not_subset_empty
  | union_left _ _ ih1 ih2 =>
    cases CaptureSet.cvar_subset_union_inv h with
    | inl h' => exact ih1 h'
    | inr h' => exact ih2 h'
  | union_right_left _ ih =>
    exact .union_right_left (ih h)
  | union_right_right _ ih =>
    exact .union_right_right (ih h)

/-! ## Droppable peak monotonicity along `Subcapt`

A droppable capture variable's peak occurrence is preserved when a capture set
is widened by subcapture: the only peak-eliminating rule is `sc_cvar`, which
is restricted to `.access_only` capture variables. -/

theorem Subcapt.droppable_peak_monotone {Γ : Ctx s} {C1 C2 : CaptureSet s}
    {c : BVar s .cvar} {a : Access}
    (hsub : Subcapt Γ C1 C2)
    (hauth : Γ.lookup_authority c = .can_drop)
    (hpeak : (CaptureSet.cvar a c) ⊆ C1.peaks Γ) :
    ∃ a', (CaptureSet.cvar a' c) ⊆ C2.peaks Γ := by
  induction hsub generalizing a with
  | sc_trans _ _ ih1 ih2 =>
    obtain ⟨a', h'⟩ := ih1 hauth hpeak
    exact ih2 hauth h'
  | sc_elem hss =>
    exact ⟨a, CaptureSet.Subset.trans hpeak (CaptureSet.peaks_subset_monotone hss)⟩
  | sc_mode hle =>
    rw [CaptureSet.peaks_applyMut_comm] at hpeak ⊢
    obtain ⟨a0, hsub0⟩ := CaptureSet.cvar_subset_applyMut_inv hpeak
    exact CaptureSet.cvar_subset_applyMut_fwd _ hsub0
  | sc_union _ _ ih1 ih2 =>
    cases CaptureSet.cvar_subset_peaks_union_inv hpeak with
    | inl h => exact ih1 hauth h
    | inr h => exact ih2 hauth h
  | sc_var hlookup =>
    rename_i x T
    rw [CaptureSet.var_peaks hlookup] at hpeak
    simp only [CaptureSet.applyAccess_M, CaptureSet.applyMut_epsilon] at hpeak
    exact ⟨a, hpeak⟩
  | sc_cvar hlookup =>
    rw [CaptureSet.peaks] at hpeak
    obtain ⟨_, hc⟩ := CaptureSet.cvar_subset_cvar_inv hpeak
    subst hc
    rw [← hlookup.eq_authority] at hauth
    cases hauth
  | sc_ro =>
    rw [CaptureSet.peaks_applyRO_comm] at hpeak
    obtain ⟨a0, _, hsub0⟩ := CaptureSet.cvar_subset_applyRO_inv hpeak
    exact ⟨a0, hsub0⟩
  | sc_ro_mono _ ih =>
    rw [CaptureSet.peaks_applyRO_comm] at hpeak ⊢
    obtain ⟨a0, _, hsub0⟩ := CaptureSet.cvar_subset_applyRO_inv hpeak
    obtain ⟨a', h'⟩ := ih hauth hsub0
    exact ⟨a'.applyRO, CaptureSet.cvar_subset_applyRO_fwd h'⟩
  | sc_drop_mono _ ih =>
    simp only [CaptureSet.applyAccess_drop] at hpeak ⊢
    rw [CaptureSet.peaks_applyDrop_comm] at hpeak ⊢
    obtain ⟨_, a0, hsub0⟩ := CaptureSet.cvar_subset_applyDrop_inv hpeak
    obtain ⟨a', h'⟩ := ih hauth hsub0
    exact ⟨.drop, CaptureSet.cvar_subset_applyDrop_fwd h'⟩

/-- **Left-monotonicity of `SepCheck` along `Subcapt`** — separation is preserved
    when the left side shrinks to a subcapture.  This is now the primitive
    `SepCheck.sep_mono` rule (it is NOT admissible from the other constructors: the
    peak-reducing `Subcapt` steps reduce to extracting separation of a sub-part of
    a `sep_lock` item, which a lock cannot witness).  Kept as a named lemma. -/
theorem SepCheck.left_mono
  (hsep : SepCheck Γ C1 C2) (hsub : Subcapt Γ C1' C1) :
  SepCheck Γ C1' C2 := SepCheck.sep_mono hsep hsub

end CoreCapybara
