import Semantic.CoreCapybara.TypeSystem
import Semantic.CoreCapybara.Capybara
namespace CoreCapybara

/-!
# Support toolkit for the application-compilation case

This module collects self-contained lemmas — about the *target* core calculus
and the *source* Capybara calculus in isolation, never the compiler itself —
that the application case of term compilation relies on.

* **Part 1** develops a small `Ctx.AllAlive` theory on the target side: a
  context in which no capture variable has been `.killed`.  Every capture set is
  `accessible` in such a context.
* **Part 2** shows that a `letin` whose head is access-only is *kill-free*: the
  sequential composition is discharged by `SeqComp.seq_access_only` and the body
  context is left untouched (no peaks are consumed).
* **Part 3** inverts source variable typing at a `.typ`-sorted type.
-/

/-! ## Part 1: `Ctx.AllAlive` (target side) -/

/-- Every capture variable in the context is alive (not `.killed`). -/
def Ctx.AllAlive (Γ : Ctx s) : Prop :=
  ∀ c : BVar s .cvar, Γ.lookup_authority c ≠ .killed

theorem Ctx.AllAlive.push_var {Γ : Ctx s} (h : Γ.AllAlive) {T : Ty .capt s} :
    (Γ,x:T).AllAlive := by
  intro c
  cases c with
  | there c' => exact h c'

theorem Ctx.AllAlive.push_tvar {Γ : Ctx s} (h : Γ.AllAlive) {S : PureTy s} :
    (Γ,X<:S).AllAlive := by
  intro c
  cases c with
  | there c' => exact h c'

theorem Ctx.AllAlive.push_lock {Γ : Ctx s} (h : Γ.AllAlive) {Ψ : ModalCtx s} :
    (Γ.push_lock Ψ).AllAlive := by
  intro c
  cases c with
  | there c' => exact h c'

theorem Ctx.AllAlive.push_cvar {Γ : Ctx s} (h : Γ.AllAlive) {a : Authority}
    {cb : CaptureBound s} (ha : a ≠ .killed) :
    (Γ,C[a]<:cb).AllAlive := by
  intro c
  cases c with
  | here => exact ha
  | there c' => exact h c'

/-- Any capture set is accessible in an all-alive context. -/
theorem CaptureSet.accessible_of_allAlive {Γ : Ctx s} (h : Γ.AllAlive)
    (C : CaptureSet s) : C.accessible Γ :=
  fun _ c _ => h c

/-! ## Part 2: kill-free `letin` (target side) -/

/-- A peaks-only capture set with no `.drop`-mode peak has empty `consumed`. -/
theorem CaptureSet.consumed_isEmpty_of_peaksOnly {cs : CaptureSet s}
    (hp : cs.PeaksOnly) :
    (∀ c : BVar s .cvar, ¬ (CaptureSet.cvar .drop c ⊆ cs)) → cs.consumed.IsEmpty := by
  induction hp with
  | empty => intro _; exact IsEmpty.empty
  | union _ _ ih1 ih2 =>
    intro hno
    simp only [CaptureSet.consumed]
    refine IsEmpty.union (ih1 ?_) (ih2 ?_)
    · intro c hc; exact hno c (CaptureSet.Subset.union_right_left hc)
    · intro c hc; exact hno c (CaptureSet.Subset.union_right_right hc)
  | cvar =>
    rename_i m c
    intro hno
    cases m with
    | M _ => exact IsEmpty.empty
    | drop => exact absurd CaptureSet.Subset.refl (hno c)

/-- The consumed (drop-mode) peaks of an access-only capture set are empty. -/
theorem CaptureSet.consumed_isEmpty_of_accessOnly {Γ : Ctx s} {C : CaptureSet s}
    (h : C.AccessOnly Γ) : ((C.peakset Γ).consumed).cs.IsEmpty :=
  CaptureSet.consumed_isEmpty_of_peaksOnly (C.peakset Γ).h h

/-- Killing an empty peak set is a no-op. -/
theorem Ctx.kill_peaks_cs_isEmpty {Γ : Ctx s} {cs : CaptureSet s}
    (h : cs.IsEmpty) : Γ.kill_peaks_cs cs = Γ := by
  induction h with
  | empty => rfl
  | union _ _ ih1 ih2 => simp only [Ctx.kill_peaks_cs, ih1, ih2]

/-- Killing the consumed peaks of an access-only capture set is a no-op. -/
theorem Ctx.kill_peaks_accessOnly {Γ : Ctx s} {C : CaptureSet s}
    (h : C.AccessOnly Γ) :
    Γ.kill_peaks ((C.peakset Γ).consumed) = Γ := by
  unfold Ctx.kill_peaks
  exact Ctx.kill_peaks_cs_isEmpty (CaptureSet.consumed_isEmpty_of_accessOnly h)

/-- `letin` with an access-only head: sequential composition is free and the
    body context is untouched (no peaks are consumed). -/
theorem HasType.letin_ao {Γ : Ctx s} {C1 C2 : CaptureSet s} {e1 : Exp s}
    {e2 : Exp (s,x)} {T : Ty .capt s} {U : Ty .exi s}
    (hcl : C1.IsClosed) (hao : C1.AccessOnly Γ)
    (h1 : HasType C1 Γ e1 (.typ T))
    (h2 : HasType (C2.rename Rename.succ) (Γ,x:T) e2 (U.rename Rename.succ)) :
    HasType (C1 ∪ C2) Γ (.letin e1 e2) U := by
  refine HasType.letin (SeqComp.seq_access_only hcl hao) h1 ?_
  rw [Ctx.kill_peaks_accessOnly hao]
  exact h2

/-! ## Part 3: source variable-typing inversion (source side)

The needed source-calculus closedness facts (`rename`- and `refineCaptureSet`-
closure, and lookup in a closed context) are re-proven here as `private`
helpers, so this file depends only on the source calculus, never on the
compiler where they otherwise live. -/

/-- Renaming preserves closedness of a source capture bound. -/
private theorem CapyCaptureBound.isClosed_rename {cb : CapyCaptureBound s1}
    (h : cb.IsClosed) {f : Rename s1 s2} : (cb.rename f).IsClosed := by
  cases h with
  | unbound => exact .unbound
  | bound hcs => exact .bound (CapyCaptureSet.rename_isClosed hcs)

/-- Renaming preserves closedness of a source type. -/
private theorem CapyTy.isClosed_rename {sort : CapyTySort} {s1 : Sig} {T : CapyTy sort s1}
    (h : T.IsClosed) : ∀ {s2 : Sig} (f : Rename s1 s2), (T.rename f).IsClosed := by
  induction h with
  | top => intro _ _; exact .top
  | tvar => intro _ _; exact .tvar
  | arrow _ hcs _ ih1 ih2 =>
    intro _ f; exact .arrow (ih1 f.lift) (CapyCaptureSet.rename_isClosed hcs) (ih2 f.lift)
  | poly _ hcs _ ih1 ih2 =>
    intro _ f; exact .poly (ih1 f) (CapyCaptureSet.rename_isClosed hcs) (ih2 f.lift)
  | cpoly hcb hcs _ ih =>
    intro _ f
    exact .cpoly (CapyCaptureBound.isClosed_rename hcb) (CapyCaptureSet.rename_isClosed hcs)
      (ih f.lift)
  | unit => intro _ _; exact .unit
  | cap hcs => intro _ _; exact .cap (CapyCaptureSet.rename_isClosed hcs)
  | bool => intro _ _; exact .bool
  | cell hcs => intro _ _; exact .cell (CapyCaptureSet.rename_isClosed hcs)
  | exi _ ih => intro _ f; exact .exi (ih f.lift)
  | typ _ ih => intro _ f; exact .typ (ih f)

/-- A term variable looked up in a closed source context has a closed type. -/
private theorem CapyCtx.lookupVar_closed {Γ : CapyCtx s} {x : BVar s .var} {T : CapyTy .capt s}
    (h : Γ.LookupVar x T) : Γ.IsClosed → T.IsClosed := by
  induction h with
  | here =>
    intro hΓ; cases hΓ with | push _ hb => cases hb with
    | var hT => exact CapyTy.isClosed_rename hT _
  | there _ ih =>
    intro hΓ; cases hΓ with | push hΓ' _ => exact CapyTy.isClosed_rename (ih hΓ') _

/-- Refining the capture set of a closed type with a closed capture set keeps it closed. -/
private theorem CapyTy.isClosed_refineCaptureSet {T : CapyTy .capt s} {cs : CapyCaptureSet s}
    (h : T.IsClosed) (hcs : cs.IsClosed) : (T.refineCaptureSet cs).IsClosed := by
  cases h with
  | top => exact .top
  | tvar => exact .tvar
  | arrow h1 _ h2 => exact .arrow h1 hcs h2
  | poly h1 _ h2 => exact .poly h1 hcs h2
  | cpoly hcb _ hT => exact .cpoly hcb hcs hT
  | unit => exact .unit
  | cap _ => exact .cap hcs
  | bool => exact .bool
  | cell _ => exact .cell hcs

/-- Discriminates the existential (`.exi`) head of a source (existential-sorted) type. -/
private def CapyTy.isExiHead : CapyTy sort s → Bool
  | .exi _ => true
  | _ => false

private theorem CapyTy.isExiHead_capt (T : CapyTy .capt s) : T.isExiHead = false := by
  cases T <;> rfl

/-- Source subtyping preserves the existential-head discriminant. -/
private theorem CapySubtyp.isExiHead_eq {Γ : CapyCtx s} {sort : CapyTySort}
    {X Y : CapyTy sort s} (h : CapySubtyp Γ X Y) : X.isExiHead = Y.isExiHead := by
  induction h with
  | trans _ _ _ ih1 ih2 => exact ih1.trans ih2
  | _ => first | rfl | simp only [CapyTy.isExiHead_capt]

/-- Source subtyping out of an existential type lands in an existential type. -/
private theorem CapySubtyp.exi_dest {Γ : CapyCtx s} {A : CapyTy .capt (s,C)}
    {E : CapyTy .exi s} (h : CapySubtyp Γ (.exi A) E) : ∃ A', E = .exi A' := by
  cases E with
  | exi A' => exact ⟨A', rfl⟩
  | typ B =>
    have he := h.isExiHead_eq
    simp [CapyTy.isExiHead] at he

/-- General inversion of source variable typing at any existential type.  Every
    such derivation traces back to `var`, `readonly`, or `fresh`; the first two
    yield a self-refined declared type subtyping the assigned type (with the
    assigned type closed), the last only that the assigned type is an existential
    (`.exi`).  The three-way form is what makes the `subtyp` case go through:
    `var`/`readonly` are chained via `CapySubtyp.trans` (using the threaded
    closedness), `fresh` is propagated via `CapySubtyp.exi_dest`. -/
private theorem CapyHasType.var_inversion_gen {s : Sig} {Γ : CapyCtx s}
    {C : CapyCaptureSet s} {v : Var .var s} {E : CapyTy .exi s}
    (h : CapyHasType C Γ (.var v) E) :
    ∃ x : BVar s .var, v = .bound x ∧
      ( (∃ T0 : CapyTy .capt s, Γ.LookupVar x T0 ∧ E.IsClosed ∧
           CapySubtyp Γ (.typ (T0.refineCaptureSet (.var (.M .epsilon) (.bound x)))) E)
      ∨ (∃ Cc : CapyCaptureSet s, Γ.LookupVar x (.cell Cc .epsilon) ∧ E.IsClosed ∧
           CapySubtyp Γ (.typ (.cell (.var (.M .ro) (.bound x)) .ro)) E)
      ∨ (∃ A : CapyTy .capt (s,C), E = .exi A) ) := by
  generalize he : CapyExp.var v = e0 at h
  induction h with
  | var hcl hlk =>
    injection he with _ hv; subst hv
    refine ⟨_, rfl, Or.inl ⟨_, hlk, ?_, CapySubtyp.refl⟩⟩
    exact CapyTy.IsClosed.typ (CapyTy.isClosed_refineCaptureSet
      (CapyCtx.lookupVar_closed hlk hcl) CapyCaptureSet.IsClosed.var_bound)
  | readonly hcl hlk =>
    injection he with _ hv; subst hv
    refine ⟨_, rfl, Or.inr (Or.inl ⟨_, hlk, ?_, CapySubtyp.refl⟩)⟩
    exact CapyTy.IsClosed.typ (CapyTy.IsClosed.cell CapyCaptureSet.IsClosed.var_bound)
  | fresh hDcl hao hlk hdrop hpb hnp =>
    injection he with _ hv; subst hv
    exact ⟨_, rfl, Or.inr (Or.inr ⟨_, rfl⟩)⟩
  | subtyp hd hsc hsub hc2 he2 ih =>
    obtain ⟨x, hv, hdisj⟩ := ih he
    refine ⟨x, hv, ?_⟩
    rcases hdisj with ⟨T0, hlk, hE1cl, hs⟩ | ⟨Cc, hlk, hE1cl, hs⟩ | ⟨A, hEeq⟩
    · exact Or.inl ⟨T0, hlk, he2, CapySubtyp.trans hE1cl hs hsub⟩
    · exact Or.inr (Or.inl ⟨Cc, hlk, he2, CapySubtyp.trans hE1cl hs hsub⟩)
    · subst hEeq
      obtain ⟨A', hA'⟩ := hsub.exi_dest
      exact Or.inr (Or.inr ⟨A', hA'⟩)
  | _ => simp at he

/-- A variable typed at a `.typ`-sorted type is a bound context variable whose
    declared type (self-refined) subtypes the assigned type, and the assigned
    type is closed.  Because the source calculus has no cell/reader subtyping
    rule, the read-only-view (`readonly`) origin cannot be folded into the `var`
    origin, so the subtyping component is a two-way disjunction.  The `fresh`
    (existential) origin is impossible at a `.typ` type and is discharged. -/
theorem CapyHasType.var_typ_inversion {s : Sig} {Γ : CapyCtx s}
    {C : CapyCaptureSet s} {v : Var .var s} {T : CapyTy .capt s}
    (h : CapyHasType C Γ (.var v) (.typ T)) :
    ∃ x : BVar s .var, v = .bound x ∧
      ( (∃ T0 : CapyTy .capt s, Γ.LookupVar x T0 ∧
           CapySubtyp Γ (.typ (T0.refineCaptureSet (.var (.M .epsilon) (.bound x)))) (.typ T))
      ∨ (∃ Cc : CapyCaptureSet s, Γ.LookupVar x (.cell Cc .epsilon) ∧
           CapySubtyp Γ (.typ (.cell (.var (.M .ro) (.bound x)) .ro)) (.typ T)) ) ∧
      (CapyTy.typ T).IsClosed := by
  obtain ⟨x, hv, hdisj⟩ := h.var_inversion_gen
  refine ⟨x, hv, ?_⟩
  rcases hdisj with ⟨T0, hlk, hcl, hs⟩ | ⟨Cc, hlk, hcl, hs⟩ | ⟨A, hEeq⟩
  · exact ⟨Or.inl ⟨T0, hlk, hs⟩, hcl⟩
  · exact ⟨Or.inr ⟨Cc, hlk, hs⟩, hcl⟩
  · simp at hEeq

/-- `.cell`/`.top` head discriminant on capturing types. -/
private def CapyTy.cellTopHead : CapyTy sort s → Bool
  | .cell _ _ => true
  | .top => true
  | _ => false

/-- `CapySubtyp` from a `.cell`/`.top`-headed capturing type reaches only
    `.cell`/`.top`-headed capturing types: `CapySubtyp` has no cell/arrow/poly
    congruence descending into a cell, so the only steps available from a cell
    head are `refl` (stays a cell) and `top` (goes to `.top`), and from `.top`
    only `.top`. -/
private theorem CapySubtyp.cellTopHead_preserved {s : Sig} {Γ : CapyCtx s}
    {sort : CapyTySort} {A B : CapyTy sort s} (h : CapySubtyp Γ A B) :
    A.cellTopHead = true → B.cellTopHead = true := by
  induction h with
  | refl => exact id
  | trans _ _ _ ih1 ih2 => exact fun ha => ih2 (ih1 ha)
  | top _ => exact fun _ => rfl
  | _ => intro ha; simp [CapyTy.cellTopHead] at ha

/-- The `.typ`-wrapped `.cell`/`.top` head discriminant. -/
private def CapyTy.typCellTopHead : CapyTy sort s → Bool
  | .typ T => T.cellTopHead
  | _ => false

private theorem CapyTy.typCellTopHead_capt (T : CapyTy .capt s) :
    T.typCellTopHead = false := by cases T <;> rfl

/-- The `.typ`-level analogue of `cellTopHead_preserved`: `CapySubtyp` from a
    `.typ (.cell _)`/`.typ .top` type stays within those two shapes. -/
private theorem CapySubtyp.typCellTopHead_preserved {s : Sig} {Γ : CapyCtx s}
    {sort : CapyTySort} {A B : CapyTy sort s} (h : CapySubtyp Γ A B) :
    A.typCellTopHead = true → B.typCellTopHead = true := by
  induction h with
  | refl => exact id
  | trans _ _ _ ih1 ih2 => exact fun ha => ih2 (ih1 ha)
  | typ hbody _ =>
    intro ha
    simp only [CapyTy.typCellTopHead] at ha ⊢
    exact hbody.cellTopHead_preserved ha
  | top _ => intro ha; rw [CapyTy.typCellTopHead_capt] at ha; simp at ha
  | _ => intro ha; simp [CapyTy.typCellTopHead] at ha

/-- A cell (of any mutability) never subtypes an arrow: `CapySubtyp` chains
    starting from a `.cell` head reach only `.cell`/`.top` heads.  Refutes the
    readonly origin of `var_typ_inversion` when the assigned type is an arrow
    (the compiled `app` case's FUNCTION subject). -/
theorem CapySubtyp.cell_not_arrow {s : Sig} {Γ : CapyCtx s} {C : CapyCaptureSet s}
    {m : Mutability} {T1 : CapyTy .capt (s,C)} {cs : CapyCaptureSet s}
    {T2 : CapyTy .exi (s,x)}
    (h : CapySubtyp Γ (.typ (.cell C m)) (.typ (.arrow T1 cs T2))) : False := by
  have hb := h.typCellTopHead_preserved (by rfl)
  simp [CapyTy.typCellTopHead, CapyTy.cellTopHead] at hb

end CoreCapybara
