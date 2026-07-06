import Semantic.CoreCapybara.TypeSystem.BasicProps

/-!
# Kill-weakening via unconditional cvar-erasure

The paper's Lemma [Kill weakening] (`lem:tr:kill`, ledger H2): typing survives the
kill operation `Γ ⊖ C₁` when the killed capture variables are avoided.

The mechanization proceeds through an **unconditional erasure theorem**: erase every
atom mentioning a killed variable from *all* components at once (use set, term
annotations, result type, and every context payload) and kill the context.  In erased
form there is no side hypothesis, so every induction closes — gratuitous intermediates
erase themselves, and authority-consulting leaves become trivial at killed variables.
The paper statement (`HasType.kill_weakening`) is then the identity corollary: if
erasure fixes the four visible components, killing preserves typing.

See `notes/kill-weakening-design.md` for the full design.
-/

namespace CoreCapybara

/-! ## §2.2 New definitions: cvar mention and erasure -/

/-- Structural boolean equality on de Bruijn variables (`BVar` derives none). -/
def BVar.beq : BVar s k -> BVar s k -> Bool
| .here, .here => true
| .there x, .there y => x.beq y
| _, _ => false

/-- Whether the capture variable `c` occurs as a `.cvar` atom of the set (at any
    access mode). -/
def CaptureSet.mentionsCVar : CaptureSet s -> BVar s .cvar -> Bool
| .empty, _ => false
| .union a b, c => a.mentionsCVar c || b.mentionsCVar c
| .var _ _, _ => false
| .cvar _ c', c => c'.beq c

/-- Erase from a capture set every `.cvar` atom whose variable is mentioned by the
    kill set `K`.  `.var` atoms are untouched; `∪`/`{}` are homomorphic. -/
def CaptureSet.eraseCVars : CaptureSet s -> CaptureSet s -> CaptureSet s
| .empty, _ => .empty
| .union a b, K => (a.eraseCVars K) ∪ (b.eraseCVars K)
| .var m x, _ => .var m x
| .cvar m c, K => if K.mentionsCVar c then {} else .cvar m c

/-- de Bruijn predecessor on the top binder: every atom mentioning the top binder
    `.here` is dropped, every other atom un-shifts (`.there v ↦ v`).  Free vars are
    inert.  Preserving var atoms (rather than dropping them) is what makes
    `strip1_rename_succ` — `(K.rename succ).strip1 = K` for arbitrary `K` — hold; that
    round-trip drives the context-push commutation lemmas.  Used only to define context
    erasure. -/
def CaptureSet.strip1 : CaptureSet (s,,k) -> CaptureSet s
| .empty => .empty
| .union a b => a.strip1 ∪ b.strip1
| .var m (.free n) => .var m (.free n)
| .var m (.bound v) =>
  match k, v with
  | .var, .here => .empty
  | _, .there v' => .var m (.bound v')
| .cvar m c =>
  match k, c with
  | .cvar, .here => .empty
  | _, .there c' => .cvar m c'

/-- Erase cvar atoms mentioned by `K` from a capture bound. -/
def CaptureBound.eraseCVars : CaptureBound s -> CaptureSet s -> CaptureBound s
| .unbound, _ => .unbound
| .bound cs, K => .bound (cs.eraseCVars K)

/-- Erase cvar atoms mentioned by `K` from a separation context. -/
def SepCtx.eraseCVars : SepCtx s -> CaptureSet s -> SepCtx s
| .empty, _ => .empty
| .cons K0 C, K => .cons (K0.eraseCVars K) (C.eraseCVars K)

/-- Erase cvar atoms mentioned by `K` from a mutability context. -/
def MutabilityCtx.eraseCVars : MutabilityCtx s -> CaptureSet s -> MutabilityCtx s
| .empty, _ => .empty
| .cons K0 C m, K => .cons (K0.eraseCVars K) (C.eraseCVars K) m

/-- Erase cvar atoms mentioned by `K` from a modal context, componentwise. -/
def ModalCtx.eraseCVars (Ψ : ModalCtx s) (K : CaptureSet s) : ModalCtx s :=
  ⟨Ψ.sep.eraseCVars K, Ψ.mutability.eraseCVars K⟩

/-- Erase cvar atoms mentioned by `K` from a type.  At each binder the kill set is
    transported by the matching weakening (`succ` for a single binder, `weakenCVars n`
    for the `n`-ary existential), mirroring `Ty.rename`. -/
def Ty.eraseCVars : Ty sort s -> CaptureSet s -> Ty sort s
| .top, _ => .top
| .tvar x, _ => .tvar x
| .arrow T1 cs T2, K =>
    .arrow (T1.eraseCVars K) (cs.eraseCVars K) (T2.eraseCVars (K.rename (Rename.succ (k := .var))))
| .poly T1 cs T2, K =>
    .poly (T1.eraseCVars K) (cs.eraseCVars K) (T2.eraseCVars (K.rename (Rename.succ (k := .tvar))))
| .cpoly cb cs T, K =>
    .cpoly (cb.eraseCVars K) (cs.eraseCVars K) (T.eraseCVars (K.rename (Rename.succ (k := .cvar))))
| .consumer T1 cs T2, K => .consumer (T1.eraseCVars K) (cs.eraseCVars K) (T2.eraseCVars K)
| .modal cs Ψ T, K => .modal (cs.eraseCVars K) (Ψ.eraseCVars K) (T.eraseCVars K)
| .unit, _ => .unit
| .cap cs, K => .cap (cs.eraseCVars K)
| .bool, _ => .bool
| .cell cs T, K => .cell (cs.eraseCVars K) (T.eraseCVars K)
| .reader cs T, K => .reader (cs.eraseCVars K) (T.eraseCVars K)
| .exi n T, K => .exi n (T.eraseCVars (K.rename (Rename.weakenCVars n)))
| .typ T, K => .typ (T.eraseCVars K)

/-- Erasure preserves emptiness. -/
theorem CaptureSet.eraseCVars_isEmpty {cs : CaptureSet s} (h : cs.IsEmpty) (K : CaptureSet s) :
    (cs.eraseCVars K).IsEmpty := by
  induction h with
  | empty => exact .empty
  | union _ _ ih1 ih2 => exact .union ih1 ih2

/-- The capture set of an erased type is the erased capture set. -/
theorem Ty.captureSet_eraseCVars {T : Ty .capt s} {K : CaptureSet s} :
    (T.eraseCVars K).captureSet = T.captureSet.eraseCVars K := by
  cases T <;> rfl

/-- Erasure preserves purity. -/
theorem Ty.IsPureType.eraseCVars {T : Ty .capt s} (h : T.IsPureType) (K : CaptureSet s) :
    (T.eraseCVars K).IsPureType := by
  unfold Ty.IsPureType at *
  rw [Ty.captureSet_eraseCVars]
  exact CaptureSet.eraseCVars_isEmpty h K

/-- Erase cvar atoms mentioned by `K` from a pure type (purity is preserved). -/
def PureTy.eraseCVars (T : PureTy s) (K : CaptureSet s) : PureTy s :=
  ⟨T.core.eraseCVars K, T.p.eraseCVars K⟩

/-- Erase cvar atoms mentioned by `K` from a binding (the authority tag is untouched). -/
def Binding.eraseCVars : Binding s k -> CaptureSet s -> Binding s k
| .var T, K => .var (T.eraseCVars K)
| .tvar T, K => .tvar (T.eraseCVars K)
| .cvar a cb, K => .cvar a (cb.eraseCVars K)
| .lock Ψ, K => .lock (Ψ.eraseCVars K)

/-- Erase cvar atoms mentioned by `K` from an expression (including its annotations).
    The kill set is transported at each binder as in `Exp.rename`. -/
def Exp.eraseCVars : Exp s -> CaptureSet s -> Exp s
| .var x, _ => .var x
| .abs cs T e, K =>
    .abs (cs.eraseCVars K) (T.eraseCVars K) (e.eraseCVars (K.rename (Rename.succ (k := .var))))
| .tabs cs T e, K =>
    .tabs (cs.eraseCVars K) (T.eraseCVars K) (e.eraseCVars (K.rename (Rename.succ (k := .tvar))))
| .cabs cs cb e, K =>
    .cabs (cs.eraseCVars K) (cb.eraseCVars K) (e.eraseCVars (K.rename (Rename.succ (k := .cvar))))
| .consumer cs T e, K =>
    .consumer (cs.eraseCVars K) (T.eraseCVars K)
      (e.eraseCVars ((K.rename (Rename.succ (k := .cvar))).rename (Rename.succ (k := .var))))
| .boxed cs Ψ e, K =>
    .boxed (cs.eraseCVars K) (Ψ.eraseCVars K) (e.eraseCVars K)
| .reader x, _ => .reader x
| .alloc x, _ => .alloc x
| .drop x, _ => .drop x
| .pack css x, K => .pack (css.map (·.eraseCVars K)) x
| .app x y, _ => .app x y
| .tapp x T, K => .tapp x (T.eraseCVars K)
| .capp x cs, K => .capp x (cs.eraseCVars K)
| .consumer_app x e, K => .consumer_app x (e.eraseCVars K)
| .unwrap x, _ => .unwrap x
| .letin e1 e2, K =>
    .letin (e1.eraseCVars K) (e2.eraseCVars (K.rename (Rename.succ (k := .var))))
| .unpack n e1 e2, K =>
    .unpack n (e1.eraseCVars K)
      (e2.eraseCVars ((K.rename (Rename.weakenCVars n)).rename (Rename.succ (k := .var))))
| .unit, _ => .unit
| .btrue, _ => .btrue
| .bfalse, _ => .bfalse
| .read x, _ => .read x
| .write x y, _ => .write x y
| .cond x e2 e3, K => .cond x (e2.eraseCVars K) (e3.eraseCVars K)
| .par C1 C2 e1 e2, K =>
    .par (C1.eraseCVars K) (C2.eraseCVars K) (e1.eraseCVars K) (e2.eraseCVars K)

/-- Erase cvar atoms mentioned by `K` from a context.  Each binding is erased with the
    kill set stripped down (`strip1`) to that binding's smaller signature. -/
def Ctx.eraseCVars : Ctx s -> CaptureSet s -> Ctx s
| .empty, _ => .empty
| .push Γ b, K => (Γ.eraseCVars K.strip1).push (b.eraseCVars K.strip1)

/-! ## §3 Layer A — erasure algebra

  Item numbers refer to `notes/kill-weakening-design.md §3`. -/

/- Item 1: `{}`/`∪` are homomorphic (definitional). -/
@[simp] theorem CaptureSet.eraseCVars_empty {K : CaptureSet s} :
    (CaptureSet.empty).eraseCVars K = .empty := rfl

@[simp] theorem CaptureSet.eraseCVars_union {a b K : CaptureSet s} :
    (a.union b).eraseCVars K = (a.eraseCVars K).union (b.eraseCVars K) := rfl

@[simp] theorem CaptureSet.eraseCVars_var {m : Access} {x : Var .var s} {K : CaptureSet s} :
    (CaptureSet.var m x).eraseCVars K = .var m x := rfl

theorem CaptureSet.eraseCVars_cvar {m : Access} {c : BVar s .cvar} {K : CaptureSet s} :
    (CaptureSet.cvar m c).eraseCVars K = if K.mentionsCVar c then {} else .cvar m c := rfl

@[simp] theorem CaptureSet.eraseCVars_cvar_pos {m : Access} {c : BVar s .cvar} {K : CaptureSet s}
    (h : K.mentionsCVar c = true) : (CaptureSet.cvar m c).eraseCVars K = {} := by
  simp [CaptureSet.eraseCVars_cvar, h]

@[simp] theorem CaptureSet.eraseCVars_cvar_neg {m : Access} {c : BVar s .cvar} {K : CaptureSet s}
    (h : K.mentionsCVar c = false) : (CaptureSet.cvar m c).eraseCVars K = .cvar m c := by
  simp [CaptureSet.eraseCVars_cvar, h]

/- Item 2: `mentionsCVar` ↔ atom-subset, and membership preservation/inversion. -/
theorem BVar.eq_of_beq : (x y : BVar s k) → x.beq y = true → x = y
  | .here, .here, _ => rfl
  | .there x0, .there y0, h => by rw [BVar.eq_of_beq x0 y0 h]
  | .here, .there _, h => by simp [BVar.beq] at h
  | .there _, .here, h => by simp [BVar.beq] at h

@[simp] theorem BVar.beq_self {x : BVar s k} : x.beq x = true := by
  induction x with
  | here => rfl
  | there x ih => exact ih

theorem BVar.beq_iff_eq {x y : BVar s k} : x.beq y = true ↔ x = y :=
  ⟨BVar.eq_of_beq x y, by rintro rfl; exact BVar.beq_self⟩

theorem CaptureSet.mentionsCVar_of_cvar_subset {C : CaptureSet s} {a : Access}
    {c : BVar s .cvar} (h : (CaptureSet.cvar a c) ⊆ C) : C.mentionsCVar c = true := by
  induction C with
  | empty => exact absurd h CaptureSet.cvar_not_subset_empty
  | union C1 C2 ih1 ih2 =>
    simp only [CaptureSet.mentionsCVar, Bool.or_eq_true]
    rcases CaptureSet.cvar_subset_union_inv h with h' | h'
    · exact Or.inl (ih1 h')
    · exact Or.inr (ih2 h')
  | var m x => exact absurd h CaptureSet.cvar_not_subset_var
  | cvar m c' =>
    obtain ⟨_, hc⟩ := CaptureSet.cvar_subset_cvar_inv h
    subst hc
    simp only [CaptureSet.mentionsCVar]
    exact BVar.beq_self

theorem CaptureSet.cvar_subset_of_mentionsCVar {C : CaptureSet s} {c : BVar s .cvar}
    (h : C.mentionsCVar c = true) : ∃ a, (CaptureSet.cvar a c) ⊆ C := by
  induction C with
  | empty => simp [CaptureSet.mentionsCVar] at h
  | union C1 C2 ih1 ih2 =>
    simp only [CaptureSet.mentionsCVar, Bool.or_eq_true] at h
    rcases h with h | h
    · obtain ⟨a, ha⟩ := ih1 h; exact ⟨a, .union_right_left ha⟩
    · obtain ⟨a, ha⟩ := ih2 h; exact ⟨a, .union_right_right ha⟩
  | var m x => simp [CaptureSet.mentionsCVar] at h
  | cvar m c' =>
    simp only [CaptureSet.mentionsCVar] at h
    have := BVar.eq_of_beq _ _ h; subst this
    exact ⟨m, .refl⟩

theorem CaptureSet.cvar_subset_eraseCVars {C K : CaptureSet s} {a : Access} {c : BVar s .cvar}
    (hK : K.mentionsCVar c = false) (h : (CaptureSet.cvar a c) ⊆ C) :
    (CaptureSet.cvar a c) ⊆ C.eraseCVars K := by
  induction C with
  | empty => exact absurd h CaptureSet.cvar_not_subset_empty
  | union C1 C2 ih1 ih2 =>
    rcases CaptureSet.cvar_subset_union_inv h with h' | h'
    · exact .union_right_left (ih1 h')
    · exact .union_right_right (ih2 h')
  | var m x => exact absurd h CaptureSet.cvar_not_subset_var
  | cvar m c' =>
    obtain ⟨ha, hc⟩ := CaptureSet.cvar_subset_cvar_inv h
    subst ha hc
    rw [CaptureSet.eraseCVars_cvar, hK]
    exact .refl

theorem CaptureSet.cvar_subset_eraseCVars_inv {C K : CaptureSet s} {a : Access} {c : BVar s .cvar}
    (h : (CaptureSet.cvar a c) ⊆ C.eraseCVars K) :
    (CaptureSet.cvar a c) ⊆ C ∧ K.mentionsCVar c = false := by
  induction C with
  | empty => exact absurd h CaptureSet.cvar_not_subset_empty
  | union C1 C2 ih1 ih2 =>
    rcases CaptureSet.cvar_subset_union_inv h with h' | h'
    · obtain ⟨hsub, hK⟩ := ih1 h'; exact ⟨.union_right_left hsub, hK⟩
    · obtain ⟨hsub, hK⟩ := ih2 h'; exact ⟨.union_right_right hsub, hK⟩
  | var m x => exact absurd h CaptureSet.cvar_not_subset_var
  | cvar m c' =>
    rw [CaptureSet.eraseCVars_cvar] at h
    cases hb : K.mentionsCVar c' with
    | true => rw [hb] at h; exact absurd h CaptureSet.cvar_not_subset_empty
    | false =>
      rw [hb] at h
      obtain ⟨ha, hc⟩ := CaptureSet.cvar_subset_cvar_inv h
      subst ha hc
      exact ⟨.refl, hb⟩

/- Item 3: erasure commutes with the access maps (access-insensitivity). -/
theorem CaptureSet.eraseCVars_applyRO {C K : CaptureSet s} :
    (C.applyRO).eraseCVars K = (C.eraseCVars K).applyRO := by
  induction C with
  | empty => rfl
  | union C1 C2 ih1 ih2 =>
    simp only [CaptureSet.applyRO_union, CaptureSet.eraseCVars_union, ih1, ih2]
  | var m x => rfl
  | cvar m c =>
    change (CaptureSet.cvar m.applyRO c).eraseCVars K
      = ((CaptureSet.cvar m c).eraseCVars K).applyRO
    rw [CaptureSet.eraseCVars_cvar, CaptureSet.eraseCVars_cvar]
    cases K.mentionsCVar c <;> rfl

theorem CaptureSet.eraseCVars_applyMut {C K : CaptureSet s} {m : Mutability} :
    (C.applyMut m).eraseCVars K = (C.eraseCVars K).applyMut m := by
  cases m with
  | epsilon => rfl
  | ro => simp only [CaptureSet.applyMut_ro]; exact CaptureSet.eraseCVars_applyRO

theorem CaptureSet.eraseCVars_applyDrop {C K : CaptureSet s} :
    (C.applyDrop).eraseCVars K = (C.eraseCVars K).applyDrop := by
  induction C with
  | empty => rfl
  | union C1 C2 ih1 ih2 =>
    simp only [CaptureSet.applyDrop, CaptureSet.eraseCVars_union, ih1, ih2]
  | var m x => rfl
  | cvar m c =>
    change (CaptureSet.cvar .drop c).eraseCVars K
      = ((CaptureSet.cvar m c).eraseCVars K).applyDrop
    rw [CaptureSet.eraseCVars_cvar, CaptureSet.eraseCVars_cvar]
    cases K.mentionsCVar c <;> rfl

theorem CaptureSet.eraseCVars_applyAccess {C K : CaptureSet s} {a : Access} :
    (C.applyAccess a).eraseCVars K = (C.eraseCVars K).applyAccess a := by
  cases a with
  | M m => simp only [CaptureSet.applyAccess_M]; exact CaptureSet.eraseCVars_applyMut
  | drop => simp only [CaptureSet.applyAccess_drop]; exact CaptureSet.eraseCVars_applyDrop

/- Item 4: `Subset`/`CoveredBy` monotone under erasure. -/
theorem CaptureSet.Subset.eraseCVars {C1 C2 K : CaptureSet s}
    (h : C1 ⊆ C2) : (C1.eraseCVars K) ⊆ (C2.eraseCVars K) := by
  induction h with
  | refl => exact .refl
  | empty => exact .empty
  | union_left _ _ ih1 ih2 => exact .union_left ih1 ih2
  | union_right_left _ ih => exact .union_right_left ih
  | union_right_right _ ih => exact .union_right_right ih

theorem CaptureSet.CoveredBy.eraseCVars {C1 C2 K : CaptureSet s}
    (h : C1.CoveredBy C2) : (C1.eraseCVars K).CoveredBy (C2.eraseCVars K) := by
  induction h with
  | refl hm =>
    rw [CaptureSet.eraseCVars_applyMut, CaptureSet.eraseCVars_applyMut]
    exact .refl hm
  | empty => exact .empty
  | union_left _ _ ih1 ih2 => exact .union_left ih1 ih2
  | union_right_left _ ih => exact .union_right_left ih
  | union_right_right _ ih => exact .union_right_right ih

/- Item 5: closedness / purity / peaks-only / emptiness preserved. -/
theorem CaptureSet.IsClosed.eraseCVars {C : CaptureSet s} (h : C.IsClosed) (K : CaptureSet s) :
    (C.eraseCVars K).IsClosed := by
  induction h with
  | empty => exact .empty
  | union _ _ ih1 ih2 => exact .union ih1 ih2
  | cvar =>
    rename_i m c
    rw [CaptureSet.eraseCVars_cvar]
    split
    · exact .empty
    · exact .cvar
  | var_bound => exact .var_bound

theorem CaptureBound.IsClosed.eraseCVars {cb : CaptureBound s} (h : cb.IsClosed)
    (K : CaptureSet s) :
    (cb.eraseCVars K).IsClosed := by
  cases h with
  | unbound => exact .unbound
  | bound hcs => exact .bound (hcs.eraseCVars K)

theorem SepCtx.IsClosed.eraseCVars {K0 : SepCtx s} (h : K0.IsClosed) (K : CaptureSet s) :
    (K0.eraseCVars K).IsClosed := by
  induction h with
  | empty => exact .empty
  | cons _ hC ih => exact .cons ih (hC.eraseCVars K)

theorem MutabilityCtx.IsClosed.eraseCVars {K0 : MutabilityCtx s} (h : K0.IsClosed)
    (K : CaptureSet s) : (K0.eraseCVars K).IsClosed := by
  induction h with
  | empty => exact .empty
  | cons _ hC ih => exact .cons ih (hC.eraseCVars K)

theorem ModalCtx.IsClosed.eraseCVars {Ψ : ModalCtx s} (h : Ψ.IsClosed) (K : CaptureSet s) :
    (Ψ.eraseCVars K).IsClosed :=
  ⟨h.sep.eraseCVars K, h.mutability.eraseCVars K⟩

theorem Ty.IsClosed.eraseCVars {T : Ty sort s} (h : T.IsClosed) (K : CaptureSet s) :
    (T.eraseCVars K).IsClosed := by
  induction h with
  | top => exact .top
  | tvar => exact .tvar
  | arrow _ hcs _ ih1 ih2 => exact .arrow (ih1 K) (hcs.eraseCVars K) (ih2 _)
  | poly _ hcs _ ih1 ih2 => exact .poly (ih1 K) (hcs.eraseCVars K) (ih2 _)
  | cpoly hcb hcs _ ih => exact .cpoly (hcb.eraseCVars K) (hcs.eraseCVars K) (ih _)
  | consumer _ hcs _ ih1 ih2 => exact .consumer (ih1 K) (hcs.eraseCVars K) (ih2 K)
  | modal hcs hΨ _ ih => exact .modal (hcs.eraseCVars K) (hΨ.eraseCVars K) (ih K)
  | unit => exact .unit
  | cap hcs => exact .cap (hcs.eraseCVars K)
  | bool => exact .bool
  | cell hcs _ ih => exact .cell (hcs.eraseCVars K) (ih K)
  | reader hcs _ ih => exact .reader (hcs.eraseCVars K) (ih K)
  | exi _ ih => exact .exi (ih _)
  | typ _ ih => exact .typ (ih K)

theorem PureTy.IsClosed.eraseCVars {T : PureTy s} (h : T.IsClosed) (K : CaptureSet s) :
    (T.eraseCVars K).IsClosed :=
  Ty.IsClosed.eraseCVars h K

theorem CaptureSet.PeaksOnly.eraseCVars {C : CaptureSet s} (h : C.PeaksOnly) (K : CaptureSet s) :
    (C.eraseCVars K).PeaksOnly := by
  induction h with
  | empty => exact .empty
  | union _ _ ih1 ih2 => exact .union ih1 ih2
  | cvar =>
    rename_i m c
    rw [CaptureSet.eraseCVars_cvar]
    split
    · exact .empty
    · exact .cvar

/- Item 6: rename–erasure commutation for cvar-injective renamings. -/
/-- A renaming is injective on capture variables. -/
def Rename.CVarInjective (ρ : Rename s1 s2) : Prop :=
  ∀ {c c' : BVar s1 .cvar}, ρ.var c = ρ.var c' → c = c'

theorem Rename.id_cvarInjective : (Rename.id : Rename s s).CVarInjective := fun h => h

theorem Rename.CVarInjective.comp {ρ1 : Rename s1 s2} {ρ2 : Rename s2 s3}
    (h1 : ρ1.CVarInjective) (h2 : ρ2.CVarInjective) : (ρ1.comp ρ2).CVarInjective :=
  fun heq => h1 (h2 heq)

theorem Rename.succ_cvarInjective : (Rename.succ (k := k) : Rename s (s,,k)).CVarInjective := by
  intro c c' h
  injection h

theorem Rename.CVarInjective.lift {ρ : Rename s1 s2} (h : ρ.CVarInjective) :
    (ρ.lift (k := k)).CVarInjective := by
  intro c c' heq
  cases c with
  | here =>
    cases c' with
    | here => rfl
    | there c0' => simp [Rename.lift] at heq
  | there c0 =>
    cases c' with
    | here => simp [Rename.lift] at heq
    | there c0' =>
      simp only [Rename.lift, BVar.there.injEq] at heq
      rw [h heq]

theorem Rename.CVarInjective.liftCVars {ρ : Rename s1 s2} (h : ρ.CVarInjective) :
    {n : Nat} → (ρ.liftCVars n).CVarInjective
  | 0 => h
  | n + 1 => Rename.CVarInjective.lift (Rename.CVarInjective.liftCVars h (n := n))

theorem Rename.weakenCVars_cvarInjective {n : Nat} :
    (Rename.weakenCVars n : Rename s (s.extendCVars n)).CVarInjective := by
  induction n with
  | zero => exact Rename.id_cvarInjective
  | succ n ih => exact Rename.CVarInjective.comp ih Rename.succ_cvarInjective

/-- Associativity of renaming composition. -/
theorem Rename.comp_assoc {f : Rename s1 s2} {g : Rename s2 s3} {h : Rename s3 s4} :
    (f.comp g).comp h = f.comp (g.comp h) := by
  apply Rename.funext; intro k x; rfl

/-- Weakening a variable by `n` cvars then applying `ρ` equals applying `ρ` first
    (lifted under the `n` cvar binders) — the variable-level commutation. -/
theorem Rename.weakenCVars_var_comm {ρ : Rename s1 s2} {k : Kind} (x : BVar s1 k) :
    {n : Nat} → (Rename.weakenCVars n).var (ρ.var x)
      = (ρ.liftCVars n).var ((Rename.weakenCVars n).var x)
  | 0 => rfl
  | n + 1 => by
    change BVar.there ((Rename.weakenCVars n).var (ρ.var x))
      = ((ρ.liftCVars n).lift).var (BVar.there ((Rename.weakenCVars n).var x))
    rw [Rename.weakenCVars_var_comm x (n := n)]
    rfl

theorem Rename.comp_weakenCVars_liftCVars {ρ : Rename s1 s2} {n : Nat} :
    ρ.comp (Rename.weakenCVars n) = (Rename.weakenCVars n).comp (ρ.liftCVars n) := by
  apply Rename.funext
  intro k x
  exact Rename.weakenCVars_var_comm x

/-- `succ`-under-a-binder alignment used at single binders in the rename lemmas. -/
theorem CaptureSet.rename_succ_lift {C : CaptureSet s1} {ρ : Rename s1 s2} {k : Kind} :
    (C.rename ρ).rename (Rename.succ (k := k))
      = (C.rename (Rename.succ (k := k))).rename ρ.lift := by
  rw [CaptureSet.rename_comp, CaptureSet.rename_comp, Rename.succ_lift_comm]

/-- `weakenCVars`-under-`n`-binders alignment used at the existential binder. -/
theorem CaptureSet.rename_weakenCVars_lift {C : CaptureSet s1} {ρ : Rename s1 s2} {n : Nat} :
    (C.rename ρ).rename (Rename.weakenCVars n)
      = (C.rename (Rename.weakenCVars n)).rename (ρ.liftCVars n) := by
  rw [CaptureSet.rename_comp, CaptureSet.rename_comp, Rename.comp_weakenCVars_liftCVars]

/-- `mentionsCVar` transports across a cvar-injective renaming. -/
theorem CaptureSet.mentionsCVar_rename {K : CaptureSet s1} {ρ : Rename s1 s2} {c : BVar s1 .cvar}
    (hρ : ρ.CVarInjective) : (K.rename ρ).mentionsCVar (ρ.var c) = K.mentionsCVar c := by
  induction K with
  | empty => rfl
  | union K1 K2 ih1 ih2 => simp only [CaptureSet.rename, CaptureSet.mentionsCVar, ih1, ih2]
  | var m x => rfl
  | cvar m c' =>
    simp only [CaptureSet.rename, CaptureSet.mentionsCVar]
    by_cases hcc : c' = c
    · subst hcc; simp only [BVar.beq_self]
    · have h1 : c'.beq c = false := by
        cases hh : c'.beq c
        · rfl
        · exact absurd (BVar.eq_of_beq _ _ hh) hcc
      have h2 : (ρ.var c').beq (ρ.var c) = false := by
        cases hh : (ρ.var c').beq (ρ.var c)
        · rfl
        · exact absurd (hρ (BVar.eq_of_beq _ _ hh)) hcc
      rw [h1, h2]

theorem CaptureSet.eraseCVars_rename {C K : CaptureSet s1} {ρ : Rename s1 s2}
    (hρ : ρ.CVarInjective) :
    (C.rename ρ).eraseCVars (K.rename ρ) = (C.eraseCVars K).rename ρ := by
  induction C with
  | empty => rfl
  | union C1 C2 ih1 ih2 =>
    simp only [CaptureSet.rename, CaptureSet.eraseCVars_union, ih1, ih2]
  | var m x => rfl
  | cvar m c =>
    simp only [CaptureSet.rename, CaptureSet.eraseCVars_cvar,
      CaptureSet.mentionsCVar_rename hρ]
    cases K.mentionsCVar c <;> rfl

theorem CaptureBound.eraseCVars_rename {cb : CaptureBound s1} {K : CaptureSet s1}
    {ρ : Rename s1 s2} (hρ : ρ.CVarInjective) :
    (cb.rename ρ).eraseCVars (K.rename ρ) = (cb.eraseCVars K).rename ρ := by
  cases cb with
  | unbound => rfl
  | bound cs =>
    simp only [CaptureBound.rename, CaptureBound.eraseCVars, CaptureSet.eraseCVars_rename hρ]

theorem SepCtx.eraseCVars_rename {K0 : SepCtx s1} {K : CaptureSet s1} {ρ : Rename s1 s2}
    (hρ : ρ.CVarInjective) :
    (K0.rename ρ).eraseCVars (K.rename ρ) = (K0.eraseCVars K).rename ρ := by
  induction K0 with
  | empty => rfl
  | cons K0 C ih =>
    simp only [SepCtx.rename, SepCtx.eraseCVars, CaptureSet.eraseCVars_rename hρ, ih]

theorem MutabilityCtx.eraseCVars_rename {K0 : MutabilityCtx s1} {K : CaptureSet s1}
    {ρ : Rename s1 s2} (hρ : ρ.CVarInjective) :
    (K0.rename ρ).eraseCVars (K.rename ρ) = (K0.eraseCVars K).rename ρ := by
  induction K0 with
  | empty => rfl
  | cons K0 C m ih =>
    simp only [MutabilityCtx.rename, MutabilityCtx.eraseCVars, CaptureSet.eraseCVars_rename hρ, ih]

theorem ModalCtx.eraseCVars_rename {Ψ : ModalCtx s1} {K : CaptureSet s1} {ρ : Rename s1 s2}
    (hρ : ρ.CVarInjective) :
    (Ψ.rename ρ).eraseCVars (K.rename ρ) = (Ψ.eraseCVars K).rename ρ := by
  cases Ψ with
  | mk sep mu =>
    simp only [ModalCtx.eraseCVars, ModalCtx.rename, SepCtx.eraseCVars_rename hρ,
      MutabilityCtx.eraseCVars_rename hρ]

theorem Ty.eraseCVars_rename {T : Ty sort s1} {K : CaptureSet s1} {ρ : Rename s1 s2}
    (hρ : ρ.CVarInjective) :
    (T.rename ρ).eraseCVars (K.rename ρ) = (T.eraseCVars K).rename ρ := by
  induction T generalizing s2 with
  | top => rfl
  | tvar x => rfl
  | unit => rfl
  | bool => rfl
  | cap cs => simp only [Ty.rename, Ty.eraseCVars, CaptureSet.eraseCVars_rename hρ]
  | arrow T1 cs T2 ih1 ih2 =>
    have hbody : (T2.rename ρ.lift).eraseCVars ((K.rename ρ).rename (Rename.succ (k := .var)))
        = (T2.eraseCVars (K.rename (Rename.succ (k := .var)))).rename ρ.lift := by
      rw [CaptureSet.rename_succ_lift]; exact ih2 (Rename.CVarInjective.lift hρ)
    simp only [Ty.rename, Ty.eraseCVars, ih1 hρ, CaptureSet.eraseCVars_rename hρ]
    congr 1
  | poly T1 cs T2 ih1 ih2 =>
    have hbody : (T2.rename ρ.lift).eraseCVars ((K.rename ρ).rename (Rename.succ (k := .tvar)))
        = (T2.eraseCVars (K.rename (Rename.succ (k := .tvar)))).rename ρ.lift := by
      rw [CaptureSet.rename_succ_lift]; exact ih2 (Rename.CVarInjective.lift hρ)
    simp only [Ty.rename, Ty.eraseCVars, ih1 hρ, CaptureSet.eraseCVars_rename hρ]
    congr 1
  | cpoly cb cs T ih =>
    have hbody : (T.rename ρ.lift).eraseCVars ((K.rename ρ).rename (Rename.succ (k := .cvar)))
        = (T.eraseCVars (K.rename (Rename.succ (k := .cvar)))).rename ρ.lift := by
      rw [CaptureSet.rename_succ_lift]; exact ih (Rename.CVarInjective.lift hρ)
    simp only [Ty.rename, Ty.eraseCVars, CaptureBound.eraseCVars_rename hρ,
      CaptureSet.eraseCVars_rename hρ]
    congr 1
  | consumer T1 cs T2 ih1 ih2 =>
    simp only [Ty.rename, Ty.eraseCVars, CaptureSet.eraseCVars_rename hρ, ih1 hρ, ih2 hρ]
  | modal cs Ψ T ih =>
    simp only [Ty.rename, Ty.eraseCVars, CaptureSet.eraseCVars_rename hρ,
      ModalCtx.eraseCVars_rename hρ, ih hρ]
  | cell cs T ih =>
    simp only [Ty.rename, Ty.eraseCVars, CaptureSet.eraseCVars_rename hρ, ih hρ]
  | reader cs T ih =>
    simp only [Ty.rename, Ty.eraseCVars, CaptureSet.eraseCVars_rename hρ, ih hρ]
  | exi n T ih =>
    have hbody : (T.rename (ρ.liftCVars n)).eraseCVars ((K.rename ρ).rename (Rename.weakenCVars n))
        = (T.eraseCVars (K.rename (Rename.weakenCVars n))).rename (ρ.liftCVars n) := by
      rw [CaptureSet.rename_weakenCVars_lift]; exact ih (Rename.CVarInjective.liftCVars hρ)
    simp only [Ty.rename, Ty.eraseCVars]
    congr 1
  | typ T ih =>
    simp only [Ty.rename, Ty.eraseCVars, ih hρ]

theorem PureTy.eraseCVars_rename {T : PureTy s1} {K : CaptureSet s1} {ρ : Rename s1 s2}
    (hρ : ρ.CVarInjective) :
    (T.rename ρ).eraseCVars (K.rename ρ) = (T.eraseCVars K).rename ρ := by
  cases T with
  | mk core p =>
    simp only [PureTy.rename, PureTy.eraseCVars, Ty.eraseCVars_rename hρ]

theorem Exp.eraseCVars_rename {e : Exp s1} {K : CaptureSet s1} {ρ : Rename s1 s2}
    (hρ : ρ.CVarInjective) :
    (e.rename ρ).eraseCVars (K.rename ρ) = (e.eraseCVars K).rename ρ := by
  induction e generalizing s2 with
  | var x => rfl
  | reader x => rfl
  | alloc x => rfl
  | drop x => rfl
  | app x y => rfl
  | unwrap x => rfl
  | unit => rfl
  | btrue => rfl
  | bfalse => rfl
  | read x => rfl
  | write x y => rfl
  | abs cs T e ih =>
    have hbody : (e.rename ρ.lift).eraseCVars ((K.rename ρ).rename (Rename.succ (k := .var)))
        = (e.eraseCVars (K.rename (Rename.succ (k := .var)))).rename ρ.lift := by
      rw [CaptureSet.rename_succ_lift]; exact ih (Rename.CVarInjective.lift hρ)
    simp only [Exp.rename, Exp.eraseCVars, CaptureSet.eraseCVars_rename hρ,
      Ty.eraseCVars_rename hρ]
    congr 1
  | tabs cs T e ih =>
    have hbody : (e.rename ρ.lift).eraseCVars ((K.rename ρ).rename (Rename.succ (k := .tvar)))
        = (e.eraseCVars (K.rename (Rename.succ (k := .tvar)))).rename ρ.lift := by
      rw [CaptureSet.rename_succ_lift]; exact ih (Rename.CVarInjective.lift hρ)
    simp only [Exp.rename, Exp.eraseCVars, CaptureSet.eraseCVars_rename hρ,
      PureTy.eraseCVars_rename hρ]
    congr 1
  | cabs cs cb e ih =>
    have hbody : (e.rename ρ.lift).eraseCVars ((K.rename ρ).rename (Rename.succ (k := .cvar)))
        = (e.eraseCVars (K.rename (Rename.succ (k := .cvar)))).rename ρ.lift := by
      rw [CaptureSet.rename_succ_lift]; exact ih (Rename.CVarInjective.lift hρ)
    simp only [Exp.rename, Exp.eraseCVars, CaptureSet.eraseCVars_rename hρ,
      CaptureBound.eraseCVars_rename hρ]
    congr 1
  | consumer cs T e ih =>
    have hbody : (e.rename ρ.lift.lift).eraseCVars
          (((K.rename ρ).rename (Rename.succ (k := .cvar))).rename (Rename.succ (k := .var)))
        = (e.eraseCVars
            ((K.rename (Rename.succ (k := .cvar))).rename (Rename.succ (k := .var)))).rename
            ρ.lift.lift := by
      rw [CaptureSet.rename_succ_lift (ρ := ρ), CaptureSet.rename_succ_lift (ρ := ρ.lift)]
      exact ih (Rename.CVarInjective.lift (Rename.CVarInjective.lift hρ))
    simp only [Exp.rename, Exp.eraseCVars, CaptureSet.eraseCVars_rename hρ,
      Ty.eraseCVars_rename hρ]
    congr 1
  | boxed cs Ψ e ih =>
    simp only [Exp.rename, Exp.eraseCVars, CaptureSet.eraseCVars_rename hρ,
      ModalCtx.eraseCVars_rename hρ, ih hρ]
  | pack css x =>
    simp only [Exp.rename, Exp.eraseCVars]
    congr 1
    apply List.Vector.toList_injective
    simp only [List.Vector.toList_map, List.map_map, Function.comp_def,
      CaptureSet.eraseCVars_rename hρ]
  | tapp x T =>
    simp only [Exp.rename, Exp.eraseCVars, PureTy.eraseCVars_rename hρ]
  | capp x cs =>
    simp only [Exp.rename, Exp.eraseCVars, CaptureSet.eraseCVars_rename hρ]
  | consumer_app x e ih =>
    simp only [Exp.rename, Exp.eraseCVars, ih hρ]
  | letin e1 e2 ih1 ih2 =>
    have hbody : (e2.rename ρ.lift).eraseCVars ((K.rename ρ).rename (Rename.succ (k := .var)))
        = (e2.eraseCVars (K.rename (Rename.succ (k := .var)))).rename ρ.lift := by
      rw [CaptureSet.rename_succ_lift]; exact ih2 (Rename.CVarInjective.lift hρ)
    simp only [Exp.rename, Exp.eraseCVars, ih1 hρ]
    congr 1
  | unpack n e1 e2 ih1 ih2 =>
    have hbody : (e2.rename (ρ.liftCVars n).lift).eraseCVars
          (((K.rename ρ).rename (Rename.weakenCVars n)).rename (Rename.succ (k := .var)))
        = (e2.eraseCVars
            ((K.rename (Rename.weakenCVars n)).rename (Rename.succ (k := .var)))).rename
            (ρ.liftCVars n).lift := by
      rw [CaptureSet.rename_weakenCVars_lift, CaptureSet.rename_succ_lift (ρ := ρ.liftCVars n)]
      exact ih2 (Rename.CVarInjective.lift (Rename.CVarInjective.liftCVars hρ))
    simp only [Exp.rename, Exp.eraseCVars, ih1 hρ]
    congr 1
  | cond x e2 e3 ih2 ih3 =>
    simp only [Exp.rename, Exp.eraseCVars, ih2 hρ, ih3 hρ]
  | par C1 C2 e1 e2 ih1 ih2 =>
    simp only [Exp.rename, Exp.eraseCVars, CaptureSet.eraseCVars_rename hρ, ih1 hρ, ih2 hρ]

/- Item 7: strip1 payload lemma (drives context/lookup erasure). -/
@[simp] theorem CaptureSet.strip1_union {a b : CaptureSet (s,,k)} :
    (a.union b).strip1 = a.strip1.union b.strip1 := rfl

theorem CaptureSet.strip1_rename_succ {C : CaptureSet s} :
    (C.rename (Rename.succ (k := k))).strip1 = C := by
  induction C with
  | empty => rfl
  | union a b ih1 ih2 => simp only [CaptureSet.rename, CaptureSet.strip1_union, ih1, ih2]
  | var m x => cases x with | free n => rfl | bound v => cases k <;> rfl
  | cvar m c => cases k <;> rfl

/-- `strip1` un-shifts membership: `K.strip1` mentions `c` iff `K` mentions `c.there`. -/
theorem CaptureSet.mentionsCVar_strip1 {K : CaptureSet (s,,k)} {c : BVar s .cvar} :
    K.strip1.mentionsCVar c = K.mentionsCVar c.there := by
  induction K with
  | empty => rfl
  | union a b ih1 ih2 => simp only [CaptureSet.strip1_union, CaptureSet.mentionsCVar, ih1, ih2]
  | var m x => cases x with | free n => rfl | bound v => cases k <;> cases v <;> rfl
  | cvar m d => cases k <;> cases d <;> rfl

theorem CaptureSet.eraseCVars_rename_succ {C : CaptureSet s} {K : CaptureSet (s,,k)} :
    (C.rename (Rename.succ (k := k))).eraseCVars K
      = (C.eraseCVars K.strip1).rename (Rename.succ (k := k)) := by
  induction C with
  | empty => rfl
  | union a b ih1 ih2 => simp only [CaptureSet.rename, CaptureSet.eraseCVars_union, ih1, ih2]
  | var m x => rfl
  | cvar m c =>
    simp only [CaptureSet.rename, CaptureSet.eraseCVars_cvar, Rename.succ,
      CaptureSet.mentionsCVar_strip1]
    cases K.mentionsCVar c.there <;> rfl

theorem CaptureBound.eraseCVars_rename_succ {cb : CaptureBound s} {K : CaptureSet (s,,k)} :
    (cb.rename (Rename.succ (k := k))).eraseCVars K
      = (cb.eraseCVars K.strip1).rename (Rename.succ (k := k)) := by
  cases cb with
  | unbound => rfl
  | bound cs =>
    simp only [CaptureBound.rename, CaptureBound.eraseCVars, CaptureSet.eraseCVars_rename_succ]

/-- Erasing a **renamed** set depends only on the kill set's values on the image of `ρ`:
    the cvar atoms of `C.rename ρ` all lie in that image, so two kill sets agreeing there
    erase identically.  This congruence is the bridge from item 6 to the `succ` form. -/
theorem CaptureSet.eraseCVars_rename_congr {C : CaptureSet s1} {ρ : Rename s1 s2}
    {K1 K2 : CaptureSet s2}
    (h : ∀ (d : BVar s1 .cvar), K1.mentionsCVar (ρ.var d) = K2.mentionsCVar (ρ.var d)) :
    (C.rename ρ).eraseCVars K1 = (C.rename ρ).eraseCVars K2 := by
  induction C with
  | empty => rfl
  | union a b ih1 ih2 => simp only [CaptureSet.rename, CaptureSet.eraseCVars_union, ih1, ih2]
  | var m x => rfl
  | cvar m c => simp only [CaptureSet.rename, CaptureSet.eraseCVars_cvar, h c]

theorem CaptureSet.mentionsCVar_rename_succ_here {K : CaptureSet s} :
    (K.rename (Rename.succ (k := .cvar))).mentionsCVar BVar.here = false := by
  induction K with
  | empty => rfl
  | union K1 K2 ih1 ih2 =>
    simp only [CaptureSet.rename, CaptureSet.mentionsCVar, ih1, ih2, Bool.false_or]
  | var m x => rfl
  | cvar m c => rfl

theorem CaptureSet.eraseCVars_rename_congr_lift_agree {ρ : Rename s1 s2}
    {K1 K2 : CaptureSet s2} {k : Kind}
    (h : ∀ (d : BVar s1 .cvar), K1.mentionsCVar (ρ.var d) = K2.mentionsCVar (ρ.var d)) :
    ∀ (d : BVar (s1,,k) .cvar),
      (K1.rename (Rename.succ (k := k))).mentionsCVar (ρ.lift.var d)
        = (K2.rename (Rename.succ (k := k))).mentionsCVar (ρ.lift.var d) := by
  intro d
  cases d with
  | here =>
    simp only [Rename.lift, CaptureSet.mentionsCVar_rename_succ_here]
  | there d0 =>
    simp only [Rename.lift]
    have h1 :
        (K1.rename (Rename.succ (k := k))).mentionsCVar (ρ.var d0).there
          = K1.mentionsCVar (ρ.var d0) := by
      simpa only [Rename.succ] using
        (CaptureSet.mentionsCVar_rename (K := K1) (ρ := Rename.succ (k := k))
          (c := ρ.var d0) Rename.succ_cvarInjective)
    have h2 :
        (K2.rename (Rename.succ (k := k))).mentionsCVar (ρ.var d0).there
          = K2.mentionsCVar (ρ.var d0) := by
      simpa only [Rename.succ] using
        (CaptureSet.mentionsCVar_rename (K := K2) (ρ := Rename.succ (k := k))
          (c := ρ.var d0) Rename.succ_cvarInjective)
    rw [h1, h2]
    exact h d0

theorem CaptureSet.eraseCVars_rename_congr_liftCVars_agree {ρ : Rename s1 s2}
    {K1 K2 : CaptureSet s2}
    (h : ∀ (d : BVar s1 .cvar), K1.mentionsCVar (ρ.var d) = K2.mentionsCVar (ρ.var d)) :
    {n : Nat} → ∀ (d : BVar (s1.extendCVars n) .cvar),
      (K1.rename (Rename.weakenCVars n)).mentionsCVar ((ρ.liftCVars n).var d)
        = (K2.rename (Rename.weakenCVars n)).mentionsCVar ((ρ.liftCVars n).var d)
  | 0, d => by
    calc
      (K1.rename (Rename.weakenCVars 0)).mentionsCVar ((ρ.liftCVars 0).var d)
          = (K1.rename (Rename.id)).mentionsCVar (ρ.var d) := rfl
      _ = K1.mentionsCVar (ρ.var d) := by rw [CaptureSet.rename_id]
      _ = K2.mentionsCVar (ρ.var d) := h d
      _ = (K2.rename (Rename.id)).mentionsCVar (ρ.var d) := by rw [CaptureSet.rename_id]
      _ = (K2.rename (Rename.weakenCVars 0)).mentionsCVar ((ρ.liftCVars 0).var d) := rfl
  | n + 1, d => by
    have hK1 : K1.rename (Rename.weakenCVars (n + 1))
        = (K1.rename (Rename.weakenCVars n)).rename (Rename.succ (k := .cvar)) := by
      rw [CaptureSet.rename_comp]
      rfl
    have hK2 : K2.rename (Rename.weakenCVars (n + 1))
        = (K2.rename (Rename.weakenCVars n)).rename (Rename.succ (k := .cvar)) := by
      rw [CaptureSet.rename_comp]
      rfl
    cases d with
    | here =>
      have hHere :
          ((ρ.liftCVars (n + 1)).var
              (BVar.here : BVar (s1.extendCVars (n + 1)) .cvar)) = BVar.here := rfl
      calc
        (K1.rename (Rename.weakenCVars (n + 1))).mentionsCVar
            ((ρ.liftCVars (n + 1)).var BVar.here)
            = ((K1.rename (Rename.weakenCVars n)).rename
                (Rename.succ (k := .cvar))).mentionsCVar BVar.here := by
              rw [hK1, hHere]
              rfl
        _ = false := CaptureSet.mentionsCVar_rename_succ_here
        _ = ((K2.rename (Rename.weakenCVars n)).rename
                (Rename.succ (k := .cvar))).mentionsCVar BVar.here := by
              rw [CaptureSet.mentionsCVar_rename_succ_here]
        _ = (K2.rename (Rename.weakenCVars (n + 1))).mentionsCVar
            ((ρ.liftCVars (n + 1)).var BVar.here) := by
              rw [hK2, hHere]
              rfl
    | there d0 =>
      have hThere :
          ((ρ.liftCVars (n + 1)).var (BVar.there d0))
            = ((ρ.liftCVars n).var d0).there := rfl
      have h1 :
          ((K1.rename (Rename.weakenCVars n)).rename (Rename.succ (k := .cvar))).mentionsCVar
              ((ρ.liftCVars n).var d0).there
            = (K1.rename (Rename.weakenCVars n)).mentionsCVar ((ρ.liftCVars n).var d0) := by
        simpa only [Rename.succ] using
          (CaptureSet.mentionsCVar_rename (K := K1.rename (Rename.weakenCVars n))
            (ρ := Rename.succ (k := .cvar)) (c := (ρ.liftCVars n).var d0)
            Rename.succ_cvarInjective)
      have h2 :
          ((K2.rename (Rename.weakenCVars n)).rename (Rename.succ (k := .cvar))).mentionsCVar
              ((ρ.liftCVars n).var d0).there
            = (K2.rename (Rename.weakenCVars n)).mentionsCVar ((ρ.liftCVars n).var d0) := by
        simpa only [Rename.succ] using
          (CaptureSet.mentionsCVar_rename (K := K2.rename (Rename.weakenCVars n))
            (ρ := Rename.succ (k := .cvar)) (c := (ρ.liftCVars n).var d0)
            Rename.succ_cvarInjective)
      calc
        (K1.rename (Rename.weakenCVars (n + 1))).mentionsCVar
            ((ρ.liftCVars (n + 1)).var (BVar.there d0))
            = ((K1.rename (Rename.weakenCVars n)).rename
                (Rename.succ (k := .cvar))).mentionsCVar ((ρ.liftCVars n).var d0).there := by
              rw [hK1, hThere]
              rfl
        _ = (K1.rename (Rename.weakenCVars n)).mentionsCVar ((ρ.liftCVars n).var d0) := h1
        _ = (K2.rename (Rename.weakenCVars n)).mentionsCVar ((ρ.liftCVars n).var d0) :=
              CaptureSet.eraseCVars_rename_congr_liftCVars_agree h d0
        _ = ((K2.rename (Rename.weakenCVars n)).rename
                (Rename.succ (k := .cvar))).mentionsCVar ((ρ.liftCVars n).var d0).there := h2.symm
        _ = (K2.rename (Rename.weakenCVars (n + 1))).mentionsCVar
            ((ρ.liftCVars (n + 1)).var (BVar.there d0)) := by
              rw [hK2, hThere]
              rfl

theorem CaptureBound.eraseCVars_rename_congr {cb : CaptureBound s1} {ρ : Rename s1 s2}
    {K1 K2 : CaptureSet s2}
    (h : ∀ (d : BVar s1 .cvar), K1.mentionsCVar (ρ.var d) = K2.mentionsCVar (ρ.var d)) :
    (cb.rename ρ).eraseCVars K1 = (cb.rename ρ).eraseCVars K2 := by
  cases cb with
  | unbound => rfl
  | bound cs =>
    simp only [CaptureBound.rename, CaptureBound.eraseCVars,
      CaptureSet.eraseCVars_rename_congr h]

theorem SepCtx.eraseCVars_rename_congr {K0 : SepCtx s1} {ρ : Rename s1 s2}
    {K1 K2 : CaptureSet s2}
    (h : ∀ (d : BVar s1 .cvar), K1.mentionsCVar (ρ.var d) = K2.mentionsCVar (ρ.var d)) :
    (K0.rename ρ).eraseCVars K1 = (K0.rename ρ).eraseCVars K2 := by
  induction K0 with
  | empty => rfl
  | cons K0 C ih =>
    simp only [SepCtx.rename, SepCtx.eraseCVars, CaptureSet.eraseCVars_rename_congr h, ih]

theorem MutabilityCtx.eraseCVars_rename_congr {K0 : MutabilityCtx s1} {ρ : Rename s1 s2}
    {K1 K2 : CaptureSet s2}
    (h : ∀ (d : BVar s1 .cvar), K1.mentionsCVar (ρ.var d) = K2.mentionsCVar (ρ.var d)) :
    (K0.rename ρ).eraseCVars K1 = (K0.rename ρ).eraseCVars K2 := by
  induction K0 with
  | empty => rfl
  | cons K0 C m ih =>
    simp only [MutabilityCtx.rename, MutabilityCtx.eraseCVars,
      CaptureSet.eraseCVars_rename_congr h, ih]

theorem ModalCtx.eraseCVars_rename_congr {Ψ : ModalCtx s1} {ρ : Rename s1 s2}
    {K1 K2 : CaptureSet s2}
    (h : ∀ (d : BVar s1 .cvar), K1.mentionsCVar (ρ.var d) = K2.mentionsCVar (ρ.var d)) :
    (Ψ.rename ρ).eraseCVars K1 = (Ψ.rename ρ).eraseCVars K2 := by
  cases Ψ with
  | mk sep mu =>
    simp only [ModalCtx.rename, ModalCtx.eraseCVars, SepCtx.eraseCVars_rename_congr h,
      MutabilityCtx.eraseCVars_rename_congr h]

/-- Type-level congruence: two kill sets agreeing on the image of `ρ` erase `T.rename ρ`
    identically. -/
theorem Ty.eraseCVars_rename_congr {T : Ty sort s1} {ρ : Rename s1 s2}
    {K1 K2 : CaptureSet s2}
    (h : ∀ (d : BVar s1 .cvar), K1.mentionsCVar (ρ.var d) = K2.mentionsCVar (ρ.var d)) :
    (T.rename ρ).eraseCVars K1 = (T.rename ρ).eraseCVars K2 := by
  induction T generalizing s2 with
  | top => rfl
  | tvar x => rfl
  | unit => rfl
  | bool => rfl
  | cap cs =>
    simp only [Ty.rename, Ty.eraseCVars, CaptureSet.eraseCVars_rename_congr h]
  | arrow T1 cs T2 ih1 ih2 =>
    have hbody :
        (T2.rename ρ.lift).eraseCVars (K1.rename (Rename.succ (k := .var)))
          = (T2.rename ρ.lift).eraseCVars (K2.rename (Rename.succ (k := .var))) :=
      ih2 (CaptureSet.eraseCVars_rename_congr_lift_agree h)
    simp only [Ty.rename, Ty.eraseCVars, ih1 h, CaptureSet.eraseCVars_rename_congr h]
    congr 1
  | poly T1 cs T2 ih1 ih2 =>
    have hbody :
        (T2.rename ρ.lift).eraseCVars (K1.rename (Rename.succ (k := .tvar)))
          = (T2.rename ρ.lift).eraseCVars (K2.rename (Rename.succ (k := .tvar))) :=
      ih2 (CaptureSet.eraseCVars_rename_congr_lift_agree h)
    simp only [Ty.rename, Ty.eraseCVars, ih1 h, CaptureSet.eraseCVars_rename_congr h]
    congr 1
  | cpoly cb cs T ih =>
    have hbody :
        (T.rename ρ.lift).eraseCVars (K1.rename (Rename.succ (k := .cvar)))
          = (T.rename ρ.lift).eraseCVars (K2.rename (Rename.succ (k := .cvar))) :=
      ih (CaptureSet.eraseCVars_rename_congr_lift_agree h)
    simp only [Ty.rename, Ty.eraseCVars, CaptureBound.eraseCVars_rename_congr h,
      CaptureSet.eraseCVars_rename_congr h]
    congr 1
  | consumer T1 cs T2 ih1 ih2 =>
    simp only [Ty.rename, Ty.eraseCVars, ih1 h, ih2 h, CaptureSet.eraseCVars_rename_congr h]
  | modal cs Ψ T ih =>
    simp only [Ty.rename, Ty.eraseCVars, CaptureSet.eraseCVars_rename_congr h,
      ModalCtx.eraseCVars_rename_congr h, ih h]
  | cell cs T ih =>
    simp only [Ty.rename, Ty.eraseCVars, CaptureSet.eraseCVars_rename_congr h, ih h]
  | reader cs T ih =>
    simp only [Ty.rename, Ty.eraseCVars, CaptureSet.eraseCVars_rename_congr h, ih h]
  | exi n T ih =>
    have hbody :
        (T.rename (ρ.liftCVars n)).eraseCVars (K1.rename (Rename.weakenCVars n))
          = (T.rename (ρ.liftCVars n)).eraseCVars (K2.rename (Rename.weakenCVars n)) :=
      ih (CaptureSet.eraseCVars_rename_congr_liftCVars_agree h)
    simp only [Ty.rename, Ty.eraseCVars]
    congr 1
  | typ T ih =>
    simp only [Ty.rename, Ty.eraseCVars, ih h]

theorem Ty.eraseCVars_rename_succ {T : Ty sort s} {K : CaptureSet (s,,k)} :
    (T.rename (Rename.succ (k := k))).eraseCVars K
      = (T.eraseCVars K.strip1).rename (Rename.succ (k := k)) := by
  rw [← Ty.eraseCVars_rename (K := K.strip1) Rename.succ_cvarInjective]
  refine Ty.eraseCVars_rename_congr (fun d => ?_)
  rw [CaptureSet.mentionsCVar_rename Rename.succ_cvarInjective, CaptureSet.mentionsCVar_strip1]
  rfl

theorem PureTy.eraseCVars_rename_succ {T : PureTy s} {K : CaptureSet (s,,k)} :
    (T.rename (Rename.succ (k := k))).eraseCVars K
      = (T.eraseCVars K.strip1).rename (Rename.succ (k := k)) := by
  cases T with
  | mk core p =>
    simp only [PureTy.rename, PureTy.eraseCVars, Ty.eraseCVars_rename_succ]

theorem SepCtx.eraseCVars_rename_succ {K0 : SepCtx s} {K : CaptureSet (s,,k)} :
    (K0.rename (Rename.succ (k := k))).eraseCVars K
      = (K0.eraseCVars K.strip1).rename (Rename.succ (k := k)) := by
  induction K0 with
  | empty => rfl
  | cons K0 C ih =>
    simp only [SepCtx.rename, SepCtx.eraseCVars, CaptureSet.eraseCVars_rename_succ, ih]

theorem MutabilityCtx.eraseCVars_rename_succ {K0 : MutabilityCtx s} {K : CaptureSet (s,,k)} :
    (K0.rename (Rename.succ (k := k))).eraseCVars K
      = (K0.eraseCVars K.strip1).rename (Rename.succ (k := k)) := by
  induction K0 with
  | empty => rfl
  | cons K0 C m ih =>
    simp only [MutabilityCtx.rename, MutabilityCtx.eraseCVars,
      CaptureSet.eraseCVars_rename_succ, ih]

theorem ModalCtx.eraseCVars_rename_succ {Ψ : ModalCtx s} {K : CaptureSet (s,,k)} :
    (Ψ.rename (Rename.succ (k := k))).eraseCVars K
      = (Ψ.eraseCVars K.strip1).rename (Rename.succ (k := k)) := by
  cases Ψ with
  | mk sep mu =>
    simp only [ModalCtx.eraseCVars, ModalCtx.rename, SepCtx.eraseCVars_rename_succ,
      MutabilityCtx.eraseCVars_rename_succ]

/- Item 8: freshCVars erasure (weakened K never mentions the fresh variables). -/
theorem CaptureSet.freshCVars_eraseCVars {K : CaptureSet s} {n : Nat} :
    (CaptureSet.freshCVars n).eraseCVars (K.rename (Rename.weakenCVars n))
      = CaptureSet.freshCVars n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hK : K.rename (Rename.weakenCVars (n + 1))
        = (K.rename (Rename.weakenCVars n)).rename (Rename.succ (k := .cvar)) := by
      rw [CaptureSet.rename_comp]
      rfl
    rw [hK]
    change
      ((CaptureSet.cvar (.M .epsilon) BVar.here).eraseCVars
          ((K.rename (Rename.weakenCVars n)).rename (Rename.succ (k := .cvar))))
        ∪ (((CaptureSet.freshCVars n).rename (Rename.succ (k := .cvar))).eraseCVars
          ((K.rename (Rename.weakenCVars n)).rename (Rename.succ (k := .cvar))))
        = CaptureSet.cvar (.M .epsilon) BVar.here
          ∪ (CaptureSet.freshCVars n).rename (Rename.succ (k := .cvar))
    simp only [CaptureSet.eraseCVars_cvar, CaptureSet.mentionsCVar_rename_succ_here,
      Bool.false_eq_true, ↓reduceIte]
    rw [CaptureSet.eraseCVars_rename Rename.succ_cvarInjective, ih]

/- Item 9: subst–erasure commutation for the four openers (unconditional). -/
theorem CaptureSet.applyAccess_cvar_epsilon {a : Access} {c : BVar s .cvar} :
    (CaptureSet.cvar (.M .epsilon) c).applyAccess a = CaptureSet.cvar a c := by
  cases a with
  | M m =>
    cases m <;> rfl
  | drop => rfl

theorem CaptureSet.eraseCVars_subst_compatible {C : CaptureSet s1} {σ σe : Subst s1 s2}
    {K1 : CaptureSet s1} {K2 : CaptureSet s2}
    (hvar : ∀ (x : BVar s1 .var), σ.var x = σe.var x)
    (hcvar : ∀ (a : Access) (c : BVar s1 .cvar),
      ((σ.cvar c).applyAccess a).eraseCVars K2
        = if K1.mentionsCVar c then {} else (σe.cvar c).applyAccess a) :
    (C.subst σ).eraseCVars K2 = (C.eraseCVars K1).subst σe := by
  induction C with
  | empty => rfl
  | union C1 C2 ih1 ih2 =>
    simp only [CaptureSet.subst, CaptureSet.eraseCVars_union, ih1, ih2]
  | var m x =>
    simp only [CaptureSet.subst, CaptureSet.eraseCVars_var]
    cases x with
    | bound x0 =>
      change CaptureSet.var m (σ.var x0) = CaptureSet.var m (σe.var x0)
      rw [hvar x0]
    | free n => rfl
  | cvar m c =>
    simp only [CaptureSet.subst, CaptureSet.eraseCVars_cvar]
    rw [hcvar m c]
    cases K1.mentionsCVar c <;> rfl

theorem CaptureBound.eraseCVars_subst_compatible {cb : CaptureBound s1} {σ σe : Subst s1 s2}
    {K1 : CaptureSet s1} {K2 : CaptureSet s2}
    (hvar : ∀ (x : BVar s1 .var), σ.var x = σe.var x)
    (hcvar : ∀ (a : Access) (c : BVar s1 .cvar),
      ((σ.cvar c).applyAccess a).eraseCVars K2
        = if K1.mentionsCVar c then {} else (σe.cvar c).applyAccess a) :
    (cb.subst σ).eraseCVars K2 = (cb.eraseCVars K1).subst σe := by
  cases cb with
  | unbound => rfl
  | bound C =>
    simp only [CaptureBound.subst, CaptureBound.eraseCVars,
      CaptureSet.eraseCVars_subst_compatible hvar hcvar]

theorem SepCtx.eraseCVars_subst_compatible {K0 : SepCtx s1} {σ σe : Subst s1 s2}
    {K1 : CaptureSet s1} {K2 : CaptureSet s2}
    (hvar : ∀ (x : BVar s1 .var), σ.var x = σe.var x)
    (hcvar : ∀ (a : Access) (c : BVar s1 .cvar),
      ((σ.cvar c).applyAccess a).eraseCVars K2
        = if K1.mentionsCVar c then {} else (σe.cvar c).applyAccess a) :
    (K0.subst σ).eraseCVars K2 = (K0.eraseCVars K1).subst σe := by
  induction K0 with
  | empty => rfl
  | cons K0 C ih =>
    simp only [SepCtx.subst, SepCtx.eraseCVars,
      CaptureSet.eraseCVars_subst_compatible hvar hcvar, ih]

theorem MutabilityCtx.eraseCVars_subst_compatible {K0 : MutabilityCtx s1}
    {σ σe : Subst s1 s2} {K1 : CaptureSet s1} {K2 : CaptureSet s2}
    (hvar : ∀ (x : BVar s1 .var), σ.var x = σe.var x)
    (hcvar : ∀ (a : Access) (c : BVar s1 .cvar),
      ((σ.cvar c).applyAccess a).eraseCVars K2
        = if K1.mentionsCVar c then {} else (σe.cvar c).applyAccess a) :
    (K0.subst σ).eraseCVars K2 = (K0.eraseCVars K1).subst σe := by
  induction K0 with
  | empty => rfl
  | cons K0 C m ih =>
    simp only [MutabilityCtx.subst, MutabilityCtx.eraseCVars,
      CaptureSet.eraseCVars_subst_compatible hvar hcvar, ih]

theorem ModalCtx.eraseCVars_subst_compatible {Ψ : ModalCtx s1} {σ σe : Subst s1 s2}
    {K1 : CaptureSet s1} {K2 : CaptureSet s2}
    (hvar : ∀ (x : BVar s1 .var), σ.var x = σe.var x)
    (hcvar : ∀ (a : Access) (c : BVar s1 .cvar),
      ((σ.cvar c).applyAccess a).eraseCVars K2
        = if K1.mentionsCVar c then {} else (σe.cvar c).applyAccess a) :
    (Ψ.subst σ).eraseCVars K2 = (Ψ.eraseCVars K1).subst σe := by
  cases Ψ with
  | mk sep mu =>
    simp only [ModalCtx.subst, ModalCtx.eraseCVars,
      SepCtx.eraseCVars_subst_compatible hvar hcvar,
      MutabilityCtx.eraseCVars_subst_compatible hvar hcvar]

theorem Subst.eraseCVars_compatible_lift_var {σ σe : Subst s1 s2} {k : Kind}
    (hvar : ∀ (x : BVar s1 .var), σ.var x = σe.var x) :
    ∀ (x : BVar (s1,,k) .var), σ.lift.var x = σe.lift.var x := by
  intro x
  cases x with
  | here => rfl
  | there x0 =>
    simp only [Subst.lift, hvar x0]

theorem Subst.eraseCVars_compatible_lift_tvar {σ σe : Subst s1 s2}
    {K2 : CaptureSet s2} {k : Kind}
    (htvar : ∀ (X : BVar s1 .tvar), (σ.tvar X).eraseCVars K2 = σe.tvar X) :
    ∀ (X : BVar (s1,,k) .tvar),
      (σ.lift.tvar X).eraseCVars (K2.rename (Rename.succ (k := k))) = σe.lift.tvar X := by
  intro X
  cases X with
  | here => rfl
  | there X0 =>
    change (((σ.tvar X0).rename (Rename.succ (k := k))).eraseCVars
        (K2.rename (Rename.succ (k := k))))
      = (σe.tvar X0).rename (Rename.succ (k := k))
    rw [PureTy.eraseCVars_rename Rename.succ_cvarInjective, htvar X0]

theorem Subst.eraseCVars_compatible_lift_cvar {σ σe : Subst s1 s2}
    {K1 : CaptureSet s1} {K2 : CaptureSet s2} {k : Kind}
    (hcvar : ∀ (a : Access) (c : BVar s1 .cvar),
      ((σ.cvar c).applyAccess a).eraseCVars K2
        = if K1.mentionsCVar c then {} else (σe.cvar c).applyAccess a) :
    ∀ (a : Access) (c : BVar (s1,,k) .cvar),
      ((σ.lift.cvar c).applyAccess a).eraseCVars (K2.rename (Rename.succ (k := k)))
        = if (K1.rename (Rename.succ (k := k))).mentionsCVar c
          then {} else (σe.lift.cvar c).applyAccess a := by
  intro a c
  cases c with
  | here =>
    change (((CaptureSet.cvar (.M .epsilon) BVar.here).applyAccess a).eraseCVars
        (K2.rename (Rename.succ (k := .cvar))))
      = if (K1.rename (Rename.succ (k := .cvar))).mentionsCVar BVar.here
        then {} else (CaptureSet.cvar (.M .epsilon) BVar.here).applyAccess a
    rw [CaptureSet.applyAccess_cvar_epsilon, CaptureSet.eraseCVars_cvar]
    simp only [CaptureSet.mentionsCVar_rename_succ_here, Bool.false_eq_true, ↓reduceIte]
  | there c0 =>
    change ((((σ.cvar c0).rename (Rename.succ (k := k))).applyAccess a).eraseCVars
        (K2.rename (Rename.succ (k := k))))
      = if (K1.rename (Rename.succ (k := k))).mentionsCVar
          ((Rename.succ (k := k)).var c0)
        then {} else (((σe.cvar c0).rename (Rename.succ (k := k))).applyAccess a)
    rw [← CaptureSet.applyAccess_rename,
      CaptureSet.eraseCVars_rename Rename.succ_cvarInjective]
    have hm :
        (K1.rename (Rename.succ (k := k))).mentionsCVar
            ((Rename.succ (k := k)).var c0) = K1.mentionsCVar c0 :=
      CaptureSet.mentionsCVar_rename Rename.succ_cvarInjective
    rw [hm, hcvar a c0]
    cases K1.mentionsCVar c0
    · exact CaptureSet.applyAccess_rename
    · rfl

theorem Subst.eraseCVars_compatible_liftCVars_var {σ σe : Subst s1 s2}
    (hvar : ∀ (x : BVar s1 .var), σ.var x = σe.var x) :
    {n : Nat} → ∀ (x : BVar (s1.extendCVars n) .var),
      (σ.liftCVars n).var x = (σe.liftCVars n).var x
  | 0, x => hvar x
  | n + 1, x =>
    Subst.eraseCVars_compatible_lift_var
      (σ := σ.liftCVars n) (σe := σe.liftCVars n) (k := .cvar)
      (Subst.eraseCVars_compatible_liftCVars_var hvar (n := n)) x

theorem Subst.eraseCVars_compatible_liftCVars_tvar {σ σe : Subst s1 s2}
    {K2 : CaptureSet s2}
    (htvar : ∀ (X : BVar s1 .tvar), (σ.tvar X).eraseCVars K2 = σe.tvar X) :
    {n : Nat} → ∀ (X : BVar (s1.extendCVars n) .tvar),
      ((σ.liftCVars n).tvar X).eraseCVars (K2.rename (Rename.weakenCVars n))
        = (σe.liftCVars n).tvar X
  | 0, X => by
    have h : (σ.tvar X).eraseCVars (K2.rename Rename.id) = σe.tvar X := by
      rw [show K2.rename Rename.id = K2 from CaptureSet.rename_id]
      exact htvar X
    simpa only [Rename.weakenCVars, Subst.liftCVars] using h
  | n + 1, X => by
    have hK : K2.rename (Rename.weakenCVars (n + 1))
        = (K2.rename (Rename.weakenCVars n)).rename (Rename.succ (k := .cvar)) := by
      rw [CaptureSet.rename_comp]
      rfl
    rw [hK]
    exact Subst.eraseCVars_compatible_lift_tvar
      (σ := σ.liftCVars n) (σe := σe.liftCVars n) (k := .cvar)
      (Subst.eraseCVars_compatible_liftCVars_tvar htvar (n := n)) X

theorem Subst.eraseCVars_compatible_liftCVars_cvar {σ σe : Subst s1 s2}
    {K1 : CaptureSet s1} {K2 : CaptureSet s2}
    (hcvar : ∀ (a : Access) (c : BVar s1 .cvar),
      ((σ.cvar c).applyAccess a).eraseCVars K2
        = if K1.mentionsCVar c then {} else (σe.cvar c).applyAccess a) :
    {n : Nat} → ∀ (a : Access) (c : BVar (s1.extendCVars n) .cvar),
      (((σ.liftCVars n).cvar c).applyAccess a).eraseCVars
          (K2.rename (Rename.weakenCVars n))
        = if (K1.rename (Rename.weakenCVars n)).mentionsCVar c
          then {} else (((σe.liftCVars n).cvar c).applyAccess a)
  | 0, a, c => by
    have h : ((σ.cvar c).applyAccess a).eraseCVars (K2.rename Rename.id)
        = if (K1.rename Rename.id).mentionsCVar c
          then {} else (σe.cvar c).applyAccess a := by
      rw [show K1.rename Rename.id = K1 from CaptureSet.rename_id,
        show K2.rename Rename.id = K2 from CaptureSet.rename_id]
      exact hcvar a c
    simpa only [Rename.weakenCVars, Subst.liftCVars] using h
  | n + 1, a, c => by
    have hK1 : K1.rename (Rename.weakenCVars (n + 1))
        = (K1.rename (Rename.weakenCVars n)).rename (Rename.succ (k := .cvar)) := by
      rw [CaptureSet.rename_comp]
      rfl
    have hK2 : K2.rename (Rename.weakenCVars (n + 1))
        = (K2.rename (Rename.weakenCVars n)).rename (Rename.succ (k := .cvar)) := by
      rw [CaptureSet.rename_comp]
      rfl
    rw [hK1, hK2]
    exact Subst.eraseCVars_compatible_lift_cvar
      (σ := σ.liftCVars n) (σe := σe.liftCVars n) (k := .cvar)
      (Subst.eraseCVars_compatible_liftCVars_cvar hcvar (n := n)) a c

theorem Ty.eraseCVars_subst_compatible {T : Ty sort s1} {σ σe : Subst s1 s2}
    {K1 : CaptureSet s1} {K2 : CaptureSet s2}
    (hvar : ∀ (x : BVar s1 .var), σ.var x = σe.var x)
    (htvar : ∀ (X : BVar s1 .tvar), (σ.tvar X).eraseCVars K2 = σe.tvar X)
    (hcvar : ∀ (a : Access) (c : BVar s1 .cvar),
      ((σ.cvar c).applyAccess a).eraseCVars K2
        = if K1.mentionsCVar c then {} else (σe.cvar c).applyAccess a) :
    (T.subst σ).eraseCVars K2 = (T.eraseCVars K1).subst σe := by
  induction T generalizing s2 with
  | top => rfl
  | tvar X =>
    change ((σ.tvar X).eraseCVars K2).core = (σe.tvar X).core
    rw [htvar X]
  | unit => rfl
  | bool => rfl
  | cap C =>
    simp only [Ty.subst, Ty.eraseCVars, CaptureSet.eraseCVars_subst_compatible hvar hcvar]
  | arrow T1 C T2 ih1 ih2 =>
    have hbody : (T2.subst σ.lift).eraseCVars (K2.rename (Rename.succ (k := .var)))
        = (T2.eraseCVars (K1.rename (Rename.succ (k := .var)))).subst σe.lift :=
      ih2 (Subst.eraseCVars_compatible_lift_var hvar)
        (Subst.eraseCVars_compatible_lift_tvar htvar)
        (Subst.eraseCVars_compatible_lift_cvar hcvar)
    simp only [Ty.subst, Ty.eraseCVars, ih1 hvar htvar hcvar,
      CaptureSet.eraseCVars_subst_compatible hvar hcvar]
    congr 1
  | poly T1 C T2 ih1 ih2 =>
    have hbody : (T2.subst σ.lift).eraseCVars (K2.rename (Rename.succ (k := .tvar)))
        = (T2.eraseCVars (K1.rename (Rename.succ (k := .tvar)))).subst σe.lift :=
      ih2 (Subst.eraseCVars_compatible_lift_var hvar)
        (Subst.eraseCVars_compatible_lift_tvar htvar)
        (Subst.eraseCVars_compatible_lift_cvar hcvar)
    simp only [Ty.subst, Ty.eraseCVars, ih1 hvar htvar hcvar,
      CaptureSet.eraseCVars_subst_compatible hvar hcvar]
    congr 1
  | cpoly cb C T ih =>
    have hbody : (T.subst σ.lift).eraseCVars (K2.rename (Rename.succ (k := .cvar)))
        = (T.eraseCVars (K1.rename (Rename.succ (k := .cvar)))).subst σe.lift :=
      ih (Subst.eraseCVars_compatible_lift_var hvar)
        (Subst.eraseCVars_compatible_lift_tvar htvar)
        (Subst.eraseCVars_compatible_lift_cvar hcvar)
    simp only [Ty.subst, Ty.eraseCVars, CaptureBound.eraseCVars_subst_compatible hvar hcvar,
      CaptureSet.eraseCVars_subst_compatible hvar hcvar]
    congr 1
  | consumer T1 C T2 ih1 ih2 =>
    simp only [Ty.subst, Ty.eraseCVars, ih1 hvar htvar hcvar, ih2 hvar htvar hcvar,
      CaptureSet.eraseCVars_subst_compatible hvar hcvar]
  | modal C Ψ T ih =>
    simp only [Ty.subst, Ty.eraseCVars, CaptureSet.eraseCVars_subst_compatible hvar hcvar,
      ModalCtx.eraseCVars_subst_compatible hvar hcvar, ih hvar htvar hcvar]
  | cell C T ih =>
    simp only [Ty.subst, Ty.eraseCVars, CaptureSet.eraseCVars_subst_compatible hvar hcvar,
      ih hvar htvar hcvar]
  | reader C T ih =>
    simp only [Ty.subst, Ty.eraseCVars, CaptureSet.eraseCVars_subst_compatible hvar hcvar,
      ih hvar htvar hcvar]
  | exi n T ih =>
    have hbody : (T.subst (σ.liftCVars n)).eraseCVars (K2.rename (Rename.weakenCVars n))
        = (T.eraseCVars (K1.rename (Rename.weakenCVars n))).subst (σe.liftCVars n) :=
      ih (Subst.eraseCVars_compatible_liftCVars_var hvar)
        (Subst.eraseCVars_compatible_liftCVars_tvar htvar)
        (Subst.eraseCVars_compatible_liftCVars_cvar hcvar)
    simp only [Ty.subst, Ty.eraseCVars]
    congr 1
  | typ T ih =>
    simp only [Ty.subst, Ty.eraseCVars, ih hvar htvar hcvar]

theorem Ty.eraseCVars_subst_openVar {T : Ty sort (s,x)} {K : CaptureSet s} {y : Var .var s} :
    (T.subst (Subst.openVar y)).eraseCVars K
      = (T.eraseCVars (K.rename (Rename.succ (k := .var)))).subst (Subst.openVar y) := by
  apply Ty.eraseCVars_subst_compatible
  · intro x
    rfl
  · intro X
    cases X with
    | there X0 => rfl
  · intro a c
    cases c with
    | there c0 =>
      simp only [Subst.openVar, CaptureSet.applyAccess_cvar_epsilon, CaptureSet.eraseCVars_cvar]
      have hm : (K.rename (Rename.succ (k := .var))).mentionsCVar c0.there
          = K.mentionsCVar c0 := by
        simpa only [Rename.succ] using
          (CaptureSet.mentionsCVar_rename (K := K) (ρ := Rename.succ (k := .var))
            (c := c0) Rename.succ_cvarInjective)
      rw [← hm]
      cases K.mentionsCVar c0 <;> rfl

theorem Ty.eraseCVars_subst_openTVar {T : Ty sort (s,X)} {K : CaptureSet s} {S : PureTy s} :
    (T.subst (Subst.openTVar S)).eraseCVars K
      = (T.eraseCVars (K.rename (Rename.succ (k := .tvar)))).subst
          (Subst.openTVar (S.eraseCVars K)) :=
  by
    apply Ty.eraseCVars_subst_compatible
    · intro x
      cases x with
      | there x0 => rfl
    · intro X
      cases X with
      | here => rfl
      | there X0 => rfl
    · intro a c
      cases c with
      | there c0 =>
        simp only [Subst.openTVar, CaptureSet.applyAccess_cvar_epsilon, CaptureSet.eraseCVars_cvar]
        have hm : (K.rename (Rename.succ (k := .tvar))).mentionsCVar c0.there
            = K.mentionsCVar c0 := by
          simpa only [Rename.succ] using
            (CaptureSet.mentionsCVar_rename (K := K) (ρ := Rename.succ (k := .tvar))
              (c := c0) Rename.succ_cvarInjective)
        rw [← hm]
        cases K.mentionsCVar c0 <;> rfl

theorem Ty.eraseCVars_subst_openCVar {T : Ty sort (s,C)} {K : CaptureSet s} {D : CaptureSet s} :
    (T.subst (Subst.openCVar D)).eraseCVars K
      = (T.eraseCVars (K.rename (Rename.succ (k := .cvar)))).subst
          (Subst.openCVar (D.eraseCVars K)) :=
  by
    apply Ty.eraseCVars_subst_compatible
    · intro x
      cases x with
      | there x0 => rfl
    · intro X
      cases X with
      | there X0 => rfl
    · intro a c
      cases c with
      | here =>
        change (D.applyAccess a).eraseCVars K
          = if (K.rename (Rename.succ (k := .cvar))).mentionsCVar BVar.here
            then {} else (D.eraseCVars K).applyAccess a
        rw [CaptureSet.mentionsCVar_rename_succ_here]
        simp only [Bool.false_eq_true, ↓reduceIte]
        exact CaptureSet.eraseCVars_applyAccess
      | there c0 =>
        simp only [Subst.openCVar, CaptureSet.applyAccess_cvar_epsilon,
          CaptureSet.eraseCVars_cvar]
        have hm : (K.rename (Rename.succ (k := .cvar))).mentionsCVar c0.there
            = K.mentionsCVar c0 := by
          simpa only [Rename.succ] using
            (CaptureSet.mentionsCVar_rename (K := K) (ρ := Rename.succ (k := .cvar))
              (c := c0) Rename.succ_cvarInjective)
        rw [← hm]
        cases K.mentionsCVar c0 <;> rfl

theorem CaptureSet.unionAll_eraseCVars {n : Nat} {Cs : List.Vector (CaptureSet s) n}
    {K : CaptureSet s} :
    CaptureSet.unionAll (Cs.map (·.eraseCVars K)) = (CaptureSet.unionAll Cs).eraseCVars K := by
  induction n with
  | zero =>
    rw [List.Vector.eq_nil Cs]
    rfl
  | succ n ih =>
    change (List.Vector.head (Cs.map (fun C => C.eraseCVars K))
        ∪ CaptureSet.unionAll (List.Vector.tail (Cs.map (fun C => C.eraseCVars K))))
      = (List.Vector.head Cs ∪ CaptureSet.unionAll (List.Vector.tail Cs)).eraseCVars K
    obtain ⟨l, hl⟩ := Cs
    cases l with
    | nil => cases hl
    | cons C l' =>
      have htl : l'.length = n := by
        simpa using Nat.succ.inj hl
      change C.eraseCVars K ∪
          CaptureSet.unionAll (List.Vector.map (fun C => C.eraseCVars K) ⟨l', htl⟩)
        = (C.eraseCVars K) ∪ (CaptureSet.unionAll ⟨l', htl⟩).eraseCVars K
      rw [ih]

theorem Subst.openCVars_eraseCVars_var {K : CaptureSet s} :
    {n : Nat} → {Cs : List.Vector (CaptureSet s) n} →
      ∀ (x : BVar (s.extendCVars n) .var),
        (Subst.openCVars Cs).var x
          = (Subst.openCVars (Cs.map (·.eraseCVars K))).var x
  | 0, Cs, x => rfl
  | n + 1, Cs, x => by
    cases x with
    | there x0 =>
      change (Subst.openCVars Cs.tail).var x0
        = (Subst.openCVars (Cs.map (fun C => C.eraseCVars K)).tail).var x0
      rw [List.Vector.tail_map]
      exact Subst.openCVars_eraseCVars_var (K := K) (Cs := Cs.tail) x0

theorem Subst.openCVars_eraseCVars_tvar {K : CaptureSet s} :
    {n : Nat} → {Cs : List.Vector (CaptureSet s) n} →
      ∀ (X : BVar (s.extendCVars n) .tvar),
        ((Subst.openCVars Cs).tvar X).eraseCVars K
          = (Subst.openCVars (Cs.map (·.eraseCVars K))).tvar X
  | 0, Cs, X => rfl
  | n + 1, Cs, X => by
    cases X with
    | there X0 =>
      change ((Subst.openCVars Cs.tail).tvar X0).eraseCVars K
        = (Subst.openCVars (Cs.map (fun C => C.eraseCVars K)).tail).tvar X0
      rw [List.Vector.tail_map]
      exact Subst.openCVars_eraseCVars_tvar (K := K) (Cs := Cs.tail) X0

theorem Subst.openCVars_eraseCVars_cvar {K : CaptureSet s} :
    {n : Nat} → {Cs : List.Vector (CaptureSet s) n} →
      ∀ (a : Access) (c : BVar (s.extendCVars n) .cvar),
        (((Subst.openCVars Cs).cvar c).applyAccess a).eraseCVars K
          = if (K.rename (Rename.weakenCVars n)).mentionsCVar c
            then {} else (((Subst.openCVars (Cs.map (·.eraseCVars K))).cvar c).applyAccess a)
  | 0, Cs, a, c => by
    change ((CaptureSet.cvar (.M .epsilon) c).applyAccess a).eraseCVars K
      = if (K.rename (Rename.weakenCVars 0)).mentionsCVar c
        then {} else (CaptureSet.cvar (.M .epsilon) c).applyAccess a
    have hK : (K.rename (Rename.weakenCVars 0)).mentionsCVar c = K.mentionsCVar c := by
      have hrename : K.rename (Rename.weakenCVars 0) = K := by
        simpa only [Rename.weakenCVars] using (CaptureSet.rename_id (cs := K))
      rw [hrename]
      rfl
    rw [CaptureSet.applyAccess_cvar_epsilon, CaptureSet.eraseCVars_cvar, hK]
    rfl
  | n + 1, Cs, a, c => by
    have hK : K.rename (Rename.weakenCVars (n + 1))
        = (K.rename (Rename.weakenCVars n)).rename (Rename.succ (k := .cvar)) := by
      rw [CaptureSet.rename_comp]
      rfl
    cases c with
    | here =>
      change ((Cs.head.applyAccess a).eraseCVars K)
        = if (K.rename (Rename.weakenCVars (n + 1))).mentionsCVar BVar.here
          then {} else ((Cs.map (fun C : CaptureSet s => C.eraseCVars K)).head.applyAccess a)
      rw [hK, List.Vector.head_map]
      have hfalse : ((K.rename (Rename.weakenCVars n)).rename
          (Rename.succ (k := .cvar))).mentionsCVar BVar.here = false :=
        CaptureSet.mentionsCVar_rename_succ_here
      rw [if_neg (by
        intro htrue
        have hbad : false = true := hfalse.symm.trans htrue
        cases hbad)]
      exact CaptureSet.eraseCVars_applyAccess
    | there c0 =>
      have hm : (K.rename (Rename.weakenCVars (n + 1))).mentionsCVar c0.there
          = (K.rename (Rename.weakenCVars n)).mentionsCVar c0 := by
        rw [hK]
        simpa only [Rename.succ] using
          (CaptureSet.mentionsCVar_rename (K := K.rename (Rename.weakenCVars n))
            (ρ := Rename.succ (k := .cvar)) (c := c0) Rename.succ_cvarInjective)
      change (((Subst.openCVars Cs.tail).cvar c0).applyAccess a).eraseCVars K
        = if (K.rename (Rename.weakenCVars (n + 1))).mentionsCVar c0.there
          then {}
          else (((Subst.openCVars (Cs.map (fun C => C.eraseCVars K)).tail).cvar c0).applyAccess a)
      rw [hm, List.Vector.tail_map]
      exact Subst.openCVars_eraseCVars_cvar (K := K) (Cs := Cs.tail) a c0

theorem Ty.eraseCVars_subst_openCVars {n : Nat} {T : Ty sort (s.extendCVars n)} {K : CaptureSet s}
    {Cs : List.Vector (CaptureSet s) n} :
    (T.subst (Subst.openCVars Cs)).eraseCVars K
      = (T.eraseCVars (K.rename (Rename.weakenCVars n))).subst
          (Subst.openCVars (Cs.map (·.eraseCVars K))) := by
  apply Ty.eraseCVars_subst_compatible
  · exact Subst.openCVars_eraseCVars_var (K := K)
  · exact Subst.openCVars_eraseCVars_tvar (K := K)
  · exact Subst.openCVars_eraseCVars_cvar (K := K)

/- Item 10: captureSet / refineCaptureSet / core commute with erasure. -/
theorem Ty.refineCaptureSet_eraseCVars {T : Ty .capt s} {C K : CaptureSet s} :
    (T.refineCaptureSet C).eraseCVars K = (T.eraseCVars K).refineCaptureSet (C.eraseCVars K) := by
  cases T <;> rfl

@[simp] theorem PureTy.core_eraseCVars {T : PureTy s} {K : CaptureSet s} :
    (T.eraseCVars K).core = T.core.eraseCVars K := rfl

/-! ## §3 Layer B — context erasure + kill -/

/- Item 11: lookup-erasure.  At `.here`/`.there` the looked-up payload is `·.rename succ`;
   the erased context pushes `b.eraseCVars K.strip1`, so the result reconciles via the
   `eraseCVars_rename_succ` family (strip1 round-trip). -/
theorem Ctx.LookupVar.eraseCVars {Γ : Ctx s} {x : BVar s .var} {T : Ty .capt s} {K : CaptureSet s}
    (h : Γ.LookupVar x T) : (Γ.eraseCVars K).LookupVar x (T.eraseCVars K) := by
  induction h with
  | here => rw [Ty.eraseCVars_rename_succ]; exact Ctx.LookupVar.here
  | there _ ih => rw [Ty.eraseCVars_rename_succ]; exact Ctx.LookupVar.there ih

theorem Ctx.LookupTVar.eraseCVars {Γ : Ctx s} {X : BVar s .tvar} {S : PureTy s} {K : CaptureSet s}
    (h : Γ.LookupTVar X S) : (Γ.eraseCVars K).LookupTVar X (S.eraseCVars K) := by
  induction h with
  | here => rw [PureTy.eraseCVars_rename_succ]; exact Ctx.LookupTVar.here
  | there _ ih => rw [PureTy.eraseCVars_rename_succ]; exact Ctx.LookupTVar.there ih

theorem Ctx.LookupCVar.eraseCVars {Γ : Ctx s} {c : BVar s .cvar} {a : Authority}
    {cb : CaptureBound s} {K : CaptureSet s}
    (h : Γ.LookupCVar c a cb) : (Γ.eraseCVars K).LookupCVar c a (cb.eraseCVars K) := by
  induction h with
  | here => rw [CaptureBound.eraseCVars_rename_succ]; exact Ctx.LookupCVar.here
  | there _ ih => rw [CaptureBound.eraseCVars_rename_succ]; exact Ctx.LookupCVar.there ih

theorem Ctx.LookupLock.eraseCVars {Γ : Ctx s} {ℓ : BVar s .lock} {Ψ : ModalCtx s} {K : CaptureSet s}
    (h : Γ.LookupLock ℓ Ψ) : (Γ.eraseCVars K).LookupLock ℓ (Ψ.eraseCVars K) := by
  induction h with
  | here => rw [ModalCtx.eraseCVars_rename_succ]; exact Ctx.LookupLock.here
  | there _ ih => rw [ModalCtx.eraseCVars_rename_succ]; exact Ctx.LookupLock.there ih

/- Item 12: kill–erasure commutation.  Erasure edits payloads, killing edits authorities;
   they touch disjoint fields, so they commute. -/
theorem Ctx.eraseCVars_kill_cvar {Γ : Ctx s} {c : BVar s .cvar} {K : CaptureSet s} :
    (Γ.eraseCVars K).kill_cvar c = (Γ.kill_cvar c).eraseCVars K := by
  induction Γ with
  | empty => cases c
  | push Γ' b ih =>
    cases c with
    | here => cases b with
      | cvar a cb => simp only [Ctx.eraseCVars, Binding.eraseCVars, Ctx.kill_cvar]
    | there c' =>
      simp only [Ctx.eraseCVars, Ctx.kill_cvar]
      rw [ih]

theorem Ctx.eraseCVars_kill_peaks_cs {Γ : Ctx s} {K P : CaptureSet s} :
    (Γ.eraseCVars K).kill_peaks_cs P = (Γ.kill_peaks_cs P).eraseCVars K := by
  induction P generalizing Γ with
  | empty => rfl
  | union P1 P2 ih1 ih2 =>
    simp only [Ctx.kill_peaks_cs]
    rw [ih1, ih2]
  | cvar a c => exact Ctx.eraseCVars_kill_cvar
  | var a v => rfl

/- Item 13: kill composition / absorption. -/
private theorem Ctx.kill_cvar_comm {Γ : Ctx s} {c1 c2 : BVar s .cvar} :
    (Γ.kill_cvar c1).kill_cvar c2 = (Γ.kill_cvar c2).kill_cvar c1 := by
  induction Γ with
  | empty => cases c1
  | push Γ b ih =>
    cases c1 with
    | here =>
      cases b with
      | cvar a cb =>
        cases c2 with
        | here => rfl
        | there c2 => rfl
    | there c1 =>
      cases c2 with
      | here =>
        cases b with
        | cvar a cb => rfl
      | there c2 =>
        simp only [Ctx.kill_cvar]
        rw [ih]

private theorem Ctx.kill_peaks_cs_kill_cvar_comm {Γ : Ctx s} {K : CaptureSet s}
    {c : BVar s .cvar} :
    (Γ.kill_peaks_cs K).kill_cvar c = (Γ.kill_cvar c).kill_peaks_cs K := by
  induction K generalizing Γ with
  | empty => rfl
  | union K1 K2 ih1 ih2 =>
    simp only [Ctx.kill_peaks_cs]
    rw [ih2, ih1]
  | cvar a c' => exact Ctx.kill_cvar_comm
  | var a x => rfl

theorem Ctx.kill_peaks_cs_comm {Γ : Ctx s} {K P : CaptureSet s} :
    (Γ.kill_peaks_cs K).kill_peaks_cs P = (Γ.kill_peaks_cs P).kill_peaks_cs K := by
  induction P generalizing Γ with
  | empty => rfl
  | union P1 P2 ih1 ih2 =>
    simp only [Ctx.kill_peaks_cs]
    rw [ih1, ih2]
  | cvar a c => exact Ctx.kill_peaks_cs_kill_cvar_comm
  | var a x => rfl

private theorem Ctx.kill_cvar_of_killed {Γ : Ctx s} {c : BVar s .cvar}
    (h : Γ.lookup_authority c = .killed) : Γ.kill_cvar c = Γ := by
  induction Γ with
  | empty => cases c
  | push Γ b ih =>
    cases c with
    | here =>
      cases b with
      | cvar a cb =>
        simp only [Ctx.lookup_authority] at h
        subst h
        rfl
    | there c =>
      simp only [Ctx.lookup_authority] at h
      simp only [Ctx.kill_cvar]
      rw [ih h]

private theorem Ctx.kill_peaks_cs_lookup_authority_not_mentioned_early {Γ : Ctx s}
    {K : CaptureSet s} {c : BVar s .cvar} (hc : K.mentionsCVar c = false) :
    (Γ.kill_peaks_cs K).lookup_authority c = Γ.lookup_authority c := by
  induction K generalizing Γ with
  | empty => rfl
  | union K1 K2 ih1 ih2 =>
    simp only [CaptureSet.mentionsCVar, Bool.or_eq_false_iff] at hc
    simp only [Ctx.kill_peaks_cs]
    rw [ih2 hc.2, ih1 hc.1]
  | var a x => rfl
  | cvar a c' =>
    simp only [Ctx.kill_peaks_cs]
    refine Ctx.kill_cvar_lookup_authority_ne Γ (fun heq => ?_)
    simp only [CaptureSet.mentionsCVar, heq, BVar.beq_self] at hc
    cases hc

private theorem Ctx.kill_peaks_cs_lookup_authority_of_mentions {Γ : Ctx s}
    {K : CaptureSet s} {c : BVar s .cvar} (h : K.mentionsCVar c = true) :
    (Γ.kill_peaks_cs K).lookup_authority c = .killed := by
  induction K generalizing Γ with
  | empty =>
    simp only [CaptureSet.mentionsCVar] at h
    cases h
  | union K1 K2 ih1 ih2 =>
    simp only [CaptureSet.mentionsCVar, Bool.or_eq_true] at h
    simp only [Ctx.kill_peaks_cs]
    rcases h with h1 | h2
    · by_cases hK2 : K2.mentionsCVar c = true
      · exact ih2 hK2
      · rw [Bool.not_eq_true] at hK2
        rw [Ctx.kill_peaks_cs_lookup_authority_not_mentioned_early hK2]
        exact ih1 h1
    · exact ih2 h2
  | cvar a c' =>
    simp only [CaptureSet.mentionsCVar] at h
    have heq : c' = c := BVar.eq_of_beq c' c h
    subst c'
    exact Ctx.kill_cvar_lookup_authority_self Γ c
  | var a x =>
    simp only [CaptureSet.mentionsCVar] at h
    cases h

theorem Ctx.kill_peaks_cs_absorb_eraseCVars {Γ : Ctx s} {K P : CaptureSet s} :
    (Γ.kill_peaks_cs K).kill_peaks_cs (P.eraseCVars K)
      = (Γ.kill_peaks_cs K).kill_peaks_cs P := by
  induction P generalizing Γ K with
  | empty => rfl
  | union P1 P2 ih1 ih2 =>
    simp only [CaptureSet.eraseCVars_union, Ctx.kill_peaks_cs]
    rw [ih1]
    have hcomm1 :
        (Γ.kill_peaks_cs K).kill_peaks_cs P1
          = (Γ.kill_peaks_cs P1).kill_peaks_cs K :=
      Ctx.kill_peaks_cs_comm
    rw [hcomm1]
    rw [ih2]
  | cvar a c =>
    by_cases hm : K.mentionsCVar c = true
    · simp only [CaptureSet.eraseCVars_cvar_pos hm, Ctx.kill_peaks_cs]
      exact (Ctx.kill_cvar_of_killed
        (Ctx.kill_peaks_cs_lookup_authority_of_mentions (Γ := Γ) hm)).symm
    · rw [Bool.not_eq_true] at hm
      simp only [CaptureSet.eraseCVars_cvar_neg hm]
  | var a x => rfl

/- Item 14: kill/erase commute with the context extensions. -/
/-- Pushing a binding commutes with killing a `succ`-weakened set: the weakened kill set
    has only `.there` cvar atoms, which `kill_cvar` routes past the fresh head binding. -/
theorem Ctx.kill_peaks_cs_push {Γ : Ctx s} {b : Binding s k} {K : CaptureSet s} :
    (Γ.push b).kill_peaks_cs (K.rename (Rename.succ (k := k))) = (Γ.kill_peaks_cs K).push b := by
  induction K generalizing Γ with
  | empty => rfl
  | union K1 K2 ih1 ih2 => simp only [CaptureSet.rename, Ctx.kill_peaks_cs, ih1, ih2]
  | var m x => rfl
  | cvar m c => simp only [CaptureSet.rename, Ctx.kill_peaks_cs, Rename.succ, Ctx.kill_cvar]

theorem Ctx.kill_peaks_cs_push_var {Γ : Ctx s} {T : Ty .capt s} {K : CaptureSet s} :
    (Γ,x:T).kill_peaks_cs (K.rename (Rename.succ (k := .var))) = (Γ.kill_peaks_cs K),x:T :=
  Ctx.kill_peaks_cs_push

theorem Ctx.kill_peaks_cs_push_tvar {Γ : Ctx s} {S : PureTy s} {K : CaptureSet s} :
    (Γ,X<:S).kill_peaks_cs (K.rename (Rename.succ (k := .tvar))) = (Γ.kill_peaks_cs K),X<:S :=
  Ctx.kill_peaks_cs_push

theorem Ctx.kill_peaks_cs_push_cvar {Γ : Ctx s} {a : Authority} {cb : CaptureBound s}
    {K : CaptureSet s} :
    (Γ,C[a]<:cb).kill_peaks_cs (K.rename (Rename.succ (k := .cvar)))
      = (Γ.kill_peaks_cs K),C[a]<:cb :=
  Ctx.kill_peaks_cs_push

theorem Ctx.kill_peaks_cs_push_lock {Γ : Ctx s} {Ψ : ModalCtx s} {K : CaptureSet s} :
    (Γ.push_lock Ψ).kill_peaks_cs (K.rename (Rename.succ (k := .lock)))
      = (Γ.kill_peaks_cs K).push_lock Ψ :=
  Ctx.kill_peaks_cs_push

theorem Ctx.kill_peaks_cs_extendCVars {Γ : Ctx s} {a : Authority} {K : CaptureSet s} {n : Nat} :
    (Ctx.extendCVars a Γ n).kill_peaks_cs (K.rename (Rename.weakenCVars n))
      = Ctx.extendCVars a (Γ.kill_peaks_cs K) n := by
  induction n with
  | zero => simp only [Ctx.extendCVars, Rename.weakenCVars, Sig.extendCVars, CaptureSet.rename_id]
  | succ n ih =>
    have hK : K.rename (Rename.weakenCVars (n + 1))
        = (K.rename (Rename.weakenCVars n)).rename (Rename.succ (k := .cvar)) := by
      rw [CaptureSet.rename_comp]; rfl
    simp only [Ctx.extendCVars, Ctx.push_cvar, hK]
    refine Ctx.kill_peaks_cs_push.trans ?_
    rw [ih]

/-- General push–erase commutation: the fresh binding's kill set strips back to `K`.
    Stated over `s,,k` (= `Sig.extend s k`) so `strip1_rename_succ` matches syntactically;
    the notation variants below follow definitionally. -/
theorem Ctx.eraseCVars_push {Γ : Ctx s} {b : Binding s k} {K : CaptureSet s} :
    (Γ.push b).eraseCVars (K.rename (Rename.succ (k := k)))
      = (Γ.eraseCVars K).push (b.eraseCVars K) := by
  simp only [Ctx.eraseCVars]
  rw [CaptureSet.strip1_rename_succ]

theorem Ctx.eraseCVars_push_var {Γ : Ctx s} {T : Ty .capt s} {K : CaptureSet s} :
    (Γ,x:T).eraseCVars (K.rename (Rename.succ (k := .var)))
      = (Γ.eraseCVars K),x:(T.eraseCVars K) :=
  Ctx.eraseCVars_push

theorem Ctx.eraseCVars_push_tvar {Γ : Ctx s} {S : PureTy s} {K : CaptureSet s} :
    (Γ,X<:S).eraseCVars (K.rename (Rename.succ (k := .tvar)))
      = (Γ.eraseCVars K),X<:(S.eraseCVars K) :=
  Ctx.eraseCVars_push

theorem Ctx.eraseCVars_push_cvar {Γ : Ctx s} {a : Authority} {cb : CaptureBound s}
    {K : CaptureSet s} :
    (Γ,C[a]<:cb).eraseCVars (K.rename (Rename.succ (k := .cvar)))
      = (Γ.eraseCVars K),C[a]<:(cb.eraseCVars K) :=
  Ctx.eraseCVars_push

theorem Ctx.eraseCVars_push_lock {Γ : Ctx s} {Ψ : ModalCtx s} {K : CaptureSet s} :
    (Γ.push_lock Ψ).eraseCVars (K.rename (Rename.succ (k := .lock)))
      = (Γ.eraseCVars K).push_lock (Ψ.eraseCVars K) :=
  Ctx.eraseCVars_push

theorem Ctx.eraseCVars_extendCVars {Γ : Ctx s} {a : Authority} {K : CaptureSet s} {n : Nat} :
    (Ctx.extendCVars a Γ n).eraseCVars (K.rename (Rename.weakenCVars n))
      = Ctx.extendCVars a (Γ.eraseCVars K) n := by
  induction n with
  | zero => simp only [Ctx.extendCVars, Rename.weakenCVars, Sig.extendCVars, CaptureSet.rename_id]
  | succ n ih =>
    have hK : K.rename (Rename.weakenCVars (n + 1))
        = (K.rename (Rename.weakenCVars n)).rename (Rename.succ (k := .cvar)) := by
      rw [CaptureSet.rename_comp]; rfl
    simp only [Ctx.extendCVars, Ctx.push_cvar, hK]
    refine Ctx.eraseCVars_push.trans ?_
    simp only [Binding.eraseCVars, CaptureBound.eraseCVars, ih]

/- Item 15: peaks-erasure (mutual with peaksVarBound).  Erasing cvars from context and set
   commutes with resolving peaks: killed cvar atoms erase to `{}` before and after resolution,
   and the transported kill set aligns through the binder via `eraseCVars_rename_succ`. -/
mutual
theorem CaptureSet.peaksVarBound_eraseCVars (Γ : Ctx s) (a : Access) (x : BVar s .var)
    (K : CaptureSet s) :
    CaptureSet.peaksVarBound (Γ.eraseCVars K) a x
      = (CaptureSet.peaksVarBound Γ a x).eraseCVars K := by
  match Γ, x, K with
  | .push Γ' (.var T), .here, K =>
    simp only [Ctx.eraseCVars, Binding.eraseCVars]
    rw [CaptureSet.peaksVarBound, CaptureSet.peaksVarBound, Ty.captureSet_eraseCVars,
      CaptureSet.peaks_eraseCVars, CaptureSet.eraseCVars_applyAccess,
      CaptureSet.eraseCVars_rename_succ]
  | .push Γ' b, .there x', K =>
    simp only [Ctx.eraseCVars]
    rw [CaptureSet.peaksVarBound, CaptureSet.peaksVarBound,
      CaptureSet.peaksVarBound_eraseCVars, CaptureSet.eraseCVars_rename_succ]
termination_by (sizeOf Γ, sizeOf x + 1)

theorem CaptureSet.peaks_eraseCVars (Γ : Ctx s) (C : CaptureSet s) (K : CaptureSet s) :
    CaptureSet.peaks (Γ.eraseCVars K) (C.eraseCVars K) = (CaptureSet.peaks Γ C).eraseCVars K := by
  match Γ, C with
  | Γ, .empty =>
    rw [CaptureSet.eraseCVars_empty, CaptureSet.peaks, CaptureSet.peaks,
      CaptureSet.eraseCVars_empty]
  | Γ, .union cs1 cs2 =>
    rw [CaptureSet.peaks, CaptureSet.eraseCVars_union, CaptureSet.peaks,
      CaptureSet.peaks_eraseCVars, CaptureSet.peaks_eraseCVars]
    exact CaptureSet.eraseCVars_union.symm
  | Γ, .cvar m c =>
    have key : CaptureSet.peaks (Γ.eraseCVars K) ((CaptureSet.cvar m c).eraseCVars K)
        = (CaptureSet.cvar m c).eraseCVars K := by
      by_cases hm : K.mentionsCVar c = true
      · simp only [CaptureSet.eraseCVars_cvar_pos hm]
        change CaptureSet.peaks (Γ.eraseCVars K) CaptureSet.empty = CaptureSet.empty
        rw [CaptureSet.peaks]
      · rw [Bool.not_eq_true] at hm
        simp only [CaptureSet.eraseCVars_cvar_neg hm]
        rw [CaptureSet.peaks]
    rw [key, CaptureSet.peaks]
  | Γ, .var m (.free n) =>
    rw [CaptureSet.eraseCVars_var, CaptureSet.peaks, CaptureSet.peaks]
    exact CaptureSet.eraseCVars_empty.symm
  | Γ, .var m (.bound x) =>
    rw [CaptureSet.eraseCVars_var, CaptureSet.peaks, CaptureSet.peaks]
    exact CaptureSet.peaksVarBound_eraseCVars Γ m x K
termination_by (sizeOf Γ, sizeOf C)
end

/- Lookup-authority under erase / kill (hoisted from item 19 — needed by item 16's
   accessible/droppable and by item 19's TwoDistinctDroppable). -/
theorem Ctx.eraseCVars_lookup_authority {s : Sig} (Γ : Ctx s) (c : BVar s .cvar)
    (K : CaptureSet s) :
    (Γ.eraseCVars K).lookup_authority c = Γ.lookup_authority c := by
  induction Γ with
  | empty => cases c
  | push Γ' b ih =>
    cases c with
    | here => cases b with | cvar a cb => rfl
    | there c' =>
      simp only [Ctx.eraseCVars, Ctx.lookup_authority]
      exact ih c' K.strip1

theorem Ctx.kill_peaks_cs_lookup_authority_not_mentioned {Γ : Ctx s} {K : CaptureSet s}
    {c : BVar s .cvar} (hc : K.mentionsCVar c = false) :
    (Γ.kill_peaks_cs K).lookup_authority c = Γ.lookup_authority c := by
  induction K generalizing Γ with
  | empty => rfl
  | union K1 K2 ih1 ih2 =>
    simp only [CaptureSet.mentionsCVar, Bool.or_eq_false_iff] at hc
    simp only [Ctx.kill_peaks_cs]
    rw [ih2 hc.2, ih1 hc.1]
  | var m x => rfl
  | cvar m c' =>
    simp only [Ctx.kill_peaks_cs]
    refine Ctx.kill_cvar_lookup_authority_ne Γ (fun heq => ?_)
    simp only [CaptureSet.mentionsCVar, heq, BVar.beq_self] at hc
    exact Bool.noConfusion hc

/- Item 16: consequences for the peak-predicates. -/
theorem CaptureSet.consumed_eraseCVars {C K : CaptureSet s} :
    (C.eraseCVars K).consumed = C.consumed.eraseCVars K := by
  induction C with
  | empty => rfl
  | union C1 C2 ih1 ih2 =>
    simp only [CaptureSet.eraseCVars_union, CaptureSet.consumed, ih1, ih2]
  | var m x => rfl
  | cvar m c =>
    cases m with
    | M m =>
      by_cases hm : K.mentionsCVar c = true
      · simp [CaptureSet.eraseCVars_cvar_pos hm, CaptureSet.consumed]
      · have hn : K.mentionsCVar c = false := by
          rw [Bool.not_eq_true] at hm
          exact hm
        simp [CaptureSet.eraseCVars_cvar_neg hn, CaptureSet.consumed]
    | drop =>
      by_cases hm : K.mentionsCVar c = true
      · rw [CaptureSet.eraseCVars_cvar_pos hm]
        simp only [CaptureSet.consumed]
        rw [CaptureSet.eraseCVars_cvar_pos hm]
        exact (show (CaptureSet.empty : CaptureSet s) = ∅ from rfl)
      · have hn : K.mentionsCVar c = false := by
          rw [Bool.not_eq_true] at hm
          exact hm
        simp [CaptureSet.eraseCVars_cvar_neg hn, CaptureSet.consumed]

/-- Peaks of the erased-and-killed target context are the erased original peaks
    (killing does not move peaks — `peaks_kill_peaks_cs` — and erasure commutes with
    peaks — lemma 15). -/
theorem CaptureSet.peaks_eraseCVars_kill {Γ : Ctx s} {C K : CaptureSet s} :
    CaptureSet.peaks ((Γ.eraseCVars K).kill_peaks_cs K) (C.eraseCVars K)
      = (CaptureSet.peaks Γ C).eraseCVars K := by
  rw [CaptureSet.peaks_kill_peaks_cs, CaptureSet.peaks_eraseCVars]

theorem CaptureSet.AccessOnly.eraseCVars {Γ : Ctx s} {C : CaptureSet s} {K : CaptureSet s}
    (h : C.AccessOnly Γ) :
    (C.eraseCVars K).AccessOnly ((Γ.eraseCVars K).kill_peaks_cs K) := by
  intro c hsub
  have hsub' : (CaptureSet.cvar .drop c) ⊆ (CaptureSet.peaks Γ C).eraseCVars K := by
    rw [← CaptureSet.peaks_eraseCVars_kill]; exact hsub
  obtain ⟨hsub0, _⟩ := CaptureSet.cvar_subset_eraseCVars_inv hsub'
  exact h c hsub0

theorem CaptureSet.accessible.eraseCVars {Γ : Ctx s} {C : CaptureSet s} {K : CaptureSet s}
    (h : C.accessible Γ) :
    (C.eraseCVars K).accessible ((Γ.eraseCVars K).kill_peaks_cs K) := by
  intro a c hsub
  have hsub' : (CaptureSet.cvar a c) ⊆ (CaptureSet.peaks Γ C).eraseCVars K := by
    rw [← CaptureSet.peaks_eraseCVars_kill]; exact hsub
  obtain ⟨hsub0, hK⟩ := CaptureSet.cvar_subset_eraseCVars_inv hsub'
  rw [Ctx.kill_peaks_cs_lookup_authority_not_mentioned hK, Ctx.eraseCVars_lookup_authority]
  exact h a c hsub0

theorem CaptureSet.droppable.eraseCVars {Γ : Ctx s} {C : CaptureSet s} {K : CaptureSet s}
    (h : C.droppable Γ) :
    (C.eraseCVars K).droppable ((Γ.eraseCVars K).kill_peaks_cs K) := by
  intro a c hsub
  have hsub' : (CaptureSet.cvar a c) ⊆ (CaptureSet.peaks Γ C).eraseCVars K := by
    rw [← CaptureSet.peaks_eraseCVars_kill]; exact hsub
  obtain ⟨hsub0, hK⟩ := CaptureSet.cvar_subset_eraseCVars_inv hsub'
  rw [Ctx.kill_peaks_cs_lookup_authority_not_mentioned hK, Ctx.eraseCVars_lookup_authority]
  exact h a c hsub0

theorem CaptureBound.IsValid.eraseCVars {Γ : Ctx s} {cb : CaptureBound s} {K : CaptureSet s}
    (h : cb.IsValid Γ) :
    (cb.eraseCVars K).IsValid ((Γ.eraseCVars K).kill_peaks_cs K) := by
  cases cb with
  | unbound => exact True.intro
  | bound C => exact CaptureSet.AccessOnly.eraseCVars h

theorem CaptureSet.SubP.eraseCVars {Γ : Ctx s} {C1 C2 : CaptureSet s} {K : CaptureSet s}
    (h : CaptureSet.SubP Γ C1 C2) :
    CaptureSet.SubP ((Γ.eraseCVars K).kill_peaks_cs K) (C1.eraseCVars K) (C2.eraseCVars K) := by
  unfold CaptureSet.SubP at h ⊢
  rw [CaptureSet.peaks_eraseCVars_kill, CaptureSet.peaks_eraseCVars_kill]
  exact h.eraseCVars

theorem CaptureSet.EquivP.eraseCVars {Γ : Ctx s} {C1 C2 : CaptureSet s} {K : CaptureSet s}
    (h : CaptureSet.EquivP Γ C1 C2) :
    CaptureSet.EquivP ((Γ.eraseCVars K).kill_peaks_cs K) (C1.eraseCVars K) (C2.eraseCVars K) :=
  ⟨h.1.eraseCVars, h.2.eraseCVars⟩

/- Item 17: `Ctx.IsClosed` preserved by erase (kill covered by the moved lemma). -/
theorem Binding.IsClosed.eraseCVars {b : Binding s k} (h : b.IsClosed) (K : CaptureSet s) :
    (b.eraseCVars K).IsClosed := by
  cases h with
  | var hT => exact .var (hT.eraseCVars K)
  | tvar hT => exact .tvar (hT.eraseCVars K)
  | cvar hcb => exact .cvar (hcb.eraseCVars K)
  | lock hΨ => exact .lock (hΨ.eraseCVars K)

theorem Ctx.IsClosed.eraseCVars {Γ : Ctx s} (h : Γ.IsClosed) (K : CaptureSet s) :
    (Γ.eraseCVars K).IsClosed := by
  induction h with
  | empty => exact .empty
  | push _ hb ih => exact .push (ih _) (hb.eraseCVars _)

/- Item 18: modal-context membership erasure (forward + inversion). -/
theorem SepCtx.Has.eraseCVars {K0 : SepCtx s} {C : CaptureSet s} {K : CaptureSet s}
    (h : K0.Has C) : (K0.eraseCVars K).Has (C.eraseCVars K) := by
  induction h with
  | here => exact .here
  | there _ ih => exact .there ih

theorem SepCtx.Has.eraseCVars_inv {K0 : SepCtx s} {C : CaptureSet s} {K : CaptureSet s}
    (h : (K0.eraseCVars K).Has C) : ∃ C0, C = C0.eraseCVars K ∧ K0.Has C0 := by
  induction K0 with
  | empty => cases h
  | cons K1 C0 ih =>
    simp only [SepCtx.eraseCVars] at h
    cases h with
    | here => exact ⟨C0, rfl, .here⟩
    | there h' => obtain ⟨C1, hC1, hh⟩ := ih h'; exact ⟨C1, hC1, .there hh⟩

theorem MutabilityCtx.Has.eraseCVars {K0 : MutabilityCtx s} {C : CaptureSet s} {m : Mutability}
    {K : CaptureSet s} (h : K0.Has C m) : (K0.eraseCVars K).Has (C.eraseCVars K) m := by
  induction h with
  | here => exact .here
  | there _ ih => exact .there ih

theorem MutabilityCtx.Has.eraseCVars_inv {K0 : MutabilityCtx s} {C : CaptureSet s} {m : Mutability}
    {K : CaptureSet s} (h : (K0.eraseCVars K).Has C m) :
    ∃ C0, C = C0.eraseCVars K ∧ K0.Has C0 m := by
  induction K0 with
  | empty => cases h
  | cons K0' C' m' ih =>
    simp only [MutabilityCtx.eraseCVars] at h
    cases h with
    | here => exact ⟨C', rfl, .here⟩
    | there h' => obtain ⟨C0, hC0, hHas⟩ := ih h'; exact ⟨C0, hC0, .there hHas⟩

theorem SepCtx.HasTwoDistinct.eraseCVars {K0 : SepCtx s} {C1 C2 : CaptureSet s} {K : CaptureSet s}
    (h : K0.HasTwoDistinct C1 C2) :
    (K0.eraseCVars K).HasTwoDistinct (C1.eraseCVars K) (C2.eraseCVars K) := by
  induction h with
  | here_there hHas => exact .here_there hHas.eraseCVars
  | there _ ih => exact .there ih
  | symm _ ih => exact .symm ih

theorem SepCtx.HasTwoDistinct.eraseCVars_inv {K0 : SepCtx s} {C1 C2 : CaptureSet s}
    {K : CaptureSet s}
    (h : (K0.eraseCVars K).HasTwoDistinct C1 C2) :
    ∃ D1 D2, C1 = D1.eraseCVars K ∧ C2 = D2.eraseCVars K ∧ K0.HasTwoDistinct D1 D2 := by
  generalize he0 : K0.eraseCVars K = Kε at h
  induction h generalizing K0
  case here_there hhas =>
    cases K0 with
    | empty => simp only [SepCtx.eraseCVars] at he0; cases he0
    | cons K1 C0 =>
      have heq := he0
      simp only [SepCtx.eraseCVars] at heq
      injection heq with hK hC
      subst hK hC
      obtain ⟨D2, hD2, hh⟩ := SepCtx.Has.eraseCVars_inv hhas
      exact ⟨C0, D2, rfl, hD2, .here_there hh⟩
  case there a ih =>
    cases K0 with
    | empty => simp only [SepCtx.eraseCVars] at he0; cases he0
    | cons K1 C0 =>
      have heq := he0
      simp only [SepCtx.eraseCVars] at heq
      injection heq with hK hC
      obtain ⟨D1, D2, hD1, hD2, hh⟩ := ih hK
      exact ⟨D1, D2, hD1, hD2, .there hh⟩
  case symm a ih =>
    obtain ⟨D2, D1, hD2, hD1, hh⟩ := ih he0
    exact ⟨D1, D2, hD1, hD2, .symm hh⟩

/- Item 19: TwoDistinctDroppable transport for non-killed variables.  Erase preserves the
   authority tag; `kill_peaks_cs` only touches mentioned cvars, so an unmentioned `c` keeps
   its `.can_drop` (the two lookup-authority helpers are hoisted above item 16). -/
theorem Ctx.TwoDistinctDroppable.eraseCVars_kill {Γ : Ctx s} {c1 c2 : BVar s .cvar}
    {K : CaptureSet s} (h : Γ.TwoDistinctDroppable c1 c2)
    (h1 : K.mentionsCVar c1 = false) (h2 : K.mentionsCVar c2 = false) :
    ((Γ.eraseCVars K).kill_peaks_cs K).TwoDistinctDroppable c1 c2 := by
  obtain ⟨ha1, ha2, hne⟩ := h
  refine ⟨?_, ?_, hne⟩
  · rw [Ctx.kill_peaks_cs_lookup_authority_not_mentioned h1, Ctx.eraseCVars_lookup_authority, ha1]
  · rw [Ctx.kill_peaks_cs_lookup_authority_not_mentioned h2, Ctx.eraseCVars_lookup_authority, ha2]

/- Lookup relations survive `kill_peaks_cs`: killing only re-tags cvar authorities, so
   var/tvar/lock lookups and cvar *bounds* are untouched; a cvar *authority* is preserved
   as long as the variable is not mentioned by the kill set.  Composed with item 11 these
   transport lookups into the erased-and-killed target context. -/
theorem Ctx.kill_peaks_cs_lookup_tvar {s : Sig} (Γ : Ctx s) (K : CaptureSet s)
    (X : BVar s .tvar) : (Γ.kill_peaks_cs K).lookup_tvar X = Γ.lookup_tvar X := by
  induction K generalizing Γ with
  | empty => rfl
  | union cs1 cs2 ih1 ih2 =>
    change ((Γ.kill_peaks_cs cs1).kill_peaks_cs cs2).lookup_tvar X = Γ.lookup_tvar X
    rw [ih2, ih1]
  | cvar a c => exact Ctx.kill_cvar_lookup_tvar Γ c X
  | var a v => rfl

theorem Ctx.kill_peaks_cs_lookup_lock {s : Sig} (Γ : Ctx s) (K : CaptureSet s)
    (ℓ : BVar s .lock) : (Γ.kill_peaks_cs K).lookup_lock ℓ = Γ.lookup_lock ℓ := by
  induction K generalizing Γ with
  | empty => rfl
  | union cs1 cs2 ih1 ih2 =>
    change ((Γ.kill_peaks_cs cs1).kill_peaks_cs cs2).lookup_lock ℓ = Γ.lookup_lock ℓ
    rw [ih2, ih1]
  | cvar a c => exact Ctx.kill_cvar_lookup_lock Γ c ℓ
  | var a v => rfl

theorem Ctx.kill_peaks_cs_lookup_cvar {s : Sig} (Γ : Ctx s) (K : CaptureSet s)
    (c : BVar s .cvar) : (Γ.kill_peaks_cs K).lookup_cvar c = Γ.lookup_cvar c := by
  induction K generalizing Γ with
  | empty => rfl
  | union cs1 cs2 ih1 ih2 =>
    change ((Γ.kill_peaks_cs cs1).kill_peaks_cs cs2).lookup_cvar c = Γ.lookup_cvar c
    rw [ih2, ih1]
  | cvar a c' => exact Ctx.kill_cvar_lookup_cvar Γ c' c
  | var a v => rfl

theorem Ctx.LookupVar.kill_peaks_cs {Γ : Ctx s} {x : BVar s .var} {T : Ty .capt s}
    (h : Γ.LookupVar x T) (K : CaptureSet s) : (Γ.kill_peaks_cs K).LookupVar x T := by
  have hs := Ctx.lookup_var_spec (Γ.kill_peaks_cs K) x
  rw [Ctx.kill_peaks_cs_lookup_var, ← h.eq_lookup] at hs
  exact hs

theorem Ctx.LookupTVar.kill_peaks_cs {Γ : Ctx s} {X : BVar s .tvar} {S : PureTy s}
    (h : Γ.LookupTVar X S) (K : CaptureSet s) : (Γ.kill_peaks_cs K).LookupTVar X S := by
  have hs := Ctx.lookup_tvar_spec (Γ.kill_peaks_cs K) X
  rw [Ctx.kill_peaks_cs_lookup_tvar, ← h.eq_lookup] at hs
  exact hs

theorem Ctx.LookupLock.kill_peaks_cs {Γ : Ctx s} {ℓ : BVar s .lock} {Ψ : ModalCtx s}
    (h : Γ.LookupLock ℓ Ψ) (K : CaptureSet s) : (Γ.kill_peaks_cs K).LookupLock ℓ Ψ := by
  have hs := Ctx.lookup_lock_spec (Γ.kill_peaks_cs K) ℓ
  rw [Ctx.kill_peaks_cs_lookup_lock, ← h.eq_lookup] at hs
  exact hs

theorem Ctx.LookupCVar.kill_peaks_cs {Γ : Ctx s} {c : BVar s .cvar} {a : Authority}
    {cb : CaptureBound s} (h : Γ.LookupCVar c a cb) {K : CaptureSet s}
    (hc : K.mentionsCVar c = false) : (Γ.kill_peaks_cs K).LookupCVar c a cb := by
  have hs := Ctx.lookup_cvar_spec (Γ.kill_peaks_cs K) c
  rw [Ctx.kill_peaks_cs_lookup_cvar, Ctx.kill_peaks_cs_lookup_authority_not_mentioned hc,
    ← h.eq_lookup, ← h.eq_authority] at hs
  exact hs

/-! ## §2.1 Headline erasure theorems (L1–L8) -/

theorem Subcapt.erase_kill {s : Sig} {Γ : Ctx s} {C1 C2 : CaptureSet s}
    (h : Subcapt Γ C1 C2) (K : CaptureSet s) :
    Subcapt ((Γ.eraseCVars K).kill_peaks_cs K) (C1.eraseCVars K) (C2.eraseCVars K) := by
  induction h with
  | sc_trans _ _ ih1 ih2 => exact .sc_trans ih1 ih2
  | sc_elem hsub => exact .sc_elem hsub.eraseCVars
  | sc_mode hle =>
    rw [CaptureSet.eraseCVars_applyMut, CaptureSet.eraseCVars_applyMut]
    exact .sc_mode hle
  | sc_union _ _ ih1 ih2 =>
    rw [CaptureSet.eraseCVars_union]
    exact .sc_union ih1 ih2
  | sc_var hlook =>
    rw [← Ty.captureSet_eraseCVars]
    exact .sc_var ((hlook.eraseCVars).kill_peaks_cs K)
  | sc_cvar hlook =>
    rename_i c C
    by_cases hm : K.mentionsCVar c = true
    · rw [CaptureSet.eraseCVars_cvar_pos hm]
      exact .sc_elem CaptureSet.Subset.empty
    · rw [Bool.not_eq_true] at hm
      rw [CaptureSet.eraseCVars_cvar_neg hm]
      exact .sc_cvar ((hlook.eraseCVars).kill_peaks_cs hm)
  | sc_ro =>
    rw [CaptureSet.eraseCVars_applyRO]
    exact .sc_ro
  | sc_ro_mono _ ih =>
    rw [CaptureSet.eraseCVars_applyRO, CaptureSet.eraseCVars_applyRO]
    exact .sc_ro_mono ih
  | sc_drop_mono _ ih =>
    rw [CaptureSet.eraseCVars_applyAccess, CaptureSet.eraseCVars_applyAccess]
    exact .sc_drop_mono ih

theorem HasKind.erase_kill {s : Sig} {Γ : Ctx s} {C : CaptureSet s} {m : Mutability}
    (h : HasKind Γ C m) (K : CaptureSet s) :
    HasKind ((Γ.eraseCVars K).kill_peaks_cs K) (C.eraseCVars K) m := by
  induction h with
  | empty => exact .empty
  | union _ _ ih1 ih2 => exact .union ih1 ih2
  | sc hsc _ ih => exact .sc (hsc.erase_kill K) ih
  | rw => exact .rw
  | imm hlock hhas => exact .imm ((hlock.eraseCVars).kill_peaks_cs K) hhas.eraseCVars
  | ro => rw [CaptureSet.eraseCVars_applyRO]; exact .ro

theorem Subbound.erase_kill {s : Sig} {Γ : Ctx s} {cb1 cb2 : CaptureBound s}
    (h : Subbound Γ cb1 cb2) (K : CaptureSet s) :
    Subbound ((Γ.eraseCVars K).kill_peaks_cs K) (cb1.eraseCVars K) (cb2.eraseCVars K) := by
  cases h with
  | capset hsc => exact .capset (hsc.erase_kill K)
  | top => exact .top

theorem SepCheck.erase_kill {s : Sig} {Γ : Ctx s} {C1 C2 : CaptureSet s}
    (h : SepCheck Γ C1 C2) (K : CaptureSet s) :
    SepCheck ((Γ.eraseCVars K).kill_peaks_cs K) (C1.eraseCVars K) (C2.eraseCVars K) := by
  induction h with
  | sep_symm _ ih => exact .sep_symm ih
  | sep_union _ _ ih1 ih2 => exact .sep_union ih1 ih2
  | sep_empty => exact .sep_empty
  | sep_ro hc1 hc2 ha1 ha2 hk1 hk2 =>
    exact .sep_ro (hc1.eraseCVars K) (hc2.eraseCVars K) ha1.eraseCVars ha2.eraseCVars
      (hk1.erase_kill K) (hk2.erase_kill K)
  | sep_sc _ hsc hequiv ih => exact .sep_sc ih (hsc.erase_kill K) hequiv.eraseCVars
  | sep_mono _ hsc ih => exact .sep_mono ih (hsc.erase_kill K)
  | sep_lock hlock htwo => exact .sep_lock ((hlock.eraseCVars).kill_peaks_cs K) htwo.eraseCVars
  | @sep_droppable m1 m2 c1 c2 htwo =>
    by_cases hm1 : K.mentionsCVar c1 = true
    · rw [CaptureSet.eraseCVars_cvar_pos hm1]
      exact .sep_empty
    · rw [Bool.not_eq_true] at hm1
      by_cases hm2 : K.mentionsCVar c2 = true
      · rw [CaptureSet.eraseCVars_cvar_pos hm2, CaptureSet.eraseCVars_cvar_neg hm1]
        exact .sep_symm .sep_empty
      · rw [Bool.not_eq_true] at hm2
        rw [CaptureSet.eraseCVars_cvar_neg hm1, CaptureSet.eraseCVars_cvar_neg hm2]
        exact .sep_droppable (htwo.eraseCVars_kill hm1 hm2)

theorem DisjCheck.erase_kill {s : Sig} {Γ : Ctx s} {C1 C2 : CaptureSet s}
    (h : DisjCheck Γ C1 C2) (K : CaptureSet s) :
    DisjCheck ((Γ.eraseCVars K).kill_peaks_cs K) (C1.eraseCVars K) (C2.eraseCVars K) := by
  induction h with
  | disj_symm _ ih => exact .disj_symm ih
  | disj_union _ _ ih1 ih2 => exact .disj_union ih1 ih2
  | disj_empty => exact .disj_empty
  | disj_sc _ hsc hequiv ih => exact .disj_sc ih (hsc.erase_kill K) hequiv.eraseCVars
  | @disj_droppable m1 m2 c1 c2 htwo =>
    by_cases hm1 : K.mentionsCVar c1 = true
    · rw [CaptureSet.eraseCVars_cvar_pos hm1]
      exact .disj_empty
    · rw [Bool.not_eq_true] at hm1
      by_cases hm2 : K.mentionsCVar c2 = true
      · rw [CaptureSet.eraseCVars_cvar_pos hm2, CaptureSet.eraseCVars_cvar_neg hm1]
        exact .disj_symm .disj_empty
      · rw [Bool.not_eq_true] at hm2
        rw [CaptureSet.eraseCVars_cvar_neg hm1, CaptureSet.eraseCVars_cvar_neg hm2]
        exact .disj_droppable (htwo.eraseCVars_kill hm1 hm2)

theorem Satisfy.erase_kill {s : Sig} {Γ : Ctx s} {Ψ : ModalCtx s}
    (h : Satisfy Γ Ψ) (K : CaptureSet s) :
    Satisfy ((Γ.eraseCVars K).kill_peaks_cs K) (Ψ.eraseCVars K) := by
  cases h with
  | satisfy hkind hsep =>
    refine Satisfy.satisfy ?_ ?_
    · intro C m hHas
      obtain ⟨C0, hCeq, hHas0⟩ := MutabilityCtx.Has.eraseCVars_inv hHas
      subst hCeq
      exact (hkind C0 m hHas0).erase_kill K
    · intro C1 C2 hTwo
      obtain ⟨D1, D2, hD1, hD2, hTwo0⟩ := SepCtx.HasTwoDistinct.eraseCVars_inv hTwo
      subst hD1 hD2
      exact (hsep D1 D2 hTwo0).erase_kill K

theorem Subtyp.erase_kill {s : Sig} {Γ : Ctx s} {sort : TySort} {T1 T2 : Ty sort s}
    (h : Subtyp Γ T1 T2) (K : CaptureSet s) :
    Subtyp ((Γ.eraseCVars K).kill_peaks_cs K) (T1.eraseCVars K) (T2.eraseCVars K) := by
  induction h with
  | top hpure => exact .top (hpure.eraseCVars K)
  | refl => exact .refl
  | trans hclosed _ _ ih1 ih2 => exact .trans (hclosed.eraseCVars K) (ih1 K) (ih2 K)
  | tvar hlook => exact .tvar ((hlook.eraseCVars).kill_peaks_cs K)
  | arrow _ hsc _ ih1 ih3 =>
    refine .arrow (ih1 K) (hsc.erase_kill K) ?_
    have h3 := ih3 (K.rename (Rename.succ (k := .var)))
    rw [Ctx.eraseCVars_push_var, Ctx.kill_peaks_cs_push_var] at h3
    exact h3
  | poly _ hsc _ ih1 ih3 =>
    have h3 := ih3 (K.rename (Rename.succ (k := .tvar)))
    rw [Ctx.eraseCVars_push_tvar, Ctx.kill_peaks_cs_push_tvar] at h3
    simp only [Ty.eraseCVars, ← PureTy.core_eraseCVars]
    exact .poly (ih1 K) (hsc.erase_kill K) h3
  | cpoly hsb hsc _ ih3 =>
    refine .cpoly (hsb.erase_kill K) (hsc.erase_kill K) ?_
    have h3 := ih3 (K.rename (Rename.succ (k := .cvar)))
    rw [Ctx.eraseCVars_push_cvar, Ctx.kill_peaks_cs_push_cvar] at h3
    exact h3
  | modal hsc _ ih =>
    refine .modal (hsc.erase_kill K) ?_
    have h3 := ih (K.rename (Rename.succ (k := .lock)))
    rw [Ctx.eraseCVars_push_lock, Ctx.kill_peaks_cs_push_lock,
      Ty.eraseCVars_rename Rename.succ_cvarInjective,
      Ty.eraseCVars_rename Rename.succ_cvarInjective] at h3
    exact h3
  | modal_modal hΓ hΨ1 hΨ2 hsat =>
    refine .modal_modal (Ctx.kill_peaks_cs_isClosed (hΓ.eraseCVars K)) (hΨ1.eraseCVars K)
      (hΨ2.eraseCVars K) ?_
    have h3 := hsat.erase_kill (K.rename (Rename.succ (k := .lock)))
    rw [Ctx.eraseCVars_push_lock, Ctx.kill_peaks_cs_push_lock,
      ModalCtx.eraseCVars_rename Rename.succ_cvarInjective] at h3
    exact h3
  | @exi s' Γ' n T1' T2' _ ih =>
    refine .exi ?_
    have h3 := ih (K.rename (Rename.weakenCVars n))
    rw [Ctx.eraseCVars_extendCVars, Ctx.kill_peaks_cs_extendCVars] at h3
    exact h3
  | cell hsc => exact .cell (hsc.erase_kill K)
  | reader hsc => exact .reader (hsc.erase_kill K)
  | cap hsc => exact .cap (hsc.erase_kill K)
  | poly_cap hsc => exact .poly_cap (hsc.erase_kill K)
  | typ _ ih => exact .typ (ih K)

theorem SeqComp.erase_kill {s : Sig} {Γ : Ctx s} {C1 C2 : CaptureSet s}
    (h : SeqComp Γ C1 C2) (K : CaptureSet s) :
    SeqComp ((Γ.eraseCVars K).kill_peaks_cs K) (C1.eraseCVars K) (C2.eraseCVars K) := by
  induction h with
  | seq_sc hsc hequiv _ ih => exact .seq_sc (hsc.erase_kill K) hequiv.eraseCVars ih
  | seq_union _ _ ih1 ih2 => exact .seq_union ih1 ih2
  | seq_access_only hc ha => exact .seq_access_only (hc.eraseCVars K) ha.eraseCVars
  | seq_sep hsep => exact .seq_sep (hsep.erase_kill K)

private theorem CaptureSet.PairwiseSep.erase_kill {s : Sig} {Γ : Ctx s}
    {n : Nat} {Cs : List.Vector (CaptureSet s) n} (h : CaptureSet.PairwiseSep Γ Cs)
    (K : CaptureSet s) :
    CaptureSet.PairwiseSep ((Γ.eraseCVars K).kill_peaks_cs K)
      (Cs.map (·.eraseCVars K)) := by
  unfold CaptureSet.PairwiseSep at h ⊢
  rw [List.Vector.toList_map]
  exact List.Pairwise.map (fun C => C.eraseCVars K)
    (fun a b (hab : DisjCheck Γ a b) => hab.erase_kill K) h

private theorem PeakSet.droppable.eraseCVars {s : Sig} {Γ : Ctx s}
    {P : PeakSet s} {K : CaptureSet s} (h : P.droppable Γ) :
    PeakSet.droppable ((Γ.eraseCVars K).kill_peaks_cs K)
      ⟨P.cs.eraseCVars K, P.h.eraseCVars K⟩ := by
  intro a c hsub
  obtain ⟨hsub0, hK⟩ := CaptureSet.cvar_subset_eraseCVars_inv hsub
  rw [Ctx.kill_peaks_cs_lookup_authority_not_mentioned hK, Ctx.eraseCVars_lookup_authority]
  exact h a c hsub0

private theorem CaptureSet.consumed_peakset_eraseCVars_kill_cs {s : Sig}
    {Γ : Ctx s} {C K : CaptureSet s} :
    (((C.eraseCVars K).peakset ((Γ.eraseCVars K).kill_peaks_cs K)).consumed).cs
      = (((C.peakset Γ).consumed).cs).eraseCVars K := by
  simp only [CaptureSet.peakset, PeakSet.consumed]
  rw [CaptureSet.peaks_eraseCVars_kill, CaptureSet.consumed_eraseCVars]

private theorem Ctx.erase_kill_consumed_base {s : Sig} {Γ : Ctx s}
    {K C1 : CaptureSet s} :
    (((Γ.kill_peaks ((C1.peakset Γ).consumed)).eraseCVars K).kill_peaks_cs K)
      =
    ((Γ.eraseCVars K).kill_peaks_cs K).kill_peaks
      (((C1.eraseCVars K).peakset ((Γ.eraseCVars K).kill_peaks_cs K)).consumed) := by
  have hcs :
      (((C1.eraseCVars K).peakset ((Γ.eraseCVars K).kill_peaks_cs K)).consumed).cs
        = (((C1.peakset Γ).consumed).cs).eraseCVars K :=
    CaptureSet.consumed_peakset_eraseCVars_kill_cs
  calc
    (((Γ.kill_peaks ((C1.peakset Γ).consumed)).eraseCVars K).kill_peaks_cs K)
        =
      Ctx.kill_peaks_cs
        ((Γ.kill_peaks_cs ((C1.peakset Γ).consumed).cs).eraseCVars K)
        K := by
          rfl
    _ =
      Ctx.kill_peaks_cs
        ((Γ.eraseCVars K).kill_peaks_cs ((C1.peakset Γ).consumed).cs)
        K := by
          rw [← Ctx.eraseCVars_kill_peaks_cs]
    _ =
      (((Γ.eraseCVars K).kill_peaks_cs K).kill_peaks_cs
        ((C1.peakset Γ).consumed).cs) := by
          rw [Ctx.kill_peaks_cs_comm]
    _ =
      ((Γ.eraseCVars K).kill_peaks_cs K).kill_peaks
        (((C1.eraseCVars K).peakset ((Γ.eraseCVars K).kill_peaks_cs K)).consumed) := by
          simp only [Ctx.kill_peaks]
          rw [hcs, Ctx.kill_peaks_cs_absorb_eraseCVars]

private theorem CaptureSet.eraseCVars_fresh_succ_cvar {s : Sig} {K : CaptureSet s}
    {a : Access} :
    (CaptureSet.cvar a BVar.here).eraseCVars (K.rename (Rename.succ (k := .cvar)))
      = CaptureSet.cvar a BVar.here := by
  rw [CaptureSet.eraseCVars_cvar]
  apply if_neg
  intro h
  have hHere :
      (K.rename (Rename.succ (k := .cvar))).mentionsCVar BVar.here = false :=
    CaptureSet.mentionsCVar_rename_succ_here
  rw [hHere] at h
  cases h

private theorem CaptureSet.eraseCVars_consumer_bound_cvar {s : Sig} {K : CaptureSet s}
    {a : Access} :
    (CaptureSet.cvar a (BVar.there (BVar.here : BVar (s,C) .cvar))).eraseCVars
        ((K.rename (Rename.succ (k := .cvar))).rename (Rename.succ (k := .var)))
      = CaptureSet.cvar a (BVar.there (BVar.here : BVar (s,C) .cvar)) := by
  rw [CaptureSet.eraseCVars_cvar]
  apply if_neg
  intro h
  have hThere :
      (((K.rename (Rename.succ (k := .cvar))).rename
          (Rename.succ (k := .var))).mentionsCVar
          (BVar.there (BVar.here : BVar (s,C) .cvar)))
        = (K.rename (Rename.succ (k := .cvar))).mentionsCVar
          (BVar.here : BVar (s,C) .cvar) := by
    simpa only [Rename.succ] using
      (CaptureSet.mentionsCVar_rename
        (K := K.rename (Rename.succ (k := .cvar)))
        (ρ := Rename.succ (k := .var))
        (c := (BVar.here : BVar (s,C) .cvar))
        Rename.succ_cvarInjective)
  have hHere :
      (K.rename (Rename.succ (k := .cvar))).mentionsCVar
          (BVar.here : BVar (s,C) .cvar) = false :=
    CaptureSet.mentionsCVar_rename_succ_here
  rw [hThere, hHere] at h
  cases h

private theorem Ctx.erase_kill_consumer_body {s : Sig} {Γ : Ctx s}
    {K : CaptureSet s} {X : PeakSet s} {T : Ty .capt (s,C)} :
    Ctx.kill_peaks_cs
      (Ctx.eraseCVars
        (Ctx.push_var (Ctx.push_cvar (Γ.kill_peaks_cs X.cs) .can_drop .unbound) T)
        ((K.rename (Rename.succ (k := .cvar))).rename (Rename.succ (k := .var))))
      ((K.rename (Rename.succ (k := .cvar))).rename (Rename.succ (k := .var)))
      =
    Ctx.push_var
      (Ctx.push_cvar (((Γ.eraseCVars K).kill_peaks_cs K).kill_peaks_cs X.cs)
        .can_drop .unbound)
      (T.eraseCVars (K.rename (Rename.succ (k := .cvar)))) := by
  have hctx :
      (((Γ.kill_peaks_cs X.cs).eraseCVars K).kill_peaks_cs K)
        = ((Γ.eraseCVars K).kill_peaks_cs K).kill_peaks_cs X.cs := by
    rw [← Ctx.eraseCVars_kill_peaks_cs, Ctx.kill_peaks_cs_comm]
  have herase :
      Ctx.eraseCVars
        (Ctx.push_var (Ctx.push_cvar (Γ.kill_peaks_cs X.cs) .can_drop .unbound) T)
        ((K.rename (Rename.succ (k := .cvar))).rename (Rename.succ (k := .var)))
        =
      Ctx.push_var
        (Ctx.push_cvar ((Γ.kill_peaks_cs X.cs).eraseCVars K) .can_drop .unbound)
        (T.eraseCVars (K.rename (Rename.succ (k := .cvar)))) := by
    calc
      Ctx.eraseCVars
        (Ctx.push_var (Ctx.push_cvar (Γ.kill_peaks_cs X.cs) .can_drop .unbound) T)
        ((K.rename (Rename.succ (k := .cvar))).rename (Rename.succ (k := .var)))
          =
        Ctx.push_var
          (Ctx.eraseCVars
            (Ctx.push_cvar (Γ.kill_peaks_cs X.cs) .can_drop .unbound)
            (K.rename (Rename.succ (k := .cvar))))
          (T.eraseCVars (K.rename (Rename.succ (k := .cvar)))) := by
            exact Ctx.eraseCVars_push_var
              (Γ := Ctx.push_cvar (Γ.kill_peaks_cs X.cs) .can_drop .unbound)
              (T := T) (K := K.rename (Rename.succ (k := .cvar)))
      _ =
        Ctx.push_var
          (Ctx.push_cvar ((Γ.kill_peaks_cs X.cs).eraseCVars K) .can_drop .unbound)
          (T.eraseCVars (K.rename (Rename.succ (k := .cvar)))) := by
            rw [Ctx.eraseCVars_push_cvar (Γ := Γ.kill_peaks_cs X.cs)
              (a := .can_drop) (cb := .unbound) (K := K)]
            rfl
  calc
    Ctx.kill_peaks_cs
      (Ctx.eraseCVars
        (Ctx.push_var (Ctx.push_cvar (Γ.kill_peaks_cs X.cs) .can_drop .unbound) T)
        ((K.rename (Rename.succ (k := .cvar))).rename (Rename.succ (k := .var))))
      ((K.rename (Rename.succ (k := .cvar))).rename (Rename.succ (k := .var)))
        =
      Ctx.push_var
        (Ctx.push_cvar (((Γ.kill_peaks_cs X.cs).eraseCVars K).kill_peaks_cs K)
          .can_drop .unbound)
        (T.eraseCVars (K.rename (Rename.succ (k := .cvar)))) := by
          rw [herase]
          apply Eq.trans
            (Ctx.kill_peaks_cs_push_var
              (Γ := Ctx.push_cvar ((Γ.kill_peaks_cs X.cs).eraseCVars K)
                .can_drop .unbound)
              (T := T.eraseCVars (K.rename (Rename.succ (k := .cvar))))
              (K := K.rename (Rename.succ (k := .cvar))))
          exact congrArg
            (fun Δ => Ctx.push_var Δ (T.eraseCVars (K.rename (Rename.succ (k := .cvar)))))
            (Ctx.kill_peaks_cs_push_cvar (Γ := (Γ.kill_peaks_cs X.cs).eraseCVars K)
              (a := .can_drop) (cb := .unbound) (K := K))
    _ =
      Ctx.push_var
        (Ctx.push_cvar (((Γ.eraseCVars K).kill_peaks_cs K).kill_peaks_cs X.cs)
          .can_drop .unbound)
        (T.eraseCVars (K.rename (Rename.succ (k := .cvar)))) := by
          rw [hctx]

private theorem Ctx.erase_kill_letin_body {s : Sig} {Γ : Ctx s}
    {K C1 : CaptureSet s} {T : Ty .capt s} :
    Ctx.kill_peaks_cs
      (Ctx.eraseCVars
        (Ctx.push_var (Γ.kill_peaks ((C1.peakset Γ).consumed)) T)
        (K.rename (Rename.succ (k := .var))))
      (K.rename (Rename.succ (k := .var)))
      =
    Ctx.push_var
      (((Γ.eraseCVars K).kill_peaks_cs K).kill_peaks
        (((C1.eraseCVars K).peakset ((Γ.eraseCVars K).kill_peaks_cs K)).consumed))
      (T.eraseCVars K) := by
  have hctx :
      (((Γ.kill_peaks ((C1.peakset Γ).consumed)).eraseCVars K).kill_peaks_cs K)
        =
      ((Γ.eraseCVars K).kill_peaks_cs K).kill_peaks
        (((C1.eraseCVars K).peakset ((Γ.eraseCVars K).kill_peaks_cs K)).consumed) := by
    have hcs :
        (((C1.eraseCVars K).peakset ((Γ.eraseCVars K).kill_peaks_cs K)).consumed).cs
          = (((C1.peakset Γ).consumed).cs).eraseCVars K :=
      CaptureSet.consumed_peakset_eraseCVars_kill_cs
    calc
      (((Γ.kill_peaks ((C1.peakset Γ).consumed)).eraseCVars K).kill_peaks_cs K)
          =
        Ctx.kill_peaks_cs
          ((Γ.kill_peaks_cs ((C1.peakset Γ).consumed).cs).eraseCVars K)
          K := by
            rfl
      _ =
        Ctx.kill_peaks_cs
          ((Γ.eraseCVars K).kill_peaks_cs ((C1.peakset Γ).consumed).cs)
          K := by
            rw [← Ctx.eraseCVars_kill_peaks_cs]
      _ =
        (((Γ.eraseCVars K).kill_peaks_cs K).kill_peaks_cs
          ((C1.peakset Γ).consumed).cs) := by
            rw [Ctx.kill_peaks_cs_comm]
      _ =
        ((Γ.eraseCVars K).kill_peaks_cs K).kill_peaks
          (((C1.eraseCVars K).peakset ((Γ.eraseCVars K).kill_peaks_cs K)).consumed) := by
            simp only [Ctx.kill_peaks]
            rw [hcs, Ctx.kill_peaks_cs_absorb_eraseCVars]
  calc
    Ctx.kill_peaks_cs
      (Ctx.eraseCVars
        (Ctx.push_var (Γ.kill_peaks ((C1.peakset Γ).consumed)) T)
        (K.rename (Rename.succ (k := .var))))
      (K.rename (Rename.succ (k := .var)))
        =
      Ctx.push_var
        (((Γ.kill_peaks ((C1.peakset Γ).consumed)).eraseCVars K).kill_peaks_cs K)
        (T.eraseCVars K) := by
          rw [Ctx.eraseCVars_push_var, Ctx.kill_peaks_cs_push_var]
    _ =
      Ctx.push_var
        (((Γ.eraseCVars K).kill_peaks_cs K).kill_peaks
          (((C1.eraseCVars K).peakset ((Γ.eraseCVars K).kill_peaks_cs K)).consumed))
        (T.eraseCVars K) := by
          rw [hctx]

private theorem CaptureSet.eraseCVars_unpack_uses {s : Sig} {C2 K : CaptureSet s}
    {n : Nat} :
    (((((C2.rename (Rename.weakenCVars n)).rename (Rename.succ (k := .lock))).rename
          (Rename.succ (k := .var))) ∪
        (((CaptureSet.freshCVars n).rename (Rename.succ (k := .lock))).rename
          (Rename.succ (k := .var))) ∪
        ((((CaptureSet.freshCVars n).rename (Rename.succ (k := .lock))).rename
          (Rename.succ (k := .var))).applyAccess .drop)).eraseCVars
        (((K.rename (Rename.weakenCVars n)).rename (Rename.succ (k := .lock))).rename
          (Rename.succ (k := .var))))
      =
    ((((C2.eraseCVars K).rename (Rename.weakenCVars n)).rename
          (Rename.succ (k := .lock))).rename (Rename.succ (k := .var))) ∪
      (((CaptureSet.freshCVars n).rename (Rename.succ (k := .lock))).rename
        (Rename.succ (k := .var))) ∪
      ((((CaptureSet.freshCVars n).rename (Rename.succ (k := .lock))).rename
        (Rename.succ (k := .var))).applyAccess .drop) := by
  have hC :
      ((((C2.rename (Rename.weakenCVars n)).rename (Rename.succ (k := .lock))).rename
          (Rename.succ (k := .var))).eraseCVars
        (((K.rename (Rename.weakenCVars n)).rename (Rename.succ (k := .lock))).rename
          (Rename.succ (k := .var))))
        =
      (((C2.eraseCVars K).rename (Rename.weakenCVars n)).rename
          (Rename.succ (k := .lock))).rename (Rename.succ (k := .var)) := by
    rw [CaptureSet.eraseCVars_rename Rename.succ_cvarInjective,
      CaptureSet.eraseCVars_rename Rename.succ_cvarInjective,
      CaptureSet.eraseCVars_rename Rename.weakenCVars_cvarInjective]
  have hfresh :
      ((((CaptureSet.freshCVars n).rename (Rename.succ (k := .lock))).rename
          (Rename.succ (k := .var))).eraseCVars
        (((K.rename (Rename.weakenCVars n)).rename (Rename.succ (k := .lock))).rename
          (Rename.succ (k := .var))))
        =
      ((CaptureSet.freshCVars n).rename (Rename.succ (k := .lock))).rename
        (Rename.succ (k := .var)) := by
    rw [CaptureSet.eraseCVars_rename Rename.succ_cvarInjective,
      CaptureSet.eraseCVars_rename Rename.succ_cvarInjective,
      CaptureSet.freshCVars_eraseCVars]
  change
    (((((C2.rename (Rename.weakenCVars n)).rename (Rename.succ (k := .lock))).rename
            (Rename.succ (k := .var))).union
          (((CaptureSet.freshCVars n).rename (Rename.succ (k := .lock))).rename
            (Rename.succ (k := .var)))).union
        ((((CaptureSet.freshCVars n).rename (Rename.succ (k := .lock))).rename
          (Rename.succ (k := .var))).applyAccess .drop)).eraseCVars
        (((K.rename (Rename.weakenCVars n)).rename (Rename.succ (k := .lock))).rename
          (Rename.succ (k := .var)))
      =
    (((((C2.eraseCVars K).rename (Rename.weakenCVars n)).rename
            (Rename.succ (k := .lock))).rename (Rename.succ (k := .var))).union
          (((CaptureSet.freshCVars n).rename (Rename.succ (k := .lock))).rename
            (Rename.succ (k := .var)))).union
        ((((CaptureSet.freshCVars n).rename (Rename.succ (k := .lock))).rename
          (Rename.succ (k := .var))).applyAccess .drop)
  rw [CaptureSet.eraseCVars_union, CaptureSet.eraseCVars_union, hC, hfresh,
    CaptureSet.eraseCVars_applyAccess, hfresh]

private theorem ModalCtx.eraseCVars_unpack_lock {s : Sig} {C2 K : CaptureSet s}
    {n : Nat} :
    (⟨(SepCtx.empty.cons (C2.rename (Rename.weakenCVars n))).cons
          (CaptureSet.freshCVars n),
        MutabilityCtx.empty⟩ : ModalCtx (s.extendCVars n)).eraseCVars
        (K.rename (Rename.weakenCVars n))
      =
    ⟨(SepCtx.empty.cons ((C2.eraseCVars K).rename (Rename.weakenCVars n))).cons
        (CaptureSet.freshCVars n),
      MutabilityCtx.empty⟩ := by
  simp only [ModalCtx.eraseCVars, SepCtx.eraseCVars, MutabilityCtx.eraseCVars,
    CaptureSet.eraseCVars_rename Rename.weakenCVars_cvarInjective,
    CaptureSet.freshCVars_eraseCVars]

private theorem Ctx.erase_kill_unpack_body {s : Sig} {Γ : Ctx s}
    {K C1 C2 : CaptureSet s} {n : Nat} {T : Ty .capt (s.extendCVars n)} :
    Ctx.kill_peaks_cs
      (Ctx.eraseCVars
        (Ctx.push_var
          (Ctx.push_lock
            (Ctx.extendCVars .can_drop (Γ.kill_peaks ((C1.peakset Γ).consumed)) n)
            ⟨(SepCtx.empty.cons (C2.rename (Rename.weakenCVars n))).cons
                (CaptureSet.freshCVars n),
              MutabilityCtx.empty⟩)
          (T.rename (Rename.succ (k := .lock))))
        (((K.rename (Rename.weakenCVars n)).rename (Rename.succ (k := .lock))).rename
          (Rename.succ (k := .var))))
      (((K.rename (Rename.weakenCVars n)).rename (Rename.succ (k := .lock))).rename
        (Rename.succ (k := .var)))
      =
    Ctx.push_var
      (Ctx.push_lock
        (Ctx.extendCVars .can_drop
          (((Γ.eraseCVars K).kill_peaks_cs K).kill_peaks
            (((C1.eraseCVars K).peakset ((Γ.eraseCVars K).kill_peaks_cs K)).consumed))
          n)
        ⟨(SepCtx.empty.cons ((C2.eraseCVars K).rename (Rename.weakenCVars n))).cons
            (CaptureSet.freshCVars n),
          MutabilityCtx.empty⟩)
      ((T.eraseCVars (K.rename (Rename.weakenCVars n))).rename
        (Rename.succ (k := .lock))) := by
  have hmodal :
      (⟨(SepCtx.empty.cons (C2.rename (Rename.weakenCVars n))).cons
            (CaptureSet.freshCVars n),
          MutabilityCtx.empty⟩ : ModalCtx (s.extendCVars n)).eraseCVars
          (K.rename (Rename.weakenCVars n))
        =
      ⟨(SepCtx.empty.cons ((C2.eraseCVars K).rename (Rename.weakenCVars n))).cons
          (CaptureSet.freshCVars n),
        MutabilityCtx.empty⟩ :=
    ModalCtx.eraseCVars_unpack_lock
  have htype :
      (T.rename (Rename.succ (k := .lock))).eraseCVars
          ((K.rename (Rename.weakenCVars n)).rename (Rename.succ (k := .lock)))
        =
      (T.eraseCVars (K.rename (Rename.weakenCVars n))).rename
        (Rename.succ (k := .lock)) :=
    Ty.eraseCVars_rename Rename.succ_cvarInjective
  calc
    Ctx.kill_peaks_cs
      (Ctx.eraseCVars
        (Ctx.push_var
          (Ctx.push_lock
            (Ctx.extendCVars .can_drop (Γ.kill_peaks ((C1.peakset Γ).consumed)) n)
            ⟨(SepCtx.empty.cons (C2.rename (Rename.weakenCVars n))).cons
                (CaptureSet.freshCVars n),
              MutabilityCtx.empty⟩)
          (T.rename (Rename.succ (k := .lock))))
        (((K.rename (Rename.weakenCVars n)).rename (Rename.succ (k := .lock))).rename
          (Rename.succ (k := .var))))
      (((K.rename (Rename.weakenCVars n)).rename (Rename.succ (k := .lock))).rename
        (Rename.succ (k := .var)))
        =
      Ctx.push_var
        (Ctx.kill_peaks_cs
          (Ctx.eraseCVars
            (Ctx.push_lock
              (Ctx.extendCVars .can_drop (Γ.kill_peaks ((C1.peakset Γ).consumed)) n)
              ⟨(SepCtx.empty.cons (C2.rename (Rename.weakenCVars n))).cons
                  (CaptureSet.freshCVars n),
                MutabilityCtx.empty⟩)
            ((K.rename (Rename.weakenCVars n)).rename (Rename.succ (k := .lock))))
          ((K.rename (Rename.weakenCVars n)).rename (Rename.succ (k := .lock))))
        ((T.rename (Rename.succ (k := .lock))).eraseCVars
          ((K.rename (Rename.weakenCVars n)).rename (Rename.succ (k := .lock)))) := by
          rw [Ctx.eraseCVars_push_var, Ctx.kill_peaks_cs_push_var]
    _ =
      Ctx.push_var
        (Ctx.kill_peaks_cs
          (Ctx.push_lock
            (Ctx.eraseCVars
              (Ctx.extendCVars .can_drop (Γ.kill_peaks ((C1.peakset Γ).consumed)) n)
              (K.rename (Rename.weakenCVars n)))
            ((⟨(SepCtx.empty.cons (C2.rename (Rename.weakenCVars n))).cons
                (CaptureSet.freshCVars n),
              MutabilityCtx.empty⟩ : ModalCtx (s.extendCVars n)).eraseCVars
                (K.rename (Rename.weakenCVars n))))
          ((K.rename (Rename.weakenCVars n)).rename (Rename.succ (k := .lock))))
        ((T.eraseCVars (K.rename (Rename.weakenCVars n))).rename
          (Rename.succ (k := .lock))) := by
          rw [Ctx.eraseCVars_push_lock, htype]
    _ =
      Ctx.push_var
        (Ctx.push_lock
          (Ctx.kill_peaks_cs
            (Ctx.eraseCVars
              (Ctx.extendCVars .can_drop (Γ.kill_peaks ((C1.peakset Γ).consumed)) n)
              (K.rename (Rename.weakenCVars n)))
            (K.rename (Rename.weakenCVars n)))
          ((⟨(SepCtx.empty.cons (C2.rename (Rename.weakenCVars n))).cons
              (CaptureSet.freshCVars n),
            MutabilityCtx.empty⟩ : ModalCtx (s.extendCVars n)).eraseCVars
              (K.rename (Rename.weakenCVars n))))
        ((T.eraseCVars (K.rename (Rename.weakenCVars n))).rename
          (Rename.succ (k := .lock))) := by
          rw [Ctx.kill_peaks_cs_push_lock]
    _ =
      Ctx.push_var
        (Ctx.push_lock
          (Ctx.extendCVars .can_drop
            (((Γ.kill_peaks ((C1.peakset Γ).consumed)).eraseCVars K).kill_peaks_cs K)
            n)
          ((⟨(SepCtx.empty.cons (C2.rename (Rename.weakenCVars n))).cons
              (CaptureSet.freshCVars n),
            MutabilityCtx.empty⟩ : ModalCtx (s.extendCVars n)).eraseCVars
              (K.rename (Rename.weakenCVars n))))
        ((T.eraseCVars (K.rename (Rename.weakenCVars n))).rename
          (Rename.succ (k := .lock))) := by
          rw [Ctx.eraseCVars_extendCVars, Ctx.kill_peaks_cs_extendCVars]
    _ =
      Ctx.push_var
        (Ctx.push_lock
          (Ctx.extendCVars .can_drop
            (((Γ.eraseCVars K).kill_peaks_cs K).kill_peaks
              (((C1.eraseCVars K).peakset
                ((Γ.eraseCVars K).kill_peaks_cs K)).consumed))
            n)
          ⟨(SepCtx.empty.cons ((C2.eraseCVars K).rename (Rename.weakenCVars n))).cons
              (CaptureSet.freshCVars n),
            MutabilityCtx.empty⟩)
        ((T.eraseCVars (K.rename (Rename.weakenCVars n))).rename
          (Rename.succ (k := .lock))) := by
          rw [Ctx.erase_kill_consumed_base, hmodal]

theorem HasType.erase_kill {s : Sig} {C : CaptureSet s} {Γ : Ctx s} {e : Exp s} {E : Ty .exi s}
    (h : HasType C Γ e E) (K : CaptureSet s) :
    HasType (C.eraseCVars K) ((Γ.eraseCVars K).kill_peaks_cs K)
      (e.eraseCVars K) (E.eraseCVars K) := by
  induction h with
  | var hΓ hlook =>
    simp only [Exp.eraseCVars, Ty.eraseCVars,
      CaptureSet.eraseCVars_var, Ty.refineCaptureSet_eraseCVars]
    exact .var (Ctx.kill_peaks_cs_isClosed (hΓ.eraseCVars K))
      ((hlook.eraseCVars).kill_peaks_cs K)
  | reader hΓ hlook =>
    simp only [Exp.eraseCVars, Ty.eraseCVars,
      CaptureSet.eraseCVars_var]
    exact .reader (Ctx.kill_peaks_cs_isClosed (hΓ.eraseCVars K))
      ((hlook.eraseCVars).kill_peaks_cs K)
  | @abs s0 Γ0 e0 T2 cs T1 hT hbody ih =>
    have hbody' := ih (K.rename (Rename.succ (k := .var)))
    rw [Ctx.eraseCVars_push_var, Ctx.kill_peaks_cs_push_var] at hbody'
    have hcs :
        (cs.rename (Rename.succ (k := .var))).eraseCVars
            (K.rename (Rename.succ (k := .var)))
          = (cs.eraseCVars K).rename (Rename.succ (k := .var)) :=
      CaptureSet.eraseCVars_rename Rename.succ_cvarInjective
    have hbody'' :
        (cs.eraseCVars K).rename (Rename.succ (k := .var)) #
          (Γ0.eraseCVars K).kill_peaks_cs K,x:T1.eraseCVars K ⊢
          e0.eraseCVars (K.rename (Rename.succ (k := .var))) :
          T2.eraseCVars (K.rename (Rename.succ (k := .var))) := by
      rw [← hcs]
      exact hbody'
    simp only [Exp.eraseCVars, Ty.eraseCVars]
    exact .abs (hT.eraseCVars K) hbody''
  | @tabs s0 Γ0 e0 T cs S hS hbody ih =>
    have hbody' := ih (K.rename (Rename.succ (k := .tvar)))
    rw [Ctx.eraseCVars_push_tvar, Ctx.kill_peaks_cs_push_tvar] at hbody'
    have hcs :
        (cs.rename (Rename.succ (k := .tvar))).eraseCVars
            (K.rename (Rename.succ (k := .tvar)))
          = (cs.eraseCVars K).rename (Rename.succ (k := .tvar)) :=
      CaptureSet.eraseCVars_rename Rename.succ_cvarInjective
    have hbody'' :
        (cs.eraseCVars K).rename (Rename.succ (k := .tvar)) #
          (Γ0.eraseCVars K).kill_peaks_cs K,X<:S.eraseCVars K ⊢
          e0.eraseCVars (K.rename (Rename.succ (k := .tvar))) :
          T.eraseCVars (K.rename (Rename.succ (k := .tvar))) := by
      rw [← hcs]
      exact hbody'
    simp only [Exp.eraseCVars, Ty.eraseCVars,
      ← PureTy.core_eraseCVars]
    exact .tabs (hS.eraseCVars K) hbody''
  | @cabs s0 Γ0 e0 T cs cb hcb hvalid hbody ih =>
    have hbody' := ih (K.rename (Rename.succ (k := .cvar)))
    rw [Ctx.eraseCVars_push_cvar, Ctx.kill_peaks_cs_push_cvar] at hbody'
    have hcs :
        (cs.rename (Rename.succ (k := .cvar))).eraseCVars
            (K.rename (Rename.succ (k := .cvar)))
          = (cs.eraseCVars K).rename (Rename.succ (k := .cvar)) :=
      CaptureSet.eraseCVars_rename Rename.succ_cvarInjective
    have hbody'' :
        (cs.eraseCVars K).rename (Rename.succ (k := .cvar)) #
          (Γ0.eraseCVars K).kill_peaks_cs K,C[.access_only]<:cb.eraseCVars K ⊢
          e0.eraseCVars (K.rename (Rename.succ (k := .cvar))) :
          T.eraseCVars (K.rename (Rename.succ (k := .cvar))) := by
      rw [← hcs]
      exact hbody'
    simp only [Exp.eraseCVars, Ty.eraseCVars]
    exact .cabs (hcb.eraseCVars K) (hvalid.eraseCVars) hbody''
  | @consumer s0 cs0 e0 Γ0 E0 T1 X hT hdich hbody ih =>
    have hrename : (Rename.weakenCVars 1 : Rename s0 (s0,C))
        = Rename.succ (k := .cvar) := by
      apply Rename.funext
      intro k x
      rfl
    have hbody' := ih
      ((K.rename (Rename.succ (k := .cvar))).rename (Rename.succ (k := .var)))
    simp only [Ctx.kill_peaks,
      Ty.eraseCVars_rename Rename.succ_cvarInjective] at hbody'
    simp only [Exp.eraseCVars, Ty.eraseCVars]
    rw [hrename]
    refine .consumer (X := X) (hT.eraseCVars (K.rename (Rename.succ (k := .cvar)))) ?_ ?_
    · intro c hcan
      have hK : K.mentionsCVar c = false := by
        cases hm : K.mentionsCVar c with
        | false => rfl
        | true =>
          have hkilled :
              (((Γ0.eraseCVars K).kill_peaks_cs K).lookup_authority c) = .killed :=
            Ctx.kill_peaks_cs_lookup_authority_of_mentions (Γ := Γ0.eraseCVars K) hm
          rw [hkilled] at hcan
          cases hcan
      have hcan0 : Γ0.lookup_authority c = .can_drop := by
        rw [Ctx.kill_peaks_cs_lookup_authority_not_mentioned hK,
          Ctx.eraseCVars_lookup_authority] at hcan
        exact hcan
      rcases hdich c hcan0 with hX | hcs
      · exact Or.inl hX
      · rcases hcs with ⟨a, ha⟩
        exact Or.inr ⟨a, CaptureSet.cvar_subset_eraseCVars hK ha⟩
    · convert hbody' using 1
      · symm
        change
          (CaptureSet.union
              (CaptureSet.union ((cs0.rename (Rename.succ (k := .cvar))).rename
                (Rename.succ (k := .var)))
                (CaptureSet.cvar (.M .epsilon)
                  (BVar.there (BVar.here : BVar (s0,C) .cvar))))
              (CaptureSet.cvar .drop
                (BVar.there (BVar.here : BVar (s0,C) .cvar)))).eraseCVars
            ((K.rename (Rename.succ (k := .cvar))).rename (Rename.succ (k := .var)))
            =
          CaptureSet.union
            (CaptureSet.union
              (((cs0.eraseCVars K).rename (Rename.succ (k := .cvar))).rename
                (Rename.succ (k := .var)))
              (CaptureSet.cvar (.M .epsilon)
                (BVar.there (BVar.here : BVar (s0,C) .cvar))))
            (CaptureSet.cvar .drop
              (BVar.there (BVar.here : BVar (s0,C) .cvar)))
        rw [CaptureSet.eraseCVars_union, CaptureSet.eraseCVars_union]
        rw [CaptureSet.eraseCVars_rename Rename.succ_cvarInjective]
        rw [CaptureSet.eraseCVars_rename Rename.succ_cvarInjective]
        rw [CaptureSet.eraseCVars_consumer_bound_cvar,
          CaptureSet.eraseCVars_consumer_bound_cvar]
      · change
          Ctx.push_var
            (Ctx.push_cvar (((Γ0.eraseCVars K).kill_peaks_cs K).kill_peaks_cs X.cs)
              .can_drop .unbound)
            (T1.eraseCVars (K.rename (Rename.succ (k := .cvar))))
            =
          Ctx.kill_peaks_cs
            (Ctx.eraseCVars
              (Ctx.push_var (Ctx.push_cvar (Γ0.kill_peaks_cs X.cs) .can_drop .unbound)
                T1)
              ((K.rename (Rename.succ (k := .cvar))).rename (Rename.succ (k := .var))))
            ((K.rename (Rename.succ (k := .cvar))).rename (Rename.succ (k := .var)))
        exact (Ctx.erase_kill_consumer_body (Γ := Γ0) (K := K) (X := X) (T := T1)).symm
  | wrap hΨ hbody ih =>
    have hbody' := ih (K.rename (Rename.succ (k := .lock)))
    rw [Ctx.eraseCVars_push_lock, Ctx.kill_peaks_cs_push_lock,
      CaptureSet.eraseCVars_rename Rename.succ_cvarInjective,
      Exp.eraseCVars_rename Rename.succ_cvarInjective,
      Ty.eraseCVars_rename Rename.succ_cvarInjective] at hbody'
    simp only [Exp.eraseCVars, Ty.eraseCVars]
    exact .wrap (hΨ.eraseCVars K) hbody'
  | @pack s0 Γ0 x n Cs T hClosed hAccess hDrop hSep hvar ih =>
    have hvar' := ih K
    simp only [Exp.eraseCVars, Ty.eraseCVars] at hvar'
    rw [Ty.eraseCVars_subst_openCVars] at hvar'
    have hvar'' :
        {} # (Γ0.eraseCVars K).kill_peaks_cs K ⊢ Exp.var x :
          ((T.eraseCVars (K.rename (Rename.weakenCVars n))).subst
            (Subst.openCVars (Cs.map (·.eraseCVars K)))).typ := by
      simpa only [CaptureSet.eraseCVars_empty] using hvar'
    have hpack := HasType.pack
      (Cs := Cs.map (·.eraseCVars K))
      (T := T.eraseCVars (K.rename (Rename.weakenCVars n)))
      (by simpa only [CaptureSet.unionAll_eraseCVars] using hClosed.eraseCVars K)
      (by simpa only [CaptureSet.unionAll_eraseCVars] using hAccess.eraseCVars (K := K))
      (by simpa only [CaptureSet.unionAll_eraseCVars] using hDrop.eraseCVars (K := K))
      (hSep.erase_kill K) hvar''
    change ((CaptureSet.unionAll Cs).eraseCVars K
        ∪ ((CaptureSet.unionAll Cs).applyAccess .drop).eraseCVars K) #
      (Γ0.eraseCVars K).kill_peaks_cs K ⊢ Exp.pack (Cs.map (·.eraseCVars K)) x :
      Ty.exi n (T.eraseCVars (K.rename (Rename.weakenCVars n)))
    rw [CaptureSet.eraseCVars_applyAccess, ← CaptureSet.unionAll_eraseCVars]
    exact hpack
  | app hacc hfun harg ihfun iharg =>
    have hfun' := ihfun K
    have harg' := iharg K
    rw [Ty.eraseCVars_subst_openVar]
    simp only [CaptureSet.eraseCVars_var, Exp.eraseCVars, Ty.eraseCVars] at hfun' harg' ⊢
    exact .app (by simpa only [CaptureSet.eraseCVars_var] using hacc.eraseCVars (K := K))
      hfun' harg'
  | @consumer_app s0 Γ0 x E0 e0 C1 T1 hseq hdrop hacc hfun harg ihfun iharg =>
    simp only [Exp.eraseCVars]
    refine .consumer_app (hseq.erase_kill K) ?_
      (by simpa only [CaptureSet.eraseCVars_var] using hacc.eraseCVars (K := K))
      (ihfun K) (iharg K)
    intro a c hsub
    have hcs :
        (((C1.eraseCVars K).peakset ((Γ0.eraseCVars K).kill_peaks_cs K)).consumed).cs
          = (((C1.peakset Γ0).consumed).cs).eraseCVars K :=
      CaptureSet.consumed_peakset_eraseCVars_kill_cs
    exact hdrop.eraseCVars a c
      (Eq.mp (congrArg (fun D => CaptureSet.cvar a c ⊆ D) hcs) hsub)
  | tapp hacc hS hfun ihfun =>
    have hfun' := ihfun K
    rw [Ty.eraseCVars_subst_openTVar]
    simp only [CaptureSet.eraseCVars_var, Exp.eraseCVars, Ty.eraseCVars,
      ← PureTy.core_eraseCVars] at hfun' ⊢
    exact .tapp (by simpa only [CaptureSet.eraseCVars_var] using hacc.eraseCVars (K := K))
      (hS.eraseCVars K) hfun'
  | @capp s0 x Γ0 T D I hacc hD hvalid hfun ihfun =>
    have hfun' := ihfun K
    rw [Ty.eraseCVars_subst_openCVar]
    simp only [CaptureSet.eraseCVars_var, Exp.eraseCVars, Ty.eraseCVars] at hfun' ⊢
    exact .capp (I := I.eraseCVars K)
      (by simpa only [CaptureSet.eraseCVars_var] using hacc.eraseCVars (K := K))
      (hD.eraseCVars K) (hvalid.eraseCVars) hfun'
  | unwrap hfun hsat ihfun =>
    have hfun' := ihfun K
    simp only [CaptureSet.eraseCVars_var, Exp.eraseCVars, Ty.eraseCVars] at hfun' ⊢
    exact .unwrap hfun' (hsat.erase_kill K)
  | @letin s0 Γ0 C1 C2 e1 T e2 U hseq h1 h2 ih1 ih2 =>
    have h2' := ih2 (K.rename (Rename.succ (k := .var)))
    rw [CaptureSet.eraseCVars_rename Rename.succ_cvarInjective,
      Ty.eraseCVars_rename Rename.succ_cvarInjective] at h2'
    change (C2.eraseCVars K).rename (Rename.succ (k := .var)) #
      Ctx.kill_peaks_cs
        (Ctx.eraseCVars
          (Ctx.push_var (Γ0.kill_peaks ((C1.peakset Γ0).consumed)) T)
          (K.rename (Rename.succ (k := .var))))
        (K.rename (Rename.succ (k := .var))) ⊢
      e2.eraseCVars (K.rename (Rename.succ (k := .var))) :
      (U.eraseCVars K).rename (Rename.succ (k := .var)) at h2'
    simp only [Exp.eraseCVars]
    refine .letin (hseq.erase_kill K) (ih1 K) ?_
    convert h2' using 1
    exact (Ctx.erase_kill_letin_body (Γ := Γ0) (K := K) (C1 := C1) (T := T)).symm
  | @unpack s0 Γ0 C1 C2 t U n T u hseq hdrop ht hu iht ihu =>
    have hbody := ihu
      (((K.rename (Rename.weakenCVars n)).rename (Rename.succ (k := .lock))).rename
        (Rename.succ (k := .var)))
    simp only [Exp.eraseCVars]
    refine .unpack (hseq.erase_kill K) ?_ (iht K) ?_
    · intro a c hsub
      have hcs :
          (((C1.eraseCVars K).peakset ((Γ0.eraseCVars K).kill_peaks_cs K)).consumed).cs
            = (((C1.peakset Γ0).consumed).cs).eraseCVars K :=
        CaptureSet.consumed_peakset_eraseCVars_kill_cs
      exact hdrop.eraseCVars a c
        (Eq.mp (congrArg (fun D => CaptureSet.cvar a c ⊆ D) hcs) hsub)
    · convert hbody using 1
      · exact (CaptureSet.eraseCVars_unpack_uses (C2 := C2) (K := K) (n := n)).symm
      · exact (Ctx.erase_kill_unpack_body (Γ := Γ0) (K := K) (C1 := C1)
          (C2 := C2) (n := n) (T := T)).symm
      · have hKbody :
            (((K.rename (Rename.weakenCVars n)).rename
                  (Rename.succ (k := .lock))).rename (Rename.succ (k := .var)))
              =
            ((K.rename (Rename.weakenCVars n)).rename
                (Rename.succ (k := .var))).rename
              ((Rename.succ (k := .lock)).lift (k := .var)) :=
          CaptureSet.rename_succ_lift
        calc
          (u.eraseCVars
              ((K.rename (Rename.weakenCVars n)).rename
                (Rename.succ (k := .var)))).rename
              ((Rename.succ (k := .lock)).lift (k := .var))
              =
            (u.rename ((Rename.succ (k := .lock)).lift (k := .var))).eraseCVars
              (((K.rename (Rename.weakenCVars n)).rename
                (Rename.succ (k := .var))).rename
                ((Rename.succ (k := .lock)).lift (k := .var))) := by
                exact (Exp.eraseCVars_rename
                  (Rename.CVarInjective.lift Rename.succ_cvarInjective)).symm
          _ =
            (u.rename ((Rename.succ (k := .lock)).lift (k := .var))).eraseCVars
              (((K.rename (Rename.weakenCVars n)).rename
                (Rename.succ (k := .lock))).rename (Rename.succ (k := .var))) := by
                rw [← hKbody]
      · symm
        rw [Ty.eraseCVars_rename Rename.succ_cvarInjective,
          Ty.eraseCVars_rename Rename.succ_cvarInjective,
          Ty.eraseCVars_rename Rename.weakenCVars_cvarInjective]
  | unit =>
    simp only [Exp.eraseCVars, Ty.eraseCVars]
    exact .unit
  | btrue =>
    simp only [Exp.eraseCVars, Ty.eraseCVars]
    exact .btrue
  | bfalse =>
    simp only [Exp.eraseCVars, Ty.eraseCVars]
    exact .bfalse
  | @alloc s0 Γ0 x T hvar ih =>
    have hvar' := ih K
    simp only [Exp.eraseCVars, Ty.eraseCVars] at hvar' ⊢
    have hvar'' : {} # (Γ0.eraseCVars K).kill_peaks_cs K ⊢ Exp.var x :
        (T.eraseCVars K).typ := by
      simpa only [CaptureSet.eraseCVars_empty] using hvar'
    have hrename : (Rename.weakenCVars 1 : Rename s0 (s0,C))
        = Rename.succ (k := .cvar) := by
      apply Rename.funext
      intro k x
      rfl
    rw [hrename]
    change {} # (Γ0.eraseCVars K).kill_peaks_cs K ⊢ Exp.alloc x :
      Ty.exi 1
        (Ty.cell ((CaptureSet.cvar (.M .epsilon) BVar.here).eraseCVars
            (K.rename (Rename.succ (k := .cvar))))
          ((T.rename (Rename.succ (k := .cvar))).eraseCVars
            (K.rename (Rename.succ (k := .cvar)))))
    have hTy :
        Ty.exi 1
            (Ty.cell ((CaptureSet.cvar (.M .epsilon) BVar.here).eraseCVars
                (K.rename (Rename.succ (k := .cvar))))
              ((T.rename (Rename.succ (k := .cvar))).eraseCVars
                (K.rename (Rename.succ (k := .cvar)))))
          =
        Ty.exi 1
          (Ty.cell (CaptureSet.cvar (.M .epsilon) BVar.here)
            ((T.eraseCVars K).rename (Rename.succ (k := .cvar)))) := by
      have hC :
          ((CaptureSet.cvar (.M .epsilon) (BVar.here : BVar (s0,C) .cvar)).eraseCVars
              (K.rename (Rename.succ (k := .cvar))))
            = CaptureSet.cvar (.M .epsilon) BVar.here :=
        CaptureSet.eraseCVars_fresh_succ_cvar
      have hT' :
          (T.rename (Rename.succ (k := .cvar))).eraseCVars
              (K.rename (Rename.succ (k := .cvar)))
            = (T.eraseCVars K).rename (Rename.succ (k := .cvar)) :=
        Ty.eraseCVars_rename Rename.succ_cvarInjective
      exact congrArg₂
        (fun (C0 : CaptureSet (s0,C)) (T0 : Ty .capt (s0,C)) =>
          Ty.exi 1 (Ty.cell C0 T0)) hC hT'
    exact hTy.symm ▸ HasType.alloc hvar''
  | drop hΓ hdrop hvar ih =>
    have hvar' := ih K
    simp only [CaptureSet.eraseCVars_var, Exp.eraseCVars, Ty.eraseCVars] at hvar' ⊢
    exact .drop (Ctx.kill_peaks_cs_isClosed (hΓ.eraseCVars K))
      (by simpa only [CaptureSet.eraseCVars_var] using hdrop.eraseCVars (K := K)) hvar'
  | read hacc hvar ih =>
    have hvar' := ih K
    simp only [CaptureSet.eraseCVars_var, Exp.eraseCVars, Ty.eraseCVars] at hvar' ⊢
    exact .read (by simpa only [CaptureSet.eraseCVars_var] using hacc.eraseCVars (K := K))
      hvar'
  | write hacc hx hy ihx ihy =>
    have hx' := ihx K
    have hy' := ihy K
    simp only [CaptureSet.eraseCVars_var, Exp.eraseCVars, Ty.eraseCVars] at hx' hy' ⊢
    exact .write (by simpa only [CaptureSet.eraseCVars_var] using hacc.eraseCVars (K := K))
      hx' hy'
  | cond hx h2 h3 ihx ih2 ih3 =>
    simp only [Exp.eraseCVars]
    exact .cond (ihx K) (ih2 K) (ih3 K)
  | par h1 h2 hsep ih1 ih2 =>
    simp only [Exp.eraseCVars, Ty.eraseCVars]
    exact .par (ih1 K) (ih2 K) (hsep.erase_kill K)
  | invoke hacc hx hy ihx ihy =>
    have hx' := ihx K
    have hy' := ihy K
    simp only [CaptureSet.eraseCVars_var, Exp.eraseCVars, Ty.eraseCVars] at hx' hy' ⊢
    exact .invoke (by simpa only [CaptureSet.eraseCVars_var] using hacc.eraseCVars (K := K))
      hx' hy'
  | subtyp hty hsc hsub hC hE ih =>
    exact .subtyp (ih K) (hsc.erase_kill K) (hsub.erase_kill K)
      (hC.eraseCVars K) (hE.eraseCVars K)

/-! ## §2.1 The paper lemma (L9) and its peak-set wrapper (L9') -/

/-- Paper Lemma [Kill weakening] (`lem:tr:kill`, ledger H2): if erasing the killed
    variables `K` fixes the use set, term, result type, and context, then killing `K`
    in the context preserves typing. -/
theorem HasType.kill_weakening {s : Sig} {C : CaptureSet s} {Γ : Ctx s} {e : Exp s}
    {E : Ty .exi s} {K : CaptureSet s}
    (h : HasType C Γ e E)
    (hC : C.eraseCVars K = C) (he : e.eraseCVars K = e)
    (hE : E.eraseCVars K = E) (hΓ : Γ.eraseCVars K = Γ) :
    HasType C (Γ.kill_peaks_cs K) e E := by
  have h' := h.erase_kill K
  rw [hC, he, hE, hΓ] at h'
  exact h'

/-- Peak-set form matching the `letin`/`unpack`/`consumer_app` kill shape. -/
theorem HasType.kill_peaks_weakening {s : Sig} {C : CaptureSet s} {Γ : Ctx s} {e : Exp s}
    {E : Ty .exi s} {P : PeakSet s}
    (h : HasType C Γ e E)
    (hC : C.eraseCVars P.cs = C) (he : e.eraseCVars P.cs = e)
    (hE : E.eraseCVars P.cs = E) (hΓ : Γ.eraseCVars P.cs = Γ) :
    HasType C (Γ.kill_peaks P) e E := by
  have h' := h.kill_weakening (K := P.cs) hC he hE hΓ
  simpa only [Ctx.kill_peaks] using h'

end CoreCapybara
