import Semantic.CoreCapybara.Syntax.CaptureSet

namespace CoreCapybara

/-- A separation constraint: a list of capture sets that are meant to be
pairwise separated. This carries *no* mutability information; mutability is
tracked separately by `MutabilityCtx`. -/
inductive SepCtx : Sig -> Type where
| empty : SepCtx s
| cons :
  SepCtx s ->
  CaptureSet s ->
  SepCtx s

/-- A mutability constraint: a list of capture sets each tagged with the
mutability (kind) it is expected to have. -/
inductive MutabilityCtx : Sig -> Type where
| empty : MutabilityCtx s
| cons :
  MutabilityCtx s ->
  CaptureSet s ->
  Mutability ->
  MutabilityCtx s

/-- A modal context, bundling the (mutability-free) separation discipline with
the mutability discipline. This is what the `modal` type, the `boxed` value, and
the `lock` binder carry. -/
structure ModalCtx (s : Sig) : Type where
  sep : SepCtx s
  mutability : MutabilityCtx s

/-! ## Separation context -/

/-- Membership in a separation context. -/
inductive SepCtx.Has : SepCtx s -> CaptureSet s -> Prop where
| here : SepCtx.Has (.cons K C) C
| there : SepCtx.Has K C -> SepCtx.Has (.cons K C') C

/-- Two distinct entries occur in a separation context. -/
inductive SepCtx.HasTwoDistinct :
    SepCtx s -> CaptureSet s -> CaptureSet s -> Prop where
| here_there :
    SepCtx.Has K C2 ->
    SepCtx.HasTwoDistinct (.cons K C1) C1 C2
| there :
    SepCtx.HasTwoDistinct K C1 C2 ->
    SepCtx.HasTwoDistinct (.cons K C) C1 C2
| symm :
    SepCtx.HasTwoDistinct K C1 C2 ->
    SepCtx.HasTwoDistinct K C2 C1

private theorem SepCtx.HasTwoDistinct.has_left_right
    (h : SepCtx.HasTwoDistinct K C1 C2) :
    SepCtx.Has K C1 ∧ SepCtx.Has K C2 := by
  induction h with
  | here_there hhas =>
    exact ⟨.here, .there hhas⟩
  | there _ ih =>
    exact ⟨.there ih.1, .there ih.2⟩
  | symm _ ih =>
    exact ⟨ih.2, ih.1⟩

theorem SepCtx.HasTwoDistinct.left
    (h : SepCtx.HasTwoDistinct K C1 C2) :
    SepCtx.Has K C1 :=
  (SepCtx.HasTwoDistinct.has_left_right h).1

theorem SepCtx.HasTwoDistinct.right
    (h : SepCtx.HasTwoDistinct K C1 C2) :
    SepCtx.Has K C2 :=
  (SepCtx.HasTwoDistinct.has_left_right h).2

/-- Applies a renaming to all bound variables in a separation context. -/
def SepCtx.rename : SepCtx s1 -> Rename s1 s2 -> SepCtx s2
| .empty, _ => .empty
| .cons K C, ρ => .cons (K.rename ρ) (C.rename ρ)

/-- Renaming by the identity renaming leaves a separation context unchanged. -/
theorem SepCtx.rename_id {K : SepCtx s} :
    K.rename Rename.id = K := by
  induction K with
  | empty => rfl
  | cons K C ih =>
    simp only [SepCtx.rename, ih, CaptureSet.rename_id]

/-- Renaming distributes over composition of renamings. -/
theorem SepCtx.rename_comp
    {K : SepCtx s1} {f : Rename s1 s2} {g : Rename s2 s3} :
    (K.rename f).rename g = K.rename (f.comp g) := by
  induction K generalizing s2 s3 with
  | empty => rfl
  | cons K C ih =>
    simp only [SepCtx.rename, ih, CaptureSet.rename_comp]

theorem SepCtx.Has.rename
    {K : SepCtx s1} {f : Rename s1 s2}
    (h : SepCtx.Has K C) :
    SepCtx.Has (K.rename f) (C.rename f) := by
  induction h with
  | here => simp only [SepCtx.rename]; exact .here
  | there h ih => simp only [SepCtx.rename]; exact .there ih

theorem SepCtx.Has.rename_inv
    {K : SepCtx s1} {f : Rename s1 s2}
    (h : SepCtx.Has (K.rename f) C) :
    ∃ C0, C = C0.rename f ∧ SepCtx.Has K C0 := by
  induction K with
  | empty =>
    cases h
  | cons K C0 ih =>
    simp only [SepCtx.rename] at h
    cases h with
    | here =>
      exact ⟨C0, rfl, .here⟩
    | there h' =>
      obtain ⟨C1, hC1, hh⟩ := ih h'
      exact ⟨C1, hC1, .there hh⟩

theorem SepCtx.HasTwoDistinct.rename
    {K : SepCtx s1} {f : Rename s1 s2}
    (h : SepCtx.HasTwoDistinct K C1 C2) :
    SepCtx.HasTwoDistinct (K.rename f) (C1.rename f) (C2.rename f) := by
  induction h with
  | here_there hhas =>
    simp only [SepCtx.rename]
    exact .here_there (hhas.rename)
  | there h ih =>
    simp only [SepCtx.rename]
    exact .there ih
  | symm h ih =>
    exact .symm ih

theorem SepCtx.HasTwoDistinct.rename_inv
    {K : SepCtx s1} {f : Rename s1 s2}
    (h : SepCtx.HasTwoDistinct (K.rename f) C1 C2) :
    ∃ D1 D2,
      C1 = D1.rename f ∧
      C2 = D2.rename f ∧
      SepCtx.HasTwoDistinct K D1 D2 := by
    generalize he0 : K.rename f = K0 at h
    induction h generalizing K
    case here_there hhas =>
      cases K with
      | empty =>
        simp only [SepCtx.rename] at he0
        cases he0
      | cons K1 C0 =>
        have heq := he0
        simp only [SepCtx.rename] at heq
        injection heq with hK hC
        subst hK hC
        obtain ⟨D2, hD2, hh⟩ := SepCtx.Has.rename_inv hhas
        exact ⟨C0, D2, rfl, hD2, .here_there hh⟩
    case there a ih =>
      cases K with
      | empty =>
        simp only [SepCtx.rename] at he0
        cases he0
      | cons K1 C0 =>
        have heq := he0
        simp only [SepCtx.rename] at heq
        injection heq with hK hC
        obtain ⟨D1, D2, hD1, hD2, hh⟩ := ih hK
        exact ⟨D1, D2, hD1, hD2, .there hh⟩
    case symm a ih =>
      obtain ⟨D2, D1, hD2, hD1, hh⟩ := ih he0
      exact ⟨D1, D2, hD1, hD2, .symm hh⟩

/-- A separation context is closed if it contains no heap pointers. -/
inductive SepCtx.IsClosed : SepCtx s -> Prop where
| empty : SepCtx.IsClosed .empty
| cons : SepCtx.IsClosed K -> CaptureSet.IsClosed C -> SepCtx.IsClosed (.cons K C)

/-! ## Mutability context -/

/-- Membership in a mutability context, recording the expected kind. -/
inductive MutabilityCtx.Has : MutabilityCtx s -> CaptureSet s -> Mutability -> Prop where
| here : MutabilityCtx.Has (.cons K C m) C m
| there : MutabilityCtx.Has K C m -> MutabilityCtx.Has (.cons K C' m') C m

/-- Applies a renaming to all bound variables in a mutability context. -/
def MutabilityCtx.rename : MutabilityCtx s1 -> Rename s1 s2 -> MutabilityCtx s2
| .empty, _ => .empty
| .cons K C m, ρ => .cons (K.rename ρ) (C.rename ρ) m

/-- Renaming by the identity renaming leaves a mutability context unchanged. -/
theorem MutabilityCtx.rename_id {K : MutabilityCtx s} :
    K.rename Rename.id = K := by
  induction K with
  | empty => rfl
  | cons K C m ih =>
    simp only [MutabilityCtx.rename, ih, CaptureSet.rename_id]

/-- Renaming distributes over composition of renamings. -/
theorem MutabilityCtx.rename_comp
    {K : MutabilityCtx s1} {f : Rename s1 s2} {g : Rename s2 s3} :
    (K.rename f).rename g = K.rename (f.comp g) := by
  induction K generalizing s2 s3 with
  | empty => rfl
  | cons K C m ih =>
    simp only [MutabilityCtx.rename, ih, CaptureSet.rename_comp]

theorem MutabilityCtx.Has.rename
    {K : MutabilityCtx s1} {f : Rename s1 s2}
    (h : MutabilityCtx.Has K C m) :
    MutabilityCtx.Has (K.rename f) (C.rename f) m := by
  induction h with
  | here => simp only [MutabilityCtx.rename]; exact .here
  | there h ih => simp only [MutabilityCtx.rename]; exact .there ih

theorem MutabilityCtx.Has.rename_inv
    {K : MutabilityCtx s1} {f : Rename s1 s2}
    (h : MutabilityCtx.Has (K.rename f) C m) :
    ∃ C0, C = C0.rename f ∧ MutabilityCtx.Has K C0 m := by
  induction K with
  | empty =>
    cases h
  | cons K C0 m0 ih =>
    simp only [MutabilityCtx.rename] at h
    cases h with
    | here =>
      exact ⟨C0, rfl, .here⟩
    | there h' =>
      obtain ⟨C1, hC1, hh⟩ := ih h'
      exact ⟨C1, hC1, .there hh⟩

/-- A mutability context is closed if it contains no heap pointers. -/
inductive MutabilityCtx.IsClosed : MutabilityCtx s -> Prop where
| empty : MutabilityCtx.IsClosed .empty
| cons : MutabilityCtx.IsClosed K -> CaptureSet.IsClosed C -> MutabilityCtx.IsClosed (.cons K C m)

/-! ## Modal context -/

/-- Applies a renaming to a modal context, componentwise. -/
def ModalCtx.rename (Ψ : ModalCtx s1) (f : Rename s1 s2) : ModalCtx s2 :=
  ⟨Ψ.sep.rename f, Ψ.mutability.rename f⟩

@[simp] theorem ModalCtx.rename_sep {Ψ : ModalCtx s1} {f : Rename s1 s2} :
    (Ψ.rename f).sep = Ψ.sep.rename f := rfl

@[simp] theorem ModalCtx.rename_mutability {Ψ : ModalCtx s1} {f : Rename s1 s2} :
    (Ψ.rename f).mutability = Ψ.mutability.rename f := rfl

/-- Renaming by the identity renaming leaves a modal context unchanged. -/
theorem ModalCtx.rename_id {Ψ : ModalCtx s} :
    Ψ.rename Rename.id = Ψ := by
  cases Ψ with
  | mk sep mu =>
    simp only [ModalCtx.rename, SepCtx.rename_id, MutabilityCtx.rename_id]

/-- Renaming distributes over composition of renamings. -/
theorem ModalCtx.rename_comp
    {Ψ : ModalCtx s1} {f : Rename s1 s2} {g : Rename s2 s3} :
    (Ψ.rename f).rename g = Ψ.rename (f.comp g) := by
  cases Ψ with
  | mk sep mu =>
    simp only [ModalCtx.rename, SepCtx.rename_comp, MutabilityCtx.rename_comp]

/-- A modal context is closed if both components are. -/
structure ModalCtx.IsClosed (Ψ : ModalCtx s) : Prop where
  sep : Ψ.sep.IsClosed
  mutability : Ψ.mutability.IsClosed

end CoreCapybara
