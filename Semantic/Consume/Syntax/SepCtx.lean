import Semantic.Consume.Syntax.CaptureSet

namespace Consume

/-- A separation constraint. -/
inductive SepCtx : Sig -> Type where
| empty : SepCtx s
| cons :
  SepCtx s ->
  CaptureSet s ->
  Mutability ->
  SepCtx s

/-- Membership in a separation context. -/
inductive SepCtx.Has : SepCtx s -> CaptureSet s -> Mutability -> Prop where
| here : SepCtx.Has (.cons K C m) C m
| there : SepCtx.Has K C m -> SepCtx.Has (.cons K C' m') C m

/-- Two distinct entries occur in a separation context. -/
inductive SepCtx.HasTwoDistinct :
    SepCtx s -> CaptureSet s -> Mutability -> CaptureSet s -> Mutability -> Prop where
| here_there :
    SepCtx.Has K C2 m2 ->
    SepCtx.HasTwoDistinct (.cons K C1 m1) C1 m1 C2 m2
| there :
    SepCtx.HasTwoDistinct K C1 m1 C2 m2 ->
    SepCtx.HasTwoDistinct (.cons K C m) C1 m1 C2 m2
| symm :
    SepCtx.HasTwoDistinct K C1 m1 C2 m2 ->
    SepCtx.HasTwoDistinct K C2 m2 C1 m1

private theorem SepCtx.HasTwoDistinct.has_left_right
    (h : SepCtx.HasTwoDistinct K C1 m1 C2 m2) :
    SepCtx.Has K C1 m1 ∧ SepCtx.Has K C2 m2 := by
  induction h with
  | here_there hhas =>
    exact ⟨.here, .there hhas⟩
  | there _ ih =>
    exact ⟨.there ih.1, .there ih.2⟩
  | symm _ ih =>
    exact ⟨ih.2, ih.1⟩

theorem SepCtx.HasTwoDistinct.left
    (h : SepCtx.HasTwoDistinct K C1 m1 C2 m2) :
    SepCtx.Has K C1 m1 :=
  (SepCtx.HasTwoDistinct.has_left_right h).1

theorem SepCtx.HasTwoDistinct.right
    (h : SepCtx.HasTwoDistinct K C1 m1 C2 m2) :
    SepCtx.Has K C2 m2 :=
  (SepCtx.HasTwoDistinct.has_left_right h).2

/-- Applies a renaming to all bound variables in a separation context. -/
def SepCtx.rename : SepCtx s1 -> Rename s1 s2 -> SepCtx s2
| .empty, _ => .empty
| .cons K C m, ρ => .cons (K.rename ρ) (C.rename ρ) m

/-- Renaming by the identity renaming leaves a separation context unchanged. -/
theorem SepCtx.rename_id {K : SepCtx s} :
    K.rename Rename.id = K := by
  induction K with
  | empty => rfl
  | cons K C m ih =>
    simp [SepCtx.rename, ih, CaptureSet.rename_id]

/-- Renaming distributes over composition of renamings. -/
theorem SepCtx.rename_comp
    {K : SepCtx s1} {f : Rename s1 s2} {g : Rename s2 s3} :
    (K.rename f).rename g = K.rename (f.comp g) := by
  induction K generalizing s2 s3 with
  | empty => rfl
  | cons K C m ih =>
    simp [SepCtx.rename, ih, CaptureSet.rename_comp]

theorem SepCtx.Has.rename
    {K : SepCtx s1} {f : Rename s1 s2}
    (h : SepCtx.Has K C m) :
    SepCtx.Has (K.rename f) (C.rename f) m := by
  induction h with
  | here => simp [SepCtx.rename]; exact .here
  | there h ih => simp [SepCtx.rename]; exact .there ih

theorem SepCtx.Has.rename_inv
    {K : SepCtx s1} {f : Rename s1 s2}
    (h : SepCtx.Has (K.rename f) C m) :
    ∃ C0, C = C0.rename f ∧ SepCtx.Has K C0 m := by
  induction K with
  | empty =>
    cases h
  | cons K C0 m0 ih =>
    simp [SepCtx.rename] at h
    cases h with
    | here =>
      exact ⟨C0, rfl, .here⟩
    | there h' =>
      obtain ⟨C1, hC1, hh⟩ := ih h'
      exact ⟨C1, hC1, .there hh⟩

theorem SepCtx.HasTwoDistinct.rename
    {K : SepCtx s1} {f : Rename s1 s2}
    (h : SepCtx.HasTwoDistinct K C1 m1 C2 m2) :
    SepCtx.HasTwoDistinct (K.rename f) (C1.rename f) m1 (C2.rename f) m2 := by
  induction h with
  | here_there hhas =>
    simp [SepCtx.rename]
    exact .here_there (hhas.rename)
  | there h ih =>
    simp [SepCtx.rename]
    exact .there ih
  | symm h ih =>
    exact .symm ih

theorem SepCtx.HasTwoDistinct.rename_inv
    {K : SepCtx s1} {f : Rename s1 s2}
    (h : SepCtx.HasTwoDistinct (K.rename f) C1 m1 C2 m2) :
    ∃ D1 D2,
      C1 = D1.rename f ∧
      C2 = D2.rename f ∧
      SepCtx.HasTwoDistinct K D1 m1 D2 m2 := by
    generalize he0 : K.rename f = K0 at h
    induction h generalizing K
    case here_there hhas =>
      cases K with
      | empty =>
        simp [SepCtx.rename] at he0
      | cons K1 C0 m0 =>
        simp [SepCtx.rename] at he0
        rcases he0 with ⟨hK, hC, hm⟩
        subst hK hC hm
        obtain ⟨D2, hD2, hh⟩ := SepCtx.Has.rename_inv hhas
        exact ⟨C0, D2, rfl, hD2, .here_there hh⟩
    case there a ih =>
      cases K with
      | empty => simp [SepCtx.rename] at he0
      | cons K1 C0 m0 =>
        simp [SepCtx.rename] at he0
        rcases he0 with ⟨hK, hC, hm⟩
        subst hC hm
        obtain ⟨D1, D2, hD1, hD2, hh⟩ := ih hK
        exact ⟨D1, D2, hD1, hD2, .there hh⟩
    case symm a ih =>
      obtain ⟨D2, D1, hD2, hD1, hh⟩ := ih he0
      exact ⟨D1, D2, hD1, hD2, .symm hh⟩

/-- A separation context is closed if it contains no heap pointers. -/
inductive SepCtx.IsClosed : SepCtx s -> Prop where
| empty : SepCtx.IsClosed .empty
| cons : SepCtx.IsClosed K -> CaptureSet.IsClosed C -> SepCtx.IsClosed (.cons K C m)

end Consume
