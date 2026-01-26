import Semantic.CaplessK.Syntax.Classifier.Subtract
import Semantic.CaplessK.Syntax.Classifier.Semantics

namespace CaplessK

/-- `K` is a subkind of `L` if every node in `K` is present in `L`. -/
inductive CapKind.Subkind : CapKind -> CapKind -> Prop where
  | subtract : Subtract K1 K2 R -> IsEmpty R -> Subkind K1 K2

theorem CapKind.Subkind.empty_r_inv (hs : Subkind K1 K2) (he : IsEmpty K2) : IsEmpty K1 := by
  cases hs
  apply! Subtract.empty_r_inv

/-- Subtract-defined subkinding agrees with semantic subkinding. -/
theorem CapKind.Subkind.semantics : Subkind A B ↔ SSubkind A B := by
  apply Iff.intro <;> intro h
  · cases h
    rename_i h he
    simp_all [← h.is_empty_is_subkind]
  · have ⟨R, h⟩ := Subtract.exists A B
    apply subtract h
    simp_all [h.is_empty_is_subkind]

theorem CapKind.Subkind.rfl : Subkind A A := by apply semantics.mpr SSubkind.rfl

theorem CapKind.Subkind.trans (ha : Subkind A B) (hb : Subkind B C) : Subkind A C := by
  rw [semantics] at *
  apply! SSubkind.trans

theorem CapKind.Subkind.of_top : Subkind A .top := by
  rw [semantics]
  intro c hc
  exact .here (.sub .of_top)

theorem CapKind.Subkind.of_empty
    (hs : Subkind K L)
    (he : L.IsEmpty)
    : K.IsEmpty := by
  cases hs
  case subtract hs he1 => apply! hs.empty_r_inv

theorem CapKind.Subkind.union_rl : Subkind K (K ++ L) := by
  rw [semantics]
  intro c hc
  apply! Contains.append_r

theorem CapKind.Subkind.union_rr : Subkind L (K ++ L) := by
  rw [semantics]
  intro c hc
  apply! Contains.append_l

theorem CapKind.Subkind.union_l (ha : Subkind K1 L) (hb : Subkind K2 L) : Subkind (K1 ++ K2) L := by
  rw [semantics] at *
  intro c hc
  cases hc.append_inv <;> rename_i hc
  · apply ha c hc
  · apply hb c hc

theorem CapKind.Subkind.join
    (hs1 : Subkind K1 L1)
    (hs2 : Subkind K2 L2)
    : Subkind (K1 ++ K2) (L1 ++ L2) := by
  apply union_l
  · apply trans hs1 .union_rl
  · apply trans hs2 .union_rr

theorem CapKind.Subkind.is_empty_l
    (he : IsEmpty K)
    : Subkind K L := by
  rw [semantics]
  rw [← SEmpty.is_empty] at he
  intro c hc
  cases he c hc

-- ** Functional versions **

/-- Functional version of `Subtree.Subtract`: compute the subtraction of two subtrees. -/
def Subtree.subtract (a b : Subtree) : CapKind :=
  subtractAux a.root a.excls b.root b.excls
where
  subtractAux (r1 : Classifier) (ex1 : List Classifier) (r2 : Classifier)
      : List Classifier -> CapKind
  | [] => .node r1 (r2 :: ex1)
  | head :: tail =>
    if head.subclass r2 then
      -- head is subclass of r2
      if head.subclass r1 then
        -- excl_subclass_r
        (.mk head ex1) :: subtractAux r1 ex1 r2 tail
      else if r1.subclass head then
        -- r1 strictly inside head (since head.subclass r1 is false)
        -- excl_subclass_l
        .node r1 ex1
      else
        -- r1 disjoint from head
        -- excl_irrelevant_l
        subtractAux r1 ex1 r2 tail
    else if r2.subclass head then
      -- r2 strictly inside head (since head.subclass r2 is false)
      -- excl_absurd_r
      .node r1 ex1
    else
      -- head disjoint from r2
      -- excl_irrelevant_r
      subtractAux r1 ex1 r2 tail

/-- Functional version of `CapKind.Subtract` for subtracting by a single subtree. -/
def CapKind.subtract' (a : CapKind) (b : Subtree) : CapKind :=
  match a with
  | [] => []
  | x :: xs => x.subtract b ++ subtract' xs b

/-- Functional version of `CapKind.Subtract`. -/
def CapKind.subtract (a b : CapKind) : CapKind :=
  match b with
  | [] => a
  | [y] => a.subtract' y
  | y :: y' :: ys => (a.subtract' y).subtract (y' :: ys)

/-- Functional version of `Subkind`: is K1 a subkind of K2? -/
def CapKind.subkind (K1 K2 : CapKind) : Bool :=
  (K1.subtract K2).isEmpty

-- ** Equivalence theorems **

/-- The functional subtraction produces a valid Subtract relation. -/
theorem Subtree.Subtract_of_subtract : Subtree.Subtract a b (a.subtract b) := by
  cases a with | mk r1 ex1 =>
  cases b with | mk r2 ex2 =>
  simp only [subtract]
  induction ex2 generalizing r1 ex1 r2 with
  | nil =>
    simp [subtract.subtractAux]
    exact .tree
  | cons head tail ih =>
    simp only [subtract.subtractAux]
    split
    case isTrue hsub2 =>
      -- hsub2 : head.subclass r2 = true
      have hsub2' : head.Subclass r2 := Classifier.subclass_is_Subclass.mpr hsub2
      split
      case isTrue hsub1 =>
        -- hsub1 : head.subclass r1 = true
        have hsub1' : head.Subclass r1 := Classifier.subclass_is_Subclass.mpr hsub1
        apply Subtree.Subtract.excl_subclass_r hsub2' hsub1'
        exact ih r1 ex1 r2
      case isFalse hnsub1 =>
        -- hnsub1 : ¬ head.subclass r1 = true
        split
        case isTrue hsub1' =>
          -- hsub1' : r1.subclass head = true
          have hsub1'' : r1.Subclass head := Classifier.subclass_is_Subclass.mpr hsub1'
          apply Subtree.Subtract.excl_subclass_l hsub2'
          cases hsub1''.might_strict with
          | inl heq =>
            subst heq
            exact absurd (Classifier.subclass_is_Subclass.mp .rfl) hnsub1
          | inr hss => exact hss
        case isFalse hnsub1' =>
          -- hnsub1' : ¬ r1.subclass head = true
          apply Subtree.Subtract.excl_irrelevant_l hsub2'
          · cases Classifier.subclass_or_disjoint head r1 with
            | inl h => exact absurd (Classifier.subclass_is_Subclass.mp h) hnsub1
            | inr h => cases h with
              | inl h => exact absurd (Classifier.subclass_is_Subclass.mp h.weaken) hnsub1'
              | inr h => exact h.symm
          · exact ih r1 ex1 r2
    case isFalse hnsub2 =>
      -- hnsub2 : ¬ head.subclass r2 = true
      split
      case isTrue hsub2' =>
        -- hsub2' : r2.subclass head = true
        have hsub2'' : r2.Subclass head := Classifier.subclass_is_Subclass.mpr hsub2'
        apply Subtree.Subtract.excl_absurd_r
        cases hsub2''.might_strict with
        | inl heq =>
          subst heq
          exact absurd (Classifier.subclass_is_Subclass.mp .rfl) hnsub2
        | inr hss => exact hss
      case isFalse hnsub2' =>
        -- hnsub2' : ¬ r2.subclass head = true
        apply Subtree.Subtract.excl_irrelevant_r
        · cases Classifier.subclass_or_disjoint head r2 with
          | inl h => exact absurd (Classifier.subclass_is_Subclass.mp h) hnsub2
          | inr h => cases h with
            | inl h => exact absurd (Classifier.subclass_is_Subclass.mp h.weaken) hnsub2'
            | inr h => exact h.symm
        · exact ih r1 ex1 r2

theorem Subtree.subtract_eq_Subtract :
    Subtree.Subtract a b R ↔ a.subtract b = R := by
  constructor
  · intro hs
    exact (hs.inj Subtract_of_subtract).symm
  · intro heq
    subst heq
    exact Subtract_of_subtract

/-- The functional subtraction for CapKind produces a valid Subtract relation. -/
theorem CapKind.Subtract'_of_subtract' : CapKind.Subtract a [b] (a.subtract' b) := by
  induction a with
  | nil => exact .empty_l
  | cons x xs ih =>
    simp only [subtract']
    apply CapKind.Subtract.union_l
    · exact Subtree.Subtract_of_subtract
    · exact ih

theorem CapKind.subtract'_eq_Subtract :
    CapKind.Subtract a [b] R ↔ a.subtract' b = R := by
  constructor
  · intro hs
    exact (hs.inj Subtract'_of_subtract').symm
  · intro heq
    subst heq
    exact Subtract'_of_subtract'

/-- The functional subtraction for CapKind produces a valid Subtract relation. -/
theorem CapKind.Subtract_of_subtract : CapKind.Subtract a b (a.subtract b) := by
  induction b generalizing a with
  | nil => simp [subtract]; exact .empty_r
  | cons y ys ih =>
    cases ys with
    | nil =>
      simp only [subtract]
      exact Subtract'_of_subtract'
    | cons y' ys' =>
      simp only [subtract]
      apply CapKind.Subtract.union_r
      · exact Subtract'_of_subtract'
      · exact ih

theorem CapKind.subtract_eq_Subtract :
    CapKind.Subtract a b R ↔ a.subtract b = R := by
  constructor
  · intro hs
    exact (hs.inj Subtract_of_subtract).symm
  · intro heq
    subst heq
    exact Subtract_of_subtract

theorem CapKind.subkind_iff_Subkind : K1.subkind K2 ↔ Subkind K1 K2 := by
  simp only [subkind]
  constructor
  · intro h
    rw [isEmpty_iff_IsEmpty] at h
    apply Subkind.subtract Subtract_of_subtract h
  · intro h
    cases h with
    | subtract hs he =>
      rw [isEmpty_iff_IsEmpty]
      have heq := (hs.inj Subtract_of_subtract).symm
      rw [heq]
      exact he

end CaplessK
