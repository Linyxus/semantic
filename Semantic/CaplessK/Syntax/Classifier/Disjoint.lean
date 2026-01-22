import Semantic.CaplessK.Syntax.Classifier.CapKind
import Semantic.CaplessK.Syntax.Classifier.Intersection
import Semantic.CaplessK.Syntax.Classifier.Semantics

namespace CaplessK

/-- Two subtrees are disjoint if they do not share any common nodes. -/
inductive CapKind.Disjoint : CapKind -> CapKind -> Prop where
  | intersect : Intersect K L R -> R.IsEmpty -> Disjoint K L

/-- Decides whether two CapKinds are disjoint. -/
def CapKind.disjoint (a b : CapKind) := (IsEmpty.decidable (K:=a.intersect b)).decide

theorem CapKind.Disjoint.empty_intersect : IsEmpty (K.intersect L) ↔ Disjoint K L := by
  apply Iff.intro <;> intro h
  · apply intersect (Intersect.lawful _ _) h
  · cases h
    rename_i h1 h2
    rw [← SEmpty.is_empty] at *
    intro c hc
    have hi' := Intersect.lawful K L
    have ⟨_, _⟩ := hi'.contains_inv hc
    apply h2 c
    apply! h1.contains

/-- Proves that `disjoint` follows derivation. -/
theorem CapKind.disjoint.lawful : Disjoint K L ↔ disjoint K L := by
  rw [disjoint, decide_eq_true_iff]
  exact Disjoint.empty_intersect.symm

theorem CapKind.Disjoint.symm (hs : Disjoint K L) : Disjoint L K := by
  cases hs
  rename_i h1 h2
  have h := Intersect.lawful L K
  apply Disjoint.intersect h
  rw [← SEmpty.is_empty] at *
  intro c hc
  apply h2 c
  have ⟨_, _⟩ := h.contains_inv hc
  apply! h1.contains

theorem CapKind.disjoint.symm (hs : disjoint K L) : disjoint L K := by
  rw [← lawful] at *
  apply! Disjoint.symm

theorem CapKind.Disjoint.union_l
    (hd1 : Disjoint K1 L) (hd2 : Disjoint K2 L) : Disjoint (K1 ++ K2) L := by
  rw [← empty_intersect, ← SEmpty.is_empty] at *
  intro c hc
  have h1 := Intersect.lawful K1 L
  have h2 := Intersect.lawful K2 L
  have h12 := Intersect.lawful (K1 ++ K2) L
  have ⟨hc12, _⟩ := h12.contains_inv hc
  cases hc12.append_inv
  · apply hd1 c; apply! h1.contains
  · apply hd2 c; apply! h2.contains

theorem CapKind.Disjoint.is_empty_l (he : IsEmpty K) : Disjoint K L := by
  rw [← empty_intersect, ← SEmpty.is_empty] at *
  intro c hc
  apply he c
  have h := Intersect.lawful K L
  have ⟨_, _⟩ := h.contains_inv hc
  assumption

theorem CapKind.Disjoint.is_empty_r (he : IsEmpty L) : Disjoint K L := by
  rw [← empty_intersect, ← SEmpty.is_empty] at *
  intro c hc
  apply he c
  have h := Intersect.lawful K L
  have ⟨_, _⟩ := h.contains_inv hc
  assumption

end CaplessK
