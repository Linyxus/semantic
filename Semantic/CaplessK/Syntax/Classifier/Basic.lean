import Semantic.CaplessK.Syntax.Classifier.Semantics
import Semantic.CaplessK.Syntax.Classifier.Subkind
import Semantic.CaplessK.Syntax.Classifier.Intersection
import Semantic.CaplessK.Syntax.Classifier.Disjoint

namespace CaplessK

theorem CapKind.Intersect.with_subkind
    (hs : K1.Subkind K2)
    : (intersect L K1).Subkind (intersect L K2) := by
  rw [Subkind.semantics] at *
  have h1 := Intersect.lawful L K1
  have h2 := Intersect.lawful L K2
  apply! Intersect.with_ssubkind_l

theorem CapKind.Intersect.with_subkind_r
    (hs : K1.Subkind K2)
    : (intersect K1 L).Subkind (intersect K2 L) := by
  rw [Subkind.semantics] at *
  have h1 := Intersect.lawful K1 L
  have h2 := Intersect.lawful K2 L
  apply! Intersect.with_ssubkind_r

theorem CapKind.Intersect.subkind_l
    : (intersect K L).Subkind K := by
  rw [Subkind.semantics]
  have h := Intersect.lawful K L
  apply h.is_ssubkind_l

theorem CapKind.Intersect.subkind_r
    : (intersect K L).Subkind L := by
  rw [Subkind.semantics]
  have h := Intersect.lawful K L
  apply h.is_ssubkind_r

theorem CapKind.Subkind.reorder_union_4 :
    Subkind ((A ++ B) ++ (C ++ D)) ((A ++ C) ++ (B ++ D)) := by
  apply union_l
  · apply union_l
    · apply trans .union_rl .union_rl
    · apply trans .union_rl .union_rr
  · apply union_l
    · apply trans .union_rr .union_rl
    · apply trans .union_rr .union_rr

theorem CapKind.Intersect.union_r_subkind :
    Subkind (.intersect K (L1 ++ L2)) ((K.intersect L1) ++ (K.intersect L2)) := by
  rw [Subkind.semantics]
  intro c hc
  have hi := Intersect.lawful K (L1 ++ L2)
  have hi1 := Intersect.lawful K L1
  have hi2 := Intersect.lawful K L2
  have ⟨h1, h2⟩ := hi.contains_inv hc
  cases h2.append_inv <;> rename_i h2
  · apply Contains.append_r; apply hi1.contains h1 h2
  · apply Contains.append_l; apply hi2.contains h1 h2

theorem CapKind.Intersect.union_r_superkind :
    Subkind ((K.intersect L1) ++ (K.intersect L2)) (.intersect K (L1 ++ L2)) := by
  rw [Subkind.semantics]
  intro c hc
  have hi := Intersect.lawful K (L1 ++ L2)
  have hi1 := Intersect.lawful K L1
  have hi2 := Intersect.lawful K L2
  cases hc.append_inv <;> rename_i hc
  · have ⟨hc1, hc2⟩ := hi1.contains_inv hc
    apply contains hi hc1 (.append_r hc2)
  · have ⟨hc1, hc2⟩ := hi2.contains_inv hc
    apply contains hi hc1 (.append_l hc2)

theorem CapKind.Intersect.subkind_self : Subkind A (.intersect A A) := by
  rw [Subkind.semantics]
  intro c hc
  have hi := Intersect.lawful A A
  apply! hi.contains

theorem CapKind.Intersect.is_empty_repeat
    (he : IsEmpty (.intersect A (.intersect B A))) : IsEmpty (.intersect B A) := by
  rw [← SEmpty.is_empty] at *
  intro c hc
  apply he c
  have hi := Intersect.lawful B A
  have hi' := Intersect.lawful A (.intersect B A)
  have ⟨_, _⟩ := hi.contains_inv hc
  apply! hi'.contains

theorem CapKind.Intersect.subkind_symm : Subkind (.intersect A B) (.intersect B A) := by
  rw [Subkind.semantics]
  intro c hc
  have ha := Intersect.lawful A B
  have hb := Intersect.lawful B A
  have ⟨_, _⟩ := ha.contains_inv hc
  apply! hb.contains

-- Disjointness and Subkinding

theorem CapKind.Disjoint.refine_subkind_l
    (hd : Disjoint K2 L)
    (hs : K1.Subkind K2)
    : Disjoint K1 L := by
  rw [← Disjoint.empty_intersect, ← SEmpty.is_empty, Subkind.semantics] at *
  intro c hc
  apply hd c
  have h2 := Intersect.lawful K2 L
  have h1 := Intersect.lawful K1 L
  have ⟨hc1, _⟩ := h1.contains_inv hc
  have hc2 := hs c hc1
  apply! h2.contains

theorem CapKind.disjoint.refine_subkind_l
    (hd : disjoint K2 L) (hs : K1.Subkind K2) : disjoint K1 L := by
  rw [← disjoint.lawful] at *; apply! Disjoint.refine_subkind_l

theorem CapKind.Disjoint.refine_subkind_r
    (hd : Disjoint L K2)
    (hs : K1.Subkind K2)
    : Disjoint L K1 := by
  apply symm; apply! hd.symm.refine_subkind_l

theorem CapKind.disjoint.refine_subkind_r
    (hd : disjoint L K2) (hs : K1.Subkind K2) : disjoint L K1 := by
  rw [← disjoint.lawful] at *; apply! Disjoint.refine_subkind_r

theorem CapKind.Disjoint.and_subkind (hd : Disjoint K L) (hs : K.Subkind L) : K.IsEmpty := by
  rw [← Disjoint.empty_intersect, Subkind.semantics, ← SEmpty.is_empty] at *
  intro c hc
  apply hd c
  have hi := Intersect.lawful K L
  apply hi.contains hc (hs c hc)

theorem CapKind.Disjoint.with_self (hd : Disjoint K K) : K.IsEmpty := by
  apply hd.and_subkind .rfl

end CaplessK
