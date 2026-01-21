import Semantic.CaplessK.Syntax.Classifier.Subtract
import Semantic.CaplessK.Syntax.Classifier.Semantics

namespace CaplessK

/-- `K` is a subkind of `L` if every node in `K` is present in `L`. -/
inductive Kind.Subkind : Kind -> Kind -> Prop where
  | subtract : Subtract K1 K2 R -> IsEmpty R -> Subkind K1 K2

theorem Kind.Subkind.empty_r_inv (hs : Subkind K1 K2) (he : IsEmpty K2) : IsEmpty K1 := by
  cases hs
  apply! Subtract.empty_r_inv

/-- Subtract-defined subkinding agrees with semantic subkinding. -/
theorem Kind.Subkind.semantics : Subkind A B ↔ SSubkind A B := by
  apply Iff.intro <;> intro h
  · cases h
    rename_i h he
    simp_all [← h.is_empty_is_subkind]
  · have ⟨R, h⟩ := Subtract.exists A B
    apply subtract h
    simp_all [h.is_empty_is_subkind]

theorem Kind.Subkind.rfl : Subkind A A := by apply semantics.mpr SSubkind.rfl

theorem Kind.Subkind.trans (ha : Subkind A B) (hb : Subkind B C) : Subkind A C := by
  rw [semantics] at *
  apply! SSubkind.trans

theorem Kind.Subkind.of_top : Subkind A .top := by
  rw [semantics]
  intro c hc
  exact .here (.sub .of_top)

theorem Kind.Subkind.of_empty
    (hs : Subkind K L)
    (he : L.IsEmpty)
    : K.IsEmpty := by
  cases hs
  case subtract hs he1 => apply! hs.empty_r_inv

theorem Kind.Subkind.union_rl : Subkind K (K ++ L) := by
  rw [semantics]
  intro c hc
  apply! Contains.append_r

theorem Kind.Subkind.union_rr : Subkind L (K ++ L) := by
  rw [semantics]
  intro c hc
  apply! Contains.append_l

theorem Kind.Subkind.union_l (ha : Subkind K1 L) (hb : Subkind K2 L) : Subkind (K1 ++ K2) L := by
  rw [semantics] at *
  intro c hc
  cases hc.append_inv <;> rename_i hc
  · apply ha c hc
  · apply hb c hc

theorem Kind.Subkind.join
    (hs1 : Subkind K1 L1)
    (hs2 : Subkind K2 L2)
    : Subkind (K1 ++ K2) (L1 ++ L2) := by
  apply union_l
  · apply trans hs1 .union_rl
  · apply trans hs2 .union_rr

theorem Kind.Subkind.is_empty_l
    (he : IsEmpty K)
    : Subkind K L := by
  rw [semantics]
  rw [← SEmpty.is_empty] at he
  intro c hc
  cases he c hc

end CaplessK
