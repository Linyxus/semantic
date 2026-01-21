import Semantic.CaplessK.Syntax.Classifier.Core
import Semantic.CaplessK.Syntax.Classifier.Kind

namespace CaplessK

/-- The intersection of two subtrees. -/
inductive Subtree.Intersect : Subtree -> Subtree -> Kind -> Prop where
  | subtree_l : r1.Subclass r2 -> Intersect (mk r1 ex1) (mk r2 ex2) [mk r1 (ex1 ++ ex2)]
  | subtree_r : r2.Subclass r1 -> Intersect (mk r1 ex1) (mk r2 ex2) [mk r2 (ex1 ++ ex2)]
  | disjoint : r1.Disjoint r2 -> Intersect (mk r1 ex1) (mk r2 ex2) []

/-- Intersection of two kinds. -/
inductive Kind.Intersect : Kind -> Kind -> Kind -> Prop where
  | empty_l : Intersect [] K []
  | empty_r : Intersect K [] []
  | append_l : Intersect [x] K R1 -> Intersect xs K R2 -> Intersect (x::xs) K (R1 ++ R2)
  | append_r : Intersect K [x] R1 -> Intersect K xs R2 -> Intersect K (x::xs) (R1 ++ R2)
  | singleton : x.Intersect y R -> Intersect [x] [y] R

@[simp]
def Subtree.intersect (s : Subtree) (t : Subtree) : Kind :=
  if s.root.subclass t.root then .node s.root (s.excls ++ t.excls)
  else if t.root.subclass s.root then .node t.root (s.excls ++ t.excls)
  else .empty

theorem Subtree.Intersect.lawful : Intersect s t (s.intersect t) := by
  simp
  split
  · rename_i h
    simp [← Classifier.subclass_is_Subclass] at h
    apply! subtree_l
  · split
    · rename_i h
      simp [← Classifier.subclass_is_Subclass] at h
      apply! subtree_r
    · simp [← Classifier.subclass_is_Subclass] at *
      cases Classifier.subclass_or_disjoint s.root t.root <;> rename_i h
      · contradiction
      · cases h <;> rename_i h
        · have h0 := h.weaken; contradiction
        · apply! disjoint

@[simp]
def Kind.intersect (k : Kind) (l : Kind) : Kind :=
  List.flatMap (fun x => List.flatMap (fun y => x.intersect y) l) k

theorem Kind.intersect.cons_l : intersect (x :: xs) K = intersect [x] K ++ intersect xs K := by simp

theorem Kind.intersect.append_l :
    intersect (xs1 ++ xs2) K = intersect xs1 K ++ intersect xs2 K := by simp

theorem Kind.intersect.cons_r :
    intersect [x] (y :: ys) = intersect [x] [y] ++ intersect [x] ys := by simp

theorem Kind.intersect.append_r :
    intersect [x] (ys1 ++ ys2) = intersect [x] ys1 ++ intersect [x] ys2 := by simp

theorem Kind.Intersect.lawful' : Intersect [x] L (.intersect [x] L) := by
  induction L
  case nil => simp; apply empty_r
  case cons y ys ih =>
    simp
    apply append_r
    · apply singleton .lawful
    · simp at ih; apply ih

theorem Kind.Intersect.lawful (K L : Kind) : Intersect K L (K.intersect L) := by
  induction K generalizing L
  case nil => simp; apply empty_l
  case cons x xs ih =>
    apply append_l _ (ih _)
    have h := lawful' (x:=x) (L:=L)
    simp_all

theorem Kind.intersect.top_r {K : Kind} : K.intersect .top = K := by
  induction K
  case nil => simp
  case cons x xs ih =>
    have h := Classifier.Subclass.of_top (a:=x.root)
    rw [Classifier.subclass_is_Subclass] at h
    rw [cons_l, ih]
    simp [h]

theorem Kind.intersect.top_l {K : Kind} : Kind.top.intersect K = K := by
  induction K
  case nil => simp
  case cons y ys ih =>
    simp at *
    rw [ih]
    cases y
    rename_i r exs
    cases r
    case top => simp [Classifier.subclass]
    case child n t =>
      simp [Classifier.subclass]
      have h := Classifier.Subclass.of_top (a:=t)
      rw [Classifier.subclass_is_Subclass] at h
      simp [h]

theorem Classifier.disjoint.implies_no_subclass
    (hd : disjoint a b) : (a.subclass b = false ∧ b.subclass a = false) := by
  simp [← Classifier.disjoint_is_Disjoint] at hd
  simp [← Bool.not_eq_true, ← Classifier.subclass_is_Subclass]
  apply And.intro
  · intro h; apply hd.not_subclass h
  · intro h; apply hd.symm.not_subclass h

theorem Classifier.StrictSub.not_superclass (hss : StrictSub a b) : (b.subclass a = false) := by
  simp [← Bool.not_eq_true, ← Classifier.subclass_is_Subclass]
  intro h
  apply hss.antisymm h

theorem Kind.intersect.assoc'' :
    (intersect [x] [y]).intersect [z] = intersect [x] (intersect [y] [z]) := by
  cases Classifier.subclass_or_disjoint x.root y.root <;> rename_i h1
  · have h1' := Classifier.subclass_is_Subclass.mp h1
    cases Classifier.subclass_or_disjoint y.root z.root <;> rename_i h2
    · have h2' := Classifier.subclass_is_Subclass.mp h2
      have h3' := Classifier.subclass_is_Subclass.mp (h1.trans h2)
      simp_all
    · cases h2 <;> rename_i h2
      · have h2' := Classifier.subclass_is_Subclass.mp h2.weaken
        have h2'' := h2.not_superclass
        cases Classifier.subclass_or_disjoint' x.root z.root <;> rename_i h3' <;> aesop
      · have h2' := Classifier.disjoint_is_Disjoint.mp <| h2.refines_subclass_l h1
        have ⟨_, _⟩ := Classifier.disjoint.implies_no_subclass h2'
        have ⟨_, _⟩ := Classifier.disjoint.implies_no_subclass <|
          Classifier.disjoint_is_Disjoint.mp h2
        simp_all
  · cases h1 <;> rename_i h1
    · have h1' := Classifier.subclass_is_Subclass.mp h1.weaken
      have h1'' := h1.not_superclass
      cases Classifier.subclass_or_disjoint y.root z.root <;> rename_i h2
      · have h2' := Classifier.subclass_is_Subclass.mp h2
        simp_all
      · cases h2 <;> rename_i h2
        · have h2' := Classifier.subclass_is_Subclass.mp h2.weaken
          have h2'' := h2.not_superclass
          have h3 := h2.subclass_r h1.weaken
          have h3' := Classifier.subclass_is_Subclass.mp h3.weaken
          have h3'' := h3.not_superclass
          simp_all
        · have ⟨_, _⟩ := Classifier.disjoint.implies_no_subclass <|
            Classifier.disjoint_is_Disjoint.mp h2
          simp_all
    · have ⟨_, _⟩ := Classifier.disjoint.implies_no_subclass <|
        Classifier.disjoint_is_Disjoint.mp h1
      cases Classifier.subclass_or_disjoint y.root z.root <;> rename_i h2
      · have h2' := Classifier.subclass_is_Subclass.mp h2
        simp_all
      · cases h2 <;> rename_i h2
        · have h2' := Classifier.subclass_is_Subclass.mp h2.weaken
          have h2'' := h2.not_superclass
          have h3 := h1.refines_subclass_r h2.weaken
          have ⟨_, _⟩ := Classifier.disjoint.implies_no_subclass <|
            Classifier.disjoint_is_Disjoint.mp h3
          simp_all
        · have ⟨_, _⟩ := Classifier.disjoint.implies_no_subclass <|
            Classifier.disjoint_is_Disjoint.mp h2
          simp_all

theorem Kind.intersect.assoc' {B C : Kind} :
    (intersect [x] B).intersect C = intersect [x] (B.intersect C) := by
  induction B generalizing C
  case nil => simp
  case cons y ys ih =>
    rw [cons_l (x:=y), cons_r, append_r, append_l, ih, List.append_left_inj]
    induction C
    case nil => simp
    case cons z zs ih2 =>
      have h : (intersect [x] [y]).intersect (z :: zs) =
          (intersect [x] [y]).intersect [z] ++ (intersect [x] [y]).intersect zs := by
        generalize h0 : intersect [x] [y] = C
        simp at h0; split at h0
        · subst_vars; apply cons_r
        · split at h0
          · subst_vars; apply cons_r
          · subst_vars; simp
      rw [cons_r (ys:=zs), append_r, h, assoc'', ih2]

theorem Kind.intersect.assoc {A B C : Kind} :
    (A.intersect B).intersect C = A.intersect (B.intersect C) := by
  induction A generalizing B C
  case nil => simp
  case cons a as ih =>
    rw [cons_l (xs:=as), cons_l (xs:=as), append_l, ih, List.append_left_inj, assoc']

end CaplessK
