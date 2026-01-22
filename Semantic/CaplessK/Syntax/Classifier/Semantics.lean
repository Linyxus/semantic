import Semantic.CaplessK.Syntax.Classifier.Subtract
import Semantic.CaplessK.Syntax.Classifier.Intersection

namespace CaplessK

inductive Subtree.Contains : Subtree -> Classifier -> Prop where
  | sub : a.Subclass r -> Contains (mk r []) a
  | incl : ¬ a.Subclass x -> Contains (mk r exs) a -> Contains (mk r (x :: exs)) a

instance Subtree.Contains.decidable : Decidable (Contains (mk r exs) c) := by
  cases exs
  case nil =>
    cases Classifier.Subclass.decidable c r
    case isTrue h => apply! isTrue (.sub h)
    case isFalse h =>
      apply isFalse; intro h0; cases h0; simp_all
  case cons x xs =>
    cases decidable (r:=r) (exs:=xs) (c:=c)
    case isFalse => apply isFalse; intro h0; cases h0; simp_all
    case isTrue ih =>
      cases Classifier.Subclass.decidable c x
      case isFalse h => apply! (isTrue <| .incl h ih)
      case isTrue h => apply isFalse; intro h0; cases h0; simp_all

theorem Subtree.Contains.subclass_of_root (hc : Contains a c) : c.Subclass a.root := by
  induction hc
  case sub => assumption
  case incl ih => apply! ih

theorem Subtree.Contains.implies_root (hc : Contains a c) : Contains a a.root := by
  induction hc
  case sub => apply sub .rfl
  case incl r exs c x hns hc ih =>
    cases r.subclass_or_disjoint x <;> rename_i hx
    · cases c.subclass_or_disjoint x <;> rename_i hxc
      · aesop
      · cases hxc <;> rename_i hxc
        · cases (hxc.subclass_l hx).antisymm hc.subclass_of_root
        · cases (hxc.refines_subclass_r hx).not_subclass hc.subclass_of_root
    · cases hx <;> rename_i hx
      · apply incl hx.antisymm ih
      · apply incl hx.not_subclass ih

theorem Subtree.Contains.not_subclass (hs : ¬ a.Subclass r) : ¬ Contains (mk r exs) a := by
  intro h
  apply hs h.subclass_of_root

theorem Subtree.Contains.strictSub_root (hs : r.StrictSub a) : ¬ Contains (mk r exs) a :=
  not_subclass hs.antisymm

theorem Subtree.Contains.disjoint_root (hd : a.Disjoint r) : ¬ Contains (mk r exs) a :=
  not_subclass hd.not_subclass

theorem Subtree.Contains.excl_subclass (hs : c.Subclass a) : ¬ Contains (mk r (a :: exs)) c := by
  intro h; cases h; simp_all

theorem Subtree.Contains.not_cons_excl
    (hs : ¬ Contains (mk r exs) a) : ¬ Contains (mk r (x :: exs)) a := by
  intro h; cases h; simp_all

theorem Subtree.Contains.weaken_root
    (hc : Contains a c) (hs : a.root.Subclass r') : Contains (mk r' a.excls) c := by
  induction hc
  case sub hsub => apply sub (hsub.trans hs)
  case incl nhs hc ih =>
    apply incl nhs
    apply! ih

theorem Subtree.Contains.append_excl
    (hc1 : Contains (mk r ex1) c) (hc2 : Contains (mk r ex2) c)
    : Contains (mk r <| ex1 ++ ex2) c := by
  induction ex1 generalizing ex2
  case nil => simp_all
  case cons x xs ih =>
    cases hc1
    apply! incl _ (ih _ _)

theorem Subtree.Contains.append_excl_inv
    (hc : Contains (mk r (ex1 ++ ex2)) c) : Contains (mk r ex1) c ∧ Contains (mk r ex2) c := by
  induction ex1 generalizing ex2
  case nil =>
    simp_all; apply sub hc.subclass_of_root
  case cons x xs ih =>
    cases hc
    rename_i hc1 hc2
    have ⟨ih1, ih2⟩ := ih hc2
    apply And.intro (.incl hc1 ih1) ih2

inductive CapKind.Contains : CapKind -> Classifier -> Prop where
  | here : t.Contains x -> Contains (t :: ts) x
  | there : Contains ts x -> Contains (t :: ts) x

theorem CapKind.Contains.not_cons
    (hc1 : ¬ t.Contains x) (hc2 : ¬ Contains ts x) : ¬ Contains (t :: ts) x := by
  intro h; cases h <;> aesop

instance CapKind.Contains.decidable : Decidable (Contains k c) := by
  cases k
  case nil => apply isFalse; intro h; cases h
  case cons x xs =>
    cases Subtree.Contains.decidable (r:=x.root) (exs:=x.excls) (c:=c)
    case isTrue h => apply! isTrue (.here h)
    case isFalse hNotHere =>
      cases decidable (k:=xs) (c:=c)
      case isTrue h => apply! isTrue (.there h)
      case isFalse hNotThere =>
        apply isFalse; intro h; cases h <;> aesop

theorem CapKind.Contains.is_singleton (hc : Contains [t] x) : t.Contains x := by
  cases hc
  case here => aesop
  case there hc => cases hc

theorem CapKind.Contains.append_l (hc : Contains as x) : Contains (bs ++ as) x := by
  induction bs
  case nil => simp_all
  case cons => rw [List.cons_append]; apply! Contains.there

theorem CapKind.Contains.append_r (hc : Contains as x) : Contains (as ++ bs) x := by
  induction as
  case nil => cases hc
  case cons b bs ih =>
    cases hc
    case here => apply! here
    case there => apply there; apply! ih

theorem CapKind.Contains.append_inv (hc : Contains (as ++ bs) x) : Contains as x ∨ Contains bs x := by
  induction as generalizing bs
  case nil => simp_all
  case cons a as ih =>
    cases hc
    case here => left; apply! here
    case there hc =>
      cases ih hc <;> rename_i ih
      · left; apply! there
      · aesop

theorem CapKind.Contains.not_append
    (hc1 : ¬ Contains as x) (hc2 : ¬ Contains bs x) :  ¬ Contains (as ++ bs) x := by
  intro h; cases h.append_inv <;> aesop

theorem CapKind.Contains.not_append_inv
    (hc : ¬ Contains (as ++ bs) x) : ¬ Contains as x ∧ ¬ Contains bs x := by
  have h : ¬ (Contains as x ∨ Contains bs x) := by
    intro h; cases h; apply! hc (append_r _); apply! hc (append_l _)
  simp_all

-- Semantic empty
@[simp]
def Subtree.SEmpty (s : Subtree) : Prop := ∀ x, ¬ s.Contains x

@[simp]
def CapKind.SEmpty (k : CapKind) : Prop := ∀ x, ¬ k.Contains x

theorem CapKind.SEmpty.cons_inv (hs : SEmpty (x :: xs)) : x.SEmpty ∧ SEmpty xs := by
  apply And.intro
  · intro c h
    apply hs c (.here h)
  · intro c h
    apply hs c (.there h)

theorem Subtree.SEmpty.excl_inv
    (he : SEmpty (mk r (x :: xs))) : r.Subclass x ∨ SEmpty (mk r xs) := by
  cases r.subclass_or_disjoint x
  · aesop
  · rename_i h; cases h <;> rename_i h
    · right; intro _ h1; rename_i c
      apply he r <| .incl h.antisymm h1.implies_root
    · right; intro _ h1; rename_i c
      apply he r <| .incl h.not_subclass h1.implies_root

theorem Subtree.SEmpty.is_empty : (mk r exs).SEmpty ↔ ContainsSupOf exs r := by
  apply Iff.intro <;> intro h
  · induction exs
    case nil =>
      cases h r (.sub .rfl)
    case cons x xs ih =>
      cases h.excl_inv <;> rename_i h
      · apply! ContainsSupOf.here
      · apply! ContainsSupOf.there <| ih _
  · intro c h0
    induction h generalizing c
    case here hs => cases h0.implies_root; contradiction
    case there hsc ih => cases h0.implies_root; apply! ih

theorem CapKind.SEmpty.is_empty : SEmpty k ↔ IsEmpty k := by
  apply Iff.intro <;> intro h
  · induction k
    case nil => constructor
    case cons x xs ih =>
      have ⟨h1, h2⟩ := h.cons_inv
      constructor
      · rw [← Subtree.SEmpty.is_empty]; exact h1
      · aesop
  · intro c hc
    induction h
    case empty => cases hc
    case absurd hsc h ih =>
      rw [← Subtree.SEmpty.is_empty] at hsc
      cases hc
      case here hc => apply hsc _ hc
      case there => apply! ih

theorem Subtree.Contains.refine_root
    (hc : Contains a c)
    (hsub1 : x.Subclass a.root)
    (hsub2 : c.Subclass x)
    : Contains (mk x a.excls) c := by
  induction hc
  case sub => apply! sub
  case incl r exs c a nhs hc ih =>
    simp_all
    apply! incl

theorem Subtree.Subtract.contains_or
    (hs : Subtract a b R1)
    (hca : a.Contains c)
    : b.Contains c ∨ R1.Contains c := by
  induction hs
  case tree r1 ex1 r2 =>
    cases Decidable.em (c.Subclass r2)
    · left; apply! Contains.sub
    · right; apply! CapKind.Contains.here <| Contains.incl _ _
  case excl_absurd_r hss => right; apply! CapKind.Contains.here
  case excl_irrelevant_r hd hs ih =>
    cases ih hca <;> rename_i ih
    · left
      apply Contains.incl
      · apply (hd.refines_subclass_l ih.subclass_of_root).not_subclass
      · assumption
    · aesop
  case excl_subclass_r r1 ex1 r2 ex2 _ a hsa2 hsa1 hs ih =>
    cases ih hca <;> rename_i ih
    · cases Decidable.em (c.Subclass a)
      · right; apply CapKind.Contains.here
        apply! Contains.refine_root hca hsa1
      · left; apply! Contains.incl
    · right; apply! CapKind.Contains.there
  case excl_subclass_l hsa2 hss1 => right; apply! CapKind.Contains.here
  case excl_irrelevant_l hsa1 hd1 hs ih =>
    cases ih hca <;> rename_i ih
    · left
      constructor
      · apply (hd1.refines_subclass_l hca.subclass_of_root).not_subclass
      · apply ih
    · aesop

theorem Subtree.Subtract.contains_inv
    (hs : Subtract a b R1)
    (hca : R1.Contains c)
    : a.Contains c ∧ ¬ b.Contains c := by
  induction hs
  case tree r1 ex1 r2 =>
    cases hca.is_singleton
    apply And.intro
    · assumption
    · apply! Contains.not_subclass
  case excl_absurd_r hss =>
    apply And.intro hca.is_singleton
    intro h; cases h
    case incl nhs h => have hss' := (hss.subclass_l h.subclass_of_root).weaken; simp_all
  case excl_irrelevant_r hd hs ih =>
    have ⟨ih1, ih2⟩ := ih hca
    apply And.intro ih1
    apply! Contains.not_cons_excl
  case excl_subclass_r hsa2 hsa1 hs ih =>
    cases hca
    case here hca =>
      apply And.intro (hca.weaken_root hsa1)
      apply Contains.excl_subclass hca.subclass_of_root
    case there hca =>
      have ⟨ih1, ih2⟩ := ih hca
      apply And.intro ih1
      apply! Contains.not_cons_excl
  case excl_subclass_l hsa2 hss1 =>
    apply And.intro hca.is_singleton
    apply Contains.excl_subclass
    apply hca.is_singleton.subclass_of_root.trans hss1.weaken
  case excl_irrelevant_l hsa2 hd1 hs ih =>
    have ⟨ih1, ih2⟩ := ih hca
    apply And.intro ih1
    apply! Contains.not_cons_excl

theorem CapKind.Subtract.contains_or'
    (hs : Subtract A [b] R1)
    (hc : A.Contains c)
    : b.Contains c ∨ R1.Contains c := by
  induction A generalizing R1
  case nil => cases hs; cases hc
  case cons a as ih =>
    have ⟨Rh, Rt, _, hh, ht⟩ := hs.cons_l_split
    simp_all
    cases hc
    case here hc =>
      cases hh.is_singleton.contains_or hc
      · aesop
      · right; apply! Contains.append_r
    case there hc =>
      cases ih ht hc
      · aesop
      · right; apply! Contains.append_l

theorem CapKind.Subtract.contains_or
    (hs : Subtract A B R1)
    (hc : A.Contains c)
    : B.Contains c ∨ R1.Contains c := by
  induction B generalizing A R1
  case nil => cases hs; simp_all
  case cons b bs ih =>
    cases bs
    case nil =>
      cases hs.contains_or' hc
      · left; apply! Contains.here
      · aesop
    case cons b' bs =>
      have ⟨R', ha, hb⟩ := hs.union_r_inv
      cases ha.contains_or' hc <;> rename_i hca
      · left; apply! Contains.here
      · cases ih hb hca <;> rename_i ih
        · left; apply! Contains.there
        · aesop

theorem CapKind.Subtract.contains_inv'
    (hs : Subtract A [b] R1)
    (hc : R1.Contains c)
    : A.Contains c ∧ ¬ b.Contains c := by
  induction A generalizing R1
  case nil => cases hs; cases hc
  case cons a as ih =>
    have ⟨Rh, Rt, _, hh, ht⟩ := hs.cons_l_split
    subst_vars
    cases hc.append_inv <;> rename_i hc
    · have ⟨h1, h2⟩ := hh.is_singleton.contains_inv hc
      apply And.intro (.here h1) h2
    · have ⟨h1, h2⟩ := ih ht hc
      apply And.intro (.there h1) h2

theorem CapKind.Subtract.contains_inv
    (hs : Subtract A B R1)
    (hc : R1.Contains c)
    : A.Contains c ∧ ¬ B.Contains c := by
  induction B generalizing A R1
  case nil => cases hs; apply And.intro hc; intro h; cases h
  case cons b bs ih =>
    cases bs
    case nil =>
      have ⟨h1, h2⟩ := hs.contains_inv' hc
      apply And.intro h1
      intro h; simp_all [h.is_singleton]
    case cons b' bs =>
      have ⟨R', ha, hb⟩ := hs.union_r_inv
      have ⟨h1, h2⟩ := ih hb hc
      have ⟨h3, h4⟩ := ha.contains_inv' h1
      apply And.intro h3; apply! Contains.not_cons

/-- Semantic subkinding. -/
def CapKind.SSubkind (a b : CapKind) : Prop := ∀ c, a.Contains c -> b.Contains c

theorem CapKind.Subtract.is_empty_is_subkind
    (hs : Subtract A B R)
    : R.IsEmpty ↔ SSubkind A B := by
  apply Iff.intro <;> intro h
  · intro c hc
    rw [← SEmpty.is_empty] at h
    cases hs.contains_or hc <;> rename_i hc
    · exact hc
    · cases h c hc
  · rw [← SEmpty.is_empty]
    intro c hc
    have ⟨h1, h2⟩ := hs.contains_inv hc
    simp_all [h c h1]

theorem CapKind.SSubkind.rfl : SSubkind A A := by intro c h; simp_all

theorem CapKind.SSubkind.trans (hs1 : SSubkind A B) (hs2 : SSubkind B C) : SSubkind A C := by
  intro c hc
  apply hs2
  apply hs1
  apply hc

/-- Semantics of intersection -/

theorem Subtree.Intersect.contains
    (hi : Intersect a b R)
    (hc1 : a.Contains c)
    (hc2 : b.Contains c)
    : R.Contains c := by
  induction hi
  case subtree_l hs =>
    apply CapKind.Contains.here
    apply hc1.append_excl (hc2.refine_root hs hc1.subclass_of_root)
  case subtree_r hs =>
    apply CapKind.Contains.here
    apply (hc1.refine_root hs hc2.subclass_of_root).append_excl hc2
  case disjoint hd =>
    cases ((hd.refines_subclass_l hc1.subclass_of_root).refines_subclass_r
      hc2.subclass_of_root).not_subclass .rfl

theorem Subtree.Intersect.contains_inv
    (hi : Intersect a b R)
    (hc : R.Contains c)
    : a.Contains c ∧ b.Contains c := by
  induction hi
  case subtree_l hs =>
    have ⟨h1, h2⟩ := hc.is_singleton.append_excl_inv
    apply And.intro h1 (h2.weaken_root hs)
  case subtree_r hs =>
    have ⟨h1, h2⟩ := hc.is_singleton.append_excl_inv
    apply And.intro (h1.weaken_root hs) h2
  case disjoint hd => cases hc

theorem CapKind.Intersect.contains
    (hi : Intersect A B R)
    (hc1 : A.Contains c)
    (hc2 : B.Contains c)
    : R.Contains c := by
  induction hi
  case empty_l => cases hc1
  case empty_r => cases hc2
  case append_l ha hb iha ihb =>
    cases hc1
    case here hc1 => apply Contains.append_r; apply! iha (.here _)
    case there hc1 => apply Contains.append_l; apply! ihb
  case append_r ha hb iha ihb =>
    cases hc2
    case here hc2 => apply Contains.append_r; apply! iha _ (.here _)
    case there hc2 => apply Contains.append_l; apply! ihb
  case singleton hi => apply hi.contains hc1.is_singleton hc2.is_singleton

theorem CapKind.Intersect.contains_inv
    (hi : Intersect A B R)
    (hc : R.Contains c)
    : A.Contains c ∧ B.Contains c := by
  induction hi
  case empty_l => cases hc
  case empty_r => cases hc
  case append_l ha hb iha ihb =>
    cases hc.append_inv <;> rename_i hc
    · have ⟨h1, h2⟩ := iha hc
      apply And.intro (.here h1.is_singleton) h2
    · have ⟨h1, h2⟩ := ihb hc
      apply And.intro (.there h1) h2
  case append_r ha hb iha ihb =>
    cases hc.append_inv <;> rename_i hc
    · have ⟨h1, h2⟩ := iha hc
      apply And.intro h1 (.here h2.is_singleton)
    · have ⟨h1, h2⟩ := ihb hc
      apply And.intro h1 (.there h2)
  case singleton hi =>
    have ⟨h1, h2⟩ := hi.contains_inv hc
    apply And.intro <;> apply! Contains.here

theorem CapKind.Intersect.is_ssubkind_l
    (hi : Intersect A B R)
    : SSubkind R A := by
  intro c hc; simp_all [hi.contains_inv hc]

theorem CapKind.Intersect.is_ssubkind_r
    (hi : Intersect A B R)
    : SSubkind R B := by
  intro c hc; simp_all [hi.contains_inv hc]

theorem CapKind.Intersect.with_ssubkind_l
    (hs : SSubkind A B)
    (hi1 : Intersect L A R1)
    (hi2 : Intersect L B R2)
    : R1.SSubkind R2 := by
  intro c hc
  have ⟨h1, h2⟩ := hi1.contains_inv hc
  apply hi2.contains h1 (hs c h2)

theorem CapKind.Intersect.with_ssubkind_r
    (hs : SSubkind A B)
    (hi1 : Intersect A L R1)
    (hi2 : Intersect B L R2)
    : R1.SSubkind R2 := by
  intro c hc
  have ⟨h1, h2⟩ := hi1.contains_inv hc
  apply hi2.contains (hs c h1) h2

theorem CapKind.intersect.is_empty_r
    (he : IsEmpty L)
    : IsEmpty (.intersect K L) := by
  rw [← SEmpty.is_empty] at *
  have h := Intersect.lawful K L
  intro c hc
  have ⟨h1, h2⟩ := h.contains_inv hc
  apply he c h2

theorem CapKind.intersect.is_empty_l
    (he : IsEmpty K)
    : IsEmpty (.intersect K L) := by
  rw [← SEmpty.is_empty] at *
  have h := Intersect.lawful K L
  intro c hc
  have ⟨h1, h2⟩ := h.contains_inv hc
  apply he c h1

end CaplessK
