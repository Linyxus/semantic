import Semantic.CaplessK.Syntax.Classifier.Kind

namespace CaplessK

/-- This file defines the "subtraction" operation between two kind sets. -/

inductive Subtree.Subtract : Subtree -> Subtree -> Kind -> Prop where
  -- Basically we follow a few broad strokes:
  -- - A \ (B \ C) = (A \ B) ∪ (A ∩ B ∩ C)
  -- - For B of the form (.node r []) (no exclusion):
  --   - If r < A, refine A
  --   - If r > A, empty
  --   - If r ⊥ A, A
  -- Base case first
  | tree : Subtract (.mk r1 ex1) (.mk r2 []) (.node r1 (r2 :: ex1))
  -- Exclusion case
  -- First, handle the cases where (B \ C) doesn't make sense
  | excl_absurd_r :
    r2.StrictSub a -> -- (B \ a) is just empty
    Subtract (.mk r1 ex1) (.mk r2 (a :: ex2)) (.node r1 ex1)
  | excl_irrelevant_r :
    r2.Disjoint a -> -- (B \ a) = B
    Subtract (.mk r1 ex1) (.mk r2 ex2) R ->
    Subtract (.mk r1 ex1) (.mk r2 (a :: ex2)) R
  -- Now, for cases where a is a subtree of r2
  -- We use the formula A \ (B \ C) = (A \ B) ∪ (A ∩ B ∩ C)
  | excl_subclass_r :
    a.Subclass r2 ->
    a.Subclass r1 -> -- A ∩ B ∩ C = a with all the exclusions
    Subtract (.mk r1 ex1) (.mk r2 ex2) R ->
    Subtract (.mk r1 ex1) (.mk r2 (a :: ex2)) ((.mk a ex1) :: R)
                                        -- ^ we'd need (ex1 ++ ex2) here to be exact,
                                        -- but if an element is in the ex2 subtree
                                        -- and not already excluded from A, it is part
                                        -- of (A \ B), so it's okay to keep anyway.
  | excl_subclass_l :
    a.Subclass r2 ->
    r1.StrictSub a ->  -- B \ C excludes the entirety of A
    Subtract (.mk r1 ex1) (.mk r2 (a :: ex2)) (.node r1 ex1)
  | excl_irrelevant_l :
    a.Subclass r2 ->
    r1.Disjoint a -> -- irrelevant exclusion, A ∪ B ∪ C = empty
    Subtract (.mk r1 ex1) (.mk r2 ex2) R ->
    Subtract (.mk r1 ex1) (.mk r2 (a :: ex2)) R

/-- Subtraction: `K.Subtract L` gives a Kind that contains all nodes in `K` but not in `L`. -/
inductive Kind.Subtract : Kind -> Kind -> Kind -> Prop where
  | empty_r : Subtract K .empty K
  | union_r :
    Subtract K [y] R1 ->
    Subtract R1 (y' :: ys) R2 ->
    Subtract K (y :: y' :: ys) R2
  | empty_l : Subtract .empty [y] .empty
  | union_l : x.Subtract y R1 -> Subtract xs [y] R2 -> Subtract (x::xs) [y] (R1 ++ R2)

theorem Kind.Subtract.singleton (hs : x.Subtract y R) : Subtract [x] [y] R := by
  have h := union_l hs .empty_l
  simp at h
  apply h

theorem Kind.Subtract.is_singleton (hs : Subtract [x] [y] R) : x.Subtract y R := by
  cases hs
  case union_l ha hb => cases hb; simp_all

theorem Subtree.Subtract.is_empty_l (hs : Subtract x y R) (hsc : Kind.IsEmpty [x]) : Kind.IsEmpty R := by
  have hsc' := hsc.is_absurd
  induction hs
  case tree =>
    apply Kind.IsEmpty.node
    apply! ContainsSupOf.there
  case excl_absurd_r => assumption
  case excl_irrelevant_r ih => apply! ih
  case excl_subclass_r hs2 hs1 hs ih =>
    constructor
    . apply hsc'.trans_subclass hs1
    . apply! ih
  case excl_subclass_l hs2 hss1 => apply! Kind.IsEmpty.node
  case excl_irrelevant_l hd2 hd1 hs ih => apply! ih

theorem Kind.Subtract.is_empty_l (hs : Subtract K1 K2 R) (he : IsEmpty K1) : IsEmpty R := by
  induction hs
  case empty_l => constructor
  case union_l ha hb ih =>
    cases he
    apply! Kind.IsEmpty.append (ha.is_empty_l $ .node _) (ih _)
  case empty_r => assumption
  case union_r ha hb =>
    apply hb
    apply! ha

theorem Kind.Subtract.empty_l' : Subtract [] K [] := by
  induction K
  case nil => apply empty_r
  case cons x xs ih =>
    cases xs
    case nil => apply empty_l
    case cons => apply union_r .empty_l ih

theorem Kind.Subtract.absurd_l (hs : Subtract (.node r1 ex1) K R) (hsc : ContainsSupOf ex1 r1) : IsEmpty R := by
  apply hs.is_empty_l
  apply IsEmpty.node
  assumption

theorem Kind.Subtract.empty_l_inv (hs : Subtract [] K R) : R = [] := by
  induction K generalizing R
  case nil => cases hs; simp
  case cons y ys ih =>
    cases hs
    case union_r ha hb => cases ha; apply! ih
    case empty_l => simp

theorem Subtree.Subtract.empty_implies_subclass
  (hs : Subtract (.mk r1 ex1) (.mk r2 ex2) R)
  (he : R.IsEmpty)
  : ContainsSupOf ex1 r1 ∨ r1.Subclass r2 := by
  cases hs
  case tree =>
    cases he.is_absurd <;> aesop
  case excl_absurd_r => left; apply he.is_absurd
  case excl_irrelevant_r hs => apply hs.empty_implies_subclass he
  case excl_subclass_r hs =>
    cases he
    apply! hs.empty_implies_subclass
  case excl_subclass_l => left; apply he.is_absurd
  case excl_irrelevant_l hs => apply! hs.empty_implies_subclass

theorem Subtree.Subtract.empty_r_inv (hs : Subtract S1 S2 R) (he : R.IsEmpty) (hsc2 : ContainsSupOf S2.excls S2.root) : ContainsSupOf S1.excls S1.root := by
  induction hs
  case tree => cases hsc2
  case excl_absurd_r hss => apply he.is_absurd
  case excl_irrelevant_r hd2 hs ih =>
    cases hsc2
    case here hs2 => cases hd2.not_subclass hs2
    case there => apply! ih
  case excl_subclass_r hs2 hs1 hs ih =>
    cases he
    rename_i he1 he2
    cases hsc2
    case here hsa =>
      cases hs2.antisymm hsa
      cases hs.empty_implies_subclass he2 <;> rename_i hs
      . aesop
      . cases hs1.antisymm hs; aesop
    case there => apply! ih
  case excl_subclass_l hs2 hss1 => apply he.is_absurd
  case excl_irrelevant_l hs2 hd1 hs ih =>
    cases hsc2
    case here hsa =>
      cases hs2.antisymm hsa
      cases hs.empty_implies_subclass he <;> rename_i hs
      . aesop
      . cases hd1.not_subclass hs
    case there => apply! ih

theorem Kind.Subtract.empty_r_inv (hs : Subtract K1 K2 R) (he : IsEmpty R) (hek2 : IsEmpty K2) : IsEmpty K1 := by
  induction hs
  case empty_l => constructor
  case union_l ha hb ih =>
    have ⟨_, _⟩ := he.append_inv
    apply! IsEmpty.append (.node $ ha.empty_r_inv _ hek2.is_absurd) (ih _ _)
  case empty_r => assumption
  case union_r ha hb =>
    cases hek2
    apply ha
    . apply! hb
    . apply! IsEmpty.node

theorem Subtree.Subtract.exists' : ∃ R, Subtract (mk r1 ex1) (mk r2 ex2) R := by
  induction ex2
  case nil => exists .node r1 (r2 :: ex1); apply tree
  case cons head tail ih =>
    cases head.subclass_or_disjoint r2
    case inl hs =>
      have ⟨R, h⟩ := ih
      cases head.subclass_or_disjoint r1
      case inl hs1 =>
        exists (.mk head ex1) :: R
        apply! excl_subclass_r
      case inr hs1 =>
        cases hs1
        case inl hs1 =>
          exists .node r1 ex1
          apply! excl_subclass_l
        case inr hs1 =>
          exists R
          apply! excl_irrelevant_l _ hs1.symm
    case inr hs =>
      cases hs
      case inl hs =>
        exists .node r1 ex1
        apply! excl_absurd_r
      case inr hs =>
        have ⟨R, h⟩ := ih
        exists R
        apply! excl_irrelevant_r hs.symm

theorem Subtree.Subtract.exists (a b : Subtree) : ∃R, Subtract a b R := exists' (r1:=a.root) (ex1:= a.excls) (r2:=b.root) (ex2:=b.excls)

theorem Kind.Subtract.exists' (a : Kind) (b : Subtree)  : ∃ R, Subtract a [b] R := by
  induction a
  case nil => exists .empty; apply empty_l
  case cons x xs ih =>
    have ⟨R1, h1⟩ := Subtree.Subtract.exists x b
    have ⟨R2, h2⟩ := ih
    exists R1 ++ R2
    apply union_l h1 h2

theorem Kind.Subtract.exists (a : Kind) (b: Kind) : ∃ R, Subtract a b R := by
  induction b generalizing a
  case nil => exists a; apply empty_r
  case cons y ys ihb =>
    cases ys
    case nil => apply! exists'
    case cons =>
      have ⟨R1, h1⟩ := exists' a y
      have ⟨R2, h2⟩ := ihb (a:=R1)
      exists R2
      apply union_r h1 h2

theorem Subtree.Subtract.excl_absurd_r_inv
  (hs : Subtract (mk r1 ex1) (mk r2 (a :: ex2)) R)
  (hss : r2.StrictSub a)
  : R = .node r1 ex1 := by
  cases hs
  case excl_absurd_r => rfl
  case excl_irrelevant_r hd _ => cases hd.not_subclass hss.weaken
  case excl_subclass_r h1 h2 _ => cases hss.antisymm h2
  case excl_subclass_l h1 h2 => cases hss.antisymm h2
  case excl_irrelevant_l h1 h2 _ => cases hss.antisymm h2

theorem Subtree.Subtract.excl_irrelevant_r_inv
  (hs : Subtract (mk r1 ex1) (mk r2 (a :: ex2)) R)
  (hd : r2.Disjoint a)
  : Subtract (mk r1 ex1) (mk r2 ex2) R := by
  cases hs
  case excl_absurd_r hss => cases hd.not_subclass hss.weaken
  case excl_irrelevant_r => assumption
  case excl_subclass_r hs1 hs2 hs => cases hd.symm.not_subclass hs2
  case excl_subclass_l hs2 => cases hd.symm.not_subclass hs2
  case excl_irrelevant_l hs2 _ => cases hd.symm.not_subclass hs2

theorem Subtree.Subtract.excl_subclass_r_inv
  (hs : Subtract (mk r1 ex1) (mk r2 (a :: ex2)) R)
  (hs1 : a.Subclass r1)
  (hs2 : a.Subclass r2)
  : ∃ R', R = (mk a ex1) :: R' ∧ Subtract (mk r1 ex1) (mk r2 ex2) R' := by
  cases hs
  case excl_absurd_r hss => cases hss.antisymm hs2
  case excl_irrelevant_r hd _ => cases hd.symm.not_subclass hs2
  case excl_subclass_r => aesop
  case excl_subclass_l hss _ => cases hss.antisymm hs1
  case excl_irrelevant_l hd1 _ _ => cases hd1.symm.not_subclass hs1

theorem Subtree.Subtract.excl_subclass_l_inv
  (hs : Subtract (mk r1 ex1) (mk r2 (a :: ex2)) R)
  (hs1 : r1.StrictSub a)
  (hs2 : a.Subclass r2)
  : R = .node r1 ex1 := by
  cases hs
  case excl_absurd_r hss => cases hss.antisymm hs2
  case excl_irrelevant_r hd _ => cases hd.symm.not_subclass hs2
  case excl_subclass_r => rename_i hsa _ _; cases hs1.antisymm hsa
  case excl_subclass_l => rfl
  case excl_irrelevant_l hd1 _ _ => cases hd1.not_subclass hs1.weaken

theorem Subtree.Subtract.excl_irrelevant_l_inv
  (hs : Subtract (mk r1 ex1) (mk r2 (a :: ex2)) R)
  (hd1 : r1.Disjoint a)
  (hs2 : a.Subclass r2)
  : Subtract (mk r1 ex1) (mk r2 ex2) R := by
  cases hs
  case excl_absurd_r hss => cases hss.antisymm hs2
  case excl_irrelevant_r hd _ => cases hd.symm.not_subclass hs2
  case excl_subclass_r => rename_i hsa _ _; cases hd1.symm.not_subclass hsa
  case excl_subclass_l => rename_i hss _; cases hd1.not_subclass hss.weaken
  case excl_irrelevant_l => assumption

theorem Subtree.Subtract.inj
  (hs1 : Subtract a b R1)
  (hs2 : Subtract a b R2)
  : R1 = R2 := by
  induction hs1 generalizing R2
  case tree => cases hs2; simp
  case excl_absurd_r hss => cases hs2.excl_absurd_r_inv hss; simp
  case excl_irrelevant_r hd2 hs1 ih =>
    apply ih
    apply! hs2.excl_irrelevant_r_inv
  case excl_subclass_r hsa2 hsa1 hs1 ih =>
    have ⟨_, _, hs2'⟩ := hs2.excl_subclass_r_inv hsa1 hsa2
    subst_vars
    rw [List.cons_inj_right]
    apply! ih
  case excl_subclass_l hsa2 hss1 => cases hs2.excl_subclass_l_inv hss1 hsa2; simp
  case excl_irrelevant_l hsa2 hd1 hs1 ih =>
    apply ih
    apply! hs2.excl_irrelevant_l_inv

theorem Kind.Subtract.inj
  (hs1 : Subtract K1 K2 R1)
  (hs2 : Subtract K1 K2 R2)
  : R1 = R2 := by
  induction hs1 generalizing R2
  case empty_r => cases hs2; simp
  case union_r ha hb =>
    cases hs2
    rename_i hs2a hs2b
    cases ha hs2a
    apply hb hs2b
  case empty_l => cases hs2; simp
  case union_l ha hb ih =>
    cases hs2
    rename_i hs2a hs2b
    cases ha.inj hs2a
    cases ih hs2b
    simp

theorem Subtree.Subtract.is_empty_insert
  (hs1 : Subtract (mk r1 (xs ++ ys)) (mk r2 ex2) R1)
  (he : R1.IsEmpty)
  (hs2 : Subtract (mk r1 (xs ++ zs ++ ys)) (mk r2 ex2) R2)
  : R2.IsEmpty := by
  induction ex2 generalizing R1 R2
  case nil =>
    cases hs1
    cases hs2
    apply Kind.IsEmpty.node
    cases he.is_absurd
    case here => apply! ContainsSupOf.here
    case there => apply! ContainsSupOf.there (.insert _)
  case cons a ex2 ih =>
    cases hs1
    case excl_absurd_r hss =>
      apply hs2.is_empty_l
      apply Kind.IsEmpty.node (.insert he.is_absurd)
    case excl_irrelevant_r hd2 hs1 => apply ih hs1 he; apply! excl_irrelevant_r_inv
    case excl_subclass_r hsa1 hsa2 hs1 =>
      cases he
      rename_i he1 he2
      have ⟨R, _, _⟩ := excl_subclass_r_inv hs2 hsa1 hsa2; subst_vars
      constructor
      . apply! ContainsSupOf.insert
      . apply! ih
    case excl_subclass_l =>
      apply hs2.is_empty_l
      apply Kind.IsEmpty.node (.insert he.is_absurd)
    case excl_irrelevant_l hs1 => apply! ih hs1 _ (hs2.excl_irrelevant_l_inv _ _)

theorem Subtree.Subtract.rfl
  (hs : Subtract a a R)
  : R.IsEmpty := by
  cases hs
  case tree => apply Kind.IsEmpty.node $ .here .rfl
  case excl_absurd_r hss =>
    apply Kind.IsEmpty.node $ .here hss.weaken
  case excl_irrelevant_r r1 ex2 a hd hs =>
    have ⟨R, h⟩ := Subtract.exists (mk r1 ex2) (mk r1 ex2)
    apply h.is_empty_insert (xs:=[]) (zs:=[a]) h.rfl hs
  case excl_subclass_r r1 ex2 _ _ _ hsa hs =>
    have ⟨R, h⟩ := Subtract.exists (mk r1 ex2) (mk r1 ex2)
    apply Kind.IsEmpty.absurd (.here .rfl)
    apply h.is_empty_insert (xs:=[]) (zs:=[_]) h.rfl hs
  case excl_subclass_l hss hs => cases hss.antisymm hs
  case excl_irrelevant_l hd hs _ => cases hd.symm.not_subclass hs

theorem Kind.Subtract.append_l'
  (hs1 : Subtract K1 [y] R1)
  (hs2 : Subtract K2 [y] R2)
  : Subtract (K1 ++ K2) [y] (R1 ++ R2) := by
  induction K1 generalizing K2 R1 R2
  case nil => cases hs1; simp_all
  case cons x xs ih =>
    cases hs1
    rename_i hs1a hs1b
    rw [List.cons_append]
    rw [List.append_assoc]
    apply union_l hs1a
    apply ih hs1b hs2

theorem Kind.Subtract.append_l
  (hs1 : Subtract K1 L R1)
  (hs2 : Subtract K2 L R2)
  : Subtract (K1 ++ K2) L (R1 ++ R2) := by
  induction L generalizing K1 K2 R1 R2
  case nil => cases hs1; cases hs2; apply empty_r
  case cons y ys ih =>
    cases ys
    case nil => apply! append_l'
    case cons =>
      cases hs1
      cases hs2
      rename_i Ra hs1a hs1b Rb hs2a hs2b
      apply union_r
      apply append_l' hs1a hs2a
      apply ih hs1b hs2b

theorem Kind.Subtract.append_l_inv' (hs : Subtract (K1 ++ K2) [y] R) (hs1 : Subtract K1 [y] R1) : ∃ R2, R = R1 ++ R2 ∧ Subtract K2 [y] R2 := by
  induction K1 generalizing K2 R R1
  case nil => cases hs1; exists R
  case cons x xs ih =>
    cases hs1
    rename_i hs1a hs1b
    rw [List.cons_append] at hs
    cases hs
    rename_i hsa hsb
    have ⟨R, heq, ih⟩ := ih hsb hs1b
    cases hs1a.inj hsa
    exists R
    apply And.intro <;> simp_all

theorem Kind.Subtract.append_l_inv (hs : Subtract (K1 ++ K2) L R) (hs1 : Subtract K1 L R1) : ∃ R2, R = R1 ++ R2 ∧ Subtract K2 L R2 := by
  induction L generalizing K1 K2 R R1
  generalize h : K1 ++ K2 = C at hs
  case nil => cases hs1; cases hs; exists K2; apply And.intro; simp_all; apply empty_r
  case cons y ys ih =>
    cases ys
    case nil => apply! append_l_inv'
    case cons =>
      cases hs1
      rename_i hs1a hs1b
      generalize h : K1 ++ K2 = C at hs
      cases hs
      rename_i hsa hsb
      subst_vars
      have ⟨R1, heq1, ih1⟩ := hsa.append_l_inv' hs1a
      subst_vars
      have ⟨R2, heq2, ih2⟩ := ih hsb hs1b
      exists R2
      simp_all
      apply! union_r

theorem Kind.Subtract.cons_l_inv (hs : Subtract (K :: K1) L R) (hs1 : Subtract [K] L R1) : ∃ R2, R = R1 ++ R2 ∧ Subtract K1 L R2 := by
  apply append_l_inv hs hs1
theorem Kind.Subtract.cons_l_inv' (hs : Subtract (x :: K1) [y] R) (hs1 : x.Subtract y R1) : ∃ R2, R = R1 ++ R2 ∧ Subtract K1 [y] R2 := by
  have ⟨R, h1, h2⟩ := cons_l_inv hs (.union_l hs1 .empty_l)
  simp at h1
  aesop

theorem Kind.Subtract.cons_l_split (hs : Subtract (K :: K1) L R): ∃ R1 R2, R = R1 ++ R2 ∧ Subtract [K] L R1 ∧ Subtract K1 L R2 := by
  have ⟨Rp, hp⟩ := Subtract.exists [K] L
  have ⟨Rt, ht⟩ := hs.cons_l_inv hp
  exists Rp, Rt
  simp_all
theorem Kind.Subtract.append_l_split (hs : Subtract (K1 ++ K2) L R): ∃ R1 R2, R = R1 ++ R2 ∧ Subtract K1 L R1 ∧ Subtract K2 L R2 := by
  have ⟨Rp, hp⟩ := Subtract.exists K1 L
  have ⟨Rt, ht⟩ := hs.append_l_inv hp
  exists Rp, Rt
  simp_all

theorem Subtree.Subtract.is_empty_subroot_l
  (hs1 : Subtract a b R1)
  (he1 : R1.IsEmpty)
  (hs2 : Subtract (mk c a.excls) b R2)
  (hsub : c.Subclass a.root)
  : R2.IsEmpty := by
  induction hs1 generalizing R2
  case tree =>
    cases hs2; simp_all; apply Kind.IsEmpty.node
    cases he1.is_absurd
    case here hsub2 => apply ContainsSupOf.here $ hsub.trans hsub2
    case there hsc => apply ContainsSupOf.there $ hsc.trans_subclass hsub
  case excl_absurd_r hss =>
    cases hs2.excl_absurd_r_inv hss
    apply! Kind.IsEmpty.node $ he1.is_absurd.trans_subclass _
  case excl_irrelevant_r hd hs1 ih =>
    have hs2 := hs2.excl_irrelevant_r_inv hd
    apply! ih
  case excl_subclass_r a hsa2 hsa1 hs1 ih =>
    simp_all
    cases he1
    cases Classifier.subclass_or_disjoint a c <;> rename_i hc
    . have ⟨R, _, hs2⟩ := hs2.excl_subclass_r_inv hc hsa2
      subst_vars
      constructor; aesop
      apply! ih
    . cases hc <;> rename_i hc
      . cases hs2.excl_subclass_l_inv hc hsa2
        apply! Kind.IsEmpty.node (ContainsSupOf.trans_subclass _ hc.weaken)
      . have hs2 := hs2.excl_irrelevant_l_inv hc.symm hsa2
        apply! ih
  case excl_subclass_l hsa2 hss1 =>
    cases hs2.excl_subclass_l_inv (hss1.subclass_l hsub) hsa2
    apply! Kind.IsEmpty.node $ he1.is_absurd.trans_subclass _
  case excl_irrelevant_l hsa2 hd1 hs1 ih =>
    have hs2 := hs2.excl_irrelevant_l_inv (hd1.refines_subclass_l hsub) hsa2
    apply! ih

theorem Subtree.Subtract.is_empty_middle
  (hs1 : Subtract x y R1)
  (he1 : R1.IsEmpty)
  (hs2 : Subtract x z R2)
  (hs3 : R2.Subtract [y] R3)
  : R3.IsEmpty := by
  induction hs2 generalizing R3
  case tree => apply hs1.is_empty_insert (xs:=[]) (zs:=[_]) he1 hs3.is_singleton
  case excl_absurd_r hss2 => cases hs1.inj hs3.is_singleton; simp_all
  case excl_irrelevant_r hd2 hs2 ih => apply! ih
  case excl_subclass_r r1 ex1 r2 ex2 _ a hsa2 hsa1 hs2 ih =>
    have ⟨R0, h0⟩ := Subtract.exists (mk a ex1) y
    have ⟨R', _, hs3'⟩ := hs3.cons_l_inv' h0
    subst_vars
    apply Kind.IsEmpty.append $ hs1.is_empty_subroot_l he1 h0 hsa1
    apply! ih
  case excl_subclass_l hsa2 hss1 => cases hs1.inj hs3.is_singleton; simp_all
  case excl_irrelevant_l hsa2 hd1 hs2 ih => apply! ih

theorem Kind.Subtract.is_empty_middle'
  (hs1 : Subtract K [y] R1)
  (he1 : R1.IsEmpty)
  (hs2 : Subtract K [z] R2)
  (hs3 : Subtract R2 [y] R3)
  : R3.IsEmpty := by
  induction K generalizing R1 R2 R3
  case nil => cases hs1; cases hs2; cases hs3; simp_all
  case cons x xs ih =>
    cases hs1
    cases hs2
    rename_i hs1a hs1b R2 R1 hs2a hs2b
    have ⟨he1a, he1b⟩ := he1.append_inv
    have ⟨Rl, hl⟩ := Kind.Subtract.exists R1 [y]
    have ⟨R3', _, hs3'⟩ := hs3.append_l_inv hl
    subst_vars
    apply IsEmpty.append
    apply! hs1a.is_empty_middle
    apply! ih

theorem Kind.Subtract.is_empty_transform_internal
  (hs1 : Subtract (.node r1 (xs ++ ys)) L R1)
  (he1 : R1.IsEmpty)
  (hs2 : Subtract (.node c (xs ++ zs ++ ys)) L R2)
  (hsub : c.Subclass r1)
  : R2.IsEmpty := by
  cases hs1
  case empty_r => cases hs2; apply IsEmpty.node (.trans_subclass (.insert he1.is_absurd) hsub)
  case union_l y   _ _ ha hb =>
    cases hb.empty_l_inv; simp at he1
    have ⟨R', h'⟩ := Subtree.Subtract.exists (.mk r1 (xs ++ zs ++ ys)) y
    apply h'.is_empty_subroot_l _ hs2.is_singleton hsub
    apply ha.is_empty_insert he1 h'
  case union_r R1' y' ys' ha1' hb1 =>
    cases hs2
    rename_i R2' ha2' hb2
    have ha1 := ha1'.is_singleton
    have ha2 := ha2'.is_singleton
    generalize h : (Subtree.mk r1 (xs ++ ys)) = x at ha1
    induction ha1 generalizing R1 R2' R2 <;> (injections; subst_vars)
    case tree =>
      cases ha2
      rw [← List.cons_append] at hb1 hb2
      apply is_empty_transform_internal hb1 he1 hb2 hsub
    case excl_absurd_r hss =>
      cases ha2.excl_absurd_r_inv hss
      apply hb1.is_empty_transform_internal he1 hb2 hsub
    case excl_irrelevant_r hd2 ha1 ih =>
      have ha2 := ha2.excl_irrelevant_r_inv hd2
      apply ih he1 (.singleton ha1) hb1 (.singleton ha2) hb2 ha2 (.refl _)
    case excl_subclass_r r1 r2 _ _ b hsa2 hsa1 ha1 ih =>
      have ⟨Rp1, hp1⟩ := Subtract.exists (.node b (xs ++ ys)) (y' :: ys')
      have ⟨Rs1, _, hh1⟩ := hb1.append_l_inv hp1
      subst_vars
      have ⟨hep1, hes1⟩ := he1.append_inv
      cases Classifier.subclass_or_disjoint b c <;> rename_i hc
      . have ⟨R, heq, ha2⟩ := ha2.excl_subclass_r_inv hc hsa2
        simp_all only [heq]
        have ⟨Rp2, hp2⟩ := Subtract.exists (.node b (xs ++ zs ++ ys)) (y' :: ys')
        have ⟨Rs2, _, hh2⟩ := hb2.append_l_inv hp2
        subst_vars
        apply IsEmpty.append
        . apply hp1.is_empty_transform_internal hep1 hp2 .rfl
        . apply ih _ (.singleton ha1) hh1 (.singleton ha2) hh2 ha2
          simp
          assumption
      . cases hc <;> rename_i hc
        . cases ha2.excl_subclass_l_inv hc hsa2
          apply hp1.is_empty_transform_internal hep1 hb2 hc.weaken
        . have ha2 := ha2.excl_irrelevant_l_inv hc.symm hsa2
          apply ih hes1 (.singleton ha1) hh1 (.singleton ha2) hb2 ha2 (.refl _)
    case excl_subclass_l hsa2 hss1 =>
      cases ha2.excl_subclass_l_inv (hss1.subclass_l hsub) hsa2
      apply hb1.is_empty_transform_internal he1 hb2 hsub
    case excl_irrelevant_l hsa2 hd1 ha1 ih =>
      have ha2 := ha2.excl_irrelevant_l_inv (hd1.refines_subclass_l hsub) hsa2
      apply ih he1 (.singleton ha1) hb1 (.singleton ha2) hb2 ha2 (.refl _)
termination_by (L.length)

theorem Kind.Subtract.is_empty_append'
  (hs1 : Subtract (.node r1 ex1) L R1)
  (he1 : R1.IsEmpty)
  (hs2 : Subtract (.node r1 (a :: ex1)) L R2)
  : R2.IsEmpty := by
  apply hs1.is_empty_transform_internal (xs:=[]) (zs:=[_]) he1 hs2 .rfl

theorem Kind.Subtract.is_empty_subroot_l'
  (hs1 : Subtract (.node r1 ex1) L R1)
  (he1 : R1.IsEmpty)
  (hs2 : Subtract (.node c ex1) L R2)
  (hsub : c.Subclass r1)
  : R2.IsEmpty := by
  apply hs1.is_empty_transform_internal (xs:=[]) (zs:=[]) he1 hs2 hsub


theorem Kind.Subtract.is_empty_cons_r'
  (hs1 : Subtract [x] L R1)
  (he1 : R1.IsEmpty)
  (hs2 : Subtract [x] (l :: L) R2)
  : R2.IsEmpty := by
  cases hs2
  case union_l ha hb =>
    cases hb.empty_l_inv
    cases hs1
    simp
    apply ha.is_empty_l he1
  case union_r R1' y' ys ha' hb =>
    have ha := ha'.is_singleton
    induction ha generalizing R1 R2
    case tree => apply! hs1.is_empty_append'
    case excl_absurd_r hss =>
      cases hs1.inj hb; aesop
    case excl_irrelevant_r hd ha ih =>
      apply! ih _ (.singleton ha)
    case excl_subclass_r r1 ex1 r2 ex2 _ a hsa2 hsa1 ha ih =>
      have ⟨R0, h0⟩ := Subtract.exists (.node a ex1) (y' :: ys)
      have ⟨Rs, _, hs⟩ := hb.cons_l_inv h0
      subst_vars
      apply IsEmpty.append
      . apply hs1.is_empty_subroot_l' he1 h0 hsa1
      . apply! ih _ (.singleton ha) hs1 hs
    case excl_subclass_l hsa2 hss1 =>
      cases hs1.inj hb; aesop
    case excl_irrelevant_l hsa2 hd1 ha ih =>
      apply! ih _ (.singleton ha)

theorem Kind.Subtract.is_empty_cons_r
  (hs1 : Subtract K L R1)
  (he1 : R1.IsEmpty)
  (hs2 : Subtract K (l :: L) R2)
  : R2.IsEmpty := by
  induction K generalizing R1 R2
  case nil => cases hs2.empty_l_inv; constructor
  case cons x xs ih =>
    have ⟨Rp1, hp1⟩ := Subtract.exists [x] L
    have ⟨Rs1, _, hh1⟩ := hs1.cons_l_inv hp1
    have ⟨Rp2, hp2⟩ := Subtract.exists [x] (l :: L)
    have ⟨Rs2, _, hh2⟩ := hs2.cons_l_inv hp2
    subst_vars
    have ⟨_, _⟩ := he1.append_inv
    apply IsEmpty.append
    . apply! hp1.is_empty_cons_r'
    . apply! ih

theorem Kind.Subtract.rfl (hs : Subtract K K R) : R.IsEmpty := by
  cases hs
  case empty_r => constructor
  case union_l ha hb =>
    cases hb.empty_l_inv
    simp
    apply ha.rfl
  case union_r y R1 y' ys ha hb =>
    have ⟨Rp, Rt, _, hp, ht⟩ := ha.cons_l_split
    subst_vars
    have ⟨Rp1, Rt1, _, hp1, ht1⟩ := hb.append_l_split
    subst_vars
    apply IsEmpty.append
    . apply hp1.is_empty_l hp.is_singleton.rfl
    . have ⟨R', h'⟩ := Subtract.exists (y' :: ys) (y' :: ys)
      apply is_empty_cons_r h' h'.rfl (.union_r ht ht1)

theorem Kind.Subtract.cons_l
  (hs1 : Subtract [x] L R1)
  (hs2 : Subtract xs L R2)
  : Subtract (x :: xs) L (R1 ++ R2) := by
  apply append_l hs1 hs2

theorem Kind.Subtract.append_r
  (hs1 : Subtract K L1 R1)
  (hs2 : Subtract R1 L2 R2)
  : Subtract K (L1 ++ L2) R2 := by
  induction L1 generalizing K L2 R1 R2
  case nil => cases hs1; simp_all
  case cons y ys ih =>
    cases hs1
    case empty_l => cases hs2.empty_l_inv; apply empty_l'
    case union_l R2 _ R1 ha hb =>
      cases L2
      case nil =>
        simp
        generalize h : R1 ++ R2 = RR at hs2; cases hs2
        subst_vars; apply! union_l
      case cons z zs =>
        have ⟨Rh, Rt, _, hh, ht⟩ := hs2.append_l_split
        subst_vars
        simp [List.append]
        apply cons_l (.union_r (.singleton ha) hh) (.union_r hb ht)
    case union_r y' ys ha1 hb1 =>
      apply union_r ha1
      apply! ih

theorem Subtree.Subtract.is_empty_not_excluded
  (hs : Subtract a b R)
  (he : R.IsEmpty)
  : ContainsSupOf a.excls a.root ∨ ¬ ContainsSupOf b.excls a.root := by
  rw [← Decidable.imp_iff_or_not]
  intro hsc
  induction hs
  case tree => cases hsc
  case excl_absurd_r hss => exact he.is_absurd
  case excl_irrelevant_r r1 ex1 r2 ex2 _ a hd hs ih =>
    cases hsc
    case there => apply! ih he
    case here hsc =>
      cases hs.empty_implies_subclass he <;> rename_i h; aesop
      cases (hd.refines_subclass_l h).not_subclass hsc
  case excl_subclass_r hsa2 hsa1 hs ih =>
    cases he
    rename_i he1 he2
    cases hsc
    case there => apply! ih
    case here hsc => apply he1.trans_subclass hsc
  case excl_subclass_l => apply he.is_absurd
  case excl_irrelevant_l hsa2 hd1 hs ih =>
    cases hsc
    case there => apply! ih
    case here hsc => cases hd1.not_subclass hsc

theorem Subtree.Subtract.is_empty_cases
  (hs : Subtract a b R)
  (he : R.IsEmpty)
  : ContainsSupOf a.excls a.root ∨ (a.root.Subclass b.root ∧ ¬ ContainsSupOf b.excls a.root) := by
  cases hs.empty_implies_subclass he; aesop
  cases hs.is_empty_not_excluded he <;> aesop

theorem Subtree.Subtract.is_empty_remaining_subroot
  (hs1 : Subtract a b R1)
  (he1 : R1.IsEmpty)
  (hsc : ContainsSupOf b.excls x)
  (hsub : x.Subclass a.root)
  : ContainsSupOf a.excls x := by
  induction hs1
  case tree => cases hsc
  case excl_absurd_r hss => apply he1.is_absurd.trans_subclass hsub
  case excl_irrelevant_r hd2 hs ih =>
    cases hsc
    case there => apply! ih
    case here hsc =>
      cases hs.empty_implies_subclass he1 <;> rename_i h
      . apply! h.trans_subclass
      . cases (hd2.symm.refines_subclass_l hsc).not_subclass (hsub.trans h)
  case excl_subclass_r hsa2 hsa1 hs1 ih =>
    simp_all
    cases he1
    cases hsc
    case there => apply! ih
    case here => apply! ContainsSupOf.trans_subclass
  case excl_subclass_l hsa2 hss1 =>
    apply! he1.is_absurd.trans_subclass
  case excl_irrelevant_l hsa2 hd1 hs1 ih =>
    simp_all
    cases hsc
    case there => apply! ih
    case here hsc => cases (hd1.symm.refines_subclass_l hsc).not_subclass hsub

theorem Subtree.Subtract.is_empty_remaining_superroot
  (hs1 : Subtract a b R1)
  (he1 : R1.IsEmpty)
  (hsc : ContainsSupOf b.excls x)
  (hsub : a.root.StrictSub x)
  : ContainsSupOf a.excls a.root := by
  induction hs1
  case tree => cases hsc
  case excl_absurd_r hss => apply he1.is_absurd
  case excl_irrelevant_r hd2 hs ih =>
    cases hsc
    case there => apply! ih
    case here hsc =>
      cases hs.empty_implies_subclass he1 <;> rename_i h
      . apply! h
      . have hd := (hd2.refines_subclass_l h).refines_subclass_r hsc
        cases hd.not_subclass hsub.weaken
  case excl_subclass_r hsa2 hsa1 hs1 ih =>
    simp_all
    cases he1
    cases hsc
    case there => apply! ih
    case here => apply! ContainsSupOf.trans_subclass _ (.trans hsub.weaken _)
  case excl_subclass_l hsa2 hss1 =>
    apply! he1.is_absurd
  case excl_irrelevant_l hsa2 hd1 hs1 ih =>
    simp_all
    cases hsc
    case there => apply! ih
    case here hsc => cases hd1.not_subclass (hsub.weaken.trans hsc)

theorem Subtree.Subtract.is_empty_trans
  (hs1 : Subtract a b R1)
  (he1 : R1.IsEmpty)
  (hs2 : Subtract b c R2)
  (he2 : R2.IsEmpty)
  (hs3 : Subtract a c R3)
  : R3.IsEmpty := by
  induction hs2 generalizing a R1 R3
  case tree =>
    cases hs3
    cases hs1.is_empty_cases he1 <;> rename_i hs1
    . apply Kind.IsEmpty.node (.there hs1)
    . have ⟨hs1, hsc1⟩ := hs1
      cases he2.is_absurd
      case there he2 => have he2 := he2.trans_subclass hs1; contradiction
      case here he2 => exact .node (.here $ hs1.trans he2)
  case excl_absurd_r hss =>
    cases hs3.excl_absurd_r_inv hss;
    apply hs3.is_empty_l
    apply Kind.IsEmpty.node
    apply hs1.empty_r_inv he1 he2.is_absurd
  case excl_irrelevant_r hd2 hs2 ih =>
    have hs3 := hs3.excl_irrelevant_r_inv hd2
    apply! ih
  case excl_subclass_r r1 ex1 r2 ex2 _ x hsa2 hsa1 hs2 ih =>
    cases he2
    rename_i he2a he2b
    cases x.subclass_or_disjoint a.root <;> rename_i hx
    . have ⟨R0, _, h0⟩ := hs3.excl_subclass_r_inv hx hsa2
      subst_vars
      apply Kind.IsEmpty.absurd
      . cases hs1.is_empty_cases he1 <;> rename_i hsc1
        . apply! hsc1.trans_subclass
        . have ⟨hx1, hy⟩ := hsc1; simp_all
          apply! is_empty_remaining_subroot hs1 he1
      . apply! ih
    . cases hx <;> rename_i hx
      . cases hs3.excl_subclass_l_inv hx hsa2
        apply Kind.IsEmpty.node
        apply! is_empty_remaining_superroot hs1 he1
      . have hs3 := hs3.excl_irrelevant_l_inv hx.symm hsa2
        apply! ih
  case excl_subclass_l hsa2 hss1 =>
    apply hs3.is_empty_l
    apply Kind.IsEmpty.node
    apply hs1.empty_r_inv he1 he2.is_absurd
  case excl_irrelevant_l r1 ex1 r2 ex2 _ x hsa2 hd1 hs2 ih =>
    simp_all
    cases x.subclass_or_disjoint a.root <;> rename_i hx
    . have ⟨R0, _, h0⟩ := hs3.excl_subclass_r_inv hx hsa2
      subst_vars
      constructor
      . have ⟨_, h⟩ := Subtract.exists (mk x a.excls) (mk r1 ex1)
        have h0 := hs1.is_empty_subroot_l he1 h hx
        cases h.empty_implies_subclass h0 <;> rename_i h; aesop
        cases hd1.symm.not_subclass h
      . apply! ih
    . cases hx <;> rename_i hx
      . cases hs3.excl_subclass_l_inv hx hsa2
        apply Kind.IsEmpty.node
        cases hs1.empty_implies_subclass he1 <;> rename_i hs1; aesop
        cases ((hd1.refines_subclass_l hs1).refines_subclass_r hx.weaken).not_subclass .rfl
      . have hs3 := hs3.excl_irrelevant_l_inv hx.symm hsa2
        apply! ih

theorem Kind.Subtract.is_empty_trans''
  (hs1 : Subtract A [b] R1)
  (he1 : R1.IsEmpty)
  (hs2 : b.Subtract c R2)
  (he2 : R2.IsEmpty)
  (hs3 : Subtract A [c] R3)
  : R3.IsEmpty := by
  induction A generalizing R1 R2 R3
  case nil => cases hs3; constructor
  case cons x xs ih =>
    have ⟨R1h, R1t, _, hh1, ht1⟩ := hs1.cons_l_split
    have ⟨R3h, R3t, _, hh3, ht3⟩ := hs3.cons_l_split
    subst_vars
    have ⟨he1h, he1t⟩ := he1.append_inv
    apply IsEmpty.append
    . apply hh1.is_singleton.is_empty_trans he1h hs2 he2 hh3.is_singleton
    . apply! ih

theorem Kind.Subtract.union_r_inv
  (hs : Subtract A (b :: b' :: bs) R)
  : ∃ R1, Subtract A [b] R1 ∧ Subtract R1 (b' :: bs) R := by
  cases hs
  aesop

end CaplessK
