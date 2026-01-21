import Mathlib.Tactic
import Semantic.Prelude

/-!
This module defines classifiers in CaplessK.
-/

namespace CaplessK

/-- Classifiers represent nodes in the infinite classifier tree.
    Essentially, they are a sequence of natural numbers, representing the indicies of the children to walk
    on the path from the root to the node. -/
inductive Classifier : Type where
  | top : Classifier
  | child : Nat -> Classifier -> Classifier
deriving DecidableEq

/-- The control classifier. -/
def Classifier.control := child 0 .top

/-- Subclass: Is `a` within the subtree rooted at `b`? -/
inductive Classifier.Subclass : Classifier -> Classifier -> Prop where
  | rfl : Subclass a a
  | parent_l : Subclass a b -> Subclass (child n a) b

/-- Strict subclass = subclass and not equal. -/
inductive Classifier.StrictSub : Classifier -> Classifier -> Prop where
  | child : StrictSub (child n a) a
  | parent_l : StrictSub a b -> StrictSub (child n a) b

theorem Classifier.Subclass.might_strict (hs : Subclass a b) : a = b ∨ StrictSub a b := by
  induction hs
  case rfl => left; simp
  case parent_l hp ih =>
    right
    cases ih
    case inl => subst_vars; constructor
    case inr => apply StrictSub.parent_l; trivial

theorem Classifier.StrictSub.weaken (hs : StrictSub a b) : Subclass a b := by
  induction hs
  case child => apply Subclass.parent_l .rfl
  case parent_l hp ih => apply Subclass.parent_l ih

theorem Classifier.StrictSub.size (hs : StrictSub a b) : sizeOf a > sizeOf b := by induction hs <;> (simp; try omega)

theorem Classifier.StrictSub.neq (hs : StrictSub a b) : a ≠ b := by
  apply Ne.intro
  intro h
  have hs := hs.size
  rw [h] at hs
  omega

/-- Disjoint: the classifier nodes are not within each other's subtrees. -/
inductive Classifier.Disjoint : Classifier -> Classifier -> Prop where
  | base : n != m -> Disjoint (child n p) (child m p)
  | left : Disjoint a b -> Disjoint (child n a) b
  | right : Disjoint a b -> Disjoint a (child m b)

theorem Classifier.Subclass.of_top : Subclass a .top := by
  induction a
  case top => apply rfl
  case child n k ih => apply parent_l ih

theorem Classifier.Subclass.parent_r (hs : Subclass a (child n b)) : Subclass a b := by
  cases hs
  case rfl => apply parent_l rfl
  case parent_l hp =>
    apply parent_l hp.parent_r

theorem Classifier.Subclass.trans (h1 : Subclass a b) (h2 : Subclass b c) : Subclass a c := by
  induction h2
  case rfl => assumption
  case parent_l hp ih => apply ih h1.parent_r

theorem Classifier.Subclass.down_r (hs : Subclass a b) : a = b ∨ ∃ n, Subclass a (child n b) := by
  induction hs
  case rfl => simp
  case parent_l ih =>
    rename_i n _
    right
    cases ih
    case inl ih => subst_vars; exists n; constructor
    case inr ih =>
      have ⟨m, ih⟩ := ih
      exists m
      apply parent_l ih

theorem Classifier.Subclass.size (hs : Subclass a b) : sizeOf a ≥ sizeOf b := by
  induction hs <;> (simp; try omega)

theorem Classifier.Subclass.antisymm (h1 : Subclass a b) (h2 : Subclass b a) : a = b := by
  induction h1
  case rfl => simp
  case parent_l hp ih =>
    have hp1 := hp.size
    have h21 := h2.size
    simp at h21
    omega

theorem Classifier.StrictSub.antisymm (hs : StrictSub a b) (hs2 : Subclass b a) : False := by
  have h := hs.size
  have h2 := hs2.size
  omega

theorem Classifier.StrictSub.subclass_r (hss : StrictSub a b) (hs : Subclass b c) : StrictSub a c := by
  induction hss
  case child n a =>
    induction hs generalizing n
    case rfl => apply child
    case parent_l m k ih =>
      apply parent_l ih
  case parent_l n a ih =>
    apply! parent_l $ ih _

theorem Classifier.StrictSub.subclass_l (hss : StrictSub a b) (hs : Subclass c a) : StrictSub c b := by
  cases hs.might_strict <;> rename_i hs
  . simp_all
  . apply hs.subclass_r hss.weaken

theorem Classifier.Disjoint.symm (hd : Disjoint a b) : Disjoint b a := by
  induction hd
  case base hne =>
    apply base; aesop
  case left => apply! right
  case right => apply! left

theorem Classifier.Disjoint.refines_subclass_r
  (hd : Disjoint b a2)
  (hs : Subclass a1 a2) : Disjoint b a1 := by
  induction hs
  case rfl => assumption
  case parent_l hs ih =>
    apply right $ ih hd

theorem Classifier.Disjoint.refines_subclass_l (hd : Disjoint a2 b) (hs : Subclass a1 a2) : Disjoint a1 b := by
  apply symm
  apply refines_subclass_r hd.symm hs

theorem Classifier.Disjoint.left_inv (hd : Disjoint (child n a) b) : Subclass b a ∨ Disjoint a b := by
  cases hd
  case base m _ => left; constructor; constructor;
  case left => right; assumption
  case right hd =>
    cases hd.left_inv
    case inl hd => left; constructor; assumption
    case inr hd => right; apply! right

theorem Classifier.Disjoint.not_subclass (hd : Disjoint a b) (hs : Subclass a b) : False := by
  induction a generalizing b
  case top =>
    induction b
    case top => cases hd
    case child n p ih => cases hs
  case child n p ih =>
    induction b
    case top => cases hs; cases hd; apply! ih
    case child m q ih2 =>
      cases hs
      case rfl =>
        cases hd
        case base => aesop
        case left hs => apply ih2 hs.symm $ .parent_l .rfl
        case right hs => apply ih2 hs $ .parent_l .rfl
      case parent_l hs =>
        cases hd
        case base => have h := hs.size; simp at h
        case left => apply! ih
        case right hd =>
          cases hd.left_inv
          case inl hd =>
            have h := hs.parent_r.antisymm hd
            subst_vars
            have h := hs.size; simp at h
          case inr hd =>
            apply ih (b:=q) hd hs.parent_r

theorem Classifier.Disjoint.to_subclass (hd : Disjoint a b) (hs : Subclass c b) : Disjoint a c := by
  induction hs
  case rfl => assumption
  case parent_l hp ih =>
    apply right
    apply ih hd

/-- Each pair of classifier nodes are either subclass of the other, or they are disjoint. -/
theorem Classifier.subclass_or_disjoint a b:
  Subclass a b ∨ StrictSub b a ∨ Disjoint a b := by
  induction a
  case top =>
    cases Subclass.of_top (a:=b).might_strict
    case inl => simp_all; left; exact .rfl
    case inr => aesop
  case child n k ih =>
    cases ih
    case inl ih =>
      left; constructor; assumption
    case inr ih =>
      cases ih
      case inl ih =>
        cases ih.weaken.down_r
        { subst_vars; left; apply Subclass.parent_l .rfl }
        { rename_i ih1; have ⟨m, ih1⟩ := ih1;
          generalize h : (n == m) = h0;
          cases h0
          right; right;
          apply Disjoint.refines_subclass_r; apply Disjoint.base (m:=m); aesop; assumption
          have h0 := LawfulBEq.eq_of_beq h; subst_vars
          cases ih1.might_strict
          . left; subst_vars; exact .rfl
          . aesop
        }
      case inr ih =>
        right; right; apply Disjoint.left ih

/-- The subclass relationm, defined as a deterministic boolean function. -/
def Classifier.subclass (a : Classifier) (b : Classifier) :=
  if a == b then true
  else match a with
    | .top => false
    | .child n p => p.subclass b

theorem Classifier.subclass_is_Subclass : Subclass a b ↔ a.subclass b := by
  apply Iff.intro
  . intro hs
    induction hs
    case rfl => unfold subclass; simp
    case parent_l n p => unfold subclass; simp; right; assumption
  . intro hs
    unfold subclass at hs
    split at hs
    case isTrue h =>
      have h1 := LawfulBEq.eq_of_beq h
      subst_vars
      constructor
    case isFalse h =>
      split at hs
      . contradiction
      . rename_i p
        constructor
        rw [subclass_is_Subclass (a:=p)]
        assumption

instance Classifier.Subclass.decidable (a b : Classifier) : Decidable (a.Subclass b) := by
  cases h : a.subclass b
  . apply Decidable.isFalse; rw [Classifier.subclass_is_Subclass]; simp_all
  . apply Decidable.isTrue; simp [Classifier.subclass_is_Subclass, h]

/-- The disjoint relation as a deterministic boolean function. -/
def Classifier.disjoint (a : Classifier) (b : Classifier) :=
  match a with
  | .top => false
  | .child n p =>
    match b with
    | .top => false
    | .child m q =>
      if p == q then n != m
      else disjoint (.child n p) q || disjoint p (.child m q)

theorem Classifier.disjoint_is_Disjoint {a b : Classifier} : Disjoint a b ↔ a.disjoint b := by
  apply Iff.intro
  . intro hs
    induction hs with
    | base hne =>
      unfold disjoint
      simp [hne]
    | @left a' b' n ha ih =>
      unfold disjoint
      match b' with
      | .top => cases ha.not_subclass .of_top
      | .child m q =>
        simp only
        split
        . rename_i heq
          have h1 := LawfulBEq.eq_of_beq heq
          subst_vars
          cases ha.symm.not_subclass $ .parent_l .rfl
        . simp [ih]
    | @right a' b' m ha ih =>
      unfold disjoint
      match a' with
      | .top =>
        have : ∀ c, ¬ Disjoint top c := fun c h => by
          induction c with
          | top => cases h
          | child n p ih =>
            cases h with
            | right ha => exact ih ha
        exact absurd ha (this _)
      | .child n p =>
        simp only
        split
        . rename_i heq
          have heq' := LawfulBEq.eq_of_beq heq
          subst heq'
          cases ha.not_subclass $ .parent_l .rfl
        . simp [ih]
  . intro hs
    unfold disjoint at hs
    split at hs
    . cases hs
    . split at hs
      . cases hs
      . split at hs
        . rename_i h
          have h1 := LawfulBEq.eq_of_beq h
          subst_vars
          apply! Disjoint.base
        . simp at hs
          cases hs
          case inl hs =>
            apply Disjoint.right
            rw [disjoint_is_Disjoint]
            assumption
          case inr hs =>
            apply Disjoint.left
            rw [disjoint_is_Disjoint]
            assumption
termination_by sizeOf a + sizeOf b

instance Classifier.Disjoint.decidable : Decidable (Disjoint a b) := by
  cases h : a.disjoint b
  case true => apply isTrue; rw [disjoint_is_Disjoint]; exact h
  case false => apply isFalse; rw[disjoint_is_Disjoint]; simp [h]

/-- Same as `subclass_or_disjoint`, but with the functions. -/
theorem Classifier.subclass_or_disjoint' (a b : Classifier) : a.subclass b ∨ b.subclass a ∨ a.disjoint b := by
  cases subclass_or_disjoint a b <;> rename_i h
  . simp_all [Classifier.subclass_is_Subclass]
  . cases h <;> rename_i h
    . have h0 := h.weaken; simp_all [subclass_is_Subclass]
    . simp_all [disjoint_is_Disjoint]

end CaplessK
