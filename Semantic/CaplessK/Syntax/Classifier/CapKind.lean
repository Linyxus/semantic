import Semantic.CaplessK.Syntax.Classifier.Core

namespace CaplessK

-- **
-- CapKinds
-- **

/-- A subtree of a single root and an exclusion list.
    Notionally, it represents the subtree rooted at `root`,
    excluding the subtrees rooted at `excls`. -/
structure Subtree : Type where
  root  : Classifier
  excls : List Classifier
deriving DecidableEq

/-- A classifier filter : a list of filtered subtree. -/
def CapKind : Type := List Subtree

@[simp]
instance : HAppend CapKind CapKind CapKind where
  hAppend xs ys := List.append xs ys

/-- A single node. -/
@[simp]
def CapKind.node (c : Classifier) (excls : List Classifier) : CapKind := [Subtree.mk c excls]

/-- Shorthand notation for a subtree without exclusions -/
@[simp]
def CapKind.classifier (c : Classifier) := CapKind.node c []

/-- The empty kind.
    Note that non-empty kinds can still represent an empty set of nodes.
    See `IsEmpty`. -/
@[simp]
def CapKind.empty : CapKind := []

/-- The "top" kind. This is a CapKind that includes all nodes in the classifier tree. -/
@[simp]
def CapKind.top := node .top []

/-- Helper relation: does `xs` contain a superclass of `c`? -/
inductive ContainsSupOf : List Classifier -> Classifier -> Prop where
  | here : b.Subclass a -> ContainsSupOf (a :: xs) b
  | there : ContainsSupOf xs b -> ContainsSupOf (a :: xs) b

instance ContainsSupOf.decidable : Decidable (ContainsSupOf xs a) := by
  cases xs
  case nil => apply Decidable.isFalse; intro h; cases h
  case cons x xs =>
    cases decidable (xs:=xs) (a:=a)
    case isTrue h => exact .isTrue (.there h)
    case isFalse h =>
      cases Classifier.Subclass.decidable a x
      case isTrue h2 => exact .isTrue (.here h2)
      case isFalse h2 =>
        apply Decidable.isFalse
        intro hx
        cases hx <;> contradiction

/-- Functional version of `ContainsSupOf`: does `xs` contain a superclass of `a`? -/
def containsSupOf (xs : List Classifier) (a : Classifier) : Bool :=
  match xs with
  | [] => false
  | x :: xs => a.subclass x || containsSupOf xs a

theorem containsSupOf_iff_ContainsSupOf : containsSupOf xs a ↔ ContainsSupOf xs a := by
  induction xs with
  | nil =>
    simp [containsSupOf]
    intro h; cases h
  | cons x xs ih =>
    simp only [containsSupOf, Bool.or_eq_true]
    constructor
    · intro h
      cases h with
      | inl hsub =>
        apply ContainsSupOf.here
        rw [Classifier.subclass_is_Subclass]
        exact hsub
      | inr htail =>
        apply ContainsSupOf.there
        rw [← ih]
        exact htail
    · intro h
      cases h with
      | here hsub =>
        left
        rw [← Classifier.subclass_is_Subclass]
        exact hsub
      | there htail =>
        right
        rw [ih]
        exact htail

theorem ContainsSupOf.append_l (h : ContainsSupOf xs b) : ContainsSupOf (xs ++ ys) b := by
  induction h with
  | here hs => exact .here hs
  | there _ ih => exact .there ih

theorem ContainsSupOf.append_r (h : ContainsSupOf ys b) : ContainsSupOf (xs ++ ys) b := by
  induction xs with
  | nil => exact h
  | cons _ _ ih => exact .there ih

theorem ContainsSupOf.insert
    (h : ContainsSupOf (xs ++ ys) b) : ContainsSupOf (xs ++ zs ++ ys) b := by
  induction xs generalizing ys with
  | nil => apply! append_r
  | cons x xs ih =>
    cases h
    case here => apply! here
    case there => apply there; apply! ih

theorem ContainsSupOf.trans_subclass
    (h : ContainsSupOf xs a) (hs : b.Subclass a) : ContainsSupOf xs b := by
  induction h with
  | here hs' => exact .here (hs.trans hs')
  | there _ ih => exact .there (ih hs)

theorem ContainsSupOf.of_append
    (h : ContainsSupOf (xs ++ ys) b) : ContainsSupOf xs b ∨ ContainsSupOf ys b := by
  induction xs with
  | nil => exact .inr h
  | cons a xs ih =>
    cases h with
    | here hs => exact .inl (.here hs)
    | there h =>
      cases ih h with
      | inl h => exact .inl (.there h)
      | inr h => exact .inr h

/-- Is a CapKind empty? -/
inductive CapKind.IsEmpty : CapKind -> Prop where
  | empty : IsEmpty []
  | absurd : ContainsSupOf exs r -> IsEmpty xs -> IsEmpty (Subtree.mk r exs :: xs)

instance CapKind.IsEmpty.decidable : Decidable (IsEmpty K) := by
  cases K
  case nil => apply isTrue .empty
  case cons x xs =>
    cases ContainsSupOf.decidable (xs:=x.excls) (a:=x.root)
    case isFalse => apply isFalse; intro h; cases h; simp_all
    cases decidable (K:=xs)
    case isFalse => apply isFalse; intro h; cases h; simp_all
    rename_i h1 h2
    apply isTrue (.absurd h1 h2)

/-- Functional version of `IsEmpty`: is a CapKind empty? -/
def CapKind.isEmpty (K : CapKind) : Bool :=
  match K with
  | [] => true
  | x :: xs => containsSupOf x.excls x.root && isEmpty xs

theorem CapKind.isEmpty_iff_IsEmpty : isEmpty K ↔ IsEmpty K := by
  induction K with
  | nil =>
    constructor
    · intro _; exact .empty
    · intro _; simp [isEmpty]
  | cons x xs ih =>
    simp only [isEmpty, Bool.and_eq_true]
    constructor
    · intro ⟨hcontains, htail⟩
      apply IsEmpty.absurd
      · rw [← containsSupOf_iff_ContainsSupOf]
        exact hcontains
      · rw [← ih]
        exact htail
    · intro h
      cases h with
      | absurd hcontains htail =>
        constructor
        · rw [containsSupOf_iff_ContainsSupOf]
          exact hcontains
        · rw [ih]
          exact htail

theorem CapKind.IsEmpty.node (hsc : ContainsSupOf exs r) : IsEmpty [.mk r exs] := absurd hsc .empty

/-- If a `node` is empty, it is absurd. -/
theorem CapKind.IsEmpty.is_absurd (he : IsEmpty (.node r exs)) : ContainsSupOf exs r := by
  cases he; assumption

theorem CapKind.IsEmpty.append (he1 : IsEmpty R1) (he2 : IsEmpty R2) : IsEmpty (R1 ++ R2) := by
  induction R1 generalizing R2
  case nil => simp_all
  case cons x xs ih =>
    rw [List.cons_append]
    cases he1
    apply! absurd _ (ih _ _)

theorem CapKind.IsEmpty.append_inv (he : IsEmpty (R1 ++ R2)) : IsEmpty R1 ∧ IsEmpty R2 := by
  induction R1 generalizing R2
  case nil => simp_all; apply empty
  case cons x xs ih =>
    rw [List.cons_append] at he
    cases he
    rename_i he1 he2
    have ⟨_, _⟩ := ih he2
    apply And.intro
    · apply! absurd
    · aesop

end CaplessK
