import Semantic.Stlc.Debruijn

/-!
Syntax definitions for the simply typed lambda calculus.

This module defines the abstract syntax tree for STLC expressions, types,
and operations on them.
-/

namespace Stlc

/-!
Types in STLC.
-/
inductive Ty : Type where
| bool : Ty
| nat : Ty
| arrow : Ty -> Ty -> Ty

/-!
Expressions in STLC.
The type parameter `n` represents the number of free variables.
-/
inductive Exp : Nat -> Type where
| var : Var n -> Exp n
| abs : Ty -> Exp (n+1) -> Exp n
| app : Exp n -> Exp n -> Exp n
| btrue : Exp n
| bfalse : Exp n
| nzero : Exp n
| nsucc : Exp n -> Exp n
| pred : Exp n -> Exp n
| iszero : Exp n -> Exp n
| cond : Exp n -> Exp n -> Exp n -> Exp n

/-!
Apply a variable renaming to an expression.
-/
def Exp.rename : Exp n1 -> Rename n1 n2 -> Exp n2
| .var x, f => .var (f.var x)
| .abs T e, f => .abs T (e.rename (f.liftVar))
| .app e1 e2, f => .app (e1.rename f) (e2.rename f)
| .btrue, _ => .btrue
| .bfalse, _ => .bfalse
| .nzero, _ => .nzero
| .nsucc e, f => .nsucc (e.rename f)
| .pred e, f => .pred (e.rename f)
| .iszero e, f => .iszero (e.rename f)
| .cond e1 e2 e3, f => .cond (e1.rename f) (e2.rename f) (e3.rename f)

/-!
Predicate for numeric values.
-/
@[aesop safe [constructors]]
inductive Exp.IsNumVal : Exp n -> Prop where
| nzero : Exp.IsNumVal .nzero
| nsucc : Exp.IsNumVal e -> Exp.IsNumVal (.nsucc e)

/-!
Predicate for boolean values.
-/
@[aesop safe [constructors]]
inductive Exp.IsBoolVal : Exp n -> Prop where
| btrue : Exp.IsBoolVal .btrue
| bfalse : Exp.IsBoolVal .bfalse

/-!
Predicate for values.
-/
@[aesop unsafe [constructors 95%]]
inductive Exp.IsVal : Exp n -> Prop where
| abs : Exp.IsVal (.abs T e)
| bool : Exp.IsBoolVal e -> Exp.IsVal e
| num : Exp.IsNumVal e -> Exp.IsVal e

/-!
A value is an expression that satisfies the value predicate.
-/
structure Val (n : Nat) where
  unwrap : Exp n
  isVal : unwrap.IsVal

/-!
Renaming preserves the numeric value predicate.
-/
theorem Exp.rename_IsNumVal {e : Exp s}
  (hv : e.IsNumVal) :
  (e.rename f).IsNumVal := by
  induction hv with
  | nzero => exact IsNumVal.nzero
  | nsucc _ ih => exact IsNumVal.nsucc ih

/-!
Renaming preserves the boolean value predicate.
-/
theorem Exp.rename_IsBoolVal {e : Exp s}
  (hv : e.IsBoolVal) :
  (e.rename f).IsBoolVal := by
  cases hv with
  | btrue => exact IsBoolVal.btrue
  | bfalse => exact IsBoolVal.bfalse

/-!
Renaming preserves the value predicate.
-/
theorem Exp.rename_IsVal {e : Exp s}
  (hv : e.IsVal) :
  (e.rename f).IsVal := by
  cases hv with
  | abs => exact IsVal.abs
  | bool hb => exact IsVal.bool (rename_IsBoolVal hb)
  | num hn => exact IsVal.num (rename_IsNumVal hn)

/-!
Apply a variable renaming to a value.
-/
def Val.rename (v : Val n1) (f : Rename n1 n2) : Val n2 where
  unwrap := v.unwrap.rename f
  isVal := Exp.rename_IsVal v.isVal

/-!
Decidable test for whether an expression is a boolean value.
-/
def Exp.is_bool_val : Exp n -> Bool
| .btrue => true
| .bfalse => true
| _ => false

/-!
Decidable test for whether an expression is a numeric value.
-/
def Exp.is_num_val : Exp n -> Bool
| .nzero => true
| .nsucc e => e.is_num_val
| _ => false

/-!
Decidable test for whether an expression is a value.
-/
def Exp.is_val : Exp n -> Bool
| .abs _ _ => true
| e => e.is_bool_val || e.is_num_val

/-!
Lifting the identity renaming yields the identity renaming.
-/
theorem Rename.id_liftVar {n : Nat} :
  (Rename.id (n:=n)).liftVar = Rename.id := by
  apply Rename.funext
  intro x
  cases x <;> rfl

/-!
Renaming with the identity renaming is a no-op.
-/
theorem Exp.rename_id {e : Exp n} :
  e.rename Rename.id = e := by
  induction e <;> try grind [Exp.rename, Rename.id]
  case var => rfl
  case abs =>
    simp [Exp.rename]
    simpa [Rename.id_liftVar]

/-!
Lifting commutes with renaming composition.
-/
theorem Rename.comp_liftVar {f1 : Rename n1 n2} {f2 : Rename n2 n3} :
  (f1.comp f2).liftVar = f1.liftVar.comp f2.liftVar := by
  apply Rename.funext
  intro x
  cases x <;> rfl

/-!
Composition of renamings distributes over expression renaming.
-/
theorem Exp.rename_comp {e : Exp n} {f2 : Rename n2 n3} :
  (e.rename f1).rename f2 = e.rename (f1.comp f2) := by
  induction e generalizing n2 n3 <;> try grind [Exp.rename, Rename.comp]
  case var => rfl
  case abs =>
    simp [Exp.rename]
    grind [Rename.comp_liftVar]

/-!
Lift a renaming under `k` binders.
-/
def Rename.lift (f : Rename n1 n2) (k : Nat) : Rename (n1+k) (n2+k) :=
  match k with
  | 0 => f
  | k+1 => (f.lift k).liftVar

/-!
Commutativity of weakening and a renaming.
-/
theorem Exp.rename_succVar_comm {e : Exp n1} {f : Rename n1 n2} :
  (e.rename f).rename (Rename.succVar) =
  (e.rename (Rename.succVar)).rename (f.liftVar) := by
  simp [Exp.rename_comp, Rename.succVar_comm]

/-!
Renaming preserves the boolean value test.
-/
theorem Exp.rename_is_boolval {e : Exp n}
  (h : e.is_bool_val) :
  (e.rename f).is_bool_val := by
  cases e <;> aesop

/-!
Renaming preserves the numeric value test.
-/
theorem Exp.rename_is_numval {e : Exp n}
  (h : e.is_num_val) :
  (e.rename f).is_num_val := by
  induction e <;> aesop

/-!
Renaming preserves the value test.
-/
theorem Exp.rename_is_val {e : Exp n}
  (h : e.is_val) :
  (e.rename f).is_val := by
  induction e <;> try (solve | cases h | rfl)
  simp [Exp.rename]
  simp [Exp.is_val]
  right
  simp [Exp.is_num_val]
  simp [Exp.is_val] at h
  cases h
  case inl h => cases h
  case inr h =>
    simp [Exp.is_num_val] at h
    apply Exp.rename_is_numval h

/-!
A store mapping variables to closed values.
The type parameter indicates the number of variables in scope.
-/
inductive Store : Nat -> Type where
| nil : Store 0
| cons : (e : Exp 0) -> (hv : e.IsVal) -> Store n -> Store (n + 1)

/-!
Look up the value associated with a variable in a store.
-/
def Store.lookup : Store n -> Var n -> Exp 0
| .cons v _ s, .here => v
| .cons _ _ s, .there i => s.lookup i

/-!
All values in a store is a value.
-/
theorem Store.lookup_is_val {s : Store n} :
  (s.lookup x).IsVal := by
  induction x
  case here => cases s; aesop
  case there ih =>
    cases s; simp [Store.lookup]
    exact ih

/-!
Predicate indicating that an expression is a lambda abstraction.
-/
inductive Exp.IsAbsVal : Exp n -> Prop where
| abs : Exp.IsAbsVal (.abs T e)

/-!
Every lambda abstraction is a value.
-/
theorem abs_val_is_val
  (hv : Exp.IsAbsVal v) :
  v.IsVal := by
  cases hv
  grind [Exp.IsVal]

end Stlc
