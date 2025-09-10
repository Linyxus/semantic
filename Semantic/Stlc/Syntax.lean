import Aesop
import Semantic.Stlc.Debruijn
/-!
Syntax definitions for the simply typed lambda calculus.
-/

inductive Ty : Type where
| bool : Ty
| nat : Ty
| arrow : Ty -> Ty -> Ty

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

@[aesop safe [constructors]]
inductive Exp.IsNumVal : Exp n -> Prop where
| nzero : Exp.IsNumVal .nzero
| nsucc : Exp.IsNumVal e -> Exp.IsNumVal (.nsucc e)

@[aesop safe [constructors]]
inductive Exp.IsBoolVal : Exp n -> Prop where
| btrue : Exp.IsBoolVal .btrue
| bfalse : Exp.IsBoolVal .bfalse

@[aesop unsafe [constructors 95%]]
inductive Exp.IsVal : Exp n -> Prop where
| abs : Exp.IsVal (.abs T e)
| bool : Exp.IsBoolVal e -> Exp.IsVal e
| num : Exp.IsNumVal e -> Exp.IsVal e

structure Val (n : Nat) where
  unwrap : Exp n
  isVal : unwrap.IsVal

theorem Exp.rename_IsNumVal {e : Exp s}
  (hv : e.IsNumVal) :
  (e.rename f).IsNumVal := by
  induction hv with
  | nzero => exact IsNumVal.nzero
  | nsucc _ ih => exact IsNumVal.nsucc ih

theorem Exp.rename_IsBoolVal {e : Exp s}
  (hv : e.IsBoolVal) :
  (e.rename f).IsBoolVal := by
  cases hv with
  | btrue => exact IsBoolVal.btrue
  | bfalse => exact IsBoolVal.bfalse

theorem Exp.rename_IsVal {e : Exp s}
  (hv : e.IsVal) :
  (e.rename f).IsVal := by
  cases hv with
  | abs => exact IsVal.abs
  | bool hb => exact IsVal.bool (rename_IsBoolVal hb)
  | num hn => exact IsVal.num (rename_IsNumVal hn)

def Val.rename (v : Val n1) (f : Rename n1 n2) : Val n2 where
  unwrap := v.unwrap.rename f
  isVal := Exp.rename_IsVal v.isVal

def Exp.is_bool_val : Exp n -> Bool
| .btrue => true
| .bfalse => true
| _ => false

def Exp.is_num_val : Exp n -> Bool
| .nzero => true
| .nsucc e => e.is_num_val
| _ => false

def Exp.is_val : Exp n -> Bool
| .abs _ _ => true
| e => e.is_bool_val || e.is_num_val
