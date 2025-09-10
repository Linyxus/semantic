import Semantic.Stlc.Syntax

structure Subst (n1 n2 : Nat) where
  exp : Var n1 -> Exp n2

def Subst.liftVar (s : Subst n1 n2) : Subst (n1+1) (n2+1) where
  exp := fun
    | .here => .var .here
    | .there x => (s.exp x).rename Rename.succVar

def Subst.id (n : Nat) : Subst n n where
  exp := fun x => .var x

def Subst.openVar (e : Exp n) : Subst (n+1) n where
  exp := fun
    | .here => e
    | .there x => .var x

def Exp.subst : Exp n1 -> Subst n1 n2 -> Exp n2
| .var x, s => s.exp x
| .abs T e, s => .abs T (e.subst s.liftVar)
| .app e1 e2, s => .app (e1.subst s) (e2.subst s)
| .btrue, _ => .btrue
| .bfalse, _ => .bfalse
| .nzero, _ => .nzero
| .nsucc e, s => .nsucc (e.subst s)
| .pred e, s => .pred (e.subst s)
| .iszero e, s => .iszero (e.subst s)
| .cond e1 e2 e3, s => .cond (e1.subst s) (e2.subst s) (e3.subst s)

theorem Exp.subst_IsNumVal {e : Exp n1} {s : Subst n1 n2}
  (hv : e.IsNumVal)  :
  (e.subst s).IsNumVal := by
  induction hv with
  | nzero => exact IsNumVal.nzero
  | nsucc _ ih => exact IsNumVal.nsucc ih

theorem Exp.subst_IsBoolVal {e : Exp n1} {s : Subst n1 n2}
  (hv : e.IsBoolVal) :
  (e.subst s).IsBoolVal := by
  cases hv with
  | btrue => exact IsBoolVal.btrue
  | bfalse => exact IsBoolVal.bfalse

theorem Exp.subst_IsVal {e : Exp n1} {s : Subst n1 n2}
  (hv : e.IsVal) :
  (e.subst s).IsVal := by
  cases hv with
  | abs => exact IsVal.abs
  | bool h => exact IsVal.bool (Exp.subst_IsBoolVal h)
  | num h => exact IsVal.num (Exp.subst_IsNumVal h)

def Val.subst {n1 n2 : Nat} (v : Val n1) (s : Subst n1 n2) : Val n2 where
  unwrap := v.unwrap.subst s
  isVal := Exp.subst_IsVal v.isVal
