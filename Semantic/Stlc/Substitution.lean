import Semantic.Stlc.Syntax
import Mathlib.Tactic

structure Subst (n1 n2 : Nat) where
  exp : Var n1 -> Exp n2

def Subst.liftVar (s : Subst n1 n2) : Subst (n1+1) (n2+1) where
  exp := fun
    | .here => .var .here
    | .there x => (s.exp x).rename Rename.succVar

def Subst.lift (s : Subst n1 n2) (k : Nat) : Subst (n1+k) (n2+k) :=
  match k with
  | 0 => s
  | k+1 => (s.lift k).liftVar

def Subst.id : Subst n n where
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

theorem Subst.funext {s1 s2 : Subst n1 n2}
  (exp : ∀ x, s1.exp x = s2.exp x) :
  s1 = s2 := by
  cases s1; cases s2
  aesop

theorem Subst.id_liftVar {n : Nat} :
  (Subst.id (n:=n)).liftVar = Subst.id := by
  apply Subst.funext
  intro x
  cases x <;> rfl

theorem Exp.subst_id {e : Exp n} :
  e.subst Subst.id = e := by
  induction e <;> try grind [Exp.subst, Subst.id]
  case var => rfl
  case abs ih => simpa [Exp.subst, Subst.id_liftVar]

def Subst.comp (s1 : Subst n1 n2) (s2 : Subst n2 n3) : Subst n1 n3 where
  exp := fun x => (s1.exp x).subst s2

theorem Exp.weaken_subst_comm {e : Exp (n1 + k)} {s : Subst n1 n2} :
  (e.subst (s.lift k)).rename (Rename.succVar.lift k) =
    (e.rename (Rename.succVar.lift k)).subst (s.liftVar.lift k) := by
  sorry

theorem Subst.comp_liftVar {s1 : Subst n1 n2} {s2 : Subst n2 n3} :
  (s1.liftVar).comp (s2.liftVar) = (s1.comp s2).liftVar := by
  apply Subst.funext
  intro x
  cases x
  case here => rfl
  case there x =>
    conv => rhs; simp [Subst.liftVar, Subst.comp]
    conv =>
      lhs
      simp [Subst.comp]
      arg 1
      simp [Subst.liftVar]
    sorry

theorem Exp.subst_comp {e : Exp n1} {s1 : Subst n1 n2} {s2 : Subst n2 n3} :
  (e.subst s1).subst s2 = e.subst (s1.comp s2) := by
  induction e generalizing n2 n3 <;> try grind [Exp.subst, Subst.comp]
  case var => rfl
  case abs ih =>
    simp [Exp.subst]
    convert ih
    sorry
