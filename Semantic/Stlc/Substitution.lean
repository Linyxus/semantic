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
  (hv : e.IsNumVal) :
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

theorem Subst.liftVar_there_eq {s : Subst n1 n2} {x : Var n1} :
  (s.liftVar).exp (.there x) = (s.exp x).rename Rename.succVar := by
  rfl

theorem Exp.var_weaken_subst_comm {x : Var (n1 + k)} {s : Subst n1 n2} :
  ((var x).subst (s.lift k)).rename (Rename.succVar.lift k) =
  ((var x).rename (Rename.succVar.lift k)).subst (s.liftVar.lift k) := by
  induction k
  case zero => rfl
  case succ k ih =>
    cases x
    case here => rfl
    case there x =>
      have ih := ih (x:=x)
      simp [Exp.subst, Exp.rename]
      simp [Subst.lift, Rename.lift]
      conv => lhs; simp [Subst.liftVar]
      conv => rhs; simp [Rename.liftVar]
      simp [Subst.liftVar_there_eq]
      conv => lhs; simp [<-Exp.rename_succVar_comm]
      congr

theorem Exp.weaken_subst_comm {e : Exp (n1 + k)} {s : Subst n1 n2} :
  (e.subst (s.lift k)).rename (Rename.succVar.lift k) =
    (e.rename (Rename.succVar.lift k)).subst (s.liftVar.lift k) := by
  match e with
  | .var x => simp [Exp.var_weaken_subst_comm (x:=x) (s:=s)]
  | .abs T e =>
    have ih := Exp.weaken_subst_comm (k:=k+1) (e:=e) (s:=s)
    simp [Exp.subst, Exp.rename]
    exact ih
  | .app e1 e2 =>
    have ih1 := Exp.weaken_subst_comm (e:=e1) (s:=s)
    have ih2 := Exp.weaken_subst_comm (e:=e2) (s:=s)
    simp [Exp.subst, Exp.rename]
    simp [ih1, ih2]
  | .btrue => rfl
  | .bfalse => rfl
  | .nzero => rfl
  | .nsucc e =>
    have ih := Exp.weaken_subst_comm (e:=e) (s:=s)
    simp [Exp.subst, Exp.rename]
    simp [ih]
  | .pred e =>
    have ih := Exp.weaken_subst_comm (e:=e) (s:=s)
    simp [Exp.subst, Exp.rename]
    simp [ih]
  | .iszero e =>
    have ih := Exp.weaken_subst_comm (e:=e) (s:=s)
    simp [Exp.subst, Exp.rename]
    simp [ih]
  | .cond e1 e2 e3 =>
    have ih1 := Exp.weaken_subst_comm (e:=e1) (s:=s)
    have ih2 := Exp.weaken_subst_comm (e:=e2) (s:=s)
    have ih3 := Exp.weaken_subst_comm (e:=e3) (s:=s)
    simp [Exp.subst, Exp.rename]
    simp [ih1, ih2, ih3]

theorem Exp.weaken_subst_comm_base {e : Exp n1} {s : Subst n1 n2} :
  (e.subst s).rename (Rename.succVar) =
    (e.rename (Rename.succVar)).subst (s.liftVar) :=
  Exp.weaken_subst_comm (k:=0) (e:=e) (s:=s)

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
    simp [Exp.weaken_subst_comm_base]

theorem Exp.subst_comp {e : Exp n1} {s1 : Subst n1 n2} {s2 : Subst n2 n3} :
  (e.subst s1).subst s2 = e.subst (s1.comp s2) := by
  induction e generalizing n2 n3 <;> try grind [Exp.subst, Subst.comp]
  case var => rfl
  case abs ih =>
    simp [Exp.subst]
    convert ih
    simp [Subst.comp_liftVar]

def Rename.asSubst (f : Rename n1 n2) : Subst n1 n2 where
  exp := fun x => .var (f.var x)

theorem Rename.asSubst_liftVar {f : Rename n1 n2} :
  (Rename.asSubst f).liftVar = Rename.asSubst (f.liftVar) := by
  apply Subst.funext
  intro x
  cases x <;> rfl

theorem Exp.subst_asSubst {e : Exp n1} {f : Rename n1 n2} :
  e.subst (Rename.asSubst f) = e.rename f := by
  induction e generalizing n2 <;> try grind [Exp.subst, Exp.rename]
  case var => rfl
  case abs ih =>
    simp [Exp.subst]
    simp [Rename.asSubst_liftVar]
    aesop

theorem Subst.openVar_rename_comm {u : Exp n1} {f : Rename n1 n2} :
  (Subst.openVar u).comp f.asSubst =
    f.asSubst.liftVar.comp (Subst.openVar (u.rename f)) := by
  apply Subst.funext
  intro x
  cases x
  case here =>
    simp [Subst.comp, Subst.openVar]
    simp [Exp.subst_asSubst]
    rfl
  case there x =>
    simp [Subst.comp, Subst.openVar, Rename.asSubst_liftVar]
    simp [Exp.subst_asSubst]
    rfl

theorem Exp.openVar_rename_comm {e : Exp (n1 + 1)} {u : Exp n1} {f : Rename n1 n2} :
  (e.subst (Subst.openVar u)).rename f
    = (e.rename (f.liftVar)).subst (Subst.openVar (u.rename f)) := by
  simp [<-Exp.subst_asSubst]
  simp [Exp.subst_comp]
  simp [Exp.subst_asSubst]
  simp [Subst.openVar_rename_comm]
  simp [Rename.asSubst_liftVar]

theorem Subst.succVar_openVar_comp {u : Exp n} :
  Rename.succVar.asSubst.comp (Subst.openVar u) = Subst.id := by
  apply Subst.funext
  intro x; cases x <;> rfl

theorem Exp.openVar_succVar_comp {e : Exp n} {u : Exp n} :
  (e.rename Rename.succVar).subst (Subst.openVar u) = e := by
  simp [<-Exp.subst_asSubst]
  simp [Exp.subst_comp]
  simp [Subst.succVar_openVar_comp]
  simp [Exp.subst_id]
