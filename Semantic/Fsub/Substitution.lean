import Semantic.Fsub.Syntax

namespace Fsub

structure Subst (s1 s2 : Sig) where
  var : BVar s1 .var -> Var s2
  tvar : BVar s1 .tvar -> Ty s2

def Subst.lift (s : Subst s1 s2) : Subst (s1,,k) (s2,,k) where
  var := fun x => by
    cases x
    case here => exact .bound .here
    case there x => exact (s.var x).rename Rename.succ
  tvar := fun x => by
    cases x
    case here => exact .tvar .here
    case there x => exact (s.tvar x).rename Rename.succ

def Subst.liftMany (s : Subst s1 s2) (K : Sig) : Subst (s1 ++ K) (s2 ++ K) :=
  match K with
  | [] => s
  | k :: K => (s.liftMany K).lift (k:=k)

def Subst.id {s : Sig} : Subst s s where
  var := fun x => .bound x
  tvar := fun x => .tvar x

def Var.subst : Var s1 -> Subst s1 s2 -> Var s2
| .bound x, s => s.var x
| .free n, _ => .free n

def Ty.subst : Ty s1 -> Subst s1 s2 -> Ty s2
| .top, _ => .top
| .tvar x, s => s.tvar x
| .singleton x, s => .singleton (x.subst s)
| .arrow T1 T2, s => .arrow (T1.subst s) (T2.subst s.lift)
| .poly T1 T2, s => .poly (T1.subst s) (T2.subst s.lift)

def Exp.subst : Exp s1 -> Subst s1 s2 -> Exp s2
| .var x, s => .var (x.subst s)
| .abs T e, s => .abs (T.subst s) (e.subst s.lift)
| .tabs T e, s => .tabs (T.subst s) (e.subst s.lift)
| .app x y, s => .app (x.subst s) (y.subst s)
| .tapp x T, s => .tapp (x.subst s) (T.subst s)
| .letin e1 e2, s => .letin (e1.subst s) (e2.subst s.lift)

def Subst.openVar (x : Var s) : Subst (s,x) s where
  var := fun
    | .here => x
    | .there x0 => .bound x0
  tvar := fun
    | .there x0 => .tvar x0

def Subst.openTVar (U : Ty s) : Subst (s,X) s where
  var := fun
    | .there x => .bound x
  tvar := fun
    | .here => U
    | .there x => .tvar x

/-!
Function extensionality principle for substitutions.
-/
theorem Subst.funext {σ1 σ2 : Subst s1 s2}
  (hvar : ∀ x, σ1.var x = σ2.var x)
  (htvar : ∀ x, σ1.tvar x = σ2.tvar x) :
  σ1 = σ2 := by
  cases σ1; cases σ2
  aesop

/-!
Composition of substitutions.
-/
def Subst.comp (σ1 : Subst s1 s2) (σ2 : Subst s2 s3) : Subst s1 s3 where
  var := fun x => (σ1.var x).subst σ2
  tvar := fun x => (σ1.tvar x).subst σ2

/-!
Composition of substitutions commutes with lifting.
This is the key technical lemma that enables substitution composition proofs.
-/
theorem Subst.comp_lift {σ1 : Subst s1 s2} {σ2 : Subst s2 s3} {k : Kind} :
  (σ1.lift (k := k)).comp (σ2.lift (k := k)) = (σ1.comp σ2).lift (k := k) := by
  apply Subst.funext
  all_goals sorry

/-!
Substituting a composition of substitutions is the same as
substituting one after the other for a variable.
-/
theorem Var.subst_comp {x : Var s1} {σ1 : Subst s1 s2} {σ2 : Subst s2 s3} :
  (x.subst σ1).subst σ2 = x.subst (σ1.comp σ2) := by
  cases x with
  | bound x => rfl
  | free n => rfl

/-!
Substituting a composition of substitutions is the same as
substituting one after the other for a type.
-/
theorem Ty.subst_comp {T : Ty s1} {σ1 : Subst s1 s2} {σ2 : Subst s2 s3} :
  (T.subst σ1).subst σ2 = T.subst (σ1.comp σ2) := by
  induction T generalizing s2 s3 with
  | top => rfl
  | tvar x => rfl
  | singleton x => simp [Ty.subst, Var.subst_comp]
  | arrow T1 T2 ih1 ih2 =>
    simp [Ty.subst, ih1, ih2, Subst.comp_lift]
  | poly T1 T2 ih1 ih2 =>
    simp [Ty.subst, ih1, ih2, Subst.comp_lift]

/-!
Substituting a composition of substitutions is the same as
substituting one after the other for an expression.
-/
theorem Exp.subst_comp {e : Exp s1} {σ1 : Subst s1 s2} {σ2 : Subst s2 s3} :
  (e.subst σ1).subst σ2 = e.subst (σ1.comp σ2) := by
  induction e generalizing s2 s3 with
  | var x => simp [Exp.subst, Var.subst_comp]
  | abs T e ih_e =>
    simp [Exp.subst, Ty.subst_comp, ih_e, Subst.comp_lift]
  | tabs T e ih_e =>
    simp [Exp.subst, Ty.subst_comp, ih_e, Subst.comp_lift]
  | app x y => simp [Exp.subst, Var.subst_comp]
  | tapp x T => simp [Exp.subst, Var.subst_comp, Ty.subst_comp]
  | letin e1 e2 ih1 ih2 =>
    simp [Exp.subst, ih1, ih2, Subst.comp_lift]

end Fsub
