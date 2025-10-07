import Semantic.CC.Syntax

namespace CC

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

theorem Subst.lift_there_var_eq {σ : Subst s1 s2} {x : BVar s1 .var} :
  (σ.lift (k:=k)).var (.there x) = (σ.var x).rename Rename.succ := by
  rfl

theorem Subst.lift_there_tvar_eq {σ : Subst s1 s2} {X : BVar s1 .tvar} :
  (σ.lift (k:=k)).tvar (.there X) = (σ.tvar X).rename Rename.succ := by
  rfl

theorem Rename.lift_there_tvar_eq {f : Rename s1 s2} {x : BVar s1 .tvar} :
  (f.lift (k:=k)).var (.there x) = (f.var x).there := by
  rfl

theorem Rename.lift_there_var_eq {f : Rename s1 s2} {x : BVar s1 .var} :
  (f.lift (k:=k)).var (.there x) = (f.var x).there := by
  rfl

theorem TVar.weaken_subst_comm_liftMany {X : BVar (s1 ++ K) .tvar} {σ : Subst s1 s2} :
  ((σ.liftMany K).tvar X).rename ((Rename.succ (k:=k0)).liftMany K) =
  (σ.lift (k:=k0).liftMany K).tvar ((Rename.succ (k:=k0).liftMany K).var X) := by
  induction K with
  | nil =>
    simp [Subst.liftMany, Rename.liftMany]
    cases X with
    | here => simp [Subst.lift, Rename.succ]
    | there X => rfl
  | cons k K ih =>
    simp [Subst.liftMany, Rename.liftMany]
    cases X with
    | here => rfl
    | there X =>
      simp [Rename.lift_there_tvar_eq]
      simp [Subst.lift_there_tvar_eq]
      simp [Ty.weaken_rename_comm]
      grind

theorem Var.weaken_subst_comm_liftMany {x : Var (s1 ++ K)} {σ : Subst s1 s2} :
  (x.subst (σ.liftMany K)).rename ((Rename.succ (k:=k0)).liftMany K) =
  (x.rename (Rename.succ.liftMany K)).subst (σ.lift (k:=k0).liftMany K) := by
  induction K with
  | nil =>
    simp [Subst.liftMany, Rename.liftMany]
    cases x <;> rfl
  | cons k K ih =>
    simp [Subst.liftMany, Rename.liftMany]
    cases x with
    | bound x =>
      cases x with
      | here => rfl
      | there x =>
        conv => lhs; simp [Var.subst]
        conv => rhs; simp [Var.rename, Var.subst]
        have ih := ih (x:=.bound x)
        simp [Subst.lift_there_var_eq, Rename.lift_there_var_eq]
        simp [Var.weaken_rename_comm]
        congr
    | free n => simp [Var.subst, Var.rename]

theorem Ty.weaken_subst_comm {T : Ty (s1 ++ K)} {σ : Subst s1 s2} :
  (T.subst (σ.liftMany K)).rename ((Rename.succ (k:=k0)).liftMany K) =
    (T.rename (Rename.succ.liftMany K)).subst (σ.lift.liftMany K) := by
  match T with
  | .top => rfl
  | .tvar X => simp [Ty.subst, Ty.rename, TVar.weaken_subst_comm_liftMany]
  | .singleton x => simp [Ty.subst, Ty.rename, Var.weaken_subst_comm_liftMany]
  | .arrow T1 T2 =>
    have ih1 := Ty.weaken_subst_comm (T:=T1) (σ:=σ) (K:=K) (k0:=k0)
    have ih2 := Ty.weaken_subst_comm (T:=T2) (σ:=σ) (K:=K,x) (k0:=k0)
    simp [Ty.subst, Ty.rename, ih1]
    exact ih2
  | .poly T1 T2 =>
    have ih1 := Ty.weaken_subst_comm (T:=T1) (σ:=σ) (K:=K) (k0:=k0)
    have ih2 := Ty.weaken_subst_comm (T:=T2) (σ:=σ) (K:=K,X) (k0:=k0)
    simp [Ty.subst, Ty.rename, ih1]
    exact ih2

theorem Ty.weaken_subst_comm_base {T : Ty s1} {σ : Subst s1 s2} :
  (T.subst σ).rename (Rename.succ (k:=k)) = (T.rename Rename.succ).subst (σ.lift (k:=k)) :=
  Ty.weaken_subst_comm (K:=[])

theorem Var.weaken_subst_comm_base {x : Var s1} {σ : Subst s1 s2} :
  (x.subst σ).rename (Rename.succ (k:=k)) = (x.rename Rename.succ).subst (σ.lift) := by
  cases x with
  | bound x => rfl
  | free n => rfl

/-!
Composition of substitutions commutes with lifting.
This is the key technical lemma that enables substitution composition proofs.
-/
theorem Subst.comp_lift {σ1 : Subst s1 s2} {σ2 : Subst s2 s3} {k : Kind} :
  (σ1.lift (k := k)).comp (σ2.lift (k := k)) = (σ1.comp σ2).lift (k := k) := by
  apply Subst.funext
  · intro x
    cases x with
    | here => rfl
    | there x0 =>
      conv =>
        lhs; simp [Subst.comp, Subst.lift_there_var_eq]
      simp only [Subst.lift_there_var_eq]
      simp only [Var.weaken_subst_comm_base, Subst.comp]
  · intro X
    cases X with
    | here => rfl
    | there x0 =>
      conv =>
        lhs; simp only [Subst.comp, Subst.lift_there_tvar_eq]
      simp only [Subst.lift_there_tvar_eq]
      simp only [Ty.weaken_subst_comm_base, Subst.comp]

/-!
Composition of substitutions commutes with lifting many levels.
-/
theorem Subst.comp_liftMany {σ1 : Subst s1 s2} {σ2 : Subst s2 s3} {K : Sig} :
  (σ1.liftMany K).comp (σ2.liftMany K) = (σ1.comp σ2).liftMany K := by
  induction K with
  | nil => rfl
  | cons k K ih =>
    simp [Subst.liftMany]
    rw [Subst.comp_lift, ih]

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

def Subst.rename_levels (s : Subst s1 s2) (f : Nat -> Nat) : Subst s1 s2 where
  var := fun x => (s.var x).rename_level f
  tvar := fun X => (s.tvar X).rename_levels f

theorem Var.subst_rename_levels {x : Var s1} {σ : Subst s1 s2} {f : Nat -> Nat} :
  (x.subst σ).rename_level f = (x.rename_level f).subst (σ.rename_levels f) := by
  cases x with
  | bound x => rfl
  | free n => rfl

/-- Lifting a substitution commutes with level renaming. -/
theorem Subst.lift_rename_levels {σ : Subst s1 s2} {f : Nat -> Nat} :
  (σ.lift (k:=k)).rename_levels f = (σ.rename_levels f).lift (k:=k) := by
  apply Subst.funext
  case hvar =>
    intro x
    cases x with
    | here => rfl
    | there x =>
      simp only [Subst.lift, Subst.rename_levels]
      exact Var.rename_rename_levels
  case htvar =>
    intro X
    cases X with
    | here => rfl
    | there X =>
      simp only [Subst.lift, Subst.rename_levels]
      exact Ty.rename_rename_levels

/-- Type substitution commutes with level renaming. -/
theorem Ty.subst_rename_levels {T : Ty s1} {σ : Subst s1 s2} {f : Nat -> Nat} :
  (T.subst σ).rename_levels f = (T.rename_levels f).subst (σ.rename_levels f) := by
  induction T generalizing s2 with
  | top => rfl
  | tvar X => rfl
  | singleton x =>
    simp [Ty.subst, Ty.rename_levels]
    exact Var.subst_rename_levels
  | arrow T1 T2 ih1 ih2 =>
    simp [Ty.subst, Ty.rename_levels]
    constructor
    · exact ih1
    · rw [ih2, Subst.lift_rename_levels]
  | poly T1 T2 ih1 ih2 =>
    simp [Ty.subst, Ty.rename_levels]
    constructor
    · exact ih1
    · rw [ih2, Subst.lift_rename_levels]

/-- Expression substitution commutes with level renaming. -/
theorem Exp.subst_rename_levels {e : Exp s1} {σ : Subst s1 s2} {f : Nat -> Nat} :
  (e.subst σ).rename_levels f = (e.rename_levels f).subst (σ.rename_levels f) := by
  induction e generalizing s2 with
  | var x =>
    simp [Exp.subst, Exp.rename_levels]
    exact Var.subst_rename_levels
  | abs T e ih =>
    simp [Exp.subst, Exp.rename_levels]
    constructor
    · exact Ty.subst_rename_levels
    · rw [ih, Subst.lift_rename_levels]
  | tabs T e ih =>
    simp [Exp.subst, Exp.rename_levels]
    constructor
    · exact Ty.subst_rename_levels
    · rw [ih, Subst.lift_rename_levels]
  | app x y =>
    simp [Exp.subst, Exp.rename_levels]
    constructor
    · exact Var.subst_rename_levels
    · exact Var.subst_rename_levels
  | tapp x T =>
    simp [Exp.subst, Exp.rename_levels]
    constructor
    · exact Var.subst_rename_levels
    · exact Ty.subst_rename_levels
  | letin e1 e2 ih1 ih2 =>
    simp [Exp.subst, Exp.rename_levels]
    constructor
    · exact ih1
    · rw [ih2, Subst.lift_rename_levels]

theorem Subst.openVar_rename_levels {x : Var s} :
  (Subst.openVar x).rename_levels f =
    Subst.openVar (x.rename_level f) := by
  apply Subst.funext
  case hvar =>
    intro x
    cases x <;> rfl
  case htvar =>
    intro X
    cases X; rfl

end CC
