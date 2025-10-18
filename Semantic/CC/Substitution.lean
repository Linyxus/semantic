import Semantic.CC.Syntax

namespace CC

structure Subst (s1 s2 : Sig) where
  var : BVar s1 .var -> Var .var s2
  tvar : BVar s1 .tvar -> Ty .shape s2
  cvar : BVar s1 .cvar -> CaptureSet s2

def Subst.lift (s : Subst s1 s2) : Subst (s1,,k) (s2,,k) where
  var := fun x => by
    cases x
    case here => exact .bound .here
    case there x => exact (s.var x).rename Rename.succ
  tvar := fun x => by
    cases x
    case here => exact .tvar .here
    case there x => exact (s.tvar x).rename Rename.succ
  cvar := fun x => by
    cases x
    case here => exact .cvar (.bound .here)
    case there x => exact (s.cvar x).rename Rename.succ

def Subst.liftMany (s : Subst s1 s2) (K : Sig) : Subst (s1 ++ K) (s2 ++ K) :=
  match K with
  | [] => s
  | k :: K => (s.liftMany K).lift (k:=k)

def Subst.id {s : Sig} : Subst s s where
  var := fun x => .bound x
  tvar := fun x => .tvar x
  cvar := fun x => .cvar (.bound x)

def Var.subst : Var .var s1 -> Subst s1 s2 -> Var .var s2
| .bound x, s => s.var x
| .free n, _ => .free n

def CaptureSet.subst : CaptureSet s1 -> Subst s1 s2 -> CaptureSet s2
| .empty, _ => .empty
| .union cs1 cs2, σ => .union (cs1.subst σ) (cs2.subst σ)
| .var x, σ => .var (x.subst σ)
| .cvar x, σ => match x with
  | .bound x => σ.cvar x
  | .free n => .cvar (.free n)

def CaptureBound.subst : CaptureBound s1 -> Subst s1 s2 -> CaptureBound s2
| .unbound, _ => .unbound
| .bound cs, σ => .bound (cs.subst σ)

def Ty.subst : Ty sort s1 -> Subst s1 s2 -> Ty sort s2
| .top, _ => .top
| .tvar x, s => s.tvar x
| .arrow T1 T2, s => .arrow (T1.subst s) (T2.subst s.lift)
| .poly T1 T2, s => .poly (T1.subst s) (T2.subst s.lift)
| .cpoly cb T, s => .cpoly (cb.subst s) (T.subst s.lift)
| .capt cs T, s => .capt (cs.subst s) (T.subst s)
| .exi T, s => .exi (T.subst s.lift)
| .typ T, s => .typ (T.subst s)

def Exp.subst : Exp s1 -> Subst s1 s2 -> Exp s2
| .var x, s => .var (x.subst s)
| .abs T e, s => .abs (T.subst s) (e.subst s.lift)
| .tabs T e, s => .tabs (T.subst s) (e.subst s.lift)
| .cabs cb e, s => .cabs (cb.subst s) (e.subst s.lift)
| .pack cs x, s => .pack (cs.subst s) (x.subst s)
| .app x y, s => .app (x.subst s) (y.subst s)
| .tapp x T, s => .tapp (x.subst s) (T.subst s)
| .capp x cs, s => .capp (x.subst s) (cs.subst s)
| .letin e1 e2, s => .letin (e1.subst s) (e2.subst s.lift)
| .unpack e1 e2, s => .unpack (e1.subst s) (e2.subst s.lift.lift)

def Subst.openVar (x : Var .var s) : Subst (s,x) s where
  var := fun
    | .here => x
    | .there x0 => .bound x0
  tvar := fun
    | .there x0 => .tvar x0
  cvar := fun
    | .there x0 => .cvar (.bound x0)

def Subst.openTVar (U : Ty .shape s) : Subst (s,X) s where
  var := fun
    | .there x => .bound x
  tvar := fun
    | .here => U
    | .there x => .tvar x
  cvar := fun
    | .there x => .cvar (.bound x)

/-!
Function extensionality principle for substitutions.
-/
theorem Subst.funext {σ1 σ2 : Subst s1 s2}
  (hvar : ∀ x, σ1.var x = σ2.var x)
  (htvar : ∀ x, σ1.tvar x = σ2.tvar x)
  (hcvar : ∀ x, σ1.cvar x = σ2.cvar x) :
  σ1 = σ2 := by
  cases σ1; cases σ2
  simp only [Subst.mk.injEq]
  constructor
  · funext x; exact hvar x
  constructor
  · funext x; exact htvar x
  · funext x; exact hcvar x

/-!
Composition of substitutions.
-/
def Subst.comp (σ1 : Subst s1 s2) (σ2 : Subst s2 s3) : Subst s1 s3 where
  var := fun x => (σ1.var x).subst σ2
  tvar := fun x => (σ1.tvar x).subst σ2
  cvar := fun x => (σ1.cvar x).subst σ2

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

theorem Subst.lift_there_cvar_eq {σ : Subst s1 s2} {C : BVar s1 .cvar} :
  (σ.lift (k:=k)).cvar (.there C) = (σ.cvar C).rename Rename.succ := by
  rfl

theorem Rename.lift_there_cvar_eq {f : Rename s1 s2} {C : BVar s1 .cvar} :
  (f.lift (k:=k)).var (.there C) = (f.var C).there := by
  rfl

theorem CaptureSet.weaken_rename_comm {cs : CaptureSet s1} {f : Rename s1 s2} :
  (cs.rename Rename.succ).rename (f.lift (k:=k0)) = (cs.rename f).rename (Rename.succ) := by
  simp [CaptureSet.rename_comp, Rename.succ_lift_comm]

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

theorem Var.weaken_subst_comm_liftMany {x : Var .var (s1 ++ K)} {σ : Subst s1 s2} :
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

theorem CVar.weaken_subst_comm_liftMany {C : BVar (s1 ++ K) .cvar} {σ : Subst s1 s2} :
  ((σ.liftMany K).cvar C).rename ((Rename.succ (k:=k0)).liftMany K) =
  (σ.lift (k:=k0).liftMany K).cvar ((Rename.succ (k:=k0).liftMany K).var C) := by
  induction K with
  | nil =>
    simp [Subst.liftMany, Rename.liftMany]
    cases C with
    | here => simp [Subst.lift, Rename.succ]
    | there C => rfl
  | cons k K ih =>
    simp [Subst.liftMany, Rename.liftMany]
    cases C with
    | here => rfl
    | there C =>
      simp [Rename.lift_there_cvar_eq]
      simp [Subst.lift_there_cvar_eq]
      simp [CaptureSet.weaken_rename_comm]
      grind

theorem CaptureSet.weaken_subst_comm_liftMany {cs : CaptureSet (s1 ++ K)} {σ : Subst s1 s2} :
  (cs.subst (σ.liftMany K)).rename ((Rename.succ (k:=k0)).liftMany K) =
  (cs.rename (Rename.succ.liftMany K)).subst (σ.lift (k:=k0).liftMany K) := by
  induction cs with
  | empty => rfl
  | union cs1 cs2 ih1 ih2 =>
    simp [CaptureSet.subst, CaptureSet.rename, ih1, ih2]
  | var x =>
    simp [CaptureSet.subst, CaptureSet.rename]
    exact Var.weaken_subst_comm_liftMany
  | cvar x =>
    cases x with
    | bound C =>
      simp [CaptureSet.subst, CaptureSet.rename, Var.rename]
      exact CVar.weaken_subst_comm_liftMany
    | free n =>
      simp [CaptureSet.subst, CaptureSet.rename, Var.rename]

theorem CaptureBound.weaken_subst_comm_liftMany {cb : CaptureBound (s1 ++ K)} {σ : Subst s1 s2} :
  (cb.subst (σ.liftMany K)).rename ((Rename.succ (k:=k0)).liftMany K) =
  (cb.rename (Rename.succ.liftMany K)).subst (σ.lift (k:=k0).liftMany K) := by
  cases cb with
  | unbound => rfl
  | bound cs =>
    simp [CaptureBound.subst, CaptureBound.rename, CaptureSet.weaken_subst_comm_liftMany]

theorem Ty.weaken_subst_comm {T : Ty sort (s1 ++ K)} {σ : Subst s1 s2} :
  (T.subst (σ.liftMany K)).rename ((Rename.succ (k:=k0)).liftMany K) =
    (T.rename (Rename.succ.liftMany K)).subst (σ.lift.liftMany K) := by
  match T with
  | .top => rfl
  | .tvar X => simp [Ty.subst, Ty.rename, TVar.weaken_subst_comm_liftMany]
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
  | .cpoly cb T =>
    have ihCB := CaptureBound.weaken_subst_comm_liftMany (cb:=cb) (σ:=σ) (K:=K) (k0:=k0)
    have ihT := Ty.weaken_subst_comm (T:=T) (σ:=σ) (K:=K,C) (k0:=k0)
    simp [Ty.subst, Ty.rename, ihCB]
    exact ihT
  | .capt cs T =>
    have ihT := Ty.weaken_subst_comm (T:=T) (σ:=σ) (K:=K) (k0:=k0)
    have ihCS := CaptureSet.weaken_subst_comm_liftMany (cs:=cs) (σ:=σ) (K:=K) (k0:=k0)
    simp [Ty.subst, Ty.rename, ihT, ihCS]
  | .exi T =>
    have ih := Ty.weaken_subst_comm (T:=T) (σ:=σ) (K:=K,C) (k0:=k0)
    simp [Ty.subst, Ty.rename]
    exact ih
  | .typ T =>
    have ih := Ty.weaken_subst_comm (T:=T) (σ:=σ) (K:=K) (k0:=k0)
    simp [Ty.subst, Ty.rename, ih]

theorem Ty.weaken_subst_comm_base {T : Ty sort s1} {σ : Subst s1 s2} :
  (T.subst σ).rename (Rename.succ (k:=k)) = (T.rename Rename.succ).subst (σ.lift (k:=k)) :=
  Ty.weaken_subst_comm (K:=[])

theorem Var.weaken_subst_comm_base {x : Var .var s1} {σ : Subst s1 s2} :
  (x.subst σ).rename (Rename.succ (k:=k)) = (x.rename Rename.succ).subst (σ.lift) := by
  cases x with
  | bound x => rfl
  | free n => rfl

theorem CVar.weaken_subst_comm_base {C : BVar s1 .cvar} {σ : Subst s1 s2} :
  (σ.cvar C).rename (Rename.succ (k:=k)) =
  (σ.lift (k:=k)).cvar ((Rename.succ (k:=k)).var C) := by
  cases C with
  | here => simp [Subst.lift, Rename.succ]
  | there C => rfl

theorem CaptureSet.weaken_subst_comm_base {cs : CaptureSet s1} {σ : Subst s1 s2} :
  (cs.subst σ).rename (Rename.succ (k:=k)) = (cs.rename Rename.succ).subst (σ.lift) := by
  induction cs with
  | empty => rfl
  | union cs1 cs2 ih1 ih2 =>
    simp [CaptureSet.subst, CaptureSet.rename, ih1, ih2]
  | var x =>
    simp [CaptureSet.subst, CaptureSet.rename]
    exact Var.weaken_subst_comm_base
  | cvar x =>
    cases x with
    | bound x =>
      simp [CaptureSet.subst, CaptureSet.rename, Var.rename, Subst.lift]
      exact CVar.weaken_subst_comm_base
    | free n =>
      simp [CaptureSet.subst, CaptureSet.rename, Var.rename]

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
  · intro C
    cases C with
    | here => rfl
    | there C0 =>
      simp [Subst.comp, Subst.lift]
      exact CaptureSet.weaken_subst_comm_base.symm

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
theorem Var.subst_comp {x : Var .var s1} {σ1 : Subst s1 s2} {σ2 : Subst s2 s3} :
  (x.subst σ1).subst σ2 = x.subst (σ1.comp σ2) := by
  cases x with
  | bound x => rfl
  | free n => rfl

theorem CaptureSet.subst_comp {cs : CaptureSet s1} {σ1 : Subst s1 s2} {σ2 : Subst s2 s3} :
  (cs.subst σ1).subst σ2 = cs.subst (σ1.comp σ2) := by
  induction cs with
  | empty => rfl
  | union cs1 cs2 ih1 ih2 =>
    simp [CaptureSet.subst, ih1, ih2]
  | var x =>
    simp [CaptureSet.subst]
    exact Var.subst_comp
  | cvar x =>
    cases x with
    | bound x =>
      simp [CaptureSet.subst, Subst.comp]
    | free n =>
      simp [CaptureSet.subst]

theorem CaptureBound.subst_comp {cb : CaptureBound s1} {σ1 : Subst s1 s2} {σ2 : Subst s2 s3} :
  (cb.subst σ1).subst σ2 = cb.subst (σ1.comp σ2) := by
  cases cb with
  | unbound => rfl
  | bound cs => simp [CaptureBound.subst, CaptureSet.subst_comp]

/-!
Substituting a composition of substitutions is the same as
substituting one after the other for a type.
-/
theorem Ty.subst_comp {T : Ty sort s1} {σ1 : Subst s1 s2} {σ2 : Subst s2 s3} :
  (T.subst σ1).subst σ2 = T.subst (σ1.comp σ2) := by
  induction T generalizing s2 s3 with
  | top => rfl
  | tvar x => rfl
  | arrow T1 T2 ih1 ih2 =>
    simp [Ty.subst, ih1, ih2, Subst.comp_lift]
  | poly T1 T2 ih1 ih2 =>
    simp [Ty.subst, ih1, ih2, Subst.comp_lift]
  | cpoly cb T ih =>
    simp [Ty.subst, ih, CaptureBound.subst_comp, Subst.comp_lift]
  | capt cs T ih =>
    simp [Ty.subst, ih, CaptureSet.subst_comp]
  | exi T ih =>
    simp [Ty.subst, ih, Subst.comp_lift]
  | typ T ih =>
    simp [Ty.subst, ih]

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
  | cabs cb e ih_e =>
    simp [Exp.subst, CaptureBound.subst_comp, ih_e, Subst.comp_lift]
  | pack cs x =>
    simp [Exp.subst, CaptureSet.subst_comp, Var.subst_comp]
  | app x y => simp [Exp.subst, Var.subst_comp]
  | tapp x T => simp [Exp.subst, Var.subst_comp, Ty.subst_comp]
  | capp x cs =>
    simp [Exp.subst, Var.subst_comp, CaptureSet.subst_comp]
  | letin e1 e2 ih1 ih2 =>
    simp [Exp.subst, ih1, ih2, Subst.comp_lift]
  | unpack e1 e2 ih1 ih2 =>
    simp [Exp.subst, ih1, ih2, Subst.comp_lift]

end CC
