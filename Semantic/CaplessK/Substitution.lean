import Semantic.CaplessK.Syntax

namespace CaplessK

/-- A substitution maps bound variables of each kind to terms of the appropriate sort. -/
structure Subst (s1 s2 : Sig) where
  var : BVar s1 .var -> Var .var s2
  tvar : BVar s1 .tvar -> Ty .shape s2
  cvar : BVar s1 .cvar -> CapKind -> CaptureSet s2

/-- Lifts a substitution under a binder. The newly bound variable maps to itself. -/
def Subst.lift (s : Subst s1 s2) : Subst (s1,,k) (s2,,k) where
  var := fun x => by
    cases x
    case here => exact .bound .here
    case there x => exact (s.var x).rename Rename.succ
  tvar := fun x => by
    cases x
    case here => exact .tvar .here
    case there x => exact (s.tvar x).rename Rename.succ
  cvar := fun x K => by
    cases x
    case here => exact .cvar .here K
    case there x => exact (s.cvar x K).rename Rename.succ

/-- Lifts a substitution under multiple binders. -/
def Subst.liftMany (s : Subst s1 s2) (K : Sig) : Subst (s1 ++ K) (s2 ++ K) :=
  match K with
  | [] => s
  | k :: K => (s.liftMany K).lift (k:=k)

/-- The identity substitution. -/
def Subst.id {s : Sig} : Subst s s where
  var := fun x => .bound x
  tvar := fun x => .tvar x
  cvar := fun x K => .cvar x K

/-- Applies a substitution to a variable. Free variables remain unchanged. -/
def Var.subst : Var .var s1 -> Subst s1 s2 -> Var .var s2
| .bound x, s => s.var x
| .free n, _ => .free n

/-- Applies a substitution to all bound variables in a capture set. -/
def CaptureSet.subst : CaptureSet s1 -> Subst s1 s2 -> CaptureSet s2
| .empty, _ => .empty
| .union cs1 cs2, σ => .union (cs1.subst σ) (cs2.subst σ)
| .var x K, σ => .var (x.subst σ) K
| .cvar x K, σ => σ.cvar x K

/-- Applies a substitution to a capture bound. -/
def CaptureBound.subst : CaptureBound s1 -> Subst s1 s2 -> CaptureBound s2
| .unbound k, _ => .unbound k
| .bound cs, σ => .bound (cs.subst σ)

/-- Applies a substitution to a type. -/
def Ty.subst : Ty sort s1 -> Subst s1 s2 -> Ty sort s2
| .top, _ => .top
| .tvar x, s => s.tvar x
| .arrow T1 T2, s => .arrow (T1.subst s) (T2.subst s.lift)
| .poly T1 T2, s => .poly (T1.subst s) (T2.subst s.lift)
| .cpoly cb T, s => .cpoly (cb.subst s) (T.subst s.lift)
| .unit, _ => .unit
| .cap, _ => .cap
| .bool, _ => .bool
| .cell, _ => .cell
| .label T, s => .label (T.subst s)
| .capt cs T, s => .capt (cs.subst s) (T.subst s)
| .exi T, s => .exi (T.subst s.lift)
| .typ T, s => .typ (T.subst s)

/-- Applies a substitution to an expression. -/
def Exp.subst : Exp s1 -> Subst s1 s2 -> Exp s2
| .var x, s => .var (x.subst s)
| .abs cs T e, s => .abs (cs.subst s) (T.subst s) (e.subst s.lift)
| .tabs cs T e, s => .tabs (cs.subst s) (T.subst s) (e.subst s.lift)
| .cabs cs cb e, s => .cabs (cs.subst s) (cb.subst s) (e.subst s.lift)
| .pack cs x, s => .pack (cs.subst s) (x.subst s)
| .app x y, s => .app (x.subst s) (y.subst s)
| .tapp x T, s => .tapp (x.subst s) (T.subst s)
| .capp x cs, s => .capp (x.subst s) (cs.subst s)
| .letin e1 e2, s => .letin (e1.subst s) (e2.subst s.lift)
| .unpack e1 e2, s => .unpack (e1.subst s) (e2.subst s.lift.lift)
| .unit, _ => .unit
| .btrue, _ => .btrue
| .bfalse, _ => .bfalse
| .read x, s => .read (x.subst s)
| .write x y, s => .write (x.subst s) (y.subst s)
| .cond x e2 e3, s => .cond (x.subst s) (e2.subst s) (e3.subst s)
| .boundary k T e, s => .boundary k (T.subst s) (e.subst s.lift.lift)

/-- Substitution that opens a variable binder by replacing the innermost bound variable with `x`. -/
def Subst.openVar (x : Var .var s) : Subst (s,x) s where
  var := fun
    | .here => x
    | .there x0 => .bound x0
  tvar := fun
    | .there x0 => .tvar x0
  cvar := fun
    | .there x0 => fun K => .cvar x0 K

/-- Opens a type variable binder, substituting `U` for the innermost bound. -/
def Subst.openTVar (U : Ty .shape s) : Subst (s,X) s where
  var := fun
    | .there x => .bound x
  tvar := fun
    | .here => U
    | .there x => .tvar x
  cvar := fun
    | .there x => fun K => .cvar x K

/-- Opens a capture variable binder, substituting `C` for the innermost bound. -/
def Subst.openCVar (C : CaptureSet s) : Subst (s,C) s where
  var := fun
    | .there x => .bound x
  tvar := fun
    | .there x => .tvar x
  cvar := fun
    | .here => fun K => C.proj K
    | .there x => fun K => .cvar x K

/-- Opens an existential package, substituting `C` and `x` for the two innermost binders. -/
def Subst.unpack (C : CaptureSet s) (x : Var .var s) : Subst (s,C,x) s where
  var := fun
    | .here => x
    | .there (.there x0) => .bound x0
  cvar := fun
    | .there .here => fun K => C.proj K
    | .there (.there c0) => fun K => .cvar c0 K
  tvar := fun
    | .there (.there X0) => .tvar X0

/-- Function extensionality for substitutions.
  Two substitutions are equal if they map all variables equally. -/
theorem Subst.funext {σ1 σ2 : Subst s1 s2}
  (hvar : ∀ x, σ1.var x = σ2.var x)
  (htvar : ∀ x, σ1.tvar x = σ2.tvar x)
  (hcvar : ∀ x K, σ1.cvar x K = σ2.cvar x K) :
  σ1 = σ2 := by
  cases σ1; cases σ2
  simp only [Subst.mk.injEq]
  constructor
  · funext x; exact hvar x
  constructor
  · funext x; exact htvar x
  · funext x K; exact hcvar x K

/-- Composition of substitutions. -/
def Subst.comp (σ1 : Subst s1 s2) (σ2 : Subst s2 s3) : Subst s1 s3 where
  var := fun x => (σ1.var x).subst σ2
  tvar := fun x => (σ1.tvar x).subst σ2
  cvar := fun x K => (σ1.cvar x K).subst σ2

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

theorem Subst.lift_there_cvar_eq {σ : Subst s1 s2} {C : BVar s1 .cvar} {K : CapKind} :
  (σ.lift (k:=k)).cvar (.there C) K = (σ.cvar C K).rename Rename.succ := by
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

theorem CVar.weaken_subst_comm_liftMany
    {C : BVar (s1 ++ K) .cvar} {σ : Subst s1 s2} {ck : CapKind} :
    ((σ.liftMany K).cvar C ck).rename ((Rename.succ (k:=k0)).liftMany K) =
    (σ.lift (k:=k0).liftMany K).cvar ((Rename.succ (k:=k0).liftMany K).var C) ck := by
  induction K with
  | nil =>
    simp [Subst.liftMany, Rename.liftMany]
    cases C with
    | here => simp [Subst.lift, Rename.succ]
    | there C => rfl
  | cons k K ih =>
    simp [Subst.liftMany, Rename.liftMany]
    cases C with
    | here => simp [Subst.lift, CaptureSet.rename, Rename.lift]
    | there C =>
      simp [Rename.lift_there_cvar_eq]
      simp [Subst.lift_there_cvar_eq]
      simp [CaptureSet.weaken_rename_comm]
      rw [ih]

theorem CaptureSet.weaken_subst_comm_liftMany {cs : CaptureSet (s1 ++ K)} {σ : Subst s1 s2} :
  (cs.subst (σ.liftMany K)).rename ((Rename.succ (k:=k0)).liftMany K) =
  (cs.rename (Rename.succ.liftMany K)).subst (σ.lift (k:=k0).liftMany K) := by
  induction cs with
  | empty => rfl
  | union cs1 cs2 ih1 ih2 =>
    simp [CaptureSet.subst, CaptureSet.rename, ih1, ih2]
  | var x ck =>
    simp [CaptureSet.subst, CaptureSet.rename]
    exact Var.weaken_subst_comm_liftMany
  | cvar C ck =>
    simp [CaptureSet.subst, CaptureSet.rename]
    exact CVar.weaken_subst_comm_liftMany

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
  | .unit => rfl
  | .cap => rfl
  | .bool => rfl
  | .cell => rfl
  | .label T =>
    have ih := Ty.weaken_subst_comm (T:=T) (σ:=σ) (K:=K) (k0:=k0)
    simp [Ty.subst, Ty.rename, ih]
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

theorem CVar.weaken_subst_comm_base {C : BVar s1 .cvar} {σ : Subst s1 s2} {ck : CapKind} :
  (σ.cvar C ck).rename (Rename.succ (k:=k)) =
  (σ.lift (k:=k)).cvar ((Rename.succ (k:=k)).var C) ck := by
  cases C with
  | here => simp [Subst.lift, Rename.succ]
  | there C => rfl

theorem CaptureSet.weaken_subst_comm_base {cs : CaptureSet s1} {σ : Subst s1 s2} :
  (cs.subst σ).rename (Rename.succ (k:=k)) = (cs.rename Rename.succ).subst (σ.lift) := by
  induction cs with
  | empty => rfl
  | union cs1 cs2 ih1 ih2 =>
    simp [CaptureSet.subst, CaptureSet.rename, ih1, ih2]
  | var x ck =>
    simp [CaptureSet.subst, CaptureSet.rename]
    exact Var.weaken_subst_comm_base
  | cvar C ck =>
    simp [CaptureSet.subst, CaptureSet.rename]
    exact CVar.weaken_subst_comm_base

/-- Composition of substitutions commutes with lifting. -/
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
  · intro C ck
    cases C with
    | here => simp [Subst.comp, Subst.lift, CaptureSet.subst]
    | there C0 =>
      simp [Subst.comp, Subst.lift]
      exact CaptureSet.weaken_subst_comm_base.symm

/-- Composition of substitutions commutes with lifting many levels. -/
theorem Subst.comp_liftMany {σ1 : Subst s1 s2} {σ2 : Subst s2 s3} {K : Sig} :
  (σ1.liftMany K).comp (σ2.liftMany K) = (σ1.comp σ2).liftMany K := by
  induction K with
  | nil => rfl
  | cons k K ih =>
    simp [Subst.liftMany]
    rw [Subst.comp_lift, ih]

/-- Substituting a composition of substitutions is the same as
  substituting one after the other. -/
theorem Var.subst_comp {x : Var .var s1} {σ1 : Subst s1 s2} {σ2 : Subst s2 s3} :
  (x.subst σ1).subst σ2 = x.subst (σ1.comp σ2) := by
  cases x with
  | bound x => rfl
  | free n => rfl

/-- Substitution on capture sets distributes over composition of substitutions. -/
theorem CaptureSet.subst_comp {cs : CaptureSet s1} {σ1 : Subst s1 s2} {σ2 : Subst s2 s3} :
  (cs.subst σ1).subst σ2 = cs.subst (σ1.comp σ2) := by
  induction cs with
  | empty => rfl
  | union cs1 cs2 ih1 ih2 =>
    simp [CaptureSet.subst, ih1, ih2]
  | var x =>
    simp [CaptureSet.subst]
    exact Var.subst_comp
  | cvar C =>
    simp [CaptureSet.subst, Subst.comp]

/-- Substitution on capture bounds distributes over composition of substitutions. -/
theorem CaptureBound.subst_comp {cb : CaptureBound s1} {σ1 : Subst s1 s2} {σ2 : Subst s2 s3} :
  (cb.subst σ1).subst σ2 = cb.subst (σ1.comp σ2) := by
  cases cb with
  | unbound => rfl
  | bound cs => simp [CaptureBound.subst, CaptureSet.subst_comp]

/-- Substitution on types distributes over composition of substitutions. -/
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
  | unit => rfl
  | cap => rfl
  | bool => rfl
  | cell => rfl
  | label T ih =>
    simp [Ty.subst, ih]
  | capt cs T ih =>
    simp [Ty.subst, ih, CaptureSet.subst_comp]
  | exi T ih =>
    simp [Ty.subst, ih, Subst.comp_lift]
  | typ T ih =>
    simp [Ty.subst, ih]

/-- Substitution on terms distributes over composition of substitutions. -/
theorem Exp.subst_comp {e : Exp s1} {σ1 : Subst s1 s2} {σ2 : Subst s2 s3} :
  (e.subst σ1).subst σ2 = e.subst (σ1.comp σ2) := by
  induction e generalizing s2 s3 with
  | var x => simp [Exp.subst, Var.subst_comp]
  | abs cs T e ih_e =>
    simp [Exp.subst, CaptureSet.subst_comp, Ty.subst_comp, ih_e, Subst.comp_lift]
  | tabs cs T e ih_e =>
    simp [Exp.subst, CaptureSet.subst_comp, Ty.subst_comp, ih_e, Subst.comp_lift]
  | cabs cs cb e ih_e =>
    simp [Exp.subst, CaptureSet.subst_comp, CaptureBound.subst_comp, ih_e, Subst.comp_lift]
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
  | unit => rfl
  | btrue => rfl
  | bfalse => rfl
  | read x => simp [Exp.subst, Var.subst_comp]
  | write x y => simp [Exp.subst, Var.subst_comp]
  | cond x e2 e3 ih2 ih3 =>
    simp [Exp.subst, Var.subst_comp, ih2, ih3]
  | boundary k T e ih_e =>
    simp [Exp.subst, Ty.subst_comp, ih_e, Subst.comp_lift]

/-- Substituting with the identity substitution leaves a variable unchanged. -/
theorem Var.subst_id {x : Var .var s} :
  x.subst Subst.id = x := by
  cases x with
  | bound x => rfl
  | free n => rfl

/-- Substituting with the identity substitution leaves a capture set unchanged. -/
theorem CaptureSet.subst_id {cs : CaptureSet s} :
  cs.subst Subst.id = cs := by
  induction cs with
  | empty => rfl
  | union cs1 cs2 ih1 ih2 =>
    simp [CaptureSet.subst, ih1, ih2]
  | var x =>
    simp [CaptureSet.subst, Var.subst_id]
  | cvar C =>
    simp [CaptureSet.subst, Subst.id]

/-- Substituting with the identity substitution leaves a capture bound unchanged. -/
theorem CaptureBound.subst_id {cb : CaptureBound s} :
  cb.subst Subst.id = cb := by
  cases cb with
  | unbound => rfl
  | bound cs => simp [CaptureBound.subst, CaptureSet.subst_id]

/-- Lifting the identity substitution yields the identity. -/
theorem Subst.lift_id :
  (Subst.id (s:=s)).lift (k:=k) = Subst.id := by
  apply Subst.funext
  · intro x
    cases x <;> rfl
  · intro X
    cases X <;> rfl
  · intro C ck
    cases C <;> rfl

/-- Substituting with the identity substitution leaves a type unchanged. -/
theorem Ty.subst_id {T : Ty sort s} :
  T.subst Subst.id = T := by
  induction T with
  | top => rfl
  | tvar x => simp [Ty.subst, Subst.id]
  | arrow T1 T2 ih1 ih2 =>
    simp [Ty.subst, ih1, ih2, Subst.lift_id]
  | poly T1 T2 ih1 ih2 =>
    simp [Ty.subst, ih1, ih2, Subst.lift_id]
  | cpoly cb T ih =>
    simp [Ty.subst, ih, Subst.lift_id, CaptureBound.subst_id]
  | unit => rfl
  | cap => rfl
  | bool => rfl
  | cell => rfl
  | label T ih =>
    simp [Ty.subst, ih]
  | capt cs T ih =>
    simp [Ty.subst, ih, CaptureSet.subst_id]
  | exi T ih =>
    simp [Ty.subst, ih, Subst.lift_id]
  | typ T ih =>
    simp [Ty.subst, ih]

/-- Substituting with the identity substitution leaves an expression unchanged. -/
theorem Exp.subst_id {e : Exp s} :
  e.subst Subst.id = e := by
  induction e with
  | var x =>
    simp [Exp.subst, Var.subst_id]
  | abs cs T e ih =>
    simp [Exp.subst, CaptureSet.subst_id, Ty.subst_id, ih, Subst.lift_id]
  | tabs cs T e ih =>
    simp [Exp.subst, CaptureSet.subst_id, Ty.subst_id, ih, Subst.lift_id]
  | cabs cs cb e ih =>
    simp [Exp.subst, CaptureSet.subst_id, CaptureBound.subst_id, ih, Subst.lift_id]
  | pack cs x =>
    simp [Exp.subst, CaptureSet.subst_id, Var.subst_id]
  | app x y =>
    simp [Exp.subst, Var.subst_id]
  | tapp x T =>
    simp [Exp.subst, Var.subst_id, Ty.subst_id]
  | capp x cs =>
    simp [Exp.subst, Var.subst_id, CaptureSet.subst_id]
  | letin e1 e2 ih1 ih2 =>
    simp [Exp.subst, ih1, ih2, Subst.lift_id]
  | unpack e1 e2 ih1 ih2 =>
    simp [Exp.subst, ih1, ih2, Subst.lift_id]
  | unit =>
    rfl
  | btrue => rfl
  | bfalse => rfl
  | read x =>
    simp [Exp.subst, Var.subst_id]
  | write x y =>
    simp [Exp.subst, Var.subst_id]
  | cond x e2 e3 ih2 ih3 =>
    simp [Exp.subst, Var.subst_id, ih2, ih3]
  | boundary k T e ih =>
    simp [Exp.subst, Ty.subst_id, ih, Subst.lift_id]

/-- Converts a renaming to a substitution. -/
def Rename.asSubst (f : Rename s1 s2) : Subst s1 s2 where
  var := fun x => .bound (f.var x)
  tvar := fun X => .tvar (f.var X)
  cvar := fun C K => .cvar (f.var C) K

/-- Lifting a renaming and then converting to a substitution is the same as
  converting to a substitution and then lifting the substitution. -/
theorem Rename.asSubst_lift {f : Rename s1 s2} :
  (f.lift (k:=k)).asSubst = (f.asSubst).lift (k:=k) := by
  apply Subst.funext
  · intro x
    cases x
    · rfl
    · rfl
  · intro X
    cases X
    · rfl
    · rfl
  · intro C ck
    cases C
    · rfl
    · rfl

/-- Substituting a substitution lifted from a renaming is the same as renaming. -/
theorem Var.subst_asSubst {x : Var .var s1} {f : Rename s1 s2} :
  x.subst (f.asSubst) = x.rename f := by
  cases x with
  | bound x => rfl
  | free n => rfl

/-- Substituting a substitution lifted from a renaming is the same as renaming. -/
theorem CaptureSet.subst_asSubst {cs : CaptureSet s1} {f : Rename s1 s2} :
  cs.subst (f.asSubst) = cs.rename f := by
  induction cs with
  | empty => rfl
  | union cs1 cs2 ih1 ih2 =>
    simp [CaptureSet.subst, CaptureSet.rename, ih1, ih2]
  | var x =>
    simp [CaptureSet.subst, CaptureSet.rename, Var.subst_asSubst]
  | cvar C =>
    simp [CaptureSet.subst, CaptureSet.rename, Rename.asSubst]

/-- Substituting a substitution lifted from a renaming is the same as renaming. -/
theorem CaptureBound.subst_asSubst {cb : CaptureBound s1} {f : Rename s1 s2} :
  cb.subst (f.asSubst) = cb.rename f := by
  cases cb with
  | unbound => rfl
  | bound cs => simp [CaptureBound.subst, CaptureBound.rename, CaptureSet.subst_asSubst]

/-- Substituting a substitution lifted from a renaming is the same as renaming. -/
theorem Ty.subst_asSubst {T : Ty sort s1} {f : Rename s1 s2} :
  T.subst (f.asSubst) = T.rename f := by
  induction T generalizing s2 with
  | top => rfl
  | tvar x => simp [Ty.subst, Ty.rename, Rename.asSubst]
  | arrow T1 T2 ih1 ih2 =>
    simp [Ty.subst, Ty.rename, ih1]
    rw [<-Rename.asSubst_lift, ih2]
  | poly T1 T2 ih1 ih2 =>
    simp [Ty.subst, Ty.rename, ih1]
    rw [<-Rename.asSubst_lift, ih2]
  | cpoly cb T ih =>
    simp [Ty.subst, Ty.rename, CaptureBound.subst_asSubst]
    rw [<-Rename.asSubst_lift, ih]
  | unit => rfl
  | cap => rfl
  | bool => rfl
  | cell => rfl
  | label T ih =>
    simp [Ty.subst, Ty.rename, ih]
  | capt cs T ih =>
    simp [Ty.subst, Ty.rename, ih, CaptureSet.subst_asSubst]
  | exi T ih =>
    simp [Ty.subst, Ty.rename]
    rw [<-Rename.asSubst_lift, ih]
  | typ T ih =>
    simp [Ty.subst, Ty.rename, ih]

/-- Substituting a substitution lifted from a renaming is the same as renaming. -/
theorem Exp.subst_asSubst {e : Exp s1} {f : Rename s1 s2} :
  e.subst (f.asSubst) = e.rename f := by
  induction e generalizing s2 with
  | var x =>
    simp [Exp.subst, Exp.rename, Var.subst_asSubst]
  | abs cs T e ih =>
    simp [Exp.subst, Exp.rename, CaptureSet.subst_asSubst, Ty.subst_asSubst]
    rw [<-Rename.asSubst_lift, ih]
  | tabs cs T e ih =>
    simp [Exp.subst, Exp.rename, CaptureSet.subst_asSubst, Ty.subst_asSubst]
    rw [<-Rename.asSubst_lift, ih]
  | cabs cs cb e ih =>
    simp [Exp.subst, Exp.rename, CaptureSet.subst_asSubst, CaptureBound.subst_asSubst]
    rw [<-Rename.asSubst_lift, ih]
  | pack cs x =>
    simp [Exp.subst, Exp.rename, CaptureSet.subst_asSubst, Var.subst_asSubst]
  | app x y =>
    simp [Exp.subst, Exp.rename, Var.subst_asSubst]
  | tapp x T =>
    simp [Exp.subst, Exp.rename, Var.subst_asSubst, Ty.subst_asSubst]
  | capp x cs =>
    simp [Exp.subst, Exp.rename, Var.subst_asSubst, CaptureSet.subst_asSubst]
  | letin e1 e2 ih1 ih2 =>
    simp [Exp.subst, Exp.rename, ih1]
    rw [<-Rename.asSubst_lift, ih2]
  | unpack e1 e2 ih1 ih2 =>
    simp [Exp.subst, Exp.rename, ih1]
    rw [<-Rename.asSubst_lift, <-Rename.asSubst_lift, ih2]
  | unit =>
    rfl
  | btrue =>
    rfl
  | bfalse =>
    rfl
  | read x =>
    simp [Exp.subst, Exp.rename, Var.subst_asSubst]
  | write x y =>
    simp [Exp.subst, Exp.rename, Var.subst_asSubst]
  | cond x e2 e3 ih2 ih3 =>
    simp [Exp.subst, Exp.rename, Var.subst_asSubst, ih2, ih3]
  | boundary k T e ih =>
    simp [Exp.subst, Exp.rename, Ty.subst_asSubst]
    rw [<-Rename.asSubst_lift, <-Rename.asSubst_lift, ih]

theorem Subst.weaken_openVar {z : Var .var s} :
  Rename.succ.asSubst.comp (Subst.openVar z) = Subst.id := by
  apply Subst.funext
  · intro x; rfl
  · intro X; rfl
  · intro C ck; rfl

theorem Subst.weaken_openTVar {U : Ty .shape s} :
  Rename.succ.asSubst.comp (Subst.openTVar U) = Subst.id := by
  apply Subst.funext
  · intro x; rfl
  · intro X; rfl
  · intro C ck; rfl

theorem Subst.weaken_openCVar {C : CaptureSet s} :
  Rename.succ.asSubst.comp (Subst.openCVar C) = Subst.id := by
  apply Subst.funext
  · intro x; rfl
  · intro X; rfl
  · intro C' ck; rfl

theorem CaptureSet.weaken_openVar {C : CaptureSet (s)} {z : Var .var s} :
  (C.rename Rename.succ).subst (Subst.openVar z) = C := by
  calc (C.rename Rename.succ).subst (Subst.openVar z)
      = (C.subst Rename.succ.asSubst).subst (Subst.openVar z) := by rw [<-CaptureSet.subst_asSubst]
    _ = C.subst (Rename.succ.asSubst.comp (Subst.openVar z)) := by rw [CaptureSet.subst_comp]
    _ = C.subst Subst.id := by rw [Subst.weaken_openVar]
    _ = C := by rw [CaptureSet.subst_id]

theorem CaptureSet.weaken_openTVar {C : CaptureSet (s)} {U : Ty .shape s} :
  (C.rename Rename.succ).subst (Subst.openTVar U) = C := by
  calc (C.rename Rename.succ).subst (Subst.openTVar U)
      = (C.subst Rename.succ.asSubst).subst (Subst.openTVar U) := by rw [<-CaptureSet.subst_asSubst]
    _ = C.subst (Rename.succ.asSubst.comp (Subst.openTVar U)) := by rw [CaptureSet.subst_comp]
    _ = C.subst Subst.id := by rw [Subst.weaken_openTVar]
    _ = C := by rw [CaptureSet.subst_id]

theorem CaptureSet.weaken_openCVar {C : CaptureSet (s)} {C' : CaptureSet s} :
  (C.rename Rename.succ).subst (Subst.openCVar C') = C := by
  calc (C.rename Rename.succ).subst (Subst.openCVar C')
      = (C.subst Rename.succ.asSubst).subst (Subst.openCVar C') := by
        rw [<-CaptureSet.subst_asSubst]
    _ = C.subst (Rename.succ.asSubst.comp (Subst.openCVar C')) := by rw [CaptureSet.subst_comp]
    _ = C.subst Subst.id := by rw [Subst.weaken_openCVar]
    _ = C := by rw [CaptureSet.subst_id]

theorem CaptureSet.ground_rename_invariant {C : CaptureSet {}} :
  C.rename f = C := by
  induction C with
  | empty => rfl
  | union cs1 cs2 ih1 ih2 =>
    simp [CaptureSet.rename]
    constructor <;> assumption
  | var x =>
    cases x with
    | bound bx => cases bx  -- No bound variables in empty signature
    | free n =>
      -- Free variables are unchanged by rename
      simp [CaptureSet.rename, Var.rename]
  | cvar c => cases c  -- No capture variables in empty signature

theorem CaptureSet.ground_subst_invariant {C : CaptureSet {}} :
  C.subst σ = C := by
  induction C with
  | empty => rfl
  | union cs1 cs2 ih1 ih2 =>
    simp [CaptureSet.subst]
    constructor <;> assumption
  | var x =>
    cases x with
    | bound bx => cases bx
    | free n => simp [CaptureSet.subst, Var.subst]
  | cvar c => cases c

/-- A substitution is closed if all its images are closed. -/
structure Subst.IsClosed (σ : Subst s1 s2) : Prop where
  var_closed : ∀ x, (σ.var x).IsClosed
  tvar_closed : ∀ X, (σ.tvar X).IsClosed
  cvar_closed : ∀ C K, (σ.cvar C K).IsClosed

/-- Substitution preserves closedness for variables. -/
def Var.is_closed_subst {x : Var .var s1} {σ : Subst s1 s2}
  (hc : x.IsClosed) (hsubst : Subst.IsClosed σ) :
  (x.subst σ).IsClosed := by
  cases x with
  | bound x =>
    exact hsubst.var_closed x
  | free n => cases hc

/-- Substitution preserves closedness for capture sets. -/
def CaptureSet.is_closed_subst {cs : CaptureSet s1} {σ : Subst s1 s2}
  (hc : cs.IsClosed) (hsubst : Subst.IsClosed σ) :
  (cs.subst σ).IsClosed := by
  induction cs with
  | empty =>
    exact IsClosed.empty
  | union cs1 cs2 ih1 ih2 =>
    cases hc with | union h1 h2 =>
    simp [CaptureSet.subst]
    exact IsClosed.union (ih1 h1) (ih2 h2)
  | cvar C ck =>
    simp [CaptureSet.subst]
    exact hsubst.cvar_closed C ck
  | var x ck =>
    cases hc with | var_bound =>
    rename_i bx
    simp [CaptureSet.subst, Var.subst]
    generalize h_eq : σ.var bx = v
    have h_var : v.IsClosed := h_eq ▸ hsubst.var_closed bx
    cases v with
    | bound y =>
      exact IsClosed.var_bound
    | free n =>
      cases h_var

/-- Substitution preserves closedness for capture bounds. -/
def CaptureBound.is_closed_subst {cb : CaptureBound s1} {σ : Subst s1 s2}
  (hc : cb.IsClosed) (hsubst : Subst.IsClosed σ) :
  (cb.subst σ).IsClosed := by
  cases cb with
  | unbound =>
    exact IsClosed.unbound
  | bound cs =>
    cases hc with | bound h_cs =>
    simp [CaptureBound.subst]
    exact IsClosed.bound (CaptureSet.is_closed_subst h_cs hsubst)

-- Helper lemmas for renaming closedness (minimal versions needed here)
private theorem Var.rename_closed_any {x : Var .var s1} {f : Rename s1 s2}
  (hc : x.IsClosed) : (x.rename f).IsClosed := by
  cases x with
  | bound _ => exact IsClosed.bound
  | free _ => cases hc

private theorem CaptureSet.rename_closed_any {cs : CaptureSet s1} {f : Rename s1 s2}
  (hc : cs.IsClosed) : (cs.rename f).IsClosed := by
  induction cs with
  | empty => exact IsClosed.empty
  | union cs1 cs2 ih1 ih2 =>
    cases hc with | union h1 h2 =>
    exact IsClosed.union (ih1 h1) (ih2 h2)
  | cvar => exact IsClosed.cvar
  | var x =>
    cases hc with | var_bound =>
    exact IsClosed.var_bound

private theorem CaptureSet.proj_closed {cs : CaptureSet s} {K : CapKind}
  (hc : cs.IsClosed) : (cs.proj K).IsClosed := by
  induction cs with
  | empty => exact IsClosed.empty
  | union cs1 cs2 ih1 ih2 =>
    cases hc with | union h1 h2 =>
    exact IsClosed.union (ih1 h1) (ih2 h2)
  | cvar => exact IsClosed.cvar
  | var x =>
    cases hc with | var_bound =>
    exact IsClosed.var_bound

private theorem CaptureBound.rename_closed_any {cb : CaptureBound s1} {f : Rename s1 s2}
  (hc : cb.IsClosed) : (cb.rename f).IsClosed := by
  cases cb <;> cases hc
  case unbound.unbound => exact IsClosed.unbound
  case bound.bound cs h_cs => exact IsClosed.bound (CaptureSet.rename_closed_any h_cs)

private theorem Ty.rename_closed_any {T : Ty sort s1} {f : Rename s1 s2}
  (hc : T.IsClosed) : (T.rename f).IsClosed := by
  induction T generalizing s2 with
  | top => exact IsClosed.top
  | tvar => exact IsClosed.tvar
  | arrow T1 T2 ih1 ih2 =>
    cases hc with | arrow h1 h2 =>
    exact IsClosed.arrow (ih1 h1) (ih2 h2)
  | poly S T ih1 ih2 =>
    cases hc with | poly h1 h2 =>
    exact IsClosed.poly (ih1 h1) (ih2 h2)
  | cpoly cb T ih =>
    cases hc with | cpoly hcb hT =>
    exact IsClosed.cpoly (CaptureBound.rename_closed_any hcb) (ih hT)
  | unit => exact IsClosed.unit
  | cap => exact IsClosed.cap
  | bool => exact IsClosed.bool
  | cell => exact IsClosed.cell
  | label T ih =>
    cases hc with | label hT =>
    exact IsClosed.label (ih hT)
  | capt cs T ih =>
    cases hc with | capt h1 h2 =>
    exact IsClosed.capt (CaptureSet.rename_closed_any h1) (ih h2)
  | typ T ih =>
    cases hc with | typ hT =>
    exact IsClosed.typ (ih hT)
  | exi T ih =>
    cases hc with | exi hT =>
    exact IsClosed.exi (ih hT)

/-- Lifting preserves closedness of substitutions. -/
theorem Subst.lift_closed {σ : Subst s1 s2} (hσ : σ.IsClosed) :
  (σ.lift (k:=k)).IsClosed := by
  constructor
  · intro x
    cases x with
    | here => exact Var.IsClosed.bound
    | there x => simp [Subst.lift]; exact Var.rename_closed_any (hσ.var_closed x)
  · intro X
    cases X with
    | here => exact Ty.IsClosed.tvar
    | there X => simp [Subst.lift]; exact Ty.rename_closed_any (hσ.tvar_closed X)
  · intro C ck
    cases C with
    | here => exact CaptureSet.IsClosed.cvar
    | there C => exact CaptureSet.rename_closed_any (hσ.cvar_closed C ck)

/-- Substitution preserves closedness for types. -/
def Ty.is_closed_subst {T : Ty sort s1} {σ : Subst s1 s2}
  (hc : T.IsClosed) (hsubst : Subst.IsClosed σ) :
  (T.subst σ).IsClosed := by
  induction T generalizing s2 with
  | top => exact IsClosed.top
  | tvar X => simp [Ty.subst]; exact hsubst.tvar_closed X
  | arrow T1 T2 ih1 ih2 =>
    cases hc with | arrow h1 h2 =>
    simp [Ty.subst]
    exact IsClosed.arrow (ih1 h1 hsubst) (ih2 h2 (Subst.lift_closed hsubst))
  | poly S T ih1 ih2 =>
    cases hc with | poly h1 h2 =>
    simp [Ty.subst]
    exact IsClosed.poly (ih1 h1 hsubst) (ih2 h2 (Subst.lift_closed hsubst))
  | cpoly cb T ih =>
    cases hc with | cpoly hcb hT =>
    simp [Ty.subst]
    exact IsClosed.cpoly
      (CaptureBound.is_closed_subst hcb hsubst)
      (ih hT (Subst.lift_closed hsubst))
  | unit => exact IsClosed.unit
  | cap => exact IsClosed.cap
  | bool => exact IsClosed.bool
  | cell => exact IsClosed.cell
  | label T ih =>
    cases hc with | label hT =>
    simp [Ty.subst]
    exact IsClosed.label (ih hT hsubst)
  | capt cs S ih =>
    cases hc with | capt h1 h2 =>
    simp [Ty.subst]
    exact IsClosed.capt (CaptureSet.is_closed_subst h1 hsubst) (ih h2 hsubst)
  | typ T ih =>
    cases hc with | typ hT =>
    simp [Ty.subst]
    exact IsClosed.typ (ih hT hsubst)
  | exi T ih =>
    cases hc with | exi hT =>
    simp [Ty.subst]
    exact IsClosed.exi (ih hT (Subst.lift_closed hsubst))

/-- Substitution preserves closedness for expressions. -/
def Exp.is_closed_subst {e : Exp s1} {σ : Subst s1 s2}
  (hc : e.IsClosed) (hsubst : Subst.IsClosed σ) :
  (e.subst σ).IsClosed := by
  induction e generalizing s2 with
  | var x =>
    cases hc with | var hx =>
    simp [Exp.subst]
    constructor
    exact Var.is_closed_subst hx hsubst
  | abs cs T e ih =>
    cases hc with | abs hcs hT he =>
    simp [Exp.subst]
    constructor
    · exact CaptureSet.is_closed_subst hcs hsubst
    · exact Ty.is_closed_subst hT hsubst
    · exact ih he (Subst.lift_closed hsubst)
  | tabs cs S e ih =>
    cases hc with | tabs hcs hS he =>
    simp [Exp.subst]
    constructor
    · exact CaptureSet.is_closed_subst hcs hsubst
    · exact Ty.is_closed_subst hS hsubst
    · exact ih he (Subst.lift_closed hsubst)
  | cabs cs cb e ih =>
    cases hc with | cabs hcs hcb he =>
    simp [Exp.subst]
    constructor
    · exact CaptureSet.is_closed_subst hcs hsubst
    · exact CaptureBound.is_closed_subst hcb hsubst
    · exact ih he (Subst.lift_closed hsubst)
  | pack cs x =>
    cases hc with | pack hcs hx =>
    simp [Exp.subst]
    constructor
    · exact CaptureSet.is_closed_subst hcs hsubst
    · exact Var.is_closed_subst hx hsubst
  | app x y =>
    cases hc with | app hx hy =>
    simp [Exp.subst]
    constructor
    · exact Var.is_closed_subst hx hsubst
    · exact Var.is_closed_subst hy hsubst
  | tapp x T =>
    cases hc with | tapp hx hT =>
    simp [Exp.subst]
    constructor
    · exact Var.is_closed_subst hx hsubst
    · exact Ty.is_closed_subst hT hsubst
  | capp x cs =>
    cases hc with | capp hx hcs =>
    simp [Exp.subst]
    constructor
    · exact Var.is_closed_subst hx hsubst
    · exact CaptureSet.is_closed_subst hcs hsubst
  | letin e1 e2 ih1 ih2 =>
    cases hc with | letin he1 he2 =>
    simp [Exp.subst]
    constructor
    · exact ih1 he1 hsubst
    · exact ih2 he2 (Subst.lift_closed hsubst)
  | unpack e1 e2 ih1 ih2 =>
    cases hc with | unpack he1 he2 =>
    simp [Exp.subst]
    constructor
    · exact ih1 he1 hsubst
    · exact ih2 he2 (Subst.lift_closed (Subst.lift_closed hsubst))
  | unit =>
    exact IsClosed.unit
  | btrue =>
    exact IsClosed.btrue
  | bfalse =>
    exact IsClosed.bfalse
  | read x =>
    cases hc with | read hx =>
    simp [Exp.subst]
    exact IsClosed.read (Var.is_closed_subst hx hsubst)
  | write x y =>
    cases hc with | write hx hy =>
    simp [Exp.subst]
    exact IsClosed.write (Var.is_closed_subst hx hsubst) (Var.is_closed_subst hy hsubst)
  | cond x e2 e3 ih2 ih3 =>
    cases hc with | cond hx h2 h3 =>
    simp [Exp.subst]
    exact IsClosed.cond (Var.is_closed_subst hx hsubst) (ih2 h2 hsubst) (ih3 h3 hsubst)
  | boundary k T e ih =>
    cases hc with | boundary hT he =>
    simp [Exp.subst]
    exact IsClosed.boundary (Ty.is_closed_subst hT hsubst)
      (ih he (Subst.lift_closed (Subst.lift_closed hsubst)))

/-- The openVar substitution is closed if the variable is closed. -/
theorem Subst.openVar_is_closed {z : Var .var s}
  (hz : z.IsClosed) :
  (Subst.openVar z).IsClosed where
  var_closed := fun x => by
    cases x with
    | here => exact hz
    | there x => exact Var.IsClosed.bound
  tvar_closed := fun X => by
    cases X with
    | there X => exact Ty.IsClosed.tvar
  cvar_closed := fun C K => by
    cases C with
    | there C => exact CaptureSet.IsClosed.cvar

/-- The openTVar substitution is closed if the type is closed. -/
theorem Subst.openTVar_is_closed {U : Ty .shape s}
  (hU : U.IsClosed) :
  (Subst.openTVar U).IsClosed where
  var_closed := fun x => by
    cases x with
    | there x => exact Var.IsClosed.bound
  tvar_closed := fun X => by
    cases X with
    | here => exact hU
    | there X => exact Ty.IsClosed.tvar
  cvar_closed := fun C K => by
    cases C with
    | there C => exact CaptureSet.IsClosed.cvar

/-- The openCVar substitution is closed if the capture set is closed. -/
theorem Subst.openCVar_is_closed {C : CaptureSet s}
  (hC : C.IsClosed) :
  (Subst.openCVar C).IsClosed where
  var_closed := fun x => by
    cases x with
    | there x => exact Var.IsClosed.bound
  tvar_closed := fun X => by
    cases X with
    | there X => exact Ty.IsClosed.tvar
  cvar_closed := fun c K => by
    cases c with
    | here => exact CaptureSet.proj_closed hC
    | there c => exact CaptureSet.IsClosed.cvar

/-- If the result of substitution is closed, the original variable was closed. -/
theorem Var.subst_closed_inv {x : Var .var s1} {σ : Subst s1 s2}
  (hclosed : (x.subst σ).IsClosed) :
  x.IsClosed := by
  cases x with
  | bound bx => constructor
  | free n =>
    simp [Var.subst] at hclosed
    cases hclosed

/-- If the result of substitution is closed, the original capture set was closed. -/
theorem CaptureSet.subst_closed_inv {cs : CaptureSet s1} {σ : Subst s1 s2}
  (hclosed : (cs.subst σ).IsClosed) :
  cs.IsClosed := by
  induction cs with
  | empty => exact IsClosed.empty
  | union cs1 cs2 ih1 ih2 =>
    simp [CaptureSet.subst] at hclosed
    cases hclosed with | union h1 h2 =>
    exact IsClosed.union (ih1 h1) (ih2 h2)
  | cvar C => exact IsClosed.cvar
  | var x =>
    cases x with
    | bound bx =>
      -- For bound variables, .var (.bound bx) is always closed
      exact IsClosed.var_bound
    | free n =>
      -- For free variables, (.var (.free n)).subst σ = .var (.free n)
      -- But this can't be closed, contradicting hclosed
      simp [CaptureSet.subst, Var.subst] at hclosed
      cases hclosed

/-- If the result of substitution is closed, the original capture bound was closed. -/
theorem CaptureBound.subst_closed_inv {cb : CaptureBound s1} {σ : Subst s1 s2}
  (hclosed : (cb.subst σ).IsClosed) :
  cb.IsClosed := by
  cases cb with
  | unbound => exact IsClosed.unbound
  | bound cs =>
    simp [CaptureBound.subst] at hclosed
    cases hclosed with | bound h_cs =>
    exact IsClosed.bound (CaptureSet.subst_closed_inv h_cs)

/-- If the result of substitution is closed, the original type was closed. -/
theorem Ty.subst_closed_inv {T : Ty sort s1} {σ : Subst s1 s2}
  (hclosed : (T.subst σ).IsClosed) :
  T.IsClosed := by
  induction T generalizing s2 with
  | top => exact IsClosed.top
  | tvar X => exact IsClosed.tvar
  | arrow T1 T2 ih1 ih2 =>
    simp [Ty.subst] at hclosed
    cases hclosed with | arrow h1 h2 =>
    exact IsClosed.arrow (ih1 h1) (ih2 h2)
  | poly T1 T2 ih1 ih2 =>
    simp [Ty.subst] at hclosed
    cases hclosed with | poly h1 h2 =>
    exact IsClosed.poly (ih1 h1) (ih2 h2)
  | cpoly cb T ih =>
    simp [Ty.subst] at hclosed
    cases hclosed with | cpoly hcb hT =>
    exact IsClosed.cpoly (CaptureBound.subst_closed_inv hcb) (ih hT)
  | unit => exact IsClosed.unit
  | cap => exact IsClosed.cap
  | bool => exact IsClosed.bool
  | cell => exact IsClosed.cell
  | label T ih =>
    simp [Ty.subst] at hclosed
    cases hclosed with | label hT =>
    exact IsClosed.label (ih hT)
  | capt cs T ih =>
    simp [Ty.subst] at hclosed
    cases hclosed with | capt h1 h2 =>
    exact IsClosed.capt (CaptureSet.subst_closed_inv h1) (ih h2)
  | exi T ih =>
    simp [Ty.subst] at hclosed
    cases hclosed with | exi hT =>
    exact IsClosed.exi (ih hT)
  | typ T ih =>
    simp [Ty.subst] at hclosed
    cases hclosed with | typ hT =>
    exact IsClosed.typ (ih hT)

/-- If the result of substitution is closed, the original expression was closed. -/
theorem Exp.subst_closed_inv {e : Exp s1} {σ : Subst s1 s2}
  (hclosed : (e.subst σ).IsClosed) :
  e.IsClosed := by
  induction e generalizing s2 with
  | var x =>
    simp [Exp.subst] at hclosed
    cases hclosed with | var hx =>
    exact IsClosed.var (Var.subst_closed_inv hx)
  | abs cs T e ih =>
    simp [Exp.subst] at hclosed
    cases hclosed with | abs hcs hT he =>
    exact IsClosed.abs (CaptureSet.subst_closed_inv hcs) (Ty.subst_closed_inv hT) (ih he)
  | tabs cs T e ih =>
    simp [Exp.subst] at hclosed
    cases hclosed with | tabs hcs hT he =>
    exact IsClosed.tabs (CaptureSet.subst_closed_inv hcs) (Ty.subst_closed_inv hT) (ih he)
  | cabs cs cb e ih =>
    simp [Exp.subst] at hclosed
    cases hclosed with | cabs hcs hcb he =>
    exact IsClosed.cabs
      (CaptureSet.subst_closed_inv hcs)
      (CaptureBound.subst_closed_inv hcb)
      (ih he)
  | pack cs x =>
    simp [Exp.subst] at hclosed
    cases hclosed with | pack hcs hx =>
    exact IsClosed.pack (CaptureSet.subst_closed_inv hcs) (Var.subst_closed_inv hx)
  | app x y =>
    simp [Exp.subst] at hclosed
    cases hclosed with | app hx hy =>
    exact IsClosed.app (Var.subst_closed_inv hx) (Var.subst_closed_inv hy)
  | tapp x T =>
    simp [Exp.subst] at hclosed
    cases hclosed with | tapp hx hT =>
    exact IsClosed.tapp (Var.subst_closed_inv hx) (Ty.subst_closed_inv hT)
  | capp x cs =>
    simp [Exp.subst] at hclosed
    cases hclosed with | capp hx hcs =>
    exact IsClosed.capp (Var.subst_closed_inv hx) (CaptureSet.subst_closed_inv hcs)
  | letin e1 e2 ih1 ih2 =>
    simp [Exp.subst] at hclosed
    cases hclosed with | letin he1 he2 =>
    exact IsClosed.letin (ih1 he1) (ih2 he2)
  | unpack e1 e2 ih1 ih2 =>
    simp [Exp.subst] at hclosed
    cases hclosed with | unpack he1 he2 =>
    exact IsClosed.unpack (ih1 he1) (ih2 he2)
  | unit => exact IsClosed.unit
  | btrue =>
    simp [Exp.subst] at hclosed
    cases hclosed with | btrue => exact IsClosed.btrue
  | bfalse =>
    simp [Exp.subst] at hclosed
    cases hclosed with | bfalse => exact IsClosed.bfalse
  | read x =>
    simp [Exp.subst] at hclosed
    cases hclosed with | read hx =>
    exact IsClosed.read (Var.subst_closed_inv hx)
  | write x y =>
    simp [Exp.subst] at hclosed
    cases hclosed with | write hx hy =>
    exact IsClosed.write (Var.subst_closed_inv hx) (Var.subst_closed_inv hy)
  | cond x e2 e3 ih2 ih3 =>
    simp [Exp.subst] at hclosed
    cases hclosed with | cond hx h2 h3 =>
    exact IsClosed.cond (Var.subst_closed_inv hx) (ih2 h2) (ih3 h3)
  | boundary k T e ih =>
    simp [Exp.subst] at hclosed
    cases hclosed with | boundary hT he =>
    exact IsClosed.boundary (Ty.subst_closed_inv hT) (ih he)

end CaplessK
