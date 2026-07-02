import Semantic.CoreCapybara.Syntax

namespace CoreCapybara

/-- A substitution maps bound variables of each kind to terms of the appropriate sort. -/
structure Subst (s1 s2 : Sig) where
  var : BVar s1 .var -> Var .var s2
  tvar : BVar s1 .tvar -> PureTy s2
  cvar : BVar s1 .cvar -> CaptureSet s2

/-- Lifts a substitution under a binder. The newly bound variable maps to itself. -/
def Subst.lift (s : Subst s1 s2) : Subst (s1,,k) (s2,,k) where
  var := fun x => by
    cases x
    case here => exact .bound .here
    case there x => exact (s.var x).rename Rename.succ
  tvar := fun x => by
    cases x
    case here => exact PureTy.tvar .here
    case there x => exact (s.tvar x).rename Rename.succ
  cvar := fun x => by
    cases x
    case here => exact .cvar (.M .epsilon) .here
    case there x => exact (s.cvar x).rename Rename.succ

/-- Lifts a substitution under multiple binders. -/
def Subst.liftMany (s : Subst s1 s2) (K : Sig) : Subst (s1 ++ K) (s2 ++ K) :=
  match K with
  | [] => s
  | k :: K => (s.liftMany K).lift (k:=k)

/-- Lifts a substitution under `n` capture-variable binders. -/
def Subst.liftCVars (σ : Subst s1 s2) : (n : Nat) -> Subst (s1.extendCVars n) (s2.extendCVars n)
| 0 => σ
| n+1 => (σ.liftCVars n).lift (k := .cvar)

/-- The identity substitution. -/
def Subst.id {s : Sig} : Subst s s where
  var := fun x => .bound x
  tvar := fun x => PureTy.tvar x
  cvar := fun x => .cvar (.M .epsilon) x

/-- Applies a substitution to a variable. Free variables remain unchanged. -/
def Var.subst : Var .var s1 -> Subst s1 s2 -> Var .var s2
| .bound x, s => s.var x
| .free n, _ => .free n

/-- Applies a substitution to all bound variables in a capture set. -/
def CaptureSet.subst : CaptureSet s1 -> Subst s1 s2 -> CaptureSet s2
| .empty, _ => .empty
| .union cs1 cs2, σ => .union (cs1.subst σ) (cs2.subst σ)
| .var m x, σ => .var m (x.subst σ)
| .cvar m x, σ => (σ.cvar x).applyAccess m

/-- Applies a substitution to a capture bound. -/
def CaptureBound.subst : CaptureBound s1 -> Subst s1 s2 -> CaptureBound s2
| .unbound, _ => .unbound
| .bound cs, σ => .bound (cs.subst σ)

/-- Applies a substitution to all bound variables in a separation context. -/
def SepCtx.subst : SepCtx s1 -> Subst s1 s2 -> SepCtx s2
| .empty, _ => .empty
| .cons K C, σ => .cons (K.subst σ) (C.subst σ)

/-- Applies a substitution to all bound variables in a mutability context. -/
def MutabilityCtx.subst : MutabilityCtx s1 -> Subst s1 s2 -> MutabilityCtx s2
| .empty, _ => .empty
| .cons K C m, σ => .cons (K.subst σ) (C.subst σ) m

/-- Applies a substitution to a modal context, componentwise. -/
def ModalCtx.subst (Ψ : ModalCtx s1) (σ : Subst s1 s2) : ModalCtx s2 :=
  ⟨Ψ.sep.subst σ, Ψ.mutability.subst σ⟩

@[simp] theorem ModalCtx.subst_sep {Ψ : ModalCtx s1} {σ : Subst s1 s2} :
    (Ψ.subst σ).sep = Ψ.sep.subst σ := rfl

@[simp] theorem ModalCtx.subst_mutability {Ψ : ModalCtx s1} {σ : Subst s1 s2} :
    (Ψ.subst σ).mutability = Ψ.mutability.subst σ := rfl

/-- Applies a substitution to a type. -/
def Ty.subst : Ty sort s1 -> Subst s1 s2 -> Ty sort s2
| .top, _ => .top
| .tvar x, s => (s.tvar x).core
| .arrow T1 cs T2, s => .arrow (T1.subst s) (cs.subst s) (T2.subst s.lift)
| .poly T1 cs T2, s => .poly (T1.subst s) (cs.subst s) (T2.subst s.lift)
| .cpoly cb cs T, s => .cpoly (cb.subst s) (cs.subst s) (T.subst s.lift)
| .consumer T1 cs T2, s => .consumer (T1.subst s) (cs.subst s) (T2.subst s)
| .modal cs Ψ T, s => .modal (cs.subst s) (Ψ.subst s) (T.subst s)
| .unit, _ => .unit
| .cap cs, s => .cap (cs.subst s)
| .bool, _ => .bool
| .cell cs T, s => .cell (cs.subst s) (T.subst s)
| .reader cs T, s => .reader (cs.subst s) (T.subst s)
| .exi n T, s => .exi n (T.subst (s.liftCVars n))
| .typ T, s => .typ (T.subst s)

/-- Substitution preserves emptiness of capture sets. -/
theorem CaptureSet.IsEmpty.subst {cs : CaptureSet s1} (h : cs.IsEmpty) (σ : Subst s1 s2) :
    (cs.subst σ).IsEmpty := by
  induction h with
  | empty => exact IsEmpty.empty
  | union _ _ ih1 ih2 => exact IsEmpty.union ih1 ih2

/-- Substitution preserves purity. -/
theorem Ty.IsPureType.subst {T : Ty .capt s1} (h : T.IsPureType) (σ : Subst s1 s2) :
    (T.subst σ).IsPureType := by
  unfold IsPureType at *
  cases T with
  | top => exact CaptureSet.IsEmpty.empty
  | tvar x => simpa [Ty.subst, Ty.captureSet] using (σ.tvar x).p
  | unit => exact CaptureSet.IsEmpty.empty
  | bool => exact CaptureSet.IsEmpty.empty
  | arrow _ _ _ => simp only [Ty.subst, Ty.captureSet] at *; exact h.subst σ
  | poly _ _ _ => simp only [Ty.subst, Ty.captureSet] at *; exact h.subst σ
  | cpoly _ _ _ => simp only [Ty.subst, Ty.captureSet] at *; exact h.subst σ
  | consumer _ _ _ => simp only [Ty.subst, Ty.captureSet] at *; exact h.subst σ
  | modal _ _ _ => simp only [Ty.subst, Ty.captureSet] at *; exact h.subst σ
  | cap cs => simp only [Ty.subst, Ty.captureSet] at *; exact h.subst σ
  | cell cs T => simp only [Ty.subst, Ty.captureSet] at *; exact h.subst σ
  | reader cs T => simp only [Ty.subst, Ty.captureSet] at *; exact h.subst σ

/-- Applies a substitution to a pure type. -/
def PureTy.subst (T : PureTy s1) (σ : Subst s1 s2) : PureTy s2 :=
  ⟨T.core.subst σ, T.p.subst σ⟩

/-- Applies a substitution to an expression. -/
def Exp.subst : Exp s1 -> Subst s1 s2 -> Exp s2
| .var x, s => .var (x.subst s)
| .abs cs T e, s => .abs (cs.subst s) (T.subst s) (e.subst s.lift)
| .tabs cs T e, s => .tabs (cs.subst s) (T.subst s) (e.subst s.lift)
| .cabs cs cb e, s => .cabs (cs.subst s) (cb.subst s) (e.subst s.lift)
| .consumer cs T e, s => .consumer (cs.subst s) (T.subst s) (e.subst s.lift.lift)
| .boxed cs Ψ e, s => .boxed (cs.subst s) (Ψ.subst s) (e.subst s)
| .reader x, s => .reader (x.subst s)
| .alloc x, s => .alloc (x.subst s)
| .drop x, s => .drop (x.subst s)
| .pack css x, s => .pack (css.map (·.subst s)) (x.subst s)
| .app x y, s => .app (x.subst s) (y.subst s)
| .tapp x T, s => .tapp (x.subst s) (T.subst s)
| .capp x cs, s => .capp (x.subst s) (cs.subst s)
| .unwrap x, s => .unwrap (x.subst s)
| .letin e1 e2, s => .letin (e1.subst s) (e2.subst s.lift)
| .unpack n e1 e2, s => .unpack n (e1.subst s) (e2.subst ((s.liftCVars n).lift))
| .unit, _ => .unit
| .btrue, _ => .btrue
| .bfalse, _ => .bfalse
| .read x, s => .read (x.subst s)
| .write x y, s => .write (x.subst s) (y.subst s)
| .cond x e2 e3, s => .cond (x.subst s) (e2.subst s) (e3.subst s)
| .par C1 C2 e1 e2, s => .par (C1.subst s) (C2.subst s) (e1.subst s) (e2.subst s)

/-- Substitution that opens a variable binder by replacing the innermost bound variable with `x`. -/
def Subst.openVar (x : Var .var s) : Subst (s,x) s where
  var := fun
    | .here => x
    | .there x0 => .bound x0
  tvar := fun
    | .there x0 => PureTy.tvar x0
  cvar := fun
    | .there x0 => .cvar (.M .epsilon) x0

/-- Opens a type variable binder, substituting `U` for the innermost bound. -/
def Subst.openTVar (U : PureTy s) : Subst (s,X) s where
  var := fun
    | .there x => .bound x
  tvar := fun
    | .here => U
    | .there x => PureTy.tvar x
  cvar := fun
    | .there x => .cvar (.M .epsilon) x

/-- Opens a capture variable binder, substituting `C` for the innermost bound. -/
def Subst.openCVar (C : CaptureSet s) : Subst (s,C) s where
  var := fun
    | .there x => .bound x
  tvar := fun
    | .there x => PureTy.tvar x
  cvar := fun
    | .here => C
    | .there x => .cvar (.M .epsilon) x

/-- Opens `n` capture-variable binders simultaneously: the `i`-th innermost bound
    capture variable (de Bruijn index `i`, so `.here` is index `0`) is replaced by
    `Cs.get i` (with `Cs.head` = `Cs.get 0` opening the innermost binder). Generalizes
    `Subst.openCVar` (the `n = 1` case, `openCVars ⟨[C], _⟩ = openCVar C`).

    All evidences live over the *outer* signature `s`, so this is a **parallel**
    substitution — no evidence may mention any of the bound capture variables. -/
def Subst.openCVars : {n : Nat} → List.Vector (CaptureSet s) n → Subst (s.extendCVars n) s
  | 0, _ => Subst.id
  | _ + 1, Cs =>
    { var := fun | .there y => (Subst.openCVars Cs.tail).var y
      tvar := fun | .there Y => (Subst.openCVars Cs.tail).tvar Y
      cvar := fun
        | .here => Cs.head
        | .there y => (Subst.openCVars Cs.tail).cvar y }

/-- Opens an `n`-ary existential package, substituting `x` for the innermost (term)
    binder and the `n` evidences `Cs` for the `n` capture-variable binders underneath
    (in parallel, as in `Subst.openCVars`). -/
def Subst.unpack {n : Nat} (Cs : List.Vector (CaptureSet s) n) (x : Var .var s) :
    Subst ((s.extendCVars n),x) s where
  var := fun
    | .here => x
    | .there y => (Subst.openCVars Cs).var y
  tvar := fun
    | .there Y => (Subst.openCVars Cs).tvar Y
  cvar := fun
    | .there c => (Subst.openCVars Cs).cvar c

/-- Function extensionality for substitutions.
  Two substitutions are equal if they map all variables equally. -/
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

/-- Composition of substitutions. -/
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
  simp only [CaptureSet.rename_comp, Rename.succ_lift_comm]

theorem PureTy.weaken_rename_comm {T : PureTy s1} {f : Rename s1 s2} :
  (T.rename Rename.succ).rename (f.lift (k:=k0)) = (T.rename f).rename (Rename.succ) := by
  simp only [PureTy.rename, Ty.weaken_rename_comm]

/-- Post-composes a substitution with a renaming: substitute, then rename the images. -/
def Subst.compRename (σ : Subst s1 s2) (f : Rename s2 s3) : Subst s1 s3 where
  var := fun x => (σ.var x).rename f
  tvar := fun X => (σ.tvar X).rename f
  cvar := fun C => (σ.cvar C).rename f

/-- Pre-composes a renaming with a substitution: rename the variable, then substitute. -/
def Rename.compSubst (f : Rename s1 s2) (σ : Subst s2 s3) : Subst s1 s3 where
  var := fun x => σ.var (f.var x)
  tvar := fun X => σ.tvar (f.var X)
  cvar := fun C => σ.cvar (f.var C)

/-! ### Substitute-then-rename equals substituting by `σ.compRename f`. -/

theorem Var.subst_rename_comm {x : Var .var s1} {σ : Subst s1 s2} {f : Rename s2 s3} :
  (x.subst σ).rename f = x.subst (σ.compRename f) := by
  cases x with
  | bound x => rfl
  | free n => rfl

theorem CaptureSet.subst_rename_comm {cs : CaptureSet s1} {σ : Subst s1 s2} {f : Rename s2 s3} :
  (cs.subst σ).rename f = cs.subst (σ.compRename f) := by
  induction cs with
  | empty => rfl
  | union cs1 cs2 ih1 ih2 => simp only [CaptureSet.subst, CaptureSet.rename, ih1, ih2]
  | var m x =>
    simp only [CaptureSet.subst, CaptureSet.rename]
    exact congrArg (CaptureSet.var m) Var.subst_rename_comm
  | cvar m C =>
    simp only [CaptureSet.subst, Subst.compRename, CaptureSet.applyAccess_rename]

theorem CaptureBound.subst_rename_comm {cb : CaptureBound s1} {σ : Subst s1 s2} {f : Rename s2 s3} :
  (cb.subst σ).rename f = cb.subst (σ.compRename f) := by
  cases cb with
  | unbound => rfl
  | bound cs => simp only [CaptureBound.subst, CaptureBound.rename, CaptureSet.subst_rename_comm]

theorem SepCtx.subst_rename_comm {Ψ : SepCtx s1} {σ : Subst s1 s2} {f : Rename s2 s3} :
  (Ψ.subst σ).rename f = Ψ.subst (σ.compRename f) := by
  induction Ψ with
  | empty => rfl
  | cons Ψ C ih => simp only [SepCtx.subst, SepCtx.rename, ih, CaptureSet.subst_rename_comm]

theorem MutabilityCtx.subst_rename_comm {Ψ : MutabilityCtx s1}
    {σ : Subst s1 s2} {f : Rename s2 s3} :
  (Ψ.subst σ).rename f = Ψ.subst (σ.compRename f) := by
  induction Ψ with
  | empty => rfl
  | cons Ψ C m ih =>
    simp only [MutabilityCtx.subst, MutabilityCtx.rename, ih, CaptureSet.subst_rename_comm]

theorem ModalCtx.subst_rename_comm {Ψ : ModalCtx s1} {σ : Subst s1 s2} {f : Rename s2 s3} :
  (Ψ.subst σ).rename f = Ψ.subst (σ.compRename f) := by
  cases Ψ with
  | mk sep mu =>
    simp only [ModalCtx.subst, ModalCtx.rename,
      SepCtx.subst_rename_comm, MutabilityCtx.subst_rename_comm]

/-! ### Rename-then-substitute equals substituting by `f.compSubst σ`. -/

theorem Var.rename_subst_comm {x : Var .var s1} {f : Rename s1 s2} {σ : Subst s2 s3} :
  (x.rename f).subst σ = x.subst (f.compSubst σ) := by
  cases x with
  | bound x => rfl
  | free n => rfl

theorem CaptureSet.rename_subst_comm {cs : CaptureSet s1} {f : Rename s1 s2} {σ : Subst s2 s3} :
  (cs.rename f).subst σ = cs.subst (f.compSubst σ) := by
  induction cs with
  | empty => rfl
  | union cs1 cs2 ih1 ih2 => simp only [CaptureSet.rename, CaptureSet.subst, ih1, ih2]
  | var m x =>
    simp only [CaptureSet.rename, CaptureSet.subst]
    exact congrArg (CaptureSet.var m) Var.rename_subst_comm
  | cvar m C =>
    simp only [CaptureSet.rename, CaptureSet.subst, Rename.compSubst]

theorem CaptureBound.rename_subst_comm {cb : CaptureBound s1} {f : Rename s1 s2} {σ : Subst s2 s3} :
  (cb.rename f).subst σ = cb.subst (f.compSubst σ) := by
  cases cb with
  | unbound => rfl
  | bound cs => simp only [CaptureBound.rename, CaptureBound.subst, CaptureSet.rename_subst_comm]

theorem SepCtx.rename_subst_comm {Ψ : SepCtx s1} {f : Rename s1 s2} {σ : Subst s2 s3} :
  (Ψ.rename f).subst σ = Ψ.subst (f.compSubst σ) := by
  induction Ψ with
  | empty => rfl
  | cons Ψ C ih => simp only [SepCtx.rename, SepCtx.subst, ih, CaptureSet.rename_subst_comm]

theorem MutabilityCtx.rename_subst_comm {Ψ : MutabilityCtx s1}
    {f : Rename s1 s2} {σ : Subst s2 s3} :
  (Ψ.rename f).subst σ = Ψ.subst (f.compSubst σ) := by
  induction Ψ with
  | empty => rfl
  | cons Ψ C m ih =>
    simp only [MutabilityCtx.rename, MutabilityCtx.subst, ih, CaptureSet.rename_subst_comm]

theorem ModalCtx.rename_subst_comm {Ψ : ModalCtx s1} {f : Rename s1 s2} {σ : Subst s2 s3} :
  (Ψ.rename f).subst σ = Ψ.subst (f.compSubst σ) := by
  cases Ψ with
  | mk sep mu =>
    simp only [ModalCtx.rename, ModalCtx.subst,
      SepCtx.rename_subst_comm, MutabilityCtx.rename_subst_comm]

/-! ### Lift commutations for the compositions. -/

theorem Subst.compRename_lift {σ : Subst s1 s2} {f : Rename s2 s3} :
  (σ.compRename f).lift (k:=k) = σ.lift.compRename f.lift := by
  apply Subst.funext
  · intro x
    cases x with
    | here => rfl
    | there x => exact Var.weaken_rename_comm.symm
  · intro X
    cases X with
    | here => rfl
    | there X => exact PureTy.weaken_rename_comm.symm
  · intro C
    cases C with
    | here => rfl
    | there C => exact CaptureSet.weaken_rename_comm.symm

theorem Rename.compSubst_lift {f : Rename s1 s2} {σ : Subst s2 s3} :
  (f.compSubst σ).lift (k:=k) = f.lift.compSubst σ.lift := by
  apply Subst.funext
  · intro x
    cases x with
    | here => rfl
    | there x => rfl
  · intro X
    cases X with
    | here => rfl
    | there X => rfl
  · intro C
    cases C with
    | here => rfl
    | there C => rfl

theorem Subst.compRename_liftCVars {σ : Subst s1 s2} {f : Rename s2 s3} {n : Nat} :
  (σ.compRename f).liftCVars n = (σ.liftCVars n).compRename (f.liftCVars n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change ((σ.compRename f).liftCVars n).lift
      = ((σ.liftCVars n).lift).compRename ((f.liftCVars n).lift)
    rw [ih]
    exact Subst.compRename_lift

theorem Rename.compSubst_liftCVars {f : Rename s1 s2} {σ : Subst s2 s3} {n : Nat} :
  (f.compSubst σ).liftCVars n = (f.liftCVars n).compSubst (σ.liftCVars n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change ((f.compSubst σ).liftCVars n).lift
      = ((f.liftCVars n).lift).compSubst ((σ.liftCVars n).lift)
    rw [ih]
    exact Rename.compSubst_lift

/-! ### Substitute-then-rename / rename-then-substitute for types. -/

theorem Ty.subst_rename_comm {T : Ty sort s1} {σ : Subst s1 s2} {f : Rename s2 s3} :
  (T.subst σ).rename f = T.subst (σ.compRename f) := by
  induction T generalizing s2 s3 with
  | top => rfl
  | tvar X => simp only [Ty.subst, Subst.compRename, PureTy.rename]
  | arrow T1 cs T2 ih1 ih2 =>
    simp only [Ty.subst, Ty.rename, ih1, ih2, CaptureSet.subst_rename_comm]
    rw [Subst.compRename_lift]
    rfl
  | poly T1 cs T2 ih1 ih2 =>
    simp only [Ty.subst, Ty.rename, ih1, ih2, CaptureSet.subst_rename_comm]
    rw [Subst.compRename_lift]
    rfl
  | cpoly cb cs T ih =>
    simp only [Ty.subst, Ty.rename, ih, CaptureBound.subst_rename_comm,
      CaptureSet.subst_rename_comm]
    rw [Subst.compRename_lift]
    rfl
  | consumer T1 cs T2 ih1 ih2 =>
    simp only [Ty.subst, Ty.rename, ih1, ih2, CaptureSet.subst_rename_comm]
  | modal cs Ψ T ih =>
    simp only [Ty.subst, Ty.rename, ih, CaptureSet.subst_rename_comm, ModalCtx.subst_rename_comm]
  | unit => rfl
  | cap cs => simp only [Ty.subst, Ty.rename, CaptureSet.subst_rename_comm]
  | bool => rfl
  | cell cs T ih => simp only [Ty.subst, Ty.rename, ih, CaptureSet.subst_rename_comm]
  | reader cs T ih => simp only [Ty.subst, Ty.rename, ih, CaptureSet.subst_rename_comm]
  | exi n T ih =>
    simp only [Ty.subst, Ty.rename, ih]
    rw [Subst.compRename_liftCVars]
  | typ T ih => simp only [Ty.subst, Ty.rename, ih]

theorem Ty.rename_subst_comm {T : Ty sort s1} {f : Rename s1 s2} {σ : Subst s2 s3} :
  (T.rename f).subst σ = T.subst (f.compSubst σ) := by
  induction T generalizing s2 s3 with
  | top => rfl
  | tvar X => simp only [Ty.rename, Ty.subst, Rename.compSubst]
  | arrow T1 cs T2 ih1 ih2 =>
    simp only [Ty.rename, Ty.subst, ih1, ih2, CaptureSet.rename_subst_comm]
    rw [Rename.compSubst_lift]
    rfl
  | poly T1 cs T2 ih1 ih2 =>
    simp only [Ty.rename, Ty.subst, ih1, ih2, CaptureSet.rename_subst_comm]
    rw [Rename.compSubst_lift]
    rfl
  | cpoly cb cs T ih =>
    simp only [Ty.rename, Ty.subst, ih, CaptureBound.rename_subst_comm,
      CaptureSet.rename_subst_comm]
    rw [Rename.compSubst_lift]
    rfl
  | consumer T1 cs T2 ih1 ih2 =>
    simp only [Ty.rename, Ty.subst, ih1, ih2, CaptureSet.rename_subst_comm]
  | modal cs Ψ T ih =>
    simp only [Ty.rename, Ty.subst, ih, CaptureSet.rename_subst_comm, ModalCtx.rename_subst_comm]
  | unit => rfl
  | cap cs => simp only [Ty.rename, Ty.subst, CaptureSet.rename_subst_comm]
  | bool => rfl
  | cell cs T ih => simp only [Ty.rename, Ty.subst, ih, CaptureSet.rename_subst_comm]
  | reader cs T ih => simp only [Ty.rename, Ty.subst, ih, CaptureSet.rename_subst_comm]
  | exi n T ih =>
    simp only [Ty.rename, Ty.subst, ih]
    rw [Rename.compSubst_liftCVars]
  | typ T ih => simp only [Ty.rename, Ty.subst, ih]

theorem Ty.weaken_subst_comm_base {T : Ty sort s1} {σ : Subst s1 s2} :
  (T.subst σ).rename (Rename.succ (k:=k)) = (T.rename Rename.succ).subst (σ.lift (k:=k)) := by
  rw [Ty.subst_rename_comm, Ty.rename_subst_comm]
  congr 1

theorem PureTy.weaken_subst_comm_base {T : PureTy s1} {σ : Subst s1 s2} :
  (T.subst σ).rename (Rename.succ (k:=k)) = (T.rename Rename.succ).subst (σ.lift (k:=k)) := by
  simp only [PureTy.subst, PureTy.rename, Ty.weaken_subst_comm_base]

theorem Var.weaken_subst_comm_base {x : Var .var s1} {σ : Subst s1 s2} :
  (x.subst σ).rename (Rename.succ (k:=k)) = (x.rename Rename.succ).subst (σ.lift) := by
  cases x with
  | bound x => rfl
  | free n => rfl

theorem CVar.weaken_subst_comm_base {C : BVar s1 .cvar} {σ : Subst s1 s2} :
  (σ.cvar C).rename (Rename.succ (k:=k)) =
  (σ.lift (k:=k)).cvar ((Rename.succ (k:=k)).var C) := by
  cases C <;> rfl

theorem CaptureSet.weaken_subst_comm_base {cs : CaptureSet s1} {σ : Subst s1 s2} :
  (cs.subst σ).rename (Rename.succ (k:=k)) = (cs.rename Rename.succ).subst (σ.lift) := by
  induction cs with
  | empty => rfl
  | union cs1 cs2 ih1 ih2 =>
    simp only [CaptureSet.subst, CaptureSet.rename, ih1, ih2]
  | var m x =>
    simp only [CaptureSet.subst, CaptureSet.rename]
    exact congrArg (CaptureSet.var m) Var.weaken_subst_comm_base
  | cvar m C =>
    simp only [CaptureSet.subst, CaptureSet.rename]
    rw [CaptureSet.applyAccess_rename]
    rw [CVar.weaken_subst_comm_base]

theorem SepCtx.weaken_subst_comm_base {Ψ : SepCtx s1} {σ : Subst s1 s2} :
  (Ψ.subst σ).rename (Rename.succ (k := k)) = (Ψ.rename Rename.succ).subst (σ.lift) := by
  induction Ψ with
  | empty => rfl
  | cons Ψ C ih =>
    simp only [SepCtx.subst, SepCtx.rename, ih, CaptureSet.weaken_subst_comm_base]

theorem MutabilityCtx.weaken_subst_comm_base {Ψ : MutabilityCtx s1} {σ : Subst s1 s2} :
  (Ψ.subst σ).rename (Rename.succ (k := k)) = (Ψ.rename Rename.succ).subst (σ.lift) := by
  induction Ψ with
  | empty => rfl
  | cons Ψ C m ih =>
    simp only [MutabilityCtx.subst, MutabilityCtx.rename, ih, CaptureSet.weaken_subst_comm_base]

theorem ModalCtx.weaken_subst_comm_base {Ψ : ModalCtx s1} {σ : Subst s1 s2} :
  (Ψ.subst σ).rename (Rename.succ (k := k)) = (Ψ.rename Rename.succ).subst (σ.lift) := by
  cases Ψ with
  | mk sep mu =>
    simp only [ModalCtx.subst, ModalCtx.rename,
      SepCtx.weaken_subst_comm_base, MutabilityCtx.weaken_subst_comm_base]

theorem CaptureBound.weaken_subst_comm_base {cb : CaptureBound s1} {σ : Subst s1 s2} :
  (cb.subst σ).rename (Rename.succ (k := k)) = (cb.rename Rename.succ).subst (σ.lift) := by
  cases cb with
  | unbound => rfl
  | bound cs =>
    simp only [CaptureBound.subst, CaptureBound.rename, CaptureSet.weaken_subst_comm_base]

/-- Composition of substitutions commutes with lifting. -/
theorem Subst.comp_lift {σ1 : Subst s1 s2} {σ2 : Subst s2 s3} {k : Kind} :
  (σ1.lift (k := k)).comp (σ2.lift (k := k)) = (σ1.comp σ2).lift (k := k) := by
  apply Subst.funext
  · intro x
    cases x with
    | here => rfl
    | there x0 =>
      conv =>
        lhs; simp only [Subst.comp, Subst.lift_there_var_eq]
      simp only [Subst.lift_there_var_eq]
      simp only [Var.weaken_subst_comm_base, Subst.comp]
  · intro X
    cases X with
    | here =>
      cases σ1
      cases σ2
      rfl
    | there x0 =>
      conv =>
        lhs; simp only [Subst.comp, Subst.lift_there_tvar_eq]
      simp only [Subst.lift_there_tvar_eq]
      simp only [PureTy.weaken_subst_comm_base, Subst.comp]
  · intro C
    cases C with
    | here =>
      change
        (CaptureSet.cvar (.M .epsilon) (BVar.here : BVar (s2,,.cvar) .cvar)).subst
            (σ2.lift (k := .cvar)) =
          CaptureSet.cvar (.M .epsilon) (BVar.here : BVar (s3,,.cvar) .cvar)
      rfl
    | there C0 =>
      simp only [Subst.comp, Subst.lift]
      exact CaptureSet.weaken_subst_comm_base.symm

/-- Composition of substitutions commutes with lifting many levels. -/
theorem Subst.comp_liftMany {σ1 : Subst s1 s2} {σ2 : Subst s2 s3} {K : Sig} :
  (σ1.liftMany K).comp (σ2.liftMany K) = (σ1.comp σ2).liftMany K := by
  induction K with
  | nil => rfl
  | cons k K ih =>
    simp only [Subst.liftMany]
    conv_rhs => rw [← ih]
    exact Subst.comp_lift

/-- Composition of substitutions commutes with lifting under `n` capture binders. -/
theorem Subst.comp_liftCVars {σ1 : Subst s1 s2} {σ2 : Subst s2 s3} {n : Nat} :
  (σ1.liftCVars n).comp (σ2.liftCVars n) = (σ1.comp σ2).liftCVars n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change ((σ1.liftCVars n).lift).comp ((σ2.liftCVars n).lift) = ((σ1.comp σ2).liftCVars n).lift
    rw [← ih]
    exact Subst.comp_lift

/-- Substituting a composition of substitutions is the same as
  substituting one after the other. -/
theorem Var.subst_comp {x : Var .var s1} {σ1 : Subst s1 s2} {σ2 : Subst s2 s3} :
  (x.subst σ1).subst σ2 = x.subst (σ1.comp σ2) := by
  cases x with
  | bound x => rfl
  | free n => rfl

/-- applyRO distributes over substitution. -/
theorem CaptureSet.applyRO_subst {cs : CaptureSet s1} {σ : Subst s1 s2} :
    cs.applyRO.subst σ = (cs.subst σ).applyRO := by
  induction cs with
  | empty => rfl
  | union cs1 cs2 ih1 ih2 =>
    simp only [CaptureSet.applyRO, CaptureSet.subst, ih1, ih2]
  | var _ x =>
    simp only [CaptureSet.applyRO, CaptureSet.subst]
  | cvar _ x =>
    simp only [CaptureSet.applyRO, CaptureSet.subst, CaptureSet.applyAccess_applyRO]

/-- applyMut distributes over substitution. -/
theorem CaptureSet.applyMut_subst {cs : CaptureSet s1} {σ : Subst s1 s2} {m : Mutability} :
    (cs.applyMut m).subst σ = (cs.subst σ).applyMut m := by
  cases m <;> simp only [CaptureSet.applyMut_epsilon, CaptureSet.applyMut_ro, applyRO_subst]

/-- applyDrop distributes over substitution. -/
theorem CaptureSet.applyDrop_subst {cs : CaptureSet s1} {σ : Subst s1 s2} :
    cs.applyDrop.subst σ = (cs.subst σ).applyDrop := by
  induction cs with
  | empty => rfl
  | union cs1 cs2 ih1 ih2 => simp only [CaptureSet.applyDrop, CaptureSet.subst, ih1, ih2]
  | var _ x => simp only [CaptureSet.applyDrop, CaptureSet.subst]
  | cvar _ x =>
    simp only [CaptureSet.applyDrop, CaptureSet.subst, CaptureSet.applyAccess_drop,
               CaptureSet.applyAccess_applyDrop]

/-- applyAccess distributes over substitution. -/
theorem CaptureSet.applyAccess_subst {cs : CaptureSet s1} {σ : Subst s1 s2} {a : Access} :
    (cs.applyAccess a).subst σ = (cs.subst σ).applyAccess a := by
  cases a with
  | M m => simp only [CaptureSet.applyAccess_M, applyMut_subst]
  | drop => simp only [CaptureSet.applyAccess_drop, applyDrop_subst]

/-- Substitution on capture sets distributes over composition of substitutions. -/
theorem CaptureSet.subst_comp {cs : CaptureSet s1} {σ1 : Subst s1 s2} {σ2 : Subst s2 s3} :
  (cs.subst σ1).subst σ2 = cs.subst (σ1.comp σ2) := by
  induction cs with
  | empty => rfl
  | union cs1 cs2 ih1 ih2 =>
    simp only [CaptureSet.subst, ih1, ih2]
  | var m x =>
    simp only [CaptureSet.subst]
    exact congrArg (CaptureSet.var m) Var.subst_comp
  | cvar m C =>
    simp only [CaptureSet.subst, Subst.comp, CaptureSet.applyAccess_subst]

theorem CaptureBound.subst_comp {cb : CaptureBound s1} {σ1 : Subst s1 s2} {σ2 : Subst s2 s3} :
  (cb.subst σ1).subst σ2 = cb.subst (σ1.comp σ2) := by
  cases cb with
  | unbound => rfl
  | bound cs => simp only [CaptureBound.subst, CaptureSet.subst_comp]

/-- Substitution on separation contexts distributes over composition of substitutions. -/
theorem SepCtx.subst_comp {K : SepCtx s1} {σ1 : Subst s1 s2} {σ2 : Subst s2 s3} :
  (K.subst σ1).subst σ2 = K.subst (σ1.comp σ2) := by
  induction K generalizing s2 s3 with
  | empty => rfl
  | cons K C ih =>
    simp only [SepCtx.subst, ih, CaptureSet.subst_comp]

theorem MutabilityCtx.subst_comp {K : MutabilityCtx s1} {σ1 : Subst s1 s2} {σ2 : Subst s2 s3} :
  (K.subst σ1).subst σ2 = K.subst (σ1.comp σ2) := by
  induction K generalizing s2 s3 with
  | empty => rfl
  | cons K C m ih =>
    simp only [MutabilityCtx.subst, ih, CaptureSet.subst_comp]

theorem ModalCtx.subst_comp {K : ModalCtx s1} {σ1 : Subst s1 s2} {σ2 : Subst s2 s3} :
  (K.subst σ1).subst σ2 = K.subst (σ1.comp σ2) := by
  cases K with
  | mk sep mu =>
    simp only [ModalCtx.subst, SepCtx.subst_comp, MutabilityCtx.subst_comp]

/-- Substitution on types distributes over composition of substitutions. -/
theorem Ty.subst_comp {T : Ty sort s1} {σ1 : Subst s1 s2} {σ2 : Subst s2 s3} :
  (T.subst σ1).subst σ2 = T.subst (σ1.comp σ2) := by
  induction T generalizing s2 s3 with
  | top => rfl
  | tvar x => rfl
  | arrow T1 cs T2 ih1 ih2 =>
    simp only [Ty.subst, ih1, ih2, CaptureSet.subst_comp]
    conv_rhs => rw [← Subst.comp_lift]
    rfl
  | poly T1 cs T2 ih1 ih2 =>
    simp only [Ty.subst, ih1, ih2, CaptureSet.subst_comp]
    conv_rhs => rw [← Subst.comp_lift]
    rfl
  | cpoly cb cs T ih =>
    simp only [Ty.subst, ih, CaptureBound.subst_comp, CaptureSet.subst_comp]
    conv_rhs => rw [← Subst.comp_lift]
    rfl
  | consumer T1 cs T2 ih1 ih2 =>
    simp only [Ty.subst, ih1, ih2, CaptureSet.subst_comp]
  | modal cs Ψ T ih =>
    simp only [Ty.subst, CaptureSet.subst_comp, ih, ModalCtx.subst_comp]
  | unit => rfl
  | cap cs => simp only [Ty.subst, CaptureSet.subst_comp]
  | bool => rfl
  | cell cs T ih => simp only [Ty.subst, CaptureSet.subst_comp, ih]
  | reader cs T ih => simp only [Ty.subst, CaptureSet.subst_comp, ih]
  | exi n T ih =>
    simp only [Ty.subst, ih]
    conv_rhs => rw [← Subst.comp_liftCVars]
  | typ T ih =>
    simp only [Ty.subst, ih]

/-- Substitution on pure types distributes over composition of substitutions. -/
theorem PureTy.subst_comp {T : PureTy s1} {σ1 : Subst s1 s2} {σ2 : Subst s2 s3} :
  (T.subst σ1).subst σ2 = T.subst (σ1.comp σ2) := by
  simp only [PureTy.subst, Ty.subst_comp]

/-- Substitution on terms distributes over composition of substitutions. -/
theorem Exp.subst_comp {e : Exp s1} {σ1 : Subst s1 s2} {σ2 : Subst s2 s3} :
  (e.subst σ1).subst σ2 = e.subst (σ1.comp σ2) := by
  induction e generalizing s2 s3 with
  | var x => simp only [Exp.subst, Var.subst_comp]
  | abs cs T e ih_e =>
    simp only [Exp.subst, CaptureSet.subst_comp, Ty.subst_comp, ih_e]
    conv_rhs => rw [← Subst.comp_lift]
    rfl
  | tabs cs T e ih_e =>
    simp only [Exp.subst, CaptureSet.subst_comp, PureTy.subst_comp, ih_e]
    conv_rhs => rw [← Subst.comp_lift]
    rfl
  | cabs cs cb e ih_e =>
    simp only [Exp.subst, CaptureSet.subst_comp, CaptureBound.subst_comp, ih_e]
    conv_rhs => rw [← Subst.comp_lift]
    rfl
  | consumer cs T e ih_e =>
    simp only [Exp.subst, CaptureSet.subst_comp, Ty.subst_comp, ih_e]
    conv_rhs => rw [← Subst.comp_lift, ← Subst.comp_lift]
    rfl
  | boxed cs Ψ e ih_e =>
    simp only [Exp.subst, CaptureSet.subst_comp, ModalCtx.subst_comp, ih_e]
  | reader x => simp only [Exp.subst, Var.subst_comp]
  | alloc x => simp only [Exp.subst, Var.subst_comp]
  | drop x => simp only [Exp.subst, Var.subst_comp]
  | pack css x =>
    simp only [Exp.subst, Var.subst_comp]
    congr 1
    apply List.Vector.toList_injective
    simp only [List.Vector.toList_map, List.map_map, Function.comp_def, CaptureSet.subst_comp]
  | app x y => simp only [Exp.subst, Var.subst_comp]
  | tapp x T => simp only [Exp.subst, Var.subst_comp, PureTy.subst_comp]
  | capp x cs =>
    simp only [Exp.subst, Var.subst_comp, CaptureSet.subst_comp]
  | unwrap x =>
    simp only [Exp.subst, Var.subst_comp]
  | letin e1 e2 ih1 ih2 =>
    simp only [Exp.subst, ih1, ih2]
    conv_rhs => rw [← Subst.comp_lift]
    rfl
  | unpack n e1 e2 ih1 ih2 =>
    simp only [Exp.subst, ih1, ih2]
    conv_rhs => rw [← Subst.comp_liftCVars, ← Subst.comp_lift]
    rfl
  | unit => rfl
  | btrue => rfl
  | bfalse => rfl
  | read x => simp only [Exp.subst, Var.subst_comp]
  | write x y => simp only [Exp.subst, Var.subst_comp]
  | cond x e2 e3 ih2 ih3 =>
    simp only [Exp.subst, Var.subst_comp, ih2, ih3]
  | par C1 C2 e1 e2 ih1 ih2 =>
    simp only [Exp.subst, CaptureSet.subst_comp, ih1, ih2]

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
    simp only [CaptureSet.subst, ih1, ih2]
  | var m x =>
    simp only [CaptureSet.subst, Var.subst_id]
  | cvar m C =>
    cases m with
    | M m =>
      cases m <;> simp only [
        CaptureSet.subst,
        Subst.id,
        CaptureSet.applyAccess_M,
        Access.applyRO,
        CaptureSet.applyRO_cvar,
        CaptureSet.applyMut_epsilon,
        CaptureSet.applyMut_ro
      ]
    | drop =>
      simp only [CaptureSet.subst, Subst.id, CaptureSet.applyAccess_drop, CaptureSet.applyDrop]

/-- Lifting the identity substitution yields the identity. -/
theorem Subst.lift_id :
  (Subst.id (s:=s)).lift (k:=k) = Subst.id := by
  apply Subst.funext
  · intro x
    cases x <;> rfl
  · intro X
    cases X <;> rfl
  · intro C
    cases C <;> rfl

/-- Lifting the identity substitution under `n` capture binders yields the identity. -/
theorem Subst.liftCVars_id {n : Nat} :
  (Subst.id (s:=s)).liftCVars n = Subst.id := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change ((Subst.id (s:=s)).liftCVars n).lift = Subst.id
    rw [ih]
    exact Subst.lift_id

theorem CaptureBound.subst_id {cb : CaptureBound s} :
  cb.subst Subst.id = cb := by
  cases cb with
  | unbound => rfl
  | bound cs => simp only [CaptureBound.subst, CaptureSet.subst_id]

/-- Substituting with the identity substitution leaves a separation context unchanged. -/
theorem SepCtx.subst_id {K : SepCtx s} :
  K.subst Subst.id = K := by
  induction K with
  | empty => rfl
  | cons K C ih =>
    simp only [SepCtx.subst, ih, CaptureSet.subst_id]

theorem MutabilityCtx.subst_id {K : MutabilityCtx s} :
  K.subst Subst.id = K := by
  induction K with
  | empty => rfl
  | cons K C m ih =>
    simp only [MutabilityCtx.subst, ih, CaptureSet.subst_id]

theorem ModalCtx.subst_id {K : ModalCtx s} :
  K.subst Subst.id = K := by
  cases K with
  | mk sep mu =>
    simp only [ModalCtx.subst, SepCtx.subst_id, MutabilityCtx.subst_id]

/-- Substituting with the identity substitution leaves a type unchanged. -/
theorem Ty.subst_id {T : Ty sort s} :
  T.subst Subst.id = T := by
  induction T with
  | top => simp only [Ty.subst]
  | tvar x => simp only [Ty.subst, Subst.id, PureTy.tvar]
  | arrow T1 cs T2 ih1 ih2 =>
    simp only [Ty.subst, ih1, CaptureSet.subst_id]
    conv_lhs => rw [Subst.lift_id]
    exact congrArg (Ty.arrow T1 cs) ih2
  | poly T1 cs T2 ih1 ih2 =>
    simp only [Ty.subst, ih1, CaptureSet.subst_id]
    conv_lhs => rw [Subst.lift_id]
    exact congrArg (Ty.poly T1 cs) ih2
  | cpoly cb cs T ih =>
    simp only [Ty.subst, CaptureBound.subst_id, CaptureSet.subst_id]
    conv_lhs => rw [Subst.lift_id]
    exact congrArg (Ty.cpoly cb cs) ih
  | consumer T1 cs T2 ih1 ih2 =>
    simp only [Ty.subst, ih1, ih2, CaptureSet.subst_id]
  | modal cs Ψ T ih =>
    simp only [Ty.subst, CaptureSet.subst_id, ih, ModalCtx.subst_id]
  | unit => simp only [Ty.subst]
  | cap cs => simp only [Ty.subst, CaptureSet.subst_id]
  | bool => simp only [Ty.subst]
  | cell cs T ih => simp only [Ty.subst, CaptureSet.subst_id, ih]
  | reader cs T ih => simp only [Ty.subst, CaptureSet.subst_id, ih]
  | exi n T ih =>
    simp only [Ty.subst]
    conv_lhs => rw [Subst.liftCVars_id]
    exact congrArg (Ty.exi n) ih
  | typ T ih =>
    simp only [Ty.subst, ih]

/-- Substituting with the identity substitution leaves a pure type unchanged. -/
theorem PureTy.subst_id {T : PureTy s} :
  T.subst Subst.id = T := by
  simp only [PureTy.subst, Ty.subst_id]

/-- Substituting with the identity substitution leaves an expression unchanged. -/
theorem Exp.subst_id {e : Exp s} :
  e.subst Subst.id = e := by
  induction e with
  | var x =>
    simp only [Exp.subst, Var.subst_id]
  | abs cs T e ih =>
    simp only [Exp.subst, CaptureSet.subst_id, Ty.subst_id]
    conv_lhs => rw [Subst.lift_id]
    exact congrArg (Exp.abs cs T) ih
  | tabs cs T e ih =>
    simp only [Exp.subst, CaptureSet.subst_id, PureTy.subst_id]
    conv_lhs => rw [Subst.lift_id]
    exact congrArg (Exp.tabs cs T) ih
  | cabs cs cb e ih =>
    simp only [Exp.subst, CaptureSet.subst_id, CaptureBound.subst_id]
    conv_lhs => rw [Subst.lift_id]
    exact congrArg (Exp.cabs cs cb) ih
  | consumer cs T e ih =>
    simp only [Exp.subst, CaptureSet.subst_id, Ty.subst_id]
    conv_lhs => rw [Subst.lift_id, Subst.lift_id]
    exact congrArg (Exp.consumer cs T) ih
  | boxed cs Ψ e ih =>
    simp only [Exp.subst, CaptureSet.subst_id, ModalCtx.subst_id, ih]
  | reader x =>
    simp only [Exp.subst, Var.subst_id]
  | alloc x =>
    simp only [Exp.subst, Var.subst_id]
  | drop x =>
    simp only [Exp.subst, Var.subst_id]
  | pack css x =>
    simp only [Exp.subst, Var.subst_id]
    congr 1
    apply List.Vector.toList_injective
    simp only [List.Vector.toList_map, CaptureSet.subst_id, List.map_id']
  | app x y =>
    simp only [Exp.subst, Var.subst_id]
  | tapp x T =>
    simp only [Exp.subst, Var.subst_id, PureTy.subst_id]
  | capp x cs =>
    simp only [Exp.subst, Var.subst_id, CaptureSet.subst_id]
  | unwrap x =>
    simp only [Exp.subst, Var.subst_id]
  | letin e1 e2 ih1 ih2 =>
    simp only [Exp.subst, ih1]
    conv_lhs => rw [Subst.lift_id]
    exact congrArg (Exp.letin e1) ih2
  | unpack n e1 e2 ih1 ih2 =>
    simp only [Exp.subst, ih1]
    conv_lhs => rw [Subst.liftCVars_id, Subst.lift_id]
    exact congrArg (Exp.unpack n e1) ih2
  | unit =>
    rfl
  | btrue => rfl
  | bfalse => rfl
  | read x =>
    simp only [Exp.subst, Var.subst_id]
  | write x y =>
    simp only [Exp.subst, Var.subst_id]
  | cond x e2 e3 ih2 ih3 =>
    simp only [Exp.subst, Var.subst_id, ih2, ih3]
  | par C1 C2 e1 e2 ih1 ih2 =>
    simp only [Exp.subst, CaptureSet.subst_id, ih1, ih2]


/-- Converts a renaming to a substitution. -/
def Rename.asSubst (f : Rename s1 s2) : Subst s1 s2 where
  var := fun x => .bound (f.var x)
  tvar := fun X => PureTy.tvar (f.var X)
  cvar := fun C => .cvar (.M .epsilon) (f.var C)

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
  · intro C
    cases C
    · rfl
    · rfl

/-- Lifting a renaming under `n` capture binders and converting to a substitution is the same as
  converting and then lifting the substitution under `n` capture binders. -/
theorem Rename.asSubst_liftCVars {f : Rename s1 s2} {n : Nat} :
  (f.liftCVars n).asSubst = (f.asSubst).liftCVars n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change ((f.liftCVars n).lift).asSubst = ((f.asSubst).liftCVars n).lift
    rw [← ih]
    exact Rename.asSubst_lift

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
    simp only [CaptureSet.subst, CaptureSet.rename, ih1, ih2]
  | var m x =>
    simp only [CaptureSet.subst, CaptureSet.rename, Var.subst_asSubst]
  | cvar m C =>
    cases m with
    | M m =>
      cases m <;> simp only [
        CaptureSet.subst,
        CaptureSet.rename,
        Rename.asSubst,
        CaptureSet.applyAccess_M,
        Access.applyRO,
        CaptureSet.applyRO_cvar,
        CaptureSet.applyMut_epsilon,
        CaptureSet.applyMut_ro
      ]
    | drop =>
      simp only [
        CaptureSet.subst,
        CaptureSet.rename,
        Rename.asSubst,
        CaptureSet.applyAccess_drop,
        CaptureSet.applyDrop
      ]

theorem CaptureBound.subst_asSubst {cb : CaptureBound s1} {f : Rename s1 s2} :
  cb.subst (f.asSubst) = cb.rename f := by
  cases cb with
  | unbound => rfl
  | bound cs => simp only [CaptureBound.subst, CaptureBound.rename, CaptureSet.subst_asSubst]

theorem SepCtx.subst_asSubst {K : SepCtx s1} {f : Rename s1 s2} :
  K.subst (f.asSubst) = K.rename f := by
  induction K generalizing s2 with
  | empty => rfl
  | cons K C ih =>
    simp only [SepCtx.subst, SepCtx.rename, ih, CaptureSet.subst_asSubst]

theorem MutabilityCtx.subst_asSubst {K : MutabilityCtx s1} {f : Rename s1 s2} :
  K.subst (f.asSubst) = K.rename f := by
  induction K generalizing s2 with
  | empty => rfl
  | cons K C m ih =>
    simp only [MutabilityCtx.subst, MutabilityCtx.rename, ih, CaptureSet.subst_asSubst]

theorem ModalCtx.subst_asSubst {K : ModalCtx s1} {f : Rename s1 s2} :
  K.subst (f.asSubst) = K.rename f := by
  cases K with
  | mk sep mu =>
    simp only [ModalCtx.subst, ModalCtx.rename, SepCtx.subst_asSubst, MutabilityCtx.subst_asSubst]

/-- Substituting a substitution lifted from a renaming is the same as renaming. -/
theorem Ty.subst_asSubst {T : Ty sort s1} {f : Rename s1 s2} :
  T.subst (f.asSubst) = T.rename f := by
  induction T generalizing s2 with
  | top => rfl
  | tvar x => simp only [Ty.subst, Ty.rename, Rename.asSubst, PureTy.tvar]
  | arrow T1 cs T2 ih1 ih2 =>
    simp only [Ty.subst, Ty.rename, ih1, CaptureSet.subst_asSubst]
    rw [← Rename.asSubst_lift]
    exact congrArg (Ty.arrow (T1.rename f) (cs.rename f)) ih2
  | poly T1 cs T2 ih1 ih2 =>
    simp only [Ty.subst, Ty.rename, ih1, CaptureSet.subst_asSubst]
    rw [← Rename.asSubst_lift]
    exact congrArg (Ty.poly (T1.rename f) (cs.rename f)) ih2
  | cpoly cb cs T ih =>
    simp only [Ty.subst, Ty.rename, CaptureBound.subst_asSubst, CaptureSet.subst_asSubst]
    rw [← Rename.asSubst_lift]
    exact congrArg (Ty.cpoly (cb.rename f) (cs.rename f)) ih
  | consumer T1 cs T2 ih1 ih2 =>
    simp only [Ty.subst, Ty.rename, CaptureSet.subst_asSubst, ih1, ih2]
  | modal cs Ψ T ih =>
    simp only [Ty.subst, Ty.rename, CaptureSet.subst_asSubst, ih, ModalCtx.subst_asSubst]
  | unit => simp only [Ty.subst, Ty.rename]
  | cap cs => simp only [Ty.subst, Ty.rename, CaptureSet.subst_asSubst]
  | bool => simp only [Ty.subst, Ty.rename]
  | cell cs T ih => simp only [Ty.subst, Ty.rename, CaptureSet.subst_asSubst, ih]
  | reader cs T ih => simp only [Ty.subst, Ty.rename, CaptureSet.subst_asSubst, ih]
  | exi n T ih =>
    simp only [Ty.subst, Ty.rename]
    rw [← Rename.asSubst_liftCVars]
    exact congrArg (Ty.exi n) ih
  | typ T ih =>
    simp only [Ty.subst, Ty.rename, ih]

/-- Substituting a substitution lifted from a renaming is the same as renaming for pure types. -/
theorem PureTy.subst_asSubst {T : PureTy s1} {f : Rename s1 s2} :
  T.subst (f.asSubst) = T.rename f := by
  simp only [PureTy.subst, PureTy.rename, Ty.subst_asSubst]

/-- Substituting a substitution lifted from a renaming is the same as renaming. -/
theorem Exp.subst_asSubst {e : Exp s1} {f : Rename s1 s2} :
  e.subst (f.asSubst) = e.rename f := by
  induction e generalizing s2 with
  | var x =>
    simp only [Exp.subst, Exp.rename, Var.subst_asSubst]
  | abs cs T e ih =>
    simp only [Exp.subst, Exp.rename, CaptureSet.subst_asSubst, Ty.subst_asSubst]
    rw [← Rename.asSubst_lift]
    exact congrArg (Exp.abs (cs.rename f) (T.rename f)) ih
  | tabs cs T e ih =>
    simp only [Exp.subst, Exp.rename, CaptureSet.subst_asSubst, PureTy.subst_asSubst]
    rw [← Rename.asSubst_lift]
    exact congrArg (Exp.tabs (cs.rename f) (T.rename f)) ih
  | cabs cs cb e ih =>
    simp only [Exp.subst, Exp.rename, CaptureSet.subst_asSubst, CaptureBound.subst_asSubst]
    rw [← Rename.asSubst_lift]
    exact congrArg (Exp.cabs (cs.rename f) (cb.rename f)) ih
  | consumer cs T e ih =>
    simp only [Exp.subst, Exp.rename, CaptureSet.subst_asSubst, Ty.subst_asSubst]
    rw [← Rename.asSubst_lift, ← Rename.asSubst_lift]
    exact congrArg (Exp.consumer (cs.rename f) (T.rename f)) ih
  | boxed cs Ψ e ih =>
    simp only [Exp.subst, Exp.rename, CaptureSet.subst_asSubst, ModalCtx.subst_asSubst, ih]
  | reader x =>
    simp only [Exp.subst, Exp.rename, Var.subst_asSubst]
  | alloc x =>
    simp only [Exp.subst, Exp.rename, Var.subst_asSubst]
  | drop x =>
    simp only [Exp.subst, Exp.rename, Var.subst_asSubst]
  | pack css x =>
    simp only [Exp.subst, Exp.rename, Var.subst_asSubst]
    congr 1
    apply List.Vector.toList_injective
    simp only [List.Vector.toList_map, CaptureSet.subst_asSubst]
  | app x y =>
    simp only [Exp.subst, Exp.rename, Var.subst_asSubst]
  | tapp x T =>
    simp only [Exp.subst, Exp.rename, Var.subst_asSubst, PureTy.subst_asSubst]
  | capp x cs =>
    simp only [Exp.subst, Exp.rename, Var.subst_asSubst, CaptureSet.subst_asSubst]
  | unwrap x =>
    simp only [Exp.subst, Exp.rename, Var.subst_asSubst]
  | letin e1 e2 ih1 ih2 =>
    simp only [Exp.subst, Exp.rename, ih1]
    rw [← Rename.asSubst_lift]
    exact congrArg (Exp.letin (e1.rename f)) ih2
  | unpack n e1 e2 ih1 ih2 =>
    simp only [Exp.subst, Exp.rename, ih1]
    rw [← Rename.asSubst_liftCVars, ← Rename.asSubst_lift]
    exact congrArg (Exp.unpack n (e1.rename f)) ih2
  | unit =>
    rfl
  | btrue =>
    rfl
  | bfalse =>
    rfl
  | read x =>
    simp only [Exp.subst, Exp.rename, Var.subst_asSubst]
  | write x y =>
    simp only [Exp.subst, Exp.rename, Var.subst_asSubst]
  | cond x e2 e3 ih2 ih3 =>
    simp only [Exp.subst, Exp.rename, Var.subst_asSubst, ih2, ih3]
  | par C1 C2 e1 e2 ih1 ih2 =>
    simp only [Exp.subst, Exp.rename, CaptureSet.subst_asSubst, ih1, ih2]

theorem Subst.weaken_openVar {z : Var .var s} :
  Rename.succ.asSubst.comp (Subst.openVar z) = Subst.id := by
  apply Subst.funext
  · intro x; rfl
  · intro X; rfl
  · intro C; rfl

theorem Subst.weaken_openTVar {U : PureTy s} :
  Rename.succ.asSubst.comp (Subst.openTVar U) = Subst.id := by
  apply Subst.funext
  · intro x; rfl
  · intro X; rfl
  · intro C; rfl

theorem Subst.weaken_openCVar {C : CaptureSet s} :
  Rename.succ.asSubst.comp (Subst.openCVar C) = Subst.id := by
  apply Subst.funext
  · intro x; rfl
  · intro X; rfl
  · intro C; rfl

theorem CaptureSet.weaken_openVar {C : CaptureSet (s)} {z : Var .var s} :
  (C.rename Rename.succ).subst (Subst.openVar z) = C := by
  calc (C.rename Rename.succ).subst (Subst.openVar z)
      = (C.subst Rename.succ.asSubst).subst (Subst.openVar z) := by rw [<-CaptureSet.subst_asSubst]
    _ = C.subst (Rename.succ.asSubst.comp (Subst.openVar z)) := by rw [CaptureSet.subst_comp]
    _ = C.subst Subst.id := by rw [Subst.weaken_openVar]
    _ = C := by rw [CaptureSet.subst_id]

theorem CaptureSet.weaken_openTVar {C : CaptureSet (s)} {U : PureTy s} :
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
    simp only [CaptureSet.rename]
    rw [ih1, ih2]
  | var m x =>
    cases x with
    | bound bx => cases bx
    | free n =>
      simp only [CaptureSet.rename, Var.rename]
  | cvar m c => cases c

theorem CaptureSet.ground_subst_invariant {C : CaptureSet {}} :
  C.subst σ = C := by
  induction C with
  | empty => rfl
  | union cs1 cs2 ih1 ih2 =>
    simp only [CaptureSet.subst]
    rw [ih1, ih2]
  | var m x =>
    cases x with
    | bound bx => cases bx
    | free n => simp only [CaptureSet.subst, Var.subst]
  | cvar m c => cases c

/-- A substitution is closed if all its images are closed. -/
structure Subst.IsClosed (σ : Subst s1 s2) : Prop where
  var_closed : ∀ x, (σ.var x).IsClosed
  tvar_closed : ∀ X, (σ.tvar X).IsClosed
  cvar_closed : ∀ C, (σ.cvar C).IsClosed

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
    simp only [CaptureSet.subst]
    exact IsClosed.union (ih1 h1) (ih2 h2)
  | cvar m C =>
    simp only [CaptureSet.subst]
    exact CaptureSet.applyAccess_isClosed (hsubst.cvar_closed C)
  | var m x =>
    cases hc with | var_bound =>
    rename_i bx
    simp only [CaptureSet.subst, Var.subst]
    generalize h_eq : σ.var bx = v
    have h_var : v.IsClosed := h_eq ▸ hsubst.var_closed bx
    cases v with
    | bound y =>
      exact IsClosed.var_bound
    | free n =>
      cases h_var

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

private theorem SepCtx.rename_closed_any {Ψ : SepCtx s1} {f : Rename s1 s2}
  (hc : Ψ.IsClosed) : (Ψ.rename f).IsClosed := by
  induction Ψ with
  | empty => exact SepCtx.IsClosed.empty
  | cons Ψ C ih =>
    cases hc with
    | cons hΨ hC =>
      exact SepCtx.IsClosed.cons (ih hΨ) (CaptureSet.rename_closed_any hC)

private theorem MutabilityCtx.rename_closed_any {Ψ : MutabilityCtx s1} {f : Rename s1 s2}
  (hc : Ψ.IsClosed) : (Ψ.rename f).IsClosed := by
  induction Ψ with
  | empty => exact MutabilityCtx.IsClosed.empty
  | cons Ψ C m ih =>
    cases hc with
    | cons hΨ hC =>
      exact MutabilityCtx.IsClosed.cons (ih hΨ) (CaptureSet.rename_closed_any hC)

private theorem ModalCtx.rename_closed_any {Ψ : ModalCtx s1} {f : Rename s1 s2}
  (hc : Ψ.IsClosed) : (Ψ.rename f).IsClosed :=
  ⟨SepCtx.rename_closed_any hc.sep, MutabilityCtx.rename_closed_any hc.mutability⟩

private theorem CaptureBound.rename_closed_any {cb : CaptureBound s1} {f : Rename s1 s2}
  (hc : cb.IsClosed) : (cb.rename f).IsClosed := by
  cases hc with
  | unbound => exact CaptureBound.IsClosed.unbound
  | bound hcs => exact CaptureBound.IsClosed.bound (CaptureSet.rename_closed_any hcs)

private theorem Ty.rename_closed_any {T : Ty sort s1} {f : Rename s1 s2}
  (hc : T.IsClosed) : (T.rename f).IsClosed := by
  induction T generalizing s2 with
  | top => exact IsClosed.top
  | tvar => exact IsClosed.tvar
  | arrow T1 cs T2 ih1 ih2 =>
    cases hc with | arrow h1 hcs h2 =>
    exact IsClosed.arrow (ih1 h1)
      (CaptureSet.rename_closed_any hcs) (ih2 h2)
  | poly T1 cs T2 ih1 ih2 =>
    cases hc with | poly h1 hcs h2 =>
    exact IsClosed.poly (ih1 h1)
      (CaptureSet.rename_closed_any hcs) (ih2 h2)
  | cpoly cb cs T ih =>
    cases hc with | cpoly hcb hcs hT =>
    exact IsClosed.cpoly (CaptureBound.rename_closed_any hcb)
      (CaptureSet.rename_closed_any hcs) (ih hT)
  | consumer T1 cs T2 ih1 ih2 =>
    cases hc with | consumer h1 hcs h2 =>
    exact IsClosed.consumer (ih1 h1)
      (CaptureSet.rename_closed_any hcs) (ih2 h2)
  | modal cs Ψ T ih =>
    cases hc with | modal hcs hΨ hT =>
    exact IsClosed.modal (CaptureSet.rename_closed_any hcs)
      (ModalCtx.rename_closed_any hΨ) (ih hT)
  | unit => exact IsClosed.unit
  | cap cs =>
    cases hc with | cap hcs =>
    exact IsClosed.cap (CaptureSet.rename_closed_any hcs)
  | bool => exact IsClosed.bool
  | cell cs T ih =>
    cases hc with | cell hcs hT =>
    exact IsClosed.cell (CaptureSet.rename_closed_any hcs) (ih hT)
  | reader cs T ih =>
    cases hc with | reader hcs hT =>
    exact IsClosed.reader (CaptureSet.rename_closed_any hcs) (ih hT)
  | typ T ih =>
    cases hc with | typ hT =>
    exact IsClosed.typ (ih hT)
  | exi n T ih =>
    cases hc with | exi hT =>
    exact IsClosed.exi (ih hT)

/-- Lifting preserves closedness of substitutions. -/
theorem Subst.lift_closed {σ : Subst s1 s2} (hσ : σ.IsClosed) :
  (σ.lift (k:=k)).IsClosed := by
  constructor
  · intro x
    cases x with
    | here => exact Var.IsClosed.bound
    | there x => simp only [Subst.lift]; exact Var.rename_closed_any (hσ.var_closed x)
  · intro X
    cases X with
    | here => exact Ty.IsClosed.tvar
    | there X => simp only [Subst.lift]; exact Ty.rename_closed_any (hσ.tvar_closed X)
  · intro C
    cases C with
    | here => exact CaptureSet.IsClosed.cvar
    | there C => simp only [Subst.lift]; exact CaptureSet.rename_closed_any (hσ.cvar_closed C)

/-- Lifting under `n` capture binders preserves closedness of substitutions. -/
theorem Subst.liftCVars_closed {σ : Subst s1 s2} (hσ : σ.IsClosed) {n : Nat} :
  (σ.liftCVars n).IsClosed := by
  induction n with
  | zero => exact hσ
  | succ n ih => exact Subst.lift_closed ih

/-- Substitution preserves closedness for separation contexts. -/
def SepCtx.is_closed_subst {Ψ : SepCtx s1} {σ : Subst s1 s2}
  (hc : Ψ.IsClosed) (hsubst : Subst.IsClosed σ) :
  (Ψ.subst σ).IsClosed := by
  induction Ψ generalizing s2 with
  | empty => exact SepCtx.IsClosed.empty
  | cons Ψ C ih =>
    cases hc with
    | cons hΨ hC =>
      simp only [SepCtx.subst]
      exact SepCtx.IsClosed.cons (ih hΨ hsubst) (CaptureSet.is_closed_subst hC hsubst)

/-- Substitution preserves closedness for mutability contexts. -/
def MutabilityCtx.is_closed_subst {Ψ : MutabilityCtx s1} {σ : Subst s1 s2}
  (hc : Ψ.IsClosed) (hsubst : Subst.IsClosed σ) :
  (Ψ.subst σ).IsClosed := by
  induction Ψ generalizing s2 with
  | empty => exact MutabilityCtx.IsClosed.empty
  | cons Ψ C m ih =>
    cases hc with
    | cons hΨ hC =>
      simp only [MutabilityCtx.subst]
      exact MutabilityCtx.IsClosed.cons (ih hΨ hsubst) (CaptureSet.is_closed_subst hC hsubst)

/-- Substitution preserves closedness for modal contexts. -/
def ModalCtx.is_closed_subst {Ψ : ModalCtx s1} {σ : Subst s1 s2}
  (hc : Ψ.IsClosed) (hsubst : Subst.IsClosed σ) :
  (Ψ.subst σ).IsClosed :=
  ⟨SepCtx.is_closed_subst hc.sep hsubst, MutabilityCtx.is_closed_subst hc.mutability hsubst⟩

def CaptureBound.is_closed_subst {cb : CaptureBound s1} {σ : Subst s1 s2}
  (hc : cb.IsClosed) (hsubst : Subst.IsClosed σ) :
  (cb.subst σ).IsClosed := by
  cases hc with
  | unbound =>
    simp only [CaptureBound.subst]
    exact CaptureBound.IsClosed.unbound
  | bound hcs =>
    simp only [CaptureBound.subst]
    exact CaptureBound.IsClosed.bound (CaptureSet.is_closed_subst hcs hsubst)

/-- Substitution preserves closedness for types. -/
def Ty.is_closed_subst {T : Ty sort s1} {σ : Subst s1 s2}
  (hc : T.IsClosed) (hsubst : Subst.IsClosed σ) :
  (T.subst σ).IsClosed := by
  induction T generalizing s2 with
  | top => exact IsClosed.top
  | tvar X => simp only [Ty.subst]; exact hsubst.tvar_closed X
  | arrow T1 cs T2 ih1 ih2 =>
    cases hc with | arrow h1 hcs h2 =>
    simp only [Ty.subst]
    exact IsClosed.arrow (ih1 h1 hsubst)
      (CaptureSet.is_closed_subst hcs hsubst) (ih2 h2 (Subst.lift_closed hsubst))
  | poly T1 cs T2 ih1 ih2 =>
    cases hc with | poly h1 hcs h2 =>
    simp only [Ty.subst]
    exact IsClosed.poly (ih1 h1 hsubst)
      (CaptureSet.is_closed_subst hcs hsubst) (ih2 h2 (Subst.lift_closed hsubst))
  | cpoly cb cs T ih =>
    cases hc with | cpoly hcb hcs hT =>
    simp only [Ty.subst]
    exact IsClosed.cpoly (CaptureBound.is_closed_subst hcb hsubst)
      (CaptureSet.is_closed_subst hcs hsubst) (ih hT (Subst.lift_closed hsubst))
  | consumer T1 cs T2 ih1 ih2 =>
    cases hc with | consumer h1 hcs h2 =>
    simp only [Ty.subst]
    exact IsClosed.consumer (ih1 h1 hsubst)
      (CaptureSet.is_closed_subst hcs hsubst) (ih2 h2 hsubst)
  | modal cs Ψ T ih =>
    cases hc with | modal hcs hΨ hT =>
    simp only [Ty.subst]
    exact IsClosed.modal
      (CaptureSet.is_closed_subst hcs hsubst)
      (ModalCtx.is_closed_subst hΨ hsubst) (ih hT hsubst)
  | unit => exact IsClosed.unit
  | cap cs =>
    cases hc with | cap hcs =>
    simp only [Ty.subst]
    exact IsClosed.cap (CaptureSet.is_closed_subst hcs hsubst)
  | bool => exact IsClosed.bool
  | cell cs T ih =>
    cases hc with | cell hcs hT =>
    simp only [Ty.subst]
    exact IsClosed.cell (CaptureSet.is_closed_subst hcs hsubst) (ih hT hsubst)
  | reader cs T ih =>
    cases hc with | reader hcs hT =>
    simp only [Ty.subst]
    exact IsClosed.reader (CaptureSet.is_closed_subst hcs hsubst) (ih hT hsubst)
  | typ T ih =>
    cases hc with | typ hT =>
    simp only [Ty.subst]
    exact IsClosed.typ (ih hT hsubst)
  | exi n T ih =>
    cases hc with | exi hT =>
    simp only [Ty.subst]
    exact IsClosed.exi (ih hT (Subst.liftCVars_closed hsubst))

/-- Substitution preserves closedness for expressions. -/
def Exp.is_closed_subst {e : Exp s1} {σ : Subst s1 s2}
  (hc : e.IsClosed) (hsubst : Subst.IsClosed σ) :
  (e.subst σ).IsClosed := by
  induction e generalizing s2 with
  | var x =>
    cases hc with | var hx =>
    simp only [Exp.subst]
    constructor
    exact Var.is_closed_subst hx hsubst
  | abs cs T e ih =>
    cases hc with | abs hcs hT he =>
    simp only [Exp.subst]
    constructor
    · exact CaptureSet.is_closed_subst hcs hsubst
    · exact Ty.is_closed_subst hT hsubst
    · exact ih he (Subst.lift_closed hsubst)
  | tabs cs S e ih =>
    cases hc with | tabs hcs hS he =>
    simp only [Exp.subst]
    constructor
    · exact CaptureSet.is_closed_subst hcs hsubst
    · exact Ty.is_closed_subst hS hsubst
    · exact ih he (Subst.lift_closed hsubst)
  | cabs cs cb e ih =>
    cases hc with | cabs hcs hcb he =>
    simp only [Exp.subst]
    constructor
    · exact CaptureSet.is_closed_subst hcs hsubst
    · exact CaptureBound.is_closed_subst hcb hsubst
    · exact ih he (Subst.lift_closed hsubst)
  | consumer cs T e ih =>
    cases hc with | consumer hcs hT he =>
    simp only [Exp.subst]
    exact IsClosed.consumer
      (CaptureSet.is_closed_subst hcs hsubst)
      (Ty.is_closed_subst hT hsubst)
      (ih he (Subst.lift_closed (Subst.lift_closed hsubst)))
  | boxed cs Ψ e ih =>
    cases hc with | boxed hcs hΨ he =>
    simp only [Exp.subst]
    exact IsClosed.boxed (CaptureSet.is_closed_subst hcs hsubst)
      (ModalCtx.is_closed_subst hΨ hsubst) (ih he hsubst)
  | reader x =>
    cases hc with | reader hx =>
    simp only [Exp.subst]
    exact IsClosed.reader (Var.is_closed_subst hx hsubst)
  | alloc x =>
    cases hc with | alloc hx =>
    simp only [Exp.subst]
    exact IsClosed.alloc (Var.is_closed_subst hx hsubst)
  | drop x =>
    cases hc with | drop hx =>
    simp only [Exp.subst]
    exact IsClosed.drop (Var.is_closed_subst hx hsubst)
  | pack css x =>
    cases hc with | pack hcs hx =>
    simp only [Exp.subst]
    refine IsClosed.pack ?_ (Var.is_closed_subst hx hsubst)
    intro cs hmem
    simp only [List.Vector.toList_map, List.mem_map] at hmem
    obtain ⟨c, hc_mem, rfl⟩ := hmem
    exact CaptureSet.is_closed_subst (hcs c hc_mem) hsubst
  | app x y =>
    cases hc with | app hx hy =>
    simp only [Exp.subst]
    constructor
    · exact Var.is_closed_subst hx hsubst
    · exact Var.is_closed_subst hy hsubst
  | tapp x T =>
    cases hc with | tapp hx hT =>
    simp only [Exp.subst]
    constructor
    · exact Var.is_closed_subst hx hsubst
    · exact Ty.is_closed_subst hT hsubst
  | capp x cs =>
    cases hc with | capp hx hcs =>
    simp only [Exp.subst]
    constructor
    · exact Var.is_closed_subst hx hsubst
    · exact CaptureSet.is_closed_subst hcs hsubst
  | unwrap x =>
    cases hc with | unwrap hx =>
    simp only [Exp.subst]
    exact IsClosed.unwrap (Var.is_closed_subst hx hsubst)
  | letin e1 e2 ih1 ih2 =>
    cases hc with | letin he1 he2 =>
    simp only [Exp.subst]
    constructor
    · exact ih1 he1 hsubst
    · exact ih2 he2 (Subst.lift_closed hsubst)
  | unpack n e1 e2 ih1 ih2 =>
    cases hc with | unpack he1 he2 =>
    simp only [Exp.subst]
    constructor
    · exact ih1 he1 hsubst
    · exact ih2 he2 (Subst.lift_closed (Subst.liftCVars_closed hsubst))
  | unit =>
    exact IsClosed.unit
  | btrue =>
    exact IsClosed.btrue
  | bfalse =>
    exact IsClosed.bfalse
  | read x =>
    cases hc with | read hx =>
    simp only [Exp.subst]
    exact IsClosed.read (Var.is_closed_subst hx hsubst)
  | write x y =>
    cases hc with | write hx hy =>
    simp only [Exp.subst]
    exact IsClosed.write (Var.is_closed_subst hx hsubst) (Var.is_closed_subst hy hsubst)
  | cond x e2 e3 ih2 ih3 =>
    cases hc with | cond hx h2 h3 =>
    simp only [Exp.subst]
    exact IsClosed.cond (Var.is_closed_subst hx hsubst) (ih2 h2 hsubst) (ih3 h3 hsubst)
  | par C1 C2 e1 e2 ih1 ih2 =>
    cases hc with | par hc1 hc2 h1 h2 =>
    simp only [Exp.subst]
    exact IsClosed.par (CaptureSet.is_closed_subst hc1 hsubst)
      (CaptureSet.is_closed_subst hc2 hsubst) (ih1 h1 hsubst) (ih2 h2 hsubst)

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
  cvar_closed := fun C => by
    cases C with
    | there C => exact CaptureSet.IsClosed.cvar

/-- The openTVar substitution is closed if the type is closed. -/
theorem Subst.openTVar_is_closed {U : PureTy s}
  (hU : U.IsClosed) :
  (Subst.openTVar U).IsClosed where
  var_closed := fun x => by
    cases x with
    | there x => exact Var.IsClosed.bound
  tvar_closed := fun X => by
    cases X with
    | here => exact hU
    | there X => exact Ty.IsClosed.tvar
  cvar_closed := fun C => by
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
  cvar_closed := fun c => by
    cases c with
    | here => exact hC
    | there c => exact CaptureSet.IsClosed.cvar

/-- If the result of substitution is closed, the original variable was closed. -/
theorem Var.subst_closed_inv {x : Var .var s1} {σ : Subst s1 s2}
  (hclosed : (x.subst σ).IsClosed) :
  x.IsClosed := by
  cases x with
  | bound bx => constructor
  | free n =>
    simp only [Var.subst] at hclosed
    cases hclosed

/-- If the result of substitution is closed, the original capture set was closed. -/
theorem CaptureSet.subst_closed_inv {cs : CaptureSet s1} {σ : Subst s1 s2}
  (hclosed : (cs.subst σ).IsClosed) :
  cs.IsClosed := by
  induction cs with
  | empty => exact IsClosed.empty
  | union cs1 cs2 ih1 ih2 =>
    simp only [CaptureSet.subst] at hclosed
    cases hclosed with | union h1 h2 =>
    exact IsClosed.union (ih1 h1) (ih2 h2)
  | cvar m C => exact IsClosed.cvar
  | var m x =>
    cases x with
    | bound bx =>
      exact IsClosed.var_bound
    | free n =>
      simp only [CaptureSet.subst, Var.subst] at hclosed
      cases hclosed

theorem SepCtx.subst_closed_inv {Ψ : SepCtx s1} {σ : Subst s1 s2}
  (hclosed : (Ψ.subst σ).IsClosed) :
  Ψ.IsClosed := by
  induction Ψ generalizing s2 with
  | empty => exact SepCtx.IsClosed.empty
  | cons Ψ C ih =>
    simp only [SepCtx.subst] at hclosed
    cases hclosed with
    | cons hΨ hC =>
      exact SepCtx.IsClosed.cons (ih hΨ) (CaptureSet.subst_closed_inv hC)

theorem MutabilityCtx.subst_closed_inv {Ψ : MutabilityCtx s1} {σ : Subst s1 s2}
  (hclosed : (Ψ.subst σ).IsClosed) :
  Ψ.IsClosed := by
  induction Ψ generalizing s2 with
  | empty => exact MutabilityCtx.IsClosed.empty
  | cons Ψ C m ih =>
    simp only [MutabilityCtx.subst] at hclosed
    cases hclosed with
    | cons hΨ hC =>
      exact MutabilityCtx.IsClosed.cons (ih hΨ) (CaptureSet.subst_closed_inv hC)

theorem ModalCtx.subst_closed_inv {Ψ : ModalCtx s1} {σ : Subst s1 s2}
  (hclosed : (Ψ.subst σ).IsClosed) :
  Ψ.IsClosed :=
  ⟨SepCtx.subst_closed_inv hclosed.sep, MutabilityCtx.subst_closed_inv hclosed.mutability⟩

theorem CaptureBound.subst_closed_inv {cb : CaptureBound s1} {σ : Subst s1 s2}
  (hclosed : (cb.subst σ).IsClosed) :
  cb.IsClosed := by
  cases cb with
  | unbound => exact CaptureBound.IsClosed.unbound
  | bound cs =>
    simp only [CaptureBound.subst] at hclosed
    cases hclosed with
    | bound hcs =>
      exact CaptureBound.IsClosed.bound (CaptureSet.subst_closed_inv hcs)

/-- If the result of substitution is closed, the original type was closed. -/
theorem Ty.subst_closed_inv {T : Ty sort s1} {σ : Subst s1 s2}
  (hclosed : (T.subst σ).IsClosed) :
  T.IsClosed := by
  induction T generalizing s2 with
  | top => exact IsClosed.top
  | tvar X => exact IsClosed.tvar
  | arrow T1 cs T2 ih1 ih2 =>
    simp only [Ty.subst] at hclosed
    cases hclosed with | arrow h1 hcs h2 =>
    exact IsClosed.arrow (ih1 h1)
      (CaptureSet.subst_closed_inv hcs) (ih2 h2)
  | poly T1 cs T2 ih1 ih2 =>
    simp only [Ty.subst] at hclosed
    cases hclosed with | poly h1 hcs h2 =>
    exact IsClosed.poly (ih1 h1)
      (CaptureSet.subst_closed_inv hcs) (ih2 h2)
  | cpoly cb cs T ih =>
    simp only [Ty.subst] at hclosed
    cases hclosed with | cpoly hcb hcs hT =>
    exact IsClosed.cpoly (CaptureBound.subst_closed_inv hcb)
      (CaptureSet.subst_closed_inv hcs) (ih hT)
  | consumer T1 cs T2 ih1 ih2 =>
    simp only [Ty.subst] at hclosed
    cases hclosed with | consumer h1 hcs h2 =>
    exact IsClosed.consumer (ih1 h1)
      (CaptureSet.subst_closed_inv hcs) (ih2 h2)
  | modal cs Ψ T ih =>
    simp only [Ty.subst] at hclosed
    cases hclosed with | modal hcs hΨ hT =>
    exact IsClosed.modal (CaptureSet.subst_closed_inv hcs)
      (ModalCtx.subst_closed_inv hΨ) (ih hT)
  | unit => exact IsClosed.unit
  | cap cs =>
    simp only [Ty.subst] at hclosed
    cases hclosed with | cap hcs =>
    exact IsClosed.cap (CaptureSet.subst_closed_inv hcs)
  | bool => exact IsClosed.bool
  | cell cs T ih =>
    simp only [Ty.subst] at hclosed
    cases hclosed with | cell hcs hT =>
    exact IsClosed.cell (CaptureSet.subst_closed_inv hcs) (ih hT)
  | reader cs T ih =>
    simp only [Ty.subst] at hclosed
    cases hclosed with | reader hcs hT =>
    exact IsClosed.reader (CaptureSet.subst_closed_inv hcs) (ih hT)
  | exi n T ih =>
    simp only [Ty.subst] at hclosed
    cases hclosed with | exi hT =>
    exact IsClosed.exi (ih hT)
  | typ T ih =>
    simp only [Ty.subst] at hclosed
    cases hclosed with | typ hT =>
    exact IsClosed.typ (ih hT)

/-- If the result of substitution is closed, the original expression was closed. -/
theorem Exp.subst_closed_inv {e : Exp s1} {σ : Subst s1 s2}
  (hclosed : (e.subst σ).IsClosed) :
  e.IsClosed := by
  induction e generalizing s2 with
  | var x =>
    simp only [Exp.subst] at hclosed
    cases hclosed with | var hx =>
    exact IsClosed.var (Var.subst_closed_inv hx)
  | abs cs T e ih =>
    simp only [Exp.subst] at hclosed
    cases hclosed with | abs hcs hT he =>
    exact IsClosed.abs (CaptureSet.subst_closed_inv hcs) (Ty.subst_closed_inv hT) (ih he)
  | tabs cs T e ih =>
    simp only [Exp.subst] at hclosed
    cases hclosed with | tabs hcs hT he =>
    exact IsClosed.tabs (CaptureSet.subst_closed_inv hcs) (Ty.subst_closed_inv hT) (ih he)
  | cabs cs cb e ih =>
    simp only [Exp.subst] at hclosed
    cases hclosed with | cabs hcs hcb he =>
    exact IsClosed.cabs (CaptureSet.subst_closed_inv hcs)
      (CaptureBound.subst_closed_inv hcb) (ih he)
  | consumer cs T e ih =>
    simp only [Exp.subst] at hclosed
    cases hclosed with | consumer hcs hT he =>
    exact IsClosed.consumer (CaptureSet.subst_closed_inv hcs)
      (Ty.subst_closed_inv hT) (ih he)
  | boxed cs Ψ e ih =>
    simp only [Exp.subst] at hclosed
    cases hclosed with | boxed hcs hΨ he =>
    exact IsClosed.boxed (CaptureSet.subst_closed_inv hcs) (ModalCtx.subst_closed_inv hΨ) (ih he)
  | reader x =>
    simp only [Exp.subst] at hclosed
    cases hclosed with | reader hx =>
    exact IsClosed.reader (Var.subst_closed_inv hx)
  | alloc x =>
    simp only [Exp.subst] at hclosed
    cases hclosed with | alloc hx =>
    exact IsClosed.alloc (Var.subst_closed_inv hx)
  | drop x =>
    simp only [Exp.subst] at hclosed
    cases hclosed with | drop hx =>
    exact IsClosed.drop (Var.subst_closed_inv hx)
  | pack css x =>
    simp only [Exp.subst] at hclosed
    cases hclosed with | pack hcs hx =>
    refine IsClosed.pack ?_ (Var.subst_closed_inv hx)
    intro cs hmem
    apply CaptureSet.subst_closed_inv (σ := σ)
    apply hcs
    simp only [List.Vector.toList_map, List.mem_map]
    exact ⟨cs, hmem, rfl⟩
  | app x y =>
    simp only [Exp.subst] at hclosed
    cases hclosed with | app hx hy =>
    exact IsClosed.app (Var.subst_closed_inv hx) (Var.subst_closed_inv hy)
  | tapp x T =>
    simp only [Exp.subst] at hclosed
    cases hclosed with | tapp hx hT =>
    exact IsClosed.tapp (Var.subst_closed_inv hx) (Ty.subst_closed_inv hT)
  | capp x cs =>
    simp only [Exp.subst] at hclosed
    cases hclosed with | capp hx hcs =>
    exact IsClosed.capp (Var.subst_closed_inv hx) (CaptureSet.subst_closed_inv hcs)
  | unwrap x =>
    simp only [Exp.subst] at hclosed
    cases hclosed with | unwrap hx =>
    exact IsClosed.unwrap (Var.subst_closed_inv hx)
  | letin e1 e2 ih1 ih2 =>
    simp only [Exp.subst] at hclosed
    cases hclosed with | letin he1 he2 =>
    exact IsClosed.letin (ih1 he1) (ih2 he2)
  | unpack n e1 e2 ih1 ih2 =>
    simp only [Exp.subst] at hclosed
    cases hclosed with | unpack he1 he2 =>
    exact IsClosed.unpack (ih1 he1) (ih2 he2)
  | unit => exact IsClosed.unit
  | btrue =>
    simp only [Exp.subst] at hclosed
    cases hclosed with | btrue => exact IsClosed.btrue
  | bfalse =>
    simp only [Exp.subst] at hclosed
    cases hclosed with | bfalse => exact IsClosed.bfalse
  | read x =>
    simp only [Exp.subst] at hclosed
    cases hclosed with | read hx =>
    exact IsClosed.read (Var.subst_closed_inv hx)
  | write x y =>
    simp only [Exp.subst] at hclosed
    cases hclosed with | write hx hy =>
    exact IsClosed.write (Var.subst_closed_inv hx) (Var.subst_closed_inv hy)
  | cond x e2 e3 ih2 ih3 =>
    simp only [Exp.subst] at hclosed
    cases hclosed with | cond hx h2 h3 =>
    exact IsClosed.cond (Var.subst_closed_inv hx) (ih2 h2) (ih3 h3)
  | par C1 C2 e1 e2 ih1 ih2 =>
    simp only [Exp.subst] at hclosed
    cases hclosed with | par hc1 hc2 h1 h2 =>
    exact IsClosed.par (CaptureSet.subst_closed_inv hc1) (CaptureSet.subst_closed_inv hc2)
      (ih1 h1) (ih2 h2)

end CoreCapybara
