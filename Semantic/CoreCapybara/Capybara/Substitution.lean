import Semantic.CoreCapybara.Capybara.Syntax

namespace CoreCapybara

/-- A substitution maps bound variables of each kind to terms of the appropriate sort. -/
structure CapySubst (s1 s2 : Sig) where
  var : BVar s1 .var -> Var .var s2
  tvar : BVar s1 .tvar -> CapyPureTy s2
  cvar : BVar s1 .cvar -> CapyCaptureSet s2

/-- Lifts a substitution under a binder. The newly bound variable maps to itself. -/
def CapySubst.lift (s : CapySubst s1 s2) : CapySubst (s1,,k) (s2,,k) where
  var := fun x => by
    cases x
    case here => exact .bound .here
    case there x => exact (s.var x).rename Rename.succ
  tvar := fun x => by
    cases x
    case here => exact CapyPureTy.tvar .here
    case there x => exact (s.tvar x).rename Rename.succ
  cvar := fun x => by
    cases x
    case here => exact .cvar (.M .epsilon) .here
    case there x => exact (s.cvar x).rename Rename.succ

/-- Lifts a substitution under multiple binders. -/
def CapySubst.liftMany (s : CapySubst s1 s2) (K : Sig) : CapySubst (s1 ++ K) (s2 ++ K) :=
  match K with
  | [] => s
  | k :: K => (s.liftMany K).lift (k:=k)

/-- The identity substitution. -/
def CapySubst.id {s : Sig} : CapySubst s s where
  var := fun x => .bound x
  tvar := fun x => CapyPureTy.tvar x
  cvar := fun x => .cvar (.M .epsilon) x

/-- Applies a substitution to a variable. Free variables remain unchanged. -/
def CapyVar.subst : Var .var s1 -> CapySubst s1 s2 -> Var .var s2
| .bound x, s => s.var x
| .free n, _ => .free n

/-- Applies a substitution to all bound variables in a capture set. -/
def CapyCaptureSet.subst : CapyCaptureSet s1 -> CapySubst s1 s2 -> CapyCaptureSet s2
| .empty, _ => .empty
| .union cs1 cs2, σ => .union ((CapyCaptureSet.subst cs1) σ) ((CapyCaptureSet.subst cs2) σ)
| .var m x, σ => .var m ((CapyVar.subst x) σ)
| .cvar m x, σ => (σ.cvar x).applyAccess m

/-- Applies a substitution to a capture bound. -/
def CapyCaptureBound.subst : CapyCaptureBound s1 -> CapySubst s1 s2 -> CapyCaptureBound s2
| .unbound m, _ => .unbound m
| .bound cs, σ => .bound ((CapyCaptureSet.subst cs) σ)

/-- Applies a substitution to a type. -/
def CapyTy.subst : CapyTy sort s1 -> CapySubst s1 s2 -> CapyTy sort s2
| .top, _ => .top
| .tvar x, s => (s.tvar x).core
| .arrow T1 cs T2, s =>
    .arrow (T1.subst s.lift) ((CapyCaptureSet.subst cs) s) (T2.subst s.lift)
| .poly T1 cs T2, s => .poly (T1.subst s) ((CapyCaptureSet.subst cs) s) (T2.subst s.lift)
| .cpoly cb cs T, s => .cpoly (cb.subst s) ((CapyCaptureSet.subst cs) s) (T.subst s.lift)
| .unit, _ => .unit
| .cap cs, s => .cap ((CapyCaptureSet.subst cs) s)
| .bool, _ => .bool
| .cell cs m, s => .cell ((CapyCaptureSet.subst cs) s) m
| .exi T, s => .exi (T.subst s.lift)
| .typ T, s => .typ (T.subst s)

/-- Substitution preserves emptiness of capture sets. -/
theorem CapyCaptureSet.IsEmpty.subst {cs : CapyCaptureSet s1} (h : cs.IsEmpty)
    (σ : CapySubst s1 s2) : ((CapyCaptureSet.subst cs) σ).IsEmpty := by
  induction h with
  | empty => exact CapyCaptureSet.IsEmpty.empty
  | union _ _ ih1 ih2 => exact CapyCaptureSet.IsEmpty.union ih1 ih2

/-- Substitution preserves purity. -/
theorem CapyTy.IsPureType.subst {T : CapyTy .capt s1} (h : T.IsPureType) (σ : CapySubst s1 s2) :
    (T.subst σ).IsPureType := by
  unfold IsPureType at *
  cases T with
  | top => simp only [CapyTy.subst, CapyTy.captureSet]; exact CapyCaptureSet.IsEmpty.empty
  | tvar x => simpa [CapyTy.subst, CapyTy.captureSet] using (σ.tvar x).p
  | unit => simp only [CapyTy.subst, CapyTy.captureSet]; exact CapyCaptureSet.IsEmpty.empty
  | bool => simp only [CapyTy.subst, CapyTy.captureSet]; exact CapyCaptureSet.IsEmpty.empty
  | arrow _ _ _ =>
    simp only [CapyTy.subst, CapyTy.captureSet] at *
    exact CapyCaptureSet.IsEmpty.subst h σ
  | poly _ _ _ =>
    simp only [CapyTy.subst, CapyTy.captureSet] at *
    exact CapyCaptureSet.IsEmpty.subst h σ
  | cpoly _ _ _ =>
    simp only [CapyTy.subst, CapyTy.captureSet] at *
    exact CapyCaptureSet.IsEmpty.subst h σ
  | cap cs =>
    simp only [CapyTy.subst, CapyTy.captureSet] at *
    exact CapyCaptureSet.IsEmpty.subst h σ
  | cell cs m =>
    simp only [CapyTy.subst, CapyTy.captureSet] at *
    exact CapyCaptureSet.IsEmpty.subst h σ

/-- Applies a substitution to a pure type. -/
def CapyPureTy.subst (T : CapyPureTy s1) (σ : CapySubst s1 s2) : CapyPureTy s2 :=
  ⟨T.core.subst σ, T.p.subst σ⟩

/-- Applies a substitution to an expression. -/
def CapyExp.subst : CapyExp s1 -> CapySubst s1 s2 -> CapyExp s2
| .var x, s => .var ((CapyVar.subst x) s)
| .abs T e, s => .abs (T.subst s.lift) (e.subst s.lift)
| .tabs T e, s => .tabs (T.subst s) (e.subst s.lift)
| .cabs cb e, s => .cabs (cb.subst s) (e.subst s.lift)
| .alloc x, s => .alloc ((CapyVar.subst x) s)
| .drop x, s => .drop ((CapyVar.subst x) s)
| .app x y, s => .app ((CapyVar.subst x) s) ((CapyVar.subst y) s)
| .tapp x T, s => .tapp ((CapyVar.subst x) s) (T.subst s)
| .capp x cs, s => .capp ((CapyVar.subst x) s) ((CapyCaptureSet.subst cs) s)
| .letin e1 e2, s => .letin (e1.subst s) (e2.subst s.lift)
| .unit, _ => .unit
| .btrue, _ => .btrue
| .bfalse, _ => .bfalse
| .read x, s => .read ((CapyVar.subst x) s)
| .write x y, s => .write ((CapyVar.subst x) s) ((CapyVar.subst y) s)
| .cond x e2 e3, s => .cond ((CapyVar.subst x) s) (e2.subst s) (e3.subst s)
| .par e1 e2, s => .par (e1.subst s) (e2.subst s)

/-- Substitution that opens a variable binder by replacing the innermost bound variable with `x`. -/
def CapySubst.openVar (x : Var .var s) : CapySubst (s,x) s where
  var := fun
    | .here => x
    | .there x0 => .bound x0
  tvar := fun
    | .there x0 => CapyPureTy.tvar x0
  cvar := fun
    | .there x0 => .cvar (.M .epsilon) x0

/-- Opens a type variable binder, substituting `U` for the innermost bound. -/
def CapySubst.openTVar (U : CapyPureTy s) : CapySubst (s,X) s where
  var := fun
    | .there x => .bound x
  tvar := fun
    | .here => U
    | .there x => CapyPureTy.tvar x
  cvar := fun
    | .there x => .cvar (.M .epsilon) x

/-- Opens a capture variable binder, substituting `C` for the innermost bound. -/
def CapySubst.openCVar (C : CapyCaptureSet s) : CapySubst (s,C) s where
  var := fun
    | .there x => .bound x
  tvar := fun
    | .there x => CapyPureTy.tvar x
  cvar := fun
    | .here => C
    | .there x => .cvar (.M .epsilon) x

/-- Opens an existential package, substituting `C` and `x` for the two innermost binders. -/
def CapySubst.unpack (C : CapyCaptureSet s) (x : Var .var s) : CapySubst (s,C,x) s where
  var := fun
    | .here => x
    | .there (.there x0) => .bound x0
  cvar := fun
    | .there (.here) => C
    | .there (.there c0) => .cvar (.M .epsilon) c0
  tvar := fun
    | .there (.there X0) => CapyPureTy.tvar X0

/-- Drops the innermost (capture-variable) binder from a capture set, lowering
    it into the enclosing signature. Realised as the substitution that opens
    that binder with the empty capture set, so references to it become `{}`. -/
def CapyCaptureSet.dropCVar (cs : CapyCaptureSet (s,C)) : CapyCaptureSet s :=
  CapyCaptureSet.subst cs (CapySubst.openCVar {})

/-- Drops the innermost (type-variable) binder from a capture set. Capture sets
    never mention type variables, so this is the substitution that reindexes the
    remaining variables down one level. -/
def CapyCaptureSet.dropTVar (cs : CapyCaptureSet (s,X)) : CapyCaptureSet s :=
  CapyCaptureSet.subst cs (CapySubst.openTVar CapyPureTy.top)

/-- Drops the innermost (term-variable) binder from a capture set. Substitution
    cannot express this — a term-variable reference always substitutes to another
    term variable, never to `{}` — so references to the dropped binder are
    discarded directly. -/
def CapyCaptureSet.dropVar : CapyCaptureSet (s,x) -> CapyCaptureSet s
| .empty => .empty
| .union cs1 cs2 => (CapyCaptureSet.dropVar cs1) ∪ (CapyCaptureSet.dropVar cs2)
| .var _ (.bound .here) => .empty
| .var a (.bound (.there y)) => .var a (.bound y)
| .var a (.free n) => .var a (.free n)
| .cvar a (.there c) => .cvar a c

/-- The *interfere set* of a type: an over-approximation of the
    capture set that values of the type may use, directly or indirectly.

    For the three function forms it folds in the function's own capture set
    `Cf`, the argument's capture set, and the interfere set of the result with
    the type's bound variables stripped:
    ```
    interfere([c](x: S^C) ->Cf E) = Cf ∪ C ∪ interfere(E) - {c, x}
    interfere([X] ->Cf E)         = Cf ∪ interfere(E)
    interfere([c] ->Cf E)         = Cf ∪ interfere(E) - {c}
    ```
    The function codomains are existential types: for `∃c. T` the bound capture
    variable is stripped from the body's interfere set, and `typ T` forwards to
    the underlying type. -/
def CapyTy.interfere_set (T : CapyTy sort s) : CapyCaptureSet s :=
  match T with
  | .top => .empty
  | .tvar _ => .empty
  | .unit => .empty
  | .bool => .empty
  | .cap cs => cs
  | .cell cs _ => cs
  -- [c](x: S^C) ->Cf E :  S under c (`,C`);  E under x (`,x`)
  | .arrow S Cf E =>
      Cf ∪ CapyCaptureSet.dropCVar S.captureSet
         ∪ CapyCaptureSet.dropVar E.interfere_set
  -- [X] ->Cf E :  E under X (`,X`)
  | .poly _ Cf E =>
      Cf ∪ CapyCaptureSet.dropTVar E.interfere_set
  -- [c] ->Cf E :  E under c (`,C`)
  | .cpoly _ Cf E =>
      Cf ∪ CapyCaptureSet.dropCVar E.interfere_set
  -- ∃c. T :  T under c (`,C`)
  | .exi T => CapyCaptureSet.dropCVar T.interfere_set
  | .typ T => T.interfere_set
termination_by sizeOf T

/-- Function extensionality for substitutions.
  Two substitutions are equal if they map all variables equally. -/
theorem CapySubst.funext {σ1 σ2 : CapySubst s1 s2}
  (hvar : ∀ x, σ1.var x = σ2.var x)
  (htvar : ∀ x, σ1.tvar x = σ2.tvar x)
  (hcvar : ∀ x, σ1.cvar x = σ2.cvar x) :
  σ1 = σ2 := by
  cases σ1; cases σ2
  simp only [CapySubst.mk.injEq]
  constructor
  · funext x; exact hvar x
  constructor
  · funext x; exact htvar x
  · funext x; exact hcvar x

/-- Composition of substitutions. -/
def CapySubst.comp (σ1 : CapySubst s1 s2) (σ2 : CapySubst s2 s3) : CapySubst s1 s3 where
  var := fun x => CapyVar.subst (σ1.var x) σ2
  tvar := fun x => (σ1.tvar x).subst σ2
  cvar := fun x => CapyCaptureSet.subst (σ1.cvar x) σ2

theorem CapySubst.lift_there_var_eq {σ : CapySubst s1 s2} {x : BVar s1 .var} :
  (σ.lift (k:=k)).var (.there x) = (σ.var x).rename Rename.succ := by
  rfl

theorem CapySubst.lift_there_tvar_eq {σ : CapySubst s1 s2} {X : BVar s1 .tvar} :
  (σ.lift (k:=k)).tvar (.there X) = (σ.tvar X).rename Rename.succ := by
  rfl

theorem CapyRename.lift_there_tvar_eq {f : Rename s1 s2} {x : BVar s1 .tvar} :
  (f.lift (k:=k)).var (.there x) = (f.var x).there := by
  rfl

theorem CapyRename.lift_there_var_eq {f : Rename s1 s2} {x : BVar s1 .var} :
  (f.lift (k:=k)).var (.there x) = (f.var x).there := by
  rfl

theorem CapySubst.lift_there_cvar_eq {σ : CapySubst s1 s2} {C : BVar s1 .cvar} :
  (σ.lift (k:=k)).cvar (.there C) = (σ.cvar C).rename Rename.succ := by
  rfl

theorem CapyRename.lift_there_cvar_eq {f : Rename s1 s2} {C : BVar s1 .cvar} :
  (f.lift (k:=k)).var (.there C) = (f.var C).there := by
  rfl

theorem CapyCaptureSet.weaken_rename_comm {cs : CapyCaptureSet s1} {f : Rename s1 s2} :
  (cs.rename Rename.succ).rename (f.lift (k:=k0)) = (cs.rename f).rename (Rename.succ) := by
  simp only [CapyCaptureSet.rename_comp, Rename.succ_lift_comm]

theorem CapyPureTy.weaken_rename_comm {T : CapyPureTy s1} {f : Rename s1 s2} :
  (T.rename Rename.succ).rename (f.lift (k:=k0)) = (T.rename f).rename (Rename.succ) := by
  simp only [CapyPureTy.rename, CapyTy.weaken_rename_comm]

theorem CapyTVar.weaken_subst_comm_liftMany {X : BVar (s1 ++ K) .tvar} {σ : CapySubst s1 s2} :
  ((σ.liftMany K).tvar X).rename ((Rename.succ (k:=k0)).liftMany K) =
  (σ.lift (k:=k0).liftMany K).tvar ((Rename.succ (k:=k0).liftMany K).var X) := by
  induction K with
  | nil =>
    cases X with
    | here => rfl
    | there X => rfl
  | cons k K ih =>
    simp only [CapySubst.liftMany, Rename.liftMany]
    cases X with
    | here => rfl
    | there X =>
      simp only [CapyRename.lift_there_tvar_eq, CapySubst.lift_there_tvar_eq]
      conv_rhs => rw [← ih]
      exact CapyPureTy.weaken_rename_comm

theorem CapyVar.weaken_subst_comm_liftMany {x : Var .var (s1 ++ K)} {σ : CapySubst s1 s2} :
  ((CapyVar.subst x) (σ.liftMany K)).rename ((Rename.succ (k:=k0)).liftMany K) =
  CapyVar.subst (x.rename (Rename.succ.liftMany K)) (σ.lift (k:=k0).liftMany K) := by
  induction K with
  | nil =>
    simp only [CapySubst.liftMany, Rename.liftMany]
    cases x <;> rfl
  | cons k K ih =>
    simp only [CapySubst.liftMany, Rename.liftMany]
    cases x with
    | bound x =>
      cases x with
      | here => rfl
      | there x =>
        conv => lhs; simp only [CapyVar.subst]
        conv => rhs; simp only [Var.rename, CapyVar.subst]
        have ih := ih (x:=.bound x)
        simp only [CapyVar.subst, Var.rename] at ih
        simp only [CapySubst.lift_there_var_eq, CapyRename.lift_there_var_eq]
        conv_rhs => rw [← ih]
        exact CapyVar.weaken_rename_comm
    | free n => simp only [CapyVar.subst, Var.rename]

theorem CapyCVar.weaken_subst_comm_liftMany {C : BVar (s1 ++ K) .cvar} {σ : CapySubst s1 s2} :
  ((σ.liftMany K).cvar C).rename ((Rename.succ (k:=k0)).liftMany K) =
  (σ.lift (k:=k0).liftMany K).cvar ((Rename.succ (k:=k0).liftMany K).var C) := by
  induction K with
  | nil =>
    cases C with
    | here => rfl
    | there C => rfl
  | cons k K ih =>
    simp only [CapySubst.liftMany, Rename.liftMany]
    cases C with
    | here => rfl
    | there C =>
      simp only [CapyRename.lift_there_cvar_eq, CapySubst.lift_there_cvar_eq]
      conv_rhs => rw [← ih]
      exact CapyCaptureSet.weaken_rename_comm

theorem CapyCaptureSet.weaken_subst_comm_liftMany
    {cs : CapyCaptureSet (s1 ++ K)} {σ : CapySubst s1 s2} :
  ((CapyCaptureSet.subst cs) (σ.liftMany K)).rename ((Rename.succ (k:=k0)).liftMany K) =
  CapyCaptureSet.subst (cs.rename (Rename.succ.liftMany K)) (σ.lift (k:=k0).liftMany K) := by
  induction cs with
  | empty => rfl
  | union cs1 cs2 ih1 ih2 =>
    simp only [CapyCaptureSet.subst, CapyCaptureSet.rename, ih1, ih2]
  | var m x =>
    simp only [CapyCaptureSet.subst, CapyCaptureSet.rename]
    exact congrArg (CapyCaptureSet.var m) CapyVar.weaken_subst_comm_liftMany
  | cvar m C =>
    simp only [CapyCaptureSet.subst, CapyCaptureSet.rename]
    rw [CapyCaptureSet.applyAccess_rename]
    rw [CapyCVar.weaken_subst_comm_liftMany]

theorem CapyCaptureBound.weaken_subst_comm_liftMany
    {cb : CapyCaptureBound (s1 ++ K)} {σ : CapySubst s1 s2} :
    (cb.subst (σ.liftMany K)).rename ((Rename.succ (k := k0)).liftMany K) =
      (cb.rename (Rename.succ.liftMany K)).subst (σ.lift (k := k0).liftMany K) := by
  cases cb with
  | unbound => rfl
  | bound cs =>
    simp only [CapyCaptureBound.subst, CapyCaptureBound.rename,
      CapyCaptureSet.weaken_subst_comm_liftMany]

/-- Arithmetic helper for the `arrow` termination goal, where the recursive argument
  sits in the middle of the size sum. Stating it with a single variable `n` lets `omega`
  discharge it; at the use site `exact` matches the two (definitionally equal but
  syntactically distinct) `sizeOf` occurrences up to defeq. -/
private theorem lt_add_mid {a b c n : Nat} (h : 0 < a) : n < a + n + b + c := by omega

theorem CapyTy.weaken_subst_comm {T : CapyTy sort (s1 ++ K)} {σ : CapySubst s1 s2} :
  (T.subst (σ.liftMany K)).rename ((Rename.succ (k:=k0)).liftMany K) =
    (T.rename (Rename.succ.liftMany K)).subst (σ.lift.liftMany K) := by
  match T with
  | .top => simp only [CapyTy.subst, CapyTy.rename]
  | .tvar X =>
    simp only [CapyTy.subst, CapyTy.rename]
    have h := CapyTVar.weaken_subst_comm_liftMany (X:=X) (σ:=σ) (K:=K) (k0:=k0)
    simp only [CapyPureTy.rename] at h
    exact congrArg CapyPureTy.core h
  | .arrow T1 cs T2 =>
    have ih1 := CapyTy.weaken_subst_comm (T:=T1) (σ:=σ) (K:=K,C) (k0:=k0)
    have ihCS := CapyCaptureSet.weaken_subst_comm_liftMany (cs:=cs) (σ:=σ) (K:=K) (k0:=k0)
    have ih2 := CapyTy.weaken_subst_comm (T:=T2) (σ:=σ) (K:=K,x) (k0:=k0)
    simp only [CapyTy.subst, CapyTy.rename, ihCS]
    congr 1
  | .poly T1 cs T2 =>
    have ih1 := CapyTy.weaken_subst_comm (T:=T1) (σ:=σ) (K:=K) (k0:=k0)
    have ihCS := CapyCaptureSet.weaken_subst_comm_liftMany (cs:=cs) (σ:=σ) (K:=K) (k0:=k0)
    have ih2 := CapyTy.weaken_subst_comm (T:=T2) (σ:=σ) (K:=K,X) (k0:=k0)
    simp only [CapyTy.subst, CapyTy.rename, ih1, ihCS]
    exact congrArg
      (CapyTy.poly
        ((T1.rename (Rename.succ.liftMany K)).subst (σ.lift.liftMany K))
        (CapyCaptureSet.subst (cs.rename (Rename.succ.liftMany K)) (σ.lift.liftMany K)))
      ih2
  | .cpoly cb cs T =>
    have ihCB :=
      CapyCaptureBound.weaken_subst_comm_liftMany (cb := cb) (σ := σ) (K := K) (k0 := k0)
    have ihCS := CapyCaptureSet.weaken_subst_comm_liftMany (cs:=cs) (σ:=σ) (K:=K) (k0:=k0)
    have ih := CapyTy.weaken_subst_comm (T:=T) (σ:=σ) (K:=K,C) (k0:=k0)
    simp only [CapyTy.subst, CapyTy.rename, ihCB, ihCS]
    exact congrArg
      (CapyTy.cpoly
        ((cb.rename (Rename.succ.liftMany K)).subst (σ.lift.liftMany K))
        (CapyCaptureSet.subst (cs.rename (Rename.succ.liftMany K)) (σ.lift.liftMany K)))
      ih
  | .unit => simp only [CapyTy.subst, CapyTy.rename]
  | .cap cs =>
    have ihCS := CapyCaptureSet.weaken_subst_comm_liftMany (cs:=cs) (σ:=σ) (K:=K) (k0:=k0)
    simp only [CapyTy.subst, CapyTy.rename, ihCS]
  | .bool => simp only [CapyTy.subst, CapyTy.rename]
  | .cell cs m =>
    have ihCS := CapyCaptureSet.weaken_subst_comm_liftMany (cs:=cs) (σ:=σ) (K:=K) (k0:=k0)
    simp only [CapyTy.subst, CapyTy.rename, ihCS]
  | .exi T =>
    have ih := CapyTy.weaken_subst_comm (T:=T) (σ:=σ) (K:=K,C) (k0:=k0)
    simp only [CapyTy.subst, CapyTy.rename]
    exact congrArg CapyTy.exi ih
  | .typ T =>
    have ih := CapyTy.weaken_subst_comm (T:=T) (σ:=σ) (K:=K) (k0:=k0)
    simp only [CapyTy.subst, CapyTy.rename, ih]
termination_by sizeOf T
decreasing_by
  all_goals first
    | decreasing_tactic
    | (simp_wf; refine Nat.lt_add_of_pos_left ?_; omega)
    | (simp_wf; exact lt_add_mid (by omega))

theorem CapyTy.weaken_subst_comm_base {T : CapyTy sort s1} {σ : CapySubst s1 s2} :
  (T.subst σ).rename (Rename.succ (k:=k)) = (T.rename Rename.succ).subst (σ.lift (k:=k)) :=
  CapyTy.weaken_subst_comm (K:=[])

theorem CapyPureTy.weaken_subst_comm_base {T : CapyPureTy s1} {σ : CapySubst s1 s2} :
  (T.subst σ).rename (Rename.succ (k:=k)) = (T.rename Rename.succ).subst (σ.lift (k:=k)) := by
  simp only [CapyPureTy.subst, CapyPureTy.rename, CapyTy.weaken_subst_comm_base]

theorem CapyVar.weaken_subst_comm_base {x : Var .var s1} {σ : CapySubst s1 s2} :
  ((CapyVar.subst x) σ).rename (Rename.succ (k:=k))
      = CapyVar.subst (x.rename Rename.succ) (σ.lift) := by
  cases x with
  | bound x => rfl
  | free n => rfl

theorem CapyCVar.weaken_subst_comm_base {C : BVar s1 .cvar} {σ : CapySubst s1 s2} :
  (σ.cvar C).rename (Rename.succ (k:=k)) =
  (σ.lift (k:=k)).cvar ((Rename.succ (k:=k)).var C) := by
  cases C <;> rfl

theorem CapyCaptureSet.weaken_subst_comm_base {cs : CapyCaptureSet s1} {σ : CapySubst s1 s2} :
  ((CapyCaptureSet.subst cs) σ).rename (Rename.succ (k:=k))
      = CapyCaptureSet.subst (cs.rename Rename.succ) (σ.lift) := by
  induction cs with
  | empty => rfl
  | union cs1 cs2 ih1 ih2 =>
    simp only [CapyCaptureSet.subst, CapyCaptureSet.rename, ih1, ih2]
  | var m x =>
    simp only [CapyCaptureSet.subst, CapyCaptureSet.rename]
    exact congrArg (CapyCaptureSet.var m) CapyVar.weaken_subst_comm_base
  | cvar m C =>
    simp only [CapyCaptureSet.subst, CapyCaptureSet.rename]
    rw [CapyCaptureSet.applyAccess_rename]
    rw [CapyCVar.weaken_subst_comm_base]

theorem CapyCaptureBound.weaken_subst_comm_base {cb : CapyCaptureBound s1} {σ : CapySubst s1 s2} :
  (cb.subst σ).rename (Rename.succ (k := k)) = (cb.rename Rename.succ).subst (σ.lift) := by
  cases cb with
  | unbound => rfl
  | bound cs =>
    simp only [CapyCaptureBound.subst, CapyCaptureBound.rename,
      CapyCaptureSet.weaken_subst_comm_base]

/-- Composition of substitutions commutes with lifting. -/
theorem CapySubst.comp_lift {σ1 : CapySubst s1 s2} {σ2 : CapySubst s2 s3} {k : Kind} :
  (σ1.lift (k := k)).comp (σ2.lift (k := k)) = (σ1.comp σ2).lift (k := k) := by
  apply CapySubst.funext
  · intro x
    cases x with
    | here => rfl
    | there x0 =>
      conv =>
        lhs; simp only [CapySubst.comp, CapySubst.lift_there_var_eq]
      simp only [CapySubst.lift_there_var_eq]
      simp only [CapyVar.weaken_subst_comm_base, CapySubst.comp]
  · intro X
    cases X with
    | here =>
      cases σ1
      cases σ2
      rfl
    | there x0 =>
      conv =>
        lhs; simp only [CapySubst.comp, CapySubst.lift_there_tvar_eq]
      simp only [CapySubst.lift_there_tvar_eq]
      simp only [CapyPureTy.weaken_subst_comm_base, CapySubst.comp]
  · intro C
    cases C with
    | here =>
      change
        CapyCaptureSet.subst
            (CapyCaptureSet.cvar (.M .epsilon) (BVar.here : BVar (s2,,.cvar) .cvar))
            (σ2.lift (k := .cvar)) =
          CapyCaptureSet.cvar (.M .epsilon) (BVar.here : BVar (s3,,.cvar) .cvar)
      rfl
    | there C0 =>
      simp only [CapySubst.comp, CapySubst.lift]
      exact CapyCaptureSet.weaken_subst_comm_base.symm

/-- Composition of substitutions commutes with lifting many levels. -/
theorem CapySubst.comp_liftMany {σ1 : CapySubst s1 s2} {σ2 : CapySubst s2 s3} {K : Sig} :
  (σ1.liftMany K).comp (σ2.liftMany K) = (σ1.comp σ2).liftMany K := by
  induction K with
  | nil => rfl
  | cons k K ih =>
    simp only [CapySubst.liftMany]
    conv_rhs => rw [← ih]
    exact CapySubst.comp_lift

/-- Substituting a composition of substitutions is the same as
  substituting one after the other. -/
theorem CapyVar.subst_comp {x : Var .var s1} {σ1 : CapySubst s1 s2} {σ2 : CapySubst s2 s3} :
  CapyVar.subst ((CapyVar.subst x) σ1) σ2 = (CapyVar.subst x) (σ1.comp σ2) := by
  cases x with
  | bound x => rfl
  | free n => rfl

/-- applyRO distributes over substitution. -/
theorem CapyCaptureSet.applyRO_subst {cs : CapyCaptureSet s1} {σ : CapySubst s1 s2} :
    (CapyCaptureSet.subst cs.applyRO) σ = ((CapyCaptureSet.subst cs) σ).applyRO := by
  induction cs with
  | empty => rfl
  | union cs1 cs2 ih1 ih2 =>
    simp only [CapyCaptureSet.applyRO, CapyCaptureSet.subst, ih1, ih2]
  | var _ x =>
    simp only [CapyCaptureSet.applyRO, CapyCaptureSet.subst]
  | cvar _ x =>
    simp only [CapyCaptureSet.applyRO, CapyCaptureSet.subst, CapyCaptureSet.applyAccess_applyRO]

/-- applyMut distributes over substitution. -/
theorem CapyCaptureSet.applyMut_subst {cs : CapyCaptureSet s1} {σ : CapySubst s1 s2}
    {m : Mutability} :
    CapyCaptureSet.subst (cs.applyMut m) σ = ((CapyCaptureSet.subst cs) σ).applyMut m := by
  cases m <;> simp only [CapyCaptureSet.applyMut_epsilon, CapyCaptureSet.applyMut_ro, applyRO_subst]

/-- applyDrop distributes over substitution. -/
theorem CapyCaptureSet.applyDrop_subst {cs : CapyCaptureSet s1} {σ : CapySubst s1 s2} :
    (CapyCaptureSet.subst cs.applyDrop) σ = ((CapyCaptureSet.subst cs) σ).applyDrop := by
  induction cs with
  | empty => rfl
  | union cs1 cs2 ih1 ih2 => simp only [CapyCaptureSet.applyDrop, CapyCaptureSet.subst, ih1, ih2]
  | var _ x => simp only [CapyCaptureSet.applyDrop, CapyCaptureSet.subst]
  | cvar _ x =>
    simp only [CapyCaptureSet.applyDrop, CapyCaptureSet.subst, CapyCaptureSet.applyAccess_drop,
               CapyCaptureSet.applyAccess_applyDrop]

/-- applyAccess distributes over substitution. -/
theorem CapyCaptureSet.applyAccess_subst {cs : CapyCaptureSet s1} {σ : CapySubst s1 s2}
    {a : Access} :
    CapyCaptureSet.subst (cs.applyAccess a) σ = ((CapyCaptureSet.subst cs) σ).applyAccess a := by
  cases a with
  | M m => simp only [CapyCaptureSet.applyAccess_M, applyMut_subst]
  | drop => simp only [CapyCaptureSet.applyAccess_drop, applyDrop_subst]

/-- Substitution on capture sets distributes over composition of substitutions. -/
theorem CapyCaptureSet.subst_comp
    {cs : CapyCaptureSet s1} {σ1 : CapySubst s1 s2} {σ2 : CapySubst s2 s3} :
  CapyCaptureSet.subst ((CapyCaptureSet.subst cs) σ1) σ2
      = (CapyCaptureSet.subst cs) (σ1.comp σ2) := by
  induction cs with
  | empty => rfl
  | union cs1 cs2 ih1 ih2 =>
    simp only [CapyCaptureSet.subst, ih1, ih2]
  | var m x =>
    simp only [CapyCaptureSet.subst]
    exact congrArg (CapyCaptureSet.var m) CapyVar.subst_comp
  | cvar m C =>
    simp only [CapyCaptureSet.subst, CapySubst.comp, CapyCaptureSet.applyAccess_subst]

theorem CapyCaptureBound.subst_comp
    {cb : CapyCaptureBound s1} {σ1 : CapySubst s1 s2} {σ2 : CapySubst s2 s3} :
  (cb.subst σ1).subst σ2 = cb.subst (σ1.comp σ2) := by
  cases cb with
  | unbound => rfl
  | bound cs => simp only [CapyCaptureBound.subst, CapyCaptureSet.subst_comp]

/-- Substitution on types distributes over composition of substitutions. -/
theorem CapyTy.subst_comp {T : CapyTy sort s1} {σ1 : CapySubst s1 s2} {σ2 : CapySubst s2 s3} :
  (T.subst σ1).subst σ2 = T.subst (σ1.comp σ2) := by
  induction T generalizing s2 s3 with
  | top => simp only [CapyTy.subst]
  | tvar x => simp only [CapyTy.subst, CapySubst.comp, CapyPureTy.subst]
  | arrow T1 cs T2 ih1 ih2 =>
    simp only [CapyTy.subst, ih1, ih2, CapyCaptureSet.subst_comp]
    conv_rhs => rw [← CapySubst.comp_lift, ← CapySubst.comp_lift]
    rfl
  | poly T1 cs T2 ih1 ih2 =>
    simp only [CapyTy.subst, ih1, ih2, CapyCaptureSet.subst_comp]
    conv_rhs => rw [← CapySubst.comp_lift]
    rfl
  | cpoly cb cs T ih =>
    simp only [CapyTy.subst, ih, CapyCaptureBound.subst_comp, CapyCaptureSet.subst_comp]
    conv_rhs => rw [← CapySubst.comp_lift]
    rfl
  | unit => simp only [CapyTy.subst]
  | cap cs => simp only [CapyTy.subst, CapyCaptureSet.subst_comp]
  | bool => simp only [CapyTy.subst]
  | cell cs m => simp only [CapyTy.subst, CapyCaptureSet.subst_comp]
  | exi T ih =>
    simp only [CapyTy.subst, ih]
    conv_rhs => rw [← CapySubst.comp_lift]
    rfl
  | typ T ih =>
    simp only [CapyTy.subst, ih]

/-- Substitution on pure types distributes over composition of substitutions. -/
theorem CapyPureTy.subst_comp {T : CapyPureTy s1} {σ1 : CapySubst s1 s2} {σ2 : CapySubst s2 s3} :
  (T.subst σ1).subst σ2 = T.subst (σ1.comp σ2) := by
  simp only [CapyPureTy.subst, CapyTy.subst_comp]

/-- Substitution on terms distributes over composition of substitutions. -/
theorem CapyExp.subst_comp {e : CapyExp s1} {σ1 : CapySubst s1 s2} {σ2 : CapySubst s2 s3} :
  (e.subst σ1).subst σ2 = e.subst (σ1.comp σ2) := by
  induction e generalizing s2 s3 with
  | var x => simp only [CapyExp.subst, CapyVar.subst_comp]
  | abs T e ih_e =>
    simp only [CapyExp.subst, CapyTy.subst_comp, ih_e]
    conv_rhs => rw [← CapySubst.comp_lift, ← CapySubst.comp_lift]
    rfl
  | tabs T e ih_e =>
    simp only [CapyExp.subst, CapyPureTy.subst_comp, ih_e]
    conv_rhs => rw [← CapySubst.comp_lift]
    rfl
  | cabs cb e ih_e =>
    simp only [CapyExp.subst, CapyCaptureBound.subst_comp, ih_e]
    conv_rhs => rw [← CapySubst.comp_lift]
    rfl
  | alloc x => simp only [CapyExp.subst, CapyVar.subst_comp]
  | drop x => simp only [CapyExp.subst, CapyVar.subst_comp]
  | app x y => simp only [CapyExp.subst, CapyVar.subst_comp]
  | tapp x T => simp only [CapyExp.subst, CapyVar.subst_comp, CapyPureTy.subst_comp]
  | capp x cs =>
    simp only [CapyExp.subst, CapyVar.subst_comp, CapyCaptureSet.subst_comp]
  | letin e1 e2 ih1 ih2 =>
    simp only [CapyExp.subst, ih1, ih2]
    conv_rhs => rw [← CapySubst.comp_lift]
    rfl
  | unit => rfl
  | btrue => rfl
  | bfalse => rfl
  | read x => simp only [CapyExp.subst, CapyVar.subst_comp]
  | write x y => simp only [CapyExp.subst, CapyVar.subst_comp]
  | cond x e2 e3 ih2 ih3 =>
    simp only [CapyExp.subst, CapyVar.subst_comp, ih2, ih3]
  | par e1 e2 ih1 ih2 =>
    simp only [CapyExp.subst, ih1, ih2]

/-- Substituting with the identity substitution leaves a variable unchanged. -/
theorem CapyVar.subst_id {x : Var .var s} :
  (CapyVar.subst x) CapySubst.id = x := by
  cases x with
  | bound x => rfl
  | free n => rfl

/-- Substituting with the identity substitution leaves a capture set unchanged. -/
theorem CapyCaptureSet.subst_id {cs : CapyCaptureSet s} :
  (CapyCaptureSet.subst cs) CapySubst.id = cs := by
  induction cs with
  | empty => rfl
  | union cs1 cs2 ih1 ih2 =>
    simp only [CapyCaptureSet.subst, ih1, ih2]
  | var m x =>
    simp only [CapyCaptureSet.subst, CapyVar.subst_id]
  | cvar m C =>
    cases m with
    | M m =>
      cases m <;> simp only [
        CapyCaptureSet.subst,
        CapySubst.id,
        CapyCaptureSet.applyAccess_M,
        Access.applyRO,
        CapyCaptureSet.applyRO_cvar,
        CapyCaptureSet.applyMut_epsilon,
        CapyCaptureSet.applyMut_ro
      ]
    | drop =>
      simp only [CapyCaptureSet.subst, CapySubst.id, CapyCaptureSet.applyAccess_drop,
        CapyCaptureSet.applyDrop]

/-- Lifting the identity substitution yields the identity. -/
theorem CapySubst.lift_id :
  (CapySubst.id (s:=s)).lift (k:=k) = CapySubst.id := by
  apply CapySubst.funext
  · intro x
    cases x <;> rfl
  · intro X
    cases X <;> rfl
  · intro C
    cases C <;> rfl

theorem CapyCaptureBound.subst_id {cb : CapyCaptureBound s} :
  cb.subst CapySubst.id = cb := by
  cases cb with
  | unbound => rfl
  | bound cs => simp only [CapyCaptureBound.subst, CapyCaptureSet.subst_id]

/-- Substituting with the identity substitution leaves a type unchanged. -/
theorem CapyTy.subst_id {T : CapyTy sort s} :
  T.subst CapySubst.id = T := by
  induction T with
  | top => simp only [CapyTy.subst]
  | tvar x => simp only [CapyTy.subst, CapySubst.id, CapyPureTy.tvar]
  | arrow T1 cs T2 ih1 ih2 =>
    simp only [CapyTy.subst, CapyCaptureSet.subst_id, CapySubst.lift_id]
    congr 1
  | poly T1 cs T2 ih1 ih2 =>
    simp only [CapyTy.subst, ih1, CapyCaptureSet.subst_id, CapySubst.lift_id]
    exact congrArg (CapyTy.poly T1 cs) ih2
  | cpoly cb cs T ih =>
    simp only [CapyTy.subst, CapyCaptureBound.subst_id, CapyCaptureSet.subst_id, CapySubst.lift_id]
    exact congrArg (CapyTy.cpoly cb cs) ih
  | unit => simp only [CapyTy.subst]
  | cap cs => simp only [CapyTy.subst, CapyCaptureSet.subst_id]
  | bool => simp only [CapyTy.subst]
  | cell cs m => simp only [CapyTy.subst, CapyCaptureSet.subst_id]
  | exi T ih =>
    simp only [CapyTy.subst, CapySubst.lift_id]
    exact congrArg CapyTy.exi ih
  | typ T ih =>
    simp only [CapyTy.subst]
    exact congrArg CapyTy.typ ih

/-- Substituting with the identity substitution leaves a pure type unchanged. -/
theorem CapyPureTy.subst_id {T : CapyPureTy s} :
  T.subst CapySubst.id = T := by
  simp only [CapyPureTy.subst, CapyTy.subst_id]

/-- Substituting with the identity substitution leaves an expression unchanged. -/
theorem CapyExp.subst_id {e : CapyExp s} :
  e.subst CapySubst.id = e := by
  induction e with
  | var x =>
    simp only [CapyExp.subst, CapyVar.subst_id]
  | abs T e ih =>
    simp only [CapyExp.subst, CapySubst.lift_id]
    have hT : T.subst CapySubst.id = T := CapyTy.subst_id
    congr 1
  | tabs T e ih =>
    simp only [CapyExp.subst, CapyPureTy.subst_id]
    conv_lhs => rw [CapySubst.lift_id]
    exact congrArg (CapyExp.tabs T) ih
  | cabs cb e ih =>
    simp only [CapyExp.subst, CapyCaptureBound.subst_id]
    conv_lhs => rw [CapySubst.lift_id]
    exact congrArg (CapyExp.cabs cb) ih
  | alloc x =>
    simp only [CapyExp.subst, CapyVar.subst_id]
  | drop x =>
    simp only [CapyExp.subst, CapyVar.subst_id]
  | app x y =>
    simp only [CapyExp.subst, CapyVar.subst_id]
  | tapp x T =>
    simp only [CapyExp.subst, CapyVar.subst_id, CapyPureTy.subst_id]
  | capp x cs =>
    simp only [CapyExp.subst, CapyVar.subst_id, CapyCaptureSet.subst_id]
  | letin e1 e2 ih1 ih2 =>
    simp only [CapyExp.subst, ih1]
    conv_lhs => rw [CapySubst.lift_id]
    exact congrArg (CapyExp.letin e1) ih2
  | unit =>
    rfl
  | btrue => rfl
  | bfalse => rfl
  | read x =>
    simp only [CapyExp.subst, CapyVar.subst_id]
  | write x y =>
    simp only [CapyExp.subst, CapyVar.subst_id]
  | cond x e2 e3 ih2 ih3 =>
    simp only [CapyExp.subst, CapyVar.subst_id, ih2, ih3]
  | par e1 e2 ih1 ih2 =>
    simp only [CapyExp.subst, ih1, ih2]

/-- Converts a renaming to a substitution. -/
def CapyRename.asSubst (f : Rename s1 s2) : CapySubst s1 s2 where
  var := fun x => .bound (f.var x)
  tvar := fun X => CapyPureTy.tvar (f.var X)
  cvar := fun C => .cvar (.M .epsilon) (f.var C)

/-- Lifting a renaming and then converting to a substitution is the same as
  converting to a substitution and then lifting the substitution. -/
theorem CapyRename.asSubst_lift {f : Rename s1 s2} :
  CapyRename.asSubst (f.lift (k:=k)) = ((CapyRename.asSubst f)).lift (k:=k) := by
  apply CapySubst.funext
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

/-- Substituting a substitution lifted from a renaming is the same as renaming. -/
theorem CapyVar.subst_asSubst {x : Var .var s1} {f : Rename s1 s2} :
  (CapyVar.subst x) ((CapyRename.asSubst f)) = x.rename f := by
  cases x with
  | bound x => rfl
  | free n => rfl

/-- Substituting a substitution lifted from a renaming is the same as renaming. -/
theorem CapyCaptureSet.subst_asSubst {cs : CapyCaptureSet s1} {f : Rename s1 s2} :
  (CapyCaptureSet.subst cs) ((CapyRename.asSubst f)) = cs.rename f := by
  induction cs with
  | empty => rfl
  | union cs1 cs2 ih1 ih2 =>
    simp only [CapyCaptureSet.subst, CapyCaptureSet.rename, ih1, ih2]
  | var m x =>
    simp only [CapyCaptureSet.subst, CapyCaptureSet.rename, CapyVar.subst_asSubst]
  | cvar m C =>
    cases m with
    | M m =>
      cases m <;> simp only [
        CapyCaptureSet.subst,
        CapyCaptureSet.rename,
        CapyRename.asSubst,
        CapyCaptureSet.applyAccess_M,
        Access.applyRO,
        CapyCaptureSet.applyRO_cvar,
        CapyCaptureSet.applyMut_epsilon,
        CapyCaptureSet.applyMut_ro
      ]
    | drop =>
      simp only [
        CapyCaptureSet.subst,
        CapyCaptureSet.rename,
        CapyRename.asSubst,
        CapyCaptureSet.applyAccess_drop,
        CapyCaptureSet.applyDrop
      ]

theorem CapyCaptureBound.subst_asSubst {cb : CapyCaptureBound s1} {f : Rename s1 s2} :
  cb.subst ((CapyRename.asSubst f)) = cb.rename f := by
  cases cb with
  | unbound => rfl
  | bound cs =>
    simp only [CapyCaptureBound.subst, CapyCaptureBound.rename, CapyCaptureSet.subst_asSubst]

/-- Substituting a substitution lifted from a renaming is the same as renaming. -/
theorem CapyTy.subst_asSubst {T : CapyTy sort s1} {f : Rename s1 s2} :
  T.subst ((CapyRename.asSubst f)) = T.rename f := by
  induction T generalizing s2 with
  | top => simp only [CapyTy.subst, CapyTy.rename]
  | tvar x => simp only [CapyTy.subst, CapyTy.rename, CapyRename.asSubst, CapyPureTy.tvar]
  | arrow T1 cs T2 ih1 ih2 =>
    have e1 := ih1 (f := f.lift)
    have e2 := ih2 (f := f.lift)
    simp only [CapyTy.subst, CapyTy.rename, CapyCaptureSet.subst_asSubst,
      ← CapyRename.asSubst_lift]
    congr 1
  | poly T1 cs T2 ih1 ih2 =>
    have e1 := ih1 (f := f)
    have e2 := ih2 (f := f.lift)
    simp only [CapyTy.subst, CapyTy.rename, CapyCaptureSet.subst_asSubst,
      ← CapyRename.asSubst_lift]
    congr 1
  | cpoly cb cs T ih =>
    have e := ih (f := f.lift)
    simp only [CapyTy.subst, CapyTy.rename, CapyCaptureBound.subst_asSubst,
      CapyCaptureSet.subst_asSubst,
      ← CapyRename.asSubst_lift]
    congr 1
  | unit => simp only [CapyTy.subst, CapyTy.rename]
  | cap cs => simp only [CapyTy.subst, CapyTy.rename, CapyCaptureSet.subst_asSubst]
  | bool => simp only [CapyTy.subst, CapyTy.rename]
  | cell cs m => simp only [CapyTy.subst, CapyTy.rename, CapyCaptureSet.subst_asSubst]
  | exi T ih =>
    have e := ih (f := f.lift)
    simp only [CapyTy.subst, CapyTy.rename, ← CapyRename.asSubst_lift]
    congr 1
  | typ T ih =>
    simp only [CapyTy.subst, CapyTy.rename, ih]

/-- Substituting a substitution lifted from a renaming is the same as renaming for pure types. -/
theorem CapyPureTy.subst_asSubst {T : CapyPureTy s1} {f : Rename s1 s2} :
  T.subst ((CapyRename.asSubst f)) = T.rename f := by
  simp only [CapyPureTy.subst, CapyPureTy.rename, CapyTy.subst_asSubst]

/-- Substituting a substitution lifted from a renaming is the same as renaming. -/
theorem CapyExp.subst_asSubst {e : CapyExp s1} {f : Rename s1 s2} :
  e.subst ((CapyRename.asSubst f)) = e.rename f := by
  induction e generalizing s2 with
  | var x =>
    simp only [CapyExp.subst, CapyExp.rename, CapyVar.subst_asSubst]
  | abs T e ih =>
    have hT := CapyTy.subst_asSubst (T := T) (f := f.lift)
    have he := ih (f := f.lift)
    simp only [CapyExp.subst, CapyExp.rename, ← CapyRename.asSubst_lift]
    congr 1
  | tabs T e ih =>
    simp only [CapyExp.subst, CapyExp.rename, CapyPureTy.subst_asSubst]
    rw [← CapyRename.asSubst_lift]
    exact congrArg (CapyExp.tabs (T.rename f)) ih
  | cabs cb e ih =>
    simp only [CapyExp.subst, CapyExp.rename, CapyCaptureBound.subst_asSubst]
    rw [← CapyRename.asSubst_lift]
    exact congrArg (CapyExp.cabs (cb.rename f)) ih
  | alloc x =>
    simp only [CapyExp.subst, CapyExp.rename, CapyVar.subst_asSubst]
  | drop x =>
    simp only [CapyExp.subst, CapyExp.rename, CapyVar.subst_asSubst]
  | app x y =>
    simp only [CapyExp.subst, CapyExp.rename, CapyVar.subst_asSubst]
  | tapp x T =>
    simp only [CapyExp.subst, CapyExp.rename, CapyVar.subst_asSubst, CapyPureTy.subst_asSubst]
  | capp x cs =>
    simp only [CapyExp.subst, CapyExp.rename, CapyVar.subst_asSubst, CapyCaptureSet.subst_asSubst]
  | letin e1 e2 ih1 ih2 =>
    simp only [CapyExp.subst, CapyExp.rename, ih1]
    rw [← CapyRename.asSubst_lift]
    exact congrArg (CapyExp.letin (e1.rename f)) ih2
  | unit =>
    rfl
  | btrue =>
    rfl
  | bfalse =>
    rfl
  | read x =>
    simp only [CapyExp.subst, CapyExp.rename, CapyVar.subst_asSubst]
  | write x y =>
    simp only [CapyExp.subst, CapyExp.rename, CapyVar.subst_asSubst]
  | cond x e2 e3 ih2 ih3 =>
    simp only [CapyExp.subst, CapyExp.rename, CapyVar.subst_asSubst, ih2, ih3]
  | par e1 e2 ih1 ih2 =>
    simp only [CapyExp.subst, CapyExp.rename, ih1, ih2]

theorem CapySubst.weaken_openVar {z : Var .var s} :
  (CapyRename.asSubst Rename.succ).comp (CapySubst.openVar z) = CapySubst.id := by
  apply CapySubst.funext
  · intro x; rfl
  · intro X; rfl
  · intro C; rfl

theorem CapySubst.weaken_openTVar {U : CapyPureTy s} :
  (CapyRename.asSubst Rename.succ).comp (CapySubst.openTVar U) = CapySubst.id := by
  apply CapySubst.funext
  · intro x; rfl
  · intro X; rfl
  · intro C; rfl

theorem CapySubst.weaken_openCVar {C : CapyCaptureSet s} :
  (CapyRename.asSubst Rename.succ).comp (CapySubst.openCVar C) = CapySubst.id := by
  apply CapySubst.funext
  · intro x; rfl
  · intro X; rfl
  · intro C; rfl

theorem CapyCaptureSet.weaken_openVar {C : CapyCaptureSet (s)} {z : Var .var s} :
  CapyCaptureSet.subst (C.rename Rename.succ) (CapySubst.openVar z) = C := by
  calc CapyCaptureSet.subst (C.rename Rename.succ) (CapySubst.openVar z)
      = CapyCaptureSet.subst ((CapyCaptureSet.subst C) (CapyRename.asSubst Rename.succ))
          (CapySubst.openVar z) := by rw [<-CapyCaptureSet.subst_asSubst]
    _ = (CapyCaptureSet.subst C) ((CapyRename.asSubst Rename.succ).comp (CapySubst.openVar z))
        := by rw [CapyCaptureSet.subst_comp]
    _ = (CapyCaptureSet.subst C) CapySubst.id := by rw [CapySubst.weaken_openVar]
    _ = C := by rw [CapyCaptureSet.subst_id]

theorem CapyCaptureSet.weaken_openTVar {C : CapyCaptureSet (s)} {U : CapyPureTy s} :
  CapyCaptureSet.subst (C.rename Rename.succ) (CapySubst.openTVar U) = C := by
  calc CapyCaptureSet.subst (C.rename Rename.succ) (CapySubst.openTVar U)
      = CapyCaptureSet.subst ((CapyCaptureSet.subst C) (CapyRename.asSubst Rename.succ))
          (CapySubst.openTVar U) := by rw [<-CapyCaptureSet.subst_asSubst]
    _ = (CapyCaptureSet.subst C) ((CapyRename.asSubst Rename.succ).comp (CapySubst.openTVar U))
        := by rw [CapyCaptureSet.subst_comp]
    _ = (CapyCaptureSet.subst C) CapySubst.id := by rw [CapySubst.weaken_openTVar]
    _ = C := by rw [CapyCaptureSet.subst_id]

theorem CapyCaptureSet.weaken_openCVar {C : CapyCaptureSet (s)} {C' : CapyCaptureSet s} :
  CapyCaptureSet.subst (C.rename Rename.succ) (CapySubst.openCVar C') = C := by
  calc CapyCaptureSet.subst (C.rename Rename.succ) (CapySubst.openCVar C')
      = CapyCaptureSet.subst ((CapyCaptureSet.subst C) (CapyRename.asSubst Rename.succ))
          (CapySubst.openCVar C') := by
        rw [<-CapyCaptureSet.subst_asSubst]
    _ = (CapyCaptureSet.subst C) ((CapyRename.asSubst Rename.succ).comp (CapySubst.openCVar C'))
        := by rw [CapyCaptureSet.subst_comp]
    _ = (CapyCaptureSet.subst C) CapySubst.id := by rw [CapySubst.weaken_openCVar]
    _ = C := by rw [CapyCaptureSet.subst_id]

theorem CapyCaptureSet.ground_rename_invariant {C : CapyCaptureSet {}} :
  C.rename f = C := by
  induction C with
  | empty => rfl
  | union cs1 cs2 ih1 ih2 =>
    simp only [CapyCaptureSet.rename]
    rw [ih1, ih2]
  | var m x =>
    cases x with
    | bound bx => cases bx
    | free n =>
      simp only [CapyCaptureSet.rename, Var.rename]
  | cvar m c => cases c

theorem CapyCaptureSet.ground_subst_invariant {C : CapyCaptureSet {}} :
  (CapyCaptureSet.subst C) σ = C := by
  induction C with
  | empty => rfl
  | union cs1 cs2 ih1 ih2 =>
    simp only [CapyCaptureSet.subst]
    rw [ih1, ih2]
  | var m x =>
    cases x with
    | bound bx => cases bx
    | free n => simp only [CapyCaptureSet.subst, CapyVar.subst]
  | cvar m c => cases c

/-- A substitution is closed if all its images are closed. -/
structure CapySubst.IsClosed (σ : CapySubst s1 s2) : Prop where
  var_closed : ∀ x, (σ.var x).IsClosed
  tvar_closed : ∀ X, (σ.tvar X).IsClosed
  cvar_closed : ∀ C, (σ.cvar C).IsClosed

/-- Substitution preserves closedness for variables. -/
def CapyVar.is_closed_subst {x : Var .var s1} {σ : CapySubst s1 s2}
  (hc : x.IsClosed) (hsubst : CapySubst.IsClosed σ) :
  ((CapyVar.subst x) σ).IsClosed := by
  cases x with
  | bound x =>
    exact hsubst.var_closed x
  | free n => cases hc

/-- Substitution preserves closedness for capture sets. -/
def CapyCaptureSet.is_closed_subst {cs : CapyCaptureSet s1} {σ : CapySubst s1 s2}
  (hc : cs.IsClosed) (hsubst : CapySubst.IsClosed σ) :
  ((CapyCaptureSet.subst cs) σ).IsClosed := by
  induction cs with
  | empty =>
    exact CapyCaptureSet.IsClosed.empty
  | union cs1 cs2 ih1 ih2 =>
    cases hc with | union h1 h2 =>
    simp only [CapyCaptureSet.subst]
    exact CapyCaptureSet.IsClosed.union (ih1 h1) (ih2 h2)
  | cvar m C =>
    simp only [CapyCaptureSet.subst]
    exact CapyCaptureSet.applyAccess_isClosed (hsubst.cvar_closed C)
  | var m x =>
    cases hc with | var_bound =>
    rename_i bx
    simp only [CapyCaptureSet.subst, CapyVar.subst]
    generalize h_eq : σ.var bx = v
    have h_var : v.IsClosed := h_eq ▸ hsubst.var_closed bx
    cases v with
    | bound y =>
      exact CapyCaptureSet.IsClosed.var_bound
    | free n =>
      cases h_var

private theorem Var.rename_closed_any {x : Var .var s1} {f : Rename s1 s2}
  (hc : x.IsClosed) : (x.rename f).IsClosed := by
  cases x with
  | bound _ => exact IsClosed.bound
  | free _ => cases hc

private theorem CapyCaptureSet.rename_closed_any {cs : CapyCaptureSet s1} {f : Rename s1 s2}
  (hc : cs.IsClosed) : (cs.rename f).IsClosed := by
  induction cs with
  | empty => exact CapyCaptureSet.IsClosed.empty
  | union cs1 cs2 ih1 ih2 =>
    cases hc with | union h1 h2 =>
    exact CapyCaptureSet.IsClosed.union (ih1 h1) (ih2 h2)
  | cvar => exact CapyCaptureSet.IsClosed.cvar
  | var x =>
    cases hc with | var_bound =>
    exact CapyCaptureSet.IsClosed.var_bound

private theorem CapyCaptureBound.rename_closed_any {cb : CapyCaptureBound s1} {f : Rename s1 s2}
  (hc : cb.IsClosed) : (cb.rename f).IsClosed := by
  cases hc with
  | unbound => exact CapyCaptureBound.IsClosed.unbound
  | bound hcs => exact CapyCaptureBound.IsClosed.bound (CapyCaptureSet.rename_closed_any hcs)

private theorem CapyTy.rename_closed_any {T : CapyTy sort s1} {f : Rename s1 s2}
  (hc : T.IsClosed) : (T.rename f).IsClosed := by
  induction T generalizing s2 with
  | top => exact IsClosed.top
  | tvar => exact IsClosed.tvar
  | arrow T1 cs T2 ih1 ih2 =>
    cases hc with | arrow h1 hcs h2 =>
    exact IsClosed.arrow (ih1 h1)
      (CapyCaptureSet.rename_closed_any hcs) (ih2 h2)
  | poly T1 cs T2 ih1 ih2 =>
    cases hc with | poly h1 hcs h2 =>
    exact IsClosed.poly (ih1 h1)
      (CapyCaptureSet.rename_closed_any hcs) (ih2 h2)
  | cpoly cb cs T ih =>
    cases hc with | cpoly hcb hcs hT =>
    exact IsClosed.cpoly (CapyCaptureBound.rename_closed_any hcb)
      (CapyCaptureSet.rename_closed_any hcs) (ih hT)
  | unit => exact IsClosed.unit
  | cap cs =>
    cases hc with | cap hcs =>
    exact IsClosed.cap (CapyCaptureSet.rename_closed_any hcs)
  | bool => exact IsClosed.bool
  | cell cs m =>
    cases hc with | cell hcs =>
    exact IsClosed.cell (CapyCaptureSet.rename_closed_any hcs)
  | exi T ih =>
    cases hc with | exi hT =>
    exact IsClosed.exi (ih hT)
  | typ T ih =>
    cases hc with | typ hT =>
    exact IsClosed.typ (ih hT)

/-- Lifting preserves closedness of substitutions. -/
theorem CapySubst.lift_closed {σ : CapySubst s1 s2} (hσ : σ.IsClosed) :
  (σ.lift (k:=k)).IsClosed := by
  constructor
  · intro x
    cases x with
    | here => exact Var.IsClosed.bound
    | there x => simp only [CapySubst.lift]; exact Var.rename_closed_any (hσ.var_closed x)
  · intro X
    cases X with
    | here => exact CapyTy.IsClosed.tvar
    | there X => simp only [CapySubst.lift]; exact CapyTy.rename_closed_any (hσ.tvar_closed X)
  · intro C
    cases C with
    | here => exact CapyCaptureSet.IsClosed.cvar
    | there C =>
      simp only [CapySubst.lift]
      exact CapyCaptureSet.rename_closed_any (hσ.cvar_closed C)

def CapyCaptureBound.is_closed_subst {cb : CapyCaptureBound s1} {σ : CapySubst s1 s2}
  (hc : cb.IsClosed) (hsubst : CapySubst.IsClosed σ) :
  (cb.subst σ).IsClosed := by
  cases hc with
  | unbound =>
    simp only [CapyCaptureBound.subst]
    exact CapyCaptureBound.IsClosed.unbound
  | bound hcs =>
    simp only [CapyCaptureBound.subst]
    exact CapyCaptureBound.IsClosed.bound (CapyCaptureSet.is_closed_subst hcs hsubst)

/-- Substitution preserves closedness for types. -/
def CapyTy.is_closed_subst {T : CapyTy sort s1} {σ : CapySubst s1 s2}
  (hc : T.IsClosed) (hsubst : CapySubst.IsClosed σ) :
  (T.subst σ).IsClosed := by
  induction T generalizing s2 with
  | top => exact IsClosed.top
  | tvar X => simp only [CapyTy.subst]; exact hsubst.tvar_closed X
  | arrow T1 cs T2 ih1 ih2 =>
    cases hc with | arrow h1 hcs h2 =>
    simp only [CapyTy.subst]
    exact IsClosed.arrow (ih1 h1 (CapySubst.lift_closed hsubst))
      (CapyCaptureSet.is_closed_subst hcs hsubst)
      (ih2 h2 (CapySubst.lift_closed hsubst))
  | poly T1 cs T2 ih1 ih2 =>
    cases hc with | poly h1 hcs h2 =>
    simp only [CapyTy.subst]
    exact IsClosed.poly (ih1 h1 hsubst)
      (CapyCaptureSet.is_closed_subst hcs hsubst)
      (ih2 h2 (CapySubst.lift_closed hsubst))
  | cpoly cb cs T ih =>
    cases hc with | cpoly hcb hcs hT =>
    simp only [CapyTy.subst]
    exact IsClosed.cpoly (CapyCaptureBound.is_closed_subst hcb hsubst)
      (CapyCaptureSet.is_closed_subst hcs hsubst)
      (ih hT (CapySubst.lift_closed hsubst))
  | unit => exact IsClosed.unit
  | cap cs =>
    cases hc with | cap hcs =>
    simp only [CapyTy.subst]
    exact IsClosed.cap (CapyCaptureSet.is_closed_subst hcs hsubst)
  | bool => exact IsClosed.bool
  | cell cs m =>
    cases hc with | cell hcs =>
    simp only [CapyTy.subst]
    exact IsClosed.cell (CapyCaptureSet.is_closed_subst hcs hsubst)
  | exi T ih =>
    cases hc with | exi hT =>
    simp only [CapyTy.subst]
    exact IsClosed.exi (ih hT (CapySubst.lift_closed hsubst))
  | typ T ih =>
    cases hc with | typ hT =>
    simp only [CapyTy.subst]
    exact IsClosed.typ (ih hT hsubst)

/-- Substitution preserves closedness for expressions. -/
def CapyExp.is_closed_subst {e : CapyExp s1} {σ : CapySubst s1 s2}
  (hc : e.IsClosed) (hsubst : CapySubst.IsClosed σ) :
  (e.subst σ).IsClosed := by
  induction e generalizing s2 with
  | var x =>
    cases hc with | var hx =>
    simp only [CapyExp.subst]
    constructor
    exact CapyVar.is_closed_subst hx hsubst
  | abs T e ih =>
    cases hc with | abs hT he =>
    simp only [CapyExp.subst]
    constructor
    · exact CapyTy.is_closed_subst hT (CapySubst.lift_closed hsubst)
    · exact ih he (CapySubst.lift_closed hsubst)
  | tabs S e ih =>
    cases hc with | tabs hS he =>
    simp only [CapyExp.subst]
    constructor
    · exact CapyTy.is_closed_subst hS hsubst
    · exact ih he (CapySubst.lift_closed hsubst)
  | cabs cb e ih =>
    cases hc with | cabs hcb he =>
    simp only [CapyExp.subst]
    constructor
    · exact CapyCaptureBound.is_closed_subst hcb hsubst
    · exact ih he (CapySubst.lift_closed hsubst)
  | alloc x =>
    cases hc with | alloc hx =>
    simp only [CapyExp.subst]
    exact IsClosed.alloc (CapyVar.is_closed_subst hx hsubst)
  | drop x =>
    cases hc with | drop hx =>
    simp only [CapyExp.subst]
    exact IsClosed.drop (CapyVar.is_closed_subst hx hsubst)
  | app x y =>
    cases hc with | app hx hy =>
    simp only [CapyExp.subst]
    constructor
    · exact CapyVar.is_closed_subst hx hsubst
    · exact CapyVar.is_closed_subst hy hsubst
  | tapp x T =>
    cases hc with | tapp hx hT =>
    simp only [CapyExp.subst]
    constructor
    · exact CapyVar.is_closed_subst hx hsubst
    · exact CapyTy.is_closed_subst hT hsubst
  | capp x cs =>
    cases hc with | capp hx hcs =>
    simp only [CapyExp.subst]
    constructor
    · exact CapyVar.is_closed_subst hx hsubst
    · exact CapyCaptureSet.is_closed_subst hcs hsubst
  | letin e1 e2 ih1 ih2 =>
    cases hc with | letin he1 he2 =>
    simp only [CapyExp.subst]
    constructor
    · exact ih1 he1 hsubst
    · exact ih2 he2 (CapySubst.lift_closed hsubst)
  | unit =>
    exact IsClosed.unit
  | btrue =>
    exact IsClosed.btrue
  | bfalse =>
    exact IsClosed.bfalse
  | read x =>
    cases hc with | read hx =>
    simp only [CapyExp.subst]
    exact IsClosed.read (CapyVar.is_closed_subst hx hsubst)
  | write x y =>
    cases hc with | write hx hy =>
    simp only [CapyExp.subst]
    exact IsClosed.write (CapyVar.is_closed_subst hx hsubst) (CapyVar.is_closed_subst hy hsubst)
  | cond x e2 e3 ih2 ih3 =>
    cases hc with | cond hx h2 h3 =>
    simp only [CapyExp.subst]
    exact IsClosed.cond (CapyVar.is_closed_subst hx hsubst) (ih2 h2 hsubst) (ih3 h3 hsubst)
  | par e1 e2 ih1 ih2 =>
    cases hc with | par h1 h2 =>
    simp only [CapyExp.subst]
    exact IsClosed.par (ih1 h1 hsubst) (ih2 h2 hsubst)

/-- The openVar substitution is closed if the variable is closed. -/
theorem CapySubst.openVar_is_closed {z : Var .var s}
  (hz : z.IsClosed) :
  (CapySubst.openVar z).IsClosed where
  var_closed := fun x => by
    cases x with
    | here => exact hz
    | there x => exact Var.IsClosed.bound
  tvar_closed := fun X => by
    cases X with
    | there X => exact CapyTy.IsClosed.tvar
  cvar_closed := fun C => by
    cases C with
    | there C => exact CapyCaptureSet.IsClosed.cvar

/-- The openTVar substitution is closed if the type is closed. -/
theorem CapySubst.openTVar_is_closed {U : CapyPureTy s}
  (hU : U.IsClosed) :
  (CapySubst.openTVar U).IsClosed where
  var_closed := fun x => by
    cases x with
    | there x => exact Var.IsClosed.bound
  tvar_closed := fun X => by
    cases X with
    | here => exact hU
    | there X => exact CapyTy.IsClosed.tvar
  cvar_closed := fun C => by
    cases C with
    | there C => exact CapyCaptureSet.IsClosed.cvar

/-- The openCVar substitution is closed if the capture set is closed. -/
theorem CapySubst.openCVar_is_closed {C : CapyCaptureSet s}
  (hC : C.IsClosed) :
  (CapySubst.openCVar C).IsClosed where
  var_closed := fun x => by
    cases x with
    | there x => exact Var.IsClosed.bound
  tvar_closed := fun X => by
    cases X with
    | there X => exact CapyTy.IsClosed.tvar
  cvar_closed := fun c => by
    cases c with
    | here => exact hC
    | there c => exact CapyCaptureSet.IsClosed.cvar

/-- If the result of substitution is closed, the original variable was closed. -/
theorem CapyVar.subst_closed_inv {x : Var .var s1} {σ : CapySubst s1 s2}
  (hclosed : ((CapyVar.subst x) σ).IsClosed) :
  x.IsClosed := by
  cases x with
  | bound bx => constructor
  | free n =>
    simp only [CapyVar.subst] at hclosed
    cases hclosed

/-- If the result of substitution is closed, the original capture set was closed. -/
theorem CapyCaptureSet.subst_closed_inv {cs : CapyCaptureSet s1} {σ : CapySubst s1 s2}
  (hclosed : ((CapyCaptureSet.subst cs) σ).IsClosed) :
  cs.IsClosed := by
  induction cs with
  | empty => exact CapyCaptureSet.IsClosed.empty
  | union cs1 cs2 ih1 ih2 =>
    simp only [CapyCaptureSet.subst] at hclosed
    cases hclosed with | union h1 h2 =>
    exact CapyCaptureSet.IsClosed.union (ih1 h1) (ih2 h2)
  | cvar m C => exact CapyCaptureSet.IsClosed.cvar
  | var m x =>
    cases x with
    | bound bx =>
      exact CapyCaptureSet.IsClosed.var_bound
    | free n =>
      simp only [CapyCaptureSet.subst, CapyVar.subst] at hclosed
      cases hclosed

theorem CapyCaptureBound.subst_closed_inv {cb : CapyCaptureBound s1} {σ : CapySubst s1 s2}
  (hclosed : (cb.subst σ).IsClosed) :
  cb.IsClosed := by
  cases cb with
  | unbound => exact CapyCaptureBound.IsClosed.unbound
  | bound cs =>
    simp only [CapyCaptureBound.subst] at hclosed
    cases hclosed with
    | bound hcs =>
      exact CapyCaptureBound.IsClosed.bound (CapyCaptureSet.subst_closed_inv hcs)

/-- If the result of substitution is closed, the original type was closed. -/
theorem CapyTy.subst_closed_inv {T : CapyTy sort s1} {σ : CapySubst s1 s2}
  (hclosed : (T.subst σ).IsClosed) :
  T.IsClosed := by
  induction T generalizing s2 with
  | top => exact IsClosed.top
  | tvar X => exact IsClosed.tvar
  | arrow T1 cs T2 ih1 ih2 =>
    simp only [CapyTy.subst] at hclosed
    cases hclosed with | arrow h1 hcs h2 =>
    exact IsClosed.arrow (ih1 h1)
      (CapyCaptureSet.subst_closed_inv hcs) (ih2 h2)
  | poly T1 cs T2 ih1 ih2 =>
    simp only [CapyTy.subst] at hclosed
    cases hclosed with | poly h1 hcs h2 =>
    exact IsClosed.poly (ih1 h1)
      (CapyCaptureSet.subst_closed_inv hcs) (ih2 h2)
  | cpoly cb cs T ih =>
    simp only [CapyTy.subst] at hclosed
    cases hclosed with | cpoly hcb hcs hT =>
    exact IsClosed.cpoly (CapyCaptureBound.subst_closed_inv hcb)
      (CapyCaptureSet.subst_closed_inv hcs) (ih hT)
  | unit => exact IsClosed.unit
  | cap cs =>
    simp only [CapyTy.subst] at hclosed
    cases hclosed with | cap hcs =>
    exact IsClosed.cap (CapyCaptureSet.subst_closed_inv hcs)
  | bool => exact IsClosed.bool
  | cell cs m =>
    simp only [CapyTy.subst] at hclosed
    cases hclosed with | cell hcs =>
    exact IsClosed.cell (CapyCaptureSet.subst_closed_inv hcs)
  | exi T ih =>
    simp only [CapyTy.subst] at hclosed
    cases hclosed with | exi hT =>
    exact IsClosed.exi (ih hT)
  | typ T ih =>
    simp only [CapyTy.subst] at hclosed
    cases hclosed with | typ hT =>
    exact IsClosed.typ (ih hT)

/-- If the result of substitution is closed, the original expression was closed. -/
theorem CapyExp.subst_closed_inv {e : CapyExp s1} {σ : CapySubst s1 s2}
  (hclosed : (e.subst σ).IsClosed) :
  e.IsClosed := by
  induction e generalizing s2 with
  | var x =>
    simp only [CapyExp.subst] at hclosed
    cases hclosed with | var hx =>
    exact IsClosed.var (CapyVar.subst_closed_inv hx)
  | abs T e ih =>
    simp only [CapyExp.subst] at hclosed
    cases hclosed with | abs hT he =>
    exact IsClosed.abs (CapyTy.subst_closed_inv hT) (ih he)
  | tabs T e ih =>
    simp only [CapyExp.subst] at hclosed
    cases hclosed with | tabs hT he =>
    exact IsClosed.tabs (CapyTy.subst_closed_inv hT) (ih he)
  | cabs cb e ih =>
    simp only [CapyExp.subst] at hclosed
    cases hclosed with | cabs hcb he =>
    exact IsClosed.cabs (CapyCaptureBound.subst_closed_inv hcb) (ih he)
  | alloc x =>
    simp only [CapyExp.subst] at hclosed
    cases hclosed with | alloc hx =>
    exact IsClosed.alloc (CapyVar.subst_closed_inv hx)
  | drop x =>
    simp only [CapyExp.subst] at hclosed
    cases hclosed with | drop hx =>
    exact IsClosed.drop (CapyVar.subst_closed_inv hx)
  | app x y =>
    simp only [CapyExp.subst] at hclosed
    cases hclosed with | app hx hy =>
    exact IsClosed.app (CapyVar.subst_closed_inv hx) (CapyVar.subst_closed_inv hy)
  | tapp x T =>
    simp only [CapyExp.subst] at hclosed
    cases hclosed with | tapp hx hT =>
    exact IsClosed.tapp (CapyVar.subst_closed_inv hx) (CapyTy.subst_closed_inv hT)
  | capp x cs =>
    simp only [CapyExp.subst] at hclosed
    cases hclosed with | capp hx hcs =>
    exact IsClosed.capp (CapyVar.subst_closed_inv hx) (CapyCaptureSet.subst_closed_inv hcs)
  | letin e1 e2 ih1 ih2 =>
    simp only [CapyExp.subst] at hclosed
    cases hclosed with | letin he1 he2 =>
    exact IsClosed.letin (ih1 he1) (ih2 he2)
  | unit => exact IsClosed.unit
  | btrue =>
    simp only [CapyExp.subst] at hclosed
    cases hclosed with | btrue => exact IsClosed.btrue
  | bfalse =>
    simp only [CapyExp.subst] at hclosed
    cases hclosed with | bfalse => exact IsClosed.bfalse
  | read x =>
    simp only [CapyExp.subst] at hclosed
    cases hclosed with | read hx =>
    exact IsClosed.read (CapyVar.subst_closed_inv hx)
  | write x y =>
    simp only [CapyExp.subst] at hclosed
    cases hclosed with | write hx hy =>
    exact IsClosed.write (CapyVar.subst_closed_inv hx) (CapyVar.subst_closed_inv hy)
  | cond x e2 e3 ih2 ih3 =>
    simp only [CapyExp.subst] at hclosed
    cases hclosed with | cond hx h2 h3 =>
    exact IsClosed.cond (CapyVar.subst_closed_inv hx) (ih2 h2) (ih3 h3)
  | par e1 e2 ih1 ih2 =>
    simp only [CapyExp.subst] at hclosed
    cases hclosed with | par h1 h2 =>
    exact IsClosed.par (ih1 h1) (ih2 h2)

end CoreCapybara
