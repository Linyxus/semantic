import Semantic.Capybara.Syntax.Ty

/-!
Expression definitions and operations for CC.
-/

namespace Capybara

/-- An expression in CC. -/
inductive Exp : Sig -> Type where
| var : Var .var s -> Exp s
| abs : Ty (s,C) -> Exp (s,x) -> Exp s
| tabs : PureTy s -> Exp (s,X) -> Exp s
| cabs : CaptureBound s -> Exp (s,C) -> Exp s
| alloc : Var .var s -> Exp s
| read : Var .var s -> Exp s
| write : Var .var s -> Var .var s -> Exp s
| drop : Var .var s -> Exp s
| app : Var .var s -> Var .var s -> Exp s
| tapp : Var .var s -> PureTy s -> Exp s
| capp : Var .var s -> CaptureSet s -> Exp s
| letin : Exp s -> Exp (s,x) -> Exp s
| unit : Exp s
| btrue : Exp s
| bfalse : Exp s
| cond : Var .var s -> Exp s -> Exp s -> Exp s
| par :
  Exp s -> Exp s ->
  Exp s

/-- Applies a renaming to all bound variables in an expression. -/
def Exp.rename : Exp s1 -> Rename s1 s2 -> Exp s2
| .var x, f => .var (x.rename f)
| .abs T e, f => .abs (T.rename (f.lift)) (e.rename (f.lift))
| .tabs T e, f => .tabs (T.rename f) (e.rename (f.lift))
| .cabs cb e, f => .cabs (cb.rename f) (e.rename (f.lift))
| .alloc x, f => .alloc (x.rename f)
| .drop x, f => .drop (x.rename f)
| .app x y, f => .app (x.rename f) (y.rename f)
| .tapp x T, f => .tapp (x.rename f) (T.rename f)
| .capp x cs, f => .capp (x.rename f) (cs.rename f)
| .letin e1 e2, f => .letin (e1.rename f) (e2.rename (f.lift))
| .unit, _ => .unit
| .btrue, _ => .btrue
| .bfalse, _ => .bfalse
| .read x, f => .read (x.rename f)
| .write x y, f => .write (x.rename f) (y.rename f)
| .cond x e2 e3, f => .cond (x.rename f) (e2.rename f) (e3.rename f)
| .par e1 e2, f => .par (e1.rename f) (e2.rename f)

/-- An expression is a value if it is an abstraction, pack, or unit. -/
inductive Exp.IsVal : Exp s -> Prop where
| abs : Exp.IsVal (.abs T e)
| tabs : Exp.IsVal (.tabs T e)
| cabs : Exp.IsVal (.cabs m e)
| unit : Exp.IsVal .unit
| btrue : Exp.IsVal .btrue
| bfalse : Exp.IsVal .bfalse

/-- A simple value is a value that is not a pack. Therefore,
      a simple value always has a capturing type, not an existential type. -/
inductive Exp.IsSimpleVal : Exp s -> Prop where
| abs : Exp.IsSimpleVal (.abs T e)
| tabs : Exp.IsSimpleVal (.tabs T e)
| cabs : Exp.IsSimpleVal (.cabs m e)
| unit : Exp.IsSimpleVal .unit
| btrue : Exp.IsSimpleVal .btrue
| bfalse : Exp.IsSimpleVal .bfalse

inductive Exp.IsSimpleAns : Exp s -> Prop where
| is_simple_val :
  (hv : Exp.IsSimpleVal v) ->
  Exp.IsSimpleAns v
| is_var :
  Exp.IsSimpleAns (.var x)

/-- A value, bundling an expression with a proof that it is a value. -/
structure Val (s : Sig) where
  unwrap : Exp s
  isVal : unwrap.IsVal

/-- Renaming by the identity renaming leaves a variable unchanged. -/
def Var.rename_id {x : Var k s} : x.rename (Rename.id) = x := by
  cases x <;> rfl

/-- Renaming by the identity renaming leaves an expression unchanged. -/
def Exp.rename_id {e : Exp s} : e.rename (Rename.id) = e := by
  induction e with
  | var x =>
    simp only [Exp.rename, Var.rename_id]
  | abs T e ih =>
    simp only [Exp.rename, Rename.lift_id]
    have hT : T.rename Rename.id = T := Ty.rename_id
    congr 1
  | tabs T e ih =>
    simp only [Exp.rename, PureTy.rename_id, Rename.lift_id]
    exact congrArg (Exp.tabs T) ih
  | cabs cb e ih =>
    simp only [Exp.rename, CaptureBound.rename_id, Rename.lift_id]
    exact congrArg (Exp.cabs cb) ih
  | alloc x =>
    simp only [Exp.rename, Var.rename_id]
  | drop x =>
    simp only [Exp.rename, Var.rename_id]
  | app x y =>
    simp only [Exp.rename, Var.rename_id]
  | tapp x T =>
    simp only [Exp.rename, Var.rename_id, PureTy.rename_id]
  | capp x cs =>
    simp only [Exp.rename, Var.rename_id, CaptureSet.rename_id]
  | letin e1 e2 ih1 ih2 =>
    simp only [Exp.rename, Rename.lift_id, ih1]
    exact congrArg (Exp.letin e1) ih2
  | unit => rfl
  | btrue => rfl
  | bfalse => rfl
  | read x =>
    simp only [Exp.rename, Var.rename_id]
  | write x y =>
    simp only [Exp.rename, Var.rename_id]
  | cond x e2 e3 ih2 ih3 =>
    simp only [Exp.rename, Var.rename_id, ih2]
    exact congrArg (Exp.cond x e2) ih3
  | par e1 e2 ih1 ih2 =>
    simp only [Exp.rename, ih1, ih2]

/-- Renaming distributes over composition of renamings. -/
theorem Var.rename_comp {x : Var k s1} {f : Rename s1 s2} {g : Rename s2 s3} :
    (x.rename f).rename g = x.rename (f.comp g) := by
  cases x <;> rfl

/-- Renaming distributes over composition of renamings. -/
theorem Exp.rename_comp {e : Exp s1} {f : Rename s1 s2} {g : Rename s2 s3} :
    (e.rename f).rename g = e.rename (f.comp g) := by
  induction e generalizing s2 s3 with
  | var x =>
    simp only [Exp.rename, Var.rename_comp]
  | abs T e ih =>
    simpa only [Exp.rename, Ty.rename_comp, Rename.lift_comp] using
      congrArg (Exp.abs (T.rename (f.lift.comp g.lift)))
        (ih (f := f.lift) (g := g.lift))
  | tabs T e ih =>
    simpa only [Exp.rename, PureTy.rename_comp, Rename.lift_comp] using
      congrArg (Exp.tabs (T.rename (f.comp g)))
        (ih (f := f.lift) (g := g.lift))
  | cabs cb e ih =>
    simpa only [
      Exp.rename,
      CaptureBound.rename_comp,
      Rename.lift_comp
    ] using
      congrArg (Exp.cabs (cb.rename (f.comp g)))
        (ih (f := f.lift) (g := g.lift))
  | alloc x =>
    simp only [Exp.rename, Var.rename_comp]
  | drop x =>
    simp only [Exp.rename, Var.rename_comp]
  | app x y =>
    simp only [Exp.rename, Var.rename_comp]
  | tapp x T =>
    simp only [Exp.rename, Var.rename_comp, PureTy.rename_comp]
  | capp x cs =>
    simp only [Exp.rename, Var.rename_comp, CaptureSet.rename_comp]
  | letin e1 e2 ih1 ih2 =>
    simpa only [Exp.rename, Rename.lift_comp, ih1] using
      congrArg (Exp.letin (e1.rename (f.comp g))) (ih2 (f := f.lift) (g := g.lift))
  | unit => rfl
  | btrue => rfl
  | bfalse => rfl
  | read x =>
    simp only [Exp.rename, Var.rename_comp]
  | write x y =>
    simp only [Exp.rename, Var.rename_comp]
  | cond x e2 e3 ih2 ih3 =>
    simpa only [Exp.rename, Var.rename_comp, ih2] using
      congrArg (Exp.cond (x.rename (f.comp g)) (e2.rename (f.comp g))) (ih3 (f := f) (g := g))
  | par e1 e2 ih1 ih2 =>
    simp only [Exp.rename, ih1, ih2]

/-- Weakening commutes with renaming under a binder. -/
theorem Var.weaken_rename_comm {x : Var k s1} {f : Rename s1 s2} :
    (x.rename Rename.succ).rename (f.lift (k:=k0)) = (x.rename f).rename (Rename.succ) := by
  simp [Var.rename_comp, Rename.succ_lift_comm]

/-- An answer is a value or a free variable in the empty context. -/
inductive Exp.IsAns : Exp {} -> Prop where
| is_val :
  (hv : Exp.IsVal v) ->
  Exp.IsAns v
| is_var :
  Exp.IsAns (.var x)

/-- An expression is closed if it contains no heap pointers. -/
inductive Exp.IsClosed : Exp s -> Prop where
| var : Var.IsClosed x -> Exp.IsClosed (.var x)
| abs : Ty.IsClosed T -> Exp.IsClosed e ->
    Exp.IsClosed (.abs T e)
| tabs : PureTy.IsClosed T -> Exp.IsClosed e ->
    Exp.IsClosed (.tabs T e)
| cabs : CaptureBound.IsClosed cb -> Exp.IsClosed e ->
    Exp.IsClosed (.cabs cb e)
| alloc : Var.IsClosed x -> Exp.IsClosed (.alloc x)
| drop : Var.IsClosed x -> Exp.IsClosed (.drop x)
| app : Var.IsClosed x -> Var.IsClosed y -> Exp.IsClosed (.app x y)
| tapp : Var.IsClosed x -> PureTy.IsClosed T -> Exp.IsClosed (.tapp x T)
| capp : Var.IsClosed x -> CaptureSet.IsClosed cs -> Exp.IsClosed (.capp x cs)
| letin : Exp.IsClosed e1 -> Exp.IsClosed e2 -> Exp.IsClosed (.letin e1 e2)
| unit : Exp.IsClosed .unit
| btrue : Exp.IsClosed .btrue
| bfalse : Exp.IsClosed .bfalse
| read : Var.IsClosed x -> Exp.IsClosed (.read x)
| write : Var.IsClosed x -> Var.IsClosed y -> Exp.IsClosed (.write x y)
| cond : Var.IsClosed x -> Exp.IsClosed e2 -> Exp.IsClosed e3 -> Exp.IsClosed (.cond x e2 e3)
| par : Exp.IsClosed e1 -> Exp.IsClosed e2 -> Exp.IsClosed (.par e1 e2)

end Capybara
