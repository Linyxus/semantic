import Semantic.CaplessK.Syntax.Ty

/-!
Expression definitions and operations for CaplessK.
-/

namespace CaplessK

/-- An expression in CC. -/
inductive Exp : Sig -> Type where
| var : Var .var s -> Exp s
| abs : CaptureSet s -> Ty .capt s -> Exp (s,x) -> Exp s
| tabs : CaptureSet s -> Ty .shape s -> Exp (s,X) -> Exp s
| cabs : CaptureSet s -> CaptureBound s -> Exp (s,C) -> Exp s
| pack : CaptureSet s -> Var .var s -> Exp s
| app : Var .var s -> Var .var s -> Exp s
| tapp : Var .var s -> Ty .shape s -> Exp s
| capp : Var .var s -> CaptureSet s -> Exp s
| letin : Exp s -> Exp (s,x) -> Exp s
| unpack : Exp s -> Exp ((s,C),x) -> Exp s
| unit : Exp s
| btrue : Exp s
| bfalse : Exp s
| read : Var .var s -> Exp s
| write : Var .var s -> Var .var s -> Exp s
| cond : Var .var s -> Exp s -> Exp s -> Exp s
| boundary : CapKind -> Ty .shape s -> Exp (s,C,x) -> Exp s
| throw : Var .var s -> Var .var s -> Exp s

/-- Applies a renaming to all bound variables in an expression. -/
def Exp.rename : Exp s1 -> Rename s1 s2 -> Exp s2
| .var x, f => .var (x.rename f)
| .abs cs T e, f => .abs (cs.rename f) (T.rename f) (e.rename (f.lift))
| .tabs cs T e, f => .tabs (cs.rename f) (T.rename f) (e.rename (f.lift))
| .cabs cs cb e, f => .cabs (cs.rename f) (cb.rename f) (e.rename (f.lift))
| .pack cs x, f => .pack (cs.rename f) (x.rename f)
| .app x y, f => .app (x.rename f) (y.rename f)
| .tapp x T, f => .tapp (x.rename f) (T.rename f)
| .capp x cs, f => .capp (x.rename f) (cs.rename f)
| .letin e1 e2, f => .letin (e1.rename f) (e2.rename (f.lift))
| .unpack e1 e2, f => .unpack (e1.rename f) (e2.rename (f.lift.lift))
| .unit, _ => .unit
| .btrue, _ => .btrue
| .bfalse, _ => .bfalse
| .read x, f => .read (x.rename f)
| .write x y, f => .write (x.rename f) (y.rename f)
| .cond x e2 e3, f => .cond (x.rename f) (e2.rename f) (e3.rename f)
| .boundary k T e, f => .boundary k (T.rename f) (e.rename (f.lift.lift))

/-- An expression is a value if it is an abstraction, pack, or unit. -/
inductive Exp.IsVal : Exp s -> Prop where
| abs : Exp.IsVal (.abs cs T e)
| tabs : Exp.IsVal (.tabs cs T e)
| cabs : Exp.IsVal (.cabs cs cb e)
| pack : Exp.IsVal (.pack cs x)
| unit : Exp.IsVal .unit
| btrue : Exp.IsVal .btrue
| bfalse : Exp.IsVal .bfalse

/-- A simple value is a value that is not a pack. Therefore,
      a simple value always has a capturing type, not an existential type. -/
inductive Exp.IsSimpleVal : Exp s -> Prop where
| abs : Exp.IsSimpleVal (.abs cs T e)
| tabs : Exp.IsSimpleVal (.tabs cs T e)
| cabs : Exp.IsSimpleVal (.cabs cs cb e)
| unit : Exp.IsSimpleVal .unit
| btrue : Exp.IsSimpleVal .btrue
| bfalse : Exp.IsSimpleVal .bfalse

inductive Exp.IsSimpleAns : Exp s -> Prop where
| is_simple_val :
  (hv : Exp.IsSimpleVal v) ->
  Exp.IsSimpleAns v
| is_var :
  Exp.IsSimpleAns (.var x)

inductive Exp.IsPack : Exp s -> Prop where
| pack : Exp.IsPack (.pack cs x)

/-- A value, bundling an expression with a proof that it is a value. -/
structure Val (s : Sig) where
  unwrap : Exp s
  isVal : unwrap.IsVal

/-- Renaming by the identity renaming leaves a variable unchanged. -/
def Var.rename_id {x : Var k s} : x.rename (Rename.id) = x := by
  cases x <;> rfl

/-- Renaming by the identity renaming leaves an expression unchanged. -/
def Exp.rename_id {e : Exp s} : e.rename (Rename.id) = e := by
  induction e
    <;> try (solve
      | rfl
      | simp [Exp.rename, Ty.rename_id, Var.rename_id,
              CaptureSet.rename_id, CaptureBound.rename_id, Rename.lift_id]
        try aesop)

/-- Renaming distributes over composition of renamings. -/
theorem Var.rename_comp {x : Var k s1} {f : Rename s1 s2} {g : Rename s2 s3} :
    (x.rename f).rename g = x.rename (f.comp g) := by
  cases x <;> rfl

/-- Renaming distributes over composition of renamings. -/
theorem Exp.rename_comp {e : Exp s1} {f : Rename s1 s2} {g : Rename s2 s3} :
    (e.rename f).rename g = e.rename (f.comp g) := by
  induction e generalizing s2 s3
    <;> try (solve
      | rfl
      | simp [Exp.rename, Ty.rename_comp, Var.rename_comp,
              CaptureSet.rename_comp, CaptureBound.rename_comp, Rename.lift_comp]
        try aesop)

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
| abs : CaptureSet.IsClosed cs -> Ty.IsClosed T -> Exp.IsClosed e ->
    Exp.IsClosed (.abs cs T e)
| tabs : CaptureSet.IsClosed cs -> Ty.IsClosed T -> Exp.IsClosed e ->
    Exp.IsClosed (.tabs cs T e)
| cabs : CaptureSet.IsClosed cs -> CaptureBound.IsClosed cb -> Exp.IsClosed e ->
    Exp.IsClosed (.cabs cs cb e)
| pack : CaptureSet.IsClosed cs -> Var.IsClosed x -> Exp.IsClosed (.pack cs x)
| app : Var.IsClosed x -> Var.IsClosed y -> Exp.IsClosed (.app x y)
| tapp : Var.IsClosed x -> Ty.IsClosed T -> Exp.IsClosed (.tapp x T)
| capp : Var.IsClosed x -> CaptureSet.IsClosed cs -> Exp.IsClosed (.capp x cs)
| letin : Exp.IsClosed e1 -> Exp.IsClosed e2 -> Exp.IsClosed (.letin e1 e2)
| unpack : Exp.IsClosed e1 -> Exp.IsClosed e2 -> Exp.IsClosed (.unpack e1 e2)
| unit : Exp.IsClosed .unit
| btrue : Exp.IsClosed .btrue
| bfalse : Exp.IsClosed .bfalse
| read : Var.IsClosed x -> Exp.IsClosed (.read x)
| write : Var.IsClosed x -> Var.IsClosed y -> Exp.IsClosed (.write x y)
| cond : Var.IsClosed x -> Exp.IsClosed e2 -> Exp.IsClosed e3 -> Exp.IsClosed (.cond x e2 e3)
| boundary : Ty.IsClosed T -> Exp.IsClosed e -> Exp.IsClosed (.boundary k T e)

end CaplessK
