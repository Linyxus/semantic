import Semantic.CoreCapybara.Capybara.Syntax.Ty

/-!
Expression definitions and operations for CC.
-/

namespace CoreCapybara

/-- An expression in CC. -/
inductive CapyExp : Sig -> Type where
| var : Var .var s -> CapyExp s
| abs : CapyTy .capt (s,C) -> CapyExp (s,x) -> CapyExp s
| tabs : CapyPureTy s -> CapyExp (s,X) -> CapyExp s
| cabs : CapyCaptureBound s -> CapyExp (s,C) -> CapyExp s
| alloc : Var .var s -> CapyExp s
| read : Var .var s -> CapyExp s
| write : Var .var s -> Var .var s -> CapyExp s
| drop : Var .var s -> CapyExp s
| app : Var .var s -> Var .var s -> CapyExp s
| tapp : Var .var s -> CapyPureTy s -> CapyExp s
| capp : Var .var s -> CaptureSet s -> CapyExp s
| letin : CapyExp s -> CapyExp (s,x) -> CapyExp s
| unit : CapyExp s
| btrue : CapyExp s
| bfalse : CapyExp s
| cond : Var .var s -> CapyExp s -> CapyExp s -> CapyExp s
| par :
  CapyExp s -> CapyExp s ->
  CapyExp s

/-- Applies a renaming to all bound variables in an expression. -/
def CapyExp.rename : CapyExp s1 -> Rename s1 s2 -> CapyExp s2
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
inductive CapyExp.IsVal : CapyExp s -> Prop where
| abs : CapyExp.IsVal (.abs T e)
| tabs : CapyExp.IsVal (.tabs T e)
| cabs : CapyExp.IsVal (.cabs m e)
| unit : CapyExp.IsVal .unit
| btrue : CapyExp.IsVal .btrue
| bfalse : CapyExp.IsVal .bfalse

/-- A simple value is a value that is not a pack. Therefore,
      a simple value always has a capturing type, not an existential type. -/
inductive CapyExp.IsSimpleVal : CapyExp s -> Prop where
| abs : CapyExp.IsSimpleVal (.abs T e)
| tabs : CapyExp.IsSimpleVal (.tabs T e)
| cabs : CapyExp.IsSimpleVal (.cabs m e)
| unit : CapyExp.IsSimpleVal .unit
| btrue : CapyExp.IsSimpleVal .btrue
| bfalse : CapyExp.IsSimpleVal .bfalse

inductive CapyExp.IsSimpleAns : CapyExp s -> Prop where
| is_simple_val :
  (hv : CapyExp.IsSimpleVal v) ->
  CapyExp.IsSimpleAns v
| is_var :
  CapyExp.IsSimpleAns (.var x)

/-- A value, bundling an expression with a proof that it is a value. -/
structure CapyVal (s : Sig) where
  unwrap : CapyExp s
  isVal : unwrap.IsVal

/-- Renaming by the identity renaming leaves a variable unchanged. -/
def CapyVar.rename_id {x : Var k s} : x.rename (Rename.id) = x := by
  cases x <;> rfl

/-- Renaming by the identity renaming leaves an expression unchanged. -/
def CapyExp.rename_id {e : CapyExp s} : e.rename (Rename.id) = e := by
  induction e with
  | var x =>
    simp only [CapyExp.rename, CapyVar.rename_id]
  | abs T e ih =>
    simp only [CapyExp.rename, Rename.lift_id]
    have hT : T.rename Rename.id = T := CapyTy.rename_id
    congr 1
  | tabs T e ih =>
    simp only [CapyExp.rename, CapyPureTy.rename_id, Rename.lift_id]
    exact congrArg (CapyExp.tabs T) ih
  | cabs cb e ih =>
    simp only [CapyExp.rename, CapyCaptureBound.rename_id, Rename.lift_id]
    exact congrArg (CapyExp.cabs cb) ih
  | alloc x =>
    simp only [CapyExp.rename, CapyVar.rename_id]
  | drop x =>
    simp only [CapyExp.rename, CapyVar.rename_id]
  | app x y =>
    simp only [CapyExp.rename, CapyVar.rename_id]
  | tapp x T =>
    simp only [CapyExp.rename, CapyVar.rename_id, CapyPureTy.rename_id]
  | capp x cs =>
    simp only [CapyExp.rename, CapyVar.rename_id, CaptureSet.rename_id]
  | letin e1 e2 ih1 ih2 =>
    simp only [CapyExp.rename, Rename.lift_id, ih1]
    exact congrArg (CapyExp.letin e1) ih2
  | unit => rfl
  | btrue => rfl
  | bfalse => rfl
  | read x =>
    simp only [CapyExp.rename, CapyVar.rename_id]
  | write x y =>
    simp only [CapyExp.rename, CapyVar.rename_id]
  | cond x e2 e3 ih2 ih3 =>
    simp only [CapyExp.rename, CapyVar.rename_id, ih2]
    exact congrArg (CapyExp.cond x e2) ih3
  | par e1 e2 ih1 ih2 =>
    simp only [CapyExp.rename, ih1, ih2]

/-- Renaming distributes over composition of renamings. -/
theorem CapyVar.rename_comp {x : Var k s1} {f : Rename s1 s2} {g : Rename s2 s3} :
    (x.rename f).rename g = x.rename (f.comp g) := by
  cases x <;> rfl

/-- Renaming distributes over composition of renamings. -/
theorem CapyExp.rename_comp {e : CapyExp s1} {f : Rename s1 s2} {g : Rename s2 s3} :
    (e.rename f).rename g = e.rename (f.comp g) := by
  induction e generalizing s2 s3 with
  | var x =>
    simp only [CapyExp.rename, CapyVar.rename_comp]
  | abs T e ih =>
    simpa only [CapyExp.rename, CapyTy.rename_comp, Rename.lift_comp] using
      congrArg (CapyExp.abs (T.rename (f.lift.comp g.lift)))
        (ih (f := f.lift) (g := g.lift))
  | tabs T e ih =>
    simpa only [CapyExp.rename, CapyPureTy.rename_comp, Rename.lift_comp] using
      congrArg (CapyExp.tabs (T.rename (f.comp g)))
        (ih (f := f.lift) (g := g.lift))
  | cabs cb e ih =>
    simpa only [
      CapyExp.rename,
      CapyCaptureBound.rename_comp,
      Rename.lift_comp
    ] using
      congrArg (CapyExp.cabs (cb.rename (f.comp g)))
        (ih (f := f.lift) (g := g.lift))
  | alloc x =>
    simp only [CapyExp.rename, CapyVar.rename_comp]
  | drop x =>
    simp only [CapyExp.rename, CapyVar.rename_comp]
  | app x y =>
    simp only [CapyExp.rename, CapyVar.rename_comp]
  | tapp x T =>
    simp only [CapyExp.rename, CapyVar.rename_comp, CapyPureTy.rename_comp]
  | capp x cs =>
    simp only [CapyExp.rename, CapyVar.rename_comp, CaptureSet.rename_comp]
  | letin e1 e2 ih1 ih2 =>
    simpa only [CapyExp.rename, Rename.lift_comp, ih1] using
      congrArg (CapyExp.letin (e1.rename (f.comp g))) (ih2 (f := f.lift) (g := g.lift))
  | unit => rfl
  | btrue => rfl
  | bfalse => rfl
  | read x =>
    simp only [CapyExp.rename, CapyVar.rename_comp]
  | write x y =>
    simp only [CapyExp.rename, CapyVar.rename_comp]
  | cond x e2 e3 ih2 ih3 =>
    simpa only [CapyExp.rename, CapyVar.rename_comp, ih2] using
      congrArg (CapyExp.cond (x.rename (f.comp g)) (e2.rename (f.comp g))) (ih3 (f := f) (g := g))
  | par e1 e2 ih1 ih2 =>
    simp only [CapyExp.rename, ih1, ih2]

/-- Weakening commutes with renaming under a binder. -/
theorem CapyVar.weaken_rename_comm {x : Var k s1} {f : Rename s1 s2} :
    (x.rename Rename.succ).rename (f.lift (k:=k0)) = (x.rename f).rename (Rename.succ) := by
  simp [CapyVar.rename_comp, Rename.succ_lift_comm]

/-- An answer is a value or a free variable in the empty context. -/
inductive CapyExp.IsAns : CapyExp {} -> Prop where
| is_val :
  (hv : CapyExp.IsVal v) ->
  CapyExp.IsAns v
| is_var :
  CapyExp.IsAns (.var x)

/-- An expression is closed if it contains no heap pointers. -/
inductive CapyExp.IsClosed : CapyExp s -> Prop where
| var : Var.IsClosed x -> CapyExp.IsClosed (.var x)
| abs : CapyTy.IsClosed T -> CapyExp.IsClosed e ->
    CapyExp.IsClosed (.abs T e)
| tabs : CapyPureTy.IsClosed T -> CapyExp.IsClosed e ->
    CapyExp.IsClosed (.tabs T e)
| cabs : CapyCaptureBound.IsClosed cb -> CapyExp.IsClosed e ->
    CapyExp.IsClosed (.cabs cb e)
| alloc : Var.IsClosed x -> CapyExp.IsClosed (.alloc x)
| drop : Var.IsClosed x -> CapyExp.IsClosed (.drop x)
| app : Var.IsClosed x -> Var.IsClosed y -> CapyExp.IsClosed (.app x y)
| tapp : Var.IsClosed x -> CapyPureTy.IsClosed T -> CapyExp.IsClosed (.tapp x T)
| capp : Var.IsClosed x -> CaptureSet.IsClosed cs -> CapyExp.IsClosed (.capp x cs)
| letin : CapyExp.IsClosed e1 -> CapyExp.IsClosed e2 -> CapyExp.IsClosed (.letin e1 e2)
| unit : CapyExp.IsClosed .unit
| btrue : CapyExp.IsClosed .btrue
| bfalse : CapyExp.IsClosed .bfalse
| read : Var.IsClosed x -> CapyExp.IsClosed (.read x)
| write : Var.IsClosed x -> Var.IsClosed y -> CapyExp.IsClosed (.write x y)
| cond : Var.IsClosed x -> CapyExp.IsClosed e2 -> CapyExp.IsClosed e3 ->
    CapyExp.IsClosed (.cond x e2 e3)
| par : CapyExp.IsClosed e1 -> CapyExp.IsClosed e2 -> CapyExp.IsClosed (.par e1 e2)

end CoreCapybara
