import Semantic.CC.Syntax.Ty

/-!
Expression definitions and operations for CC.
-/

namespace CC

inductive Exp : Sig -> Type where
| var : Var .var s -> Exp s
| abs : Ty .capt s -> Exp (s,x) -> Exp s
| tabs : Ty .shape s -> Exp (s,X) -> Exp s
| cabs : CaptureBound s -> Exp (s,C) -> Exp s
| pack : CaptureSet s -> Var .var s -> Exp s
| app : Var .var s -> Var .var s -> Exp s
| tapp : Var .var s -> Ty .shape s -> Exp s
| capp : Var .var s -> CaptureSet s -> Exp s
| letin : Exp s -> Exp (s,x) -> Exp s
| unpack : Exp s -> Exp ((s,C),x) -> Exp s

def Exp.rename : Exp s1 -> Rename s1 s2 -> Exp s2
| .var x, f => .var (x.rename f)
| .abs T e, f => .abs (T.rename f) (e.rename (f.lift))
| .tabs T e, f => .tabs (T.rename f) (e.rename (f.lift))
| .cabs cb e, f => .cabs (cb.rename f) (e.rename (f.lift))
| .pack cs x, f => .pack (cs.rename f) (x.rename f)
| .app x y, f => .app (x.rename f) (y.rename f)
| .tapp x T, f => .tapp (x.rename f) (T.rename f)
| .capp x cs, f => .capp (x.rename f) (cs.rename f)
| .letin e1 e2, f => .letin (e1.rename f) (e2.rename (f.lift))
| .unpack e1 e2, f => .unpack (e1.rename f) (e2.rename (f.lift.lift))

inductive Exp.IsVal : Exp s -> Prop where
| abs : Exp.IsVal (.abs T e)
| tabs : Exp.IsVal (.tabs T e)

structure Val (s : Sig) where
  unwrap : Exp s
  isVal : unwrap.IsVal

def Var.rename_id {x : Var k s} : x.rename (Rename.id) = x := by
  cases x <;> rfl

def Exp.rename_id {e : Exp s} : e.rename (Rename.id) = e := by
  induction e
    <;> try (solve
      | rfl
      | simp [Exp.rename, Ty.rename_id, Var.rename_id,
              CaptureSet.rename_id, CaptureBound.rename_id, Rename.lift_id]
        try aesop)

theorem Var.rename_comp {x : Var k s1} {f : Rename s1 s2} {g : Rename s2 s3} :
    (x.rename f).rename g = x.rename (f.comp g) := by
  cases x <;> rfl

theorem Exp.rename_comp {e : Exp s1} {f : Rename s1 s2} {g : Rename s2 s3} :
    (e.rename f).rename g = e.rename (f.comp g) := by
  induction e generalizing s2 s3
    <;> try (solve
      | rfl
      | simp [Exp.rename, Ty.rename_comp, Var.rename_comp,
              CaptureSet.rename_comp, CaptureBound.rename_comp, Rename.lift_comp]
        try aesop)

theorem Var.weaken_rename_comm {x : Var k s1} {f : Rename s1 s2} :
    (x.rename Rename.succ).rename (f.lift (k:=k0)) = (x.rename f).rename (Rename.succ) := by
  simp [Var.rename_comp, Rename.succ_lift_comm]

inductive Exp.IsAns : Exp {} -> Prop where
| is_val :
  (hv : Exp.IsVal v) ->
  Exp.IsAns v
| is_var :
  Exp.IsAns (.var x)

end CC
