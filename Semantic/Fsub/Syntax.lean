import Semantic.Fsub.Debruijn

/-!
Syntax definitions for F<:.
-/

namespace Fsub

inductive Var : Sig -> Type where
| bound : BVar s .var -> Var s
| free : Nat -> Var s

inductive Ty : Sig -> Type where
| top : Ty s
| tvar : BVar s .tvar -> Ty s
| singleton : Var s -> Ty s
| arrow : Ty s -> Ty (s,x) -> Ty s
| poly : Ty s -> Ty (s,X) -> Ty s

inductive Exp : Sig -> Type where
| var : Var s -> Exp s
| abs : Ty s -> Exp (s,x) -> Exp s
| tabs : Ty s -> Exp (s,X) -> Exp s
| app : Var s -> Var s -> Exp s
| tapp : Var s -> Ty s -> Exp s
| letin : Exp s -> Exp (s,x) -> Exp s

def Var.rename : Var s1 -> Rename s1 s2 -> Var s2
| .bound x, f => .bound (f.var x)
| .free n, _ => .free n

def Ty.rename : Ty s1 -> Rename s1 s2 -> Ty s2
| .top, _ => .top
| .tvar x, f => .tvar (f.var x)
| .singleton x, f => .singleton (x.rename f)
| .arrow T1 T2, f => .arrow (T1.rename f) (T2.rename (f.lift))
| .poly T1 T2, f => .poly (T1.rename f) (T2.rename (f.lift))

def Exp.rename : Exp s1 -> Rename s1 s2 -> Exp s2
| .var x, f => .var (x.rename f)
| .abs T e, f => .abs (T.rename f) (e.rename (f.lift))
| .tabs T e, f => .tabs (T.rename f) (e.rename (f.lift))
| .app x y, f => .app (x.rename f) (y.rename f)
| .tapp x T, f => .tapp (x.rename f) (T.rename f)
| .letin e1 e2, f => .letin (e1.rename f) (e2.rename (f.lift))

inductive Exp.IsVal : Exp s -> Prop where
| abs : Exp.IsVal (.abs T e)
| tabs : Exp.IsVal (.tabs T e)

structure Val (s : Sig) where
  unwrap : Exp s
  isVal : unwrap.IsVal

def Var.rename_id {x : Var s} : x.rename (Rename.id) = x := by
  cases x <;> rfl

def Ty.rename_id {T : Ty s} : T.rename (Rename.id) = T := by
  induction T with
  | top => rfl
  | tvar x => rfl
  | singleton x =>
      simpa only [Ty.rename] using congrArg Ty.singleton (Var.rename_id (x:=x))
  | arrow T1 T2 ih1 ih2 =>
      simpa only [Ty.rename, Rename.lift_id, ih1] using congrArg (Ty.arrow T1) ih2
  | poly T1 T2 ih1 ih2 =>
      simpa only [Ty.rename, Rename.lift_id, ih1] using congrArg (Ty.poly T1) ih2

def Exp.rename_id {e : Exp s} : e.rename (Rename.id) = e := by
  induction e with
  | var x =>
      simpa only [Exp.rename] using congrArg Exp.var (Var.rename_id (x:=x))
  | abs T e ih =>
      simpa only [Exp.rename, Ty.rename_id, Rename.lift_id] using congrArg (Exp.abs T) ih
  | tabs T e ih =>
      simpa only [Exp.rename, Ty.rename_id, Rename.lift_id] using congrArg (Exp.tabs T) ih
  | app x y =>
      rw [Exp.rename, Var.rename_id]
      exact congrArg (Exp.app x) (Var.rename_id (x:=y))
  | tapp x T =>
      rw [Exp.rename, Var.rename_id]
      exact congrArg (Exp.tapp x) (Ty.rename_id (T:=T))
  | letin e1 e2 ih1 ih2 =>
      simpa only [Exp.rename, Rename.lift_id, ih1] using congrArg (Exp.letin e1) ih2

theorem Var.rename_comp {x : Var s1} {f : Rename s1 s2} {g : Rename s2 s3} :
    (x.rename f).rename g = x.rename (f.comp g) := by
  cases x <;> rfl

theorem Ty.rename_comp {T : Ty s1} {f : Rename s1 s2} {g : Rename s2 s3} :
    (T.rename f).rename g = T.rename (f.comp g) := by
  induction T generalizing s2 s3 with
  | top => rfl
  | tvar x => rfl
  | singleton x =>
      simpa only [Ty.rename] using congrArg Ty.singleton (Var.rename_comp (x:=x) (f:=f) (g:=g))
  | arrow T1 T2 ih1 ih2 =>
      simpa only [Ty.rename, Rename.lift_comp, ih1] using
        congrArg (Ty.arrow (T1.rename (f.comp g))) (ih2 (f:=f.lift) (g:=g.lift))
  | poly T1 T2 ih1 ih2 =>
      simpa only [Ty.rename, Rename.lift_comp, ih1] using
        congrArg (Ty.poly (T1.rename (f.comp g))) (ih2 (f:=f.lift) (g:=g.lift))

theorem Exp.rename_comp {e : Exp s1} {f : Rename s1 s2} {g : Rename s2 s3} :
    (e.rename f).rename g = e.rename (f.comp g) := by
  induction e generalizing s2 s3 with
  | var x =>
      simpa only [Exp.rename] using congrArg Exp.var (Var.rename_comp (x:=x) (f:=f) (g:=g))
  | abs T e ih =>
      simpa only [Exp.rename, Ty.rename_comp, Rename.lift_comp] using
        congrArg (Exp.abs (T.rename (f.comp g))) (ih (f:=f.lift) (g:=g.lift))
  | tabs T e ih =>
      simpa only [Exp.rename, Ty.rename_comp, Rename.lift_comp] using
        congrArg (Exp.tabs (T.rename (f.comp g))) (ih (f:=f.lift) (g:=g.lift))
  | app x y =>
      change
        Exp.app ((x.rename f).rename g) ((y.rename f).rename g) =
          Exp.app (x.rename (f.comp g)) (y.rename (f.comp g))
      rw [Var.rename_comp, Var.rename_comp]
  | tapp x T =>
      change
        Exp.tapp ((x.rename f).rename g) ((T.rename f).rename g) =
          Exp.tapp (x.rename (f.comp g)) (T.rename (f.comp g))
      rw [Var.rename_comp, Ty.rename_comp]
  | letin e1 e2 ih1 ih2 =>
      simpa only [Exp.rename, Rename.lift_comp, ih1] using
        congrArg (Exp.letin (e1.rename (f.comp g))) (ih2 (f:=f.lift) (g:=g.lift))

theorem Ty.weaken_rename_comm {T : Ty s1} {f : Rename s1 s2} :
    (T.rename Rename.succ).rename (f.lift (k:=k0)) = (T.rename f).rename (Rename.succ) := by
  simp [Ty.rename_comp, Rename.succ_lift_comm]

theorem Var.weaken_rename_comm {x : Var s1} {f : Rename s1 s2} :
    (x.rename Rename.succ).rename (f.lift (k:=k0)) = (x.rename f).rename (Rename.succ) := by
  simp [Var.rename_comp, Rename.succ_lift_comm]

inductive Exp.IsAns : Exp {} -> Prop where
| is_val :
  (hv : Exp.IsVal v) ->
  Exp.IsAns v
| is_var :
  Exp.IsAns (.var x)

end Fsub
