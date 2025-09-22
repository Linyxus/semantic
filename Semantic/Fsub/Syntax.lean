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
  induction T
    <;> try (solve | rfl | simp [Ty.rename, Var.rename_id, Rename.lift_id]; try aesop)

def Exp.rename_id {e : Exp s} : e.rename (Rename.id) = e := by
  induction e
    <;> try (solve
      | rfl
      | simp [Exp.rename, Ty.rename_id, Var.rename_id, Rename.lift_id]; try aesop)

theorem Var.rename_comp {x : Var s1} {f : Rename s1 s2} {g : Rename s2 s3} :
    (x.rename f).rename g = x.rename (f.comp g) := by
  cases x <;> rfl

theorem Ty.rename_comp {T : Ty s1} {f : Rename s1 s2} {g : Rename s2 s3} :
    (T.rename f).rename g = T.rename (f.comp g) := by
  induction T generalizing s2 s3
    <;> try (solve | rfl | simp [Ty.rename, Var.rename_comp, Rename.lift_comp]; try aesop)

theorem Exp.rename_comp {e : Exp s1} {f : Rename s1 s2} {g : Rename s2 s3} :
    (e.rename f).rename g = e.rename (f.comp g) := by
  induction e generalizing s2 s3
    <;> try (solve
      | rfl
      | simp [Exp.rename, Ty.rename_comp, Var.rename_comp, Rename.lift_comp]; try aesop)

theorem Ty.weaken_rename_comm {T : Ty s1} {f : Rename s1 s2} :
    (T.rename Rename.succ).rename (f.lift (k:=k0)) = (T.rename f).rename (Rename.succ) := by
  simp [Ty.rename_comp, Rename.succ_lift_comm]

theorem Var.weaken_rename_comm {x : Var s1} {f : Rename s1 s2} :
    (x.rename Rename.succ).rename (f.lift (k:=k0)) = (x.rename f).rename (Rename.succ) := by
  simp [Var.rename_comp, Rename.succ_lift_comm]

end Fsub
