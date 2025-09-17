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

end Fsub
