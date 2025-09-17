import Semantic.Fsub.Syntax

namespace Fsub

structure Subst (s1 s2 : Sig) where
  var : BVar s1 .var -> Var s2
  tvar : BVar s1 .tvar -> Ty s2

def Subst.lift (s : Subst s1 s2) : Subst (s1,,k) (s2,,k) where
  var := fun x => by
    cases x
    case here => exact .bound .here
    case there x => exact (s.var x).rename Rename.succ
  tvar := fun x => by
    cases x
    case here => exact .tvar .here
    case there x => exact (s.tvar x).rename Rename.succ

def Subst.id {s : Sig} : Subst s s where
  var := fun x => .bound x
  tvar := fun x => .tvar x

def Var.subst : Var s1 -> Subst s1 s2 -> Var s2
| .bound x, s => s.var x
| .free n, _ => .free n

def Ty.subst : Ty s1 -> Subst s1 s2 -> Ty s2
| .top, _ => .top
| .tvar x, s => s.tvar x
| .singleton x, s => .singleton (x.subst s)
| .arrow T1 T2, s => .arrow (T1.subst s) (T2.subst s.lift)
| .poly T1 T2, s => .poly (T1.subst s) (T2.subst s.lift)

def Exp.subst : Exp s1 -> Subst s1 s2 -> Exp s2
| .var x, s => .var (x.subst s)
| .abs T e, s => .abs (T.subst s) (e.subst s.lift)
| .tabs T e, s => .tabs (T.subst s) (e.subst s.lift)
| .app x y, s => .app (x.subst s) (y.subst s)
| .tapp x T, s => .tapp (x.subst s) (T.subst s)
| .letin e1 e2, s => .letin (e1.subst s) (e2.subst s.lift)

def Subst.openVar (x : Var s) : Subst (s,x) s where
  var := fun
    | .here => x
    | .there x0 => .bound x0
  tvar := fun
    | .there x0 => .tvar x0

def Subst.openTVar (U : Ty s) : Subst (s,X) s where
  var := fun
    | .there x => .bound x
  tvar := fun
    | .here => U
    | .there x => .tvar x

end Fsub
