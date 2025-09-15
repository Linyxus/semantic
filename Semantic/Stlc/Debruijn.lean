import Mathlib.Tactic
/-!
Library for De Bruijn indices and parallel operations.
-/

namespace Stlc

inductive Var : Nat -> Type where
| here : Var (n+1)
| there : Var n -> Var (n+1)

structure Rename (n1 n2 : Nat) where
  var : Var n1 -> Var n2

def Rename.id {n : Nat} : Rename n n where
  var := fun x => x

def Rename.liftVar (f : Rename n1 n2) : Rename (n1+1) (n2+1) where
  var := fun
    | .here => .here
    | .there x => .there (f.var x)

def Rename.succVar : Rename n (n+1) where
  var := fun x => .there x

def Rename.comp (f1 : Rename n1 n2) (f2 : Rename n2 n3) : Rename n1 n3 where
  var := fun x => f2.var (f1.var x)

theorem Rename.funext {f1 f2 : Rename n1 n2}
  (hvar : ∀ x, f1.var x = f2.var x) :
  f1 = f2 := by
  cases f1; cases f2
  aesop

theorem Rename.succVar_comm {f : Rename n1 n2} :
  f.comp Rename.succVar = Rename.succVar.comp (f.liftVar) := by
  apply Rename.funext
  intro x; rfl

end Stlc
