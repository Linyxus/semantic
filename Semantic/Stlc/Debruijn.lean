/-!
Library for De Bruijn indices and parallel operations.
-/

inductive Var : Nat -> Type where
| here : Var (n+1)
| there : Var n -> Var (n+1)

structure Rename (n1 n2 : Nat) where
  var : Var n1 -> Var n2

def Rename.id (n : Nat) : Rename n n where
  var := fun x => x

def Rename.liftVar (f : Rename n1 n2) : Rename (n1+1) (n2+1) where
  var := fun
    | .here => .here
    | .there x => .there (f.var x)

def Rename.succVar : Rename n (n+1) where
  var := fun x => .there x
