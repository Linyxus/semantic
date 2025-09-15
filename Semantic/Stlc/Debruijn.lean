import Mathlib.Tactic

/-!
De Bruijn indices and variable renamings for STLC.
-/

namespace Stlc

/-!
A variable represented as a De Bruijn index in a context of size `n`.
-/
inductive Var : Nat -> Type where
| here : Var (n+1)
| there : Var n -> Var (n+1)

/-!
A renaming `r : Rename n1 n2` maps variables from a context of size `n1`
to variables in a context of size `n2`.
-/
structure Rename (n1 n2 : Nat) where
  var : Var n1 -> Var n2

/-!
The identity renaming that maps each variable to itself.
-/
def Rename.id {n : Nat} : Rename n n where
  var := fun x => x

/-!
Lift a renaming under a binder. The newly bound variable (represented by `here`)
maps to itself, while all other variables are mapped according to the original
renaming and then shifted outward by one level.
-/
def Rename.liftVar (f : Rename n1 n2) : Rename (n1+1) (n2+1) where
  var := fun
    | .here => .here
    | .there x => .there (f.var x)

/-!
The successor renaming that shifts all variables outward by one level.
-/
def Rename.succVar : Rename n (n+1) where
  var := fun x => .there x

/-!
Composition of two renamings.
-/
def Rename.comp (f1 : Rename n1 n2) (f2 : Rename n2 n3) : Rename n1 n3 where
  var := fun x => f2.var (f1.var x)

/-!
Function extensionality principle for renamings. Two renamings are equal
if they map each variable to the same target variable.
-/
theorem Rename.funext {f1 f2 : Rename n1 n2}
  (hvar : ∀ x, f1.var x = f2.var x) :
  f1 = f2 := by
  cases f1; cases f2
  aesop

/-!
Commutativity property for weakening renaming and lifting.
-/
theorem Rename.succVar_comm {f : Rename n1 n2} :
  f.comp Rename.succVar = Rename.succVar.comp (f.liftVar) := by
  apply Rename.funext
  intro x; rfl

end Stlc
