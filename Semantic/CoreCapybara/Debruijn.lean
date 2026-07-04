import Mathlib.Tactic

/-!
De Bruijn indices and variable renamings for CC.
-/

namespace CoreCapybara

/-- Kind of a variable. -/
inductive Kind : Type where
/-- Term variable -/
| var : Kind
/-- Type variable -/
| tvar : Kind
/-- Capture variable -/
| cvar : Kind
/-- Lock variable -/
| lock : Kind
deriving DecidableEq, Repr

/-- A `Sig` describes the shape of a context, which is a list of variable kinds. -/
@[reducible]
def Sig : Type := List Kind

instance Sig.instEmptyCollection : EmptyCollection Sig where
  emptyCollection := []

/-- Extends a signature with a term variable. -/
def Sig.extend_var : Sig -> Sig := fun s => .var :: s
/-- Extends a signature with a type variable. -/
def Sig.extend_tvar : Sig -> Sig := fun s => .tvar :: s
/-- Extends a signature with a capture variable. -/
def Sig.extend_cvar : Sig -> Sig := fun s => .cvar :: s
/-- Extends a signature with a variable of the given kind. -/
def Sig.extend : Sig -> Kind -> Sig := fun s k => k :: s

/-- Extends a signature with multiple variables. -/
def Sig.extendMany : Sig -> Sig -> Sig
| s, [] => s
| s, k :: K => (s.extendMany K).extend k

/-- Extends a signature with `n` capture variables. -/
def Sig.extendCVars : Sig -> Nat -> Sig
| s, 0 => s
| s, n+1 => (s.extendCVars n).extend_cvar

postfix:80 ",x" => Sig.extend_var
postfix:80 ",X" => Sig.extend_tvar
postfix:80 ",C" => Sig.extend_cvar
infixl:65 ",," => Sig.extend

instance Sig.instAppend : Append Sig where
  append := Sig.extendMany

/-- A bound variable, de Bruijn indexed. -/
inductive BVar : Sig -> Kind -> Type where
| here : BVar (s,,k) k
| there :
  BVar s k ->
  BVar (s,,k0) k

/-- A `Rename` maps bound variables in one context to another. -/
structure Rename (s1 s2 : Sig) where
  var : BVar s1 k -> BVar s2 k

/-- The identity `Rename`. -/
def Rename.id {s : Sig} : Rename s s where
  var := fun x => x

/-- Composition of two renamings. -/
def Rename.comp {s1 s2 s3 : Sig} (f1 : Rename s1 s2) (f2 : Rename s2 s3) : Rename s1 s3 where
  var := fun x => f2.var (f1.var x)

/-- Lifts a renaming under a binder. The newly bound variable maps to itself. -/
def Rename.lift (f : Rename s1 s2) : Rename (s1,,k) (s2,,k) where
  var := fun
    | .here => .here
    | .there x => .there (f.var x)

/-- Lifts a renaming under multiple binders. -/
def Rename.liftMany (f : Rename s1 s2) (K : Sig) : Rename (s1 ++ K) (s2 ++ K) :=
  match K with
  | [] => f
  | k :: K => (f.liftMany K).lift (k:=k)

/-- Lifts a renaming under `n` capture-variable binders. -/
def Rename.liftCVars (f : Rename s1 s2) : (n : Nat) -> Rename (s1.extendCVars n) (s2.extendCVars n)
| 0 => f
| n+1 => (f.liftCVars n).lift (k := .cvar)

/-- The "successor" renaming that weakens all variables by one level. -/
def Rename.succ : Rename s (s,,k) where
  var := fun x => x.there

/-- Weakens all variables past `n` fresh capture-variable binders. -/
def Rename.weakenCVars : (n : Nat) → Rename s (s.extendCVars n)
| 0 => Rename.id
| n+1 => (Rename.weakenCVars n).comp Rename.succ

/-- Function extensionality for renamings.
  Two renamings are equal if they map all variables equally. -/
theorem Rename.funext {f1 f2 : Rename s1 s2}
  (hvar : ∀ {k} (x : BVar s1 k), f1.var x = f2.var x) :
  f1 = f2 := by
  cases f1; cases f2
  aesop

/-- The successor renaming commutes with lifting. -/
theorem Rename.succ_lift_comm {f : Rename s1 s2} :
  (Rename.succ (k:=k0)).comp f.lift = f.comp (Rename.succ (k:=k0)) := by
  apply Rename.funext
  intro k x
  cases x <;> rfl

/-- Lifting the identity renaming yields the identity. -/
theorem Rename.lift_id :
  (Rename.id (s:=s)).lift (k:=k0) = Rename.id := by
  apply Rename.funext
  intro k x
  cases x <;> rfl

/-- Lifting distributes over composition of renamings. -/
theorem Rename.lift_comp {f1 : Rename s1 s2} {f2 : Rename s2 s3} :
  (f1.comp f2).lift (k:=k0) = f1.lift.comp f2.lift := by
  apply Rename.funext
  intro k x
  cases x <;> rfl

/-- Lifting the identity renaming under `n` capture-variable binders yields the identity. -/
theorem Rename.liftCVars_id {n : Nat} :
  (Rename.id (s:=s)).liftCVars n = Rename.id := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (Rename.id.liftCVars n).lift = Rename.id
    rw [ih]
    exact Rename.lift_id

/-- Lifting under `n` capture-variable binders distributes over composition of renamings. -/
theorem Rename.liftCVars_comp {f1 : Rename s1 s2} {f2 : Rename s2 s3} {n : Nat} :
  (f1.comp f2).liftCVars n = (f1.liftCVars n).comp (f2.liftCVars n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change ((f1.comp f2).liftCVars n).lift
      = ((f1.liftCVars n).lift).comp ((f2.liftCVars n).lift)
    rw [ih]
    exact Rename.lift_comp

/-- Weakening that inserts an implicit capture variable just below the top
    binder, mapping `s,,k` into `s,C,,k`. -/
def Rename.implicit_cvar : Rename (s,,k) (s,C,,k) where
  var := fun
    | .here => .here
    | .there y => .there (.there y)

/-- The implicit-cvar weakening is the lift of the cvar-kind successor: inserting
    the unused `C` slot below the top binder is weakening by `C` under that binder. -/
theorem Rename.implicit_cvar_eq_succ_lift {s : Sig} {k : Kind} :
    (Rename.implicit_cvar : Rename (s,,k) (s,C,,k))
      = (Rename.succ (k := .cvar)).lift := by
  apply Rename.funext
  intro k' x
  cases x <;> rfl

/-- The implicit-cvar weakening commutes with lifting: inserting the unused `C`
    slot before applying a (doubly) lifted renaming is the same as renaming first
    and inserting the slot after. -/
theorem Rename.implicit_cvar_lift_comm {f : Rename s1 s2} {k0 : Kind} :
    (Rename.implicit_cvar (k := k0)).comp ((f.lift (k := .cvar)).lift (k := k0))
      = (f.lift (k := k0)).comp Rename.implicit_cvar := by
  apply Rename.funext
  intro k x
  cases x <;> rfl

/-- Weakening that inserts an implicit capture variable just below the two top
    binders, mapping `s,,k1,,k2` into `s,C,,k1,,k2`. -/
def Rename.implicit_cvar2 : Rename (s,,k1,,k2) (s,C,,k1,,k2) where
  var := fun
    | .here => .here
    | .there .here => .there .here
    | .there (.there y) => .there (.there (.there y))

end CoreCapybara
