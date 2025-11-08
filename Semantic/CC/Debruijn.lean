import Mathlib.Tactic

/-!
De Bruijn indices and variable renamings for CC.
-/

namespace CC

/-- Kind of a variable. -/
inductive Kind : Type where
/-- Term variable -/
| var : Kind
/-- Type variable -/
| tvar : Kind
/-- Capture variable -/
| cvar : Kind

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

/-- The "successor" renaming that weakens all variables by one level. -/
def Rename.succ : Rename s (s,,k) where
  var := fun x => x.there

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

end CC
