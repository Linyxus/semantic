import Mathlib.Tactic

/-!
De Bruijn indices and variable renamings for Fsub.
-/

namespace FsubNext

inductive Kind : Type where
| var : Kind
| tvar : Kind

@[reducible]
def Sig : Type := List Kind

instance Sig.instEmptyCollection : EmptyCollection Sig where
  emptyCollection := []

def Sig.extend_var : Sig -> Sig := fun s => .var :: s
def Sig.extend_tvar : Sig -> Sig := fun s => .tvar :: s
def Sig.extend : Sig -> Kind -> Sig := fun s k => k :: s

def Sig.extendMany : Sig -> Sig -> Sig
| s, [] => s
| s, k :: K => (s.extendMany K).extend k

postfix:80 ",x" => Sig.extend_var
postfix:80 ",X" => Sig.extend_tvar
infixl:65 ",," => Sig.extend

instance Sig.instAppend : Append Sig where
  append := Sig.extendMany

inductive BVar : Sig -> Kind -> Type where
| here : BVar (s,,k) k
| there :
  BVar s k ->
  BVar (s,,k0) k

structure Rename (s1 s2 : Sig) where
  var : BVar s1 k -> BVar s2 k

def Rename.id {s : Sig} : Rename s s where
  var := fun x => x

def Rename.comp {s1 s2 s3 : Sig} (f1 : Rename s1 s2) (f2 : Rename s2 s3) : Rename s1 s3 where
  var := fun x => f2.var (f1.var x)

def Rename.lift (f : Rename s1 s2) : Rename (s1,,k) (s2,,k) where
  var := fun
    | .here => .here
    | .there x => .there (f.var x)

def Rename.liftMany (f : Rename s1 s2) (K : Sig) : Rename (s1 ++ K) (s2 ++ K) :=
  match K with
  | [] => f
  | k :: K => (f.liftMany K).lift (k:=k)

def Rename.succ : Rename s (s,,k) where
  var := fun x => x.there

theorem Rename.funext {f1 f2 : Rename s1 s2}
  (hvar : ∀ {k} (x : BVar s1 k), f1.var x = f2.var x) :
  f1 = f2 := by
  cases f1; cases f2
  aesop

theorem Rename.succ_lift_comm {f : Rename s1 s2} :
  (Rename.succ (k:=k0)).comp f.lift = f.comp (Rename.succ (k:=k0)) := by
  apply Rename.funext
  intro k x
  cases x <;> rfl

theorem Rename.lift_id :
  (Rename.id (s:=s)).lift (k:=k0) = Rename.id := by
  apply Rename.funext
  intro k x
  cases x <;> rfl

theorem Rename.lift_comp {f1 : Rename s1 s2} {f2 : Rename s2 s3} :
  (f1.comp f2).lift (k:=k0) = f1.lift.comp f2.lift := by
  apply Rename.funext
  intro k x
  cases x <;> rfl

end FsubNext
