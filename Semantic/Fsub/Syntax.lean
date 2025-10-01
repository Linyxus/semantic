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

/-!
## Level renaming

Operations for renaming de Bruijn levels (free names) while leaving de Bruijn indices
(bound variables) untouched. These operations apply a renaming function to free term
variables but preserve all bound variables and type variables.
-/

/-- Rename free term variables (levels) in a term variable.
Bound variables are left unchanged. -/
def Var.rename_level (x : Var s) (f : Nat -> Nat) : Var s :=
  match x with
  | .bound n => .bound n
  | .free n => .free (f n)

/-- Rename free term variables (levels) in a type.
This only affects free term variables appearing in singleton types. -/
def Ty.rename_levels (T : Ty s) (f : Nat -> Nat) : Ty s :=
  match T with
  | .top => .top
  | .tvar x => .tvar x
  | .singleton x => .singleton (x.rename_level f)
  | .arrow T1 T2 => .arrow (T1.rename_levels f) (T2.rename_levels f)
  | .poly T1 T2 => .poly (T1.rename_levels f) (T2.rename_levels f)

/-- Rename free term variables (levels) in an expression.
This applies the renaming function to all free term variables while leaving
bound variables unchanged. Since levels are absolute positions, we don't need
to adjust the renaming function when going under binders. -/
def Exp.rename_levels (e : Exp s) (f : Nat -> Nat) : Exp s :=
  match e with
  | .var x => .var (x.rename_level f)
  | .abs T e => .abs (T.rename_levels f) (e.rename_levels f)
  | .tabs T e => .tabs (T.rename_levels f) (e.rename_levels f)
  | .app x y => .app (x.rename_level f) (y.rename_level f)
  | .tapp x T => .tapp (x.rename_level f) (T.rename_levels f)
  | .letin e1 e2 => .letin (e1.rename_levels f) (e2.rename_levels f)

/-- The identity function on levels leaves variables unchanged. -/
theorem Var.rename_level_id (x : Var s) : x.rename_level id = x := by
  cases x <;> rfl

/-- The identity function on levels leaves types unchanged. -/
theorem Ty.rename_levels_id (T : Ty s) : T.rename_levels id = T := by
  induction T <;> simp [Ty.rename_levels, Var.rename_level_id, *]

/-- The identity function on levels leaves expressions unchanged. -/
theorem Exp.rename_levels_id (e : Exp s) : e.rename_levels id = e := by
  induction e <;> simp [Exp.rename_levels, Ty.rename_levels_id, Var.rename_level_id, *]

/-- Level renaming composes functorially for variables. -/
theorem Var.rename_level_comp (x : Var s) (f g : Nat -> Nat) :
    (x.rename_level f).rename_level g = x.rename_level (g ∘ f) := by
  cases x <;> rfl

/-- Level renaming composes functorially for types. -/
theorem Ty.rename_levels_comp (T : Ty s) (f g : Nat -> Nat) :
    (T.rename_levels f).rename_levels g = T.rename_levels (g ∘ f) := by
  induction T <;> simp [Ty.rename_levels, Var.rename_level_comp, *]

/-- Level renaming composes functorially for expressions. -/
theorem Exp.rename_levels_comp (e : Exp s) (f g : Nat -> Nat) :
    (e.rename_levels f).rename_levels g = e.rename_levels (g ∘ f) := by
  induction e <;> simp [Exp.rename_levels, Ty.rename_levels_comp, Var.rename_level_comp, *]

end Fsub
