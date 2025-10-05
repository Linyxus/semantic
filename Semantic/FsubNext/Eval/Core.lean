import Semantic.FsubNext.Syntax
import Semantic.FsubNext.Substitution

namespace FsubNext

/-!
A store is a list of locally-closed expressions.
-/
inductive Store : Type where
| nil : Store
| cons : Val {} -> Store -> Store

def Store.lookup : Store -> Nat -> Option (Val {})
| .cons v _, 0 => some v
| .cons _ s, n+1 => Store.lookup s n
| .nil, _ => none

def Store.snoc : Store -> Val {} -> Store
| .cons v s, v0 => .cons v (s.snoc v0)
| .nil, v => .cons v nil

def Store.append : Store -> Store -> Store
| .nil, s2 => s2
| .cons v s1, s2 => .cons v (s1.append s2)

instance Store.instAppend : Append Store where
  append := Store.append

def Store.len : Store -> Nat
| .cons _ s => s.len + 1
| .nil => 0

/-- Rename free term variables (levels) in all values stored in the store.
This applies the level renaming function to each value in the store. -/
def Store.rename_levels : Store -> (Nat -> Nat) -> Store
| .nil, _ => .nil
| .cons v s, f => .cons (v.rename_levels f) (s.rename_levels f)

inductive Step : Store -> Exp {} -> Store -> Exp {} -> Prop where
| st_ctx :
  Step s1 e1 s2 e2 ->
  Step s1 (.letin e1 u) s2 (.letin e2 u)
| st_apply :
  s1.lookup x = some ⟨.abs T e, hv⟩ ->
  Step s1 (.app (.free x) y) s1 (e.subst (Subst.openVar y))
| st_tapply :
  s1.lookup x = some ⟨.tabs T0 e, hv⟩ ->
  Step s1 (.tapp (.free x) T) s1 (e.subst (Subst.openTVar .top))
| st_rename :
  Step s1 (.letin (.var x) e) s1 (e.subst (Subst.openVar x))
| st_lift :
  (hv : Exp.IsVal v) ->
  Step s1 (.letin v e) (s1.snoc ⟨v, hv⟩) (e.subst (Subst.openVar (.free s1.len)))

inductive Reduce : Store -> Exp {} -> Store -> Exp {} -> Prop where
| red_refl :
  Reduce s e s e
| red_step :
  Step s e s' e' ->
  Reduce s' e' s'' e'' ->
  Reduce s e s'' e''

inductive Exp.IsAns : Exp {} -> Prop where
| is_val :
  (hv : Exp.IsVal v) ->
  Exp.IsAns v
| is_var :
  Exp.IsAns (.var x)

/-- Domain of a variable: the minimal length of its heap context. -/
def Var.dom (x : Var s) : Nat :=
  match x with
  | .free n => n + 1
  | .bound _ => 0

/-- Domain of a type: the minimal store length needed for all free type variables to be in scope. -/
def Ty.dom : Ty s -> Nat
| .top => 0
| .tvar _ => 0
| .arrow T1 T2 => max T1.dom T2.dom
| .poly T1 T2 => max T1.dom T2.dom
| .singleton x => x.dom

/-- Domain of an expression:
  the minimal store length needed for all free variables to be in scope. -/
def Exp.dom : Exp s -> Nat
| .var x => x.dom
| .abs T e => max T.dom e.dom
| .app e1 e2 => max e1.dom e2.dom
| .tabs T e => max T.dom e.dom
| .tapp e T => max e.dom T.dom
| .letin e1 e2 => max e1.dom e2.dom

def Exp.WfIn (e : Exp s) (s : Store) : Prop :=
  e.dom <= s.len

def Ty.WfIn (T : Ty s) (s : Store) : Prop :=
  T.dom <= s.len

theorem Exp.letin_wf_inv
  (hwf : Exp.WfIn (.letin e1 e2) s) :
  Exp.WfIn e1 s ∧ Exp.WfIn e2 s := by
  unfold Exp.WfIn at hwf ⊢
  simp only [Exp.dom] at hwf ⊢
  exact ⟨Nat.le_trans (Nat.le_max_left _ _) hwf,
         Nat.le_trans (Nat.le_max_right _ _) hwf⟩

theorem Var.rename_dom {x : Var s} :
  (x.rename f).dom = x.dom := by cases x <;> rfl

/-- Renaming type variables in a type doesn't change its domain
(since domain tracks free term variables, not type variables). -/
theorem Ty.rename_dom {T : Ty s1} {f : Rename s1 s2} :
  (T.rename f).dom = T.dom := by
  induction T generalizing s2 with
  | top => rfl
  | tvar _ => rfl
  | singleton x =>
    simp [Ty.rename, Ty.dom]
    exact Var.rename_dom
  | arrow T1 T2 ih1 ih2 =>
    simp [Ty.rename, Ty.dom]
    rw [ih1, ih2]
  | poly T1 T2 ih1 ih2 =>
    simp [Ty.rename, Ty.dom]
    rw [ih1, ih2]

/-- Renaming type variables in an expression doesn't change its domain
(since domain tracks free term variables, not type variables). -/
theorem Exp.rename_dom {e : Exp s1} {f : Rename s1 s2} :
  (e.rename f).dom = e.dom := by
  induction e generalizing s2 with
  | var x =>
    simp [Exp.rename, Exp.dom]
    exact Var.rename_dom
  | abs T e ih =>
    simp [Exp.rename, Exp.dom]
    rw [Ty.rename_dom, ih]
  | app x y =>
    simp [Exp.rename, Exp.dom]
    rw [Var.rename_dom, Var.rename_dom]
  | tabs T e ih =>
    simp [Exp.rename, Exp.dom]
    rw [Ty.rename_dom, ih]
  | tapp x T =>
    simp [Exp.rename, Exp.dom]
    rw [Var.rename_dom, Ty.rename_dom]
  | letin e1 e2 ih1 ih2 =>
    simp [Exp.rename, Exp.dom]
    rw [ih1, ih2]

structure Subst.has_dom (σ : Subst s1 s2) (n : Nat) where
  hvar : ∀ x, (σ.var x).dom <= n
  htvar : ∀ X, (σ.tvar X).dom <= n

theorem Var.subst_dom {x : Var s1} {σ : Subst s1 s2}
  (hd : σ.has_dom ns) :
  (x.subst σ).dom <= max x.dom ns := by
  cases x with
  | bound n =>
    -- bound variable: subst gives σ.var n, with domain <= ns
    simp [Var.subst, Var.dom]
    exact hd.hvar n
  | free n =>
    -- free variable: subst keeps it as is
    simp [Var.subst, Var.dom]

/-- Lifting a substitution preserves the domain bound. -/
theorem Subst.lift_has_dom {σ : Subst s1 s2} {k : Kind} (hd : σ.has_dom ns) :
    (σ.lift (k:=k)).has_dom ns := by
  constructor
  · intro x
    simp [Subst.lift]
    cases x with
    | here => simp [Var.dom]
    | there x' =>
      simp
      rw [Var.rename_dom]
      exact hd.hvar x'
  · intro X
    simp [Subst.lift]
    cases X with
    | here => simp [Ty.dom]
    | there X' =>
      simp
      rw [Ty.rename_dom]
      exact hd.htvar X'

theorem Ty.subst_dom {T : Ty s1} {σ : Subst s1 s2}
  (hd : σ.has_dom ns) :
  (T.subst σ).dom <= max T.dom ns := by
  induction T generalizing s2 with
  | top => simp [Ty.subst, Ty.dom]
  | tvar x => simp [Ty.subst, Ty.dom]; exact hd.htvar x
  | singleton x =>
    simp [Ty.subst, Ty.dom]
    have := Var.subst_dom hd (x:=x)
    omega
  | arrow T1 T2 ih1 ih2 =>
    simp [Ty.subst, Ty.dom]
    have h1 := ih1 hd
    have h2 := ih2 (Subst.lift_has_dom hd)
    omega
  | poly T1 T2 ih1 ih2 =>
    simp [Ty.subst, Ty.dom]
    have h1 := ih1 hd
    have h2 := ih2 (Subst.lift_has_dom hd)
    omega

theorem Exp.subst_dom {e : Exp s1} {σ : Subst s1 s2}
  (hd : σ.has_dom ns) :
  (e.subst σ).dom <= max e.dom ns := by
  induction e generalizing s2 with
  | var x =>
    simp [Exp.subst, Exp.dom]
    have := Var.subst_dom hd (x:=x)
    omega
  | abs T e ih =>
    simp [Exp.subst, Exp.dom]
    have h1 := Ty.subst_dom hd (T:=T)
    have h2 := ih (Subst.lift_has_dom hd)
    omega
  | app x y =>
    simp [Exp.subst, Exp.dom]
    have hx := Var.subst_dom hd (x:=x)
    have hy := Var.subst_dom hd (x:=y)
    omega
  | tabs T e ih =>
    simp [Exp.subst, Exp.dom]
    have h1 := Ty.subst_dom hd (T:=T)
    have h2 := ih (Subst.lift_has_dom hd)
    omega
  | tapp x T =>
    simp [Exp.subst, Exp.dom]
    have hx := Var.subst_dom hd (x:=x)
    have hT := Ty.subst_dom hd (T:=T)
    omega
  | letin e1 e2 ih1 ih2 =>
    simp [Exp.subst, Exp.dom]
    have h1 := ih1 hd
    have h2 := ih2 (Subst.lift_has_dom hd)
    omega

end FsubNext
