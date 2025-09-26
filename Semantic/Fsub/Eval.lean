import Semantic.Fsub.Syntax
import Semantic.Fsub.Substitution

namespace Fsub

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

def Store.len : Store -> Nat
| .cons _ s => s.len + 1
| .nil => 0

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

end Fsub
