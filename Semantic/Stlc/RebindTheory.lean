import Semantic.Stlc.TypeSystem
import Semantic.Stlc.Interpreter
import Mathlib.Tactic

def hello : Nat := 42

structure Rebind (s1 : Store n1) (f : Rename n1 n2) (s2 : Store n2) where
  var : ∀ (x : Var n1),
    s2.lookup (f.var x) = (s1.lookup x).rename f

theorem eval_rebind {f : Rename n1 n2}
  (ρ : Rebind s1 f s2)
  (e : Exp n1) :
  eval s2 (e.rename f) fuel = (eval s1 e fuel).rename f := by
  induction e generalizing fuel s2
  case var x0 =>
    cases fuel
    case zero => rfl
    case succ fuel =>
      simp [Exp.rename, eval]
      have := ρ.var x0
      grind [EvalResult.rename]
  case abs ih =>
    cases fuel
    case zero => rfl
    case succ fuel =>
      simp [Exp.rename, eval]
      grind [EvalResult.rename, Exp.rename]
  case app ih1 ih2 =>
    cases fuel
    case zero => rfl
    case succ fuel =>
      conv => lhs; simp [Exp.rename]
      sorry
  case btrue => sorry
  case bfalse => sorry
  case nzero => sorry
  case nsucc => sorry
  case pred => sorry
  case iszero => sorry
  case cond => sorry
