import Semantic.Stlc.TypeSystem
import Semantic.Stlc.Interpreter
import Mathlib.Tactic

def hello : Nat := 42

structure Rebind (s1 : Store n1) (f : Rename n1 n2) (s2 : Store n2) where
  var : ∀ (x : Var n1),
    s2.lookup (f.var x) = (s1.lookup x).rename f

def Eval.rebind {f : Rename n1 n2}
  (hev : Eval s1 e1 v1)
  (ρ : Rebind s1 f s2) :
  Eval s2 (e1.rename f) (v1.rename f) := by
  induction hev generalizing n2
  case ev_var x0 =>
    have h := ρ.var x0
    simp [<-h]
    grind [Exp.rename, Eval]
  case ev_app ih1 ih2 => sorry
  case ev_abs => sorry
  case ev_nsucc ih => sorry
  case ev_btrue => sorry
  case ev_bfalse => sorry
  case ev_nzero => sorry
  case ev_pred_nzero ih => sorry
  case ev_pred_nsucc ih => sorry
  case ev_iszero_nzero ih => sorry
  case ev_iszero_nsucc ih => sorry
  case ev_cond_true ih1 ih2 => sorry
  case ev_cond_false ih1 ih2 => sorry
