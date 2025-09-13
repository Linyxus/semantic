import Semantic.Stlc.TypeSystem
import Semantic.Stlc.Interpreter
import Semantic.Stlc.Denotation
import Mathlib.Tactic

structure Rebind (s1 : Store n1) (f : Rename n1 n2) (s2 : Store n2) where
  var : ∀ (x : Var n1),
    s2.lookup (f.var x) = (s1.lookup x).rename f

def Rebind.liftVar (ρ : Rebind s1 f s2) :
  Rebind (s1.val v0) (f.liftVar) (s2.val (v0.rename f)) where
  var := fun
  | .here => by
    conv => lhs; simp [Rename.liftVar]
    simp [Store.lookup]
    simp [Exp.rename_succVar_comm]
  | .there x => by
    have h := ρ.var x
    conv => lhs; simp [Rename.liftVar]
    simp [Store.lookup]
    simp [<-Exp.rename_succVar_comm]
    congr

def Eval.rebind {f : Rename n1 n2}
  (hev : Eval s1 e1 v1)
  (ρ : Rebind s1 f s2) :
  Eval s2 (e1.rename f) (v1.rename f) := by
  induction hev generalizing n2 <;> try (solve | grind [Eval, Exp.rename])
  case ev_var x0 =>
    have h := ρ.var x0
    simp [<-h]
    grind [Exp.rename, Eval]
  case ev_app ih1 ih2 ih3 =>
    simp [Exp.openVar_rename_comm]
    apply ev_app
    { apply ih1 ρ }
    { apply ih2 ρ }
    { apply ih3
      apply ρ.liftVar }
  case ev_nsucc ih =>
    apply ev_nsucc
    · apply ih; apply ρ
    · grind [Exp.rename_is_numval]
  case ev_pred_nsucc ih =>
    apply ev_pred_nsucc
    · apply ih; apply ρ
    · grind [Exp.rename_is_numval]
  case ev_iszero_nsucc ih =>
    apply ev_iszero_nsucc
    · apply ih; apply ρ
    · grind [Exp.rename_is_numval]

def Rebind.succVar : Rebind s1 Rename.succVar (s1.val v) where
  var := fun x => by simp [Store.lookup, Rename.succVar]

mutual

theorem Ty.val_denot_rebind
  (ht : Ty.val_denot T ⟨s1, v1⟩)
  (ρ : Rebind s1 f s2) :
  Ty.val_denot T ⟨s2, v1.rename f⟩ := by
  cases T with
  | bool =>
    simp [Ty.val_denot] at ht ⊢
    exact Exp.rename_is_boolval ht
  | nat =>
    simp [Ty.val_denot] at ht ⊢
    exact Exp.rename_is_numval ht
  | arrow T U => sorry

theorem Ty.exp_denot_rebind
  (ht : Ty.exp_denot T ⟨s1, e1⟩)
  (ρ : Rebind s1 f s2) :
  Ty.exp_denot T ⟨s2, e1.rename f⟩ := by
  simp [Ty.exp_denot] at ht ⊢
  obtain ⟨v, heval, hval⟩ := ht
  use v.rename f
  constructor
  · exact Eval.rebind heval ρ
  · exact Ty.val_denot_rebind hval ρ

end
