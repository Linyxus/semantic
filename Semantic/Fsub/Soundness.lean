import Semantic.Fsub.Denotation
namespace Fsub

theorem sem_typ_var :
  Γ ⊨ (.var x) : (.singleton x) := by
  intro s e hts
  simp [Ty.exp_denot]
  constructor; constructor
  apply And.intro Reduce.red_refl _
  cases x
  case bound bx => rfl
  case free fx => rfl

theorem sem_typ_abs
  (ht : (Γ,x:T1) ⊨ e : T2) :
  Γ ⊨ (.abs T1 e) : (.arrow T1 T2) := by
  intro env store hts
  simp [Ty.exp_denot]
  constructor; constructor
  apply And.intro Reduce.red_refl _
  simp [Ty.val_denot]
  constructor; constructor
  split_ands
  · rfl
  · unfold SemanticTyping at ht
    sorry

theorem soundness
  (ht : Γ ⊢ e : T) :
  Γ ⊨ e : T := by
  induction ht
  case var => apply sem_typ_var
  case abs => sorry
  all_goals sorry

end Fsub
