import Semantic.Fsub.Denotation
namespace Fsub

theorem soundness
  (ht : Γ ⊢ e : T) :
  Γ ⊨ e : T := by
  induction ht
  case var => sorry
  all_goals sorry

end Fsub
