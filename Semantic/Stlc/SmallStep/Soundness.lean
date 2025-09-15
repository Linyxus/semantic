import Semantic.Stlc.SmallStep.Eval
import Semantic.Stlc.TypeSystem
import Semantic.Stlc.SmallStep.Denotation

theorem semantic_soundness
  (ht : Γ ⊢ e : T) :
  Γ ⊨ e : T := by sorry
