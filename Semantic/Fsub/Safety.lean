import Semantic.Fsub.Soundness
import Semantic.Fsub.Eval.Props

namespace Fsub

/-! # Adequacy: semantic typing implies safety

A configuration `(h, e)` is _safe_ when every configuration reachable from it
by multi-step reduction is progressive, i.e. is either an answer or can take a step.
Semantically well-typed expressions are safe on finite heaps. -/

def Exp.Safe (h : Heap) (e : Exp {}) : Prop :=
  ∀ h' e',
    Reduce h e h' e' ->
    IsProgressive h' e'

/-- A configuration with an evaluation is safe (on a finite heap). -/
theorem eval_implies_safe
  (hfin : h.Finite)
  (heval : Eval h e Q) :
  Exp.Safe h e := by
  intro h' e' hred
  exact eval_implies_progressive
    (reduce_preserves_finite hfin hred)
    (reduce_preserves_eval heval hred)

/-- Adequacy of semantic typing: a semantically well-typed expression, closed by
  any environment typed in a finite heap, is safe in that heap. -/
theorem adequacy
  (ht : Γ ⊨ e : T)
  (hts : EnvTyping Γ env h)
  (hfin : h.Finite) :
  Exp.Safe h (e.subst (Subst.from_TypeEnv env)) := by
  have heval := ht env h hts
  simp only [Ty.exp_denot] at heval
  exact eval_implies_safe hfin heval

theorem Subst.from_TypeEnv_empty :
  Subst.from_TypeEnv .empty = Subst.id := by
  apply Subst.funext
  · intro x; cases x
  · intro x; cases x

/-- Adequacy for closed expressions: a closed semantically well-typed expression
  is safe in the empty heap. -/
theorem adequacy_closed {e : Exp {}}
  (ht : Ctx.empty ⊨ e : T) :
  Exp.Safe ∅ e := by
  have h := adequacy ht (env := .empty) (h := ∅) True.intro Heap.empty_finite
  rwa [Subst.from_TypeEnv_empty, Exp.subst_id] at h

/-- Type soundness for closed expressions: syntactic typing implies safety. -/
theorem soundness {e : Exp {}}
  (ht : Ctx.empty ⊢ e : T) :
  Exp.Safe ∅ e :=
  adequacy_closed (fundamental ht)

end Fsub
