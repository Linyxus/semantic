import Semantic.FsubNext.Syntax
import Semantic.FsubNext.Substitution
import Semantic.FsubNext.Heap

namespace FsubNext

inductive Eval : Heap -> Exp {} -> Hpost -> Prop where
| eval_val :
  (hv : Exp.IsVal v) ->
  (hQ : Q v h) ->
  Eval h v Q
| eval_var :
  (hQ : Q (.var x) h) ->
  Eval h (.var x) Q
| eval_apply {h : Heap} {x : Nat} :
  h x = some ⟨.abs T e, hv⟩ ->
  Eval h (e.subst (Subst.openVar y)) Q ->
  Eval h (.app (.free x) y) Q
| eval_tapply {h : Heap} {x : Nat} :
  h x = some ⟨.tabs T0 e, hv⟩ ->
  Eval h (e.subst (Subst.openTVar .top)) Q ->
  Eval h (.tapp (.free x) S) Q
| eval_letin {h : Heap} {Q1 : Hpost} :
  (hpred : Q1.is_monotonic) ->  -- this local Q1 must be monotonic
  Eval h e1 Q1 ->
  (h_val : ∀ {h1} {v : Exp {}},
    (hv : Exp.IsVal v) ->
    Q1 v h1 ->
    ∀ l', h1 l' = none ->
      Eval
        (h1.extend l' ⟨v, hv⟩)
        (e2.subst (Subst.openVar (.free l')))
        Q) ->
  (h_var : ∀ {h1} {x : Var {}},
    Q1 (.var x) h1 ->
    Eval h1 (e2.subst (Subst.openVar x)) Q) ->
  Eval h (.letin e1 e2) Q

theorem eval_monotonic {h1 h2 : Heap}
  (hpred : Q.is_monotonic)
  (hsub : h2.subsumes h1)
  (heval : Eval h1 e Q) :
  Eval h2 e Q := by
  induction heval generalizing h2
  case eval_val => grind [Eval, Hpost.is_monotonic]
  case eval_var => grind [Eval, Hpost.is_monotonic]
  case eval_apply hx _ ih =>
    specialize ih hpred hsub
    apply Eval.eval_apply
    · apply hsub _ _ hx
    · assumption
  case eval_tapply hx _ ih =>
    specialize ih hpred hsub
    apply Eval.eval_tapply
    · apply hsub _ _ hx
    · assumption
  case eval_letin Q1 hpred0 _ _ _ ih ih_val ih_var =>
    specialize ih hpred0 hsub
    apply Eval.eval_letin (Q1:=Q1) hpred0 ih
    case h_val =>
      intro h1 v hv hq1 l' hfresh
      apply ih_val hv hq1 l' hfresh hpred
      apply Heap.subsumes_refl
    case h_var =>
      intro h1 x hq1
      apply ih_var hq1 hpred
      apply Heap.subsumes_refl

end FsubNext
