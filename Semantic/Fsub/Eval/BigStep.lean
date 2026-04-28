import Semantic.Fsub.Syntax
import Semantic.Fsub.Substitution
import Semantic.Fsub.Heap

namespace Fsub

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
    (h1.subsumes h) ->
    (hv : Exp.IsVal v) ->
    Q1 v h1 ->
    ∀ l', h1 l' = none ->
      Eval
        (h1.extend l' ⟨v, hv⟩)
        (e2.subst (Subst.openVar (.free l')))
        Q) ->
  (h_var : ∀ {h1} {x : Var {}},
    (h1.subsumes h) ->
    Q1 (.var x) h1 ->
    Eval h1 (e2.subst (Subst.openVar x)) Q) ->
  Eval h (.letin e1 e2) Q

theorem eval_monotonic {h1 h2 : Heap}
  (hpred : Q.is_monotonic)
  (hsub : h2.subsumes h1)
  (heval : Eval h1 e Q) :
  Eval h2 e Q := by
  induction heval generalizing h2
  case eval_val hv hQ => exact Eval.eval_val hv (hpred hsub hQ)
  case eval_var hQ => exact Eval.eval_var (hpred hsub hQ)
  case eval_apply hx _ ih =>
    exact Eval.eval_apply (hsub _ _ hx) (ih hpred hsub)
  case eval_tapply hx _ ih =>
    exact Eval.eval_tapply (hsub _ _ hx) (ih hpred hsub)
  case eval_letin Q1 hpred0 _ _ _ ih ih_val ih_var =>
    apply Eval.eval_letin (Q1:=Q1) hpred0 (ih hpred0 hsub)
    case h_val =>
      intro h1 v hs1 hv hq1 l' hfresh
      exact ih_val (Heap.subsumes_trans hs1 hsub) hv hq1 l' hfresh hpred (Heap.subsumes_refl _)
    case h_var =>
      intro h1 x hs1 hq1
      exact ih_var (Heap.subsumes_trans hs1 hsub) hq1 hpred (Heap.subsumes_refl _)

def Hpost.entails_at (Q1 : Hpost) (h : Heap) (Q2 : Hpost) : Prop :=
  ∀ e, Q1 e h -> Q2 e h

def Hpost.entails_after (Q1 : Hpost) (h : Heap) (Q2 : Hpost) : Prop :=
  ∀ h', h'.subsumes h -> Q1.entails_at h' Q2

lemma Hpost.entails_to_entails_after {Q1 Q2 : Hpost}
  (himp : Q1.entails Q2) :
  Q1.entails_after h Q2 :=
  fun h' _ => himp h'

theorem Hpost.entails_after_refl (Q : Hpost) (h : Heap) :
  Q.entails_after h Q :=
  fun _ _ _ => id

theorem Hpost.entails_after_subsumes
  (himp : Hpost.entails_after Q1 h Q2)
  (hsub : h'.subsumes h) :
  Q1.entails_after h' Q2 :=
  fun H hheap => himp H (Heap.subsumes_trans hheap hsub)

theorem eval_post_monotonic_general {Q1 Q2 : Hpost}
  (himp : Q1.entails_after h Q2)
  (heval : Eval h e Q1) :
  Eval h e Q2 := by
  induction heval generalizing Q2
  case eval_val v Q H hv hQ =>
    exact Eval.eval_val hv (himp H (Heap.subsumes_refl H) _ hQ)
  case eval_var Q1 H x hQ =>
    exact Eval.eval_var (himp H (Heap.subsumes_refl H) _ hQ)
  case eval_apply hx _ ih => exact Eval.eval_apply hx (ih himp)
  case eval_tapply hx _ ih => exact Eval.eval_tapply hx (ih himp)
  case eval_letin _ Q0 hpred he1 _ _ ih ih_val ih_var =>
    specialize ih (Hpost.entails_after_refl _ _)
    apply Eval.eval_letin (Q1:=Q0) hpred ih
    case h_val =>
      intro h1 v hs1 hv hq1 l' hfresh
      exact ih_val hs1 hv hq1 l' hfresh
        (Hpost.entails_after_subsumes himp (Heap.subsumes_trans (Heap.extend_subsumes hfresh) hs1))
    case h_var =>
      intro h1 x hs1 hq1
      exact ih_var hs1 hq1 (Hpost.entails_after_subsumes himp hs1)

theorem eval_post_monotonic {Q1 Q2 : Hpost}
  (himp : Q1.entails Q2)
  (heval : Eval h e Q1) :
  Eval h e Q2 :=
  eval_post_monotonic_general (Hpost.entails_to_entails_after himp) heval

end Fsub
