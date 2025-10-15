import Semantic.CC.Syntax
import Semantic.CC.Substitution
import Semantic.CC.Heap

namespace CC

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
  (h_var : ∀ {h1} {x : Var .var {}},
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
      intro h1 v hs1 hv hq1 l' hfresh
      -- h1.subsumes h2, h2.subsumes h1_original, so h1.subsumes h1_original
      have hs_orig := Heap.subsumes_trans hs1 hsub
      apply ih_val hs_orig hv hq1 l' hfresh hpred
      apply Heap.subsumes_refl
    case h_var =>
      intro h1 x hs1 hq1
      -- h1.subsumes h2, h2.subsumes h1_original, so h1.subsumes h1_original
      have hs_orig := Heap.subsumes_trans hs1 hsub
      apply ih_var hs_orig hq1 hpred
      apply Heap.subsumes_refl

def Hpost.entails_at (Q1 : Hpost) (h : Heap) (Q2 : Hpost) : Prop :=
  ∀ e, Q1 e h -> Q2 e h

def Hpost.entails_after (Q1 : Hpost) (h : Heap) (Q2 : Hpost) : Prop :=
  ∀ h', h'.subsumes h -> Q1.entails_at h' Q2

lemma Hpost.entails_to_entails_after {Q1 Q2 : Hpost}
  (himp : Q1.entails Q2) :
  Q1.entails_after h Q2 := by
  intro h' hsub
  intro e hQ
  apply himp h' e hQ

theorem Hpost.entails_after_refl (Q : Hpost) (h : Heap) :
  Q.entails_after h Q := by
  intro h' _
  intro e hQ
  exact hQ

theorem Hpost.entails_after_subsumes
  (himp : Hpost.entails_after Q1 h Q2)
  (hsub : h'.subsumes h) :
  Q1.entails_after h' Q2 := by
  intro H hheap e
  apply himp H _
  apply Heap.subsumes_trans hheap hsub

theorem eval_post_monotonic_general {Q1 Q2 : Hpost}
  (himp : Q1.entails_after h Q2)
  (heval : Eval h e Q1) :
  Eval h e Q2 := by
  induction heval generalizing Q2
  case eval_val v Q H hv hQ =>
    apply Eval.eval_val hv
    apply himp H _ _ hQ
    apply Heap.subsumes_refl
  case eval_var Q1 H x hQ =>
    apply Eval.eval_var
    apply himp H _ _ hQ
    apply Heap.subsumes_refl
  case eval_apply hx _ ih =>
    apply Eval.eval_apply hx
    apply ih himp
  case eval_tapply hx _ ih =>
    apply Eval.eval_tapply hx
    apply ih himp
  case eval_letin _ Q0 hpred he1 _ _ ih ih_val ih_var =>
    specialize ih (by apply Hpost.entails_after_refl)
    apply Eval.eval_letin (Q1:=Q0) hpred ih
    case h_val =>
      intro h1 v hs1 hv hq1 l' hfresh
      apply ih_val hs1 hv hq1 l' hfresh
      apply Hpost.entails_after_subsumes himp
      apply Heap.subsumes_trans (Heap.extend_subsumes hfresh) hs1
    case h_var =>
      intro h1 x hs1 hq1
      apply ih_var hs1 hq1
      apply Hpost.entails_after_subsumes himp
      apply hs1

theorem eval_post_monotonic {Q1 Q2 : Hpost}
  (himp : Q1.entails Q2)
  (heval : Eval h e Q1) :
  Eval h e Q2 := by
  apply eval_post_monotonic_general _ heval
  apply Hpost.entails_to_entails_after himp

end CC
