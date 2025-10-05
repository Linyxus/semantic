import Semantic.FsubNext.Syntax
import Semantic.FsubNext.Substitution
import Semantic.FsubNext.Heap

namespace FsubNext

inductive Eval : Heap -> Exp {} -> (Heap -> Exp {} -> Prop) -> Prop where
| eval_val :
  (hv : Exp.IsVal v) ->
  (hQ : Q h v) ->
  Eval h v Q
| eval_var :
  (hQ : Q h (.var x)) ->
  Eval h (.var x) Q
| eval_apply {h : Heap} {x : Nat} :
  h x = some ⟨.abs T e, hv⟩ ->
  Eval h (e.subst (Subst.openVar y)) Q ->
  Eval h (.app (.free x) y) Q
| eval_tapply {h : Heap} {x : Nat} :
  h x = some ⟨.tabs T0 e, hv⟩ ->
  Eval h (e.subst (Subst.openTVar .top)) Q ->
  Eval h (.tapp (.free x) S) Q
| eval_letin {h : Heap} :
  Eval h e1 Q1 ->
  Eval h (.letin e1 e2) Q

end FsubNext
