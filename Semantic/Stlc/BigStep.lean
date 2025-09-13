import Semantic.Stlc.Syntax
import Semantic.Stlc.Substitution

inductive Eval : Exp 0 -> Exp 0 -> Prop where
| ev_abs :
  Eval (.abs T e) (.abs T e)
| ev_app :
  Eval e1 (.abs T body) ->
  Eval e2 v2 ->
  Eval (body.subst (Subst.openVar v2)) v ->
  Eval (.app e1 e2) v
| ev_btrue :
  Eval .btrue .btrue
| ev_bfalse :
  Eval .bfalse .bfalse
| ev_nzero :
  Eval .nzero .nzero
| ev_nsucc :
  Eval e (.nsucc nv) ->
  nv.IsNumVal ->
  Eval (.nsucc e) (.nsucc nv)
| ev_pred_nzero :
  Eval (.pred .nzero) .nzero
| ev_pred_nsucc :
  Eval e (.nsucc nv) ->
  nv.IsNumVal ->
  Eval (.pred e) nv
| ev_iszero_nzero :
  Eval (.iszero .nzero) .btrue
| ev_iszero_nsucc :
  Eval e (.nsucc nv) ->
  nv.IsNumVal ->
  Eval (.iszero e) .bfalse
| ev_cond_true :
  Eval e1 .btrue ->
  Eval e2 v2 ->
  Eval e3 v3 ->
  Eval (.cond e1 e2 e3) v2
| ev_cond_false :
  Eval e1 .bfalse ->
  Eval e2 v2 ->
  Eval e3 v3 ->
  Eval (.cond e1 e2 e3) v3
