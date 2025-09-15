import Semantic.Stlc.Syntax
import Semantic.Stlc.Substitution

inductive Step : Exp 0 -> Exp 0 -> Prop where
-- Application rules
| st_app_1 :
  Step e1 e1' ->
  Step (.app e1 e2) (.app e1' e2)
| st_app_2 :
  e1.IsVal ->
  Step e2 e2' ->
  Step (.app e1 e2) (.app e1 e2')
| st_app_beta :
  v.IsVal ->
  Step (.app (.abs T body) v) (body.subst (Subst.openVar v))

-- Successor rules
| st_nsucc :
  Step e e' ->
  Step (.nsucc e) (.nsucc e')

-- Predecessor rules
| st_pred :
  Step e e' ->
  Step (.pred e) (.pred e')
| st_pred_nzero :
  Step (.pred .nzero) .nzero
| st_pred_nsucc :
  nv.IsNumVal ->
  Step (.pred (.nsucc nv)) nv

-- IsZero rules
| st_iszero :
  Step e e' ->
  Step (.iszero e) (.iszero e')
| st_iszero_nzero :
  Step (.iszero .nzero) .btrue
| st_iszero_nsucc :
  nv.IsNumVal ->
  Step (.iszero (.nsucc nv)) .bfalse

-- Conditional rules
| st_cond :
  Step e1 e1' ->
  Step (.cond e1 e2 e3) (.cond e1' e2 e3)
| st_cond_true :
  Step (.cond .btrue e2 e3) e2
| st_cond_false :
  Step (.cond .bfalse e2 e3) e3

inductive Reduce : Exp 0 -> Exp 0 -> Prop where
| red_refl :
  Reduce e e
| red_step :
  Step e e' ->
  Reduce e' e'' ->
  Reduce e e''
