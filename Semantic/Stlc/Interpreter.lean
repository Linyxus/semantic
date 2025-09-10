import Semantic.Stlc.Substitution

inductive Store : Nat -> Type where
| empty : Store 0
| val : Store n -> Exp n -> Store (n+1)

def Store.lookup : Store n -> Var n -> Exp n
| .val _ v, .here => v.rename Rename.succVar
| .val s _, .there x => (s.lookup x).rename Rename.succVar

inductive EvalResult : Nat -> Type where
| ok : Exp n -> EvalResult n
| stuck : EvalResult n
| timeout : EvalResult n

def eval : Store n -> Exp n -> Nat -> EvalResult n
| _, _, 0 => .timeout
| s, .var x, _+1 => .ok (s.lookup x)
| _, .abs T e, _+1 => .ok (.abs T e)
| s, .app e1 e2, fuel+1 =>
  eval s e2 fuel |> fun
  | .ok v2 =>
    eval s e1 fuel |> fun
    | .ok v1 =>
      match v1 with
      | .abs _ body =>
        eval (Store.val s v2) body fuel |> fun
        | .ok v => .ok (v.subst (Subst.openVar v2))
        | .stuck => .stuck
        | .timeout => .timeout
      | _ => .stuck
    | .stuck => .stuck
    | .timeout => .timeout
  | .stuck => .stuck
  | .timeout => .timeout
| _, .btrue, _+1 => .ok .btrue
| _, .bfalse, _+1 => .ok .bfalse
| _, .nzero, _+1 => .ok .nzero
| s, .nsucc e, fuel+1 =>
  eval s e fuel |> fun
  | .ok v =>
    if v.is_num_val then
      .ok (.nsucc v)
    else
      .stuck
  | .stuck => .stuck
  | .timeout => .timeout
| s, .pred e, fuel+1 =>
  eval s e fuel |> fun
  | .ok v =>
    match v with
    | .nzero => .ok .nzero
    | .nsucc nv =>
      if nv.is_num_val then
        .ok nv
      else
        .stuck
    | _ => .stuck
  | .stuck => .stuck
  | .timeout => .timeout
| s, .iszero e, fuel+1 =>
  eval s e fuel |> fun
  | .ok v =>
    match v with
    | .nzero => .ok .btrue
    | .nsucc nv =>
      if nv.is_num_val then
        .ok .bfalse
      else
        .stuck
    | _ => .stuck
  | .stuck => .stuck
  | .timeout => .timeout
| s, .cond e1 e2 e3, fuel+1 =>
  eval s e1 fuel |> fun
  | .ok v =>
    match v with
    | .btrue => eval s e2 fuel
    | .bfalse => eval s e3 fuel
    | _ => .stuck
  | .stuck => .stuck
  | .timeout => .timeout

structure Config (n : Nat) where
  s : Store n
  e : Exp n

def EvalResult.rename : EvalResult n1 -> (f : Rename n1 n2) -> EvalResult n2
| .ok v, f => .ok (v.rename f)
| .stuck, _ => .stuck
| .timeout, _ => .timeout

inductive Eval : Store n -> Exp n -> Exp n -> Prop where
| ev_var :
  Eval s (.var x) (s.lookup x)
| ev_abs :
  Eval s (.abs T e) (.abs T e)
| ev_app :
  Eval s e1 (.abs T ebody) ->
  Eval s e2 v2 ->
  Eval (Store.val s v2) ebody eres ->
  Eval s (.app e1 e2) (eres.subst (Subst.openVar v2))
| ev_btrue :
  Eval s .btrue .btrue
| ev_bfalse :
  Eval s .bfalse .bfalse
| ev_nzero :
  Eval s .nzero .nzero
| ev_nsucc :
  Eval s e v ->
  v.is_num_val ->
  Eval s (.nsucc e) (.nsucc v)
| ev_pred_nzero :
  Eval s (.pred .nzero) .nzero
| ev_pred_nsucc :
  Eval s e (.nsucc v) ->
  v.is_num_val ->
  Eval s (.pred (.nsucc v)) v
| ev_iszero_nzero :
  Eval s (.iszero .nzero) .btrue
| ev_iszero_nsucc :
  Eval s e (.nsucc v) ->
  v.is_num_val ->
  Eval s (.iszero (.nsucc v)) .bfalse
| ev_cond_true :
  Eval s e1 .btrue ->
  Eval s e2 v2 ->
  Eval s (.cond e1 e2 e3) v2
| ev_cond_false :
  Eval s e1 .bfalse ->
  Eval s e3 v3 ->
  Eval s (.cond e1 e2 e3) v3
