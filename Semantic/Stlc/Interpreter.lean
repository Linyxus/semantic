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
