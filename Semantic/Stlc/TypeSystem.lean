import Semantic.Stlc.Substitution
/-!
Type system definitions for the simply typed lambda calculus.
-/

namespace Stlc

inductive Ctx : Nat -> Type where
| empty : Ctx 0
| var : Ctx n -> Ty -> Ctx (n+1)

infix:65 ",x:" => Ctx.var

inductive Ctx.Lookup : Ctx n -> Var n -> Ty -> Prop where
| here : Ctx.Lookup (Γ,x:T) .here T
| there :
  Ctx.Lookup Γ x U ->
  Ctx.Lookup (Γ,x:V) (.there x) U

inductive HasType : Ctx n -> Exp n -> Ty -> Prop where
| var :
  Ctx.Lookup Γ x T ->
  HasType Γ (.var x) T
| abs :
  HasType (Γ,x:T1) e T2 ->
  HasType Γ (.abs T1 e) (Ty.arrow T1 T2)
| app :
  HasType Γ e1 (Ty.arrow T1 T2) ->
  HasType Γ e2 T1 ->
  HasType Γ (.app e1 e2) T2
| btrue :
  HasType Γ .btrue Ty.bool
| bfalse :
  HasType Γ .bfalse Ty.bool
| nzero :
  HasType Γ .nzero Ty.nat
| nsucc :
  HasType Γ e Ty.nat ->
  HasType Γ (.nsucc e) Ty.nat
| pred :
  HasType Γ e Ty.nat ->
  HasType Γ (.pred e) Ty.nat
| iszero :
  HasType Γ e Ty.nat ->
  HasType Γ (.iszero e) Ty.bool
| cond :
  HasType Γ e1 Ty.bool ->
  HasType Γ e2 T ->
  HasType Γ e3 T ->
  HasType Γ (.cond e1 e2 e3) T

notation:65 Γ " ⊢ " e " : " T => HasType Γ e T

end Stlc
