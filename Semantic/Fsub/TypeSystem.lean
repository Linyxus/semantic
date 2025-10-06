import Semantic.Fsub.Syntax
import Semantic.Fsub.Substitution

namespace Fsub

inductive Binding : Sig -> Kind -> Type where
| var : Ty s -> Binding s .var
| tvar : Ty s -> Binding s .tvar

def Binding.rename : Binding s1 k -> Rename s1 s2 -> Binding s2 k
| .var T, f => .var (T.rename f)
| .tvar T, f => .tvar (T.rename f)

inductive Ctx : Sig -> Type where
| empty : Ctx {}
| push : Ctx s -> Binding s k -> Ctx (s,,k)

def Ctx.push_var : Ctx s -> Ty s -> Ctx (s,x)
| Γ, T => Γ.push (.var T)

def Ctx.push_tvar : Ctx s -> Ty s -> Ctx (s,X)
| Γ, T => Γ.push (.tvar T)

infixl:65 ",x:" => Ctx.push_var
infixl:65 ",X<:" => Ctx.push_tvar

inductive Ctx.LookupTVar : Ctx s -> BVar s .tvar -> Ty s -> Prop
| here :
  Ctx.LookupTVar (.push Γ (.tvar S)) .here (S.rename Rename.succ)
| there {S : Ty s} {b : Binding s k} :
  Ctx.LookupTVar Γ X S ->
  Ctx.LookupTVar (.push Γ b) (.there X) (S.rename Rename.succ)

inductive Ctx.LookupVar : Ctx s -> BVar s .var -> Ty s -> Prop
| here :
  Ctx.LookupVar (.push Γ (.var T)) .here (T.rename Rename.succ)
| there {T : Ty s} {b : Binding s k} :
  Ctx.LookupVar Γ x T ->
  Ctx.LookupVar (.push Γ b) (.there x) (T.rename Rename.succ)

inductive Subtyp : Ctx s -> Ty s -> Ty s -> Prop where
| top :
  -------------------
  Subtyp Γ T .top
| refl :
  -------------------
  Subtyp Γ T T
| trans :
  Subtyp Γ T1 T2 ->
  Subtyp Γ T2 T3 ->
  -------------------
  Subtyp Γ T1 T3
| tvar :
  Ctx.LookupTVar Γ X S ->
  -------------------
  Subtyp Γ (.tvar X) S
| singleton :
  Ctx.LookupVar Γ x T ->
  -------------------
  Subtyp Γ (.singleton (.bound x)) T
| arrow :
  Subtyp Γ T2 T1 ->
  Subtyp (Γ,x:T2) U1 U2 ->
  --------------------------
  Subtyp Γ (.arrow T1 U1) (.arrow T2 U2)
| poly :
  Subtyp Γ S2 S1 ->
  Subtyp (Γ,X<:S2) T1 T2 ->
  --------------------------
  Subtyp Γ (.poly S1 T1) (.poly S2 T2)

inductive HasType : Ctx s -> Exp s -> Ty s -> Prop where
| var :
  ----------------------------
  HasType Γ (.var x) (.singleton x)
| abs :
  HasType (Γ,x:T1) e T2 ->
  ----------------------------
  HasType Γ (.abs T1 e) (.arrow T1 T2)
| tabs :
  HasType (Γ,X<:S) e T ->
  ----------------------------
  HasType Γ (.tabs S e) (.poly S T)
| app :
  HasType Γ (.var x) (.arrow T1 T2) ->
  HasType Γ (.var y) T1 ->
  ----------------------------
  HasType Γ (.app x y) (T2.subst (Subst.openVar y))
| tapp :
  HasType Γ (.var x) (.poly S T) ->
  ----------------------------
  HasType Γ (.tapp x S) (T.subst (Subst.openTVar S))
| letin :
  HasType Γ e1 T ->
  HasType (Γ,x:T) e2 (U.rename Rename.succ) ->
  --------------------------------
  HasType Γ (.letin e1 e2) U
| subtyp :
  HasType Γ e S ->
  Subtyp Γ S T ->
  ----------------------------
  HasType Γ e T

notation:65 Γ " ⊢ " e " : " T => HasType Γ e T

end Fsub
