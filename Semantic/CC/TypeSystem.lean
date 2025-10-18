import Semantic.CC.Syntax
import Semantic.CC.Substitution

namespace CC

inductive Binding : Sig -> Kind -> Type where
| var : Ty .capt s -> Binding s .var
| tvar : Ty .shape s -> Binding s .tvar
| cvar : Binding s .cvar

def Binding.rename : Binding s1 k -> Rename s1 s2 -> Binding s2 k
| .var T, f => .var (T.rename f)
| .tvar T, f => .tvar (T.rename f)
| .cvar, _ => .cvar

inductive Ctx : Sig -> Type where
| empty : Ctx {}
| push : Ctx s -> Binding s k -> Ctx (s,,k)

def Ctx.push_var : Ctx s -> Ty .capt s -> Ctx (s,x)
| Γ, T => Γ.push (.var T)

def Ctx.push_tvar : Ctx s -> Ty .shape s -> Ctx (s,X)
| Γ, T => Γ.push (.tvar T)

def Ctx.push_cvar : Ctx s -> Ctx (s,C)
| Γ => Γ.push .cvar

infixl:65 ",x:" => Ctx.push_var
infixl:65 ",X<:" => Ctx.push_tvar
postfix:65 ",C<:*" => Ctx.push_cvar

inductive Ctx.LookupTVar : Ctx s -> BVar s .tvar -> Ty .shape s -> Prop
| here :
  Ctx.LookupTVar (.push Γ (.tvar S)) .here (S.rename Rename.succ)
| there {S : Ty .shape s} {b : Binding s k} :
  Ctx.LookupTVar Γ X S ->
  Ctx.LookupTVar (.push Γ b) (.there X) (S.rename Rename.succ)

inductive Ctx.LookupVar : Ctx s -> BVar s .var -> Ty .capt s -> Prop
| here :
  Ctx.LookupVar (.push Γ (.var T)) .here (T.rename Rename.succ)
| there {T : Ty .capt s} {b : Binding s k} :
  Ctx.LookupVar Γ x T ->
  Ctx.LookupVar (.push Γ b) (.there x) (T.rename Rename.succ)

inductive Ctx.LookupCVar : Ctx s -> BVar s .cvar -> Prop
| here :
  Ctx.LookupCVar (.push Γ .cvar) .here
| there {b : Binding s k} :
  Ctx.LookupCVar Γ X ->
  Ctx.LookupCVar (.push Γ b) (.there X)

inductive Subcapt : Ctx s -> CaptureSet s -> CaptureSet s -> Prop where
| sc_trans :
  Subcapt Γ C1 C2 ->
  Subcapt Γ C2 C3 ->
  -------------------
  Subcapt Γ C1 C3
| sc_elem :
  CaptureSet.Subset C1 C2 ->
  -------------------
  Subcapt Γ C1 C2
| sc_var :
  Ctx.LookupVar Γ x (.capt C S) ->
  ----------------------------------
  Subcapt Γ (.var (.bound x)) C
| sc_union :
  Subcapt Γ C1 C3 ->
  Subcapt Γ C2 C3 ->
  -------------------
  Subcapt Γ (.union C1 C2) C3

inductive Subtyp : Ctx s -> Ty k s -> Ty k s -> Prop where
| top {T : Ty .shape s} :
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
| capt :
  Subcapt Γ C1 C2 ->
  Subtyp Γ S1 S2 ->
  --------------------------
  Subtyp Γ (.capt C1 S1) (.capt C2 S2)
| exi :
  Subtyp (Γ,C<:*) T1 T2 ->
  --------------------------
  Subtyp Γ (.exi T1) (.exi T2)
| typ :
  Subtyp Γ T1 T2 ->
  --------------------------
  Subtyp Γ (.typ T1) (.typ T2)

inductive HasType : CaptureSet s -> Ctx s -> Exp s -> Ty .exi s -> Prop where
| var :
  Γ.LookupVar x T ->
  ----------------------------
  HasType (.var (.bound x)) Γ (.var (.bound x)) (.typ T)
| abs :
  HasType (Γ,x:T1) e T2 ->
  ----------------------------
  HasType Γ (.abs T1 e) (.typ (.arrow T1 T2))
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

end CC
