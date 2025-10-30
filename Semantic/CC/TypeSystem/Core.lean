import Semantic.CC.Syntax
import Semantic.CC.Substitution

namespace CC

inductive Binding : Sig -> Kind -> Type where
| var : Ty .capt s -> Binding s .var
| tvar : Ty .shape s -> Binding s .tvar
| cvar : CaptureBound s -> Binding s .cvar

def Binding.rename : Binding s1 k -> Rename s1 s2 -> Binding s2 k
| .var T, f => .var (T.rename f)
| .tvar T, f => .tvar (T.rename f)
| .cvar cb, f => .cvar (cb.rename f)

inductive Ctx : Sig -> Type where
| empty : Ctx {}
| push : Ctx s -> Binding s k -> Ctx (s,,k)

def Ctx.push_var : Ctx s -> Ty .capt s -> Ctx (s,x)
| Γ, T => Γ.push (.var T)

def Ctx.push_tvar : Ctx s -> Ty .shape s -> Ctx (s,X)
| Γ, T => Γ.push (.tvar T)

def Ctx.push_cvar : Ctx s -> CaptureBound s -> Ctx (s,C)
| Γ, cb => Γ.push (.cvar cb)

infixl:65 ",x:" => Ctx.push_var
infixl:65 ",X<:" => Ctx.push_tvar
infixl:65 ",C<:" => Ctx.push_cvar

/-- A binding is closed if the type it contains is closed. -/
inductive Binding.IsClosed : Binding s k -> Prop where
| var : T.IsClosed -> Binding.IsClosed (.var T)
| tvar : T.IsClosed -> Binding.IsClosed (.tvar T)
| cvar : cb.IsClosed -> Binding.IsClosed (.cvar cb)

/-- A context is closed if all bindings in it are closed. -/
inductive Ctx.IsClosed : Ctx s -> Prop where
| empty : Ctx.IsClosed .empty
| push : Ctx.IsClosed Γ -> b.IsClosed -> Ctx.IsClosed (.push Γ b)

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

inductive Ctx.LookupCVar : Ctx s -> BVar s .cvar -> CaptureBound s -> Prop
| here :
  Ctx.LookupCVar (.push Γ (.cvar cb)) .here (cb.rename Rename.succ)
| there {b : Binding s k} :
  Ctx.LookupCVar Γ c cb ->
  Ctx.LookupCVar (.push Γ b0) (.there c) (cb.rename Rename.succ)

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
| sc_union :
  Subcapt Γ C1 C3 ->
  Subcapt Γ C2 C3 ->
  -------------------
  Subcapt Γ (.union C1 C2) C3
| sc_var :
  Ctx.LookupVar Γ x (.capt C S) ->
  ----------------------------------
  Subcapt Γ (.var (.bound x)) C
| sc_cvar :
  Ctx.LookupCVar Γ c (.bound C) ->
  ----------------------------------
  Subcapt Γ (.cvar c) C

inductive Subbound : Ctx s -> CaptureBound s -> CaptureBound s -> Prop where
| capset :
  Subcapt Γ C1 C2 ->
  -------------------
  Subbound Γ (.bound C1) (.bound C2)
| top :
  -------------------
  Subbound Γ B .unbound

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
| cpoly :
  Subbound Γ cb2 cb1 ->
  Subtyp (Γ,C<:cb2) T1 T2 ->
  ----------------------------------------
  Subtyp Γ (.cpoly cb1 T1) (.cpoly cb2 T2)
| capt :
  Subcapt Γ C1 C2 ->
  Subtyp Γ S1 S2 ->
  --------------------------
  Subtyp Γ (.capt C1 S1) (.capt C2 S2)
| exi :
  Subtyp (Γ,C<:.unbound) T1 T2 ->
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
| abs {T1 : Ty .capt s} :
  T1.IsClosed ->
  HasType (cs.rename Rename.succ ∪ (.var (.bound .here))) (Γ,x:T1) e T2 ->
  ----------------------------
  HasType {} Γ (.abs cs T1 e) (.typ (.capt cs (.arrow T1 T2)))
| tabs {S : Ty .shape s} :
  S.IsClosed ->
  HasType (cs.rename Rename.succ) (Γ,X<:S) e T ->
  ----------------------------
  HasType {} Γ (.tabs cs S e) (.typ (.capt cs (.poly S T)))
| cabs {cb : CaptureBound s} :
  cb.IsClosed ->
  HasType (cs.rename Rename.succ) (Γ,C<:cb) e T ->
  -----------------------------
  HasType {} Γ (.cabs cs cb e) (.typ (.capt cs (.cpoly cb T)))
| pack {C : CaptureSet s} :
  C.IsClosed ->
  HasType (.var x) Γ (.var x) (.typ (T.subst (Subst.openCVar C))) ->
  ----------------------------
  HasType (.var x) Γ (.pack C x) (.exi T)
| app :
  HasType C Γ (.var x) (.typ (.capt Cx (.arrow T1 T2))) ->
  HasType C Γ (.var y) (.typ T1) ->
  ----------------------------
  HasType C Γ (.app x y) (T2.subst (Subst.openVar y))
| tapp {S : Ty .shape s} :
  S.IsClosed ->
  HasType C Γ (.var x) (.typ (.capt Cx (.poly S T))) ->
  ----------------------------
  HasType C Γ (.tapp x S) (T.subst (Subst.openTVar S))
| capp {D : CaptureSet s} :
  D.IsClosed ->
  HasType C Γ (.var x) (.typ (.capt Cx (.cpoly cb T))) ->
  ----------------------------
  HasType C Γ (.capp x D) (T.subst (Subst.openCVar D))
| letin :
  HasType C Γ e1 (.typ T) ->
  HasType (C.rename Rename.succ) (Γ,x:T) e2 (U.rename Rename.succ) ->
  --------------------------------
  HasType C Γ (.letin e1 e2) U
| unpack :
  HasType C Γ t (.exi T) ->
  HasType
    ((C.rename Rename.succ).rename Rename.succ ∪ (.var (.bound .here)))
    (Γ,C<:.unbound,x:T)
    u
    ((U.rename Rename.succ).rename Rename.succ) ->
  --------------------------------------------
  HasType C Γ (.unpack t u) U
| unit :
  ----------------------------
  HasType {} Γ (.unit) (.typ (.capt {} .unit))
| invoke :
  HasType C Γ (.var x) (.typ (.capt Cx .cap)) ->
  HasType C Γ (.var y) (.typ (.capt Cy .unit)) ->
  ------------------------------------------------
  HasType C Γ (.app x y) (.typ (.capt {} .unit))
| subtyp :
  HasType C1 Γ e E1 ->
  Subcapt Γ C1 C2 ->
  Subtyp Γ E1 E2 ->
  C2.IsClosed -> E2.IsClosed ->
  ----------------------------
  HasType C2 Γ e E2

notation:65 C " # " Γ " ⊢ " e " : " T => HasType C Γ e T

end CC
