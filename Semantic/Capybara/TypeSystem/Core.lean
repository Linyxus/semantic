import Semantic.Capybara.Syntax
import Semantic.Capybara.Substitution

namespace Capybara

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
  Ctx.LookupVar Γ x T ->
  ----------------------------------
  Subcapt Γ (.var .epsilon (.bound x)) T.captureSet
| sc_ro :
  ----------------------------------
  Subcapt Γ C.applyRO C
| sc_ro_mono :
  Subcapt Γ C1 C2 ->
  ----------------------------------
  Subcapt Γ C1.applyRO C2.applyRO

inductive HasKind : Ctx s -> CaptureSet s -> Mutability -> Prop where
| eps :
  -------------------
  HasKind Γ C .epsilon
| ro {C : CaptureSet s} :
  -------------------
  HasKind Γ C.applyRO .ro
| cvar_ro :
  Ctx.LookupCVar Γ c .ro ->
  -------------------
  HasKind Γ (.cvar .epsilon c) .ro

inductive Subtyp : Ctx s -> Ty k s -> Ty k s -> Prop where
| top {T : Ty .capt s} :
  T.IsPureType ->
  -------------------
  Subtyp Γ T .top
| refl :
  -------------------
  Subtyp Γ T T
| trans :
  (hT2 : T2.IsClosed) ->
  Subtyp Γ T1 T2 ->
  Subtyp Γ T2 T3 ->
  -------------------
  Subtyp Γ T1 T3
| tvar :
  Ctx.LookupTVar Γ X S ->
  -------------------
  Subtyp Γ (.tvar X) S.core
| arrow :
  Subtyp Γ T2 T1 ->
  Subcapt Γ cs1 cs2 ->
  Subtyp (Γ,x:T2) U1 U2 ->
  --------------------------
  Subtyp Γ (.arrow T1 cs1 U1) (.arrow T2 cs2 U2)
| poly {S1 S2 : PureTy s} :
  Subtyp Γ S2.core S1.core ->
  Subcapt Γ cs1 cs2 ->
  Subtyp (Γ,X<:S2) T1 T2 ->
  --------------------------
  Subtyp Γ (.poly S1.core cs1 T1) (.poly S2.core cs2 T2)
| cpoly :
  m2 ≤ m1 ->
  Subcapt Γ cs1 cs2 ->
  Subtyp (Γ,C<:m2) T1 T2 ->
  ----------------------------------------
  Subtyp Γ (.cpoly m1 cs1 T1) (.cpoly m2 cs2 T2)
| exi :
  Subtyp (Γ,C<:.epsilon) T1 T2 ->
  --------------------------
  Subtyp Γ (.exi T1) (.exi T2)
| typ :
  Subtyp Γ T1 T2 ->
  --------------------------
  Subtyp Γ (.typ T1) (.typ T2)

inductive SepCheck : Ctx s -> CaptureSet s -> CaptureSet s -> Prop where
| sep_symm :
  SepCheck Γ C1 C2 ->
  -------------------
  SepCheck Γ C2 C1
| sep_var :
  Ctx.LookupVar Γ x T ->
  SepCheck Γ (T.captureSet.applyMut m) C ->
  -------------------
  SepCheck Γ (.var m (.bound x)) C
| sep_union :
  SepCheck Γ C1 C3 ->
  SepCheck Γ C2 C3 ->
  -------------------
  SepCheck Γ (C1 ∪ C2) C3
| sep_empty :
  -------------------
  SepCheck Γ {} C
| sep_ro :
  HasKind Γ C1 .ro ->
  HasKind Γ C2 .ro ->
  -------------------
  SepCheck Γ C1 C2
| sep_distinct_roots :
  c1 ≠ c2 ->
  --------------------
  SepCheck Γ (.cvar m1 c1) (.cvar m2 c2)

inductive HasType : CaptureSet s -> Ctx s -> Exp s -> Ty .exi s -> Prop where
| var :
  Γ.IsClosed ->
  Γ.LookupVar x T ->
  ----------------------------
  HasType
    (.var .epsilon (.bound x))
    Γ
    (.var (.bound x))
    (.typ (T.refineCaptureSet (.var .epsilon (.bound x))))
| reader :
  Γ.IsClosed ->
  Γ.LookupVar x (.cell C) ->
  ---------------------------------
  HasType
    (.var .ro (.bound x))
    Γ
    (.reader (.bound x))
    (.typ (.reader (.var .ro (.bound x))))
| abs {T1 : Ty .capt s} :
  T1.IsClosed ->
  HasType (cs.rename Rename.succ ∪ (.var .epsilon (.bound .here))) (Γ,x:T1) e T2 ->
  ----------------------------
  HasType {} Γ (.abs cs T1 e) (.typ (.arrow T1 cs T2))
| tabs {S : PureTy s} :
  S.IsClosed ->
  HasType (cs.rename Rename.succ) (Γ,X<:S) e T ->
  ----------------------------
  HasType {} Γ (.tabs cs S e) (.typ (.poly S.core cs T))
| cabs {m : Mutability} :
  HasType (cs.rename Rename.succ) (Γ,C<:m) e T ->
  -----------------------------
  HasType {} Γ (.cabs cs m e) (.typ (.cpoly m cs T))
| pack {C : CaptureSet s} :
  C.IsClosed ->
  HasType (.var .epsilon x) Γ (.var x) (.typ (T.subst (Subst.openCVar C))) ->
  ----------------------------
  HasType (.var .epsilon x) Γ (.pack C x) (.exi T)
| app :
  HasType (.var .epsilon x) Γ (.var x) (.typ (.arrow T1 (.var .epsilon x) T2)) ->
  HasType (.var .epsilon y) Γ (.var y) (.typ T1) ->
  ----------------------------
  HasType ((.var .epsilon x) ∪ (.var .epsilon y)) Γ (.app x y) (T2.subst (Subst.openVar y))
| tapp {S : PureTy s} :
  S.IsClosed ->
  HasType (.var .epsilon x) Γ (.var x) (.typ (.poly S.core (.var .epsilon x) T)) ->
  ----------------------------
  HasType (.var .epsilon x) Γ (.tapp x S) (T.subst (Subst.openTVar S))
| capp {D : CaptureSet s} {m : Mutability} {I : CaptureSet s} :
  D.IsClosed ->
  HasKind Γ D m ->
  HasType (.var .epsilon x) Γ (.var x) (.typ (.cpoly m (.var .epsilon x) T)) ->
  (Ty.cpoly m (.var .epsilon x) T).interfere_set = some I ->
  SepCheck Γ D I ->
  ----------------------------
  HasType (.var .epsilon x) Γ (.capp x D) (T.subst (Subst.openCVar D))
| letin :
  HasType C Γ e1 (.typ T) ->
  HasType (C.rename Rename.succ) (Γ,x:T) e2 (U.rename Rename.succ) ->
  --------------------------------
  HasType C Γ (.letin e1 e2) U
| unpack :
  HasType C Γ t (.exi T) ->
  HasType
    ((C.rename Rename.succ).rename Rename.succ)
    (Γ,C<:.epsilon,x:T)
    u
    ((U.rename Rename.succ).rename Rename.succ) ->
  --------------------------------------------
  HasType C Γ (.unpack t u) U
| unit :
  ----------------------------
  HasType {} Γ (.unit) (.typ .unit)
| btrue :
  ----------------------------
  HasType {} Γ (.btrue) (.typ .bool)
| bfalse :
  ----------------------------
  HasType {} Γ (.bfalse) (.typ .bool)
| read :
  HasType (.var .epsilon x) Γ (.var x) (.typ (.reader C)) ->
  ----------------------------
  HasType (.var .epsilon x) Γ (.read x) (.typ .bool)
| write :
  HasType (.var .epsilon x) Γ (.var x) (.typ (.cell Cx)) ->
  HasType (.var .epsilon y) Γ (.var y) (.typ .bool) ->
  ----------------------------
  HasType ((.var .epsilon x) ∪ (.var .epsilon y)) Γ (.write x y) (.typ .unit)
| cond :
  HasType C1 Γ (.var x) (.typ .bool) ->
  HasType C2 Γ e2 T ->
  HasType C3 Γ e3 T ->
  ----------------------------
  HasType (C1 ∪ C2 ∪ C3) Γ (.cond x e2 e3) T
| par :
  HasType C1 Γ e1 E ->
  HasType C2 Γ e2 E ->
  SepCheck Γ C1 C2 ->
  ----------------------------
  HasType (C1 ∪ C2) Γ (.par e1 e2) E
| invoke :
  HasType (.var .epsilon x) Γ (.var x) (.typ (.cap (.var .epsilon x))) ->
  HasType (.var .epsilon y) Γ (.var y) (.typ .unit) ->
  ------------------------------------------------
  HasType ((.var .epsilon x) ∪ (.var .epsilon y)) Γ (.app x y) (.typ .unit)
| subtyp :
  HasType C1 Γ e E1 ->
  Subcapt Γ C1 C2 ->
  Subtyp Γ E1 E2 ->
  C2.IsClosed -> E2.IsClosed ->
  ----------------------------
  HasType C2 Γ e E2

notation:65 C " # " Γ " ⊢ " e " : " T => HasType C Γ e T

end Capybara
