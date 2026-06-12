import Semantic.CoreCapybara.Syntax
import Semantic.CoreCapybara.Substitution

namespace CoreCapybara

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
| sc_mode {C : CaptureSet s} :
  m1 ≤ m2 ->
  -------------------
  Subcapt Γ (C.applyMut m1) (C.applyMut m2)
| sc_union :
  Subcapt Γ C1 C3 ->
  Subcapt Γ C2 C3 ->
  -------------------
  Subcapt Γ (.union C1 C2) C3
| sc_var :
  Ctx.LookupVar Γ x T ->
  ----------------------------------
  Subcapt Γ (.var (.M .epsilon) (.bound x)) T.captureSet
| sc_cvar :
  Ctx.LookupCVar Γ c .access_only (.bound C) ->
  ----------------------------------
  Subcapt Γ (.cvar (.M .epsilon) c) C
| sc_ro :
  ----------------------------------
  Subcapt Γ C.applyRO C
| sc_ro_mono :
  Subcapt Γ C1 C2 ->
  ----------------------------------
  Subcapt Γ C1.applyRO C2.applyRO
| sc_drop_mono :
  Subcapt Γ C1 C2 ->
  ----------------------------------
  Subcapt Γ (C1.applyAccess .drop) (C2.applyAccess .drop)

inductive HasKind : Ctx s -> CaptureSet s -> Mutability -> Prop where
| empty {m : Mutability} :
  -------------------
  HasKind Γ {} m
| union {C1 C2 : CaptureSet s} :
  HasKind Γ C1 m ->
  HasKind Γ C2 m ->
  -------------------
  HasKind Γ (C1 ∪ C2) m
| sc {C1 C2 : CaptureSet s} :
  Subcapt Γ C1 C2 ->
  HasKind Γ C2 m ->
  -------------------
  HasKind Γ C1 m
| rw {C : CaptureSet s} :
  -------------------
  HasKind Γ C .epsilon
| imm {C : CaptureSet s} :
  Ctx.LookupLock Γ ℓ Ψ ->
  SepCtx.Has Ψ C .ro ->
  -------------------
  HasKind Γ C .ro
| ro {C : CaptureSet s} :
  -------------------
  HasKind Γ C.applyRO .ro

inductive Subbound : Ctx s -> CaptureBound s -> CaptureBound s -> Prop where
| capset :
  Subcapt Γ C1 C2 ->
  -------------------
  Subbound Γ (.bound C1) (.bound C2)
| top :
  -------------------
  Subbound Γ B .unbound

inductive SepCheck : Ctx s -> CaptureSet s -> CaptureSet s -> Prop where
| sep_symm :
  SepCheck Γ C1 C2 ->
  -------------------
  SepCheck Γ C2 C1
| sep_union :
  SepCheck Γ C1 C3 ->
  SepCheck Γ C2 C3 ->
  -------------------
  SepCheck Γ (C1 ∪ C2) C3
| sep_empty {C : CaptureSet s} :
  -------------------
  SepCheck Γ {} C
| sep_ro :
  C1.IsClosed ->
  C2.IsClosed ->
  C1.AccessOnly Γ ->
  C2.AccessOnly Γ ->
  HasKind Γ C1 .ro ->
  HasKind Γ C2 .ro ->
  -------------------
  SepCheck Γ C1 C2
| sep_sc {C1 C2 C1' : CaptureSet s} :
  SepCheck Γ C1 C2 ->
  Subcapt Γ C1' C1 ->
  CaptureSet.EquivP Γ C1' C1 ->
  --------------------
  SepCheck Γ C1' C2
| sep_lock {C1 C2 : CaptureSet s} :
  Ctx.LookupLock Γ ℓ Ψ ->
  SepCtx.HasTwoDistinct Ψ C1 m1 C2 m2 ->
  --------------------
  SepCheck Γ C1 C2
| sep_droppable {c1 c2 : BVar s .cvar} :
  Γ.TwoDistinctDroppable c1 c2 ->
  --------------------
  SepCheck Γ (.cvar m1 c1) (.cvar m2 c2)

inductive DisjCheck : Ctx s -> CaptureSet s -> CaptureSet s -> Prop where
| disj_symm :
  DisjCheck Γ C1 C2 ->
  -------------------
  DisjCheck Γ C2 C1
| disj_empty {C : CaptureSet s} :
  -------------------
  DisjCheck Γ {} C
| disj_union :
  DisjCheck Γ C1 C3 ->
  DisjCheck Γ C2 C3 ->
  -------------------
  DisjCheck Γ (C1 ∪ C2) C3
| disj_peaks :
  C1.IsClosed ->
  DisjCheck Γ (C1.peaks Γ) C2 ->
  --------------------
  DisjCheck Γ C1 C2
| disj_droppable {c1 c2 : BVar s .cvar} :
  Γ.TwoDistinctDroppable c1 c2 ->
  --------------------
  DisjCheck Γ (.cvar a1 c1) (.cvar a2 c2)

inductive Satisfy : Ctx s -> SepCtx s -> Prop where
| satisfy {Ψ : SepCtx s} :
  (hkind : ∀ C m, Ψ.Has C m -> HasKind Γ C m) ->
  (hsep : ∀ C1 m1 C2 m2, Ψ.HasTwoDistinct C1 m1 C2 m2 -> SepCheck Γ C1 C2) ->
  -------------------------------------------
  Satisfy Γ Ψ

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
  Subbound Γ cb2 cb1 ->
  Subcapt Γ cs1 cs2 ->
  Subtyp (Γ,C[.access_only]<:cb2) T1 T2 ->
  ----------------------------------------
  Subtyp Γ (.cpoly cb1 cs1 T1) (.cpoly cb2 cs2 T2)
| modal :
  Subcapt Γ cs1 cs2 ->
  Subtyp (Γ.push_lock Ψ) (E1.rename Rename.succ) (E2.rename Rename.succ) ->
  ----------------------------------------
  Subtyp Γ (.modal cs1 Ψ E1) (.modal cs2 Ψ E2)
| modal_modal :
  Γ.IsClosed ->
  Ψ1.IsClosed ->
  Ψ2.IsClosed ->
  Satisfy (Γ.push_lock Ψ2) (Ψ1.rename Rename.succ) ->
  ----------------------------------
  Subtyp Γ (.modal cs Ψ1 E) (.modal cs Ψ2 E)
| exi :
  Subtyp (Γ,C[.can_drop]<:.unbound) T1 T2 ->
  --------------------------
  Subtyp Γ (.exi T1) (.exi T2)
| typ :
  Subtyp Γ T1 T2 ->
  --------------------------
  Subtyp Γ (.typ T1) (.typ T2)

inductive SeqComp : Ctx s -> CaptureSet s -> CaptureSet s -> Prop where
| seq_sc :
  Subcapt Γ C1 C1' ->
  CaptureSet.EquivP Γ C1 C1' ->
  SeqComp Γ C1' C2 ->
  --------------------
  SeqComp Γ C1 C2
| seq_union :
  SeqComp Γ C1 C ->
  SeqComp Γ C2 C ->
  --------------------
  SeqComp Γ (C1 ∪ C2) C
| seq_access_only :
  C1.IsClosed ->
  CaptureSet.AccessOnly Γ C1 ->
  ----------------------
  SeqComp Γ C1 C2
| seq_drop :
  DisjCheck Γ C1 C2 ->
  ----------------------
  SeqComp Γ C1.applyDrop C2

inductive HasType : CaptureSet s -> Ctx s -> Exp s -> Ty .exi s -> Prop where
| var :
  Γ.IsClosed ->
  Γ.LookupVar x T ->
  ----------------------------
  HasType
    {}
    Γ
    (.var (.bound x))
    (.typ (T.refineCaptureSet (.var (.M .epsilon) (.bound x))))
| reader :
  Γ.IsClosed ->
  Γ.LookupVar x (.cell C) ->
  ---------------------------------
  HasType
    {}
    Γ
    (.reader (.bound x))
    (.typ (.reader (.var (.M .ro) (.bound x))))
| abs {T1 : Ty .capt s} :
  T1.IsClosed ->
  HasType (cs.rename Rename.succ) (Γ,x:T1) e T2 ->
  ----------------------------
  HasType {} Γ (.abs cs T1 e) (.typ (.arrow T1 cs T2))
| tabs {S : PureTy s} :
  S.IsClosed ->
  HasType (cs.rename Rename.succ) (Γ,X<:S) e T ->
  ----------------------------
  HasType {} Γ (.tabs cs S e) (.typ (.poly S.core cs T))
| cabs {cb : CaptureBound s} :
  cb.IsClosed ->
  cb.IsValid Γ ->
  HasType (cs.rename Rename.succ) (Γ,C[.access_only]<:cb) e T ->
  -----------------------------
  HasType {} Γ (.cabs cs cb e) (.typ (.cpoly cb cs T))
| wrap :
  Ψ.IsClosed ->
  HasType
    (cs.rename Rename.succ) (Γ.push_lock Ψ)
    (e.rename Rename.succ) (E.rename Rename.succ) ->
  HasType {} Γ (.boxed cs Ψ e) (.typ (.modal cs Ψ E))
| pack {C : CaptureSet s} :
  C.IsClosed ->
  C.AccessOnly Γ ->
  C.droppable Γ ->
  HasType {} Γ (.var x) (.typ (T.subst (Subst.openCVar C))) ->
  ----------------------------
  HasType (C.applyAccess .drop) Γ (.pack C x) (.exi T)
| app :
  (CaptureSet.var (.M .epsilon) x).accessible Γ ->
  HasType {} Γ (.var x) (.typ (.arrow T1 (.var (.M .epsilon) x) T2)) ->
  HasType {} Γ (.var y) (.typ T1) ->
  ----------------------------
  HasType (.var (.M .epsilon) x) Γ (.app x y) (T2.subst (Subst.openVar y))
| tapp {S : PureTy s} :
  (CaptureSet.var (.M .epsilon) x).accessible Γ ->
  S.IsClosed ->
  HasType {} Γ (.var x) (.typ (.poly S.core (.var (.M .epsilon) x) T)) ->
  ----------------------------
  HasType (.var (.M .epsilon) x) Γ (.tapp x S) (T.subst (Subst.openTVar S))
| capp {D : CaptureSet s} {I : CaptureSet s} :
  (CaptureSet.var (.M .epsilon) x).accessible Γ ->
  D.IsClosed ->
  CaptureBound.IsValid Γ (.bound D) ->
  HasType {} Γ (.var x) (.typ (.cpoly (.bound D) (.var (.M .epsilon) x) T)) ->
  ----------------------------
  HasType (.var (.M .epsilon) x) Γ (.capp x D) (T.subst (Subst.openCVar D))
| unwrap :
  HasType {} Γ (.var x) (.typ (.modal (.var (.M .epsilon) x) Ψ E)) ->
  Satisfy Γ Ψ ->
  ----------------------------
  HasType (.var (.M .epsilon) x) Γ (.unwrap x) E
| letin :
  SeqComp Γ C1 C2 ->
  HasType C1 Γ e1 (.typ T) ->
  HasType (C2.rename Rename.succ) ((Γ.kill_peaks ((C1.peakset Γ).consumed)),x:T) e2
    (U.rename Rename.succ) ->
  --------------------------------
  HasType (C1 ∪ C2) Γ (.letin e1 e2) U
| unpack :
  SeqComp Γ C1 C2 ->
  ((C1.peakset Γ).consumed).droppable Γ ->
  HasType C1 Γ t (.exi T) ->
  HasType
    (((C2.rename Rename.succ).rename Rename.succ) ∪
     (.cvar (.M .epsilon) (.there .here)) ∪
     (.cvar .drop (.there .here)))
    ((Γ.kill_peaks ((C1.peakset Γ).consumed)),C[.can_drop]<:.unbound,x:T)
    u
    ((U.rename Rename.succ).rename Rename.succ) ->
  --------------------------------------------
  HasType (C1 ∪ C2) Γ (.unpack t u) U
| unit :
  ----------------------------
  HasType {} Γ (.unit) (.typ .unit)
| btrue :
  ----------------------------
  HasType {} Γ (.btrue) (.typ .bool)
| bfalse :
  ----------------------------
  HasType {} Γ (.bfalse) (.typ .bool)
| alloc :
  HasType {} Γ (.var x) (.typ .bool) ->
  ----------------------------
  HasType {} Γ (.alloc x) (.exi (.cell (.cvar (.M .epsilon) .here)))
| drop :
  Γ.IsClosed ->
  (CaptureSet.var (.M .epsilon) x).droppable Γ ->
  HasType {} Γ (.var x) (.typ (.cell (.var (.M .epsilon) x))) ->
  ----------------------------
  HasType (.var .drop x) Γ (.drop x) (.typ .unit)
| read :
  (CaptureSet.var (.M .epsilon) x).accessible Γ ->
  HasType {} Γ (.var x) (.typ (.reader C)) ->
  ----------------------------
  HasType (.var (.M .epsilon) x) Γ (.read x) (.typ .bool)
| write :
  (CaptureSet.var (.M .epsilon) x).accessible Γ ->
  HasType {} Γ (.var x) (.typ (.cell Cx)) ->
  HasType {} Γ (.var y) (.typ .bool) ->
  ----------------------------
  HasType (.var (.M .epsilon) x) Γ (.write x y) (.typ .unit)
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
  (CaptureSet.var (.M .epsilon) x).accessible Γ ->
  HasType {} Γ (.var x) (.typ (.cap (.var (.M .epsilon) x))) ->
  HasType {} Γ (.var y) (.typ .unit) ->
  ------------------------------------------------
  HasType (.var (.M .epsilon) x) Γ (.app x y) (.typ .unit)
| subtyp :
  HasType C1 Γ e E1 ->
  Subcapt Γ C1 C2 ->
  Subtyp Γ E1 E2 ->
  C2.IsClosed -> E2.IsClosed ->
  ----------------------------
  HasType C2 Γ e E2

notation:65 C " # " Γ " ⊢ " e " : " T => HasType C Γ e T

end CoreCapybara
