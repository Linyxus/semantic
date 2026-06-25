import Semantic.CoreCapybara.Capybara.Syntax
import Semantic.CoreCapybara.Capybara.Substitution

namespace CoreCapybara

inductive CapySubcapt : CapyCtx s -> CaptureSet s -> CaptureSet s -> Prop where
| sc_trans :
  CapySubcapt Γ C1 C2 ->
  CapySubcapt Γ C2 C3 ->
  -------------------
  CapySubcapt Γ C1 C3
| sc_elem :
  CaptureSet.Subset C1 C2 ->
  -------------------
  CapySubcapt Γ C1 C2
| sc_mode {C : CaptureSet s} :
  m1 ≤ m2 ->
  -------------------
  CapySubcapt Γ (C.applyMut m1) (C.applyMut m2)
| sc_union :
  CapySubcapt Γ C1 C3 ->
  CapySubcapt Γ C2 C3 ->
  -------------------
  CapySubcapt Γ (.union C1 C2) C3
| sc_var :
  CapyCtx.LookupVar Γ x T ->
  ----------------------------------
  CapySubcapt Γ (.var (.M .epsilon) (.bound x)) T.captureSet
| sc_cvar :
  CapyCtx.LookupCVar Γ c .access_only (.bound C) ->
  ----------------------------------
  CapySubcapt Γ (.cvar (.M .epsilon) c) C
| sc_ro :
  ----------------------------------
  CapySubcapt Γ C.applyRO C
| sc_ro_mono :
  CapySubcapt Γ C1 C2 ->
  ----------------------------------
  CapySubcapt Γ C1.applyRO C2.applyRO
| sc_drop_mono :
  CapySubcapt Γ C1 C2 ->
  ----------------------------------
  CapySubcapt Γ (C1.applyAccess .drop) (C2.applyAccess .drop)

inductive CapyHasKind : CapyCtx s -> CaptureSet s -> Mutability -> Prop where
| empty {m : Mutability} :
  -------------------
  CapyHasKind Γ {} m
| union {C1 C2 : CaptureSet s} :
  CapyHasKind Γ C1 m ->
  CapyHasKind Γ C2 m ->
  -------------------
  CapyHasKind Γ (C1 ∪ C2) m
| sc {C1 C2 : CaptureSet s} :
  CapySubcapt Γ C1 C2 ->
  CapyHasKind Γ C2 m ->
  -------------------
  CapyHasKind Γ C1 m
| rw {C : CaptureSet s} :
  -------------------
  CapyHasKind Γ C .epsilon
| imm {c : BVar s .cvar} :
  CapyCtx.LookupCVar Γ c a (.unbound .ro) ->
  -------------------
  CapyHasKind Γ (.cvar (.M .epsilon) c) .ro
| ro {C : CaptureSet s} :
  -------------------
  CapyHasKind Γ C.applyRO .ro

inductive CapySubbound : CapyCtx s -> CapyCaptureBound s -> CapyCaptureBound s -> Prop where
| capset :
  CapySubcapt Γ C1 C2 ->
  -------------------
  CapySubbound Γ (.bound C1) (.bound C2)
| unbound {m1 m2 : Mutability} :
  m1 ≤ m2 ->
  -------------------
  CapySubbound Γ (.unbound m1) (.unbound m2)
| bound_unbound {C : CaptureSet s} {m : Mutability} :
  CapyHasKind Γ C m ->
  -------------------
  CapySubbound Γ (.bound C) (.unbound m)

inductive CapySepCheck : CapyCtx s -> CaptureSet s -> CaptureSet s -> Prop where
| sep_symm :
  CapySepCheck Γ C1 C2 ->
  -------------------
  CapySepCheck Γ C2 C1
| sep_union :
  CapySepCheck Γ C1 C3 ->
  CapySepCheck Γ C2 C3 ->
  -------------------
  CapySepCheck Γ (C1 ∪ C2) C3
| sep_empty {C : CaptureSet s} :
  -------------------
  CapySepCheck Γ {} C
| sep_ro :
  C1.IsClosed ->
  C2.IsClosed ->
  CapyCaptureSet.AccessOnly Γ C1 ->
  CapyCaptureSet.AccessOnly Γ C2 ->
  CapyHasKind Γ C1 .ro ->
  CapyHasKind Γ C2 .ro ->
  -------------------
  CapySepCheck Γ C1 C2
| sep_sc {C1 C2 C1' : CaptureSet s} :
  CapySepCheck Γ C1 C2 ->
  CapySubcapt Γ C1' C1 ->
  CapyCaptureSet.EquivP Γ C1' C1 ->
  --------------------
  CapySepCheck Γ C1' C2
| sep_distinct {c1 c2 : BVar s .cvar} :
  c1 ≠ c2 ->
  --------------------
  CapySepCheck Γ (.cvar m1 c1) (.cvar m2 c2)

inductive CapyDisjCheck : CapyCtx s -> CaptureSet s -> CaptureSet s -> Prop where
| disj_symm :
  CapyDisjCheck Γ C1 C2 ->
  -------------------
  CapyDisjCheck Γ C2 C1
| disj_empty {C : CaptureSet s} :
  -------------------
  CapyDisjCheck Γ {} C
| disj_union :
  CapyDisjCheck Γ C1 C3 ->
  CapyDisjCheck Γ C2 C3 ->
  -------------------
  CapyDisjCheck Γ (C1 ∪ C2) C3
| disj_peaks :
  C1.IsClosed ->
  CapyDisjCheck Γ (CapyCaptureSet.peaks Γ C1) C2 ->
  --------------------
  CapyDisjCheck Γ C1 C2
| disj_droppable {c1 c2 : BVar s .cvar} :
  Γ.TwoDistinctDroppable c1 c2 ->
  --------------------
  CapyDisjCheck Γ (.cvar a1 c1) (.cvar a2 c2)

-- obsolete: superseded by direct kind/separation checks
-- inductive Satisfy : CapyCtx s -> SepCtx s -> Prop where
-- | satisfy {Ψ : SepCtx s} :
--   (hkind : ∀ C m, Ψ.Has C m -> CapyHasKind Γ C m) ->
--   (hsep : ∀ C1 m1 C2 m2, Ψ.HasTwoDistinct C1 m1 C2 m2 -> CapySepCheck Γ C1 C2) ->
--   -------------------------------------------
--   Satisfy Γ Ψ

inductive CapySubtyp : CapyCtx s -> CapyTy .capt s -> CapyTy .capt s -> Prop where
| top {T : CapyTy .capt s} :
  T.IsPureType ->
  -------------------
  CapySubtyp Γ T .top
| refl :
  -------------------
  CapySubtyp Γ T T
| trans :
  (hT2 : T2.IsClosed) ->
  CapySubtyp Γ T1 T2 ->
  CapySubtyp Γ T2 T3 ->
  -------------------
  CapySubtyp Γ T1 T3
| tvar :
  CapyCtx.LookupTVar Γ X S ->
  -------------------
  CapySubtyp Γ (.tvar X) S.core
| arrow :
  CapySubtyp (Γ,C<:.unbound .epsilon) T2 T1 ->
  CapySubcapt Γ cs1 cs2 ->
  CapySubtyp
    (Γ,C<:.unbound .epsilon,x:T2,C<:.unbound .epsilon)
    (U1.rename Rename.implicit_cvar2) (U2.rename Rename.implicit_cvar2) ->
  --------------------------
  CapySubtyp Γ (.arrow T1 cs1 U1) (.arrow T2 cs2 U2)
| poly {S1 S2 : CapyPureTy s} :
  CapySubtyp Γ S2.core S1.core ->
  CapySubcapt Γ cs1 cs2 ->
  CapySubtyp (Γ,X<:S2,C<:.unbound .epsilon) T1 T2 ->
  --------------------------
  CapySubtyp Γ (.poly S1.core cs1 T1) (.poly S2.core cs2 T2)
| cpoly :
  CapySubbound Γ cb2 cb1 ->
  CapySubcapt Γ cs1 cs2 ->
  CapySubtyp (Γ,C<:cb2,C<:.unbound .epsilon) T1 T2 ->
  ----------------------------------------
  CapySubtyp Γ (.cpoly cb1 cs1 T1) (.cpoly cb2 cs2 T2)

inductive CapySeqComp : CapyCtx s -> CaptureSet s -> CaptureSet s -> Prop where
| seq_sc :
  CapySubcapt Γ C1 C1' ->
  CapyCaptureSet.EquivP Γ C1 C1' ->
  CapySeqComp Γ C1' C2 ->
  --------------------
  CapySeqComp Γ C1 C2
| seq_union :
  CapySeqComp Γ C1 C ->
  CapySeqComp Γ C2 C ->
  --------------------
  CapySeqComp Γ (C1 ∪ C2) C
| seq_access_only :
  C1.IsClosed ->
  CapyCaptureSet.AccessOnly Γ C1 ->
  ----------------------
  CapySeqComp Γ C1 C2
| seq_drop :
  CapyDisjCheck Γ C1 C2 ->
  ----------------------
  CapySeqComp Γ C1.applyDrop C2

/-- Typing judgement. -/
inductive CapyHasType : CaptureSet s -> CapyCtx s -> CapyExp s -> CapyTy sort s -> Prop where
| var :
  Γ.IsClosed ->
  Γ.LookupVar x T ->
  ----------------------------
  CapyHasType
    (.var (.M .epsilon) (.bound x))
    Γ
    (.var (.bound x))
    (T.refineCaptureSet (.var (.M .epsilon) (.bound x)))
| readonly :
  Γ.IsClosed ->
  Γ.LookupVar x (.cell C .epsilon) ->
  ---------------------------------
  CapyHasType
    (.var (.M .ro) (.bound x))
    Γ
    (.var (.bound x))
    (.cell (.var (.M .ro) (.bound x)) .ro)
| abs {T1 : CapyTy .capt (s,C)} {T2 : CapyTy .capt (s,x,C)} :
  T1.IsClosed ->
  CapyHasType
    ((cs.rename Rename.succ).rename Rename.succ ∪ (.var (.M .epsilon) (.bound .here)))
    (Γ,C<:.unbound .epsilon,x:T1)
    (e.rename Rename.implicit_cvar)
    ((T2.subst (CapySubst.openCVar D)).rename Rename.implicit_cvar) ->
  ----------------------------
  CapyHasType {} Γ (.abs T1 e) (.arrow T1 cs T2)
| tabs {S : CapyPureTy s} {T : CapyTy .capt (s,X,C)} :
  S.IsClosed ->
  CapyHasType (cs.rename Rename.succ) (Γ,X<:S) e (T.subst (CapySubst.openCVar D)) ->
  ----------------------------
  CapyHasType {} Γ (.tabs S e) (.poly S.core cs T)
| cabs {cb : CapyCaptureBound s} {T : CapyTy .capt (s,C,C)} :
  cb.IsClosed ->
  cb.IsValid Γ ->
  CapyHasType
    (cs.rename Rename.succ)
    (Γ,C<:cb)
    e
    (T.subst (CapySubst.openCVar D)) ->
  -----------------------------
  CapyHasType {} Γ (.cabs cb e) (.cpoly cb cs T)
| app :
  CapyHasType (.var (.M .epsilon) x) Γ (.var x) (.arrow T1 (.var (.M .epsilon) x) T2) ->
  CapyHasType (.var (.M .epsilon) y) Γ (.var y) (T1.subst (CapySubst.openCVar D)) ->
  CapySepCheck Γ D (CapyTy.interfere_set (.arrow T1 (.var (.M .epsilon) x) T2)) ->
  ----------------------------
  CapyHasType (.var (.M .epsilon) x ∪ .var (.M .epsilon) y) Γ (.app x y)
    (.exi (T2.subst (CapySubst.openVar y).lift))
| tapp {S : CapyPureTy s} :
  S.IsClosed ->
  CapyHasType (.var (.M .epsilon) x) Γ (.var x) (.poly S.core (.var (.M .epsilon) x) T) ->
  ----------------------------
  CapyHasType (.var (.M .epsilon) x) Γ (.tapp x S)
    (.exi (T.subst (CapySubst.openTVar S).lift))
| capp {D : CaptureSet s} :
  D.IsClosed ->
  CapyCaptureBound.IsValid Γ (.bound D) ->
  CapyHasType (.var (.M .epsilon) x) Γ (.var x) (.cpoly (.bound D) (.var (.M .epsilon) x) T) ->
  ----------------------------
  CapyHasType (.var (.M .epsilon) x) Γ (.capp x D)
    (.exi (T.subst (CapySubst.openCVar D).lift))
| letin :
  CapySeqComp Γ C1 C2 ->
  CapyHasType C1 Γ e1 T ->
  CapyHasType (C2.rename Rename.succ) (Γ,x:T) e2 (U.rename Rename.succ) ->
  --------------------------------
  CapyHasType (C1 ∪ C2) Γ (.letin e1 e2) U
| letin_unpack {T : CapyTy .capt (s,C)} :
  CapySeqComp Γ C1 C2 ->
  CapyHasType C1 Γ e1 (.exi T) ->
  CapyHasType
    (((C2.rename Rename.succ).rename Rename.succ) ∪
     (.cvar (.M .epsilon) (.there .here)) ∪
     (.cvar .drop (.there .here)))
    (Γ,C[.can_drop]<:.unbound .epsilon,x:T)
    (e2.rename Rename.implicit_cvar)
    ((U.rename Rename.succ).rename Rename.succ) ->
  --------------------------------
  CapyHasType (C1 ∪ C2) Γ (.letin e1 e2) U
| unit :
  ----------------------------
  CapyHasType {} Γ (.unit) .unit
| btrue :
  ----------------------------
  CapyHasType {} Γ (.btrue) .bool
| bfalse :
  ----------------------------
  CapyHasType {} Γ (.bfalse) .bool
| alloc :
  -- `alloc` introduces a fresh capability: the result is the existential
  -- `∃C. cell{C}` — a read-write cell capturing the freshly bound `C`.
  CapyHasType {} Γ (.var x) .bool ->
  ----------------------------
  CapyHasType {} Γ (.alloc x) (.exi (.cell (.cvar (.M .epsilon) .here) .epsilon))
| drop :
  Γ.IsClosed ->
  CapyCaptureSet.droppable Γ (CaptureSet.var (.M .epsilon) x) ->
  CapyHasType Cx Γ (.var x) (.cell (.var (.M .epsilon) x) .epsilon) ->
  ----------------------------
  CapyHasType (.var .drop x) Γ (.drop x) .unit
| read :
  CapyHasType Cx Γ (.var x) (.cell Cx .ro) ->
  ----------------------------
  CapyHasType Cx Γ (.read x) .bool
| write :
  CapyHasType Cx Γ (.var x) (.cell Cx .epsilon) ->
  CapyHasType {} Γ (.var y) .bool ->
  ----------------------------
  CapyHasType Cx Γ (.write x y) .unit
| cond :
  CapyHasType C1 Γ (.var x) .bool ->
  CapyHasType C2 Γ e2 T ->
  CapyHasType C3 Γ e3 T ->
  ----------------------------
  CapyHasType (C1 ∪ C2 ∪ C3) Γ (.cond x e2 e3) T
| par :
  CapyHasType C1 Γ e1 E1 ->
  CapyHasType C2 Γ e2 E2 ->
  CapySepCheck Γ C1 C2 ->
  ----------------------------
  CapyHasType (C1 ∪ C2) Γ (.par e1 e2) .unit
| invoke :
  CapyHasType (.var (.M .epsilon) x) Γ (.var x) (.cap (.var (.M .epsilon) x)) ->
  CapyHasType {} Γ (.var y) .unit ->
  ------------------------------------------------
  CapyHasType (.var (.M .epsilon) x) Γ (.app x y) .unit
| subtyp :
  CapyHasType C1 Γ e E1 ->
  CapySubcapt Γ C1 C2 ->
  CapySubtyp Γ E1 E2 ->
  C2.IsClosed -> E2.IsClosed ->
  ----------------------------
  CapyHasType C2 Γ e E2

notation:65 C " # " Γ " ⊢ " e " : " T => CapyHasType C Γ e T

end CoreCapybara
