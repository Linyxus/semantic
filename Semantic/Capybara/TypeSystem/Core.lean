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
| imm {c : BVar s .cvar} :
  Ctx.LookupCVar Γ c a (.unbound .ro) ->
  -------------------
  HasKind Γ (.cvar (.M .epsilon) c) .ro
| ro {C : CaptureSet s} :
  -------------------
  HasKind Γ C.applyRO .ro

inductive Subbound : Ctx s -> CaptureBound s -> CaptureBound s -> Prop where
| capset :
  Subcapt Γ C1 C2 ->
  -------------------
  Subbound Γ (.bound C1) (.bound C2)
| unbound {m1 m2 : Mutability} :
  m1 ≤ m2 ->
  -------------------
  Subbound Γ (.unbound m1) (.unbound m2)
| bound_unbound {C : CaptureSet s} {m : Mutability} :
  HasKind Γ C m ->
  -------------------
  Subbound Γ (.bound C) (.unbound m)

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
| sep_distinct {c1 c2 : BVar s .cvar} :
  c1 ≠ c2 ->
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

-- obsolete: superseded by direct kind/separation checks
-- inductive Satisfy : Ctx s -> SepCtx s -> Prop where
-- | satisfy {Ψ : SepCtx s} :
--   (hkind : ∀ C m, Ψ.Has C m -> HasKind Γ C m) ->
--   (hsep : ∀ C1 m1 C2 m2, Ψ.HasTwoDistinct C1 m1 C2 m2 -> SepCheck Γ C1 C2) ->
--   -------------------------------------------
--   Satisfy Γ Ψ

inductive Subtyp : Ctx s -> Ty s -> Ty s -> Prop where
| top {T : Ty s} :
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
  Subtyp (Γ,C<:.unbound .epsilon) T2 T1 ->
  Subcapt Γ cs1 cs2 ->
  Subtyp 
    (Γ,C<:.unbound .epsilon,x:T2,C<:.unbound .epsilon) 
    (U1.rename Rename.implicit_cvar2) (U2.rename Rename.implicit_cvar2) ->
  --------------------------
  Subtyp Γ (.arrow T1 cs1 U1) (.arrow T2 cs2 U2)
| poly {S1 S2 : PureTy s} :
  Subtyp Γ S2.core S1.core ->
  Subcapt Γ cs1 cs2 ->
  Subtyp (Γ,X<:S2,C<:.unbound .epsilon) T1 T2 ->
  --------------------------
  Subtyp Γ (.poly S1.core cs1 T1) (.poly S2.core cs2 T2)
| cpoly :
  Subbound Γ cb2 cb1 ->
  Subcapt Γ cs1 cs2 ->
  Subtyp (Γ,C<:cb2,C<:.unbound .epsilon) T1 T2 ->
  ----------------------------------------
  Subtyp Γ (.cpoly cb1 cs1 T1) (.cpoly cb2 cs2 T2)

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

-- Types are no longer sort-indexed, so the old `.typ`/`.exi` result wrappers are
-- gone: a judgement now produces a plain `Ty s`.
inductive HasType : CaptureSet s -> Ctx s -> Exp s -> Ty s -> Prop where
| var :
  Γ.IsClosed ->
  Γ.LookupVar x T ->
  ----------------------------
  HasType
    {}
    Γ
    (.var (.bound x))
    (T.refineCaptureSet (.var (.M .epsilon) (.bound x)))
| readonly :
  Γ.IsClosed ->
  Γ.LookupVar x (.cell C .epsilon) ->
  ---------------------------------
  HasType
    {}
    Γ
    (.var (.bound x))
    (.cell (.var (.M .ro) (.bound x)) .ro)
| abs {T1 : Ty (s,C)} {T2 : Ty (s,x,C)} :
  T1.IsClosed ->
  HasType 
    ((cs.rename Rename.succ).rename Rename.succ)
    (Γ,C<:.unbound .epsilon,x:T1) 
    (e.rename Rename.implicit_cvar) 
    ((T2.subst (Subst.openCVar D)).rename Rename.implicit_cvar) ->
  ----------------------------
  HasType {} Γ (.abs T1 e) (.arrow T1 cs T2)
| tabs {S : PureTy s} {T : Ty (s,X,C)} :
  S.IsClosed ->
  HasType (cs.rename Rename.succ) (Γ,X<:S) e (T.subst (Subst.openCVar D)) ->
  ----------------------------
  HasType {} Γ (.tabs S e) (.poly S.core cs T)
| cabs {cb : CaptureBound s} {T : Ty (s,C,C)} :
  cb.IsClosed ->
  cb.IsValid Γ ->
  HasType 
    (cs.rename Rename.succ) 
    (Γ,C<:cb) 
    e 
    (T.subst (Subst.openCVar D)) ->
  -----------------------------
  HasType {} Γ (.cabs cb e) (.cpoly cb cs T)
| app :
  -- DESIGN(flagged): the `accessible` (liveness) premise was dropped.  The
  -- argument's capture param is instantiated to `{y}`; the codomain existential
  -- `,C` is opened to `{}` (placeholder for the call's result capture).
  HasType {} Γ (.var x) (.arrow T1 (.var (.M .epsilon) x) T2) ->
  HasType {} Γ (.var y) (T1.subst (Subst.openCVar (.var (.M .epsilon) y))) ->
  ----------------------------
  HasType (.var (.M .epsilon) x) Γ (.app x y)
    (T2.subst ((Subst.openCVar {}).comp (Subst.openVar y)))
| tapp {S : PureTy s} :
  -- DESIGN(flagged): codomain existential `,C` opened to `{}` (placeholder).
  S.IsClosed ->
  HasType {} Γ (.var x) (.poly S.core (.var (.M .epsilon) x) T) ->
  ----------------------------
  HasType (.var (.M .epsilon) x) Γ (.tapp x S)
    (T.subst ((Subst.openCVar {}).comp (Subst.openTVar S)))
| capp {D : CaptureSet s} :
  -- DESIGN(flagged): codomain existential `,C` opened to `{}` (placeholder).
  D.IsClosed ->
  CaptureBound.IsValid Γ (.bound D) ->
  HasType {} Γ (.var x) (.cpoly (.bound D) (.var (.M .epsilon) x) T) ->
  ----------------------------
  HasType (.var (.M .epsilon) x) Γ (.capp x D)
    (T.subst ((Subst.openCVar {}).comp (Subst.openCVar D)))
| letin :
  -- DESIGN(flagged): `kill_peaks` (liveness) dropped; the let-bound type is now a
  -- plain `Ty s`.
  SeqComp Γ C1 C2 ->
  HasType C1 Γ e1 T ->
  HasType (C2.rename Rename.succ) (Γ,x:T) e2 (U.rename Rename.succ) ->
  --------------------------------
  HasType (C1 ∪ C2) Γ (.letin e1 e2) U
| unit :
  ----------------------------
  HasType {} Γ (.unit) .unit
| btrue :
  ----------------------------
  HasType {} Γ (.btrue) .bool
| bfalse :
  ----------------------------
  HasType {} Γ (.bfalse) .bool
| alloc :
  -- DESIGN(flagged): the existential result was dropped; `alloc` returns a cell
  -- with a placeholder empty capture and read-write mutability.  Fresh-capability
  -- handling needs the implicit-existential design.
  HasType {} Γ (.var x) .bool ->
  ----------------------------
  HasType {} Γ (.alloc x) (.cell {} .epsilon)
| drop :
  -- DESIGN(flagged): cell mutability := `.epsilon`.
  Γ.IsClosed ->
  (CaptureSet.var (.M .epsilon) x).droppable Γ ->
  HasType {} Γ (.var x) (.cell (.var (.M .epsilon) x) .epsilon) ->
  ----------------------------
  HasType (.var .drop x) Γ (.drop x) .unit
| read :
  -- DESIGN(flagged): `accessible` dropped; reads a read-only cell (was a reader).
  HasType {} Γ (.var x) (.cell C .ro) ->
  ----------------------------
  HasType (.var (.M .epsilon) x) Γ (.read x) .bool
| write :
  -- DESIGN(flagged): `accessible` dropped; cell mutability := `.epsilon`.
  HasType {} Γ (.var x) (.cell Cx .epsilon) ->
  HasType {} Γ (.var y) .bool ->
  ----------------------------
  HasType (.var (.M .epsilon) x) Γ (.write x y) .unit
| cond :
  HasType C1 Γ (.var x) .bool ->
  HasType C2 Γ e2 T ->
  HasType C3 Γ e3 T ->
  ----------------------------
  HasType (C1 ∪ C2 ∪ C3) Γ (.cond x e2 e3) T
| par :
  -- `par` no longer carries capture sets.
  HasType C1 Γ e1 E1 ->
  HasType C2 Γ e2 E2 ->
  SepCheck Γ C1 C2 ->
  ----------------------------
  HasType (C1 ∪ C2) Γ (.par e1 e2) .unit
| invoke :
  -- DESIGN(flagged): `accessible` dropped.
  HasType {} Γ (.var x) (.cap (.var (.M .epsilon) x)) ->
  HasType {} Γ (.var y) .unit ->
  ------------------------------------------------
  HasType (.var (.M .epsilon) x) Γ (.app x y) .unit
| subtyp :
  HasType C1 Γ e E1 ->
  Subcapt Γ C1 C2 ->
  Subtyp Γ E1 E2 ->
  C2.IsClosed -> E2.IsClosed ->
  ----------------------------
  HasType C2 Γ e E2

notation:65 C " # " Γ " ⊢ " e " : " T => HasType C Γ e T

end Capybara
