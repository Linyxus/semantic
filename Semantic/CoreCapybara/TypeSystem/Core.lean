import Semantic.CoreCapybara.Syntax
import Semantic.CoreCapybara.Substitution

namespace CoreCapybara

/-- The union of all capture sets in a vector. `⋃ᵢ Cs.get i`, with `unionAll ⟨[], _⟩ = {}`.
Used as the combined evidence of an `n`-ary `pack`. -/
def CaptureSet.unionAll {s : Sig} : {n : Nat} → List.Vector (CaptureSet s) n → CaptureSet s
  | 0, _ => {}
  | _ + 1, Cs => Cs.head ∪ CaptureSet.unionAll Cs.tail

/-- Substitution distributes over the union of a vector of capture sets. -/
theorem CaptureSet.unionAll_subst {s1 s2 : Sig} {σ : Subst s1 s2} :
    {n : Nat} → {Cs : List.Vector (CaptureSet s1) n} →
    (CaptureSet.unionAll Cs).subst σ
      = CaptureSet.unionAll (List.Vector.map (fun C => C.subst σ) Cs)
  | 0, _ => rfl
  | _ + 1, Cs => by
    change (List.Vector.head Cs ∪ CaptureSet.unionAll (List.Vector.tail Cs)).subst σ = _
    change _ = ((List.Vector.map _ Cs).head ∪ CaptureSet.unionAll ((List.Vector.map _ Cs).tail))
    obtain ⟨l, hl⟩ := Cs
    cases l with
    | nil => cases hl
    | cons c l' =>
      change (c.subst σ) ∪ (CaptureSet.unionAll ⟨l', _⟩).subst σ
        = (c.subst σ) ∪ CaptureSet.unionAll ⟨l'.map _, _⟩
      rw [CaptureSet.unionAll_subst]
      rfl

/-- If the union of all capture sets in a vector is closed, so is each entry. -/
theorem CaptureSet.unionAll_closed_inv {s : Sig} :
    {n : Nat} → {Cs : List.Vector (CaptureSet s) n} →
    (CaptureSet.unionAll Cs).IsClosed → ∀ cs ∈ Cs.toList, cs.IsClosed
  | 0, Cs, _ => by
    rw [List.Vector.eq_nil Cs]
    intro cs hmem
    cases hmem
  | _ + 1, Cs, h => by
    intro cs hmem
    obtain ⟨l, hl⟩ := Cs
    cases l with
    | nil => cases hl
    | cons c l' =>
      cases h with
      | union h1 h2 =>
        cases hmem with
        | head => exact h1
        | tail _ hmem => exact CaptureSet.unionAll_closed_inv h2 cs hmem

/-- The `n` freshly-bound capture variables of an `n`-ary existential, taken at access
`ε`: `⋃_{i<n} (cvar ε cᵢ)` over `s.extendCVars n`. In the `unpack` rule the continuation
accesses (this set) and drops (its `.drop` variant) all `n` unpacked capabilities. -/
def CaptureSet.freshCVars {s : Sig} : (n : Nat) → CaptureSet (s.extendCVars n)
  | 0 => {}
  | n + 1 => (.cvar (.M .epsilon) .here) ∪ (CaptureSet.freshCVars (s := s) n).rename Rename.succ

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
  MutabilityCtx.Has Ψ.mutability C .ro ->
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
| sep_mono {C1 C2 C1' : CaptureSet s} :
  -- Left-monotonicity: separation is preserved when the left side shrinks to a
  -- subcapture.  Sound (`SemSepCheck` = `Noninterference`, downward-closed); it
  -- closes the `fresh`-compilation cross pairs that `sep_sc` (peak-equivalence
  -- only) cannot.  Generalizes `sep_sc` by dropping its `EquivP` premise.
  SepCheck Γ C1 C2 ->
  Subcapt Γ C1' C1 ->
  --------------------
  SepCheck Γ C1' C2
| sep_lock {C1 C2 : CaptureSet s} :
  Ctx.LookupLock Γ ℓ Ψ ->
  SepCtx.HasTwoDistinct Ψ.sep C1 C2 ->
  --------------------
  SepCheck Γ C1 C2
| sep_droppable {c1 c2 : BVar s .cvar} :
  Γ.TwoDistinctDroppable c1 c2 ->
  --------------------
  SepCheck Γ (.cvar m1 c1) (.cvar m2 c2)

/-- Disjointness check. -/
inductive DisjCheck : Ctx s -> CaptureSet s -> CaptureSet s -> Prop where
| disj_symm :
  DisjCheck Γ C1 C2 ->
  -------------------
  DisjCheck Γ C2 C1
| disj_union :
  DisjCheck Γ C1 C3 ->
  DisjCheck Γ C2 C3 ->
  -------------------
  DisjCheck Γ (C1 ∪ C2) C3
| disj_empty {C : CaptureSet s} :
  -------------------
  DisjCheck Γ {} C
| disj_sc {C1 C2 C1' : CaptureSet s} :
  DisjCheck Γ C1 C2 ->
  Subcapt Γ C1' C1 ->
  CaptureSet.EquivP Γ C1' C1 ->
  --------------------
  DisjCheck Γ C1' C2
| disj_droppable {c1 c2 : BVar s .cvar} :
  Γ.TwoDistinctDroppable c1 c2 ->
  --------------------
  DisjCheck Γ (.cvar m1 c1) (.cvar m2 c2)

/-- The capture sets in a vector are mutually disjoint: any two distinct entries pass
the separation check (`SepCheck` is symmetric, so the ordering of the list is
immaterial). Premise of the `n`-ary `pack` rule: parallel opening instantiates the `n`
bound capture variables with the `n` evidences, and an `unpack` continuation is
entitled to treat distinct capture variables as separate — so overlapping evidences
would be unsound. -/
def CaptureSet.PairwiseSep {s : Sig} {n : Nat}
    (Γ : Ctx s) (Cs : List.Vector (CaptureSet s) n) : Prop :=
  Cs.toList.Pairwise (DisjCheck Γ)

inductive Satisfy : Ctx s -> ModalCtx s -> Prop where
| satisfy {Ψ : ModalCtx s} :
  (hkind : ∀ C m, Ψ.mutability.Has C m -> HasKind Γ C m) ->
  (hsep : ∀ C1 C2, Ψ.sep.HasTwoDistinct C1 C2 -> SepCheck Γ C1 C2) ->
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
| exi {s : Sig} {Γ : Ctx s} {n : Nat} {T1 T2 : Ty .capt (s.extendCVars n)} :
  Subtyp (Ctx.extendCVars .access_only Γ n) T1 T2 ->
  --------------------------
  Subtyp Γ (.exi n T1) (.exi n T2)
| typ :
  Subtyp Γ T1 T2 ->
  --------------------------
  Subtyp Γ (.typ T1) (.typ T2)
| cell {cs1 cs2 : CaptureSet s} {T : Ty .capt s} :
  -- Capture-covariance with the element type held invariant (conservative
  -- extension; the element stays rigid, only the handle's capture widens).
  Subcapt Γ cs1 cs2 ->
  --------------------------
  Subtyp Γ (.cell cs1 T) (.cell cs2 T)
| reader {cs1 cs2 : CaptureSet s} {T : Ty .capt s} :
  Subcapt Γ cs1 cs2 ->
  --------------------------
  Subtyp Γ (.reader cs1 T) (.reader cs2 T)
| cap {cs1 cs2 : CaptureSet s} :
  Subcapt Γ cs1 cs2 ->
  --------------------------
  Subtyp Γ (.cap cs1) (.cap cs2)
| poly_cap {S : Ty .capt s} {T : Ty .exi (s,X)} {cs1 cs2 : CaptureSet s} :
  Subcapt Γ cs1 cs2 ->
  --------------------------
  Subtyp Γ (.poly S cs1 T) (.poly S cs2 T)

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
| seq_sep :
  SepCheck Γ C1 C2 ->
  ----------------------
  SeqComp Γ C1 C2

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
  Γ.LookupVar x (.cell C T) ->
  ---------------------------------
  HasType
    {}
    Γ
    (.reader (.bound x))
    (.typ (.reader (.var (.M .ro) (.bound x)) T))
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
| consumer {T1 : Ty .capt (s,C)} {X : PeakSet s} :
  T1.IsClosed ->
  -- Every droppable capture variable of `Γ` is either killed in the body's
  -- context (`X`) or occurs in the closure's capture set `cs`.  The body can
  -- never use a droppable outside `cs` anyway (its use set is `cs ∪ C`), so
  -- killing the complement costs no expressiveness — and it is what lets the
  -- witness binder `C` (which may alias the capabilities consumed at the
  -- application site) coexist with `Γ`'s droppables in the separation
  -- invariant: the witness is separated from the closure's own captures by
  -- the application rule's `SeqComp`, and everything else is dead.
  (∀ c : BVar s .cvar, Γ.lookup_authority c = .can_drop →
    (∃ a, (CaptureSet.cvar a c) ⊆ X.cs) ∨ (∃ a, (CaptureSet.cvar a c) ⊆ cs)) ->
  HasType
    (((cs.rename (Rename.succ (k := .cvar))).rename (Rename.succ (k := .var))) ∪
      (.cvar (.M .epsilon) (.there .here)) ∪
      (.cvar .drop (.there .here)))
    (((Γ.kill_peaks X),C[.can_drop]<:.unbound),x:T1)
    e
    ((E.rename (Rename.succ (k := .cvar))).rename (Rename.succ (k := .var))) ->
  -----------------------------
  HasType {} Γ (.consumer cs (.exi 1 T1) e) (.typ (.consumer (.exi 1 T1) cs E))
| wrap :
  Ψ.IsClosed ->
  HasType
    (cs.rename Rename.succ) (Γ.push_lock Ψ)
    (e.rename Rename.succ) (E.rename Rename.succ) ->
  HasType {} Γ (.boxed cs Ψ e) (.typ (.modal cs Ψ E))
| pack {n : Nat} {Cs : List.Vector (CaptureSet s) n} {T : Ty .capt (s.extendCVars n)} :
  (CaptureSet.unionAll Cs).IsClosed ->
  (CaptureSet.unionAll Cs).AccessOnly Γ ->
  (CaptureSet.unionAll Cs).droppable Γ ->
  CaptureSet.PairwiseSep Γ Cs ->
  HasType {} Γ (.var x) (.typ (T.subst (Subst.openCVars Cs))) ->
  ----------------------------
  HasType
    ((CaptureSet.unionAll Cs) ∪ (CaptureSet.unionAll Cs).applyAccess .drop)
    Γ (.pack Cs x) (.exi n T)
| app :
  (CaptureSet.var (.M .epsilon) x).accessible Γ ->
  HasType {} Γ (.var x) (.typ (.arrow T1 (.var (.M .epsilon) x) T2)) ->
  HasType {} Γ (.var y) (.typ T1) ->
  ----------------------------
  HasType (.var (.M .epsilon) x) Γ (.app x y) (T2.subst (Subst.openVar y))
| consumer_app {C1 : CaptureSet s} {T1 : Ty .capt (s,C)} :
  SeqComp Γ C1 (.var (.M .epsilon) x) ->
  ((C1.peakset Γ).consumed).droppable Γ ->
  (CaptureSet.var (.M .epsilon) x).accessible Γ ->
  HasType {} Γ (.var x) (.typ (.consumer (.exi 1 T1) (.var (.M .epsilon) x) E)) ->
  HasType C1 Γ e (.exi 1 T1) ->
  ----------------------------
  HasType (C1 ∪ (.var (.M .epsilon) x)) Γ (.consumer_app x e) E
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
  /-- Unpack with a manufactured certificate-lock (paper H1 `unpack-own`,
  unified into THE unpack rule 2026-07-06).  Eliminates the existential: kills
  `C1`'s consumed peaks, binds the `n` witnesses at `.can_drop`, and pushes the
  lock `Ψw = [freshCVars n, C2↑n]` between the witnesses and `x` — the
  continuation reads witness-vs-`C2` separation off the lock (`sep_lock`) and
  witness-vs-witness off `sep_droppable`.  The plain `SeqComp` premise pays the
  lock: `pack_bound` confines every witness location to `C1`'s drop-covered
  footprint or fresh cells, the `droppable` premise is the anti-laundering
  anchor, and `captureSet_seqcomp_denot` turns `SeqComp` into the semantic
  drop-vs-any conflict — see notes/sep-owned-mechanization.md §07 (which
  corrects §05l: the earlier 'unsound-as-specified' verdict refuted only the
  `fundamental_sepcheck` discharge route, not the rule).  The lock stores `C2`
  PLAIN — a peaks-enriched entry would need a genuinely stronger premise.  The
  syntax `.unpack n t u` has no lock slot, so the continuation subject is
  `u.rename ((Rename.succ (k := .lock)).lift)`. -/
| unpack {s : Sig} {Γ : Ctx s} {C1 C2 : CaptureSet s} {t : Exp s} {U : Ty .exi s}
    {n : Nat} {T : Ty .capt (s.extendCVars n)} {u : Exp ((s.extendCVars n),x)} :
  SeqComp Γ C1 C2 ->
  ((C1.peakset Γ).consumed).droppable Γ ->
  HasType C1 Γ t (.exi n T) ->
  HasType
    ((((C2.rename (Rename.weakenCVars n)).rename (Rename.succ (k := .lock))).rename Rename.succ) ∪
     (((CaptureSet.freshCVars n).rename (Rename.succ (k := .lock))).rename Rename.succ) ∪
     ((((CaptureSet.freshCVars n).rename (Rename.succ (k := .lock))).rename Rename.succ).applyAccess
        .drop))
    (((Ctx.extendCVars .can_drop (Γ.kill_peaks ((C1.peakset Γ).consumed)) n).push_lock
        ⟨(SepCtx.empty.cons (C2.rename (Rename.weakenCVars n))).cons (CaptureSet.freshCVars n),
         MutabilityCtx.empty⟩),x:(T.rename (Rename.succ (k := .lock))))
    (u.rename ((Rename.succ (k := .lock)).lift))
    ((((U.rename (Rename.weakenCVars n)).rename (Rename.succ (k := .lock))).rename Rename.succ)) ->
  --------------------------------------------
  HasType (C1 ∪ C2) Γ (.unpack n t u) U
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
  HasType {} Γ (.var x) (.typ T) ->
  ----------------------------
  HasType
    {} Γ
    (.alloc x)
    (.exi 1 (.cell (.cvar (.M .epsilon) .here) (T.rename Rename.succ)))
| drop :
  Γ.IsClosed ->
  (CaptureSet.var (.M .epsilon) x).droppable Γ ->
  HasType {} Γ (.var x) (.typ (.cell (.var (.M .epsilon) x) T)) ->
  ----------------------------
  HasType (.var .drop x) Γ (.drop x) (.typ .unit)
| read :
  (CaptureSet.var (.M .epsilon) x).accessible Γ ->
  HasType {} Γ (.var x) (.typ (.reader C T)) ->
  ----------------------------
  HasType (.var (.M .epsilon) x) Γ (.read x) (.typ T)
| write :
  (CaptureSet.var (.M .epsilon) x).accessible Γ ->
  HasType {} Γ (.var x) (.typ (.cell Cx T)) ->
  HasType {} Γ (.var y) (.typ T) ->
  ----------------------------
  HasType (.var (.M .epsilon) x) Γ (.write x y) (.typ .unit)
| cond :
  HasType C1 Γ (.var x) (.typ .bool) ->
  HasType C2 Γ e2 T ->
  HasType C3 Γ e3 T ->
  ----------------------------
  HasType (C1 ∪ C2 ∪ C3) Γ (.cond x e2 e3) T
| par :
  HasType C1 Γ e1 E1 ->
  HasType C2 Γ e2 E2 ->
  SepCheck Γ C1 C2 ->
  ----------------------------
  HasType (C1 ∪ C2) Γ (.par C1 C2 e1 e2) (.typ .unit)
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
