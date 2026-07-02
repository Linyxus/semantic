import Semantic.CoreCapybara.Semantics.Standardization
import Semantic.CoreCapybara.Semantics.Equivariance

/-! # Church–Rosser / confluence up to location-iso (for partial reductions)

  The generalization of `standardization` from runs-to-answers to ARBITRARY partial
  reductions.  Two genuine interleaving reductions out of the same configuration can
  always be brought back together.

  Design points (for audit):

  * **Up to a location renaming `π : Equiv.Perm Nat`.**  Confluence is only provable
    up to a location bijection: `step_alloc` chooses fresh names freely, so two runs
    diverge already at a single `alloc` (memory AND expression differ, only iso-equal).
    `π` is exposed explicitly (rather than hidden behind `Memory.Iso`/`ConfigIso`) so the
    same `π` ties together the memory agreement, the expression agreement, and the trace
    equivalence.  Taking `π = Equiv.refl` is the special case where both runs happen to
    pick the same fresh names.

  * **Up to `Trace.Equiv` (Mazurkiewicz).**  The two paths' combined traces agree only
    after renaming one by `π` and quotienting by independent-event reordering — i.e.
    `Trace.Equiv ((t1 ++ s1).renameLoc π) (t2 ++ s2)`.  This is the observable content of
    data-race freedom: scheduling is unobservable.

  * **CARRIER-FREE separation.**  Separation is exactly what rules out data races and
    makes `par` confluent — and it is carried by the interleaving `Step`'s OWN `par`
    guards (`TraceOk` trace bounds + branch `Noninterference`), not by a `Safe` carrier
    threaded through the run.  Threading the budget-indexed rely–guarantee `Safe.par`
    across single interleaved steps would demand the false operational-monotonicity
    transport (see the NOTE in `Semantics/BigStep.lean`); instead the
    diamond records the PROVENANCE of its closing legs (renamed replays of the opposite
    step), from which the wrap guards follow.  `Exp.WfInHeap` is the only precondition,
    mirroring the carrier-free `standardization`.

  Intended proof route: a local diamond (resolve the `alloc` name-clash by renaming one
  side via `Equiv.swap`, using the operational `*.renameLoc` equivariance from
  `Equivariance.lean`), lifted to runs by a strip lemma on top of the proven separation
  diamond `BigStep.step_run_commute`.

  Headline corollary (DRF / determinacy, to state separately): every interleaving run of
  a safe program to an answer reaches the SAME answer and memory up to `π`, with trace
  pinned down only up to `Trace.Equiv` — schedule-determinism. -/

namespace CoreCapybara

/-! ### PART 1 — guard-invariance under capability-set membership equivalence

  The genuine `Step` relation depends on `par` annotations ONLY through the reachability-based
  guards `TraceOk t (Cᵢ.reachability m)` and the `Noninterference` of the branches' reachabilities.
  Both guards are invariant under hasmem-equivalence of the underlying capability sets, letting us
  weaken confluence to hold up to reachability-equivalence of the (order-sensitive) `growByAllocs`
  annotations. -/

/-- Two capability sets are membership-equivalent when they have the same `hasmem` members. -/
def CapabilitySet.HmEq (A B : CapabilitySet) : Prop := ∀ mu l, A.hasmem mu l ↔ B.hasmem mu l

namespace CapabilitySet.HmEq

theorem refl (A : CapabilitySet) : HmEq A A := fun _ _ => Iff.rfl

theorem symm {A B : CapabilitySet} (h : HmEq A B) : HmEq B A := fun mu l => (h mu l).symm

theorem trans {A B C : CapabilitySet} (h1 : HmEq A B) (h2 : HmEq B C) : HmEq A C :=
  fun mu l => (h1 mu l).trans (h2 mu l)

/-- `union` is a congruence for `HmEq`. -/
theorem union {A A' B B' : CapabilitySet} (hA : HmEq A A') (hB : HmEq B B') :
    HmEq (A ∪ B) (A' ∪ B') := by
  intro mu l
  rw [CapabilitySet.hasmem_union_iff, CapabilitySet.hasmem_union_iff]
  exact or_congr (hA mu l) (hB mu l)

end CapabilitySet.HmEq

/-- `covers` is invariant under `HmEq`: coverage is membership weakened by mode. -/
theorem CapabilitySet.covers_hmEq {A B : CapabilitySet} (h : HmEq A B) {cm : CapMode} {l : Nat}
    (hcov : A.covers cm l) : B.covers cm l := by
  obtain ⟨mu, hmem, hle⟩ := CapabilitySet.covers_imp_exists_hasmem hcov
  exact CapabilitySet.covers_of_hasmem_le ((h mu l).mp hmem) hle

/-- `TraceOkFrom` is invariant under `HmEq` of the budget (it only consults `covers`). -/
theorem TraceOkFrom.hmEq {t : Trace} {A B : CapabilitySet} {L : List Nat}
    (htok : TraceOkFrom A L t) (h : CapabilitySet.HmEq A B) : TraceOkFrom B L t := by
  induction htok with
  | nil => exact TraceOkFrom.nil
  | alloc _ ih => exact TraceOkFrom.alloc ih
  | access hcond _ ih =>
    exact TraceOkFrom.access (hcond.imp (fun hcov => CapabilitySet.covers_hmEq h hcov) id) ih
  | dealloc hcond _ ih =>
    exact TraceOkFrom.dealloc (hcond.imp (fun hcov => CapabilitySet.covers_hmEq h hcov) id) ih

/-- `TraceOk` is invariant under `HmEq` of the budget. -/
theorem TraceOk.hmEq {t : Trace} {A B : CapabilitySet} (htok : TraceOk t A)
    (h : CapabilitySet.HmEq A B) : TraceOk t B :=
  TraceOkFrom.hmEq htok h

/-- Hasmem characterization of `Noninterference` (reverse of `shared_ro`): if every shared member
  is `.access .ro` on both sides, the two sets are non-interfering.  Proved by structural induction
  on both sets. -/
theorem CapabilitySet.noninterference_of_hasmem {A B : CapabilitySet}
    (h : ∀ mu1 mu2 l, A.hasmem mu1 l → B.hasmem mu2 l → mu1 = .access .ro ∧ mu2 = .access .ro) :
    CapabilitySet.Noninterference A B := by
  induction A with
  | empty => exact CapabilitySet.Noninterference.ni_empty
  | union A1 A2 ih1 ih2 =>
    exact CapabilitySet.Noninterference.ni_union
      (ih1 (fun mu1 mu2 l h1 h2 => h mu1 mu2 l (CapabilitySet.hasmem.left h1) h2))
      (ih2 (fun mu1 mu2 l h1 h2 => h mu1 mu2 l (CapabilitySet.hasmem.right h1) h2))
  | cap ma la =>
    induction B with
    | empty => exact CapabilitySet.Noninterference.ni_symm CapabilitySet.Noninterference.ni_empty
    | union B1 B2 ihb1 ihb2 =>
      exact CapabilitySet.Noninterference.ni_symm (CapabilitySet.Noninterference.ni_union
        (CapabilitySet.Noninterference.ni_symm
          (ihb1 (fun mu1 mu2 l h1 h2 => h mu1 mu2 l h1 (CapabilitySet.hasmem.left h2))))
        (CapabilitySet.Noninterference.ni_symm
          (ihb2 (fun mu1 mu2 l h1 h2 => h mu1 mu2 l h1 (CapabilitySet.hasmem.right h2)))))
    | cap mb lb =>
      by_cases hl : la = lb
      · subst hl
        obtain ⟨e1, e2⟩ := h ma mb la CapabilitySet.hasmem.here CapabilitySet.hasmem.here
        subst e1; subst e2
        exact CapabilitySet.Noninterference.ni_ro
      · exact CapabilitySet.Noninterference.ni_disj hl

/-- `Noninterference` is invariant under `HmEq` on the left. -/
theorem CapabilitySet.Noninterference.hmEq_left {A A' C : CapabilitySet}
    (hni : CapabilitySet.Noninterference A C) (h : CapabilitySet.HmEq A A') :
    CapabilitySet.Noninterference A' C := by
  refine CapabilitySet.noninterference_of_hasmem (fun mu1 mu2 l h1 h2 => ?_)
  exact hni.shared_ro ((h mu1 l).mpr h1) h2

/-- `Noninterference` is invariant under `HmEq` on the right. -/
theorem CapabilitySet.Noninterference.hmEq_right {A C C' : CapabilitySet}
    (hni : CapabilitySet.Noninterference A C) (h : CapabilitySet.HmEq C C') :
    CapabilitySet.Noninterference A C' :=
  (hni.ni_symm.hmEq_left h).ni_symm

/-! ### PART 2 — reachability equivalence of capture-set annotations

  `RReq C C'` holds when `C` and `C'` have membership-equal reachability in EVERY memory.  This is
  the equivalence under which `par` annotations may freely differ: `growByAllocs` is order-sensitive
  syntactically, but two grown annotations over traces with the same allocation SET are `RReq`. -/

/-- Membership in `(C.growByAllocs t).reachability m` decomposes into membership in `C`'s
  reachability or in some allocated cell's full-authority contribution. -/
theorem growByAllocs_reachability_hasmem_iff {m : Memory} {mu : CapMode} {k : Nat} :
    ∀ {t : Trace} {C : CaptureSet {}},
      CapabilitySet.hasmem mu k ((C.growByAllocs t).reachability m) ↔
        CapabilitySet.hasmem mu k (C.reachability m) ∨
          ∃ l, Trace.allocd t l ∧
            CapabilitySet.hasmem mu k
              (((CaptureSet.var (.M .epsilon) (.free l)) ∪ (CaptureSet.var .drop (.free l))
                : CaptureSet {}).reachability m) := by
  intro t
  induction t with
  | nil =>
    intro C
    simp only [CaptureSet.growByAllocs]
    constructor
    · intro h; exact Or.inl h
    · rintro (h | ⟨l, hl, _⟩)
      · exact h
      · simp only [Trace.allocd] at hl
  | cons it t ih =>
    intro C
    cases it with
    | alloc l =>
      rw [CaptureSet.growByAllocs, ih]
      constructor
      · rintro (h | ⟨l', hl', hcontrib⟩)
        · -- membership in `(var(Mε)l ∪ (var drop l ∪ C)).reachability m`
          rw [CaptureSet.reachability_union, CapabilitySet.hasmem_union_iff] at h
          rcases h with hl | hrest
          · refine Or.inr ⟨l, Or.inl rfl, ?_⟩
            rw [CaptureSet.reachability_union, CapabilitySet.hasmem_union_iff]
            exact Or.inl hl
          · rw [CaptureSet.reachability_union, CapabilitySet.hasmem_union_iff] at hrest
            rcases hrest with hd | hC
            · refine Or.inr ⟨l, Or.inl rfl, ?_⟩
              rw [CaptureSet.reachability_union, CapabilitySet.hasmem_union_iff]
              exact Or.inr hd
            · exact Or.inl hC
        · exact Or.inr ⟨l', Or.inr hl', hcontrib⟩
      · rintro (hC | ⟨l', hl', hcontrib⟩)
        · refine Or.inl ?_
          rw [CaptureSet.reachability_union, CapabilitySet.hasmem_union_iff]
          refine Or.inr ?_
          rw [CaptureSet.reachability_union, CapabilitySet.hasmem_union_iff]
          exact Or.inr hC
        · rcases hl' with rfl | hl'
          · refine Or.inl ?_
            rw [CaptureSet.reachability_union, CapabilitySet.hasmem_union_iff] at hcontrib ⊢
            rcases hcontrib with he | hd
            · exact Or.inl he
            · refine Or.inr ?_
              rw [CaptureSet.reachability_union, CapabilitySet.hasmem_union_iff]
              exact Or.inl hd
          · exact Or.inr ⟨l', hl', hcontrib⟩
    | access mu' l =>
      rw [CaptureSet.growByAllocs, ih]
      simp only [Trace.allocd]
    | dealloc l =>
      rw [CaptureSet.growByAllocs, ih]
      simp only [Trace.allocd]

/-- Reachability equivalence of capture-set annotations: same `hasmem` reachability at every
  memory.  The equivalence up to which `par` annotations may differ. -/
def CaptureSet.RReq (C C' : CaptureSet {}) : Prop :=
  ∀ m, CapabilitySet.HmEq (C.reachability m) (C'.reachability m)

namespace CaptureSet.RReq

theorem refl (C : CaptureSet {}) : RReq C C := fun _ => CapabilitySet.HmEq.refl _

theorem symm {C C' : CaptureSet {}} (h : RReq C C') : RReq C' C := fun m => (h m).symm

theorem trans {C C' C'' : CaptureSet {}} (h1 : RReq C C') (h2 : RReq C' C'') : RReq C C'' :=
  fun m => (h1 m).trans (h2 m)

/-- `RReq` is preserved by location renaming (reachability commutes with renaming). -/
theorem renameLoc {C C' : CaptureSet {}} (h : RReq C C') (π : Equiv.Perm Nat) :
    RReq (C.renameLoc π) (C'.renameLoc π) := by
  intro m mu l
  have hm : (m.renameLoc π.symm).renameLoc π = m := by
    rw [Memory.renameLoc_comp, Equiv.symm_trans_self, Memory.renameLoc_id]
  have hkey : ∀ (B : CaptureSet {}),
      CapabilitySet.hasmem mu l ((B.renameLoc π).reachability m) ↔
        CapabilitySet.hasmem mu (π.symm l) (B.reachability (m.renameLoc π.symm)) := by
    intro B
    calc CapabilitySet.hasmem mu l ((B.renameLoc π).reachability m)
        ↔ CapabilitySet.hasmem mu l
            ((B.renameLoc π).reachability ((m.renameLoc π.symm).renameLoc π)) := by rw [hm]
      _ ↔ CapabilitySet.hasmem mu l
            ((B.reachability (m.renameLoc π.symm)).renameLoc π) := by
          rw [CaptureSet.reachability_renameLoc]
      _ ↔ CapabilitySet.hasmem mu (π.symm l) (B.reachability (m.renameLoc π.symm)) := by
          have hh := CapabilitySet.hasmem_renameLoc π
            (C := B.reachability (m.renameLoc π.symm)) (m := mu) (l := π.symm l)
          rw [Equiv.apply_symm_apply] at hh; exact hh
  rw [hkey C, hkey C']
  exact h (m.renameLoc π.symm) mu (π.symm l)

end CaptureSet.RReq

/-- Two grown annotations over the SAME base `C` are `RReq` whenever their traces allocate the
  same SET of cells: the grown reachability adds only per-allocated-cell contributions, which are
  set-determined (not order-determined).  THIS closes the `par` SAME case. -/
theorem CaptureSet.growByAllocs_RReq_of_allocd_iff {C : CaptureSet {}} {t1 t2 : Trace}
    (h : ∀ l, Trace.allocd t1 l ↔ Trace.allocd t2 l) :
    CaptureSet.RReq (C.growByAllocs t1) (C.growByAllocs t2) := by
  intro m mu k
  rw [growByAllocs_reachability_hasmem_iff, growByAllocs_reachability_hasmem_iff]
  refine or_congr Iff.rfl ?_
  exact ⟨fun ⟨l, hl, hc⟩ => ⟨l, (h l).mp hl, hc⟩, fun ⟨l, hl, hc⟩ => ⟨l, (h l).mpr hl, hc⟩⟩

/-- `growByAllocs` over a common trace is a congruence for `RReq` on the base. -/
theorem CaptureSet.growByAllocs_RReq_congr {C C' : CaptureSet {}} (h : CaptureSet.RReq C C')
    (t : Trace) : CaptureSet.RReq (C.growByAllocs t) (C'.growByAllocs t) := by
  intro m mu k
  rw [growByAllocs_reachability_hasmem_iff, growByAllocs_reachability_hasmem_iff]
  exact or_congr (h m mu k) Iff.rfl

/-! ### PART 3 — annotation equivalence on expressions

  `Exp.AEq` is the structural congruence that allows the (order-sensitive) `par` annotations to
  differ up to reachability-equivalence `RReq`, while requiring SYNTACTIC equality of everything
  that can be lifted to the heap (all values, including their annotations) — so that `aeq_sim`
  preserves memory exactly.  Only the evaluation-position sub-terms (`par` branches, `cond`
  branches, `letin`/`unpack` heads) recurse with `AEq`; under-binder continuations stay
  syntactic. -/

inductive Exp.AEq : Exp {} → Exp {} → Prop where
  | eq {a b : Exp {}} : a = b → AEq a b
  | par {C1 C1' C2 C2' : CaptureSet {}} {e1 e1' e2 e2' : Exp {}} :
    CaptureSet.RReq C1 C1' → CaptureSet.RReq C2 C2' → AEq e1 e1' → AEq e2 e2' →
    AEq (.par C1 C2 e1 e2) (.par C1' C2' e1' e2')
  | cond {x : Var .var {}} {e2 e2' e3 e3' : Exp {}} :
    AEq e2 e2' → AEq e3 e3' → AEq (.cond x e2 e3) (.cond x e2' e3')
  | letin {e1 e1' : Exp {}} {k : Exp ({},x)} :
    AEq e1 e1' → AEq (.letin e1 k) (.letin e1' k)
  | unpack {e1 e1' : Exp {}} {k : Exp (({},C),x)} :
    AEq e1 e1' → AEq (.unpack e1 k) (.unpack e1' k)

namespace Exp.AEq

theorem of_eq {a b : Exp {}} (h : a = b) : AEq a b := AEq.eq h

theorem refl (e : Exp {}) : AEq e e := AEq.eq rfl

theorem symm {a b : Exp {}} (h : AEq a b) : AEq b a := by
  induction h with
  | eq h => exact AEq.eq h.symm
  | par h1 h2 _ _ ih1 ih2 => exact AEq.par h1.symm h2.symm ih1 ih2
  | cond _ _ ih2 ih3 => exact AEq.cond ih2 ih3
  | letin _ ih => exact AEq.letin ih
  | unpack _ ih => exact AEq.unpack ih

theorem trans {a b c : Exp {}} (hab : AEq a b) (hbc : AEq b c) : AEq a c := by
  induction hab generalizing c with
  | eq h => exact h ▸ hbc
  | @par C1 C1' C2 C2' e1 e1' e2 e2' h1 h2 _ _ ih1 ih2 =>
    cases hbc with
    | eq h => exact h ▸ AEq.par h1 h2 (ih1 (AEq.refl _)) (ih2 (AEq.refl _))
    | par h1' h2' hb1 hb2 => exact AEq.par (h1.trans h1') (h2.trans h2') (ih1 hb1) (ih2 hb2)
  | cond _ _ ih2 ih3 =>
    cases hbc with
    | eq h => exact h ▸ AEq.cond (ih2 (AEq.refl _)) (ih3 (AEq.refl _))
    | cond hb2 hb3 => exact AEq.cond (ih2 hb2) (ih3 hb3)
  | letin _ ih =>
    cases hbc with
    | eq h => exact h ▸ AEq.letin (ih (AEq.refl _))
    | letin hb => exact AEq.letin (ih hb)
  | unpack _ ih =>
    cases hbc with
    | eq h => exact h ▸ AEq.unpack (ih (AEq.refl _))
    | unpack hb => exact AEq.unpack (ih hb)

theorem renameLoc {a b : Exp {}} (h : AEq a b) (π : Equiv.Perm Nat) :
    AEq (a.renameLoc π) (b.renameLoc π) := by
  induction h with
  | eq h => exact AEq.eq (by rw [h])
  | par h1 h2 _ _ ih1 ih2 =>
    exact AEq.par (h1.renameLoc π) (h2.renameLoc π) ih1 ih2
  | cond _ _ ih2 ih3 => exact AEq.cond ih2 ih3
  | letin _ ih => exact AEq.letin ih
  | unpack _ ih => exact AEq.unpack ih

/-- An answer is `AEq` only to itself: answers are values/vars, never the compound shapes
  (`par`/`cond`/`letin`/`unpack`) the non-`eq` `AEq` constructors relate. -/
theorem eq_of_isAns {a b : Exp {}} (h : AEq a b) (hans : a.IsAns) : a = b := by
  cases h with
  | eq h => exact h
  | par _ _ _ _ => cases hans with | is_val hv => cases hv
  | cond _ _ => cases hans with | is_val hv => cases hv
  | letin _ => cases hans with | is_val hv => cases hv
  | unpack _ => cases hans with | is_val hv => cases hv

end Exp.AEq

/-! ### PART 4 — `AEq` is a `Step`-bisimulation

  Annotations affect `Step` only through the reachability-based `par` guards, so `AEq`-related
  configurations make the SAME move to the SAME memory, up to `AEq` of the reducts. -/

/-- **`AEq` is a `Step`-bisimulation.**  If `e1 ≈ e2` (annotation-equivalent) and `e1` steps, then
  `e2` makes the SAME step (same trace, same memory) to an annotation-equivalent reduct.  The leaf
  cases force syntactic equality (off `par`); the `par` cases transfer the reachability guards via
  PART 1 and the grown-annotation `RReq` via PART 2. -/
theorem Step.aeq_sim {t : Trace} {m m' : Memory} {e1 e1' e2 : Exp {}}
    (hae : Exp.AEq e1 e2) (hstep : Step t m e1 m' e1') :
    ∃ e2', Step t m e2 m' e2' ∧ Exp.AEq e1' e2' := by
  induction hstep generalizing e2 with
  | step_apply hlk => cases hae with | eq h => exact ⟨_, h ▸ Step.step_apply hlk, Exp.AEq.refl _⟩
  | step_invoke h1 h2 =>
    cases hae with | eq h => exact ⟨_, h ▸ Step.step_invoke h1 h2, Exp.AEq.refl _⟩
  | step_tapply hlk => cases hae with | eq h => exact ⟨_, h ▸ Step.step_tapply hlk, Exp.AEq.refl _⟩
  | step_capply hlk => cases hae with | eq h => exact ⟨_, h ▸ Step.step_capply hlk, Exp.AEq.refl _⟩
  | step_unwrap hlk => cases hae with | eq h => exact ⟨_, h ▸ Step.step_unwrap hlk, Exp.AEq.refl _⟩
  | step_cond_var_true hlk =>
    cases hae with
    | eq h => exact ⟨_, h ▸ Step.step_cond_var_true hlk, Exp.AEq.refl _⟩
    | cond hae2 _ => exact ⟨_, Step.step_cond_var_true hlk, hae2⟩
  | step_cond_var_false hlk =>
    cases hae with
    | eq h => exact ⟨_, h ▸ Step.step_cond_var_false hlk, Exp.AEq.refl _⟩
    | cond _ hae3 => exact ⟨_, Step.step_cond_var_false hlk, hae3⟩
  | step_read h1 h2 =>
    cases hae with | eq h => exact ⟨_, h ▸ Step.step_read h1 h2, Exp.AEq.refl _⟩
  | step_write h1 h2 =>
    cases hae with | eq h => exact ⟨_, h ▸ Step.step_write h1 h2, Exp.AEq.refl _⟩
  | step_alloc h1 h2 =>
    cases hae with | eq h => exact ⟨_, h ▸ Step.step_alloc h1 h2, Exp.AEq.refl _⟩
  | step_drop hx => cases hae with | eq h => exact ⟨_, h ▸ Step.step_drop hx, Exp.AEq.refl _⟩
  | step_rename =>
    cases hae with
    | eq h => exact ⟨_, h ▸ Step.step_rename, Exp.AEq.refl _⟩
    | letin hh =>
      cases Exp.AEq.eq_of_isAns hh Exp.IsAns.is_var
      exact ⟨_, Step.step_rename, Exp.AEq.refl _⟩
  | step_unpack =>
    cases hae with
    | eq h => exact ⟨_, h ▸ Step.step_unpack, Exp.AEq.refl _⟩
    | unpack hh =>
      cases Exp.AEq.eq_of_isAns hh (Exp.IsAns.is_val Exp.IsVal.pack)
      exact ⟨_, Step.step_unpack, Exp.AEq.refl _⟩
  | step_lift hv hwf hfresh =>
    cases hae with
    | eq h => exact ⟨_, h ▸ Step.step_lift hv hwf hfresh, Exp.AEq.refl _⟩
    | letin hh =>
      cases Exp.AEq.eq_of_isAns hh (Exp.IsAns.is_val (Exp.isVal_of_isSimpleVal hv))
      exact ⟨_, Step.step_lift hv hwf hfresh, Exp.AEq.refl _⟩
  | step_ctx_letin inner ih =>
    cases hae with
    | eq h => exact ⟨_, h ▸ Step.step_ctx_letin inner, Exp.AEq.refl _⟩
    | letin hh =>
      obtain ⟨eh', stepb, haeh⟩ := ih hh
      exact ⟨_, Step.step_ctx_letin stepb, Exp.AEq.letin haeh⟩
  | step_ctx_unpack inner ih =>
    cases hae with
    | eq h => exact ⟨_, h ▸ Step.step_ctx_unpack inner, Exp.AEq.refl _⟩
    | unpack hh =>
      obtain ⟨eh', stepb, haeh⟩ := ih hh
      exact ⟨_, Step.step_ctx_unpack stepb, Exp.AEq.unpack haeh⟩
  | step_par_left inner ht hni ih =>
    cases hae with
    | eq h => exact ⟨_, h ▸ Step.step_par_left inner ht hni, Exp.AEq.refl _⟩
    | par hC1 hC2 hea heb =>
      obtain ⟨ea', stepb, haea⟩ := ih hea
      refine ⟨_, Step.step_par_left stepb (ht.hmEq (hC1 _))
        ((hni.hmEq_left (hC1 _)).hmEq_right (hC2 _)),
        Exp.AEq.par (CaptureSet.growByAllocs_RReq_congr hC1 _) hC2 haea heb⟩
  | step_par_right ht hni inner ih =>
    cases hae with
    | eq h => exact ⟨_, h ▸ Step.step_par_right ht hni inner, Exp.AEq.refl _⟩
    | par hC1 hC2 hea heb =>
      obtain ⟨eb', stepb, haeb⟩ := ih heb
      refine ⟨_, Step.step_par_right (ht.hmEq (hC2 _))
        ((hni.hmEq_left (hC1 _)).hmEq_right (hC2 _)) stepb,
        Exp.AEq.par hC1 (CaptureSet.growByAllocs_RReq_congr hC2 _) hea haeb⟩
  | step_par_join h1 h2 =>
    cases hae with
    | eq h => exact ⟨_, h ▸ Step.step_par_join h1 h2, Exp.AEq.refl _⟩
    | par _ _ hea heb =>
      cases Exp.AEq.eq_of_isAns hea h1
      cases Exp.AEq.eq_of_isAns heb h2
      exact ⟨_, Step.step_par_join h1 h2, Exp.AEq.refl _⟩

/-- **`AEq` is a `Reduce`-bisimulation.**  An `AEq`-related configuration replays an entire run with
  the SAME trace and SAME final memory, up to `AEq` of the final reducts.  (Memory is identical at
  every step, so this transports continuations across `AEq` without touching the memory side.) -/
theorem Reduce.aeq_sim {t : Trace} {m m' : Memory} {e1 e1' e2 : Exp {}}
    (hae : Exp.AEq e1 e2) (hred : Reduce t m e1 m' e1') :
    ∃ e2', Reduce t m e2 m' e2' ∧ Exp.AEq e1' e2' := by
  induction hred generalizing e2 with
  | refl => exact ⟨e2, Reduce.refl, hae⟩
  | step hstep _ ih =>
    obtain ⟨emid, stepb, haemid⟩ := Step.aeq_sim hae hstep
    obtain ⟨e2', restb, hae'⟩ := ih haemid
    exact ⟨e2', Reduce.step stepb restb, hae'⟩

/-! ### Trace renaming helpers

  The external access/drop sequence `Trace.extSeq` and the allocation predicate
  `Trace.allocd` interact cleanly with location renaming: renaming the trace by `π`
  is the same as querying the original trace at `π.symm`-shifted locations.  From this,
  `Trace.Equiv` is a congruence for `renameLoc`. -/

/-- The renaming condition shared by the `access`/`dealloc` cases below. -/
private theorem renameLoc_cond {l l' : Nat} {A : List Nat} {π : Equiv.Perm Nat} :
    (l = π l' ∧ l ∉ A) ↔ (π.symm l = l' ∧ π.symm l ∉ A.map π.symm) := by
  apply and_congr
  · exact ⟨fun h => by rw [h, Equiv.symm_apply_apply], fun h => by rw [← h, Equiv.apply_symm_apply]⟩
  · rw [not_iff_not]
    constructor
    · intro hmem; exact List.mem_map.mpr ⟨l, hmem, rfl⟩
    · intro hmem
      obtain ⟨a, ha, hae⟩ := List.mem_map.mp hmem
      exact (π.symm.injective hae) ▸ ha

/-- `extSeqFrom` commutes with renaming: querying the `π`-renamed trace at `l` (with exempt
  set `A`) equals querying the original at `π.symm l` (with exempt set `A.map π.symm`). -/
theorem Trace.extSeqFrom_renameLoc {A : List Nat} {l : Nat} {t : Trace} {π : Equiv.Perm Nat} :
    Trace.extSeqFrom A l (t.renameLoc π)
      = Trace.extSeqFrom (A.map π.symm) (π.symm l) t := by
  simp only [Trace.renameLoc]
  induction t generalizing A with
  | nil => rfl
  | cons it t ih =>
    cases it with
    | alloc l' =>
      simp only [List.map_cons, TraceItem.renameLoc, Trace.extSeqFrom]
      rw [ih (A := π l' :: A), List.map_cons, Equiv.symm_apply_apply]
    | access mu l' =>
      simp only [List.map_cons, TraceItem.renameLoc, Trace.extSeqFrom]
      rw [ih (A := A)]
      by_cases hc : l = π l' ∧ l ∉ A
      · rw [if_pos hc, if_pos (renameLoc_cond.mp hc)]
      · rw [if_neg hc, if_neg (fun h => hc (renameLoc_cond.mpr h))]
    | dealloc l' =>
      simp only [List.map_cons, TraceItem.renameLoc, Trace.extSeqFrom]
      rw [ih (A := A)]
      by_cases hc : l = π l' ∧ l ∉ A
      · rw [if_pos hc, if_pos (renameLoc_cond.mp hc)]
      · rw [if_neg hc, if_neg (fun h => hc (renameLoc_cond.mpr h))]

/-- `extSeq` commutes with renaming. -/
theorem Trace.extSeq_renameLoc {l : Nat} {t : Trace} {π : Equiv.Perm Nat} :
    Trace.extSeq l (t.renameLoc π) = Trace.extSeq (π.symm l) t := by
  simp only [Trace.extSeq, Trace.extSeqFrom_renameLoc, List.map_nil]

/-- `Trace.Equiv` is a congruence for renaming. -/
theorem Trace.Equiv.renameLoc {t1 t2 : Trace} (h : Trace.Equiv t1 t2) (π : Equiv.Perm Nat) :
    Trace.Equiv (t1.renameLoc π) (t2.renameLoc π) := by
  intro l
  rw [Trace.extSeq_renameLoc, Trace.extSeq_renameLoc]
  exact h (π.symm l)

/-- Allocation is shifted by renaming: the `π`-renamed trace allocates `l` iff the original
  allocates `π.symm l`. -/
theorem Trace.allocd_renameLoc {t : Trace} {l : Nat} {π : Equiv.Perm Nat} :
    Trace.allocd (t.renameLoc π) l ↔ Trace.allocd t (π.symm l) := by
  simp only [Trace.renameLoc]
  induction t with
  | nil => exact Iff.rfl
  | cons it t ih =>
    cases it with
    | alloc l' =>
      simp only [List.map_cons, TraceItem.renameLoc, Trace.allocd]
      rw [ih]
      exact or_congr_left ⟨fun h => by rw [h, Equiv.symm_apply_apply],
        fun h => by rw [← h, Equiv.apply_symm_apply]⟩
    | access mu l' =>
      simp only [List.map_cons, TraceItem.renameLoc, Trace.allocd]; exact ih
    | dealloc l' =>
      simp only [List.map_cons, TraceItem.renameLoc, Trace.allocd]; exact ih

/-- `extTouchesMode` commutes with renaming: the `π`-renamed trace externally touches `l` (mode
  `cm`) iff the original touches `π.symm l`. -/
theorem Trace.extTouchesMode_renameLoc {t : Trace} {l : Nat} {cm : CapMode} {π : Equiv.Perm Nat} :
    Trace.extTouchesMode (t.renameLoc π) l cm ↔ Trace.extTouchesMode t (π.symm l) cm := by
  constructor
  · intro h
    have hmem : cm ∈ Trace.extSeq l (t.renameLoc π) := Trace.mem_extSeqFrom_iff.mpr h
    rw [Trace.extSeq_renameLoc] at hmem
    exact Trace.mem_extSeqFrom_iff.mp hmem
  · intro h
    have hmem : cm ∈ Trace.extSeq (π.symm l) t := Trace.mem_extSeqFrom_iff.mpr h
    rw [← Trace.extSeq_renameLoc] at hmem
    exact Trace.mem_extSeqFrom_iff.mp hmem

/-- A trace whose every location is fixed by `π` is unchanged by renaming. -/
theorem Trace.renameLoc_eq_self {t : Trace} {π : Equiv.Perm Nat}
    (h : ∀ it ∈ t, TraceItem.renameLoc π it = it) : t.renameLoc π = t := by
  induction t with
  | nil => rfl
  | cons it t ih =>
    have ht := ih (fun a ha => h a (List.mem_cons_of_mem it ha))
    change TraceItem.renameLoc π it :: Trace.renameLoc π t = it :: t
    rw [h it (by simp), ht]

/-- A membership `.alloc l ∈ t` witnesses that `t` allocates `l`. -/
theorem Trace.allocd_of_mem {t : Trace} {l : Nat} (h : TraceItem.alloc l ∈ t) :
    Trace.allocd t l := by
  induction t with
  | nil => cases h
  | cons it t ih =>
    rcases List.mem_cons.mp h with heq | hmem
    · subst heq; exact Or.inl rfl
    · cases it with
      | alloc _ => exact Or.inr (ih hmem)
      | access _ _ => exact ih hmem
      | dealloc _ => exact ih hmem

/-- A membership `.access mu l ∈ t` witnesses that `t` touches `l`. -/
theorem Trace.touched_of_mem_access {t : Trace} {l : Nat} {mu : Mutability}
    (h : TraceItem.access mu l ∈ t) : Trace.touched t l := by
  induction t with
  | nil => cases h
  | cons it t ih =>
    rcases List.mem_cons.mp h with heq | hmem
    · subst heq; exact Or.inl rfl
    · cases it with
      | alloc _ => exact ih hmem
      | access _ _ => exact Or.inr (ih hmem)
      | dealloc _ => exact Or.inr (ih hmem)

/-- A membership `.dealloc l ∈ t` witnesses that `t` touches `l`. -/
theorem Trace.touched_of_mem_dealloc {t : Trace} {l : Nat}
    (h : TraceItem.dealloc l ∈ t) : Trace.touched t l := by
  induction t with
  | nil => cases h
  | cons it t ih =>
    rcases List.mem_cons.mp h with heq | hmem
    · subst heq; exact Or.inl rfl
    · cases it with
      | alloc _ => exact ih hmem
      | access _ _ => exact Or.inr (ih hmem)
      | dealloc _ => exact Or.inr (ih hmem)

/-- A single `Step`'s trace mentions only locations present in the post-step memory, so a
  permutation fixing that memory's domain leaves the trace unchanged.  (Allocations land in
  `m'`; accesses/drops are of cells present in `m`, hence in `m'` by monotonicity.) -/
theorem Step.trace_renameLoc_eq {t : Trace} {m m' : Memory} {e e' : Exp {}} {π : Equiv.Perm Nat}
    (hstep : Step t m e m' e') (hfix : ∀ l, m'.heap l ≠ none → π l = l) :
    Trace.renameLoc π t = t := by
  apply Trace.renameLoc_eq_self
  intro it hit
  cases it with
  | alloc l =>
    simp only [TraceItem.renameLoc]
    rw [hfix l (Step.allocd_present hstep (Trace.allocd_of_mem hit))]
  | access mu l =>
    simp only [TraceItem.renameLoc]
    refine congrArg _ (hfix l (fun hm' => ?_))
    exact step_touched_present hstep (Trace.touched_of_mem_access hit)
      (Heap.none_of_subsumes_none (Step.subsumes hstep) hm')
  | dealloc l =>
    simp only [TraceItem.renameLoc]
    refine congrArg _ (hfix l (fun hm' => ?_))
    exact step_touched_present hstep (Trace.touched_of_mem_dealloc hit)
      (Heap.none_of_subsumes_none (Step.subsumes hstep) hm')

/-! ### Renaming cancellation helpers -/

theorem Memory.renameLoc_symm_self {m : Memory} {π : Equiv.Perm Nat} :
    (m.renameLoc π.symm).renameLoc π = m := by
  rw [Memory.renameLoc_comp, Equiv.symm_trans_self, Memory.renameLoc_id]

theorem Memory.renameLoc_self_symm {m : Memory} {π : Equiv.Perm Nat} :
    (m.renameLoc π).renameLoc π.symm = m := by
  rw [Memory.renameLoc_comp, Equiv.self_trans_symm, Memory.renameLoc_id]

theorem Exp.renameLoc_symm_self {e : Exp s} {π : Equiv.Perm Nat} :
    (e.renameLoc π.symm).renameLoc π = e := by
  rw [Exp.renameLoc_comp, Equiv.symm_trans_self, Exp.renameLoc_id]

theorem Exp.renameLoc_self_symm {e : Exp s} {π : Equiv.Perm Nat} :
    (e.renameLoc π).renameLoc π.symm = e := by
  rw [Exp.renameLoc_comp, Equiv.self_trans_symm, Exp.renameLoc_id]

theorem Trace.renameLoc_comp {t : Trace} {π ρ : Equiv.Perm Nat} :
    (t.renameLoc π).renameLoc ρ = t.renameLoc (π.trans ρ) := by
  simp only [Trace.renameLoc, List.map_map]
  apply List.map_congr_left
  intro it _
  cases it <;> simp [TraceItem.renameLoc, Function.comp, Equiv.trans_apply]

theorem Trace.renameLoc_symm_self {t : Trace} {π : Equiv.Perm Nat} :
    (t.renameLoc π.symm).renameLoc π = t := by
  rw [Trace.renameLoc_comp, Equiv.symm_trans_self, Trace.renameLoc_id]

theorem Trace.renameLoc_self_symm {t : Trace} {π : Equiv.Perm Nat} :
    (t.renameLoc π).renameLoc π.symm = t := by
  rw [Trace.renameLoc_comp, Equiv.self_trans_symm, Trace.renameLoc_id]

/-! ### Allocation-footprint congruences

  The allocation predicate `Trace.allocd` is unaffected by appended/renamed structure in the
  same way `Trace.Equiv` is, but — being a pure membership predicate — its append congruences
  carry no side conditions. -/

theorem Trace.allocd_cong_left {t s s' : Trace} (h : ∀ l, Trace.allocd s l ↔ Trace.allocd s' l) :
    ∀ l, Trace.allocd (t ++ s) l ↔ Trace.allocd (t ++ s') l := fun l => by
  rw [Trace.allocd_append, Trace.allocd_append]; exact or_congr_right (h l)

theorem Trace.allocd_cong_right {t t' s : Trace} (h : ∀ l, Trace.allocd t l ↔ Trace.allocd t' l) :
    ∀ l, Trace.allocd (t ++ s) l ↔ Trace.allocd (t' ++ s) l := fun l => by
  rw [Trace.allocd_append, Trace.allocd_append]; exact or_congr_left (h l)

theorem Trace.allocd_cong_renameLoc {t1 t2 : Trace}
    (h : ∀ l, Trace.allocd t1 l ↔ Trace.allocd t2 l) (ρ : Equiv.Perm Nat) :
    ∀ l, Trace.allocd (t1.renameLoc ρ) l ↔ Trace.allocd (t2.renameLoc ρ) l := fun l => by
  rw [Trace.allocd_renameLoc, Trace.allocd_renameLoc]; exact h (ρ.symm l)

theorem Trace.allocd_cong_trans {t1 t2 t3 : Trace}
    (h1 : ∀ l, Trace.allocd t1 l ↔ Trace.allocd t2 l)
    (h2 : ∀ l, Trace.allocd t2 l ↔ Trace.allocd t3 l) :
    ∀ l, Trace.allocd t1 l ↔ Trace.allocd t3 l := fun l => (h1 l).trans (h2 l)

/-! ### Reconvergence predicate and the local diamond

  `Recon D t1 m1 e1 t2 m2 e2` packages the confluence conclusion for two configs descending
  from a common ancestor whose domain is the protected set `D`.  It records continuations to a
  common reduct (up to a permutation `π` that fixes `D`), the `Trace.Equiv` of the combined
  histories (after renaming path 1 by `π`), and the matching allocation footprint (the side
  condition needed to extend `Trace.Equiv` by a shared suffix). -/

/-- Zero-or-one `Step`: the closing legs of the local diamond. -/
inductive RStep : Trace → Memory → Exp {} → Memory → Exp {} → Prop where
  | refl {m e} : RStep [] m e m e
  | step {t m e m' e'} : Step t m e m' e' → RStep t m e m' e'

theorem RStep.toReduce {t : Trace} {m m' : Memory} {e e' : Exp {}}
    (h : RStep t m e m' e') : Reduce t m e m' e' := by
  cases h with
  | refl => exact Reduce.refl
  | step hs => exact (List.append_nil t) ▸ Reduce.step hs Reduce.refl

theorem RStep.ctx_letin {t : Trace} {m m' : Memory} {e1 e1' : Exp {}} {e2 : Exp ({},x)}
    (h : RStep t m e1 m' e1') : RStep t m (.letin e1 e2) m' (.letin e1' e2) := by
  cases h with
  | refl => exact RStep.refl
  | step hs => exact RStep.step (Step.step_ctx_letin hs)

theorem RStep.ctx_unpack {t : Trace} {m m' : Memory} {e1 e1' : Exp {}} {e2 : Exp ({},C,x)}
    (h : RStep t m e1 m' e1') : RStep t m (.unpack e1 e2) m' (.unpack e1' e2) := by
  cases h with
  | refl => exact RStep.refl
  | step hs => exact RStep.step (Step.step_ctx_unpack hs)

/-- Reconvergence of two configs sharing an ancestor (protected domain `D`). -/
def Recon (D : Nat → Prop) (t1 : Trace) (m1 : Memory) (e1 : Exp {})
    (t2 : Trace) (m2 : Memory) (e2 : Exp {}) : Prop :=
  ∃ (s1 s2 : Trace) (mf1 mf2 : Memory) (ef1 ef2 : Exp {}) (π : Equiv.Perm Nat),
    Reduce s1 m1 e1 mf1 ef1 ∧ Reduce s2 m2 e2 mf2 ef2 ∧
    mf2 = mf1.renameLoc π ∧ Exp.AEq ef2 (ef1.renameLoc π) ∧
    (∀ l, D l → π l = l) ∧
    Trace.Equiv ((t1 ++ s1).renameLoc π) (t2 ++ s2) ∧
    (∀ l, Trace.allocd ((t1 ++ s1).renameLoc π) l ↔ Trace.allocd (t2 ++ s2) l)

/-- Two lookups of the same location agree. -/
theorem lookup_cell_eq {x : Nat} {m : Memory} {c1 c2 : Cell}
    (h1 : m.lookup x = some c1) (h2 : m.lookup x = some c2) : c1 = c2 := by
  rw [h1] at h2; exact Option.some.inj h2

/-- Two value-cell lookups of the same location agree on the stored expression. -/
theorem lookup_val_unwrap_eq {x : Nat} {m : Memory} {v1 v2 : HeapVal}
    (h1 : m.lookup x = some (.val v1)) (h2 : m.lookup x = some (.val v2)) :
    v1.unwrap = v2.unwrap := by
  have hc := lookup_cell_eq h1 h2
  injection hc with hv; exact congrArg HeapVal.unwrap hv

/-! ### Well-formed terms are fixed by a domain-fixing permutation

  A permutation `π` that fixes every allocated location leaves any term well-formed in that
  heap unchanged (its free locations are all allocated).  This is what lets the congruence
  cases of `local_diamond` reuse the inner diamond's permutation on the untouched
  continuation. -/

theorem Var.renameLoc_eq_of_wf {k s} {x : Var k s} {h : Heap} (hwf : x.WfInHeap h)
    {π : Equiv.Perm Nat} (hfix : ∀ l, h l ≠ none → π l = l) : x.renameLoc π = x := by
  cases hwf with
  | wf_bound => rfl
  | wf_free hn => simp only [Var.renameLoc]; rw [hfix _ (by rw [hn]; simp)]

theorem CaptureSet.renameLoc_eq_of_wf {s} {cs : CaptureSet s} {h : Heap} (hwf : cs.WfInHeap h)
    {π : Equiv.Perm Nat} (hfix : ∀ l, h l ≠ none → π l = l) : cs.renameLoc π = cs := by
  induction hwf with
  | wf_empty => rfl
  | wf_union _ _ ih1 ih2 => simp only [CaptureSet.renameLoc, ih1 hfix, ih2 hfix]; rfl
  | wf_var_free hx =>
    simp only [CaptureSet.renameLoc, Var.renameLoc]; rw [hfix _ (by rw [hx]; simp)]
  | wf_var_bound => rfl
  | wf_cvar => rfl

theorem CaptureBound.renameLoc_eq_of_wf {s} {cb : CaptureBound s} {h : Heap}
    (hwf : cb.WfInHeap h) {π : Equiv.Perm Nat} (hfix : ∀ l, h l ≠ none → π l = l) :
    cb.renameLoc π = cb := by
  cases hwf with
  | wf_unbound => rfl
  | wf_bound hcs => simp only [CaptureBound.renameLoc, CaptureSet.renameLoc_eq_of_wf hcs hfix]

theorem SepCtx.renameLoc_eq_of_wf {s} {K : SepCtx s} {h : Heap} (hwf : K.WfInHeap h)
    {π : Equiv.Perm Nat} (hfix : ∀ l, h l ≠ none → π l = l) : K.renameLoc π = K := by
  induction hwf with
  | wf_empty => rfl
  | wf_cons _ hC ih => simp only [SepCtx.renameLoc, ih hfix, CaptureSet.renameLoc_eq_of_wf hC hfix]

theorem MutabilityCtx.renameLoc_eq_of_wf {s} {K : MutabilityCtx s} {h : Heap} (hwf : K.WfInHeap h)
    {π : Equiv.Perm Nat} (hfix : ∀ l, h l ≠ none → π l = l) : K.renameLoc π = K := by
  induction hwf with
  | wf_empty => rfl
  | wf_cons _ hC ih =>
    simp only [MutabilityCtx.renameLoc, ih hfix, CaptureSet.renameLoc_eq_of_wf hC hfix]

theorem ModalCtx.renameLoc_eq_of_wf {s} {K : ModalCtx s} {h : Heap} (hwf : K.WfInHeap h)
    {π : Equiv.Perm Nat} (hfix : ∀ l, h l ≠ none → π l = l) : K.renameLoc π = K := by
  cases K with
  | mk sep mu =>
    simp only [ModalCtx.renameLoc,
      SepCtx.renameLoc_eq_of_wf hwf.sep hfix, MutabilityCtx.renameLoc_eq_of_wf hwf.mutability hfix]

theorem Ty.renameLoc_eq_of_wf {sort s} {T : Ty sort s} {h : Heap} (hwf : T.WfInHeap h)
    {π : Equiv.Perm Nat} (hfix : ∀ l, h l ≠ none → π l = l) : T.renameLoc π = T := by
  induction hwf with
  | wf_top => rfl
  | wf_tvar => rfl
  | wf_arrow _ hcs _ ih1 ih2 =>
    simp only [Ty.renameLoc, ih1 hfix, CaptureSet.renameLoc_eq_of_wf hcs hfix, ih2 hfix]
  | wf_poly _ hcs _ ih1 ih2 =>
    simp only [Ty.renameLoc, ih1 hfix, CaptureSet.renameLoc_eq_of_wf hcs hfix, ih2 hfix]
  | wf_cpoly hcb hcs _ ih =>
    simp only [Ty.renameLoc, CaptureBound.renameLoc_eq_of_wf hcb hfix,
      CaptureSet.renameLoc_eq_of_wf hcs hfix, ih hfix]
  | wf_modal hcs hΨ _ ih =>
    simp only [Ty.renameLoc, CaptureSet.renameLoc_eq_of_wf hcs hfix,
      ModalCtx.renameLoc_eq_of_wf hΨ hfix, ih hfix]
  | wf_unit => rfl
  | wf_cap hcs => simp only [Ty.renameLoc, CaptureSet.renameLoc_eq_of_wf hcs hfix]
  | wf_bool => rfl
  | wf_cell hcs _ ih => simp only [Ty.renameLoc, CaptureSet.renameLoc_eq_of_wf hcs hfix, ih hfix]
  | wf_reader hcs _ ih =>
    simp only [Ty.renameLoc, CaptureSet.renameLoc_eq_of_wf hcs hfix, ih hfix]
  | wf_exi _ ih => simp only [Ty.renameLoc, ih hfix]
  | wf_typ _ ih => simp only [Ty.renameLoc, ih hfix]

theorem PureTy.renameLoc_eq_of_wf {s} {T : PureTy s} {h : Heap} (hwf : T.WfInHeap h)
    {π : Equiv.Perm Nat} (hfix : ∀ l, h l ≠ none → π l = l) : T.renameLoc π = T :=
  PureTy.eq_of_core (Ty.renameLoc_eq_of_wf hwf hfix)

theorem Exp.renameLoc_eq_of_wf {s} {e : Exp s} {h : Heap} (hwf : e.WfInHeap h)
    {π : Equiv.Perm Nat} (hfix : ∀ l, h l ≠ none → π l = l) : e.renameLoc π = e := by
  induction hwf with
  | wf_var hx => simp only [Exp.renameLoc, Var.renameLoc_eq_of_wf hx hfix]
  | wf_abs hcs hT _ ih =>
    simp only [Exp.renameLoc, CaptureSet.renameLoc_eq_of_wf hcs hfix,
      Ty.renameLoc_eq_of_wf hT hfix, ih hfix]
  | wf_tabs hcs hT _ ih =>
    simp only [Exp.renameLoc, CaptureSet.renameLoc_eq_of_wf hcs hfix,
      PureTy.renameLoc_eq_of_wf hT hfix, ih hfix]
  | wf_cabs hcs hcb _ ih =>
    simp only [Exp.renameLoc, CaptureSet.renameLoc_eq_of_wf hcs hfix,
      CaptureBound.renameLoc_eq_of_wf hcb hfix, ih hfix]
  | wf_boxed hcs hΨ _ ih =>
    simp only [Exp.renameLoc, CaptureSet.renameLoc_eq_of_wf hcs hfix,
      ModalCtx.renameLoc_eq_of_wf hΨ hfix, ih hfix]
  | wf_reader hx => simp only [Exp.renameLoc, Var.renameLoc_eq_of_wf hx hfix]
  | wf_alloc hx => simp only [Exp.renameLoc, Var.renameLoc_eq_of_wf hx hfix]
  | wf_drop hx => simp only [Exp.renameLoc, Var.renameLoc_eq_of_wf hx hfix]
  | wf_pack hcs hx =>
    simp only [Exp.renameLoc, CaptureSet.renameLoc_eq_of_wf hcs hfix,
      Var.renameLoc_eq_of_wf hx hfix]
  | wf_app hx hy =>
    simp only [Exp.renameLoc, Var.renameLoc_eq_of_wf hx hfix, Var.renameLoc_eq_of_wf hy hfix]
  | wf_tapp hx hT =>
    simp only [Exp.renameLoc, Var.renameLoc_eq_of_wf hx hfix, PureTy.renameLoc_eq_of_wf hT hfix]
  | wf_capp hx hcs =>
    simp only [Exp.renameLoc, Var.renameLoc_eq_of_wf hx hfix,
      CaptureSet.renameLoc_eq_of_wf hcs hfix]
  | wf_unwrap hx => simp only [Exp.renameLoc, Var.renameLoc_eq_of_wf hx hfix]
  | wf_letin _ _ ih1 ih2 => simp only [Exp.renameLoc, ih1 hfix, ih2 hfix]
  | wf_unpack _ _ ih1 ih2 => simp only [Exp.renameLoc, ih1 hfix, ih2 hfix]
  | wf_unit => rfl
  | wf_btrue => rfl
  | wf_bfalse => rfl
  | wf_read hx => simp only [Exp.renameLoc, Var.renameLoc_eq_of_wf hx hfix]
  | wf_write hx hy =>
    simp only [Exp.renameLoc, Var.renameLoc_eq_of_wf hx hfix, Var.renameLoc_eq_of_wf hy hfix]
  | wf_cond hx _ _ ih2 ih3 =>
    simp only [Exp.renameLoc, Var.renameLoc_eq_of_wf hx hfix, ih2 hfix, ih3 hfix]
  | wf_par hC1 hC2 _ _ ih1 ih2 =>
    simp only [Exp.renameLoc, CaptureSet.renameLoc_eq_of_wf hC1 hfix,
      CaptureSet.renameLoc_eq_of_wf hC2 hfix, ih1 hfix, ih2 hfix]

/-! ### Heap renaming identity for a swap of fresh locations

  A swap of two unallocated locations leaves a well-formed heap unchanged: every stored cell's
  free locations and reachability are within the (swap-fixed) domain.  This is what lets the
  `alloc`/`lift` cases close their fresh-name divergence with `π = Equiv.swap`. -/

/-- A runtime capability set whose members are all fixed by `π` is unchanged by renaming. -/
theorem CapabilitySet.renameLoc_eq_of_fix {R : CapabilitySet} {π : Equiv.Perm Nat}
    (hfix : ∀ mu l', R.hasmem mu l' → π l' = l') : R.renameLoc π = R := by
  induction R with
  | empty => rfl
  | cap m l => simp only [CapabilitySet.renameLoc]; rw [hfix m l CapabilitySet.hasmem.here]
  | union a b ih1 ih2 =>
    simp only [CapabilitySet.renameLoc,
      ih1 (fun mu l' h => hfix mu l' (CapabilitySet.hasmem.left h)),
      ih2 (fun mu l' h => hfix mu l' (CapabilitySet.hasmem.right h))]

/-- A heap value, well-formed with reachability inside the heap, is fixed by a domain-fixing
  permutation. -/
theorem HeapVal.renameLoc_eq_of_wf {hv : HeapVal} {h : Heap}
    (hwfv : Exp.WfInHeap hv.unwrap h)
    (hreach : ∀ mu l', hv.reachability.hasmem mu l' → h l' ≠ none)
    {π : Equiv.Perm Nat} (hfix : ∀ l, h l ≠ none → π l = l) : hv.renameLoc π = hv :=
  HeapVal.eq_of (Exp.renameLoc_eq_of_wf hwfv hfix)
    (CapabilitySet.renameLoc_eq_of_fix (fun mu l' hm => hfix l' (hreach mu l' hm)))

/-- A capability whose stored (live) location is fixed by `π` is itself fixed. -/
theorem CapabilityInfo.renameLoc_eq_of_live_fix {info : CapabilityInfo} {π : Equiv.Perm Nat}
    (hfix : ∀ n, info = .mcell n .live → π n = n) : info.renameLoc π = info := by
  cases info with
  | basic => rfl
  | mcell n ℓ =>
    cases ℓ with
    | live => simp only [CapabilityInfo.renameLoc, hfix n rfl]
    | dead => rfl

/-- A swap of two fresh locations leaves a well-formed heap unchanged.  The content
    closure (live mcells point at present value locations) is supplied as `hmcell`, so the
    swap — which fixes every present location — also fixes mcell content pointers. -/
theorem Heap.renameLoc_eq_of_fresh {h : Heap} (hwf : h.WfHeap)
    (hmcell : ∀ l n, h l = some (.capability (.mcell n .live)) → h n ≠ none) {l1 l2 : Nat}
    (hf1 : h l1 = none) (hf2 : h l2 = none) :
    h.renameLoc (Equiv.swap l1 l2) = h := by
  have hA : ∀ k, h k ≠ none → Equiv.swap l1 l2 k = k := fun k hk =>
    Equiv.swap_apply_of_ne_of_ne (fun he => hk (by rw [he]; exact hf1))
      (fun he => hk (by rw [he]; exact hf2))
  funext l'
  change (h ((Equiv.swap l1 l2).symm l')).map (Cell.renameLoc (Equiv.swap l1 l2)) = h l'
  rw [Equiv.symm_swap]
  cases hc : h l' with
  | none =>
    have hn : h (Equiv.swap l1 l2 l') = none := by
      by_cases h1 : l' = l1
      · subst h1; rw [Equiv.swap_apply_left]; exact hf2
      · by_cases h2 : l' = l2
        · subst h2; rw [Equiv.swap_apply_right]; exact hf1
        · rwa [Equiv.swap_apply_of_ne_of_ne h1 h2]
    rw [hn]; rfl
  | some c =>
    have hcell : Cell.renameLoc (Equiv.swap l1 l2) c = c := by
      cases c with
      | val hv =>
        simp only [Cell.renameLoc]
        rw [HeapVal.renameLoc_eq_of_wf (hwf.wf_val l' hv hc)
          (fun mu k hm => hwf.wf_reach_dom l' hv.unwrap hv.isVal hv.reachability hc mu k hm) hA]
      | capability info =>
        simp only [Cell.renameLoc]
        rw [CapabilityInfo.renameLoc_eq_of_live_fix
          (fun n hn => hA n (hmcell l' n (by rw [hc, hn])))]
      | masked => rfl
    rw [hA l' (by rw [hc]; simp), hc]
    change some (Cell.renameLoc (Equiv.swap l1 l2) c) = some c
    rw [hcell]

/-- A swap of two fresh locations leaves a memory's heap unchanged (content closure
    supplied from the memory's `mcell_wf` invariant). -/
theorem Memory.heap_renameLoc_eq_of_fresh {m : Memory} {l1 l2 : Nat}
    (hf1 : m.heap l1 = none) (hf2 : m.heap l2 = none) :
    m.heap.renameLoc (Equiv.swap l1 l2) = m.heap :=
  Heap.renameLoc_eq_of_fresh m.wf (fun l n hl => m.mcell_wf l n hl) hf1 hf2

/-- A swap of two fresh locations leaves a memory unchanged. -/
theorem Memory.renameLoc_eq_of_fresh {m : Memory} {l1 l2 : Nat}
    (hf1 : m.heap l1 = none) (hf2 : m.heap l2 = none) :
    m.renameLoc (Equiv.swap l1 l2) = m :=
  Memory.eq_of_heap (Memory.heap_renameLoc_eq_of_fresh hf1 hf2)

/-- An answer is a normal form for the genuine step relation too. -/
theorem Step.not_isAns {t : Trace} {m m' : Memory} {a e' : Exp {}}
    (hstep : Step t m a m' e') (hans : a.IsAns) : False := by
  cases hans with
  | is_val hv => cases hv <;> cases hstep
  | is_var => cases hstep

/-! ### Reachability frame for genuine `Step`'s `par` guards

  Two memories agreeing off a single capability cell `c` (both holding *a* capability there)
  compute the same `CaptureSet.reachability` for any ground capture set: a capability's
  reachability is bit/liveness-independent (`reachability_of_loc_frame`).  This is what
  re-establishes the `TraceOk`/`Noninterference` guards on `Step.step_par_left`/`_right` when
  framing a step across the other branch's single-cell update. -/
theorem CaptureSet.reachability_frame {ma mb : Memory} {c : Nat} {ci1 ci2}
    (hc1 : ma.heap c = some (.capability ci1)) (hc2 : mb.heap c = some (.capability ci2))
    (hag : ∀ l, l ≠ c → ma.heap l = mb.heap l) (cs : CaptureSet {}) :
    cs.reachability ma = cs.reachability mb := by
  induction cs with
  | empty => rfl
  | union cs1 cs2 ih1 ih2 => simp only [CaptureSet.reachability, ih1, ih2]
  | var m' x =>
    cases x with
    | bound bx => cases bx
    | free loc =>
      simp only [CaptureSet.reachability]
      rw [reachability_of_loc_frame hc1 hc2 hag loc]
  | cvar m' c0 => cases c0

/-- Reachability frame for an absent cell: a capture set well-formed in `mb.heap` (so none of
  its free locations is the cell `c` absent in `mb`) computes the same `reachability` in any
  memory agreeing with `mb` off `c`.  The absent-cell companion of `reachability_frame`, used
  by `Step.frame_off_absent`'s `par` guards. -/
theorem CaptureSet.reachability_frame_wf {ma mb : Memory} {c : Nat}
    (hc2 : mb.heap c = none) (hag : ∀ l, l ≠ c → ma.heap l = mb.heap l) (cs : CaptureSet {})
    (hwf : CaptureSet.WfInHeap cs mb.heap) :
    cs.reachability ma = cs.reachability mb := by
  induction cs with
  | empty => rfl
  | union cs1 cs2 ih1 ih2 =>
    cases hwf with
    | wf_union hwf1 hwf2 => simp only [CaptureSet.reachability, ih1 hwf1, ih2 hwf2]
  | var m' x =>
    cases x with
    | bound bx => cases bx
    | free loc =>
      cases hwf with
      | wf_var_free hex =>
        have hlc : loc ≠ c := fun h => by rw [h, hc2] at hex; cases hex
        simp only [CaptureSet.reachability, reachability_of_loc, hag loc hlc]
  | cvar m' c0 => cases c0

/-- **Single-step exact frame (genuine `Step`).**  The genuine-`Step` analogue of
  `SeqStep.frame_off`: if `e` steps from `ma`, and `mb` agrees with `ma` off a capability cell
  `c` the step never touches, then `e` replays the SAME step from `mb`.  The leaf cases are
  verbatim from `SeqStep.frame_off`; the `par` congruences additionally re-establish the
  `TraceOk`/`Noninterference` guards via `CaptureSet.reachability_frame`. -/
theorem Step.frame_off {ma mb ma' : Memory} {e e' : Exp {}} {t : Trace} {c : Nat}
    (hstep : Step t ma e ma' e')
    (hc : ∃ ci, ma.lookup c = some (.capability ci))
    (hcb : ∃ ci, mb.lookup c = some (.capability ci))
    (hag : ∀ l, l ≠ c → ma.lookup l = mb.lookup l)
    (hnt : ¬ Trace.touched t c)
    (hwf : Exp.WfInHeap e mb.heap) :
    ∃ mb', Step t mb e mb' e' ∧ (∀ l, l ≠ c → ma'.lookup l = mb'.lookup l) ∧
      mb'.lookup c = mb.lookup c := by
  induction hstep generalizing mb with
  | step_apply hlk =>
    obtain ⟨ci, hci⟩ := hc
    exact ⟨mb, Step.step_apply ((hag _ (Memory.val_ne_cap hci hlk)) ▸ hlk), hag, rfl⟩
  | step_tapply hlk =>
    obtain ⟨ci, hci⟩ := hc
    exact ⟨mb, Step.step_tapply ((hag _ (Memory.val_ne_cap hci hlk)) ▸ hlk), hag, rfl⟩
  | step_capply hlk =>
    obtain ⟨ci, hci⟩ := hc
    exact ⟨mb, Step.step_capply ((hag _ (Memory.val_ne_cap hci hlk)) ▸ hlk), hag, rfl⟩
  | step_unwrap hlk =>
    obtain ⟨ci, hci⟩ := hc
    exact ⟨mb, Step.step_unwrap ((hag _ (Memory.val_ne_cap hci hlk)) ▸ hlk), hag, rfl⟩
  | step_cond_var_true hlk =>
    obtain ⟨ci, hci⟩ := hc
    exact ⟨mb, Step.step_cond_var_true ((hag _ (Memory.val_ne_cap hci hlk)) ▸ hlk), hag, rfl⟩
  | step_cond_var_false hlk =>
    obtain ⟨ci, hci⟩ := hc
    exact ⟨mb, Step.step_cond_var_false ((hag _ (Memory.val_ne_cap hci hlk)) ▸ hlk), hag, rfl⟩
  | step_invoke hlkx hlky =>
    obtain ⟨ci, hci⟩ := hc
    have hxc : _ ≠ c := fun h => hnt (Or.inl h.symm)
    exact ⟨mb, Step.step_invoke ((hag _ hxc) ▸ hlkx)
      ((hag _ (Memory.val_ne_cap hci hlky)) ▸ hlky), hag, rfl⟩
  | step_read hlkx hlky =>
    obtain ⟨ci, hci⟩ := hc
    have hyc : _ ≠ c := fun h => hnt (Or.inl h.symm)
    exact ⟨mb, Step.step_read ((hag _ (Memory.val_ne_cap hci hlkx)) ▸ hlkx)
      ((hag _ hyc) ▸ hlky), hag, rfl⟩
  | step_write hx hy =>
    obtain ⟨ci, hci⟩ := hc
    have hxc : _ ≠ c := fun h => hnt (Or.inl h.symm)
    have hyb : mb.heap _ ≠ none := match hwf with
      | .wf_write _ (.wf_free h) => Option.ne_none_iff_exists'.mpr ⟨_, h⟩
    refine ⟨mb.update_mcell _ _ .live ⟨_, (hag _ hxc) ▸ hx⟩ (fun _ => hyb),
      Step.step_write ((hag _ hxc) ▸ hx) hyb,
      Memory.update_mcell_lookup_agree hag, Memory.update_mcell_lookup_ne (Ne.symm hxc)⟩
  | step_drop hx =>
    obtain ⟨ci, hci⟩ := hc
    have hxc : _ ≠ c := fun h => hnt (Or.inl h.symm)
    refine ⟨mb.drop_mcell _ ⟨_, (hag _ hxc) ▸ hx⟩,
      Step.step_drop ((hag _ hxc) ▸ hx),
      Memory.drop_mcell_lookup_agree hag, Memory.drop_mcell_lookup_ne (Ne.symm hxc)⟩
  | step_alloc hlk hfresh =>
    obtain ⟨ci, hci⟩ := hc
    have hlc := Memory.fresh_ne_cap hfresh hci
    have hfreshb : mb.heap _ = none := (hag _ hlc).symm.trans hfresh
    have hxb : mb.heap _ ≠ none := match hwf with
      | .wf_alloc (.wf_free h) => Option.ne_none_iff_exists'.mpr ⟨_, h⟩
    refine ⟨mb.extend_mcell _ _ hfreshb hxb,
      Step.step_alloc hxb hfreshb,
      Memory.extend_mcell_lookup_agree hag, ?_⟩
    simp only [Memory.lookup, Memory.extend_mcell, Heap.extend_mcell, if_neg (Ne.symm hlc)]
  | step_rename =>
    exact ⟨mb, Step.step_rename, hag, rfl⟩
  | step_unpack =>
    exact ⟨mb, Step.step_unpack, hag, rfl⟩
  | step_par_join h1 h2 =>
    exact ⟨mb, Step.step_par_join h1 h2, hag, rfl⟩
  | step_lift hv hwf_v hfresh =>
    obtain ⟨ci, hci⟩ := hc
    obtain ⟨cib, hcib⟩ := hcb
    have hlc := Memory.fresh_ne_cap hfresh hci
    have hfreshb : mb.heap _ = none := (hag _ hlc).symm.trans hfresh
    have hwf_vb : _ := (Exp.wf_inv_letin hwf).1
    have hreach_eq : compute_reachability _ _ hv = compute_reachability mb.heap _ hv :=
      compute_reachability_frame hci hcib hag _ hv
    refine ⟨mb.extend _ ⟨_, hv, compute_reachability mb.heap _ hv⟩ hwf_vb rfl hfreshb,
      Step.step_lift hv hwf_vb hfreshb,
      Memory.extend_lookup_agree hag hreach_eq, ?_⟩
    simp only [Memory.lookup, Memory.extend, Heap.extend, if_neg (Ne.symm hlc)]
  | step_ctx_letin hinner ih =>
    obtain ⟨mb', stepb, agb, cpresb⟩ := ih hc hcb hag hnt (Exp.wf_inv_letin hwf).1
    exact ⟨mb', Step.step_ctx_letin stepb, agb, cpresb⟩
  | step_ctx_unpack hinner ih =>
    obtain ⟨mb', stepb, agb, cpresb⟩ := ih hc hcb hag hnt (Exp.wf_inv_unpack hwf).1
    exact ⟨mb', Step.step_ctx_unpack stepb, agb, cpresb⟩
  | step_par_left hinner ht hni ih =>
    rename_i _ mpar _ _ _ _ Cp1 Cp2
    obtain ⟨mb', stepb, agb, cpresb⟩ := ih hc hcb hag hnt (Exp.wf_inv_par hwf).1
    obtain ⟨ci, hci⟩ := hc; obtain ⟨cib, hcib⟩ := hcb
    have e1 : Cp1.reachability mpar = Cp1.reachability mb :=
      CaptureSet.reachability_frame hci hcib hag _
    have e2 : Cp2.reachability mpar = Cp2.reachability mb :=
      CaptureSet.reachability_frame hci hcib hag _
    exact ⟨mb', Step.step_par_left stepb (e1 ▸ ht) (e1 ▸ e2 ▸ hni), agb, cpresb⟩
  | step_par_right ht hni hinner ih =>
    rename_i _ mpar _ _ _ Cp1 Cp2 _
    obtain ⟨mb', stepb, agb, cpresb⟩ := ih hc hcb hag hnt (Exp.wf_inv_par hwf).2
    obtain ⟨ci, hci⟩ := hc; obtain ⟨cib, hcib⟩ := hcb
    have e1 : Cp1.reachability mpar = Cp1.reachability mb :=
      CaptureSet.reachability_frame hci hcib hag _
    have e2 : Cp2.reachability mpar = Cp2.reachability mb :=
      CaptureSet.reachability_frame hci hcib hag _
    exact ⟨mb', Step.step_par_right (e2 ▸ ht) (e1 ▸ e2 ▸ hni) stepb, agb, cpresb⟩

/-- **Single-step frame, absent variant (genuine `Step`).**  The genuine-`Step` analogue of
  `SeqStep.frame_off_absent`: if `e` (well-formed in `mb`) steps from `ma`, and `mb` agrees with
  `ma` off a cell `c` present in `ma` but absent in `mb`, then `e` replays from `mb`, results
  agree off `c`, `c` stays absent, and the step never touched `c`. -/
theorem Step.frame_off_absent {ma mb ma' : Memory} {e e' : Exp {}} {t : Trace} {c : Nat}
    (hstep : Step t ma e ma' e')
    (hc : ma.lookup c ≠ none)
    (hcb : mb.lookup c = none)
    (hag : ∀ l, l ≠ c → ma.lookup l = mb.lookup l)
    (hwf : Exp.WfInHeap e mb.heap) :
    ∃ mb', Step t mb e mb' e' ∧ (∀ l, l ≠ c → ma'.lookup l = mb'.lookup l) ∧
      mb'.lookup c = none ∧ ¬ Trace.touched t c := by
  induction hstep generalizing mb with
  | step_apply hlk =>
    match hwf with
    | .wf_app (.wf_free (n := xx) hx1) hwfy =>
      have hxc : xx ≠ c := fun h => by
        rw [h] at hx1; rw [show mb.heap c = none from hcb] at hx1; cases hx1
      exact ⟨mb, Step.step_apply ((hag xx hxc) ▸ hlk), hag, hcb, by simp [Trace.touched]⟩
  | step_tapply hlk =>
    match hwf with
    | .wf_tapp (.wf_free (n := xx) hx1) _ =>
      have hxc : xx ≠ c := fun h => by
        rw [h] at hx1; rw [show mb.heap c = none from hcb] at hx1; cases hx1
      exact ⟨mb, Step.step_tapply ((hag xx hxc) ▸ hlk), hag, hcb, by simp [Trace.touched]⟩
  | step_capply hlk =>
    match hwf with
    | .wf_capp (.wf_free (n := xx) hx1) _ =>
      have hxc : xx ≠ c := fun h => by
        rw [h] at hx1; rw [show mb.heap c = none from hcb] at hx1; cases hx1
      exact ⟨mb, Step.step_capply ((hag xx hxc) ▸ hlk), hag, hcb, by simp [Trace.touched]⟩
  | step_unwrap hlk =>
    match hwf with
    | .wf_unwrap (.wf_free (n := xx) hx1) =>
      have hxc : xx ≠ c := fun h => by
        rw [h] at hx1; rw [show mb.heap c = none from hcb] at hx1; cases hx1
      exact ⟨mb, Step.step_unwrap ((hag xx hxc) ▸ hlk), hag, hcb, by simp [Trace.touched]⟩
  | step_cond_var_true hlk =>
    obtain ⟨hwfx, hwf2, _⟩ := Exp.wf_inv_cond hwf
    match hwfx with
    | .wf_free (n := xb) hxb =>
      have hxc : xb ≠ c := fun h => by
        rw [h] at hxb; rw [show mb.heap c = none from hcb] at hxb; cases hxb
      have hlkb := (hag xb hxc) ▸ hlk
      exact ⟨mb, Step.step_cond_var_true hlkb, hag, hcb, by simp [Trace.touched]⟩
  | step_cond_var_false hlk =>
    obtain ⟨hwfx, _, hwf3⟩ := Exp.wf_inv_cond hwf
    match hwfx with
    | .wf_free (n := xb) hxb =>
      have hxc : xb ≠ c := fun h => by
        rw [h] at hxb; rw [show mb.heap c = none from hcb] at hxb; cases hxb
      have hlkb := (hag xb hxc) ▸ hlk
      exact ⟨mb, Step.step_cond_var_false hlkb, hag, hcb, by simp [Trace.touched]⟩
  | step_invoke hlkx hlky =>
    match hwf with
    | .wf_app (.wf_free (n := xx) hx1) (.wf_free (n := yy) hy1) =>
      have hxc : xx ≠ c := fun h => by
        rw [h] at hx1; rw [show mb.heap c = none from hcb] at hx1; cases hx1
      have hyc : yy ≠ c := fun h => by
        rw [h] at hy1; rw [show mb.heap c = none from hcb] at hy1; cases hy1
      exact ⟨mb, Step.step_invoke ((hag xx hxc) ▸ hlkx) ((hag yy hyc) ▸ hlky), hag, hcb,
        by simp only [Trace.touched, or_false]; exact fun h => hxc h.symm⟩
  | step_read hlkx hlky =>
    match hwf with
    | .wf_read (.wf_free (n := xx) hx1) =>
      have hxc : xx ≠ c := fun h => by
        rw [h] at hx1; rw [show mb.heap c = none from hcb] at hx1; cases hx1
      have hlkxb := (hag xx hxc) ▸ hlkx
      match Memory.wf_lookup hlkxb with
      | .wf_reader (.wf_free (n := yy) hy1) =>
        have hyc : yy ≠ c := fun h => by
          rw [h] at hy1; rw [show mb.heap c = none from hcb] at hy1; cases hy1
        exact ⟨mb, Step.step_read hlkxb ((hag yy hyc) ▸ hlky), hag, hcb,
          by simp only [Trace.touched, or_false]; exact fun h => hyc h.symm⟩
  | step_write hlkx hlky =>
    cases hwf with
    | wf_write hwfx hwfy => cases hwfx with | wf_free hxb => cases hwfy with | wf_free hyb =>
      have hxc := Memory.present_ne_absent hxb hcb
      have hyb' : mb.heap _ ≠ none := Option.ne_none_iff_exists'.mpr ⟨_, hyb⟩
      refine ⟨mb.update_mcell _ _ .live ⟨_, (hag _ hxc) ▸ hlkx⟩ (fun _ => hyb'),
        Step.step_write ((hag _ hxc) ▸ hlkx) hyb',
        Memory.update_mcell_lookup_agree hag, ?_,
        by simp only [Trace.touched, or_false]; exact fun h => hxc h.symm⟩
      rw [Memory.update_mcell_lookup_ne (Ne.symm hxc)]; exact hcb
  | step_drop hlkx =>
    cases hwf with
    | wf_drop hwfx => cases hwfx with | wf_free hxb =>
      have hxc := Memory.present_ne_absent hxb hcb
      refine ⟨mb.drop_mcell _ ⟨_, (hag _ hxc) ▸ hlkx⟩, Step.step_drop ((hag _ hxc) ▸ hlkx),
        Memory.drop_mcell_lookup_agree hag, ?_,
        by simp only [Trace.touched, or_false]; exact fun h => hxc h.symm⟩
      rw [Memory.drop_mcell_lookup_ne (Ne.symm hxc)]; exact hcb
  | step_alloc hlk hfresh =>
    have hlc := Memory.fresh_ne_present hfresh hc
    cases hwf with
    | wf_alloc hwfx => cases hwfx with | wf_free hx1 =>
      have hfreshb : mb.heap _ = none := (hag _ hlc).symm.trans hfresh
      have hxb' : mb.heap _ ≠ none := Option.ne_none_iff_exists'.mpr ⟨_, hx1⟩
      refine ⟨mb.extend_mcell _ _ hfreshb hxb',
        Step.step_alloc hxb' hfreshb,
        Memory.extend_mcell_lookup_agree hag, ?_, by simp [Trace.touched]⟩
      simp only [Memory.lookup, Memory.extend_mcell, Heap.extend_mcell, if_neg (Ne.symm hlc)]
      exact hcb
  | step_rename =>
    exact ⟨mb, Step.step_rename, hag, hcb, by simp [Trace.touched]⟩
  | step_unpack =>
    exact ⟨mb, Step.step_unpack, hag, hcb, by simp [Trace.touched]⟩
  | step_par_join h1 h2 =>
    exact ⟨mb, Step.step_par_join h1 h2, hag, hcb, by simp [Trace.touched]⟩
  | step_lift hv hwf_v hfresh =>
    have hlc := Memory.fresh_ne_present hfresh hc
    have hwf_vb : _ := (Exp.wf_inv_letin hwf).1
    have hfreshb : mb.heap _ = none := (hag _ hlc).symm.trans hfresh
    have hreach_eq : compute_reachability _ _ hv = compute_reachability mb.heap _ hv :=
      compute_reachability_frame_wf hcb hag _ hv hwf_vb
    refine ⟨mb.extend _ ⟨_, hv, compute_reachability mb.heap _ hv⟩ hwf_vb rfl hfreshb,
      Step.step_lift hv hwf_vb hfreshb,
      Memory.extend_lookup_agree hag hreach_eq, ?_, by simp [Trace.touched]⟩
    simp only [Memory.lookup, Memory.extend, Heap.extend, if_neg (Ne.symm hlc)]
    exact hcb
  | step_ctx_letin hinner ih =>
    obtain ⟨mb', stepb, agb, cpresb, hntb⟩ := ih hc hcb hag (Exp.wf_inv_letin hwf).1
    exact ⟨mb', Step.step_ctx_letin stepb, agb, cpresb, hntb⟩
  | step_ctx_unpack hinner ih =>
    obtain ⟨mb', stepb, agb, cpresb, hntb⟩ := ih hc hcb hag (Exp.wf_inv_unpack hwf).1
    exact ⟨mb', Step.step_ctx_unpack stepb, agb, cpresb, hntb⟩
  | step_par_left hinner ht hni ih =>
    rename_i _ mpar _ _ _ _ Cp1 Cp2
    obtain ⟨mb', stepb, agb, cpresb, hntb⟩ := ih hc hcb hag (Exp.wf_inv_par hwf).1
    have e1 : Cp1.reachability mpar = Cp1.reachability mb :=
      CaptureSet.reachability_frame_wf hcb hag _ (by cases hwf with | wf_par h _ _ _ => exact h)
    have e2 : Cp2.reachability mpar = Cp2.reachability mb :=
      CaptureSet.reachability_frame_wf hcb hag _ (by cases hwf with | wf_par _ h _ _ => exact h)
    exact ⟨mb', Step.step_par_left stepb (e1 ▸ ht) (e1 ▸ e2 ▸ hni), agb, cpresb, hntb⟩
  | step_par_right ht hni hinner ih =>
    rename_i _ mpar _ _ _ Cp1 Cp2 _
    obtain ⟨mb', stepb, agb, cpresb, hntb⟩ := ih hc hcb hag (Exp.wf_inv_par hwf).2
    have e1 : Cp1.reachability mpar = Cp1.reachability mb :=
      CaptureSet.reachability_frame_wf hcb hag _ (by cases hwf with | wf_par h _ _ _ => exact h)
    have e2 : Cp2.reachability mpar = Cp2.reachability mb :=
      CaptureSet.reachability_frame_wf hcb hag _ (by cases hwf with | wf_par _ h _ _ => exact h)
    exact ⟨mb', Step.step_par_right (e2 ▸ ht) (e1 ▸ e2 ▸ hni) stepb, agb, cpresb, hntb⟩

/-- Single-step frame, fresh variant (genuine `Step`): `c` is a capability present in `ma` but
  absent in `mb`. -/
theorem Step.frame_off_fresh {ma mb ma' : Memory} {e e' : Exp {}} {t : Trace} {c : Nat}
    (hstep : Step t ma e ma' e')
    (hc : ∃ ci, ma.lookup c = some (.capability ci))
    (hcb : mb.lookup c = none)
    (hag : ∀ l, l ≠ c → ma.lookup l = mb.lookup l)
    (hwf : Exp.WfInHeap e mb.heap) :
    ∃ mb', Step t mb e mb' e' ∧ (∀ l, l ≠ c → ma'.lookup l = mb'.lookup l) ∧
      mb'.lookup c = none ∧ ¬ Trace.touched t c :=
  Step.frame_off_absent hstep (by obtain ⟨ci, h⟩ := hc; rw [h]; simp) hcb hag hwf

/-- A genuine `Step` preserves a value cell. -/
theorem Step.val_preserved {t : Trace} {m m' : Memory} {e e' : Exp {}} {l : Nat} {w}
    (hstep : Step t m e m' e') (hl : m.lookup l = some (.val w)) :
    m'.lookup l = some (.val w) := by
  obtain ⟨c', hc', hsubc⟩ := Step.subsumes hstep l _ hl
  cases c' with
  | val w' => simp only [Cell.subsumes] at hsubc; exact hsubc ▸ hc'
  | capability ci => simp only [Cell.subsumes] at hsubc; cases hsubc
  | masked => simp only [Cell.subsumes] at hsubc; cases hsubc

/-- A genuine `Step` preserves a present cell it does not externally touch. -/
theorem Step.untouched_preserved {t : Trace} {m m' : Memory} {e e' : Exp {}} {c : Nat}
    (hstep : Step t m e m' e') (hne : m.lookup c ≠ none) (hnt : ¬ Trace.touched t c) :
    m'.lookup c = m.lookup c := by
  induction hstep with
  | step_apply _ | step_invoke _ _ | step_tapply _ | step_capply _ | step_unwrap _
  | step_cond_var_true _ | step_cond_var_false _ | step_read _ _
  | step_rename | step_unpack | step_par_join _ _ => rfl
  | step_write hx _ =>
    simp only [Trace.touched, or_false] at hnt
    exact Memory.update_mcell_lookup_ne hnt
  | step_drop hx =>
    simp only [Trace.touched, or_false] at hnt
    exact Memory.drop_mcell_lookup_ne hnt
  | step_alloc _ hfresh =>
    simp only [Memory.lookup, Memory.extend_mcell, Heap.extend_mcell]
    rw [if_neg (fun h => hne (by rw [Memory.lookup, h]; exact hfresh))]
  | step_lift hv hwf hfresh =>
    simp only [Memory.lookup, Memory.extend, Heap.extend]
    rw [if_neg (fun h => hne (by rw [Memory.lookup, h]; exact hfresh))]
  | step_ctx_letin _ ih | step_ctx_unpack _ ih => exact ih hne hnt
  | step_par_left _ _ _ ih => exact ih hne hnt
  | step_par_right _ _ _ ih => exact ih hne hnt

/-- **Single-step frame, add variant (genuine `Step`).**  Transport a step into a LARGER
  memory `ma` that agrees with the source `m` off a single cell `c` ABSENT in `m` but present
  in `ma` (the other branch's freshly-allocated cell).  Since `e` is well-formed in `m` (which
  lacks `c`) it never references `c`, and since the step does not itself allocate `c` (`hnal`),
  it replays from `ma` with the SAME trace and result, results agree off `c`, and `c` is
  unchanged.  The mirror of `frame_off_absent` (source lacks `c` rather than target). -/
theorem Step.frame_add {m ma m' : Memory} {e e' : Exp {}} {t : Trace} {c : Nat}
    (hstep : Step t m e m' e')
    (hc : m.lookup c = none)
    (hc' : m'.lookup c = none)
    (hag : ∀ l, l ≠ c → m.lookup l = ma.lookup l)
    (hwf : Exp.WfInHeap e m.heap) :
    ∃ ma', Step t ma e ma' e' ∧ (∀ l, l ≠ c → m'.lookup l = ma'.lookup l) ∧
      ma'.lookup c = ma.lookup c := by
  induction hstep generalizing ma with
  | step_apply hlk =>
    match hwf with
    | .wf_app (.wf_free (n := xx) hx1) _ =>
      have hxc : xx ≠ c := Memory.present_ne_absent hx1 hc
      exact ⟨ma, Step.step_apply ((hag xx hxc) ▸ hlk), hag, rfl⟩
  | step_tapply hlk =>
    match hwf with
    | .wf_tapp (.wf_free (n := xx) hx1) _ =>
      have hxc : xx ≠ c := Memory.present_ne_absent hx1 hc
      exact ⟨ma, Step.step_tapply ((hag xx hxc) ▸ hlk), hag, rfl⟩
  | step_capply hlk =>
    match hwf with
    | .wf_capp (.wf_free (n := xx) hx1) _ =>
      have hxc : xx ≠ c := Memory.present_ne_absent hx1 hc
      exact ⟨ma, Step.step_capply ((hag xx hxc) ▸ hlk), hag, rfl⟩
  | step_unwrap hlk =>
    match hwf with
    | .wf_unwrap (.wf_free (n := xx) hx1) =>
      have hxc : xx ≠ c := Memory.present_ne_absent hx1 hc
      exact ⟨ma, Step.step_unwrap ((hag xx hxc) ▸ hlk), hag, rfl⟩
  | step_cond_var_true hlk =>
    obtain ⟨hwfx, _, _⟩ := Exp.wf_inv_cond hwf
    match hwfx with
    | .wf_free (n := xb) hxb =>
      have hxc : xb ≠ c := Memory.present_ne_absent hxb hc
      exact ⟨ma, Step.step_cond_var_true ((hag xb hxc) ▸ hlk), hag, rfl⟩
  | step_cond_var_false hlk =>
    obtain ⟨hwfx, _, _⟩ := Exp.wf_inv_cond hwf
    match hwfx with
    | .wf_free (n := xb) hxb =>
      have hxc : xb ≠ c := Memory.present_ne_absent hxb hc
      exact ⟨ma, Step.step_cond_var_false ((hag xb hxc) ▸ hlk), hag, rfl⟩
  | step_invoke hlkx hlky =>
    match hwf with
    | .wf_app (.wf_free (n := xx) hx1) (.wf_free (n := yy) hy1) =>
      have hxc : xx ≠ c := Memory.present_ne_absent hx1 hc
      have hyc : yy ≠ c := Memory.present_ne_absent hy1 hc
      exact ⟨ma, Step.step_invoke ((hag xx hxc) ▸ hlkx) ((hag yy hyc) ▸ hlky), hag, rfl⟩
  | step_read hlkx hlky =>
    match hwf with
    | .wf_read (.wf_free (n := xx) hx1) =>
      have hxc : xx ≠ c := Memory.present_ne_absent hx1 hc
      have hlkxa := (hag xx hxc) ▸ hlkx
      match Memory.wf_lookup hlkx with
      | .wf_reader (.wf_free (n := yy) hy1) =>
        have hyc : yy ≠ c := Memory.present_ne_absent hy1 hc
        exact ⟨ma, Step.step_read hlkxa ((hag yy hyc) ▸ hlky), hag, rfl⟩
  | step_write hlkx hlky =>
    cases hwf with
    | wf_write hwfx hwfy => cases hwfx with | wf_free hxb => cases hwfy with | wf_free hyb =>
      have hxc := Memory.present_ne_absent hxb hc
      have hyc := Memory.present_ne_absent hyb hc
      have hyb' := Memory.heap_ne_none_of_agree hag hyc (Memory.heap_ne_none_of_lookup hyb)
      refine ⟨ma.update_mcell _ _ .live ⟨_, (hag _ hxc) ▸ hlkx⟩ (fun _ => hyb'),
        Step.step_write ((hag _ hxc) ▸ hlkx) hyb',
        Memory.update_mcell_lookup_agree hag, ?_⟩
      exact Memory.update_mcell_lookup_ne (Ne.symm hxc)
  | step_drop hlkx =>
    cases hwf with
    | wf_drop hwfx => cases hwfx with | wf_free hxb =>
      have hxc := Memory.present_ne_absent hxb hc
      refine ⟨ma.drop_mcell _ ⟨_, (hag _ hxc) ▸ hlkx⟩, Step.step_drop ((hag _ hxc) ▸ hlkx),
        Memory.drop_mcell_lookup_agree hag, ?_⟩
      exact Memory.drop_mcell_lookup_ne (Ne.symm hxc)
  | step_alloc hlk hfresh =>
    have hlc := Memory.present_ne_absent (Memory.extend_mcell_lookup hfresh hlk) hc'
    cases hwf with
    | wf_alloc hwfx => cases hwfx with | wf_free hx1 =>
      have hxc := Memory.present_ne_absent hx1 hc
      have hfresha : ma.heap _ = none := (hag _ hlc).symm.trans hfresh
      have hxb' := Memory.heap_ne_none_of_agree hag hxc (Memory.heap_ne_none_of_lookup hx1)
      refine ⟨ma.extend_mcell _ _ hfresha hxb',
        Step.step_alloc hxb' hfresha,
        Memory.extend_mcell_lookup_agree hag, ?_⟩
      simp only [Memory.lookup, Memory.extend_mcell, Heap.extend_mcell, if_neg (Ne.symm hlc)]
  | step_rename =>
    exact ⟨ma, Step.step_rename, hag, rfl⟩
  | step_unpack =>
    exact ⟨ma, Step.step_unpack, hag, rfl⟩
  | step_par_join h1 h2 =>
    exact ⟨ma, Step.step_par_join h1 h2, hag, rfl⟩
  | @step_lift v m0 e0 l hv hwf_v hfresh =>
    have hlc : l ≠ c := fun h => by
      subst h
      rw [show (m0.extend l ⟨v, hv, compute_reachability m0.heap v hv⟩ hwf_v rfl hfresh).lookup l
            = some (Cell.val ⟨v, hv, compute_reachability m0.heap v hv⟩) from by
          simp only [Memory.lookup, Memory.extend, Heap.extend_lookup_eq]] at hc'
      cases hc'
    have hwf_va : _ := (Exp.wf_inv_letin hwf).1
    have hfresha : ma.heap _ = none := (hag _ hlc).symm.trans hfresh
    have hwf_v_ma : Exp.WfInHeap v ma.heap := by
      have hsub : ma.subsumes m0 := by
        intro l0 cc hl0
        by_cases hl0c : l0 = c
        · subst hl0c; rw [Memory.lookup] at hc; rw [hc] at hl0; cases hl0
        · exact ⟨cc, (hag l0 hl0c).symm.trans hl0, Cell.subsumes_refl cc⟩
      exact Exp.wf_monotonic hsub hwf_va
    have hreach_eq : compute_reachability m0.heap v hv = compute_reachability ma.heap v hv :=
      (compute_reachability_frame_wf hc (fun l0 hl0 => (hag l0 hl0).symm) v hv hwf_va).symm
    refine ⟨ma.extend _ ⟨_, hv, compute_reachability ma.heap _ hv⟩ hwf_v_ma rfl hfresha,
      Step.step_lift hv hwf_v_ma hfresha,
      Memory.extend_lookup_agree hag hreach_eq, ?_⟩
    simp only [Memory.lookup, Memory.extend, Heap.extend, if_neg (Ne.symm hlc)]
  | step_ctx_letin hinner ih =>
    obtain ⟨ma', stepa, aga, cpresa⟩ := ih hc hc' hag (Exp.wf_inv_letin hwf).1
    exact ⟨ma', Step.step_ctx_letin stepa, aga, cpresa⟩
  | step_ctx_unpack hinner ih =>
    obtain ⟨ma', stepa, aga, cpresa⟩ := ih hc hc' hag (Exp.wf_inv_unpack hwf).1
    exact ⟨ma', Step.step_ctx_unpack stepa, aga, cpresa⟩
  | step_par_left hinner ht hni ih =>
    rename_i _ mpar _ _ _ _ Cp1 Cp2
    obtain ⟨ma', stepa, aga, cpresa⟩ := ih hc hc' hag (Exp.wf_inv_par hwf).1
    have e1 : Cp1.reachability mpar = Cp1.reachability ma :=
      (CaptureSet.reachability_frame_wf hc (fun l0 hl0 => (hag l0 hl0).symm) _
        (by cases hwf with | wf_par h _ _ _ => exact h)).symm
    have e2 : Cp2.reachability mpar = Cp2.reachability ma :=
      (CaptureSet.reachability_frame_wf hc (fun l0 hl0 => (hag l0 hl0).symm) _
        (by cases hwf with | wf_par _ h _ _ => exact h)).symm
    exact ⟨ma', Step.step_par_left stepa (e1 ▸ ht) (e1 ▸ e2 ▸ hni), aga, cpresa⟩
  | step_par_right ht hni hinner ih =>
    rename_i _ mpar _ _ _ Cp1 Cp2 _
    obtain ⟨ma', stepa, aga, cpresa⟩ := ih hc hc' hag (Exp.wf_inv_par hwf).2
    have e1 : Cp1.reachability mpar = Cp1.reachability ma :=
      (CaptureSet.reachability_frame_wf hc (fun l0 hl0 => (hag l0 hl0).symm) _
        (by cases hwf with | wf_par h _ _ _ => exact h)).symm
    have e2 : Cp2.reachability mpar = Cp2.reachability ma :=
      (CaptureSet.reachability_frame_wf hc (fun l0 hl0 => (hag l0 hl0).symm) _
        (by cases hwf with | wf_par _ h _ _ => exact h)).symm
    exact ⟨ma', Step.step_par_right (e2 ▸ ht) (e1 ▸ e2 ▸ hni) stepa, aga, cpresa⟩

/-- **Single-cell delta.**  A genuine `Step` either leaves the memory unchanged, updates a single
  capability cell `c` (keeping it a capability), or freshly allocates a single cell `c` (absent in
  `m`, present in `m'`, with `c` in the trace's allocations).  This bounded footprint is what lets
  the cross-`par` diamond frame the two separated steps past each other. -/
theorem Step.delta {t : Trace} {m m' : Memory} {e e' : Exp {}} (hstep : Step t m e m' e') :
    m' = m ∨
    (∃ c ci ci', m.lookup c = some (.capability ci) ∧ m'.lookup c = some (.capability ci') ∧
      (∃ cm, Trace.extTouchesMode t c cm ∧ cm ≠ .access .ro) ∧
      ∀ l, l ≠ c → m.lookup l = m'.lookup l) ∨
    (∃ c, m.lookup c = none ∧ m'.lookup c ≠ none ∧
      ∀ l, l ≠ c → m.lookup l = m'.lookup l) := by
  induction hstep with
  | step_apply _ | step_invoke _ _ | step_tapply _ | step_capply _ | step_unwrap _
  | step_cond_var_true _ | step_cond_var_false _ | step_read _ _
  | step_rename | step_unpack | step_par_join _ _ => exact Or.inl rfl
  | step_write hx _ =>
    refine Or.inr (Or.inl ⟨_, _, _, hx, Memory.update_mcell_lookup,
      ⟨.access .epsilon, Or.inl ⟨rfl, by simp, rfl⟩, by simp⟩,
      fun l hl => (Memory.update_mcell_lookup_ne hl).symm⟩)
  | step_drop hx =>
    refine Or.inr (Or.inl ⟨_, _, .mcell 0 .dead, hx, ?_,
      ⟨.drop, Or.inl ⟨rfl, by simp, rfl⟩, by simp⟩,
      fun l hl => (Memory.drop_mcell_lookup_ne hl).symm⟩)
    simp only [Memory.lookup, Memory.drop_mcell, Heap.update_cell, if_true]
  | step_alloc hlk hfresh =>
    refine Or.inr (Or.inr ⟨_, hfresh, ?_, fun k hk => ?_⟩)
    · rw [Memory.extend_mcell_lookup hfresh hlk]; simp
    · simp only [Memory.lookup, Memory.extend_mcell, Heap.extend_mcell, if_neg hk]
  | @step_lift v m0 e0 l hv hwf hfresh =>
    refine Or.inr (Or.inr ⟨l, hfresh, ?_, fun k hk => ?_⟩)
    · rw [show (m0.extend l ⟨v, hv, compute_reachability m0.heap v hv⟩ hwf rfl hfresh).lookup l
            = some (Cell.val ⟨v, hv, compute_reachability m0.heap v hv⟩) from by
          simp only [Memory.lookup, Memory.extend, Heap.extend_lookup_eq]]; simp
    · simp only [Memory.lookup, Memory.extend, Heap.extend, if_neg hk]
  | step_ctx_letin _ ih | step_ctx_unpack _ ih
  | step_par_left _ _ _ ih | step_par_right _ _ _ ih => exact ih

/-- A capability cell present in `m` is not freshly allocated by a separated step. -/
theorem Step.not_allocd_present {t : Trace} {m m' : Memory} {e e' : Exp {}} {c : Nat}
    (hstep : Step t m e m' e') (hpres : m.lookup c ≠ none) : ¬ Trace.allocd t c :=
  fun ha => hpres (Step.alloc_fresh hstep ha)

/-- **Right-leg replay (no clash).**  Transport the separated step `h2` (the right `par`
  branch, originally from `m`) across the left branch's single-cell delta `ma`: provided `h2`
  does not re-allocate the left's freshly-allocated cell (`hnoclash`), `h2` replays from `ma`
  with the SAME trace and result, reaching a memory `md` that agrees with `h2`'s original result
  `mb` off the left's cell.  The single building block of the cross-`par` diamond's two legs. -/
theorem Step.replay_across {ts1 ts2 : Trace} {m ma mb : Memory} {e1 e1' e2 e2' : Exp {}}
    (h1 : Step ts1 m e1 ma e1') (h2 : Step ts2 m e2 mb e2')
    (hsep : Trace.Noninterfere ts1 ts2) (hwf2 : Exp.WfInHeap e2 m.heap)
    (hnoclash : ∀ c, m.lookup c = none → ma.lookup c ≠ none → mb.lookup c = none) :
    ∃ md, Step ts2 ma e2 md e2' ∧
      (∀ l, m.lookup l ≠ ma.lookup l → md.lookup l = ma.lookup l) ∧
      (∀ l, m.lookup l = ma.lookup l → md.lookup l = mb.lookup l) := by
  -- `e2` is well-formed in `ma.heap` too: `ma` subsumes `m` (it differs by ≤1 added/updated cell).
  have hsubma : ma.subsumes m := Step.subsumes h1
  have hwf2a : Exp.WfInHeap e2 ma.heap := Exp.wf_monotonic hsubma hwf2
  rcases Step.delta h1 with hpres | ⟨c, ci, ci', hmc, hmac, ⟨cm, hext, hcmne⟩, hag⟩ |
    ⟨c, hmc, hmac, hag⟩
  · -- left preserves memory: ma = m, replay h2 directly
    subst hpres
    exact ⟨mb, h2, fun l hl => absurd rfl hl, fun l _ => rfl⟩
  · -- left updates capability cell c
    have hntc : ¬ Trace.touched ts2 c := by
      have hnal2 : ¬ Trace.allocd ts2 c := Step.not_allocd_present h2 (by rw [hmc]; simp)
      exact Trace.not_touched_of_noninterfere hsep.symm hext hcmne hnal2
    obtain ⟨md, stepd, agd, cpresd⟩ :=
      Step.frame_off h2 ⟨ci, hmc⟩ ⟨ci', hmac⟩ hag hntc hwf2a
    refine ⟨md, stepd, fun l hl => ?_, fun l hl => ?_⟩
    · by_cases h0 : l = c
      · subst h0; rw [cpresd]
      · exact absurd (hag l h0) hl
    · by_cases h0 : l = c
      · subst h0; rw [cpresd, ← hl]
        exact (Step.untouched_preserved h2 (by rw [hmc]; simp) hntc).symm
      · exact (agd l h0).symm
  · -- left allocates fresh cell c
    have hc'b : mb.lookup c = none := hnoclash c hmc hmac
    obtain ⟨md, stepd, agd, cpresd⟩ :=
      Step.frame_add h2 hmc hc'b hag hwf2
    refine ⟨md, stepd, fun l hl => ?_, fun l hl => ?_⟩
    · by_cases h0 : l = c
      · subst h0; rw [cpresd]
      · exact absurd (hag l h0) hl
    · by_cases h0 : l = c
      · subst h0; exact absurd (hl.symm.trans hmc) hmac
      · exact (agd l h0).symm

/-- **Footprint disjointness.**  Two separated steps from the same memory have disjoint
  single-cell footprints, provided neither freshly allocates the cell the other does
  (`hnoclash`): a shared cap-update is forbidden by non-interference, and a present cell cannot
  be a fresh allocation of the other branch.  This is the geometric core of the cross diamond. -/
theorem Step.delta_disjoint {ts1 ts2 : Trace} {m ma mb : Memory} {e1 e1' e2 e2' : Exp {}}
    (h1 : Step ts1 m e1 ma e1') (h2 : Step ts2 m e2 mb e2')
    (hsep : Trace.Noninterfere ts1 ts2)
    (hnoclash : ∀ c, m.lookup c = none → ma.lookup c ≠ none → mb.lookup c = none)
    {l : Nat} (hl1 : m.lookup l ≠ ma.lookup l) (hl2 : m.lookup l ≠ mb.lookup l) : False := by
  rcases Step.delta h1 with hpres | ⟨c, ci, ci', hmc, hmac, ⟨cm, hext, hcmne⟩, hag⟩ |
    ⟨c, hmc, hmac, hag⟩
  · exact hl1 (by rw [hpres])
  · -- left mutates cap c; so l = c (else m,ma agree). Then right also touched c.
    by_cases h0 : l = c
    · subst h0
      rcases Step.delta h2 with hpres2 | ⟨c2, ci2, ci2', hmc2, hmac2, ⟨cm2, hext2, hcmne2⟩, hag2⟩ |
          ⟨c2, hmc2, hmac2, hag2⟩
      · exact hl2 (by rw [hpres2])
      · -- right mutates cap c2; need l = c2 too. If c2 ≠ l then m,mb agree at l → contra hl2.
        by_cases h02 : l = c2
        · subst h02
          exact absurd (hsep _ cm cm2 hext hext2).1 hcmne
        · exact hl2 (hag2 _ h02)
      · -- right allocates fresh c2; if c2 ≠ l, agree at l; else l fresh in m yet cap in m → contra
        by_cases h02 : l = c2
        · subst h02; rw [hmc] at hmc2; cases hmc2
        · exact hl2 (hag2 _ h02)
    · exact hl1 (hag l h0)
  · -- left allocates fresh c; l = c (else agree); then mb fresh at c by noclash → contra hl2
    by_cases h0 : l = c
    · subst h0
      have hmbc : mb.lookup l = none := hnoclash l hmc hmac
      exact hl2 (hmc.trans hmbc.symm)
    · exact hl1 (hag l h0)

/-- **Cross diamond (no clash).**  Two separated steps from a common memory, neither
  re-allocating the other's freshly-chosen cell (`hncR`/`hncL`), reconverge to the SAME memory
  `md` in one step each (each keeping its own trace and result): the right branch replays from
  `ma`, the left replays from `mb`, both reaching `md`.  The merge `md1 = md2` is `ext_lookup`
  via `delta_disjoint`.  No permutation is needed — `π = id`. -/
theorem step_step_diamond_noclash {ts1 ts2 : Trace} {m ma mb : Memory} {e1 e1' e2 e2' : Exp {}}
    (h1 : Step ts1 m e1 ma e1') (h2 : Step ts2 m e2 mb e2')
    (hsep : Trace.Noninterfere ts1 ts2)
    (hwf1 : Exp.WfInHeap e1 m.heap) (hwf2 : Exp.WfInHeap e2 m.heap)
    (hncR : ∀ c, m.lookup c = none → ma.lookup c ≠ none → mb.lookup c = none)
    (hncL : ∀ c, m.lookup c = none → mb.lookup c ≠ none → ma.lookup c = none) :
    ∃ md, Step ts2 ma e2 md e2' ∧ Step ts1 mb e1 md e1' := by
  obtain ⟨md1, stepR, hR1, hR2⟩ := Step.replay_across h1 h2 hsep hwf2 hncR
  obtain ⟨md2, stepL, hL1, hL2⟩ := Step.replay_across h2 h1 hsep.symm hwf1 hncL
  have hmd : md1 = md2 := by
    apply Memory.ext_lookup; intro l
    by_cases ha : m.lookup l = ma.lookup l <;> by_cases hb : m.lookup l = mb.lookup l
    · -- l in neither footprint: md1 = mb = m, md2 = ma = m
      rw [hR2 l ha, hL2 l hb, ← ha, hb]
    · -- l in right's footprint only: md1 = mb here, md2 = ma = m here
      rw [hR2 l ha, hL1 l (fun h => hb h)]
    · -- l in left's footprint only: md1 = ma here, md2 = mb here
      rw [hR1 l (fun h => ha h), hL2 l hb]
    · -- l in both footprints: impossible
      exact absurd (Step.delta_disjoint h1 h2 hsep hncR ha hb) (fun h => h)
  exact ⟨md1, stepR, hmd ▸ stepL⟩

/-! ### Guard transport for diamond closing legs

  The old development discharged the `par` guards of the diamond's closing legs
  from a total `Safe` carrier (run-extension via `has_answer`/`head_expand`) —
  a device that is unavailable (and dishonest) under the budget-indexed
  rely–guarantee `Safe.par`.  The carrier-free replacement: the closing legs are
  (possibly renamed) REPLAYS of the opposite input step, so their guards follow
  from the input steps' OWN guards, transported across the fresh-location
  renaming (which fixes the ancestor domain) and the one-step memory growth
  (reachability is subsumption-invariant for wf annotations). -/

/-- A trace bound at a wf annotation survives the opposite step's memory growth
  (reachability is subsumption-invariant). -/
theorem traceok_across {u t : Trace} {m m' : Memory} {C : CaptureSet {}} {e0 e0' : Exp {}}
    (hstep : Step u m e0 m' e0') (hwfC : C.WfInHeap m.heap)
    (ht : TraceOk t (C.reachability m)) :
    TraceOk t (C.reachability m') := by
  rwa [CaptureSet.reachability_monotonic (Step.subsumes hstep) C hwfC]

/-- A trace bound survives a renaming that fixes the memory's domain: the
  annotation's reachability sits inside the domain, so the renamed guard set is
  the guard set itself. -/
theorem traceok_rename {t : Trace} {m : Memory} {C : CaptureSet {}} {σ : Equiv.Perm Nat}
    (hσ : ∀ l, m.heap l ≠ none → σ l = l)
    (ht : TraceOk t (C.reachability m)) :
    TraceOk (t.renameLoc σ) (C.reachability m) := by
  have hfix : (C.reachability m).renameLoc σ = C.reachability m :=
    CapabilitySet.renameLoc_eq_of_fix
      (fun _ l h => hσ l (CaptureSet.reachability_dom h))
  have hren := TraceOk.renameLoc ht σ
  rwa [hfix] at hren

/-- A trace bound at the initial annotation restricts to the annotation grown by
  a genuine step's allocations, at the post-step memory. -/
theorem traceok_grow {u t : Trace} {m m' : Memory} {C : CaptureSet {}} {e0 e0' : Exp {}}
    (hstep : Step u m e0 m' e0') (hwfC : C.WfInHeap m.heap)
    (ht : TraceOk t (C.reachability m)) :
    TraceOk t ((C.growByAllocs u).reachability m') :=
  TraceOk.mono growByAllocs_reachability_ge (traceok_across hstep hwfC ht)

/-- `ni_growByAllocs` specialized to a genuine step: after the stepping branch's
  annotation grows by the step's allocations, non-interference against the other
  side persists at the post-step memory. -/
theorem Step.ni_grow {u : Trace} {m m' : Memory} {CL CR : CaptureSet {}} {e0 e0' : Exp {}}
    (hstep : Step u m e0 m' e0')
    (hwfL : CL.WfInHeap m.heap) (hwfR : CR.WfInHeap m.heap)
    (hni : CapabilitySet.Noninterference (CL.reachability m) (CR.reachability m)) :
    CapabilitySet.Noninterference
      ((CL.growByAllocs u).reachability m') (CR.reachability m') :=
  ni_growByAllocs (Step.subsumes hstep) hwfL hwfR
    (fun _ hl => Step.allocd_mcell hstep (Trace.mem_allocList.mp hl))
    (fun _ hl => Step.alloc_fresh hstep (Trace.mem_allocList.mp hl))
    hni

/-- Wrap a zero-or-one left-branch `RStep` into a `par` context with the guards
  supplied directly (carrier-free replacement of the old `Safe`-consuming lift). -/
theorem RStep.par_left_guarded {t : Trace} {m m' : Memory} {C1 C2 : CaptureSet {}}
    {e1 e2 e1' : Exp {}}
    (ht : TraceOk t (C1.reachability m))
    (hni : CapabilitySet.Noninterference (C1.reachability m) (C2.reachability m))
    (h : RStep t m e1 m' e1') :
    RStep t m (.par C1 C2 e1 e2) m' (.par (C1.growByAllocs t) C2 e1' e2) := by
  cases h with
  | refl => exact RStep.refl
  | step hs => exact RStep.step (Step.step_par_left hs ht hni)

/-- Wrap a zero-or-one right-branch `RStep` into a `par` context with the guards
  supplied directly. -/
theorem RStep.par_right_guarded {t : Trace} {m m' : Memory} {C1 C2 : CaptureSet {}}
    {e1 e2 e2' : Exp {}}
    (ht : TraceOk t (C2.reachability m))
    (hni : CapabilitySet.Noninterference (C1.reachability m) (C2.reachability m))
    (h : RStep t m e2 m' e2') :
    RStep t m (.par C1 C2 e1 e2) m' (.par C1 (C2.growByAllocs t) e1 e2') := by
  cases h with
  | refl => exact RStep.refl
  | step hs => exact RStep.step (Step.step_par_right ht hni hs)

/-- The shape of `local_diamond`'s conclusion, abstracted so it can be stated once.
  The final conjunct records the PROVENANCE of the closing legs — each is either
  empty or a replay of the opposite input step's trace under a domain-fixing
  renaming.  This is what lets the `par` congruence cases derive the closing
  legs' guards from the input steps' own guards, with no `Safe` carrier. -/
def Diamond (D : Nat → Prop) (ts1 : Trace) (ma : Memory) (ea : Exp {})
    (ts2 : Trace) (mb : Memory) (eb : Exp {}) : Prop :=
  ∃ (w1 w2 : Trace) (d1m d2m : Memory) (d1e d2e : Exp {}) (π : Equiv.Perm Nat),
    RStep w1 ma ea d1m d1e ∧ RStep w2 mb eb d2m d2e ∧
    d2m = d1m.renameLoc π ∧ Exp.AEq d2e (d1e.renameLoc π) ∧
    (∀ l, D l → π l = l) ∧
    Trace.Equiv ((ts1 ++ w1).renameLoc π) (ts2 ++ w2) ∧
    (∀ l, Trace.allocd ((ts1 ++ w1).renameLoc π) l ↔ Trace.allocd (ts2 ++ w2) l) ∧
    ((w1 = [] ∧ w2 = []) ∨
      ∃ σ : Equiv.Perm Nat, w1 = ts2.renameLoc σ ∧ w2 = ts1.renameLoc σ ∧
        ∀ l, D l → σ l = l)

/-- A deterministic redex: both steps coincide (same memory, expression and trace), so the
  diamond closes in zero steps with `π = id`. -/
theorem Diamond.det {D : Nat → Prop} {ts1 ts2 : Trace} {ma mb : Memory} {ea eb : Exp {}}
    (hm : ma = mb) (he : ea = eb) (ht : ts1 = ts2) : Diamond D ts1 ma ea ts2 mb eb := by
  subst hm; subst he; subst ht
  exact ⟨[], [], ma, ma, ea, ea, Equiv.refl Nat, RStep.refl, RStep.refl,
    (Memory.renameLoc_id).symm, Exp.AEq.of_eq (Exp.renameLoc_id).symm, fun _ _ => rfl,
    by simp only [List.append_nil, Trace.renameLoc_id]; exact Trace.Equiv.refl _,
    by simp only [List.append_nil, Trace.renameLoc_id]; exact fun _ => trivial,
    Or.inl ⟨rfl, rfl⟩⟩

/-- A location fresh in BOTH memories exists (their domains are jointly finite). -/
theorem Memory.exists_fresh_two (ma mb : Memory) :
    ∃ f : Nat, ma.lookup f = none ∧ mb.lookup f = none := by
  obtain ⟨doma, hda⟩ := ma.findom
  obtain ⟨domb, hdb⟩ := mb.findom
  refine ⟨(doma ∪ domb).sup id + 1, ?_, ?_⟩
  · by_contra h
    have hmem : (doma ∪ domb).sup id + 1 ∈ doma := (hda _).mp h
    have : (doma ∪ domb).sup id + 1 ≤ (doma ∪ domb).sup id :=
      Finset.le_sup (f := id) (Finset.mem_union.mpr (Or.inl hmem))
    omega
  · by_contra h
    have hmem : (doma ∪ domb).sup id + 1 ∈ domb := (hdb _).mp h
    have : (doma ∪ domb).sup id + 1 ≤ (doma ∪ domb).sup id :=
      Finset.le_sup (f := id) (Finset.mem_union.mpr (Or.inr hmem))
    omega

/-- **Local diamond.**  Two single steps from a common well-formed config reconverge in
  at most one step on each side, up to a permutation fixing the ancestor domain `D ⊆ dom(m)`,
  with `Trace.Equiv` combined traces and matching allocation footprint.  Deterministic redexes
  close in zero steps with `π = id`; `alloc`/`lift` and the `par` left/right schedule close up
  to a swap of freshly-chosen locations.  Proven by induction on the first step with the second
  universally quantified (so the congruence cases recurse).

  CARRIER-FREE: no `Safe` hypothesis — the separation content that closes the `par`
  cases is carried by the two input `Step`s' own guards, transported to the closing
  legs via the `Diamond` provenance conjunct. -/
theorem local_diamond {ts1 : Trace} {m ma : Memory} {e ea : Exp {}}
    (hst1 : Step ts1 m e ma ea) :
    ∀ {D : Nat → Prop} {ts2 : Trace} {mb : Memory} {eb : Exp {}},
      (∀ l, D l → m.heap l ≠ none) → Exp.WfInHeap e m.heap →
      Step ts2 m e mb eb → Diamond D ts1 ma ea ts2 mb eb := by
  induction hst1 with
  | step_apply hlk =>
    intro D ts2 mb eb hD hwf hst2
    cases hst2 with
    | step_apply hlk2 =>
      have hu := lookup_val_unwrap_eq hlk hlk2; injection hu with _ _ _ hbody
      exact Diamond.det rfl (by rw [hbody]) rfl
    | step_invoke hlkx2 hlky2 => have := lookup_cell_eq hlk hlkx2; simp at this
  | step_invoke hlkx hlky =>
    intro D ts2 mb eb hD hwf hst2
    cases hst2 with
    | step_apply hlk2 => have := lookup_cell_eq hlkx hlk2; simp at this
    | step_invoke hlkx2 hlky2 => exact Diamond.det rfl rfl rfl
  | step_tapply hlk =>
    intro D ts2 mb eb hD hwf hst2
    cases hst2 with
    | step_tapply hlk2 =>
      have hu := lookup_val_unwrap_eq hlk hlk2; injection hu with _ _ _ hbody
      exact Diamond.det rfl (by rw [hbody]) rfl
  | step_capply hlk =>
    intro D ts2 mb eb hD hwf hst2
    cases hst2 with
    | step_capply hlk2 =>
      have hu := lookup_val_unwrap_eq hlk hlk2; injection hu with _ _ _ hbody
      exact Diamond.det rfl (by rw [hbody]) rfl
  | step_unwrap hlk =>
    intro D ts2 mb eb hD hwf hst2
    cases hst2 with
    | step_unwrap hlk2 =>
      have hu := lookup_val_unwrap_eq hlk hlk2; injection hu with _ _ _ hbody
      exact Diamond.det rfl hbody rfl
  | step_cond_var_true hlk =>
    intro D ts2 mb eb hD hwf hst2
    cases hst2 with
    | step_cond_var_true hlk2 => exact Diamond.det rfl rfl rfl
    | step_cond_var_false hlk2 => have := lookup_val_unwrap_eq hlk hlk2; simp at this
  | step_cond_var_false hlk =>
    intro D ts2 mb eb hD hwf hst2
    cases hst2 with
    | step_cond_var_true hlk2 => have := lookup_val_unwrap_eq hlk hlk2; simp at this
    | step_cond_var_false hlk2 => exact Diamond.det rfl rfl rfl
  | step_read hlkx hlky =>
    intro D ts2 mb eb hD hwf hst2
    cases hst2 with
    | step_read hlkx2 hlky2 =>
      have hy := lookup_val_unwrap_eq hlkx hlkx2
      simp only [Exp.reader.injEq, Var.free.injEq] at hy
      subst hy
      have hb := lookup_cell_eq hlky hlky2
      simp only [Cell.capability.injEq, CapabilityInfo.mcell.injEq, and_true] at hb
      subst hb
      exact Diamond.det rfl rfl rfl
  | step_write hx hy =>
    intro D ts2 mb eb hD hwf hst2
    cases hst2 with
    | step_write hx2 hy2 => exact Diamond.det (Memory.eq_of_heap rfl) rfl rfl
  | @step_alloc l m0 x hlk hfresh =>
    intro D ts2 mb eb hD hwf hst2
    cases hst2 with
    | @step_alloc l2 _ _ hlk2 hfresh2 =>
      -- Both steps box the same content var `x` at fresh locations `l`, `l2`.  `x` is
      -- present, so the swap of the two fresh locations fixes it.
      have hxl : x ≠ l := Memory.present_ne_fresh hlk hfresh
      have hxl2 : x ≠ l2 := Memory.present_ne_fresh hlk hfresh2
      refine ⟨[], [], _, _, _, _, Equiv.swap l l2, RStep.refl, RStep.refl, ?_, ?_, ?_, ?_, ?_,
        Or.inl ⟨rfl, rfl⟩⟩
      · apply Memory.eq_of_heap
        change m0.heap.extend_mcell l2 x
          = (m0.heap.extend_mcell l x).renameLoc (Equiv.swap l l2)
        rw [Heap.extend_mcell_renameLoc, Memory.heap_renameLoc_eq_of_fresh hfresh hfresh2,
          Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne hxl hxl2]
      · apply Exp.AEq.of_eq
        simp only [Exp.renameLoc, CaptureSet.renameLoc, Var.renameLoc, Equiv.swap_apply_left]
      · exact fun l' hl' => Equiv.swap_apply_of_ne_of_ne
          (fun he => hD l' hl' (by rw [he]; exact hfresh))
          (fun he => hD l' hl' (by rw [he]; exact hfresh2))
      · simp only [List.append_nil, Trace.renameLoc, List.map_cons, List.map_nil,
          TraceItem.renameLoc, Equiv.swap_apply_left]
        exact Trace.Equiv.refl _
      · simp only [List.append_nil, Trace.renameLoc, List.map_cons, List.map_nil,
          TraceItem.renameLoc, Equiv.swap_apply_left]
        exact fun _ => trivial
  | step_drop hx =>
    intro D ts2 mb eb hD hwf hst2
    cases hst2 with
    | step_drop hx2 => exact Diamond.det (Memory.eq_of_heap rfl) rfl rfl
  | @step_ctx_letin _ m0 _ _ _ e2 inner ih =>
    intro D ts2 mb eb hD hwf hst2
    obtain ⟨hwf1, hwf2⟩ := Exp.wf_inv_letin hwf
    cases hst2 with
    | step_ctx_letin inner2 =>
      obtain ⟨w1, w2, d1m, d2m, d1e, d2e, π, hr1, hr2, hdm, hde, hπ, htr, hal, hprov⟩ :=
        ih (D := fun l => m0.heap l ≠ none) (fun _ h => h) hwf1 inner2
      have he2 : e2.renameLoc π = e2 := Exp.renameLoc_eq_of_wf hwf2 hπ
      refine ⟨w1, w2, d1m, d2m, .letin d1e e2, .letin d2e e2, π,
        RStep.ctx_letin hr1, RStep.ctx_letin hr2, hdm, ?_, fun l hl => hπ l (hD l hl),
        htr, hal, ?_⟩
      · change Exp.AEq (.letin d2e e2) (.letin (d1e.renameLoc π) (e2.renameLoc π))
        rw [he2]; exact Exp.AEq.letin hde
      · rcases hprov with h | ⟨σ, h1, h2, h3⟩
        · exact Or.inl h
        · exact Or.inr ⟨σ, h1, h2, fun l hl => h3 l (hD l hl)⟩
    | step_rename => cases inner
    | step_lift hv2 _ _ =>
      exact (Step.not_isAns inner (Exp.IsAns.is_val (Exp.isVal_of_isSimpleVal hv2))).elim
  | @step_ctx_unpack _ m0 _ _ _ e2 inner ih =>
    intro D ts2 mb eb hD hwf hst2
    obtain ⟨hwf1, hwf2⟩ := Exp.wf_inv_unpack hwf
    cases hst2 with
    | step_ctx_unpack inner2 =>
      obtain ⟨w1, w2, d1m, d2m, d1e, d2e, π, hr1, hr2, hdm, hde, hπ, htr, hal, hprov⟩ :=
        ih (D := fun l => m0.heap l ≠ none) (fun _ h => h) hwf1 inner2
      have he2 : e2.renameLoc π = e2 := Exp.renameLoc_eq_of_wf hwf2 hπ
      refine ⟨w1, w2, d1m, d2m, .unpack d1e e2, .unpack d2e e2, π,
        RStep.ctx_unpack hr1, RStep.ctx_unpack hr2, hdm, ?_, fun l hl => hπ l (hD l hl),
        htr, hal, ?_⟩
      · change Exp.AEq (.unpack d2e e2) (.unpack (d1e.renameLoc π) (e2.renameLoc π))
        rw [he2]; exact Exp.AEq.unpack hde
      · rcases hprov with h | ⟨σ, h1, h2, h3⟩
        · exact Or.inl h
        · exact Or.inr ⟨σ, h1, h2, fun l hl => h3 l (hD l hl)⟩
    | step_unpack => cases inner
  | step_par_left inner ht hni ih =>
    rename_i ts1' m0 e1 ma0 e1' e2 C1 C2
    intro D ts2 mb eb hD hwf hst2
    obtain ⟨hwf_e1, hwf_e2⟩ := Exp.wf_inv_par hwf
    cases hst2 with
    | step_par_join h1 _ => exact (Step.not_isAns inner h1).elim
    | step_par_left inner2 ht2 hni2 =>
      -- SAME side: both step the left branch.  Recurse via the left-branch IH, wrap into `par`.
      -- The outer `C1` annotation reorders allocs between the two paths, but only up to `RReq`
      -- (allocd-set agreement is recorded by the diamond), which `AEq.par` permits.
      have hwf_C1 : C1.WfInHeap m0.heap := by cases hwf with | wf_par h _ _ _ => exact h
      have hwf_C2 : C2.WfInHeap m0.heap := by cases hwf with | wf_par _ h _ _ => exact h
      obtain ⟨w1, w2, d1m, d2m, d1e, d2e, π, hr1, hr2, hdm, hde, hπ, htr, hal, hprov⟩ :=
        ih (D := fun l => m0.heap l ≠ none) (fun _ h => h) hwf_e1 inner2
      -- closing legs' guards: replays of the OTHER input step, transported by provenance
      have hniA : CapabilitySet.Noninterference
          ((C1.growByAllocs ts1').reachability ma0) (C2.reachability ma0) :=
        Step.ni_grow inner hwf_C1 hwf_C2 hni
      have hniB : CapabilitySet.Noninterference
          ((C1.growByAllocs ts2).reachability mb) (C2.reachability mb) :=
        Step.ni_grow inner2 hwf_C1 hwf_C2 hni2
      have htw1 : TraceOk w1 ((C1.growByAllocs ts1').reachability ma0) := by
        rcases hprov with ⟨h1, _⟩ | ⟨σ, h1, _, hσ⟩ <;> rw [h1]
        · exact TraceOk.nil
        · exact traceok_grow inner hwf_C1 (traceok_rename hσ ht2)
      have htw2 : TraceOk w2 ((C1.growByAllocs ts2).reachability mb) := by
        rcases hprov with ⟨_, h2⟩ | ⟨σ, _, h2, hσ⟩ <;> rw [h2]
        · exact TraceOk.nil
        · exact traceok_grow inner2 hwf_C1 (traceok_rename hσ ht)
      have legL1 := RStep.par_left_guarded (e2 := e2) htw1 hniA hr1
      have legL2 := RStep.par_left_guarded (e2 := e2) htw2 hniB hr2
      rw [← CaptureSet.growByAllocs_append] at legL1 legL2
      have he2 : e2.renameLoc π = e2 := Exp.renameLoc_eq_of_wf hwf_e2 hπ
      have hC2 : C2.renameLoc π = C2 := CaptureSet.renameLoc_eq_of_wf hwf_C2 hπ
      have hC1grow : (C1.growByAllocs (ts1' ++ w1)).renameLoc π
          = C1.growByAllocs ((ts1' ++ w1).renameLoc π) := by
        rw [CaptureSet.growByAllocs_renameLoc, CaptureSet.renameLoc_eq_of_wf hwf_C1 hπ]
      have hC2req : CaptureSet.RReq C2 (C2.renameLoc π) := by
        rw [hC2]; exact CaptureSet.RReq.refl C2
      refine ⟨w1, w2, d1m, d2m, _, _, π, legL1, legL2, hdm, ?_, fun l hl => hπ l (hD l hl),
        htr, hal, ?_⟩
      · refine Exp.AEq.par ?_ hC2req hde (Exp.AEq.of_eq he2.symm)
        rw [hC1grow]
        exact CaptureSet.growByAllocs_RReq_of_allocd_iff (fun l => (hal l).symm)
      · rcases hprov with h | ⟨σ, h1, h2, h3⟩
        · exact Or.inl h
        · exact Or.inr ⟨σ, h1, h2, fun l hl => h3 l (hD l hl)⟩
    | step_par_right ht2 hni2 inner2 =>
      rename_i mb0
      -- CROSS: left vs right; close by stepping the OTHER branch on each side.
      have hsep : Trace.Noninterfere ts1' ts2 := traceOk_noninterfere ht ht2 hni
      have hwf_C1 : C1.WfInHeap m0.heap := by cases hwf with | wf_par h _ _ _ => exact h
      have hwf_C2 : C2.WfInHeap m0.heap := by cases hwf with | wf_par _ h _ _ => exact h
      by_cases hclash : ∃ c, m0.lookup c = none ∧ ma0.lookup c ≠ none ∧ mb.lookup c ≠ none
      · -- both branches allocate the same fresh cell `c`: reconverge up to `σ = Equiv.swap c f`.
        obtain ⟨c, hc0, hca, hcb⟩ := hclash
        -- single-cell delta of the LEFT branch pins `c` as its fresh cell (agree off `c`)
        have hagA : ∀ l, l ≠ c → m0.lookup l = ma0.lookup l := by
          rcases Step.delta inner with h | ⟨c0, _, _, hmc0, _, _, hag⟩ | ⟨c0, _, _, hag⟩
          · rw [h]; exact fun l _ => rfl
          · exfalso
            by_cases hc0c : c0 = c
            · subst hc0c; rw [hc0] at hmc0; cases hmc0
            · exact hca (by rw [← hag c (fun h => hc0c h.symm), hc0])
          · by_cases hc0c : c0 = c
            · subst hc0c; exact hag
            · exact absurd (by rw [← hag c (fun h => hc0c h.symm)]; exact hc0) hca
        -- pick `f` fresh in both `ma0` and `mb` (hence in `m0`); rename right's alloc `c ↦ f`
        obtain ⟨f, hfa, hfb⟩ := Memory.exists_fresh_two ma0 mb
        have hfm0 : m0.lookup f = none := by
          by_cases hfc : f = c
          · subst hfc; exact hc0
          · rw [hagA f hfc]; exact hfa
        have hcf : c ≠ f := fun h => by rw [h] at hca; exact hca hfa
        set σ : Equiv.Perm Nat := Equiv.swap c f with hσ
        have hm0σ : m0.renameLoc σ = m0 := Memory.renameLoc_eq_of_fresh hc0 hfm0
        have hσfix : ∀ l, m0.heap l ≠ none → σ l = l := fun l hl =>
          Equiv.swap_apply_of_ne_of_ne (fun he => hl (by rw [he]; exact hc0))
            (fun he => hl (by rw [he]; exact hfm0))
        have hσσ : σ.trans σ = Equiv.refl Nat := by rw [hσ]; exact Equiv.swap_mul_self c f
        -- `σ` (a swap of two `m0`-fresh cells) preserves `m0`-freshness
        have hσfresh : ∀ l, m0.lookup l = none → m0.lookup (σ l) = none := by
          intro l hl
          by_cases hlc : l = c
          · subst hlc; rw [hσ, Equiv.swap_apply_left]; exact hfm0
          · by_cases hlf : l = f
            · subst hlf; rw [hσ, Equiv.swap_apply_right]; exact hc0
            · rw [hσ, Equiv.swap_apply_of_ne_of_ne hlc hlf]; exact hl
        have he1σ : e1.renameLoc σ = e1 := Exp.renameLoc_eq_of_wf hwf_e1 hσfix
        have he2σ : e2.renameLoc σ = e2 := Exp.renameLoc_eq_of_wf hwf_e2 hσfix
        have hC1σ : C1.renameLoc σ = C1 := CaptureSet.renameLoc_eq_of_wf hwf_C1 hσfix
        have hC2σ : C2.renameLoc σ = C2 := CaptureSet.renameLoc_eq_of_wf hwf_C2 hσfix
        have inner2σ : Step (ts2.renameLoc σ) m0 e2 (mb.renameLoc σ) (mb0.renameLoc σ) := by
          have := inner2.renameLoc σ; rwa [hm0σ, he2σ] at this
        -- `inner` (allocs `c`) and `inner2σ` (allocs `f ≠ c`) do not clash → noclash diamond
        have hsepσ : Trace.Noninterfere ts1' (ts2.renameLoc σ) := by
          intro l cm1 cm2 hx1 hx2
          rw [Trace.extTouchesMode_renameLoc] at hx2
          -- `ts2` only ext-touches cells live in `m0`; `σ` fixes those, so realign at `σ.symm l`
          have hpres : (C2.reachability m0).covers cm2 (σ.symm l) :=
            ht2.covers_of_extTouchesMode hx2
          obtain ⟨mu2, hmem2, _⟩ := CapabilitySet.covers_imp_exists_hasmem hpres
          have hlm0 : m0.heap (σ.symm l) ≠ none := CaptureSet.reachability_dom hmem2
          have hfix : σ.symm l = l := by
            have : σ (σ.symm l) = σ.symm l := hσfix _ hlm0
            rw [Equiv.apply_symm_apply] at this; exact this.symm
          rw [hfix] at hx2; exact hsep l cm1 cm2 hx1 hx2
        have hsepσ' : Trace.Noninterfere (ts1'.renameLoc σ) ts2 := by
          intro l cm1 cm2 hx1 hx2
          rw [Trace.extTouchesMode_renameLoc] at hx1
          have hpres : (C2.reachability m0).covers cm2 l := ht2.covers_of_extTouchesMode hx2
          obtain ⟨mu2, hmem2, _⟩ := CapabilitySet.covers_imp_exists_hasmem hpres
          have hlm0 : m0.heap l ≠ none := CaptureSet.reachability_dom hmem2
          have hfix : σ.symm l = l := by rw [hσ, Equiv.symm_swap, ← hσ]; exact hσfix l hlm0
          rw [hfix] at hx1; exact hsep l cm1 cm2 hx1 hx2
        have hncR : ∀ c', m0.lookup c' = none → ma0.lookup c' ≠ none →
            (mb.renameLoc σ).lookup c' = none := by
          intro c' hc'0 hc'a
          -- left allocs only `c`; so `c' = c`; and `(mb.renameLoc σ).lookup c = mb.lookup f = none`
          by_cases hc'c : c' = c
          · subst hc'c
            have hlk : (mb.renameLoc σ).lookup c' = (mb.lookup f).map (Cell.renameLoc σ) := by
              have := Memory.lookup_renameLoc σ mb f
              rwa [hσ, Equiv.swap_apply_right] at this
            rw [hlk, hfb]; rfl
          · exact absurd (by rw [← hagA c' hc'c]; exact hc'0) hc'a
        have hncL : ∀ c', m0.lookup c' = none → (mb.renameLoc σ).lookup c' ≠ none →
            ma0.lookup c' = none := by
          intro c' hc'0 hc'b
          by_contra hc'a
          exact hc'b (hncR c' hc'0 hc'a)
        obtain ⟨md, stepR, stepLσ⟩ :=
          step_step_diamond_noclash inner inner2σ hsepσ hwf_e1 hwf_e2 hncR hncL
        -- rename the LEFT leg back so it starts from `mb` (not `mb.renameLoc σ`)
        have stepL : Step (ts1'.renameLoc σ) mb e1 (md.renameLoc σ) (e1'.renameLoc σ) := by
          have := stepLσ.renameLoc σ
          rw [Memory.renameLoc_comp, hσσ, Memory.renameLoc_id, he1σ] at this
          exact this
        have legR : RStep (ts2.renameLoc σ) ma0 (.par (C1.growByAllocs ts1') C2 e1' e2) md
            (.par (C1.growByAllocs ts1') (C2.growByAllocs (ts2.renameLoc σ)) e1'
              (mb0.renameLoc σ)) :=
          RStep.par_right_guarded
            (traceok_across inner hwf_C2 (traceok_rename hσfix ht2))
            (Step.ni_grow inner hwf_C1 hwf_C2 hni)
            (RStep.step stepR)
        have legL : RStep (ts1'.renameLoc σ) mb (.par C1 (C2.growByAllocs ts2) e1 mb0)
            (md.renameLoc σ)
            (.par (C1.growByAllocs (ts1'.renameLoc σ)) (C2.growByAllocs ts2) (e1'.renameLoc σ) mb0)
            := RStep.par_left_guarded
            (traceok_across inner2 hwf_C1 (traceok_rename hσfix ht))
            ((Step.ni_grow inner2 hwf_C2 hwf_C1 hni2.ni_symm).ni_symm)
            (RStep.step stepL)
        refine ⟨ts2.renameLoc σ, ts1'.renameLoc σ, md, md.renameLoc σ, _, _, σ, legR, legL, rfl, ?_,
          fun l hl => hσfix l (hD l hl), ?_, ?_,
          Or.inr ⟨σ, rfl, rfl, fun l hl => hσfix l (hD l hl)⟩⟩
        · -- `AEq d2e (d1e.renameLoc σ)` holds EXACTLY (σ² = id, C1/C2 fixed)
          apply Exp.AEq.of_eq
          simp only [Exp.renameLoc, CaptureSet.growByAllocs_renameLoc, hC1σ, hC2σ,
            Trace.renameLoc_comp, hσσ, Trace.renameLoc_id, Exp.renameLoc_comp, Exp.renameLoc_id]
        · -- `Trace.Equiv ((ts1' ++ ts2.renameLoc σ).renameLoc σ) (ts2 ++ ts1'.renameLoc σ)`
          rw [Trace.renameLoc_append, Trace.renameLoc_comp, hσσ, Trace.renameLoc_id]
          refine Trace.equiv_comm_of_noninterfere hsepσ' ?_ ?_
          · -- `allocd ts2 l → extSeq l (ts1'.renameLoc σ) = []`
            intro l hl
            change Trace.extSeq l (ts1'.renameLoc σ) = []
            rw [Trace.extSeq_renameLoc]
            refine fresh_not_extSeq ht ?_
            have hlf : m0.lookup l = none := Step.alloc_fresh inner2 hl
            have := hσfresh l hlf
            rwa [hσ, ← Equiv.symm_swap, ← hσ] at this
          · -- `allocd (ts1'.renameLoc σ) l → extSeq l ts2 = []`
            intro l hl
            rw [Trace.allocd_renameLoc] at hl
            have hlm0 : m0.lookup (σ.symm l) = none := Step.alloc_fresh inner hl
            have hl0 : m0.lookup l = none := by
              have hh := hσfresh _ hlm0
              rwa [hσ, Equiv.symm_swap, ← hσ, show σ (σ l) = l from by
                rw [show σ (σ l) = (σ.trans σ) l from rfl, hσσ]; rfl] at hh
            exact fresh_not_extSeq ht2 hl0
        · intro l
          rw [Trace.renameLoc_append, Trace.renameLoc_comp, hσσ, Trace.renameLoc_id,
            Trace.allocd_append, Trace.allocd_append]
          exact or_comm
      · -- no clash: reconverge with `π = id` via `step_step_diamond_noclash`.
        push Not at hclash
        have hncR : ∀ c, m0.lookup c = none → ma0.lookup c ≠ none → mb.lookup c = none :=
          fun c h1 h2 => hclash c h1 h2
        have hncL : ∀ c, m0.lookup c = none → mb.lookup c ≠ none → ma0.lookup c = none :=
          fun c h1 h2 => by by_contra h3; exact h2 (hclash c h1 (h3))
        obtain ⟨md, stepR, stepL⟩ :=
          step_step_diamond_noclash inner inner2 hsep hwf_e1 hwf_e2 hncR hncL
        -- Path 1: from `ea` step the RIGHT branch; Path 2: from `eb` step the LEFT branch.
        have legR : RStep ts2 ma0 (.par (C1.growByAllocs ts1') C2 e1' e2) md
            (.par (C1.growByAllocs ts1') (C2.growByAllocs ts2) e1' mb0) :=
          RStep.par_right_guarded
            (traceok_across inner hwf_C2 ht2)
            (Step.ni_grow inner hwf_C1 hwf_C2 hni)
            (RStep.step stepR)
        have legL : RStep ts1' mb (.par C1 (C2.growByAllocs ts2) e1 mb0) md
            (.par (C1.growByAllocs ts1') (C2.growByAllocs ts2) e1' mb0) :=
          RStep.par_left_guarded
            (traceok_across inner2 hwf_C1 ht)
            ((Step.ni_grow inner2 hwf_C2 hwf_C1 hni2.ni_symm).ni_symm)
            (RStep.step stepL)
        refine ⟨ts2, ts1', md, md, _, _, Equiv.refl Nat, legR, legL,
          (Memory.renameLoc_id).symm, Exp.AEq.of_eq (Exp.renameLoc_id).symm, fun _ _ => rfl,
          ?_, ?_,
          Or.inr ⟨Equiv.refl Nat, (Trace.renameLoc_id).symm, (Trace.renameLoc_id).symm,
            fun _ _ => rfl⟩⟩
        · -- `(ts1' ++ ts2)` ≈ `(ts2 ++ ts1')` (commutation of separated traces)
          rw [Trace.renameLoc_id]
          refine Trace.equiv_comm_of_noninterfere hsep ?_ ?_
          · intro l hl
            exact fresh_not_extSeq ht (Step.alloc_fresh inner2 hl)
          · intro l hl
            exact fresh_not_extSeq ht2 (Step.alloc_fresh inner hl)
        · intro l
          rw [Trace.renameLoc_id, Trace.allocd_append, Trace.allocd_append]; exact or_comm
  | step_par_right ht hni inner ih =>
    -- Symmetric to `step_par_left` (mirror left↔right): the RIGHT branch steps.
    rename_i ts1' m0 e2 ma0 e2' C1 C2 e1
    intro D ts2 mb eb hD hwf hst2
    obtain ⟨hwf_e1, hwf_e2⟩ := Exp.wf_inv_par hwf
    cases hst2 with
    | step_par_join _ h2 => exact (Step.not_isAns inner h2).elim
    | step_par_right ht2 hni2 inner2 =>
      -- SAME side: both step the right branch.
      have hwf_C1 : C1.WfInHeap m0.heap := by cases hwf with | wf_par h _ _ _ => exact h
      have hwf_C2 : C2.WfInHeap m0.heap := by cases hwf with | wf_par _ h _ _ => exact h
      obtain ⟨w1, w2, d1m, d2m, d1e, d2e, π, hr1, hr2, hdm, hde, hπ, htr, hal, hprov⟩ :=
        ih (D := fun l => m0.heap l ≠ none) (fun _ h => h) hwf_e2 inner2
      -- closing legs' guards: replays of the OTHER input step, transported by provenance
      have hniA : CapabilitySet.Noninterference
          (C1.reachability ma0) ((C2.growByAllocs ts1').reachability ma0) :=
        (Step.ni_grow inner hwf_C2 hwf_C1 hni.ni_symm).ni_symm
      have hniB : CapabilitySet.Noninterference
          (C1.reachability mb) ((C2.growByAllocs ts2).reachability mb) :=
        (Step.ni_grow inner2 hwf_C2 hwf_C1 hni2.ni_symm).ni_symm
      have htw1 : TraceOk w1 ((C2.growByAllocs ts1').reachability ma0) := by
        rcases hprov with ⟨h1, _⟩ | ⟨σ, h1, _, hσ⟩ <;> rw [h1]
        · exact TraceOk.nil
        · exact traceok_grow inner hwf_C2 (traceok_rename hσ ht2)
      have htw2 : TraceOk w2 ((C2.growByAllocs ts2).reachability mb) := by
        rcases hprov with ⟨_, h2⟩ | ⟨σ, _, h2, hσ⟩ <;> rw [h2]
        · exact TraceOk.nil
        · exact traceok_grow inner2 hwf_C2 (traceok_rename hσ ht)
      have legR1 := RStep.par_right_guarded (e1 := e1) htw1 hniA hr1
      have legR2 := RStep.par_right_guarded (e1 := e1) htw2 hniB hr2
      rw [← CaptureSet.growByAllocs_append] at legR1 legR2
      have he1 : e1.renameLoc π = e1 := Exp.renameLoc_eq_of_wf hwf_e1 hπ
      have hC1 : C1.renameLoc π = C1 := CaptureSet.renameLoc_eq_of_wf hwf_C1 hπ
      have hC2grow : (C2.growByAllocs (ts1' ++ w1)).renameLoc π
          = C2.growByAllocs ((ts1' ++ w1).renameLoc π) := by
        rw [CaptureSet.growByAllocs_renameLoc, CaptureSet.renameLoc_eq_of_wf hwf_C2 hπ]
      have hC1req : CaptureSet.RReq C1 (C1.renameLoc π) := by
        rw [hC1]; exact CaptureSet.RReq.refl C1
      refine ⟨w1, w2, d1m, d2m, _, _, π, legR1, legR2, hdm, ?_, fun l hl => hπ l (hD l hl),
        htr, hal, ?_⟩
      · refine Exp.AEq.par hC1req ?_ (Exp.AEq.of_eq he1.symm) hde
        rw [hC2grow]
        exact CaptureSet.growByAllocs_RReq_of_allocd_iff (fun l => (hal l).symm)
      · rcases hprov with h | ⟨σ, h1, h2, h3⟩
        · exact Or.inl h
        · exact Or.inr ⟨σ, h1, h2, fun l hl => h3 l (hD l hl)⟩
    | step_par_left inner2 ht2 hni2 =>
      rename_i mb0
      -- CROSS: right vs left; close by stepping the OTHER branch on each side.
      have hsep : Trace.Noninterfere ts1' ts2 := traceOk_noninterfere ht ht2 hni.ni_symm
      have hwf_C1 : C1.WfInHeap m0.heap := by cases hwf with | wf_par h _ _ _ => exact h
      have hwf_C2 : C2.WfInHeap m0.heap := by cases hwf with | wf_par _ h _ _ => exact h
      by_cases hclash : ∃ c, m0.lookup c = none ∧ ma0.lookup c ≠ none ∧ mb.lookup c ≠ none
      · -- both branches allocate the same fresh cell `c`: reconverge up to `σ = Equiv.swap c f`.
        obtain ⟨c, hc0, hca, hcb⟩ := hclash
        have hagA : ∀ l, l ≠ c → m0.lookup l = ma0.lookup l := by
          rcases Step.delta inner with h | ⟨c0, _, _, hmc0, _, _, hag⟩ | ⟨c0, _, _, hag⟩
          · rw [h]; exact fun l _ => rfl
          · exfalso
            by_cases hc0c : c0 = c
            · subst hc0c; rw [hc0] at hmc0; cases hmc0
            · exact hca (by rw [← hag c (fun h => hc0c h.symm), hc0])
          · by_cases hc0c : c0 = c
            · subst hc0c; exact hag
            · exact absurd (by rw [← hag c (fun h => hc0c h.symm)]; exact hc0) hca
        obtain ⟨f, hfa, hfb⟩ := Memory.exists_fresh_two ma0 mb
        have hfm0 : m0.lookup f = none := by
          by_cases hfc : f = c
          · subst hfc; exact hc0
          · rw [hagA f hfc]; exact hfa
        have hcf : c ≠ f := fun h => by rw [h] at hca; exact hca hfa
        set σ : Equiv.Perm Nat := Equiv.swap c f with hσ
        have hm0σ : m0.renameLoc σ = m0 := Memory.renameLoc_eq_of_fresh hc0 hfm0
        have hσfix : ∀ l, m0.heap l ≠ none → σ l = l := fun l hl =>
          Equiv.swap_apply_of_ne_of_ne (fun he => hl (by rw [he]; exact hc0))
            (fun he => hl (by rw [he]; exact hfm0))
        have hσσ : σ.trans σ = Equiv.refl Nat := by rw [hσ]; exact Equiv.swap_mul_self c f
        have hσfresh : ∀ l, m0.lookup l = none → m0.lookup (σ l) = none := by
          intro l hl
          by_cases hlc : l = c
          · subst hlc; rw [hσ, Equiv.swap_apply_left]; exact hfm0
          · by_cases hlf : l = f
            · subst hlf; rw [hσ, Equiv.swap_apply_right]; exact hc0
            · rw [hσ, Equiv.swap_apply_of_ne_of_ne hlc hlf]; exact hl
        have he1σ : e1.renameLoc σ = e1 := Exp.renameLoc_eq_of_wf hwf_e1 hσfix
        have he2σ : e2.renameLoc σ = e2 := Exp.renameLoc_eq_of_wf hwf_e2 hσfix
        have hC1σ : C1.renameLoc σ = C1 := CaptureSet.renameLoc_eq_of_wf hwf_C1 hσfix
        have hC2σ : C2.renameLoc σ = C2 := CaptureSet.renameLoc_eq_of_wf hwf_C2 hσfix
        have inner2σ : Step (ts2.renameLoc σ) m0 e1 (mb.renameLoc σ) (mb0.renameLoc σ) := by
          have := inner2.renameLoc σ; rwa [hm0σ, he1σ] at this
        have hsepσ : Trace.Noninterfere ts1' (ts2.renameLoc σ) := by
          intro l cm1 cm2 hx1 hx2
          rw [Trace.extTouchesMode_renameLoc] at hx2
          have hpres : (C1.reachability m0).covers cm2 (σ.symm l) :=
            ht2.covers_of_extTouchesMode hx2
          obtain ⟨mu2, hmem2, _⟩ := CapabilitySet.covers_imp_exists_hasmem hpres
          have hlm0 : m0.heap (σ.symm l) ≠ none := CaptureSet.reachability_dom hmem2
          have hfix : σ.symm l = l := by
            have : σ (σ.symm l) = σ.symm l := hσfix _ hlm0
            rw [Equiv.apply_symm_apply] at this; exact this.symm
          rw [hfix] at hx2; exact hsep l cm1 cm2 hx1 hx2
        have hsepσ' : Trace.Noninterfere (ts1'.renameLoc σ) ts2 := by
          intro l cm1 cm2 hx1 hx2
          rw [Trace.extTouchesMode_renameLoc] at hx1
          have hpres : (C1.reachability m0).covers cm2 l := ht2.covers_of_extTouchesMode hx2
          obtain ⟨mu2, hmem2, _⟩ := CapabilitySet.covers_imp_exists_hasmem hpres
          have hlm0 : m0.heap l ≠ none := CaptureSet.reachability_dom hmem2
          have hfix : σ.symm l = l := by rw [hσ, Equiv.symm_swap, ← hσ]; exact hσfix l hlm0
          rw [hfix] at hx1; exact hsep l cm1 cm2 hx1 hx2
        have hncR : ∀ c', m0.lookup c' = none → ma0.lookup c' ≠ none →
            (mb.renameLoc σ).lookup c' = none := by
          intro c' hc'0 hc'a
          by_cases hc'c : c' = c
          · subst hc'c
            have hlk : (mb.renameLoc σ).lookup c' = (mb.lookup f).map (Cell.renameLoc σ) := by
              have := Memory.lookup_renameLoc σ mb f
              rwa [hσ, Equiv.swap_apply_right] at this
            rw [hlk, hfb]; rfl
          · exact absurd (by rw [← hagA c' hc'c]; exact hc'0) hc'a
        have hncL : ∀ c', m0.lookup c' = none → (mb.renameLoc σ).lookup c' ≠ none →
            ma0.lookup c' = none := by
          intro c' hc'0 hc'b
          by_contra hc'a
          exact hc'b (hncR c' hc'0 hc'a)
        obtain ⟨md, stepR, stepLσ⟩ :=
          step_step_diamond_noclash inner inner2σ hsepσ hwf_e2 hwf_e1 hncR hncL
        have stepL : Step (ts1'.renameLoc σ) mb e2 (md.renameLoc σ) (e2'.renameLoc σ) := by
          have := stepLσ.renameLoc σ
          rw [Memory.renameLoc_comp, hσσ, Memory.renameLoc_id, he2σ] at this
          exact this
        have legR : RStep (ts2.renameLoc σ) ma0 (.par C1 (C2.growByAllocs ts1') e1 e2') md
            (.par (C1.growByAllocs (ts2.renameLoc σ)) (C2.growByAllocs ts1') (mb0.renameLoc σ)
              e2') :=
          RStep.par_left_guarded
            (traceok_across inner hwf_C1 (traceok_rename hσfix ht2))
            ((Step.ni_grow inner hwf_C2 hwf_C1 hni.ni_symm).ni_symm)
            (RStep.step stepR)
        have legL : RStep (ts1'.renameLoc σ) mb (.par (C1.growByAllocs ts2) C2 mb0 e2)
            (md.renameLoc σ)
            (.par (C1.growByAllocs ts2) (C2.growByAllocs (ts1'.renameLoc σ)) mb0 (e2'.renameLoc σ))
            := RStep.par_right_guarded
            (traceok_across inner2 hwf_C2 (traceok_rename hσfix ht))
            (Step.ni_grow inner2 hwf_C1 hwf_C2 hni2)
            (RStep.step stepL)
        refine ⟨ts2.renameLoc σ, ts1'.renameLoc σ, md, md.renameLoc σ, _, _, σ, legR, legL, rfl, ?_,
          fun l hl => hσfix l (hD l hl), ?_, ?_,
          Or.inr ⟨σ, rfl, rfl, fun l hl => hσfix l (hD l hl)⟩⟩
        · apply Exp.AEq.of_eq
          simp only [Exp.renameLoc, CaptureSet.growByAllocs_renameLoc, hC1σ, hC2σ,
            Trace.renameLoc_comp, hσσ, Trace.renameLoc_id, Exp.renameLoc_comp, Exp.renameLoc_id]
        · rw [Trace.renameLoc_append, Trace.renameLoc_comp, hσσ, Trace.renameLoc_id]
          refine Trace.equiv_comm_of_noninterfere hsepσ' ?_ ?_
          · intro l hl
            change Trace.extSeq l (ts1'.renameLoc σ) = []
            rw [Trace.extSeq_renameLoc]
            refine fresh_not_extSeq ht ?_
            have hlf : m0.lookup l = none := Step.alloc_fresh inner2 hl
            have := hσfresh l hlf
            rwa [hσ, ← Equiv.symm_swap, ← hσ] at this
          · intro l hl
            rw [Trace.allocd_renameLoc] at hl
            have hlm0 : m0.lookup (σ.symm l) = none := Step.alloc_fresh inner hl
            have hl0 : m0.lookup l = none := by
              have hh := hσfresh _ hlm0
              rwa [hσ, Equiv.symm_swap, ← hσ, show σ (σ l) = l from by
                rw [show σ (σ l) = (σ.trans σ) l from rfl, hσσ]; rfl] at hh
            exact fresh_not_extSeq ht2 hl0
        · intro l
          rw [Trace.renameLoc_append, Trace.renameLoc_comp, hσσ, Trace.renameLoc_id,
            Trace.allocd_append, Trace.allocd_append]
          exact or_comm
      · -- no clash: reconverge with `π = id` via `step_step_diamond_noclash`.
        push Not at hclash
        have hncR : ∀ c, m0.lookup c = none → ma0.lookup c ≠ none → mb.lookup c = none :=
          fun c h1 h2 => hclash c h1 h2
        have hncL : ∀ c, m0.lookup c = none → mb.lookup c ≠ none → ma0.lookup c = none :=
          fun c h1 h2 => by by_contra h3; exact h2 (hclash c h1 (h3))
        obtain ⟨md, stepR, stepL⟩ :=
          step_step_diamond_noclash inner inner2 hsep hwf_e2 hwf_e1 hncR hncL
        have legR : RStep ts2 ma0 (.par C1 (C2.growByAllocs ts1') e1 e2') md
            (.par (C1.growByAllocs ts2) (C2.growByAllocs ts1') mb0 e2') :=
          RStep.par_left_guarded
            (traceok_across inner hwf_C1 ht2)
            ((Step.ni_grow inner hwf_C2 hwf_C1 hni.ni_symm).ni_symm)
            (RStep.step stepR)
        have legL : RStep ts1' mb (.par (C1.growByAllocs ts2) C2 mb0 e2) md
            (.par (C1.growByAllocs ts2) (C2.growByAllocs ts1') mb0 e2') :=
          RStep.par_right_guarded
            (traceok_across inner2 hwf_C2 ht)
            (Step.ni_grow inner2 hwf_C1 hwf_C2 hni2)
            (RStep.step stepL)
        refine ⟨ts2, ts1', md, md, _, _, Equiv.refl Nat, legR, legL,
          (Memory.renameLoc_id).symm, Exp.AEq.of_eq (Exp.renameLoc_id).symm, fun _ _ => rfl,
          ?_, ?_,
          Or.inr ⟨Equiv.refl Nat, (Trace.renameLoc_id).symm, (Trace.renameLoc_id).symm,
            fun _ _ => rfl⟩⟩
        · rw [Trace.renameLoc_id]
          refine Trace.equiv_comm_of_noninterfere hsep ?_ ?_
          · intro l hl
            exact fresh_not_extSeq ht (Step.alloc_fresh inner2 hl)
          · intro l hl
            exact fresh_not_extSeq ht2 (Step.alloc_fresh inner hl)
        · intro l
          rw [Trace.renameLoc_id, Trace.allocd_append, Trace.allocd_append]; exact or_comm
  | step_par_join h1 h2 =>
    intro D ts2 mb eb hD hwf hst2
    cases hst2 with
    | step_par_left inner _ _ => exact (Step.not_isAns inner h1).elim
    | step_par_right _ _ inner => exact (Step.not_isAns inner h2).elim
    | step_par_join h1' h2' => exact Diamond.det rfl rfl rfl
  | step_rename =>
    intro D ts2 mb eb hD hwf hst2
    cases hst2 with
    | step_ctx_letin inner => cases inner
    | step_rename => exact Diamond.det rfl rfl rfl
    | step_lift hv2 _ _ => cases hv2
  | @step_lift v m0 e l hv hwf_v hfresh =>
    intro D ts2 mb eb hD hwf hst2
    obtain ⟨_, hwf_e⟩ := Exp.wf_inv_letin hwf
    cases hst2 with
    | @step_lift _ _ _ l2 hv2 hwf_v2 hfresh2 =>
      have hAfix : ∀ l', m0.heap l' ≠ none → Equiv.swap l l2 l' = l' := fun l' hl' =>
        Equiv.swap_apply_of_ne_of_ne (fun he => hl' (by rw [he]; exact hfresh))
          (fun he => hl' (by rw [he]; exact hfresh2))
      refine ⟨[], [], _, _, _, _, Equiv.swap l l2, RStep.refl, RStep.refl, ?_, ?_, ?_, ?_, ?_,
        Or.inl ⟨rfl, rfl⟩⟩
      · apply Memory.eq_of_heap
        change m0.heap.extend l2 ⟨v, hv2, compute_reachability m0.heap v hv2⟩
          = (m0.heap.extend l ⟨v, hv, compute_reachability m0.heap v hv⟩).renameLoc
              (Equiv.swap l l2)
        rw [Heap.extend_renameLoc, Memory.heap_renameLoc_eq_of_fresh hfresh hfresh2,
          Equiv.swap_apply_left]
        congr 1
        apply HeapVal.eq_of
        · exact (Exp.renameLoc_eq_of_wf hwf_v hAfix).symm
        · change compute_reachability m0.heap v hv2
            = (compute_reachability m0.heap v hv).renameLoc (Equiv.swap l l2)
          rw [← compute_reachability_renameLoc, Memory.heap_renameLoc_eq_of_fresh hfresh hfresh2]
          simp only [Exp.renameLoc_eq_of_wf hwf_v hAfix]
      · apply Exp.AEq.of_eq
        rw [Exp.openVar_renameLoc, Exp.renameLoc_eq_of_wf hwf_e hAfix, Equiv.swap_apply_left]
      · exact fun l' hl' => Equiv.swap_apply_of_ne_of_ne
          (fun he => hD l' hl' (by rw [he]; exact hfresh))
          (fun he => hD l' hl' (by rw [he]; exact hfresh2))
      · exact Trace.Equiv.refl _
      · exact fun _ => Iff.rfl
    | step_ctx_letin inner =>
      exact (Step.not_isAns inner (Exp.IsAns.is_val (Exp.isVal_of_isSimpleVal hv))).elim
    | step_rename => cases hv
  | step_unpack =>
    intro D ts2 mb eb hD hwf hst2
    cases hst2 with
    | step_ctx_unpack inner => cases inner
    | step_unpack => exact Diamond.det rfl rfl rfl

/-- **Strip lemma (semi-confluence).**  A single step and a run from the same well-formed
  config reconverge.  Proven by induction on the run, closing each prefix tile with
  `local_diamond` and recursing with the IH on the run's tail.  `D` and the first-path data
  are universally quantified so the IH applies to a fresh step out of the run's interior. -/
theorem strip {m mc : Memory} {e ec : Exp {}} {t2 : Trace}
    (hr2 : Reduce t2 m e mc ec) :
    ∀ {D : Nat → Prop} {ts : Trace} {m' : Memory} {e' : Exp {}},
      (∀ l, D l → m.heap l ≠ none) → Exp.WfInHeap e m.heap →
      Step ts m e m' e' → Recon D ts m' e' t2 mc ec := by
  induction hr2 with
  | refl =>
    intro D ts m' e' _ _ h1
    refine ⟨[], ts, m', m', e', e', Equiv.refl Nat, Reduce.refl, ?_,
      (Memory.renameLoc_id).symm, Exp.AEq.of_eq (Exp.renameLoc_id).symm, fun l _ => rfl, ?_, ?_⟩
    · have h := Reduce.step h1 Reduce.refl; rwa [List.append_nil] at h
    · simp only [List.append_nil, List.nil_append, Trace.renameLoc_id]; exact Trace.Equiv.refl _
    · simp only [List.append_nil, List.nil_append, Trace.renameLoc_id]; exact fun _ => trivial
  | @step tk m1 e1 mk ek tr mfin efin k1 krest ih =>
    intro D ts m' e' hD hwf h1
    obtain ⟨w1, w2, d1m, d2m, d1e, d2e, π0, hrs1, hrs2, hd2m, hd2e, hπ0D, hLDtr, hLDal, _⟩ :=
      local_diamond h1 hD hwf k1
    have hwfk : Exp.WfInHeap ek mk.heap := Step.preserves_wf k1 hwf
    cases hrs2 with
    | refl =>
      have hmk : mk.renameLoc π0.symm = d1m := by rw [hd2m, Memory.renameLoc_self_symm]
      -- transport `krest` (renamed by `π0.symm`) across `AEq (ek.renameLoc π0.symm) d1e`
      have haek : Exp.AEq (ek.renameLoc π0.symm) d1e := by
        have := hd2e.renameLoc π0.symm
        rwa [Exp.renameLoc_self_symm] at this
      have hkr0 := Reduce.renameLoc krest π0.symm
      rw [hmk] at hkr0
      obtain ⟨efin', hkr, haefin⟩ := Reduce.aeq_sim haek hkr0
      have hp1 : Reduce (w1 ++ tr.renameLoc π0.symm) m' e'
          (mfin.renameLoc π0.symm) efin' := reduce_trans hrs1.toReduce hkr
      simp only [List.append_nil] at hLDtr hLDal
      have eqL : (ts ++ (w1 ++ tr.renameLoc π0.symm)).renameLoc π0
          = (ts ++ w1).renameLoc π0 ++ tr := by
        rw [← List.append_assoc, Trace.renameLoc_append, Trace.renameLoc_symm_self]
      refine ⟨w1 ++ tr.renameLoc π0.symm, [], mfin.renameLoc π0.symm, mfin,
        efin', efin, π0, hp1, Reduce.refl,
        (Memory.renameLoc_symm_self).symm, ?_, hπ0D, ?_, ?_⟩
      · -- `AEq efin (efin'.renameLoc π0)`
        have h := haefin.symm.renameLoc π0
        rw [Exp.renameLoc_symm_self] at h
        exact h.symm
      · rw [eqL, List.append_nil]; exact Trace.Equiv.append_right_congr hLDtr hLDal
      · rw [eqL, List.append_nil]; exact Trace.allocd_cong_right hLDal
    | step hk2 =>
      obtain ⟨u1, u2, g1m, g2m, g1e, g2e, π1, hu1, hu2, hg2m, hg2e, hπ1D, hIHtr, hIHal⟩ :=
        ih (D := fun l => mk.heap l ≠ none) (fun _ h => h) hwfk hk2
      have hd1m : d2m.renameLoc π0.symm = d1m := by rw [hd2m, Memory.renameLoc_self_symm]
      have had2e : Exp.AEq (d2e.renameLoc π0.symm) d1e := by
        have := hd2e.renameLoc π0.symm
        rwa [Exp.renameLoc_self_symm] at this
      have hu1r := Reduce.renameLoc hu1 π0.symm
      rw [hd1m] at hu1r
      obtain ⟨g1e', hu1', hg1e'⟩ := Reduce.aeq_sim had2e hu1r
      have hp1 : Reduce (w1 ++ u1.renameLoc π0.symm) m' e'
          (g1m.renameLoc π0.symm) g1e' := reduce_trans hrs1.toReduce hu1'
      have htk : Trace.renameLoc π1 tk = tk := Step.trace_renameLoc_eq k1 hπ1D
      have eqL : (ts ++ (w1 ++ u1.renameLoc π0.symm)).renameLoc (π0.trans π1)
          = ((ts ++ w1).renameLoc π0 ++ u1).renameLoc π1 := by
        rw [← Trace.renameLoc_comp, ← List.append_assoc, Trace.renameLoc_append,
          Trace.renameLoc_symm_self]
      have step2 : ((tk ++ w2) ++ u1).renameLoc π1 = tk ++ (w2 ++ u1).renameLoc π1 := by
        rw [Trace.renameLoc_append, Trace.renameLoc_append, htk, List.append_assoc,
          ← Trace.renameLoc_append]
      refine ⟨w1 ++ u1.renameLoc π0.symm, u2, g1m.renameLoc π0.symm, g2m,
        g1e', g2e, π0.trans π1, hp1, hu2, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hg2m, Memory.renameLoc_comp, ← Equiv.trans_assoc, Equiv.symm_trans_self,
          Equiv.refl_trans]
      · -- `AEq g2e (g1e'.renameLoc (π0.trans π1))`
        have hstep0 : Exp.AEq (g1e'.renameLoc π0) g1e := by
          have := hg1e'.symm.renameLoc π0
          rwa [Exp.renameLoc_symm_self] at this
        have hstep1 : Exp.AEq (g1e'.renameLoc (π0.trans π1)) (g1e.renameLoc π1) := by
          have := hstep0.renameLoc π1
          rwa [Exp.renameLoc_comp] at this
        exact hg2e.trans hstep1.symm
      · intro l hl
        have hmkl : mk.heap l ≠ none := fun hc =>
          hD l hl (Heap.none_of_subsumes_none (Step.subsumes k1) hc)
        rw [Equiv.trans_apply, hπ0D l hl, hπ1D l hmkl]
      · rw [eqL, List.append_assoc]
        refine (Trace.Equiv.renameLoc (Trace.Equiv.append_right_congr hLDtr hLDal) π1).trans ?_
        rw [step2]
        exact Trace.Equiv.append_left_congr hIHtr
      · rw [eqL, List.append_assoc]
        refine Trace.allocd_cong_trans
          (Trace.allocd_cong_renameLoc (Trace.allocd_cong_right hLDal) π1) ?_
        rw [step2]
        exact Trace.allocd_cong_left hIHal

/-- **Confluence engine (run vs run).**  Induction on the first run, closing the leading tile
  with `strip` and recursing with the IH on the run's tail; the protected domain and second-path
  data are universally quantified so the IH applies to the strip-produced sub-run. -/
theorem confluence_aux {m m1 : Memory} {e e1 : Exp {}} {t1 : Trace}
    (hr1 : Reduce t1 m e m1 e1) :
    ∀ {D : Nat → Prop} {t2 : Trace} {m2 : Memory} {e2 : Exp {}},
      (∀ l, D l → m.heap l ≠ none) → Exp.WfInHeap e m.heap →
      Reduce t2 m e m2 e2 → Recon D t1 m1 e1 t2 m2 e2 := by
  induction hr1 with
  | refl =>
    intro D t2 m2 e2 _ _ hr2
    refine ⟨t2, [], m2, m2, e2, e2, Equiv.refl Nat, hr2, Reduce.refl,
      (Memory.renameLoc_id).symm, Exp.AEq.of_eq (Exp.renameLoc_id).symm, fun _ _ => rfl, ?_, ?_⟩
    · simp only [List.nil_append, List.append_nil, Trace.renameLoc_id]; exact Trace.Equiv.refl _
    · simp only [List.nil_append, List.append_nil, Trace.renameLoc_id]; exact fun _ => trivial
  | @step ts ma ea mk ek trest m1fin e1fin h1 hrest ih =>
    intro D t2 m2 e2 hD hwf hr2
    obtain ⟨a1, a2, p1m, p2m, p1e, p2e, ρ, ha1, ha2, hp2m, hp2e, hρD, hStrTr, hStrAl⟩ :=
      strip hr2 hD hwf h1
    have hwfk : Exp.WfInHeap ek mk.heap := Step.preserves_wf h1 hwf
    obtain ⟨b1, b2, q1m, q2m, q1e, q2e, σ, hb1, hb2, hq2m, hq2e, hσD, hIHTr, hIHAl⟩ :=
      ih (D := fun l => mk.heap l ≠ none) (fun _ h => h) hwfk ha1
    have hb2r := Reduce.renameLoc hb2 ρ
    rw [← hp2m] at hb2r
    -- transport `b2`-run (renamed by ρ) across `AEq (p1e.renameLoc ρ) p2e`
    obtain ⟨q2e', hb2', haq2e⟩ := Reduce.aeq_sim hp2e.symm hb2r
    have hp2 : Reduce (a2 ++ b2.renameLoc ρ) m2 e2 (q2m.renameLoc ρ) q2e' :=
      reduce_trans ha2 hb2'
    have hts : Trace.renameLoc σ ts = ts := Step.trace_renameLoc_eq h1 hσD
    have eqL : (ts ++ trest ++ b1).renameLoc (σ.trans ρ)
        = (ts ++ (trest ++ b1).renameLoc σ).renameLoc ρ := by
      rw [← Trace.renameLoc_comp, List.append_assoc, Trace.renameLoc_append, hts]
    have eqRHS : t2 ++ (a2 ++ b2.renameLoc ρ) = (t2 ++ a2) ++ b2.renameLoc ρ :=
      (List.append_assoc t2 a2 (b2.renameLoc ρ)).symm
    have eqMid : (ts ++ (a1 ++ b2)).renameLoc ρ = (ts ++ a1).renameLoc ρ ++ b2.renameLoc ρ := by
      simp only [Trace.renameLoc_append, List.append_assoc]
    refine ⟨b1, a2 ++ b2.renameLoc ρ, q1m, q2m.renameLoc ρ, q1e, q2e',
      σ.trans ρ, hb1, hp2, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hq2m, Memory.renameLoc_comp]
    · -- `AEq q2e' (q1e.renameLoc (σ.trans ρ))`
      have hcomp : Exp.AEq (q2e.renameLoc ρ) (q1e.renameLoc (σ.trans ρ)) := by
        have := hq2e.renameLoc ρ
        rwa [Exp.renameLoc_comp] at this
      exact haq2e.symm.trans hcomp
    · intro l hl
      have hmkl : mk.heap l ≠ none := fun hc =>
        hD l hl (Heap.none_of_subsumes_none (Step.subsumes h1) hc)
      rw [Equiv.trans_apply, hσD l hmkl, hρD l hl]
    · rw [eqL, eqRHS]
      refine Trace.Equiv.trans ?_ (Trace.Equiv.append_right_congr hStrTr hStrAl)
      rw [← eqMid]
      exact Trace.Equiv.renameLoc (Trace.Equiv.append_left_congr hIHTr) ρ
    · rw [eqL, eqRHS]
      refine Trace.allocd_cong_trans ?_ (Trace.allocd_cong_right hStrAl)
      rw [← eqMid]
      exact Trace.allocd_cong_renameLoc (Trace.allocd_cong_left hIHAl) ρ

/-- **Confluence (Church–Rosser) up to `Trace.Equiv`, a location renaming, and annotation
  equivalence.**  From a well-formed configuration `(m, e)`, any two interleaving reductions
  `Reduce t1 m e m1 e1` and `Reduce t2 m e m2 e2` have continuations `s1`, `s2` to a common reduct
  that agrees up to a single location renaming `π` on the memory exactly and on the expression up to
  `Exp.AEq` (reachability-equivalence of the order-sensitive `par` annotations), and whose combined
  external traces agree (Mazurkiewicz `Trace.Equiv`) after renaming by `π`.

  CARRIER-FREE: no `Safe` hypothesis — the separation content that commutes independent
  `par` steps is carried by the interleaving `Step`'s own guards. -/
theorem confluence {m m1 m2 : Memory} {e e1 e2 : Exp {}} {t1 t2 : Trace}
    (hwf : Exp.WfInHeap e m.heap)
    (hr1 : Reduce t1 m e m1 e1) (hr2 : Reduce t2 m e m2 e2) :
    ∃ (s1 s2 : Trace) (mf1 mf2 : Memory) (ef1 ef2 : Exp {}) (π : Equiv.Perm Nat),
      Reduce s1 m1 e1 mf1 ef1 ∧
      Reduce s2 m2 e2 mf2 ef2 ∧
      mf2 = mf1.renameLoc π ∧
      Exp.AEq ef2 (ef1.renameLoc π) ∧
      Trace.Equiv ((t1 ++ s1).renameLoc π) (t2 ++ s2) := by
  obtain ⟨s1, s2, mf1, mf2, ef1, ef2, π, hp1, hp2, hm, he, _, htr, _⟩ :=
    confluence_aux hr1 (D := fun l => m.heap l ≠ none) (fun _ h => h) hwf hr2
  exact ⟨s1, s2, mf1, mf2, ef1, ef2, π, hp1, hp2, hm, he, htr⟩

end CoreCapybara
