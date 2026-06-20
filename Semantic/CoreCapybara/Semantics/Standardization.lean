import Semantic.CoreCapybara.Semantics.Props

/-! # Standardization (theorem B)

  The standardization theorem relates the GENUINE interleaving `Step` to the
  SEQUENTIAL `SeqStep`: every interleaving run to an answer is matched by a sequential
  run reaching the **identical** final memory and answer, the only difference being a
  reordering of the trace.

  Why equality (not an isomorphism) of the final memory/answer: the local diamond
  `BigStep.step_run_commute` has an EXACT meet — commuting a step past a separated run
  reaches the *same* memory and keeps each step's chosen fresh-allocation name (its
  trace `[.alloc l]` is preserved verbatim).  So this is a confluence situation:
  separated `par` ⇒ unique normal form ⇒ every schedule of a given run reaches the
  same `(mf, a)`.  Only the trace genuinely differs, and only up to `Trace.Equiv`:

  * `Trace.Equiv` — the two traces record the same EXTERNAL access/drop *sequence* at
    every location (Mazurkiewicz trace equivalence with locations as independent
    objects: independent touches commute, same-location order is preserved).
    Restricting to *external* touches makes it robust to the differing internal
    allocation ORDER (a self-allocated cell is private, never externally touched).

  This file defines `Trace.Equiv` and states `standardization` (proof on top of the
  diamond `BigStep.step_run_commute`, fed by the separation carrier `Safe` via
  `Safe.par_noninterfere`). -/

namespace CoreCapybara

/-! ## Trace equivalence

  Two traces are equivalent when, at EVERY location, they record the same external
  access/drop *sequence* — the mode-carrying, order-preserving refinement of the
  existing `Trace.extTouchesFromMode` (existence) / `Trace.Noninterfere`.  This is
  Mazurkiewicz trace equivalence: touches to *different* locations are independent
  (commute), touches to the *same* location keep their order.

  Restricting to *external* touches (a self-allocated cell — its index in the running
  set `A` — is private and contributes nothing) makes the relation robust to
  fresh-cell renaming, so it carries no location bijection and is orthogonal to
  `Memory.Iso`.  It still transports the immutability facts: for an external (e.g.
  platform) cell `l`, `.access .epsilon ∈ extSeq l t ↔ access .epsilon l ∈ t`. -/

/-- The external access/drop **sequence** to `l` in `t`, given the running set `A` of
  locations already allocated within `t`.  Each external read/write contributes its
  `.access mu` mode and each external drop a `.drop`, in order; an `alloc` extends `A`
  (so a self-allocated cell is thereafter internal).  This is the order-recording
  refinement of `Trace.extTouchesFromMode`. -/
def Trace.extSeqFrom (A : List Nat) (l : Nat) : Trace → List CapMode
| []                   => []
| (.alloc l' :: t)     => Trace.extSeqFrom (l' :: A) l t
| (.access mu l' :: t) =>
    if l = l' ∧ l ∉ A then .access mu :: Trace.extSeqFrom A l t
    else Trace.extSeqFrom A l t
| (.dealloc l' :: t)   =>
    if l = l' ∧ l ∉ A then .drop :: Trace.extSeqFrom A l t
    else Trace.extSeqFrom A l t

/-- The external access/drop sequence to `l` in a whole trace (nothing allocated yet). -/
def Trace.extSeq (l : Nat) (t : Trace) : List CapMode := Trace.extSeqFrom [] l t

/-- **Trace equivalence.**  `t1` and `t2` have the same external access/drop sequence
  at every location.  An equivalence relation (it is per-location equality of
  sequences), and it subsumes "same external (location, mode) touch set". -/
def Trace.Equiv (t1 t2 : Trace) : Prop := ∀ l, Trace.extSeq l t1 = Trace.extSeq l t2

namespace Trace.Equiv

theorem refl (t : Trace) : Trace.Equiv t t := fun _ => rfl

theorem symm {t1 t2 : Trace} (h : Trace.Equiv t1 t2) : Trace.Equiv t2 t1 :=
  fun l => (h l).symm

theorem trans {t1 t2 t3 : Trace}
    (h1 : Trace.Equiv t1 t2) (h2 : Trace.Equiv t2 t3) : Trace.Equiv t1 t3 :=
  fun l => (h1 l).trans (h2 l)

end Trace.Equiv

/-- **Bridge to the existence-level external touch.**  A mode `cm` appears in the
  external sequence to `l` exactly when `l` is externally touched with mode `cm` —
  connecting `Trace.Equiv` to the existing `Trace.extTouchesFromMode`/`Noninterfere`
  machinery. -/
theorem Trace.mem_extSeqFrom_iff {A : List Nat} {l : Nat} {cm : CapMode} {t : Trace} :
    cm ∈ Trace.extSeqFrom A l t ↔ Trace.extTouchesFromMode A l cm t := by
  induction t generalizing A with
  | nil => simp [Trace.extSeqFrom, Trace.extTouchesFromMode]
  | cons it t ih =>
    cases it with
    | alloc l' =>
      simp only [Trace.extSeqFrom, Trace.extTouchesFromMode]; exact ih
    | access mu l' =>
      simp only [Trace.extSeqFrom, Trace.extTouchesFromMode]
      split
      · rename_i hcond
        simp only [List.mem_cons, ih]
        constructor
        · rintro (rfl | h)
          · exact Or.inl ⟨hcond.1, hcond.2, rfl⟩
          · exact Or.inr h
        · rintro (⟨_, _, rfl⟩ | h)
          · exact Or.inl rfl
          · exact Or.inr h
      · rename_i hcond
        rw [ih]
        constructor
        · exact Or.inr
        · rintro (⟨h1, h2, _⟩ | h)
          · exact absurd ⟨h1, h2⟩ hcond
          · exact h
    | dealloc l' =>
      simp only [Trace.extSeqFrom, Trace.extTouchesFromMode]
      split
      · rename_i hcond
        simp only [List.mem_cons, ih]
        constructor
        · rintro (rfl | h)
          · exact Or.inl ⟨hcond.1, hcond.2, rfl⟩
          · exact Or.inr h
        · rintro (⟨_, _, rfl⟩ | h)
          · exact Or.inl rfl
          · exact Or.inr h
      · rename_i hcond
        rw [ih]
        constructor
        · exact Or.inr
        · rintro (⟨h1, h2, _⟩ | h)
          · exact absurd ⟨h1, h2⟩ hcond
          · exact h

/-- Equivalent traces externally touch every location with the same modes — the
  transport principle the immutability facts (e.g. `access .epsilon l ∉ t`) ride on. -/
theorem Trace.Equiv.extTouchesMode_iff {t1 t2 : Trace} (h : Trace.Equiv t1 t2)
    {l : Nat} {cm : CapMode} :
    Trace.extTouchesMode t1 l cm ↔ Trace.extTouchesMode t2 l cm := by
  unfold Trace.extTouchesMode
  rw [← Trace.mem_extSeqFrom_iff, ← Trace.mem_extSeqFrom_iff,
      show Trace.extSeqFrom [] l t1 = Trace.extSeqFrom [] l t2 from h l]

/-! ### Projection algebra

  `extSeqFrom A l t` reads the alloc-set `A` only through `l`'s own membership (the
  sole place `A` is consulted is the `l ∉ A` guard), and a cell already in `A` is
  internal forever — these two facts give the decomposition over `++` that the
  `Trace.Equiv` reasoning is built on. -/

/-- `extSeqFrom` consults `A` only through `l`'s membership. -/
theorem Trace.extSeqFrom_mem_self {A1 A2 : List Nat} {l : Nat} {t : Trace}
    (h : l ∈ A1 ↔ l ∈ A2) :
    Trace.extSeqFrom A1 l t = Trace.extSeqFrom A2 l t := by
  induction t generalizing A1 A2 with
  | nil => rfl
  | cons it t ih =>
    cases it with
    | alloc l' =>
      simp only [Trace.extSeqFrom]
      exact ih (by simp only [List.mem_cons, h])
    | access mu l' =>
      simp only [Trace.extSeqFrom]
      have hc : (l = l' ∧ l ∉ A1) ↔ (l = l' ∧ l ∉ A2) := by rw [h]
      by_cases hcond : l = l' ∧ l ∉ A1
      · rw [if_pos hcond, if_pos (hc.mp hcond), ih h]
      · rw [if_neg hcond, if_neg (fun h2 => hcond (hc.mpr h2)), ih h]
    | dealloc l' =>
      simp only [Trace.extSeqFrom]
      have hc : (l = l' ∧ l ∉ A1) ↔ (l = l' ∧ l ∉ A2) := by rw [h]
      by_cases hcond : l = l' ∧ l ∉ A1
      · rw [if_pos hcond, if_pos (hc.mp hcond), ih h]
      · rw [if_neg hcond, if_neg (fun h2 => hcond (hc.mpr h2)), ih h]

/-- A cell already in the alloc-set is internal: it contributes nothing. -/
theorem Trace.extSeqFrom_eq_nil {A : List Nat} {l : Nat} {t : Trace} (hl : l ∈ A) :
    Trace.extSeqFrom A l t = [] := by
  induction t generalizing A with
  | nil => rfl
  | cons it t ih =>
    cases it with
    | alloc l' => simp only [Trace.extSeqFrom]; exact ih (List.mem_cons_of_mem _ hl)
    | access mu l' =>
      simp only [Trace.extSeqFrom, if_neg (show ¬(l = l' ∧ l ∉ A) from fun h => h.2 hl)]
      exact ih hl
    | dealloc l' =>
      simp only [Trace.extSeqFrom, if_neg (show ¬(l = l' ∧ l ∉ A) from fun h => h.2 hl)]
      exact ih hl

/-- The alloc-set acts as an all-or-nothing gate on `l`. -/
theorem Trace.extSeqFrom_eq_ite {A : List Nat} {l : Nat} {t : Trace} :
    Trace.extSeqFrom A l t = if l ∈ A then [] else Trace.extSeqFrom [] l t := by
  by_cases hl : l ∈ A
  · rw [if_pos hl, Trace.extSeqFrom_eq_nil hl]
  · rw [if_neg hl]
    exact Trace.extSeqFrom_mem_self (iff_of_false hl (by simp))

/-- Decomposition of the external sequence over trace concatenation: process `t1`,
  then `t2` with `t1`'s allocations added to the exempt set. -/
theorem Trace.extSeqFrom_append {A : List Nat} {l : Nat} {t1 t2 : Trace} :
    Trace.extSeqFrom A l (t1 ++ t2)
      = Trace.extSeqFrom A l t1 ++ Trace.extSeqFrom (Trace.allocList t1 ++ A) l t2 := by
  induction t1 generalizing A with
  | nil => rfl
  | cons it t1 ih =>
    cases it with
    | alloc l' =>
      simp only [List.cons_append, Trace.extSeqFrom, Trace.allocList, ih]
      congr 1
      exact Trace.extSeqFrom_mem_self (by simp only [List.mem_append, List.mem_cons]; tauto)
    | access mu l' =>
      by_cases hcond : l = l' ∧ l ∉ A
      · simp only [List.cons_append, Trace.extSeqFrom, Trace.allocList, if_pos hcond, ih,
          List.cons_append]
      · simp only [List.cons_append, Trace.extSeqFrom, Trace.allocList, if_neg hcond, ih]
    | dealloc l' =>
      by_cases hcond : l = l' ∧ l ∉ A
      · simp only [List.cons_append, Trace.extSeqFrom, Trace.allocList, if_pos hcond, ih,
          List.cons_append]
      · simp only [List.cons_append, Trace.extSeqFrom, Trace.allocList, if_neg hcond, ih]

/-- Two lists whose every element equals `c` commute under append (both are the same
  `replicate`). -/
theorem List.append_comm_of_const {α} {L1 L2 : List α} {c : α}
    (h1 : ∀ x ∈ L1, x = c) (h2 : ∀ x ∈ L2, x = c) : L1 ++ L2 = L2 ++ L1 := by
  have key : ∀ (M N : List α), (∀ x ∈ M, x = c) → (∀ x ∈ N, x = c) →
      M ++ N = List.replicate (M.length + N.length) c := by
    intro M N hM hN
    rw [List.eq_replicate_iff]
    refine ⟨by rw [List.length_append], fun x hx => ?_⟩
    rcases List.mem_append.mp hx with h | h
    · exact hM x h
    · exact hN x h
  rw [key L1 L2 h1 h2, key L2 L1 h2 h1, Nat.add_comm]

/-- **Commutation of separated traces.**  Two traces that do not interfere
  (`Noninterfere`) and whose allocations are disjoint from each other's external
  touches (the operational freshness — a branch's fresh cells are not pre-existing for
  the other) are `Trace.Equiv` when concatenated in either order.  This is the trace
  heart of the diamond: a shared external touch is `.ro` on both sides (so the merged
  per-location sequence is a run of identical `.ro`'s, order-free), and a freshly
  allocated cell is private (its sequence is empty on the other side). -/
theorem Trace.equiv_comm_of_noninterfere {t s : Trace}
    (hni : Trace.Noninterfere t s)
    (hf1 : ∀ l, Trace.allocd s l → Trace.extSeqFrom [] l t = [])
    (hf2 : ∀ l, Trace.allocd t l → Trace.extSeqFrom [] l s = []) :
    Trace.Equiv (t ++ s) (s ++ t) := by
  intro l
  change Trace.extSeqFrom [] l (t ++ s) = Trace.extSeqFrom [] l (s ++ t)
  rw [Trace.extSeqFrom_append, Trace.extSeqFrom_append, List.append_nil, List.append_nil,
      Trace.extSeqFrom_eq_ite (A := Trace.allocList t),
      Trace.extSeqFrom_eq_ite (A := Trace.allocList s)]
  by_cases hat : l ∈ Trace.allocList t
  · rw [if_pos hat, hf2 l (Trace.mem_allocList.mp hat)]
    by_cases has : l ∈ Trace.allocList s
    · rw [if_pos has, hf1 l (Trace.mem_allocList.mp has)]
    · rw [if_neg has]; simp
  · rw [if_neg hat]
    by_cases has : l ∈ Trace.allocList s
    · rw [if_pos has, hf1 l (Trace.mem_allocList.mp has)]; simp
    · rw [if_neg has]
      by_cases hP : Trace.extSeqFrom [] l t = []
      · rw [hP]; simp
      · by_cases hQ : Trace.extSeqFrom [] l s = []
        · rw [hQ]; simp
        · obtain ⟨cm2, hcm2⟩ := List.exists_mem_of_ne_nil _ hQ
          have hes2 : Trace.extTouchesMode s l cm2 := Trace.mem_extSeqFrom_iff.mp hcm2
          obtain ⟨cm1, hcm1⟩ := List.exists_mem_of_ne_nil _ hP
          have hes1 : Trace.extTouchesMode t l cm1 := Trace.mem_extSeqFrom_iff.mp hcm1
          refine List.append_comm_of_const (c := CapMode.access .ro)
            (fun x hx => ?_) (fun x hx => ?_)
          · exact (hni l x cm2 (Trace.mem_extSeqFrom_iff.mp hx) hes2).1
          · exact (hni l cm1 x hes1 (Trace.mem_extSeqFrom_iff.mp hx)).2

/-! ## The down-frame lemma (`Safe.frame_down`)

  The downward companion of `Safe.lift`: safety transfers from a larger memory `ma` to
  a smaller `m1` that AGREES with it on the cells `b` touches.  The reachability worry
  is dissolved by IMMUTABILITY: only mcells are ever written/dropped, and they are
  exactly the cells the budgets track — so value cells (readers, abstractions) are
  preserved by subsumption for free, and the frame only needs to constrain mcells. -/

/-- Down-frame condition: a live mcell of `ma` that `t` externally touches is the SAME
  live mcell in the smaller `m1`.  (Dual of `Memory.SubsumeOk`.) -/
def Memory.AgreeOk (m1 : Memory) (t : Trace) (ma : Memory) : Prop :=
  ∀ l b,
    ma.lookup l = some (.capability (.mcell b .live)) →
    Trace.extTouches t l →
    m1.lookup l = some (.capability (.mcell b .live))

/-- **Down-frame for safety.**  If `b` is safe at the larger `ma` and the smaller `m1`
  agrees with `ma` on every mcell `b` touches (the frame `hok`), then `b` is safe at
  `m1`.  Mirrors `Safe.lift` in the opposite subsumption direction; value cells are
  recovered by `Memory.lookup_down` (subsumption pins them), mcells by the frame. -/
theorem Safe.frame_down {ma : Memory} {b : Exp {}} {Q : Tpost} (hsafe : Safe ma b)
    (hsub : ma.subsumes m1)
    (hpres : ∀ t v m', BigStep ma b t v m' → Q t v m')
    (hok : ∀ t v m, m.subsumes ma → Q t v m → Memory.AgreeOk m1 t ma)
    (hwf : Exp.WfInHeap b m1.heap) : Safe m1 b := by
  induction hsafe generalizing m1 Q with
  | ans hans => exact Safe.ans hans
  | alloc hlka =>
    cases hwf with
    | wf_alloc hwfx => cases hwfx with
      | wf_free hxm1 =>
        have hc := Memory.lookup_down hsub hxm1 hlka
        simp only [Cell.subsumes] at hc; subst hc
        exact Safe.alloc hxm1
  | invoke hlkx hlky =>
    cases hwf with
    | wf_app hwfx hwfy => cases hwfx with
      | wf_free hxm1 => cases hwfy with
        | wf_free hym1 =>
          have hcx := Memory.lookup_down hsub hxm1 hlkx
          have hcy := Memory.lookup_down hsub hym1 hlky
          simp only [Cell.subsumes] at hcx hcy; subst hcx; subst hcy
          exact Safe.invoke hxm1 hym1
  | apply hlk _ ih =>
    cases hwf with
    | wf_app hwfx hwfy => cases hwfx with
      | wf_free hxm1 =>
        have hc := Memory.lookup_down hsub hxm1 hlk
        simp only [Cell.subsumes] at hc; subst hc
        obtain ⟨_, _, he⟩ := Exp.wf_inv_abs (Memory.wf_lookup hxm1)
        exact Safe.apply hxm1 (ih hsub
          (fun t v m' hbs => hpres t v m' (BigStep.bs_apply hlk hbs)) hok
          (Exp.wf_subst he (Subst.wf_openVar hwfy)))
  | tapply hlk _ ih =>
    cases hwf with
    | wf_tapp hwfx hwfS => cases hwfx with
      | wf_free hxm1 =>
        have hc := Memory.lookup_down hsub hxm1 hlk
        simp only [Cell.subsumes] at hc; subst hc
        obtain ⟨_, _, he⟩ := Exp.wf_inv_tabs (Memory.wf_lookup hxm1)
        exact Safe.tapply hxm1 (ih hsub
          (fun t v m' hbs => hpres t v m' (BigStep.bs_tapply hlk hbs)) hok
          (Exp.wf_subst he (Subst.wf_openTVar Ty.WfInHeap.wf_top)))
  | capply hlk _ ih =>
    cases hwf with
    | wf_capp hwfx hcs => cases hwfx with
      | wf_free hxm1 =>
        have hc := Memory.lookup_down hsub hxm1 hlk
        simp only [Cell.subsumes] at hc; subst hc
        obtain ⟨_, _, he⟩ := Exp.wf_inv_cabs (Memory.wf_lookup hxm1)
        exact Safe.capply hxm1 (ih hsub
          (fun t v m' hbs => hpres t v m' (BigStep.bs_capply hlk hbs)) hok
          (Exp.wf_subst he (Subst.wf_openCVar hcs)))
  | unwrap hlk _ ih =>
    cases hwf with
    | wf_unwrap hwfx => cases hwfx with
      | wf_free hxm1 =>
        have hc := Memory.lookup_down hsub hxm1 hlk
        simp only [Cell.subsumes] at hc; subst hc
        exact Safe.unwrap hxm1 (ih hsub
          (fun t v m' hbs => hpres t v m' (BigStep.bs_unwrap hlk hbs)) hok
          (match Memory.wf_lookup hxm1 with | .wf_boxed _ _ he => he))
  | read hlkx hlky =>
    cases hwf with
    | wf_read hwfx => cases hwfx with
      | wf_free hxm1 =>
        have hcx := Memory.lookup_down hsub hxm1 hlkx
        simp only [Cell.subsumes] at hcx; subst hcx
        have hagree := hok _ _ _ (Memory.subsumes_refl _)
          (hpres _ _ _ (BigStep.bs_read (b' := true) hlkx hlky))
        exact Safe.read hxm1 (hagree _ _ hlky (by simp [Trace.extTouches, Trace.extTouchesFrom]))
  | write_true hlkx hlky =>
    cases hwf with
    | wf_write hwfx hwfy => cases hwfy with
      | wf_free hym1 =>
        have hcy := Memory.lookup_down hsub hym1 hlky
        simp only [Cell.subsumes] at hcy; subst hcy
        have hagree := hok _ _ _ (Memory.update_mcell_subsumes _ _ _ _ ⟨_, hlkx⟩)
          (hpres _ _ _ (BigStep.bs_write_true hlkx hlky))
        exact Safe.write_true
          (hagree _ _ hlkx (by simp [Trace.extTouches, Trace.extTouchesFrom])) hym1
  | write_false hlkx hlky =>
    cases hwf with
    | wf_write hwfx hwfy => cases hwfy with
      | wf_free hym1 =>
        have hcy := Memory.lookup_down hsub hym1 hlky
        simp only [Cell.subsumes] at hcy; subst hcy
        have hagree := hok _ _ _ (Memory.update_mcell_subsumes _ _ _ _ ⟨_, hlkx⟩)
          (hpres _ _ _ (BigStep.bs_write_false hlkx hlky))
        exact Safe.write_false
          (hagree _ _ hlkx (by simp [Trace.extTouches, Trace.extTouchesFrom])) hym1
  | drop hlkx =>
    have hagree := hok _ _ _ (Memory.drop_mcell_subsumes _ _ ⟨_, hlkx⟩)
      (hpres _ _ _ (BigStep.bs_drop hlkx))
    exact Safe.drop (hagree _ _ hlkx (by simp [Trace.extTouches, Trace.extTouchesFrom]))
  | @cond e2 e3 ma2 xv hres h_true h_false ih_true ih_false =>
    obtain ⟨xn, rfl⟩ := Var.free_cases xv
    obtain ⟨hwfx, hwf2, hwf3⟩ := Exp.wf_inv_cond hwf
    cases hwfx with
    | wf_free hxm1 =>
      have hxne : m1.heap xn ≠ none := by rw [hxm1]; simp
      refine Safe.cond (hres.imp (resolve_down hsub hxne) (resolve_down hsub hxne)) ?_ ?_
      · intro hbt
        cases hres with
        | inl hb1 =>
          exact ih_true hb1 hsub
            (fun t v m' hbs => hpres t v m' (BigStep.bs_cond_true hb1 hbs)) hok hwf2
        | inr hbf => rw [resolve_down hsub hxne hbf] at hbt; simp at hbt
      · intro hbf
        cases hres with
        | inl hbt => rw [resolve_down hsub hxne hbt] at hbf; simp at hbf
        | inr hb1 =>
          exact ih_false hb1 hsub
            (fun t v m' hbs => hpres t v m' (BigStep.bs_cond_false hb1 hbs)) hok hwf3
  -- REMAINING (3 of 15 cases; the 12 leaf/`cond` cases above are PROVEN, which already
  -- disproves the earlier "research-grade reachability" fear — value cells are immutable,
  -- so the footprint stays mcell-tracked and the downward extraction goes through):
  --  * `letin`/`unpack` reconstruct safety at the SMALLER `m1`, whose continuation
  --    fields quantify over `m1`-runs of the head; using the `ma`-side handlers needs
  --    lifting an `m1`-run UP to an `ma`-run (a `simulate_up`, dual to `simulate_down`,
  --    ~100 lines and not yet present).  Buildable; not a design gap.
  --  * `par` (nested) reconstructs `Safe.par`'s robust bounds at `m1`, re-anchoring them
  --    from `ma` to the smaller `m1` — the genuine remaining crux (a bound `∀ m' ⊒ ma`
  --    does not directly give `∀ m' ⊒ m1`).
  | par hs1 h2 hb1 hb2 hrs2 hpres1 hpres2 hni ih1 ih2 _hrs2ih => sorry
  | letin _ h_ans h_val h_var ih1 ih_val ih_var => sorry
  | unpack _ h_ans h_val ih1 ih_val => sorry

/-! ## The separation carrier and the standardization theorem

  The runtime separation invariant is `Safe` itself (plus `WfInHeap`): each `Safe.par`
  node bundles the robust budget bounds `hb1`/`hb2` and `Noninterference` `hni`, which
  compose — via `traceOk_noninterfere` — into `Trace.Noninterfere` between any two
  branch runs.  That is exactly what the diamond `BigStep.step_run_commute` consumes,
  and it is what the platform supplies (the fundamental theorem hands us `Safe`). -/

/-- **The diamond's fuel.**  From `Safe.par`, any two runs of the two branches — from
  any memories `⊒` the par node's `m` — have non-interfering traces. -/
theorem Safe.par_noninterfere {m m1 m2 m1' m2' : Memory} {e1 e2 v1 v2 : Exp {}}
    {t1 t2 : Trace}
    (hsafe : Safe m (.par e1 e2))
    (hr1 : BigStep m1 e1 t1 v1 m1') (hsub1 : m1.subsumes m) (hwf1 : Exp.WfInHeap e1 m1.heap)
    (hr2 : BigStep m2 e2 t2 v2 m2') (hsub2 : m2.subsumes m) (hwf2 : Exp.WfInHeap e2 m2.heap) :
    Trace.Noninterfere t1 t2 := by
  cases hsafe with
  | par _ _ hb1 hb2 _ _ _ hni =>
      exact traceOk_noninterfere (hb1 hsub1 hwf1 hr1) (hb2 hsub2 hwf2 hr2) hni
  | ans hans => cases hans with | is_val hv => cases hv

/-- **Standardization (theorem B).**  Every interleaving run to an answer is matched by
  a SEQUENTIAL run reaching the IDENTICAL final memory and answer, the only difference
  being a `Trace.Equiv` reordering of the trace.

  The hypotheses are only the natural ones: `e` is well-formed in `m` (`WfInHeap`, what
  the diamond needs), and the configuration is `Safe` — the runtime separation carrier,
  whose `par` nodes supply the `Noninterference` that drives the diamond.

  Proof engine: postponement — bubble each premature right-branch step past the
  remaining left-run via the EXACT-meet diamond `BigStep.step_run_commute` (fed by
  `Safe.par_noninterfere`), each swap preserving `(mf, a)` and reordering the trace
  within `Trace.Equiv` (the trace algebra above — `extSeqFrom_*`,
  `equiv_comm_of_noninterfere` — is the complete, proven foundation for that step).

  **The remaining obstruction is a genuine, fundamental design gap (the sorry below).**
  Postponing `step_par_right` (`b` steps while the left branch `a` is mid-run) requires
  bounding `b`'s step by its budget `C2`, which needs a run of `b` from the pre-step
  memory `m1`, which needs `Safe m1 b`.  But `Safe.par` is ASYMMETRIC: it carries
  `Safe m e1` (the LEFT branch, safe at the par's own memory) yet only CONDITIONAL
  right-branch safety `hrs2 : m'.is_compatible C2 → Safe m' e2`.  Discharging
  `is_compatible C2` at a general `m1` is exactly what `AllLive` bought; without it,
  `Safe m1 b` must be derived operationally — `b`'s touched cells are live at `m1`
  because the run uses them and the separated left branch never disturbs them.  That is
  the dynamic-footprint / ownership-transfer reasoning the project's DEFINITIVE FINDING
  established as research-grade; equivalently, it is the symmetric branch-safety field
  (`Safe m e2`) that `Safe.par` would need to carry (constructible in `sem_typ_par` from
  `is_compatible C2 ⊆ is_compatible C`, but a large ripple through `Fundamental` and the
  `SeqStep` theory, and itself maintained per-step only via the same ownership argument).

  CONCRETE FINDING (from attempting the down-frame lemma `Safe.frame_down`, the downward
  companion of `Safe.lift`): it needs `m1` and `ma` to AGREE on `b`'s reachable footprint,
  and that footprint is strictly broader than `C2`.  The `read` leaf is the witness:
  `read x` resolves a `reader y` cell at `x`, then accesses `y` — the trace carries only
  `access ro y` (so `C2` covers `y`), but the `reader` cell at `x` emits NO trace event, so
  `x ∉ C2`, yet the redex needs `m1`/`ma` to agree at `x`.  Since `a` genuinely modifies its
  OWN cells, the agreement is necessarily PARTIAL (`b`'s footprint, not all of `m1`), so it
  cannot even be STATED without `b`'s reachability closure — the denotation-level
  reachability/capture machinery (`compute_reachability`).  The induction must also maintain
  "`b` stays within its footprint" across `alloc`/`drop`.  This definitively places the gap
  in the dynamic-footprint development that threads operational safety through the
  DENOTATION — research-grade, exactly as the DEFINITIVE FINDING predicted.

  This is the precise human-intervention point: either re-admit a liveness premise, or
  build the operational dynamic-footprint development / symmetric `Safe.par`. -/
theorem standardization {m mf : Memory} {e a : Exp {}} {t : Trace}
    (hwf : Exp.WfInHeap e m.heap) (hsafe : Safe m e)
    (hred : Reduce t m e mf a) (hans : a.IsAns) :
    ∃ t', SeqReduce t' m e mf a ∧ Trace.Equiv t t' :=
  -- GAP: needs symmetric branch safety `Safe m1 b` from `Safe m1 (.par a b)` without
  -- `AllLive` — the research-grade dynamic-footprint kernel documented above.
  sorry

end CoreCapybara
