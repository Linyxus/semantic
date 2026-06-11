import Semantic.CoreCapybara.Fundamental

/-! # Definition-level counterexamples for the irreducible proof gaps

Every remaining `sorry` of the development is not merely unproven but
*unprovable as stated*: this file constructs explicit, concrete instances —
contexts, environments, and memories — refuting the exact statement each
`sorry` stands for.

## The semantic model (dead-set form, first-class)

The environment-separation invariant is `TypeEnv.DropSepIn env K C`: some
dead set covering the peaks of the *static* dead-set `K` witnesses
`DropSepExcept`, and the budget `C`'s droppable peaks avoid it. The typing
judgment `HasType K C Γ e T` threads `K` explicitly, growing it at
sequencing by what the first component consumed (`consumed_peaks`); closure
types record their creation-time dead-set `ds`, and the closure denotations
state their body premise relative to it. This *closed* the former
closure-creation gap (the `abs`/`tabs`/`cabs`/`wrap` cases discharge their
body premise exactly, `ds = K`) and the sequencing gap (`letin`/`unpack`
grow the dead set by `TypeEnv.DropSepIn.seq_grow`, anchored at
`SeqComp.cross_droppable`).

## The remaining gaps

1. **Capture instantiation erases peak identity** (`Retype.open_carg`, used
   at `capp` and `pack`/`unpack`): the bound capture variable `.here` is one
   atomic peak with one stored authority and capability, while its image `C`
   may have zero droppable peaks (a ground witness —
   `open_carg_dpeak_fwd_false`) or several (a union argument —
   `open_carg_dpeak_unique_false`).

2. **Subsumption peak slack** (`sem_typ_app`'s `hps`, `sem_subtyp_arrow`'s
   identity-`Retype` `var_peaks`): converting between the peaks of a
   variable's *declared* type and the peaks of the (super)type the
   elimination rule demands requires a peak-membership *equivalence*, but a
   well-typed environment can bind a variable whose stored peaks are
   strictly below its semantic type's peaks (`app_peak_slack_false`) — the
   `subtyp` rule makes exactly this mismatch typeable. A static lever:
   peak-faithful subsumption (`EquivP` side conditions on the `Subcapt`
   premises inside `Subtyp`, the same device already adopted for `sep_sc`
   and `seq_sc`).

3. **Lock-stored separation facts** (`fundamental_sepcheck_global`): lock
   facts are consumed at arbitrary later program points with no budget in
   scope, and `EnvTyping` admits aliased droppable capture variables
   (`sepcheck_global_droppable_false`).

4. **Dead-set supply at eliminations** (`dead_set_supply`, used at `app`,
   `tapp`, `capp`, `unwrap`): a closure's denotation demands the invariant
   relative to the closure's *stored* dead-set `ds`; the caller owns it
   relative to the *ambient* `K`. By `TypeEnv.DropSepIn.retarget` the supply
   reduces to "the budget's droppable peaks avoid `deadIn ds`" — true in
   derivable programs (dead-sets only grow along sequencing, so
   `ds = K_creation ⊑ K_call`, and the caller's avoidance covers it), but
   the elimination rules accept *any* `ds`: a lambda parameter may be
   annotated with an arrow type whose stored dead-set names a live capture
   variable that the arrow also captures, and then the supply is false
   (`dead_set_supply_false`). Static fix options: an elimination-side
   premise `ds ⊑ K` (the type's dead-set is covered by the ambient one), or
   a well-formedness condition on closure types (the capture annotation's
   droppable peaks avoid the stored dead-set). A type-system design
   decision — to be made with the human. -/

namespace CoreCapybara.Gaps

open CoreCapybara

/-! ## The shared world -/

/-- A memory holding a single (basic) capability cell at location `0`. -/
def mem1 : Memory := Memory.extend_cap Memory.empty 0 rfl

/-- The ground capture set `{ε·0}`. -/
def cs0 : CaptureSet {} := .var (.M .epsilon) (.free 0)

/-- The capability `ε·0`. -/
def cap0 : CapabilitySet := .cap (.access .epsilon) 0

theorem cs0_ground : cs0.ground_denot mem1 = cap0 := rfl

theorem cap0_drop_free : cap0.drop_free := by
  intro l h
  cases h

theorem cap0_not_disjoint_self : ¬ CapabilitySet.disjoint cap0 cap0 := by
  intro h
  exact h (.access .epsilon) (.access .epsilon) 0 .here .here

theorem noninterference_cap0_self_false :
    ¬ CapabilitySet.Noninterference cap0 cap0 := by
  intro h
  have key : ∀ (A B : CapabilitySet), CapabilitySet.Noninterference A B →
      A = cap0 → B = cap0 → False := by
    intro A B h
    induction h with
    | ni_symm _ ih => intro h1 h2; exact ih h2 h1
    | ni_empty => intro h1 _; cases h1
    | ni_union _ _ _ _ => intro h1 _; cases h1
    | ni_ro => intro h1 _; cases h1
    | ni_disj hne =>
      intro h1 h2
      cases h1; cases h2
      exact hne rfl
  exact key cap0 cap0 h rfl rfl

/-- The aliased two-droppable context: `∅,C[.can_drop]<:⊤,C[.can_drop]<:⊤`. -/
def Γ2 : Ctx ({},C,C) :=
  ((Ctx.empty).push_cvar .can_drop .unbound).push_cvar .can_drop .unbound

/-- An environment binding *both* droppable capture variables of `Γ2` to the
same capability `cap0`. -/
def env2 : TypeEnv ({},C,C) :=
  ((TypeEnv.empty).extend_cvar cs0 cap0 .can_drop).extend_cvar cs0 cap0 .can_drop

theorem envtyping2 : EnvTyping Γ2 env2 mem1 := by
  refine ⟨?_, ?_, ?_, rfl, ?_, rfl, ?_, ?_, ?_, rfl, ?_, rfl, trivial⟩
  · exact .wf_var_free (val := .capability .basic) rfl
  · exact .wf_unbound
  · exact .top
  · exact cap0_drop_free
  · exact .wf_var_free (val := .capability .basic) rfl
  · exact .wf_unbound
  · exact .top
  · exact cap0_drop_free

/-- The budget peaking both droppable capture variables of `Γ2`. -/
def Cb2 : CaptureSet ({},C,C) :=
  (.cvar (.M .epsilon) (.there .here)) ∪ (.cvar (.M .epsilon) .here)

/-- A well-typed environment may alias two droppable capture variables; no
budget peaking both can satisfy the separation invariant, whatever the
dead-set: the avoidance condition forbids excusing either peak. -/
theorem env2_not_dropsep (K : CaptureSet ({},C,C)) : ¬ env2.DropSepIn K Cb2 := by
  intro h
  exact cap0_not_disjoint_self
    (h.pairs (.there .here) .here (.M .epsilon) (.M .epsilon)
      (by intro heq; cases heq) rfl rfl
      (.union_right_left .refl) (.union_right_right .refl))

/-! ## Gap 1: capture instantiation erases peak identity

These refute the `.here` branches of `Retype.open_carg`'s droppable-peak
transport fields — the obstacle to transporting the closure premise through
`capp` and `unpack`. -/

/-- Forward transport fails: a droppable capture binder may be instantiated
with a *ground* capture set, which has no droppable peak at all (this is
exactly the `unpack` situation, where the witness is a runtime capture set).
Refutes the `.here` branch of `Retype.open_carg`'s `dpeak_cvar_fwd`. -/
theorem open_carg_dpeak_fwd_false :
    ¬ (∀ {s : Sig} (env : TypeEnv s) (C : CaptureSet s)
        (cap : CapabilitySet) (a : Authority) (c : BVar (s,C) .cvar),
        (env.extend_cvar (C.subst (Subst.from_TypeEnv env)) cap a).lookup_cvar_auth c
          = .can_drop →
        ∃ d, TypeEnv.HasDroppablePeak env ((Subst.openCVar C).cvar c) d ∧
          (env.lookup_cvar d).2
            = ((env.extend_cvar (C.subst (Subst.from_TypeEnv env)) cap a).lookup_cvar c).2) := by
  intro h
  obtain ⟨d, -, -⟩ :=
    h (s := {}) TypeEnv.empty cs0 cap0 .can_drop .here rfl
  cases d

/-- Uniqueness fails: a capture binder may be instantiated with a capture set
peaking *two distinct* droppable capture variables (this is the `capp`
situation — `CaptureBound.IsValid` is mode-based and does not constrain the
authority of the peaks). Refutes the `.here` branch of `Retype.open_carg`'s
`dpeak_cvar_unique`. -/
theorem open_carg_dpeak_unique_false :
    ¬ (∀ {s : Sig} (env : TypeEnv s) (C : CaptureSet s) (c : BVar (s,C) .cvar)
        (d1 d2 : BVar s .cvar),
        TypeEnv.HasDroppablePeak env ((Subst.openCVar C).cvar c) d1 →
        TypeEnv.HasDroppablePeak env ((Subst.openCVar C).cvar c) d2 → d1 = d2) := by
  intro h
  have heq := h env2 Cb2 .here (.there .here) .here
    ⟨rfl, .M .epsilon, .union_right_left .refl⟩
    ⟨rfl, .M .epsilon, .union_right_right .refl⟩
  cases heq

/-! ## Gap 2: subsumption peak slack

These refute the peak-membership equivalence needed by `sem_typ_app` (the
`hps` hypothesis of `Retype.open_arg`) and by `sem_subtyp_arrow` (the
`.here` branch of `var_peaks` for the identity `Retype` between the sub- and
supertype's argument peak sets). -/

/-- The aliased two-droppable context extended with a value binding at a
*ground* capability type: the stored peak set of the variable is empty. -/
def Γ4 : Ctx ({},C,x) :=
  ((Ctx.empty).push_cvar .can_drop .unbound).push_var (.cap (.var (.M .epsilon) (.free 0)))

/-- The matching environment: one droppable capture variable bound to `cap0`,
and a value variable bound to location `0` with (statically computed, empty)
peaks. -/
def env4 : TypeEnv ({},C,x) :=
  ((TypeEnv.empty).extend_cvar cs0 cap0 .can_drop).extend
    (.var 0 ((Ty.cap (.var (.M .epsilon) (.free 0))).captureSet.peakset
      ((Ctx.empty).push_cvar .can_drop .unbound)))

theorem envtyping4 : EnvTyping Γ4 env4 mem1 := by
  refine ⟨?_, rfl, ?_, ?_, ?_, rfl, ?_, rfl, trivial⟩
  · change Ty.val_denot _ (.cap (.var (.M .epsilon) (.free 0))) mem1 (.var (.free 0))
    simp only [Ty.val_denot]
    exact ⟨.wf_var (.wf_free (val := .capability .basic) rfl),
      .wf_var_free (val := .capability .basic) rfl,
      0, rfl, rfl, CapabilitySet.covers.here CapMode.Le.refl⟩
  · exact .wf_var_free (val := .capability .basic) rfl
  · exact .wf_unbound
  · exact .top
  · exact cap0_drop_free

/-- A well-typed environment can inhabit a variable at a semantic type whose
peaks strictly exceed the variable's stored peaks: here `y`'s declared type
is the ground `cap {ε·0}` (no peaks), while the value also inhabits
`cap {ε·c}` for the droppable capture variable `c` (one droppable peak).
This refutes the `hps` peak-membership equivalence that `sem_typ_app` must
supply to `Retype.open_arg` when opening the dependent result type — the
subsumption rule (`subtyp`) makes exactly this mismatch typeable. -/
theorem app_peak_slack_false :
    ¬ (∀ {s : Sig} (Γ : Ctx s) (env : TypeEnv s) (store : Memory)
        (T1 : Ty .capt s) (y : BVar s .var),
        EnvTyping Γ env store →
        Ty.val_denot env T1 store (.var (.free (env.lookup_var y).1)) →
        ∀ (d : BVar s .cvar),
          env.HasPeak (compute_peakset env T1.captureSet).cs d ↔
          env.HasPeak (.var (.M .epsilon) (.bound y)) d) := by
  intro h
  have hval : Ty.val_denot env4 (.cap (.cvar (.M .epsilon) (.there .here))) mem1
      (.var (.free (env4.lookup_var .here).1)) := by
    simp only [Ty.val_denot]
    exact ⟨.wf_var (.wf_free (val := .capability .basic) rfl),
      .wf_var_free (val := .capability .basic) rfl,
      0, rfl, rfl, CapabilitySet.covers.here CapMode.Le.refl⟩
  have hiff := h Γ4 env4 mem1 (.cap (.cvar (.M .epsilon) (.there .here))) .here
    envtyping4 hval (.there .here)
  obtain ⟨a, hsub⟩ := hiff.mp ⟨.M .epsilon, .refl⟩
  have heq : compute_peaks env4 (.var (.M .epsilon) (.bound .here)) = .empty := by
    change (CaptureSet.peaks ((Ctx.empty).push_cvar .can_drop .unbound)
      (.var (.M .epsilon) (.free 0))).rename Rename.succ = .empty
    rw [CaptureSet.peaks]
    rfl
  rw [heq] at hsub
  exact CaptureSet.cvar_not_subset_empty hsub

/-! ## Gap 3: lock-stored `sep_droppable` facts

This refutes the `sep_droppable` case of `fundamental_sepcheck_global` (the
interpretation of lock-stored `SepCheck` facts, which must hold with no
separation invariant available): two distinct droppable capture variables may
denote overlapping — here, equal — capabilities. -/

theorem sepcheck_global_droppable_false :
    ¬ (∀ {s : Sig} {Γ : Ctx s} {c1 c2 : BVar s .cvar} {m1 m2 : Access},
        Γ.TwoDistinctDroppable c1 c2 →
        Γ.IsClosed →
        ∀ env H, EnvTyping Γ env H →
          CapabilitySet.Noninterference
            ((CaptureSet.cvar m1 c1).denot env H)
            ((CaptureSet.cvar m2 c2).denot env H)) := by
  intro h
  have hni := h (Γ := Γ2) (c1 := .there .here) (c2 := .here)
    (m1 := .M .epsilon) (m2 := .M .epsilon)
    ⟨rfl, rfl, by intro heq; cases heq⟩
    (.push (.push .empty (.cvar .unbound)) (.cvar .unbound))
    env2 mem1 envtyping2
  exact noninterference_cap0_self_false hni

/-! ## Gap 4: dead-set supply at eliminations

This refutes `dead_set_supply` exactly as stated: the elimination rules
accept a function type with an *arbitrary* stored dead-set `ds`, and nothing
ties it to the ambient `K`. A well-typed world can hold a droppable capture
variable that is live in the ambient dead-set (`K = ∅`) but named by the
type's dead-set, while also being a budget peak — the avoidance condition of
`DropSepIn ds` is then self-contradictory and cannot be supplied. -/

theorem dead_set_supply_false :
    ¬ (∀ {s : Sig} (Γ : Ctx s) (env : TypeEnv s) (m : Memory) (K ds C : CaptureSet s),
        EnvTyping Γ env m →
        env.DropSepIn K C → env.DropSepIn ds C) := by
  intro h
  -- The caller's invariant: ambient dead-set `∅`, budget `{ε·cB}` — holds
  -- (a single peak has no pairs, and nothing is statically dead).
  have hdsi : env2.DropSepIn .empty (.cvar (.M .epsilon) .here) := by
    apply TypeEnv.DropSepIn.of_pairs
    · intro c1 c2 a1 a2 hne h1 h2 hp1 hp2
      exact absurd
        (((CaptureSet.cvar_subset_cvar_inv hp1).2).trans
          ((CaptureSet.cvar_subset_cvar_inv hp2).2).symm)
        hne
    · intro a c hp _ hdead
      obtain ⟨a', hsub⟩ := hdead
      exact CaptureSet.cvar_not_subset_empty hsub
  -- The closure's demand: stored dead-set `{ε·cB}` — its avoidance condition
  -- forbids the budget peak `cB` itself.
  have h2 := h Γ2 env2 mem1 .empty (.cvar (.M .epsilon) .here)
    (.cvar (.M .epsilon) .here) envtyping2 hdsi
  exact h2.avoid (.M .epsilon) .here .refl rfl ⟨.M .epsilon, .refl⟩

end CoreCapybara.Gaps
