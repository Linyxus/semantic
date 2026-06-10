import Semantic.CoreCapybara.Fundamental

/-! # Definition-level counterexamples for the irreducible proof gaps

Every remaining `sorry` of the development is not merely unproven but
*unprovable as stated*: this file constructs explicit, concrete instances —
contexts, environments, and memories — refuting the exact statement each
`sorry` stands for.

## The closed gaps (for the record)

* **Subcapture laundering** is gone: `sep_sc`/`seq_sc` carry a
  `CaptureSet.EquivP` premise (peak-preserving budget shrinking), so
  separation/sequencing evidence cannot be moved to a budget whose peaks hide
  its droppable anchors. `fundamental_sepcheck`, `captureSet_seqcomp_denot`,
  and `SeqComp.cross_droppable` are fully proven, and
  `TypeEnv.DropSepIn.of_subcapt` holds thanks to the `.access_only`
  restriction of `sc_cvar`.

* **Closure creation** is gone: the closure denotations (`arrow`, `poly`,
  `cpoly`, `modal` in `Ty.val_denot`) carry an `env.DropSepIn cs` premise on
  their body conditions, where `cs` is the capture annotation. Creation sites
  (`abs`/`tabs`/`cabs`/`wrap`) discharge the body's separation invariant from
  the premise (the body's budget is the weakened annotation), and elimination
  sites (`app`/`tapp`/`capp`/`unwrap`) supply it from their own budget — the
  elimination rules' use-set *is* the annotation `{ε·x}`. The previously
  `sorry`ed (and false) `TypeEnv.DropSepIn.of_envtyping` is deleted;
  `envtyping_dropsep_false` below records why no `EnvTyping`-only discharge
  could ever have worked. The premise transports along `Rebind` (proven) and
  along `Retype` via the droppable-peak correspondence fields
  (`var_peaks`/`dpeak_cvar_*`, yielding `Retype.dsep`).

## The remaining gaps

All remaining gaps are *transport* failures of the closure premise — places
where a `Retype`-style conversion must relate droppable peaks across a
substitution or a peak-set change and the relation is genuinely false:

1. **Capture instantiation erases peak identity** (`Retype.open_carg`, used
   at `capp` and `unpack`): the bound capture variable `.here` is one atomic
   peak with one stored authority and capability, while its image `C` may
   have zero droppable peaks (a ground witness — refuting the forward
   transport, `open_carg_dpeak_fwd_false`) or several (a union argument —
   refuting uniqueness, `open_carg_dpeak_unique_false`).

2. **Subsumption peak slack** (`sem_typ_app`'s `hps`, `sem_subtyp_arrow`'s
   identity-`Retype`): converting between the peaks of a variable's
   *declared* type and the peaks of the (super)type the elimination rule
   demands requires a peak-membership *equivalence*, but `Subcapt` only
   yields one-directional droppable-peak coverage
   (`subcapt_peak_slack_false`), and a well-typed environment can bind a
   variable whose stored peaks are strictly below its semantic type's peaks
   (`app_peak_slack_false`).

3. **Lock-stored separation facts** (`fundamental_sepcheck_global`,
   pre-existing): lock facts are consumed at arbitrary later program points
   with no budget in scope, and `EnvTyping` admits aliased droppable capture
   variables (`sepcheck_global_droppable_false`).

What a solution must provide, WITHOUT restricting the type system: peak
information that survives instantiation and subsumption — e.g. "deep peaks"
(environments record, for every capture-variable binding, the peaks of the
set it was instantiated with, and peak computation resolves through them), so
that `openCVar`/`openVar` become peak-faithful and the `Retype` fields become
provable; the lock gap additionally needs a device carrying cross-variable
separation facts to budget-less program points.
-/

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

theorem env2_not_dropsep : ¬ env2.DropSepIn Cb2 := by
  intro h
  exact cap0_not_disjoint_self
    (h (.there .here) .here (.M .epsilon) (.M .epsilon)
      (by intro heq; cases heq) rfl rfl
      (.union_right_left .refl) (.union_right_right .refl))

/-! ## Why the closure premise exists: `EnvTyping` alone cannot supply the
separation invariant

This refutes any `EnvTyping`-only discharge of the closure body's
separation invariant (the deleted `TypeEnv.DropSepIn.of_envtyping`):
well-typed environments may alias droppable capture variables, so the
invariant must instead be *carried* — which is exactly what the `DropSepIn`
premise of the closure denotations does. -/

theorem envtyping_dropsep_false :
    ¬ (∀ {s : Sig} {Γ : Ctx s} {env : TypeEnv s} {m : Memory} (C : CaptureSet s),
        EnvTyping Γ env m → env.DropSepIn C) := by
  intro h
  exact env2_not_dropsep (h Cb2 envtyping2)

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
        ∃ d, TypeEnv.DropPeak env ((Subst.openCVar C).cvar c) d ∧
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
        TypeEnv.DropPeak env ((Subst.openCVar C).cvar c) d1 →
        TypeEnv.DropPeak env ((Subst.openCVar C).cvar c) d2 → d1 = d2) := by
  intro h
  have heq := h env2 Cb2 .here (.there .here) .here
    ⟨rfl, .M .epsilon, .union_right_left .refl⟩
    ⟨rfl, .M .epsilon, .union_right_right .refl⟩
  cases heq

/-! ## Gap 2: subsumption peak slack

These refute the peak-membership equivalences needed by `sem_typ_app` (the
`hps` hypothesis of `Retype.open_arg`) and by `sem_subtyp_arrow` (the
`.here` branch of `var_peaks` for the identity `Retype` between the sub- and
supertype's argument peak sets). -/

/-- `Subcapt` does not preserve peak membership as an equivalence — it only
gives one-directional coverage. A budget may grow a fresh droppable peak. -/
theorem subcapt_peak_slack_false :
    ¬ (∀ {s : Sig} (Γ : Ctx s) (env : TypeEnv s) (C1 C2 : CaptureSet s),
        Subcapt Γ C1 C2 →
        ∀ d, env.PeaksAt C1 d ↔ env.PeaksAt C2 d) := by
  intro h
  have hiff := h Γ2 env2 (.cvar (.M .epsilon) .here) Cb2
    (.sc_elem (.union_right_right .refl)) (.there .here)
  obtain ⟨a, hsub⟩ := hiff.mpr ⟨.M .epsilon, .union_right_left .refl⟩
  cases (CaptureSet.cvar_subset_cvar_inv hsub).2

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
          env.PeaksAt (compute_peakset env T1.captureSet).cs d ↔
          env.PeaksAt (.var (.M .epsilon) (.bound y)) d) := by
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

end CoreCapybara.Gaps
