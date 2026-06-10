import Semantic.CoreCapybara.Fundamental

/-! # Definition-level counterexamples for the irreducible proof gaps

Every remaining `sorry` of the development is not merely unproven but
*unprovable as stated*: this file constructs explicit, concrete instances —
contexts, environments, and memories — refuting the exact statement each
`sorry` stands for.

## The remaining gaps

1. **Capture instantiation erases peak identity** (`Retype.open_carg`, used
   at `capp` and `unpack`): the bound capture variable `.here` is one atomic
   peak with one stored authority and capability, while its image `C` may
   have zero droppable peaks (a ground witness — `open_carg_dpeak_fwd_false`)
   or several (a union argument — `open_carg_dpeak_unique_false`).

2. **Subsumption peak slack** (`sem_typ_app`'s `hps`, `sem_subtyp_arrow`'s
   identity-`Retype`): converting between the peaks of a variable's
   *declared* type and the peaks of the (super)type the elimination rule
   demands requires a peak-membership *equivalence*, but a well-typed
   environment can bind a variable whose stored peaks are strictly below its
   semantic type's peaks (`app_peak_slack_false`), and the antitone repair —
   stored peaks under-approximating declared peaks — is also refuted
   (`fundamental_sepcheck_underapprox_false`).

3. **Lock-stored separation facts** (`fundamental_sepcheck_global`): lock
   facts are consumed at arbitrary later program points with no budget in
   scope, and `EnvTyping` admits aliased droppable capture variables
   (`sepcheck_global_droppable_false`).

## Why the closure premise is rigid (the three-way pincer)

The closure denotations carry `env.DropSepIn cs` on their body conditions.
Could a different premise `P env m cs` close the transport gaps? No premise
exists, because three machine-checked constraints pin `P` from three sides:

* **Supply** (`dropSepTouch_unsuppliable`): at `app`, the caller owns only
  its own budget invariant — `DropSepIn` at the annotation's *peaks* (the
  variable `f`'s stored peak set is the annotation's peak set). In a
  pack/unpack-aliased environment (`env2`), `DropSepIn` of a single-peak
  budget holds vacuously while any *value-level* premise (droppable
  capabilities touching the budget's denotation must be disjoint) is false:
  the dead alias touches without peaking. So `P` must not demand more than
  the budget's peak pairs.

* **Discharge** (`dropSepTouch_insufficient`): at `abs`, `P cs` must imply
  the body judgment's `DropSepIn (cs.rename succ)`, whose droppable pairs
  are the *peaks* of the annotation — routed through variables' *stored*
  (declared-type) peak sets. A variable may under-fill its declared capture
  annotation (a closure value capturing nothing, declared at a two-peak
  capture set — `env5`), so its value's capabilities touch no droppable name
  while its stored peaks demand a pair. So `P` must demand at least the
  budget's peak pairs.

* **Transport**: hence `P` is exactly peak-pair separation (`DropSepIn`,
  up to equivalence), and its transport along `openVar` needs the
  peak-membership equivalence between a variable's stored peaks and its
  occurrence's peaks — which subsumption breaks (`app_peak_slack_false`).

The dead-set formulation itself ("everything is separate except an excused,
already-dropped set the budget avoids") is *implemented*: `TypeEnv.DropSepIn`
is defined in exactly that form (see `Denotation/Core.lean`), with peak-pair
separation derived as its intro/elim characterization (`pairs`/`of_pairs`,
restated here as `dropSepExcept_collapse`). The equivalence is also why the
re-phrasing cannot by itself repair anything: every transport obligation is
left intact. A *threaded* (global, non-existential) dead set would have to
mark the pack/unpack alias pair asymmetrically — per-name data that the
extension-only environment architecture cannot update, and per-location data
cannot express (`env2`'s two names share their capabilities).

Closing these gaps therefore requires a *static* change — making demands
peak-faithful across subsumption and instantiation — which is a type-system
design decision, not a proof device. -/

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

These refute the peak-membership equivalences needed by `sem_typ_app` (the
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

/-- The natural repair attempt — close the slack *antitonically*, by letting
a variable's stored peak set droppably **under-approximate** the peaks of its
declared type (weakening `EnvTyping`'s `ps = T.captureSet.peakset Γ` to
coverage) — is itself refuted. Stored peaks are the currency budgets pay in:
`sc_var` together with the `EquivP` premise of `sep_sc` lets a derivation
re-budget `{ε·x}` to the full capture set of `x`'s *declared* type (their
static peaks coincide), so the interpretation of `SepCheck` can demand
declared-type peak facts that an under-approximating environment no longer
reports. Concretely: with `x` declared at `cap {ε·c2}` but stored with empty
peaks, the budget `{ε·x} ∪ {ε·c1}` has no droppable peak pair — yet
`SepCheck (Γ,x) {ε·x} {ε·c1}` is derivable via `sep_sc`/`sc_var` ending in
`sep_droppable c2 c1`, and in an aliased environment its interpretation is
false. (Under the stored-peak *equality* of `EnvTyping`, the same world makes
the `DropSepIn` premise unsatisfiable and the instance vacuous — the equality
is load-bearing.) -/
theorem fundamental_sepcheck_underapprox_false :
    ¬ (∀ {s : Sig} (Γ : Ctx s) (T : Ty .capt s) (env : TypeEnv s) (m : Memory)
        (n : Nat) (ps : PeakSet s) (C1 C2 : CaptureSet (s,x)),
        SepCheck (Γ.push_var T) C1 C2 →
        EnvTyping Γ env m →
        Ty.val_denot env T m (.var (.free n)) →
        (∀ d, env.HasDroppablePeak ps.cs d → env.HasDroppablePeak T.captureSet d) →
        (env.extend_var n ps).DropSepIn (C1 ∪ C2) →
        CapabilitySet.Noninterference
          (C1.denot (env.extend_var n ps) m)
          (C2.denot (env.extend_var n ps) m)) := by
  intro h
  -- The world: `Γ2` (two aliased droppables cA = .there .here, cB = .here),
  -- extended with `x : cap {ε·cB}`, but `x` STORED with empty peaks.
  -- The check: `SepCheck {ε·x} {ε·cA}` via re-budgeting `{ε·x}` to `{ε·cB}`.
  have hval : Ty.val_denot env2 (.cap (.cvar (.M .epsilon) .here)) mem1
      (.var (.free 0)) := by
    simp only [Ty.val_denot]
    exact ⟨.wf_var (.wf_free (val := .capability .basic) rfl),
      .wf_var_free (val := .capability .basic) rfl,
      0, rfl, rfl, CapabilitySet.covers.here CapMode.Le.refl⟩
  have hpeaks_eq :
      CaptureSet.peaks (Γ2.push_var (.cap (.cvar (.M .epsilon) .here)))
        (.var (.M .epsilon) (.bound .here))
      = CaptureSet.peaks (Γ2.push_var (.cap (.cvar (.M .epsilon) .here)))
        (.cvar (.M .epsilon) (.there .here)) := by
    change CaptureSet.peaks (Ctx.push Γ2 (.var (.cap (.cvar (.M .epsilon) .here))))
        (.var (.M .epsilon) (.bound .here))
      = CaptureSet.peaks (Ctx.push Γ2 (.var (.cap (.cvar (.M .epsilon) .here))))
        (.cvar (.M .epsilon) (.there .here))
    rw [CaptureSet.peaks, CaptureSet.peaks, CaptureSet.peaksVarBound]
    simp only [Ty.captureSet]
    rw [CaptureSet.peaks]
    rfl
  have hsep : SepCheck (Γ2.push_var (.cap (.cvar (.M .epsilon) .here)))
      (.var (.M .epsilon) (.bound .here))
      (.cvar (.M .epsilon) (.there (.there .here))) := by
    refine .sep_sc (.sep_droppable ⟨rfl, rfl, ?_⟩) (.sc_var .here) ⟨?_, ?_⟩
    · intro heq
      cases heq
    · unfold CaptureSet.SubP
      rw [hpeaks_eq]
      exact CaptureSet.CoveredBy.refl'
    · unfold CaptureSet.SubP
      rw [hpeaks_eq]
      exact CaptureSet.CoveredBy.refl'
  have hdsep : (env2.extend_var 0 ⟨CaptureSet.empty, .empty⟩).DropSepIn
      ((CaptureSet.var (.M .epsilon) (.bound .here))
        ∪ (.cvar (.M .epsilon) (.there (.there .here)))) := by
    apply TypeEnv.DropSepIn.of_pairs
    intro c1 c2 a1 a2 hne hauth1 hauth2 hp1 hp2
    have key : ∀ (a : Access) (c : BVar ({},C,C,x) .cvar),
        (CaptureSet.cvar a c) ⊆
          compute_peaks (env2.extend_var 0 ⟨CaptureSet.empty, .empty⟩)
            ((CaptureSet.var (.M .epsilon) (.bound .here))
              ∪ (.cvar (.M .epsilon) (.there (.there .here)))) →
        c = .there (.there .here) := by
      intro a c hp
      rcases CaptureSet.cvar_subset_union_inv hp with h | h
      · exact absurd h CaptureSet.cvar_not_subset_empty
      · exact (CaptureSet.cvar_subset_cvar_inv h).2
    exact absurd ((key a1 c1 hp1).trans (key a2 c2 hp2).symm) hne
  exact noninterference_cap0_self_false
    (h Γ2 (.cap (.cvar (.M .epsilon) .here)) env2 mem1 0 ⟨CaptureSet.empty, .empty⟩
      _ _ hsep envtyping2 hval
      (fun d hd => absurd hd.2 TypeEnv.HasPeak.not_empty) hdsep)

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

/-! ## The dead-set formulation is the premise — and it changes no obligation

`TypeEnv.DropSepIn` *is defined* in the dead-set form (an excused set of
already-dropped capture variables, separation outside it, the budget's peaks
avoiding it — see `Denotation/Core.lean`). The collapse below records why
this re-phrasing, while it is the intended reading of the invariant, cannot
*by itself* repair any transport gap: with the dead set chosen per judgment
(existentially), the premise is logically equivalent to peak-pair separation
— the dead set may always be taken to be the complement of the budget's
peaks ("everything I am not using may as well be dead"). Consequently every
transport obligation of the closure premise, and every counterexample above,
applies to the dead-set phrasing verbatim. -/

/-- The collapse: the existential dead-set premise (here phrased via
`TypeEnv.HasPeak`) is equivalent to peak-pair separation. -/
theorem dropSepExcept_collapse (env : TypeEnv s) (C : CaptureSet s) :
    (∃ dead : BVar s .cvar → Prop, TypeEnv.DropSepExcept env dead ∧
      (∀ c, env.HasPeak C c → ¬ dead c)) ↔ env.DropSepIn C := by
  constructor
  · rintro ⟨dead, hdse, hdisj⟩
    exact ⟨dead, hdse, fun a c hp => hdisj c ⟨a, hp⟩⟩
  · rintro ⟨dead, hdse, havoid⟩
    exact ⟨dead, hdse, fun c hp => by
      obtain ⟨a, hsub⟩ := hp
      exact havoid a c hsub⟩

/-! ## The value-level ("spendable denotation") closure premise is refuted
from both sides

The remaining repair direction for the closure premise was to make it
*value-level*: instead of selecting droppable capture variables by the
budget's **peaks** (which subsumption and instantiation break), select them
by **capability contact** — any droppable name whose capabilities touch the
budget's denotation. Value-level statements transport perfectly (denotations
are preserved by `Retype` substitutions and shrink along `Subcapt`), so the
three transport gaps would vanish. The two theorems below show the premise
is nevertheless unusable: it can neither be *supplied* at the elimination
sites nor *consumed* at the creation sites. -/

/-- The value-level closure premise: any two distinct droppable capture
variables whose capabilities both touch the budget's denotation have disjoint
capabilities. -/
def DropSepTouch (env : TypeEnv s) (m : Memory) (C : CaptureSet s) : Prop :=
  ∀ (c1 c2 : BVar s .cvar),
    c1 ≠ c2 →
    env.lookup_cvar_auth c1 = .can_drop →
    env.lookup_cvar_auth c2 = .can_drop →
    (∃ mu l, ((env.lookup_cvar c1).2).hasmem mu l ∧ (C.denot env m).hasmem mu l) →
    (∃ mu l, ((env.lookup_cvar c2).2).hasmem mu l ∧ (C.denot env m).hasmem mu l) →
    CapabilitySet.disjoint (env.lookup_cvar c1).2 (env.lookup_cvar c2).2

/-- **Supply fails.** At `app`, all the caller owns is `DropSepIn` of its own
budget, whose peaks are the annotation's peaks. In the aliased world `env2`,
`DropSepIn {ε·cB}` holds vacuously (a single peak has no pairs), but
`DropSepTouch {ε·cB}` demands disjointness of the alias pair — both `cA` and
`cB` *touch* the budget's denotation `cap0` — which is false. A value-level
closure premise is strictly stronger than what elimination sites can pay. -/
theorem dropSepTouch_unsuppliable :
    ¬ (∀ {s : Sig} (Γ : Ctx s) (env : TypeEnv s) (m : Memory) (C : CaptureSet s),
        EnvTyping Γ env m →
        env.DropSepIn C →
        DropSepTouch env m C) := by
  intro h
  have hdsi : env2.DropSepIn (.cvar (.M .epsilon) .here) := by
    apply TypeEnv.DropSepIn.of_pairs
    intro c1 c2 a1 a2 hne h1 h2 hp1 hp2
    exact absurd
      (((CaptureSet.cvar_subset_cvar_inv hp1).2).trans
        ((CaptureSet.cvar_subset_cvar_inv hp2).2).symm)
      hne
  have ht := h Γ2 env2 mem1 (.cvar (.M .epsilon) .here) envtyping2 hdsi
  exact cap0_not_disjoint_self
    (ht (.there .here) .here (by intro heq; cases heq) rfl rfl
      ⟨.access .epsilon, 0, .here, .here⟩
      ⟨.access .epsilon, 0, .here, .here⟩)

/-- The closure value for the under-fill world: a lambda capturing nothing. -/
def absVal : HeapVal where
  unwrap := .abs CaptureSet.empty .top (.var (.bound .here))
  isVal := .abs
  reachability := {}

/-- The under-fill memory: `mem1` extended at location `1` with `absVal`. -/
def mem5 : Memory :=
  mem1.extend 1 absVal
    (.wf_abs .wf_empty .wf_top (.wf_var .wf_bound))
    rfl
    rfl

/-- The under-fill type: a function type whose capture annotation names both
droppable capture variables of `Γ2` — legally inhabited by `absVal`, which
captures *nothing*. -/
def T5 : Ty .capt ({},C,C) := .arrow .top Cb2 (.typ .top)

def Γ5 : Ctx ({},C,C,x) := Γ2.push_var T5

/-- The matching environment: `env2` extended with the variable bound to the
empty-capture closure at location `1`, stored (per `EnvTyping`) at the
declared type's peak set — both droppable capture variables. -/
def env5 : TypeEnv ({},C,C,x) :=
  env2.extend (.var 1 (T5.captureSet.peakset Γ2))

theorem envtyping5 : EnvTyping Γ5 env5 mem5 := by
  refine ⟨?_, rfl, ?_, ?_, ?_, rfl, ?_, rfl, ?_, ?_, ?_, rfl, ?_, rfl, trivial⟩
  · change Ty.val_denot env2 T5 mem5 (.var (.free 1))
    simp only [T5, Ty.val_denot]
    refine ⟨.wf_var (.wf_free (val := .val absVal) rfl), ?_, ?_⟩
    · exact .wf_union (.wf_var_free (val := .capability .basic) rfl)
        (.wf_var_free (val := .capability .basic) rfl)
    · refine ⟨CaptureSet.empty, .top, .var (.bound .here), rfl, .wf_empty, .empty, ?_⟩
      intro arg m' _ _ hdsep _
      exact absurd hdsep env2_not_dropsep
  · exact .wf_var_free (val := .capability .basic) rfl
  · exact .wf_unbound
  · exact .top
  · exact cap0_drop_free
  · exact .wf_var_free (val := .capability .basic) rfl
  · exact .wf_unbound
  · exact .top
  · exact cap0_drop_free

/-- **Discharge fails.** At `abs`, the closure premise must imply the body
judgment's `DropSepIn`, whose droppable pairs are the budget's *stored peaks*.
In the under-fill world `env5`, the variable's budget `{ε·x}` *touches* no
droppable capability at all (the closure value captures nothing, so its
denotation is empty) — `DropSepTouch` holds vacuously — while its stored
peaks are the declared annotation's two aliased droppable capture variables,
so `DropSepIn {ε·x}` is false. A value-level closure premise is strictly
weaker than what creation sites must pay. -/
theorem dropSepTouch_insufficient :
    ¬ (∀ {s : Sig} (Γ : Ctx s) (env : TypeEnv s) (m : Memory) (C : CaptureSet s),
        EnvTyping Γ env m →
        DropSepTouch env m C →
        env.DropSepIn C) := by
  intro h
  have htouch : DropSepTouch env5 mem5 (.var (.M .epsilon) (.bound .here)) := by
    intro c1 c2 hne h1 h2 ht1 ht2
    obtain ⟨mu, l, -, hd⟩ := ht1
    cases hd
  have hdsi := h Γ5 env5 mem5 (.var (.M .epsilon) (.bound .here)) envtyping5 htouch
  have hpk : compute_peaks env5 (.var (.M .epsilon) (.bound .here))
      = ((CaptureSet.cvar (.M .epsilon) (.there (.there .here)))
          ∪ (.cvar (.M .epsilon) (.there .here))) := by
    change ((CaptureSet.peaks Γ2
        ((CaptureSet.cvar (.M .epsilon) (.there .here))
          ∪ (.cvar (.M .epsilon) .here))).rename Rename.succ).applyAccess (.M .epsilon) = _
    rw [CaptureSet.peaks_union, CaptureSet.peaks, CaptureSet.peaks]
    rfl
  refine cap0_not_disjoint_self
    (hdsi.pairs (.there (.there .here)) (.there .here) (.M .epsilon) (.M .epsilon)
      (by intro heq; cases heq) rfl rfl ?_ ?_)
  · rw [hpk]
    exact .union_right_left .refl
  · rw [hpk]
    exact .union_right_right .refl

end CoreCapybara.Gaps
