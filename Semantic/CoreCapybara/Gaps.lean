import Semantic.CoreCapybara.Fundamental

/-! # Definition-level counterexamples for the irreducible proof gaps

The restored type system (the `sep_sc`/`seq_sc` subcapture rules,
unrestricted closure capture, and locks storing full `SepCheck` facts) leaves
five `sorry`s in the development. Each of them is not merely unproven but
*unprovable*: this file constructs explicit, concrete instances — contexts,
environments, and memories — refuting the exact statement each `sorry` stands
for.

Note that `sc_cvar` is restricted to `.access_only` capture variables (an
approved deviation), which makes droppable peaks monotone along `Subcapt` and
renders `TypeEnv.DropSepIn.of_subcapt` provable — that gap is gone. The
laundering counterexamples below survive the restriction: they expand an
`.access_only` capture variable whose *bound* mentions a droppable one, which
the restricted rule still permits. The `cabs` rule now requires borrow-only
bounds (`CaptureBound.BorrowOnly`, an approved deviation), so such contexts
cannot arise in *typing derivations* — but the refuted lemmas quantify over
arbitrary contexts, and the budget-relative invariant `DropSepIn` only sees
*syntactic* peaks of the budget, which `sc_cvar` escapes by moving a
capability under its bound's peaks. Exploiting the `cabs` restriction
therefore requires both a context-validity hypothesis on these lemmas and a
relativization of `DropSepIn` to bound-closed ("deep") peaks — a redesign of
the invariant and all its suppliers, left as future work.

All counterexamples share one tiny world: a memory `mem1` holding a single
capability cell at location `0`, and environments binding several capture
variables to the *same* capability `{ε·0}`. Such aliased environments are
well-typed (`EnvTyping` records only per-binding facts), which is the root of
every gap.
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

/-! ## Gap 1: `EnvTyping` does not imply the separation invariant

This refutes the obligation at the closure-forming rules
(`sem_typ_abs`/`tabs`/`cabs`/`wrap`, via `TypeEnv.DropSepIn.of_envtyping`):
their use-set is `{}`, so the only source for the body's `DropSepIn` would be
`EnvTyping` itself — but well-typed environments may alias droppable capture
variables. -/

theorem envtyping_dropsep_false :
    ¬ (∀ {s : Sig} {Γ : Ctx s} {env : TypeEnv s} {m : Memory} (C : CaptureSet s),
        EnvTyping Γ env m → env.DropSepIn C) := by
  intro h
  exact env2_not_dropsep (h Cb2 envtyping2)

/-! ## Gap 2: lock-stored `sep_droppable` facts

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

/-! ## The authority-laundering context

`Γ4` binds two droppable capture variables `c₁`, `c₂` and an `.access_only`
capture variable `c₃` whose bound is `{ε·c₁}`. Even the `.access_only`-restricted
`sc_cvar` applies to `c₃`, so `sep_sc`/`seq_sc` transfer separation or
sequencing evidence anchored at `(c₁, c₂)` to `c₃`, whose authority no longer
records droppability — and whose capability may alias `c₂`'s. -/

def Γ4 : Ctx ({},C,C,C) :=
  (((Ctx.empty).push_cvar .can_drop .unbound).push_cvar .can_drop .unbound).push_cvar
    .access_only (.bound (.cvar (.M .epsilon) .here))

def env4 : TypeEnv ({},C,C,C) :=
  (((TypeEnv.empty).extend_cvar cs0 cap0 .can_drop).extend_cvar
    cs0 cap0 .can_drop).extend_cvar cs0 cap0 .access_only

theorem envtyping4 : EnvTyping Γ4 env4 mem1 := by
  refine ⟨?_, ?_, ?_, rfl, ?_, rfl, ?_, ?_, ?_, rfl, ?_, rfl,
    ?_, ?_, ?_, rfl, ?_, rfl, trivial⟩
  · exact .wf_var_free (val := .capability .basic) rfl
  · exact .wf_bound (.wf_var_free (val := .capability .basic) rfl)
  · exact .set .refl
  · exact cap0_drop_free
  · exact .wf_var_free (val := .capability .basic) rfl
  · exact .wf_unbound
  · exact .top
  · exact cap0_drop_free
  · exact .wf_var_free (val := .capability .basic) rfl
  · exact .wf_unbound
  · exact .top
  · exact cap0_drop_free

/-- `c₃` (access-only, bound `{ε·c₁}`) of `Γ4`. -/
def c3 : BVar ({},C,C,C) .cvar := .here
/-- `c₁` (droppable) of `Γ4`. -/
def c1 : BVar ({},C,C,C) .cvar := .there .here
/-- `c₂` (droppable) of `Γ4`. -/
def c2 : BVar ({},C,C,C) .cvar := .there (.there .here)

theorem Γ4_closed : Γ4.IsClosed :=
  .push (.push (.push .empty (.cvar .unbound)) (.cvar .unbound))
    (.cvar (.bound .cvar))

theorem two_distinct_c1_c2 : Γ4.TwoDistinctDroppable c1 c2 :=
  ⟨rfl, rfl, by intro heq; cases heq⟩

/-- Any budget peaking only `c₃` and `c₂` satisfies the separation invariant
vacuously: `c₃` is access-only, so no *droppable pair* is peaked. -/
theorem dropsep_c3_c2 {C : CaptureSet ({},C,C,C)}
    (hpk : ∀ (a : Access) (c : BVar ({},C,C,C) .cvar),
      (CaptureSet.cvar a c) ⊆ compute_peaks env4 C → c = c3 ∨ c = c2) :
    env4.DropSepIn C := by
  intro ca cb a1 a2 hne h1 h2 hp1 hp2
  rcases hpk a1 ca hp1 with rfl | rfl
  · cases h1
  · rcases hpk a2 cb hp2 with rfl | rfl
    · cases h2
    · exact absurd rfl hne

/-! ## Gap 4: `SeqComp.cross_droppable` fails at `seq_sc`

Purely static: `seq_sc` + `sc_drop_mono` + `sc_cvar` launder the consuming
side of a `seq_drop` through the access-only `c₃`, so a `.drop`-mode peak of
the left budget need not be droppable. -/

theorem seqcomp_cross_droppable_false :
    ¬ (∀ {s : Sig} {Γ : Ctx s} {C1 C2 : CaptureSet s}
        {ca cb : BVar s .cvar} {a2 : Access},
        SeqComp Γ C1 C2 →
        (CaptureSet.cvar .drop ca) ⊆ C1.peaks Γ →
        (CaptureSet.cvar a2 cb) ⊆ C2.peaks Γ →
        Γ.TwoDistinctDroppable ca cb) := by
  intro h
  have hd : DisjCheck Γ4 (.cvar (.M .epsilon) c1) (.cvar (.M .epsilon) c2) :=
    .disj_droppable two_distinct_c1_c2
  have hs2 : SeqComp Γ4 ((CaptureSet.cvar (.M .epsilon) c1).applyDrop)
      (.cvar (.M .epsilon) c2) := .seq_drop hd
  have hsub3 : Subcapt Γ4 (.cvar (.M .epsilon) c3) (.cvar (.M .epsilon) c1) :=
    .sc_cvar .here
  have hsub3' : Subcapt Γ4 ((CaptureSet.cvar (.M .epsilon) c3).applyAccess .drop)
      ((CaptureSet.cvar (.M .epsilon) c1).applyAccess .drop) :=
    .sc_drop_mono hsub3
  have hseq : SeqComp Γ4 (.cvar .drop c3) (.cvar (.M .epsilon) c2) :=
    .seq_sc hsub3' hs2
  have hpa : (CaptureSet.cvar .drop c3) ⊆
      (CaptureSet.cvar .drop c3).peaks Γ4 := by
    rw [CaptureSet.peaks]
    exact .refl
  have hpb : (CaptureSet.cvar (.M .epsilon) c2) ⊆
      (CaptureSet.cvar (.M .epsilon) c2).peaks Γ4 := by
    rw [CaptureSet.peaks]
    exact .refl
  have htdd := h hseq hpa hpb
  cases htdd.1

/-! ## Gap 5: `fundamental_sepcheck` fails at `sep_sc`

`sep_droppable (c₁, c₂)` is laundered by `sep_sc`/`sc_cvar` into
`SepCheck Γ4 {ε·c₃} {ε·c₂}`. In `env4`, the conclusion's budget peaks only
`{c₃, c₂}` — no droppable pair, so the separation invariant holds vacuously —
yet both sides denote the same capability `cap0`, which interferes with
itself. -/

theorem fundamental_sepcheck_false :
    ¬ (∀ {s : Sig} {Γ : Ctx s} {C1 C2 : CaptureSet s},
        SepCheck Γ C1 C2 → SemSepCheck Γ C1 C2) := by
  intro h
  have hsd : SepCheck Γ4 (.cvar (.M .epsilon) c1) (.cvar (.M .epsilon) c2) :=
    .sep_droppable two_distinct_c1_c2
  have hsub3 : Subcapt Γ4 (.cvar (.M .epsilon) c3) (.cvar (.M .epsilon) c1) :=
    .sc_cvar .here
  have hsep : SepCheck Γ4 (.cvar (.M .epsilon) c3) (.cvar (.M .epsilon) c2) :=
    .sep_sc hsd hsub3
  have hdsep : env4.DropSepIn
      ((CaptureSet.cvar (.M .epsilon) c3) ∪ (.cvar (.M .epsilon) c2)) := by
    refine dropsep_c3_c2 ?_
    intro a c hp
    have hp0 : (CaptureSet.cvar a c) ⊆
        (compute_peaks env4 (.cvar (.M .epsilon) c3))
          ∪ (compute_peaks env4 (.cvar (.M .epsilon) c2)) := hp
    rcases CaptureSet.cvar_subset_union_inv hp0 with hp' | hp'
    · have hp'' : (CaptureSet.cvar a c) ⊆ (.cvar (.M .epsilon) c3) := hp'
      obtain ⟨_, hc⟩ := CaptureSet.cvar_subset_cvar_inv hp''
      exact Or.inl hc
    · have hp'' : (CaptureSet.cvar a c) ⊆ (.cvar (.M .epsilon) c2) := hp'
      obtain ⟨_, hc⟩ := CaptureSet.cvar_subset_cvar_inv hp''
      exact Or.inr hc
  have hni := h hsep Γ4_closed env4 mem1 envtyping4 hdsep
  exact noninterference_cap0_self_false hni

/-! ## Gap 6: the `SeqComp` bridge fails at `seq_sc`

The same laundering defeats the runtime sequencing bridge
(`captureSet_seqcomp_denot`): statically, `{drop·c₃}` may precede `{ε·c₂}`,
but at `env4` the consumed capability set is `cap0.to_drop` and the
continuation's is `cap0` — the same location is consumed and then used. -/

theorem seqcomp_denot_false :
    ¬ (∀ {s : Sig} {Γ : Ctx s} {C1 C2 : CaptureSet s}
        {env : TypeEnv s} {store : Memory},
        EnvTyping Γ env store → Γ.IsClosed →
        env.DropSepIn (C1 ∪ C2) → SeqComp Γ C1 C2 →
        (C1.denot env store).SeqComp (C2.denot env store)) := by
  intro h
  have hd : DisjCheck Γ4 (.cvar (.M .epsilon) c1) (.cvar (.M .epsilon) c2) :=
    .disj_droppable two_distinct_c1_c2
  have hs2 : SeqComp Γ4 ((CaptureSet.cvar (.M .epsilon) c1).applyDrop)
      (.cvar (.M .epsilon) c2) := .seq_drop hd
  have hsub3 : Subcapt Γ4 (.cvar (.M .epsilon) c3) (.cvar (.M .epsilon) c1) :=
    .sc_cvar .here
  have hsub3' : Subcapt Γ4 ((CaptureSet.cvar (.M .epsilon) c3).applyAccess .drop)
      ((CaptureSet.cvar (.M .epsilon) c1).applyAccess .drop) :=
    .sc_drop_mono hsub3
  have hseq : SeqComp Γ4 (.cvar .drop c3) (.cvar (.M .epsilon) c2) :=
    .seq_sc hsub3' hs2
  have hdsep : env4.DropSepIn
      ((CaptureSet.cvar .drop c3) ∪ (.cvar (.M .epsilon) c2)) := by
    refine dropsep_c3_c2 ?_
    intro a c hp
    have hp0 : (CaptureSet.cvar a c) ⊆
        (compute_peaks env4 (.cvar .drop c3))
          ∪ (compute_peaks env4 (.cvar (.M .epsilon) c2)) := hp
    rcases CaptureSet.cvar_subset_union_inv hp0 with hp' | hp'
    · have hp'' : (CaptureSet.cvar a c) ⊆ (.cvar .drop c3) := hp'
      obtain ⟨_, hc⟩ := CaptureSet.cvar_subset_cvar_inv hp''
      exact Or.inl hc
    · have hp'' : (CaptureSet.cvar a c) ⊆ (.cvar (.M .epsilon) c2) := hp'
      obtain ⟨_, hc⟩ := CaptureSet.cvar_subset_cvar_inv hp''
      exact Or.inr hc
  have hrt := h envtyping4 Γ4_closed hdsep hseq
  exact hrt (.access .epsilon) 0 .here .here

end CoreCapybara.Gaps
