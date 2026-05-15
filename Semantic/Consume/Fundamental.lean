import Semantic.Consume.Denotation
import Semantic.Consume.Semantics
namespace Consume

theorem typed_env_lookup_var
  (hts : EnvTyping Γ env store)
  (hx : Ctx.LookupVar Γ x T) :
  Ty.val_denot env T store (.var (.free (env.lookup_var x).1)) := by
  induction hx generalizing store
  case here =>
    -- The environment must match the context structure
    rename_i Γ0 T0
    cases env with
    | extend env0 info =>
      cases info with
      | var n ps =>
        simp only [EnvTyping, TypeEnv.lookup_var] at hts ⊢
        -- Apply weaken_val_denot equivalence
        have heqv := weaken_val_denot (env:=env0) (x:=n) (ps:=ps) (T:=T0)
        apply (Denot.equiv_to_imply heqv).1
        exact hts.1
  case there b =>
    -- Need to handle three cases based on the binding kind
    rename_i k Γ0 x0 T0 binding hlk
    cases binding
    case var =>
      -- binding is .var Tb
      rename_i Tb
      cases env with
      | extend env0 info =>
        cases info with
        | var n ps =>
          simp only [EnvTyping, TypeEnv.lookup_var] at hts ⊢
          obtain ⟨_, _, henv0⟩ := hts
          -- Apply IH to get the result for env0
          have hih := b henv0
          -- Apply weakening
          have heqv := weaken_val_denot (env:=env0) (x:=n) (ps:=ps) (T:=T0)
          apply (Denot.equiv_to_imply heqv).1
          exact hih
    case tvar =>
      -- binding is .tvar Sb
      rename_i Sb
      match env with
      | .extend env0 (.tvar d) =>
        simp only [EnvTyping, TypeEnv.lookup_var] at hts ⊢
        obtain ⟨_, _, _, _, _, henv0⟩ := hts
        have hih := b henv0
        have heqv := tweaken_val_denot (env:=env0) (d:=d) (T:=T0)
        apply (Denot.equiv_to_imply heqv).1
        exact hih
    case cvar =>
      -- binding is .cvar Bb
      rename_i Bb
      match env with
      | .extend env0 (.cvar cs cap) =>
        simp only [EnvTyping, TypeEnv.lookup_var] at hts ⊢
        obtain ⟨_, _, _, _, henv0⟩ := hts
        have hih := b henv0
        have heqv := cweaken_val_denot (env:=env0) (cs:=cs) (cap:=cap) (T:=T0)
        apply (Denot.equiv_to_imply heqv).1
        exact hih
  case lock ih =>
    change EnvTyping _ env store at hts
    exact ih hts


theorem typed_env_lookup_var_reachability
  (hts : EnvTyping Γ env m)
  (hx : Ctx.LookupVar Γ x T) :
  reachability_of_loc m.heap (env.lookup_var x).1 ⊆ T.captureSet.denot env m := by
  -- Use typed_env_lookup_var to get the value denotation
  have hval := typed_env_lookup_var hts hx
  -- Apply val_denot_enforces_captures to get reachability bound
  have hreach := val_denot_enforces_captures hts (.var (.free (env.lookup_var x).1)) hval
  -- resolve_reachability of a free variable is reachability_of_loc by definition
  simp only [resolve_reachability] at hreach
  exact hreach

theorem sem_typ_var
  (hx : Γ.LookupVar x T) :
  {} # Γ ⊨ (Exp.var (.bound x)) :
    (.typ (T.refineCaptureSet (.var .epsilon (.bound x)))) := by
  intro env m hts _
  apply Eval.eval_var
  simp only [Ty.exi_val_denot]
  -- From typed_env_lookup_var, we get that .var (.free n) satisfies T
  have h_lookup := typed_env_lookup_var hts hx
  have hpeaks :
      compute_peaks env T.captureSet = compute_peaks env (.var .epsilon (.bound x)) := by
    rw [← compute_peaks_correct hts T.captureSet]
    rw [← compute_peaks_correct hts (.var .epsilon (.bound x))]
    simpa using (CaptureSet.var_peaks (m := .epsilon) (x := x) (T := T) hx).symm
  have h_refined := val_denot_refine (x := .bound x) h_lookup hpeaks
  simp only [Var.subst, Subst.from_TypeEnv] at h_refined
  exact h_refined


theorem expand_captures_eq_ground_denot (cs : CaptureSet {}) (m : Memory) :
  expand_captures m.heap cs = cs.ground_denot m := by
  induction cs with
  | empty => rfl
  | var m v =>
    cases v with
    | free x => rfl
    | bound bv => cases bv
  | cvar m cv => cases cv
  | union cs1 cs2 ih1 ih2 =>
    simp only [expand_captures, CaptureSet.ground_denot, ih1, ih2]

theorem typed_env_lookup_cvar_aux
  (hts : EnvTyping Γ env m)
  (hc : Ctx.LookupCVar Γ c useM cb locked) :
  ((env.lookup_cvar c).1.ground_denot m).BoundedBy (cb.denot env m) := by
  induction hc generalizing m
  case here =>
    rename_i Γ' cb'
    match env with
    | .extend env' (.cvar cs cap) =>
      simp only [EnvTyping, TypeEnv.lookup_cvar] at hts ⊢
      obtain ⟨_, _, hbound, hcap_eq, _⟩ := hts
      have hcb := rebind_capturebound_denot
        (Rebind.cweaken (env := env') (cs := cs) (cap := cap)) cb'
      rw [congrFun hcb m] at hbound
      rw [← hcap_eq]
      exact hbound
  case there b0 _lk b hc_prev ih =>
    cases b
    case var =>
      rename_i Γ' c' Tb
      match env with
      | .extend env' (.var x ps) =>
        simp only [EnvTyping, TypeEnv.lookup_cvar] at hts ⊢
        obtain ⟨_, _, henv'⟩ := hts
        have hih := ih henv'
        have hcb := rebind_capturebound_denot (Rebind.weaken (env := env') (x := x) (ps := ps)) b0
        rw [congrFun hcb m] at hih
        simpa [TypeEnv.extend_var] using hih
    case tvar =>
      rename_i Γ' c' Sb
      match env with
      | .extend env' (.tvar d) =>
        simp only [EnvTyping, TypeEnv.lookup_cvar] at hts ⊢
        obtain ⟨_, _, _, _, _, henv'⟩ := hts
        have hih := ih henv'
        have hcb := rebind_capturebound_denot (Rebind.tweaken (env := env') (d := d)) b0
        rw [congrFun hcb m] at hih
        simpa [TypeEnv.extend_tvar] using hih
    case cvar =>
      rename_i Γ' c' Bb
      match env with
      | .extend env' (.cvar cs cap) =>
        simp only [EnvTyping, TypeEnv.lookup_cvar] at hts ⊢
        obtain ⟨_, _, _, _, henv'⟩ := hts
        have hih := ih henv'
        have hcb :=
          rebind_capturebound_denot
            (Rebind.cweaken (env := env') (cs := cs) (cap := cap)) b0
        rw [congrFun hcb m] at hih
        simpa [TypeEnv.extend_cvar] using hih
  case lock ih =>
    change EnvTyping _ env m at hts
    exact ih hts

theorem typed_env_cvar_cap_eq
  {Γ : Ctx s} {env : TypeEnv s} {m : Memory}
  (hts : EnvTyping Γ env m)
  (c : BVar s .cvar) :
  (env.lookup_cvar c).2 = (env.lookup_cvar c).1.ground_denot m := by
  induction Γ with
  | empty =>
    cases c
  | push Γ' b ih =>
    cases b
    case var T =>
      match env with
      | .extend env' (.var n ps) =>
        simp only [EnvTyping] at hts
        obtain ⟨_, _, henv'⟩ := hts
        cases c with
        | there c' => exact ih henv' c'
    case tvar S =>
      match env with
      | .extend env' (.tvar d) =>
        simp only [EnvTyping] at hts
        obtain ⟨_, _, _, _, _, henv'⟩ := hts
        cases c with
        | there c' => exact ih henv' c'
    case cvar useM B =>
      match env with
      | .extend env' (.cvar cs cap) =>
        simp only [EnvTyping] at hts
        obtain ⟨_, _, _, hcap_eq, henv'⟩ := hts
        cases c with
        | here => exact hcap_eq
        | there c' => exact ih henv' c'
  | lock Γ' ih =>
    change EnvTyping Γ' env m at hts
    exact ih hts c
/-- `applyMut` on a `CaptureSet {}` commutes with `ground_denot`. -/
private theorem captureSet_ground_denot_applyMut_comm
    {C : CaptureSet {}} {m : Memory} {mty : Mutability} :
    (C.applyMut mty).ground_denot m = (C.ground_denot m).applyMut mty := by
  cases mty with
  | epsilon => rfl
  | ro =>
    simp only [CaptureSet.applyMut_ro, CapabilitySet.applyMut]
    exact ground_denot_applyRO_comm.symm

/-- `applyMut` commutes with `subst`. -/
private theorem captureSet_subst_applyMut_comm
    {s1 s2 : Sig} (C : CaptureSet s1) (σ : Subst s1 s2) (mty : Mutability) :
    (C.applyMut mty).subst σ = (C.subst σ).applyMut mty := by
  cases mty with
  | epsilon => rfl
  | ro =>
    simp only [CaptureSet.applyMut_ro]
    induction C with
    | empty => rfl
    | union C1 C2 ih1 ih2 =>
      simp only [CaptureSet.applyRO, CaptureSet.subst, ih1, ih2]
    | var m' v => cases v <;> rfl
    | cvar m' c =>
      simp only [CaptureSet.applyRO, CaptureSet.subst]
      cases m' with
      | epsilon => rfl
      | ro => simp [CaptureSet.applyMut, CaptureSet.applyRO_applyRO]

/-- `applyMut` on a general `CaptureSet s` commutes with `denot`. -/
private theorem captureSet_denot_applyMut_comm
    {s : Sig} {env : TypeEnv s} {C : CaptureSet s} {store : Memory} {mty : Mutability} :
    (C.applyMut mty).denot env store = (C.denot env store).applyMut mty := by
  unfold CaptureSet.denot
  rw [captureSet_subst_applyMut_comm, captureSet_ground_denot_applyMut_comm]

/-- `Ty.captureSet T` has size at most `sizeOf T`. -/
private theorem sizeOf_captureSet_le {s : Sig} (T : Ty .capt s) :
    sizeOf T.captureSet ≤ sizeOf T := by
  cases T <;> simp [Ty.captureSet] <;> omega

/-- For a peaks-only capture set, `peaks` is the identity. -/
private theorem peaks_of_peaksOnly {s : Sig} {Γ : Ctx s}
    {P : CaptureSet s} (hP : P.PeaksOnly) :
    P.peaks Γ = P := by
  induction hP with
  | empty => simp only [CaptureSet.peaks]
  | union _ _ ih1 ih2 =>
    simp only [CaptureSet.peaks]
    rw [ih1, ih2]
    rfl
  | cvar => simp only [CaptureSet.peaks]

/-- From `hasmem mu l (C.applyMut m)`, extract a witness for `l` in `C`. -/
private theorem hasmem_of_applyMut {C : CapabilitySet} {m : Mutability} {mu : CapMode}
    {l : Nat} (h : (C.applyMut m).hasmem mu l) :
    ∃ mu', C.hasmem mu' l := by
  cases m with
  | epsilon => exact ⟨mu, h⟩
  | ro =>
    simp only [CapabilitySet.applyMut] at h
    obtain ⟨mu', _, hm⟩ := CapabilitySet.hasmem_applyRO_iff.mp h
    exact ⟨mu', hm⟩

/-- Lift `hasmem` through `applyMut`: given `hasmem mu l C`, produce a witness
    for `l` in `C.applyMut m` (with possibly different mode). -/
private theorem hasmem_applyMut_lift {C : CapabilitySet} {mu : CapMode}
    {l : Nat} (h : C.hasmem mu l) (m : Mutability) :
    ∃ mu', (C.applyMut m).hasmem mu' l := by
  cases m with
  | epsilon => exact ⟨mu, h⟩
  | ro =>
    simp only [CapabilitySet.applyMut]
    exact ⟨mu.applyRO, CapabilitySet.hasmem_applyRO_of_hasmem h⟩

/-- Subset on `CapabilitySet` preserves location membership (modulo mode). -/
private theorem hasmem_of_capabilitySet_subset {C1 C2 : CapabilitySet} (hsub : C1 ⊆ C2)
    {mu : CapMode} {l : Nat} (h : C1.hasmem mu l) :
    ∃ mu', C2.hasmem mu' l := by
  induction hsub generalizing mu with
  | refl => exact ⟨mu, h⟩
  | empty => exact (CapabilitySet.not_hasmem_empty h).elim
  | trans _ _ ih1 ih2 =>
    obtain ⟨mu', h'⟩ := ih1 h
    exact ih2 h'
  | union_left _ _ ih1 ih2 =>
    cases h with
    | left h' => exact ih1 h'
    | right h' => exact ih2 h'
  | union_right_left =>
    exact ⟨mu, CapabilitySet.hasmem.left h⟩
  | union_right_right =>
    exact ⟨mu, CapabilitySet.hasmem.right h⟩
  | cap_ro =>
    cases h
    exact ⟨.access .epsilon, CapabilitySet.hasmem.here⟩

/-- Helper: from `consumable` on a peaks-only capture set, extract a
    `.consume`-unlocked cvar witness for any element of its denotation. The
    proof is by induction on `PeaksOnly`, which only has `empty | union | cvar`
    cases — no `var .bound x` recursion is needed. -/
private theorem consumable_to_consume_witness_peaks
    {s : Sig} {Γ : Ctx s} {env : TypeEnv s} {store : Memory}
    {P : CaptureSet s} (hP : P.PeaksOnly) {l : Nat} {mu : CapMode}
    (hts : EnvTyping Γ env store)
    (hcons : P.consumable Γ)
    (hmem : (P.denot env store).hasmem mu l) :
    ∃ c B mu', Γ.LookupCVar c .consume B false ∧
      ((env.lookup_cvar c).2).hasmem mu' l := by
  induction hP generalizing mu with
  | empty =>
    simp only [CaptureSet.denot, CaptureSet.subst, CaptureSet.ground_denot] at hmem
    exact (CapabilitySet.not_hasmem_empty hmem).elim
  | union hP1 hP2 ih1 ih2 =>
    rename_i C1 C2
    have hcons1 : C1.consumable Γ := by
      intro m' c' hsub
      apply hcons m' c'
      rw [CaptureSet.peaks]
      exact hsub.union_right_left
    have hcons2 : C2.consumable Γ := by
      intro m' c' hsub
      apply hcons m' c'
      rw [CaptureSet.peaks]
      exact hsub.union_right_right
    have hunion : (C1.union C2).denot env store
        = C1.denot env store ∪ C2.denot env store := rfl
    rw [hunion] at hmem
    cases hmem with
    | left hm => exact ih1 hcons1 hm
    | right hm => exact ih2 hcons2 hm
  | cvar =>
    rename_i m c
    have hpeak : ConsumablePeak Γ c := by
      apply hcons m c
      rw [CaptureSet.peaks]
      exact CaptureSet.Subset.refl
    cases hpeak with
    | lookup hLookup =>
      rename_i B
      have hdenot :
          (CaptureSet.cvar m c).denot env store
            = ((env.lookup_cvar c).2).applyMut m := by
        change ((env.lookup_cvar c).1.applyMut m).ground_denot store = _
        rw [captureSet_ground_denot_applyMut_comm, ← typed_env_cvar_cap_eq hts c]
      rw [hdenot] at hmem
      obtain ⟨mu', hmem'⟩ := hasmem_of_applyMut hmem
      exact ⟨c, B, mu', hLookup, hmem'⟩

mutual

/-- Membership in `C.denot env store` is preserved when projecting to
    `(compute_peaks env C).denot`. Empty/union/cvar cases hold by direct
    computation. The `.var .bound x` case delegates to
    `hasmem_compute_peaks_denot_var_bound`, which in turn recursively calls
    this lemma on `T_x.captureSet` at the smaller context `Γ_rest`. -/
private theorem hasmem_compute_peaks_denot
    {s : Sig} {Γ : Ctx s} {env : TypeEnv s} {store : Memory}
    (hts : EnvTyping Γ env store) (hΓ : Γ.IsClosed)
    (C : CaptureSet s) (hC : C.IsClosed) {l : Nat} {mu : CapMode}
    (hmem : (C.denot env store).hasmem mu l) :
    ∃ mu', ((compute_peaks env C).denot env store).hasmem mu' l := by
  match C, hC, hmem with
  | .empty, _, hmem =>
    simp only [CaptureSet.denot, CaptureSet.subst, CaptureSet.ground_denot] at hmem
    exact (CapabilitySet.not_hasmem_empty hmem).elim
  | .union C1 C2, hC, hmem =>
    cases hC with | union hC1 hC2 =>
    have hunion : (C1.union C2).denot env store
        = C1.denot env store ∪ C2.denot env store := rfl
    rw [hunion] at hmem
    match hmem with
    | .left hm =>
      obtain ⟨mu', hm'⟩ := hasmem_compute_peaks_denot hts hΓ C1 hC1 hm
      refine ⟨mu', ?_⟩
      change ((compute_peaks env C1).denot env store
              ∪ (compute_peaks env C2).denot env store).hasmem mu' l
      exact .left hm'
    | .right hm =>
      obtain ⟨mu', hm'⟩ := hasmem_compute_peaks_denot hts hΓ C2 hC2 hm
      refine ⟨mu', ?_⟩
      change ((compute_peaks env C1).denot env store
              ∪ (compute_peaks env C2).denot env store).hasmem mu' l
      exact .right hm'
  | .cvar m c, _, hmem =>
    refine ⟨mu, ?_⟩
    change (CaptureSet.cvar m c).denot env store |>.hasmem mu l
    exact hmem
  | .var m (.bound x), _, hmem =>
    exact hasmem_compute_peaks_denot_var_bound hts hΓ hmem
  | .var m (.free n), hC, _ =>
    -- `.var m (.free n)` cannot be closed: `CaptureSet.IsClosed` has no
    -- constructor for `.var .free`, so `hC` is vacuous.
    cases hC
termination_by 2 * (sizeOf Γ + sizeOf C) + 1

/-- The `.var .bound x` arm of `hasmem_compute_peaks_denot`.

    Proof outline (mutually recursive with `hasmem_compute_peaks_denot` via
    `termination_by sizeOf Γ`):
    - `.here` case under `.var T` push: by `val_denot_enforces_captures` on
      x's stored value, lift `reachability_of_loc store.heap fx` into
      `T.captureSet.denot env_rest store`, recurse on `T.captureSet` at
      `Γ_rest`, then rebind via `Rename.succ` and commute applyMut.
    - `.there` cases (var/tvar/cvar push): recurse on the smaller `Γ_rest`.
    - `.lock` case: forward (env unchanged across lock).

    Each non-base step is mechanical bookkeeping with
    `rebind_captureset_denot`, `rebind_compute_peaks`,
    `captureSet_ground_denot_applyMut_comm`, and `hasmem_of_subset` /
    `hasmem_of_applyMut`. -/
private theorem hasmem_compute_peaks_denot_var_bound
    {s : Sig} {Γ : Ctx s} {env : TypeEnv s} {store : Memory}
    (hts : EnvTyping Γ env store) (hΓ : Γ.IsClosed)
    {x : BVar s .var} {m : Mutability} {l : Nat} {mu : CapMode}
    (hmem : ((CaptureSet.var m (.bound x)).denot env store).hasmem mu l) :
    ∃ mu', ((compute_peaks env (CaptureSet.var m (.bound x))).denot env store).hasmem mu' l := by
  match s, Γ, env, hts, hΓ, x, hmem with
  | _, .empty, .empty, _, _, x, _ => cases x
  | _, .push Γ_rest (.var T), .extend env_rest (.var n ps), hts, hΓ, .here, hmem =>
    obtain ⟨hval_T, hps_eq, hts_rest⟩ := hts
    cases hΓ with | push hΓ_rest hb =>
    cases hb with | var hT =>
    have hT_cs : T.captureSet.IsClosed := Ty.captureSet_isClosed hT
    -- (.var m (.bound .here)).denot env store = (reachability_of_loc store.heap n).applyMut m.
    change CapabilitySet.hasmem mu l
      ((reachability_of_loc store.heap n).applyMut m) at hmem
    obtain ⟨mu0, hmem0⟩ := hasmem_of_applyMut hmem
    -- Bridge: fx's heap reachability ⊆ T.captureSet.denot env_rest store.
    have hreach_sub : reachability_of_loc store.heap n ⊆ T.captureSet.denot env_rest store := by
      have h := val_denot_enforces_captures hts_rest (.var (.free n)) hval_T
      simp only [resolve_reachability] at h
      exact h
    -- Promote hasmem through subset.
    obtain ⟨mu1, hmem_T⟩ := hasmem_of_capabilitySet_subset hreach_sub hmem0
    -- Recurse on T.captureSet at Γ_rest (sizeOf Γ_rest < sizeOf Γ).
    obtain ⟨mu2, hmem_cp⟩ :=
      hasmem_compute_peaks_denot hts_rest hΓ_rest T.captureSet hT_cs hmem_T
    -- Lift back to env via rebind: denot env_rest = denot env_extended after rename.
    have hcp_denot := rebind_captureset_denot
      (ρ := @Rebind.weaken _ env_rest n ps)
      (compute_peaks env_rest T.captureSet)
    rw [hcp_denot] at hmem_cp
    -- Translate the renamed compute_peaks to compute_peaks env (T.captureSet.rename Rename.succ).
    have hcp_rename := rebind_compute_peaks
      (ρ := @Rebind.weaken _ env_rest n ps) T.captureSet
    rw [hcp_rename] at hmem_cp
    -- hmem_cp now lives at `compute_peaks env (T.captureSet.rename Rename.succ)`.
    -- Apply applyMut m: get a witness for the m-mutated version.
    obtain ⟨mu_final, h_final⟩ :=
      hasmem_applyMut_lift hmem_cp m
    -- ps.cs = compute_peaks env_rest T.captureSet via hps_eq + compute_peaks_correct.
    have hps_cs : ps.cs = compute_peaks env_rest T.captureSet := by
      rw [hps_eq]
      change T.captureSet.peaks Γ_rest = _
      exact compute_peaks_correct hts_rest T.captureSet
    -- Build the equality lifting the renamed compute_peaks back through applyMut m.
    have hcp_eq : compute_peaks (env_rest.extend_var n ps) (CaptureSet.var m (.bound BVar.here))
                = (compute_peaks (env_rest.extend_var n ps)
                    (T.captureSet.rename Rename.succ)).applyMut m := by
      change ((ps.rename Rename.succ).cs.applyMut m) = _
      change (ps.cs.rename Rename.succ).applyMut m = _
      rw [hps_cs, hcp_rename]
      rfl
    refine ⟨mu_final, ?_⟩
    -- Convert env's `extend (.var n ps)` form to `extend_var n ps` (definitionally equal).
    change CapabilitySet.hasmem mu_final l
      ((compute_peaks (env_rest.extend_var n ps) (CaptureSet.var m (.bound BVar.here))).denot
        (env_rest.extend_var n ps) store)
    rw [hcp_eq, captureSet_denot_applyMut_comm]
    exact h_final

  | _, .push Γ_rest (.var T), .extend env_rest (.var n ps), hts, hΓ, .there x', hmem =>
    obtain ⟨_, _, hts_rest⟩ := hts
    cases hΓ with | push hΓ_rest _ =>
    -- The captureSet `.var m (.bound (.there x'))` equals
    -- `(.var m (.bound x')).rename Rename.succ` definitionally.
    change CapabilitySet.hasmem mu l
      (((CaptureSet.var m (.bound x')).rename Rename.succ).denot
        (env_rest.extend_var n ps) store) at hmem
    have hC := rebind_captureset_denot
      (ρ := @Rebind.weaken _ env_rest n ps)
      (CaptureSet.var m (.bound x'))
    have hmem_rest : ((CaptureSet.var m (.bound x')).denot env_rest store).hasmem mu l := by
      rw [hC]; exact hmem
    obtain ⟨mu', hmem'⟩ := hasmem_compute_peaks_denot_var_bound hts_rest hΓ_rest hmem_rest
    refine ⟨mu', ?_⟩
    change CapabilitySet.hasmem mu' l
      ((compute_peaks (env_rest.extend_var n ps)
         ((CaptureSet.var m (.bound x')).rename Rename.succ)).denot
        (env_rest.extend_var n ps) store)
    have hcp_rename := rebind_compute_peaks
      (ρ := @Rebind.weaken _ env_rest n ps)
      (CaptureSet.var m (.bound x'))
    have hcp_denot := rebind_captureset_denot
      (ρ := @Rebind.weaken _ env_rest n ps)
      (compute_peaks env_rest (CaptureSet.var m (.bound x')))
    rw [hcp_denot, hcp_rename] at hmem'
    exact hmem'
  | _, .push Γ_rest (.tvar S), .extend env_rest (.tvar d), hts, hΓ, .there x', hmem =>
    obtain ⟨_, _, _, _, _, hts_rest⟩ := hts
    cases hΓ with | push hΓ_rest _ =>
    change CapabilitySet.hasmem mu l
      (((CaptureSet.var m (.bound x')).rename Rename.succ).denot
        (env_rest.extend_tvar d) store) at hmem
    have hC := rebind_captureset_denot
      (ρ := @Rebind.tweaken _ env_rest d)
      (CaptureSet.var m (.bound x'))
    have hmem_rest : ((CaptureSet.var m (.bound x')).denot env_rest store).hasmem mu l := by
      rw [hC]; exact hmem
    obtain ⟨mu', hmem'⟩ := hasmem_compute_peaks_denot_var_bound hts_rest hΓ_rest hmem_rest
    refine ⟨mu', ?_⟩
    change CapabilitySet.hasmem mu' l
      ((compute_peaks (env_rest.extend_tvar d)
         ((CaptureSet.var m (.bound x')).rename Rename.succ)).denot
        (env_rest.extend_tvar d) store)
    have hcp_rename := rebind_compute_peaks
      (ρ := @Rebind.tweaken _ env_rest d)
      (CaptureSet.var m (.bound x'))
    have hcp_denot := rebind_captureset_denot
      (ρ := @Rebind.tweaken _ env_rest d)
      (compute_peaks env_rest (CaptureSet.var m (.bound x')))
    rw [hcp_denot, hcp_rename] at hmem'
    exact hmem'
  | _, .push Γ_rest (.cvar md B), .extend env_rest (.cvar cs cap), hts, hΓ, .there x', hmem =>
    obtain ⟨_, _, _, _, hts_rest⟩ := hts
    cases hΓ with | push hΓ_rest _ =>
    change CapabilitySet.hasmem mu l
      (((CaptureSet.var m (.bound x')).rename Rename.succ).denot
        (env_rest.extend_cvar cs cap) store) at hmem
    have hC := rebind_captureset_denot
      (ρ := @Rebind.cweaken _ env_rest cs cap)
      (CaptureSet.var m (.bound x'))
    have hmem_rest : ((CaptureSet.var m (.bound x')).denot env_rest store).hasmem mu l := by
      rw [hC]; exact hmem
    obtain ⟨mu', hmem'⟩ := hasmem_compute_peaks_denot_var_bound hts_rest hΓ_rest hmem_rest
    refine ⟨mu', ?_⟩
    change CapabilitySet.hasmem mu' l
      ((compute_peaks (env_rest.extend_cvar cs cap)
         ((CaptureSet.var m (.bound x')).rename Rename.succ)).denot
        (env_rest.extend_cvar cs cap) store)
    have hcp_rename := rebind_compute_peaks
      (ρ := @Rebind.cweaken _ env_rest cs cap)
      (CaptureSet.var m (.bound x'))
    have hcp_denot := rebind_captureset_denot
      (ρ := @Rebind.cweaken _ env_rest cs cap)
      (compute_peaks env_rest (CaptureSet.var m (.bound x')))
    rw [hcp_denot, hcp_rename] at hmem'
    exact hmem'
  | _, .lock Γ_rest, env, hts, hΓ, x, hmem =>
    -- Lock does not change env. EnvTyping forwards; recurse on Γ_rest.
    have hts_rest : EnvTyping Γ_rest env store := hts
    cases hΓ with | lock hΓ_rest =>
    exact hasmem_compute_peaks_denot_var_bound hts_rest hΓ_rest hmem
termination_by 2 * (sizeOf Γ + sizeOf (CaptureSet.var m (.bound x)))
decreasing_by
  all_goals simp_wf
  all_goals try omega
  all_goals (have := sizeOf_captureSet_le T; omega)

end

/-- Bridge theorem: from a syntactic `consumable Γ C` premise and a semantic
    membership of location `l` in `C`'s denotation, extract a `.consume`-unlocked
    cvar witness `c` whose runtime cap contains `l`.

    The proof reduces to the peaks-only case by showing that any element of
    `C.denot` is also in `(compute_peaks env C).denot` — the syntactic
    `compute_peaks` produces a `PeaksOnly` capture set, on which the helper
    `consumable_to_consume_witness_peaks` applies structurally. -/
theorem consumable_to_consume_witness
    {s : Sig} {Γ : Ctx s} {env : TypeEnv s} {store : Memory}
    {C : CaptureSet s} {l : Nat} {mu : CapMode}
    (hts : EnvTyping Γ env store) (hΓ : Γ.IsClosed)
    (hC : C.IsClosed)
    (hcons : C.consumable Γ)
    (hmem : (C.denot env store).hasmem mu l) :
    ∃ c B mu', Γ.LookupCVar c .consume B false ∧
      ((env.lookup_cvar c).2).hasmem mu' l := by
  -- Reduce to the peaks-only helper.
  let P := compute_peaks env C
  have hP : P.PeaksOnly := compute_peaks_is_peak env C
  -- `C.peaks Γ = compute_peaks env C` under EnvTyping.
  have hpeaks_eq : C.peaks Γ = P := compute_peaks_correct hts C
  -- For a PeaksOnly capture set, taking peaks again is idempotent.
  have hPP : P.peaks Γ = P := peaks_of_peaksOnly hP
  -- Consumability transfers to `P`.
  have hcons' : P.consumable Γ := by
    intro m' c' hsub
    apply hcons m' c'
    rw [hpeaks_eq]
    rw [hPP] at hsub
    exact hsub
  -- Membership: `l` is in `P`'s denotation, via the bridge lemma.
  obtain ⟨mu', hmem'⟩ := hasmem_compute_peaks_denot hts hΓ C hC hmem
  exact consumable_to_consume_witness_peaks hP hts hcons' hmem'

/-- `to_drop` rewrites every cap mode to `.drop`, so existing membership at any
mode transfers to `.drop`-membership in the rewritten capability set. -/
private theorem CapabilitySet.hasmem_to_drop_drop
    {C : CapabilitySet} {mu : CapMode} {l : Nat}
    (h : C.hasmem mu l) : C.to_drop.hasmem .drop l := by
  induction h with
  | here =>
    -- C = .cap mu l, to_drop = .cap .drop l
    exact CapabilitySet.hasmem.here
  | left _ ih => exact CapabilitySet.hasmem.left ih
  | right _ ih => exact CapabilitySet.hasmem.right ih

/-- A consume-unlocked cvar's runtime denotation is contained in the
context's `consumeset.cs` denotation. Structural recursion on `Γ` walks
through the bindings; the `.lock` case is ruled out because crossing a lock
forces `locked = true`. -/
private theorem consumeset_hasmem_via_cs
    {s : Sig} {Γ : Ctx s} {env : TypeEnv s} {store : Memory}
    {c : BVar s .cvar} {B : CaptureBound s} {l : Nat} {mu : CapMode}
    (hlk : Γ.LookupCVar c .consume B false)
    (hmem : ((env.lookup_cvar c).1.ground_denot store).hasmem mu l) :
    (Γ.consumeset.cs.denot env store).hasmem mu l := by
  induction Γ with
  | empty => cases hlk
  | push Γ' b ih =>
    cases b with
    | var T =>
      cases env with | extend env' info =>
      cases info with | var n ps =>
      cases hlk with
      | there hlk' =>
        -- hmem definitionally equals `((env'.lookup_cvar _).1.ground_denot store).hasmem mu l`
        have ihres := ih hlk' hmem
        change ((Γ'.consumeset.rename Rename.succ).cs.denot
                  (env'.extend_var n ps) store).hasmem mu l
        have hrebind := rebind_captureset_denot
          (Rebind.weaken (env := env') (x := n) (ps := ps)) Γ'.consumeset.cs
        have heq := congrFun hrebind store
        change ((Γ'.consumeset.cs.rename Rename.succ).denot
                  (env'.extend_var n ps) store).hasmem mu l
        exact heq ▸ ihres
    | tvar S =>
      cases env with | extend env' info =>
      cases info with | tvar d =>
      cases hlk with
      | there hlk' =>
        have ihres := ih hlk' hmem
        change ((Γ'.consumeset.rename Rename.succ).cs.denot
                  (env'.extend_tvar d) store).hasmem mu l
        have hrebind := rebind_captureset_denot
          (Rebind.tweaken (env := env') (d := d)) Γ'.consumeset.cs
        have heq := congrFun hrebind store
        change ((Γ'.consumeset.cs.rename Rename.succ).denot
                  (env'.extend_tvar d) store).hasmem mu l
        exact heq ▸ ihres
    | cvar useM B' =>
      cases env with | extend env' info =>
      cases info with | cvar cs0 cap0 =>
      cases hlk with
      | here =>
        -- c = .here, useM = .consume. env.lookup_cvar .here = (cs0, cap0).
        change (cs0.ground_denot store).hasmem mu l at hmem
        change ((Γ'.consumeset.rename Rename.succ).cs.denot
                  (env'.extend_cvar cs0 cap0) store
                 ∪ (CaptureSet.cvar Mutability.epsilon BVar.here).denot
                     (env'.extend_cvar cs0 cap0) store).hasmem mu l
        exact CapabilitySet.hasmem.right hmem
      | there hlk' =>
        have ihres := ih hlk' hmem
        have hrebind := rebind_captureset_denot
          (Rebind.cweaken (env := env') (cs := cs0) (cap := cap0)) Γ'.consumeset.cs
        have heq := congrFun hrebind store
        cases useM with
        | access =>
          change ((Γ'.consumeset.rename Rename.succ).cs.denot
                    (env'.extend_cvar cs0 cap0) store).hasmem mu l
          change ((Γ'.consumeset.cs.rename Rename.succ).denot
                    (env'.extend_cvar cs0 cap0) store).hasmem mu l
          exact heq ▸ ihres
        | empty =>
          change ((Γ'.consumeset.rename Rename.succ).cs.denot
                    (env'.extend_cvar cs0 cap0) store).hasmem mu l
          change ((Γ'.consumeset.cs.rename Rename.succ).denot
                    (env'.extend_cvar cs0 cap0) store).hasmem mu l
          exact heq ▸ ihres
        | consume =>
          change ((Γ'.consumeset.rename Rename.succ).cs.denot
                    (env'.extend_cvar cs0 cap0) store
                   ∪ (CaptureSet.cvar Mutability.epsilon BVar.here).denot
                       (env'.extend_cvar cs0 cap0) store).hasmem mu l
          apply CapabilitySet.hasmem.left
          change ((Γ'.consumeset.cs.rename Rename.succ).denot
                    (env'.extend_cvar cs0 cap0) store).hasmem mu l
          exact heq ▸ ihres
  | lock Γ' _ =>
    -- `LookupCVar.lock` produces `locked = true`, contradicting `locked = false`.
    cases hlk

/-- Extract a hasmem witness from a covers proof, exposing the `mu ≤ mu'`
    relation that's hidden in the inductive structure. -/
private theorem CapabilitySet.covers_exists_hasmem
    {X : CapabilitySet} {mu : CapMode} {l : Nat}
    (h : X.covers mu l) : ∃ mu', mu ≤ mu' ∧ X.hasmem mu' l := by
  induction h with
  | here hle => exact ⟨_, hle, .here⟩
  | left _ ih =>
    obtain ⟨mu', hle', hmem'⟩ := ih
    exact ⟨mu', hle', .left hmem'⟩
  | right _ ih =>
    obtain ⟨mu', hle', hmem'⟩ := ih
    exact ⟨mu', hle', .right hmem'⟩

/-- An accessible cvar's runtime denotation is contained in the context's
    `accessset.cs` denotation. Locks are transparent (the refactored
    `accessset` passes through `.lock`), so the lock case recurses. -/
private theorem accessset_hasmem_via_cs
    {s : Sig} {Γ : Ctx s} {env : TypeEnv s} {store : Memory}
    {c : BVar s .cvar} {B : CaptureBound s} {locked : Bool}
    {l : Nat} {mu : CapMode}
    (hlk : Γ.LookupCVar c .access B locked)
    (hmem : ((env.lookup_cvar c).1.ground_denot store).hasmem mu l) :
    (Γ.accessset.cs.denot env store).hasmem mu l := by
  induction Γ generalizing locked with
  | empty => cases hlk
  | push Γ' b ih =>
    cases b with
    | var T =>
      cases env with | extend env' info =>
      cases info with | var n ps =>
      cases hlk with
      | there hlk' =>
        have ihres := ih hlk' hmem
        have hrebind := rebind_captureset_denot
          (Rebind.weaken (env := env') (x := n) (ps := ps)) Γ'.accessset.cs
        have heq := congrFun hrebind store
        change ((Γ'.accessset.cs.rename Rename.succ).denot
                  (env'.extend_var n ps) store).hasmem mu l
        exact heq ▸ ihres
    | tvar S =>
      cases env with | extend env' info =>
      cases info with | tvar d =>
      cases hlk with
      | there hlk' =>
        have ihres := ih hlk' hmem
        have hrebind := rebind_captureset_denot
          (Rebind.tweaken (env := env') (d := d)) Γ'.accessset.cs
        have heq := congrFun hrebind store
        change ((Γ'.accessset.cs.rename Rename.succ).denot
                  (env'.extend_tvar d) store).hasmem mu l
        exact heq ▸ ihres
    | cvar useM B' =>
      cases env with | extend env' info =>
      cases info with | cvar cs0 cap0 =>
      cases hlk with
      | here =>
        -- c = .here, useM = .access. env.lookup_cvar .here = (cs0, cap0).
        change (cs0.ground_denot store).hasmem mu l at hmem
        change ((Γ'.accessset.cs.rename Rename.succ).denot
                  (env'.extend_cvar cs0 cap0) store
                 ∪ (CaptureSet.cvar Mutability.epsilon BVar.here).denot
                     (env'.extend_cvar cs0 cap0) store).hasmem mu l
        exact CapabilitySet.hasmem.right hmem
      | there hlk' =>
        have ihres := ih hlk' hmem
        have hrebind := rebind_captureset_denot
          (Rebind.cweaken (env := env') (cs := cs0) (cap := cap0)) Γ'.accessset.cs
        have heq := congrFun hrebind store
        cases useM with
        | empty =>
          change ((Γ'.accessset.cs.rename Rename.succ).denot
                    (env'.extend_cvar cs0 cap0) store).hasmem mu l
          exact heq ▸ ihres
        | consume =>
          change ((Γ'.accessset.cs.rename Rename.succ).denot
                    (env'.extend_cvar cs0 cap0) store).hasmem mu l
          exact heq ▸ ihres
        | access =>
          change ((Γ'.accessset.cs.rename Rename.succ).denot
                    (env'.extend_cvar cs0 cap0) store
                   ∪ (CaptureSet.cvar Mutability.epsilon BVar.here).denot
                       (env'.extend_cvar cs0 cap0) store).hasmem mu l
          apply CapabilitySet.hasmem.left
          exact heq ▸ ihres
  | lock Γ' ih =>
    -- After the refactor: `(.lock Γ').accessset = Γ'.accessset`. Lock is
    -- transparent for accessibility, so we recurse.
    cases hlk with
    | lock hlk' =>
      exact ih hlk' hmem

/-- Covers-version of `consumeset_hasmem_via_cs`. -/
private theorem consumeset_covers_via_cs
    {s : Sig} {Γ : Ctx s} {env : TypeEnv s} {store : Memory}
    {c : BVar s .cvar} {B : CaptureBound s} {l : Nat} {mu : CapMode}
    (hlk : Γ.LookupCVar c .consume B false)
    (hcov : ((env.lookup_cvar c).1.ground_denot store).covers mu l) :
    (Γ.consumeset.cs.denot env store).covers mu l := by
  obtain ⟨mu', hle, hhm⟩ := CapabilitySet.covers_exists_hasmem hcov
  exact CapabilitySet.covers_of_hasmem_le (consumeset_hasmem_via_cs hlk hhm) hle

/-- Covers-version of `accessset_hasmem_via_cs`. -/
private theorem accessset_covers_via_cs
    {s : Sig} {Γ : Ctx s} {env : TypeEnv s} {store : Memory}
    {c : BVar s .cvar} {B : CaptureBound s} {locked : Bool}
    {l : Nat} {mu : CapMode}
    (hlk : Γ.LookupCVar c .access B locked)
    (hcov : ((env.lookup_cvar c).1.ground_denot store).covers mu l) :
    (Γ.accessset.cs.denot env store).covers mu l := by
  obtain ⟨mu', hle, hhm⟩ := CapabilitySet.covers_exists_hasmem hcov
  exact CapabilitySet.covers_of_hasmem_le (accessset_hasmem_via_cs hlk hhm) hle

/-- A `hasmem`-with-`mu ≤ mu'`-tracking version of `hasmem_of_applyMut`. -/
private theorem hasmem_of_applyMut_le {C : CapabilitySet} {m : Mutability} {mu : CapMode}
    {l : Nat} (h : (C.applyMut m).hasmem mu l) :
    ∃ mu', mu ≤ mu' ∧ C.hasmem mu' l := by
  cases m with
  | epsilon => exact ⟨mu, CapMode.Le.refl, h⟩
  | ro =>
    simp only [CapabilitySet.applyMut] at h
    obtain ⟨mu', heq, hm⟩ := CapabilitySet.hasmem_applyRO_iff.mp h
    subst heq
    exact ⟨mu', CapMode.applyRO_le, hm⟩

/-- A `hasmem`-with-`mu ≤ mu'`-tracking version of `hasmem_of_capabilitySet_subset`.
    Traces the `Subset` derivation, showing the witness mode is monotone in `≤`. -/
private theorem hasmem_of_subset_le {C1 C2 : CapabilitySet} (hsub : C1 ⊆ C2)
    {mu : CapMode} {l : Nat} (h : C1.hasmem mu l) :
    ∃ mu', mu ≤ mu' ∧ C2.hasmem mu' l := by
  induction hsub generalizing mu with
  | refl => exact ⟨mu, CapMode.Le.refl, h⟩
  | empty => exact (CapabilitySet.not_hasmem_empty h).elim
  | trans _ _ ih1 ih2 =>
    obtain ⟨mu', hle1, h'⟩ := ih1 h
    obtain ⟨mu'', hle2, h''⟩ := ih2 h'
    exact ⟨mu'', CapMode.Le.trans hle1 hle2, h''⟩
  | union_left _ _ ih1 ih2 =>
    cases h with
    | left h' => exact ih1 h'
    | right h' => exact ih2 h'
  | union_right_left =>
    exact ⟨mu, CapMode.Le.refl, CapabilitySet.hasmem.left h⟩
  | union_right_right =>
    exact ⟨mu, CapMode.Le.refl, CapabilitySet.hasmem.right h⟩
  | cap_ro =>
    cases h
    -- h forces mu = .access .ro; the cap goes to .cap (.access .ε) l.
    exact ⟨.access .epsilon, .access Mutability.Le.ro_eps, CapabilitySet.hasmem.here⟩

/-- A `consumable`-extraction with the `mu ≤ mu'` relation preserved.
    Built directly on the peaks-only structure; this preserves `mu` through
    the `applyMut` operation in the cvar case. -/
private theorem consumable_to_consume_covers_witness_peaks
    {s : Sig} {Γ : Ctx s} {env : TypeEnv s} {store : Memory}
    {P : CaptureSet s} (hP : P.PeaksOnly) {l : Nat} {mu : CapMode}
    (hts : EnvTyping Γ env store)
    (hcons : P.consumable Γ)
    (hmem : (P.denot env store).hasmem mu l) :
    ∃ c B, Γ.LookupCVar c .consume B false ∧
      ((env.lookup_cvar c).2).covers mu l := by
  induction hP generalizing mu with
  | empty =>
    simp only [CaptureSet.denot, CaptureSet.subst, CaptureSet.ground_denot] at hmem
    exact (CapabilitySet.not_hasmem_empty hmem).elim
  | union hP1 hP2 ih1 ih2 =>
    rename_i C1 C2
    have hcons1 : C1.consumable Γ := by
      intro m' c' hsub
      apply hcons m' c'
      rw [CaptureSet.peaks]
      exact hsub.union_right_left
    have hcons2 : C2.consumable Γ := by
      intro m' c' hsub
      apply hcons m' c'
      rw [CaptureSet.peaks]
      exact hsub.union_right_right
    have hunion : (C1.union C2).denot env store
        = C1.denot env store ∪ C2.denot env store := rfl
    rw [hunion] at hmem
    cases hmem with
    | left hm => exact ih1 hcons1 hm
    | right hm => exact ih2 hcons2 hm
  | cvar =>
    rename_i m c
    have hpeak : ConsumablePeak Γ c := by
      apply hcons m c
      rw [CaptureSet.peaks]
      exact CaptureSet.Subset.refl
    cases hpeak with
    | lookup hLookup =>
      rename_i B
      have hdenot :
          (CaptureSet.cvar m c).denot env store
            = ((env.lookup_cvar c).2).applyMut m := by
        change ((env.lookup_cvar c).1.applyMut m).ground_denot store = _
        rw [captureSet_ground_denot_applyMut_comm, ← typed_env_cvar_cap_eq hts c]
      rw [hdenot] at hmem
      exact ⟨c, B, hLookup, CapabilitySet.hasmem_applyMut_implies_covers hmem⟩

/-- Parallel of `consumable_to_consume_covers_witness_peaks` for `accessible`. -/
private theorem accessible_to_access_covers_witness_peaks
    {s : Sig} {Γ : Ctx s} {env : TypeEnv s} {store : Memory}
    {P : CaptureSet s} (hP : P.PeaksOnly) {l : Nat} {mu : CapMode}
    (hts : EnvTyping Γ env store)
    (haccess : P.accessible Γ)
    (hmem : (P.denot env store).hasmem mu l) :
    ∃ c B locked, Γ.LookupCVar c .access B locked ∧
      ((env.lookup_cvar c).2).covers mu l := by
  induction hP generalizing mu with
  | empty =>
    simp only [CaptureSet.denot, CaptureSet.subst, CaptureSet.ground_denot] at hmem
    exact (CapabilitySet.not_hasmem_empty hmem).elim
  | union hP1 hP2 ih1 ih2 =>
    rename_i C1 C2
    have haccess1 : C1.accessible Γ := by
      intro m' c' hsub
      apply haccess m' c'
      rw [CaptureSet.peaks]
      exact hsub.union_right_left
    have haccess2 : C2.accessible Γ := by
      intro m' c' hsub
      apply haccess m' c'
      rw [CaptureSet.peaks]
      exact hsub.union_right_right
    have hunion : (C1.union C2).denot env store
        = C1.denot env store ∪ C2.denot env store := rfl
    rw [hunion] at hmem
    cases hmem with
    | left hm => exact ih1 haccess1 hm
    | right hm => exact ih2 haccess2 hm
  | cvar =>
    rename_i m c
    have hpeak : AccessiblePeak Γ c := by
      apply haccess m c
      rw [CaptureSet.peaks]
      exact CaptureSet.Subset.refl
    cases hpeak with
    | lookup hLookup =>
      rename_i B locked
      have hdenot :
          (CaptureSet.cvar m c).denot env store
            = ((env.lookup_cvar c).2).applyMut m := by
        change ((env.lookup_cvar c).1.applyMut m).ground_denot store = _
        rw [captureSet_ground_denot_applyMut_comm, ← typed_env_cvar_cap_eq hts c]
      rw [hdenot] at hmem
      exact ⟨c, B, locked, hLookup, CapabilitySet.hasmem_applyMut_implies_covers hmem⟩

mutual

/-- Membership in `C.denot` lifts to coverage in `(compute_peaks env C).denot`
    at the *same* `mu`. The proof threads through `applyMut`/`subset` chains by
    bridging via `covers` (which is monotone where `hasmem` is not). -/
private theorem covers_compute_peaks_denot
    {s : Sig} {Γ : Ctx s} {env : TypeEnv s} {store : Memory}
    (hts : EnvTyping Γ env store) (hΓ : Γ.IsClosed)
    (C : CaptureSet s) (hC : C.IsClosed) {l : Nat} {mu : CapMode}
    (hmem : (C.denot env store).hasmem mu l) :
    ((compute_peaks env C).denot env store).covers mu l := by
  match C, hC, hmem with
  | .empty, _, hmem =>
    simp only [CaptureSet.denot, CaptureSet.subst, CaptureSet.ground_denot] at hmem
    exact (CapabilitySet.not_hasmem_empty hmem).elim
  | .union C1 C2, hC, hmem =>
    cases hC with | union hC1 hC2 =>
    have hunion : (C1.union C2).denot env store
        = C1.denot env store ∪ C2.denot env store := rfl
    rw [hunion] at hmem
    match hmem with
    | .left hm =>
      have hcov := covers_compute_peaks_denot hts hΓ C1 hC1 hm
      change ((compute_peaks env C1).denot env store
              ∪ (compute_peaks env C2).denot env store).covers mu l
      exact .left hcov
    | .right hm =>
      have hcov := covers_compute_peaks_denot hts hΓ C2 hC2 hm
      change ((compute_peaks env C1).denot env store
              ∪ (compute_peaks env C2).denot env store).covers mu l
      exact .right hcov
  | .cvar m c, _, hmem =>
    change ((CaptureSet.cvar m c).denot env store).covers mu l
    exact CapabilitySet.hasmem_implies_covers hmem
  | .var m (.bound x), _, hmem =>
    exact covers_compute_peaks_denot_var_bound hts hΓ hmem
  | .var m (.free n), hC, _ => cases hC
termination_by 2 * (sizeOf Γ + sizeOf C) + 1

/-- The `.var .bound x` arm of `covers_compute_peaks_denot`. Recurses on `Γ`. -/
private theorem covers_compute_peaks_denot_var_bound
    {s : Sig} {Γ : Ctx s} {env : TypeEnv s} {store : Memory}
    (hts : EnvTyping Γ env store) (hΓ : Γ.IsClosed)
    {x : BVar s .var} {m : Mutability} {l : Nat} {mu : CapMode}
    (hmem : ((CaptureSet.var m (.bound x)).denot env store).hasmem mu l) :
    ((compute_peaks env (CaptureSet.var m (.bound x))).denot env store).covers mu l := by
  match s, Γ, env, hts, hΓ, x, hmem with
  | _, .empty, .empty, _, _, x, _ => cases x
  | _, .push Γ_rest (.var T), .extend env_rest (.var n ps), hts, hΓ, .here, hmem =>
    obtain ⟨hval_T, hps_eq, hts_rest⟩ := hts
    cases hΓ with | push hΓ_rest hb =>
    cases hb with | var hT =>
    have hT_cs : T.captureSet.IsClosed := Ty.captureSet_isClosed hT
    -- hmem : hasmem mu l ((reachability_of_loc store.heap n).applyMut m)
    change CapabilitySet.hasmem mu l
      ((reachability_of_loc store.heap n).applyMut m) at hmem
    -- Pull off applyMut on the hasmem side: covers mu l (reachability).
    have hcov_reach : (reachability_of_loc store.heap n).covers mu l :=
      CapabilitySet.hasmem_applyMut_implies_covers hmem
    -- Bridge through reachability ⊆ T.captureSet.denot env_rest store.
    have hreach_sub : reachability_of_loc store.heap n ⊆ T.captureSet.denot env_rest store := by
      have h := val_denot_enforces_captures hts_rest (.var (.free n)) hval_T
      simp only [resolve_reachability] at h
      exact h
    have hcov_T : (T.captureSet.denot env_rest store).covers mu l :=
      CapabilitySet.subset_preserves_covers hreach_sub hcov_reach
    -- Recurse on T.captureSet at Γ_rest. The IH takes hasmem, so extract one
    -- via covers_exists_hasmem and weaken back to mu afterwards.
    obtain ⟨mu1, hle1, hmem_T⟩ := CapabilitySet.covers_exists_hasmem hcov_T
    have hcov_cp1 :
        ((compute_peaks env_rest T.captureSet).denot env_rest store).covers mu1 l :=
      covers_compute_peaks_denot hts_rest hΓ_rest T.captureSet hT_cs hmem_T
    have hcov_cp : ((compute_peaks env_rest T.captureSet).denot env_rest store).covers mu l :=
      CapabilitySet.covers_weaken hcov_cp1 hle1
    -- Rebind through Rename.succ and the extended environment.
    have hps_cs : ps.cs = compute_peaks env_rest T.captureSet := by
      rw [hps_eq]
      change T.captureSet.peaks Γ_rest = _
      exact compute_peaks_correct hts_rest T.captureSet
    have hcp_denot := rebind_captureset_denot
      (ρ := @Rebind.weaken _ env_rest n ps)
      (compute_peaks env_rest T.captureSet)
    have hcp_rename := rebind_compute_peaks
      (ρ := @Rebind.weaken _ env_rest n ps) T.captureSet
    -- Move hcov_cp into the extended env via rebind.
    have heq_d := congrFun hcp_denot store
    have hcov_renamed :
        (((compute_peaks env_rest T.captureSet).rename Rename.succ).denot
            (env_rest.extend_var n ps) store).covers mu l := heq_d ▸ hcov_cp
    rw [hcp_rename] at hcov_renamed
    have hcov_cp_ext :
        ((compute_peaks (env_rest.extend_var n ps)
            (T.captureSet.rename Rename.succ)).denot
              (env_rest.extend_var n ps) store).covers mu l := hcov_renamed
    -- The mode `mu` is `m`-stable (forced by the original hmem's applyMut shape).
    have hmu_stable : m = .epsilon ∨ (m = .ro ∧ mu = mu.applyRO) := by
      cases m with
      | epsilon => exact .inl rfl
      | ro =>
        right
        refine ⟨rfl, ?_⟩
        simp only [CapabilitySet.applyMut] at hmem
        exact CapabilitySet.hasmem_applyRO_fixed hmem
    -- Final equality: compute_peaks of (.var m .bound .here) = (compute_peaks rename).applyMut m.
    have hcp_eq : compute_peaks (env_rest.extend_var n ps) (CaptureSet.var m (.bound BVar.here))
                = (compute_peaks (env_rest.extend_var n ps)
                    (T.captureSet.rename Rename.succ)).applyMut m := by
      change ((ps.rename Rename.succ).cs.applyMut m) = _
      change (ps.cs.rename Rename.succ).applyMut m = _
      rw [hps_cs, hcp_rename]
      rfl
    change CapabilitySet.covers mu l
      ((compute_peaks (env_rest.extend_var n ps) (CaptureSet.var m (.bound BVar.here))).denot
        (env_rest.extend_var n ps) store)
    rw [hcp_eq, captureSet_denot_applyMut_comm]
    -- Goal: covers mu l (Y.applyMut m). Push applyMut over covers using mu's m-stability.
    cases hmu_stable with
    | inl heq =>
      subst heq
      simpa [CapabilitySet.applyMut] using hcov_cp_ext
    | inr h =>
      obtain ⟨heq, hmu_eq⟩ := h
      subst heq
      simp only [CapabilitySet.applyMut]
      exact CapabilitySet.covers_applyRO_of_covers hcov_cp_ext hmu_eq
  | _, .push Γ_rest (.var T), .extend env_rest (.var n ps), hts, hΓ, .there x', hmem =>
    obtain ⟨_, _, hts_rest⟩ := hts
    cases hΓ with | push hΓ_rest _ =>
    change CapabilitySet.hasmem mu l
      (((CaptureSet.var m (.bound x')).rename Rename.succ).denot
        (env_rest.extend_var n ps) store) at hmem
    have hC := rebind_captureset_denot
      (ρ := @Rebind.weaken _ env_rest n ps)
      (CaptureSet.var m (.bound x'))
    have hmem_rest : ((CaptureSet.var m (.bound x')).denot env_rest store).hasmem mu l := by
      rw [hC]; exact hmem
    have hcov_rest :
        ((compute_peaks env_rest (CaptureSet.var m (.bound x'))).denot
            env_rest store).covers mu l :=
      covers_compute_peaks_denot_var_bound hts_rest hΓ_rest hmem_rest
    have hcp_rename := rebind_compute_peaks
      (ρ := @Rebind.weaken _ env_rest n ps)
      (CaptureSet.var m (.bound x'))
    have hcp_denot := rebind_captureset_denot
      (ρ := @Rebind.weaken _ env_rest n ps)
      (compute_peaks env_rest (CaptureSet.var m (.bound x')))
    rw [congrFun hcp_denot store, hcp_rename] at hcov_rest
    exact hcov_rest
  | _, .push Γ_rest (.tvar S), .extend env_rest (.tvar d), hts, hΓ, .there x', hmem =>
    obtain ⟨_, _, _, _, _, hts_rest⟩ := hts
    cases hΓ with | push hΓ_rest _ =>
    change CapabilitySet.hasmem mu l
      (((CaptureSet.var m (.bound x')).rename Rename.succ).denot
        (env_rest.extend_tvar d) store) at hmem
    have hC := rebind_captureset_denot
      (ρ := @Rebind.tweaken _ env_rest d)
      (CaptureSet.var m (.bound x'))
    have hmem_rest : ((CaptureSet.var m (.bound x')).denot env_rest store).hasmem mu l := by
      rw [hC]; exact hmem
    have hcov_rest :
        ((compute_peaks env_rest (CaptureSet.var m (.bound x'))).denot
            env_rest store).covers mu l :=
      covers_compute_peaks_denot_var_bound hts_rest hΓ_rest hmem_rest
    have hcp_rename := rebind_compute_peaks
      (ρ := @Rebind.tweaken _ env_rest d)
      (CaptureSet.var m (.bound x'))
    have hcp_denot := rebind_captureset_denot
      (ρ := @Rebind.tweaken _ env_rest d)
      (compute_peaks env_rest (CaptureSet.var m (.bound x')))
    rw [congrFun hcp_denot store, hcp_rename] at hcov_rest
    exact hcov_rest
  | _, .push Γ_rest (.cvar md B), .extend env_rest (.cvar cs cap), hts, hΓ, .there x', hmem =>
    obtain ⟨_, _, _, _, hts_rest⟩ := hts
    cases hΓ with | push hΓ_rest _ =>
    change CapabilitySet.hasmem mu l
      (((CaptureSet.var m (.bound x')).rename Rename.succ).denot
        (env_rest.extend_cvar cs cap) store) at hmem
    have hC := rebind_captureset_denot
      (ρ := @Rebind.cweaken _ env_rest cs cap)
      (CaptureSet.var m (.bound x'))
    have hmem_rest : ((CaptureSet.var m (.bound x')).denot env_rest store).hasmem mu l := by
      rw [hC]; exact hmem
    have hcov_rest :
        ((compute_peaks env_rest (CaptureSet.var m (.bound x'))).denot
            env_rest store).covers mu l :=
      covers_compute_peaks_denot_var_bound hts_rest hΓ_rest hmem_rest
    have hcp_rename := rebind_compute_peaks
      (ρ := @Rebind.cweaken _ env_rest cs cap)
      (CaptureSet.var m (.bound x'))
    have hcp_denot := rebind_captureset_denot
      (ρ := @Rebind.cweaken _ env_rest cs cap)
      (compute_peaks env_rest (CaptureSet.var m (.bound x')))
    rw [congrFun hcp_denot store, hcp_rename] at hcov_rest
    exact hcov_rest
  | _, .lock Γ_rest, env, hts, hΓ, x, hmem =>
    have hts_rest : EnvTyping Γ_rest env store := hts
    cases hΓ with | lock hΓ_rest =>
    exact covers_compute_peaks_denot_var_bound hts_rest hΓ_rest hmem
termination_by 2 * (sizeOf Γ + sizeOf (CaptureSet.var m (.bound x)))
decreasing_by
  all_goals simp_wf
  all_goals try omega
  all_goals (have := sizeOf_captureSet_le T; omega)

end

/-- Every cap in an accessible capture set's denotation is covered by the
    context's `accessset.cs` denotation. -/
theorem CaptureSet.accessible_denot_covers
    {s : Sig} {Γ : Ctx s} {C : CaptureSet s}
    {env : TypeEnv s} {store : Memory}
    (hts : EnvTyping Γ env store) (hΓ : Γ.IsClosed)
    (hC : C.IsClosed) (haccess : C.accessible Γ)
    {mu : CapMode} {l : Nat}
    (hmem : (C.denot env store).hasmem mu l) :
    (Γ.accessset.cs.denot env store).covers mu l := by
  -- Step 1: lift to coverage in compute_peaks form (mu preserved).
  have hcov_cp : ((compute_peaks env C).denot env store).covers mu l :=
    covers_compute_peaks_denot hts hΓ C hC hmem
  -- Step 2: accessibility transfers to compute_peaks form.
  have hP := compute_peaks_is_peak env C
  have hpeaks_eq := compute_peaks_correct hts C
  have hPP := peaks_of_peaksOnly (Γ := Γ) hP
  have haccess_P : (compute_peaks env C).accessible Γ := by
    intro m' c' hsub
    apply haccess m' c'
    rw [hpeaks_eq]
    rw [hPP] at hsub
    exact hsub
  -- Step 3: extract a hasmem witness with mu ≤ mu', then call witness theorem.
  obtain ⟨mu', hle, hmem'⟩ := CapabilitySet.covers_exists_hasmem hcov_cp
  obtain ⟨c, B, locked, hlk, hcov_cvar⟩ :=
    accessible_to_access_covers_witness_peaks hP hts haccess_P hmem'
  -- Step 4: convert (env.lookup_cvar c).2 to .1.ground_denot.
  rw [typed_env_cvar_cap_eq hts c] at hcov_cvar
  -- Step 5: lift to accessset.cs.denot via accessset_covers_via_cs.
  have hcov_acc := accessset_covers_via_cs hlk hcov_cvar
  -- Step 6: weaken covers from mu' down to mu.
  exact CapabilitySet.covers_weaken hcov_acc hle

/-- Companion to `accessible_denot_covers` for `consumable` capture sets. -/
theorem CaptureSet.consumable_denot_covers
    {s : Sig} {Γ : Ctx s} {C : CaptureSet s}
    {env : TypeEnv s} {store : Memory}
    (hts : EnvTyping Γ env store) (hΓ : Γ.IsClosed)
    (hC : C.IsClosed) (hcons : C.consumable Γ)
    {mu : CapMode} {l : Nat}
    (hmem : (C.denot env store).hasmem mu l) :
    (Γ.consumeset.cs.denot env store).covers mu l := by
  have hcov_cp : ((compute_peaks env C).denot env store).covers mu l :=
    covers_compute_peaks_denot hts hΓ C hC hmem
  have hP := compute_peaks_is_peak env C
  have hpeaks_eq := compute_peaks_correct hts C
  have hPP := peaks_of_peaksOnly (Γ := Γ) hP
  have hcons_P : (compute_peaks env C).consumable Γ := by
    intro m' c' hsub
    apply hcons m' c'
    rw [hpeaks_eq]
    rw [hPP] at hsub
    exact hsub
  obtain ⟨mu', hle, hmem'⟩ := CapabilitySet.covers_exists_hasmem hcov_cp
  obtain ⟨c, B, hlk, hcov_cvar⟩ :=
    consumable_to_consume_covers_witness_peaks hP hts hcons_P hmem'
  rw [typed_env_cvar_cap_eq hts c] at hcov_cvar
  have hcov_cons := consumeset_covers_via_cs hlk hcov_cvar
  exact CapabilitySet.covers_weaken hcov_cons hle

/-- When `C` is accessible in `Γ`, the use-set after SemanticTyping's
    `intersect`-tightening is *equal* to `C.denot env m`. Accessible peaks
    live in `Γ.accessset ⊆ Γ.useset`, so coverage transfers via
    `covers.left`. -/
theorem intersect_useset_eq_self_of_accessible
    {s : Sig} {Γ : Ctx s} {C : CaptureSet s}
    {env : TypeEnv s} {store : Memory}
    (hts : EnvTyping Γ env store) (hΓ : Γ.IsClosed)
    (hC : C.IsClosed) (haccess : C.accessible Γ) :
    (C.denot env store).intersect (Γ.useset.cs.denot env store)
      = C.denot env store := by
  apply CapabilitySet.intersect_eq_self_when_covered
  intro mu l hmem
  -- Γ.useset.cs.denot = (Γ.accessset.cs ∪ Γ.consumeset.cs).denot
  --                  = Γ.accessset.cs.denot ∪ Γ.consumeset.cs.denot  (by ground_denot on union)
  exact .left (CaptureSet.accessible_denot_covers hts hΓ hC haccess hmem)

/-- Same shape but for `consumable` capture sets. Consumable peaks live in
    `Γ.consumeset ⊆ Γ.useset`, so coverage transfers via `covers.right`. -/
theorem intersect_useset_eq_self_of_consumable
    {s : Sig} {Γ : Ctx s} {C : CaptureSet s}
    {env : TypeEnv s} {store : Memory}
    (hts : EnvTyping Γ env store) (hΓ : Γ.IsClosed)
    (hC : C.IsClosed) (hcons : C.consumable Γ) :
    (C.denot env store).intersect (Γ.useset.cs.denot env store)
      = C.denot env store := by
  apply CapabilitySet.intersect_eq_self_when_covered
  intro mu l hmem
  exact .right (CaptureSet.consumable_denot_covers hts hΓ hC hcons hmem)

/-- Converts the `SemanticTyping` form into the `Ty.exi_exp_denot` form used by
many call sites. The budget includes the contextual drop-authority
`Γ.consumeset.to_drop` granted by the new `SemanticTyping`. The use-set in
the source is widened from the tightened `intersect C.denot accessset.cs.denot`
to the full `C.denot` via `intersect_subset_left`. -/
theorem semtyp_to_exi_exp_denot
    {s : Sig} {C : CaptureSet s} {Γ : Ctx s} {e : Exp s} {E : Ty .exi s}
    {ρ : TypeEnv s} {m : Memory}
    (ht : C # Γ ⊨ e : E)
    (hts : EnvTyping Γ ρ m)
    (hcompat : m.is_compatible (C.denot ρ m)) :
    Ty.exi_exp_denot ρ E
      (C.denot ρ m ∪ (Γ.consumeset.cs.denot ρ m).to_drop) m
      (e.subst (Subst.from_TypeEnv ρ)) := by
  apply eval_capability_set_monotonic (ht ρ m hts hcompat)
  exact CapabilitySet.Subset.union_left
    (CapabilitySet.Subset.trans CapabilitySet.intersect_subset_left
      CapabilitySet.Subset.union_right_left)
    CapabilitySet.Subset.union_right_right

private theorem closed_capture_denot_monotonic
    {Cf : CaptureSet s} {env : TypeEnv s} {store m' : Memory} {Γ : Ctx s}
    (hCf_closed : Cf.IsClosed)
    (hts : EnvTyping Γ env store)
    (hsub : m'.subsumes store) :
    Cf.denot env store = Cf.denot env m' := by
  exact capture_set_denot_is_monotonic
    (C := Cf) (ρ := env)
    (by apply CaptureSet.wf_subst
        · exact CaptureSet.wf_of_closed hCf_closed
        · exact from_TypeEnv_wf_in_heap hts)
    hsub

private theorem authority_eq_expand_captures
    {k : Kind} {Cf : CaptureSet s} {env_ext : TypeEnv (s,,k)}
    {store m' : Memory}
    (hcap_rename : (Cf.rename Rename.succ).denot env_ext = Cf.denot env)
    (hCf_mono : Cf.denot env store = Cf.denot env m') :
    (Cf.rename Rename.succ).denot env_ext m' =
    expand_captures store.heap (Cf.subst (Subst.from_TypeEnv env)) := by
  calc (Cf.rename Rename.succ).denot env_ext m'
    _ = Cf.denot env m' := by rw [congrFun hcap_rename m']
    _ = Cf.denot env store := by rw [← hCf_mono]
    _ = (Cf.subst (Subst.from_TypeEnv env)).ground_denot store := by simp [CaptureSet.denot]
    _ = expand_captures store.heap (Cf.subst (Subst.from_TypeEnv env)) := by
        rw [← expand_captures_eq_ground_denot]

theorem sem_typ_abs {T2 : Ty TySort.exi (s,x)} {Cf : CaptureSet s}
  (hclosed_abs : (Exp.abs Cf T1 e).IsClosed)
  (ht : Cf.rename Rename.succ # Γ.lock,x:T1 ⊨ e : T2) :
  ∅ # Γ ⊨ Exp.abs Cf T1 e : (T1.arrow Cf T2).typ := by
  intro env store hts _
  apply Eval.eval_val
  · simp only [Exp.subst]; constructor
  · simp only [Ty.exi_val_denot, Ty.val_denot]
    -- Goal structure for arrow val_denot:
    -- 1. e.WfInHeap m.heap
    -- 2. (cs.subst ...).WfInHeap m.heap
    -- 3. ∃ cs' T0 t0, resolve ... = some (.abs cs' T0 t0) ∧ ...
    constructor
    · -- 1. Prove (abs ...).WfInHeap store.heap
      apply Exp.wf_subst
      · apply Exp.wf_of_closed hclosed_abs
      · apply from_TypeEnv_wf_in_heap hts
    · constructor
      · -- 2. Prove (Cf.subst ...).WfInHeap store.heap
        apply CaptureSet.wf_subst
        · apply CaptureSet.wf_of_closed
          cases hclosed_abs
          assumption
        · apply from_TypeEnv_wf_in_heap hts
      · -- 3. Provide existential witnesses: cs', T0, t0
        use (Cf.subst (Subst.from_TypeEnv env)), (T1.subst (Subst.from_TypeEnv env)),
          (e.subst (Subst.from_TypeEnv env).lift)
        constructor
        · -- Show that resolve gives back the abstraction
          simp only [resolve, Exp.subst]
        · constructor
          · -- Prove cs'.WfInHeap store.heap
            apply CaptureSet.wf_subst
            · apply CaptureSet.wf_of_closed
              cases hclosed_abs
              assumption
            · apply from_TypeEnv_wf_in_heap hts
          · constructor
            · -- Prove expand_captures ... ⊆ Cf.denot env store
              rw [expand_captures_eq_ground_denot]
              simp only [List.empty_eq]
              apply CapabilitySet.Subset.refl
            · -- Show the function property
              intro arg m' hsub hcompat harg
              -- Use compute_peakset which equals peakset by compute_peakset_correct
              let ps := compute_peakset env T1.captureSet
              have hkey := @Exp.from_TypeEnv_weaken_open s env arg e ps
              refine hkey ▸ ?_
              -- Build EnvTyping using the computed peak set
              have henv :
                EnvTyping (Γ.lock,x:T1) (env.extend_var arg ps) m' := by
                constructor
                · exact harg
                · constructor
                  · rw [CaptureSet.peakset_lock]
                    exact (compute_peakset_correct hts T1.captureSet).symm
                  · change EnvTyping Γ env m'
                    apply env_typing_monotonic hts hsub
              have hcap_rename :
                (Cf.rename Rename.succ).denot (env.extend_var arg ps)
                = Cf.denot env := by
                have := rebind_captureset_denot
                  (Rebind.weaken (env:=env) (x:=arg) (ps:=ps)) Cf
                exact this.symm
              have hCf_closed : Cf.IsClosed := by cases hclosed_abs; assumption
              -- Convert hcompat (in `expand_captures store.heap ...` form) to compat for
              -- `(Cf.rename Rename.succ).denot (env.extend_var arg ps) m'`.
              have hauth :=
                authority_eq_expand_captures hcap_rename
                  (closed_capture_denot_monotonic hCf_closed hts hsub)
              have hcompat' :
                  m'.is_compatible ((Cf.rename Rename.succ).denot (env.extend_var arg ps) m') :=
                hauth ▸ hcompat
              -- Apply the hypothesis. With the locked body context,
              -- `(Γ.lock,x:T1).consumeset.cs = .empty` definitionally, so the
              -- wider budget reduces to `Cf.denot' ∪ .empty`, which we narrow
              -- to `Cf.denot'` via `eval_capability_set_monotonic` (the union
              -- with empty is subset of the left).
              have htyped := ht (env.extend_var arg ps) m' henv hcompat'
              have htyped_narrow :
                  Eval ((Cf.rename Rename.succ).denot (env.extend_var arg ps) m') m'
                    (e.subst (Subst.from_TypeEnv (env.extend_var arg ps)))
                    (fun v m'' =>
                      Ty.exi_val_denot (env.extend_var arg ps) T2 m'' v) := by
                apply eval_capability_set_monotonic htyped
                exact CapabilitySet.Subset.union_left
                  CapabilitySet.intersect_subset_left CapabilitySet.Subset.empty
              -- Show the body's authority equals the closure's authority
              rw [← authority_eq_expand_captures hcap_rename
                    (closed_capture_denot_monotonic hCf_closed hts hsub)]
              exact htyped_narrow


theorem sem_typ_tabs {T : Ty TySort.exi (s,X)} {Cf : CaptureSet s} {S : PureTy s}
  (hclosed_tabs : (Exp.tabs Cf S e).IsClosed)
  (ht : Cf.rename Rename.succ # (Γ.lock,X<:S) ⊨ e : T) :
  ∅ # Γ ⊨ Exp.tabs Cf S e : (S.core.poly Cf T).typ := by
  intro env store hts _
  apply Eval.eval_val
  · simp only [Exp.subst]; constructor
  · simp only [Ty.exi_val_denot, Ty.val_denot]
    -- Goal structure for poly val_denot:
    -- 1. e.WfInHeap m.heap
    -- 2. (cs.subst ...).WfInHeap m.heap
    -- 3. ∃ cs' S0 t0, resolve ... = some (.tabs cs' S0 t0) ∧ ...
    constructor
    · -- 1. Prove (tabs ...).WfInHeap store.heap
      apply Exp.wf_subst
      · apply Exp.wf_of_closed hclosed_tabs
      · apply from_TypeEnv_wf_in_heap hts
    · constructor
      · -- 2. Prove (Cf.subst ...).WfInHeap store.heap
        apply CaptureSet.wf_subst
        · apply CaptureSet.wf_of_closed
          cases hclosed_tabs
          assumption
        · apply from_TypeEnv_wf_in_heap hts
      · -- 3. Provide existential witnesses: cs', S0, t0
        use (Cf.subst (Subst.from_TypeEnv env)), (S.subst (Subst.from_TypeEnv env)),
          (e.subst (Subst.from_TypeEnv env).lift)
        constructor
        · -- Show that resolve gives back the type abstraction
          simp only [resolve, Exp.subst]
        · constructor
          · -- Prove cs'.WfInHeap store.heap
            apply CaptureSet.wf_subst
            · apply CaptureSet.wf_of_closed
              cases hclosed_tabs
              assumption
            · apply from_TypeEnv_wf_in_heap hts
          · constructor
            · -- Prove expand_captures ... ⊆ Cf.denot env store
              rw [expand_captures_eq_ground_denot]
              simp only [List.empty_eq]
              apply CapabilitySet.Subset.refl
            · -- Show the polymorphic function property
              intro m' denot hsub hcompat hproper himply_simple_ans himply hpure
              have hkey := @Exp.from_TypeEnv_weaken_open_tvar s env denot e
              refine hkey ▸ ?_
              -- Build EnvTyping using the type denotation
              have henv : EnvTyping (Γ.lock,X<:S) (env.extend_tvar denot) m' := by
                constructor
                · exact hproper
                · constructor
                  · -- denot.implies_wf: now included in is_proper
                    exact hproper.2.2.2
                  · constructor
                    · exact himply_simple_ans
                    · constructor
                      · exact himply
                      · constructor
                        · exact hpure
                        · change EnvTyping Γ env m'
                          apply env_typing_monotonic hts hsub
              have hcap_rename :
                (Cf.rename Rename.succ).denot (env.extend_tvar denot) = Cf.denot env := by
                have := rebind_captureset_denot (Rebind.tweaken (env:=env) (d:=denot)) Cf
                exact this.symm
              have hCf_closed : Cf.IsClosed := by cases hclosed_tabs; assumption
              have hauth :=
                authority_eq_expand_captures hcap_rename
                  (closed_capture_denot_monotonic hCf_closed hts hsub)
              have hcompat' :
                  m'.is_compatible ((Cf.rename Rename.succ).denot (env.extend_tvar denot) m') :=
                hauth ▸ hcompat
              -- Apply the hypothesis. The body's context `Γ.lock,X<:S` has
              -- empty `consumeset`, so the wider budget narrows to `Cf.denot'`.
              have htyped := ht (env.extend_tvar denot) m' henv hcompat'
              have htyped_narrow :
                  Eval ((Cf.rename Rename.succ).denot (env.extend_tvar denot) m') m'
                    (e.subst (Subst.from_TypeEnv (env.extend_tvar denot)))
                    (fun v m'' =>
                      Ty.exi_val_denot (env.extend_tvar denot) T m'' v) := by
                apply eval_capability_set_monotonic htyped
                exact CapabilitySet.Subset.union_left
                  CapabilitySet.intersect_subset_left CapabilitySet.Subset.empty
              -- Show the authority matches
              rw [← authority_eq_expand_captures hcap_rename
                    (closed_capture_denot_monotonic hCf_closed hts hsub)]
              exact htyped_narrow


theorem sem_typ_cabs {T : Ty TySort.exi (s,C)} {Cf : CaptureSet s} {cb : CaptureBound s}
  (hclosed_cabs : (Exp.cabs Cf cb e).IsClosed)
  (ht : Cf.rename Rename.succ # Γ.lock,C<:cb ⊨ e : T) :
  ∅ # Γ ⊨ Exp.cabs Cf cb e : (Ty.cpoly cb Cf T).typ := by
  intro env store hts _
  apply Eval.eval_val
  · simp only [Exp.subst]; constructor
  · simp only [Ty.exi_val_denot, Ty.val_denot]
    -- Goal structure for cpoly val_denot:
    -- 1. e.WfInHeap m.heap
    -- 2. (cs.subst ...).WfInHeap m.heap
    -- 3. ∃ cs' B0 t0, resolve ... = some (.cabs cs' B0 t0) ∧ ...
    constructor
    · -- 1. Prove (cabs ...).WfInHeap store.heap
      apply Exp.wf_subst
      · apply Exp.wf_of_closed hclosed_cabs
      · apply from_TypeEnv_wf_in_heap hts
    · constructor
      · -- 2. Prove (Cf.subst ...).WfInHeap store.heap
        apply CaptureSet.wf_subst
        · apply CaptureSet.wf_of_closed
          cases hclosed_cabs
          assumption
        · apply from_TypeEnv_wf_in_heap hts
      · -- 3. Provide existential witnesses: cs', B0, t0
        use (Cf.subst (Subst.from_TypeEnv env)), (cb.subst (Subst.from_TypeEnv env)),
          (e.subst (Subst.from_TypeEnv env).lift)
        constructor
        · -- Show that resolve gives back the capture abstraction
          simp only [resolve, Exp.subst]
        · constructor
          · -- Prove cs'.WfInHeap store.heap
            apply CaptureSet.wf_subst
            · apply CaptureSet.wf_of_closed
              cases hclosed_cabs
              assumption
            · apply from_TypeEnv_wf_in_heap hts
          · constructor
            · -- Prove expand_captures ... ⊆ Cf.denot env store
              rw [expand_captures_eq_ground_denot]
              simp only [List.empty_eq]
              apply CapabilitySet.Subset.refl
            · -- Show the capture polymorphic function property
              intro m' CS hwf hsub hcompat hsub_bound
              have hkey := @Exp.from_TypeEnv_weaken_open_cvar s env CS e
              refine hkey ▸ ?_
              -- Build EnvTyping
              have henv : EnvTyping (Γ.lock,C<:cb)
                  (env.extend_cvar CS (cap := CS.ground_denot m')) m' := by
                constructor
                · exact hwf  -- CS.WfInHeap m'.heap
                constructor
                · have hclosed_cb : cb.IsClosed := by
                    cases hclosed_cabs
                    assumption
                  have hwf_cb_at_store :
                      (cb.subst (Subst.from_TypeEnv env)).WfInHeap store.heap := by
                    exact CaptureBound.wf_subst (CaptureBound.wf_of_closed hclosed_cb)
                                                  (from_TypeEnv_wf_in_heap hts)
                  exact CaptureBound.wf_monotonic hsub hwf_cb_at_store
                constructor
                · -- Need to show: (CS.ground_denot m').BoundedBy (cb.denot m')
                  have heq : CS.ground_denot = CaptureSet.denot TypeEnv.empty CS := by
                    funext m
                    simp only [CaptureSet.denot, Subst.from_TypeEnv_empty, CaptureSet.subst_id]
                  rw [heq]
                  exact hsub_bound
                constructor
                · rfl
                · change EnvTyping Γ env m'
                  apply env_typing_monotonic hts hsub
              have hcap_rename :
                  (Cf.rename Rename.succ).denot
                    (env.extend_cvar CS (cap := CS.ground_denot m')) = Cf.denot env := by
                have :=
                  rebind_captureset_denot
                    (Rebind.cweaken (env:=env) (cs:=CS) (cap:=CS.ground_denot m')) Cf
                exact this.symm
              have hCf_closed : Cf.IsClosed := by cases hclosed_cabs; assumption
              have hauth :=
                authority_eq_expand_captures hcap_rename
                  (closed_capture_denot_monotonic hCf_closed hts hsub)
              have hcompat' :
                  m'.is_compatible
                    ((Cf.rename Rename.succ).denot
                      (env.extend_cvar CS (cap := CS.ground_denot m')) m') :=
                hauth ▸ hcompat
              -- Apply the hypothesis. The body's context `Γ.lock,C<:cb` has
              -- empty `consumeset` (the topmost cvar is `.access`-mode, deeper
              -- cvars are behind the lock), so the wider budget narrows.
              have htyped :=
                ht (env.extend_cvar CS (cap := CS.ground_denot m')) m' henv hcompat'
              have htyped_narrow :
                  Eval ((Cf.rename Rename.succ).denot
                          (env.extend_cvar CS (cap := CS.ground_denot m')) m') m'
                    (e.subst (Subst.from_TypeEnv
                              (env.extend_cvar CS (cap := CS.ground_denot m'))))
                    (fun v m'' =>
                      Ty.exi_val_denot
                        (env.extend_cvar CS (cap := CS.ground_denot m')) T m'' v) := by
                apply eval_capability_set_monotonic htyped
                exact CapabilitySet.Subset.union_left
                  CapabilitySet.intersect_subset_left CapabilitySet.Subset.empty
              -- Show capability sets match (using hcap_rename and hCf_closed above)
              rw [← authority_eq_expand_captures hcap_rename
                    (closed_capture_denot_monotonic hCf_closed hts hsub)]
              rw [Subst.from_TypeEnv_extend_cvar_cap_irrelevant
                (cap := .empty) (cap' := CS.ground_denot m')]
              exact htyped_narrow

theorem sem_typ_pack
  {T : Ty .capt (s,C)} {cs : CaptureSet s} {x : Var .var s} {Γ : Ctx s}
  (hclosed_e : (Exp.pack cs x).IsClosed)
  (hΓ : Γ.IsClosed)
  (hcons : cs.consumable Γ)
  (ht : {} # Γ ⊨ Exp.var x : (T.subst (Subst.openCVar cs)).typ) :
  cs # Γ ⊨ Exp.pack cs x : T.exi := by
  intro env store hts _
  -- pack is no longer a simple value; use eval_pack instead
  have hsubst : (Exp.pack cs x).subst (Subst.from_TypeEnv env) =
         Exp.pack (cs.subst (Subst.from_TypeEnv env)) (x.subst (Subst.from_TypeEnv env)) := by
    simp only [Exp.subst]
  have hclosed_cs : cs.IsClosed := by
    cases hclosed_e with
    | pack hcs_closed _hx_closed => exact hcs_closed
  rw [hsubst]
  apply Eval.eval_pack
  · -- Need: (cs.subst _).reachability store ⊆ use-set ∪ drop-set.
    -- After ground_denot=reachability and folding to `cs.denot env store`,
    -- the post-refactor `intersect` against `Γ.accessset.cs.denot` is a no-op
    -- (since `cs.consumable Γ` and accessset includes `.consume` peaks).
    rw [← CaptureSet.ground_denot_eq_reachability]
    change cs.denot env store ⊆
      (cs.denot env store).intersect (Γ.useset.cs.denot env store)
        ∪ (Γ.consumeset.cs.denot env store).to_drop
    rw [intersect_useset_eq_self_of_consumable hts hΓ hclosed_cs hcons]
    exact CapabilitySet.Subset.union_right_left
  · simp only [Ty.exi_val_denot]
    -- Goal: CS.WfInHeap ∧ capt_val_denot (env.extend_cvar ...) T store ...
    constructor
    · -- Well-formedness of the capture set
      have hclosed_cs : cs.IsClosed := by
        cases hclosed_e with
        | pack hcs_closed _hx_closed => exact hcs_closed
      exact CaptureSet.wf_subst (CaptureSet.wf_of_closed hclosed_cs) (from_TypeEnv_wf_in_heap hts)
    · -- From ht, we have semantic typing for x at type T.subst (Subst.openCVar cs)
      have hx :
          Eval ((∅ : CaptureSet s).denot env store
                ∪ (Γ.consumeset.cs.denot env store).to_drop) store
            ((Exp.var x).subst (Subst.from_TypeEnv env))
            (fun v m' => Ty.exi_val_denot env (T.subst (Subst.openCVar cs)).typ m' v) := by
        have hcompat0 : store.is_compatible ((∅ : CaptureSet s).denot env store) := by
          simpa using Memory.is_compatible_empty store
        exact ht env store hts hcompat0
      have hvar : (Exp.var x).subst (Subst.from_TypeEnv env) =
             Exp.var (x.subst (Subst.from_TypeEnv env)) := by
        cases x <;> simp only [Exp.subst, Var.subst]
      rw [hvar] at hx
      cases hx
      case eval_var hQ =>
        have hQ' : Ty.val_denot env (T.subst (Subst.openCVar cs)) store
            (Exp.var (x.subst (Subst.from_TypeEnv env))) := by
          simpa only [Ty.exi_val_denot] using hQ
        let cs' := cs.subst (Subst.from_TypeEnv env)
        have hretype := open_carg_val_denot (env := env) (cap := cs'.ground_denot store)
          (C := cs) (T := T)
        exact (hretype store (Exp.var (x.subst (Subst.from_TypeEnv env)))).mpr hQ'
      case eval_val =>
        contradiction


theorem abs_val_denot_inv
  (hv : Ty.val_denot env (.arrow T1 cs T2) store (.var x)) :
  ∃ fx, x = .free fx
    ∧ ∃ cs' T0 e0 hval R,
      store.heap fx = some (Cell.val ⟨Exp.abs cs' T0 e0, hval, R⟩)
    ∧ expand_captures store.heap cs' ⊆ cs.denot env store
    ∧ (∀ (arg : Nat) (m' : Memory),
      m'.subsumes store ->
      m'.is_compatible (expand_captures store.heap cs') ->
      Ty.val_denot env T1 m' (.var (.free arg)) ->
      Eval (expand_captures store.heap cs') m'
        (e0.subst (Subst.openVar (.free arg)))
        (fun v m'' =>
          Ty.exi_val_denot
            (env.extend_var arg (compute_peakset env T1.captureSet)) T2 m'' v)) := by
  cases x with
  | bound bx => cases bx
  | free fx =>
    simp only [Ty.val_denot, resolve] at hv
    obtain ⟨hwf_e, hwf_cs, cs', T0, e0, hresolve, hwf_cs', hR0_sub, hfun⟩ := hv
    -- Analyze what's in the store at fx
    generalize hres : store.heap fx = res at hresolve ⊢
    cases res
    case none => simp at hresolve
    case some cell =>
      -- Match on the cell to extract HeapVal
      cases cell with
      | val hval =>
        -- hval : HeapVal, hresolve should relate to hval.unwrap
        simp only [List.empty_eq] at hresolve
        cases hval with | mk unwrap isVal reachability =>
        injection hresolve with hresolve
        subst hresolve
        use fx, rfl, cs', T0, e0, isVal, reachability, hres, hR0_sub, hfun
      | capability =>
        simp at hresolve
      | masked =>
        simp at hresolve


theorem tabs_val_denot_inv
  (hv : Ty.val_denot env (.poly T1 cs T2) store (.var x)) :
  ∃ fx, x = .free fx
    ∧ ∃ cs' S0 e0 hval R,
      store.heap fx = some (Cell.val ⟨Exp.tabs cs' S0 e0, hval, R⟩)
    ∧ expand_captures store.heap cs' ⊆ cs.denot env store
    ∧ (∀ (m' : Memory) (denot : Denot),
      m'.subsumes store ->
      m'.is_compatible (expand_captures store.heap cs') ->
      denot.is_proper ->
      denot.implies_simple_ans ->
      denot.ImplyAfter m' (Ty.val_denot env T1) ->
      denot.enforce_pure ->
      Eval (expand_captures store.heap cs') m'
        (e0.subst (Subst.openTVar .top))
        (fun v m'' =>
          Ty.exi_val_denot (env.extend_tvar denot) T2 m'' v)) := by
  cases x with
  | bound bx => cases bx
  | free fx =>
    simp only [Ty.val_denot, resolve] at hv
    obtain ⟨hwf_e, hwf_cs, cs', S0, e0, hresolve, hwf_cs', hR0_sub, hfun⟩ := hv
    -- Analyze what's in the store at fx
    generalize hres : store.heap fx = res at hresolve ⊢
    cases res
    case none => simp at hresolve
    case some cell =>
      -- Match on the cell to extract HeapVal
      cases cell with
      | val hval =>
        -- hval : HeapVal, hresolve should relate to hval.unwrap
        simp only [List.empty_eq] at hresolve
        cases hval with | mk unwrap isVal reachability =>
        injection hresolve with hresolve
        subst hresolve
        use fx, rfl, cs', S0, e0, isVal, reachability, hres, hR0_sub, hfun
      | capability =>
        simp at hresolve
      | masked =>
        simp at hresolve

theorem cabs_val_denot_inv
  (hv : Ty.val_denot env (.cpoly B cs T) store (.var x)) :
  ∃ fx, x = .free fx
    ∧ ∃ cs' B0 e0 hval R,
      store.heap fx = some (Cell.val ⟨Exp.cabs cs' B0 e0, hval, R⟩)
    ∧ expand_captures store.heap cs' ⊆ cs.denot env store
    ∧ (∀ (m' : Memory) (CS : CaptureSet {}),
      CS.WfInHeap m'.heap ->
      m'.subsumes store ->
      m'.is_compatible (expand_captures store.heap cs') ->
      ((CS.denot TypeEnv.empty m').BoundedBy (B.denot env m')) ->
      Eval (expand_captures store.heap cs') m'
        (e0.subst (Subst.openCVar CS))
        (fun v m'' =>
          Ty.exi_val_denot
            (env.extend_cvar CS (cap := CS.ground_denot m')) T m'' v)) := by
  cases x with
  | bound bx => cases bx
  | free fx =>
    simp only [Ty.val_denot, resolve] at hv
    obtain ⟨hwf_e, hwf_cs, cs', B0, e0, hresolve, hwf_cs', hR0_sub, hfun⟩ := hv
    -- Analyze what's in the store at fx
    generalize hres : store.heap fx = res at hresolve ⊢
    cases res
    case none => simp at hresolve
    case some cell =>
      -- Match on the cell to extract HeapVal
      cases cell with
      | val hval =>
        -- hval : HeapVal, hresolve should relate to hval.unwrap
        simp only [List.empty_eq] at hresolve
        cases hval with | mk unwrap isVal reachability =>
        injection hresolve with hresolve
        subst hresolve
        use fx, rfl, cs', B0, e0, isVal, reachability, hres, hR0_sub, hfun
      | capability =>
        simp at hresolve
      | masked =>
        simp at hresolve


theorem cap_val_denot_inv
  (hv : Ty.val_denot env (.cap cs) store (.var x)) :
  ∃ fx, x = .free fx ∧ store.heap fx = some (.capability .basic) ∧
    (cs.denot env store).covers (.access .epsilon) fx := by
  cases x with
  | bound bx => cases bx
  | free fx =>
    simp only [Ty.val_denot, Memory.lookup] at hv
    obtain ⟨hwf_e, hwf_cs, label, heq, hlookup, hmem⟩ := hv
    have : fx = label := by
      injection heq with h1
      rename_i heq_var
      injection heq_var
    subst this
    use fx, rfl, hlookup, hmem

theorem unit_val_denot_inv
  (hv : Ty.val_denot env .unit store (.var x)) :
  ∃ fx, x = .free fx
    ∧ ∃ hval R,
      store.heap fx = some (Cell.val ⟨Exp.unit, hval, R⟩) := by
  cases x with
  | bound bx => cases bx
  | free fx =>
    simp only [Ty.val_denot, resolve] at hv
    generalize hres : store.heap fx = res at hv ⊢
    cases res
    case none => simp at hv
    case some cell =>
      cases cell with
      | val hval =>
        simp only [List.empty_eq] at hv
        cases hval with | mk unwrap isVal reachability =>
        injection hv with hv
        subst hv
        use fx, rfl, isVal, reachability, hres
      | capability =>
        simp at hv
      | masked =>
        simp at hv

theorem cell_val_denot_inv
  (hv : Ty.val_denot env (.cell cs) store (.var x)) :
  ∃ fx b0 ℓ0, x = .free fx ∧ store.heap fx = some (.capability (.mcell b0 ℓ0)) ∧
    (cs.denot env store).covers (.access .epsilon) fx := by
  cases x with
  | bound bx => cases bx
  | free fx =>
    simp only [Ty.val_denot, Memory.lookup] at hv
    obtain ⟨hwf_cs, label, b0, ℓ0, heq, hlookup, hmem⟩ := hv
    cases heq
    exact ⟨fx, b0, ℓ0, rfl, hlookup, hmem⟩

theorem reader_val_denot_inv
  (hv : Ty.val_denot env (.reader cs) store (.var x)) :
  ∃ fx y b0 ℓ0 hval R,
    x = .free fx ∧
    store.heap fx = some (Cell.val ⟨Exp.reader (.free y), hval, R⟩) ∧
    store.heap y = some (.capability (.mcell b0 ℓ0)) ∧
    (cs.denot env store).covers (.access .ro) y := by
  cases x with
  | bound bx => cases bx
  | free fx =>
    have hv' := hv
    simp only [Ty.val_denot] at hv'
    rcases hv' with ⟨_, _, y, b0, ℓ0, hres, hlookup, hcov⟩
    -- From hres, the heap at fx must store a reader value
    have hheap :
        ∃ v, store.heap fx = some (Cell.val v) ∧ v.unwrap = Exp.reader (.free y) := by
      cases hmem : store.heap fx with
      | none => simp [resolve, hmem] at hres
      | some cell =>
        cases cell with
        | val v =>
          have hvunwrap : v.unwrap = Exp.reader (.free y) := by
            simpa only [resolve, hmem, Option.some.injEq] using hres
          exact ⟨v, rfl, hvunwrap⟩
        | capability => simp [resolve, hmem] at hres
        | masked => simp [resolve, hmem] at hres
    obtain ⟨v, hlookup_fx, hvunwrap⟩ := hheap
    cases v with
    | mk unwrap isVal reachability =>
      cases hvunwrap
      refine ⟨fx, y, b0, ℓ0, isVal, reachability, rfl, ?_, ?_, hcov⟩
      · simp [hlookup_fx]
      · simpa [Memory.lookup] using hlookup

theorem bool_val_denot_inv
  (hv : Ty.val_denot env .bool store (.var x)) :
  ∃ fx, ∃ b : Bool, ∃ hval R,
    x = .free fx ∧
    store.heap fx = some (Cell.val ⟨(if b then Exp.btrue else Exp.bfalse), hval, R⟩) := by
  cases x with
  | bound bx => cases bx
  | free fx =>
    simp only [Ty.val_denot, resolve, List.empty_eq] at hv
    generalize hres : store.heap fx = res at hv ⊢
    cases res
    case none =>
      cases hv with
      | inl h => cases h
      | inr h => cases h
    case some cell =>
      cases cell with
      | val hval =>
        cases hval with | mk unwrap isVal reachability =>
        cases hv with
        | inl hl =>
          injection hl with hl
          subst hl
          use fx, true, isVal, reachability, rfl, hres
        | inr hr =>
          injection hr with hr
          subst hr
          use fx, false, isVal, reachability, rfl, hres
      | capability =>
        cases hv with
        | inl h => cases h
        | inr h => cases h
      | masked =>
        cases hv with
        | inl h => cases h
        | inr h => cases h

theorem var_subst_is_free {x : BVar s .var} :
  ∃ fx, (Subst.from_TypeEnv env).var x = .free fx := by
  use (env.lookup_var x).1
  rfl

theorem var_exp_denot_inv {A : CapabilitySet}
  (hv : Ty.exi_exp_denot env T A store (.var x)) :
  Ty.exi_val_denot env T store (.var x) := by
  simp only [Ty.exi_exp_denot, List.empty_eq] at hv
  cases hv
  case eval_val _ hQ => exact hQ
  case eval_var hQ => exact hQ

theorem closed_var_inv (x : Var .var {}) :
  ∃ fx, x = .free fx := by
  cases x
  case bound bx => cases bx
  case free fx => use fx

/-- For closed capture sets, the denotation is preserved under substitution with from_TypeEnv,
provided the environment satisfies the cvar invariant. -/
theorem closed_captureset_subst_denot
  {s : Sig} {env : TypeEnv s} {D : CaptureSet s}
  (hD_closed : D.IsClosed) :
  (D.subst (Subst.from_TypeEnv env)).denot TypeEnv.empty = D.denot env := by
  induction hD_closed with
  | empty =>
    rfl
  | union _ _ ih1 ih2 =>
    simp only [CaptureSet.subst, CaptureSet.denot] at ih1 ih2 ⊢
    funext m
    simp only [CaptureSet.ground_denot]
    rw [congrFun ih1 m, congrFun ih2 m]
  | cvar =>
    rename_i m cv
    cases m <;> simp [CaptureSet.denot, Subst.from_TypeEnv_empty, CaptureSet.subst_id]
  | var_bound =>
    rename_i m xb
    simp only [CaptureSet.subst, CaptureSet.denot, Var.subst, Subst.from_TypeEnv]

theorem sem_typ_app
  {T1 : Ty .capt s} {T2 : Ty .exi (s,x)}
  {x y : BVar s .var} -- x and y must be BOUND variables (from typing rule)
  (hΓ : Γ.IsClosed)
  (haccess : (CaptureSet.var .epsilon (.bound x)).accessible Γ)
  (hx : {} # Γ ⊨ Exp.var (.bound x) :
    .typ ((Ty.arrow T1 (.var .epsilon (.bound x)) T2)))
  (hy : {} # Γ ⊨ Exp.var (.bound y) : .typ T1) :
  (.var .epsilon (.bound x)) # Γ ⊨
    Exp.app (.bound x) (.bound y) : T2.subst (Subst.openVar (.bound y)) := by
  intro env store hts hcompat
  -- Extract function denotation (via the val_denot conjunct only)
  have h1 := semtyp_to_exi_exp_denot hx hts (Memory.is_compatible_empty store)
  simp only [List.empty_eq] at h1
  have h1' := var_exp_denot_inv h1
  -- refineCaptureSet for arrow replaces the capture set:
  --   (Ty.arrow T1 cs T2).refineCaptureSet cs' = Ty.arrow T1 cs' T2
  -- So h1' : Ty.val_denot env (Ty.arrow T1 (.var .epsilon (.bound x)) T2) ...
  simp only [Ty.exi_val_denot] at h1'
  -- Extract the arrow structure
  have ⟨fx, hfx, cs', T0, e0, hval, R, hlk, hR0_sub, hfun⟩ := abs_val_denot_inv h1'
  -- Extract argument denotation
  have h2 := semtyp_to_exi_exp_denot hy hts (Memory.is_compatible_empty store)
  simp only [List.empty_eq] at h2
  have h2' := var_exp_denot_inv h2
  simp only [Ty.exi_val_denot] at h2'
  -- Determine concrete locations
  have : fx = (env.lookup_var x).1 := by cases hfx; rfl
  subst this
  let fy := (env.lookup_var y).1
  simp only [Exp.subst, Subst.from_TypeEnv, Var.subst, CaptureSet.denot,
    List.empty_eq]
  -- Derive compat for the closure's authority from the budget compat.
  have hcompat_closure : store.is_compatible (expand_captures store.heap cs') :=
    Memory.is_compatible_subset hR0_sub hcompat
  -- Apply function to argument; happ's post is `Ty.exi_val_denot` only.
  have happ := hfun fy store (Memory.subsumes_refl store) hcompat_closure h2'
  -- Convert val_denot at extended env to val_denot at substituted env.
  let ps := compute_peakset env T1.captureSet
  have heqv := open_arg_exi_val_denot (env:=env) (y:=.bound y) (ps:=ps) (T:=T2)
  have hinterp : interp_var env (Var.bound y) = fy := rfl
  rw [hinterp] at heqv
  have happ' : Eval (expand_captures store.heap cs') store
      (e0.subst (Subst.openVar (Var.free fy)))
      (fun v m'' =>
        Ty.exi_val_denot env (T2.subst (Subst.openVar (Var.bound y))) m'' v) := by
    apply eval_post_monotonic _ happ
    intro m'' v hval
    exact (heqv m'' v).mp hval
  -- Widen the authority: expand_captures cs' ⊆ (.var .epsilon (.bound x)).denot env store
  have happ'' := eval_capability_set_monotonic happ' hR0_sub
  -- Build the application's Eval and widen budget to include consumeset.to_drop.
  have heval := Eval.eval_apply hlk happ''
  have huse_eq :
      ((CaptureSet.var .epsilon (.bound x)).denot env store).intersect
          (Γ.useset.cs.denot env store)
        = (CaptureSet.var .epsilon (.bound x)).denot env store :=
    intersect_useset_eq_self_of_accessible hts hΓ
      CaptureSet.IsClosed.var_bound haccess
  apply eval_capability_set_monotonic heval
  change CaptureSet.denot env (.var .epsilon (.bound x)) store ⊆
    ((CaptureSet.var .epsilon (.bound x)).denot env store).intersect
        (Γ.useset.cs.denot env store)
      ∪ (Γ.consumeset.cs.denot env store).to_drop
  rw [huse_eq]
  exact CapabilitySet.Subset.union_right_left

theorem sem_typ_tapp
  {S : PureTy s} {T : Ty .exi (s,X)}
  {x : BVar s .var} -- x must be a BOUND variable (from typing rule)
  (hΓ : Γ.IsClosed)
  (haccess : (CaptureSet.var .epsilon (.bound x)).accessible Γ)
  (hx : {} # Γ ⊨ Exp.var (.bound x) :
    .typ (Ty.poly S.core (.var .epsilon (.bound x)) T)) :
  (.var .epsilon (.bound x)) # Γ ⊨ Exp.tapp (.bound x) S : T.subst (Subst.openTVar S) := by
  intro env store hts hcompat
  -- Extract function denotation
  have h1 := semtyp_to_exi_exp_denot hx hts (Memory.is_compatible_empty store)
  simp only [List.empty_eq] at h1
  have h1' := var_exp_denot_inv h1
  simp only [Ty.exi_val_denot] at h1'
  -- Extract the poly structure
  have ⟨fx, hfx, cs, S0, e0, hval, R, hlk, hR0_sub, hfun⟩ := tabs_val_denot_inv h1'
  -- Determine concrete location
  have : fx = (env.lookup_var x).1 := by cases hfx; rfl
  subst this
  have huse_eq :
      ((CaptureSet.var .epsilon (.bound x)).denot env store).intersect
          (Γ.useset.cs.denot env store)
        = (CaptureSet.var .epsilon (.bound x)).denot env store :=
    intersect_useset_eq_self_of_accessible hts hΓ
      CaptureSet.IsClosed.var_bound haccess
  -- Build the body Eval at the narrower budget, then widen to the
  -- `Cf.denot ∪ consumeset.to_drop` budget required by SemanticTyping.
  suffices heval : Eval ((CaptureSet.var .epsilon (.bound x)).denot env store) store
      ((Exp.tapp (.bound x) S).subst (Subst.from_TypeEnv env))
      (fun v m'' =>
        Ty.exi_val_denot env (T.subst (Subst.openTVar S)) m'' v) by
    apply eval_capability_set_monotonic heval
    show (CaptureSet.var .epsilon (.bound x)).denot env store ⊆
      ((CaptureSet.var .epsilon (.bound x)).denot env store).intersect
          (Γ.useset.cs.denot env store)
        ∪ (Γ.consumeset.cs.denot env store).to_drop
    rw [huse_eq]
    exact CapabilitySet.Subset.union_right_left
  simp only [Exp.subst, Subst.from_TypeEnv, Var.subst, CaptureSet.denot,
    List.empty_eq]
  have hcompat_closure : store.is_compatible (expand_captures store.heap cs) :=
    Memory.is_compatible_subset hR0_sub hcompat
  have himply_simple := val_denot_implies_simple_ans (typed_env_is_implying_simple_ans hts) S.core
  have happ := hfun store (Ty.val_denot env S.core) (Memory.subsumes_refl store)
    hcompat_closure
    (val_denot_is_proper hts)
    himply_simple
    (by intro m' hsub; exact Denot.imply_implyat (Denot.imply_refl _))
    (pure_ty_enforce_pure (typed_env_enforces_pure hts) S.p)
  have heqv := open_targ_exi_val_denot (env:=env) (S:=S) (T:=T)
  have happ' : Eval (expand_captures store.heap cs) store
      (e0.subst (Subst.openTVar .top))
      (fun v m'' =>
        Ty.exi_val_denot env (T.subst (Subst.openTVar S)) m'' v) := by
    apply eval_post_monotonic _ happ
    intro m'' v hval
    exact (heqv m'' v).mp hval
  have happ'' := eval_capability_set_monotonic happ' hR0_sub
  apply Eval.eval_tapply hlk happ''


theorem sem_typ_capp
  {x : BVar s .var}
  {T : Ty .exi (s,C)}
  {D : CaptureSet s}
  (hΓ : Γ.IsClosed)
  (haccess : (CaptureSet.var .epsilon (.bound x)).accessible Γ)
  (hD_closed : D.IsClosed)
  (hx : {} # Γ ⊨ Exp.var (.bound x) :
    .typ (.cpoly (.bound D) (.var .epsilon (.bound x)) T)) :
  (.var .epsilon (.bound x)) # Γ ⊨ Exp.capp (.bound x) D : T.subst (Subst.openCVar D) := by
  intro env store hts hcompat
  -- Extract function denotation
  have h1 := semtyp_to_exi_exp_denot hx hts (Memory.is_compatible_empty store)
  simp only [List.empty_eq] at h1
  have h1' := var_exp_denot_inv h1
  simp only [Ty.exi_val_denot] at h1'
  -- Extract the cpoly structure
  have ⟨fx, hfx, cs, B0, e0, hval, R, hlk, hR0_sub, hfun⟩ := cabs_val_denot_inv h1'
  -- Determine concrete location
  have : fx = (env.lookup_var x).1 := by cases hfx; rfl
  subst this
  have huse_eq :
      ((CaptureSet.var .epsilon (.bound x)).denot env store).intersect
          (Γ.useset.cs.denot env store)
        = (CaptureSet.var .epsilon (.bound x)).denot env store :=
    intersect_useset_eq_self_of_accessible hts hΓ
      CaptureSet.IsClosed.var_bound haccess
  -- Build the body Eval at the narrower budget, then widen to include
  -- `consumeset.to_drop` as required by SemanticTyping.
  suffices heval : Eval ((CaptureSet.var .epsilon (.bound x)).denot env store) store
      ((Exp.capp (.bound x) D).subst (Subst.from_TypeEnv env))
      (fun v m'' =>
        Ty.exi_val_denot env (T.subst (Subst.openCVar D)) m'' v) by
    apply eval_capability_set_monotonic heval
    show (CaptureSet.var .epsilon (.bound x)).denot env store ⊆
      ((CaptureSet.var .epsilon (.bound x)).denot env store).intersect
          (Γ.useset.cs.denot env store)
        ∪ (Γ.consumeset.cs.denot env store).to_drop
    rw [huse_eq]
    exact CapabilitySet.Subset.union_right_left
  simp only [Exp.subst, Subst.from_TypeEnv, Var.subst, List.empty_eq]
  let D' := D.subst (Subst.from_TypeEnv env)
  have hD'_denot : D'.denot TypeEnv.empty = D.denot env :=
    closed_captureset_subst_denot hD_closed
  have hD'_wf : D'.WfInHeap store.heap := by
    have hD_wf : D.WfInHeap store.heap := CaptureSet.wf_of_closed hD_closed
    have hσ_wf : (Subst.from_TypeEnv env).WfInHeap store.heap :=
      from_TypeEnv_wf_in_heap hts
    exact CaptureSet.wf_subst hD_wf hσ_wf
  have hcompat_closure : store.is_compatible (expand_captures store.heap cs) :=
    Memory.is_compatible_subset hR0_sub hcompat
  have happ := hfun store D'
    hD'_wf
    (Memory.subsumes_refl store)
    hcompat_closure
    (by
      rw [hD'_denot]
      simpa only [CaptureBound.denot, List.empty_eq] using
        (CapabilitySet.BoundedBy.set CapabilitySet.Subset.refl))
  have heqv := open_carg_exi_val_denot (env:=env) (C:=D) (T:=T)
    (cap := D'.ground_denot store)
  have happ2 : Eval (expand_captures store.heap cs) store
      (e0.subst (Subst.openCVar D'))
      (fun v m'' =>
        Ty.exi_val_denot env (T.subst (Subst.openCVar D)) m'' v) := by
    apply eval_post_monotonic _ happ
    intro m'' v hval
    exact (heqv m'' v).mp hval
  have happ3 := eval_capability_set_monotonic happ2 hR0_sub
  apply Eval.eval_capply hlk happ3


theorem sem_typ_invoke
  {x y : BVar s .var} -- x and y must be BOUND variables (from typing rule)
  (hΓ : Γ.IsClosed)
  (haccess : (CaptureSet.var .epsilon (.bound x)).accessible Γ)
  (hx : {} # Γ ⊨ Exp.var (.bound x) :
    .typ (.cap (.var .epsilon (.bound x))))
  (hy : {} # Γ ⊨ Exp.var (.bound y) :
    .typ .unit) :
  (.var .epsilon (.bound x)) # Γ ⊨
    Exp.app (.bound x) (.bound y) : .typ .unit := by
  intro env store hts _
  -- Extract capability denotation from hx
  have h1 := semtyp_to_exi_exp_denot hx hts (Memory.is_compatible_empty store)
  simp only [List.empty_eq] at h1
  have h1' := var_exp_denot_inv h1
  simp only [Ty.exi_val_denot] at h1'
  -- Extract the capability structure
  have ⟨fx, hfx, hlk_cap, hmem_cap⟩ := cap_val_denot_inv h1'
  -- Extract unit denotation from hy
  have h2 := semtyp_to_exi_exp_denot hy hts (Memory.is_compatible_empty store)
  simp only [List.empty_eq] at h2
  have h2' := var_exp_denot_inv h2
  simp only [Ty.exi_val_denot] at h2'
  -- Extract the unit structure
  have ⟨fy, hfy, hval_unit, R, hlk_unit⟩ := unit_val_denot_inv h2'
  -- Determine concrete locations
  have : fx = (env.lookup_var x).1 := by cases hfx; rfl
  subst this
  have : fy = (env.lookup_var y).1 := by cases hfy; rfl
  subst this
  simp only [Exp.subst, Subst.from_TypeEnv, Var.subst, CaptureSet.denot, List.empty_eq]
  -- Show env.lookup_var x is covered in the capability set
  have hcov :
    (CaptureSet.denot env (.var .epsilon (.bound x)) store).covers
      (.access .epsilon) (env.lookup_var x).1 := hmem_cap
  -- The use-set after tightening equals var.denot via accessibility.
  have huse_eq :
      ((CaptureSet.var .epsilon (.bound x)).denot env store).intersect
          (Γ.useset.cs.denot env store)
        = (CaptureSet.var .epsilon (.bound x)).denot env store :=
    intersect_useset_eq_self_of_accessible hts hΓ
      CaptureSet.IsClosed.var_bound haccess
  -- Build the Eval at the narrower budget, then widen to include consumeset.to_drop.
  suffices heval : Eval (CaptureSet.denot env (.var .epsilon (.bound x)) store) store
      (Exp.app (Var.free (env.lookup_var x).1) (Var.free (env.lookup_var y).1))
      (fun v m' => Ty.exi_val_denot env Ty.unit.typ m' v) by
    apply eval_capability_set_monotonic heval
    change CaptureSet.denot env (.var .epsilon (.bound x)) store ⊆
      ((CaptureSet.var .epsilon (.bound x)).denot env store).intersect
          (Γ.useset.cs.denot env store)
        ∪ (Γ.consumeset.cs.denot env store).to_drop
    rw [huse_eq]
    exact CapabilitySet.Subset.union_right_left
  apply Eval.eval_invoke hcov hlk_cap hlk_unit
  simp only [Ty.exi_val_denot, Ty.val_denot, resolve]


theorem sem_typ_unit :
  {} # Γ ⊨ Exp.unit : .typ .unit := by
  intro env store hts _
  simp only [Exp.subst]
  apply Eval.eval_val
  · exact Exp.IsSimpleVal.unit
  · simp only [Ty.exi_val_denot, Ty.val_denot, resolve]

theorem sem_typ_btrue :
  {} # Γ ⊨ Exp.btrue : .typ .bool := by
  intro env store hts _
  simp only [Exp.subst]
  apply Eval.eval_val
  · exact Exp.IsSimpleVal.btrue
  · simp only [Ty.exi_val_denot, Ty.val_denot, resolve]
    left; trivial

theorem sem_typ_bfalse :
  {} # Γ ⊨ Exp.bfalse : .typ .bool := by
  intro env store hts _
  simp only [Exp.subst]
  apply Eval.eval_val
  · exact Exp.IsSimpleVal.bfalse
  · simp only [Ty.exi_val_denot, Ty.val_denot, resolve]
    right; trivial

theorem sem_typ_cond
  {C1 C2 C3 : CaptureSet s} {Γ : Ctx s}
  {x : Var .var s} {e2 e3 : Exp s} {T : Ty .exi s}
  (ht1 : C1 # Γ ⊨ (.var x) : .typ .bool)
  (ht2 : C2 # Γ ⊨ e2 : T)
  (ht3 : C3 # Γ ⊨ e3 : T) :
  (C1 ∪ C2 ∪ C3) # Γ ⊨ (.cond x e2 e3) : T := by
  intro env store hts hcompat
  simp only [Exp.subst, List.empty_eq]
  -- Get the guard's evaluation, then use Eval.var_inv to extract Q1 at store.
  have hcompat_C1 : store.is_compatible (C1.denot env store) :=
    Memory.is_compatible_union_left (Memory.is_compatible_union_left hcompat)
  have hguard_base := semtyp_to_exi_exp_denot ht1 hts hcompat_C1
  simp only [Ty.exi_exp_denot] at hguard_base
  -- The guard is a `.var`, so by `Eval.var_inv` the bool postcondition holds at `store`.
  have hQ1_at_store : Ty.val_denot env .bool store (.var (x.subst (Subst.from_TypeEnv env))) := by
    have h := Eval.var_inv hguard_base
    simpa [Denot.as_mpost, Ty.exi_val_denot] using h
  simp only [Ty.val_denot] at hQ1_at_store
  -- Resolve the var to a bool at store.
  have hres :
      resolve store.heap (.var (x.subst (Subst.from_TypeEnv env))) = some .btrue ∨
      resolve store.heap (.var (x.subst (Subst.from_TypeEnv env))) = some .bfalse :=
    hQ1_at_store
  -- Compat for C2 and C3 (subsets of C1 ∪ C2 ∪ C3).
  have hcompat_C2 : store.is_compatible (C2.denot env store) :=
    Memory.is_compatible_union_right (Memory.is_compatible_union_left hcompat)
  have hcompat_C3 : store.is_compatible (C3.denot env store) :=
    Memory.is_compatible_union_right hcompat
  -- Widening lemmas.
  have hsubC2 : CaptureSet.denot env C2 store ⊆ CaptureSet.denot env (C1 ∪ C2 ∪ C3) store :=
    CapabilitySet.Subset.trans CapabilitySet.Subset.union_right_right
      CapabilitySet.Subset.union_right_left
  have hsubC3 : CaptureSet.denot env C3 store ⊆ CaptureSet.denot env (C1 ∪ C2 ∪ C3) store := by
    simp only [CaptureSet.denot, CaptureSet.subst, CaptureSet.ground_denot, List.empty_eq]
    apply CapabilitySet.Subset.union_right_right
  -- Construct eval_cond. Each branch's budget gets the same `consumeset.to_drop`
  -- gift, so widening just on the capture-set side covers everything. Under the
  -- new tightening, `intersect` distributes over `∪` by structural definition,
  -- so `intersect (C1 ∪ C2 ∪ C3) D` decomposes structurally.
  let X := (Γ.consumeset.cs.denot env store).to_drop
  let D := Γ.useset.cs.denot env store
  -- `intersect` distributes over `∪` structurally:
  -- `(A ∪ B ∪ C).intersect D = A.intersect D ∪ B.intersect D ∪ C.intersect D`
  -- (by `rfl`, since `intersect` matches structurally on its first arg).
  have hwidenC2 :
      (C2.denot env store).intersect D ∪ X ⊆
        ((C1 ∪ C2 ∪ C3).denot env store).intersect D ∪ X := by
    apply CapabilitySet.Subset.union_left
    · -- `I_C2 ⊆ ((I_C1 ∪ I_C2) ∪ I_C3) ∪ X`
      exact CapabilitySet.Subset.trans
        CapabilitySet.Subset.union_right_right
        (CapabilitySet.Subset.trans
          CapabilitySet.Subset.union_right_left
          CapabilitySet.Subset.union_right_left)
    · exact CapabilitySet.Subset.union_right_right
  have hwidenC3 :
      (C3.denot env store).intersect D ∪ X ⊆
        ((C1 ∪ C2 ∪ C3).denot env store).intersect D ∪ X := by
    apply CapabilitySet.Subset.union_left
    · -- `I_C3 ⊆ ((I_C1 ∪ I_C2) ∪ I_C3) ∪ X`
      exact CapabilitySet.Subset.trans
        CapabilitySet.Subset.union_right_right
        CapabilitySet.Subset.union_right_left
    · exact CapabilitySet.Subset.union_right_right
  apply Eval.eval_cond hres
  · -- true branch
    intro _hres_true
    have hthen := ht2 env store hts hcompat_C2
    exact eval_capability_set_monotonic hthen hwidenC2
  · -- false branch
    intro _hres_false
    have helse := ht3 env store hts hcompat_C3
    exact eval_capability_set_monotonic helse hwidenC3

theorem sem_typ_reader
  (_hclosed : Γ.IsClosed)
  (hx : Γ.LookupVar x (.cell C)) :
  {} # Γ ⊨ Exp.reader (.bound x) :
    (.typ (.reader (.var .ro (.bound x)))) := by
  intro env store hts _
  simp only [Exp.subst]
  apply Eval.eval_val
  · exact Exp.IsSimpleVal.reader
  · simp only [Ty.exi_val_denot, Ty.val_denot]
    -- Get the cell denotation from the lookup
    have hcell := typed_env_lookup_var hts hx
    -- hcell : Ty.val_denot env (.cell C) store (.var (.free (env.lookup_var x).1))
    have ⟨_, b0, ℓ0, rfl, hlookup_cell, _⟩ := cell_val_denot_inv hcell
    -- Ty.val_denot .reader cs = e.WfInHeap ∧ cs'.WfInHeap ∧ ∃ label b0, ...
    simp only [Var.subst, Subst.from_TypeEnv]
    refine ⟨?hwf_e, ?hwf_cs, (env.lookup_var x).1, b0, ℓ0, ?hres, ?hlookup, ?hcover⟩
    · -- e.WfInHeap
      exact Exp.WfInHeap.wf_reader (Var.WfInHeap.wf_free hlookup_cell)
    · -- cs.subst.WfInHeap
      exact CaptureSet.WfInHeap.wf_var_free hlookup_cell
    · -- resolve = some (.reader (.free label))
      rfl
    · -- lookup = .capability (.mcell b0)
      simpa [Memory.lookup] using hlookup_cell
    · -- covers (.access .ro) label
      have hden :
        CaptureSet.denot env (CaptureSet.var .ro (Var.bound x)) store
          = CapabilitySet.singleton .ro (env.lookup_var x).1 := by
        simp only [CaptureSet.denot, CaptureSet.subst, Subst.from_TypeEnv, Var.subst,
              CaptureSet.ground_denot, CapabilitySet.applyMut, CapabilitySet.applyRO,
              CapabilitySet.singleton, reachability_of_loc, hlookup_cell,
              CapMode.applyRO]
      have hcov_singleton :
          CapabilitySet.covers (.access .ro) (env.lookup_var x).1
            (CapabilitySet.singleton .ro (env.lookup_var x).1) :=
        CapabilitySet.covers.here (l:=(env.lookup_var x).1) CapMode.Le.refl
      simpa [hden] using hcov_singleton

theorem sem_typ_alloc
  {x : BVar s .var}
  (hx : {} # Γ ⊨ Exp.var (.bound x) : .typ .bool) :
  {} # Γ ⊨ Exp.alloc (.bound x) : .exi (.cell (.cvar .epsilon .here)) := by
  intro env store hts _
  simp only [Exp.subst, Var.subst, Subst.from_TypeEnv, List.empty_eq]
  set fx := (env.lookup_var x).1
  -- From hx, the variable resolves to a bool in `store`.
  have hx_eval := semtyp_to_exi_exp_denot hx hts (Memory.is_compatible_empty store)
  simp only [Ty.exi_exp_denot, Ty.exi_val_denot,
    Exp.subst, Var.subst, Subst.from_TypeEnv, List.empty_eq] at hx_eval
  have hbool : Ty.val_denot env .bool store (.var (.free fx)) := by
    cases hx_eval with
    | eval_val hv _ => cases hv
    | eval_var hQ => exact hQ
  simp only [Ty.val_denot, resolve] at hbool
  -- Destruct the heap entry at `fx` to extract the underlying boolean value.
  cases hres : store.heap fx with
  | none =>
    rcases hbool with h | h <;> rw [hres] at h <;> cases h
  | some cell =>
    cases cell with
    | capability =>
      rcases hbool with h | h <;> rw [hres] at h <;> cases h
    | masked =>
      rcases hbool with h | h <;> rw [hres] at h <;> cases h
    | val v =>
      rw [hres] at hbool
      simp only at hbool
      obtain ⟨unwrap, isVal, R⟩ := v
      simp only at hbool
      -- `hbool : unwrap = .btrue ∨ unwrap = .bfalse`.  Case on which boolean.
      have hclose : ∀ (b : Bool),
          (b = true → some unwrap = some Exp.btrue) →
          (b = false → some unwrap = some Exp.bfalse) →
          Eval (CaptureSet.denot env ∅ store
                ∪ (Γ.consumeset.cs.denot env store).to_drop) store
            (Exp.alloc (Var.free fx))
            (fun v m' =>
              Ty.exi_val_denot env
                (Ty.exi (Ty.cell (CaptureSet.cvar Mutability.epsilon BVar.here))) m' v) := by
        intro b hbt hbf
        have hunwrap : unwrap = (if b then Exp.btrue else Exp.bfalse) := by
          cases b
          · exact Option.some.inj (hbf rfl)
          · exact Option.some.inj (hbt rfl)
        subst hunwrap
        apply Eval.eval_alloc (b := b) (hv := isVal) (R := R)
        · change store.heap fx = _
          exact hres
        · intro l hfresh
          let m' := store.extend_mcell l b hfresh
          have hlookup_l : m'.heap l = some (.capability (.mcell b .live)) :=
            Memory.extend_mcell_lookup hfresh
          simp only [Ty.exi_val_denot]
          change _ ∧ Ty.val_denot _ _ _ _
          refine ⟨CaptureSet.WfInHeap.wf_var_free hlookup_l, ?_⟩
          simp only [Ty.val_denot]
          refine ⟨CaptureSet.WfInHeap.wf_var_free hlookup_l, l, b, .live, rfl, hlookup_l, ?_⟩
          change ((CaptureSet.var Mutability.epsilon (Var.free l)).ground_denot m').covers
            (.access Mutability.epsilon) l
          simp only [CaptureSet.ground_denot, reachability_of_loc, hlookup_l,
            CapabilitySet.applyMut]
          exact CapabilitySet.covers.here CapMode.Le.refl
      rcases hbool with hb | hb
      · exact hclose true (fun _ => hb) (by intro h; cases h)
      · exact hclose false (by intro h; cases h) (fun _ => hb)


theorem sem_typ_drop {x : BVar s .var}
  (hx : {} # Γ ⊨ Exp.var (.bound x) :
    .typ (.cell (.var .epsilon (.bound x))))
  (hΓ : Γ.IsClosed)
  (hcons : (CaptureSet.var .epsilon (.bound x) : CaptureSet s).consumable Γ) :
  (.var .epsilon (.bound x)) # Γ ⊨ Exp.drop (.bound x) : .typ .unit := by
  intro env store hts hcompat
  -- Extract cell denotation from hx
  have h1 := semtyp_to_exi_exp_denot hx hts (Memory.is_compatible_empty store)
  simp only [List.empty_eq] at h1
  have h1' := var_exp_denot_inv h1
  simp only [Ty.exi_val_denot] at h1'
  have ⟨fx, b0, ℓ0, hfx, hlk_cell, hmem_cell⟩ := cell_val_denot_inv h1'
  have : fx = (env.lookup_var x).1 := by cases hfx; rfl
  subst this
  simp only [Exp.subst, Subst.from_TypeEnv, Var.subst, List.empty_eq]
  -- Prove covers: env.lookup_var x is covered by the budget capture set
  have hcov :
    (((CaptureSet.var .epsilon (Var.bound x)).subst
      (Subst.from_TypeEnv env)).ground_denot store).covers (.access .epsilon)
        (env.lookup_var x).1 := by
    simp only [CaptureSet.subst, Var.subst, Subst.from_TypeEnv, CaptureSet.ground_denot,
          CapabilitySet.applyMut, reachability_of_loc, hlk_cell, CapabilitySet.singleton]
    exact CapabilitySet.covers.here CapMode.Le.refl
  -- Use hcompat to derive that the cell is live
  have hlive : ℓ0 = .live := by
    have hbudget_denot :
      ((CaptureSet.var .epsilon (Var.bound x)).denot env store) =
        CapabilitySet.singleton .epsilon (env.lookup_var x).1 := by
      simp only [CaptureSet.denot, CaptureSet.subst, Var.subst, Subst.from_TypeEnv,
        CaptureSet.ground_denot, CapabilitySet.applyMut, reachability_of_loc, hlk_cell]
    have hcompat' : store.is_compatible (CapabilitySet.singleton .epsilon (env.lookup_var x).1) :=
      hbudget_denot ▸ hcompat
    exact hcompat' (.access .epsilon) (env.lookup_var x).1 b0 ℓ0
      CapabilitySet.hasmem.here hlk_cell
  subst hlive
  have hlk_cell' :
    store.lookup (env.lookup_var x).1 = some (.capability (.mcell b0 .live)) := by
    simpa [Memory.lookup] using hlk_cell
  -- Extract a `.consume`-unlocked cvar witness for the drop location.
  have hbudget_hasmem :
      ((CaptureSet.var .epsilon (.bound x)).denot env store).hasmem
        (.access .epsilon) (env.lookup_var x).1 := by
    simp only [CaptureSet.denot, CaptureSet.subst, Var.subst, Subst.from_TypeEnv,
      CaptureSet.ground_denot, CapabilitySet.applyMut, reachability_of_loc, hlk_cell,
      CapabilitySet.singleton]
    exact CapabilitySet.hasmem.here
  obtain ⟨c, B, mu', hlookup_cvar, hcvar_mem⟩ :=
    consumable_to_consume_witness hts hΓ CaptureSet.IsClosed.var_bound hcons hbudget_hasmem
  -- Apply Eval.eval_drop and discharge the post directly with the witness.
  apply Eval.eval_drop (hx := hlk_cell')
  · simp only [Ty.exi_val_denot, Ty.val_denot, resolve]
  · -- The `.drop` covers needed by eval_drop comes from `Γ.consumeset.to_drop`
    -- in the budget: the consume-unlocked cvar `c` witnessed above contributes
    -- its runtime cap set to `Γ.consumeset.cs.denot`, and `.to_drop` lowers it
    -- to `.drop` mode.
    apply CapabilitySet.covers.right
    -- Switch from `(env.lookup_cvar c).2` form to the `.1.ground_denot` form
    -- (equal under EnvTyping by `typed_env_cvar_cap_eq`).
    have hcvar_mem_cs :
        ((env.lookup_cvar c).1.ground_denot store).hasmem mu' (env.lookup_var x).1 := by
      rw [← typed_env_cvar_cap_eq hts c]
      exact hcvar_mem
    have hcs_mem : (Γ.consumeset.cs.denot env store).hasmem mu' (env.lookup_var x).1 :=
      consumeset_hasmem_via_cs hlookup_cvar hcvar_mem_cs
    exact CapabilitySet.hasmem_implies_covers (CapabilitySet.hasmem_to_drop_drop hcs_mem)

theorem sem_typ_read
  {x : BVar s .var}
  (hΓ : Γ.IsClosed)
  (haccess : (CaptureSet.var .epsilon (.bound x)).accessible Γ)
  (hx : {} # Γ ⊨ Exp.var (.bound x) : .typ (.reader C)) :
  (.var .epsilon (.bound x)) # Γ ⊨ Exp.read (.bound x) : .typ .bool := by
  intro env store hts hcompat
  -- Extract reader denotation from hx
  have h1 := semtyp_to_exi_exp_denot hx hts (Memory.is_compatible_empty store)
  simp only [List.empty_eq] at h1
  have h1' := var_exp_denot_inv h1
  simp only [Ty.exi_val_denot] at h1'
  -- Extract the reader structure
  have ⟨fx, y, b0, ℓ0, hval_reader, R, hfx, hlookup_reader, hlookup_cell, hcov_reader⟩ :=
    reader_val_denot_inv h1'
  -- Determine concrete location
  have : fx = (env.lookup_var x).1 := by cases hfx; rfl
  subst this
  -- Simplify goal
  simp only [Exp.subst, Subst.from_TypeEnv, Var.subst, List.empty_eq]
  -- The reachability stored with the reader gives the needed .ro capability
  have hreach :
    reachability_of_loc store.heap (env.lookup_var x).1 = CapabilitySet.singleton .ro y := by
    have heq := reachability_of_loc_eq_resolve_reachability store (env.lookup_var x).1
      ⟨Exp.reader (.free y), hval_reader, R⟩ hlookup_reader
    simpa [resolve_reachability] using heq
  have hcov :
      CapabilitySet.covers (.access .ro) y
        (((CaptureSet.var .epsilon (Var.bound x)).subst (Subst.from_TypeEnv env)).ground_denot
          store) := by
    have hden :
        (((CaptureSet.var .epsilon (Var.bound x)).subst (Subst.from_TypeEnv env)).ground_denot
          store) = CapabilitySet.singleton .ro y := by
      simp only [CaptureSet.subst, Var.subst, Subst.from_TypeEnv, CaptureSet.ground_denot,
            CapabilitySet.applyMut, hreach]
    simpa [hden] using (CapabilitySet.covers.here (l:=y) CapMode.Le.refl)
  -- Use hcompat to derive that the cell at y is live.
  have hlive : ℓ0 = .live := by
    have hbudget_denot :
        ((CaptureSet.var .epsilon (Var.bound x)).denot env store) =
          CapabilitySet.singleton .ro y := by
      simp only [CaptureSet.denot, CaptureSet.subst, Var.subst, Subst.from_TypeEnv,
        CaptureSet.ground_denot, CapabilitySet.applyMut, hreach]
    have hcompat' : store.is_compatible (CapabilitySet.singleton .ro y) :=
      hbudget_denot ▸ hcompat
    exact hcompat' (.access .ro) y b0 ℓ0 CapabilitySet.hasmem.here hlookup_cell
  subst hlive
  have hlookup_reader' :
      store.lookup (env.lookup_var x).1 =
        some (Cell.val ⟨Exp.reader (.free y), hval_reader, R⟩) := by
    simpa [Memory.lookup] using hlookup_reader
  have hlookup_cell' : store.lookup y = some (.capability (.mcell b0 .live)) := by
    simpa [Memory.lookup] using hlookup_cell
  have huse_eq :
      ((CaptureSet.var .epsilon (.bound x)).denot env store).intersect
          (Γ.useset.cs.denot env store)
        = (CaptureSet.var .epsilon (.bound x)).denot env store :=
    intersect_useset_eq_self_of_accessible hts hΓ
      CaptureSet.IsClosed.var_bound haccess
  -- Build the read at the narrower budget, then widen.
  suffices heval : Eval (((CaptureSet.var .epsilon (Var.bound x)).subst
                            (Subst.from_TypeEnv env)).ground_denot store) store
      (Exp.read (Var.free (env.lookup_var x).1))
      (fun v m' => Ty.exi_val_denot env Ty.bool.typ m' v) by
    apply eval_capability_set_monotonic heval
    change (CaptureSet.var .epsilon (.bound x)).denot env store ⊆
      ((CaptureSet.var .epsilon (.bound x)).denot env store).intersect
          (Γ.useset.cs.denot env store)
        ∪ (Γ.consumeset.cs.denot env store).to_drop
    rw [huse_eq]
    exact CapabilitySet.Subset.union_right_left
  apply Eval.eval_read hcov hlookup_reader' hlookup_cell'
  simp only [Ty.exi_val_denot, Ty.val_denot, resolve]
  cases b0 <;> simp

theorem sem_typ_write
  {x y : BVar s .var}
  (hΓ : Γ.IsClosed)
  (haccess : (CaptureSet.var .epsilon (.bound x)).accessible Γ)
  (hx : {} # Γ ⊨ Exp.var (.bound x) : .typ (.cell Cx))
  (hy : {} # Γ ⊨ Exp.var (.bound y) : .typ .bool) :
  (.var .epsilon (.bound x)) # Γ ⊨
    Exp.write (.bound x) (.bound y) : .typ .unit := by
  intro env store hts hcompat
  -- Extract cell denotation from hx
  have h1 := semtyp_to_exi_exp_denot hx hts (Memory.is_compatible_empty store)
  simp only [List.empty_eq] at h1
  have h1' := var_exp_denot_inv h1
  simp only [Ty.exi_val_denot] at h1'
  -- Extract the cell structure
  have ⟨fx, b0, ℓ0, hfx, hlk_cell, hmem_cell⟩ := cell_val_denot_inv h1'
  -- Extract bool denotation from hy
  have h2 := semtyp_to_exi_exp_denot hy hts (Memory.is_compatible_empty store)
  simp only [List.empty_eq] at h2
  have h2' := var_exp_denot_inv h2
  simp only [Ty.exi_val_denot] at h2'
  -- Extract the bool structure
  have ⟨fy, b, hval, R, hfy, hlk_bool⟩ := bool_val_denot_inv h2'
  -- Determine concrete locations
  have : fx = (env.lookup_var x).1 := by cases hfx; rfl
  subst this
  have : fy = (env.lookup_var y).1 := by cases hfy; rfl
  subst this
  -- Simplify goal
  simp only [Exp.subst, Subst.from_TypeEnv, Var.subst, List.empty_eq]
  -- Prove covers: env.lookup_var x is covered by the denotation of the write's capture set
  have hcov :
    (((CaptureSet.var .epsilon (Var.bound x)).subst
      (Subst.from_TypeEnv env)).ground_denot store).covers (.access .epsilon)
        (env.lookup_var x).1 := by
    simp only [CaptureSet.subst, Var.subst, Subst.from_TypeEnv, CaptureSet.ground_denot,
          CapabilitySet.applyMut, reachability_of_loc, hlk_cell, CapabilitySet.singleton]
    exact CapabilitySet.covers.here CapMode.Le.refl
  -- Use hcompat to derive that the cell at env.lookup_var x is live.
  have hlive : ℓ0 = .live := by
    have hbudget_denot :
      ((CaptureSet.var .epsilon (Var.bound x)).denot env store) =
        CapabilitySet.singleton .epsilon (env.lookup_var x).1 := by
      simp only [CaptureSet.denot, CaptureSet.subst, Var.subst, Subst.from_TypeEnv,
        CaptureSet.ground_denot, CapabilitySet.applyMut, reachability_of_loc, hlk_cell]
    have hcompat' : store.is_compatible (CapabilitySet.singleton .epsilon (env.lookup_var x).1) :=
      hbudget_denot ▸ hcompat
    exact hcompat' (.access .epsilon) (env.lookup_var x).1 b0 ℓ0
      CapabilitySet.hasmem.here hlk_cell
  subst hlive
  have huse_eq :
      ((CaptureSet.var .epsilon (.bound x)).denot env store).intersect
          (Γ.useset.cs.denot env store)
        = (CaptureSet.var .epsilon (.bound x)).denot env store :=
    intersect_useset_eq_self_of_accessible hts hΓ
      CaptureSet.IsClosed.var_bound haccess
  -- Build the write at the narrower budget, then widen.
  suffices heval : Eval (((CaptureSet.var .epsilon (Var.bound x)).subst
                            (Subst.from_TypeEnv env)).ground_denot store) store
      (Exp.write (Var.free (env.lookup_var x).1) (Var.free (env.lookup_var y).1))
      (fun v m' => Ty.exi_val_denot env Ty.unit.typ m' v) by
    apply eval_capability_set_monotonic heval
    change (CaptureSet.var .epsilon (.bound x)).denot env store ⊆
      ((CaptureSet.var .epsilon (.bound x)).denot env store).intersect
          (Γ.useset.cs.denot env store)
        ∪ (Γ.consumeset.cs.denot env store).to_drop
    rw [huse_eq]
    exact CapabilitySet.Subset.union_right_left
  cases b
  · apply Eval.eval_write_false hcov (hx := hlk_cell) hlk_bool
    simp only [Ty.exi_val_denot, Ty.val_denot, resolve]
  · apply Eval.eval_write_true hcov (hx := hlk_cell) hlk_bool
    simp only [Ty.exi_val_denot, Ty.val_denot, resolve]

/-- `EnvTyping` is preserved by `Ctx.SeqComp` from `Γ` to `Γ1`. Since the
cvar-clause of `EnvTyping` ignores the use mode (mode-agnostic semantic model),
an env that types `Γ` also types `Γ1`. -/
theorem EnvTyping.seqcomp_left
    {Γ1 Γ2 Γ : Ctx s} {env : TypeEnv s} {m : Memory}
    (h : Ctx.SeqComp Γ1 Γ2 Γ) (he : EnvTyping Γ env m) :
    EnvTyping Γ1 env m := by
  induction h with
  | empty => exact he
  | push_var hseq ih =>
    cases env with
    | extend env' info =>
      cases info with
      | var n ps =>
        simp only [EnvTyping] at he ⊢
        obtain ⟨h1, h2, h3⟩ := he
        refine ⟨h1, ?_, ih h3⟩
        rw [h2]
        exact CaptureSet.peakset_seqcomp_eq hseq _
  | push_tvar hseq ih =>
    cases env with
    | extend env' info =>
      cases info with
      | tvar denot =>
        simp only [EnvTyping] at he ⊢
        obtain ⟨h1, h2, h3, h4, h5, h6⟩ := he
        exact ⟨h1, h2, h3, h4, h5, ih h6⟩
  | push_cvar hseq _ ih =>
    cases env with
    | extend env' info =>
      cases info with
      | cvar cs cap =>
        simp only [EnvTyping] at he ⊢
        obtain ⟨h1, h2, h3, h4, h5⟩ := he
        exact ⟨h1, h2, h3, h4, ih h5⟩
  | lock => exact he

/-- Symmetric version: `EnvTyping` is preserved by `Ctx.SeqComp` from `Γ` to `Γ2`. -/
theorem EnvTyping.seqcomp_right
    {Γ1 Γ2 Γ : Ctx s} {env : TypeEnv s} {m : Memory}
    (h : Ctx.SeqComp Γ1 Γ2 Γ) (he : EnvTyping Γ env m) :
    EnvTyping Γ2 env m := by
  induction h with
  | empty => exact he
  | push_var hseq ih =>
    cases env with
    | extend env' info =>
      cases info with
      | var n ps =>
        simp only [EnvTyping] at he ⊢
        obtain ⟨h1, h2, h3⟩ := he
        refine ⟨h1, ?_, ih h3⟩
        rw [h2]
        exact CaptureSet.peakset_seqcomp_eq_right hseq _
  | push_tvar hseq ih =>
    cases env with
    | extend env' info =>
      cases info with
      | tvar denot =>
        simp only [EnvTyping] at he ⊢
        obtain ⟨h1, h2, h3, h4, h5, h6⟩ := he
        exact ⟨h1, h2, h3, h4, h5, ih h6⟩
  | push_cvar hseq _ ih =>
    cases env with
    | extend env' info =>
      cases info with
      | cvar cs cap =>
        simp only [EnvTyping] at he ⊢
        obtain ⟨h1, h2, h3, h4, h5⟩ := he
        exact ⟨h1, h2, h3, h4, ih h5⟩
  | lock => exact he

/-- `CaptureSet.Subset` lifts to a `CapabilitySet.Subset` on denotations,
independently of any context (the env merely determines what each cvar
denotes pointwise). -/
private theorem captureset_denot_subset_of_subset
    {s : Sig} {C1 C2 : CaptureSet s} (hsub : C1 ⊆ C2)
    (env : TypeEnv s) (m : Memory) :
    C1.denot env m ⊆ C2.denot env m := by
  unfold CaptureSet.denot
  induction hsub with
  | empty => exact CapabilitySet.Subset.empty
  | refl => exact CapabilitySet.Subset.refl
  | union_left _ _ ih1 ih2 => exact CapabilitySet.Subset.union_left ih1 ih2
  | union_right_left _ ih =>
    exact CapabilitySet.Subset.trans ih CapabilitySet.Subset.union_right_left
  | union_right_right _ ih =>
    exact CapabilitySet.Subset.trans ih CapabilitySet.Subset.union_right_right

/-- `to_drop` is monotone in `Subset`: it rewrites every cap mode to `.drop`
without touching locations or the structure of unions/caps. -/
private theorem CapabilitySet.Subset.to_drop_mono {A B : CapabilitySet}
    (h : A ⊆ B) : A.to_drop ⊆ B.to_drop := by
  induction h with
  | refl => exact CapabilitySet.Subset.refl
  | empty => exact CapabilitySet.Subset.empty
  | trans _ _ ih12 ih23 => exact CapabilitySet.Subset.trans ih12 ih23
  | union_left _ _ ih1 ih2 => exact CapabilitySet.Subset.union_left ih1 ih2
  | union_right_left => exact CapabilitySet.Subset.union_right_left
  | union_right_right => exact CapabilitySet.Subset.union_right_right
  | cap_ro =>
    -- `(cap (.access .ro) l).to_drop = cap .drop l = (cap (.access .epsilon) l).to_drop`.
    exact CapabilitySet.Subset.refl

/-- The consumeset of `Γ1` is a syntactic sub–capture-set of the composed
context `Γ`'s consumeset: `Ctx.SeqComp` rules force every `.consume`-unlocked
cvar in `Γ1` to also be `.consume`-unlocked in `Γ`. -/
private theorem consumeset_subset_seqcomp_left
    {s : Sig} {Γ1 Γ2 Γ : Ctx s}
    (h : Ctx.SeqComp Γ1 Γ2 Γ) :
    Γ1.consumeset.cs ⊆ Γ.consumeset.cs := by
  induction Γ with
  | empty =>
    cases h
    exact CaptureSet.Subset.refl
  | push Γ_inner b ih =>
    cases b with
    | var _ =>
      cases h with
      | push_var h' => exact CaptureSet.Subset.rename' (ih h')
    | tvar _ =>
      cases h with
      | push_tvar h' => exact CaptureSet.Subset.rename' (ih h')
    | cvar m _ =>
      cases h with
      | push_cvar h' mode_comp =>
        cases m with
        | empty =>
          -- m3 = .empty: only `l_empty (R := .empty)` or `r_empty (R := .empty)` fire,
          -- both forcing m1 = .empty. LHS and RHS are both `.rename succ`.
          cases mode_comp <;>
            exact CaptureSet.Subset.rename' (ih h')
        | access =>
          -- m3 = .access: l_empty/r_empty give m1 ∈ {.empty/.access}; access_access gives .access.
          -- All three: LHS and RHS are both `.rename succ`.
          cases mode_comp <;>
            exact CaptureSet.Subset.rename' (ih h')
        | consume =>
          -- m3 = .consume: l_empty gives m1 = .empty; r_empty gives m1 = .consume;
          -- access_consume gives m1 = .access.
          cases mode_comp with
          | l_empty =>
            exact CaptureSet.Subset.union_right_left
              (CaptureSet.Subset.rename' (ih h'))
          | r_empty =>
            -- Both sides have `union (...rename) (.cvar .epsilon .here)`.
            exact CaptureSet.Subset.union_left
              (CaptureSet.Subset.union_right_left
                (CaptureSet.Subset.rename' (ih h')))
              (CaptureSet.Subset.union_right_right CaptureSet.Subset.refl)
          | access_consume =>
            exact CaptureSet.Subset.union_right_left
              (CaptureSet.Subset.rename' (ih h'))
  | lock Γ_inner _ =>
    cases h with
    | lock =>
      -- Both `(Γ_inner.lock).consumeset.cs` reduce to `.empty`.
      exact CaptureSet.Subset.refl

/-- Symmetric to `consumeset_subset_seqcomp_left`: `Γ2.consumeset.cs ⊆ Γ.consumeset.cs`. -/
private theorem consumeset_subset_seqcomp_right
    {s : Sig} {Γ1 Γ2 Γ : Ctx s}
    (h : Ctx.SeqComp Γ1 Γ2 Γ) :
    Γ2.consumeset.cs ⊆ Γ.consumeset.cs := by
  induction Γ with
  | empty =>
    cases h
    exact CaptureSet.Subset.refl
  | push Γ_inner b ih =>
    cases b with
    | var _ =>
      cases h with
      | push_var h' => exact CaptureSet.Subset.rename' (ih h')
    | tvar _ =>
      cases h with
      | push_tvar h' => exact CaptureSet.Subset.rename' (ih h')
    | cvar m _ =>
      cases h with
      | push_cvar h' mode_comp =>
        cases m with
        | empty =>
          cases mode_comp <;>
            exact CaptureSet.Subset.rename' (ih h')
        | access =>
          cases mode_comp <;>
            exact CaptureSet.Subset.rename' (ih h')
        | consume =>
          cases mode_comp with
          | l_empty =>
            -- m2 = .consume, both sides have union.
            exact CaptureSet.Subset.union_left
              (CaptureSet.Subset.union_right_left
                (CaptureSet.Subset.rename' (ih h')))
              (CaptureSet.Subset.union_right_right CaptureSet.Subset.refl)
          | r_empty =>
            -- m2 = .empty
            exact CaptureSet.Subset.union_right_left
              (CaptureSet.Subset.rename' (ih h'))
          | access_consume =>
            -- m2 = .consume
            exact CaptureSet.Subset.union_left
              (CaptureSet.Subset.union_right_left
                (CaptureSet.Subset.rename' (ih h')))
              (CaptureSet.Subset.union_right_right CaptureSet.Subset.refl)
  | lock Γ_inner _ =>
    cases h with
    | lock => exact CaptureSet.Subset.refl

/-- The consumeset is built from `.empty`, `.union`, and `.cvar`/rename — never
free variables — so it is always `IsClosed`. -/
private theorem consumeset_isClosed {s : Sig} (Γ : Ctx s) :
    Γ.consumeset.cs.IsClosed := by
  induction Γ with
  | empty => exact CaptureSet.IsClosed.empty
  | push Γ' b ih =>
    cases b with
    | var _ => exact CaptureSet.rename_isClosed ih
    | tvar _ => exact CaptureSet.rename_isClosed ih
    | cvar useM _ =>
      cases useM with
      | access => exact CaptureSet.rename_isClosed ih
      | empty => exact CaptureSet.rename_isClosed ih
      | consume =>
        exact CaptureSet.IsClosed.union (CaptureSet.rename_isClosed ih)
          CaptureSet.IsClosed.cvar
  | lock _ _ => exact CaptureSet.IsClosed.empty

/-- The accessset includes only `.access` peaks (locks transparent). It is
    `IsClosed` for the same structural reason as consumeset. -/
private theorem accessset_isClosed {s : Sig} (Γ : Ctx s) :
    Γ.accessset.cs.IsClosed := by
  induction Γ with
  | empty => exact CaptureSet.IsClosed.empty
  | push Γ' b ih =>
    cases b with
    | var _ => exact CaptureSet.rename_isClosed ih
    | tvar _ => exact CaptureSet.rename_isClosed ih
    | cvar useM _ =>
      cases useM with
      | empty => exact CaptureSet.rename_isClosed ih
      | access =>
        exact CaptureSet.IsClosed.union (CaptureSet.rename_isClosed ih)
          CaptureSet.IsClosed.cvar
      | consume => exact CaptureSet.rename_isClosed ih
  | lock _ ih => exact ih

/-- `useset.cs.IsClosed` follows from `accessset.cs.IsClosed` and
    `consumeset.cs.IsClosed`, since `useset.cs` is their union. -/
private theorem useset_isClosed {s : Sig} (Γ : Ctx s) :
    Γ.useset.cs.IsClosed :=
  CaptureSet.IsClosed.union (accessset_isClosed Γ) (consumeset_isClosed Γ)

/-- Pushing a cvar onto `Γ_inner` only adds to its `useset.cs` (the renamed
inner useset always embeds into the pushed useset). -/
private theorem useset_push_cvar_widen
    {s : Sig} (Γ_inner : Ctx s) (m : UseMode) (B : CaptureBound s) :
    (Γ_inner.useset.cs).rename (Rename.succ (k := .cvar)) ⊆
      (Γ_inner.push (.cvar m B)).useset.cs := by
  cases m with
  | empty => exact CaptureSet.Subset.refl
  | access =>
    apply CaptureSet.Subset.union_left
    · exact .union_right_left (.union_right_left .refl)
    · exact .union_right_right .refl
  | consume =>
    apply CaptureSet.Subset.union_left
    · exact .union_right_left .refl
    · exact .union_right_right (.union_right_left .refl)

/-- A `Subset` on a union decomposes into subsets on each side. -/
private theorem CaptureSet.Subset.union_split
    {s : Sig} {C1 C2 C : CaptureSet s}
    (h : C1.union C2 ⊆ C) : C1 ⊆ C ∧ C2 ⊆ C := by
  generalize hCU : C1.union C2 = CU at h
  induction h generalizing C1 C2 with
  | refl =>
    subst hCU
    exact ⟨.union_right_left .refl, .union_right_right .refl⟩
  | empty => cases hCU
  | union_left h1 h2 _ _ =>
    cases hCU
    exact ⟨h1, h2⟩
  | union_right_left _ ih =>
    obtain ⟨hC1, hC2⟩ := ih hCU
    exact ⟨.union_right_left hC1, .union_right_left hC2⟩
  | union_right_right _ ih =>
    obtain ⟨hC1, hC2⟩ := ih hCU
    exact ⟨.union_right_right hC1, .union_right_right hC2⟩

/-- Transitivity for `CaptureSet.Subset`, derived from `union_split`. -/
private theorem CaptureSet.Subset.trans
    {s : Sig} {C1 C2 C3 : CaptureSet s}
    (h12 : C1 ⊆ C2) (h23 : C2 ⊆ C3) : C1 ⊆ C3 := by
  induction h12 generalizing C3 with
  | refl => exact h23
  | empty => exact .empty
  | union_left _ _ ih1 ih2 => exact .union_left (ih1 h23) (ih2 h23)
  | union_right_left _ ih =>
    obtain ⟨hLeft, _⟩ := CaptureSet.Subset.union_split h23
    exact ih hLeft
  | union_right_right _ ih =>
    obtain ⟨_, hRight⟩ := CaptureSet.Subset.union_split h23
    exact ih hRight

/-- `Γ1.useset.cs ⊆ Γ.useset.cs` under `SeqComp Γ1 Γ2 Γ`. Holds for all
    cases: var/tvar pushes propagate the inner subset through `rename succ`;
    cvar pushes are handled per use-mode (with `access_consume` working because
    the cvar contributes to `Γ1.accessset` and `Γ.consumeset`, both feeding
    `useset`); the restricted `SeqComp.lock` rule forces `Γ1 = Γ` so the lock
    case is reflexive. -/
private theorem useset_subset_seqcomp_left
    {s : Sig} {Γ1 Γ2 Γ : Ctx s}
    (h : Ctx.SeqComp Γ1 Γ2 Γ) :
    Γ1.useset.cs ⊆ Γ.useset.cs := by
  induction Γ with
  | empty =>
    cases h
    exact CaptureSet.Subset.refl
  | push Γ_inner b ih =>
    cases b with
    | var _ =>
      cases h with
      | push_var h' =>
        exact CaptureSet.Subset.rename' (ih h')
    | tvar _ =>
      cases h with
      | push_tvar h' =>
        exact CaptureSet.Subset.rename' (ih h')
    | cvar m B =>
      cases h with
      | push_cvar h' mode_comp =>
        have hih := ih h'
        obtain ⟨hA1, hC1⟩ := CaptureSet.Subset.union_split hih
        have hA1_r := CaptureSet.Subset.rename' (f := Rename.succ (k := .cvar)) hA1
        have hC1_r := CaptureSet.Subset.rename' (f := Rename.succ (k := .cvar)) hC1
        -- hA1_r : (Γ1_inner.accessset.cs).rename succ ⊆ (Γ_inner.useset.cs).rename succ
        -- hC1_r : (Γ1_inner.consumeset.cs).rename succ ⊆ (Γ_inner.useset.cs).rename succ
        -- (Γ_inner.useset.cs).rename succ = Γ_inner.accessset.cs.rename succ ∪
        --                                   Γ_inner.consumeset.cs.rename succ (def. eq.)
        -- Build the further embedding to (push m3 B).useset.cs via union_left on
        -- the renamed useset, then mode-specific union_right_*.
        -- Bridge G via the helper: useset_inner.rename succ ⊆ (push m B).useset.cs.
        have G := useset_push_cvar_widen Γ_inner m B
        cases m with
        | empty =>
          cases mode_comp with
          | l_empty => exact CaptureSet.Subset.rename' hih
          | r_empty => exact CaptureSet.Subset.rename' hih
        | access =>
          cases mode_comp with
          | l_empty =>
            -- m1 = .empty. LHS = acc1.r ∪ cons1.r (= useset_inner1.rename).
            apply CaptureSet.Subset.union_left
            · exact CaptureSet.Subset.trans hA1_r G
            · exact CaptureSet.Subset.trans hC1_r G
          | r_empty =>
            -- m1 = .access. LHS = (acc1.r ∪ cvar.here) ∪ cons1.r.
            apply CaptureSet.Subset.union_left
            · apply CaptureSet.Subset.union_left
              · exact CaptureSet.Subset.trans hA1_r G
              · exact .union_right_left (.union_right_right .refl)
            · exact CaptureSet.Subset.trans hC1_r G
          | access_access =>
            apply CaptureSet.Subset.union_left
            · apply CaptureSet.Subset.union_left
              · exact CaptureSet.Subset.trans hA1_r G
              · exact .union_right_left (.union_right_right .refl)
            · exact CaptureSet.Subset.trans hC1_r G
        | consume =>
          cases mode_comp with
          | l_empty =>
            apply CaptureSet.Subset.union_left
            · exact CaptureSet.Subset.trans hA1_r G
            · exact CaptureSet.Subset.trans hC1_r G
          | r_empty =>
            -- m1 = .consume. LHS = acc1.r ∪ (cons1.r ∪ cvar.here).
            apply CaptureSet.Subset.union_left
            · exact CaptureSet.Subset.trans hA1_r G
            · apply CaptureSet.Subset.union_left
              · exact CaptureSet.Subset.trans hC1_r G
              · exact .union_right_right (.union_right_right .refl)
          | access_consume =>
            -- m1 = .access, m3 = .consume.
            apply CaptureSet.Subset.union_left
            · apply CaptureSet.Subset.union_left
              · exact CaptureSet.Subset.trans hA1_r G
              · exact .union_right_right (.union_right_right .refl)
            · exact CaptureSet.Subset.trans hC1_r G
  | lock Γ_inner _ =>
    cases h with
    | lock => exact CaptureSet.Subset.refl

/-- Symmetric: `Γ2.useset.cs ⊆ Γ.useset.cs`. -/
private theorem useset_subset_seqcomp_right
    {s : Sig} {Γ1 Γ2 Γ : Ctx s}
    (h : Ctx.SeqComp Γ1 Γ2 Γ) :
    Γ2.useset.cs ⊆ Γ.useset.cs := by
  induction Γ with
  | empty =>
    cases h
    exact CaptureSet.Subset.refl
  | push Γ_inner b ih =>
    cases b with
    | var _ =>
      cases h with
      | push_var h' =>
        exact CaptureSet.Subset.rename' (ih h')
    | tvar _ =>
      cases h with
      | push_tvar h' =>
        exact CaptureSet.Subset.rename' (ih h')
    | cvar m B =>
      cases h with
      | push_cvar h' mode_comp =>
        have hih := ih h'
        obtain ⟨hA2, hC2⟩ := CaptureSet.Subset.union_split hih
        have hA2_r := CaptureSet.Subset.rename' (f := Rename.succ (k := .cvar)) hA2
        have hC2_r := CaptureSet.Subset.rename' (f := Rename.succ (k := .cvar)) hC2
        have G := useset_push_cvar_widen Γ_inner m B
        cases m with
        | empty =>
          -- m3 = .empty. Then m2 = .empty (from l_empty/r_empty).
          cases mode_comp with
          | l_empty => exact CaptureSet.Subset.rename' hih
          | r_empty => exact CaptureSet.Subset.rename' hih
        | access =>
          cases mode_comp with
          | l_empty =>
            -- m2 = .access. LHS = (acc2.r ∪ cvar.here) ∪ cons2.r.
            apply CaptureSet.Subset.union_left
            · apply CaptureSet.Subset.union_left
              · exact CaptureSet.Subset.trans hA2_r G
              · exact .union_right_left (.union_right_right .refl)
            · exact CaptureSet.Subset.trans hC2_r G
          | r_empty =>
            -- m2 = .empty. LHS = acc2.r ∪ cons2.r.
            apply CaptureSet.Subset.union_left
            · exact CaptureSet.Subset.trans hA2_r G
            · exact CaptureSet.Subset.trans hC2_r G
          | access_access =>
            -- m2 = .access.
            apply CaptureSet.Subset.union_left
            · apply CaptureSet.Subset.union_left
              · exact CaptureSet.Subset.trans hA2_r G
              · exact .union_right_left (.union_right_right .refl)
            · exact CaptureSet.Subset.trans hC2_r G
        | consume =>
          cases mode_comp with
          | l_empty =>
            -- m2 = .consume. LHS = acc2.r ∪ (cons2.r ∪ cvar.here).
            apply CaptureSet.Subset.union_left
            · exact CaptureSet.Subset.trans hA2_r G
            · apply CaptureSet.Subset.union_left
              · exact CaptureSet.Subset.trans hC2_r G
              · exact .union_right_right (.union_right_right .refl)
          | r_empty =>
            -- m2 = .empty.
            apply CaptureSet.Subset.union_left
            · exact CaptureSet.Subset.trans hA2_r G
            · exact CaptureSet.Subset.trans hC2_r G
          | access_consume =>
            -- m2 = .consume.
            apply CaptureSet.Subset.union_left
            · exact CaptureSet.Subset.trans hA2_r G
            · apply CaptureSet.Subset.union_left
              · exact CaptureSet.Subset.trans hC2_r G
              · exact .union_right_right (.union_right_right .refl)
  | lock Γ_inner _ =>
    cases h with
    | lock => exact CaptureSet.Subset.refl

theorem sem_typ_letin
  {C1 C2 : CaptureSet s} {Γ Γ1 Γ2 : Ctx s} {e1 : Exp s} {T : Ty .capt s}
  {e2 : Exp (s,,Kind.var)} {U : Ty .exi s}
  (hseq : Ctx.SeqComp Γ1 Γ2 Γ)
  (_hclosed_C1 : C1.IsClosed)
  (hclosed_C2 : C2.IsClosed)
  (_hclosed_e : (Exp.letin e1 e2).IsClosed)
  (ht1 : C1 # Γ1 ⊨ e1 : .typ T)
  (ht2 : C2.rename Rename.succ # (Γ2,x:T) ⊨ e2 : U.rename Rename.succ) :
  C1 ∪ C2 # Γ ⊨ (Exp.letin e1 e2) : U := by
  intro env store hts hcompat
  have hts1 := EnvTyping.seqcomp_left hseq hts
  have hts2 := EnvTyping.seqcomp_right hseq hts
  simp only [Exp.subst]
  -- Definitional decomposition of the union budget.
  have hunion_denot :
      (C1 ∪ C2).denot env store
        = C1.denot env store ∪ C2.denot env store := rfl
  -- Drop-authority piece of the outer budget.
  let D : CapabilitySet := (Γ.consumeset.cs.denot env store).to_drop
  -- SeqComp lifts: `Γi.consumeset.cs ⊆ Γ.consumeset.cs`, hence `to_drop ⊆ D`.
  have hsub1_drop :
      (Γ1.consumeset.cs.denot env store).to_drop ⊆ D :=
    CapabilitySet.Subset.to_drop_mono
      (captureset_denot_subset_of_subset
        (consumeset_subset_seqcomp_left hseq) env store)
  have hsub2_drop :
      (Γ2.consumeset.cs.denot env store).to_drop ⊆ D :=
    CapabilitySet.Subset.to_drop_mono
      (captureset_denot_subset_of_subset
        (consumeset_subset_seqcomp_right hseq) env store)
  have hΓ2_closed : Γ2.consumeset.cs.IsClosed := consumeset_isClosed Γ2
  apply Eval.eval_letin (Q1 := fun v m' => Ty.val_denot env T m' v)
  case hpred =>
    intro m1 m2 e hwf hsub hQ
    exact val_denot_is_monotonic (typed_env_is_monotonic hts) T hsub hQ
  case hbool =>
    intro m'
    exact val_denot_is_bool_independent (typed_env_is_bool_independent hts) T
  case a =>
    -- ht1 gives `Eval (intersect C1.denot Γ1.accessset ∪ Γ1.consumeset.to_drop) store e1 _`.
    -- `Ty.exi_val_denot env T.typ = Ty.val_denot env T` by pattern matching.
    have hcompat_C1 : store.is_compatible (C1.denot env store) :=
      Memory.is_compatible_union_left hcompat
    have h1 := ht1 env store hts1 hcompat_C1
    simp only [Ty.exi_val_denot] at h1
    apply eval_capability_set_monotonic h1
    -- With the refactored `accessset` (now including `.consume` peaks),
    -- `Γ1.accessset.cs ⊆ Γ.accessset.cs` under `SeqComp`. Use this with
    -- `intersect_mono_right` to widen the inner use-set into the outer one.
    apply CapabilitySet.Subset.union_left
    · -- intersect C1.denot Γ1.access ⊆ intersect (C1∪C2).denot Γ.access
      have hacc_sub : Γ1.useset.cs.denot env store ⊆ Γ.useset.cs.denot env store :=
        captureset_denot_subset_of_subset (useset_subset_seqcomp_left hseq) env store
      have h_right :
          (C1.denot env store).intersect (Γ1.useset.cs.denot env store)
            ⊆ (C1.denot env store).intersect (Γ.useset.cs.denot env store) :=
        CapabilitySet.intersect_mono_right hacc_sub
      have h_left :
          (C1.denot env store).intersect (Γ.useset.cs.denot env store)
            ⊆ ((C1 ∪ C2).denot env store).intersect (Γ.useset.cs.denot env store) := by
        rw [hunion_denot]
        change (C1.denot env store).intersect (Γ.useset.cs.denot env store) ⊆
          (C1.denot env store).intersect (Γ.useset.cs.denot env store) ∪
            (C2.denot env store).intersect (Γ.useset.cs.denot env store)
        exact CapabilitySet.Subset.union_right_left
      exact CapabilitySet.Subset.trans
        (CapabilitySet.Subset.trans h_right h_left)
        CapabilitySet.Subset.union_right_left
    · -- Γ1.consumeset.to_drop ⊆ D ⊆ ... ∪ D
      exact CapabilitySet.Subset.trans hsub1_drop CapabilitySet.Subset.union_right_right
  case h_nonstuck =>
    intro m1 v hQ1
    constructor
    · exact val_denot_implies_simple_ans (typed_env_is_implying_simple_ans hts) T m1 v hQ1
    · exact val_denot_implies_wf (typed_env_is_implying_wf hts) T m1 v hQ1
  case h_val =>
    intro m1 v hs1 hv hwf_v hQ1 l' hfresh
    let heapval : HeapVal := ⟨v, hv, compute_reachability m1.heap v hv⟩
    let ps := CaptureSet.peakset Γ2 T.captureSet
    set m_ext := m1.extend_val l' heapval hwf_v rfl hfresh with hm_ext_def
    have hext_subsumes : m_ext.subsumes m1 :=
      Memory.extend_val_subsumes m1 l' heapval hwf_v rfl hfresh
    have hsub_full : m_ext.subsumes store := Memory.subsumes_trans hext_subsumes hs1
    -- Body EnvTyping for `(Γ2, x:T)` at the extended env / extended memory.
    have henv_body : EnvTyping (Γ2,x:T) (env.extend_var l' ps) m_ext := by
      constructor
      · have htrans : (Ty.val_denot env T).is_transparent :=
          val_denot_is_transparent (typed_env_is_transparent hts) T
        have hQ1_lifted : Ty.val_denot env T m_ext v :=
          val_denot_is_monotonic (typed_env_is_monotonic hts) T hext_subsumes hQ1
        have hlookup : m_ext.lookup l' = some (Cell.val heapval) := by
          change (m1.heap.extend l' heapval) l' = some (.val heapval)
          exact Heap.extend_lookup_eq m1.heap l' heapval
        exact htrans hlookup hQ1_lifted
      · constructor
        · rfl
        · exact env_typing_monotonic hts2 hsub_full
    -- Rebind C2 and Γ2.consumeset.cs into the extended env.
    have hcap_rename_C2 :
        (C2.rename Rename.succ).denot (env.extend_var l' ps) = C2.denot env := by
      have := rebind_captureset_denot
        (Rebind.weaken (env := env) (x := l') (ps := ps)) C2
      exact this.symm
    have hcap_rename_consumeset :
        (Γ2,x:T).consumeset.cs.denot (env.extend_var l' ps) = Γ2.consumeset.cs.denot env := by
      have := rebind_captureset_denot
        (Rebind.weaken (env := env) (x := l') (ps := ps)) Γ2.consumeset.cs
      exact this.symm
    -- Memory-monotonicity on closed capture sets.
    have hC2_mono : C2.denot env store = C2.denot env m_ext :=
      closed_capture_denot_monotonic hclosed_C2 hts hsub_full
    have hconsumeset_mono :
        Γ2.consumeset.cs.denot env store = Γ2.consumeset.cs.denot env m_ext :=
      closed_capture_denot_monotonic hΓ2_closed hts hsub_full
    -- Body budget ⊆ outer budget.
    have hsub_body :
        (C2.rename Rename.succ).denot (env.extend_var l' ps) m_ext
          ∪ ((Γ2,x:T).consumeset.cs.denot (env.extend_var l' ps) m_ext).to_drop
            ⊆ (C1 ∪ C2).denot env store ∪ D := by
      rw [congrFun hcap_rename_C2 m_ext, congrFun hcap_rename_consumeset m_ext,
          ← hC2_mono, ← hconsumeset_mono]
      apply CapabilitySet.Subset.union_left
      · rw [hunion_denot]
        exact CapabilitySet.Subset.trans
          CapabilitySet.Subset.union_right_right
          CapabilitySet.Subset.union_right_left
      · exact CapabilitySet.Subset.trans hsub2_drop CapabilitySet.Subset.union_right_right
    have hcompat_body :
        m_ext.is_compatible
          ((C2.rename Rename.succ).denot (env.extend_var l' ps) m_ext) := by
      sorry
    have h2 := ht2 (env.extend_var l' ps) m_ext henv_body hcompat_body
    -- Bridge the substitution shape: `e2.subst ... .lift then openVar l'`
    -- equals `e2.subst (from_TypeEnv (env.extend_var l' ps))`.
    have hkey := @Exp.from_TypeEnv_weaken_open s env l' e2 ps
    have h2' : Eval _ m_ext
        ((e2.subst (Subst.from_TypeEnv env).lift).subst (Subst.openVar (Var.free l')))
        _ := hkey ▸ h2
    -- With the refactored `accessset`, the body's inner use-set widens into
    -- the outer one via `useset_subset_seqcomp_right`.
    have hcap_rename_accessset :
        (Γ2,x:T).useset.cs.denot (env.extend_var l' ps) = Γ2.useset.cs.denot env := by
      have := rebind_captureset_denot
        (Rebind.weaken (env := env) (x := l') (ps := ps)) Γ2.useset.cs
      exact this.symm
    have hΓ2_use_closed : Γ2.useset.cs.IsClosed := useset_isClosed Γ2
    have haccessset_mono :
        Γ2.useset.cs.denot env store = Γ2.useset.cs.denot env m_ext :=
      closed_capture_denot_monotonic hΓ2_use_closed hts hsub_full
    have hsub_body_tight :
        ((C2.rename Rename.succ).denot (env.extend_var l' ps) m_ext).intersect
            ((Γ2,x:T).useset.cs.denot (env.extend_var l' ps) m_ext)
          ∪ ((Γ2,x:T).consumeset.cs.denot (env.extend_var l' ps) m_ext).to_drop ⊆
        ((C1 ∪ C2).denot env store).intersect (Γ.useset.cs.denot env store) ∪ D := by
      rw [congrFun hcap_rename_C2 m_ext, congrFun hcap_rename_accessset m_ext,
          congrFun hcap_rename_consumeset m_ext,
          ← hC2_mono, ← haccessset_mono, ← hconsumeset_mono]
      apply CapabilitySet.Subset.union_left
      · -- intersect C2.denot Γ2.useset ⊆ intersect (C1∪C2).denot Γ.useset
        have hacc_sub : Γ2.useset.cs.denot env store ⊆ Γ.useset.cs.denot env store :=
          captureset_denot_subset_of_subset (useset_subset_seqcomp_right hseq) env store
        have h_right :
            (C2.denot env store).intersect (Γ2.useset.cs.denot env store)
              ⊆ (C2.denot env store).intersect (Γ.useset.cs.denot env store) :=
          CapabilitySet.intersect_mono_right hacc_sub
        have h_left :
            (C2.denot env store).intersect (Γ.useset.cs.denot env store)
              ⊆ ((C1 ∪ C2).denot env store).intersect (Γ.useset.cs.denot env store) := by
          rw [hunion_denot]
          change (C2.denot env store).intersect (Γ.useset.cs.denot env store) ⊆
            (C1.denot env store).intersect (Γ.useset.cs.denot env store) ∪
              (C2.denot env store).intersect (Γ.useset.cs.denot env store)
          exact CapabilitySet.Subset.union_right_right
        exact CapabilitySet.Subset.trans
          (CapabilitySet.Subset.trans h_right h_left)
          CapabilitySet.Subset.union_right_left
      · exact CapabilitySet.Subset.trans hsub2_drop CapabilitySet.Subset.union_right_right
    have hcompose := eval_capability_set_monotonic h2' hsub_body_tight
    -- Lift post: `Ty.exi_val_denot env_ext (U.rename succ) ≈ Ty.exi_val_denot env U`.
    have heqv := weaken_exi_val_denot (env := env) (x := l') (ps := ps) (T := U)
    apply eval_post_monotonic _ hcompose
    exact Denot.imply_to_entails _ _ (Denot.equiv_to_imply heqv).2
  case h_var =>
    intro m1 x hs1 hwf_x hQ1
    cases x
    case bound bv => cases bv
    case free fx =>
      let ps := CaptureSet.peakset Γ2 T.captureSet
      have henv_body : EnvTyping (Γ2,x:T) (env.extend_var fx ps) m1 := by
        constructor
        · exact hQ1
        · constructor
          · rfl
          · exact env_typing_monotonic hts2 hs1
      have hcap_rename_C2 :
          (C2.rename Rename.succ).denot (env.extend_var fx ps) = C2.denot env := by
        have := rebind_captureset_denot
          (Rebind.weaken (env := env) (x := fx) (ps := ps)) C2
        exact this.symm
      have hcap_rename_consumeset :
          (Γ2,x:T).consumeset.cs.denot (env.extend_var fx ps) = Γ2.consumeset.cs.denot env := by
        have := rebind_captureset_denot
          (Rebind.weaken (env := env) (x := fx) (ps := ps)) Γ2.consumeset.cs
        exact this.symm
      have hC2_mono : C2.denot env store = C2.denot env m1 :=
        closed_capture_denot_monotonic hclosed_C2 hts hs1
      have hconsumeset_mono :
          Γ2.consumeset.cs.denot env store = Γ2.consumeset.cs.denot env m1 :=
        closed_capture_denot_monotonic hΓ2_closed hts hs1
      have hsub_body :
          (C2.rename Rename.succ).denot (env.extend_var fx ps) m1
            ∪ ((Γ2,x:T).consumeset.cs.denot (env.extend_var fx ps) m1).to_drop
              ⊆ (C1 ∪ C2).denot env store ∪ D := by
        rw [congrFun hcap_rename_C2 m1, congrFun hcap_rename_consumeset m1,
            ← hC2_mono, ← hconsumeset_mono]
        apply CapabilitySet.Subset.union_left
        · rw [hunion_denot]
          exact CapabilitySet.Subset.trans
            CapabilitySet.Subset.union_right_right
            CapabilitySet.Subset.union_right_left
        · exact CapabilitySet.Subset.trans hsub2_drop CapabilitySet.Subset.union_right_right
      -- Same gap as `h_val`: `hda : store.drops_authorized m1 (outer budget)`
      -- is now available, but closing requires disjointness of `C2.denot`
      -- and `Γ.consumeset.cs.denot`, which the typing rule does not
      -- currently enforce. See the comment in the `h_val` case above.
      have hcompat_body :
          m1.is_compatible
            ((C2.rename Rename.succ).denot (env.extend_var fx ps) m1) := by
        sorry
      have h2 := ht2 (env.extend_var fx ps) m1 henv_body hcompat_body
      have hkey := @Exp.from_TypeEnv_weaken_open s env fx e2 ps
      have h2' : Eval _ m1
          ((e2.subst (Subst.from_TypeEnv env).lift).subst (Subst.openVar (Var.free fx)))
          _ := hkey ▸ h2
      -- With the refactored `accessset`, the body's inner use-set widens into
      -- the outer one via `useset_subset_seqcomp_right`.
      have hcap_rename_accessset :
          (Γ2,x:T).useset.cs.denot (env.extend_var fx ps) = Γ2.useset.cs.denot env := by
        have := rebind_captureset_denot
          (Rebind.weaken (env := env) (x := fx) (ps := ps)) Γ2.useset.cs
        exact this.symm
      have hΓ2_use_closed : Γ2.useset.cs.IsClosed := useset_isClosed Γ2
      have haccessset_mono :
          Γ2.useset.cs.denot env store = Γ2.useset.cs.denot env m1 :=
        closed_capture_denot_monotonic hΓ2_use_closed hts hs1
      have hsub_body_tight :
          ((C2.rename Rename.succ).denot (env.extend_var fx ps) m1).intersect
              ((Γ2,x:T).useset.cs.denot (env.extend_var fx ps) m1)
            ∪ ((Γ2,x:T).consumeset.cs.denot (env.extend_var fx ps) m1).to_drop ⊆
          ((C1 ∪ C2).denot env store).intersect (Γ.useset.cs.denot env store) ∪ D := by
        rw [congrFun hcap_rename_C2 m1, congrFun hcap_rename_accessset m1,
            congrFun hcap_rename_consumeset m1,
            ← hC2_mono, ← haccessset_mono, ← hconsumeset_mono]
        apply CapabilitySet.Subset.union_left
        · have hacc_sub : Γ2.useset.cs.denot env store ⊆ Γ.useset.cs.denot env store :=
            captureset_denot_subset_of_subset (useset_subset_seqcomp_right hseq) env store
          have h_right :
              (C2.denot env store).intersect (Γ2.useset.cs.denot env store)
                ⊆ (C2.denot env store).intersect (Γ.useset.cs.denot env store) :=
            CapabilitySet.intersect_mono_right hacc_sub
          have h_left :
              (C2.denot env store).intersect (Γ.useset.cs.denot env store)
                ⊆ ((C1 ∪ C2).denot env store).intersect (Γ.useset.cs.denot env store) := by
            rw [hunion_denot]
            change (C2.denot env store).intersect (Γ.useset.cs.denot env store) ⊆
              (C1.denot env store).intersect (Γ.useset.cs.denot env store) ∪
                (C2.denot env store).intersect (Γ.useset.cs.denot env store)
            exact CapabilitySet.Subset.union_right_right
          exact CapabilitySet.Subset.trans
            (CapabilitySet.Subset.trans h_right h_left)
            CapabilitySet.Subset.union_right_left
        · exact CapabilitySet.Subset.trans hsub2_drop CapabilitySet.Subset.union_right_right
      have hcompose := eval_capability_set_monotonic h2' hsub_body_tight
      have heqv := weaken_exi_val_denot (env := env) (x := fx) (ps := ps) (T := U)
      apply eval_post_monotonic _ hcompose
      exact Denot.imply_to_entails _ _ (Denot.equiv_to_imply heqv).2

theorem sem_sc_trans
  (hsub1 : SemSubcapt Γ C1 C2)
  (hsub2 : SemSubcapt Γ C2 C3) :
  SemSubcapt Γ C1 C3 := by
  intro env store hts
  specialize hsub1 env store hts
  specialize hsub2 env store hts
  apply CapabilitySet.Subset.trans hsub1 hsub2

theorem sem_sc_elem {C1 C2 : CaptureSet s}
  (hmem : C1 ⊆ C2) :
  SemSubcapt Γ C1 C2 := by
  intro env m hts
  unfold CaptureSet.denot
  induction hmem
  case empty =>
    -- ∅.subst σ = ∅
    simp only [List.empty_eq]
    exact CapabilitySet.Subset.empty
  case refl =>
    exact CapabilitySet.Subset.refl
  case union_left ih1 ih2 =>
    -- (C1 ∪ C2).subst σ = (C1.subst σ) ∪ (C2.subst σ)
    simp only [List.empty_eq]
    exact CapabilitySet.Subset.union_left ih1 ih2
  case union_right_left ih =>
    simp only [List.empty_eq]
    exact CapabilitySet.Subset.trans ih CapabilitySet.Subset.union_right_left
  case union_right_right ih =>
    simp only [List.empty_eq]
    exact CapabilitySet.Subset.trans ih CapabilitySet.Subset.union_right_right

theorem sem_sc_union {C1 C2 C3 : CaptureSet s}
  (hsub1 : SemSubcapt Γ C1 C3)
  (hsub2 : SemSubcapt Γ C2 C3) :
  SemSubcapt Γ (C1.union C2) C3 := by
  intro env m hts
  unfold CaptureSet.denot
  simp only [List.empty_eq]
  exact CapabilitySet.Subset.union_left (hsub1 env m hts) (hsub2 env m hts)
theorem sem_sc_var {x : BVar s .var} {T : Ty .capt s}
  (hlookup : Γ.LookupVar x T) :
  SemSubcapt Γ (.var m (.bound x)) T.captureSet := by
  intro env m' hts
  unfold CaptureSet.denot
  simp only [List.empty_eq]
  have h : reachability_of_loc m'.heap (env.lookup_var x).1 ⊆ T.captureSet.denot env m' := by
    simpa only [Ty.captureSet] using typed_env_lookup_var_reachability hts hlookup
  cases m with
  | epsilon =>
    simpa [CaptureSet.ground_denot]
      using h
  | ro =>
    have hro :
        (CaptureSet.var .ro (Var.free (env.lookup_var x).1)).ground_denot m' ⊆
        reachability_of_loc m'.heap (env.lookup_var x).1 := by
      simpa [CaptureSet.applyRO, CaptureSet.ground_denot]
        using (ground_denot_applyRO_subset
          (C := CaptureSet.var .epsilon (Var.free (env.lookup_var x).1)) (m := m'))
    exact CapabilitySet.Subset.trans hro h

theorem sem_sc_cvar {c : BVar s .cvar} {C : CaptureSet s} {useM : UseMode} {locked : Bool}
  (hlookup : Γ.LookupCVar c useM (.bound C) locked) :
  SemSubcapt Γ (.cvar .epsilon c) C := by
  intro env m hts
  unfold CaptureSet.denot
  simp only [CaptureSet.subst, Subst.from_TypeEnv, List.empty_eq]
  have hbound := typed_env_lookup_cvar_aux hts hlookup
  simp only [CaptureBound.denot, List.empty_eq] at hbound
  cases hbound with
  | set hsub =>
    exact hsub

/-- applyRO on CaptureSet gives a subset in denotation. -/
theorem sem_sc_ro {C : CaptureSet s} :
  SemSubcapt Γ C.applyRO C := by
  intro env m _hts
  unfold CaptureSet.denot
  simp only [CaptureSet.applyRO_subst]
  -- Need: (C.subst σ).applyRO.ground_denot m ⊆ (C.subst σ).ground_denot m
  exact ground_denot_applyRO_subset

/-- applyRO is monotonic for subcapturing. -/
theorem sem_sc_ro_mono {C1 C2 : CaptureSet s}
  (hsub : SemSubcapt Γ C1 C2) :
  SemSubcapt Γ C1.applyRO C2.applyRO := by
  intro env m hts
  unfold CaptureSet.denot
  simp only [CaptureSet.applyRO_subst]
  -- Need: (C1.subst σ).applyRO.ground_denot m ⊆ (C2.subst σ).applyRO.ground_denot m
  exact ground_denot_applyRO_mono (hsub env m hts)

theorem sem_sc_mode {C : CaptureSet s}
  (hm : m1 ≤ m2) :
  SemSubcapt Γ (C.applyMut m1) (C.applyMut m2) := by
  intro env m hts
  unfold CaptureSet.denot
  cases hm with
  | refl =>
    simp only [List.empty_eq]
    exact CapabilitySet.Subset.refl
  | ro_eps =>
    simp only [List.empty_eq, CaptureSet.applyMut_ro, CaptureSet.applyMut_epsilon,
      CaptureSet.applyRO_subst]
    exact ground_denot_applyRO_subset

theorem fundamental_subcapt
  (hsub : Subcapt Γ C1 C2) :
  SemSubcapt Γ C1 C2 := by
  induction hsub
  case sc_trans => grind [sem_sc_trans]
  case sc_elem hsub => exact sem_sc_elem hsub
  case sc_mode hm => exact sem_sc_mode hm
  case sc_union ih1 ih2 => exact sem_sc_union ih1 ih2
  case sc_var hlookup => exact sem_sc_var hlookup
  case sc_cvar hlookup => exact sem_sc_cvar hlookup
  case sc_ro => exact sem_sc_ro
  case sc_ro_mono _ ih => exact sem_sc_ro_mono ih

private theorem fundamental_haskind_ro
  (hkind : HasKind Γ C mode)
  : mode = .ro -> SemHasKind Γ C .ro := by
  induction hkind with
  | empty =>
    intro hm env mem hts
    cases hm
    simp only [CaptureSet.denot, CaptureSet.subst, CaptureSet.ground_denot, List.empty_eq]
    exact CapabilitySet.HasKind.ro_empty
  | union h1 h2 ih1 ih2 =>
    intro hm env mem hts
    cases hm
    simp only [CaptureSet.denot, CaptureSet.subst, CaptureSet.ground_denot, List.empty_eq]
    exact CapabilitySet.HasKind.ro_union (ih1 rfl env mem hts) (ih2 rfl env mem hts)
  | sc hsub hk ih =>
    intro hm env mem hts
    cases hm
    exact CapabilitySet.HasKind.subset_ro
      (fundamental_subcapt hsub env mem hts)
      (ih rfl env mem hts)
  | rw =>
    intro hm
    cases hm
  | ro =>
    rename_i C0
    intro hm env mem hts
    cases hm
    simpa [CaptureSet.denot, CaptureSet.applyRO_subst, ground_denot_applyRO_comm] using
      (CapabilitySet.HasKind.applyRO
        (C := ((C0.subst (Subst.from_TypeEnv env)).ground_denot mem)))

theorem fundamental_haskind
  (hkind : HasKind Γ C mode) :
  SemHasKind Γ C mode := by
  cases hmode : mode with
  | epsilon =>
    intro env mem hts
    exact CapabilitySet.HasKind.eps
  | ro =>
    simpa [hmode] using fundamental_haskind_ro hkind hmode


lemma sem_subtyp_top {T : Ty .capt s}
  (hpure : T.IsPureType) :
  SemSubtyp Γ T .top := by
  -- Unfold SemSubtyp for capturing types
  simp only [SemSubtyp]
  -- Introduce the environment, memory, and typing assumption
  intro env H htyping
  -- Unfold ImplyAfter to handle memory subsumption
  simp only [Denot.ImplyAfter]
  intro m' hsubsumes
  -- Unfold ImplyAt to get the implication at a specific memory
  simp only [Denot.ImplyAt]
  intro e hdenot_T
  -- Need to prove: Ty.val_denot env .top m' e
  -- Which unfolds to: e.IsSimpleAns ∧ e.WfInHeap m'.heap ∧ resolve_reachability m'.heap e ⊆ .empty
  simp only [Ty.val_denot]
  constructor
  · -- Prove IsSimpleAns
    have himply_simple := val_denot_implies_simple_ans (typed_env_is_implying_simple_ans htyping) T
    exact himply_simple m' e hdenot_T
  constructor
  · -- Prove well-formedness: e.WfInHeap m'.heap
    have hwf_env := typed_env_is_implying_wf htyping
    have hwf_denot := val_denot_implies_wf hwf_env T
    exact hwf_denot m' e hdenot_T
  · -- Prove reachability bound: resolve_reachability m'.heap e ⊆ .empty
    -- First get the typing for m' (need monotonicity)
    have htyping' := env_typing_monotonic htyping hsubsumes
    -- Use val_denot_enforces_captures to bound reachability by T.captureSet
    have hbound := val_denot_enforces_captures htyping' e hdenot_T
    -- Since T is pure, T.captureSet is empty, so its denotation is empty
    unfold Ty.IsPureType at hpure
    have hempty := hpure.denot_empty (env := env) (m := m')
    exact hempty.subset_of_subset hbound


-- Helper lemma for extracting type variable bounds from EnvTyping
lemma env_typing_lookup_tvar {X : BVar s .tvar} {S : PureTy s} {env : TypeEnv s} {m : Memory}
  (hlookup : Ctx.LookupTVar Γ X S)
  (htyping : EnvTyping Γ env m) :
  (env.lookup_tvar X).ImplyAfter m (Ty.val_denot env S.core) := by
  induction hlookup generalizing m
  case here Γ S =>
    match env with
    | .extend env0 (.tvar d) =>
      simp only [EnvTyping, TypeEnv.lookup_tvar] at htyping ⊢
      obtain ⟨hproper, himply_wf, himply_simple, himply, hpure, htyping'⟩ := htyping
      -- Need: d.ImplyAfter m (Ty.val_denot (env0.extend_tvar d) (S.rename Rename.succ).core)
      -- Have: d.ImplyAfter m (Ty.val_denot env0 S.core)
      -- Note: (S.rename Rename.succ).core = S.core.rename Rename.succ
      -- Use weakening theorem to relate the denotations
      have hw : Ty.val_denot env0 S.core ≈
                Ty.val_denot (env0.extend_tvar d) (S.core.rename Rename.succ) :=
        tweaken_val_denot (d := d)
      simp only [TypeEnv.extend_tvar] at hw
      -- The result follows by transitivity: himply gives d ⊑ val_denot env0 S.core,
      -- hw gives val_denot env0 S.core ≈ val_denot (env0.extend_tvar d) (S.core.rename Rename.succ)
      -- Compose ImplyAfter with equivalence
      simp only [Denot.ImplyAfter] at himply ⊢
      intro m' hsub
      simp only [Denot.ImplyAt]
      intro e hd
      have himply_spec := himply m' hsub e hd
      exact (Denot.equiv_to_imply hw).1 m' e himply_spec
  case there Γ X S b a a_ih =>
    -- Need to case split on what kind of binding b is
    cases b with
    | var T =>
      -- Context extended with a term variable
      match env with
      | .extend env0 (.var v ps0) =>
        simp only [EnvTyping, TypeEnv.lookup_tvar] at htyping ⊢
        obtain ⟨hval_denot, _, htyping'⟩ := htyping
        -- Apply IH to get the result for the smaller environment
        have ih_result := a_ih htyping'
        -- Use weakening lemma for var extension
        have hw : Ty.val_denot env0 S.core ≈
                  Ty.val_denot (env0.extend_var v ps0) (S.core.rename Rename.succ) :=
          weaken_val_denot (x := v) (ps := ps0)
        simp only [TypeEnv.extend_var] at hw
        -- Compose IH with weakening
        simp only [Denot.ImplyAfter] at ih_result ⊢
        intro m' hsub
        simp only [Denot.ImplyAt]
        intro e hd
        have himply_spec := ih_result m' hsub e hd
        exact (Denot.equiv_to_imply hw).1 m' e himply_spec
    | tvar T =>
      -- Context extended with a type variable
      match env with
      | .extend env0 (.tvar d) =>
        simp only [EnvTyping, TypeEnv.lookup_tvar] at htyping ⊢
        obtain ⟨hproper, himply_wf, himply_simple, himply_bound, hpure, htyping'⟩ := htyping
        -- Apply IH
        have ih_result := a_ih htyping'
        -- Use tweaken for tvar extension
        have hw : Ty.val_denot env0 S.core ≈
                  Ty.val_denot (env0.extend_tvar d) (S.core.rename Rename.succ) :=
          tweaken_val_denot (d := d)
        simp only [TypeEnv.extend_tvar] at hw
        -- Compose IH with weakening
        simp only [Denot.ImplyAfter] at ih_result ⊢
        intro m' hsub
        simp only [Denot.ImplyAt]
        intro e hd
        have himply_spec := ih_result m' hsub e hd
        exact (Denot.equiv_to_imply hw).1 m' e himply_spec
    | cvar useM cb =>
      -- Context extended with a capture variable
      match env with
      | .extend env0 (.cvar cs cap) =>
        simp only [EnvTyping, TypeEnv.lookup_tvar] at htyping ⊢
        obtain ⟨hwf_cb, hbound_wf, hbound, _, htyping'⟩ := htyping
        -- Apply IH
        have ih_result := a_ih htyping'
        -- Use cweaken for cvar extension
        have hw : Ty.val_denot env0 S.core ≈
                  Ty.val_denot (env0.extend_cvar cs cap) (S.core.rename Rename.succ) :=
          cweaken_val_denot (cs := cs) (cap := cap)
        simp only [TypeEnv.extend_cvar] at hw
        -- Compose IH with weakening
        simp only [Denot.ImplyAfter] at ih_result ⊢
        intro m' hsub
        simp only [Denot.ImplyAt]
        intro e hd
        have himply_spec := ih_result m' hsub e hd
        exact (Denot.equiv_to_imply hw).1 m' e himply_spec
  case lock ih =>
    change EnvTyping _ env m at htyping
    exact ih htyping

lemma sem_subtyp_tvar {X : BVar s .tvar} {S : PureTy s}
  (hlookup : Ctx.LookupTVar Γ X S) :
  SemSubtyp Γ (.tvar X) S.core := by
  -- Unfold SemSubtyp for capturing types
  simp only [SemSubtyp]
  intro env H htyping
  -- Extract the type variable bound using the helper lemma
  have himply := env_typing_lookup_tvar hlookup htyping
  -- Unfold the denotations
  simp only [Ty.val_denot]
  -- The result follows directly from himply
  exact himply

lemma sem_subtyp_arrow {T1 T2 : Ty .capt s} {cs1 cs2 : CaptureSet s} {U1 U2 : Ty .exi (s,x)}
  (harg : SemSubtyp Γ T2 T1)
  (hcs : SemSubcapt Γ cs1 cs2)
  (hcs2_closed : CaptureSet.IsClosed cs2)
  (hres : SemSubtyp (Γ,x:T2) U1 U2) :
  SemSubtyp Γ (.arrow T1 cs1 U1) (.arrow T2 cs2 U2) := by
  -- Unfold SemSubtyp for capturing types
  simp only [SemSubtyp]
  intro env H htyping
  -- Need to prove Denot.ImplyAfter for arrow types
  simp only [Denot.ImplyAfter]
  intro m' hsubsumes e h_arrow_T1_cs1_U1
  -- Unfold the denotation of arrow types
  simp only [Ty.val_denot] at h_arrow_T1_cs1_U1 ⊢
  -- Extract the components from the (.arrow T1 cs1 U1) denotation
  obtain ⟨hwf, hcs1_wf, cs', T0, t0, hresolve, hcs'_wf, hR0_subset_cs1, hbody⟩ := h_arrow_T1_cs1_U1
  -- Construct the proof for (.arrow T2 cs2 U2)
  constructor
  · exact hwf  -- Well-formedness is preserved
  · constructor
    · -- Need to show cs2 is well-formed in m'.heap
      -- First show it's well-formed at H.heap
      have hwf_cs2_at_H : (cs2.subst (Subst.from_TypeEnv env)).WfInHeap H.heap := by
        apply CaptureSet.wf_subst
        · -- cs2.WfInHeap H.heap follows from closedness
          apply CaptureSet.wf_of_closed hcs2_closed
        · -- (Subst.from_TypeEnv env).WfInHeap H.heap follows from EnvTyping
          exact from_TypeEnv_wf_in_heap htyping
      -- Then lift to m'.heap using monotonicity
      exact CaptureSet.wf_monotonic hsubsumes hwf_cs2_at_H
    · use cs', T0, t0
      constructor
      · exact hresolve  -- Same resolution
      · constructor
        · exact hcs'_wf  -- Capture set well-formedness preserved for cs'
        · constructor
          · -- Need to show: expand_captures m'.heap cs' ⊆ cs2.denot env m'
            -- We have: hR0_subset_cs1 : expand_captures m'.heap cs' ⊆ cs1.denot env m'
            -- We have: hcs : SemSubcapt Γ cs1 cs2, which gives cs1.denot ⊆ cs2.denot
            have hcs_sem := hcs env m' (env_typing_monotonic htyping hsubsumes)
            -- Use calc mode with Trans instance for CapabilitySet.Subset
            calc expand_captures m'.heap cs'
              _ ⊆ cs1.denot env m' := hR0_subset_cs1
              _ ⊆ cs2.denot env m' := hcs_sem
          · -- Need to prove the body property with contravariant arg and covariant result
            intro arg m'' hsub hcompat harg_T2
            -- Use the computed peak sets
            let psT1 := compute_peakset env T1.captureSet
            let psT2 := compute_peakset env T2.captureSet
            -- Apply contravariance: if arg satisfies T2, it also satisfies T1
            have harg_T1 : Ty.val_denot env T1 m'' (.var (.free arg)) := by
              have harg_sem := harg env H htyping
              have hsub_H_m'' := Memory.subsumes_trans hsub hsubsumes
              exact harg_sem m'' hsub_H_m'' (.var (.free arg)) harg_T2
            -- Define the authority sets
            let R0 := expand_captures m'.heap cs'
            let R := R0
            -- Apply hbody at the T1 peak set; hbody_spec now has the strong post.
            have hbody_spec := hbody arg m'' hsub hcompat harg_T1
            -- Transport from psT1 to psT2 using Retype with the identity substitution.
            have hretype :
                Retype (env.extend_var arg psT1) Subst.id
                  (env.extend_var arg psT2) (psT1.rename Rename.succ) :=
              { var := by
                  intro x
                  cases x
                  case here => rfl
                  case there x =>
                    change
                      (env.lookup_var x).1 =
                        interp_var (env.extend_var arg psT2)
                          ((Subst.id.var x).rename Rename.succ)
                    rw [← weaken_interp_var]
                    rfl
                tvar := by
                  intro X
                  cases X with
                  | there X =>
                    change
                      env.lookup_tvar X
                        ≈ Ty.val_denot (env.extend_var arg psT2) (Ty.tvar X.there)
                    rw [Ty.val_denot.eq_2]
                    exact Denot.equiv_refl _
                cvar := by
                  intro C
                  cases C
                  case there C =>
                    change
                      (env.lookup_cvar C).1 =
                        ((Subst.id.cvar C).rename Rename.succ).subst
                          (Subst.from_TypeEnv (env.extend_var arg psT2))
                    rfl }
            have heq_val := retype_exi_val_denot (ρ := hretype) U1
            -- Convert hbody_spec from psT1 to psT2 (preserves_liveness conjunct unchanged).
            have hbody_psT2 :
                Eval R m'' (t0.subst (Subst.openVar (.free arg)))
                  (fun v m''' =>
                    Ty.exi_val_denot (env.extend_var arg psT2) U1 m''' v) := by
              apply eval_post_monotonic _ hbody_spec
              intro m''' v hval
              have heqv := Denot.equiv_to_imply (by simpa [Ty.subst_id] using heq_val)
              exact heqv.1 m''' v hval
            -- Apply covariance: if body satisfies U1, it also satisfies U2
            -- Build EnvTyping for the extended context with T2's peak set
            have htyping_ext : EnvTyping (Γ,x:T2) (env.extend_var arg psT2) m'' := by
              simp only [TypeEnv.extend_var]
              constructor
              · exact harg_T2
              · constructor
                · exact (compute_peakset_correct htyping T2.captureSet).symm
                · have hsub_H_m'' := Memory.subsumes_trans hsub hsubsumes
                  exact env_typing_monotonic htyping hsub_H_m''
            -- Apply semantic subtyping for the result (lifts U1 → U2 in val_denot).
            have hres_sem := hres (env.extend_var arg psT2) m'' htyping_ext
            have himply_entails := Denot.imply_after_to_m_entails_after hres_sem
            -- Lift hbody_psT2 from U1 to U2.
            apply eval_post_monotonic_general _ hbody_psT2
            intro m''' hsub' v hval
            exact himply_entails m''' hsub' v hval


lemma sem_subtyp_trans {k : TySort} {T1 T2 T3 : Ty k s}
  (h12 : SemSubtyp Γ T1 T2)
  (h23 : SemSubtyp Γ T2 T3) :
  SemSubtyp Γ T1 T3 := by
  -- Unfold SemSubtyp and handle each type sort
  simp only [SemSubtyp] at h12 h23 ⊢
  -- Match on the type sort
  cases k with
  | capt =>
    -- For capturing types
    intro env H htyping
    have h12' := h12 env H htyping
    have h23' := h23 env H htyping
    simp only [Denot.ImplyAfter] at h12' h23' ⊢
    intro m' hsubsumes
    exact Denot.implyat_trans (h12' m' hsubsumes) (h23' m' hsubsumes)
  | exi =>
    -- For existential types
    intro env H htyping
    have h12' := h12 env H htyping
    have h23' := h23 env H htyping
    simp only [Denot.ImplyAfter] at h12' h23' ⊢
    intro m' hsubsumes
    exact Denot.implyat_trans (h12' m' hsubsumes) (h23' m' hsubsumes)

lemma sem_subtyp_refl {k : TySort} {T : Ty k s} :
  SemSubtyp Γ T T := by
  -- Unfold SemSubtyp and handle each type sort
  simp only [SemSubtyp]
  -- Match on the type sort
  cases k with
  | capt =>
    -- For capturing types
    intro env H htyping
    simp only [Denot.ImplyAfter]
    intro m' hsubsumes
    exact Denot.imply_implyat (Denot.imply_refl _)
  | exi =>
    -- For existential types
    intro env H htyping
    simp only [Denot.ImplyAfter]
    intro m' hsubsumes
    exact Denot.imply_implyat (Denot.imply_refl _)


lemma fundamental_subbound
  (hsub : Subbound Γ B1 B2) :
  SemSubbound Γ B1 B2 := by
  induction hsub with
  | capset hsubcapt =>
    intro env m htyping
    simp only [CaptureBound.denot]
    have hsem := fundamental_subcapt hsubcapt
    exact CapabilityBound.SubsetEq.set (hsem env m htyping)
  | top =>
    intro env m htyping
    simp only [CaptureBound.denot]
    exact CapabilityBound.SubsetEq.top


lemma sem_subtyp_cpoly {cb1 cb2 : CaptureBound s} {cs1 cs2 : CaptureSet s} {T1 T2 : Ty .exi (s,C)}
  (hB : SemSubbound Γ cb2 cb1) -- contravariant in bound
  (hcs : SemSubcapt Γ cs1 cs2) -- covariant in capture set
  (hcs2_closed : CaptureSet.IsClosed cs2) -- cs2 is closed
  (hT : SemSubtyp (Γ,C<:cb2) T1 T2) -- covariant in body under tighter bound
  (hclosed_cb2 : cb2.IsClosed)
  : SemSubtyp Γ (.cpoly cb1 cs1 T1) (.cpoly cb2 cs2 T2) := by
  -- Unfold SemSubtyp for capturing types
  simp only [SemSubtyp]
  intro env H htyping
  -- Need to prove Denot.ImplyAfter for cpoly types
  simp only [Denot.ImplyAfter]
  intro m' hsubsumes e h_cpoly_cb1_cs1_T1
  -- Unfold the denotation of cpoly types
  simp only [Ty.val_denot] at h_cpoly_cb1_cs1_T1 ⊢
  -- Extract the components from (.cpoly cb1 cs1 T1) denotation
  obtain ⟨hwf, hcs1_wf, cs', B0, t0, hresolve, hcs'_wf, hR0_subset_cs1, hbody⟩ := h_cpoly_cb1_cs1_T1
  -- Construct the proof for (.cpoly cb2 cs2 T2)
  constructor
  · exact hwf  -- Well-formedness is preserved
  · constructor
    · -- Need to show cs2 is well-formed in m'.heap
      have hwf_cs2_at_H : (cs2.subst (Subst.from_TypeEnv env)).WfInHeap H.heap := by
        apply CaptureSet.wf_subst
        · apply CaptureSet.wf_of_closed hcs2_closed
        · exact from_TypeEnv_wf_in_heap htyping
      exact CaptureSet.wf_monotonic hsubsumes hwf_cs2_at_H
    · use cs', B0, t0
      constructor
      · exact hresolve  -- Same resolution
      · constructor
        · exact hcs'_wf  -- Capture set well-formedness preserved for cs'
        · constructor
          · -- Need to show: expand_captures m'.heap cs' ⊆ cs2.denot env m'
            have hcs_sem := hcs env m' (env_typing_monotonic htyping hsubsumes)
            calc expand_captures m'.heap cs'
              _ ⊆ cs1.denot env m' := hR0_subset_cs1
              _ ⊆ cs2.denot env m' := hcs_sem
          · -- Need to prove the body property with contravariant bound and covariant body
            intro m'' CS hCS_wf hsub_m'' hcompat hCS_satisfies_cb2
            let A0 := CS.denot TypeEnv.empty
            have hCS_satisfies_cb1 : (A0 m'').BoundedBy (cb1.denot env m'') := by
              have hB_trans := Memory.subsumes_trans hsub_m'' hsubsumes
              have htyping_m'' := env_typing_monotonic htyping hB_trans
              have hB_at_m'' := hB env m'' htyping_m''
              exact CapabilitySet.BoundedBy.trans hCS_satisfies_cb2 hB_at_m''
            -- Apply the original function body with this CS
            have heval1 := hbody m'' CS hCS_wf hsub_m'' hcompat hCS_satisfies_cb1
            -- Now use covariance hT
            have henv' : EnvTyping (Γ,C<:cb2)
                (env.extend_cvar CS (cap := CS.ground_denot m'')) m'' := by
              simp only [TypeEnv.extend_cvar]
              constructor
              · exact hCS_wf
              constructor
              · have hwf_cb2_at_H : (cb2.subst (Subst.from_TypeEnv env)).WfInHeap H.heap := by
                  exact CaptureBound.wf_subst (CaptureBound.wf_of_closed hclosed_cb2)
                                                (from_TypeEnv_wf_in_heap htyping)
                have hB_trans := Memory.subsumes_trans hsub_m'' hsubsumes
                exact CaptureBound.wf_monotonic hB_trans hwf_cb2_at_H
              constructor
              · -- Convert hCS_satisfies_cb2 from CS.denot TypeEnv.empty to CS.ground_denot
                have : CS.denot TypeEnv.empty = CS.ground_denot := by
                  simp only [CaptureSet.denot, Subst.from_TypeEnv_empty, CaptureSet.subst_id]
                rw [← this]
                exact hCS_satisfies_cb2
              constructor
              · rfl
              · have hB_trans := Memory.subsumes_trans hsub_m'' hsubsumes
                exact env_typing_monotonic htyping hB_trans
            have hT_sem := hT (env.extend_cvar CS (cap := CS.ground_denot m'')) m'' henv'
            -- Convert to postcondition entailment
            have himply_entails := Denot.imply_after_to_m_entails_after hT_sem
            -- Lift heval1 from T1 to T2 in the val_denot.
            apply eval_post_monotonic_general _ heval1
            intro m''' hsub' v hval
            exact himply_entails m''' hsub' v hval

-- lemma sem_subtyp_capt {C1 C2 : CaptureSet s} {S1 S2 : Ty .shape s}
--   (hC : SemSubcapt Γ C1 C2) -- covariant in capture set
--   (hS : SemSubtyp Γ S1 S2) -- covariant in shape
--   (hclosed_C2 : C2.IsClosed) -- C2 is closed
--   : SemSubtyp Γ (.capt C1 S1) (.capt C2 S2) := by
--   -- Unfold SemSubtyp for capt types
--   simp [SemSubtyp]
--   intro env H htyping
--   -- Need to prove Denot.ImplyAfter for capt types
--   simp [Denot.ImplyAfter, Denot.ImplyAt]
--   intro m hsubsumes e h_capt_C1_S1
--   -- Unfold the denotation of capt types
--   simp [Ty.capt_val_denot] at h_capt_C1_S1 ⊢
--   -- Extract components from C1 S1 denotation
--   obtain ⟨hsimple, hwf, hC1_wf, hS1_at_C1⟩ := h_capt_C1_S1
--   -- Construct proof for C2 S2
--   constructor
--   · exact hsimple  -- IsSimpleAns preserved
--   constructor
--   · exact hwf  -- Well-formedness preserved
--   · constructor
--     · -- Need: (C2.subst (Subst.from_TypeEnv env)).WfInHeap m.heap
--       -- From closedness of C2, we get well-formedness at any heap
--       -- First show it's well-formed at H.heap
--       have hwf_C2_at_H : (C2.subst (Subst.from_TypeEnv env)).WfInHeap H.heap := by
--         -- Use wf_subst with closedness of C2 and well-formedness of the substitution
--         apply CaptureSet.wf_subst
--         · -- C2.WfInHeap H.heap follows from closedness
--           apply CaptureSet.wf_of_closed hclosed_C2
--         · -- (Subst.from_TypeEnv env).WfInHeap H.heap follows from EnvTyping
--           exact from_TypeEnv_wf_in_heap htyping
--       -- Then lift to m.heap using monotonicity
--       exact CaptureSet.wf_monotonic hsubsumes hwf_C2_at_H
--     · -- Need: Ty.shape_val_denot env S2 (C2.denot env m) m e
--       -- We have: hS1_at_C1 : Ty.shape_val_denot env S1 (C1.denot env m) m e
--       -- Strategy:
--       -- 1. Get C1.denot ⊆ C2.denot from hC
--       -- 2. Use capability set covariance to get S1 at C2.denot
--       -- 3. Use semantic subtyping hS to get S2 at C2.denot

--       -- Step 1: Get capability set subsumption
--       have hC_subset : C1.denot env m ⊆ C2.denot env m := by
--         have htyping_m := env_typing_monotonic htyping hsubsumes
--         exact hC env m htyping_m

--       -- Step 2: Lift S1 from C1.denot to C2.denot
--       have hS1_at_C2 : Ty.shape_val_denot env S1 (C2.denot env m) m e := by
--         -- Use reachability monotonicity: shape types are covariant in capability sets
--         have henv_mono := typed_env_is_reachability_monotonic htyping
--         have hshape_mono := shape_val_denot_is_reachability_monotonic henv_mono S1
--         simp [PreDenot.is_reachability_monotonic] at hshape_mono
--         exact hshape_mono (C1.denot env m) (C2.denot env m) hC_subset m e hS1_at_C1

--       -- Step 3: Apply semantic subtyping
--       have hS_sem := hS env H htyping
--       simp [PreDenot.ImplyAfter] at hS_sem
--       have hS_at_H := hS_sem (C2.denot env m)
--       simp [Denot.ImplyAfter, Denot.ImplyAt] at hS_at_H
--       exact hS_at_H m hsubsumes e hS1_at_C2

lemma sem_subtyp_exi {T1 T2 : Ty .capt (s,C)}
  (hT : SemSubtyp (Γ,C<:.unbound) T1 T2) -- covariant in body
  : SemSubtyp Γ (.exi T1) (.exi T2) := by
  -- Unfold SemSubtyp for exi types
  simp only [SemSubtyp]
  intro env H htyping
  -- Need to prove Denot.ImplyAfter for exi types
  simp only [Denot.ImplyAfter, Denot.ImplyAt]
  intro m hsubsumes e h_exi_T1
  -- Unfold the denotation of exi types
  simp only [Ty.exi_val_denot] at h_exi_T1 ⊢
  -- Extract the pack from the exi denotation
  cases hresolve : resolve m.heap e with
  | none =>
    -- e doesn't resolve, contradiction
    simp only [hresolve] at h_exi_T1
  | some cell =>
    simp only [hresolve] at h_exi_T1 ⊢
    cases cell with
    | pack CS x =>
      -- h_exi_T1 : CS.WfInHeap m.heap ∧ Ty.capt_val_denot (env.extend_cvar CS) T1 m (.var x)
      -- Need: CS.WfInHeap m.heap ∧ Ty.capt_val_denot (env.extend_cvar CS) T2 m (.var x)
      obtain ⟨hwf_CS, h_body_T1⟩ := h_exi_T1
      -- Construct the well-formedness part of the goal
      constructor
      · exact hwf_CS
      · -- Construct EnvTyping for the extended context
        have henv' : EnvTyping (Γ,C<:.unbound)
            (env.extend_cvar CS (cap := CS.ground_denot m)) m := by
          simp only [TypeEnv.extend_cvar]
          constructor
          · -- Need: CS.WfInHeap m.heap
            exact hwf_CS
          constructor
          · simp only [CaptureBound.subst]
            exact CaptureBound.WfInHeap.wf_unbound
          constructor
          · simp only [CaptureBound.denot]
            exact CapabilitySet.BoundedBy.top
          constructor
          · rfl
          · exact env_typing_monotonic htyping hsubsumes
        -- Apply semantic subtyping
        have hT_sem := hT (env.extend_cvar CS (cap := CS.ground_denot m)) m henv'
        simp only [Denot.ImplyAfter, Denot.ImplyAt] at hT_sem
        exact hT_sem m (Memory.subsumes_refl m) (.var x) h_body_T1
    | _ =>
      -- Other cell types don't match exi
      simp at h_exi_T1

lemma sem_subtyp_typ {T1 T2 : Ty .capt s}
  (hT : SemSubtyp Γ T1 T2) -- covariant in body
  : SemSubtyp Γ (.typ T1) (.typ T2) := by
  -- Unfold SemSubtyp for exi types
  simp only [SemSubtyp]
  intro env H htyping
  -- Unfold exi_val_denot for .typ
  -- .typ T has denotation capt_val_denot env T
  simp only [Ty.exi_val_denot]
  -- The goal is now: (capt_val_denot env T1).ImplyAfter H (capt_val_denot env T2)
  -- Which is exactly SemSubtyp Γ T1 T2 (for capt types)
  exact hT env H htyping


lemma sem_subtyp_poly {S1 S2 : PureTy s} {cs1 cs2 : CaptureSet s} {T1 T2 : Ty .exi (s,X)}
  (hS : SemSubtyp Γ S2.core S1.core) -- contravariant in bound
  (hcs : SemSubcapt Γ cs1 cs2) -- covariant in capture set
  (hcs2_closed : CaptureSet.IsClosed cs2) -- cs2 is closed
  (hT : SemSubtyp (Γ,X<:S2) T1 T2) -- covariant in body under tighter bound
  : SemSubtyp Γ (.poly S1.core cs1 T1) (.poly S2.core cs2 T2) := by
  -- Unfold SemSubtyp for capturing types
  simp only [SemSubtyp]
  intro env H htyping
  -- Need to prove Denot.ImplyAfter for poly types
  simp only [Denot.ImplyAfter]
  intro m' hsubsumes e h_poly_S1_cs1_T1
  -- Unfold the denotation of poly types
  simp only [Ty.val_denot] at h_poly_S1_cs1_T1 ⊢
  -- Extract the components from (.poly S1.core cs1 T1) denotation
  obtain ⟨hwf, hcs1_wf, cs', S0, t0, hresolve, hcs'_wf, hR0_subset_cs1, hbody⟩ := h_poly_S1_cs1_T1
  -- Construct the proof for (.poly S2.core cs2 T2)
  constructor
  · exact hwf  -- Well-formedness is preserved
  · constructor
    · -- Need to show cs2 is well-formed in m'.heap
      have hwf_cs2_at_H : (cs2.subst (Subst.from_TypeEnv env)).WfInHeap H.heap := by
        apply CaptureSet.wf_subst
        · apply CaptureSet.wf_of_closed hcs2_closed
        · exact from_TypeEnv_wf_in_heap htyping
      exact CaptureSet.wf_monotonic hsubsumes hwf_cs2_at_H
    · use cs', S0, t0
      constructor
      · exact hresolve  -- Same resolution
      · constructor
        · exact hcs'_wf  -- Capture set well-formedness preserved for cs'
        · constructor
          · -- Need to show: expand_captures m'.heap cs' ⊆ cs2.denot env m'
            have hcs_sem := hcs env m' (env_typing_monotonic htyping hsubsumes)
            calc expand_captures m'.heap cs'
              _ ⊆ cs1.denot env m' := hR0_subset_cs1
              _ ⊆ cs2.denot env m' := hcs_sem
          · -- Need to prove the body property with contravariant bound and covariant body
            intro m'' denot hsub_m'' hcompat hdenot_proper hdenot_simple himply_S2 hdenot_pure
            -- hbody expects denot.ImplyAfter m'' (Ty.val_denot env S1.core)
            -- We have himply_S2 : denot.ImplyAfter m'' (Ty.val_denot env S2.core)
            -- And hS : SemSubtyp Γ S2.core S1.core, i.e., S2.core <: S1.core
            -- So we need to compose: denot -> S2.core -> S1.core
            have himply_S1 : denot.ImplyAfter m'' (Ty.val_denot env S1.core) := by
              simp only [Denot.ImplyAfter, Denot.ImplyAt]
              intro m''' hsub_m''' e' hdenot_e
              simp only [Denot.ImplyAfter, Denot.ImplyAt] at himply_S2
              have hS2 := himply_S2 m''' hsub_m''' e' hdenot_e
              have hS_trans :=
                Memory.subsumes_trans hsub_m''' (Memory.subsumes_trans hsub_m'' hsubsumes)
              have hS_sem := hS env H htyping
              simp only [Denot.ImplyAfter, Denot.ImplyAt] at hS_sem
              exact hS_sem m''' hS_trans e' hS2
            -- Apply the original function body with this denot
            have heval1 :=
              hbody m'' denot hsub_m'' hcompat hdenot_proper hdenot_simple himply_S1 hdenot_pure
            -- Now use covariance hT
            have henv' : EnvTyping (Γ,X<:S2) (env.extend_tvar denot) m'' := by
              constructor
              · exact hdenot_proper
              · constructor
                · -- implies_wf follows from is_proper
                  exact hdenot_proper.2.2.2
                · constructor
                  · exact hdenot_simple
                  · constructor
                    · exact himply_S2
                    · constructor
                      · exact hdenot_pure
                      · apply env_typing_monotonic htyping
                          (Memory.subsumes_trans hsub_m'' hsubsumes)
            have hT_sem := hT (env.extend_tvar denot) m'' henv'
            -- Convert to postcondition entailment
            have himply_entails := Denot.imply_after_to_m_entails_after hT_sem
            -- Lift heval1 from T1 to T2 in the val_denot.
            apply eval_post_monotonic_general _ heval1
            intro m''' hsub' v hval
            exact himply_entails m''' hsub' v hval

theorem fundamental_subtyp
  (hT1 : T1.IsClosed) (hT2 : T2.IsClosed)
  (hsub : Subtyp Γ T1 T2) :
  SemSubtyp Γ T1 T2 := by
  induction hsub
  case top hpure => exact sem_subtyp_top hpure
  case tvar hlookup => exact sem_subtyp_tvar hlookup
  case arrow hsub_arg hsub_cs hsub_res ih_arg ih_res =>
    -- T1 = (.arrow T1_arg cs1 U1), T2 = (.arrow T2_arg cs2 U2)
    -- hsub_arg : Subtyp Γ T2_arg T1_arg (contravariant)
    -- hsub_cs : Subcapt Γ cs1 cs2 (covariant)
    -- hsub_res : Subtyp (Γ,x:T2_arg) U1 U2 (covariant)
    -- Extract closedness from arrow types
    cases hT1 with | arrow hT1_arg_closed hcs1_closed hU1_closed =>
    cases hT2 with | arrow hT2_arg_closed hcs2_closed hU2_closed =>
    -- Apply sem_subtyp_arrow
    apply sem_subtyp_arrow
    · -- Prove SemSubtyp Γ T2_arg T1_arg (contravariant)
      exact ih_arg hT2_arg_closed hT1_arg_closed
    · -- Prove SemSubcapt Γ cs1 cs2
      exact fundamental_subcapt hsub_cs
    · -- Prove closedness of cs2
      exact hcs2_closed
    · -- Prove SemSubtyp (Γ,x:T2_arg) U1 U2 (covariant)
      exact ih_res hU1_closed hU2_closed
  case refl =>
    -- T1 = T2
    exact sem_subtyp_refl
  case trans hT2_mid _hsub12 _hsub23 ih12 ih23 =>
    -- hsub is (T1 <: T2_mid <: T2), where T2_mid is the middle type
    -- hT2_mid : T2_mid.IsClosed (provided by the trans rule)
    -- ih12 : T1.IsClosed → T2_mid.IsClosed → SemSubtyp Γ T1 T2_mid
    -- ih23 : T2_mid.IsClosed → T2.IsClosed → SemSubtyp Γ T2_mid T2
    exact sem_subtyp_trans (ih12 hT1 hT2_mid) (ih23 hT2_mid hT2)
  case cpoly hle hsub_cs hsub_body ih_body =>
    -- T1 = (.cpoly m1 cs1 T1_body), T2 = (.cpoly m2 cs2 T2_body)
    -- hle : cb2 <: cb1 (contravariant)
    -- hsub_cs : Subcapt Γ cs1 cs2 (covariant)
    -- hsub_body : Subtyp (Γ,C<:m2) T1_body T2_body (covariant)
    -- Extract closedness from cpoly types
    cases hT1 with | cpoly hcb1_closed hcs1_closed hT1_body_closed =>
    cases hT2 with | cpoly hcb2_closed hcs2_closed hT2_body_closed =>
    -- Apply sem_subtyp_cpoly
    apply sem_subtyp_cpoly
    · exact fundamental_subbound hle
    · exact fundamental_subcapt hsub_cs
    · exact hcs2_closed
    · exact ih_body hT1_body_closed hT2_body_closed
    · exact hcb2_closed
  case poly hsub_bound hsub_cs hsub_body ih_bound ih_body =>
    -- T1 = (.poly S1.core cs1 T1_body), T2 = (.poly S2.core cs2 T2_body)
    -- hsub_bound : Subtyp Γ S2.core S1.core (contravariant)
    -- hsub_cs : Subcapt Γ cs1 cs2 (covariant)
    -- hsub_body : Subtyp (Γ,X<:S2) T1_body T2_body (covariant)
    -- Extract closedness from poly types
    cases hT1 with | poly hS1_closed hcs1_closed hT1_body_closed =>
    cases hT2 with | poly hS2_closed hcs2_closed hT2_body_closed =>
    -- Apply sem_subtyp_poly
    apply sem_subtyp_poly
    · exact ih_bound hS2_closed hS1_closed  -- contravariant
    · exact fundamental_subcapt hsub_cs
    · exact hcs2_closed
    · exact ih_body hT1_body_closed hT2_body_closed
  case exi hsub_body ih_body =>
    -- T1 = (.exi T1_body), T2 = (.exi T2_body)
    -- hsub_body : Subtyp (Γ,C<:.epsilon) T1_body T2_body
    -- Extract closedness from exi types
    cases hT1 with | exi hT1_body_closed =>
    cases hT2 with | exi hT2_body_closed =>
    -- Apply sem_subtyp_exi
    exact sem_subtyp_exi (ih_body hT1_body_closed hT2_body_closed)
  case typ hsub_body ih_body =>
    -- T1 = (.typ T1_body), T2 = (.typ T2_body)
    -- hsub_body : Subtyp Γ T1_body T2_body
    -- Extract closedness from typ types
    cases hT1 with | typ hT1_body_closed =>
    cases hT2 with | typ hT2_body_closed =>
    -- Apply sem_subtyp_typ
    exact sem_subtyp_typ (ih_body hT1_body_closed hT2_body_closed)


theorem sem_typ_subtyp
  {C1 C2 : CaptureSet s} {E1 E2 : Ty .exi s}
  (ht : C1 # Γ ⊨ e : E1)
  (hsubcapt : Subcapt Γ C1 C2)
  (hsubtyp : Subtyp Γ E1 E2)
  (_hclosed_C1 : C1.IsClosed) (hclosed_E1 : E1.IsClosed)
  (_hclosed_C2 : C2.IsClosed) (hclosed_E2 : E2.IsClosed) :
  C2 # Γ ⊨ e : E2 := by
  intro env m htyping hcompat
  -- Use fundamental_subcapt to get C1.denot ⊆ C2.denot (semantic subcapt)
  have hsubcapt_sem := fundamental_subcapt hsubcapt env m htyping
  have hcompat_C1 : m.is_compatible (C1.denot env m) :=
    Memory.is_compatible_subset hsubcapt_sem hcompat
  -- Raw evaluation from ht at the wider budget (C1 ∪ consumeset.to_drop).
  have h_eval_E1 := ht env m htyping hcompat_C1
  -- Widen the authority side from C1 to C2 (preserves the shared drop component).
  -- The use-set is now tightened via intersect with Γ.accessset, so we use
  -- intersect_mono_left to lift the subcapt subset.
  have hwiden :
      (C1.denot env m).intersect (Γ.useset.cs.denot env m)
          ∪ (Γ.consumeset.cs.denot env m).to_drop ⊆
        (C2.denot env m).intersect (Γ.useset.cs.denot env m)
          ∪ (Γ.consumeset.cs.denot env m).to_drop :=
    CapabilitySet.Subset.union_left
      (CapabilitySet.Subset.trans
        (CapabilitySet.intersect_mono_left hsubcapt_sem)
        CapabilitySet.Subset.union_right_left)
      CapabilitySet.Subset.union_right_right
  have h_eval_E1_at_C2 :=
    eval_capability_set_monotonic h_eval_E1 hwiden
  -- Use fundamental_subtyp to get E1 → E2 semantically.
  have hsubtyp_sem := fundamental_subtyp hclosed_E1 hclosed_E2 hsubtyp env m htyping
  have h_entails := Denot.imply_after_to_m_entails_after hsubtyp_sem
  -- Lift the val_denot from E1 to E2.
  apply eval_post_monotonic_general _ h_eval_E1_at_C2
  intro m' hsub e_ hval
  exact h_entails m' hsub e_ hval


lemma simple_val_not_pack {e : Exp s}
  (hsimple : e.IsSimpleVal)
  (hpack : e.IsPack) : False := by
  -- IsSimpleVal and IsPack apply to disjoint sets of constructors
  cases hsimple <;> cases hpack

lemma resolve_pack_eq {e : Exp {}} {m : Memory} {CS : CaptureSet {}} {x : Var .var {}}
  (hres : resolve m.heap e = some (.pack CS x))
  (hpack : e.IsPack) : e = .pack CS x := by
  -- If resolve returns a pack and e is a pack, then e equals that pack
  cases hpack
  -- e = .pack cs y for some cs, y
  rename_i cs y
  change some (Exp.pack cs y) = some (Exp.pack CS x) at hres
  cases hres
  rfl

theorem resolve_is_pack {e : Exp {}} {m : Memory}
  (hres : resolve m.heap e = some v)
  (hv : v.IsPack) : e.IsPack := by
  cases (resolve_var_or_val (store := m.heap) (e := e) (v := v) hres) with
  | inr heq =>
    rw [heq]
    exact hv
  | inl hvar =>
    obtain ⟨x, rfl⟩ := hvar
    cases x with
    | bound bv => cases bv
    | free fy =>
      cases hval : m.heap fy with
      | none =>
        simp only [resolve, hval] at hres
        contradiction
      | some cell =>
        cases cell with
        | val val =>
          simp only [resolve, hval] at hres
          cases hres
          exfalso
          exact simple_val_not_pack val.isVal hv
        | capability info =>
          simp only [resolve, hval] at hres
          contradiction
        | masked =>
          simp only [resolve, hval] at hres
          contradiction

theorem sem_typ_unpack
  {C1 C2 : CaptureSet s} {Γ Γ1 Γ2 : Ctx s} {t : Exp s} {T : Ty .capt (s,C)}
  {u : Exp (s,C,x)} {U : Ty .exi s}
  (hseq : Ctx.SeqComp Γ1 Γ2 Γ)
  (_hclosed_C1 : C1.IsClosed)
  (hclosed_C2 : C2.IsClosed)
  (ht : C1 # Γ1 ⊨ t : .exi T)
  (hu : ((C2.rename Rename.succ).rename Rename.succ ∪ (.cvar .epsilon (.there .here))) #
        (Γ2.push_cvar .consume .unbound,x:T) ⊨ u : (U.rename Rename.succ).rename Rename.succ) :
  C1 ∪ C2 # Γ ⊨ (Exp.unpack t u) : U := by
  intro env store hts hcompat
  -- Full restructuring of sem_typ_unpack for the new wider-budget shape is
  -- non-trivial: the body context `Γ2.push_cvar .consume .unbound,x:T` now
  -- contributes `consumeset` (one consume-unlocked cvar at depth 1), and the
  -- `SeqComp` widening `Γ1.consumeset, Γ2.consumeset ⊆ Γ.consumeset` is
  -- pending. Deferred along with `sem_typ_letin`.
  sorry

-- Helper: rename preserves subset
theorem CaptureSet.Subset.rename {C1 C2 : CaptureSet s1} {f : Rename s1 s2}
  (hsub : C1 ⊆ C2) : C1.rename f ⊆ C2.rename f := by
  induction hsub with
  | refl => exact .refl
  | union_left _ _ ih1 ih2 =>
    simp only [CaptureSet.rename]
    exact .union_left ih1 ih2
  | union_right_left _ ih =>
    simp only [CaptureSet.rename]
    exact .union_right_left ih
  | union_right_right _ ih =>
    simp only [CaptureSet.rename]
    exact .union_right_right ih
  | empty =>
    simp only [CaptureSet.rename]
    exact .empty

-- Helper: peaks is monotonic w.r.t. CaptureSet.Subset
theorem peaks_mono {Γ : Ctx s} {C1 C2 : CaptureSet s}
  (hsub : C1 ⊆ C2) : (C1.peaks Γ) ⊆ (C2.peaks Γ) := by
  induction hsub with
  | refl => exact .refl
  | union_left _ _ ih1 ih2 =>
    simp only [CaptureSet.peaks]
    exact .union_left ih1 ih2
  | union_right_left _ ih =>
    simp only [CaptureSet.peaks]
    exact .union_right_left ih
  | union_right_right _ ih =>
    simp only [CaptureSet.peaks]
    exact .union_right_right ih
  | empty =>
    simp only [CaptureSet.peaks]
    exact .empty

-- Helper: peaks commutes with rename and context extension (subset version)
theorem peaks_rename_succ_sub {Γ : Ctx s} {b : Binding s k} {C : CaptureSet s} :
  (C.peaks Γ).rename Rename.succ ⊆ (C.rename Rename.succ).peaks (Γ.push b) := by
  rw [CaptureSet.peaks_rename_succ_eq]
  exact .refl

-- Helper: peaks commutes with applyRO
theorem peaks_applyRO_comm (Γ : Ctx s) (C : CaptureSet s) :
  C.applyRO.peaks Γ = (C.peaks Γ).applyRO :=
  CaptureSet.peaks_applyRO_comm Γ C

-- Helper: peaks commutes with applyMut
theorem peaks_applyMut_comm {Γ : Ctx s} {C : CaptureSet s} {m : Mutability} :
  (C.applyMut m).peaks Γ = (C.peaks Γ).applyMut m := by
  cases m with
  | epsilon => simp only [CaptureSet.applyMut_epsilon]
  | ro =>
    simp only [CaptureSet.applyMut_ro]
    exact peaks_applyRO_comm Γ C

-- Helper: peaks is monotonic w.r.t. CaptureSet.CoveredBy
theorem peaks_mono_coveredby {Γ : Ctx s} {C1 C2 : CaptureSet s}
  (hcov : C1.CoveredBy C2) : (C1.peaks Γ).CoveredBy (C2.peaks Γ) := by
  induction hcov with
  | refl hm =>
    rw [peaks_applyMut_comm, peaks_applyMut_comm]
    exact .refl hm
  | empty =>
    simp only [CaptureSet.peaks]
    exact .empty
  | union_left _ _ ih1 ih2 =>
    simp only [CaptureSet.peaks]
    exact .union_left ih1 ih2
  | union_right_left _ ih =>
    simp only [CaptureSet.peaks]
    exact .union_right_left ih
  | union_right_right _ ih =>
    simp only [CaptureSet.peaks]
    exact .union_right_right ih

-- Helper: peaks commutes with rename and context extension (CoveredBy version)
theorem peaks_rename_succ_coveredby {Γ : Ctx s} {b : Binding s k} {C : CaptureSet s} :
  (C.peaks Γ).rename Rename.succ |>.CoveredBy <| (C.rename Rename.succ).peaks (Γ.push b) := by
  rw [CaptureSet.peaks_rename_succ_eq]
  exact .refl'

-- Helper: Subset implies CoveredBy (Subset is stricter)
theorem CaptureSet.Subset.coveredby {C1 C2 : CaptureSet s}
  (hsub : C1 ⊆ C2) : C1.CoveredBy C2 := by
  induction hsub with
  | refl => exact .refl'
  | empty => exact .empty
  | union_left _ _ ih1 ih2 => exact .union_left ih1 ih2
  | union_right_left _ ih => exact .union_right_left ih
  | union_right_right _ ih => exact .union_right_right ih

-- Helper: peaks of applyRO is covered by peaks (key lemma using CoveredBy)
theorem peaks_applyRO_coveredby {Γ : Ctx s} {C : CaptureSet s} :
  (C.applyRO.peaks Γ).CoveredBy (C.peaks Γ) := by
  rw [<-CaptureSet.applyMut_ro, peaks_applyMut_comm]
  -- Goal: ((C.peaks Γ).applyMut .ro).CoveredBy (C.peaks Γ)
  -- C.peaks Γ = (C.peaks Γ).applyMut .epsilon
  conv_rhs => rw [<-CaptureSet.applyMut_epsilon (cs := C.peaks Γ)]
  exact .refl Mutability.Le.ro_le

-- Helper: peaks respects applyRO monotonically (CoveredBy version)
theorem peaks_applyRO_mono_coveredby {Γ : Ctx s} {C1 C2 : CaptureSet s}
  (hcov : (C1.peaks Γ).CoveredBy (C2.peaks Γ)) :
  (C1.applyRO.peaks Γ).CoveredBy (C2.applyRO.peaks Γ) := by
  rw [<-CaptureSet.applyMut_ro, peaks_applyMut_comm]
  rw [<-CaptureSet.applyMut_ro, peaks_applyMut_comm]
  exact hcov.applyMut_mono

theorem ground_denot_applyMut_comm {C : CaptureSet {}} {m : Memory} {mu : Mutability} :
  (C.applyMut mu).ground_denot m = (C.ground_denot m).applyMut mu := by
  cases mu with
  | epsilon =>
    simp only [CaptureSet.applyMut, CapabilitySet.applyMut]
  | ro =>
    simp only [CaptureSet.applyMut, CapabilitySet.applyMut]
    exact ground_denot_applyRO_comm.symm

-- Helper: variable subcaptures its type's capture set with matching mutability
theorem var_subcapt_captureSet_applyMut
  (hlk : Γ.LookupVar x T) :
  Subcapt Γ (.var m (.bound x)) (T.captureSet.applyMut m) := by
  cases m with
  | epsilon =>
    simpa [CaptureSet.applyMut] using (Subcapt.sc_var (m := .epsilon) hlk)
  | ro =>
    simpa [CaptureSet.applyMut]
      using (Subcapt.sc_ro_mono (Subcapt.sc_var (m := .epsilon) hlk))

-- Helper: applyMut is monotonic for CapabilitySet.Subset
theorem CapabilitySet.applyMut_mono {C1 C2 : CapabilitySet} {m : Mutability}
  (hsub : C1 ⊆ C2) : C1.applyMut m ⊆ C2.applyMut m := by
  cases m with
  | epsilon => simp only [CapabilitySet.applyMut]; exact hsub
  | ro => simp only [CapabilitySet.applyMut]; exact CapabilitySet.applyRO_mono hsub

-- Helper: for well-typed variables, the denotation is bounded by the type's capture set
theorem var_denot_subset_captureSet_denot
  (hlk : Γ.LookupVar x T)
  (henv : EnvTyping Γ env H) :
  (CaptureSet.var m (.bound x)).denot env H ⊆ (T.captureSet.applyMut m).denot env H := by
  -- From typed_env_lookup_var_reachability:
  -- reachability_of_loc H.heap (env.lookup_var x).1 ⊆ T.captureSet.denot env H
  have hreach := typed_env_lookup_var_reachability henv hlk
  -- Apply applyMut m to both sides (monotonicity)
  have hreach_mut : (reachability_of_loc H.heap (env.lookup_var x).1).applyMut m ⊆
                    (T.captureSet.denot env H).applyMut m :=
    CapabilitySet.applyMut_mono (m := m) hreach
  -- LHS: (CaptureSet.var m (.bound x)).denot env H
  --    = (reachability_of_loc H.heap (env.lookup_var x).1).applyMut m
  simp only [CaptureSet.denot, CaptureSet.subst, Var.subst, Subst.from_TypeEnv,
             CaptureSet.ground_denot]
  -- RHS: (T.captureSet.applyMut m).denot env H
  --    = (T.captureSet.subst ...).applyMut m).ground_denot H   (by applyMut_subst)
  --    = (T.captureSet.subst ...).ground_denot H).applyMut m   (by ground_denot_applyMut_comm.symm)
  --    = (T.captureSet.denot env H).applyMut m
  simp only [CaptureSet.applyMut_subst]
  rw [ground_denot_applyMut_comm]
  exact hreach_mut

/-- From a `HasType` derivation of a bound variable, extract `Γ.IsClosed` and
    the syntactic accessibility of the variable's self-capture set.

    The proof inducts through `HasType.var` (which directly carries these
    facts) and `HasType.subtyp` (where the underlying typing still carries
    them). Left as `sorry` pending a careful inversion lemma. -/
theorem var_typing_extract_closed_accessible
    {Γ : Ctx s} {x : BVar s .var} {E : Ty .exi s}
    (ht : C # Γ ⊢ Exp.var (.bound x) : E) :
    Γ.IsClosed ∧ (CaptureSet.var .epsilon (.bound x)).accessible Γ := by
  sorry

/-- The fundamental theorem of semantic type soundness. -/
theorem fundamental
  (ht : C # Γ ⊢ e : T) :
  C # Γ ⊨ e : T := by
  have hclosed_e := HasType.exp_is_closed ht
  induction ht
  case var _ hx _ =>
    exact sem_typ_var hx
  case abs ih =>
    apply sem_typ_abs
    · exact hclosed_e
    · cases hclosed_e
      rename_i hclosed_cs hclosed_T1 hclosed_e0
      exact ih hclosed_e0
  case tabs ih =>
    apply sem_typ_tabs
    · exact hclosed_e
    · cases hclosed_e
      rename_i hclosed_cs hclosed_S hclosed_e0
      exact ih hclosed_e0
  case cabs ih =>
    apply sem_typ_cabs
    · exact hclosed_e
    · cases hclosed_e
      rename_i hclosed_cs hclosed_cb hclosed_e0
      exact ih hclosed_e0
  case pack ih =>
    rename_i hC_closed hcons hx_syn
    cases hclosed_e with | pack hcs_closed hx_closed =>
      cases hx_closed
      obtain ⟨hΓ, _⟩ := var_typing_extract_closed_accessible hx_syn
      apply sem_typ_pack
      · exact Exp.IsClosed.pack hcs_closed Var.IsClosed.bound
      · exact hΓ
      · exact hcons
      · exact ih (Exp.IsClosed.var Var.IsClosed.bound)
  case app =>
    rename_i hx_syn _hy_syn hx_ih hy_ih
    -- From closedness of (app x y), extract that x and y are closed variables
    cases hclosed_e with
    | app hx_closed hy_closed =>
      cases hx_closed
      cases hy_closed
      have ih_x := hx_ih (Exp.IsClosed.var Var.IsClosed.bound)
      have ih_y := hy_ih (Exp.IsClosed.var Var.IsClosed.bound)
      -- Extract Γ.IsClosed and accessibility from the syntactic typing of x.
      obtain ⟨hΓ, haccess⟩ := var_typing_extract_closed_accessible hx_syn
      exact sem_typ_app hΓ haccess ih_x ih_y
  case tapp =>
    rename_i _hS_closed hx_syn hx_ih
    cases hclosed_e with
    | tapp hx_closed hS_closed =>
      cases hx_closed
      have ih_x := hx_ih (Exp.IsClosed.var Var.IsClosed.bound)
      obtain ⟨hΓ, haccess⟩ := var_typing_extract_closed_accessible hx_syn
      exact sem_typ_tapp hΓ haccess ih_x
  case capp =>
    rename_i hD_closed hx_syn hx_ih
    cases hclosed_e with
    | capp hx_closed hD_closed_exp =>
      cases hx_closed
      have hx := hx_ih (Exp.IsClosed.var Var.IsClosed.bound)
      obtain ⟨hΓ, haccess⟩ := var_typing_extract_closed_accessible hx_syn
      exact sem_typ_capp hΓ haccess hD_closed_exp hx
  case invoke =>
    rename_i hx_syn _hy_syn ih_x ih_y
    cases hclosed_e with
    | app hx_closed hy_closed =>
      cases hx_closed
      cases hy_closed
      have hx := ih_x (Exp.IsClosed.var Var.IsClosed.bound)
      have hy := ih_y (Exp.IsClosed.var Var.IsClosed.bound)
      obtain ⟨hΓ, haccess⟩ := var_typing_extract_closed_accessible hx_syn
      exact sem_typ_invoke hΓ haccess hx hy
  case unit => exact sem_typ_unit
  case btrue => exact sem_typ_btrue
  case bfalse => exact sem_typ_bfalse
  case cond ht1 ht2 ht3 ih1 ih2 ih3 =>
    cases hclosed_e with
    | cond hclosed_guard hclosed_then hclosed_else =>
      exact sem_typ_cond
        (ih1 (Exp.IsClosed.var hclosed_guard)) (ih2 hclosed_then) (ih3 hclosed_else)
  case reader hΓ_closed hx =>
    exact sem_typ_reader hΓ_closed hx
  case alloc =>
    rename_i hx_syn hx_ih
    cases hclosed_e with
    | alloc hx_closed =>
      cases hx_closed
      exact sem_typ_alloc
        (hx_ih (Exp.IsClosed.var Var.IsClosed.bound))
  case drop =>
    rename_i hΓ_closed hx_syn hcons hx_ih
    cases hclosed_e with
    | drop hx_closed =>
      cases hx_closed
      exact sem_typ_drop
        (hx_ih (Exp.IsClosed.var Var.IsClosed.bound))
        hΓ_closed
        hcons
  case read =>
    rename_i hx_syn hx_ih
    cases hclosed_e with
    | read hx_closed =>
      cases hx_closed
      obtain ⟨hΓ, haccess⟩ := var_typing_extract_closed_accessible hx_syn
      exact sem_typ_read hΓ haccess
        (hx_ih (Exp.IsClosed.var Var.IsClosed.bound))
  case write =>
    rename_i hx_syn _hy_syn hx_ih hy_ih
    cases hclosed_e with
    | write hx_closed hy_closed =>
      cases hx_closed
      cases hy_closed
      obtain ⟨hΓ, haccess⟩ := var_typing_extract_closed_accessible hx_syn
      exact sem_typ_write hΓ haccess
        (hx_ih (Exp.IsClosed.var Var.IsClosed.bound))
        (hy_ih (Exp.IsClosed.var Var.IsClosed.bound))
  case letin =>
    rename_i hseq ht1_syn ht2_syn ht1_ih ht2_ih
    cases hclosed_e with
    | letin he1_closed he2_closed =>
      exact sem_typ_letin
        hseq
        (HasType.use_set_is_closed ht1_syn)
        (CaptureSet.rename_closed_inv (HasType.use_set_is_closed ht2_syn))
        (Exp.IsClosed.letin he1_closed he2_closed)
        (ht1_ih he1_closed)
        (ht2_ih he2_closed)
  case subtyp ht_syn hsubcapt hsubtyp hclosed_C2 hclosed_E2 ht_ih =>
    -- Get closedness of C1 and E1 from the syntactic typing derivation
    have hclosed_C1 := HasType.use_set_is_closed ht_syn
    have hclosed_E1 := HasType.type_is_closed ht_syn
    -- Apply the semantic subtyping lemma
    exact sem_typ_subtyp (ht_ih hclosed_e) hsubcapt hsubtyp
      hclosed_C1 hclosed_E1 hclosed_C2 hclosed_E2
  case unpack hseq ht_syn hu_syn ht_ih hu_ih =>
    cases hclosed_e with
    | unpack ht_closed hu_closed =>
      exact sem_typ_unpack
        hseq
        (HasType.use_set_is_closed ht_syn)
        (by
          have h := HasType.use_set_is_closed hu_syn
          cases h with
          | union h _ =>
            exact CaptureSet.rename_closed_inv (CaptureSet.rename_closed_inv h))
        (ht_ih ht_closed)
        (hu_ih hu_closed)

end Consume
