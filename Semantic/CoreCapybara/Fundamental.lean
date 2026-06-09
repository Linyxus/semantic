import Semantic.CoreCapybara.Denotation
import Semantic.CoreCapybara.Semantics
namespace CoreCapybara

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
        exact (Denot.equiv_to_imply (weaken_val_denot (env:=env0) (x:=n) (ps:=ps) (T:=T0))).1
          _ _ hts.1
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
          exact (Denot.equiv_to_imply (weaken_val_denot (env:=env0) (x:=n) (ps:=ps) (T:=T0))).1
            _ _ (b henv0)
    case tvar =>
      -- binding is .tvar Sb
      rename_i Sb
      match env with
      | .extend env0 (.tvar d) =>
        simp only [EnvTyping, TypeEnv.lookup_var] at hts ⊢
        obtain ⟨_, _, _, _, _, henv0⟩ := hts
        exact (Denot.equiv_to_imply (tweaken_val_denot (env:=env0) (d:=d) (T:=T0))).1
          _ _ (b henv0)
    case cvar =>
      -- binding is .cvar Bb
      rename_i Bb
      match env with
      | .extend env0 (.cvar cs cap) =>
        simp only [EnvTyping, TypeEnv.lookup_var] at hts ⊢
        obtain ⟨_, _, _, _, _, henv0⟩ := hts
        exact (Denot.equiv_to_imply (cweaken_val_denot (env:=env0) (cs:=cs) (cap:=cap) (T:=T0))).1
          _ _ (b henv0)
    case lock =>
      rename_i Ψ
      match env with
      | .extend env0 (.lock) =>
        simp only [EnvTyping, TypeEnv.lookup_var] at hts ⊢
        obtain ⟨_, henv0⟩ := hts
        exact (Denot.equiv_to_imply (lweaken_val_denot (env:=env0) (T:=T0))).1
          _ _ (b henv0)


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
    (.typ (T.refineCaptureSet (.var (.M .epsilon) (.bound x)))) := by
  intro env m hts _ _
  simp only [Ty.exi_exp_denot]
  apply Eval.eval_var
  simp only [Denot.as_mpost, Ty.exi_val_denot]
  -- From typed_env_lookup_var, we get that .var (.free n) satisfies T
  have h_lookup := typed_env_lookup_var hts hx
  have hpeaks :
      compute_peaks env T.captureSet = compute_peaks env (.var (.M .epsilon) (.bound x)) := by
    rw [← compute_peaks_correct hts T.captureSet]
    rw [← compute_peaks_correct hts (.var (.M .epsilon) (.bound x))]
    simpa using (CaptureSet.var_peaks (m := .M .epsilon) (x := x) (T := T) hx).symm
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
    simp [expand_captures, CaptureSet.ground_denot, ih1, ih2]

theorem typed_env_lookup_cvar_aux
  (hts : EnvTyping Γ env m)
  (hc : Ctx.LookupCVar Γ c a cb) :
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
  case there hc_prev ih =>
    rename_i cb' b
    cases b
    case var =>
      match env with
      | .extend env' (.var x ps) =>
        simp only [EnvTyping, TypeEnv.lookup_cvar] at hts ⊢
        obtain ⟨_, _, henv'⟩ := hts
        have hih := ih henv'
        have hcb := rebind_capturebound_denot (Rebind.weaken (env := env') (x := x) (ps := ps)) cb'
        rw [congrFun hcb m] at hih
        simpa [TypeEnv.extend_var] using hih
    case tvar =>
      match env with
      | .extend env' (.tvar d) =>
        simp only [EnvTyping, TypeEnv.lookup_cvar] at hts ⊢
        obtain ⟨_, _, _, _, _, henv'⟩ := hts
        have hih := ih henv'
        have hcb := rebind_capturebound_denot (Rebind.tweaken (env := env') (d := d)) cb'
        rw [congrFun hcb m] at hih
        simpa [TypeEnv.extend_tvar] using hih
    case cvar =>
      match env with
      | .extend env' (.cvar cs cap) =>
        simp only [EnvTyping, TypeEnv.lookup_cvar] at hts ⊢
        obtain ⟨_, _, _, _, _, henv'⟩ := hts
        have hih := ih henv'
        have hcb :=
          rebind_capturebound_denot
            (Rebind.cweaken (env := env') (cs := cs) (cap := cap)) cb'
        rw [congrFun hcb m] at hih
        simpa [TypeEnv.extend_cvar] using hih
    case lock =>
      match env with
      | .extend env' (.lock) =>
        simp only [EnvTyping, TypeEnv.lookup_cvar] at hts ⊢
        obtain ⟨_, henv'⟩ := hts
        have hih := ih henv'
        have hcb := rebind_capturebound_denot (Rebind.lweaken (env := env')) cb'
        rw [congrFun hcb m] at hih
        simpa [TypeEnv.extend_lock] using hih

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
    case cvar _ B =>
      match env with
      | .extend env' (.cvar cs cap) =>
        simp only [EnvTyping] at hts
        obtain ⟨_, _, _, hcap_eq, _, henv'⟩ := hts
        cases c with
        | here => exact hcap_eq
        | there c' => exact ih henv' c'
    case lock Ψ =>
      match env with
      | .extend env' (.lock) =>
        simp only [EnvTyping] at hts
        obtain ⟨_, henv'⟩ := hts
        cases c with
        | there c' => exact ih henv' c'

/-- The capture set of a closed capturing type is closed. -/
theorem Ty.captureSet_isClosed {T : Ty .capt s}
    (h : T.IsClosed) : T.captureSet.IsClosed := by
  cases T <;> simp only [Ty.captureSet]
  case top => exact CaptureSet.IsClosed.empty
  case tvar => exact CaptureSet.IsClosed.empty
  case arrow => cases h with | arrow _ hcs _ => exact hcs
  case poly => cases h with | poly _ hcs _ => exact hcs
  case cpoly => cases h with | cpoly _ hcs _ => exact hcs
  case modal => cases h with | modal hcs _ _ => exact hcs
  case cap => cases h with | cap hcs => exact hcs
  case cell => cases h with | cell hcs => exact hcs
  case reader => cases h with | reader hcs => exact hcs
  case unit => exact CaptureSet.IsClosed.empty
  case bool => exact CaptureSet.IsClosed.empty

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
    exact CaptureSet.applyRO_subst

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

/-- `applyDrop` on a ground capture set corresponds to `to_drop` at the
    capability level. -/
private theorem ground_denot_applyDrop_eq_to_drop {C : CaptureSet {}} {store : Memory} :
    (C.applyDrop).ground_denot store = (C.ground_denot store).to_drop := by
  induction C with
  | empty => rfl
  | union C1 C2 ih1 ih2 =>
    simp only [CaptureSet.applyDrop, CaptureSet.ground_denot, ih1, ih2]
    rfl
  | var m' v =>
    cases v with
    | bound x => cases x
    | free x =>
      simp only [CaptureSet.applyDrop, CaptureSet.ground_denot,
        CapabilitySet.applyAccess_drop, CapabilitySet.to_drop_applyAccess]
  | cvar _ c => cases c

/-- `applyAccess` on a `CaptureSet {}` commutes with `ground_denot`. -/
private theorem captureSet_ground_denot_applyAccess_comm
    {C : CaptureSet {}} {store : Memory} {a : Access} :
    (C.applyAccess a).ground_denot store = (C.ground_denot store).applyAccess a := by
  cases a with
  | M mty =>
    simp only [CaptureSet.applyAccess_M, CapabilitySet.applyAccess_M]
    exact captureSet_ground_denot_applyMut_comm
  | drop =>
    simp only [CaptureSet.applyAccess_drop, CapabilitySet.applyAccess_drop]
    exact ground_denot_applyDrop_eq_to_drop

/-- From `hasmem mu l (C.applyAccess a)`, extract a witness for `l` in `C`. -/
private theorem hasmem_of_applyAccess {C : CapabilitySet} {a : Access} {mu : CapMode}
    {l : Nat} (h : (C.applyAccess a).hasmem mu l) :
    ∃ mu', C.hasmem mu' l := by
  cases a with
  | M m =>
    simp only [CapabilitySet.applyAccess_M] at h
    exact hasmem_of_applyMut h
  | drop =>
    simp only [CapabilitySet.applyAccess_drop] at h
    obtain ⟨_, mu', hm⟩ := CapabilitySet.hasmem_to_drop_imp h
    exact ⟨mu', hm⟩

/-- Lift `hasmem` through `applyAccess`. -/
private theorem hasmem_applyAccess_lift {C : CapabilitySet} {mu : CapMode}
    {l : Nat} (h : C.hasmem mu l) (a : Access) :
    ∃ mu', (C.applyAccess a).hasmem mu' l := by
  cases a with
  | M m => simpa only [CapabilitySet.applyAccess_M] using hasmem_applyMut_lift h m
  | drop =>
    simp only [CapabilitySet.applyAccess_drop]
    exact ⟨.drop, CapabilitySet.hasmem_to_drop_of_hasmem h⟩

/-- `applyAccess` on a general `CaptureSet s` commutes with `denot`. -/
private theorem captureSet_denot_applyAccess_comm
    {s : Sig} {env : TypeEnv s} {C : CaptureSet s} {store : Memory} {a : Access} :
    (C.applyAccess a).denot env store = (C.denot env store).applyAccess a := by
  unfold CaptureSet.denot
  rw [CaptureSet.applyAccess_subst, captureSet_ground_denot_applyAccess_comm]

/-- If `Y` covers `mu` at `l`, and a `hasmem` witness in `reach.applyAccess a`
    forces the stability of `mu`, then `Y.applyAccess a` covers `mu` at `l`. -/
private theorem covers_applyAccess_of_covers_of_hasmem
    {Y reach : CapabilitySet} {a : Access} {mu : CapMode} {l l' : Nat}
    (hcov : Y.covers mu l) (hmem : (reach.applyAccess a).hasmem mu l') :
    (Y.applyAccess a).covers mu l := by
  cases a with
  | M mu0 =>
    cases mu0 with
    | epsilon => simpa only [CapabilitySet.applyAccess_M, CapabilitySet.applyMut] using hcov
    | ro =>
      simp only [CapabilitySet.applyAccess_M, CapabilitySet.applyMut] at hmem ⊢
      exact CapabilitySet.covers_applyRO_of_covers hcov (CapabilitySet.hasmem_applyRO_fixed hmem)
  | drop =>
    simp only [CapabilitySet.applyAccess_drop] at hmem ⊢
    obtain ⟨hmu_eq, _⟩ := CapabilitySet.hasmem_to_drop_imp hmem
    subst hmu_eq
    exact CapabilitySet.covers_to_drop_of_covers hcov

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
    {x : BVar s .var} {m : Access} {l : Nat} {mu : CapMode}
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
      ((reachability_of_loc store.heap n).applyAccess m) at hmem
    obtain ⟨mu0, hmem0⟩ := hasmem_of_applyAccess hmem
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
      hasmem_applyAccess_lift hmem_cp m
    -- ps.cs = compute_peaks env_rest T.captureSet via hps_eq + compute_peaks_correct.
    have hps_cs : ps.cs = compute_peaks env_rest T.captureSet := by
      rw [hps_eq]
      change T.captureSet.peaks Γ_rest = _
      exact compute_peaks_correct hts_rest T.captureSet
    -- Build the equality lifting the renamed compute_peaks back through applyMut m.
    have hcp_eq : compute_peaks (env_rest.extend_var n ps) (CaptureSet.var m (.bound BVar.here))
                = (compute_peaks (env_rest.extend_var n ps)
                    (T.captureSet.rename Rename.succ)).applyAccess m := by
      change ((ps.rename Rename.succ).cs.applyAccess m) = _
      change (ps.cs.rename Rename.succ).applyAccess m = _
      rw [hps_cs, hcp_rename]
      rfl
    refine ⟨mu_final, ?_⟩
    -- Convert env's `extend (.var n ps)` form to `extend_var n ps` (definitionally equal).
    change CapabilitySet.hasmem mu_final l
      ((compute_peaks (env_rest.extend_var n ps) (CaptureSet.var m (.bound BVar.here))).denot
        (env_rest.extend_var n ps) store)
    rw [hcp_eq, captureSet_denot_applyAccess_comm]
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
  | _, .push Γ_rest (.cvar _ B), .extend env_rest (.cvar cs cap), hts, hΓ, .there x', hmem =>
    obtain ⟨_, _, _, _, _, hts_rest⟩ := hts
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
  | _, .push Γ_rest (.lock Ψ), .extend env_rest (.lock), hts, hΓ, .there x', hmem =>
    obtain ⟨_, hts_rest⟩ := hts
    cases hΓ with | push hΓ_rest _ =>
    change CapabilitySet.hasmem mu l
      (((CaptureSet.var m (.bound x')).rename Rename.succ).denot
        (env_rest.extend_lock) store) at hmem
    have hC := rebind_captureset_denot
      (ρ := @Rebind.lweaken _ env_rest)
      (CaptureSet.var m (.bound x'))
    have hmem_rest : ((CaptureSet.var m (.bound x')).denot env_rest store).hasmem mu l := by
      rw [hC]; exact hmem
    obtain ⟨mu', hmem'⟩ := hasmem_compute_peaks_denot_var_bound hts_rest hΓ_rest hmem_rest
    refine ⟨mu', ?_⟩
    change CapabilitySet.hasmem mu' l
      ((compute_peaks (env_rest.extend_lock)
         ((CaptureSet.var m (.bound x')).rename Rename.succ)).denot
        (env_rest.extend_lock) store)
    have hcp_rename := rebind_compute_peaks
      (ρ := @Rebind.lweaken _ env_rest)
      (CaptureSet.var m (.bound x'))
    have hcp_denot := rebind_captureset_denot
      (ρ := @Rebind.lweaken _ env_rest)
      (compute_peaks env_rest (CaptureSet.var m (.bound x')))
    rw [hcp_denot, hcp_rename] at hmem'
    exact hmem'
termination_by 2 * (sizeOf Γ + sizeOf (CaptureSet.var m (.bound x)))
decreasing_by
  all_goals simp_wf
  all_goals try omega
  all_goals (have := sizeOf_captureSet_le T; omega)

end


/-- `.drop`-membership is preserved by `CapabilitySet.Subset`: the only mode-
    changing rule `cap_ro` is access-only, so it never produces a `.drop`. -/
private theorem hasmem_drop_of_subset {C1 C2 : CapabilitySet} {l : Nat}
    (hsub : C1 ⊆ C2) (h : C1.hasmem .drop l) : C2.hasmem .drop l := by
  induction hsub with
  | refl => exact h
  | empty => exact (CapabilitySet.not_hasmem_empty h).elim
  | trans _ _ ih1 ih2 => exact ih2 (ih1 h)
  | union_left _ _ ih1 ih2 =>
    cases h with
    | left h' => exact ih1 h'
    | right h' => exact ih2 h'
  | union_right_left => exact .left h
  | union_right_right => exact .right h
  | cap_ro => cases h

/-- `.drop`-membership reflects through `applyRO`: `applyRO` never *creates* a
    `.drop` (it only demotes access modes), so a `.drop` in `C.applyRO` was in `C`. -/
private theorem hasmem_drop_of_applyRO {C : CapabilitySet} {l : Nat} :
    (C.applyRO).hasmem .drop l → C.hasmem .drop l := by
  induction C with
  | empty => intro h; simp only [CapabilitySet.applyRO] at h; cases h
  | cap m' l' =>
    intro h
    simp only [CapabilitySet.applyRO] at h
    cases m' with
    | drop => simpa only [CapMode.applyRO] using h
    | access mu => simp only [CapMode.applyRO] at h; cases h
  | union C1 C2 ih1 ih2 =>
    intro h
    simp only [CapabilitySet.applyRO] at h
    cases h with
    | left h' => exact .left (ih1 h')
    | right h' => exact .right (ih2 h')

/-- `.drop`-membership reflects through `applyMut`: a mutability never *creates*
    a `.drop`, so a `.drop` in `C.applyMut m` was already in `C`. -/
private theorem hasmem_drop_of_applyMut {C : CapabilitySet} {m : Mutability} {l : Nat}
    (h : (C.applyMut m).hasmem .drop l) : C.hasmem .drop l := by
  cases m with
  | epsilon => exact h
  | ro => exact hasmem_drop_of_applyRO h

/-- `.drop`-membership survives `applyRO` (forward): `applyRO` fixes `.drop`. -/
private theorem hasmem_drop_applyRO_fwd {C : CapabilitySet} {l : Nat}
    (h : C.hasmem .drop l) : (C.applyRO).hasmem .drop l := by
  induction h with
  | here => simp only [CapabilitySet.applyRO, CapMode.applyRO]; exact .here
  | left _ ih => simp only [CapabilitySet.applyRO]; exact .left ih
  | right _ ih => simp only [CapabilitySet.applyRO]; exact .right ih

/-- `.drop`-membership survives `applyMut` (forward): a mutability fixes `.drop`. -/
private theorem hasmem_drop_applyMut_fwd {C : CapabilitySet} {m : Mutability} {l : Nat}
    (h : C.hasmem .drop l) : (C.applyMut m).hasmem .drop l := by
  cases m with
  | epsilon => exact h
  | ro => exact hasmem_drop_applyRO_fwd h


/-- Peak-level decomposition: any member of a *peaks-only* capture set's
    denotation comes from one of its capture-variable peaks. Pure structural
    induction on `PeaksOnly` (`empty | union | cvar`); the `cvar` leaf uses the
    `EnvTyping` bridge `(.cvar m c).denot = (lookup_cvar c).2.applyAccess m`. -/
private theorem peaks_denot_mem_decomp
    {s : Sig} {Γ : Ctx s} {env : TypeEnv s} {store : Memory}
    (hts : EnvTyping Γ env store)
    {P : CaptureSet s} (hP : P.PeaksOnly) {l : Nat} {mu : CapMode}
    (hmem : (P.denot env store).hasmem mu l) :
    ∃ (a : Access) (c : BVar s .cvar),
      (CaptureSet.cvar a c) ⊆ P ∧ ∃ mu', ((env.lookup_cvar c).2).hasmem mu' l := by
  induction hP generalizing mu with
  | empty =>
    simp only [CaptureSet.denot, CaptureSet.subst, CaptureSet.ground_denot] at hmem
    exact (CapabilitySet.not_hasmem_empty hmem).elim
  | union hP1 hP2 ih1 ih2 =>
    rename_i C1 C2
    have hunion : (C1.union C2).denot env store
        = C1.denot env store ∪ C2.denot env store := rfl
    rw [hunion] at hmem
    cases hmem with
    | left hm =>
      obtain ⟨a, c, hsub, mu', hmemc⟩ := ih1 hm
      exact ⟨a, c, hsub.union_right_left, mu', hmemc⟩
    | right hm =>
      obtain ⟨a, c, hsub, mu', hmemc⟩ := ih2 hm
      exact ⟨a, c, hsub.union_right_right, mu', hmemc⟩
  | cvar =>
    rename_i m c
    have hdenot :
        (CaptureSet.cvar m c).denot env store
          = ((env.lookup_cvar c).2).applyAccess m := by
      change ((env.lookup_cvar c).1.applyAccess m).ground_denot store = _
      rw [captureSet_ground_denot_applyAccess_comm, ← typed_env_cvar_cap_eq hts c]
    rw [hdenot] at hmem
    obtain ⟨mu', hmem'⟩ := hasmem_of_applyAccess hmem
    exact ⟨m, c, CaptureSet.Subset.refl, mu', hmem'⟩

/-- Drop-faithful peak decomposition: if no capture variable's stored capability
    holds a `.drop` (the `hcv` invariant), then a `.drop` member of a peaks-only
    denotation can only come from a `.drop`-*access* capture-variable peak. -/
private theorem peaks_denot_drop_decomp
    {s : Sig} {Γ : Ctx s} {env : TypeEnv s} {store : Memory}
    (hts : EnvTyping Γ env store)
    (hcv : ∀ (c : BVar s .cvar), ((env.lookup_cvar c).2).drop_free)
    {P : CaptureSet s} (hP : P.PeaksOnly) {l : Nat}
    (hmem : (P.denot env store).hasmem .drop l) :
    ∃ (c : BVar s .cvar),
      (CaptureSet.cvar .drop c) ⊆ P ∧ ∃ mu', ((env.lookup_cvar c).2).hasmem mu' l := by
  induction hP with
  | empty =>
    simp only [CaptureSet.denot, CaptureSet.subst, CaptureSet.ground_denot] at hmem
    exact (CapabilitySet.not_hasmem_empty hmem).elim
  | union hP1 hP2 ih1 ih2 =>
    rename_i C1 C2
    have hunion : (C1.union C2).denot env store
        = C1.denot env store ∪ C2.denot env store := rfl
    rw [hunion] at hmem
    cases hmem with
    | left hm =>
      obtain ⟨c, hsub, mu', hmemc⟩ := ih1 hm
      exact ⟨c, hsub.union_right_left, mu', hmemc⟩
    | right hm =>
      obtain ⟨c, hsub, mu', hmemc⟩ := ih2 hm
      exact ⟨c, hsub.union_right_right, mu', hmemc⟩
  | cvar =>
    rename_i a c
    have hdenot :
        (CaptureSet.cvar a c).denot env store
          = ((env.lookup_cvar c).2).applyAccess a := by
      change ((env.lookup_cvar c).1.applyAccess a).ground_denot store = _
      rw [captureSet_ground_denot_applyAccess_comm, ← typed_env_cvar_cap_eq hts c]
    rw [hdenot] at hmem
    cases a with
    | M μ =>
      simp only [CapabilitySet.applyAccess_M] at hmem
      exact absurd (hasmem_drop_of_applyMut hmem) (hcv c l)
    | drop =>
      simp only [CapabilitySet.applyAccess_drop] at hmem
      obtain ⟨_, mu', hmem'⟩ := CapabilitySet.hasmem_to_drop_imp hmem
      exact ⟨c, CaptureSet.Subset.refl, mu', hmem'⟩

/-- C2-side bridge: a member of `C.denot` (at any mode) traces to a
    capture-variable peak of `C` whose stored capability holds the location.
    Composes the (mode-lossy) `hasmem_compute_peaks_denot` with the peak
    decomposition, then rewrites `compute_peaks env C` back to `C.peaks Γ`. -/
private theorem mem_denot_peak
    {s : Sig} {Γ : Ctx s} {env : TypeEnv s} {store : Memory}
    (hts : EnvTyping Γ env store) (hΓ : Γ.IsClosed)
    {C : CaptureSet s} (hC : C.IsClosed) {l : Nat} {mu : CapMode}
    (hmem : (C.denot env store).hasmem mu l) :
    ∃ (a : Access) (c : BVar s .cvar),
      (CaptureSet.cvar a c) ⊆ CaptureSet.peaks Γ C ∧
        ∃ mu', ((env.lookup_cvar c).2).hasmem mu' l := by
  obtain ⟨mu', hmem'⟩ := hasmem_compute_peaks_denot hts hΓ C hC hmem
  obtain ⟨a, c, hsub, mu'', hmemc⟩ :=
    peaks_denot_mem_decomp hts (compute_peaks_is_peak env C) hmem'
  refine ⟨a, c, ?_, mu'', hmemc⟩
  rw [compute_peaks_correct hts C]
  exact hsub

/- Drop-faithful structural bridge: a `.drop` cap in `C.denot` is also a `.drop`
   cap in `(compute_peaks env C).denot`. The mode-lossy `hasmem_compute_peaks_denot`
   only transfers *some* mode; here we keep `.drop` exactly, which holds because
   the bound-variable / closure expansion routes through `val_denot_enforces_captures`
   (`reachability ⊆ T.captureSet.denot`) and `CapabilitySet.Subset` preserves
   `.drop`-membership. -/
mutual

private theorem drop_mem_compute_peaks
    {s : Sig} {Γ : Ctx s} {env : TypeEnv s} {store : Memory}
    (hts : EnvTyping Γ env store) (hΓ : Γ.IsClosed)
    (C : CaptureSet s) (hC : C.IsClosed) {l : Nat}
    (hmem : (C.denot env store).hasmem .drop l) :
    ((compute_peaks env C).denot env store).hasmem .drop l := by
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
      have hm' := drop_mem_compute_peaks hts hΓ C1 hC1 hm
      change ((compute_peaks env C1).denot env store
              ∪ (compute_peaks env C2).denot env store).hasmem .drop l
      exact .left hm'
    | .right hm =>
      have hm' := drop_mem_compute_peaks hts hΓ C2 hC2 hm
      change ((compute_peaks env C1).denot env store
              ∪ (compute_peaks env C2).denot env store).hasmem .drop l
      exact .right hm'
  | .cvar m c, _, hmem =>
    change ((CaptureSet.cvar m c).denot env store).hasmem .drop l
    exact hmem
  | .var m (.bound x), _, hmem =>
    exact drop_mem_compute_peaks_var_bound hts hΓ hmem
  | .var m (.free n), hC, _ =>
    cases hC
termination_by 2 * (sizeOf Γ + sizeOf C) + 1

private theorem drop_mem_compute_peaks_var_bound
    {s : Sig} {Γ : Ctx s} {env : TypeEnv s} {store : Memory}
    (hts : EnvTyping Γ env store) (hΓ : Γ.IsClosed)
    {x : BVar s .var} {m : Access} {l : Nat}
    (hmem : ((CaptureSet.var m (.bound x)).denot env store).hasmem .drop l) :
    ((compute_peaks env (CaptureSet.var m (.bound x))).denot env store).hasmem .drop l := by
  match s, Γ, env, hts, hΓ, x, hmem with
  | _, .empty, .empty, _, _, x, _ => cases x
  | _, .push Γ_rest (.var T), .extend env_rest (.var n ps), hts, hΓ, .here, hmem =>
    obtain ⟨hval_T, hps_eq, hts_rest⟩ := hts
    cases hΓ with | push hΓ_rest hb =>
    cases hb with | var hT =>
    have hT_cs : T.captureSet.IsClosed := Ty.captureSet_isClosed hT
    have hreach_sub : reachability_of_loc store.heap n ⊆ T.captureSet.denot env_rest store := by
      have h := val_denot_enforces_captures hts_rest (.var (.free n)) hval_T
      simp only [resolve_reachability] at h
      exact h
    have hps_cs : ps.cs = compute_peaks env_rest T.captureSet := by
      rw [hps_eq]
      change T.captureSet.peaks Γ_rest = _
      exact compute_peaks_correct hts_rest T.captureSet
    have hcp_rename := rebind_compute_peaks
      (ρ := @Rebind.weaken _ env_rest n ps) T.captureSet
    have hcp_denot := rebind_captureset_denot
      (ρ := @Rebind.weaken _ env_rest n ps)
      (compute_peaks env_rest T.captureSet)
    have hcp_eq : compute_peaks (env_rest.extend_var n ps) (CaptureSet.var m (.bound BVar.here))
                = (compute_peaks (env_rest.extend_var n ps)
                    (T.captureSet.rename Rename.succ)).applyAccess m := by
      change ((ps.rename Rename.succ).cs.applyAccess m) = _
      change (ps.cs.rename Rename.succ).applyAccess m = _
      rw [hps_cs, hcp_rename]
      rfl
    change CapabilitySet.hasmem .drop l
      ((reachability_of_loc store.heap n).applyAccess m) at hmem
    change CapabilitySet.hasmem .drop l
      ((compute_peaks (env_rest.extend_var n ps)
        (CaptureSet.var m (.bound BVar.here))).denot (env_rest.extend_var n ps) store)
    rw [hcp_eq, captureSet_denot_applyAccess_comm]
    cases m with
    | M μ =>
      rw [CapabilitySet.applyAccess_M] at hmem ⊢
      have hmem0 := hasmem_drop_of_applyMut hmem
      have hmem_T := hasmem_drop_of_subset hreach_sub hmem0
      have hmem_cp := drop_mem_compute_peaks hts_rest hΓ_rest T.captureSet hT_cs hmem_T
      rw [hcp_denot, hcp_rename] at hmem_cp
      exact hasmem_drop_applyMut_fwd hmem_cp
    | drop =>
      rw [CapabilitySet.applyAccess_drop] at hmem ⊢
      obtain ⟨_, mu0, hmem0⟩ := CapabilitySet.hasmem_to_drop_imp hmem
      obtain ⟨mu1, hmem_T⟩ := hasmem_of_capabilitySet_subset hreach_sub hmem0
      obtain ⟨mu2, hmem_cp⟩ :=
        hasmem_compute_peaks_denot hts_rest hΓ_rest T.captureSet hT_cs hmem_T
      rw [hcp_denot, hcp_rename] at hmem_cp
      exact CapabilitySet.hasmem_to_drop_of_hasmem hmem_cp
  | _, .push Γ_rest (.var T), .extend env_rest (.var n ps), hts, hΓ, .there x', hmem =>
    obtain ⟨_, _, hts_rest⟩ := hts
    cases hΓ with | push hΓ_rest _ =>
    change CapabilitySet.hasmem .drop l
      (((CaptureSet.var m (.bound x')).rename Rename.succ).denot
        (env_rest.extend_var n ps) store) at hmem
    have hC := rebind_captureset_denot
      (ρ := @Rebind.weaken _ env_rest n ps)
      (CaptureSet.var m (.bound x'))
    have hmem_rest : ((CaptureSet.var m (.bound x')).denot env_rest store).hasmem .drop l := by
      rw [hC]; exact hmem
    have hmem' := drop_mem_compute_peaks_var_bound hts_rest hΓ_rest hmem_rest
    change CapabilitySet.hasmem .drop l
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
    change CapabilitySet.hasmem .drop l
      (((CaptureSet.var m (.bound x')).rename Rename.succ).denot
        (env_rest.extend_tvar d) store) at hmem
    have hC := rebind_captureset_denot
      (ρ := @Rebind.tweaken _ env_rest d)
      (CaptureSet.var m (.bound x'))
    have hmem_rest : ((CaptureSet.var m (.bound x')).denot env_rest store).hasmem .drop l := by
      rw [hC]; exact hmem
    have hmem' := drop_mem_compute_peaks_var_bound hts_rest hΓ_rest hmem_rest
    change CapabilitySet.hasmem .drop l
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
  | _, .push Γ_rest (.cvar _ B), .extend env_rest (.cvar cs cap), hts, hΓ, .there x', hmem =>
    obtain ⟨_, _, _, _, _, hts_rest⟩ := hts
    cases hΓ with | push hΓ_rest _ =>
    change CapabilitySet.hasmem .drop l
      (((CaptureSet.var m (.bound x')).rename Rename.succ).denot
        (env_rest.extend_cvar cs cap) store) at hmem
    have hC := rebind_captureset_denot
      (ρ := @Rebind.cweaken _ env_rest cs cap)
      (CaptureSet.var m (.bound x'))
    have hmem_rest : ((CaptureSet.var m (.bound x')).denot env_rest store).hasmem .drop l := by
      rw [hC]; exact hmem
    have hmem' := drop_mem_compute_peaks_var_bound hts_rest hΓ_rest hmem_rest
    change CapabilitySet.hasmem .drop l
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
  | _, .push Γ_rest (.lock Ψ), .extend env_rest (.lock), hts, hΓ, .there x', hmem =>
    obtain ⟨_, hts_rest⟩ := hts
    cases hΓ with | push hΓ_rest _ =>
    change CapabilitySet.hasmem .drop l
      (((CaptureSet.var m (.bound x')).rename Rename.succ).denot
        (env_rest.extend_lock) store) at hmem
    have hC := rebind_captureset_denot
      (ρ := @Rebind.lweaken _ env_rest)
      (CaptureSet.var m (.bound x'))
    have hmem_rest : ((CaptureSet.var m (.bound x')).denot env_rest store).hasmem .drop l := by
      rw [hC]; exact hmem
    have hmem' := drop_mem_compute_peaks_var_bound hts_rest hΓ_rest hmem_rest
    change CapabilitySet.hasmem .drop l
      ((compute_peaks (env_rest.extend_lock)
         ((CaptureSet.var m (.bound x')).rename Rename.succ)).denot
        (env_rest.extend_lock) store)
    have hcp_rename := rebind_compute_peaks
      (ρ := @Rebind.lweaken _ env_rest)
      (CaptureSet.var m (.bound x'))
    have hcp_denot := rebind_captureset_denot
      (ρ := @Rebind.lweaken _ env_rest)
      (compute_peaks env_rest (CaptureSet.var m (.bound x')))
    rw [hcp_denot, hcp_rename] at hmem'
    exact hmem'
termination_by 2 * (sizeOf Γ + sizeOf (CaptureSet.var m (.bound x)))
decreasing_by
  all_goals simp_wf
  all_goals try omega
  all_goals (have := sizeOf_captureSet_le T; omega)

end


/-- A `.drop` cap in `C.denot` traces to a `.drop`-access capture-variable peak,
    **provided** no capture variable's stored capability itself holds a `.drop`
    (`hcv`). That invariant is what the `is_valid_inst` discipline on capture-
    parameter instantiation buys: capture variables are bound only to drop-free
    instances, so a runtime `.drop` can only come from an explicit `.drop` access. -/
private theorem drop_denot_peak
    {s : Sig} {Γ : Ctx s} {env : TypeEnv s} {store : Memory}
    (hts : EnvTyping Γ env store) (hΓ : Γ.IsClosed)
    (hcv : ∀ (c : BVar s .cvar), ((env.lookup_cvar c).2).drop_free)
    {C : CaptureSet s} (hC : C.IsClosed) {l : Nat}
    (hmem : (C.denot env store).hasmem .drop l) :
    ∃ (c : BVar s .cvar),
      (CaptureSet.cvar .drop c) ⊆ CaptureSet.peaks Γ C ∧
        ∃ mu', ((env.lookup_cvar c).2).hasmem mu' l := by
  have hbridge : ((compute_peaks env C).denot env store).hasmem .drop l :=
    drop_mem_compute_peaks hts hΓ C hC hmem
  obtain ⟨c, hsub, mu', hmemc⟩ :=
    peaks_denot_drop_decomp hts hcv (compute_peaks_is_peak env C) hbridge
  refine ⟨c, ?_, mu', hmemc⟩
  rw [compute_peaks_correct hts C]
  exact hsub


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


/-- Converts the `SemanticTyping` form into the `Ty.exi_exp_denot` form used by
many call sites. Under the new budget model the budget is exactly `C.denot ρ m`
on both sides, so this is just unfolding `SemanticTyping`/`exi_exp_denot`. -/
theorem semtyp_to_exi_exp_denot
    {s : Sig} {C : CaptureSet s} {Γ : Ctx s} {e : Exp s} {E : Ty .exi s}
    {ρ : TypeEnv s} {m : Memory}
    (ht : C # Γ ⊨ e : E)
    (hts : EnvTyping Γ ρ m)
    (hdsep : DroppableSep Γ ρ)
    (hcompat : m.is_compatible (C.denot ρ m)) :
    Ty.exi_exp_denot ρ E (C.denot ρ m) m (e.subst (Subst.from_TypeEnv ρ)) :=
  ht ρ m hts hdsep hcompat

/-! ### Preservation of `DroppableSep` under environment extension

`DroppableSep` quantifies only over `.can_drop` capture variables. Extending the
context with a `var`/`tvar` binding, or with an `.access_only` cvar, introduces
no new droppable cvar, so separation is preserved verbatim (every cvar in the
extended context is `.there`-shifted, and both `lookup_authority` and the stored
capability reduce definitionally to the underlying context/env). Extending with a
fresh `.can_drop` cvar additionally requires the new capability to be disjoint
from every existing droppable cvar — a freshness obligation supplied by the
caller. -/

theorem DroppableSep.extend_var {Γ : Ctx s} {env : TypeEnv s} {T : Ty .capt s}
    {n : Nat} {ps : PeakSet s} (h : DroppableSep Γ env) :
    DroppableSep (Γ.push_var T) (env.extend_var n ps) := by
  intro c1 c2 hne ha1
  cases c1 with
  | there c1' => cases c2 with
    | there c2' => exact h c1' c2' (fun heq => hne (by rw [heq])) ha1

theorem DroppableSep.extend_tvar {Γ : Ctx s} {env : TypeEnv s} {S : PureTy s}
    {d : Denot} (h : DroppableSep Γ env) :
    DroppableSep (Γ.push_tvar S) (env.extend_tvar d) := by
  intro c1 c2 hne ha1
  cases c1 with
  | there c1' => cases c2 with
    | there c2' => exact h c1' c2' (fun heq => hne (by rw [heq])) ha1

theorem DroppableSep.extend_cvar_access_only {Γ : Ctx s} {env : TypeEnv s}
    {cb : CaptureBound s} {cs : CaptureSet {}} {cap : CapabilitySet}
    (h : DroppableSep Γ env)
    (hfresh : ∀ c, Γ.lookup_authority c = .can_drop →
      CapabilitySet.disjoint (env.lookup_cvar c).2 cap) :
    DroppableSep (Γ.push_cvar .access_only cb) (env.extend_cvar cs cap) := by
  intro c1 c2 hne ha1
  cases c1 with
  | here =>
    exact Authority.noConfusion (show Authority.access_only = Authority.can_drop from ha1)
  | there c1' => cases c2 with
    | here =>
      -- existing droppable `c1'` vs. the new (access-only) cvar
      exact hfresh c1' ha1
    | there c2' => exact h c1' c2' (fun heq => hne (by rw [heq])) ha1

theorem DroppableSep.extend_cvar_can_drop {Γ : Ctx s} {env : TypeEnv s}
    {cb : CaptureBound s} {cs : CaptureSet {}} {cap : CapabilitySet}
    (h : DroppableSep Γ env)
    (hfresh : ∀ c, CapabilitySet.disjoint cap (env.lookup_cvar c).2) :
    DroppableSep (Γ.push_cvar .can_drop cb) (env.extend_cvar cs cap) := by
  intro c1 c2 hne ha1
  cases c1 with
  | here => cases c2 with
    | here => exact absurd rfl hne
    | there c2' =>
      -- new (droppable) cvar vs. an existing cvar `c2'`
      exact hfresh c2'
  | there c1' => cases c2 with
    | here =>
      -- symmetric: existing droppable `c1'` vs. the new cvar
      exact (hfresh c1').symm
    | there c2' => exact h c1' c2' (fun heq => hne (by rw [heq])) ha1

theorem DroppableSep.extend_lock {Γ : Ctx s} {env : TypeEnv s} {Ψ : SepCtx s}
    (h : DroppableSep Γ env) :
    DroppableSep (Γ.push_lock Ψ) (env.extend_lock) := by
  intro c1 c2 hne ha1
  cases c1 with
  | there c1' => cases c2 with
    | there c2' => exact h c1' c2' (fun heq => hne (by rw [heq])) ha1

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
  (ht : Cf.rename Rename.succ # Γ,x:T1 ⊨ e : T2) :
  ∅ # Γ ⊨ Exp.abs Cf T1 e : (T1.arrow Cf T2).typ := by
  intro env store hts hdsep _
  simp only [Ty.exi_exp_denot]
  apply Eval.eval_val
  · simp only [Exp.subst]; constructor
  · simp only [Denot.as_mpost, Ty.exi_val_denot, Ty.val_denot]
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
                EnvTyping (Γ,x:T1) (env.extend_var arg ps) m' := by
                constructor
                · exact harg
                · constructor
                  · exact (compute_peakset_correct hts T1.captureSet).symm
                  · exact env_typing_monotonic hts hsub
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
              -- New budget is exactly `C.denot`, so the hypothesis applies directly.
              have htyped := ht (env.extend_var arg ps) m' henv hdsep.extend_var hcompat'
              -- Show the body's authority equals the closure's authority.
              rw [← authority_eq_expand_captures hcap_rename
                    (closed_capture_denot_monotonic hCf_closed hts hsub)]
              exact htyped


theorem sem_typ_tabs {T : Ty TySort.exi (s,X)} {Cf : CaptureSet s} {S : PureTy s}
  (hclosed_tabs : (Exp.tabs Cf S e).IsClosed)
  (ht : Cf.rename Rename.succ # (Γ,X<:S) ⊨ e : T) :
  ∅ # Γ ⊨ Exp.tabs Cf S e : (S.core.poly Cf T).typ := by
  intro env store hts hdsep _
  simp only [Ty.exi_exp_denot]
  apply Eval.eval_val
  · simp only [Exp.subst]; constructor
  · simp only [Denot.as_mpost, Ty.exi_val_denot, Ty.val_denot]
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
              have henv : EnvTyping (Γ,X<:S) (env.extend_tvar denot) m' := by
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
                        · exact env_typing_monotonic hts hsub
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
              -- New budget is exactly `C.denot`, so the hypothesis applies directly.
              have htyped := ht (env.extend_tvar denot) m' henv hdsep.extend_tvar hcompat'
              -- Show the authority matches
              rw [← authority_eq_expand_captures hcap_rename
                    (closed_capture_denot_monotonic hCf_closed hts hsub)]
              exact htyped


theorem sem_typ_cabs {T : Ty TySort.exi (s,C)} {Cf : CaptureSet s} {cb : CaptureBound s}
  (hclosed_cabs : (Exp.cabs Cf cb e).IsClosed)
  (ht : Cf.rename Rename.succ # Γ,C[.access_only]<:cb ⊨ e : T) :
  ∅ # Γ ⊨ Exp.cabs Cf cb e : (Ty.cpoly cb Cf T).typ := by
  intro env store hts hdsep _
  simp only [Ty.exi_exp_denot]
  apply Eval.eval_val
  · simp only [Exp.subst]; constructor
  · simp only [Denot.as_mpost, Ty.exi_val_denot, Ty.val_denot]
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
              intro m' CS hwf hdf hsub hcompat hsub_bound
              have hkey := @Exp.from_TypeEnv_weaken_open_cvar s env CS e
              refine hkey ▸ ?_
              -- Build EnvTyping
              have henv : EnvTyping (Γ,C[.access_only]<:cb)
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
                constructor
                · exact hdf  -- `CS.ground_denot m'` drop-free (cpoly denotation precondition)
                · exact env_typing_monotonic hts hsub
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
              -- New budget is exactly `C.denot`, so the hypothesis applies directly.
              -- GAP: the capture argument `CS` supplied to this
              -- abstraction is disjoint from every existing droppable cvar — the
              -- environment-separation invariant that a borrowed capture does not
              -- alias a live owned (droppable) capability. Same gap family as
              -- `captureSet_seqcomp_denot`.
              have hfresh_cabs : ∀ c, Γ.lookup_authority c = .can_drop →
                  CapabilitySet.disjoint (env.lookup_cvar c).2 (CS.ground_denot m') := by
                sorry
              have htyped :=
                ht (env.extend_cvar CS (cap := CS.ground_denot m')) m' henv
                  (hdsep.extend_cvar_access_only hfresh_cabs) hcompat'
              -- Show capability sets match (using hcap_rename and hCf_closed above)
              rw [← authority_eq_expand_captures hcap_rename
                    (closed_capture_denot_monotonic hCf_closed hts hsub)]
              rw [Subst.from_TypeEnv_extend_cvar_cap_irrelevant
                (cap := .empty) (cap' := CS.ground_denot m')]
              exact htyped

theorem sem_typ_pack
  {T : Ty .capt (s,C)} {cs : CaptureSet s} {x : Var .var s} {Γ : Ctx s}
  (hclosed_e : (Exp.pack cs x).IsClosed)
  (hΓ : Γ.IsClosed)
  (hvalid_cs : cs.AccessOnly Γ)
  (ht : {} # Γ ⊨ Exp.var x : (T.subst (Subst.openCVar cs)).typ) :
  cs.applyAccess .drop # Γ ⊨ Exp.pack cs x : T.exi := by
  intro env store hts hdsep _
  -- pack is no longer a simple value; use eval_pack instead
  have hsubst : (Exp.pack cs x).subst (Subst.from_TypeEnv env) =
         Exp.pack (cs.subst (Subst.from_TypeEnv env)) (x.subst (Subst.from_TypeEnv env)) := by
    simp only [Exp.subst]
  have hclosed_cs : cs.IsClosed := by
    cases hclosed_e with
    | pack hcs_closed _hx_closed => exact hcs_closed
  simp only [Ty.exi_exp_denot, List.empty_eq]
  rw [hsubst]
  apply Eval.eval_pack
  · -- `eval_pack` now needs `(cs'.reachability store).to_drop ⊆ budget`, and the
    -- budget is `cs.applyAccess .drop`. Both sides reduce to `(cs.denot env store).to_drop`:
    -- the reachability of the (substituted) `cs` is `cs.denot env store`, and
    -- `(cs.applyAccess .drop).denot = (cs.denot env store).to_drop`.
    rw [← CaptureSet.ground_denot_eq_reachability,
      captureSet_denot_applyAccess_comm, CapabilitySet.applyAccess_drop]
    exact CapabilitySet.Subset.refl
  · simp only [Denot.as_mpost, Ty.exi_val_denot]
    -- Goal: CS.WfInHeap ∧ capt_val_denot (env.extend_cvar ...) T store ...
    constructor
    · -- Well-formedness of the capture set
      exact CaptureSet.wf_subst (CaptureSet.wf_of_closed hclosed_cs) (from_TypeEnv_wf_in_heap hts)
    · -- From ht, we have semantic typing for x at type T.subst (Subst.openCVar cs)
      have hcompat0 : store.is_compatible ((∅ : CaptureSet s).denot env store) := by
        simpa using Memory.is_compatible_empty store
      have hx := ht env store hts hdsep hcompat0
      simp only [Ty.exi_exp_denot, List.empty_eq] at hx
      have hvar : (Exp.var x).subst (Subst.from_TypeEnv env) =
             Exp.var (x.subst (Subst.from_TypeEnv env)) := by
        cases x <;> simp only [Exp.subst, Var.subst]
      rw [hvar] at hx
      cases hx
      case eval_var hQ =>
        have hQ' : Ty.val_denot env (T.subst (Subst.openCVar cs)) store
            (Exp.var (x.subst (Subst.from_TypeEnv env))) := by
          simpa only [Denot.as_mpost, Ty.exi_val_denot] using hQ
        let cs' := cs.subst (Subst.from_TypeEnv env)
        have hretype := open_carg_val_denot (env := env) (cap := cs'.ground_denot store)
          (C := cs) (T := T)
        refine ⟨?_, (hretype store (Exp.var (x.subst (Subst.from_TypeEnv env)))).mpr hQ'⟩
        -- A `.drop` in `cs`'s runtime image traces (via `drop_denot_peak`) to a
        -- `.drop`-access peak of `cs`, contradicting `cs.is_valid_inst Γ`.
        intro l hmem
        have hmem' : (cs.denot env store).hasmem .drop l := hmem
        obtain ⟨c, hsub, _⟩ :=
          drop_denot_peak hts hΓ (envtyping_lookup_cvar_drop_free hts) hclosed_cs hmem'
        exact hvalid_cs c hsub
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
      Ty.exi_exp_denot
        (env.extend_var arg (compute_peakset env T1.captureSet))
        T2 (expand_captures store.heap cs') m'
        (e0.subst (Subst.openVar (.free arg)))) := by
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
      Ty.exi_exp_denot
        (env.extend_tvar denot)
        T2 (expand_captures store.heap cs') m'
        (e0.subst (Subst.openTVar .top))) := by
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
      (CS.ground_denot m').drop_free ->
      m'.subsumes store ->
      m'.is_compatible (expand_captures store.heap cs') ->
      ((CS.denot TypeEnv.empty m').BoundedBy (B.denot env m')) ->
      Ty.exi_exp_denot
        (env.extend_cvar CS (cap := CS.ground_denot m'))
        T (expand_captures store.heap cs') m'
        (e0.subst (Subst.openCVar CS))) := by
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

theorem SepCtx.Has.subst
    {K : SepCtx s1} {σ : Subst s1 s2}
    (h : SepCtx.Has K C m) :
    SepCtx.Has (K.subst σ) (C.subst σ) m := by
  induction h with
  | here =>
    change SepCtx.Has (.cons _ _ _) _ _
    exact .here
  | there h ih =>
    change SepCtx.Has (.cons _ _ _) _ _
    exact .there ih

theorem SepCtx.Has.subst_inv
    {K : SepCtx s1} {σ : Subst s1 s2}
    (h : SepCtx.Has (K.subst σ) C m) :
    ∃ C0, C = C0.subst σ ∧ SepCtx.Has K C0 m := by
  induction K with
  | empty =>
    cases h
  | cons K C0 m0 ih =>
    change SepCtx.Has (.cons (K.subst σ) (C0.subst σ) m0) C m at h
    cases h with
    | here =>
      exact ⟨C0, rfl, .here⟩
    | there h' =>
      obtain ⟨C1, hC1, hh⟩ := ih h'
      exact ⟨C1, hC1, .there hh⟩

theorem SepCtx.HasTwoDistinct.subst
    {K : SepCtx s1} {σ : Subst s1 s2}
    (h : SepCtx.HasTwoDistinct K C1 m1 C2 m2) :
    SepCtx.HasTwoDistinct (K.subst σ) (C1.subst σ) m1 (C2.subst σ) m2 := by
  induction h with
  | here_there hhas =>
    change SepCtx.HasTwoDistinct (.cons _ _ _) _ _ _ _
    exact .here_there (hhas.subst)
  | there h ih =>
    change SepCtx.HasTwoDistinct (.cons _ _ _) _ _ _ _
    exact .there ih
  | symm h ih =>
    exact .symm ih

theorem SepCtx.HasTwoDistinct.subst_inv
    {K : SepCtx s1} {σ : Subst s1 s2}
    (h : SepCtx.HasTwoDistinct (K.subst σ) C1 m1 C2 m2) :
    ∃ D1 D2,
      C1 = D1.subst σ ∧
      C2 = D2.subst σ ∧
      SepCtx.HasTwoDistinct K D1 m1 D2 m2 := by
  generalize he0 : K.subst σ = K0 at h
  induction h generalizing K with
  | here_there hhas =>
    cases K with
    | empty =>
      simp [SepCtx.subst] at he0
    | cons K1 C0 m0 =>
      simp only [SepCtx.subst, SepCtx.cons.injEq] at he0
      rcases he0 with ⟨hK, hC, hm⟩
      subst hK hC hm
      obtain ⟨D2, hD2, hh⟩ := SepCtx.Has.subst_inv hhas
      exact ⟨C0, D2, rfl, hD2, .here_there hh⟩
  | there a ih =>
    cases K with
    | empty => simp [SepCtx.subst] at he0
    | cons K1 C0 m0 =>
      simp only [SepCtx.subst, SepCtx.cons.injEq] at he0
      rcases he0 with ⟨hK, hC, hm⟩
      subst hC hm
      obtain ⟨D1, D2, hD1, hD2, hh⟩ := ih hK
      exact ⟨D1, D2, hD1, hD2, .there hh⟩
  | symm a ih =>
    obtain ⟨D2, D1, hD2, hD1, hh⟩ := ih he0
    exact ⟨D1, D2, hD1, hD2, .symm hh⟩

theorem TypeEnv.satisfy_subst_iff
    {env : TypeEnv s} {Ψ : SepCtx s} {m : Memory} :
    env.Satisfy Ψ m ↔ TypeEnv.empty.Satisfy (Ψ.subst (Subst.from_TypeEnv env)) m := by
  constructor
  · intro hsat
    constructor
    · intro C mode hhas
      obtain ⟨C0, rfl, hhas0⟩ := SepCtx.Has.subst_inv hhas
      simpa [CaptureSet.denot, Subst.from_TypeEnv_empty, CaptureSet.subst_id] using
        hsat.wf C0 mode hhas0
    · intro C mode hhas
      obtain ⟨C0, rfl, hhas0⟩ := SepCtx.Has.subst_inv hhas
      simpa [CaptureSet.denot, Subst.from_TypeEnv_empty, CaptureSet.subst_id] using
        hsat.kind C0 mode hhas0
    · intro C1 m1 C2 m2 hdistinct
      obtain ⟨D1, D2, rfl, rfl, hdistinct0⟩ := SepCtx.HasTwoDistinct.subst_inv hdistinct
      simpa [CaptureSet.denot, Subst.from_TypeEnv_empty, CaptureSet.subst_id] using
        hsat.sep D1 m1 D2 m2 hdistinct0
  · intro hsat
    constructor
    · intro C mode hhas
      have hhas' := hhas.subst (σ := Subst.from_TypeEnv env)
      simpa [CaptureSet.denot, Subst.from_TypeEnv_empty, CaptureSet.subst_id] using
        hsat.wf (C.subst (Subst.from_TypeEnv env)) mode hhas'
    · intro C mode hhas
      have hhas' := hhas.subst (σ := Subst.from_TypeEnv env)
      simpa [CaptureSet.denot, Subst.from_TypeEnv_empty, CaptureSet.subst_id] using
        hsat.kind (C.subst (Subst.from_TypeEnv env)) mode hhas'
    · intro C1 m1 C2 m2 hdistinct
      have hdistinct' := hdistinct.subst (σ := Subst.from_TypeEnv env)
      simpa [CaptureSet.denot, Subst.from_TypeEnv_empty, CaptureSet.subst_id] using
        hsat.sep (C1.subst (Subst.from_TypeEnv env)) m1
          (C2.subst (Subst.from_TypeEnv env)) m2 hdistinct'

theorem SepCtx.WfInHeap.of_has
    {Ψ : SepCtx s} {H : Heap}
    (hwf : SepCtx.WfInHeap Ψ H)
    (hhas : Ψ.Has C m) :
    CaptureSet.WfInHeap C H := by
  induction hhas with
  | here =>
    cases hwf with
    | wf_cons _ hwf_C =>
      exact hwf_C
  | there h ih =>
    cases hwf with
    | wf_cons hwf_Ψ _ =>
      exact ih hwf_Ψ

theorem Subst.from_TypeEnv_lweaken {env : TypeEnv s} :
    Rename.succ.asSubst.comp (Subst.from_TypeEnv (env.extend_lock)) =
      Subst.from_TypeEnv env := by
  apply Subst.funext
  · intro x
    simp [Subst.comp, Subst.from_TypeEnv, Rename.asSubst, Var.subst,
      TypeEnv.extend_lock, Rename.succ, TypeEnv.lookup_var]
  · intro X
    rfl
  · intro C
    simp [Subst.comp, Subst.from_TypeEnv, Rename.asSubst, CaptureSet.subst,
      TypeEnv.extend_lock, Rename.succ, TypeEnv.lookup_cvar]

theorem TypeEnv.satisfy_lweaken_iff
    {env : TypeEnv s} {Ψ : SepCtx s} {m : Memory} :
    (env.extend_lock).Satisfy (Ψ.rename Rename.succ) m ↔ env.Satisfy Ψ m := by
  have hsubst :
      (Ψ.rename Rename.succ).subst (Subst.from_TypeEnv (env.extend_lock)) =
        Ψ.subst (Subst.from_TypeEnv env) := by
    calc
      (Ψ.rename Rename.succ).subst (Subst.from_TypeEnv (env.extend_lock))
        = (Ψ.subst Rename.succ.asSubst).subst (Subst.from_TypeEnv (env.extend_lock)) := by
            rw [SepCtx.subst_asSubst]
      _ = Ψ.subst (Rename.succ.asSubst.comp (Subst.from_TypeEnv (env.extend_lock))) := by
            rw [SepCtx.subst_comp]
      _ = Ψ.subst (Subst.from_TypeEnv env) := by
            rw [Subst.from_TypeEnv_lweaken]
  constructor
  · intro h
    have h' := (TypeEnv.satisfy_subst_iff
      (env := env.extend_lock) (Ψ := Ψ.rename Rename.succ) (m := m)).mp h
    rw [hsubst] at h'
    exact (TypeEnv.satisfy_subst_iff (env := env) (Ψ := Ψ) (m := m)).mpr h'
  · intro h
    have h' := (TypeEnv.satisfy_subst_iff (env := env) (Ψ := Ψ) (m := m)).mp h
    rw [← hsubst] at h'
    exact (TypeEnv.satisfy_subst_iff
      (env := env.extend_lock) (Ψ := Ψ.rename Rename.succ) (m := m)).mpr h'

/-- Modal introduction as a semantic typing rule. -/
theorem sem_typ_wrap
  {cs : CaptureSet s} {Ψ : SepCtx s} {e : Exp s} {E : Ty .exi s}
  (hclosed_e : (Exp.boxed cs Ψ e).IsClosed)
  (ht : cs.rename Rename.succ # Γ.push_lock Ψ ⊨ e.rename Rename.succ : E.rename Rename.succ) :
  ∅ # Γ ⊨ Exp.boxed cs Ψ e : (Ty.modal cs Ψ E).typ := by
  intro env store hts hdsep _
  simp only [Ty.exi_exp_denot, Ty.exi_val_denot]
  apply Eval.eval_val
  · constructor
  · simp only [Denot.as_mpost, Ty.val_denot]
    cases hclosed_e with
    | boxed hclosed_cs hclosed_Ψ hclosed_body =>
      constructor
      · apply Exp.wf_subst
        · exact Exp.wf_of_closed (Exp.IsClosed.boxed hclosed_cs hclosed_Ψ hclosed_body)
        · exact from_TypeEnv_wf_in_heap hts
      constructor
      · apply CaptureSet.wf_subst
        · exact CaptureSet.wf_of_closed hclosed_cs
        · exact from_TypeEnv_wf_in_heap hts
      · refine ⟨cs.subst (Subst.from_TypeEnv env), Ψ.subst (Subst.from_TypeEnv env),
          e.subst (Subst.from_TypeEnv env), ?_, ?_, ?_, ?_, ?_, ?_⟩
        · simp [resolve, Exp.subst]
        · apply CaptureSet.wf_subst
          · exact CaptureSet.wf_of_closed hclosed_cs
          · exact from_TypeEnv_wf_in_heap hts
        · apply SepCtx.wf_subst
          · exact SepCtx.wf_of_closed hclosed_Ψ
          · exact from_TypeEnv_wf_in_heap hts
        · intro m' hsub hsat
          exact (TypeEnv.satisfy_subst_iff (env := env) (Ψ := Ψ) (m := m')).mp hsat
        · rw [← closed_captureset_subst_denot (env := env) hclosed_cs]
          rw [expand_captures_eq_ground_denot]
          simpa [CaptureSet.denot, Subst.from_TypeEnv_empty, CaptureSet.subst_id] using
            (CapabilitySet.Subset.refl :
              (cs.subst (Subst.from_TypeEnv env)).ground_denot store ⊆
                (cs.subst (Subst.from_TypeEnv env)).ground_denot store)
        · intro m' hsub hcompat hkind hsep
          have hsat_Ψ : env.Satisfy Ψ m' := by
            constructor
            · intro C mode hhas
              exact CaptureSet.wf_subst
                (SepCtx.WfInHeap.of_has (SepCtx.wf_of_closed hclosed_Ψ) hhas)
                (from_TypeEnv_wf_in_heap (env_typing_monotonic hts hsub))
            · intro C mode hhas
              exact hkind C mode hhas
            · intro C1 m1 C2 m2 hdistinct
              exact hsep C1 m1 C2 m2 hdistinct
          have henv_lock : EnvTyping (Γ.push_lock Ψ) (env.extend_lock) m' := by
            constructor
            · exact hsat_Ψ
            · exact env_typing_monotonic hts hsub
          have hcap_rename :
              (cs.rename Rename.succ).denot (env.extend_lock) = cs.denot env := by
            exact (rebind_captureset_denot (Rebind.lweaken (env := env)) cs).symm
          have hcs_mono : cs.denot env m' = cs.denot env store := by
            have hwf_cs : (cs.subst (Subst.from_TypeEnv env)).WfInHeap store.heap := by
              exact CaptureSet.wf_subst (CaptureSet.wf_of_closed hclosed_cs)
                                        (from_TypeEnv_wf_in_heap hts)
            exact (capture_set_denot_is_monotonic (ρ := env) (C := cs) hwf_cs hsub).symm
          have hauthority :
              (cs.rename Rename.succ).denot (env.extend_lock) m' =
                expand_captures store.heap (cs.subst (Subst.from_TypeEnv env)) := by
            calc (cs.rename Rename.succ).denot (env.extend_lock) m'
              _ = cs.denot env m' := by rw [congrFun hcap_rename m']
              _ = cs.denot env store := by rw [hcs_mono]
              _ = (cs.subst (Subst.from_TypeEnv env)).ground_denot store := by
                simp [CaptureSet.denot]
              _ = expand_captures store.heap (cs.subst (Subst.from_TypeEnv env)) := by
                rw [← expand_captures_eq_ground_denot]
          have hcompat' :
              m'.is_compatible ((cs.rename Rename.succ).denot (env.extend_lock) m') := by
            rw [hauthority]
            exact hcompat
          have htyped := ht (env.extend_lock) m' henv_lock hdsep.extend_lock hcompat'
          have hsubst :
              (e.rename Rename.succ).subst (Subst.from_TypeEnv (env.extend_lock)) =
                e.subst (Subst.from_TypeEnv env) := by
            calc
              (e.rename Rename.succ).subst (Subst.from_TypeEnv (env.extend_lock))
                = (e.subst Rename.succ.asSubst).subst (Subst.from_TypeEnv (env.extend_lock)) := by
                    rw [Exp.subst_asSubst]
              _ = e.subst (Rename.succ.asSubst.comp (Subst.from_TypeEnv (env.extend_lock))) := by
                    rw [Exp.subst_comp]
              _ = e.subst (Subst.from_TypeEnv env) := by
                    rw [Subst.from_TypeEnv_lweaken]
          rw [hsubst] at htyped
          rw [hauthority] at htyped
          simp only [Ty.exi_exp_denot, List.empty_eq] at htyped ⊢
          apply eval_post_monotonic _ htyped
          exact Denot.imply_to_entails _ _
            (Denot.equiv_to_imply (lweaken_exi_val_denot (env := env) (T := E))).2

theorem sem_typ_app
  {T1 : Ty .capt s} {T2 : Ty .exi (s,x)}
  {x y : BVar s .var} -- x and y must be BOUND variables (from typing rule)
  (hx : {} # Γ ⊨ Exp.var (.bound x) :
    .typ ((Ty.arrow T1 (.var (.M .epsilon) (.bound x)) T2)))
  (hy : {} # Γ ⊨ Exp.var (.bound y) : .typ T1) :
  (.var (.M .epsilon) (.bound x)) # Γ ⊨
    Exp.app (.bound x) (.bound y) : T2.subst (Subst.openVar (.bound y)) := by
  intro env store hts hdsep hcompat
  -- Extract function denotation
  have h1 := hx env store hts hdsep (Memory.is_compatible_empty store)
  simp only [List.empty_eq] at h1
  have h1' := var_exp_denot_inv h1
  simp only [Ty.exi_val_denot] at h1'
  -- Extract the arrow structure
  have ⟨fx, hfx, cs', T0, e0, hval, R, hlk, hR0_sub, hfun⟩ := abs_val_denot_inv h1'
  -- Extract argument denotation
  have h2 := hy env store hts hdsep (Memory.is_compatible_empty store)
  simp only [List.empty_eq] at h2
  have h2' := var_exp_denot_inv h2
  simp only [Ty.exi_val_denot] at h2'
  -- Determine concrete locations
  have : fx = (env.lookup_var x).1 := by cases hfx; rfl
  subst this
  let fy := (env.lookup_var y).1
  -- Derive compat for the closure's authority from the budget compat.
  have hcompat_closure : store.is_compatible (expand_captures store.heap cs') :=
    Memory.is_compatible_subset hR0_sub hcompat
  -- Apply function to argument
  have happ := hfun fy store (Memory.subsumes_refl store) hcompat_closure h2'
  -- The opening lemma relates extended environment to substituted type
  let ps := compute_peakset env T1.captureSet
  let R := expand_captures store.heap cs'
  have heqv := open_arg_exi_exp_denot (env:=env) (y:=.bound y) (ps:=ps) (T:=T2) (R:=R)
  have hinterp : interp_var env (Var.bound y) = fy := rfl
  rw [hinterp] at heqv
  have happ' :=
    (heqv store (e0.subst (Subst.openVar (Var.free fy)))).1 happ
  simp only [Ty.exi_exp_denot, List.empty_eq] at happ'
  -- Widen the authority
  have happ'' := eval_capability_set_monotonic happ' hR0_sub
  simpa [Exp.subst, Var.subst, Subst.from_TypeEnv, Ty.exi_exp_denot] using
    (Eval.eval_apply hlk happ'')

theorem sem_typ_tapp
  {S : PureTy s} {T : Ty .exi (s,X)}
  {x : BVar s .var} -- x must be a BOUND variable (from typing rule)
  (hx : {} # Γ ⊨ Exp.var (.bound x) :
    .typ (Ty.poly S.core (.var (.M .epsilon) (.bound x)) T)) :
  (.var (.M .epsilon) (.bound x)) # Γ ⊨ Exp.tapp (.bound x) S : T.subst (Subst.openTVar S) := by
  intro env store hts hdsep hcompat
  -- Extract function denotation
  have h1 := hx env store hts hdsep (Memory.is_compatible_empty store)
  simp only [List.empty_eq] at h1
  have h1' := var_exp_denot_inv h1
  simp only [Ty.exi_val_denot] at h1'
  -- Extract the poly structure
  have ⟨fx, hfx, cs, S0, e0, hval, R, hlk, hR0_sub, hfun⟩ := tabs_val_denot_inv h1'
  -- Determine concrete location
  have : fx = (env.lookup_var x).1 := by cases hfx; rfl
  subst this
  have hcompat_closure : store.is_compatible (expand_captures store.heap cs) :=
    Memory.is_compatible_subset hR0_sub hcompat
  have himply_simple := val_denot_implies_simple_ans (typed_env_is_implying_simple_ans hts) S.core
  have happ := hfun store (Ty.val_denot env S.core) (Memory.subsumes_refl store)
    hcompat_closure
    (val_denot_is_proper hts)
    himply_simple
    (by intro m' hsub; exact Denot.imply_implyat (Denot.imply_refl _))
    (pure_ty_enforce_pure (typed_env_enforces_pure hts) S.p)
  have heqv := open_targ_exi_exp_denot (env:=env) (S:=S) (T:=T) (R:=expand_captures store.heap cs)
  have happ' := (heqv store (e0.subst (Subst.openTVar .top))).1 happ
  simp only [Ty.exi_exp_denot, List.empty_eq] at happ'
  have happ'' := eval_capability_set_monotonic happ' hR0_sub
  simpa [Exp.subst, Var.subst, Subst.from_TypeEnv, Ty.exi_exp_denot] using
    (Eval.eval_tapply hlk happ'')

theorem sem_typ_capp
  {x : BVar s .var}
  {T : Ty .exi (s,C)}
  {D : CaptureSet s}
  (hΓ : Γ.IsClosed)
  (hD_closed : D.IsClosed)
  (hvalid_D : CaptureBound.IsValid Γ (.bound D))
  (hx : {} # Γ ⊨ Exp.var (.bound x) :
    .typ (.cpoly (.bound D) (.var (.M .epsilon) (.bound x)) T)) :
  (.var (.M .epsilon) (.bound x)) # Γ ⊨ Exp.capp (.bound x) D : T.subst (Subst.openCVar D) := by
  intro env store hts hdsep hcompat
  -- Extract function denotation
  have h1 := hx env store hts hdsep (Memory.is_compatible_empty store)
  simp only [List.empty_eq] at h1
  have h1' := var_exp_denot_inv h1
  simp only [Ty.exi_val_denot] at h1'
  -- Extract the cpoly structure
  have ⟨fx, hfx, cs, B0, e0, hval, R, hlk, hR0_sub, hfun⟩ := cabs_val_denot_inv h1'
  -- Determine concrete location
  have : fx = (env.lookup_var x).1 := by cases hfx; rfl
  subst this
  let D' := D.subst (Subst.from_TypeEnv env)
  have hD'_denot : D'.denot TypeEnv.empty = D.denot env :=
    closed_captureset_subst_denot hD_closed
  have hD'_wf : D'.WfInHeap store.heap :=
    CaptureSet.wf_subst (CaptureSet.wf_of_closed hD_closed) (from_TypeEnv_wf_in_heap hts)
  have hcompat_closure : store.is_compatible (expand_captures store.heap cs) :=
    Memory.is_compatible_subset hR0_sub hcompat
  have hdf_D' : (D'.ground_denot store).drop_free := by
    -- A `.drop` in `D`'s runtime image would, by `drop_denot_peak`, trace to a
    -- `.drop`-access peak of `D` — contradicting `CaptureBound.IsValid` (the
    -- concrete bound `D` is access-only).
    intro l hmem
    have hmem' : (D.denot env store).hasmem .drop l := hmem
    obtain ⟨c, hsub, _⟩ :=
      drop_denot_peak hts hΓ (envtyping_lookup_cvar_drop_free hts) hD_closed hmem'
    exact hvalid_D c hsub
  have happ := hfun store D'
    hD'_wf
    hdf_D'
    (Memory.subsumes_refl store)
    hcompat_closure
    (by
      rw [hD'_denot]
      simpa only [CaptureBound.denot] using
        (CapabilitySet.BoundedBy.set CapabilitySet.Subset.refl :
          (D.denot env store).BoundedBy (.set (D.denot env store))))
  have heqv := open_carg_exi_exp_denot (env:=env) (C:=D) (T:=T)
    (R:=expand_captures store.heap cs) (cap := D'.ground_denot store)
  have happ2 :=
    (heqv store (e0.subst (Subst.openCVar D'))).1 happ
  simp only [Ty.exi_exp_denot, List.empty_eq] at happ2
  simpa [Exp.subst, Var.subst, Subst.from_TypeEnv, CaptureSet.subst, Ty.exi_exp_denot] using
    Eval.eval_capply hlk (eval_capability_set_monotonic happ2 hR0_sub)

theorem sem_typ_invoke
  {x y : BVar s .var} -- x and y must be BOUND variables (from typing rule)
    (hx : {} # Γ ⊨ Exp.var (.bound x) :
    .typ (.cap (.var (.M .epsilon) (.bound x))))
  (hy : {} # Γ ⊨ Exp.var (.bound y) :
    .typ .unit) :
  (.var (.M .epsilon) (.bound x)) # Γ ⊨
    Exp.app (.bound x) (.bound y) : .typ .unit := by
  intro env store hts hdsep _
  -- Extract capability denotation from hx
  have h1 := semtyp_to_exi_exp_denot hx hts hdsep (Memory.is_compatible_empty store)
  simp only [List.empty_eq] at h1
  have h1' := var_exp_denot_inv h1
  simp only [Ty.exi_val_denot] at h1'
  -- Extract the capability structure
  have ⟨fx, hfx, hlk_cap, hmem_cap⟩ := cap_val_denot_inv h1'
  -- Extract unit denotation from hy
  have h2 := semtyp_to_exi_exp_denot hy hts hdsep (Memory.is_compatible_empty store)
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
  simp only [Ty.exi_exp_denot, Exp.subst, Subst.from_TypeEnv, Var.subst,
    CaptureSet.denot, List.empty_eq]
  -- Show env.lookup_var x is covered in the capability set
  have hcov :
    (CaptureSet.denot env (.var (.M .epsilon) (.bound x)) store).covers
      (.access .epsilon) (env.lookup_var x).1 := hmem_cap
  apply Eval.eval_invoke hcov hlk_cap hlk_unit
  simp only [Denot.as_mpost, Ty.exi_val_denot, Ty.val_denot, resolve]

theorem sem_typ_unit :
  {} # Γ ⊨ Exp.unit : .typ .unit := by
  intro env store hts _ _
  simp only [Ty.exi_exp_denot, Exp.subst, List.empty_eq]
  apply Eval.eval_val
  · exact Exp.IsSimpleVal.unit
  · simp only [Denot.as_mpost, Ty.exi_val_denot, Ty.val_denot, resolve]

theorem sem_typ_btrue :
  {} # Γ ⊨ Exp.btrue : .typ .bool := by
  intro env store hts _ _
  simp only [Ty.exi_exp_denot, Exp.subst, List.empty_eq]
  apply Eval.eval_val
  · exact Exp.IsSimpleVal.btrue
  · simp only [Denot.as_mpost, Ty.exi_val_denot, Ty.val_denot, resolve]
    left; trivial

theorem sem_typ_bfalse :
  {} # Γ ⊨ Exp.bfalse : .typ .bool := by
  intro env store hts _ _
  simp only [Ty.exi_exp_denot, Exp.subst, List.empty_eq]
  apply Eval.eval_val
  · exact Exp.IsSimpleVal.bfalse
  · simp only [Denot.as_mpost, Ty.exi_val_denot, Ty.val_denot, resolve]
    right; trivial

theorem sem_typ_cond
  {C1 C2 C3 : CaptureSet s} {Γ : Ctx s}
  {x : Var .var s} {e2 e3 : Exp s} {T : Ty .exi s}
  (ht1 : C1 # Γ ⊨ (.var x) : .typ .bool)
  (ht2 : C2 # Γ ⊨ e2 : T)
  (ht3 : C3 # Γ ⊨ e3 : T) :
  (C1 ∪ C2 ∪ C3) # Γ ⊨ (.cond x e2 e3) : T := by
  intro env store hts hdsep hcompat
  simp only [Ty.exi_exp_denot, Exp.subst, List.empty_eq]
  -- Each sub-budget's denotation is contained in the outer `(C1 ∪ C2 ∪ C3).denot`.
  have hsubC1 :
      CaptureSet.denot env C1 store ⊆ CaptureSet.denot env (C1 ∪ C2 ∪ C3) store :=
    CapabilitySet.Subset.trans CapabilitySet.Subset.union_right_left
      CapabilitySet.Subset.union_right_left
  have hsubC2 : CaptureSet.denot env C2 store ⊆ CaptureSet.denot env (C1 ∪ C2 ∪ C3) store :=
    CapabilitySet.Subset.trans CapabilitySet.Subset.union_right_right
      CapabilitySet.Subset.union_right_left
  have hsubC3 : CaptureSet.denot env C3 store ⊆ CaptureSet.denot env (C1 ∪ C2 ∪ C3) store := by
    simp only [CaptureSet.denot, CaptureSet.subst, CaptureSet.ground_denot, List.empty_eq]
    apply CapabilitySet.Subset.union_right_right
  -- Guard: the new budget is exactly `C1.denot`, a subset of the outer budget.
  have hcompat_C1 : store.is_compatible (C1.denot env store) :=
    Memory.is_compatible_subset hsubC1 hcompat
  have hguard_base := semtyp_to_exi_exp_denot ht1 hts hdsep hcompat_C1
  simp only [Ty.exi_exp_denot] at hguard_base
  -- The guard is a `.var`, so by `Eval.var_inv` the bool postcondition holds at `store`.
  have hQ1_at_store : Ty.val_denot env .bool store (.var (x.subst (Subst.from_TypeEnv env))) := by
    have h := Eval.var_inv hguard_base
    simpa [Denot.as_mpost, Ty.exi_val_denot] using h
  simp only [Ty.val_denot] at hQ1_at_store
  have hres :
      resolve store.heap (.var (x.subst (Subst.from_TypeEnv env))) = some .btrue ∨
      resolve store.heap (.var (x.subst (Subst.from_TypeEnv env))) = some .bfalse :=
    hQ1_at_store
  have hcompat_C2 : store.is_compatible (C2.denot env store) :=
    Memory.is_compatible_subset hsubC2 hcompat
  have hcompat_C3 : store.is_compatible (C3.denot env store) :=
    Memory.is_compatible_subset hsubC3 hcompat
  apply Eval.eval_cond hres
  · -- true branch: run `e2` at its own budget, widen to the outer budget.
    intro _hres_true
    have h2 := ht2 env store hts hdsep hcompat_C2
    simp only [Ty.exi_exp_denot] at h2
    exact eval_capability_set_monotonic h2 hsubC2
  · -- false branch
    intro _hres_false
    have h3 := ht3 env store hts hdsep hcompat_C3
    simp only [Ty.exi_exp_denot] at h3
    exact eval_capability_set_monotonic h3 hsubC3

theorem sem_typ_reader
  (_hclosed : Γ.IsClosed)
  (hx : Γ.LookupVar x (.cell C)) :
  {} # Γ ⊨ Exp.reader (.bound x) :
    (.typ (.reader (.var (.M .ro) (.bound x)))) := by
  intro env store hts _ _
  simp only [Ty.exi_exp_denot, Exp.subst, List.empty_eq]
  apply Eval.eval_val
  · exact Exp.IsSimpleVal.reader
  · simp only [Denot.as_mpost, Ty.exi_val_denot, Ty.val_denot]
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
        CaptureSet.denot env (CaptureSet.var (.M .ro) (Var.bound x)) store
          = CapabilitySet.singleton .ro (env.lookup_var x).1 := by
        simp only [CaptureSet.denot, CaptureSet.subst, Subst.from_TypeEnv, Var.subst,
              CaptureSet.ground_denot, CapabilitySet.applyAccess_M, CapabilitySet.applyMut,
              CapabilitySet.applyRO, CapabilitySet.singleton, reachability_of_loc, hlookup_cell,
              CapMode.applyRO]
      have hcov_singleton :
          CapabilitySet.covers (.access .ro) (env.lookup_var x).1
            (CapabilitySet.singleton .ro (env.lookup_var x).1) :=
        CapabilitySet.covers.here (l:=(env.lookup_var x).1) CapMode.Le.refl
      simpa [hden] using hcov_singleton

theorem sem_typ_alloc
  {x : BVar s .var}
  (hx : {} # Γ ⊨ Exp.var (.bound x) : .typ .bool) :
  {} # Γ ⊨ Exp.alloc (.bound x) : .exi (.cell (.cvar (.M .epsilon) .here)) := by
  intro env store hts hdsep _
  simp only [Ty.exi_exp_denot, Exp.subst, Var.subst, Subst.from_TypeEnv, List.empty_eq]
  set fx := (env.lookup_var x).1
  -- From hx, the variable resolves to a bool in `store`.
  have hx_eval := semtyp_to_exi_exp_denot hx hts hdsep (Memory.is_compatible_empty store)
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
          Eval (CaptureSet.denot env ∅ store) store
            (Exp.alloc (Var.free fx))
            (fun v m' =>
              Ty.exi_val_denot env
                (Ty.exi (Ty.cell (CaptureSet.cvar (.M Mutability.epsilon) BVar.here))) m' v) := by
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
          change _ ∧ _ ∧ Ty.val_denot _ _ _ _
          refine ⟨CaptureSet.WfInHeap.wf_var_free hlookup_l, ?_, ?_⟩
          · -- the fresh capability cell's reachability is a drop-free singleton
            change ∀ l', ¬ CapabilitySet.hasmem .drop l'
              ((CaptureSet.var (.M .epsilon) (.free l)).ground_denot m')
            simp only [CaptureSet.ground_denot, reachability_of_loc, hlookup_l]
            intro l' hmem
            exact CapabilitySet.singleton_no_drop hmem
          simp only [Ty.val_denot]
          refine ⟨CaptureSet.WfInHeap.wf_var_free hlookup_l, l, b, .live, rfl, hlookup_l, ?_⟩
          change ((CaptureSet.var (.M Mutability.epsilon) (Var.free l)).ground_denot m').covers
            (.access Mutability.epsilon) l
          simp only [CaptureSet.ground_denot, reachability_of_loc, hlookup_l]
          exact CapabilitySet.covers.here CapMode.Le.refl
      rcases hbool with hb | hb
      · exact hclose true (fun _ => hb) (by intro h; cases h)
      · exact hclose false (by intro h; cases h) (fun _ => hb)

theorem sem_typ_drop {x : BVar s .var}
  (hx : {} # Γ ⊨ Exp.var (.bound x) :
    .typ (.cell (.var (.M .epsilon) (.bound x))))
  (_hΓ : Γ.IsClosed) :
  (.var .drop (.bound x)) # Γ ⊨ Exp.drop (.bound x) : .typ .unit := by
  intro env store hts hdsep hcompat
  -- Extract cell denotation from hx
  have h1 := semtyp_to_exi_exp_denot hx hts hdsep (Memory.is_compatible_empty store)
  simp only [List.empty_eq] at h1
  have h1' := var_exp_denot_inv h1
  simp only [Ty.exi_val_denot] at h1'
  have ⟨fx, b0, ℓ0, hfx, hlk_cell, hmem_cell⟩ := cell_val_denot_inv h1'
  have : fx = (env.lookup_var x).1 := by cases hfx; rfl
  subst this
  simp only [Ty.exi_exp_denot, Exp.subst, Subst.from_TypeEnv, Var.subst, List.empty_eq]
  -- The budget for `.var .drop x` is the drop-image of x's reachability.
  have hbudget_denot :
      ((CaptureSet.var .drop (Var.bound x)).denot env store) =
        (CapabilitySet.singleton .epsilon (env.lookup_var x).1).to_drop := by
    simp only [CaptureSet.denot, CaptureSet.subst, Var.subst, Subst.from_TypeEnv,
      CaptureSet.ground_denot, CapabilitySet.applyAccess_drop,
      reachability_of_loc, hlk_cell, CapabilitySet.singleton]
  -- Liveness of the dropped cell, from the (drop-mode) budget compat.
  have hlive : ℓ0 = .live := by
    have hcompat' :
        store.is_compatible
          ((CapabilitySet.singleton .epsilon (env.lookup_var x).1).to_drop) :=
      hbudget_denot ▸ hcompat
    exact hcompat' .drop (env.lookup_var x).1 b0 ℓ0
      (CapabilitySet.hasmem_to_drop_of_hasmem CapabilitySet.hasmem.here) hlk_cell
  subst hlive
  have hlk_cell' :
    store.lookup (env.lookup_var x).1 = some (.capability (.mcell b0 .live)) := by
    simpa [Memory.lookup] using hlk_cell
  apply Eval.eval_drop (hx := hlk_cell')
  · simp only [Denot.as_mpost, Ty.exi_val_denot, Ty.val_denot, resolve]
  · -- The `.drop` coverage comes directly from the drop-qualified budget:
    -- `(reachability_of_loc … x).to_drop` covers `x` at `.drop`.
    have hcov_access :
        CapabilitySet.covers (.access .epsilon) (env.lookup_var x).1
          (reachability_of_loc store.heap (env.lookup_var x).1) := by
      simp only [reachability_of_loc, hlk_cell, CapabilitySet.singleton]
      exact CapabilitySet.covers.here CapMode.Le.refl
    have hcov_drop := CapabilitySet.covers_to_drop_of_covers hcov_access
    simpa only [CaptureSet.denot, CaptureSet.subst, Var.subst, Subst.from_TypeEnv,
      CaptureSet.ground_denot, CapabilitySet.applyAccess_drop] using hcov_drop

theorem sem_typ_read
  {x : BVar s .var}
  (_hΓ : Γ.IsClosed)
  (hx : {} # Γ ⊨ Exp.var (.bound x) : .typ (.reader C)) :
  (.var (.M .epsilon) (.bound x)) # Γ ⊨ Exp.read (.bound x) : .typ .bool := by
  intro env store hts hdsep hcompat
  -- Extract reader denotation from hx
  have h1 := semtyp_to_exi_exp_denot hx hts hdsep (Memory.is_compatible_empty store)
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
  simp only [Ty.exi_exp_denot, Exp.subst, Subst.from_TypeEnv, Var.subst, List.empty_eq]
  -- The reachability stored with the reader gives the needed .ro capability
  have hreach :
    reachability_of_loc store.heap (env.lookup_var x).1 = CapabilitySet.singleton .ro y := by
    have heq := reachability_of_loc_eq_resolve_reachability store (env.lookup_var x).1
      ⟨Exp.reader (.free y), hval_reader, R⟩ hlookup_reader
    simpa [resolve_reachability] using heq
  have hcov :
      CapabilitySet.covers (.access .ro) y
        (((CaptureSet.var (.M .epsilon) (Var.bound x)).subst (Subst.from_TypeEnv env)).ground_denot
          store) := by
    have hden :
        (((CaptureSet.var (.M .epsilon) (Var.bound x)).subst (Subst.from_TypeEnv env)).ground_denot
          store) = CapabilitySet.singleton .ro y := by
      simp only [CaptureSet.subst, Var.subst, Subst.from_TypeEnv, CaptureSet.ground_denot,
            CapabilitySet.applyAccess_M, CapabilitySet.applyMut, hreach]
    simpa [hden] using (CapabilitySet.covers.here (l:=y) CapMode.Le.refl)
  -- Use hcompat to derive that the cell at y is live.
  have hlive : ℓ0 = .live := by
    have hbudget_denot :
        ((CaptureSet.var (.M .epsilon) (Var.bound x)).denot env store) =
          CapabilitySet.singleton .ro y := by
      simp only [CaptureSet.denot, CaptureSet.subst, Var.subst, Subst.from_TypeEnv,
        CaptureSet.ground_denot, CapabilitySet.applyAccess_M, CapabilitySet.applyMut, hreach]
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
  apply Eval.eval_read hcov hlookup_reader' hlookup_cell'
  simp only [Denot.as_mpost, Ty.exi_val_denot, Ty.val_denot, resolve]
  cases b0 <;> simp

theorem sem_typ_write
  {x y : BVar s .var}
  (_hΓ : Γ.IsClosed)
  (hx : {} # Γ ⊨ Exp.var (.bound x) : .typ (.cell Cx))
  (hy : {} # Γ ⊨ Exp.var (.bound y) : .typ .bool) :
  (.var (.M .epsilon) (.bound x)) # Γ ⊨
    Exp.write (.bound x) (.bound y) : .typ .unit := by
  intro env store hts hdsep hcompat
  -- Extract cell denotation from hx
  have h1 := semtyp_to_exi_exp_denot hx hts hdsep (Memory.is_compatible_empty store)
  simp only [List.empty_eq] at h1
  have h1' := var_exp_denot_inv h1
  simp only [Ty.exi_val_denot] at h1'
  -- Extract the cell structure
  have ⟨fx, b0, ℓ0, hfx, hlk_cell, hmem_cell⟩ := cell_val_denot_inv h1'
  -- Extract bool denotation from hy
  have h2 := semtyp_to_exi_exp_denot hy hts hdsep (Memory.is_compatible_empty store)
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
  simp only [Ty.exi_exp_denot, Exp.subst, Subst.from_TypeEnv, Var.subst, List.empty_eq]
  -- Prove covers: env.lookup_var x is covered by the denotation of the write's capture set
  have hcov :
    (((CaptureSet.var (.M .epsilon) (Var.bound x)).subst
      (Subst.from_TypeEnv env)).ground_denot store).covers (.access .epsilon)
        (env.lookup_var x).1 := by
    simp only [CaptureSet.subst, Var.subst, Subst.from_TypeEnv, CaptureSet.ground_denot,
          reachability_of_loc, hlk_cell, CapabilitySet.singleton]
    exact CapabilitySet.covers.here CapMode.Le.refl
  -- Use hcompat to derive that the cell at env.lookup_var x is live.
  have hlive : ℓ0 = .live := by
    have hbudget_denot :
      ((CaptureSet.var (.M .epsilon) (Var.bound x)).denot env store) =
        CapabilitySet.singleton .epsilon (env.lookup_var x).1 := by
      simp only [CaptureSet.denot, CaptureSet.subst, Var.subst, Subst.from_TypeEnv,
        CaptureSet.ground_denot, CapabilitySet.applyAccess_M, CapabilitySet.applyMut,
        reachability_of_loc, hlk_cell]
    have hcompat' : store.is_compatible (CapabilitySet.singleton .epsilon (env.lookup_var x).1) :=
      hbudget_denot ▸ hcompat
    exact hcompat' (.access .epsilon) (env.lookup_var x).1 b0 ℓ0
      CapabilitySet.hasmem.here hlk_cell
  subst hlive
  cases b
  · apply Eval.eval_write_false hcov (hx := hlk_cell) hlk_bool
    simp only [Denot.as_mpost, Ty.exi_val_denot, Ty.val_denot, resolve]
  · apply Eval.eval_write_true hcov (hx := hlk_cell) hlk_bool
    simp only [Denot.as_mpost, Ty.exi_val_denot, Ty.val_denot, resolve]

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
  SemSubcapt Γ (.var (.M .epsilon) (.bound x)) T.captureSet := by
  intro env m' hts
  unfold CaptureSet.denot
  simp only [List.empty_eq]
  have h : reachability_of_loc m'.heap (env.lookup_var x).1 ⊆ T.captureSet.denot env m' := by
    simpa only [Ty.captureSet] using typed_env_lookup_var_reachability hts hlookup
  -- The new `sc_var` fixes the qualifier to `.M .epsilon`, which `ground_denot`
  -- treats as the identity, so the budget is exactly `x`'s reachability.
  simpa [CaptureSet.ground_denot] using h

theorem sem_sc_cvar {c : BVar s .cvar} {C : CaptureSet s}
  (hlookup : Γ.LookupCVar c a (.bound C)) :
  SemSubcapt Γ (.cvar (.M .epsilon) c) C := by
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

/-- `applyAccess .drop` is monotonic for subcapturing: the semantic image of the
    new `sc_drop_mono` rule. At the capability level `applyAccess .drop` is
    `to_drop`, which is monotone under `CapabilitySet.Subset`. -/
theorem sem_sc_drop_mono {C1 C2 : CaptureSet s}
  (hsub : SemSubcapt Γ C1 C2) :
  SemSubcapt Γ (C1.applyAccess .drop) (C2.applyAccess .drop) := by
  intro env m hts
  simp only [captureSet_denot_applyAccess_comm, CapabilitySet.applyAccess_drop]
  exact CapabilitySet.Subset.to_drop_mono (hsub env m hts)

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
  case sc_drop_mono _ ih => exact sem_sc_drop_mono ih

private theorem fundamental_haskind_ro
  (hkind : HasKind Γ C mode)
  : mode = .ro -> SemHasKind Γ C .ro := by
  induction hkind with
  | empty =>
    intro hm env mem hts
    cases hm
    simpa only [CaptureSet.denot, CaptureSet.subst, CaptureSet.ground_denot, List.empty_eq] using
      CapabilitySet.HasKind.ro_empty
  | union h1 h2 ih1 ih2 =>
    intro hm env mem hts
    cases hm
    simpa only [CaptureSet.denot, CaptureSet.subst, CaptureSet.ground_denot, List.empty_eq] using
      CapabilitySet.HasKind.ro_union (ih1 rfl env mem hts) (ih2 rfl env mem hts)
  | sc hsub hk ih =>
    intro hm env mem hts
    cases hm
    exact CapabilitySet.HasKind.subset_ro
      (fundamental_subcapt hsub env mem hts)
      (ih rfl env mem hts)
  | rw =>
    intro hm
    cases hm
  | imm hlock hhas =>
    intro hm env mem hts
    cases hm
    exact (typed_env_lookup_lock_satisfy hlock hts).kind _ _ hhas
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

/-- `Noninterference` from full location-disjointness. -/
theorem CapabilitySet.noninterference_of_disjoint : ∀ {C1 C2 : CapabilitySet},
  CapabilitySet.disjoint C1 C2 → CapabilitySet.Noninterference C1 C2 := by
  intro C1
  induction C1 with
  | empty =>
    intro C2 _
    exact .ni_empty
  | cap m l =>
    intro C2
    induction C2 with
    | empty =>
      intro _
      exact .ni_symm .ni_empty
    | cap m' l' =>
      intro hdisj
      refine .ni_disj (fun heq => ?_)
      subst heq
      exact hdisj m m' l .here .here
    | union C2a C2b ih2a ih2b =>
      intro hdisj
      refine .ni_symm (.ni_union (.ni_symm (ih2a ?_)) (.ni_symm (ih2b ?_)))
      · intro mu1 mu2 l0 h1 h2
        exact hdisj mu1 mu2 l0 h1 (.left h2)
      · intro mu1 mu2 l0 h1 h2
        exact hdisj mu1 mu2 l0 h1 (.right h2)
  | union C1a C1b ih1a ih1b =>
    intro C2 hdisj
    refine .ni_union (ih1a ?_) (ih1b ?_)
    · intro mu1 mu2 l0 h1 h2
      exact hdisj mu1 mu2 l0 (.left h1) h2
    · intro mu1 mu2 l0 h1 h2
      exact hdisj mu1 mu2 l0 (.right h1) h2

theorem sem_sepcheck_symm
  (ih : SemSepCheck Γ C1 C2) :
  SemSepCheck Γ C2 C1 := by
  intro env H hts hdsep
  exact CapabilitySet.Noninterference.ni_symm (ih env H hts hdsep)

theorem sem_sepcheck_union
  (ih1 : SemSepCheck Γ C1 C3)
  (ih2 : SemSepCheck Γ C2 C3) :
  SemSepCheck Γ (C1 ∪ C2) C3 := by
  intro env H hts hdsep
  simp only [CaptureSet.denot, CaptureSet.subst, CaptureSet.ground_denot]
  exact CapabilitySet.Noninterference.ni_union (ih1 env H hts hdsep) (ih2 env H hts hdsep)

theorem CapabilitySet.noninterference_of_ro_ro
  (hk1 : CapabilitySet.HasKind C1 .ro)
  (hk2 : CapabilitySet.HasKind C2 .ro) :
  CapabilitySet.Noninterference C1 C2 := by
  induction C1 with
  | empty => exact .ni_empty
  | cap m l =>
    cases hk1 with
    | ro_cap =>
      induction C2 with
      | empty => exact .ni_symm .ni_empty
      | cap m' l' =>
        cases hk2 with
        | ro_cap => exact .ni_ro
        | ro_drop =>
          -- REAL GAP: runtime read-only kinding admits `.drop` capabilities
          -- (`HasKind.ro_drop`, forced by `applyRO` fixing `.drop`), but
          -- `Noninterference` has no constructor for a shared location held at
          -- `.drop`. `sep_ro` is semantically sound only for *drop-free*
          -- capability sets — same gap family as `seq_drop` in
          -- `captureSet_seqcomp_denot`.
          sorry
      | union C2a C2b ih2a ih2b =>
        cases hk2 with
        | ro_union hk2a hk2b =>
          exact .ni_symm (.ni_union (.ni_symm (ih2a hk2a)) (.ni_symm (ih2b hk2b)))
    | ro_drop =>
      -- REAL GAP: see the `ro_drop` case above.
      sorry
  | union C1a C1b ih1a ih1b =>
    cases hk1 with
    | ro_union hk1a hk1b =>
      exact .ni_union (ih1a hk1a) (ih1b hk1b)

theorem sem_sepcheck_empty :
  SemSepCheck Γ {} C := by
  intro env H hts _hdsep
  simp only [CaptureSet.denot, CaptureSet.subst, CaptureSet.ground_denot]
  exact .ni_empty

theorem sem_sepcheck_ro
  (hk1 : HasKind Γ C1 .ro)
  (hk2 : HasKind Γ C2 .ro) :
  SemSepCheck Γ C1 C2 := by
  intro env H hts _hdsep
  exact CapabilitySet.noninterference_of_ro_ro
    (fundamental_haskind hk1 env H hts) (fundamental_haskind hk2 env H hts)

/-- Semantic content of `sep_droppable`: two *distinct* droppable capture
variables denote disjoint capability sets (the `DroppableSep` environment
invariant), and disjointness entails `Noninterference` at any access modes. -/
theorem sem_sepcheck_droppable {c1 c2 : BVar s .cvar} {m1 m2 : Access}
  (hdistinct : Γ.TwoDistinctDroppable c1 c2) :
  SemSepCheck Γ (.cvar m1 c1) (.cvar m2 c2) := by
  intro env H hts hdsep
  obtain ⟨ha1, _ha2, hne⟩ := hdistinct
  have hdenot1 :
      (CaptureSet.cvar m1 c1).denot env H = ((env.lookup_cvar c1).2).applyAccess m1 := by
    change ((env.lookup_cvar c1).1.applyAccess m1).ground_denot H = _
    rw [captureSet_ground_denot_applyAccess_comm, ← typed_env_cvar_cap_eq hts c1]
  have hdenot2 :
      (CaptureSet.cvar m2 c2).denot env H = ((env.lookup_cvar c2).2).applyAccess m2 := by
    change ((env.lookup_cvar c2).1.applyAccess m2).ground_denot H = _
    rw [captureSet_ground_denot_applyAccess_comm, ← typed_env_cvar_cap_eq hts c2]
  rw [hdenot1, hdenot2]
  apply CapabilitySet.noninterference_of_disjoint
  intro mu1 mu2 l h1 h2
  obtain ⟨mu1', h1'⟩ := hasmem_of_applyAccess h1
  obtain ⟨mu2', h2'⟩ := hasmem_of_applyAccess h2
  exact hdsep c1 c2 hne ha1 mu1' mu2' l h1' h2' 

theorem fundamental_sepcheck
  (hsep : SepCheck Γ C1 C2) :
  SemSepCheck Γ C1 C2 := by
  induction hsep with
  | sep_symm _ ih =>
    exact sem_sepcheck_symm ih
  | sep_union _ _ ih1 ih2 =>
    exact sem_sepcheck_union ih1 ih2
  | sep_empty =>
    exact sem_sepcheck_empty
  | sep_ro hk1 hk2 =>
    exact sem_sepcheck_ro hk1 hk2
  | sep_sc _ hsub ih =>
    intro env H henv hdsep
    exact CapabilitySet.Noninterference.subset_left
      (ih env H henv hdsep)
      (fundamental_subcapt hsub env H henv)
  | sep_lock hlock hdistinct =>
    intro env H henv _hdsep
    exact (typed_env_lookup_lock_satisfy hlock henv).sep _ _ _ _ hdistinct
  | sep_droppable hdistinct =>
    exact sem_sepcheck_droppable hdistinct

theorem sem_satisfy
  (hclosed_Ψ : Ψ.IsClosed)
  (hsatisfy : Satisfy Γ Ψ) :
  ∀ env m,
    EnvTyping Γ env m ->
    DroppableSep Γ env ->
    env.Satisfy Ψ m := by
  intro env m henv hdsep
  cases hsatisfy with
  | satisfy hkind hsep =>
    constructor
    · intro C mode hhas
      exact CaptureSet.wf_subst (SepCtx.WfInHeap.of_has (SepCtx.wf_of_closed hclosed_Ψ) hhas)
                                (from_TypeEnv_wf_in_heap henv)
    · intro C mode hhas
      exact fundamental_haskind (hkind C mode hhas) env m henv
    · intro C1 m1 C2 m2 hdistinct
      exact fundamental_sepcheck (hsep C1 m1 C2 m2 hdistinct) env m henv hdsep

theorem sem_typ_par
  {C1 C2 : CaptureSet s} {Γ : Ctx s}
  {e1 e2 : Exp s} {E : Ty .exi s}
  (ht1 : C1 # Γ ⊨ e1 : E)
  (ht2 : C2 # Γ ⊨ e2 : E)
  (hsep : SemSepCheck Γ C1 C2) :
  (C1 ∪ C2) # Γ ⊨ (.par e1 e2) : E := by
  intro env store hts hdsep hcompat
  suffices hpar :
      Eval (CaptureSet.denot env (C1 ∪ C2) store) store
        (.par (e1.subst (Subst.from_TypeEnv env)) (e2.subst (Subst.from_TypeEnv env)))
        (Ty.exi_val_denot env E).as_mpost by
    simpa only [Ty.exi_exp_denot, Exp.subst, List.empty_eq] using hpar
  have hunion : (C1 ∪ C2).denot env store = C1.denot env store ∪ C2.denot env store := rfl
  have hcompat' := hunion ▸ hcompat
  have he1 : Eval (CaptureSet.denot env C1 store) store
      (e1.subst (Subst.from_TypeEnv env)) (Ty.exi_val_denot env E).as_mpost := by
    simpa only [Ty.exi_exp_denot] using
      ht1 env store hts hdsep (Memory.is_compatible_union_left hcompat')
  have he2 : Eval (CaptureSet.denot env C2 store) store
      (e2.subst (Subst.from_TypeEnv env)) (Ty.exi_val_denot env E).as_mpost := by
    simpa only [Ty.exi_exp_denot] using
      ht2 env store hts hdsep (Memory.is_compatible_union_right hcompat')
  have hni := hsep env store hts hdsep
  exact Eval.eval_par he1 he2 hni CapabilitySet.Subset.refl

/-- Shared-location elimination for `Noninterference`: a location member of
both sides must be held read-only on both sides (`ni_ro` is the only
constructor permitting overlap). -/
theorem CapabilitySet.Noninterference.shared_ro
    {C1 C2 : CapabilitySet} {mu1 mu2 : CapMode} {l : Nat}
    (hni : CapabilitySet.Noninterference C1 C2)
    (h1 : C1.hasmem mu1 l) (h2 : C2.hasmem mu2 l) :
    mu1 = .access .ro ∧ mu2 = .access .ro := by
  induction hni generalizing mu1 mu2 with
  | ni_symm _ ih =>
    obtain ⟨ha, hb⟩ := ih h2 h1
    exact ⟨hb, ha⟩
  | ni_empty => cases h1
  | ni_union _ _ ih1 ih2 =>
    cases h1 with
    | left h => exact ih1 h h2
    | right h => exact ih2 h h2
  | ni_ro =>
    cases h1
    cases h2
    exact ⟨rfl, rfl⟩
  | ni_disj hne =>
    cases h1
    cases h2
    exact absurd rfl hne

/-- An access-only (no `.drop` peak) *closed* capture set denotes a drop-free
capability set: any runtime `.drop` member would trace (via `drop_denot_peak`)
to a `.drop`-access peak, contradicting `AccessOnly`. Closedness is essential:
a free location referenced at `.drop` access has no peaks at all, so
`AccessOnly` would be vacuous about it. -/
theorem accessonly_denot_drop_free
    {Γ : Ctx s} {env : TypeEnv s} {store : Memory} {C : CaptureSet s}
    (hts : EnvTyping Γ env store) (hΓ : Γ.IsClosed) (hC : C.IsClosed)
    (hao : C.AccessOnly Γ) :
    (C.denot env store).drop_free := by
  intro l hmem
  obtain ⟨c, hsub, _⟩ :=
    drop_denot_peak hts hΓ (envtyping_lookup_cvar_drop_free hts) hC hmem
  exact hao c hsub

/-- Bridge: the syntactic sequential-composition relation `SeqComp Γ C1 C2`
transfers, under a well-typed environment, to the runtime capability level:
no location consumed (`.drop`) by `C1`'s denotation is touched at any mode by
`C2`'s denotation.

Per constructor:
- `seq_sc`: `fundamental_subcapt` shrinks the budget; `.drop`-membership is
  preserved forward by `Subset`.
- `seq_union`: split the union membership.
- `seq_access_only`: the (closed) access-only budget is drop-free, so there is
  no `.drop` member to begin with.
- `seq_drop`: the one REAL GAP (see the `sorry` below). -/
theorem captureSet_seqcomp_denot
    {C1 C2 : CaptureSet s} {Γ : Ctx s} {env : TypeEnv s} {store : Memory}
    (hts : EnvTyping Γ env store)
    (hΓ : Γ.IsClosed)
    (hdsep : DroppableSep Γ env)
    (hseq : SeqComp Γ C1 C2) :
    (C1.denot env store).SeqComp (C2.denot env store) := by
  induction hseq with
  | seq_sc hsub _ ih =>
    intro mu l h1 h2
    exact ih mu l (hasmem_drop_of_subset (fundamental_subcapt hsub env store hts) h1) h2
  | seq_union _ _ ih1 ih2 =>
    intro mu l h1 h2
    cases h1 with
    | left h => exact ih1 mu l h h2
    | right h => exact ih2 mu l h h2
  | seq_access_only hclosed hao =>
    intro mu l h1 _h2
    exact accessonly_denot_drop_free hts hΓ hclosed hao l h1
  | seq_drop hsep =>
    intro mu l h1 h2
    rename_i Ca Cb
    have heq : (Ca.applyDrop).denot env store = (Ca.denot env store).to_drop := by
      have h := captureSet_denot_applyAccess_comm
        (env := env) (C := Ca) (store := store) (a := .drop)
      rw [CaptureSet.applyAccess_drop, CapabilitySet.applyAccess_drop] at h
      exact h
    rw [heq] at h1
    obtain ⟨_, mu1, h1'⟩ := CapabilitySet.hasmem_to_drop_imp h1
    have hni := fundamental_sepcheck hsep env store hts hdsep
    have hro := hni.shared_ro h1' h2
    -- REAL GAP: `seq_drop` only demands `SepCheck Γ Ca Cb`, whose semantic
    -- content (`Noninterference`) still allows `Ca` and `Cb` to share a
    -- location read-only (`sep_ro` / `ni_ro`, witnessed by `hro` above).
    -- `Ca.applyDrop` then consumes that shared location while `Cb` may still
    -- use it — exactly what runtime `SeqComp` forbids. To close this, the
    -- `seq_drop` rule needs a premise entailing *location-disjointness* of
    -- `Ca` and `Cb` (e.g. a `SepCheck` variant excluding read-only overlap).
    sorry

/-- Semantic typing for `letin`. The inductive `SeqComp Γ C1 C2` linearity
    premise (`hseq`) is threaded to `eval_letin`'s `hseq` premise via the
    `captureSet_seqcomp_denot` bridge. The rest of the construction does not
    rely on it: `eval_letin`'s `h_val`/`h_var` premises *assume*
    `m1.is_compatible C2` (so we never derive it from `e1`'s behaviour), and
    `C2` is closed so its denotation is memory-stable. -/
theorem sem_typ_letin
  {C1 C2 : CaptureSet s} {Γ : Ctx s} {e1 : Exp s} {T : Ty .capt s}
  {e2 : Exp (s,,Kind.var)} {U : Ty .exi s}
  (hseq : SeqComp Γ C1 C2)
  (hΓ : Γ.IsClosed)
  (_hclosed_C1 : C1.IsClosed)
  (_hclosed_C2 : C2.IsClosed)
  (_hclosed_e : (Exp.letin e1 e2).IsClosed)
  (ht1 : C1 # Γ ⊨ e1 : .typ T)
  (ht2 : C2.rename Rename.succ # (Γ,x:T) ⊨ e2 : U.rename Rename.succ) :
  C1 ∪ C2 # Γ ⊨ (Exp.letin e1 e2) : U := by
  intro env store hts hdsep hcompat
  simp only [Ty.exi_exp_denot, Exp.subst, List.empty_eq]
  have hunion_denot :
      (C1 ∪ C2).denot env store = C1.denot env store ∪ C2.denot env store := rfl
  apply Eval.eval_letin (Q1 := fun v m' => Ty.val_denot env T m' v)
    (C1 := C1.denot env store) (C2 := C2.denot env store)
  case hpred =>
    intro m1 m2 e hwf hsub hQ
    exact val_denot_is_monotonic (typed_env_is_monotonic hts) T hsub hQ
  case hbool =>
    intro m'
    exact val_denot_is_bool_independent (typed_env_is_bool_independent hts) T
  case a =>
    -- `e1` runs at exactly its own budget `C1.denot`, a subset of the union.
    have hsubC1 : C1.denot env store ⊆ (C1 ∪ C2).denot env store := by
      rw [hunion_denot]; exact CapabilitySet.Subset.union_right_left
    have hcompat_C1 : store.is_compatible (C1.denot env store) :=
      Memory.is_compatible_subset hsubC1 hcompat
    have h1 := ht1 env store hts hdsep hcompat_C1
    simpa only [Ty.exi_exp_denot, Ty.exi_val_denot] using h1
  case h_nonstuck =>
    intro m1 v hQ1
    constructor
    · exact val_denot_implies_simple_ans (typed_env_is_implying_simple_ans hts) T m1 v hQ1
    · exact val_denot_implies_wf (typed_env_is_implying_wf hts) T m1 v hQ1
  case h_val =>
    intro m1 v hs1 hcompat_m1 hv hwf_v hQ1 l' hfresh
    let heapval : HeapVal := ⟨v, hv, compute_reachability m1.heap v hv⟩
    let ps := CaptureSet.peakset Γ T.captureSet
    set m_ext := m1.extend_val l' heapval hwf_v rfl hfresh with hm_ext_def
    have hext_subsumes : m_ext.subsumes m1 :=
      Memory.extend_val_subsumes m1 l' heapval hwf_v rfl hfresh
    have hsub_full : m_ext.subsumes store := Memory.subsumes_trans hext_subsumes hs1
    -- Body EnvTyping for `(Γ,x:T)` at the extended env / extended memory.
    have henv_body : EnvTyping (Γ,x:T) (env.extend_var l' ps) m_ext := by
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
        · exact env_typing_monotonic hts hsub_full
    -- Rebind `C2` into the extended env; closedness makes its denotation stable.
    have hcap_rename_C2 :
        (C2.rename Rename.succ).denot (env.extend_var l' ps) = C2.denot env := by
      have := rebind_captureset_denot
        (Rebind.weaken (env := env) (x := l') (ps := ps)) C2
      exact this.symm
    have hC2_mono : C2.denot env store = C2.denot env m_ext :=
      closed_capture_denot_monotonic _hclosed_C2 hts hsub_full
    -- The body's compat: `eval_letin` hands us `m1.is_compatible (C2.denot env store)`,
    -- which transports to `m_ext` (a fresh value cell preserves liveness) and equals
    -- the body budget `(C2.rename succ).denot (extended) m_ext`.
    have hcompat_body :
        m_ext.is_compatible ((C2.rename Rename.succ).denot (env.extend_var l' ps) m_ext) := by
      rw [congrFun hcap_rename_C2 m_ext, ← hC2_mono]
      exact Memory.is_compatible_extend_val m1 l' heapval hwf_v rfl hfresh hcompat_m1
    have h2 := ht2 (env.extend_var l' ps) m_ext henv_body hdsep.extend_var hcompat_body
    simp only [Ty.exi_exp_denot] at h2
    have hkey := @Exp.from_TypeEnv_weaken_open s env l' e2 ps
    have h2' : Eval _ m_ext
        ((e2.subst (Subst.from_TypeEnv env).lift).subst (Subst.openVar (Var.free l')))
        _ := hkey ▸ h2
    -- The body budget equals `C2.denot env store` (the chosen `eval_letin` C2).
    have hsub_body :
        (C2.rename Rename.succ).denot (env.extend_var l' ps) m_ext ⊆ C2.denot env store := by
      rw [congrFun hcap_rename_C2 m_ext, ← hC2_mono]
      exact CapabilitySet.Subset.refl
    have hcompose := eval_capability_set_monotonic h2' hsub_body
    -- Lift the post from `(U.rename succ)` at the extended env back to `U`.
    have heqv := weaken_exi_val_denot (env := env) (x := l') (ps := ps) (T := U)
    apply eval_post_monotonic _ hcompose
    exact Denot.imply_to_entails _ _ (Denot.equiv_to_imply heqv).2
  case h_var =>
    intro m1 x hs1 hcompat_m1 hwf_x hQ1
    cases x
    case bound bv => cases bv
    case free fx =>
      let ps := CaptureSet.peakset Γ T.captureSet
      have henv_body : EnvTyping (Γ,x:T) (env.extend_var fx ps) m1 := by
        constructor
        · exact hQ1
        · constructor
          · rfl
          · exact env_typing_monotonic hts hs1
      have hcap_rename_C2 :
          (C2.rename Rename.succ).denot (env.extend_var fx ps) = C2.denot env := by
        have := rebind_captureset_denot
          (Rebind.weaken (env := env) (x := fx) (ps := ps)) C2
        exact this.symm
      have hC2_mono : C2.denot env store = C2.denot env m1 :=
        closed_capture_denot_monotonic _hclosed_C2 hts hs1
      have hcompat_body :
          m1.is_compatible ((C2.rename Rename.succ).denot (env.extend_var fx ps) m1) := by
        rw [congrFun hcap_rename_C2 m1, ← hC2_mono]
        exact hcompat_m1
      have h2 := ht2 (env.extend_var fx ps) m1 henv_body hdsep.extend_var hcompat_body
      simp only [Ty.exi_exp_denot] at h2
      have hkey := @Exp.from_TypeEnv_weaken_open s env fx e2 ps
      have h2' : Eval _ m1
          ((e2.subst (Subst.from_TypeEnv env).lift).subst (Subst.openVar (Var.free fx)))
          _ := hkey ▸ h2
      have hsub_body :
          (C2.rename Rename.succ).denot (env.extend_var fx ps) m1 ⊆ C2.denot env store := by
        rw [congrFun hcap_rename_C2 m1, ← hC2_mono]
        exact CapabilitySet.Subset.refl
      have hcompose := eval_capability_set_monotonic h2' hsub_body
      have heqv := weaken_exi_val_denot (env := env) (x := fx) (ps := ps) (T := U)
      apply eval_post_monotonic _ hcompose
      exact Denot.imply_to_entails _ _ (Denot.equiv_to_imply heqv).2
  case hseq =>
    exact captureSet_seqcomp_denot hts hΓ hdsep hseq
  case hagg =>
    rw [hunion_denot]
    exact CapabilitySet.Subset.refl

lemma sem_subtyp_top {T : Ty .capt s}
  (hpure : T.IsPureType) :
  SemSubtyp Γ T .top := by
  -- Unfold SemSubtyp for capturing types
  unfold SemSubtyp
  -- Introduce the environment, memory, and typing assumption
  intro env H htyping _hdsep
  -- Unfold ImplyAfter to handle memory subsumption
  unfold Denot.ImplyAfter
  intro m' hsubsumes
  -- Unfold ImplyAt to get the implication at a specific memory
  unfold Denot.ImplyAt
  intro e hdenot_T
  -- Need to prove: Ty.val_denot env .top m' e
  -- Which unfolds to: e.IsSimpleAns ∧ e.WfInHeap m'.heap ∧ resolve_reachability m'.heap e ⊆ .empty
  unfold Ty.val_denot
  constructor
  · -- Prove IsSimpleAns
    exact val_denot_implies_simple_ans (typed_env_is_implying_simple_ans htyping) T m' e hdenot_T
  constructor
  · -- Prove well-formedness: e.WfInHeap m'.heap
    exact val_denot_implies_wf (typed_env_is_implying_wf htyping) T m' e hdenot_T
  · -- Prove reachability bound: resolve_reachability m'.heap e ⊆ .empty
    -- First get the typing for m' (need monotonicity)
    have htyping' := env_typing_monotonic htyping hsubsumes
    -- Use val_denot_enforces_captures to bound reachability by T.captureSet
    have hbound := val_denot_enforces_captures htyping' e hdenot_T
    -- Since T is pure, T.captureSet is empty, so its denotation is empty
    unfold Ty.IsPureType at hpure
    exact (hpure.denot_empty (env := env) (m := m')).subset_of_subset hbound


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
                Ty.val_denot (env0.extend_tvar d) (S.core.rename Rename.succ) := by
        simpa only [TypeEnv.extend_tvar] using tweaken_val_denot (d := d)
      -- The result follows by transitivity: himply gives d ⊑ val_denot env0 S.core,
      -- hw gives val_denot env0 S.core ≈ val_denot (env0.extend_tvar d) (S.core.rename Rename.succ)
      -- Compose ImplyAfter with equivalence
      unfold Denot.ImplyAfter at himply ⊢
      intro m' hsub e hd
      exact (Denot.equiv_to_imply hw).1 m' e (himply m' hsub e hd)
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
                  Ty.val_denot (env0.extend_var v ps0) (S.core.rename Rename.succ) := by
          simpa only [TypeEnv.extend_var] using weaken_val_denot (x := v) (ps := ps0)
        -- Compose IH with weakening
        unfold Denot.ImplyAfter at ih_result ⊢
        intro m' hsub e hd
        exact (Denot.equiv_to_imply hw).1 m' e (ih_result m' hsub e hd)
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
                  Ty.val_denot (env0.extend_tvar d) (S.core.rename Rename.succ) := by
          simpa only [TypeEnv.extend_tvar] using tweaken_val_denot (d := d)
        -- Compose IH with weakening
        unfold Denot.ImplyAfter at ih_result ⊢
        intro m' hsub e hd
        exact (Denot.equiv_to_imply hw).1 m' e (ih_result m' hsub e hd)
    | cvar _ cb =>
      -- Context extended with a capture variable
      match env with
      | .extend env0 (.cvar cs cap) =>
        simp only [EnvTyping, TypeEnv.lookup_tvar] at htyping ⊢
        obtain ⟨hwf_cb, hbound_wf, hbound, _, _, htyping'⟩ := htyping
        -- Apply IH
        have ih_result := a_ih htyping'
        -- Use cweaken for cvar extension
        have hw : Ty.val_denot env0 S.core ≈
                  Ty.val_denot (env0.extend_cvar cs cap) (S.core.rename Rename.succ) := by
          simpa only [TypeEnv.extend_cvar] using cweaken_val_denot (cs := cs) (cap := cap)
        -- Compose IH with weakening
        unfold Denot.ImplyAfter at ih_result ⊢
        intro m' hsub e hd
        exact (Denot.equiv_to_imply hw).1 m' e (ih_result m' hsub e hd)
    | lock Ψ =>
      -- Context extended with a lock binding
      match env with
      | .extend env0 (.lock) =>
        simp only [EnvTyping, TypeEnv.lookup_tvar] at htyping ⊢
        obtain ⟨_, htyping'⟩ := htyping
        have ih_result := a_ih htyping'
        have hw : Ty.val_denot env0 S.core ≈
                  Ty.val_denot (env0.extend_lock) (S.core.rename Rename.succ) := by
          simpa only [TypeEnv.extend_lock] using (lweaken_val_denot : Ty.val_denot env0 S.core ≈
            Ty.val_denot (env0.extend_lock) (S.core.rename Rename.succ))
        unfold Denot.ImplyAfter at ih_result ⊢
        intro m' hsub e hd
        exact (Denot.equiv_to_imply hw).1 m' e (ih_result m' hsub e hd)

lemma sem_subtyp_tvar {X : BVar s .tvar} {S : PureTy s}
  (hlookup : Ctx.LookupTVar Γ X S) :
  SemSubtyp Γ (.tvar X) S.core := by
  -- Unfold SemSubtyp for capturing types
  unfold SemSubtyp
  intro env H htyping _hdsep
  -- Extract the type variable bound using the helper lemma
  have himply := env_typing_lookup_tvar hlookup htyping
  -- The result follows directly from himply
  simpa only [Ty.val_denot] using himply

lemma sem_subtyp_arrow {T1 T2 : Ty .capt s} {cs1 cs2 : CaptureSet s} {U1 U2 : Ty .exi (s,x)}
  (harg : SemSubtyp Γ T2 T1)
  (hcs : SemSubcapt Γ cs1 cs2)
  (hcs2_closed : CaptureSet.IsClosed cs2)
  (hres : SemSubtyp (Γ,x:T2) U1 U2) :
  SemSubtyp Γ (.arrow T1 cs1 U1) (.arrow T2 cs2 U2) := by
  -- Unfold SemSubtyp for capturing types
  unfold SemSubtyp
  intro env H htyping hdsep
  -- Need to prove Denot.ImplyAfter for arrow types
  unfold Denot.ImplyAfter
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
              exact harg env H htyping hdsep m'' (Memory.subsumes_trans hsub hsubsumes)
                (.var (.free arg)) harg_T2
            -- Define the authority sets
            let R0 := expand_captures m'.heap cs'
            let R := R0
            -- Apply hbody at the T1 peak set
            have hbody_spec := hbody arg m'' hsub hcompat harg_T1
            simp only [Ty.exi_exp_denot] at hbody_spec
            -- Transport from psT1 to psT2 using Retype with the identity substitution.
            have hretype :
                Retype (env.extend_var arg psT1) Subst.id
                  (env.extend_var arg psT2) (psT1.rename Rename.succ) :=
              { var := by
                  intro x
                  cases x
                  case here => rfl
                  case there x =>
                    change (env.lookup_var x).1 =
                      interp_var (env.extend_var arg psT2)
                        ((Subst.id.var x).rename Rename.succ)
                    rw [← weaken_interp_var]
                    rfl
                tvar := by
                  intro X
                  cases X with
                  | there X =>
                    change env.lookup_tvar X ≈
                      Ty.val_denot (env.extend_var arg psT2) (Ty.tvar X.there)
                    rw [Ty.val_denot.eq_2]
                    exact Denot.equiv_refl _
                cvar := by
                  intro C
                  cases C
                  case there C =>
                    change (env.lookup_cvar C).1 =
                      ((Subst.id.cvar C).rename Rename.succ).subst
                        (Subst.from_TypeEnv (env.extend_var arg psT2))
                    rfl }
            have heq_val := retype_exi_val_denot (ρ := hretype) U1
            -- Lift the evaluation along the exi-val equivalence
            have h_entails_body :
                Mpost.entails_after
                  (Ty.exi_val_denot (env.extend_var arg psT1) U1).as_mpost m''
                  (Ty.exi_val_denot (env.extend_var arg psT2) U1).as_mpost := by
              apply Mpost.entails_to_entails_after
              exact Denot.imply_to_entails _ _
                (Denot.equiv_to_imply (by simpa [Ty.subst_id] using heq_val)).1
            have hbody_psT2 :
                Eval R m'' (t0.subst (Subst.openVar (.free arg)))
                  (Ty.exi_val_denot (env.extend_var arg psT2) U1).as_mpost :=
              eval_post_monotonic_general h_entails_body hbody_spec
            -- Apply covariance: if body satisfies U1, it also satisfies U2
            -- Build EnvTyping for the extended context with T2's peak set
            have htyping_ext : EnvTyping (Γ,x:T2) (env.extend_var arg psT2) m'' := by
              have htyping_ext_base : EnvTyping (Γ,x:T2) (.extend env (.var arg psT2)) m'' := by
                constructor
                · exact harg_T2
                · constructor
                  · exact (compute_peakset_correct htyping T2.captureSet).symm
                  · have hsub_H_m'' := Memory.subsumes_trans hsub hsubsumes
                    exact env_typing_monotonic htyping hsub_H_m''
              simpa only [TypeEnv.extend_var] using htyping_ext_base
            -- Apply semantic subtyping for the result
            have himply_entails :=
              Denot.imply_after_to_m_entails_after
                (hres (env.extend_var arg psT2) m'' htyping_ext hdsep.extend_var)
            -- Apply monotonicity - goal is already at psT2, no back-rebind needed
            unfold Ty.exi_exp_denot at hbody_psT2 ⊢
            exact eval_post_monotonic_general himply_entails hbody_psT2


lemma sem_subtyp_trans {k : TySort} {T1 T2 T3 : Ty k s}
  (h12 : SemSubtyp Γ T1 T2)
  (h23 : SemSubtyp Γ T2 T3) :
  SemSubtyp Γ T1 T3 := by
  cases k with
  | capt =>
    unfold SemSubtyp at h12 h23 ⊢
    -- For capturing types
    intro env H htyping hdsep
    have h12' := h12 env H htyping hdsep
    have h23' := h23 env H htyping hdsep
    unfold Denot.ImplyAfter at h12' h23' ⊢
    intro m' hsubsumes
    exact Denot.implyat_trans (h12' m' hsubsumes) (h23' m' hsubsumes)
  | exi =>
    unfold SemSubtyp at h12 h23 ⊢
    -- For existential types
    intro env H htyping hdsep
    have h12' := h12 env H htyping hdsep
    have h23' := h23 env H htyping hdsep
    unfold Denot.ImplyAfter at h12' h23' ⊢
    intro m' hsubsumes
    exact Denot.implyat_trans (h12' m' hsubsumes) (h23' m' hsubsumes)

lemma sem_subtyp_refl {k : TySort} {T : Ty k s} :
  SemSubtyp Γ T T := by
  cases k with
  | capt =>
    unfold SemSubtyp
    -- For capturing types
    intro env H htyping _hdsep
    unfold Denot.ImplyAfter
    intro m' hsubsumes
    exact Denot.imply_implyat (Denot.imply_refl _)
  | exi =>
    unfold SemSubtyp
    -- For existential types
    intro env H htyping _hdsep
    unfold Denot.ImplyAfter
    intro m' hsubsumes
    exact Denot.imply_implyat (Denot.imply_refl _)


lemma fundamental_subbound
  (hsub : Subbound Γ B1 B2) :
  SemSubbound Γ B1 B2 := by
  induction hsub with
  | capset hsubcapt =>
    intro env m htyping
    simpa only [CaptureBound.denot] using
      CapabilityBound.SubsetEq.set (fundamental_subcapt hsubcapt env m htyping)
  | top =>
    intro env m htyping
    simpa only [CaptureBound.denot] using
      (CapabilityBound.SubsetEq.top : CapabilityBound.SubsetEq _ .top)


lemma sem_subtyp_cpoly {cb1 cb2 : CaptureBound s} {cs1 cs2 : CaptureSet s} {T1 T2 : Ty .exi (s,C)}
  (hB : SemSubbound Γ cb2 cb1) -- contravariant in bound
  (hcs : SemSubcapt Γ cs1 cs2) -- covariant in capture set
  (hcs2_closed : CaptureSet.IsClosed cs2) -- cs2 is closed
  (hT : SemSubtyp (Γ,C[.access_only]<:cb2) T1 T2) -- covariant in body under tighter bound
  (hclosed_cb2 : cb2.IsClosed)
  : SemSubtyp Γ (.cpoly cb1 cs1 T1) (.cpoly cb2 cs2 T2) := by
  -- Unfold SemSubtyp for capturing types
  unfold SemSubtyp
  intro env H htyping hdsep
  -- Need to prove Denot.ImplyAfter for cpoly types
  unfold Denot.ImplyAfter
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
            intro m'' CS hCS_wf hdf hsub_m'' hcompat hCS_satisfies_cb2
            let A0 := CS.denot TypeEnv.empty
            have hCS_satisfies_cb1 : (A0 m'').BoundedBy (cb1.denot env m'') := by
              have hB_trans := Memory.subsumes_trans hsub_m'' hsubsumes
              have htyping_m'' := env_typing_monotonic htyping hB_trans
              have hB_at_m'' := hB env m'' htyping_m''
              exact CapabilitySet.BoundedBy.trans hCS_satisfies_cb2 hB_at_m''
            -- Apply the original function body with this CS
            have heval1 := hbody m'' CS hCS_wf hdf hsub_m'' hcompat hCS_satisfies_cb1
            -- Now use covariance hT
            have henv' : EnvTyping (Γ,C[.access_only]<:cb2)
                (env.extend_cvar CS (cap := CS.ground_denot m'')) m'' := by
              have henv'_base : EnvTyping (Γ,C[.access_only]<:cb2)
                  (.extend env (.cvar CS (CS.ground_denot m''))) m'' := by
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
                    simp [CaptureSet.denot, Subst.from_TypeEnv_empty, CaptureSet.subst_id]
                  rw [← this]
                  exact hCS_satisfies_cb2
                constructor
                · rfl
                constructor
                · exact hdf
                · have hB_trans := Memory.subsumes_trans hsub_m'' hsubsumes
                  exact env_typing_monotonic htyping hB_trans
              simpa only [TypeEnv.extend_cvar] using henv'_base
            -- GAP: the capture argument `CS` supplied to this abstraction must
            -- be disjoint from every existing droppable cvar to extend
            -- `DroppableSep` — same environment-separation gap family as
            -- `sem_typ_cabs`/`sem_typ_unpack`.
            have hfresh_cpoly : ∀ c, Γ.lookup_authority c = .can_drop →
                CapabilitySet.disjoint (env.lookup_cvar c).2 (CS.ground_denot m'') := by
              sorry
            have himply_entails :=
              Denot.imply_after_to_m_entails_after
                (hT (env.extend_cvar CS (cap := CS.ground_denot m'')) m'' henv'
                  (hdsep.extend_cvar_access_only hfresh_cpoly))
            -- Use eval_post_monotonic_general to lift heval1 from T1 to T2
            unfold Ty.exi_exp_denot at heval1 ⊢
            exact eval_post_monotonic_general himply_entails heval1

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
  (hT : SemSubtyp (Γ,C[.can_drop]<:.unbound) T1 T2) -- covariant in body
  : SemSubtyp Γ (.exi T1) (.exi T2) := by
  unfold SemSubtyp
  intro env H htyping hdsep
  unfold Denot.ImplyAfter Denot.ImplyAt
  intro m hsubsumes e h_exi_T1
  simp only [Ty.exi_val_denot] at h_exi_T1 ⊢
  cases hresolve : resolve m.heap e with
  | none =>
    simp [hresolve] at h_exi_T1
  | some cell =>
    simp only [hresolve, List.empty_eq] at h_exi_T1 ⊢
    cases cell with
    | pack CS x =>
      obtain ⟨hwf_CS, hdf_CS, h_body_T1⟩ := h_exi_T1
      refine ⟨hwf_CS, hdf_CS, ?_⟩
      have henv' : EnvTyping (Γ,C[.can_drop]<:.unbound)
          (env.extend_cvar CS (cap := CS.ground_denot m)) m := by
        have henv'_base :
            EnvTyping (Γ,C[.can_drop]<:.unbound)
              (.extend env (.cvar CS (CS.ground_denot m))) m := by
          constructor
          · exact hwf_CS
          constructor
          · simp only [List.empty_eq]
            exact CaptureBound.WfInHeap.wf_unbound
          constructor
          · simp only [CaptureBound.denot]
            exact CapabilitySet.BoundedBy.top
          constructor
          · rfl
          constructor
          · exact hdf_CS
          · exact env_typing_monotonic htyping hsubsumes
        simpa only [TypeEnv.extend_cvar] using henv'_base
      -- GAP: the packed witness `CS` must be disjoint from every existing
      -- cvar to extend `DroppableSep` — the same environment-separation
      -- invariant as in `sem_typ_unpack`.
      have hfresh_exi : ∀ c,
          CapabilitySet.disjoint (CS.ground_denot m) (env.lookup_cvar c).2 := by
        sorry
      have hT_sem := hT (env.extend_cvar CS (cap := CS.ground_denot m)) m henv'
        (hdsep.extend_cvar_can_drop hfresh_exi)
      unfold Denot.ImplyAfter Denot.ImplyAt at hT_sem
      exact hT_sem m (Memory.subsumes_refl m) (.var x) h_body_T1
    | _ =>
      cases h_exi_T1

lemma sem_subtyp_typ {T1 T2 : Ty .capt s}
  (hT : SemSubtyp Γ T1 T2) -- covariant in body
  : SemSubtyp Γ (.typ T1) (.typ T2) := by
  -- Unfold SemSubtyp for exi types
  unfold SemSubtyp
  intro env H htyping hdsep
  -- Unfold exi_val_denot for .typ
  -- .typ T has denotation capt_val_denot env T
  simp only [Ty.exi_val_denot]
  -- The goal is now: (capt_val_denot env T1).ImplyAfter H (capt_val_denot env T2)
  -- Which is exactly SemSubtyp Γ T1 T2 (for capt types)
  exact hT env H htyping hdsep


lemma sem_subtyp_poly {S1 S2 : PureTy s} {cs1 cs2 : CaptureSet s} {T1 T2 : Ty .exi (s,X)}
  (hS : SemSubtyp Γ S2.core S1.core) -- contravariant in bound
  (hcs : SemSubcapt Γ cs1 cs2) -- covariant in capture set
  (hcs2_closed : CaptureSet.IsClosed cs2) -- cs2 is closed
  (hT : SemSubtyp (Γ,X<:S2) T1 T2) -- covariant in body under tighter bound
  : SemSubtyp Γ (.poly S1.core cs1 T1) (.poly S2.core cs2 T2) := by
  -- Unfold SemSubtyp for capturing types
  unfold SemSubtyp
  intro env H htyping hdsep
  -- Need to prove Denot.ImplyAfter for poly types
  unfold Denot.ImplyAfter
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
              unfold Denot.ImplyAfter Denot.ImplyAt
              intro m''' hsub_m''' e' hdenot_e
              unfold Denot.ImplyAfter Denot.ImplyAt at himply_S2
              have hS2 := himply_S2 m''' hsub_m''' e' hdenot_e
              have hS_trans :=
                Memory.subsumes_trans hsub_m''' (Memory.subsumes_trans hsub_m'' hsubsumes)
              have hS_sem := hS env H htyping hdsep
              unfold Denot.ImplyAfter Denot.ImplyAt at hS_sem
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
            have hT_sem := hT (env.extend_tvar denot) m'' henv' hdsep.extend_tvar
            -- Convert to postcondition entailment
            have himply_entails := Denot.imply_after_to_m_entails_after hT_sem
            -- Use eval_post_monotonic_general to lift heval1 from T1 to T2
            unfold Ty.exi_exp_denot at heval1 ⊢
            exact eval_post_monotonic_general himply_entails heval1

lemma sem_subtyp_modal {cs1 cs2 : CaptureSet s} {Ψ : SepCtx s} {E1 E2 : Ty .exi s}
  (hcs : SemSubcapt Γ cs1 cs2)
  (hcs2_closed : CaptureSet.IsClosed cs2)
  (hΨ_closed : SepCtx.IsClosed Ψ)
  (hT : SemSubtyp (Γ.push_lock Ψ) (E1.rename Rename.succ) (E2.rename Rename.succ)) :
  SemSubtyp Γ (.modal cs1 Ψ E1) (.modal cs2 Ψ E2) := by
  unfold SemSubtyp
  intro env H htyping hdsep
  unfold Denot.ImplyAfter
  intro m' hsubsumes e h_modal
  simp only [Ty.val_denot] at h_modal ⊢
  obtain ⟨hwf_e, hcs1_wf, cs0, sepctx0, t0, hresolve, hcs0_wf, hsepctx0_wf,
    hsat_impl, hR0_sub, hbody⟩ := h_modal
  constructor
  · exact hwf_e
  · constructor
    · have hwf_cs2_at_H : (cs2.subst (Subst.from_TypeEnv env)).WfInHeap H.heap := by
        exact CaptureSet.wf_subst (CaptureSet.wf_of_closed hcs2_closed)
                                  (from_TypeEnv_wf_in_heap htyping)
      exact CaptureSet.wf_monotonic hsubsumes hwf_cs2_at_H
    · refine ⟨cs0, sepctx0, t0, hresolve, hcs0_wf, hsepctx0_wf, ?_, ?_, ?_⟩
      · intro m'' hsubm'' hsat
        exact hsat_impl m'' hsubm'' hsat
      · have hcs_sem := hcs env m' (env_typing_monotonic htyping hsubsumes)
        calc expand_captures m'.heap cs0
          _ ⊆ cs1.denot env m' := hR0_sub
          _ ⊆ cs2.denot env m' := hcs_sem
      · intro m'' hsubm'' hcompat hkind hsep
        have heval1 := hbody m'' hsubm'' hcompat hkind hsep
        have heval1_eval :
            Eval (expand_captures m'.heap cs0) m'' t0
              (Ty.exi_val_denot env E1).as_mpost := by
          simpa [Ty.exi_exp_denot] using heval1
        have htyping_m'' := env_typing_monotonic htyping (Memory.subsumes_trans hsubm'' hsubsumes)
        have hsat_Ψ : env.Satisfy Ψ m'' := by
          constructor
          · intro C mode hhas
            exact CaptureSet.wf_subst (SepCtx.WfInHeap.of_has (SepCtx.wf_of_closed hΨ_closed) hhas)
                                      (from_TypeEnv_wf_in_heap htyping_m'')
          · intro C mode hhas
            exact hkind C mode hhas
          · intro C1 m1 C2 m2 hdistinct
            exact hsep C1 m1 C2 m2 hdistinct
        have htyping_lock : EnvTyping (Γ.push_lock Ψ) (env.extend_lock) m'' := by
          constructor
          · exact hsat_Ψ
          · exact htyping_m''
        have himply_entails :=
          Denot.imply_after_to_m_entails_after
            (hT (env.extend_lock) m'' htyping_lock hdsep.extend_lock)
        have heval1' :
            Eval (expand_captures m'.heap cs0) m'' t0
              (Ty.exi_val_denot (env.extend_lock) (E1.rename Rename.succ)).as_mpost := by
          apply eval_post_monotonic _ heval1_eval
          exact Denot.imply_to_entails _ _
            (Denot.equiv_to_imply (lweaken_exi_val_denot (env := env) (T := E1))).1
        have heval2' :
            Eval (expand_captures m'.heap cs0) m'' t0
              (Ty.exi_val_denot (env.extend_lock) (E2.rename Rename.succ)).as_mpost := by
          exact eval_post_monotonic_general himply_entails heval1'
        simpa [Ty.exi_exp_denot] using
          (eval_post_monotonic
            ((Denot.imply_to_entails _ _
              ((Denot.equiv_to_imply (lweaken_exi_val_denot (env := env) (T := E2))).2)))
            heval2')

lemma sem_subtyp_modal_modal {cs : CaptureSet s} {Ψ1 Ψ2 : SepCtx s} {E : Ty .exi s}
  (hΨ1_closed : SepCtx.IsClosed Ψ1)
  (hΨ2_closed : SepCtx.IsClosed Ψ2)
  (hsat : Satisfy (Γ.push_lock Ψ2) (Ψ1.rename Rename.succ)) :
  SemSubtyp Γ (.modal cs Ψ1 E) (.modal cs Ψ2 E) := by
  unfold SemSubtyp
  intro env H htyping hdsep
  unfold Denot.ImplyAfter
  intro m' hsubsumes e h_modal
  simp only [Ty.val_denot] at h_modal ⊢
  obtain ⟨hwf_e, hcs_wf, cs0, sepctx0, t0, hresolve, hcs0_wf, hsepctx0_wf,
    hsat_impl, hR0_sub, hbody⟩ := h_modal
  constructor
  · exact hwf_e
  · constructor
    · exact hcs_wf
    · refine ⟨cs0, sepctx0, t0, hresolve, hcs0_wf, hsepctx0_wf, ?_, hR0_sub, ?_⟩
      · intro m'' hsubm'' hsat_Ψ2
        have htyping_m'' := env_typing_monotonic htyping (Memory.subsumes_trans hsubm'' hsubsumes)
        have htyping_lock : EnvTyping (Γ.push_lock Ψ2) (env.extend_lock) m'' := by
          constructor
          · exact hsat_Ψ2
          · exact htyping_m''
        have hsat_ren := sem_satisfy (SepCtx.rename_closed hΨ1_closed) hsat
          (env.extend_lock) m'' htyping_lock hdsep.extend_lock
        have hsat_Ψ1 := (TypeEnv.satisfy_lweaken_iff (env := env) (Ψ := Ψ1) (m := m'')).mp hsat_ren
        exact hsat_impl m'' hsubm'' hsat_Ψ1
      · intro m'' hsubm'' hcompat hkind hsep
        have htyping_m'' := env_typing_monotonic htyping (Memory.subsumes_trans hsubm'' hsubsumes)
        have hsat_Ψ2 : env.Satisfy Ψ2 m'' := by
          constructor
          · intro C mode hhas
            exact CaptureSet.wf_subst (SepCtx.WfInHeap.of_has (SepCtx.wf_of_closed hΨ2_closed) hhas)
                                      (from_TypeEnv_wf_in_heap htyping_m'')
          · intro C mode hhas
            exact hkind C mode hhas
          · intro C1 m1 C2 m2 hdistinct
            exact hsep C1 m1 C2 m2 hdistinct
        have htyping_lock : EnvTyping (Γ.push_lock Ψ2) (env.extend_lock) m'' := by
          constructor
          · exact hsat_Ψ2
          · exact htyping_m''
        have hsat_ren := sem_satisfy (SepCtx.rename_closed hΨ1_closed) hsat
          (env.extend_lock) m'' htyping_lock hdsep.extend_lock
        have hsat_Ψ1 := (TypeEnv.satisfy_lweaken_iff (env := env) (Ψ := Ψ1) (m := m'')).mp hsat_ren
        exact hbody m'' hsubm'' hcompat
          (fun C mode hhas => hsat_Ψ1.kind C mode hhas)
          (fun C1 m1 C2 m2 hdistinct => hsat_Ψ1.sep C1 m1 C2 m2 hdistinct)

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
  case modal hsub_cs hsub_body ih_body =>
    cases hT1 with
    | modal _ hΨ_closed hE1_closed =>
      cases hT2 with
      | modal hcs2_closed _ hE2_closed =>
        apply sem_subtyp_modal
        · exact fundamental_subcapt hsub_cs
        · exact hcs2_closed
        · exact hΨ_closed
        · exact ih_body (Ty.rename_closed hE1_closed) (Ty.rename_closed hE2_closed)
  case modal_modal hsat =>
    cases hT1 with
    | modal _ hΨ1_closed _ =>
      cases hT2 with
      | modal _ hΨ2_closed _ =>
        exact sem_subtyp_modal_modal hΨ1_closed hΨ2_closed hsat
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
  intro env m htyping hdsep hcompat
  simp only [Ty.exi_exp_denot, List.empty_eq]
  -- The budget shrinks from C2 to C1 via subcapturing.
  have hsubcapt_sem := fundamental_subcapt hsubcapt env m htyping
  have hcompat_C1 : m.is_compatible (C1.denot env m) :=
    Memory.is_compatible_subset hsubcapt_sem hcompat
  have h_eval_E1 := ht env m htyping hdsep hcompat_C1
  simp only [Ty.exi_exp_denot, List.empty_eq] at h_eval_E1
  -- Lift the evaluation from C1 to C2 using capability set monotonicity
  have h_eval_E1_at_C2 := eval_capability_set_monotonic h_eval_E1 hsubcapt_sem
  -- Use fundamental_subtyp to get E1 <: E2 semantically
  have hsubtyp_sem := fundamental_subtyp hclosed_E1 hclosed_E2 hsubtyp env m htyping hdsep
  have h_entails := Denot.imply_after_to_m_entails_after hsubtyp_sem
  exact eval_post_monotonic_general h_entails h_eval_E1_at_C2

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

/-- Semantic typing for `unpack`. As with `letin`, the inductive
    `SeqComp Γ C1 C2` premise (`hseq`) is threaded to `eval_unpack`'s `hseq`
    premise via the `captureSet_seqcomp_denot` bridge. The rest of the
    construction does not rely on it: `eval_unpack`'s `h_val` premise *assumes*
    `m1.is_compatible (C2 ∪ R ∪ R.to_drop)` (R = the unpacked capability's
    reachability), so we never derive it from `e1`. The body use-set's
    `.drop`-qualified cvar `(.cvar .drop (.there .here))` denotes exactly to
    `R.to_drop`, matching `eval_unpack`'s budget; the `.M .epsilon` cvar denotes
    to `R`; and the doubly-renamed `C2` (closed) is memory-stable. -/
theorem sem_typ_unpack
  {C1 C2 : CaptureSet s} {Γ : Ctx s} {t : Exp s} {T : Ty .capt (s,C)}
  {u : Exp (s,C,x)} {U : Ty .exi s}
  (hseq : SeqComp Γ C1 C2)
  (hΓ : Γ.IsClosed)
  (_hclosed_C1 : C1.IsClosed)
  (hclosed_C2 : C2.IsClosed)
  (ht : C1 # Γ ⊨ t : .exi T)
  (hu : ((C2.rename Rename.succ).rename Rename.succ ∪ (.cvar (.M .epsilon) (.there .here))
          ∪ (.cvar .drop (.there .here))) #
        (Γ.push_cvar .can_drop .unbound,x:T) ⊨ u : (U.rename Rename.succ).rename Rename.succ) :
  C1 ∪ C2 # Γ ⊨ (Exp.unpack t u) : U := by
  intro env store hts hdsep hcompat
  simp only [Ty.exi_exp_denot, Exp.subst, List.empty_eq]
  have hunion_denot :
      (C1 ∪ C2).denot env store = C1.denot env store ∪ C2.denot env store := rfl
  apply Eval.eval_unpack (Q1 := fun v m' => Ty.exi_val_denot env (.exi T) m' v)
    (C1 := C1.denot env store) (C2 := C2.denot env store)
  case hpred =>
    intro m1 m2 e hwf hsub hQ
    exact exi_val_denot_is_monotonic (typed_env_is_monotonic hts) (.exi T) hsub hQ
  case hbool =>
    intro m'
    exact exi_val_denot_is_bool_independent (typed_env_is_bool_independent hts) (.exi T)
  case a =>
    have hsubC1 : C1.denot env store ⊆ (C1 ∪ C2).denot env store := by
      rw [hunion_denot]; exact CapabilitySet.Subset.union_right_left
    have h1 := ht env store hts hdsep (Memory.is_compatible_subset hsubC1 hcompat)
    simpa only [Ty.exi_exp_denot] using h1
  case h_nonstuck =>
    intro m1 v hQ1
    change Ty.exi_val_denot env (.exi T) m1 v at hQ1
    simp only [Ty.exi_val_denot] at hQ1
    cases hres : resolve m1.heap v with
    | none => simp only [hres] at hQ1
    | some exp =>
      simp only [hres] at hQ1
      cases exp <;> simp only [List.empty_eq] at hQ1
      rename_i CS x_pack
      obtain ⟨hwf_CS, hQ1_body⟩ := hQ1
      constructor
      · exact resolve_is_pack hres Exp.IsPack.pack
      · have hv_pack : v.IsPack := resolve_is_pack hres Exp.IsPack.pack
        have heq : v = .pack CS x_pack := resolve_pack_eq hres hv_pack
        rw [heq]
        apply Exp.WfInHeap.wf_pack
        · exact hwf_CS
        · have hwf_env : (env.extend_cvar CS (cap := CS.ground_denot m1)).is_implying_wf := by
            intro X
            cases X with
            | there X' =>
              simpa only [TypeEnv.lookup_tvar] using typed_env_is_implying_wf hts X'
          have hwf_exp := val_denot_implies_wf hwf_env T m1 (.var x_pack) hQ1_body.2
          cases hwf_exp with
          | wf_var hwf_v => exact hwf_v
  case h_val =>
    intro m1 x cs hs1 hcompat_m1 hwf_x hwf_cs hQ1
    change Ty.exi_val_denot env (.exi T) m1 (.pack cs x) at hQ1
    simp only [Ty.exi_val_denot, List.empty_eq] at hQ1
    cases x
    case bound bx => cases bx
    case free fx =>
      obtain ⟨hwf_cs2, hdf_cs, hQ1_body⟩ := hQ1
      let ps := CaptureSet.peakset (Γ.push_cvar .can_drop .unbound) T.captureSet
      let env' := env.extend_cvar cs (cap := cs.ground_denot m1)
      have hts_extended :
          EnvTyping (Γ.push_cvar .can_drop .unbound,x:T) (env'.extend_var fx ps) m1 := by
        constructor
        · exact hQ1_body
        · constructor
          · rfl
          · constructor
            · exact hwf_cs2
            constructor
            · simpa only [List.empty_eq] using CaptureBound.WfInHeap.wf_unbound
            constructor
            · simpa only [List.empty_eq] using CapabilitySet.BoundedBy.top
            constructor
            · rfl
            constructor
            · exact hdf_cs  -- unpacked witness drop-free (from the exi denotation)
            · exact env_typing_monotonic hts hs1
      have hReq : cs.ground_denot m1 = cs.reachability m1 :=
        CaptureSet.ground_denot_eq_reachability cs m1
      have hcvar_denot :
          (CaptureSet.cvar (.M .epsilon) (.there .here)).denot (env'.extend_var fx ps) m1
            = cs.ground_denot m1 := by
        have hc : (CaptureSet.cvar (.M .epsilon) (.there .here)).denot (env'.extend_var fx ps) m1
            = (CaptureSet.cvar (.M .epsilon) .here).denot env' m1 :=
          (congrFun (rebind_captureset_denot (Rebind.weaken (env:=env') (x:=fx) (ps:=ps))
            (CaptureSet.cvar (.M .epsilon) .here)) m1).symm
        rw [hc]
        rfl
      have hcvar_drop_denot :
          (CaptureSet.cvar .drop (.there .here)).denot (env'.extend_var fx ps) m1
            = (cs.ground_denot m1).to_drop := by
        have hc : (CaptureSet.cvar .drop (.there .here)).denot (env'.extend_var fx ps) m1
            = (CaptureSet.cvar .drop .here).denot env' m1 :=
          (congrFun (rebind_captureset_denot (Rebind.weaken (env:=env') (x:=fx) (ps:=ps))
            (CaptureSet.cvar .drop .here)) m1).symm
        rw [hc]
        change (cs.applyAccess .drop).ground_denot m1 = (cs.ground_denot m1).to_drop
        rw [captureSet_ground_denot_applyAccess_comm, CapabilitySet.applyAccess_drop]
      have hrebind2 : ∀ (Cx : CaptureSet s),
          ((Cx.rename Rename.succ).rename Rename.succ).denot (env'.extend_var fx ps) m1
            = Cx.denot env m1 := by
        intro Cx
        have h1 := rebind_captureset_denot
          (Rebind.cweaken (env:=env) (cs:=cs) (cap:=cs.ground_denot m1)) Cx
        have h2 := rebind_captureset_denot
          (Rebind.weaken (env:=env') (x:=fx) (ps:=ps)) (Cx.rename Rename.succ)
        exact (congrFun h2.symm m1).trans (congrFun h1.symm m1)
      have hbudget_denot :
          ((C2.rename Rename.succ).rename Rename.succ
              ∪ (CaptureSet.cvar (.M .epsilon) (.there .here))
              ∪ (CaptureSet.cvar .drop (.there .here))).denot (env'.extend_var fx ps) m1
          = C2.denot env m1 ∪ cs.ground_denot m1 ∪ (cs.ground_denot m1).to_drop := by
        change ((C2.rename Rename.succ).rename Rename.succ).denot (env'.extend_var fx ps) m1
            ∪ (CaptureSet.cvar (.M .epsilon) (.there .here)).denot (env'.extend_var fx ps) m1
            ∪ (CaptureSet.cvar .drop (.there .here)).denot (env'.extend_var fx ps) m1
          = C2.denot env m1 ∪ cs.ground_denot m1 ∪ (cs.ground_denot m1).to_drop
        rw [hrebind2 C2, hcvar_denot, hcvar_drop_denot]
      have hexp_eq :
          (u.subst (Subst.from_TypeEnv env).lift.lift).subst (Subst.unpack cs (Var.free fx)) =
          u.subst (Subst.from_TypeEnv (env'.extend_var fx ps)) := by
        rw [Exp.subst_comp]
        have h1 := congrArg (u.subst) (@Subst.from_TypeEnv_weaken_unpack s env cs fx ps)
        exact h1.trans (congrArg (u.subst)
          Subst.from_TypeEnv_extend_cvar_extend_var_cap_irrelevant)
      have heqv_composed : Ty.exi_val_denot env U ≈
        Ty.exi_val_denot (env'.extend_var fx ps)
          ((U.rename Rename.succ).rename Rename.succ) := by
        have heqv1 := rebind_exi_val_denot
          (Rebind.cweaken (env:=env) (cs:=cs) (cap:=cs.ground_denot m1)) U
        have heqv2 := rebind_exi_val_denot
          (Rebind.weaken (env:=env') (x:=fx) (ps:=ps)) (U.rename Rename.succ)
        intro m e
        exact Iff.trans (heqv1 m e) (heqv2 m e)
      have hC2_mono : C2.denot env m1 = C2.denot env store :=
        (closed_capture_denot_monotonic hclosed_C2 hts hs1).symm
      have hcompat_body :
          m1.is_compatible
            (((C2.rename Rename.succ).rename Rename.succ
                ∪ (CaptureSet.cvar (.M .epsilon) (.there .here))
                ∪ (CaptureSet.cvar .drop (.there .here))).denot (env'.extend_var fx ps) m1) := by
        rw [hbudget_denot, hC2_mono, hReq]
        exact hcompat_m1
      -- GAP (the only `sorry`): the freshly-unpacked capability `cs` is disjoint
      -- from every existing cvar. This is the operational freshness / separation
      -- invariant — an unpacked capability does not alias any capability already
      -- tracked by `env`. Its justification needs the compatibility (`hcompat_m1`)
      -- and `SeqComp` (`hseq`) history of this unpack; it is the same
      -- environment-separation gap as `captureSet_seqcomp_denot`.
      have hfresh : ∀ c,
          CapabilitySet.disjoint (cs.ground_denot m1) (env.lookup_cvar c).2 := by
        sorry
      have hdsep_ext :
          DroppableSep (Γ.push_cvar .can_drop .unbound,x:T) (env'.extend_var fx ps) :=
        (hdsep.extend_cvar_can_drop hfresh).extend_var
      have hu'' := hu (env'.extend_var fx ps) m1 hts_extended hdsep_ext hcompat_body
      simp only [Ty.exi_exp_denot] at hu''
      change Eval (C2.denot env store ∪ cs.reachability m1 ∪ (cs.reachability m1).to_drop) m1
        ((u.subst (Subst.from_TypeEnv env).lift.lift).subst (Subst.unpack cs (Var.free fx)))
        (fun v m' => Ty.exi_val_denot env U m' v)
      rw [hexp_eq]
      have hsub_budget :
          ((C2.rename Rename.succ).rename Rename.succ
              ∪ (CaptureSet.cvar (.M .epsilon) (.there .here))
              ∪ (CaptureSet.cvar .drop (.there .here))).denot (env'.extend_var fx ps) m1
            ⊆ C2.denot env store ∪ cs.reachability m1 ∪ (cs.reachability m1).to_drop := by
        rw [hbudget_denot, hC2_mono, hReq]
        exact CapabilitySet.Subset.refl
      have hcompose := eval_capability_set_monotonic hu'' hsub_budget
      apply eval_post_monotonic _ hcompose
      exact Denot.imply_to_entails _ _ (Denot.equiv_to_imply heqv_composed).2
  case hseq =>
    exact captureSet_seqcomp_denot hts hΓ hdsep hseq
  case hagg =>
    rw [hunion_denot]
    exact CapabilitySet.Subset.refl

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
  Subcapt Γ (.var (.M m) (.bound x)) (T.captureSet.applyMut m) := by
  cases m with
  | epsilon =>
    simpa [CaptureSet.applyMut] using (Subcapt.sc_var hlk)
  | ro =>
    simpa [CaptureSet.applyMut]
      using (Subcapt.sc_ro_mono (Subcapt.sc_var hlk))

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
  (CaptureSet.var (.M m) (.bound x)).denot env H ⊆ (T.captureSet.applyMut m).denot env H := by
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
             CaptureSet.ground_denot, CapabilitySet.applyAccess_M]
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
    them). -/
theorem var_typing_extract_closed
    {Γ : Ctx s} {x : BVar s .var} {E : Ty .exi s}
    (ht : C # Γ ⊢ Exp.var (.bound x) : E) :
    Γ.IsClosed := by
  generalize hexpr : Exp.var (Var.bound x) = e at ht
  induction ht
  case var hclosed hlk =>
    cases hexpr
    exact hclosed
  case subtyp _ _ _ _ _ ih => exact ih hexpr
  all_goals (cases hexpr)

theorem sem_typ_unwrap
  {x : BVar s .var} {Ψ : SepCtx s} {E : Ty .exi s}
  (hclosed_Ψ : Ψ.IsClosed)
  (hx : {} # Γ ⊨ Exp.var (.bound x) :
    .typ (.modal (.var (.M .epsilon) (.bound x)) Ψ E))
  (hsatisfy : Satisfy Γ Ψ) :
  (CaptureSet.var (.M .epsilon) (.bound x)) # Γ ⊨ Exp.unwrap (.bound x) : E := by
  intro env store hts hdsep hcompat
  have hmodal_exp :
      Ty.exi_exp_denot env (.typ (.modal (.var (.M .epsilon) (.bound x)) Ψ E))
        (CaptureSet.denot env {} store) store
        (.var (.free (env.lookup_var x).1)) := by
    simpa [Exp.subst, Var.subst, Subst.from_TypeEnv] using
      hx env store hts hdsep (Memory.is_compatible_empty store)
  have hmodal := var_exp_denot_inv hmodal_exp
  simp only [Ty.exi_val_denot, Ty.val_denot, List.empty_eq] at hmodal
  obtain ⟨_hwf_e, _hwf_cs, cs0, sepctx0, t0, hres, _hwf_cs0,
    _hwf_sepctx0, hsat_impl, hR0_sub, hbody⟩ := hmodal
  have hsat_Ψ : env.Satisfy Ψ store := sem_satisfy hclosed_Ψ hsatisfy env store hts hdsep
  have hcompat_body : store.is_compatible (expand_captures store.heap cs0) :=
    Memory.is_compatible_subset hR0_sub hcompat
  have hbody_eval :
      Eval (expand_captures store.heap cs0) store t0
        (Denot.as_mpost (Ty.exi_val_denot env E)) := by
    simpa [Ty.exi_exp_denot] using
      hbody store (Memory.subsumes_refl store) hcompat_body
        (fun C mode hhas => hsat_Ψ.kind C mode hhas)
        (fun C1 m1 C2 m2 hdistinct => hsat_Ψ.sep C1 m1 C2 m2 hdistinct)
  simp only [Ty.exi_exp_denot, Exp.subst, Var.subst, Subst.from_TypeEnv, List.empty_eq]
  simp only [resolve] at hres
  cases hcell : store.heap (env.lookup_var x).1 with
  | none =>
    simp [hcell] at hres
  | some cell =>
    simp only [hcell] at hres
    cases cell with
    | val v =>
      cases v with
      | mk unwrap isVal reachability =>
        injection hres with h
        subst h
        exact Eval.eval_unwrap
          (m := store)
          (x := (env.lookup_var x).1)
          (cs := cs0)
          (Ψ := sepctx0)
          (e := t0)
          (hv := isVal)
          (R := reachability)
          (by simp [Memory.lookup, hcell])
          (by exact eval_capability_set_monotonic hbody_eval hR0_sub)
    | capability cap =>
      simp at hres
    | masked =>
      simp at hres

/-- The fundamental theorem of semantic type soundness. -/
theorem fundamental
  (hΓ : Γ.IsClosed)
  (ht : C # Γ ⊢ e : T) :
  C # Γ ⊨ e : T := by
  have hclosed_e := HasType.exp_is_closed ht
  induction ht
  case var _ hx =>
    exact sem_typ_var hx
  case reader hΓ_closed hx =>
    exact sem_typ_reader hΓ_closed hx
  case abs ih =>
    apply sem_typ_abs
    · exact hclosed_e
    · cases hclosed_e
      rename_i hclosed_cs hclosed_T1 hclosed_e0
      exact ih (Ctx.IsClosed.push hΓ (Binding.IsClosed.var hclosed_T1)) hclosed_e0
  case tabs ih =>
    apply sem_typ_tabs
    · exact hclosed_e
    · cases hclosed_e
      rename_i hclosed_cs hclosed_S hclosed_e0
      exact ih (Ctx.IsClosed.push hΓ (Binding.IsClosed.tvar hclosed_S)) hclosed_e0
  case cabs ih =>
    apply sem_typ_cabs
    · exact hclosed_e
    · cases hclosed_e
      rename_i hclosed_cs hclosed_cb hclosed_e0
      exact ih (Ctx.IsClosed.push hΓ (Binding.IsClosed.cvar hclosed_cb)) hclosed_e0
  case wrap =>
    rename_i hΨ_closed ht_body ih
    cases hclosed_e with
    | boxed hclosed_cs hclosed_Ψ hclosed_body =>
      exact sem_typ_wrap (Exp.IsClosed.boxed hclosed_cs hclosed_Ψ hclosed_body)
        (ih (Ctx.IsClosed.push hΓ (Binding.IsClosed.lock hclosed_Ψ))
          (HasType.exp_is_closed ht_body))
  case pack ih =>
    rename_i _hC_closed hvalid_cs _hdroppable hx_syn
    cases hclosed_e with
    | pack hcs_closed hx_closed =>
      cases hx_closed
      apply sem_typ_pack
      · exact Exp.IsClosed.pack hcs_closed Var.IsClosed.bound
      · exact var_typing_extract_closed hx_syn
      · exact hvalid_cs
      · exact ih hΓ (Exp.IsClosed.var Var.IsClosed.bound)
  case app =>
    rename_i hx_syn _hy_syn hx_ih hy_ih
    cases hclosed_e with
    | app hx_closed hy_closed =>
      cases hx_closed
      cases hy_closed
      exact sem_typ_app
        (hx_ih hΓ (Exp.IsClosed.var Var.IsClosed.bound))
        (hy_ih hΓ (Exp.IsClosed.var Var.IsClosed.bound))
  case tapp =>
    rename_i _hS_closed hx_syn hx_ih
    cases hclosed_e with
    | tapp hx_closed hS_closed =>
      cases hx_closed
      exact sem_typ_tapp (hx_ih hΓ (Exp.IsClosed.var Var.IsClosed.bound))
  case capp =>
    rename_i hD_closed hvalid_D hx_syn hx_ih
    cases hclosed_e with
    | capp hx_closed hD_closed_exp =>
      cases hx_closed
      have hx := hx_ih hΓ (Exp.IsClosed.var Var.IsClosed.bound)
      exact sem_typ_capp (var_typing_extract_closed hx_syn) hD_closed_exp hvalid_D hx
  case unwrap =>
    rename_i x Ψ E hx hsatisfy ih_x
    have hx_closed := HasType.typed_var_closed hx
    cases x with
    | free fx =>
      cases hx_closed
    | bound bx =>
      have hclosed_Ψ : Ψ.IsClosed := by
        cases HasType.type_is_closed hx with
        | typ hclosed_modal =>
          cases hclosed_modal with
          | modal _ hclosed_Ψ _ =>
            exact hclosed_Ψ
      exact sem_typ_unwrap (x := bx) hclosed_Ψ
        (ih_x hΓ (by constructor; constructor))
        hsatisfy
  case invoke =>
    rename_i hx_syn _hy_syn ih_x ih_y
    cases hclosed_e with
    | app hx_closed hy_closed =>
      cases hx_closed
      cases hy_closed
      exact sem_typ_invoke
        (ih_x hΓ (Exp.IsClosed.var Var.IsClosed.bound))
        (ih_y hΓ (Exp.IsClosed.var Var.IsClosed.bound))
  case unit => exact sem_typ_unit
  case btrue => exact sem_typ_btrue
  case bfalse => exact sem_typ_bfalse
  case cond ht1 ht2 ht3 ih1 ih2 ih3 =>
    cases hclosed_e with
    | cond hclosed_guard hclosed_then hclosed_else =>
      exact sem_typ_cond
        (ih1 hΓ (Exp.IsClosed.var hclosed_guard)) (ih2 hΓ hclosed_then) (ih3 hΓ hclosed_else)
  case alloc =>
    rename_i hx_syn hx_ih
    cases hclosed_e with
    | alloc hx_closed =>
      cases hx_closed
      exact sem_typ_alloc
        (hx_ih hΓ (Exp.IsClosed.var Var.IsClosed.bound))
  case drop =>
    rename_i hΓ_closed _hdroppable hx_syn hx_ih
    cases hclosed_e with
    | drop hx_closed =>
      cases hx_closed
      exact sem_typ_drop
        (hx_ih hΓ (Exp.IsClosed.var Var.IsClosed.bound))
        hΓ_closed
  case read =>
    rename_i hx_syn hx_ih
    cases hclosed_e with
    | read hx_closed =>
      cases hx_closed
      exact sem_typ_read hΓ
        (hx_ih hΓ (Exp.IsClosed.var Var.IsClosed.bound))
  case write =>
    rename_i hx_syn _hy_syn hx_ih hy_ih
    cases hclosed_e with
    | write hx_closed hy_closed =>
      cases hx_closed
      cases hy_closed
      exact sem_typ_write hΓ
        (hx_ih hΓ (Exp.IsClosed.var Var.IsClosed.bound))
        (hy_ih hΓ (Exp.IsClosed.var Var.IsClosed.bound))
  case par ht1_syn ht2_syn hsep_syn ht1_ih ht2_ih =>
    cases hclosed_e with
    | par hclosed_e1 hclosed_e2 =>
      exact sem_typ_par
        (ht1_ih hΓ hclosed_e1)
        (ht2_ih hΓ hclosed_e2)
        (fundamental_sepcheck hsep_syn)
  case letin =>
    rename_i hseq ht1_syn ht2_syn ht1_ih ht2_ih
    cases hclosed_e with
    | letin he1_closed he2_closed =>
      apply sem_typ_letin hseq hΓ
        (HasType.use_set_is_closed ht1_syn)
        (CaptureSet.rename_closed_inv (HasType.use_set_is_closed ht2_syn))
        (Exp.IsClosed.letin he1_closed he2_closed)
        (ht1_ih hΓ he1_closed)
      apply ht2_ih ?_ he2_closed
      cases HasType.type_is_closed ht1_syn with
      | typ hT => exact Ctx.IsClosed.push hΓ (Binding.IsClosed.var hT)
  case subtyp ht_syn hsubcapt hsubtyp hclosed_C2 hclosed_E2 ht_ih =>
    have hclosed_C1 := HasType.use_set_is_closed ht_syn
    have hclosed_E1 := HasType.type_is_closed ht_syn
    exact sem_typ_subtyp (ht_ih hΓ hclosed_e) hsubcapt hsubtyp
      hclosed_C1 hclosed_E1 hclosed_C2 hclosed_E2
  case unpack hseq ht_syn hu_syn ht_ih hu_ih =>
    cases hclosed_e with
    | unpack ht_closed hu_closed =>
      apply sem_typ_unpack hseq hΓ
        (HasType.use_set_is_closed ht_syn)
        (by
          have h := HasType.use_set_is_closed hu_syn
          cases h with
          | union h _ =>
            cases h with
            | union h _ =>
              exact CaptureSet.rename_closed_inv (CaptureSet.rename_closed_inv h))
        (ht_ih hΓ ht_closed)
      apply hu_ih ?_ hu_closed
      cases HasType.type_is_closed ht_syn with
      | exi hT =>
        exact Ctx.IsClosed.push
          (Ctx.IsClosed.push hΓ (Binding.IsClosed.cvar CaptureBound.IsClosed.unbound))
          (Binding.IsClosed.var hT)

end CoreCapybara
