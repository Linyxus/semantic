import Semantic.CoreCapybara.Denotation
import Semantic.CoreCapybara.Semantics
namespace CoreCapybara

open CoreCapybara.WP (WorldLe)

/-- **Environment-typing descent along the typed future relation *and* an index drop `j ≤ k`.**
This is the step-counted generalization of `env_typing_worldle_down`: the arrow/poly/cpoly/modal
value-relation body quantifies its future world at a *strictly smaller* index `j < k`, so the
body's `EnvTyping` premise for the extended context must be reconstructed at `(j, st', m')`.
The `var` binding descends `val_denot` through the index via `val_denot_down_trunc` (needing the
tail's downward-closure) and then along `WorldLe`; the `tvar` binding uses the index-uniform
`ImplyAfter` (applied at the lower index, base world reconciled by `trunc_trunc`); `cvar`/`lock`
transport their closed denotations along `subsumes` (`hwle.1`), unchanged by the index drop. -/
theorem env_typing_worldle_trunc {s : Sig} {Γ : Ctx s} {env : TypeEnv s}
    {j k : Nat} (hjk : j ≤ k) {st : StoreTyping k} {st' : StoreTyping j} {m m' : Memory}
    (hts : EnvTyping Γ env k st m) (hwle : WorldLe st' m' (st.trunc hjk) m) :
    EnvTyping Γ env j st' m' := by
  induction Γ with
  | empty =>
    cases env with
    | empty => trivial
  | push Γ item ih =>
    cases env with
    | extend env' info =>
      cases item with
      | var T =>
        cases info with
        | var n ps =>
          unfold EnvTyping at hts ⊢
          obtain ⟨hval, hps, ht'⟩ := hts
          refine ⟨?_, by simpa using hps, ih ht'⟩
          have hdown := val_denot_down_trunc (typed_env_is_downward_closed ht') T hjk
            (.var (.free n)) hval
          exact val_denot_worldle_monotonic (typed_env_is_monotonic ht') T hwle hdown
      | tvar S =>
        cases info with
        | tvar d =>
          simp only [EnvTyping] at hts ⊢
          obtain ⟨hproper, himply_wf, himply_simple_ans, himply, hpure, ht'⟩ := hts
          refine ⟨hproper, himply_wf, himply_simple_ans, ?_, hpure, ih ht'⟩
          intro i hij st'' m'' hwle'' e h
          have hik : i ≤ k := Nat.le_trans hij hjk
          have hbridge : WorldLe (st'.trunc hij) m' (st.trunc hik) m := by
            have := WP.WorldLe.trunc hij hwle
            rwa [WP.World.trunc_trunc] at this
          exact himply i hik st'' m'' (WorldLe.trans hbridge hwle'') e h
      | cvar _ B =>
        cases info with
        | cvar a cs cap =>
          simp only [EnvTyping] at hts ⊢
          obtain ⟨hwf, hwf_bound, hsub, hcap, hdf, hauth, ht'⟩ := hts
          have h_denot_eq := ground_denot_is_monotonic hwf hwle.1
          have h_bound_eq : B.denot env' m = B.denot env' m' :=
            capture_bound_denot_is_monotonic hwf_bound hwle.1
          refine ⟨CaptureSet.wf_monotonic hwle.1 hwf, CaptureBound.wf_monotonic hwle.1 hwf_bound,
            ?_, by rw [hcap, h_denot_eq], hdf, hauth, ih ht'⟩
          rw [hcap, h_denot_eq] at hsub
          rw [← h_bound_eq]
          simpa [hcap, h_denot_eq] using hsub
      | lock Ψ =>
        cases info with
        | lock =>
          simp only [EnvTyping] at hts ⊢
          exact ⟨TypeEnv.Satisfy.monotonic hts.1 hwle.1, ih hts.2⟩

/-- **Environment-typing `WorldLe`-monotonicity at a fixed index.**  The same-index
(`j = k`) instance of `env_typing_worldle_trunc` (`st.trunc (le_refl k) = st` by
`trunc_self`).  Kept as a named lemma for the many callers that stay at index `k`. -/
theorem env_typing_worldle_down {s : Sig} {Γ : Ctx s} {env : TypeEnv s}
    {k : Nat} {st st' : StoreTyping k} {m m' : Memory}
    (hts : EnvTyping Γ env k st m) (hwle : WorldLe st' m' st m) :
    EnvTyping Γ env k st' m' :=
  env_typing_worldle_trunc (Nat.le_refl k) hts
    (by rw [WP.World.trunc_self]; exact hwle)

/- NOTE (Phase 6): the FALSE `memTyped_subsumes` (operational subsumption-monotonicity —
`Cell.subsumes` for mcells orders only liveness, so a non-type-preserving `write` is
`subsumes`-compatible while destroying `MemTyped`) was DELETED.  Its only consumer was
`sem_typ_par`, which now discharges the rely–guarantee `Safe.par` at *well-typed future
worlds* (e2 runs at e1's post-world, `letin`-style; robust fields re-run the branch's
semantic typing at the rely-world) — no operational transport of well-typedness remains. -/

theorem typed_env_lookup_var
  (hts : EnvTyping Γ env k st store)
  (hx : Ctx.LookupVar Γ x T) :
  Ty.val_denot env T k st store (.var (.free (env.lookup_var x).1)) := by
  induction hx generalizing store
  case here =>
    rename_i Γ0 T0
    cases env with
    | extend env0 info =>
      cases info with
      | var n ps =>
        simp only [EnvTyping, TypeEnv.lookup_var] at hts ⊢
        exact IDenot.equiv_ltr (weaken_val_denot (env:=env0) (x:=n) (ps:=ps) (T:=T0)) hts.1
  case there b =>
    rename_i k' Γ0 x0 T0 binding hlk
    cases binding
    case var =>
      rename_i Tb
      cases env with
      | extend env0 info =>
        cases info with
        | var n ps =>
          simp only [EnvTyping, TypeEnv.lookup_var] at hts ⊢
          obtain ⟨_, _, henv0⟩ := hts
          exact IDenot.equiv_ltr (weaken_val_denot (env:=env0) (x:=n) (ps:=ps) (T:=T0)) (b henv0)
    case tvar =>
      rename_i Sb
      match env with
      | .extend env0 (.tvar d) =>
        simp only [EnvTyping, TypeEnv.lookup_var] at hts ⊢
        obtain ⟨_, _, _, _, _, henv0⟩ := hts
        exact IDenot.equiv_ltr (tweaken_val_denot (env:=env0) (d:=d) (T:=T0)) (b henv0)
    case cvar =>
      rename_i Bb
      match env with
      | .extend env0 (.cvar _ cs cap) =>
        simp only [EnvTyping, TypeEnv.lookup_var] at hts ⊢
        obtain ⟨_, _, _, _, _, _, henv0⟩ := hts
        exact IDenot.equiv_ltr (cweaken_val_denot (env:=env0) (cs:=cs) (cap:=cap) (T:=T0)) (b henv0)
    case lock =>
      rename_i Ψ
      match env with
      | .extend env0 (.lock) =>
        simp only [EnvTyping, TypeEnv.lookup_var] at hts ⊢
        obtain ⟨_, henv0⟩ := hts
        exact IDenot.equiv_ltr (lweaken_val_denot (env:=env0) (T:=T0)) (b henv0)


theorem typed_env_lookup_var_reachability
  (hts : EnvTyping Γ env k st m)
  (hx : Ctx.LookupVar Γ x T) :
  reachability_of_loc m.heap (env.lookup_var x).1 ⊆ T.captureSet.denot env m := by
  have hval := typed_env_lookup_var hts hx
  have hreach := val_denot_enforces_captures hts (.var (.free (env.lookup_var x).1)) hval
  simp only [resolve_reachability] at hreach
  exact hreach

/-- `pack_bound` holds vacuously for any value that is not a syntactic pack. -/
theorem pack_bound_of_ne_pack {R : CapabilitySet} {m m' : Memory} {v : Exp {}}
    (h : ∀ (n : Nat) (cs : List.Vector (CaptureSet {}) n) (x : Var .var {}),
      v ≠ .pack cs x) :
    pack_bound R m v m' :=
  fun n cs x heq => absurd heq (h n cs x)


theorem sem_typ_var
  (hx : Γ.LookupVar x T) :
  SemanticTyping {} Γ (Exp.var (.bound x))
    (.typ (T.refineCaptureSet (.var (.M .epsilon) (.bound x)))) := by
  intro env k st m hts _ _
  simp only [Ty.exi_exp_denot]
  intro hmt
  apply Eval.eval_var
  intro _hguard
  simp only [Ty.exi_val_denot]
  refine ⟨TraceOk.nil, st, WorldLe.refl_trunc_self _ st m, hmt, ?_,
    pack_bound_of_ne_pack (fun _ _ _ h => nomatch h),
    witness_live_of_ne_pack (fun _ _ _ h => nomatch h)⟩
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
  (hts : EnvTyping Γ env k st m)
  (hc : Ctx.LookupCVar Γ c a cb) :
  ((env.lookup_cvar c).1.ground_denot m).BoundedBy (cb.denot env m) := by
  induction hc generalizing m
  case here =>
    rename_i Γ' cb'
    match env with
    | .extend env' (.cvar a0 cs cap) =>
      simp only [EnvTyping, TypeEnv.lookup_cvar] at hts ⊢
      obtain ⟨_, _, hbound, hcap_eq, _⟩ := hts
      have hcb := rebind_capturebound_denot
        (Rebind.cweaken (env := env') (cs := cs) (cap := cap) (a := a0)) cb'
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
      | .extend env' (.cvar a0 cs cap) =>
        simp only [EnvTyping, TypeEnv.lookup_cvar] at hts ⊢
        obtain ⟨_, _, _, _, _, _, henv'⟩ := hts
        have hih := ih henv'
        have hcb :=
          rebind_capturebound_denot
            (Rebind.cweaken (env := env') (cs := cs) (cap := cap) (a := a0)) cb'
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
  {Γ : Ctx s} {env : TypeEnv s} {k : Nat} {st : StoreTyping k} {m : Memory}
  (hts : EnvTyping Γ env k st m)
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
      | .extend env' (.cvar _ cs cap) =>
        simp only [EnvTyping] at hts
        obtain ⟨_, _, _, hcap_eq, _, _, henv'⟩ := hts
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
    (hts : EnvTyping Γ env k st store) (hΓ : Γ.IsClosed)
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
    -- `.var m (.free n)` cannot be closed, so `hC` is vacuous.
    cases hC
termination_by 2 * (sizeOf Γ + sizeOf C) + 1

/-- The `.var .bound x` arm of `hasmem_compute_peaks_denot`, mutually recursive
    with it via `termination_by sizeOf Γ`. -/
private theorem hasmem_compute_peaks_denot_var_bound
    {s : Sig} {Γ : Ctx s} {env : TypeEnv s} {store : Memory}
    (hts : EnvTyping Γ env k st store) (hΓ : Γ.IsClosed)
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
    change CapabilitySet.hasmem mu l
      ((reachability_of_loc store.heap n).applyAccess m) at hmem
    obtain ⟨mu0, hmem0⟩ := hasmem_of_applyAccess hmem
    have hreach_sub : reachability_of_loc store.heap n ⊆ T.captureSet.denot env_rest store := by
      have h := val_denot_enforces_captures hts_rest (.var (.free n)) hval_T
      simp only [resolve_reachability] at h
      exact h
    obtain ⟨mu1, hmem_T⟩ := hasmem_of_capabilitySet_subset hreach_sub hmem0
    obtain ⟨mu2, hmem_cp⟩ :=
      hasmem_compute_peaks_denot hts_rest hΓ_rest T.captureSet hT_cs hmem_T
    have hcp_denot := rebind_captureset_denot
      (ρ := @Rebind.weaken _ env_rest n ps)
      (compute_peaks env_rest T.captureSet)
    rw [hcp_denot] at hmem_cp
    have hcp_rename := rebind_compute_peaks
      (ρ := @Rebind.weaken _ env_rest n ps) T.captureSet
    rw [hcp_rename] at hmem_cp
    obtain ⟨mu_final, h_final⟩ :=
      hasmem_applyAccess_lift hmem_cp m
    have hps_cs : ps.cs = compute_peaks env_rest T.captureSet := by
      rw [hps_eq]
      change T.captureSet.peaks Γ_rest = _
      exact compute_peaks_correct hts_rest T.captureSet
    have hcp_eq : compute_peaks (env_rest.extend_var n ps) (CaptureSet.var m (.bound BVar.here))
                = (compute_peaks (env_rest.extend_var n ps)
                    (T.captureSet.rename Rename.succ)).applyAccess m := by
      change ((ps.rename Rename.succ).cs.applyAccess m) = _
      change (ps.cs.rename Rename.succ).applyAccess m = _
      rw [hps_cs, hcp_rename]
      rfl
    refine ⟨mu_final, ?_⟩
    change CapabilitySet.hasmem mu_final l
      ((compute_peaks (env_rest.extend_var n ps) (CaptureSet.var m (.bound BVar.here))).denot
        (env_rest.extend_var n ps) store)
    rw [hcp_eq, captureSet_denot_applyAccess_comm]
    exact h_final

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
  | _, .push Γ_rest (.cvar _ B), .extend env_rest (.cvar a0 cs cap), hts, hΓ, .there x', hmem =>
    obtain ⟨_, _, _, _, _, _, hts_rest⟩ := hts
    cases hΓ with | push hΓ_rest _ =>
    change CapabilitySet.hasmem mu l
      (((CaptureSet.var m (.bound x')).rename Rename.succ).denot
        (env_rest.extend_cvar cs cap a0) store) at hmem
    have hC := rebind_captureset_denot
      (ρ := @Rebind.cweaken _ env_rest cs cap a0)
      (CaptureSet.var m (.bound x'))
    have hmem_rest : ((CaptureSet.var m (.bound x')).denot env_rest store).hasmem mu l := by
      rw [hC]; exact hmem
    obtain ⟨mu', hmem'⟩ := hasmem_compute_peaks_denot_var_bound hts_rest hΓ_rest hmem_rest
    refine ⟨mu', ?_⟩
    change CapabilitySet.hasmem mu' l
      ((compute_peaks (env_rest.extend_cvar cs cap a0)
         ((CaptureSet.var m (.bound x')).rename Rename.succ)).denot
        (env_rest.extend_cvar cs cap a0) store)
    have hcp_rename := rebind_compute_peaks
      (ρ := @Rebind.cweaken _ env_rest cs cap a0)
      (CaptureSet.var m (.bound x'))
    have hcp_denot := rebind_captureset_denot
      (ρ := @Rebind.cweaken _ env_rest cs cap a0)
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

/-- `pack_bound` weakens along budget growth and start-memory shrinkage: a
larger budget admits more consumable locations, and locations fresh relative
to a later memory are fresh relative to any earlier one. -/
theorem pack_bound_mono {R R' : CapabilitySet} {m0 m1 m' : Memory} {v : Exp {}}
    (hRsub : R' ⊆ R) (hmm : m1.subsumes m0)
    (h : pack_bound R' m1 v m') : pack_bound R m0 v m' := by
  intro n cs x heq mu l hmem
  rcases h n cs x heq mu l hmem with ⟨hcov, hd⟩ | hr
  · exact Or.inl ⟨CapabilitySet.covers_mono hRsub hcov, hasmem_drop_of_subset hRsub hd⟩
  · refine Or.inr ?_
    exact Heap.none_of_subsumes_none hmm hr

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
    (hts : EnvTyping Γ env k st store)
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
    (hts : EnvTyping Γ env k st store)
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
    (hts : EnvTyping Γ env k st store) (hΓ : Γ.IsClosed)
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
   cap in `(compute_peaks env C).denot`, keeping `.drop` exactly (unlike the
   mode-lossy `hasmem_compute_peaks_denot`), since expansion routes through
   `val_denot_enforces_captures` and `CapabilitySet.Subset` preserves `.drop`. -/
mutual

private theorem drop_mem_compute_peaks
    {s : Sig} {Γ : Ctx s} {env : TypeEnv s} {store : Memory}
    (hts : EnvTyping Γ env k st store) (hΓ : Γ.IsClosed)
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
    (hts : EnvTyping Γ env k st store) (hΓ : Γ.IsClosed)
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
  | _, .push Γ_rest (.cvar _ B), .extend env_rest (.cvar a0 cs cap), hts, hΓ, .there x', hmem =>
    obtain ⟨_, _, _, _, _, _, hts_rest⟩ := hts
    cases hΓ with | push hΓ_rest _ =>
    change CapabilitySet.hasmem .drop l
      (((CaptureSet.var m (.bound x')).rename Rename.succ).denot
        (env_rest.extend_cvar cs cap a0) store) at hmem
    have hC := rebind_captureset_denot
      (ρ := @Rebind.cweaken _ env_rest cs cap a0)
      (CaptureSet.var m (.bound x'))
    have hmem_rest : ((CaptureSet.var m (.bound x')).denot env_rest store).hasmem .drop l := by
      rw [hC]; exact hmem
    have hmem' := drop_mem_compute_peaks_var_bound hts_rest hΓ_rest hmem_rest
    change CapabilitySet.hasmem .drop l
      ((compute_peaks (env_rest.extend_cvar cs cap a0)
         ((CaptureSet.var m (.bound x')).rename Rename.succ)).denot
        (env_rest.extend_cvar cs cap a0) store)
    have hcp_rename := rebind_compute_peaks
      (ρ := @Rebind.cweaken _ env_rest cs cap a0)
      (CaptureSet.var m (.bound x'))
    have hcp_denot := rebind_captureset_denot
      (ρ := @Rebind.cweaken _ env_rest cs cap a0)
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
    (hts : EnvTyping Γ env k st store) (hΓ : Γ.IsClosed)
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
    exact CapabilitySet.hasmem.here
  | left _ ih => exact CapabilitySet.hasmem.left ih
  | right _ ih => exact CapabilitySet.hasmem.right ih


/-- Converts the `SemanticTyping` form into the `Ty.exi_exp_denot` form. The
budget is exactly `C.denot ρ m` on both sides, so this just unfolds
`SemanticTyping`/`exi_exp_denot`. -/
theorem semtyp_to_exi_exp_denot
    {s : Sig} {C : CaptureSet s} {Γ : Ctx s} {e : Exp s} {E : Ty .exi s}
    {ρ : TypeEnv s} {k : Nat} {st : StoreTyping k} {m : Memory}
    (ht : SemanticTyping C Γ e E)
    (hts : EnvTyping Γ ρ k st m)
    (hdsep : ρ.EnvSepWf)
    (hcompat : m.is_compatible (C.denot ρ m)) :
    Ty.exi_exp_denot ρ E (C.denot ρ m) k st m (e.subst (Subst.from_TypeEnv ρ)) :=
  ht ρ k st m hts hdsep hcompat

/-- Under `EnvTyping`, computed peaks of statically-computed peaks collapse. -/
theorem compute_peaks_peaks {Γ : Ctx s} {env : TypeEnv s} {k : Nat} {st : StoreTyping k}
    {m : Memory} (hts : EnvTyping Γ env k st m) (C : CaptureSet s) :
    compute_peaks env (CaptureSet.peaks Γ C) = compute_peaks env C := by
  rw [← compute_peaks_correct hts, ← compute_peaks_correct hts,
    (CaptureSet.peaks_peaksOnly Γ C).peaks_fixed]

private theorem closed_capture_denot_monotonic
    {Cf : CaptureSet s} {env : TypeEnv s} {store m' : Memory} {Γ : Ctx s}
    (hCf_closed : Cf.IsClosed)
    (hts : EnvTyping Γ env k st store)
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
  (ht : SemanticTyping (Cf.rename Rename.succ) (Γ,x:T1) e T2) :
  SemanticTyping ∅ Γ (Exp.abs Cf T1 e) (T1.arrow Cf T2).typ := by
  intro env k st store hts hdsep _
  simp only [Ty.exi_exp_denot]
  intro hmt
  apply Eval.eval_val
  · simp only [Exp.subst]; constructor
  · intro _hguard
    refine ⟨TraceOk.nil, st, WorldLe.refl_trunc_self _ st store, hmt, ?_,
      pack_bound_of_ne_pack (fun _ _ _ h => by simp [Exp.subst] at h),
    witness_live_of_ne_pack (fun _ _ _ h => by simp [Exp.subst] at h)⟩
    simp only [Ty.exi_val_denot, Ty.val_denot]
    constructor
    · apply Exp.wf_subst
      · apply Exp.wf_of_closed hclosed_abs
      · apply from_TypeEnv_wf_in_heap hts
    · constructor
      · apply CaptureSet.wf_subst
        · apply CaptureSet.wf_of_closed
          cases hclosed_abs
          assumption
        · apply from_TypeEnv_wf_in_heap hts
      · use (Cf.subst (Subst.from_TypeEnv env)), (T1.subst (Subst.from_TypeEnv env)),
          (e.subst (Subst.from_TypeEnv env).lift)
        constructor
        · simp only [resolve, Exp.subst]
        · constructor
          · apply CaptureSet.wf_subst
            · apply CaptureSet.wf_of_closed
              cases hclosed_abs
              assumption
            · apply from_TypeEnv_wf_in_heap hts
          · constructor
            · rw [expand_captures_eq_ground_denot]
              simp only [List.empty_eq]
              apply CapabilitySet.Subset.refl
            · -- The body's separation invariant is discharged from the arrow
              -- denotation's `DropSepIn` premise (supplied by the caller's budget
              -- at `app`), closing the closure-capture gap for value abstractions.
              intro j hjk st' m' arg hwle hmt_body hcompat harg
              have hsub : m'.subsumes store := hwle.1
              let ps := compute_peakset env T1.captureSet
              have hkey := @Exp.from_TypeEnv_weaken_open s env arg e ps
              refine hkey ▸ ?_
              have henv :
                EnvTyping (Γ,x:T1) (env.extend_var arg ps) j st' m' := by
                constructor
                · exact harg
                · constructor
                  · exact (compute_peakset_correct hts T1.captureSet).symm
                  · exact env_typing_worldle_trunc hjk hts hwle
              have hcap_rename :
                (Cf.rename Rename.succ).denot (env.extend_var arg ps)
                = Cf.denot env := by
                have := rebind_captureset_denot
                  (Rebind.weaken (env:=env) (x:=arg) (ps:=ps)) Cf
                exact this.symm
              have hCf_closed : Cf.IsClosed := by cases hclosed_abs; assumption
              have hauth :=
                authority_eq_expand_captures hcap_rename
                  (closed_capture_denot_monotonic hCf_closed hts hsub)
              have hcompat' :
                  m'.is_compatible ((Cf.rename Rename.succ).denot (env.extend_var arg ps) m') :=
                hauth ▸ hcompat
              have htyped := ht (env.extend_var arg ps) j st' m' henv
                hdsep.extend_var hcompat'
              rw [← authority_eq_expand_captures hcap_rename
                    (closed_capture_denot_monotonic hCf_closed hts hsub)]
              simp only [Ty.exi_exp_denot] at htyped ⊢
              exact htyped hmt_body


theorem sem_typ_tabs {T : Ty TySort.exi (s,X)} {Cf : CaptureSet s} {S : PureTy s}
  (hclosed_tabs : (Exp.tabs Cf S e).IsClosed)
  (ht : SemanticTyping (Cf.rename Rename.succ) (Γ,X<:S) e T) :
  SemanticTyping ∅ Γ (Exp.tabs Cf S e) (S.core.poly Cf T).typ := by
  intro env k st store hts hdsep _
  simp only [Ty.exi_exp_denot]
  intro hmt
  apply Eval.eval_val
  · simp only [Exp.subst]; constructor
  · intro _hguard
    refine ⟨TraceOk.nil, st, WorldLe.refl_trunc_self _ st store, hmt, ?_,
      pack_bound_of_ne_pack (fun _ _ _ h => by simp [Exp.subst] at h),
    witness_live_of_ne_pack (fun _ _ _ h => by simp [Exp.subst] at h)⟩
    simp only [Ty.exi_val_denot, Ty.val_denot]
    constructor
    · apply Exp.wf_subst
      · apply Exp.wf_of_closed hclosed_tabs
      · apply from_TypeEnv_wf_in_heap hts
    · constructor
      · apply CaptureSet.wf_subst
        · apply CaptureSet.wf_of_closed
          cases hclosed_tabs
          assumption
        · apply from_TypeEnv_wf_in_heap hts
      · use (Cf.subst (Subst.from_TypeEnv env)), (S.subst (Subst.from_TypeEnv env)),
          (e.subst (Subst.from_TypeEnv env).lift)
        constructor
        · simp only [resolve, Exp.subst]
        · constructor
          · apply CaptureSet.wf_subst
            · apply CaptureSet.wf_of_closed
              cases hclosed_tabs
              assumption
            · apply from_TypeEnv_wf_in_heap hts
          · constructor
            · rw [expand_captures_eq_ground_denot]
              simp only [List.empty_eq]
              apply CapabilitySet.Subset.refl
            · -- The body's separation invariant comes from the `DropSepIn` premise.
              intro j hjk st' m' denot hwle hmt_body hcompat hproper himply_simple_ans himply hpure
              have hsub : m'.subsumes store := hwle.1
              have hkey := @Exp.from_TypeEnv_weaken_open_tvar s env denot e
              refine hkey ▸ ?_
              have henv : EnvTyping (Γ,X<:S) (env.extend_tvar denot) j st' m' := by
                constructor
                · exact hproper
                · constructor
                  · exact hproper.2.2.2.1
                  · constructor
                    · exact himply_simple_ans
                    · constructor
                      · exact himply
                      · constructor
                        · exact hpure
                        · exact env_typing_worldle_trunc hjk hts hwle
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
              have htyped := ht (env.extend_tvar denot) j st' m' henv
                hdsep.extend_tvar hcompat'
              rw [← authority_eq_expand_captures hcap_rename
                    (closed_capture_denot_monotonic hCf_closed hts hsub)]
              simp only [Ty.exi_exp_denot] at htyped ⊢
              exact htyped hmt_body


theorem sem_typ_cabs {T : Ty TySort.exi (s,C)} {Cf : CaptureSet s} {cb : CaptureBound s}
  (hclosed_cabs : (Exp.cabs Cf cb e).IsClosed)
  (ht : SemanticTyping (Cf.rename Rename.succ)
    (Γ,C[.access_only]<:cb) e T) :
  SemanticTyping ∅ Γ (Exp.cabs Cf cb e) (Ty.cpoly cb Cf T).typ := by
  intro env k st store hts hdsep _
  simp only [Ty.exi_exp_denot]
  intro hmt
  apply Eval.eval_val
  · simp only [Exp.subst]; constructor
  · intro _hguard
    refine ⟨TraceOk.nil, st, WorldLe.refl_trunc_self _ st store, hmt, ?_,
      pack_bound_of_ne_pack (fun _ _ _ h => by simp [Exp.subst] at h),
    witness_live_of_ne_pack (fun _ _ _ h => by simp [Exp.subst] at h)⟩
    simp only [Ty.exi_val_denot, Ty.val_denot]
    constructor
    · apply Exp.wf_subst
      · apply Exp.wf_of_closed hclosed_cabs
      · apply from_TypeEnv_wf_in_heap hts
    · constructor
      · apply CaptureSet.wf_subst
        · apply CaptureSet.wf_of_closed
          cases hclosed_cabs
          assumption
        · apply from_TypeEnv_wf_in_heap hts
      · use (Cf.subst (Subst.from_TypeEnv env)), (cb.subst (Subst.from_TypeEnv env)),
          (e.subst (Subst.from_TypeEnv env).lift)
        constructor
        · simp only [resolve, Exp.subst]
        · constructor
          · apply CaptureSet.wf_subst
            · apply CaptureSet.wf_of_closed
              cases hclosed_cabs
              assumption
            · apply from_TypeEnv_wf_in_heap hts
          · constructor
            · rw [expand_captures_eq_ground_denot]
              simp only [List.empty_eq]
              apply CapabilitySet.Subset.refl
            · -- The body's separation invariant comes from the `DropSepIn` premise.
              intro j hjk st' m' CS hwf hdf hwle hmt_body hcompat hsub_bound
              have hsub : m'.subsumes store := hwle.1
              have hkey := @Exp.from_TypeEnv_weaken_open_cvar s env CS e
              refine hkey ▸ ?_
              have henv : EnvTyping (Γ,C[.access_only]<:cb)
                  (env.extend_cvar CS (cap := CS.ground_denot m')) j st' m' := by
                constructor
                · exact hwf
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
                · have heq : CS.ground_denot = CaptureSet.denot TypeEnv.empty CS := by
                    funext m
                    simp only [CaptureSet.denot, Subst.from_TypeEnv_empty, CaptureSet.subst_id]
                  rw [heq]
                  exact hsub_bound
                constructor
                · rfl
                constructor
                · exact hdf
                constructor
                · rfl
                · exact env_typing_worldle_trunc hjk hts hwle
              have hcap_rename :
                  (Cf.rename Rename.succ).denot
                    (env.extend_cvar CS (cap := CS.ground_denot m')) = Cf.denot env := by
                have :=
                  rebind_captureset_denot
                    (Rebind.cweaken (env:=env) (cs:=CS) (cap:=CS.ground_denot m')
                      (a:=.access_only)) Cf
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
              have htyped :=
                ht (env.extend_cvar CS (cap := CS.ground_denot m')) j st' m' henv
                  hdsep.extend_cvar_access_only hcompat'
              rw [← authority_eq_expand_captures hcap_rename
                    (closed_capture_denot_monotonic hCf_closed hts hsub)]
              rw [Subst.from_TypeEnv_extend_cvar_cap_irrelevant
                (cap := .empty) (cap' := CS.ground_denot m')]
              -- `rw` leaves the `extend_cvar` authority as a metavariable (a second
              -- `Authority` goal); focusing the main goal resolves it by unification.
              · simp only [Ty.exi_exp_denot] at htyped ⊢
                exact htyped hmt_body

/-- Wraps a subset-of-peaks fact about one member of an evidence vector into the
    corresponding fact about the combined evidence `CaptureSet.unionAll`. -/
private theorem subset_peaks_unionAll {s : Sig} {Γ : Ctx s} {X : CaptureSet s} :
    {n : Nat} → {Cs : List.Vector (CaptureSet s) n} → (c0 : CaptureSet s) →
    c0 ∈ Cs.toList → X ⊆ CaptureSet.peaks Γ c0 →
    X ⊆ CaptureSet.peaks Γ (CaptureSet.unionAll Cs)
  | 0, Cs, c0, hmem, _ => by
    obtain ⟨l, hl⟩ := Cs
    cases l with
    | nil => cases hmem
    | cons _ _ => cases hl
  | n + 1, Cs, c0, hmem, hsub => by
    obtain ⟨l, hl⟩ := Cs
    cases l with
    | nil => cases hl
    | cons c l' =>
      have hl' : l'.length = n := by simpa using hl
      change X ⊆ CaptureSet.peaks Γ
        (c ∪ CaptureSet.unionAll (⟨l', hl'⟩ : List.Vector (CaptureSet s) n))
      rw [CaptureSet.peaks_union]
      cases hmem with
      | head => exact .union_right_left hsub
      | tail _ hmem' =>
        exact .union_right_right (subset_peaks_unionAll c0 hmem' hsub)

/-- **Semantic mutual disjointness** of the `n` evidences of a pack: under every
    world satisfying the context, the evidences denote pairwise location-disjoint
    capability sets. Recorded in `exi_val_denot` at the pack site and consumed by
    `unpack`, whose continuation binds all `n` evidences as simultaneous
    `.can_drop` capture variables — `EnvSepWf` there demands their mutual
    `CapabilitySet.disjoint`ness (dropping one must not dangle another). -/
def SemPairwiseSep (Γ : Ctx s) {n : Nat} (Cs : List.Vector (CaptureSet s) n) : Prop :=
  ∀ {k : Nat} {env : TypeEnv s} {st : StoreTyping k} {m : Memory},
    EnvTyping Γ env k st m → env.EnvSepWf →
    Cs.toList.Pairwise (fun c1 c2 =>
      CapabilitySet.disjoint (c1.denot env m) (c2.denot env m))

theorem sem_typ_pack
  {n : Nat} {T : Ty .capt (Sig.extendCVars s n)} {Cs : List.Vector (CaptureSet s) n}
  {x : Var .var s} {Γ : Ctx s}
  (hclosed_e : (Exp.pack Cs x).IsClosed)
  (hΓ : Γ.IsClosed)
  (hvalid_cs : (CaptureSet.unionAll Cs).AccessOnly Γ)
  (hsem_sep : SemPairwiseSep Γ Cs)
  (ht : SemanticTyping {} Γ (Exp.var x) (T.subst (Subst.openCVars Cs)).typ) :
  SemanticTyping ((CaptureSet.unionAll Cs) ∪ (CaptureSet.unionAll Cs).applyAccess .drop)
    Γ (Exp.pack Cs x) (.exi n T) := by
  intro env k st store hts hdsep hcompat
  have hsubst : (Exp.pack Cs x).subst (Subst.from_TypeEnv env) =
         Exp.pack (Cs.map (fun C => C.subst (Subst.from_TypeEnv env)))
           (x.subst (Subst.from_TypeEnv env)) := by
    simp only [Exp.subst]
  have hclosed_cs : ∀ c ∈ Cs.toList, c.IsClosed := by
    cases hclosed_e with
    | pack hcs_closed _hx_closed => exact hcs_closed
  simp only [Ty.exi_exp_denot, List.empty_eq]
  rw [hsubst]
  intro hmt
  apply Eval.eval_pack
  -- Extract the result world `st1` from the (var) sub-derivation: since `Exp.var x`
  -- does not allocate, its result store typing `st1 ⊒ st` is the world at which the
  -- packed value's denotation holds.  We carry `st1` as the pack's result world.
  have hcompat0 : store.is_compatible ((∅ : CaptureSet s).denot env store) := by
    simpa using Memory.is_compatible_empty store
  have hx := ht env k st store hts hdsep hcompat0
  simp only [Ty.exi_exp_denot, List.empty_eq] at hx
  have hvar : (Exp.var x).subst (Subst.from_TypeEnv env) =
         Exp.var (x.subst (Subst.from_TypeEnv env)) := by
    cases x <;> simp only [Exp.subst, Var.subst]
  rw [hvar] at hx
  intro hguard
  obtain ⟨_, st1, hwle1, hmt1, hval1, _⟩ := Eval.var_inv (hx hmt) hguard
  -- The combined evidence resolves, in the runtime environment, to its denotation.
  have hreach :
      (CaptureSet.unionAll
        (Cs.map (fun C => C.subst (Subst.from_TypeEnv env)))).reachability store
      = (CaptureSet.unionAll Cs).denot env store := by
    rw [← CaptureSet.unionAll_subst, ← CaptureSet.ground_denot_eq_reachability]
    rfl
  refine ⟨TraceOk.nil, st1, hwle1, hmt1, ?_, ?_, ?_⟩
  · simp only [Ty.exi_val_denot]
    refine ⟨Cs.map (fun C => C.subst (Subst.from_TypeEnv env)),
      x.subst (Subst.from_TypeEnv env), rfl, ?_, ?_, ?_, ?_⟩
    · -- well-formedness of each (resolved) evidence
      intro cs hmem
      rw [List.Vector.toList_map] at hmem
      obtain ⟨c, hmem', rfl⟩ := List.mem_map.mp hmem
      exact CaptureSet.wf_subst (CaptureSet.wf_of_closed (hclosed_cs c hmem'))
        (from_TypeEnv_wf_in_heap hts)
    · -- drop-freedom of each evidence: a `.drop` in `c`'s runtime image traces
      -- (via `drop_denot_peak`) to a `.drop`-access peak of `c`, hence of the
      -- combined evidence, contradicting its `AccessOnly Γ`.
      intro cs hmem
      rw [List.Vector.toList_map] at hmem
      obtain ⟨c, hmem', rfl⟩ := List.mem_map.mp hmem
      intro l hmem_l
      have hmem_l' : (c.denot env store).hasmem .drop l := hmem_l
      obtain ⟨cv, hsub, _⟩ :=
        drop_denot_peak hts hΓ (envtyping_lookup_cvar_drop_free hts)
          (hclosed_cs c hmem') hmem_l'
      exact hvalid_cs cv (subset_peaks_unionAll c hmem' hsub)
    · -- pairwise disjointness of the evidences, from the semantic hypothesis
      have hpw := hsem_sep hts hdsep
      rw [List.Vector.toList_map]
      exact List.pairwise_map.mpr hpw
    · -- the packed witness inhabits `T` under the `n`-fold evidence extension
      have hQ' : Ty.val_denot env (T.subst (Subst.openCVars Cs)) k st1 store
          (Exp.var (x.subst (Subst.from_TypeEnv env))) := by
        simpa only [Ty.exi_val_denot] using hval1
      exact (open_cargs_val_denot (m := store) (a := .can_drop) (Cs := Cs) (T := T)
        k st1 store (Exp.var (x.subst (Subst.from_TypeEnv env)))).mpr hQ'
  · -- pack_bound: every witness location is covered by the pack budget
    -- `R = (unionAll Cs ∪ (unionAll Cs).applyAccess .drop).denot` at its own access
    -- mode (the `unionAll Cs` summand) AND is consumable (`.drop`, from the
    -- `applyAccess .drop` summand).
    intro n0 cs0 x0 heq mu l hmem
    cases heq
    left
    rw [hreach] at hmem
    have hgoal :
        CaptureSet.denot env ((CaptureSet.unionAll Cs).applyAccess .drop) store
          = ((CaptureSet.unionAll Cs).denot env store).to_drop := by
      rw [captureSet_denot_applyAccess_comm, CapabilitySet.applyAccess_drop]
    refine ⟨CapabilitySet.covers_union_left (CapabilitySet.hasmem_implies_covers hmem), ?_⟩
    refine CapabilitySet.hasmem_union_right ?_
    change (CaptureSet.denot env ((CaptureSet.unionAll Cs).applyAccess .drop) store).hasmem
      .drop l
    rw [hgoal]
    exact CapabilitySet.hasmem_to_drop_of_hasmem hmem
  · -- witness_live: the combined witness is live in `store`, since the pack budget
    -- (compatible by `hcompat`) contains it directly (its `unionAll Cs` summand).
    intro n0 cs0 x0 heq
    cases heq
    rw [hreach]
    refine Memory.is_compatible_subset ?_ hcompat
    exact CapabilitySet.Subset.union_right_left


theorem abs_val_denot_inv {k : Nat} {st : StoreTyping k}
  (hv : Ty.val_denot env (.arrow T1 cs T2) k st store (.var x)) :
  ∃ fx, x = .free fx
    ∧ ∃ cs' T0 e0 hval R,
      store.heap fx = some (Cell.val ⟨Exp.abs cs' T0 e0, hval, R⟩)
    ∧ expand_captures store.heap cs' ⊆ cs.denot env store
    ∧ (∀ (j : Nat) (hjk : j ≤ k) (st' : StoreTyping j) (m' : Memory) (arg : Nat),
      WorldLe st' m' (st.trunc hjk) store ->
      MemTyped j st' m' ->
      m'.is_compatible (expand_captures store.heap cs') ->
      Ty.val_denot env T1 j st' m' (.var (.free arg)) ->
      Ty.exi_exp_denot
        (env.extend_var arg (compute_peakset env T1.captureSet))
        T2 (expand_captures store.heap cs') j st' m'
        (e0.subst (Subst.openVar (.free arg)))) := by
  cases x with
  | bound bx => cases bx
  | free fx =>
    simp only [Ty.val_denot, resolve] at hv
    obtain ⟨hwf_e, hwf_cs, cs', T0, e0, hresolve, hwf_cs', hR0_sub, hfun⟩ := hv
    generalize hres : store.heap fx = res at hresolve ⊢
    cases res
    case none => simp at hresolve
    case some cell =>
      cases cell with
      | val hval =>
        simp only [List.empty_eq] at hresolve
        cases hval with | mk unwrap isVal reachability =>
        injection hresolve with hresolve
        subst hresolve
        refine ⟨fx, rfl, cs', T0, e0, isVal, reachability, hres, hR0_sub, ?_⟩
        intro j hjk st' m' arg hwle hmt hcompat harg
        simp only [Ty.exi_exp_denot]
        intro _
        exact hfun j hjk st' m' arg hwle hmt hcompat harg
      | capability =>
        simp at hresolve
      | masked =>
        simp at hresolve


theorem tabs_val_denot_inv {k : Nat} {st : StoreTyping k}
  (hv : Ty.val_denot env (.poly T1 cs T2) k st store (.var x)) :
  ∃ fx, x = .free fx
    ∧ ∃ cs' S0 e0 hval R,
      store.heap fx = some (Cell.val ⟨Exp.tabs cs' S0 e0, hval, R⟩)
    ∧ expand_captures store.heap cs' ⊆ cs.denot env store
    ∧ (∀ (j : Nat) (hjk : j ≤ k) (st' : StoreTyping j) (m' : Memory) (denot : IDenot),
      WorldLe st' m' (st.trunc hjk) store ->
      MemTyped j st' m' ->
      m'.is_compatible (expand_captures store.heap cs') ->
      denot.is_proper ->
      denot.implies_simple_ans ->
      denot.ImplyAfter j st' m' (Ty.val_denot env T1) ->
      denot.enforce_pure ->
      Ty.exi_exp_denot
        (env.extend_tvar denot)
        T2 (expand_captures store.heap cs') j st' m'
        (e0.subst (Subst.openTVar .top))) := by
  cases x with
  | bound bx => cases bx
  | free fx =>
    simp only [Ty.val_denot, resolve] at hv
    obtain ⟨hwf_e, hwf_cs, cs', S0, e0, hresolve, hwf_cs', hR0_sub, hfun⟩ := hv
    generalize hres : store.heap fx = res at hresolve ⊢
    cases res
    case none => simp at hresolve
    case some cell =>
      cases cell with
      | val hval =>
        simp only [List.empty_eq] at hresolve
        cases hval with | mk unwrap isVal reachability =>
        injection hresolve with hresolve
        subst hresolve
        refine ⟨fx, rfl, cs', S0, e0, isVal, reachability, hres, hR0_sub, ?_⟩
        intro j hjk st' m' denot hwle hmt hcompat hproper hsimple himply hpure
        simp only [Ty.exi_exp_denot]
        intro _
        exact hfun j hjk st' m' denot hwle hmt hcompat hproper hsimple himply hpure
      | capability =>
        simp at hresolve
      | masked =>
        simp at hresolve

theorem cabs_val_denot_inv {k : Nat} {st : StoreTyping k}
  (hv : Ty.val_denot env (.cpoly B cs T) k st store (.var x)) :
  ∃ fx, x = .free fx
    ∧ ∃ cs' B0 e0 hval R,
      store.heap fx = some (Cell.val ⟨Exp.cabs cs' B0 e0, hval, R⟩)
    ∧ expand_captures store.heap cs' ⊆ cs.denot env store
    ∧ (∀ (j : Nat) (hjk : j ≤ k) (st' : StoreTyping j) (m' : Memory) (CS : CaptureSet {}),
      CS.WfInHeap m'.heap ->
      (CS.ground_denot m').drop_free ->
      WorldLe st' m' (st.trunc hjk) store ->
      MemTyped j st' m' ->
      m'.is_compatible (expand_captures store.heap cs') ->
      ((CS.denot TypeEnv.empty m').BoundedBy (B.denot env m')) ->
      Ty.exi_exp_denot
        (env.extend_cvar CS (cap := CS.ground_denot m'))
        T (expand_captures store.heap cs') j st' m'
        (e0.subst (Subst.openCVar CS))) := by
  cases x with
  | bound bx => cases bx
  | free fx =>
    simp only [Ty.val_denot, resolve] at hv
    obtain ⟨hwf_e, hwf_cs, cs', B0, e0, hresolve, hwf_cs', hR0_sub, hfun⟩ := hv
    generalize hres : store.heap fx = res at hresolve ⊢
    cases res
    case none => simp at hresolve
    case some cell =>
      cases cell with
      | val hval =>
        simp only [List.empty_eq] at hresolve
        cases hval with | mk unwrap isVal reachability =>
        injection hresolve with hresolve
        subst hresolve
        refine ⟨fx, rfl, cs', B0, e0, isVal, reachability, hres, hR0_sub, ?_⟩
        intro j hjk st' m' CS hCSwf hCSdf hwle hmt hcompat hbound
        simp only [Ty.exi_exp_denot]
        intro _
        exact hfun j hjk st' m' CS hCSwf hCSdf hwle hmt hcompat hbound
      | capability =>
        simp at hresolve
      | masked =>
        simp at hresolve


theorem cap_val_denot_inv
  (hv : Ty.val_denot env (.cap cs) k st store (.var x)) :
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
  (hv : Ty.val_denot env .unit k st store (.var x)) :
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
  (hv : Ty.val_denot env (.cell cs T) k st store (.var x)) :
  ∃ fx b0 ℓ0, x = .free fx ∧ store.heap fx = some (.capability (.mcell b0 ℓ0)) ∧
    (cs.denot env store).covers (.access .epsilon) fx := by
  cases x with
  | bound bx => cases bx
  | free fx =>
    simp only [Ty.val_denot, Memory.lookup] at hv
    obtain ⟨hwf_cs, label, b0, ℓ0, R, heq, hlookup, hmem, _hstl, _himpl⟩ := hv
    cases heq
    exact ⟨fx, b0, ℓ0, rfl, hlookup, hmem⟩

/-- Richer cell inversion exposing the cell's store-typing relation `R` and the biconditional
content agreement `R ↔ val_denot T` over all lower worlds. Used by `sem_typ_read`/`reader`. -/
theorem cell_val_denot_inv_store {k : Nat} {st : StoreTyping k}
  (hv : Ty.val_denot env (.cell cs T) k st store (.var x)) :
  ∃ fx b0 ℓ0 R, x = .free fx ∧ store.heap fx = some (.capability (.mcell b0 ℓ0)) ∧
    (cs.denot env store).covers (.access .epsilon) fx ∧
    st.lookup fx = some R ∧
    (∀ (j : Fin k) (w' : StoreTyping j.val) m' e',
      R j w' m' e' ↔ Ty.val_denot env T j.val w' m' e') := by
  cases x with
  | bound bx => cases bx
  | free fx =>
    simp only [Ty.val_denot, Memory.lookup] at hv
    obtain ⟨hwf_cs, label, b0, ℓ0, R, heq, hlookup, hmem, hstl, himpl⟩ := hv
    cases heq
    exact ⟨fx, b0, ℓ0, R, rfl, hlookup, hmem, hstl, himpl⟩

theorem reader_val_denot_inv
  (hv : Ty.val_denot env (.reader cs T) k st store (.var x)) :
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
    rcases hv' with ⟨_, _, y, b0, ℓ0, R, hres, hlookup, hcov, _hstl, _himpl⟩
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

/-- Richer reader inversion exposing the underlying cell's store-typing relation `Rst`
and the biconditional content agreement over all lower worlds. Used by `sem_typ_read`. -/
theorem reader_val_denot_inv_store {k : Nat} {st : StoreTyping k}
  (hv : Ty.val_denot env (.reader cs T) k st store (.var x)) :
  ∃ fx y b0 ℓ0 hval Rcell Rst,
    x = .free fx ∧
    store.heap fx = some (Cell.val ⟨Exp.reader (.free y), hval, Rcell⟩) ∧
    store.heap y = some (.capability (.mcell b0 ℓ0)) ∧
    (cs.denot env store).covers (.access .ro) y ∧
    st.lookup y = some Rst ∧
    (∀ (j : Fin k) (w' : StoreTyping j.val) m' e',
      Rst j w' m' e' ↔ Ty.val_denot env T j.val w' m' e') := by
  cases x with
  | bound bx => cases bx
  | free fx =>
    have hv' := hv
    simp only [Ty.val_denot] at hv'
    rcases hv' with ⟨_, _, y, b0, ℓ0, Rst, hres, hlookup, hcov, hstl, himpl⟩
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
      refine ⟨fx, y, b0, ℓ0, isVal, reachability, Rst, rfl, ?_, ?_, hcov, hstl, himpl⟩
      · simp [hlookup_fx]
      · simpa [Memory.lookup] using hlookup

theorem bool_val_denot_inv
  (hv : Ty.val_denot env .bool k st store (.var x)) :
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

theorem var_exp_denot_inv {A : CapabilitySet} {k : Nat} {st : StoreTyping k}
  (hk : 0 < k)
  (hmt : MemTyped k st store)
  (hv : Ty.exi_exp_denot env T A k st store (.var x)) :
  ∃ st', WorldLe st' store st store ∧ MemTyped k st' store
    ∧ Ty.exi_val_denot env T k st' store (.var x) := by
  simp only [Ty.exi_exp_denot, List.empty_eq] at hv
  obtain ⟨_htrace, st', hwle, hmt', hval, _⟩ := Eval.var_inv (hv hmt) hk
  -- a variable evaluates with the empty trace (`readCount = 0`), so the step-counted result
  -- world stays at index `k` and `st.trunc (le_refl) = st`.
  simp only [Trace.readCount_nil, Nat.sub_zero, WP.World.trunc_self] at hwle hmt' hval ⊢
  exact ⟨st', hwle, hmt', hval⟩

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
    (h : SepCtx.Has K C) :
    SepCtx.Has (K.subst σ) (C.subst σ) := by
  induction h with
  | here =>
    change SepCtx.Has (.cons _ _) _
    exact .here
  | there h ih =>
    change SepCtx.Has (.cons _ _) _
    exact .there ih

theorem SepCtx.Has.subst_inv
    {K : SepCtx s1} {σ : Subst s1 s2}
    (h : SepCtx.Has (K.subst σ) C) :
    ∃ C0, C = C0.subst σ ∧ SepCtx.Has K C0 := by
  induction K with
  | empty =>
    cases h
  | cons K C0 ih =>
    change SepCtx.Has (.cons (K.subst σ) (C0.subst σ)) C at h
    cases h with
    | here =>
      exact ⟨C0, rfl, .here⟩
    | there h' =>
      obtain ⟨C1, hC1, hh⟩ := ih h'
      exact ⟨C1, hC1, .there hh⟩

theorem MutabilityCtx.Has.subst
    {K : MutabilityCtx s1} {σ : Subst s1 s2}
    (h : MutabilityCtx.Has K C m) :
    MutabilityCtx.Has (K.subst σ) (C.subst σ) m := by
  induction h with
  | here =>
    change MutabilityCtx.Has (.cons _ _ _) _ _
    exact .here
  | there h ih =>
    change MutabilityCtx.Has (.cons _ _ _) _ _
    exact .there ih

theorem MutabilityCtx.Has.subst_inv
    {K : MutabilityCtx s1} {σ : Subst s1 s2}
    (h : MutabilityCtx.Has (K.subst σ) C m) :
    ∃ C0, C = C0.subst σ ∧ MutabilityCtx.Has K C0 m := by
  induction K with
  | empty =>
    cases h
  | cons K C0 m0 ih =>
    change MutabilityCtx.Has (.cons (K.subst σ) (C0.subst σ) m0) C m at h
    cases h with
    | here =>
      exact ⟨C0, rfl, .here⟩
    | there h' =>
      obtain ⟨C1, hC1, hh⟩ := ih h'
      exact ⟨C1, hC1, .there hh⟩

theorem SepCtx.HasTwoDistinct.subst
    {K : SepCtx s1} {σ : Subst s1 s2}
    (h : SepCtx.HasTwoDistinct K C1 C2) :
    SepCtx.HasTwoDistinct (K.subst σ) (C1.subst σ) (C2.subst σ) := by
  induction h with
  | here_there hhas =>
    change SepCtx.HasTwoDistinct (.cons _ _) _ _
    exact .here_there (hhas.subst)
  | there h ih =>
    change SepCtx.HasTwoDistinct (.cons _ _) _ _
    exact .there ih
  | symm h ih =>
    exact .symm ih

theorem SepCtx.HasTwoDistinct.subst_inv
    {K : SepCtx s1} {σ : Subst s1 s2}
    (h : SepCtx.HasTwoDistinct (K.subst σ) C1 C2) :
    ∃ D1 D2,
      C1 = D1.subst σ ∧
      C2 = D2.subst σ ∧
      SepCtx.HasTwoDistinct K D1 D2 := by
  generalize he0 : K.subst σ = K0 at h
  induction h generalizing K with
  | here_there hhas =>
    cases K with
    | empty =>
      simp [SepCtx.subst] at he0
    | cons K1 C0 =>
      simp only [SepCtx.subst, SepCtx.cons.injEq] at he0
      rcases he0 with ⟨hK, hC⟩
      subst hK hC
      obtain ⟨D2, hD2, hh⟩ := SepCtx.Has.subst_inv hhas
      exact ⟨C0, D2, rfl, hD2, .here_there hh⟩
  | there a ih =>
    cases K with
    | empty => simp [SepCtx.subst] at he0
    | cons K1 C0 =>
      simp only [SepCtx.subst, SepCtx.cons.injEq] at he0
      rcases he0 with ⟨hK, hC⟩
      subst hC
      obtain ⟨D1, D2, hD1, hD2, hh⟩ := ih hK
      exact ⟨D1, D2, hD1, hD2, .there hh⟩
  | symm a ih =>
    obtain ⟨D2, D1, hD2, hD1, hh⟩ := ih he0
    exact ⟨D1, D2, hD1, hD2, .symm hh⟩

theorem TypeEnv.satisfy_subst_iff
    {env : TypeEnv s} {Ψ : ModalCtx s} {m : Memory} :
    env.Satisfy Ψ m ↔ TypeEnv.empty.Satisfy (Ψ.subst (Subst.from_TypeEnv env)) m := by
  constructor
  · intro hsat
    constructor
    · intro C hhas
      obtain ⟨C0, rfl, hhas0⟩ := SepCtx.Has.subst_inv hhas
      simpa [CaptureSet.denot, Subst.from_TypeEnv_empty, CaptureSet.subst_id] using
        hsat.wf_sep C0 hhas0
    · intro C mode hhas
      obtain ⟨C0, rfl, hhas0⟩ := MutabilityCtx.Has.subst_inv hhas
      simpa [CaptureSet.denot, Subst.from_TypeEnv_empty, CaptureSet.subst_id] using
        hsat.wf_mut C0 mode hhas0
    · intro C mode hhas
      obtain ⟨C0, rfl, hhas0⟩ := MutabilityCtx.Has.subst_inv hhas
      simpa [CaptureSet.denot, Subst.from_TypeEnv_empty, CaptureSet.subst_id] using
        hsat.kind C0 mode hhas0
    · intro C1 C2 hdistinct
      obtain ⟨D1, D2, rfl, rfl, hdistinct0⟩ := SepCtx.HasTwoDistinct.subst_inv hdistinct
      simpa [CaptureSet.denot, Subst.from_TypeEnv_empty, CaptureSet.subst_id] using
        hsat.sep D1 D2 hdistinct0
  · intro hsat
    constructor
    · intro C hhas
      have hhas' := hhas.subst (σ := Subst.from_TypeEnv env)
      simpa [CaptureSet.denot, Subst.from_TypeEnv_empty, CaptureSet.subst_id] using
        hsat.wf_sep (C.subst (Subst.from_TypeEnv env)) hhas'
    · intro C mode hhas
      have hhas' := hhas.subst (σ := Subst.from_TypeEnv env)
      simpa [CaptureSet.denot, Subst.from_TypeEnv_empty, CaptureSet.subst_id] using
        hsat.wf_mut (C.subst (Subst.from_TypeEnv env)) mode hhas'
    · intro C mode hhas
      have hhas' := hhas.subst (σ := Subst.from_TypeEnv env)
      simpa [CaptureSet.denot, Subst.from_TypeEnv_empty, CaptureSet.subst_id] using
        hsat.kind (C.subst (Subst.from_TypeEnv env)) mode hhas'
    · intro C1 C2 hdistinct
      have hdistinct' := hdistinct.subst (σ := Subst.from_TypeEnv env)
      simpa [CaptureSet.denot, Subst.from_TypeEnv_empty, CaptureSet.subst_id] using
        hsat.sep (C1.subst (Subst.from_TypeEnv env))
          (C2.subst (Subst.from_TypeEnv env)) hdistinct'

theorem SepCtx.WfInHeap.of_has
    {Ψ : SepCtx s} {H : Heap}
    (hwf : SepCtx.WfInHeap Ψ H)
    (hhas : Ψ.Has C) :
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

theorem MutabilityCtx.WfInHeap.of_has
    {Ψ : MutabilityCtx s} {H : Heap}
    (hwf : MutabilityCtx.WfInHeap Ψ H)
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
    {env : TypeEnv s} {Ψ : ModalCtx s} {m : Memory} :
    (env.extend_lock).Satisfy (Ψ.rename Rename.succ) m ↔ env.Satisfy Ψ m := by
  have hsubst :
      (Ψ.rename Rename.succ).subst (Subst.from_TypeEnv (env.extend_lock)) =
        Ψ.subst (Subst.from_TypeEnv env) := by
    calc
      (Ψ.rename Rename.succ).subst (Subst.from_TypeEnv (env.extend_lock))
        = (Ψ.subst Rename.succ.asSubst).subst (Subst.from_TypeEnv (env.extend_lock)) := by
            rw [ModalCtx.subst_asSubst]
      _ = Ψ.subst (Rename.succ.asSubst.comp (Subst.from_TypeEnv (env.extend_lock))) := by
            rw [ModalCtx.subst_comp]
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
  {cs : CaptureSet s} {Ψ : ModalCtx s} {e : Exp s} {E : Ty .exi s}
  (hclosed_e : (Exp.boxed cs Ψ e).IsClosed)
  (ht : SemanticTyping (cs.rename Rename.succ) (Γ.push_lock Ψ)
    (e.rename Rename.succ) (E.rename Rename.succ)) :
  SemanticTyping ∅ Γ (Exp.boxed cs Ψ e) (Ty.modal cs Ψ E).typ := by
  intro env k st store hts hdsep _
  simp only [Ty.exi_exp_denot, Ty.exi_val_denot]
  intro hmt
  apply Eval.eval_val
  · constructor
  · intro _hguard
    refine ⟨TraceOk.nil, st, WorldLe.refl_trunc_self _ st store, hmt, ?_,
      pack_bound_of_ne_pack (fun _ _ _ h => by simp [Exp.subst] at h),
    witness_live_of_ne_pack (fun _ _ _ h => by simp [Exp.subst] at h)⟩
    simp only [Ty.val_denot]
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
        · apply ModalCtx.wf_subst
          · exact ModalCtx.wf_of_closed hclosed_Ψ
          · exact from_TypeEnv_wf_in_heap hts
        · intro m' hsub hsat
          exact (TypeEnv.satisfy_subst_iff (env := env) (Ψ := Ψ) (m := m')).mp hsat
        · rw [← closed_captureset_subst_denot (env := env) hclosed_cs]
          rw [expand_captures_eq_ground_denot]
          simpa [CaptureSet.denot, Subst.from_TypeEnv_empty, CaptureSet.subst_id] using
            (CapabilitySet.Subset.refl :
              (cs.subst (Subst.from_TypeEnv env)).ground_denot store ⊆
                (cs.subst (Subst.from_TypeEnv env)).ground_denot store)
        · intro j hjk st' m' hwle hmt_body hcompat hkind hsep
          have hsub : m'.subsumes store := hwle.1
          have hsat_Ψ : env.Satisfy Ψ m' := by
            constructor
            · intro C hhas
              exact CaptureSet.wf_subst
                (SepCtx.WfInHeap.of_has (SepCtx.wf_of_closed hclosed_Ψ.sep) hhas)
                (from_TypeEnv_wf_in_heap (env_typing_monotonic hts hsub))
            · intro C mode hhas
              exact CaptureSet.wf_subst
                (MutabilityCtx.WfInHeap.of_has
                  (MutabilityCtx.wf_of_closed hclosed_Ψ.mutability) hhas)
                (from_TypeEnv_wf_in_heap (env_typing_monotonic hts hsub))
            · intro C mode hhas
              exact hkind C mode hhas
            · intro C1 C2 hdistinct
              exact hsep C1 C2 hdistinct
          have henv_lock : EnvTyping (Γ.push_lock Ψ) (env.extend_lock) j st' m' := by
            constructor
            · exact hsat_Ψ
            · exact env_typing_worldle_trunc hjk hts hwle
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
          have htyped := ht (env.extend_lock) j st' m' henv_lock
            hdsep.extend_lock hcompat'
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
          refine eval_post_monotonic ?_ (htyped hmt_body)
          intro t m v hpost hguard
          obtain ⟨htr, st'', hwle'', hmt'', hval'', hpb, hwl⟩ := hpost hguard
          exact ⟨htr, st'', hwle'', hmt'',
            IDenot.equiv_rtl (lweaken_exi_val_denot (env := env) (T := E)) hval'',
            hpb, hwl⟩

theorem sem_typ_app
  {T1 : Ty .capt s} {T2 : Ty .exi (s,x)}
  {x y : BVar s .var}
  (hx : SemanticTyping {} Γ (Exp.var (.bound x))
    (.typ ((Ty.arrow T1 (.var (.M .epsilon) (.bound x)) T2))))
  (hy : SemanticTyping {} Γ (Exp.var (.bound y)) (.typ T1)) :
  SemanticTyping (.var (.M .epsilon) (.bound x)) Γ
    (Exp.app (.bound x) (.bound y)) (T2.subst (Subst.openVar (.bound y))) := by
  intro env k st store hts hdsep hcompat
  simp only [Ty.exi_exp_denot, List.empty_eq]
  intro hmt
  -- Step-counted design: the function-body property fires at the FULL index `k` (`j := k`),
  -- so the result index `k - t.readCount` matches the goal.  Observe the function value at
  -- world `(stx, store)`, re-run the argument at that world (via `env_typing_worldle_down`),
  -- fire the body at `j := k`, then bridge the result type with `open_arg_exi_val_denot`.
  -- At budget `0` nothing is owed (`Eval.exhausted`); positivity feeds the var inversions.
  rcases Nat.eq_zero_or_pos k with rfl | hkpos
  · exact Eval.exhausted
  have hxd := semtyp_to_exi_exp_denot hx hts hdsep (Memory.is_compatible_empty store)
  obtain ⟨stx, hwlex, hmtx, hxval⟩ := var_exp_denot_inv hkpos hmt hxd
  simp only [Ty.exi_val_denot] at hxval
  obtain ⟨fx, hfx, cs', T0, e0, hval0, Rcell, hlk, hR0_sub, hbody⟩ := abs_val_denot_inv hxval
  have htsx := env_typing_worldle_down hts hwlex
  have hyd := semtyp_to_exi_exp_denot hy htsx hdsep (Memory.is_compatible_empty store)
  obtain ⟨sty, hwley, hmty, hyval⟩ := var_exp_denot_inv hkpos hmtx hyd
  simp only [Ty.exi_val_denot] at hyval
  have hfxeq : fx = (env.lookup_var x).1 := by cases hfx; rfl
  subst hfxeq
  have hcompatR0 : store.is_compatible (expand_captures store.heap cs') :=
    Memory.is_compatible_subset hR0_sub hcompat
  have hbody' := hbody k (Nat.le_refl k) sty store (env.lookup_var y).1
    (by rw [WP.World.trunc_self]; exact hwley) hmty hcompatR0 hyval
  simp only [Ty.exi_exp_denot] at hbody'
  have hrec0 := hbody' hmty
  have hgoal_expr : (Exp.app (.bound x) (.bound y)).subst (Subst.from_TypeEnv env)
      = Exp.app (.free (env.lookup_var x).1) (.free (env.lookup_var y).1) := rfl
  rw [hgoal_expr]
  apply Eval.eval_apply hlk
  refine eval_post_monotonic ?_ hrec0
  intro t m'' v hp hguard
  obtain ⟨htr, st'', hwle'', hmt'', hval'', hpb, hwl⟩ := hp hguard
  refine ⟨TraceOk.mono hR0_sub htr, st'',
    WorldLe.trans (WP.WorldLe.trunc (Nat.sub_le k t.readCount)
      (WorldLe.trans hwlex hwley)) hwle'', hmt'', ?_,
    pack_bound_mono hR0_sub (Memory.subsumes_refl store) hpb, hwl⟩
  exact IDenot.equiv_ltr (open_arg_exi_val_denot (env := env) (y := .bound y)
    (ps := compute_peakset env T1.captureSet) (T := T2)) hval''

theorem sem_typ_tapp
  {S : PureTy s} {T : Ty .exi (s,X)}
  {x : BVar s .var}
  (hx : SemanticTyping {} Γ (Exp.var (.bound x))
    (.typ (Ty.poly S.core (.var (.M .epsilon) (.bound x)) T))) :
  SemanticTyping (.var (.M .epsilon) (.bound x)) Γ
    (Exp.tapp (.bound x) S) (T.subst (Subst.openTVar S)) := by
  intro env k st store hts hdsep hcompat
  simp only [Ty.exi_exp_denot, List.empty_eq]
  intro hmt
  -- Step-counted design: the `poly` body fires at the FULL index `k` (`j := k`).  Observe the
  -- type-function value at world `(stx, store)`, instantiate its body with
  -- `denot := val_denot env S.core`, then bridge the result type with `open_targ_exi_val_denot`.
  rcases Nat.eq_zero_or_pos k with rfl | hkpos
  · exact Eval.exhausted
  have hxd := semtyp_to_exi_exp_denot hx hts hdsep (Memory.is_compatible_empty store)
  obtain ⟨stx, hwlex, hmtx, hxval⟩ := var_exp_denot_inv hkpos hmt hxd
  simp only [Ty.exi_val_denot] at hxval
  obtain ⟨fx, hfx, cs', S0, e0, hval0, Rcell, hlk, hR0_sub, hbody⟩ := tabs_val_denot_inv hxval
  have hfxeq : fx = (env.lookup_var x).1 := by cases hfx; rfl
  subst hfxeq
  have hcompatR0 : store.is_compatible (expand_captures store.heap cs') :=
    Memory.is_compatible_subset hR0_sub hcompat
  have hbody' := hbody k (Nat.le_refl k) stx store (Ty.val_denot env S.core)
    (by rw [WP.World.trunc_self]; exact WorldLe.refl stx store) hmtx
    hcompatR0 (val_denot_is_proper hts)
    (val_denot_implies_simple_ans (typed_env_is_implying_simple_ans hts) S.core)
    (fun _ _ _ _ _ _ h => h)
    (pure_ty_enforce_pure (typed_env_enforces_pure hts) S.p)
  simp only [Ty.exi_exp_denot] at hbody'
  have hrec0 := hbody' hmtx
  have hgoal_expr : (Exp.tapp (.bound x) S).subst (Subst.from_TypeEnv env)
      = Exp.tapp (.free (env.lookup_var x).1) (S.subst (Subst.from_TypeEnv env)) := rfl
  rw [hgoal_expr]
  apply Eval.eval_tapply hlk
  refine eval_post_monotonic ?_ hrec0
  intro t m'' v hp hguard
  obtain ⟨htr, st'', hwle'', hmt'', hval'', hpb, hwl⟩ := hp hguard
  refine ⟨TraceOk.mono hR0_sub htr, st'',
    WorldLe.trans (WP.WorldLe.trunc (Nat.sub_le k t.readCount) hwlex) hwle'', hmt'', ?_,
    pack_bound_mono hR0_sub (Memory.subsumes_refl store) hpb, hwl⟩
  exact IDenot.equiv_ltr (open_targ_exi_val_denot (env := env) (S := S) (T := T)) hval''

theorem sem_typ_capp
  {x : BVar s .var}
  {T : Ty .exi (s,C)}
  {D : CaptureSet s}
  (hΓ : Γ.IsClosed)
  (hD_closed : D.IsClosed)
  (hvalid_D : CaptureBound.IsValid Γ (.bound D))
  (hx : SemanticTyping {} Γ (Exp.var (.bound x))
    (.typ (.cpoly (.bound D) (.var (.M .epsilon) (.bound x)) T))) :
  SemanticTyping (.var (.M .epsilon) (.bound x)) Γ
    (Exp.capp (.bound x) D) (T.subst (Subst.openCVar D)) := by
  intro env k st store hts hdsep hcompat
  simp only [Ty.exi_exp_denot, List.empty_eq]
  intro hmt
  -- Step-counted design: the `cpoly` body fires at the FULL index `k` (`j := k`).  Observe the
  -- capture-function value at world `(stx, store)`, instantiate its body with the ground
  -- capture `CS := D.subst (from_TypeEnv env)`, then bridge with `open_carg_exi_val_denot`.
  rcases Nat.eq_zero_or_pos k with rfl | hkpos
  · exact Eval.exhausted
  have hxd := semtyp_to_exi_exp_denot hx hts hdsep (Memory.is_compatible_empty store)
  obtain ⟨stx, hwlex, hmtx, hxval⟩ := var_exp_denot_inv hkpos hmt hxd
  simp only [Ty.exi_val_denot] at hxval
  obtain ⟨fx, hfx, cs', B0, e0, hval0, Rcell, hlk, hR0_sub, hbody⟩ := cabs_val_denot_inv hxval
  have hfxeq : fx = (env.lookup_var x).1 := by cases hfx; rfl
  subst hfxeq
  have hcompatR0 : store.is_compatible (expand_captures store.heap cs') :=
    Memory.is_compatible_subset hR0_sub hcompat
  have hCSwf : (D.subst (Subst.from_TypeEnv env)).WfInHeap store.heap :=
    CaptureSet.wf_subst (CaptureSet.wf_of_closed hD_closed) (from_TypeEnv_wf_in_heap hts)
  have hCSdf : ((D.subst (Subst.from_TypeEnv env)).ground_denot store).drop_free := by
    intro l hmem
    obtain ⟨c, hsub, _⟩ :=
      drop_denot_peak hts hΓ (envtyping_lookup_cvar_drop_free hts) hD_closed hmem
    exact hvalid_D c hsub
  have hbody' := hbody k (Nat.le_refl k) stx store (D.subst (Subst.from_TypeEnv env)) hCSwf hCSdf
    (by rw [WP.World.trunc_self]; exact WorldLe.refl stx store) hmtx hcompatR0 (by
      have heq : (D.subst (Subst.from_TypeEnv env)).denot TypeEnv.empty store
          = D.denot env store :=
        congrFun (closed_captureset_subst_denot hD_closed) store
      rw [heq]
      exact CapabilitySet.BoundedBy.set CapabilitySet.Subset.refl)
  simp only [Ty.exi_exp_denot] at hbody'
  have hrec0 := hbody' hmtx
  have hgoal_expr : (Exp.capp (.bound x) D).subst (Subst.from_TypeEnv env)
      = Exp.capp (.free (env.lookup_var x).1) (D.subst (Subst.from_TypeEnv env)) := rfl
  rw [hgoal_expr]
  apply Eval.eval_capply hlk
  refine eval_post_monotonic ?_ hrec0
  intro t m'' v hp hguard
  obtain ⟨htr, st'', hwle'', hmt'', hval'', hpb, hwl⟩ := hp hguard
  refine ⟨TraceOk.mono hR0_sub htr, st'',
    WorldLe.trans (WP.WorldLe.trunc (Nat.sub_le k t.readCount) hwlex) hwle'', hmt'', ?_,
    pack_bound_mono hR0_sub (Memory.subsumes_refl store) hpb, hwl⟩
  exact IDenot.equiv_ltr (open_carg_exi_val_denot (env := env) (C := D) (T := T)
    (cap := (D.subst (Subst.from_TypeEnv env)).ground_denot store)) hval''

theorem sem_typ_invoke
  {x y : BVar s .var}
    (hx : SemanticTyping {} Γ (Exp.var (.bound x))
    (.typ (.cap (.var (.M .epsilon) (.bound x)))))
  (hy : SemanticTyping {} Γ (Exp.var (.bound y))
    (.typ .unit)) :
  SemanticTyping (.var (.M .epsilon) (.bound x)) Γ
    (Exp.app (.bound x) (.bound y)) (.typ .unit) := by
  intro env k st store hts hdsep _
  simp only [Ty.exi_exp_denot, Exp.subst, Subst.from_TypeEnv, Var.subst,
    CaptureSet.denot, List.empty_eq]
  intro hmt
  rcases Nat.eq_zero_or_pos k with rfl | hkpos
  · exact Eval.exhausted
  have h1 := semtyp_to_exi_exp_denot hx hts hdsep
    (Memory.is_compatible_empty store)
  simp only [List.empty_eq] at h1
  obtain ⟨st1, _, _, h1'⟩ := var_exp_denot_inv hkpos hmt h1
  simp only [Ty.exi_val_denot] at h1'
  have ⟨fx, hfx, hlk_cap, hmem_cap⟩ := cap_val_denot_inv h1'
  have h2 := semtyp_to_exi_exp_denot hy hts hdsep
    (Memory.is_compatible_empty store)
  simp only [List.empty_eq] at h2
  obtain ⟨st2, _, _, h2'⟩ := var_exp_denot_inv hkpos hmt h2
  simp only [Ty.exi_val_denot] at h2'
  have ⟨fy, hfy, hval_unit, R, hlk_unit⟩ := unit_val_denot_inv h2'
  have : fx = (env.lookup_var x).1 := by cases hfx; rfl
  subst this
  have : fy = (env.lookup_var y).1 := by cases hfy; rfl
  subst this
  have hcov :
    (CaptureSet.denot env (.var (.M .epsilon) (.bound x)) store).covers
      (.access .epsilon) (env.lookup_var x).1 := hmem_cap
  apply Eval.eval_invoke hlk_cap hlk_unit
  intro _hguard
  exact ⟨TraceOk.access hcov, st, WorldLe.refl_trunc_self _ st store, hmt,
    by simp only [Ty.exi_val_denot, Ty.val_denot, resolve],
    pack_bound_of_ne_pack (fun _ _ _ h => nomatch h),
    witness_live_of_ne_pack (fun _ _ _ h => nomatch h)⟩

theorem sem_typ_unit :
  SemanticTyping {} Γ Exp.unit (.typ .unit) := by
  intro env k st store hts _ _
  simp only [Ty.exi_exp_denot, Exp.subst, List.empty_eq]
  intro hmt
  apply Eval.eval_val
  · exact Exp.IsSimpleVal.unit
  · intro _hguard
    exact ⟨TraceOk.nil, st, WorldLe.refl_trunc_self _ st store, hmt,
      by simp only [Ty.exi_val_denot, Ty.val_denot, resolve],
      pack_bound_of_ne_pack (fun _ _ _ h => nomatch h),
    witness_live_of_ne_pack (fun _ _ _ h => nomatch h)⟩

theorem sem_typ_btrue :
  SemanticTyping {} Γ Exp.btrue (.typ .bool) := by
  intro env k st store hts _ _
  simp only [Ty.exi_exp_denot, Exp.subst, List.empty_eq]
  intro hmt
  apply Eval.eval_val
  · exact Exp.IsSimpleVal.btrue
  · intro _hguard
    refine ⟨TraceOk.nil, st, WorldLe.refl_trunc_self _ st store, hmt, ?_,
      pack_bound_of_ne_pack (fun _ _ _ h => nomatch h),
    witness_live_of_ne_pack (fun _ _ _ h => nomatch h)⟩
    simp only [Ty.exi_val_denot, Ty.val_denot, resolve]
    left; trivial

theorem sem_typ_bfalse :
  SemanticTyping {} Γ Exp.bfalse (.typ .bool) := by
  intro env k st store hts _ _
  simp only [Ty.exi_exp_denot, Exp.subst, List.empty_eq]
  intro hmt
  apply Eval.eval_val
  · exact Exp.IsSimpleVal.bfalse
  · intro _hguard
    refine ⟨TraceOk.nil, st, WorldLe.refl_trunc_self _ st store, hmt, ?_,
      pack_bound_of_ne_pack (fun _ _ _ h => nomatch h),
    witness_live_of_ne_pack (fun _ _ _ h => nomatch h)⟩
    simp only [Ty.exi_val_denot, Ty.val_denot, resolve]
    right; trivial

theorem sem_typ_cond
  {C1 C2 C3 : CaptureSet s} {Γ : Ctx s}
  {x : Var .var s} {e2 e3 : Exp s} {T : Ty .exi s}
  (ht1 : SemanticTyping C1 Γ (.var x) (.typ .bool))
  (ht2 : SemanticTyping C2 Γ e2 T)
  (ht3 : SemanticTyping C3 Γ e3 T) :
  SemanticTyping (C1 ∪ C2 ∪ C3) Γ (.cond x e2 e3) T := by
  intro env k st store hts hdsep hcompat
  simp only [Ty.exi_exp_denot, Exp.subst, List.empty_eq]
  intro hmt
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
  have hcompat_C1 : store.is_compatible (C1.denot env store) :=
    Memory.is_compatible_subset hsubC1 hcompat
  rcases Nat.eq_zero_or_pos k with rfl | hkpos
  · exact Eval.exhausted
  have hguard_base := semtyp_to_exi_exp_denot ht1 hts hdsep hcompat_C1
  simp only [Ty.exi_exp_denot] at hguard_base
  have hQ1_at_store : ∃ st_g,
      Ty.val_denot env .bool k st_g store (.var (x.subst (Subst.from_TypeEnv env))) := by
    obtain ⟨_, st_g, _, _, h1, _⟩ := Eval.var_inv (hguard_base hmt) hkpos
    exact ⟨st_g, by simpa [Ty.exi_val_denot] using h1⟩
  obtain ⟨st_g, hQ1_at_store⟩ := hQ1_at_store
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
  · intro _hres_true
    have h2 := ht2 env k st store hts hdsep hcompat_C2
    simp only [Ty.exi_exp_denot] at h2
    refine eval_post_monotonic ?_ (h2 hmt)
    intro t m v hpost hguard
    obtain ⟨htr, st', hwle', hmt', hval', hpb, hwl⟩ := hpost hguard
    exact ⟨TraceOk.mono hsubC2 htr, st', hwle', hmt', hval',
      pack_bound_mono hsubC2 (Memory.subsumes_refl store) hpb, hwl⟩
  · intro _hres_false
    have h3 := ht3 env k st store hts hdsep hcompat_C3
    simp only [Ty.exi_exp_denot] at h3
    refine eval_post_monotonic ?_ (h3 hmt)
    intro t m v hpost hguard
    obtain ⟨htr, st', hwle', hmt', hval', hpb, hwl⟩ := hpost hguard
    exact ⟨TraceOk.mono hsubC3 htr, st', hwle', hmt', hval',
      pack_bound_mono hsubC3 (Memory.subsumes_refl store) hpb, hwl⟩

theorem sem_typ_reader
  (_hclosed : Γ.IsClosed)
  (hx : Γ.LookupVar x (.cell C T)) :
  SemanticTyping {} Γ (Exp.reader (.bound x))
    (.typ (.reader (.var (.M .ro) (.bound x)) T)) := by
  intro env k st store hts _ _
  simp only [Ty.exi_exp_denot, Exp.subst, List.empty_eq]
  intro hmt
  apply Eval.eval_val
  · exact Exp.IsSimpleVal.reader
  · intro _hguard
    refine ⟨TraceOk.nil, st, WorldLe.refl_trunc_self _ st store, hmt, ?_,
      pack_bound_of_ne_pack (fun _ _ _ h => nomatch h),
    witness_live_of_ne_pack (fun _ _ _ h => nomatch h)⟩
    simp only [Ty.exi_val_denot, Ty.val_denot]
    have hcell := typed_env_lookup_var hts hx
    have ⟨_, b0, ℓ0, R, rfl, hlookup_cell, _, hstl, himpl⟩ := cell_val_denot_inv_store hcell
    simp only [Var.subst, Subst.from_TypeEnv]
    refine ⟨?hwf_e, ?hwf_cs, (env.lookup_var x).1, b0, ℓ0, R, ?hres, ?hlookup, ?hcover,
      hstl, himpl⟩
    · exact Exp.WfInHeap.wf_reader (Var.WfInHeap.wf_free hlookup_cell)
    · exact CaptureSet.WfInHeap.wf_var_free hlookup_cell
    · rfl
    · simpa [Memory.lookup] using hlookup_cell
    · have hden :
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
  (hx : SemanticTyping {} Γ (Exp.var (.bound x)) (.typ T)) :
  SemanticTyping {} Γ (Exp.alloc (.bound x))
    (.exi 1 (.cell (.cvar (.M .epsilon) .here) (T.rename Rename.succ))) := by
  intro env k st store hts hdsep hcompat
  simp only [Ty.exi_exp_denot, Exp.subst, Subst.from_TypeEnv, Var.subst, List.empty_eq]
  intro hmt
  -- `x`'s location is present in the store (it satisfies `val_denot T`).  Retain `hmt1`
  -- (`MemTyped k st1 store`) so the fresh cell's stored relation, which lives at `st1`,
  -- lines up with the world the cell op operates at.
  rcases Nat.eq_zero_or_pos k with rfl | hkpos
  · exact Eval.exhausted
  have h1 := semtyp_to_exi_exp_denot hx hts hdsep (Memory.is_compatible_empty store)
  obtain ⟨st1, hwle1, hmt1, hval1⟩ := var_exp_denot_inv hkpos hmt h1
  simp only [Ty.exi_val_denot] at hval1
  have hwf := val_denot_implies_wf (typed_env_is_implying_wf hts) T k st1 store
    (.var (.free (env.lookup_var x).1)) hval1
  have hlk : store.heap (env.lookup_var x).1 ≠ none := by
    cases hwf with
    | wf_var hv => cases hv with | wf_free hh => exact Option.ne_none_iff_exists'.mpr ⟨_, hh⟩
  -- Reduce the alloc to its (faithful-cell) postcondition.
  apply Eval.eval_alloc (hlk := hlk)
  intro l' hfresh _hguard
  -- The fresh cell `l'` stores the content relation `R := val_denot env T k st1` (monotone
  -- by `val_denot_is_monotonic`), and the result world is `st1.set l' R`.  `WT_alloc`
  -- discharges `WorldLe (st1.set l' R) ext st1 store` and `MemTyped k (st1.set l' R) ext`.
  set fx := (env.lookup_var x).1 with hfx
  -- The fresh cell stores the content type's denotation as a *world-parametrized* relation
  -- `R j w' := val_denot env T j.val w'` (so the cell agreement is definitional, and its
  -- growth-stability is `val_denot_worldle_monotonic`).
  set R : MonRel k := fun j w' m' e' => Ty.val_denot env T j.val w' m' e' with hRdef
  set ext := store.extend_mcell l' fx hfresh hlk with hext
  have hsub_ext : ext.subsumes store := Memory.extend_mcell_subsumes store l' fx hfresh hlk
  -- `l'` is heap-fresh in `store`, hence store-typing-fresh in `st1` (by consistency).
  have hst1_fresh : st1.lookup l' = none := by
    rcases hopt : st1.lookup l' with _ | R0
    · rfl
    · obtain ⟨n, ℓ, hlkn⟩ := hmt1.1 l' R0 hopt
      rw [show store.lookup l' = store.heap l' from rfl, hfresh] at hlkn
      cases hlkn
  have hRstable : ∀ (i : Fin k) (w1 w2 : StoreTyping i.val) (m1 m2 : Memory),
      WorldLe w2 m2 w1 m1 → ∀ e, R i w1 m1 e → R i w2 m2 e :=
    fun i _ _ _ _ hw e h => val_denot_worldle_monotonic (typed_env_is_monotonic hts) T hw h
  have hRext : ∀ (i : Fin k),
      R i ((st1.set l' R).trunc (Nat.le_of_lt i.isLt)) ext (.var (.free fx)) := by
    -- from `hval1 : val_denot env T k st1 store (var fx)`, drop the index `k → i.val` through the
    -- truncation (`val_denot_down_trunc`) and then transport to the grown world `st1.set l' R`
    -- (a fresh cell was added) at the extended memory `ext` (`val_denot_worldle_monotonic`).
    intro i
    change Ty.val_denot env T i.val ((st1.set l' R).trunc (Nat.le_of_lt i.isLt)) ext
      (.var (.free fx))
    have hdown := val_denot_down_trunc (typed_env_is_downward_closed hts) T
      (Nat.le_of_lt i.isLt) (.var (.free fx)) hval1
    -- the set adds only the fresh cell `l'` (absent from `st1`), so `st1.set l' R` grows `st1`.
    have hwle_base : WorldLe (st1.set l' R) ext st1 store := by
      refine ⟨hsub_ext, ?_⟩
      intro l R0 hl
      rw [WP.World.set_lookup]
      by_cases hll' : l = l'
      · exfalso; subst hll'; rw [hst1_fresh] at hl; cases hl
      · rw [if_neg hll']; exact hl
    exact val_denot_worldle_monotonic (typed_env_is_monotonic hts) T
      (WP.WorldLe.trunc (Nat.le_of_lt i.isLt) hwle_base) hdown
  obtain ⟨walloc, hmtalloc⟩ := WT_alloc hfresh hlk hmt1 hRstable hRext
  have hlk_l' : ext.lookup l' = some (.capability (.mcell fx .live)) :=
    Memory.extend_mcell_lookup hfresh hlk
  have hlk_l'_heap : ext.heap l' = some (.capability (.mcell fx .live)) := hlk_l'
  -- the alloc trace has no `.access .ro`, so the step-counted result index stays at `k`
  -- (`readCount [alloc] = 0`, `st.trunc (le_refl) = st`).
  refine ⟨TraceOk.alloc, ?_⟩
  rw [show st.trunc (Nat.sub_le k (Trace.readCount [TraceItem.alloc l'])) = st from
    WP.World.trunc_self _ st]
  refine ⟨st1.set l' R, WorldLe.trans hwle1 walloc, hmtalloc, ?_, ?_, ?_⟩
  · -- existential value denotation: `.pack ⟨[.var (.M .epsilon) (.free l')], rfl⟩ (.free l')`
    -- is an `exi 1 (cell (cvar ε here) (T.rename succ))`, with the fresh cell storing `R`.
    simp only [Ty.exi_val_denot]
    refine ⟨⟨[.var (.M .epsilon) (.free l')], rfl⟩, .free l', rfl, ?_, ?_, ?_, ?_⟩
    · -- well-formedness of the (single) evidence
      intro cs hmem
      cases hmem with
      | head => exact CaptureSet.WfInHeap.wf_var_free hlk_l'
      | tail _ h => cases h
    · -- drop-free: the cvar witness denotes a singleton at `l'`, which has no `.drop`.
      intro cs hmem
      cases hmem with
      | tail _ h => cases h
      | head =>
        simp only [CaptureSet.ground_denot, reachability_of_loc, hlk_l'_heap,
          CapabilitySet.applyAccess_M, CapabilitySet.applyMut_singleton_epsilon]
        intro l'' hmem
        exact CapabilitySet.singleton_no_drop hmem
    · -- pairwise disjointness: vacuous for a single evidence
      exact List.Pairwise.cons (fun b hb => nomatch hb) List.Pairwise.nil
    · -- the cell value denotation at the (cvar-extended) env / extended world.
      simp only [Ty.val_denot]
      refine ⟨?_, l', fx, .live, R, rfl, hlk_l', ?_, ?_, ?_⟩
      · -- WfInHeap of the substituted cvar capture
        exact CaptureSet.WfInHeap.wf_var_free hlk_l'
      · -- coverage: the cvar `.here` denotes (definitionally) the singleton at `l'`
        change ((CaptureSet.var (.M .epsilon) (.free l')).ground_denot ext).covers
          (.access .epsilon) l'
        simp only [CaptureSet.ground_denot, reachability_of_loc, hlk_l'_heap,
          CapabilitySet.applyAccess_M,
          CapabilitySet.singleton]
        exact CapabilitySet.covers.here CapMode.Le.refl
      · -- store typing: the fresh cell is typed with `R`
        change (st1.set l' R).lookup l' = some R
        simp [WP.World.set_lookup]
      · -- content agreement (biconditional over all lower worlds).  `R j w' = val_denot env T
        -- j.val w'` by definition, and the cvar-weaken equivalence `rebind_val_denot` (a
        -- genuine biconditional) identifies `val_denot env T` with `val_denot (extend_cvar)
        -- (T.rename succ)` at every lower world.
        intro j w' m' e'
        exact rebind_val_denot (Rebind.cweaken (env := env)
          (cs := .var (.M .epsilon) (.free l'))
          (cap := (CaptureSet.var (.M .epsilon) (.free l')).ground_denot ext)
          (a := .can_drop)) T j.val w' m' e'
  · -- pack_bound: the witness `l'` is fresh in `store` (`store.lookup l' = none`).
    intro n0 cs0 x0 heq mu l hmem
    cases heq
    right
    -- `unionAll ⟨[c], rfl⟩ = c ∪ ∅`; unfold the union-reachability definitionally.
    change ((CaptureSet.var (.M .epsilon) (.free l')).reachability ext
      ∪ (CaptureSet.empty : CaptureSet {}).reachability ext).hasmem mu l at hmem
    cases hmem with
    | right h => cases h
    | left h =>
      simp only [CaptureSet.reachability, reachability_of_loc, hlk_l'_heap,
        CapabilitySet.applyAccess_M, CapabilitySet.singleton] at h
      cases h
      show store.lookup l' = none
      exact hfresh
  · -- witness_live: the fresh cell `l'` is live in `ext`.
    intro n0 cs0 x0 heq
    cases heq
    intro mu l b ℓ hmem hheap
    change ((CaptureSet.var (.M .epsilon) (.free l')).reachability ext
      ∪ (CaptureSet.empty : CaptureSet {}).reachability ext).hasmem mu l at hmem
    cases hmem with
    | right h => cases h
    | left h =>
      simp only [CaptureSet.reachability, reachability_of_loc, hlk_l'_heap,
        CapabilitySet.applyAccess_M, CapabilitySet.singleton] at h
      cases h
      rw [hlk_l'_heap] at hheap
      cases hheap; rfl

theorem sem_typ_drop {x : BVar s .var}
  (hx : SemanticTyping {} Γ (Exp.var (.bound x))
    (.typ (.cell (.var (.M .epsilon) (.bound x)) T)))
  (_hΓ : Γ.IsClosed) :
  SemanticTyping (.var .drop (.bound x)) Γ (Exp.drop (.bound x)) (.typ .unit) := by
  intro env k st store hts hdsep hcompat
  simp only [Ty.exi_exp_denot, Exp.subst, Subst.from_TypeEnv, Var.subst, List.empty_eq]
  intro hmt
  have h1 := semtyp_to_exi_exp_denot hx hts hdsep
    (Memory.is_compatible_empty store)
  simp only [List.empty_eq] at h1
  rcases Nat.eq_zero_or_pos k with rfl | hkpos
  · exact Eval.exhausted
  obtain ⟨st1, _, _, h1'⟩ := var_exp_denot_inv hkpos hmt h1
  simp only [Ty.exi_val_denot] at h1'
  have ⟨fx, b0, ℓ0, hfx, hlk_cell, hmem_cell⟩ := cell_val_denot_inv h1'
  have : fx = (env.lookup_var x).1 := by cases hfx; rfl
  subst this
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
  -- MemTyped is preserved under `drop_mcell`: the dropped cell is no longer live (so its
  -- `MemTyped` obligation is vacuous), and every *other* live cell `l'` holds the same
  -- content, with `R l'` carrying from `store` to the subsuming dropped memory.  Carrying
  -- it requires the stored relation `R` to be MEMORY-MONOTONE, which `MemTyped`/`StoreTyping`
  -- do not record (the relations are arbitrary `Memory → Exp → Prop`).  At the call site the
  -- stored relations are always `val_denot env Tc k st` (monotone, `val_denot_is_monotonic`),
  -- but that fact is not available through the abstract `MemTyped` interface.  Closing this
  -- needs `Core.lean` to refine `StoreTyping`/`MemTyped` to carry relation-monotonicity.
  have hmt_dropped : MemTyped k st
      (store.drop_mcell (env.lookup_var x).1 ⟨b0, hlk_cell'⟩) :=
    (WT_drop ⟨b0, hlk_cell'⟩ hmt).2
  -- the dealloc trace has no `.access .ro`, so the step-counted result index stays at `k`
  -- (`st.trunc (le_refl) = st`).
  intro _hguard
  refine ⟨TraceOk.dealloc ?_, ?ex⟩
  case ex =>
    rw [show st.trunc (Nat.sub_le k
        (Trace.readCount [TraceItem.dealloc (env.lookup_var x).1])) = st from
      WP.World.trunc_self _ st]
    exact ⟨st, ⟨Memory.drop_mcell_subsumes _ _ ⟨b0, hlk_cell'⟩, fun _ _ h => h⟩,
      hmt_dropped,
      by simp only [Ty.exi_val_denot, Ty.val_denot, resolve],
      pack_bound_of_ne_pack (fun _ _ _ h => nomatch h),
      witness_live_of_ne_pack (fun _ _ _ h => nomatch h)⟩
  -- The `.drop` coverage comes directly from the drop-qualified budget:
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
  (hx : SemanticTyping {} Γ (Exp.var (.bound x)) (.typ (.reader C T))) :
  SemanticTyping (.var (.M .epsilon) (.bound x)) Γ (Exp.read (.bound x)) (.typ T) := by
  intro env k st store hts hdsep hcompat
  simp only [Ty.exi_exp_denot, Exp.subst, Subst.from_TypeEnv, Var.subst, List.empty_eq]
  intro hmt
  -- **Budget 0: nothing is owed** (`Eval.exhausted`).  This is where the former
  -- step-index-0 gap of the read rule is discharged honestly: the budget-indexed `Safe`
  -- is trivial at 0 and the `μ(t) < 0` guard is vacuous (Phase 2c design finding).
  rcases Nat.eq_zero_or_pos k with rfl | hkpos
  · exact Eval.exhausted
  -- `x` is a reader; recover its underlying cell `y`, content `b0`, store relation `Rst`,
  -- and the content-type implication.  Retain `hmt1` so `read_typed`/`himpl` live at `st1`.
  have h1 := semtyp_to_exi_exp_denot hx hts hdsep (Memory.is_compatible_empty store)
  simp only [Ty.exi_exp_denot, List.empty_eq] at h1
  obtain ⟨_, st1, hwle1, hmt1, hval1, _, _⟩ := Eval.var_inv (h1 hmt) hkpos
  simp only [Ty.exi_val_denot] at hval1
  obtain ⟨fx, y, b0, ℓ0, hval, Rcell, Rst, hfx, hlk_fx, hlk_y, _hcov, hstl, himpl⟩ :=
    reader_val_denot_inv_store hval1
  have hfxeq : fx = (env.lookup_var x).1 := by cases hfx; rfl
  subst hfxeq
  -- The reader cell's stored reachability is `{ro: y}` (heap well-formedness), so the
  -- use-set budget `{x}@ε` denotes `singleton ro y`; compatibility forces `y` live.
  have hRcell : Rcell = CapabilitySet.cap (.access .ro) y := by
    have := store.wf.wf_reach _ _ hval _ hlk_fx
    simpa only [compute_reachability] using this
  have hbudget :
      (CaptureSet.var (.M .epsilon) (Var.bound x)).denot env store
        = CapabilitySet.singleton .ro y := by
    simp only [CaptureSet.denot, CaptureSet.subst, Var.subst, Subst.from_TypeEnv,
      CaptureSet.ground_denot, reachability_of_loc, hlk_fx, hRcell,
      CapabilitySet.applyAccess_M, CapabilitySet.applyMut, CapabilitySet.singleton]
  have hlive : ℓ0 = .live := by
    have hcompat' : store.is_compatible (CapabilitySet.singleton .ro y) := hbudget ▸ hcompat
    exact hcompat' (.access .ro) y b0 ℓ0 CapabilitySet.hasmem.here hlk_y
  subst hlive
  have hlk_y' : store.lookup y = some (.capability (.mcell b0 .live)) := by
    simpa [Memory.lookup] using hlk_y
  have hlk_fx' : store.lookup (env.lookup_var x).1
      = some (.val ⟨Exp.reader (.free y), hval, Rcell⟩) := by
    simpa [Memory.lookup] using hlk_fx
  have hlkn : store.heap b0 ≠ none := store.mcell_wf y b0 hlk_y
  apply Eval.eval_read (hlkx := hlk_fx') (hlky := hlk_y') (hlkn := hlkn)
  -- The single `.access ro y` event is covered by the use-set budget `{x}@ε = {ro: y}`.
  have hcov_y : ((CaptureSet.var (.M .epsilon) (Var.bound x)).denot env store).covers
      (.access .ro) y := by
    rw [hbudget]; exact CapabilitySet.covers.here CapMode.Le.refl
  -- `st1`/`hwle1`/`hmt1` came from a variable (empty trace), so they live at the full index `k`.
  simp only [Trace.readCount_nil, Nat.sub_zero, WP.World.trunc_self] at hwle1 hmt1
  -- STEP DROP: the read event `.access .ro y` consumes one index, so the result index is `k − 1`.
  -- `MemTyped k` (`hmt1`) exposes the cell content at every `i < k`; the reader biconditional
  -- `himpl` turns the stored relation into `val_denot env T` there.  At the result index
  -- `k − 1 < k` this is exactly what the step-counted postcondition demands (delivery is only
  -- owed within budget, `μ(t) = 1 < k`).
  intro _hguard
  have hpred : k - 1 < k := Nat.sub_lt hkpos Nat.one_pos
  -- the read event `.access .ro y` has `readCount 1`, so the result index is `k − 1`
  -- (`k - readCount [.access .ro y]` is definitionally `k - 1`).
  refine ⟨TraceOk.access hcov_y, st1.trunc (Nat.sub_le k 1),
    WP.WorldLe.trunc (Nat.sub_le k 1) hwle1, MemTyped_trunc (Nat.sub_le k 1) hmt1, ?_,
    pack_bound_of_ne_pack (fun _ _ _ h => nomatch h),
    witness_live_of_ne_pack (fun _ _ _ h => nomatch h)⟩
  simp only [Ty.exi_val_denot]
  -- content at the result index `k − 1`, extracted from `MemTyped`/`himpl` at `⟨k-1, _⟩ : Fin k`.
  exact (himpl ⟨k - 1, hpred⟩ (st1.trunc (Nat.le_of_lt hpred)) store (.var (.free b0))).mp
    (hmt1.2.2 y b0 Rst hstl hlk_y' ⟨k - 1, hpred⟩)

theorem sem_typ_write
  {x y : BVar s .var}
  (_hΓ : Γ.IsClosed)
  (hx : SemanticTyping {} Γ (Exp.var (.bound x)) (.typ (.cell Cx T)))
  (hy : SemanticTyping {} Γ (Exp.var (.bound y)) (.typ T)) :
  SemanticTyping (.var (.M .epsilon) (.bound x)) Γ
    (Exp.write (.bound x) (.bound y)) (.typ .unit) := by
  intro env k st store hts hdsep hcompat
  simp only [Ty.exi_exp_denot, Exp.subst, Subst.from_TypeEnv, Var.subst, List.empty_eq]
  intro hmt
  -- `x` is a live cell; recover its location, content cell, store relation `R`, and the
  -- content-type implication `himpl`.  Retain `hmt1` so `R`/`himpl` (at `st1`) line up with
  -- `WT_write` (which writes into the cell typed by `R`).
  rcases Nat.eq_zero_or_pos k with rfl | hkpos
  · exact Eval.exhausted
  have h1 := semtyp_to_exi_exp_denot hx hts hdsep (Memory.is_compatible_empty store)
  obtain ⟨st1, hwle1, hmt1, hval1⟩ := var_exp_denot_inv hkpos hmt h1
  simp only [Ty.exi_val_denot] at hval1
  obtain ⟨fx, b0, ℓ0, R, hfx, hlk_cell, _hmem_cell, hstl, himpl⟩ :=
    cell_val_denot_inv_store hval1
  have hfxeq : fx = (env.lookup_var x).1 := by cases hfx; rfl
  subst hfxeq
  -- **Sequential world-threading**: run `y`'s soundness at `x`'s post-world `st1` (not the
  -- original `st`), so `y`'s value is native at `st2 ⊒ st1`, where the cell is still typed `R`.
  -- This is what lets the write payoff (`hyR`) draw the content type at `st2`'s truncation
  -- rather than reconciling two incomparable futures of `st`.
  have htsx1 : EnvTyping Γ env k st1 store := env_typing_worldle_down hts hwle1
  have h2 := semtyp_to_exi_exp_denot hy htsx1 hdsep (Memory.is_compatible_empty store)
  obtain ⟨st2, hwle2, hmt2, hval2⟩ := var_exp_denot_inv hkpos hmt1 h2
  simp only [Ty.exi_val_denot] at hval2
  -- the cell (typed `R` at `st1`) is still typed `R` at the grown world `st2 ⊒ st1`.
  have hstl2 : st2.lookup (env.lookup_var x).1 = some R := hwle2.2 _ R hstl
  have hwf_y := val_denot_implies_wf (typed_env_is_implying_wf hts) T k st2 store
    (.var (.free (env.lookup_var y).1)) hval2
  have hly : store.heap (env.lookup_var y).1 ≠ none := by
    cases hwf_y with
    | wf_var hv => cases hv with | wf_free hh => exact Option.ne_none_iff_exists'.mpr ⟨_, hh⟩
  -- The use-set budget is `{x}` at access `ε`.
  have hbudget_denot :
      (CaptureSet.var (.M .epsilon) (Var.bound x)).denot env store
        = CapabilitySet.singleton .epsilon (env.lookup_var x).1 := by
    simp only [CaptureSet.denot, CaptureSet.subst, Var.subst, Subst.from_TypeEnv,
      CaptureSet.ground_denot, CapabilitySet.applyAccess_M, CapabilitySet.applyMut,
      reachability_of_loc, hlk_cell, CapabilitySet.singleton]
  -- Liveness of the written cell, from the (access-mode) budget compatibility.
  have hlive : ℓ0 = .live := by
    have hcompat' :
        store.is_compatible (CapabilitySet.singleton .epsilon (env.lookup_var x).1) :=
      hbudget_denot ▸ hcompat
    exact hcompat' (.access .epsilon) (env.lookup_var x).1 b0 ℓ0
      CapabilitySet.hasmem.here hlk_cell
  subst hlive
  have hlk_cell' :
      store.lookup (env.lookup_var x).1 = some (.capability (.mcell b0 .live)) := by
    simpa [Memory.lookup] using hlk_cell
  apply Eval.eval_write (hx := hlk_cell') (hlky := hly)
  -- The single `.access ε x` event is covered by the use-set budget `{x}`.
  have hcov :
      ((CaptureSet.var (.M .epsilon) (Var.bound x)).denot env store).covers
        (.access .epsilon) (env.lookup_var x).1 := by
    rw [hbudget_denot]; exact CapabilitySet.covers.here CapMode.Le.refl
  -- `WT_write` requires the written value `y` to satisfy the cell's STORED relation `R` at each
  -- lower level, at the updated memory: `∀ i<k, R i (st2.trunc) m_upd (.var y)`.  With the
  -- **world-parametrized store** the cell agreement `himpl` is a BICONDITIONAL, so its BACKWARD
  -- direction (`himpl i _ _ _ |>.mpr`) reduces this to `val_denot env T i.val (st2.trunc) m_upd
  -- (.var y)` — exactly the `write_reestablishes` payoff the frozen model could not give.  With
  -- `y` native at `st2` this is now: drop the index through truncation (`val_denot_down_trunc`)
  -- then carry the memory `store → m_upd` (subsuming) by `val_denot_worldle_monotonic`.
  set m_upd := store.update_mcell (env.lookup_var x).1 (env.lookup_var y).1 .live
    ⟨b0, hlk_cell'⟩ (fun _ => hly) with hm_upd
  have hsub_upd : m_upd.subsumes store :=
    Memory.update_mcell_subsumes store (env.lookup_var x).1 (env.lookup_var y).1 .live
      ⟨b0, hlk_cell'⟩ (fun _ => hly)
  have hyR : ∀ (i : Fin k), R i (st2.trunc (Nat.le_of_lt i.isLt))
      m_upd (.var (.free (env.lookup_var y).1)) := by
    intro i
    refine (himpl i _ _ _).mpr ?_
    have hdown := val_denot_down_trunc (typed_env_is_downward_closed hts) T
      (Nat.le_of_lt i.isLt) (.var (.free (env.lookup_var y).1)) hval2
    exact val_denot_worldle_monotonic (typed_env_is_monotonic hts) T
      ⟨hsub_upd, fun _ _ h => h⟩ hdown
  obtain ⟨hwle_w, hmt_w⟩ := WT_write hlk_cell' (fun _ => hly) hstl2 hmt2 hyR
  -- result world `st2` at the same index `k` (the write's `.access ε` event has `readCount 0`).
  intro _hguard
  refine ⟨TraceOk.access hcov, ?_⟩
  rw [show st.trunc (Nat.sub_le k
      (Trace.readCount [TraceItem.access Mutability.epsilon (env.lookup_var x).1])) = st from
    WP.World.trunc_self _ st]
  exact ⟨st2, WorldLe.trans (WorldLe.trans hwle1 hwle2) hwle_w, hmt_w,
    by simp only [Ty.exi_val_denot, Ty.val_denot, resolve],
    pack_bound_of_ne_pack (fun _ _ _ h => nomatch h),
    witness_live_of_ne_pack (fun _ _ _ h => nomatch h)⟩

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
  intro env k st store hts
  specialize hsub1 env k st store hts
  specialize hsub2 env k st store hts
  apply CapabilitySet.Subset.trans hsub1 hsub2

theorem sem_sc_elem {C1 C2 : CaptureSet s}
  (hmem : C1 ⊆ C2) :
  SemSubcapt Γ C1 C2 := by
  intro env k st m hts
  unfold CaptureSet.denot
  induction hmem
  case empty =>
    simp only [List.empty_eq]
    exact CapabilitySet.Subset.empty
  case refl =>
    exact CapabilitySet.Subset.refl
  case union_left ih1 ih2 =>
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
  intro env k st m hts
  unfold CaptureSet.denot
  simp only [List.empty_eq]
  exact CapabilitySet.Subset.union_left (hsub1 env k st m hts) (hsub2 env k st m hts)

theorem sem_sc_var {x : BVar s .var} {T : Ty .capt s}
  (hlookup : Γ.LookupVar x T) :
  SemSubcapt Γ (.var (.M .epsilon) (.bound x)) T.captureSet := by
  intro env k st m' hts
  unfold CaptureSet.denot
  simp only [List.empty_eq]
  have h : reachability_of_loc m'.heap (env.lookup_var x).1 ⊆ T.captureSet.denot env m' := by
    simpa only [Ty.captureSet] using typed_env_lookup_var_reachability hts hlookup
  -- The `.M .epsilon` qualifier is the identity for `ground_denot`, so the budget
  -- is exactly `x`'s reachability.
  simpa [CaptureSet.ground_denot] using h

theorem sem_sc_cvar {c : BVar s .cvar} {C : CaptureSet s}
  (hlookup : Γ.LookupCVar c a (.bound C)) :
  SemSubcapt Γ (.cvar (.M .epsilon) c) C := by
  intro env k st m hts
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
  intro env k st m _hts
  unfold CaptureSet.denot
  simp only [CaptureSet.applyRO_subst]
  exact ground_denot_applyRO_subset

/-- applyRO is monotonic for subcapturing. -/
theorem sem_sc_ro_mono {C1 C2 : CaptureSet s}
  (hsub : SemSubcapt Γ C1 C2) :
  SemSubcapt Γ C1.applyRO C2.applyRO := by
  intro env k st m hts
  unfold CaptureSet.denot
  simp only [CaptureSet.applyRO_subst]
  exact ground_denot_applyRO_mono (hsub env k st m hts)

/-- `applyAccess .drop` is monotonic for subcapturing: the semantic image of the
    new `sc_drop_mono` rule. At the capability level `applyAccess .drop` is
    `to_drop`, which is monotone under `CapabilitySet.Subset`. -/
theorem sem_sc_drop_mono {C1 C2 : CaptureSet s}
  (hsub : SemSubcapt Γ C1 C2) :
  SemSubcapt Γ (C1.applyAccess .drop) (C2.applyAccess .drop) := by
  intro env k st m hts
  simp only [captureSet_denot_applyAccess_comm, CapabilitySet.applyAccess_drop]
  exact CapabilitySet.Subset.to_drop_mono (hsub env k st m hts)

theorem sem_sc_mode {C : CaptureSet s}
  (hm : m1 ≤ m2) :
  SemSubcapt Γ (C.applyMut m1) (C.applyMut m2) := by
  intro env k st m hts
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
    intro hm env k st mem hts
    cases hm
    simpa only [CaptureSet.denot, CaptureSet.subst, CaptureSet.ground_denot, List.empty_eq] using
      CapabilitySet.HasKind.ro_empty
  | union h1 h2 ih1 ih2 =>
    intro hm env k st mem hts
    cases hm
    simpa only [CaptureSet.denot, CaptureSet.subst, CaptureSet.ground_denot, List.empty_eq] using
      CapabilitySet.HasKind.ro_union (ih1 rfl env k st mem hts) (ih2 rfl env k st mem hts)
  | sc hsub hk ih =>
    intro hm env k st mem hts
    cases hm
    exact CapabilitySet.HasKind.subset_ro
      (fundamental_subcapt hsub env k st mem hts)
      (ih rfl env k st mem hts)
  | rw =>
    intro hm
    cases hm
  | imm hlock hhas =>
    intro hm env k st mem hts
    cases hm
    exact (typed_env_lookup_lock_satisfy hlock hts).kind _ _ hhas
  | ro =>
    rename_i C0
    intro hm env k st mem hts
    cases hm
    simpa [CaptureSet.denot, CaptureSet.applyRO_subst, ground_denot_applyRO_comm] using
      (CapabilitySet.HasKind.applyRO
        (C := ((C0.subst (Subst.from_TypeEnv env)).ground_denot mem)))

theorem fundamental_haskind
  (hkind : HasKind Γ C mode) :
  SemHasKind Γ C mode := by
  cases hmode : mode with
  | epsilon =>
    intro env k st mem hts
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

/-- `applyAccess` is monotone under `CapabilitySet.Subset`. -/
private theorem capabilitySet_applyAccess_mono {C1 C2 : CapabilitySet} {a : Access}
    (hsub : C1 ⊆ C2) : C1.applyAccess a ⊆ C2.applyAccess a := by
  cases a with
  | M m =>
    cases m with
    | epsilon => exact hsub
    | ro => exact CapabilitySet.applyRO_mono hsub
  | drop => exact CapabilitySet.Subset.to_drop_mono hsub

mutual

/-- Subset-level peak projection: a *closed* capture set's denotation is
contained in its computed peaks' denotation. This is the `Subset`-valued
strengthening of `hasmem_compute_peaks_denot`, used to interpret the
`sep_peaks`/`disj_peaks` rules. -/
private theorem denot_subset_compute_peaks_denot
    {s : Sig} {Γ : Ctx s} {env : TypeEnv s} {store : Memory}
    (hts : EnvTyping Γ env k st store) (hΓ : Γ.IsClosed)
    (C : CaptureSet s) (hC : C.IsClosed) :
    C.denot env store ⊆ (compute_peaks env C).denot env store := by
  match C, hC with
  | .empty, _ => exact CapabilitySet.Subset.refl
  | .union C1 C2, hC =>
    cases hC with | union hC1 hC2 =>
    have ih1 := denot_subset_compute_peaks_denot hts hΓ C1 hC1
    have ih2 := denot_subset_compute_peaks_denot hts hΓ C2 hC2
    change C1.denot env store ∪ C2.denot env store ⊆
      (compute_peaks env C1).denot env store ∪ (compute_peaks env C2).denot env store
    exact CapabilitySet.Subset.union_left
      (CapabilitySet.Subset.trans ih1 CapabilitySet.Subset.union_right_left)
      (CapabilitySet.Subset.trans ih2 CapabilitySet.Subset.union_right_right)
  | .cvar m c, _ => exact CapabilitySet.Subset.refl
  | .var m (.bound x), _ =>
    exact denot_subset_compute_peaks_denot_var_bound hts hΓ
  | .var m (.free n), hC =>
    cases hC
termination_by 2 * (sizeOf Γ + sizeOf C) + 1

private theorem denot_subset_compute_peaks_denot_var_bound
    {s : Sig} {Γ : Ctx s} {env : TypeEnv s} {store : Memory}
    (hts : EnvTyping Γ env k st store) (hΓ : Γ.IsClosed)
    {x : BVar s .var} {m : Access} :
    (CaptureSet.var m (.bound x)).denot env store ⊆
      (compute_peaks env (CaptureSet.var m (.bound x))).denot env store := by
  match s, Γ, env, hts, hΓ, x with
  | _, .empty, .empty, _, _, x => cases x
  | _, .push Γ_rest (.var T), .extend env_rest (.var n ps), hts, hΓ, .here =>
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
    change (reachability_of_loc store.heap n).applyAccess m ⊆
      ((compute_peaks (env_rest.extend_var n ps)
        (CaptureSet.var m (.bound BVar.here))).denot (env_rest.extend_var n ps) store)
    rw [hcp_eq, captureSet_denot_applyAccess_comm]
    apply capabilitySet_applyAccess_mono
    have hsub_peaks := denot_subset_compute_peaks_denot hts_rest hΓ_rest T.captureSet hT_cs
    rw [hcp_denot, hcp_rename] at hsub_peaks
    exact CapabilitySet.Subset.trans hreach_sub hsub_peaks
  | _, .push Γ_rest (.var T), .extend env_rest (.var n ps), hts, hΓ, .there x' =>
    obtain ⟨_, _, hts_rest⟩ := hts
    cases hΓ with | push hΓ_rest _ =>
    have hsub_rest := denot_subset_compute_peaks_denot_var_bound hts_rest hΓ_rest
      (x := x') (m := m)
    have hC := rebind_captureset_denot
      (ρ := @Rebind.weaken _ env_rest n ps)
      (CaptureSet.var m (.bound x'))
    have hcp_rename := rebind_compute_peaks
      (ρ := @Rebind.weaken _ env_rest n ps)
      (CaptureSet.var m (.bound x'))
    have hcp_denot := rebind_captureset_denot
      (ρ := @Rebind.weaken _ env_rest n ps)
      (compute_peaks env_rest (CaptureSet.var m (.bound x')))
    rw [hC, hcp_denot, hcp_rename] at hsub_rest
    exact hsub_rest
  | _, .push Γ_rest (.tvar S), .extend env_rest (.tvar d), hts, hΓ, .there x' =>
    obtain ⟨_, _, _, _, _, hts_rest⟩ := hts
    cases hΓ with | push hΓ_rest _ =>
    have hsub_rest := denot_subset_compute_peaks_denot_var_bound hts_rest hΓ_rest
      (x := x') (m := m)
    have hC := rebind_captureset_denot
      (ρ := @Rebind.tweaken _ env_rest d)
      (CaptureSet.var m (.bound x'))
    have hcp_rename := rebind_compute_peaks
      (ρ := @Rebind.tweaken _ env_rest d)
      (CaptureSet.var m (.bound x'))
    have hcp_denot := rebind_captureset_denot
      (ρ := @Rebind.tweaken _ env_rest d)
      (compute_peaks env_rest (CaptureSet.var m (.bound x')))
    rw [hC, hcp_denot, hcp_rename] at hsub_rest
    exact hsub_rest
  | _, .push Γ_rest (.cvar _ B), .extend env_rest (.cvar a0 cs cap), hts, hΓ, .there x' =>
    obtain ⟨_, _, _, _, _, _, hts_rest⟩ := hts
    cases hΓ with | push hΓ_rest _ =>
    have hsub_rest := denot_subset_compute_peaks_denot_var_bound hts_rest hΓ_rest
      (x := x') (m := m)
    have hC := rebind_captureset_denot
      (ρ := @Rebind.cweaken _ env_rest cs cap a0)
      (CaptureSet.var m (.bound x'))
    have hcp_rename := rebind_compute_peaks
      (ρ := @Rebind.cweaken _ env_rest cs cap a0)
      (CaptureSet.var m (.bound x'))
    have hcp_denot := rebind_captureset_denot
      (ρ := @Rebind.cweaken _ env_rest cs cap a0)
      (compute_peaks env_rest (CaptureSet.var m (.bound x')))
    rw [hC, hcp_denot, hcp_rename] at hsub_rest
    exact hsub_rest
  | _, .push Γ_rest (.lock Ψ), .extend env_rest (.lock), hts, hΓ, .there x' =>
    obtain ⟨_, hts_rest⟩ := hts
    cases hΓ with | push hΓ_rest _ =>
    have hsub_rest := denot_subset_compute_peaks_denot_var_bound hts_rest hΓ_rest
      (x := x') (m := m)
    have hC := rebind_captureset_denot
      (ρ := @Rebind.lweaken _ env_rest)
      (CaptureSet.var m (.bound x'))
    have hcp_rename := rebind_compute_peaks
      (ρ := @Rebind.lweaken _ env_rest)
      (CaptureSet.var m (.bound x'))
    have hcp_denot := rebind_captureset_denot
      (ρ := @Rebind.lweaken _ env_rest)
      (compute_peaks env_rest (CaptureSet.var m (.bound x')))
    rw [hC, hcp_denot, hcp_rename] at hsub_rest
    exact hsub_rest
termination_by 2 * (sizeOf Γ + sizeOf (CaptureSet.var m (.bound x)))
decreasing_by
  all_goals simp_wf
  all_goals try omega
  all_goals (have := sizeOf_captureSet_le T; omega)

end

/-! ### `DropSepIn` transport helpers for the separation interpretations -/

private theorem cvar_subset_cp_union_inv {env : TypeEnv s} {a : Access}
    {c : BVar s .cvar} {A B : CaptureSet s}
    (h : (CaptureSet.cvar a c) ⊆ compute_peaks env (A ∪ B)) :
    (CaptureSet.cvar a c) ⊆ compute_peaks env A ∨
      (CaptureSet.cvar a c) ⊆ compute_peaks env B :=
  CaptureSet.cvar_subset_union_inv h

private theorem cvar_subset_cp_union_l {env : TypeEnv s} {a : Access}
    {c : BVar s .cvar} {A B : CaptureSet s}
    (h : (CaptureSet.cvar a c) ⊆ compute_peaks env A) :
    (CaptureSet.cvar a c) ⊆ compute_peaks env (A ∪ B) :=
  CaptureSet.Subset.union_right_left h

private theorem cvar_subset_cp_union_r {env : TypeEnv s} {a : Access}
    {c : BVar s .cvar} {A B : CaptureSet s}
    (h : (CaptureSet.cvar a c) ⊆ compute_peaks env B) :
    (CaptureSet.cvar a c) ⊆ compute_peaks env (A ∪ B) :=
  CaptureSet.Subset.union_right_right h

/-- Commutativity of the budget union for `DropSepIn`. -/
theorem sem_sepcheck_symm
  (ih : SemSepCheck Γ C1 C2) :
  SemSepCheck Γ C2 C1 := by
  intro hΓ env k st H hts hdsep
  exact CapabilitySet.Noninterference.ni_symm (ih hΓ env k st H hts hdsep)

theorem sem_sepcheck_union
  (ih1 : SemSepCheck Γ C1 C3)
  (ih2 : SemSepCheck Γ C2 C3) :
  SemSepCheck Γ (C1 ∪ C2) C3 := by
  intro hΓ env k st H hts hdsep
  simp only [CaptureSet.denot, CaptureSet.subst, CaptureSet.ground_denot]
  exact CapabilitySet.Noninterference.ni_union
    (ih1 hΓ env k st H hts hdsep) (ih2 hΓ env k st H hts hdsep)

/-- Two read-only *drop-free* capability sets do not interfere: any shared
location is held read-only on both sides. The drop-freedom hypotheses rule
out the `ro_drop` kinding alternative. -/
theorem CapabilitySet.noninterference_of_ro_ro
  (hk1 : CapabilitySet.HasKind C1 .ro)
  (hk2 : CapabilitySet.HasKind C2 .ro)
  (hdf1 : C1.drop_free)
  (hdf2 : C2.drop_free) :
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
        | ro_drop => exact absurd CapabilitySet.hasmem.here (hdf2 _)
      | union C2a C2b ih2a ih2b =>
        cases hk2 with
        | ro_union hk2a hk2b =>
          have hdf2a : C2a.drop_free := fun l h => hdf2 l (.left h)
          have hdf2b : C2b.drop_free := fun l h => hdf2 l (.right h)
          exact .ni_symm (.ni_union (.ni_symm (ih2a hk2a hdf2a)) (.ni_symm (ih2b hk2b hdf2b)))
    | ro_drop => exact absurd CapabilitySet.hasmem.here (hdf1 _)
  | union C1a C1b ih1a ih1b =>
    cases hk1 with
    | ro_union hk1a hk1b =>
      have hdf1a : C1a.drop_free := fun l h => hdf1 l (.left h)
      have hdf1b : C1b.drop_free := fun l h => hdf1 l (.right h)
      exact .ni_union (ih1a hk1a hdf1a) (ih1b hk1b hdf1b)

theorem sem_sepcheck_empty :
  SemSepCheck Γ {} C := by
  intro _hΓ env k st H hts _hdsep
  simp only [CaptureSet.denot, CaptureSet.subst, CaptureSet.ground_denot]
  exact .ni_empty

/-- An access-only (no `.drop` peak) *closed* capture set denotes a drop-free
capability set: any runtime `.drop` member would trace (via `drop_denot_peak`)
to a `.drop`-access peak, contradicting `AccessOnly`. Closedness is essential:
a free location referenced at `.drop` access has no peaks at all, so
`AccessOnly` would be vacuous about it. -/
theorem accessonly_denot_drop_free
    {Γ : Ctx s} {env : TypeEnv s} {store : Memory} {C : CaptureSet s}
    (hts : EnvTyping Γ env k st store) (hΓ : Γ.IsClosed) (hC : C.IsClosed)
    (hao : C.AccessOnly Γ) :
    (C.denot env store).drop_free := by
  intro l hmem
  obtain ⟨c, hsub, _⟩ :=
    drop_denot_peak hts hΓ (envtyping_lookup_cvar_drop_free hts) hC hmem
  exact hao c hsub

theorem sem_sepcheck_ro
  (hcl1 : C1.IsClosed) (hcl2 : C2.IsClosed)
  (hao1 : C1.AccessOnly Γ) (hao2 : C2.AccessOnly Γ)
  (hk1 : HasKind Γ C1 .ro)
  (hk2 : HasKind Γ C2 .ro) :
  SemSepCheck Γ C1 C2 := by
  intro hΓ env k st H hts _hdsep
  exact CapabilitySet.noninterference_of_ro_ro
    (fundamental_haskind hk1 env k st H hts) (fundamental_haskind hk2 env k st H hts)
    (accessonly_denot_drop_free hts hΓ hcl1 hao1)
    (accessonly_denot_drop_free hts hΓ hcl2 hao2)

/-- Semantic content of `sep_droppable`: two *distinct* droppable capture
variables denote disjoint capability sets — exactly the `EnvSepWf`
environment invariant — and disjointness entails `Noninterference` at any
access modes. -/
theorem sem_sepcheck_droppable {c1 c2 : BVar s .cvar} {m1 m2 : Access}
  (hdistinct : Γ.TwoDistinctDroppable c1 c2) :
  SemSepCheck Γ (.cvar m1 c1) (.cvar m2 c2) := by
  intro _hΓ env k st H hts hdsep
  obtain ⟨ha1, ha2, hne⟩ := hdistinct
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
  have ha1' : env.lookup_cvar_auth c1 = .can_drop := by
    rw [envtyping_lookup_cvar_auth hts c1]; exact ha1
  have ha2' : env.lookup_cvar_auth c2 = .can_drop := by
    rw [envtyping_lookup_cvar_auth hts c2]; exact ha2
  exact hdsep c1 c2 hne ha1' ha2' mu1' mu2' l h1' h2'

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
  | sep_ro hcl1 hcl2 hao1 hao2 hk1 hk2 =>
    exact sem_sepcheck_ro hcl1 hcl2 hao1 hao2 hk1 hk2
  | sep_sc _ hsub _hequiv ih =>
    -- The environment-separation invariant is budget-independent, so the budget
    -- move needs no transport.
    intro hΓ env k st H hts hdsep
    exact CapabilitySet.Noninterference.subset_left
      (ih hΓ env k st H hts hdsep) (fundamental_subcapt hsub env k st H hts)
  | sep_lock hlock hdistinct =>
    intro _hΓ env k st H henv _hdsep
    exact (typed_env_lookup_lock_satisfy hlock henv).sep _ _ hdistinct
  | sep_droppable hdistinct =>
    exact sem_sepcheck_droppable hdistinct

/-- Interpretation of lock-stored separation facts in *arbitrary* well-typed
environments carrying the `EnvSepWf` invariant. The `sep_droppable` case is the
reason `EnvSepWf` is threaded: two distinct droppable capture variables denote
disjoint capabilities exactly by that invariant. The invariant reaches the
`modal_modal` consumption point because `SemSubtyp` carries it — the `exi`
subtyping rule re-tags its fresh binder `.access_only`, which preserves `EnvSepWf`. -/
theorem fundamental_sepcheck_global
  (hsep : SepCheck Γ C1 C2) (hΓ : Γ.IsClosed) :
  ∀ env k st H,
    EnvTyping Γ env k st H ->
    env.EnvSepWf ->
    CapabilitySet.Noninterference (C1.denot env H) (C2.denot env H) := by
  induction hsep with
  | sep_symm _ ih =>
    intro env k st H hts hdsep
    exact CapabilitySet.Noninterference.ni_symm (ih env k st H hts hdsep)
  | sep_union _ _ ih1 ih2 =>
    intro env k st H hts hdsep
    simp only [CaptureSet.denot, CaptureSet.subst, CaptureSet.ground_denot]
    exact CapabilitySet.Noninterference.ni_union (ih1 env k st H hts hdsep)
      (ih2 env k st H hts hdsep)
  | sep_empty =>
    intro env k st H hts _hdsep
    simp only [CaptureSet.denot, CaptureSet.subst, CaptureSet.ground_denot]
    exact .ni_empty
  | sep_ro hcl1 hcl2 hao1 hao2 hk1 hk2 =>
    intro env k st H hts _hdsep
    exact CapabilitySet.noninterference_of_ro_ro
      (fundamental_haskind hk1 env k st H hts) (fundamental_haskind hk2 env k st H hts)
      (accessonly_denot_drop_free hts hΓ hcl1 hao1)
      (accessonly_denot_drop_free hts hΓ hcl2 hao2)
  | sep_sc _ hsub _ ih =>
    intro env k st H hts hdsep
    exact CapabilitySet.Noninterference.subset_left (ih env k st H hts hdsep)
      (fundamental_subcapt hsub env k st H hts)
  | sep_lock hlock hdistinct =>
    intro env k st H henv _hdsep
    exact (typed_env_lookup_lock_satisfy hlock henv).sep _ _ hdistinct
  | sep_droppable hdistinct =>
    -- Two distinct droppable capture variables denote disjoint capabilities by
    -- the `EnvSepWf` invariant (as in `sem_sepcheck_droppable`).
    intro env k st H hts hdsep
    exact sem_sepcheck_droppable hdistinct hΓ env k st H hts hdsep

/-- Disjoint core of `disj_droppable`: two *distinct* droppable capture variables
denote fully `disjoint` capability sets — exactly the `EnvSepWf` invariant.  This
is the strengthening of `sem_sepcheck_droppable` that `DisjCheck` (which drops the
`sep_ro`/`sep_lock` noninterference-only escape hatches) makes available. -/
theorem sem_disjcheck_droppable {c1 c2 : BVar s .cvar} {m1 m2 : Access}
  (hdistinct : Γ.TwoDistinctDroppable c1 c2) :
  ∀ env k st H, EnvTyping Γ env k st H → env.EnvSepWf →
    CapabilitySet.disjoint ((CaptureSet.cvar m1 c1).denot env H)
      ((CaptureSet.cvar m2 c2).denot env H) := by
  intro env k st H hts hdsep
  obtain ⟨ha1, ha2, hne⟩ := hdistinct
  have hdenot1 :
      (CaptureSet.cvar m1 c1).denot env H = ((env.lookup_cvar c1).2).applyAccess m1 := by
    change ((env.lookup_cvar c1).1.applyAccess m1).ground_denot H = _
    rw [captureSet_ground_denot_applyAccess_comm, ← typed_env_cvar_cap_eq hts c1]
  have hdenot2 :
      (CaptureSet.cvar m2 c2).denot env H = ((env.lookup_cvar c2).2).applyAccess m2 := by
    change ((env.lookup_cvar c2).1.applyAccess m2).ground_denot H = _
    rw [captureSet_ground_denot_applyAccess_comm, ← typed_env_cvar_cap_eq hts c2]
  rw [hdenot1, hdenot2]
  intro mu1 mu2 l h1 h2
  obtain ⟨mu1', h1'⟩ := hasmem_of_applyAccess h1
  obtain ⟨mu2', h2'⟩ := hasmem_of_applyAccess h2
  have ha1' : env.lookup_cvar_auth c1 = .can_drop := by
    rw [envtyping_lookup_cvar_auth hts c1]; exact ha1
  have ha2' : env.lookup_cvar_auth c2 = .can_drop := by
    rw [envtyping_lookup_cvar_auth hts c2]; exact ha2
  exact hdsep c1 c2 hne ha1' ha2' mu1' mu2' l h1' h2'

/-- **Soundness of `DisjCheck`**: a syntactic disjointness check denotes genuine
location-level `CapabilitySet.disjoint`.  Unlike `SepCheck`/`fundamental_sepcheck`
(which yield only `Noninterference` because of the `sep_ro`/`sep_lock` cases),
`DisjCheck` has no read-only or lock escape hatch, so every constructor genuinely
gives disjointness.  This is what makes the `n`-ary `pack` rule sound: the unpack
continuation binds all evidences as simultaneous `.can_drop` capture variables,
whose `EnvSepWf` invariant demands mutual `disjoint`ness. -/
theorem fundamental_disjcheck_global
  (hdisj : DisjCheck Γ C1 C2) :
  ∀ env k st H,
    EnvTyping Γ env k st H ->
    env.EnvSepWf ->
    CapabilitySet.disjoint (C1.denot env H) (C2.denot env H) := by
  induction hdisj with
  | disj_symm _ ih =>
    intro env k st H hts hdsep
    exact (ih env k st H hts hdsep).symm
  | disj_union _ _ ih1 ih2 =>
    intro env k st H hts hdsep
    simp only [CaptureSet.denot, CaptureSet.subst, CaptureSet.ground_denot]
    intro mu1 mu2 l h1 h2
    cases h1 with
    | left h1' => exact ih1 env k st H hts hdsep mu1 mu2 l h1' h2
    | right h1' => exact ih2 env k st H hts hdsep mu1 mu2 l h1' h2
  | disj_empty =>
    intro env k st H hts _hdsep
    simp only [CaptureSet.denot, CaptureSet.subst, CaptureSet.ground_denot]
    intro mu1 mu2 l h1 h2
    exact CapabilitySet.not_hasmem_empty h1
  | disj_sc _ hsub _ ih =>
    intro env k st H hts hdsep
    exact CapabilitySet.disjoint.subset_left
      (fundamental_subcapt hsub env k st H hts) (ih env k st H hts hdsep)
  | disj_droppable hdistinct =>
    intro env k st H hts hdsep
    exact sem_disjcheck_droppable hdistinct env k st H hts hdsep

/-- **Bridge from the syntactic to the semantic pairwise-separation premise of the
`pack` rule.**  `CaptureSet.PairwiseSep Γ Cs` (pairwise `DisjCheck`) implies, at
every well-typed `EnvSepWf` world, that the evidences denote pairwise
`CapabilitySet.disjoint` capability sets — the invariant `exi_val_denot` records
and `unpack`'s continuation consumes. -/
theorem CaptureSet.PairwiseSep.sem {s : Sig} {Γ : Ctx s} {n : Nat}
    {Cs : List.Vector (CaptureSet s) n}
    (h : CaptureSet.PairwiseSep Γ Cs) : SemPairwiseSep Γ Cs := by
  intro k env st m hts hdsep
  exact List.Pairwise.imp
    (fun {a b} hab => fundamental_disjcheck_global hab env k st m hts hdsep) h

/-- `Satisfy` interpretation in arbitrary well-typed environments carrying the
`EnvSepWf` invariant. Used only by `modal_modal`. -/
theorem sem_satisfy_global
  (hclosed_Ψ : Ψ.IsClosed)
  (hΓ : Γ.IsClosed)
  (hsatisfy : Satisfy Γ Ψ) :
  ∀ env k st m,
    EnvTyping Γ env k st m ->
    env.EnvSepWf ->
    env.Satisfy Ψ m := by
  intro env k st m henv hdsep
  cases hsatisfy with
  | satisfy hkind hsep =>
    constructor
    · intro C hhas
      exact CaptureSet.wf_subst (SepCtx.WfInHeap.of_has (SepCtx.wf_of_closed hclosed_Ψ.sep) hhas)
                                (from_TypeEnv_wf_in_heap henv)
    · intro C mode hhas
      exact CaptureSet.wf_subst
        (MutabilityCtx.WfInHeap.of_has (MutabilityCtx.wf_of_closed hclosed_Ψ.mutability) hhas)
        (from_TypeEnv_wf_in_heap henv)
    · intro C mode hhas
      exact fundamental_haskind (hkind C mode hhas) env k st m henv
    · intro C1 C2 hdistinct
      exact fundamental_sepcheck_global (hsep C1 C2 hdistinct) hΓ env k st m henv hdsep

theorem sem_satisfy
  (hclosed_Ψ : Ψ.IsClosed)
  (hΓ : Γ.IsClosed)
  (hsatisfy : Satisfy Γ Ψ) :
  ∀ env k st m,
    EnvTyping Γ env k st m ->
    env.EnvSepWf ->
    env.Satisfy Ψ m := by
  intro env k st m henv hdsep
  cases hsatisfy with
  | satisfy hkind hsep =>
    constructor
    · intro C hhas
      exact CaptureSet.wf_subst (SepCtx.WfInHeap.of_has (SepCtx.wf_of_closed hclosed_Ψ.sep) hhas)
                                (from_TypeEnv_wf_in_heap henv)
    · intro C mode hhas
      exact CaptureSet.wf_subst
        (MutabilityCtx.WfInHeap.of_has (MutabilityCtx.wf_of_closed hclosed_Ψ.mutability) hhas)
        (from_TypeEnv_wf_in_heap henv)
    · intro C mode hhas
      exact fundamental_haskind (hkind C mode hhas) env k st m henv
    · intro C1 C2 hdistinct
      exact fundamental_sepcheck (hsep C1 C2 hdistinct) hΓ env k st m henv hdsep

theorem sem_typ_par
  {C1 C2 : CaptureSet s} {Γ : Ctx s}
  {e1 e2 : Exp s} {E1 E2 : Ty .exi s}
  (hΓ : Γ.IsClosed)
  (_hclosed_C1 : C1.IsClosed)
  (_hclosed_C2 : C2.IsClosed)
  (_hclosed_e1 : e1.IsClosed)
  (_hclosed_e2 : e2.IsClosed)
  (ht1 : SemanticTyping C1 Γ e1 E1)
  (ht2 : SemanticTyping C2 Γ e2 E2)
  (hsep : SemSepCheck Γ C1 C2) :
  SemanticTyping (C1 ∪ C2) Γ (.par C1 C2 e1 e2) (.typ .unit) := by
  intro env k st store hts hdsep hcompat
  simp only [Ty.exi_exp_denot, Exp.subst, List.empty_eq]
  intro hmt
  suffices hpar :
      Eval k store
        (.par (C1.subst (Subst.from_TypeEnv env)) (C2.subst (Subst.from_TypeEnv env))
          (e1.subst (Subst.from_TypeEnv env)) (e2.subst (Subst.from_TypeEnv env)))
        (fun t v m' => t.readCount < k →
          TraceOk t (CaptureSet.denot env (C1 ∪ C2) store) ∧
          ∃ (st' : StoreTyping (k - t.readCount)),
            WorldLe st' m' (st.trunc (Nat.sub_le k t.readCount)) store ∧
            MemTyped (k - t.readCount) st' m' ∧
            Ty.exi_val_denot env (.typ .unit) (k - t.readCount) st' m' v ∧
            pack_bound (CaptureSet.denot env (C1 ∪ C2) store) store v m' ∧
            witness_live v m')by
    simpa only [Ty.exi_exp_denot, Exp.subst, List.empty_eq] using hpar
  have hunion : (C1 ∪ C2).denot env store = C1.denot env store ∪ C2.denot env store := rfl
  have hcompat' := hunion ▸ hcompat
  have hsubC1 : C1.denot env store ⊆ (C1 ∪ C2).denot env store :=
    CapabilitySet.Subset.union_right_left
  have hsubC2 : C2.denot env store ⊆ (C1 ∪ C2).denot env store :=
    CapabilitySet.Subset.union_right_right
  -- Separation: the two branches' footprints are non-interfering.
  have hni : CapabilitySet.Noninterference (C1.denot env store) (C2.denot env store) :=
    hsep hΓ env k st store hts hdsep
  have hpresent_C2 : ∀ mu l, (C2.denot env store).hasmem mu l → store.heap l ≠ none := by
    intro mu l hmem
    simp only [CaptureSet.denot, CaptureSet.ground_denot_eq_reachability] at hmem
    exact CaptureSet.reachability_dom hmem
  have he1 : Eval k store (e1.subst (Subst.from_TypeEnv env))
      (fun t v m' => t.readCount < k →
        TraceOk t (C1.denot env store) ∧
        ∃ (st' : StoreTyping (k - t.readCount)),
          WorldLe st' m' (st.trunc (Nat.sub_le k t.readCount)) store ∧
          MemTyped (k - t.readCount) st' m' ∧
          Ty.exi_val_denot env E1 (k - t.readCount) st' m' v ∧
        pack_bound (C1.denot env store) store v m' ∧ witness_live v m') := by
    have h := ht1 env k st store hts hdsep (Memory.is_compatible_union_left hcompat')
    simp only [Ty.exi_exp_denot] at h
    exact h hmt
  -- `e2`'s soundness run from `store`, used only to bound its trace by `C2` when
  -- discharging the separation premise of `eval_par`.
  have he2_store : Eval k store (e2.subst (Subst.from_TypeEnv env))
      (fun t v m' => t.readCount < k →
        TraceOk t (C2.denot env store) ∧
        ∃ (st' : StoreTyping (k - t.readCount)),
          WorldLe st' m' (st.trunc (Nat.sub_le k t.readCount)) store ∧
          MemTyped (k - t.readCount) st' m' ∧
          Ty.exi_val_denot env E2 (k - t.readCount) st' m' v ∧
        pack_bound (C2.denot env store) store v m' ∧ witness_live v m') := by
    have h := ht2 env k st store hts hdsep (Memory.is_compatible_union_right hcompat')
    simp only [Ty.exi_exp_denot] at h
    exact h hmt
  -- Bridge the denotational budgets to the operational reachability budgets that
  -- `eval_par` expects (they are pointwise equal on ground capture sets).
  have hrC1 : C1.denot env store = (C1.subst (Subst.from_TypeEnv env)).reachability store :=
    CaptureSet.ground_denot_eq_reachability _ _
  have hrC2 : C2.denot env store = (C2.subst (Subst.from_TypeEnv env)).reachability store :=
    CaptureSet.ground_denot_eq_reachability _ _
  -- **The rely** (Phase 6): a well-typed future world of `(st, store)` at budget `j`.
  -- Every separation field of `Safe.par` is discharged by re-running the branch's
  -- SEMANTIC typing at that world — never by operational replay from an arbitrary
  -- subsuming memory (`simulate_down`/`memTyped_subsumes` are gone).
  -- Shared engine: a branch's `Eval` at any rely-world with a compatible budget.
  have hbranch1 : ∀ (j : Nat) (st' : StoreTyping j) (m' : Memory) (hjk : j ≤ k),
      WorldLe st' m' (st.trunc hjk) store → MemTyped j st' m' →
      m'.is_compatible ((C1.subst (Subst.from_TypeEnv env)).reachability store) →
      Eval j m' (e1.subst (Subst.from_TypeEnv env))
        (fun t v m'' => t.readCount < j →
          TraceOk t (C1.denot env m') ∧
          ∃ (st'' : StoreTyping (j - t.readCount)),
            WorldLe st'' m'' (st'.trunc (Nat.sub_le j t.readCount)) m' ∧
            MemTyped (j - t.readCount) st'' m'' ∧
            Ty.exi_val_denot env E1 (j - t.readCount) st'' m'' v ∧
            pack_bound (C1.denot env m') m' v m'' ∧ witness_live v m'') := by
    intro j st' m' hjk hwle' hmt' hcompat1'
    have hts' : EnvTyping Γ env j st' m' := env_typing_worldle_trunc hjk hts hwle'
    have hC1_eq : C1.denot env store = C1.denot env m' :=
      closed_capture_denot_monotonic _hclosed_C1 hts hwle'.1
    have h := ht1 env j st' m' hts' hdsep (by rw [← hC1_eq, hrC1]; exact hcompat1')
    simp only [Ty.exi_exp_denot] at h
    exact h hmt'
  have hbranch2 : ∀ (j : Nat) (st' : StoreTyping j) (m' : Memory) (hjk : j ≤ k),
      WorldLe st' m' (st.trunc hjk) store → MemTyped j st' m' →
      m'.is_compatible ((C2.subst (Subst.from_TypeEnv env)).reachability store) →
      Eval j m' (e2.subst (Subst.from_TypeEnv env))
        (fun t v m'' => t.readCount < j →
          TraceOk t (C2.denot env m') ∧
          ∃ (st'' : StoreTyping (j - t.readCount)),
            WorldLe st'' m'' (st'.trunc (Nat.sub_le j t.readCount)) m' ∧
            MemTyped (j - t.readCount) st'' m'' ∧
            Ty.exi_val_denot env E2 (j - t.readCount) st'' m'' v ∧
            pack_bound (C2.denot env m') m' v m'' ∧ witness_live v m'') := by
    intro j st' m' hjk hwle' hmt' hcompat2'
    have hts' : EnvTyping Γ env j st' m' := env_typing_worldle_trunc hjk hts hwle'
    have hC2_eq : C2.denot env store = C2.denot env m' :=
      closed_capture_denot_monotonic _hclosed_C2 hts hwle'.1
    have h := ht2 env j st' m' hts' hdsep (by rw [← hC2_eq, hrC2]; exact hcompat2')
    simp only [Ty.exi_exp_denot] at h
    exact h hmt'
  have hni' : CapabilitySet.Noninterference
      ((C1.subst (Subst.from_TypeEnv env)).reachability store)
      ((C2.subst (Subst.from_TypeEnv env)).reachability store) := by
    rw [← hrC1, ← hrC2]; exact hni
  refine Eval.eval_par
    (W := fun j m' => ∃ (hjk : j ≤ k) (st' : StoreTyping j),
      WorldLe st' m' (st.trunc hjk) store ∧ MemTyped j st' m')
    ⟨Nat.le_refl k, st, WorldLe.refl_trunc_self _ st store, hmt⟩
    ?hWdown ?hWpres1 ?hWpres2 he1 he2_store.1 ?hb1 ?hb2 ?hrs1 ?hrs2 hni'
    (fun t v m' hover hguard => absurd hguard (Nat.not_lt.mpr hover)) ?hcont
  case hWdown =>
    intro j j' m' hj' hW'
    obtain ⟨hjk, st', hwle', hmt'⟩ := hW'
    refine ⟨Nat.le_trans hj' hjk, st'.trunc hj', ?_, MemTyped_trunc hj' hmt'⟩
    have h := WP.WorldLe.trunc hj' hwle'
    rwa [WP.World.trunc_trunc] at h
  case hWpres1 =>
    intro j m' t v m'' hW' hcompat1' hbs hbud
    obtain ⟨hjk, st', hwle', hmt'⟩ := hW'
    obtain ⟨_, st'', hwle'', hmt'', _, _, _⟩ :=
      (hbranch1 j st' m' hjk hwle' hmt' hcompat1').2 t v m'' hbs hbud
    refine ⟨Nat.le_trans (Nat.sub_le j t.readCount) hjk, st'', ?_, hmt''⟩
    have hdesc := WP.WorldLe.trunc (Nat.sub_le j t.readCount) hwle'
    rw [WP.World.trunc_trunc] at hdesc
    exact WorldLe.trans hdesc hwle''
  case hWpres2 =>
    intro j m' t v m'' hW' hcompat2' hbs hbud
    obtain ⟨hjk, st', hwle', hmt'⟩ := hW'
    obtain ⟨_, st'', hwle'', hmt'', _, _, _⟩ :=
      (hbranch2 j st' m' hjk hwle' hmt' hcompat2').2 t v m'' hbs hbud
    refine ⟨Nat.le_trans (Nat.sub_le j t.readCount) hjk, st'', ?_, hmt''⟩
    have hdesc := WP.WorldLe.trunc (Nat.sub_le j t.readCount) hwle'
    rw [WP.World.trunc_trunc] at hdesc
    exact WorldLe.trans hdesc hwle''
  case hb1 =>
    intro j m' t v m'' hW' hcompat1' hbs hbud
    obtain ⟨hjk, st', hwle', hmt'⟩ := hW'
    obtain ⟨hok, _⟩ := (hbranch1 j st' m' hjk hwle' hmt' hcompat1').2 t v m'' hbs hbud
    have hC1_eq : C1.denot env store = C1.denot env m' :=
      closed_capture_denot_monotonic _hclosed_C1 hts hwle'.1
    have hok' : TraceOk t (C1.denot env store) := hC1_eq.symm ▸ hok
    exact hrC1 ▸ hok'
  case hb2 =>
    intro j m' t v m'' hW' hcompat2' hbs hbud
    obtain ⟨hjk, st', hwle', hmt'⟩ := hW'
    obtain ⟨hok, _⟩ := (hbranch2 j st' m' hjk hwle' hmt' hcompat2').2 t v m'' hbs hbud
    have hC2_eq : C2.denot env store = C2.denot env m' :=
      closed_capture_denot_monotonic _hclosed_C2 hts hwle'.1
    have hok' : TraceOk t (C2.denot env store) := hC2_eq.symm ▸ hok
    exact hrC2 ▸ hok'
  case hrs1 =>
    intro j m' hW' hcompat1'
    obtain ⟨hjk, st', hwle', hmt'⟩ := hW'
    exact (hbranch1 j st' m' hjk hwle' hmt' hcompat1').1
  case hrs2 =>
    intro j m' hW' hcompat2'
    obtain ⟨hjk, st', hwle', hmt'⟩ := hW'
    exact (hbranch2 j st' m' hjk hwle' hmt' hcompat2').1
  -- Given `e1`'s answer at `m1` (WITHIN budget — overflow is internalized by
  -- `eval_par`), run `e2` from `m1` at the residual budget `k − t1.readCount`.
  -- `par` returns `.unit`, so the only separation content needed is framing `C2`'s
  -- compatibility across `e1`'s run (`t1`) so that `e2` may start from `m1` — the
  -- left/right branch values are discarded, so no value framing is required.
  intro t1 v1 m1 hbud1 hsub_m1 hframe hQ1
  obtain ⟨hok1, st1, hwle1, hmt1, _, _, _⟩ := hQ1 hbud1
  -- (A) Frame `C2`'s compatibility across `e1`'s run (`t1` never drops a `C2`-cell,
  -- by non-interference) so that `e2` may run from `m1`.
  have hnodrop_C2_t1 : ∀ mu l, (C2.denot env store).hasmem mu l → ¬ Trace.extDrops t1 l := by
    intro mu l hmem hd
    obtain ⟨m', hm', hle⟩ :=
      CapabilitySet.covers_imp_exists_hasmem (TraceOk.drop_covers_of_extDrops hok1 hd)
    cases hle
    obtain ⟨hc, _⟩ := hni.shared_ro hm' hmem
    simp at hc
  have hcompat_m1_C2 : m1.is_compatible (C2.denot env store) :=
    Memory.is_compatible_frame (Memory.is_compatible_union_right hcompat')
      hpresent_C2 hframe hsub_m1 hnodrop_C2_t1
  -- `C2`'s denotation is stable under the memory growth (it is closed).
  have hC2_eq : C2.denot env store = C2.denot env m1 :=
    closed_capture_denot_monotonic _hclosed_C2 hts hsub_m1
  -- `e2`'s soundness at `C2`, run from `m1` at the RESIDUAL budget `k − t1.readCount`,
  -- at `e1`'s POST-WORLD `st1` (delivered by `e1`'s budget-guarded postcondition) — the
  -- `letin`-style composition; no operational transport of well-typedness is needed.
  have he2 := by
    have h := ht2 env (k - t1.readCount) st1 m1
      (env_typing_worldle_trunc (Nat.sub_le k t1.readCount) hts hwle1)
      hdsep (hC2_eq ▸ hcompat_m1_C2)
    simp only [Ty.exi_exp_denot] at h
    exact h hmt1
  -- Certify `Q` for the `.unit` result at the joined memory `m2` — only WITHIN the
  -- composite budget (`(t1 ++ t2).readCount < k`).  The trace is `t1 ++ t2`
  -- (union-lifted from both branches); the value is unit, so its
  -- `exi_val_denot`/`pack_bound`/`witness_live` are immediate.  The result index bridges
  -- by `readCount_append` + `Nat.sub_sub`: `(k − μt1) − μt2 = k − μ(t1++t2)`.
  refine ⟨he2.1, ?_⟩
  intro t2 v2 m2 hbs2 hguard
  have hbud2 : t2.readCount < k - t1.readCount := by
    rw [Trace.readCount_append] at hguard; omega
  obtain ⟨hok2, st', hwle', hmt', _hval', _, _⟩ := he2.2 t2 v2 m2 hbs2 hbud2
  have hok2' : TraceOk t2 (C2.denot env store) := hC2_eq.symm ▸ hok2
  have hjk : k - (t1 ++ t2).readCount ≤ k - t1.readCount - t2.readCount :=
    Nat.le_of_eq (by rw [Trace.readCount_append, Nat.sub_sub])
  refine ⟨TraceOk.append (TraceOk.mono hsubC1 hok1) (TraceOk.mono hsubC2 hok2'),
    st'.trunc hjk, ?_, MemTyped_trunc hjk hmt',
    by simp only [Ty.exi_val_denot, Ty.val_denot, resolve],
    pack_bound_of_ne_pack (fun _ _ _ h => nomatch h),
    witness_live_of_ne_pack (fun _ _ _ h => nomatch h)⟩
  -- Compose `e1`'s world-step (`hwle1`, descended to the `e2` level) with `e2`'s
  -- (`hwle'`), then descend once more to the compound level — the `letin_cont` pattern.
  have h2le : k - t1.readCount - t2.readCount ≤ k - t1.readCount := Nat.sub_le _ _
  have hwle1_desc := WP.WorldLe.trunc h2le hwle1
  rw [WP.World.trunc_trunc] at hwle1_desc
  have hwle_comp := WorldLe.trans hwle1_desc hwle'
  have hwle_fin := WP.WorldLe.trunc hjk hwle_comp
  rw [WP.World.trunc_trunc] at hwle_fin
  exact hwle_fin

/-- Bridge: the syntactic sequential-composition relation `SeqComp Γ C1 C2`
transfers, under a well-typed environment satisfying the (budget-relativized)
droppable-separation invariant, to the runtime capability level: no location
consumed (`.drop`) by `C1`'s denotation is touched at any mode by `C2`'s
denotation.

Per constructor:
- `seq_union`: split the union membership, restricting the invariant.
- `seq_access_only`: the (closed) access-only budget is drop-free, so there is
  no `.drop` member to begin with.
- `seq_sep`: `SepCheck` denotes to `Noninterference`, whose only shared-location
  case is read-only sharing; hence a `.drop` on the left never meets the right. -/
theorem captureSet_seqcomp_denot
    {C1 C2 : CaptureSet s} {Γ : Ctx s} {env : TypeEnv s} {store : Memory}
    (hts : EnvTyping Γ env k st store)
    (hΓ : Γ.IsClosed)
    (hdsep : env.EnvSepWf)
    (hseq : SeqComp Γ C1 C2) :
    (C1.denot env store).SeqComp (C2.denot env store) := by
  induction hseq with
  | seq_sc hsub hequiv _ ih =>
    -- The environment-separation invariant is budget-independent; the
    -- consumed location flows into the evidence budget's denotation by
    -- subcapture monotonicity.
    intro mu l h1 h2
    exact ih mu l
      (hasmem_drop_of_subset (fundamental_subcapt hsub env k st store hts) h1) h2
  | seq_union _ _ ih1 ih2 =>
    intro mu l h1 h2
    cases h1 with
    | left h => exact ih1 mu l h h2
    | right h => exact ih2 mu l h h2
  | seq_access_only hclosed hao =>
    intro mu l h1 _h2
    exact accessonly_denot_drop_free hts hΓ hclosed hao l h1
  | seq_sep hsep =>
    exact (fundamental_sepcheck hsep hΓ env k st store hts hdsep).seqComp

/-- **Extending memory with a fresh value cell preserves `MemTyped`.**  A value cell is
never an mcell, so the store typing (which only tracks mcells) is untouched: consistency
holds because every tracked location stays the same mcell it was, and each live tracked
cell's good-value obligation transports along `extend_val_subsumes` via the stored
relation's own monotonicity (`R.2`).  Unlike bare subsumption-monotonicity of `MemTyped`
(which is FALSE for a higher-order store — see the Phase-6 note at the top of this file),
this is a *local* growth (only the fresh, untracked location changes), so no global
relation-monotonicity is needed. -/
theorem WT_extend_val {k : Nat} {st : StoreTyping k} {m : Memory} {l : Nat} {w : HeapVal}
    (hwf_v : Exp.WfInHeap w.unwrap m.heap)
    (hreach : w.reachability = compute_reachability m.heap w.unwrap w.isVal)
    (hfresh : m.heap l = none)
    (hwt : MemTyped k st m) :
    MemTyped k st (m.extend_val l w hwf_v hreach hfresh) := by
  obtain ⟨hcons, hstable, hgood⟩ := hwt
  have hsub : (m.extend_val l w hwf_v hreach hfresh).subsumes m :=
    Memory.extend_val_subsumes m l w hwf_v hreach hfresh
  have hne : ∀ {l' : Nat} {R : MonRel k}, st.lookup l' = some R → l' ≠ l := by
    rintro l' R hst' rfl
    obtain ⟨n, ℓ, hlk⟩ := hcons l' R hst'
    simp [Memory.lookup, hfresh] at hlk
  refine ⟨?_, hstable, ?_⟩
  · intro l' R' hst'
    obtain ⟨n, ℓ, hlk⟩ := hcons l' R' hst'
    refine ⟨n, ℓ, ?_⟩
    rw [show (m.extend_val l w hwf_v hreach hfresh).lookup l' = m.lookup l' from by
      simp only [Memory.lookup, Memory.extend_val, Heap.extend, if_neg (hne hst')]]
    exact hlk
  · intro l' n R' hst' hlk' i
    have hl'ne : l' ≠ l := hne hst'
    have hlk_old : m.lookup l' = some (.capability (.mcell n .live)) := by
      rw [← hlk']
      simp only [Memory.lookup, Memory.extend_val, Heap.extend, if_neg hl'ne]
    have hgv := hgood l' n R' hst' hlk_old i
    exact hstable l' R' hst' i _ _ _ _
      (WP.WorldLe.trunc (Nat.le_of_lt i.isLt) ⟨hsub, fun _ _ h => h⟩) _ hgv

/-- A `_hpred`/`_hbool`-free variant of `Eval.eval_letin`: those two hypotheses are
vestigial (unused) in `eval_letin`'s proof, but for the semantic-typing `Q1`
(the `exi_exp_denot` postcondition) they are *false* — `Q1` carries `MemTyped` (not
subsumption-monotone for a higher-order store) and `witness_live` (anti-monotone).  This
copy drops them; the operational composition is identical. -/
theorem Eval.eval_letin' {k : Nat} {m : Memory} {e1 : Exp {}} {e2 : Exp ({},x)} {Q Q1 : Tpost}
    (he1 : Eval k m e1 Q1)
    (hQ_over : ∀ t v m', k ≤ t.readCount -> Q t v m')
    (h_nonstuck : ∀ {t1 : Trace} {m1 : Memory} {v : Exp {}}, t1.readCount < k ->
      Q1 t1 v m1 -> v.IsSimpleAns ∧ Exp.WfInHeap v m1.heap)
    (h_val : ∀ {t1 : Trace} {m1} {v : Exp {}}, t1.readCount < k ->
      m1.subsumes m -> Memory.FrameLive m t1 m1 ->
      (hv : Exp.IsSimpleVal v) -> (hwf_v : Exp.WfInHeap v m1.heap) -> Q1 t1 v m1 ->
      ∀ l' (hfresh : m1.lookup l' = none),
        Eval (k - t1.readCount)
          (m1.extend_val l' ⟨v, hv, compute_reachability m1.heap v hv⟩ hwf_v rfl hfresh)
          (e2.subst (Subst.openVar (.free l'))) (fun t2 => Q (t1 ++ t2)))
    (h_var : ∀ {t1 : Trace} {m1} {x : Var .var {}}, t1.readCount < k ->
      m1.subsumes m -> Memory.FrameLive m t1 m1 ->
      (hwf_x : x.WfInHeap m1.heap) -> Q1 t1 (.var x) m1 ->
      Eval (k - t1.readCount) m1 (e2.subst (Subst.openVar x)) (fun t2 => Q (t1 ++ t2))) :
    Eval k m (.letin e1 e2) Q := by
  refine ⟨?_, ?_⟩
  · refine Safe.letin he1.1
      (fun t1 v m1 hrun hbud => h_nonstuck hbud (he1.2 t1 v m1 hrun)) ?_ ?_
    · intro t1 m1 v hrun hv hwf_v l' hfresh
      rcases Nat.lt_or_ge t1.readCount k with hbud | hover
      · exact (h_val hbud (BigStep.subsumes hrun) (BigStep.frameLive hrun) hv hwf_v
          (he1.2 t1 v m1 hrun) l' hfresh).1
      · rw [Nat.sub_eq_zero_of_le hover]; exact Safe.exhausted
    · intro t1 m1 x hrun
      rcases Nat.lt_or_ge t1.readCount k with hbud | hover
      · have hq1 := he1.2 t1 (.var x) m1 hrun
        have hwfx : x.WfInHeap m1.heap := by
          cases (h_nonstuck hbud hq1).2 with | wf_var h => exact h
        exact (h_var hbud (BigStep.subsumes hrun) (BigStep.frameLive hrun) hwfx hq1).1
      · rw [Nat.sub_eq_zero_of_le hover]; exact Safe.exhausted
  · intro t v m' hbs
    cases hbs with
    | bs_letin_val hrun_e1 hv hwf_v hfresh hrun_e2 =>
      rename_i t1 t2 _ _ _
      rcases Nat.lt_or_ge t1.readCount k with hbud | hover
      · exact (h_val hbud (BigStep.subsumes hrun_e1) (BigStep.frameLive hrun_e1) hv hwf_v
          (he1.2 _ _ _ hrun_e1) _ hfresh).2 _ _ _ hrun_e2
      · exact hQ_over _ _ _ (by rw [Trace.readCount_append]; omega)
    | bs_letin_var hrun_e1 hrun_e2 =>
      rename_i t1 t2 _ _
      rcases Nat.lt_or_ge t1.readCount k with hbud | hover
      · have hq1 := he1.2 _ _ _ hrun_e1
        cases (h_nonstuck hbud hq1).2 with
        | wf_var hwfx =>
          exact (h_var hbud (BigStep.subsumes hrun_e1) (BigStep.frameLive hrun_e1) hwfx hq1).2
            _ _ _ hrun_e2
      · exact hQ_over _ _ _ (by rw [Trace.readCount_append]; omega)
    | bs_val hv => cases hv

/-- The shared `letin`-continuation runner used by both the value-binding and
variable-binding cases of `sem_typ_letin`.  Given the freshly-bound location `l0`
(holding a `T`-value at the post-`e1` world `(st1, mb)`, where `mb ⊒ store`) plus the
framed compatibility of `C2` at `mb`, it runs `e2`'s semantic typing in the killed,
`x:T`-extended environment and reassembles the outer `letin` postcondition (`t1 ++ t2`
trace, world composed through `(st1, mb)`, result value un-weakened/un-killed back to
`env`, pack-bound relativised to `store`). -/
theorem sem_typ_letin_cont
    {C1 C2 : CaptureSet s} {Γ : Ctx s} {T : Ty .capt s}
    {e2 : Exp (s,,Kind.var)} {U : Ty .exi s} {K : PeakSet s}
    {env : TypeEnv s} {k : Nat} {st : StoreTyping k} {store mb : Memory}
    {t1 : Trace} {st1 : StoreTyping (k - t1.readCount)} {l0 : Nat}
    (hclosed_C2 : C2.IsClosed)
    (ht2 : SemanticTyping (C2.rename Rename.succ) ((Γ.kill_peaks K),x:T) e2
      (U.rename Rename.succ))
    (hts : EnvTyping Γ env k st store)
    (hdsep : env.EnvSepWf)
    (hsubC1 : C1.denot env store ⊆ (C1 ∪ C2).denot env store)
    (hsubC2 : C2.denot env store ⊆ (C1 ∪ C2).denot env store)
    (hok1 : TraceOk t1 (C1.denot env store))
    (hwle1_mb : WorldLe st1 mb (st.trunc (Nat.sub_le k t1.readCount)) store)
    (hmt_mb : MemTyped (k - t1.readCount) st1 mb)
    (hval_l0 : Ty.val_denot env T (k - t1.readCount) st1 mb (.var (.free l0)))
    (hcompat_mb_C2 : mb.is_compatible (C2.denot env store)) :
    Eval (k - t1.readCount) mb
      ((e2.subst (Subst.from_TypeEnv env).lift).subst (Subst.openVar (.free l0)))
      (fun t2 v m' =>
        (t1 ++ t2).readCount < k →
        TraceOk (t1 ++ t2) ((C1 ∪ C2).denot env store) ∧
        ∃ (st' : StoreTyping (k - (t1 ++ t2).readCount)),
          WorldLe st' m' (st.trunc (Nat.sub_le k (t1 ++ t2).readCount)) store ∧
          MemTyped (k - (t1 ++ t2).readCount) st' m' ∧
          Ty.exi_val_denot env U (k - (t1 ++ t2).readCount) st' m' v ∧
          pack_bound ((C1 ∪ C2).denot env store) store v m' ∧ witness_live v m') := by
  -- `e1`'s post-world lives at the decremented index `k − t1.readCount`; run `e2`'s soundness
  -- there (`env_typing_worldle_trunc` descends the environment through the truncation).
  have hts_mb : EnvTyping Γ env (k - t1.readCount) st1 mb :=
    env_typing_worldle_trunc (Nat.sub_le k t1.readCount) hts hwle1_mb
  have henv_kill : EnvTyping (Γ.kill_peaks K) (env.kill_peaks K) (k - t1.readCount) st1 mb :=
    EnvTyping.kill_peaks K hts_mb
  have henv2 : EnvTyping ((Γ.kill_peaks K),x:T)
      ((env.kill_peaks K).extend_var l0 (compute_peakset env T.captureSet))
      (k - t1.readCount) st1 mb := by
    refine ⟨?_, ?_, henv_kill⟩
    · exact IDenot.equiv_ltr (kill_peaks_cs_val_denot (K := K.cs) T) hval_l0
    · show compute_peakset env T.captureSet = T.captureSet.peakset (Γ.kill_peaks K)
      rw [show T.captureSet.peakset (Γ.kill_peaks K) = T.captureSet.peakset Γ from
            CaptureSet.peakset_kill_peaks_cs Γ K.cs T.captureSet]
      exact (compute_peakset_correct hts T.captureSet).symm
  have hdsep2 : ((env.kill_peaks K).extend_var l0 (compute_peakset env T.captureSet)).EnvSepWf :=
    (TypeEnv.EnvSepWf.kill_peaks hdsep).extend_var
  have hC2_env2 : (C2.rename Rename.succ).denot
      ((env.kill_peaks K).extend_var l0 (compute_peakset env T.captureSet)) = C2.denot env := by
    have h1 : (C2.rename Rename.succ).denot
        ((env.kill_peaks K).extend_var l0 (compute_peakset env T.captureSet))
        = C2.denot (env.kill_peaks K) :=
      (rebind_captureset_denot (Rebind.weaken (env := env.kill_peaks K) (x := l0)
        (ps := compute_peakset env T.captureSet)) C2).symm
    rw [h1]
    funext mm
    simp only [CaptureSet.denot, TypeEnv.kill_peaks, Subst.from_TypeEnv_kill_peaks_cs]
  have hC2_mb_store : C2.denot env mb = C2.denot env store :=
    (closed_capture_denot_monotonic hclosed_C2 hts hwle1_mb.1).symm
  have hcompat2 : mb.is_compatible ((C2.rename Rename.succ).denot
      ((env.kill_peaks K).extend_var l0 (compute_peakset env T.captureSet)) mb) := by
    rw [hC2_env2, hC2_mb_store]; exact hcompat_mb_C2
  have he2 := ht2 ((env.kill_peaks K).extend_var l0 (compute_peakset env T.captureSet))
    (k - t1.readCount) st1 mb henv2 hdsep2 hcompat2
  simp only [Ty.exi_exp_denot] at he2
  have he2' := he2 hmt_mb
  have hexpr : (e2.subst (Subst.from_TypeEnv env).lift).subst (Subst.openVar (.free l0))
      = e2.subst (Subst.from_TypeEnv
          ((env.kill_peaks K).extend_var l0 (compute_peakset env T.captureSet))) := by
    rw [show (Subst.from_TypeEnv env) = Subst.from_TypeEnv (env.kill_peaks K) from
          (Subst.from_TypeEnv_kill_peaks_cs).symm]
    exact Exp.from_TypeEnv_weaken_open
  rw [hexpr]
  refine eval_post_monotonic ?_ he2'
  intro t2 m' v hp2 hguard
  have hbud2 : t2.readCount < k - t1.readCount := by
    rw [Trace.readCount_append] at hguard; omega
  obtain ⟨hok2, st', hwle2, hmt2, hval2, hpb2, hwl2⟩ := hp2 hbud2
  have hR2_eq : (C2.rename Rename.succ).denot
      ((env.kill_peaks K).extend_var l0 (compute_peakset env T.captureSet)) mb
      = C2.denot env store := (congrFun hC2_env2 mb).trans hC2_mb_store
  -- **Index bridge.**  `e2`'s post lands at `(k − t1.readCount) − t2.readCount`, which equals
  -- the compound decrement `k − (t1 ++ t2).readCount` (`readCount_append` + `Nat.sub_sub`).
  -- Descend `e2`'s witness through this (equality-level) truncation.
  have hidx_eq : k - (t1 ++ t2).readCount = (k - t1.readCount) - t2.readCount := by
    rw [Trace.readCount_append, Nat.sub_sub]
  have hjk : k - (t1 ++ t2).readCount ≤ (k - t1.readCount) - t2.readCount := Nat.le_of_eq hidx_eq
  have h2le : (k - t1.readCount) - t2.readCount ≤ k - t1.readCount := Nat.sub_le _ _
  refine ⟨TraceOk.append (TraceOk.mono hsubC1 hok1)
      (TraceOk.mono hsubC2 (hR2_eq ▸ hok2)), st'.trunc hjk, ?_, MemTyped_trunc hjk hmt2, ?_,
    pack_bound_mono hsubC2 hwle1_mb.1 (hR2_eq ▸ hpb2), hwl2⟩
  · -- Compose `e1`'s world-step (`hwle1_mb`, descended to the `e2` level) with `e2`'s
    -- (`hwle2`), then descend once more to the compound level.
    have hwle1_desc := WP.WorldLe.trunc h2le hwle1_mb
    rw [WP.World.trunc_trunc] at hwle1_desc
    have hwle_comp := WorldLe.trans hwle1_desc hwle2
    have hwle_fin := WP.WorldLe.trunc hjk hwle_comp
    rw [WP.World.trunc_trunc] at hwle_fin
    exact hwle_fin
  · -- Un-kill/un-weaken `e2`'s value back to `env`, then descend the index.
    have hval_env : Ty.exi_val_denot env U ((k - t1.readCount) - t2.readCount) st' m' v :=
      IDenot.equiv_rtl (kill_peaks_cs_exi_val_denot (K := K.cs) U)
        (IDenot.equiv_rtl (weaken_exi_val_denot
          (env := env.kill_peaks K) (T := U) (x := l0)
          (ps := compute_peakset env T.captureSet)) hval2)
    exact exi_val_denot_down_trunc (typed_env_is_downward_closed hts) U hjk v hval_env

/-- Semantic typing for `letin`. -/
theorem sem_typ_letin
  {C1 C2 : CaptureSet s} {Γ : Ctx s} {e1 : Exp s} {T : Ty .capt s}
  {e2 : Exp (s,,Kind.var)} {U : Ty .exi s}
  (hseq : SeqComp Γ C1 C2)
  (hΓ : Γ.IsClosed)
  (_hclosed_C1 : C1.IsClosed)
  (_hclosed_C2 : C2.IsClosed)
  (_hclosed_e : (Exp.letin e1 e2).IsClosed)
  (ht1 : SemanticTyping C1 Γ e1 (.typ T))
  (ht2 : SemanticTyping
    (C2.rename Rename.succ) ((Γ.kill_peaks ((C1.peakset Γ).consumed)),x:T) e2
    (U.rename Rename.succ)) :
  SemanticTyping (C1 ∪ C2) Γ (Exp.letin e1 e2) U := by
  intro env k st store hts hdsep hcompat
  simp only [Ty.exi_exp_denot, List.empty_eq]
  intro hmt
  simp only [Exp.subst]
  -- Budgets.
  have hunion : (C1 ∪ C2).denot env store = C1.denot env store ∪ C2.denot env store := rfl
  have hcompat' : store.is_compatible (C1.denot env store ∪ C2.denot env store) :=
    hunion ▸ hcompat
  have hsubC1 : C1.denot env store ⊆ (C1 ∪ C2).denot env store :=
    CapabilitySet.Subset.union_right_left
  have hsubC2 : C2.denot env store ⊆ (C1 ∪ C2).denot env store :=
    CapabilitySet.Subset.union_right_right
  have hcompat_C1 : store.is_compatible (C1.denot env store) :=
    Memory.is_compatible_union_left hcompat'
  have hcompat_C2 : store.is_compatible (C2.denot env store) :=
    Memory.is_compatible_union_right hcompat'
  -- `e1`'s evaluation.
  have he1 := ht1 env k st store hts hdsep hcompat_C1
  simp only [Ty.exi_exp_denot] at he1
  have he1' := he1 hmt
  -- Sequential composition at the denotation level: `C1`'s drops never meet `C2`.
  have hseqcomp : (C1.denot env store).SeqComp (C2.denot env store) :=
    captureSet_seqcomp_denot hts hΓ hdsep hseq
  have hpresent_C2 : ∀ mu l, (C2.denot env store).hasmem mu l → store.heap l ≠ none := by
    intro mu l hmem
    simp only [CaptureSet.denot, CaptureSet.ground_denot_eq_reachability] at hmem
    exact CaptureSet.reachability_dom hmem
  -- Frame `C2`'s compatibility across `e1`'s run (`t1` never drops a `C2`-cell).
  have hnodrop_C2_t1 : ∀ {t1 : Trace}, TraceOk t1 (C1.denot env store) →
      ∀ mu l, (C2.denot env store).hasmem mu l → ¬ Trace.extDrops t1 l := by
    intro t1 hok1 mu l hmem hd
    obtain ⟨mu', hm', hle⟩ :=
      CapabilitySet.covers_imp_exists_hasmem (TraceOk.drop_covers_of_extDrops hok1 hd)
    cases hle
    exact hseqcomp mu l hm' hmem
  refine Eval.eval_letin' he1'
    (fun t v m' hover hguard => absurd hguard (Nat.not_lt.mpr hover))
    (fun {t1 m1 v} hbud hq1 => ?_)
    (fun {t1 m1 v} hbud hsub_m1 hframe hv hwf_v hq1 l' hfresh => ?_)
    (fun {t1 m1 x0} hbud hsub_m1 hframe hwf_x hq1 => ?_)
  · -- h_nonstuck: the `e1`-result is a `T`-value, hence a simple answer + heap-wf.
    obtain ⟨_, st1, _, _, hval1, _, _⟩ := hq1 hbud
    simp only [Ty.exi_val_denot] at hval1
    exact ⟨val_denot_implies_simple_ans (typed_env_is_implying_simple_ans hts) T
             (k - t1.readCount) st1 m1 v hval1,
           val_denot_implies_wf (typed_env_is_implying_wf hts) T
             (k - t1.readCount) st1 m1 v hval1⟩
  · -- h_val: `e1` yields a value `v`; bind it at the fresh cell `l'`.
    obtain ⟨hok1, st1, hwle1, hmt1, hval1, _, _⟩ := hq1 hbud
    simp only [Ty.exi_val_denot] at hval1
    set w : HeapVal := ⟨v, hv, compute_reachability m1.heap v hv⟩ with hw
    set m_ext := m1.extend_val l' w hwf_v rfl hfresh with hm_ext
    have hsub_ext : m_ext.subsumes m1 := Memory.extend_val_subsumes m1 l' w hwf_v rfl hfresh
    have hmt_ext : MemTyped (k - t1.readCount) st1 m_ext := WT_extend_val hwf_v rfl hfresh hmt1
    have hlookup_l' : m_ext.lookup l' = some (.val w) := by
      rw [hm_ext]; simp [Memory.lookup, Memory.extend_val, Heap.extend]
    have hval_ext : Ty.val_denot env T (k - t1.readCount) st1 m_ext v :=
      val_denot_is_monotonic (typed_env_is_monotonic hts) T (k - t1.readCount) st1 hsub_ext hval1
    have hval_var : Ty.val_denot env T (k - t1.readCount) st1 m_ext (.var (.free l')) :=
      val_denot_is_transparent (typed_env_is_transparent hts) T (k - t1.readCount) st1
        hlookup_l' hval_ext
    have hwle1_ext : WorldLe st1 m_ext (st.trunc (Nat.sub_le k t1.readCount)) store :=
      ⟨Memory.subsumes_trans hsub_ext hwle1.1, hwle1.2⟩
    have hcompat_m1_C2 : m1.is_compatible (C2.denot env store) :=
      Memory.is_compatible_frame hcompat_C2 hpresent_C2 hframe hsub_m1
        (hnodrop_C2_t1 hok1)
    have hcompat_ext_C2 : m_ext.is_compatible (C2.denot env store) :=
      Memory.is_compatible_extend_val m1 l' w hwf_v rfl hfresh hcompat_m1_C2
    exact sem_typ_letin_cont _hclosed_C2 ht2 hts hdsep hsubC1 hsubC2 hok1
      hwle1_ext hmt_ext hval_var hcompat_ext_C2
  · -- h_var: `e1` yields a variable `x0`; reuse its existing cell.
    obtain ⟨hok1, st1, hwle1, hmt1, hval1, _, _⟩ := hq1 hbud
    simp only [Ty.exi_val_denot] at hval1
    cases x0 with
    | bound b => cases b
    | free x0 =>
      have hcompat_m1_C2 : m1.is_compatible (C2.denot env store) :=
        Memory.is_compatible_frame hcompat_C2 hpresent_C2 hframe hsub_m1
          (hnodrop_C2_t1 hok1)
      exact sem_typ_letin_cont _hclosed_C2 ht2 hts hdsep hsubC1 hsubC2 hok1
        hwle1 hmt1 hval1 hcompat_m1_C2

lemma sem_subtyp_top {T : Ty .capt s}
  (hpure : T.IsPureType) :
  SemSubtyp Γ T .top := by
  unfold SemSubtyp
  intro env k st H htyping _hdsep
  unfold IDenot.ImplyAfter
  intro j hjk st' m' hwle e hdenot_T
  have hsubsumes : m'.subsumes H := hwle.1
  unfold Ty.val_denot
  constructor
  · exact val_denot_implies_simple_ans (typed_env_is_implying_simple_ans htyping)
      T j st' m' e hdenot_T
  constructor
  · exact val_denot_implies_wf (typed_env_is_implying_wf htyping) T j st' m' e hdenot_T
  · have htyping' := env_typing_worldle_trunc hjk htyping hwle
    have hbound := val_denot_enforces_captures htyping' e hdenot_T
    -- `T` pure ⇒ `T.captureSet` denotes the empty set.
    unfold Ty.IsPureType at hpure
    exact (hpure.denot_empty (env := env) (m := m')).subset_of_subset hbound


lemma env_typing_lookup_tvar {X : BVar s .tvar} {S : PureTy s} {env : TypeEnv s}
  {k : Nat} {st : StoreTyping k} {m : Memory}
  (hlookup : Ctx.LookupTVar Γ X S)
  (htyping : EnvTyping Γ env k st m) :
  (env.lookup_tvar X).ImplyAfter k st m (Ty.val_denot env S.core) := by
  induction hlookup generalizing m
  case here Γ S =>
    match env with
    | .extend env0 (.tvar d) =>
      simp only [EnvTyping, TypeEnv.lookup_tvar] at htyping ⊢
      obtain ⟨hproper, himply_wf, himply_simple, himply, hpure, htyping'⟩ := htyping
      have hw : IDenot.Equiv (Ty.val_denot env0 S.core)
                (Ty.val_denot (env0.extend_tvar d) (S.core.rename Rename.succ)) := by
        simpa only [TypeEnv.extend_tvar] using tweaken_val_denot (d := d)
      unfold IDenot.ImplyAfter at himply ⊢
      intro j hjk st' m' hsub e hd
      exact IDenot.equiv_ltr hw (himply j hjk st' m' hsub e hd)
  case there Γ X S b a a_ih =>
    cases b with
    | var T =>
      match env with
      | .extend env0 (.var v ps0) =>
        simp only [EnvTyping, TypeEnv.lookup_tvar] at htyping ⊢
        obtain ⟨hval_denot, _, htyping'⟩ := htyping
        have ih_result := a_ih htyping'
        have hw : IDenot.Equiv (Ty.val_denot env0 S.core)
                  (Ty.val_denot (env0.extend_var v ps0) (S.core.rename Rename.succ)) := by
          simpa only [TypeEnv.extend_var] using weaken_val_denot (x := v) (ps := ps0)
        unfold IDenot.ImplyAfter at ih_result ⊢
        intro j hjk st' m' hsub e hd
        exact IDenot.equiv_ltr hw (ih_result j hjk st' m' hsub e hd)
    | tvar T =>
      match env with
      | .extend env0 (.tvar d) =>
        simp only [EnvTyping, TypeEnv.lookup_tvar] at htyping ⊢
        obtain ⟨hproper, himply_wf, himply_simple, himply_bound, hpure, htyping'⟩ := htyping
        have ih_result := a_ih htyping'
        have hw : IDenot.Equiv (Ty.val_denot env0 S.core)
                  (Ty.val_denot (env0.extend_tvar d) (S.core.rename Rename.succ)) := by
          simpa only [TypeEnv.extend_tvar] using tweaken_val_denot (d := d)
        unfold IDenot.ImplyAfter at ih_result ⊢
        intro j hjk st' m' hsub e hd
        exact IDenot.equiv_ltr hw (ih_result j hjk st' m' hsub e hd)
    | cvar _ cb =>
      match env with
      | .extend env0 (.cvar a0 cs cap) =>
        simp only [EnvTyping, TypeEnv.lookup_tvar] at htyping ⊢
        obtain ⟨hwf_cb, hbound_wf, hbound, _, _, _, htyping'⟩ := htyping
        have ih_result := a_ih htyping'
        have hw : IDenot.Equiv (Ty.val_denot env0 S.core)
                  (Ty.val_denot (env0.extend_cvar cs cap a0) (S.core.rename Rename.succ)) := by
          simpa only [TypeEnv.extend_cvar] using
            cweaken_val_denot (cs := cs) (cap := cap) (a := a0)
        unfold IDenot.ImplyAfter at ih_result ⊢
        intro j hjk st' m' hsub e hd
        exact IDenot.equiv_ltr hw (ih_result j hjk st' m' hsub e hd)
    | lock Ψ =>
      match env with
      | .extend env0 (.lock) =>
        simp only [EnvTyping, TypeEnv.lookup_tvar] at htyping ⊢
        obtain ⟨_, htyping'⟩ := htyping
        have ih_result := a_ih htyping'
        have hw : IDenot.Equiv (Ty.val_denot env0 S.core)
                  (Ty.val_denot (env0.extend_lock) (S.core.rename Rename.succ)) := by
          simpa only [TypeEnv.extend_lock] using
            (lweaken_val_denot (env := env0) (T := S.core))
        unfold IDenot.ImplyAfter at ih_result ⊢
        intro j hjk st' m' hsub e hd
        exact IDenot.equiv_ltr hw (ih_result j hjk st' m' hsub e hd)

lemma sem_subtyp_tvar {X : BVar s .tvar} {S : PureTy s}
  (hlookup : Ctx.LookupTVar Γ X S) :
  SemSubtyp Γ (.tvar X) S.core := by
  unfold SemSubtyp
  intro env k st H htyping _hdsep
  have himply := env_typing_lookup_tvar hlookup htyping
  intro j hjk st' m' hwle e hd
  simp only [Ty.val_denot] at hd
  exact himply j hjk st' m' hwle e hd

/-- The peakset recorded for a `var` binding is denotationally inert: the value
relation reads the environment only through variable indices, type-variable
denotations, and capture-variable data (never the peakset, which only feeds
`compute_peaks` and never escapes into a proposition).  We transport along a
`Retype` at the identity substitution, whose structure imposes no constraint on
the two peaksets. -/
def Retype.extend_var_peak {env : TypeEnv s} (arg : Nat) (ps1 ps2 : PeakSet s) :
    Retype (env.extend_var arg ps1) Subst.id (env.extend_var arg ps2)
      ⟨CaptureSet.empty, .empty⟩ where
  var := fun x => by
    change ((env.extend_var arg ps1).lookup_var x).1
      = ((env.extend_var arg ps2).lookup_var x).1
    cases x with
    | here => rfl
    | there y => rfl
  tvar := fun X => by
    intro k st m e
    simp only [Subst.id, PureTy.tvar, Ty.val_denot]
    cases X with
    | there X' => rfl
  cvar := fun C => by
    cases C with
    | there C' => rfl

theorem extend_var_peak_exi_val_denot {env : TypeEnv s} {arg : Nat} {ps1 ps2 : PeakSet s}
    (U : Ty .exi (s,x)) :
    IDenot.Equiv (Ty.exi_val_denot (env.extend_var arg ps1) U)
      (Ty.exi_val_denot (env.extend_var arg ps2) U) := by
  have h := retype_exi_val_denot (Retype.extend_var_peak (env := env) arg ps1 ps2) U
  rwa [Ty.subst_id] at h

lemma sem_subtyp_arrow {T1 T2 : Ty .capt s} {cs1 cs2 : CaptureSet s} {U1 U2 : Ty .exi (s,x)}
  (harg : SemSubtyp Γ T2 T1)
  (hcs : SemSubcapt Γ cs1 cs2)
  (hcs2_closed : CaptureSet.IsClosed cs2)
  (hres : SemSubtyp (Γ,x:T2) U1 U2) :
  SemSubtyp Γ (.arrow T1 cs1 U1) (.arrow T2 cs2 U2) := by
  unfold SemSubtyp
  intro env ki st H htyping hdsep j hjk st' m' hwle e hv
  have htyping' := env_typing_worldle_trunc hjk htyping hwle
  simp only [Ty.val_denot] at hv ⊢
  obtain ⟨hwf_e, _hwf_cs1, cs', T0, t0, hresolve, hwf_cs', hR0_sub1, hbody1⟩ := hv
  refine ⟨hwf_e, ?_, cs', T0, t0, hresolve, hwf_cs', ?_, ?_⟩
  · exact CaptureSet.wf_subst (CaptureSet.wf_of_closed hcs2_closed)
      (from_TypeEnv_wf_in_heap htyping')
  · exact CapabilitySet.Subset.trans hR0_sub1 (hcs env j st' m' htyping')
  · -- The arrow body: argument is contravariant (harg : T2 <: T1), codomain
    -- covariant (hres : U1 <: U2 under x:T2), capture set covariant.
    intro i hij st'' m'' arg hwle'' hmt'' hcompat'' harg2
    -- Coerce the T2-argument to a T1-argument via `harg`.
    have harg1 : Ty.val_denot env T1 i st'' m'' (.var (.free arg)) :=
      harg env j st' m' htyping' hdsep i hij st'' m'' hwle'' (.var (.free arg)) harg2
    -- Fire hv's body at the same world with the coerced argument.
    have hbody1' := hbody1 i hij st'' m'' arg hwle'' hmt'' hcompat'' harg1
    refine eval_post_monotonic_general ?_ hbody1'
    intro m''' _hsub''' t v hpost hguard
    obtain ⟨htr, st''', hwle''', hmt''', hval1, hpb, hwl⟩ := hpost hguard
    refine ⟨htr, st''', hwle''', hmt''', ?_, hpb, hwl⟩
    -- hval1 lives at peakset `compute_peakset env T1.captureSet` and type U1;
    -- swap to the goal's peakset (peakset-inert) then weaken U1 → U2 via hres.
    have hval1' :
        Ty.exi_val_denot (env.extend_var arg (compute_peakset env T2.captureSet)) U1
          (i - t.readCount) st''' m''' v :=
      IDenot.equiv_ltr (extend_var_peak_exi_val_denot U1) hval1
    -- EnvTyping for the extended context `(Γ,x:T2)` at world `(st'', m'')`.
    have htyping'' : EnvTyping Γ env i st'' m'' :=
      env_typing_worldle_trunc hij htyping' hwle''
    have henv2 : EnvTyping (Γ,x:T2) (env.extend_var arg (compute_peakset env T2.captureSet))
        i st'' m'' := by
      refine ⟨harg2, ?_, htyping''⟩
      exact (compute_peakset_correct htyping'' T2.captureSet).symm
    exact hres _ i st'' m'' henv2 hdsep.extend_var (i - t.readCount) (Nat.sub_le i t.readCount)
      st''' m''' hwle''' v hval1'

lemma sem_subtyp_trans {k : TySort} {T1 T2 T3 : Ty k s}
  (h12 : SemSubtyp Γ T1 T2)
  (h23 : SemSubtyp Γ T2 T3) :
  SemSubtyp Γ T1 T3 := by
  cases k with
  | capt =>
    intro env ki st H htyping hdsep j hjk st' m' hwle e hd
    exact h23 env ki st H htyping hdsep j hjk st' m' hwle e
      (h12 env ki st H htyping hdsep j hjk st' m' hwle e hd)
  | exi =>
    intro env ki st H htyping hdsep j hjk st' m' hwle e hd
    exact h23 env ki st H htyping hdsep j hjk st' m' hwle e
      (h12 env ki st H htyping hdsep j hjk st' m' hwle e hd)

lemma sem_subtyp_refl {k : TySort} {T : Ty k s} :
  SemSubtyp Γ T T := by
  cases k with
  | capt =>
    unfold SemSubtyp
    intro env k st H htyping _hdsep j hjk st' m' _hwle e hd
    exact hd
  | exi =>
    unfold SemSubtyp
    intro env k st H htyping _hdsep j hjk st' m' _hwle e hd
    exact hd


lemma fundamental_subbound
  (hsub : Subbound Γ B1 B2) :
  SemSubbound Γ B1 B2 := by
  induction hsub with
  | capset hsubcapt =>
    intro env k st m htyping
    simpa only [CaptureBound.denot] using
      CapabilityBound.SubsetEq.set (fundamental_subcapt hsubcapt env k st m htyping)
  | top =>
    intro env k st m htyping
    simpa only [CaptureBound.denot] using
      (CapabilityBound.SubsetEq.top : CapabilityBound.SubsetEq _ .top)


lemma sem_subtyp_cpoly {cb1 cb2 : CaptureBound s} {cs1 cs2 : CaptureSet s} {T1 T2 : Ty .exi (s,C)}
  (hB : SemSubbound Γ cb2 cb1) -- contravariant in bound
  (hcs : SemSubcapt Γ cs1 cs2) -- covariant in capture set
  (hcs2_closed : CaptureSet.IsClosed cs2) -- cs2 is closed
  (hT : SemSubtyp (Γ,C[.access_only]<:cb2) T1 T2) -- covariant in body under tighter bound
  (hclosed_cb2 : cb2.IsClosed)
  : SemSubtyp Γ (.cpoly cb1 cs1 T1) (.cpoly cb2 cs2 T2) := by
  unfold SemSubtyp
  intro env ki st H htyping hdsep j hjk st' m' hwle e hv
  have htyping' := env_typing_worldle_trunc hjk htyping hwle
  simp only [Ty.val_denot] at hv ⊢
  obtain ⟨hwf_e, _hwf_cs1, cs', B0, t0, hresolve, hwf_cs', hR0_sub1, hbody1⟩ := hv
  refine ⟨hwf_e, ?_, cs', B0, t0, hresolve, hwf_cs', ?_, ?_⟩
  · exact CaptureSet.wf_subst (CaptureSet.wf_of_closed hcs2_closed)
      (from_TypeEnv_wf_in_heap htyping')
  · exact CapabilitySet.Subset.trans hR0_sub1 (hcs env j st' m' htyping')
  · intro i hij st'a m'a CS hCSwf hCSdf hwle'a hmt'a hcompat'a hbound2
    have htyping_a : EnvTyping Γ env i st'a m'a :=
      env_typing_worldle_trunc hij htyping' hwle'a
    -- The bound is contravariant: from the target's `A0 ≤ cb2`, derive `A0 ≤ cb1`
    -- via `hB : cb2 <: cb1`.
    have hbound1 : ((CS.denot TypeEnv.empty m'a).BoundedBy (cb1.denot env m'a)) :=
      CapabilitySet.BoundedBy.trans hbound2 (hB env i st'a m'a htyping_a)
    have hbody1' := hbody1 i hij st'a m'a CS hCSwf hCSdf hwle'a hmt'a hcompat'a hbound1
    refine eval_post_monotonic_general ?_ hbody1'
    intro m'' _hsub t v hpost hguard
    obtain ⟨htr, st'', hwle'', hmt'', hval1, hpb, hwl⟩ := hpost hguard
    refine ⟨htr, st'', hwle'', hmt'', ?_, hpb, hwl⟩
    -- Weaken the codomain T1 → T2 via `hT` at `(Γ,C[.access_only]<:cb2)`.
    have henvT : EnvTyping (Γ,C[.access_only]<:cb2)
        (env.extend_cvar CS (cap := CS.ground_denot m'a)) i st'a m'a := by
      refine ⟨hCSwf, ?_, ?_, rfl, hCSdf, rfl, htyping_a⟩
      · exact CaptureBound.wf_subst (CaptureBound.wf_of_closed hclosed_cb2)
          (from_TypeEnv_wf_in_heap htyping_a)
      · have heq : CS.ground_denot = CaptureSet.denot TypeEnv.empty CS := by
          funext m
          simp only [CaptureSet.denot, Subst.from_TypeEnv_empty, CaptureSet.subst_id]
        rw [heq]
        exact hbound2
    exact hT _ i st'a m'a henvT hdsep.extend_cvar_access_only (i - t.readCount)
      (Nat.sub_le i t.readCount) st'' m'' hwle'' v hval1

/-- Builds `EnvTyping` for the `n`-ary evidence extension `TypeEnv.extend_cvars`,
    matching `Ctx.extendCVars a Γ n`.  Each binder is `[a]<:.unbound`, so its per-cvar
    obligations are: well-formed evidence (`hwf`), trivially-well-formed unbound bound,
    `BoundedBy .top`, the definitional `cap = ground_denot`, drop-freedom (`hdf`), and
    the authority tag `rfl`. -/
theorem EnvTyping.extend_cvars {s : Sig} {Γ : Ctx s} {env : TypeEnv s}
    {k : Nat} {st : StoreTyping k} {m : Memory} {a : Authority} :
    {n : Nat} → {CS : List.Vector (CaptureSet {}) n} →
    EnvTyping Γ env k st m →
    (∀ cs ∈ CS.toList, cs.WfInHeap m.heap) →
    (∀ cs ∈ CS.toList, (cs.ground_denot m).drop_free) →
    EnvTyping (Ctx.extendCVars a Γ n) (TypeEnv.extend_cvars env m a CS) k st m
  | 0, _, hts, _, _ => hts
  | n + 1, CS, hts, hwf, hdf => by
    obtain ⟨l, hl⟩ := CS
    cases l with
    | nil => cases hl
    | cons c l' =>
      have hl' : l'.length = n := by simpa using hl
      refine ⟨hwf c List.mem_cons_self, ?_, ?_, rfl, hdf c List.mem_cons_self, rfl, ?_⟩
      · simpa only [CaptureBound.subst] using CaptureBound.WfInHeap.wf_unbound
      · simp only [CaptureBound.denot]; exact CapabilitySet.BoundedBy.top
      · exact EnvTyping.extend_cvars (CS := ⟨l', hl'⟩) hts
          (fun cs hmem => hwf cs (List.mem_cons_of_mem c hmem))
          (fun cs hmem => hdf cs (List.mem_cons_of_mem c hmem))

/-- `EnvSepWf.extend_cvar_access_only` iterated over `n` binders: extending with
    `n` `.access_only` evidence binders preserves `EnvSepWf` (access-only binders are
    exempt from the disjointness demand). -/
theorem TypeEnv.EnvSepWf.extend_cvars_access_only {s : Sig} {env : TypeEnv s}
    {m : Memory} :
    {n : Nat} → {CS : List.Vector (CaptureSet {}) n} →
    env.EnvSepWf → (TypeEnv.extend_cvars env m .access_only CS).EnvSepWf
  | 0, _, h => h
  | _ + 1, CS, h =>
    (TypeEnv.EnvSepWf.extend_cvars_access_only (CS := List.Vector.tail CS) h)
      |>.extend_cvar_access_only

lemma sem_subtyp_exi {n : Nat} {T1 T2 : Ty .capt (Sig.extendCVars s n)}
  (hT : SemSubtyp (Ctx.extendCVars .access_only Γ n) T1 T2) -- covariant in body
  : SemSubtyp Γ (.exi n T1) (.exi n T2) := by
  unfold SemSubtyp
  intro env ki st H htyping hdsep j hjk st' m' hwle e hv
  have htyping' := env_typing_worldle_trunc hjk htyping hwle
  simp only [Ty.exi_val_denot] at hv ⊢
  -- `exi_val_denot` (exi n) is the ∃-form recording the pack witness `CS`/`x`.
  obtain ⟨CS, x, hres, hCSwf, hCSdf, hCSdisj, hval1⟩ := hv
  refine ⟨CS, x, hres, hCSwf, hCSdf, hCSdisj, ?_⟩
  -- Re-tag all `n` fresh binders `.can_drop` → `.access_only` (authority is inert),
  -- weaken T1 → T2 via `hT` at the `.access_only`-extended context, then re-tag back.
  have hval1' :
      Ty.val_denot (TypeEnv.extend_cvars env m' .access_only CS) T1 j st' m' (.var x) :=
    IDenot.equiv_ltr (val_denot_auth_irrel_cvars T1) hval1
  have henvC :
      EnvTyping (Ctx.extendCVars .access_only Γ n)
        (TypeEnv.extend_cvars env m' .access_only CS) j st' m' :=
    EnvTyping.extend_cvars htyping'
      (fun cs hmem => hCSwf cs hmem) (fun cs hmem => hCSdf cs hmem)
  have hval2' :=
    hT _ j st' m' henvC hdsep.extend_cvars_access_only j (Nat.le_refl j) st' m'
      (WorldLe.refl_trunc_self (Nat.le_refl j) st' m') (.var x) hval1'
  exact IDenot.equiv_rtl (val_denot_auth_irrel_cvars T2) hval2'

lemma sem_subtyp_typ {T1 T2 : Ty .capt s}
  (hT : SemSubtyp Γ T1 T2) -- covariant in body
  : SemSubtyp Γ (.typ T1) (.typ T2) := by
  unfold SemSubtyp
  -- `.typ T` denotes `capt_val_denot env T`, so the goal is exactly `SemSubtyp Γ T1 T2`.
  intro env k st H htyping hdsep j hjk st' m' hwle e hd
  simp only [Ty.exi_val_denot] at hd ⊢
  exact hT env k st H htyping hdsep j hjk st' m' hwle e hd


lemma sem_subtyp_poly {S1 S2 : PureTy s} {cs1 cs2 : CaptureSet s} {T1 T2 : Ty .exi (s,X)}
  (hS : SemSubtyp Γ S2.core S1.core) -- contravariant in bound
  (hcs : SemSubcapt Γ cs1 cs2) -- covariant in capture set
  (hcs2_closed : CaptureSet.IsClosed cs2) -- cs2 is closed
  (hT : SemSubtyp (Γ,X<:S2) T1 T2) -- covariant in body under tighter bound
  : SemSubtyp Γ (.poly S1.core cs1 T1) (.poly S2.core cs2 T2) := by
  unfold SemSubtyp
  intro env ki st H htyping hdsep j hjk st' m' hwle e hv
  have htyping' := env_typing_worldle_trunc hjk htyping hwle
  simp only [Ty.val_denot] at hv ⊢
  obtain ⟨hwf_e, _hwf_cs1, cs', S0, t0, hresolve, hwf_cs', hR0_sub1, hbody1⟩ := hv
  refine ⟨hwf_e, ?_, cs', S0, t0, hresolve, hwf_cs', ?_, ?_⟩
  · exact CaptureSet.wf_subst (CaptureSet.wf_of_closed hcs2_closed)
      (from_TypeEnv_wf_in_heap htyping')
  · exact CapabilitySet.Subset.trans hR0_sub1 (hcs env j st' m' htyping')
  · intro i hij st'a m'a denot hwle'a hmt'a hcompat'a hproper himply_simple_ans himply2 hpure
    have htyping_a : EnvTyping Γ env i st'a m'a :=
      env_typing_worldle_trunc hij htyping' hwle'a
    -- The bound is contravariant: from the target's `denot ⊆ val_denot S2.core`,
    -- derive `denot ⊆ val_denot S1.core` via `hS : S2.core <: S1.core`.
    have himply1 : denot.ImplyAfter i st'a m'a (Ty.val_denot env S1.core) := by
      intro i' hi'i st''a m''a hw e' hd
      exact hS env i st'a m'a htyping_a hdsep i' hi'i st''a m''a hw e'
        (himply2 i' hi'i st''a m''a hw e' hd)
    have hbody1' := hbody1 i hij st'a m'a denot hwle'a hmt'a hcompat'a hproper
      himply_simple_ans himply1 hpure
    refine eval_post_monotonic_general ?_ hbody1'
    intro m'' _hsub t v hpost hguard
    obtain ⟨htr, st'', hwle'', hmt'', hval1, hpb, hwl⟩ := hpost hguard
    refine ⟨htr, st'', hwle'', hmt'', ?_, hpb, hwl⟩
    -- Weaken the codomain T1 → T2 via `hT` at the extended context `(Γ,X<:S2)`.
    have henvT : EnvTyping (Γ,X<:S2) (env.extend_tvar denot) i st'a m'a :=
      ⟨hproper, hproper.2.2.2.1, himply_simple_ans, himply2, hpure, htyping_a⟩
    exact hT _ i st'a m'a henvT hdsep.extend_tvar (i - t.readCount) (Nat.sub_le i t.readCount)
      st'' m'' hwle'' v hval1

lemma sem_subtyp_modal {cs1 cs2 : CaptureSet s} {Ψ : ModalCtx s} {E1 E2 : Ty .exi s}
  (hcs : SemSubcapt Γ cs1 cs2)
  (hcs2_closed : CaptureSet.IsClosed cs2)
  (hΨ_closed : ModalCtx.IsClosed Ψ)
  (hT : SemSubtyp (Γ.push_lock Ψ) (E1.rename Rename.succ) (E2.rename Rename.succ)) :
  SemSubtyp Γ (.modal cs1 Ψ E1) (.modal cs2 Ψ E2) := by
  unfold SemSubtyp
  intro env ki st H htyping hdsep j hjk st' m' hwle e hv
  have htyping' := env_typing_worldle_trunc hjk htyping hwle
  simp only [Ty.val_denot] at hv ⊢
  obtain ⟨hwf_e, _hwf_cs1, cs0, sepctx0, t0, hresolve, hwf_cs0, hwf_sepctx0,
    hsat_impl, hR0_sub1, hbody1⟩ := hv
  refine ⟨hwf_e, ?_, cs0, sepctx0, t0, hresolve, hwf_cs0, hwf_sepctx0, hsat_impl, ?_, ?_⟩
  · exact CaptureSet.wf_subst (CaptureSet.wf_of_closed hcs2_closed)
      (from_TypeEnv_wf_in_heap htyping')
  · exact CapabilitySet.Subset.trans hR0_sub1 (hcs env j st' m' htyping')
  · intro i hij st'a m'a hwle'a hmt'a hcompat'a hkind hsep
    have htyping_a : EnvTyping Γ env i st'a m'a :=
      env_typing_worldle_trunc hij htyping' hwle'a
    have hbody1' := hbody1 i hij st'a m'a hwle'a hmt'a hcompat'a hkind hsep
    refine eval_post_monotonic_general ?_ hbody1'
    intro m'' _hsub t v hpost hguard
    obtain ⟨htr, st'', hwle'', hmt'', hval1, hpb, hwl⟩ := hpost hguard
    refine ⟨htr, st'', hwle'', hmt'', ?_, hpb, hwl⟩
    -- Weaken codomain E1 → E2 via `hT` under the lock (push_lock Ψ).  The `Satisfy`
    -- premise of the lock context is rebuilt from the body's kind/sep + closed Ψ.
    have hsat_Ψ : env.Satisfy Ψ m'a := by
      refine ⟨?_, ?_, hkind, hsep⟩
      · intro C hhas
        exact CaptureSet.wf_subst
          (SepCtx.WfInHeap.of_has (SepCtx.wf_of_closed hΨ_closed.sep) hhas)
          (from_TypeEnv_wf_in_heap htyping_a)
      · intro C mode hhas
        exact CaptureSet.wf_subst
          (MutabilityCtx.WfInHeap.of_has
            (MutabilityCtx.wf_of_closed hΨ_closed.mutability) hhas)
          (from_TypeEnv_wf_in_heap htyping_a)
    have henv_lock : EnvTyping (Γ.push_lock Ψ) (env.extend_lock) i st'a m'a :=
      ⟨hsat_Ψ, htyping_a⟩
    have hval1' :
        Ty.exi_val_denot (env.extend_lock) (E1.rename Rename.succ) (i - t.readCount) st'' m'' v :=
      IDenot.equiv_ltr (lweaken_exi_val_denot (env := env) (T := E1)) hval1
    have hval2' :
        Ty.exi_val_denot (env.extend_lock) (E2.rename Rename.succ) (i - t.readCount) st'' m'' v :=
      hT _ i st'a m'a henv_lock hdsep.extend_lock (i - t.readCount) (Nat.sub_le i t.readCount)
        st'' m'' hwle'' v hval1'
    exact IDenot.equiv_rtl (lweaken_exi_val_denot (env := env) (T := E2)) hval2'

/-- Renaming preserves closedness of a separation context (public re-statement of
the private `SepCtx.rename_closed_any`, used by `sem_subtyp_modal_modal`). -/
theorem SepCtx.rename_isClosed {Ψ : SepCtx s1} {f : Rename s1 s2}
    (hc : Ψ.IsClosed) : (Ψ.rename f).IsClosed := by
  induction hc with
  | empty => exact SepCtx.IsClosed.empty
  | cons _ hC ih =>
    simp only [SepCtx.rename]
    exact SepCtx.IsClosed.cons ih (CaptureSet.rename_isClosed hC)

lemma sem_subtyp_modal_modal {cs : CaptureSet s} {Ψ1 Ψ2 : ModalCtx s} {E : Ty .exi s}
  (hΓ : Γ.IsClosed)
  (hΨ1_closed : ModalCtx.IsClosed Ψ1)
  (hΨ2_closed : ModalCtx.IsClosed Ψ2)
  (hsat : Satisfy (Γ.push_lock Ψ2) (Ψ1.rename Rename.succ)) :
  SemSubtyp Γ (.modal cs Ψ1 E) (.modal cs Ψ2 E) := by
  unfold SemSubtyp
  intro env ki st H htyping hdsep j hjk st' m' hwle e hv
  have htyping' := env_typing_worldle_trunc hjk htyping hwle
  have hΨ1r_closed : (Ψ1.rename (Rename.succ (k := Kind.lock))).IsClosed :=
    ModalCtx.rename_closed hΨ1_closed
  have hΓlock_closed : (Γ.push_lock Ψ2).IsClosed :=
    Ctx.IsClosed.push hΓ (Binding.IsClosed.lock hΨ2_closed)
  simp only [Ty.val_denot] at hv ⊢
  obtain ⟨hwf_e, hwf_cs, cs0, sepctx0, t0, hresolve, hwf_cs0, hwf_sepctx0,
    hsat_impl1, hR0_sub1, hbody1⟩ := hv
  -- `cs` and `E` are unchanged; only `Ψ1 ⇒ Ψ2` (the separation weakening).
  refine ⟨hwf_e, hwf_cs, cs0, sepctx0, t0, hresolve, hwf_cs0, hwf_sepctx0, ?_, hR0_sub1, ?_⟩
  · -- The `Satisfy`-implication field: from a target `env.Satisfy Ψ2 m0` derive the
    -- source's `env.Satisfy Ψ1 m0` via `hsat` (read in the lock-extended env).
    intro m0 hsub hsatΨ2
    have htyping0 : EnvTyping Γ env j st' m0 := env_typing_monotonic htyping' hsub
    have henvlock0 : EnvTyping (Γ.push_lock Ψ2) (env.extend_lock) j st' m0 :=
      ⟨hsatΨ2, htyping0⟩
    have hsatΨ1 : env.Satisfy Ψ1 m0 :=
      TypeEnv.satisfy_lweaken_iff.mp
        (sem_satisfy_global hΨ1r_closed hΓlock_closed hsat
          (env.extend_lock) j st' m0 henvlock0 hdsep.extend_lock)
    exact hsat_impl1 m0 hsub hsatΨ1
  · -- The body: the target supplies `Ψ2` kind/sep facts; convert to `Ψ1` and feed
    -- the source body (codomain `E` is unchanged).
    intro i hij st'a m'a hwle'a hmt'a hcompat'a hkind hsep
    have htyping_a : EnvTyping Γ env i st'a m'a :=
      env_typing_worldle_trunc hij htyping' hwle'a
    have hsatΨ2 : env.Satisfy Ψ2 m'a := by
      refine ⟨?_, ?_, hkind, hsep⟩
      · intro C hhas
        exact CaptureSet.wf_subst
          (SepCtx.WfInHeap.of_has (SepCtx.wf_of_closed hΨ2_closed.sep) hhas)
          (from_TypeEnv_wf_in_heap htyping_a)
      · intro C mode hhas
        exact CaptureSet.wf_subst
          (MutabilityCtx.WfInHeap.of_has
            (MutabilityCtx.wf_of_closed hΨ2_closed.mutability) hhas)
          (from_TypeEnv_wf_in_heap htyping_a)
    have henvlock_a : EnvTyping (Γ.push_lock Ψ2) (env.extend_lock) i st'a m'a :=
      ⟨hsatΨ2, htyping_a⟩
    have hsatΨ1 : env.Satisfy Ψ1 m'a :=
      TypeEnv.satisfy_lweaken_iff.mp
        (sem_satisfy_global hΨ1r_closed hΓlock_closed hsat
          (env.extend_lock) i st'a m'a henvlock_a hdsep.extend_lock)
    exact hbody1 i hij st'a m'a hwle'a hmt'a hcompat'a hsatΨ1.kind hsatΨ1.sep

theorem fundamental_subtyp
  (hT1 : T1.IsClosed) (hT2 : T2.IsClosed)
  (hsub : Subtyp Γ T1 T2) :
  SemSubtyp Γ T1 T2 := by
  -- Induction on the derivation, dispatching each constructor to the matching
  -- `sem_subtyp_*` lemma.  Closedness of both endpoints is threaded through the IHs.
  revert hT1 hT2
  induction hsub with
  | top hpure => intro _ _; exact sem_subtyp_top hpure
  | refl => intro _ _; exact sem_subtyp_refl
  | trans hmid _ _ ih1 ih2 =>
    intro hT1 hT2
    exact sem_subtyp_trans (ih1 hT1 hmid) (ih2 hmid hT2)
  | tvar hlookup => intro _ _; exact sem_subtyp_tvar hlookup
  | arrow _ s_cs _ ih_arg ih_res =>
    intro hT1 hT2
    cases hT1 with | arrow hT1a _ hU1 =>
    cases hT2 with | arrow hT2a hcs2 hU2 =>
    exact sem_subtyp_arrow (ih_arg hT2a hT1a) (fundamental_subcapt s_cs) hcs2 (ih_res hU1 hU2)
  | poly _ s_cs _ ih_bound ih_body =>
    intro hT1 hT2
    cases hT1 with | poly hS1 _ hT1b =>
    cases hT2 with | poly hS2 hcs2 hT2b =>
    exact sem_subtyp_poly (ih_bound hS2 hS1) (fundamental_subcapt s_cs) hcs2 (ih_body hT1b hT2b)
  | cpoly s_bound s_cs _ ih_body =>
    intro hT1 hT2
    cases hT1 with | cpoly _ _ hT1b =>
    cases hT2 with | cpoly hcb2 hcs2 hT2b =>
    exact sem_subtyp_cpoly (fundamental_subbound s_bound) (fundamental_subcapt s_cs) hcs2
      (ih_body hT1b hT2b) hcb2
  | modal s_cs _ ih_body =>
    intro hT1 hT2
    cases hT1 with | modal _ hΨ hE1 =>
    cases hT2 with | modal hcs2 _ hE2 =>
    exact sem_subtyp_modal (fundamental_subcapt s_cs) hcs2 hΨ
      (ih_body (Ty.rename_closed hE1) (Ty.rename_closed hE2))
  | modal_modal hΓ hΨ1 hΨ2 hsat =>
    intro _ _; exact sem_subtyp_modal_modal hΓ hΨ1 hΨ2 hsat
  | exi _ ih_body =>
    intro hT1 hT2
    cases hT1 with | exi hT1b =>
    cases hT2 with | exi hT2b =>
    exact sem_subtyp_exi (ih_body hT1b hT2b)
  | typ _ ih_body =>
    intro hT1 hT2
    cases hT1 with | typ hT1b =>
    cases hT2 with | typ hT2b =>
    exact sem_subtyp_typ (ih_body hT1b hT2b)

theorem sem_typ_subtyp
  {C1 C2 : CaptureSet s} {E1 E2 : Ty .exi s}
  (ht : SemanticTyping C1 Γ e E1)
  (hsubcapt : Subcapt Γ C1 C2)
  (hsubtyp : Subtyp Γ E1 E2)
  (_hclosed_C1 : C1.IsClosed) (hclosed_E1 : E1.IsClosed)
  (_hclosed_C2 : C2.IsClosed) (hclosed_E2 : E2.IsClosed) :
  SemanticTyping C2 Γ e E2 := by
  intro ρ k st m htyping hdsep hcompat2
  -- Capture coercion `C1 ⊆ C2` (subcapture) and type coercion `E1 <: E2` (subtype).
  have hsubC : C1.denot ρ m ⊆ C2.denot ρ m := fundamental_subcapt hsubcapt ρ k st m htyping
  have hcompat1 : m.is_compatible (C1.denot ρ m) := Memory.is_compatible_subset hsubC hcompat2
  have hsub_E := fundamental_subtyp hclosed_E1 hclosed_E2 hsubtyp ρ k st m htyping hdsep
  have htd := ht ρ k st m htyping hdsep hcompat1
  simp only [Ty.exi_exp_denot] at htd ⊢
  intro hmt
  refine eval_post_monotonic_general ?_ (htd hmt)
  intro m' _hsub t v hpost hguard
  obtain ⟨htr, st', hwle', hmt', hval1, hpb, hwl⟩ := hpost hguard
  exact ⟨TraceOk.mono hsubC htr, st', hwle', hmt',
    hsub_E (k - t.readCount) (Nat.sub_le k t.readCount) st' m' hwle' v hval1,
    pack_bound_mono hsubC (Memory.subsumes_refl m) hpb, hwl⟩

lemma simple_val_not_pack {e : Exp s} {n : Nat}
  (hsimple : e.IsSimpleVal)
  (hpack : e.IsPack n) : False := by
  cases hsimple <;> cases hpack

lemma resolve_pack_eq {e : Exp {}} {m : Memory} {n : Nat}
  {CS : List.Vector (CaptureSet {}) n} {x : Var .var {}}
  (hres : resolve m.heap e = some (.pack CS x))
  (hpack : e.IsPack n) : e = .pack CS x := by
  cases hpack
  rename_i cs y
  change some (Exp.pack cs y) = some (Exp.pack CS x) at hres
  cases hres
  rfl

theorem resolve_is_pack {e : Exp {}} {m : Memory} {n : Nat} {v : Exp {}}
  (hres : resolve m.heap e = some v)
  (hv : v.IsPack n) : e.IsPack n := by
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

/-- Every `.drop`-mode peak of a budget whose consumed peaks are droppable is
a `can_drop` variable. The `droppable` premise is the `unpack` rule's
anti-laundering side condition (`((C1.peakset Γ).consumed).droppable Γ`):
without it, `subtyp`'s `Subcapt` could widen a budget with a `drop·c` atom
over an `access_only` variable `c` aliasing a live droppable, and the
witness-separation argument below would lose its anchor. Leaf-generated
budgets satisfy the premise by construction (`drop`/`pack` carry `droppable`
premises). -/
theorem consumed_peaks_droppable {Γ : Ctx s} {C : CaptureSet s} {c : BVar s .cvar}
    (hdrop : ((C.peakset Γ).consumed).droppable Γ)
    (hsub : (CaptureSet.cvar .drop c) ⊆ CaptureSet.peaks Γ C) :
    Γ.lookup_authority c = .can_drop :=
  hdrop .drop c (CaptureSet.cvar_drop_subset_consumed hsub)

/-- General `EnvSepWf` builder for an `extend_cvars` extension at `.can_drop`.
    Requires: the base env is separated (`hbase`); each new evidence is disjoint
    from every droppable *base* cvar (`hcross`); and the evidences are pairwise
    disjoint (`hCSdisj`).  Proved by induction on the vector, peeling the head
    binding and classifying every inner cvar via `extend_cvars_lookup_cvar`. -/
theorem TypeEnv.EnvSepWf.extend_cvars_gen {s : Sig} {base : TypeEnv s} {m : Memory} :
    {n : Nat} → {CS : List.Vector (CaptureSet {}) n} →
    base.EnvSepWf →
    (∀ cs ∈ CS.toList, ∀ (c0 : BVar s .cvar),
      base.lookup_cvar_auth c0 = .can_drop →
      CapabilitySet.disjoint (cs.ground_denot m) (base.lookup_cvar c0).2) →
    CS.toList.Pairwise (fun c1 c2 =>
      CapabilitySet.disjoint (c1.ground_denot m) (c2.ground_denot m)) →
    (TypeEnv.extend_cvars base m .can_drop CS).EnvSepWf
  | 0, _, hbase, _, _ => hbase
  | n + 1, CS, hbase, hcross, hCSdisj => by
    obtain ⟨l, hl⟩ := CS
    cases l with
    | nil => cases hl
    | cons hd tl =>
      have hl' : tl.length = n := by simpa using hl
      have hpw : List.Pairwise
          (fun c1 c2 => CapabilitySet.disjoint (c1.ground_denot m) (c2.ground_denot m))
          (hd :: tl) := hCSdisj
      rw [List.pairwise_cons] at hpw
      obtain ⟨hhd_tl, htl_pw⟩ := hpw
      have hinner_wf :
          (TypeEnv.extend_cvars base m .can_drop ⟨tl, hl'⟩).EnvSepWf :=
        TypeEnv.EnvSepWf.extend_cvars_gen (CS := ⟨tl, hl'⟩) hbase
          (fun cs hmem => hcross cs (List.mem_cons_of_mem hd hmem)) htl_pw
      have hkey : ∀ (c2' : BVar (Sig.extendCVars s n) .cvar),
          (TypeEnv.extend_cvars base m .can_drop ⟨tl, hl'⟩).lookup_cvar_auth c2' = .can_drop →
          CapabilitySet.disjoint (hd.ground_denot m)
            ((TypeEnv.extend_cvars base m .can_drop ⟨tl, hl'⟩).lookup_cvar c2').2 := by
        intro c2' hauth
        obtain ⟨cs, hcs_mem, hlk, _⟩ | ⟨c0, hlk, hauth0⟩ :=
          TypeEnv.extend_cvars_lookup_cvar (m := m) (a := .can_drop) (CS := ⟨tl, hl'⟩)
            (env := base) c2'
        · rw [hlk]; exact hhd_tl cs hcs_mem
        · rw [hlk]; exact hcross hd List.mem_cons_self c0 (hauth0 ▸ hauth)
      have henv_eq : TypeEnv.extend_cvars base m .can_drop ⟨hd :: tl, hl⟩ =
          (TypeEnv.extend_cvars base m .can_drop ⟨tl, hl'⟩).extend_cvar hd
            (cap := hd.ground_denot m) (a := .can_drop) := rfl
      rw [henv_eq]
      intro c1 c2 hne h1 h2
      cases c1 with
      | here =>
        cases c2 with
        | here => exact absurd rfl hne
        | there c2' => exact hkey c2' h2
      | there c1' =>
        cases c2 with
        | here => exact (hkey c1' h1).symm
        | there c2' =>
          exact hinner_wf c1' c2' (fun heq => hne (congrArg BVar.there heq)) h1 h2

/-- `EnvSepWf` for the continuation environment of `unpack`: the killed base env
    extended with the `n` pack witnesses at `.can_drop`.  Each witness is disjoint
    from every surviving droppable base cvar (`pack_bound` → the shared location is
    `C1`-drop-covered, hence traces to a `kill_peaks`-killed variable), and the
    witnesses are pairwise disjoint by the pack's `PairwiseSep` evidence. -/
theorem TypeEnv.EnvSepWf.extend_cvars_can_drop
    {s : Sig} {Γ : Ctx s} {env : TypeEnv s} {k : Nat} {st : StoreTyping k}
    {store m1 : Memory} {C1 : CaptureSet s} {n : Nat}
    {CS : List.Vector (CaptureSet {}) n} {x0 : Var .var {}}
    (hts : EnvTyping Γ env k st store)
    (hΓ : Γ.IsClosed)
    (hdsep : env.EnvSepWf)
    (hclosed_C1 : C1.IsClosed)
    (hdrop : ((C1.peakset Γ).consumed).droppable Γ)
    (hpb : pack_bound (C1.denot env store) store (.pack CS x0) m1)
    (hCSdisj : CS.toList.Pairwise (fun c1 c2 =>
      CapabilitySet.disjoint (c1.ground_denot m1) (c2.ground_denot m1))) :
    (TypeEnv.extend_cvars (env.kill_peaks ((C1.peakset Γ).consumed)) m1 .can_drop CS).EnvSepWf := by
  refine TypeEnv.EnvSepWf.extend_cvars_gen (TypeEnv.EnvSepWf.kill_peaks hdsep) ?_ hCSdisj
  have hlk_eq : ∀ (c' : BVar s .cvar),
      (env.kill_peaks ((C1.peakset Γ).consumed)).lookup_cvar c' = env.lookup_cvar c' := by
    intro c'; simp only [TypeEnv.kill_peaks]; exact TypeEnv.kill_peaks_cs_lookup_cvar env _ c'
  intro cs hcs_mem c2' h2 mu1 mu2 l hm1 hm2
  have h2' : env.lookup_cvar_auth c2' = .can_drop :=
    TypeEnv.kill_peaks_cs_can_drop_inv h2
  rw [hlk_eq] at hm2
  have hpres : store.heap l ≠ none := by
    rw [typed_env_cvar_cap_eq hts c2', CaptureSet.ground_denot_eq_reachability] at hm2
    exact CaptureSet.reachability_dom hm2
  have hm1' : (cs.reachability m1).hasmem mu1 l := by
    rw [← CaptureSet.ground_denot_eq_reachability]; exact hm1
  have hm1'' : ((CaptureSet.unionAll CS).reachability m1).hasmem mu1 l :=
    CaptureSet.hasmem_reachability_unionAll hcs_mem hm1'
  rcases hpb n CS x0 rfl mu1 l hm1'' with ⟨_, hdroplcov⟩ | hfresh
  · obtain ⟨c, hsub_c, mu', hmemc⟩ :=
      drop_denot_peak hts hΓ (envtyping_lookup_cvar_drop_free hts) hclosed_C1 hdroplcov
    have hsub_K : (CaptureSet.cvar .drop c) ⊆ ((C1.peakset Γ).consumed).cs :=
      CaptureSet.cvar_drop_subset_consumed hsub_c
    have hc_auth : env.lookup_cvar_auth c = .can_drop := by
      rw [envtyping_lookup_cvar_auth hts]; exact hdrop .drop c hsub_K
    have hc_killed :
        (env.kill_peaks ((C1.peakset Γ).consumed)).lookup_cvar_auth c = .killed := by
      simp only [TypeEnv.kill_peaks]; exact TypeEnv.kill_peaks_cs_killed hsub_K
    have hne : c ≠ c2' := by rintro rfl; rw [hc_killed] at h2; cases h2
    exact hdsep c c2' hne hc_auth h2' mu' mu2 l hmemc hm2
  · exact hpres hfresh

/-- Extending with a capture variable preserves `is_implying_wf` (type variables,
    the only thing `is_implying_wf` consults, are untouched by a cvar extension). -/
theorem TypeEnv.is_implying_wf.extend_cvar {s : Sig} {env : TypeEnv s}
    {cs : CaptureSet {}} {cap : CapabilitySet} {a : Authority}
    (h : env.is_implying_wf) : (env.extend_cvar cs cap a).is_implying_wf := by
  intro X; cases X with | there X' => exact h X'

/-- `n`-ary iteration of `is_implying_wf.extend_cvar`. -/
theorem TypeEnv.is_implying_wf.extend_cvars {s : Sig} {env : TypeEnv s}
    {m : Memory} {a : Authority} :
    {n : Nat} → {CS : List.Vector (CaptureSet {}) n} →
    env.is_implying_wf → (TypeEnv.extend_cvars env m a CS).is_implying_wf
  | 0, _, h => h
  | _ + 1, CS, h =>
    (TypeEnv.is_implying_wf.extend_cvars (CS := List.Vector.tail CS) h).extend_cvar

/-- `is_compatible` depends only on the *locations* of a capability set: if every
    member location of `C` is a member location of `D` (at some mode), then
    compatibility with `D` transfers to `C`.  Generalises `is_compatible_subset`
    (which needs a structural `Subset`) to a pointwise location cover. -/
theorem Memory.is_compatible_of_loc {m : Memory} {C D : CapabilitySet}
    (hCD : ∀ mu l, C.hasmem mu l → ∃ mu', D.hasmem mu' l)
    (hD : m.is_compatible D) : m.is_compatible C := by
  intro mu l b ℓ hmem hheap
  obtain ⟨mu', hmem'⟩ := hCD mu l hmem
  exact hD mu' l b ℓ hmem' hheap

/-- The `n` fresh capture variables of an unpack, evaluated in the witness-extended
    environment `extend_cvars env m0 a CS`, denote exactly the (access-`ε`-inert)
    union of the `n` evidences — i.e. the ground reachability of `unionAll CS`.  The
    head binder looks up to its evidence `hd` (`ε` is inert at ground level); the tail
    reindexes through `Rename.succ` back to the smaller `extend_cvars`. -/
private theorem freshCVars_denot_eq_unionAll {s : Sig} {env : TypeEnv s}
    {m0 : Memory} {a : Authority} :
    {n : Nat} → {CS : List.Vector (CaptureSet {}) n} → (m : Memory) →
    ((CaptureSet.freshCVars n).subst
        (Subst.from_TypeEnv (TypeEnv.extend_cvars env m0 a CS))).ground_denot m
      = (CaptureSet.unionAll CS).ground_denot m
  | 0, _, _ => rfl
  | n + 1, CS, m => by
    obtain ⟨l, hl⟩ := CS
    cases l with
    | nil => cases hl
    | cons hd tl =>
      have hl' : tl.length = n := by simpa using hl
      have ih := freshCVars_denot_eq_unionAll (env := env) (m0 := m0) (a := a)
        (CS := (⟨tl, hl'⟩ : List.Vector (CaptureSet {}) n)) m
      have hreindex :
          ((CaptureSet.freshCVars n).rename Rename.succ).subst
            (Subst.from_TypeEnv (TypeEnv.extend_cvars env m0 a ⟨hd :: tl, hl⟩))
          = (CaptureSet.freshCVars n).subst
            (Subst.from_TypeEnv (TypeEnv.extend_cvars env m0 a ⟨tl, hl'⟩)) := by
        rw [CaptureSet.rename_subst_comm]
        congr 1
      change ((hd.applyAccess (.M .epsilon)).ground_denot m)
          ∪ ((((CaptureSet.freshCVars n).rename Rename.succ).subst
              (Subst.from_TypeEnv (TypeEnv.extend_cvars env m0 a ⟨hd :: tl, hl⟩))).ground_denot m)
        = (hd.ground_denot m)
          ∪ ((CaptureSet.unionAll (⟨tl, hl'⟩ : List.Vector (CaptureSet {}) n)).ground_denot m)
      rw [hreindex, ih, captureSet_ground_denot_applyAccess_comm]
      simp only [CapabilitySet.applyAccess_M, CapabilitySet.applyMut]

/-- Semantic typing for `unpack`.

    Frame: `eval_unpack` supplies `FrameLive store t1 m1` from the real `e1`-run
    (`BigStep.frameLive`).

    Witness liveness: the continuation's `m1.is_compatible (cs.reachability m1 ∪
    to_drop)` is supplied by `Q1`'s `witness_live` conjunct. A value denotation
    cannot carry liveness (it is anti-monotonic), but the existential *expression*
    postcondition can — established at the pack-creation site
    (`sem_typ_pack`/`sem_typ_alloc`) from `AccessOnly` evidence + budget
    compatibility and threaded through `exi_exp_denot`.

    Witness access-coverage: the pack rule's budget `C ∪ C.applyAccess .drop`
    makes `pack_bound` record each witness cell at its natural access mode
    (`R.covers mu l`) alongside `.drop`. The reassembly `TraceOk (t1 ++ t2)
    ((C1 ∪ C2).denot)` follows from trace machinery (`TraceOkFrom.append_seq`):
    a non-fresh witness access touch is covered by `C1` at access, `.drop` touches
    by `C1.drop`, and fresh cells are `allocd t1`.

    Fresh-witness provenance: a store-fresh witness cell touched by `t2` must be
    `allocd t1`. Rather than a capability-reachability wf invariant, read the cell
    type from the run: `BigStep.trace_cells_cap` proves every cell a trace
    accesses/deallocates is a capability, and the body `Eval` is built manually to
    expose the body run, so a touched fresh witness cell is a capability in `m'`,
    hence in `m1` (`lookup_down` + `reachability_dom`), hence `allocd t1`. -/
theorem sem_typ_unpack
  {C1 C2 : CaptureSet s} {Γ : Ctx s} {t : Exp s}
  {n : Nat} {T : Ty .capt (s.extendCVars n)}
  {u : Exp ((s.extendCVars n),x)} {U : Ty .exi s}
  (hseq : SeqComp Γ C1 C2)
  (hdrop : ((C1.peakset Γ).consumed).droppable Γ)
  (hΓ : Γ.IsClosed)
  (hclosed_C1 : C1.IsClosed)
  (hclosed_C2 : C2.IsClosed)
  (ht : SemanticTyping C1 Γ t (.exi n T))
  (hu : SemanticTyping
        (((C2.rename (Rename.weakenCVars n)).rename Rename.succ)
          ∪ ((CaptureSet.freshCVars n).rename Rename.succ)
          ∪ (((CaptureSet.freshCVars n).rename Rename.succ).applyAccess .drop))
        ((Ctx.extendCVars .can_drop (Γ.kill_peaks ((C1.peakset Γ).consumed)) n),x:T) u
        ((U.rename (Rename.weakenCVars n)).rename Rename.succ)) :
  SemanticTyping (C1 ∪ C2) Γ (Exp.unpack n t u) U := by
  intro env k st store hts hdsep hcompat
  set K := (C1.peakset Γ).consumed with hKdef
  set Cbud := ((C2.rename (Rename.weakenCVars n)).rename Rename.succ)
    ∪ ((CaptureSet.freshCVars n).rename Rename.succ)
    ∪ (((CaptureSet.freshCVars n).rename Rename.succ).applyAccess .drop) with hCbud
  simp only [Ty.exi_exp_denot, List.empty_eq]
  intro hmt
  simp only [Exp.subst]
  -- Budgets.
  have hunion : (C1 ∪ C2).denot env store = C1.denot env store ∪ C2.denot env store := rfl
  have hcompat' : store.is_compatible (C1.denot env store ∪ C2.denot env store) := hunion ▸ hcompat
  have hsubC1 : C1.denot env store ⊆ (C1 ∪ C2).denot env store :=
    CapabilitySet.Subset.union_right_left
  have hsubC2 : C2.denot env store ⊆ (C1 ∪ C2).denot env store :=
    CapabilitySet.Subset.union_right_right
  have hcompat_C1 : store.is_compatible (C1.denot env store) :=
    Memory.is_compatible_union_left hcompat'
  have hcompat_C2 : store.is_compatible (C2.denot env store) :=
    Memory.is_compatible_union_right hcompat'
  -- `t`'s evaluation.
  have he1 := ht env k st store hts hdsep hcompat_C1
  simp only [Ty.exi_exp_denot] at he1
  have he1' := he1 hmt
  -- Sequential composition and framing prep (mirrors `sem_typ_letin`).
  have hseqcomp : (C1.denot env store).SeqComp (C2.denot env store) :=
    captureSet_seqcomp_denot hts hΓ hdsep hseq
  have hpresent_C2 : ∀ mu l, (C2.denot env store).hasmem mu l → store.heap l ≠ none := by
    intro mu l hmem
    simp only [CaptureSet.denot, CaptureSet.ground_denot_eq_reachability] at hmem
    exact CaptureSet.reachability_dom hmem
  have hnodrop_C2_t1 : ∀ {t1 : Trace}, TraceOk t1 (C1.denot env store) →
      ∀ mu l, (C2.denot env store).hasmem mu l → ¬ Trace.extDrops t1 l := by
    intro t1 hok1 mu l hmem hd
    obtain ⟨mu', hm', hle⟩ :=
      CapabilitySet.covers_imp_exists_hasmem (TraceOk.drop_covers_of_extDrops hok1 hd)
    cases hle
    exact hseqcomp mu l hm' hmem
  refine Eval.eval_unpack he1'
    (fun t v m' hover hguard => absurd hguard (Nat.not_lt.mpr hover))
    (fun {t1 m1 v} hbud hq1 => ?_)
    (fun {t1 m1 x0 cs} hbud hsub_m1 hframe hallocd _hwf_x _hwf_cs hq1 => ?_)
  · -- h_nonstuck: the `t`-result is a pack + heap-wf.
    obtain ⟨_, st1, _, _, hval1, _, _⟩ := hq1 hbud
    simp only [Ty.exi_val_denot] at hval1
    obtain ⟨CS, x, heq, hCSwf, _, _, hvalT⟩ := hval1
    have hvpack : v.IsPack n := resolve_is_pack heq Exp.IsPack.pack
    have hveq : v = .pack CS x := resolve_pack_eq heq hvpack
    subst hveq
    refine ⟨Exp.IsPack.pack, Exp.WfInHeap.wf_pack hCSwf ?_⟩
    have hiw : (TypeEnv.extend_cvars env m1 .can_drop CS).is_implying_wf :=
      (typed_env_is_implying_wf hts).extend_cvars
    cases val_denot_implies_wf hiw T (k - t1.readCount) st1 m1 (.var x) hvalT with
    | wf_var hx => exact hx
  · -- h_val: run `u` in the witness-extended, killed environment and reassemble.
    obtain ⟨hok1, st1, hwle1, hmt1, hval1, hpb1, hwl1⟩ := hq1 hbud
    have hres : resolve m1.heap (Exp.pack cs x0) = some (.pack cs x0) := rfl
    simp only [Ty.exi_val_denot] at hval1
    obtain ⟨CS, xx, hres_eq, hCSwf, hCSdf, hCSdisj, hvalT⟩ := hval1
    rw [hres] at hres_eq
    obtain ⟨rfl, rfl⟩ : cs = CS ∧ x0 = xx := by
      have h := Option.some.inj hres_eq
      rw [Exp.pack.injEq] at h
      exact ⟨eq_of_heq h.2.1, h.2.2⟩
    cases x0 with
    | bound b => cases b
    | free l0 =>
    -- Environment reassembly (at the decremented index `k − t1.readCount`, where `t`'s
    -- post-world `st1` lives).
    have hts1 : EnvTyping Γ env (k - t1.readCount) st1 m1 :=
      env_typing_worldle_trunc (Nat.sub_le k t1.readCount) hts hwle1
    have henv_kill : EnvTyping (Γ.kill_peaks K) (env.kill_peaks K) (k - t1.readCount) st1 m1 :=
      EnvTyping.kill_peaks K hts1
    set ENVCV := TypeEnv.extend_cvars (env.kill_peaks K) m1 .can_drop cs
      with hENVCVdef
    have henv_cvar : EnvTyping (Ctx.extendCVars .can_drop (Γ.kill_peaks K) n) ENVCV
        (k - t1.readCount) st1 m1 :=
      EnvTyping.extend_cvars henv_kill hCSwf hCSdf
    have hvalT_kill : Ty.val_denot ENVCV T (k - t1.readCount) st1 m1 (.var (.free l0)) := by
      have hEnvEq : ENVCV
          = (TypeEnv.extend_cvars env m1 .can_drop cs).kill_peaks_cs
              (K.cs.rename (Rename.weakenCVars n)) :=
        TypeEnv.kill_peaks_cs_extend_cvars (K := K.cs)
      rw [hEnvEq]
      exact IDenot.equiv_ltr
        (kill_peaks_cs_val_denot (env := TypeEnv.extend_cvars env m1 .can_drop cs)
          (K := K.cs.rename (Rename.weakenCVars n)) T) hvalT
    set PS := compute_peakset ENVCV T.captureSet with hPSdef
    set ENV2 := ENVCV.extend_var l0 PS with hENV2def
    have henv2 : EnvTyping ((Ctx.extendCVars .can_drop (Γ.kill_peaks K) n),x:T) ENV2
        (k - t1.readCount) st1 m1 :=
      ⟨hvalT_kill, (compute_peakset_correct henv_cvar T.captureSet).symm, henv_cvar⟩
    -- OBSTACLE 1: `EnvSepWf` for the continuation environment.
    have hdsep2 : ENV2.EnvSepWf :=
      (TypeEnv.EnvSepWf.extend_cvars_can_drop hts hΓ hdsep hclosed_C1 hdrop hpb1
        hCSdisj).extend_var
    -- The three `hu`-budget summands, evaluated at `ENV2`, `m1`.
    have hD_C2 : CaptureSet.denot ENV2 ((C2.rename (Rename.weakenCVars n)).rename Rename.succ) m1
        = C2.denot env store := by
      have e1 := rebind_captureset_denot
        (Rebind.weaken (env := ENVCV) (x := l0) (ps := PS)) (C2.rename (Rename.weakenCVars n))
      rw [← hENV2def] at e1
      have e2 := rebind_captureset_denot
        (Rebind.cweakenCVars (env := env.kill_peaks K) (m := m1) (a := .can_drop) (CS := cs)) C2
      rw [← hENVCVdef] at e2
      have e3 : CaptureSet.denot (env.kill_peaks K) C2 = CaptureSet.denot env C2 := by
        simp only [CaptureSet.denot, TypeEnv.kill_peaks, Subst.from_TypeEnv_kill_peaks_cs]
      have hfun : CaptureSet.denot ENV2 ((C2.rename (Rename.weakenCVars n)).rename Rename.succ)
          = CaptureSet.denot env C2 := e1.symm.trans (e2.symm.trans e3)
      calc CaptureSet.denot ENV2 ((C2.rename (Rename.weakenCVars n)).rename Rename.succ) m1
          = CaptureSet.denot env C2 m1 := congrFun hfun m1
        _ = C2.denot env store := (closed_capture_denot_monotonic hclosed_C2 hts hsub_m1).symm
    have hD_fresh : CaptureSet.denot ENV2 ((CaptureSet.freshCVars n).rename Rename.succ) m1
        = (CaptureSet.unionAll cs).ground_denot m1 := by
      have e1 := rebind_captureset_denot
        (Rebind.weaken (env := ENVCV) (x := l0) (ps := PS)) (CaptureSet.freshCVars n)
      rw [← hENV2def] at e1
      have e1m : CaptureSet.denot ENV2 ((CaptureSet.freshCVars n).rename Rename.succ) m1
          = CaptureSet.denot ENVCV (CaptureSet.freshCVars n) m1 := (congrArg (· m1) e1).symm
      rw [e1m]
      simp only [CaptureSet.denot, hENVCVdef]
      exact freshCVars_denot_eq_unionAll m1
    have hD_drop_fresh :
        CaptureSet.denot ENV2 (((CaptureSet.freshCVars n).rename Rename.succ).applyAccess .drop) m1
        = ((CaptureSet.unionAll cs).ground_denot m1).to_drop := by
      have key : (((CaptureSet.freshCVars n).rename Rename.succ).subst
            (Subst.from_TypeEnv ENV2)).ground_denot m1
          = (CaptureSet.unionAll cs).ground_denot m1 := hD_fresh
      simp only [CaptureSet.denot, CaptureSet.applyAccess_subst,
        captureSet_ground_denot_applyAccess_comm]
      rw [CapabilitySet.applyAccess_drop]
      exact congrArg (·.to_drop) key
    have hbudget_eq : CaptureSet.denot ENV2 Cbud m1
        = (C2.denot env store ∪ (CaptureSet.unionAll cs).ground_denot m1)
          ∪ ((CaptureSet.unionAll cs).ground_denot m1).to_drop := by
      change (CaptureSet.denot ENV2 ((C2.rename (Rename.weakenCVars n)).rename Rename.succ) m1
          ∪ CaptureSet.denot ENV2 ((CaptureSet.freshCVars n).rename Rename.succ) m1)
          ∪ CaptureSet.denot ENV2
              (((CaptureSet.freshCVars n).rename Rename.succ).applyAccess .drop) m1 = _
      rw [hD_C2, hD_fresh, hD_drop_fresh]
    -- Compatibility of the `hu` budget at `m1`.
    have hc_C2 : m1.is_compatible (C2.denot env store) :=
      Memory.is_compatible_frame hcompat_C2 hpresent_C2 hframe hsub_m1 (hnodrop_C2_t1 hok1)
    have hc_wit : m1.is_compatible ((CaptureSet.unionAll cs).ground_denot m1) := by
      have h := hwl1 n cs (.free l0) rfl
      rwa [← CaptureSet.ground_denot_eq_reachability] at h
    have hcompat2 : m1.is_compatible (CaptureSet.denot ENV2 Cbud m1) := by
      rw [hbudget_eq]
      intro mu l b ℓ hmem hheap
      cases hmem with
      | left h12 =>
        cases h12 with
        | left hC2 => exact hc_C2 mu l b ℓ hC2 hheap
        | right hEps => exact hc_wit mu l b ℓ hEps hheap
      | right hDrop =>
        exact Memory.is_compatible_of_loc
          (fun _ _ h => (CapabilitySet.hasmem_to_drop_imp h).2) hc_wit mu l b ℓ hDrop hheap
    -- The re-bucketing lemmas: every `hu`-budget member is `(C1∪C2)`-covered/dropped or fresh.
    have hbucket_cov : ∀ mu l, (CaptureSet.denot ENV2 Cbud m1).hasmem mu l →
        ((C1 ∪ C2).denot env store).covers mu l ∨ (m1.heap l ≠ none ∧ store.lookup l = none) := by
      intro mu l hmem
      rw [hbudget_eq] at hmem
      cases hmem with
      | left h12 =>
        cases h12 with
        | left hC2 =>
          exact Or.inl (CapabilitySet.covers_mono hsubC2 (CapabilitySet.hasmem_implies_covers hC2))
        | right hEps =>
          have hreach : ((CaptureSet.unionAll cs).reachability m1).hasmem mu l :=
            CaptureSet.ground_denot_eq_reachability (CaptureSet.unionAll cs) m1 ▸ hEps
          rcases hpb1 n cs (.free l0) rfl mu l hreach with ⟨hcov, _⟩ | hfresh
          · exact Or.inl (CapabilitySet.covers_mono hsubC1 hcov)
          · exact Or.inr ⟨CaptureSet.reachability_dom hreach, hfresh⟩
      | right hDrop =>
        obtain ⟨rfl, mu', hmem'⟩ := CapabilitySet.hasmem_to_drop_imp hDrop
        have hreach : ((CaptureSet.unionAll cs).reachability m1).hasmem mu' l :=
          CaptureSet.ground_denot_eq_reachability (CaptureSet.unionAll cs) m1 ▸ hmem'
        rcases hpb1 n cs (.free l0) rfl mu' l hreach with ⟨_, hdroplcov⟩ | hfresh
        · exact Or.inl (CapabilitySet.hasmem_implies_covers
            (hasmem_drop_of_subset hsubC1 hdroplcov))
        · exact Or.inr ⟨CaptureSet.reachability_dom hreach, hfresh⟩
    have hbucket_drop : ∀ l, (CaptureSet.denot ENV2 Cbud m1).hasmem .drop l →
        ((C1 ∪ C2).denot env store).hasmem .drop l ∨
          (m1.heap l ≠ none ∧ store.lookup l = none) := by
      intro l hmem
      rw [hbudget_eq] at hmem
      cases hmem with
      | left h12 =>
        cases h12 with
        | left hC2 => exact Or.inl (hasmem_drop_of_subset hsubC2 hC2)
        | right hEps =>
          exact absurd hEps (CaptureSet.unionAll_ground_denot_drop_free hCSdf l)
      | right hDrop =>
        obtain ⟨_, mu', hmem'⟩ := CapabilitySet.hasmem_to_drop_imp hDrop
        have hreach : ((CaptureSet.unionAll cs).reachability m1).hasmem mu' l :=
          CaptureSet.ground_denot_eq_reachability (CaptureSet.unionAll cs) m1 ▸ hmem'
        rcases hpb1 n cs (.free l0) rfl mu' l hreach with ⟨_, hdroplcov⟩ | hfresh
        · exact Or.inl (hasmem_drop_of_subset hsubC1 hdroplcov)
        · exact Or.inr ⟨CaptureSet.reachability_dom hreach, hfresh⟩
    -- Invoke `hu` and rewrite the continuation expression.
    have he2 := hu ENV2 (k - t1.readCount) st1 m1 henv2 hdsep2 hcompat2
    simp only [Ty.exi_exp_denot] at he2
    have he2' := he2 hmt1
    have hexpr :
        (u.subst ((Subst.from_TypeEnv env).liftCVars n).lift).subst (Subst.unpack cs (.free l0))
        = u.subst (Subst.from_TypeEnv ENV2) := by
      rw [hENV2def, hENVCVdef]
      rw [show (Subst.from_TypeEnv env) = Subst.from_TypeEnv (env.kill_peaks K) from
            (Subst.from_TypeEnv_kill_peaks_cs).symm, Exp.subst_comp]
      exact congrArg (u.subst ·) (Subst.from_TypeEnv_weaken_unpack (ps := PS))
    -- Transport the goal along `hexpr`, then build the `Eval` manually to expose the body
    -- run (needed for `trace_cells_cap`).
    refine hexpr ▸ ?_
    refine ⟨he2'.1, ?_⟩
    intro t2 vv m' hbs hguard
    have hbud2 : t2.readCount < k - t1.readCount := by
      rw [Trace.readCount_append] at hguard; omega
    obtain ⟨hok2, st'', hwle2, hmt2, hval2, hpb2, hwl2⟩ := he2'.2 t2 vv m' hbs hbud2
    -- Index bridge: `u`'s post lands at `(k − t1.readCount) − t2.readCount`, which equals the
    -- compound decrement `k − (t1 ++ t2).readCount`.
    have hidx_eq : k - (t1 ++ t2).readCount = (k - t1.readCount) - t2.readCount := by
      rw [Trace.readCount_append, Nat.sub_sub]
    have hjk : k - (t1 ++ t2).readCount ≤ (k - t1.readCount) - t2.readCount := Nat.le_of_eq hidx_eq
    have h2le : (k - t1.readCount) - t2.readCount ≤ k - t1.readCount := Nat.sub_le _ _
    -- Compose `t`'s world-step (`hwle1`, descended) with `u`'s (`hwle2`), then descend once more.
    have hwle_fin : WorldLe (st''.trunc hjk) m'
        (st.trunc (Nat.sub_le k (t1 ++ t2).readCount)) store := by
      have hwle1_desc := WP.WorldLe.trunc h2le hwle1
      rw [WP.World.trunc_trunc] at hwle1_desc
      have hwle_comp := WorldLe.trans hwle1_desc hwle2
      have h := WP.WorldLe.trunc hjk hwle_comp
      rw [WP.World.trunc_trunc] at h
      exact h
    refine ⟨?_, st''.trunc hjk, hwle_fin, MemTyped_trunc hjk hmt2, ?_, ?_, hwl2⟩
    · -- OBSTACLE 2: the trace bound `TraceOk (t1 ++ t2) ((C1∪C2).denot env store)`.
      have hrebucket : ∀ mode l, Trace.touched t2 l →
          (CaptureSet.denot ENV2 Cbud m1).covers mode l →
          ((C1 ∪ C2).denot env store).covers mode l ∨ l ∈ Trace.allocList t1 := by
        intro mode l htouched hcov
        obtain ⟨mu', hm_b, hle⟩ := CapabilitySet.covers_imp_exists_hasmem hcov
        rcases hbucket_cov mu' l hm_b with hRcov | ⟨hm1pres, hfresh_store⟩
        · exact Or.inl (CapabilitySet.covers_weaken hRcov hle)
        · right
          rw [Trace.mem_allocList]
          obtain ⟨c', hc'⟩ := BigStep.trace_cells_cap hbs l htouched
          cases hcell : m1.heap l with
          | none => exact absurd hcell hm1pres
          | some cell_small =>
            obtain ⟨w', hw', hsubcell⟩ := hbs.subsumes l cell_small hcell
            have hweq : w' = .capability c' := Option.some.inj (hw'.symm.trans hc')
            subst hweq
            cases cell_small with
            | capability c0 => exact hallocd hfresh_store hcell
            | val _ => simp [Cell.subsumes] at hsubcell
            | masked => simp [Cell.subsumes] at hsubcell
      refine TraceOkFrom.append_seq (TraceOk.mono hsubC1 hok1) ?_
      have htr2 := TraceOkFrom.translate (S := Trace.allocList t1) hok2 hrebucket
      simpa using htr2
    · -- Value: un-weaken (var, then the `n` cvars) and un-kill back to `env`, then descend index.
      have hv1 := IDenot.equiv_rtl
        (weaken_exi_val_denot (env := ENVCV) (T := U.rename (Rename.weakenCVars n))
          (x := l0) (ps := PS)) hval2
      have hv2 := IDenot.equiv_rtl
        (cweakenCVars_exi_val_denot (env := env.kill_peaks K) (m := m1)
          (a := .can_drop) (CS := cs) (T := U)) hv1
      have hv3 := IDenot.equiv_rtl (kill_peaks_cs_exi_val_denot (env := env) (K := K.cs) U) hv2
      exact exi_val_denot_down_trunc (typed_env_is_downward_closed hts) U hjk vv hv3
    · -- `pack_bound`: re-bucket the outer witness through the `hu`-budget bound.
      intro n_v cs_v x_v heq_v mu l hmem_l
      rcases hpb2 n_v cs_v x_v heq_v mu l hmem_l with ⟨hcov_b, hdrop_b⟩ | hfresh_m1
      · obtain ⟨mu', hm_b, hle⟩ := CapabilitySet.covers_imp_exists_hasmem hcov_b
        rcases hbucket_cov mu' l hm_b with hRcov | ⟨_, hfresh_store⟩
        · rcases hbucket_drop l hdrop_b with hRdrop | ⟨_, hfresh_store⟩
          · exact Or.inl ⟨CapabilitySet.covers_weaken hRcov hle, hRdrop⟩
          · exact Or.inr hfresh_store
        · exact Or.inr hfresh_store
      · exact Or.inr (Heap.none_of_subsumes_none hsub_m1 hfresh_m1)

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

-- peaks is monotonic w.r.t. CaptureSet.Subset
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

-- peaks commutes with rename and context extension (subset version)
theorem peaks_rename_succ_sub {Γ : Ctx s} {b : Binding s k} {C : CaptureSet s} :
  (C.peaks Γ).rename Rename.succ ⊆ (C.rename Rename.succ).peaks (Γ.push b) := by
  rw [CaptureSet.peaks_rename_succ_eq]
  exact .refl

-- peaks commutes with applyRO
theorem peaks_applyRO_comm (Γ : Ctx s) (C : CaptureSet s) :
  C.applyRO.peaks Γ = (C.peaks Γ).applyRO :=
  CaptureSet.peaks_applyRO_comm Γ C

-- peaks commutes with applyMut
theorem peaks_applyMut_comm {Γ : Ctx s} {C : CaptureSet s} {m : Mutability} :
  (C.applyMut m).peaks Γ = (C.peaks Γ).applyMut m := by
  cases m with
  | epsilon => simp only [CaptureSet.applyMut_epsilon]
  | ro =>
    simp only [CaptureSet.applyMut_ro]
    exact peaks_applyRO_comm Γ C

-- peaks is monotonic w.r.t. CaptureSet.CoveredBy
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

-- peaks commutes with rename and context extension (CoveredBy version)
theorem peaks_rename_succ_coveredby {Γ : Ctx s} {b : Binding s k} {C : CaptureSet s} :
  (C.peaks Γ).rename Rename.succ |>.CoveredBy <| (C.rename Rename.succ).peaks (Γ.push b) := by
  rw [CaptureSet.peaks_rename_succ_eq]
  exact .refl'

-- Subset implies CoveredBy (Subset is stricter)
theorem CaptureSet.Subset.coveredby {C1 C2 : CaptureSet s}
  (hsub : C1 ⊆ C2) : C1.CoveredBy C2 := by
  induction hsub with
  | refl => exact .refl'
  | empty => exact .empty
  | union_left _ _ ih1 ih2 => exact .union_left ih1 ih2
  | union_right_left _ ih => exact .union_right_left ih
  | union_right_right _ ih => exact .union_right_right ih

-- peaks of applyRO is covered by peaks
theorem peaks_applyRO_coveredby {Γ : Ctx s} {C : CaptureSet s} :
  (C.applyRO.peaks Γ).CoveredBy (C.peaks Γ) := by
  rw [<-CaptureSet.applyMut_ro, peaks_applyMut_comm]
  conv_rhs => rw [<-CaptureSet.applyMut_epsilon (cs := C.peaks Γ)]
  exact .refl Mutability.Le.ro_le

-- peaks respects applyRO monotonically (CoveredBy version)
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

-- variable subcaptures its type's capture set with matching mutability
theorem var_subcapt_captureSet_applyMut
  (hlk : Γ.LookupVar x T) :
  Subcapt Γ (.var (.M m) (.bound x)) (T.captureSet.applyMut m) := by
  cases m with
  | epsilon =>
    simpa [CaptureSet.applyMut] using (Subcapt.sc_var hlk)
  | ro =>
    simpa [CaptureSet.applyMut]
      using (Subcapt.sc_ro_mono (Subcapt.sc_var hlk))

-- applyMut is monotonic for CapabilitySet.Subset
theorem CapabilitySet.applyMut_mono {C1 C2 : CapabilitySet} {m : Mutability}
  (hsub : C1 ⊆ C2) : C1.applyMut m ⊆ C2.applyMut m := by
  cases m with
  | epsilon => simp only [CapabilitySet.applyMut]; exact hsub
  | ro => simp only [CapabilitySet.applyMut]; exact CapabilitySet.applyRO_mono hsub

-- for well-typed variables, the denotation is bounded by the type's capture set
theorem var_denot_subset_captureSet_denot
  (hlk : Γ.LookupVar x T)
  (henv : EnvTyping Γ env k st H) :
  (CaptureSet.var (.M m) (.bound x)).denot env H ⊆ (T.captureSet.applyMut m).denot env H := by
  have hreach := typed_env_lookup_var_reachability henv hlk
  have hreach_mut : (reachability_of_loc H.heap (env.lookup_var x).1).applyMut m ⊆
                    (T.captureSet.denot env H).applyMut m :=
    CapabilitySet.applyMut_mono (m := m) hreach
  simp only [CaptureSet.denot, CaptureSet.subst, Var.subst, Subst.from_TypeEnv,
             CaptureSet.ground_denot, CapabilitySet.applyAccess_M]
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
    (ht : HasType C Γ (Exp.var (.bound x)) E) :
    Γ.IsClosed := by
  generalize hexpr : Exp.var (Var.bound x) = e at ht
  induction ht
  case var hclosed hlk =>
    cases hexpr
    exact hclosed
  case subtyp _ _ _ _ _ ih => exact ih hexpr
  all_goals (cases hexpr)

/-- Inversion for the value denotation of a `modal` type.  Mirrors
`abs_val_denot_inv`: a modal value is a `boxed` value cell whose stored body, when
fired at any descended well-typed world that is compatible with its captures and
whose `Ψ`-capabilities satisfy the modal kind/non-interference obligations, runs to
the existential postcondition `exi_exp_denot env E R0`. -/
theorem modal_val_denot_inv {k : Nat} {st : StoreTyping k}
  (hv : Ty.val_denot env (.modal cs Ψ E) k st store (.var x)) :
  ∃ fx, x = .free fx
    ∧ ∃ cs0 sepctx0 t0 hval R,
      store.heap fx = some (Cell.val ⟨Exp.boxed cs0 sepctx0 t0, hval, R⟩)
    ∧ expand_captures store.heap cs0 ⊆ cs.denot env store
    ∧ (∀ (st' : StoreTyping k) (m' : Memory),
        WorldLe st' m' st store →
        MemTyped k st' m' →
        m'.is_compatible (expand_captures store.heap cs0) →
        (∀ C mode, Ψ.mutability.Has C mode → CapabilitySet.HasKind (C.denot env m') mode) →
        (∀ C1 C2, Ψ.sep.HasTwoDistinct C1 C2 →
          CapabilitySet.Noninterference (C1.denot env m') (C2.denot env m')) →
        Ty.exi_exp_denot env E (expand_captures store.heap cs0) k st' m' t0) := by
  cases x with
  | bound bx => cases bx
  | free fx =>
    simp only [Ty.val_denot] at hv
    obtain ⟨_hwf_e, _hwf_cs, cs0, sepctx0, t0, hresolve, _hwf_cs0, _hwf_sep0, _hsat_imp,
            hR0_sub, hbody⟩ := hv
    have hheap : ∃ v, store.heap fx = some (Cell.val v) ∧
        v.unwrap = Exp.boxed cs0 sepctx0 t0 := by
      cases hmem : store.heap fx with
      | none => simp [resolve, hmem] at hresolve
      | some cell =>
        cases cell with
        | val v =>
          have hvunwrap : v.unwrap = Exp.boxed cs0 sepctx0 t0 := by
            simpa only [resolve, hmem, Option.some.injEq] using hresolve
          exact ⟨v, rfl, hvunwrap⟩
        | capability => simp [resolve, hmem] at hresolve
        | masked => simp [resolve, hmem] at hresolve
    obtain ⟨v, hlookup_fx, hvunwrap⟩ := hheap
    cases v with
    | mk unwrap isVal reachability =>
      cases hvunwrap
      refine ⟨fx, rfl, cs0, sepctx0, t0, isVal, reachability, hlookup_fx, hR0_sub, ?_⟩
      intro st' m' hwle hmt hcompat hkind hsep
      simp only [Ty.exi_exp_denot]
      intro _
      -- Instantiate the modal body at the top index `j = k` (the restated inversion holds
      -- there); `st.trunc (le_refl) = st` bridges the truncated base world.
      exact hbody k (Nat.le_refl k) st' m'
        (by rw [WP.World.trunc_self]; exact hwle) hmt hcompat hkind hsep

theorem sem_typ_unwrap
  {x : BVar s .var} {Ψ : ModalCtx s} {E : Ty .exi s}
  (hclosed_Ψ : Ψ.IsClosed)
  (hΓ : Γ.IsClosed)
  (hx : SemanticTyping {} Γ (Exp.var (.bound x))
    (.typ (.modal (.var (.M .epsilon) (.bound x)) Ψ E)))
  (hsatisfy : Satisfy Γ Ψ) :
  SemanticTyping (CaptureSet.var (.M .epsilon) (.bound x)) Γ (Exp.unwrap (.bound x)) E := by
  intro env k st store hts hdsep hcompat
  simp only [Ty.exi_exp_denot, List.empty_eq]
  intro hmt
  -- Observe `x`'s modal value at world `(stx, store)`, invert it to expose the boxed body
  -- `t0`, then fire the body at the SAME world (`WorldLe.refl`) supplying the modal
  -- kind/non-interference obligations from `env.Satisfy Ψ store` (from `hsatisfy`).
  rcases Nat.eq_zero_or_pos k with rfl | hkpos
  · exact Eval.exhausted
  have hxd := semtyp_to_exi_exp_denot hx hts hdsep (Memory.is_compatible_empty store)
  obtain ⟨stx, hwlex, hmtx, hxval⟩ := var_exp_denot_inv hkpos hmt hxd
  simp only [Ty.exi_val_denot] at hxval
  obtain ⟨fx, hfx, cs0, sepctx0, t0, hval, R, hlk, hR0_sub, hbody⟩ := modal_val_denot_inv hxval
  have hfxeq : fx = (env.lookup_var x).1 := by cases hfx; rfl
  subst hfxeq
  have hcompatR0 : store.is_compatible (expand_captures store.heap cs0) :=
    Memory.is_compatible_subset hR0_sub hcompat
  have hsatΨ : env.Satisfy Ψ store :=
    sem_satisfy hclosed_Ψ hΓ hsatisfy env k st store hts hdsep
  have hbody' := hbody stx store (WorldLe.refl stx store) hmtx hcompatR0 hsatΨ.kind hsatΨ.sep
  simp only [Ty.exi_exp_denot] at hbody'
  have hrec0 := hbody' hmtx
  have hgoal_expr : (Exp.unwrap (.bound x)).subst (Subst.from_TypeEnv env)
      = Exp.unwrap (.free (env.lookup_var x).1) := rfl
  rw [hgoal_expr]
  apply Eval.eval_unwrap hlk
  refine eval_post_monotonic ?_ hrec0
  intro t m'' v hp hguard
  obtain ⟨htr, st'', hwle'', hmt'', hval'', hpb, hwl⟩ := hp hguard
  -- `hwle''` is based at `stx.trunc`; descend `x`'s world-step `hwlex` (based at `st`) to the
  -- same level and compose so the result is anchored at `st.trunc`.
  have hwlex_desc := WP.WorldLe.trunc (Nat.sub_le k t.readCount) hwlex
  exact ⟨TraceOk.mono hR0_sub htr, st'', WorldLe.trans hwlex_desc hwle'', hmt'', hval'',
    pack_bound_mono hR0_sub (Memory.subsumes_refl store) hpb, hwl⟩

/-- Extending a closed context with `n` unbound capture variables stays closed. -/
theorem Ctx.extendCVars_isClosed {s : Sig} {Γ : Ctx s} {a : Authority} :
    {n : Nat} → Γ.IsClosed → (Ctx.extendCVars a Γ n).IsClosed
  | 0, h => h
  | _ + 1, h =>
    Ctx.IsClosed.push (Ctx.extendCVars_isClosed h)
      (Binding.IsClosed.cvar CaptureBound.IsClosed.unbound)

theorem fundamental
  (hΓ : Γ.IsClosed)
  (ht : HasType C Γ e T) :
  SemanticTyping C Γ e T := by
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
    rename_i _hC_isclosed haccess _hdroppable hpairwise hx_syn
    cases hclosed_e with
    | pack hcs_closed hx_closed =>
      cases hx_closed
      apply sem_typ_pack
      · exact Exp.IsClosed.pack hcs_closed Var.IsClosed.bound
      · exact hΓ
      · exact haccess
      · exact CaptureSet.PairwiseSep.sem hpairwise
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
      exact sem_typ_unwrap (x := bx) hclosed_Ψ hΓ
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
        (ih1 hΓ (Exp.IsClosed.var hclosed_guard)) (ih2 hΓ hclosed_then)
        (ih3 hΓ hclosed_else)
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
    | par hclosed_C1 hclosed_C2 hclosed_e1 hclosed_e2 =>
      exact sem_typ_par hΓ
        hclosed_C1
        hclosed_C2
        hclosed_e1
        hclosed_e2
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
      | typ hT =>
        exact Ctx.IsClosed.push (Ctx.kill_peaks_cs_isClosed hΓ) (Binding.IsClosed.var hT)
  case subtyp ht_syn hsubcapt hsubtyp hclosed_C2 hclosed_E2 ht_ih =>
    have hclosed_C1 := HasType.use_set_is_closed ht_syn
    have hclosed_E1 := HasType.type_is_closed ht_syn
    exact sem_typ_subtyp (ht_ih hΓ hclosed_e) hsubcapt hsubtyp
      hclosed_C1 hclosed_E1 hclosed_C2 hclosed_E2
  case unpack hseq hdrop ht_syn hu_syn ht_ih hu_ih =>
    cases hclosed_e with
    | unpack ht_closed hu_closed =>
      apply sem_typ_unpack hseq hdrop hΓ
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
          (Ctx.extendCVars_isClosed (Ctx.kill_peaks_cs_isClosed hΓ))
          (Binding.IsClosed.var hT)

end CoreCapybara
