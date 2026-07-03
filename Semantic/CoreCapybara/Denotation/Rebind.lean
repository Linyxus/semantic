import Semantic.CoreCapybara.Denotation.Core
namespace CoreCapybara

open CoreCapybara.WP (WorldLe)

structure Rebind (env1 : TypeEnv s1) (f : Rename s1 s2) (env2 : TypeEnv s2) : Prop where
  var :
    ∀ (x : BVar s1 .var),
      (env1.lookup_var x).1 = (env2.lookup_var (f.var x)).1
  var_peaks :
    ∀ (x : BVar s1 .var),
      (env1.lookup_var x).2.rename f = (env2.lookup_var (f.var x)).2
  tvar :
    ∀ (x : BVar s1 .tvar),
      env1.lookup_tvar x = env2.lookup_tvar (f.var x)
  cvar :
    ∀ (x : BVar s1 .cvar),
      env1.lookup_cvar x = env2.lookup_cvar (f.var x)
  cvar_injective :
    ∀ (x y : BVar s1 .cvar),
      f.var x = f.var y → x = y

def Rebind.liftVar
  {s1 s2 : Sig} {env1 : TypeEnv s1} {env2 : TypeEnv s2} {f : Rename s1 s2}
  (ρ : Rebind env1 f env2) {x : Nat} (ps1 : PeakSet s1) (ps2 : PeakSet s2)
  (hps : ps1.rename f = ps2) :
  Rebind (env1.extend_var x ps1) (f.lift) (env2.extend_var x ps2) where
  var := fun
    | .here => rfl
    | .there y => by
      simp only [TypeEnv.extend_var, Rename.lift, TypeEnv.lookup_var]
      exact ρ.var y
  var_peaks := fun
    | .here => by
      change (ps1.rename Rename.succ).rename f.lift = (ps2.rename Rename.succ)
      unfold PeakSet.rename
      congr 1
      rw [CaptureSet.rename_comp, Rename.succ_lift_comm,
          ← CaptureSet.rename_comp]
      exact congrArg (CaptureSet.rename · Rename.succ)
        (congrArg PeakSet.cs hps)
    | .there y => by
      change ((env1.lookup_var y).2.rename Rename.succ).rename f.lift
        = ((env2.lookup_var (f.var y)).2.rename Rename.succ)
      unfold PeakSet.rename
      congr 1
      have h := congrArg PeakSet.cs (ρ.var_peaks y)
      simp only [PeakSet.rename] at h
      rw [CaptureSet.rename_comp, Rename.succ_lift_comm,
          ← CaptureSet.rename_comp, h]
  tvar := fun
    | .there y => by
      simp only [TypeEnv.extend_var, Rename.lift, TypeEnv.lookup_tvar]
      exact ρ.tvar y
  cvar := fun
    | .there y => by
      simp only [TypeEnv.extend_var, Rename.lift, TypeEnv.lookup_cvar]
      exact ρ.cvar y
  cvar_injective := fun
    | .there x, .there y, h => by
      simp only [Rename.lift] at h
      exact congrArg BVar.there (ρ.cvar_injective x y (BVar.there.inj h))

def Rebind.liftTVar
  (ρ : Rebind env1 f env2) :
  Rebind (env1.extend_tvar d) (f.lift) (env2.extend_tvar d) where
  var := fun
    | .there y => by
      simp only [TypeEnv.extend_tvar, Rename.lift, TypeEnv.lookup_var]
      exact ρ.var y
  var_peaks := fun
    | .there y => by
      change ((env1.lookup_var y).2.rename Rename.succ).rename f.lift
        = ((env2.lookup_var (f.var y)).2.rename Rename.succ)
      unfold PeakSet.rename
      congr 1
      have h := congrArg PeakSet.cs (ρ.var_peaks y)
      simp only [PeakSet.rename] at h
      rw [CaptureSet.rename_comp, Rename.succ_lift_comm,
          ← CaptureSet.rename_comp, h]
  tvar := fun
    | .here => rfl
    | .there y => by
      simp only [TypeEnv.extend_tvar, Rename.lift, TypeEnv.lookup_tvar]
      exact ρ.tvar y
  cvar := fun
    | .there y => by
      simp only [TypeEnv.extend_tvar, Rename.lift, TypeEnv.lookup_cvar]
      exact ρ.cvar y
  cvar_injective := fun
    | .there x, .there y, h => by
      simp only [Rename.lift] at h
      exact congrArg BVar.there (ρ.cvar_injective x y (BVar.there.inj h))

def Rebind.liftCVar
  (ρ : Rebind env1 f env2) (cs : CaptureSet {}) (cap : CapabilitySet := .empty)
  (a : Authority := .access_only) :
  Rebind (env1.extend_cvar cs cap a) (f.lift) (env2.extend_cvar cs cap a) where
  var := fun
    | .there y => by
      simp only [TypeEnv.extend_cvar, Rename.lift, TypeEnv.lookup_var]
      exact ρ.var y
  var_peaks := fun
    | .there y => by
      change ((env1.lookup_var y).2.rename Rename.succ).rename f.lift
        = ((env2.lookup_var (f.var y)).2.rename Rename.succ)
      unfold PeakSet.rename
      congr 1
      have h := congrArg PeakSet.cs (ρ.var_peaks y)
      simp only [PeakSet.rename] at h
      rw [CaptureSet.rename_comp, Rename.succ_lift_comm,
          ← CaptureSet.rename_comp, h]
  tvar := fun
    | .there y => by
      simp only [TypeEnv.extend_cvar, Rename.lift, TypeEnv.lookup_tvar]
      exact ρ.tvar y
  cvar := fun
    | .here => rfl
    | .there y => by
      simp only [TypeEnv.extend_cvar, Rename.lift, TypeEnv.lookup_cvar]
      exact ρ.cvar y
  cvar_injective := fun
    | .here, .here, _ => rfl
    | .there x, .there y, h => by
      simp only [Rename.lift] at h
      exact congrArg BVar.there (ρ.cvar_injective x y (BVar.there.inj h))

/-- `Rebind.liftCVar` iterated over the `n` evidences of a pack: rebinding lifts
    under the `n` capture binders of `TypeEnv.extend_cvars`. -/
def Rebind.liftCVars {s1 s2 : Sig} {env1 : TypeEnv s1} {f : Rename s1 s2} {env2 : TypeEnv s2}
    (ρ : Rebind env1 f env2) (m : Memory) (a : Authority) :
    {n : Nat} → (CS : List.Vector (CaptureSet {}) n) →
    Rebind (TypeEnv.extend_cvars env1 m a CS) (f.liftCVars n)
      (TypeEnv.extend_cvars env2 m a CS)
  | 0, _ => ρ
  | _ + 1, CS =>
    (Rebind.liftCVars ρ m a (List.Vector.tail CS)).liftCVar (List.Vector.head CS)
      (cap := (List.Vector.head CS).ground_denot m) (a := a)

theorem rebind_resolved_capture_set {C : CaptureSet s1}
  (ρ : Rebind env1 f env2) :
  C.subst (Subst.from_TypeEnv env1) =
    (C.rename f).subst (Subst.from_TypeEnv env2) := by
  induction C with
  | empty =>
    simp only [CaptureSet.subst, CaptureSet.rename]
  | union C1 C2 ih1 ih2 =>
    simp only [CaptureSet.subst, CaptureSet.rename, ih1, ih2]
  | var m x =>
    cases x with
    | free n =>
      simp only [CaptureSet.subst, CaptureSet.rename, Var.subst, Var.rename]
    | bound x =>
      have h := ρ.var x
      simp only [CaptureSet.subst, CaptureSet.rename, Var.subst, Var.rename,
        Subst.from_TypeEnv, List.empty_eq]
      rw [<-h]
  | cvar m x =>
    have h := ρ.cvar x
    simp only [CaptureSet.subst, CaptureSet.rename, Subst.from_TypeEnv, List.empty_eq]
    rw [<-h]


/- Rebinding for CaptureSet.denot -/
theorem rebind_captureset_denot
  {s1 s2 : Sig} {env1 : TypeEnv s1} {f : Rename s1 s2} {env2 : TypeEnv s2}
  (ρ : Rebind env1 f env2) (C : CaptureSet s1) :
  CaptureSet.denot env1 C = CaptureSet.denot env2 (C.rename f) := by
  unfold CaptureSet.denot
  congr 1
  exact rebind_resolved_capture_set ρ

theorem rebind_capturebound_denot
  {s1 s2 : Sig} {env1 : TypeEnv s1} {f : Rename s1 s2} {env2 : TypeEnv s2}
  (ρ : Rebind env1 f env2) (B : CaptureBound s1) :
  CaptureBound.denot env1 B = CaptureBound.denot env2 (B.rename f) := by
  cases B with
  | unbound =>
    simp [CaptureBound.denot, CaptureBound.rename]
  | bound C =>
    simp [CaptureBound.denot, CaptureBound.rename, rebind_captureset_denot ρ C]

theorem rebind_compute_peaks
  {s1 s2 : Sig} {env1 : TypeEnv s1} {f : Rename s1 s2} {env2 : TypeEnv s2}
  (ρ : Rebind env1 f env2) (cs : CaptureSet s1) :
  (compute_peaks env1 cs).rename f = compute_peaks env2 (cs.rename f) := by
  induction cs with
  | empty => rfl
  | union cs1 cs2 ih1 ih2 =>
    simp only [compute_peaks, CaptureSet.rename]
    rw [← ih1, ← ih2]
  | cvar m c =>
    simp [compute_peaks, CaptureSet.rename]
  | var m x =>
    cases x with
    | free n => simp [compute_peaks, CaptureSet.rename, Var.rename]
    | bound x =>
      simp only [compute_peaks, CaptureSet.rename, Var.rename]
      have h := congrArg PeakSet.cs (ρ.var_peaks x)
      simp only [PeakSet.rename] at h
      rw [CaptureSet.applyAccess_rename, h]

theorem CaptureSet.Subset.rename' {C1 C2 : CaptureSet s1} {f : Rename s1 s2}
  (hsub : C1 ⊆ C2) : C1.rename f ⊆ C2.rename f := by
  induction hsub with
  | refl => exact .refl
  | empty => exact .empty
  | union_left _ _ ih1 ih2 =>
    simp only [CaptureSet.rename]
    exact .union_left ih1 ih2
  | union_right_left _ ih =>
    simp only [CaptureSet.rename]
    exact .union_right_left ih
  | union_right_right _ ih =>
    simp only [CaptureSet.rename]
    exact .union_right_right ih

theorem CaptureSet.PeaksOnly.cvar_subset_rename_inv
  {cs : CaptureSet s1} (hpo : cs.PeaksOnly) {f : Rename s1 s2}
  {m : Access} {c : BVar s2 .cvar}
  (hsub : (.cvar m c) ⊆ cs.rename f) :
  ∃ c', f.var c' = c ∧ (.cvar m c') ⊆ cs := by
  induction hpo with
  | empty =>
    simp only [CaptureSet.rename] at hsub
    cases hsub
  | cvar =>
    simp only [CaptureSet.rename] at hsub
    cases hsub
    exact ⟨_, rfl, .refl⟩
  | union _ _ ih1 ih2 =>
    simp only [CaptureSet.rename] at hsub
    cases hsub with
    | union_right_left hsub1 =>
      obtain ⟨c', hfc, hsub'⟩ := ih1 hsub1
      exact ⟨c', hfc, .union_right_left hsub'⟩
    | union_right_right hsub2 =>
      obtain ⟨c', hfc, hsub'⟩ := ih2 hsub2
      exact ⟨c', hfc, .union_right_right hsub'⟩

theorem Rebind.hassepdom
  {s1 s2 : Sig} {env1 : TypeEnv s1} {f : Rename s1 s2} {env2 : TypeEnv s2}
  (ρ : Rebind env1 f env2) (cs : CaptureSet s1) :
  env1.HasSepDom cs ↔ env2.HasSepDom (cs.rename f) := by
  unfold TypeEnv.HasSepDom
  have hpeaks := rebind_compute_peaks ρ cs
  have hpo := compute_peaks_is_peak env1 cs
  constructor
  · intro h m1 c1 m2 c2 hsub1 hsub2 hne
    rw [← hpeaks] at hsub1 hsub2
    obtain ⟨c1', hc1, hsub1'⟩ := hpo.cvar_subset_rename_inv hsub1
    obtain ⟨c2', hc2, hsub2'⟩ := hpo.cvar_subset_rename_inv hsub2
    subst hc1; subst hc2
    have hne' : c1' ≠ c2' := by
      intro heq; subst heq; exact hne rfl
    have := h m1 c1' m2 c2' hsub1' hsub2' hne'
    rwa [ρ.cvar c1', ρ.cvar c2'] at this
  · intro h m1 c1 m2 c2 hsub1 hsub2 hne
    have hsub1' : (.cvar m1 (f.var c1)) ⊆ compute_peaks env2 (cs.rename f) := by
      rw [← hpeaks]
      exact hsub1.rename'
    have hsub2' : (.cvar m2 (f.var c2)) ⊆ compute_peaks env2 (cs.rename f) := by
      rw [← hpeaks]
      exact hsub2.rename'
    have hne' : f.var c1 ≠ f.var c2 := by
      intro heq; exact hne (ρ.cvar_injective c1 c2 heq)
    have := h m1 (f.var c1) m2 (f.var c2) hsub1' hsub2' hne'
    rwa [← ρ.cvar c1, ← ρ.cvar c2] at this

theorem rebind_satisfy_iff
  {s1 s2 : Sig} {env1 : TypeEnv s1} {f : Rename s1 s2} {env2 : TypeEnv s2}
  (ρ : Rebind env1 f env2) (Ψ : ModalCtx s1) (m : Memory) :
  TypeEnv.Satisfy env1 Ψ m ↔ TypeEnv.Satisfy env2 (Ψ.rename f) m := by
  constructor
  · intro hsat
    constructor
    · intro C hhas
      obtain ⟨C0, rfl, hhas0⟩ := SepCtx.Has.rename_inv hhas
      simpa only [rebind_resolved_capture_set (ρ := ρ) (C := C0)] using
        hsat.wf_sep C0 hhas0
    · intro C mode hhas
      obtain ⟨C0, rfl, hhas0⟩ := MutabilityCtx.Has.rename_inv hhas
      simpa only [rebind_resolved_capture_set (ρ := ρ) (C := C0)] using
        hsat.wf_mut C0 mode hhas0
    · intro C mode hhas
      obtain ⟨C0, rfl, hhas0⟩ := MutabilityCtx.Has.rename_inv hhas
      simpa only [rebind_captureset_denot (ρ := ρ) (C := C0)] using
        hsat.kind C0 mode hhas0
    · intro C1 C2 hdistinct
      obtain ⟨D1, D2, rfl, rfl, hdistinct0⟩ := SepCtx.HasTwoDistinct.rename_inv hdistinct
      simpa only [rebind_captureset_denot (ρ := ρ) (C := D1),
        rebind_captureset_denot (ρ := ρ) (C := D2)] using
        hsat.sep D1 D2 hdistinct0
  · intro hsat
    constructor
    · intro C hhas
      have hhas' := hhas.rename (f := f)
      simpa only [rebind_resolved_capture_set (ρ := ρ) (C := C)] using
        hsat.wf_sep (C.rename f) hhas'
    · intro C mode hhas
      have hhas' := hhas.rename (f := f)
      simpa only [rebind_resolved_capture_set (ρ := ρ) (C := C)] using
        hsat.wf_mut (C.rename f) mode hhas'
    · intro C mode hhas
      have hhas' := hhas.rename (f := f)
      simpa only [rebind_captureset_denot (ρ := ρ) (C := C)] using
        hsat.kind (C.rename f) mode hhas'
    · intro C1 C2 hdistinct
      have hdistinct' := hdistinct.rename (f := f)
      simpa only [rebind_captureset_denot (ρ := ρ) (C := C1),
        rebind_captureset_denot (ρ := ρ) (C := C2)] using
        hsat.sep (C1.rename f) (C2.rename f) hdistinct'

set_option maxHeartbeats 1000000 in
-- The mutual rebind denotation definitions trigger heavy reducibility checks
-- from the higher-order assumption transport in the modal branch.
mutual

def rebind_val_denot
  {s1 s2 : Sig} {env1 : TypeEnv s1} {f : Rename s1 s2} {env2 : TypeEnv s2}
  (ρ : Rebind env1 f env2) (T : Ty .capt s1) :
  IDenot.Equiv (Ty.val_denot env1 T) (Ty.val_denot env2 (T.rename f)) :=
  match T with
  | .top | .unit | .bool => by
    intro k st m e
    simp [Ty.val_denot, Ty.rename]
  | .tvar X => by
    have h := ρ.tvar X
    intro k st m e
    simp [Ty.val_denot, Ty.rename, h]
  | .cap cs => by
    intro k st m e
    simp only [Ty.val_denot, Ty.rename]
    rw [← rebind_resolved_capture_set ρ]
    rw [← rebind_captureset_denot ρ cs]
  | .cell cs Tc | .reader cs Tc => by
    have ih := rebind_val_denot ρ Tc
    have heq : Ty.val_denot env1 Tc = Ty.val_denot env2 (Tc.rename f) := by
      funext k st m e; exact propext (ih k st m e)
    intro k st m e
    simp only [Ty.val_denot, Ty.rename]
    rw [← rebind_resolved_capture_set ρ]
    rw [← rebind_captureset_denot ρ cs]
    rw [heq]
  | .arrow T1 cs T2 => by
    have ih1 := rebind_val_denot ρ T1
    intro k st m e
    simp only [Ty.val_denot, Ty.rename]
    rw [← rebind_resolved_capture_set ρ]
    rw [← rebind_captureset_denot ρ cs]
    have hps : (compute_peakset env1 T1.captureSet).rename f =
        compute_peakset env2 (T1.rename f).captureSet := by
      simp only [compute_peakset, PeakSet.rename,
                  Ty.captureSet_rename]
      congr 1
      exact rebind_compute_peaks ρ T1.captureSet
    constructor
    · intro ⟨hwf_e, hwf_cs, cs', T0, t0, hr, hwf_cs', hR0_sub, hd⟩
      refine ⟨hwf_e, hwf_cs, cs', T0, t0, hr, hwf_cs', hR0_sub, ?_⟩
      intro j hjk st' m' arg hwle hmt hcompat harg
      let ps1 := compute_peakset env1 T1.captureSet
      let ps2 := compute_peakset env2 (T1.rename f).captureSet
      have ih2 := rebind_exi_val_denot (ρ.liftVar (x:=arg) ps1 ps2 hps) T2
      have harg' := (ih1 j st' m' (.var (.free arg))).mpr harg
      have hd' := hd j hjk st' m' arg hwle hmt hcompat harg'
      refine eval_post_monotonic_general ?_ hd'
      intro m'' hsub'' t v hpost hguard
      obtain ⟨htr, st'', hwle'', hmt'', hval, hpb, hwl⟩ := hpost hguard
      exact ⟨htr, st'', hwle'', hmt'', (ih2 (j - t.readCount) st'' m'' v).mp hval, hpb, hwl⟩
    · intro ⟨hwf_e, hwf_cs, cs', T0, t0, hr, hwf_cs', hR0_sub, hd⟩
      refine ⟨hwf_e, hwf_cs, cs', T0, t0, hr, hwf_cs', hR0_sub, ?_⟩
      intro j hjk st' m' arg hwle hmt hcompat harg
      let ps1 := compute_peakset env1 T1.captureSet
      let ps2 := compute_peakset env2 (T1.rename f).captureSet
      have ih2 := rebind_exi_val_denot (ρ.liftVar (x:=arg) ps1 ps2 hps) T2
      have harg' := (ih1 j st' m' (.var (.free arg))).mp harg
      have hd' := hd j hjk st' m' arg hwle hmt hcompat harg'
      refine eval_post_monotonic_general ?_ hd'
      intro m'' hsub'' t v hpost hguard
      obtain ⟨htr, st'', hwle'', hmt'', hval, hpb, hwl⟩ := hpost hguard
      exact ⟨htr, st'', hwle'', hmt'', (ih2 (j - t.readCount) st'' m'' v).mpr hval, hpb, hwl⟩
  | .poly T1 cs T2 => by
    have ih1 := rebind_val_denot ρ T1
    intro k st m e
    simp only [Ty.val_denot, Ty.rename]
    rw [← rebind_resolved_capture_set ρ]
    rw [← rebind_captureset_denot ρ cs]
    constructor
    · intro ⟨hwf_e, hwf_cs, cs', S0, t0, hr, hwf_cs', hR0_sub, hd⟩
      refine ⟨hwf_e, hwf_cs, cs', S0, t0, hr, hwf_cs', hR0_sub, ?_⟩
      intro j hjk st' m' denot hwle hmt hcompat hproper himply_simple_ans himply hpure
      have ih2 := rebind_exi_val_denot (ρ.liftTVar (d:=denot)) T2
      have himply' : denot.ImplyAfter j st' m' (Ty.val_denot env1 T1) := by
        intro i hij st'' m'' hwle'' e' hdenot
        exact (ih1 i st'' m'' e').mpr (himply i hij st'' m'' hwle'' e' hdenot)
      have hd' := hd j hjk st' m' denot hwle hmt hcompat hproper himply_simple_ans himply' hpure
      refine eval_post_monotonic_general ?_ hd'
      intro m'' hsub'' t v hpost hguard
      obtain ⟨htr, st'', hwle3, hmt3, hval, hpb, hwl⟩ := hpost hguard
      exact ⟨htr, st'', hwle3, hmt3, (ih2 (j - t.readCount) st'' m'' v).mp hval, hpb, hwl⟩
    · intro ⟨hwf_e, hwf_cs, cs', S0, t0, hr, hwf_cs', hR0_sub, hd⟩
      refine ⟨hwf_e, hwf_cs, cs', S0, t0, hr, hwf_cs', hR0_sub, ?_⟩
      intro j hjk st' m' denot hwle hmt hcompat hproper himply_simple_ans himply hpure
      have ih2 := rebind_exi_val_denot (ρ.liftTVar (d:=denot)) T2
      have himply' : denot.ImplyAfter j st' m' (Ty.val_denot env2 (T1.rename f)) := by
        intro i hij st'' m'' hwle'' e' hdenot
        exact (ih1 i st'' m'' e').mp (himply i hij st'' m'' hwle'' e' hdenot)
      have hd' := hd j hjk st' m' denot hwle hmt hcompat hproper himply_simple_ans himply' hpure
      refine eval_post_monotonic_general ?_ hd'
      intro m'' hsub'' t v hpost hguard
      obtain ⟨htr, st'', hwle3, hmt3, hval, hpb, hwl⟩ := hpost hguard
      exact ⟨htr, st'', hwle3, hmt3, (ih2 (j - t.readCount) st'' m'' v).mpr hval, hpb, hwl⟩
  | .cpoly B cs T => by
    have hB := rebind_capturebound_denot ρ B
    intro k st m e
    simp only [Ty.val_denot, Ty.rename]
    rw [← rebind_resolved_capture_set ρ]
    rw [← rebind_captureset_denot ρ cs]
    rw [hB]
    constructor
    · intro ⟨hwf_e, hwf_cs, cs', B0, t0, hr, hwf_cs', hR0_sub, hd⟩
      refine ⟨hwf_e, hwf_cs, cs', B0, t0, hr, hwf_cs', hR0_sub, ?_⟩
      intro j hjk st' m' CS hwf_CS hdf hwle hmt hcompat hsub_bound
      have ih2 := rebind_exi_val_denot (ρ.liftCVar CS (cap := CS.ground_denot m')) T
      have hd' := hd j hjk st' m' CS hwf_CS hdf hwle hmt hcompat hsub_bound
      refine eval_post_monotonic_general ?_ hd'
      intro m'' hsub'' t v hpost hguard
      obtain ⟨htr, st'', hwle3, hmt3, hval, hpb, hwl⟩ := hpost hguard
      exact ⟨htr, st'', hwle3, hmt3, (ih2 (j - t.readCount) st'' m'' v).mp hval, hpb, hwl⟩
    · intro ⟨hwf_e, hwf_cs, cs', B0, t0, hr, hwf_cs', hR0_sub, hd⟩
      refine ⟨hwf_e, hwf_cs, cs', B0, t0, hr, hwf_cs', hR0_sub, ?_⟩
      intro j hjk st' m' CS hwf_CS hdf hwle hmt hcompat hsub_bound
      have ih2 := rebind_exi_val_denot (ρ.liftCVar CS (cap := CS.ground_denot m')) T
      have hd' := hd j hjk st' m' CS hwf_CS hdf hwle hmt hcompat hsub_bound
      refine eval_post_monotonic_general ?_ hd'
      intro m'' hsub'' t v hpost hguard
      obtain ⟨htr, st'', hwle3, hmt3, hval, hpb, hwl⟩ := hpost hguard
      exact ⟨htr, st'', hwle3, hmt3, (ih2 (j - t.readCount) st'' m'' v).mpr hval, hpb, hwl⟩
  | .consumer _ cs _ => by
    intro k st m e
    simp only [Ty.val_denot, Ty.rename]
    rw [← rebind_resolved_capture_set ρ]
    rw [← rebind_captureset_denot ρ cs]
  | .modal cs Ψ T => by
    intro k st m e
    simp only [Ty.val_denot, Ty.rename]
    rw [← rebind_resolved_capture_set ρ]
    rw [← rebind_captureset_denot ρ cs]
    constructor
    · rintro ⟨hwf_e, hwf_cs, cs0, sepctx0, t0, hres, hwf_cs0, hwf_sepctx0,
        hsat, hR0_sub, hbody⟩
      refine ⟨hwf_e, hwf_cs, cs0, sepctx0, t0, hres, hwf_cs0, hwf_sepctx0, ?_, hR0_sub, ?_⟩
      · intro m' hsub hsat'
        exact hsat m' hsub ((rebind_satisfy_iff ρ Ψ m').mpr hsat')
      · intro j hjk st' m' hwle hmt hcompat hkind hsep
        have ih := rebind_exi_val_denot ρ T
        have hkind' :
            ∀ (C : CaptureSet s1) (mode : Mutability),
              Ψ.mutability.Has C mode -> CapabilitySet.HasKind (C.denot env1 m') mode := by
          intro C mode hhas
          simpa only [rebind_captureset_denot (ρ := ρ) (C := C)] using
            hkind (C.rename f) mode (hhas.rename)
        have hsep' :
            ∀ (C1 : CaptureSet s1) (C2 : CaptureSet s1),
              Ψ.sep.HasTwoDistinct C1 C2 ->
              CapabilitySet.Noninterference (C1.denot env1 m') (C2.denot env1 m') := by
          intro C1 C2 hdistinct
          simpa only [rebind_captureset_denot (ρ := ρ) (C := C1),
            rebind_captureset_denot (ρ := ρ) (C := C2)] using
              hsep (C1.rename f) (C2.rename f) (hdistinct.rename)
        have hd' := hbody j hjk st' m' hwle hmt hcompat hkind' hsep'
        refine eval_post_monotonic_general ?_ hd'
        intro m'' hsub'' t v hpost hguard
        obtain ⟨htr, st'', hwle3, hmt3, hval, hpb, hwl⟩ := hpost hguard
        exact ⟨htr, st'', hwle3, hmt3, (ih (j - t.readCount) st'' m'' v).mp hval, hpb, hwl⟩
    · rintro ⟨hwf_e, hwf_cs, cs0, sepctx0, t0, hres, hwf_cs0, hwf_sepctx0,
        hsat, hR0_sub, hbody⟩
      refine ⟨hwf_e, hwf_cs, cs0, sepctx0, t0, hres, hwf_cs0, hwf_sepctx0, ?_, hR0_sub, ?_⟩
      · intro m' hsub hsat'
        exact hsat m' hsub ((rebind_satisfy_iff ρ Ψ m').mp hsat')
      · intro j hjk st' m' hwle hmt hcompat hkind hsep
        have ih := rebind_exi_val_denot ρ T
        have hkind' :
            ∀ (C : CaptureSet s2) (mode : Mutability),
              (Ψ.rename f).mutability.Has C mode ->
                CapabilitySet.HasKind (C.denot env2 m') mode := by
          intro C mode hhas
          obtain ⟨C0, rfl, hhas0⟩ := MutabilityCtx.Has.rename_inv hhas
          simpa only [rebind_captureset_denot (ρ := ρ) (C := C0)] using
            hkind C0 mode hhas0
        have hsep' :
            ∀ (C1 : CaptureSet s2) (C2 : CaptureSet s2),
              (Ψ.rename f).sep.HasTwoDistinct C1 C2 ->
              CapabilitySet.Noninterference (C1.denot env2 m') (C2.denot env2 m') := by
          intro C1 C2 hdistinct
          obtain ⟨D1, D2, rfl, rfl, hdistinct0⟩ := SepCtx.HasTwoDistinct.rename_inv hdistinct
          simpa only [rebind_captureset_denot (ρ := ρ) (C := D1),
            rebind_captureset_denot (ρ := ρ) (C := D2)] using
              hsep D1 D2 hdistinct0
        have hd' := hbody j hjk st' m' hwle hmt hcompat hkind' hsep'
        refine eval_post_monotonic_general ?_ hd'
        intro m'' hsub'' t v hpost hguard
        obtain ⟨htr, st'', hwle3, hmt3, hval, hpb, hwl⟩ := hpost hguard
        exact ⟨htr, st'', hwle3, hmt3, (ih (j - t.readCount) st'' m'' v).mpr hval, hpb, hwl⟩

def rebind_exi_val_denot
  {s1 s2 : Sig} {env1 : TypeEnv s1} {f : Rename s1 s2} {env2 : TypeEnv s2}
  (ρ : Rebind env1 f env2) (T : Ty .exi s1) :
  IDenot.Equiv (Ty.exi_val_denot env1 T) (Ty.exi_val_denot env2 (T.rename f)) :=
  match T with
  | .typ T => by
    have ih := rebind_val_denot ρ T
    intro k st m e
    simp only [Ty.exi_val_denot, Ty.rename]
    exact ih k st m e
  | .exi n T => by
    intro k st m e
    simp only [Ty.exi_val_denot, Ty.rename]
    constructor
    · rintro ⟨CS, y, hres, hwf, hdf, hdisj, hbody⟩
      exact ⟨CS, y, hres, hwf, hdf, hdisj,
        (rebind_val_denot (ρ.liftCVars m .can_drop CS) T k st m (Exp.var y)).mp hbody⟩
    · rintro ⟨CS, y, hres, hwf, hdf, hdisj, hbody⟩
      exact ⟨CS, y, hres, hwf, hdf, hdisj,
        (rebind_val_denot (ρ.liftCVars m .can_drop CS) T k st m (Exp.var y)).mpr hbody⟩

def rebind_exi_exp_denot
  {s1 s2 : Sig} {env1 : TypeEnv s1} {f : Rename s1 s2} {env2 : TypeEnv s2}
  (ρ : Rebind env1 f env2) (T : Ty .exi s1) (R : CapabilitySet) :
  IDenot.Equiv (Ty.exi_exp_denot env1 T R) (Ty.exi_exp_denot env2 (T.rename f) R) := by
  have ih := rebind_exi_val_denot ρ T
  intro k st m e
  simp only [Ty.exi_exp_denot]
  constructor
  · intro h hmt
    refine eval_post_monotonic_general ?_ (h hmt)
    intro mm hsub t v hpost hguard
    obtain ⟨htr, st', hwle, hmt', hval, hpb, hwl⟩ := hpost hguard
    exact ⟨htr, st', hwle, hmt', (ih (k - t.readCount) st' mm v).mp hval, hpb, hwl⟩
  · intro h hmt
    refine eval_post_monotonic_general ?_ (h hmt)
    intro mm hsub t v hpost hguard
    obtain ⟨htr, st', hwle, hmt', hval, hpb, hwl⟩ := hpost hguard
    exact ⟨htr, st', hwle, hmt', (ih (k - t.readCount) st' mm v).mpr hval, hpb, hwl⟩

end

def Rebind.weaken {env : TypeEnv s} {x : Nat} {ps : PeakSet s} :
  Rebind env Rename.succ (env.extend_var x ps) where
  var := fun _ => rfl
  var_peaks := fun _ => rfl
  tvar := fun _ => rfl
  cvar := fun _ => rfl
  cvar_injective := fun _ _ h => BVar.there.inj h

def Rebind.tweaken {env : TypeEnv s} {d : IDenot} :
  Rebind env Rename.succ (env.extend_tvar d) where
  var := fun _ => rfl
  var_peaks := fun _ => rfl
  tvar := fun _ => rfl
  cvar := fun _ => rfl
  cvar_injective := fun _ _ h => BVar.there.inj h

def Rebind.cweaken {env : TypeEnv s} {cs : CaptureSet {}} {cap : CapabilitySet}
  {a : Authority} :
  Rebind env Rename.succ (env.extend_cvar cs cap a) where
  var := fun _ => rfl
  var_peaks := fun _ => rfl
  tvar := fun _ => rfl
  cvar := fun _ => rfl
  cvar_injective := fun _ _ h => BVar.there.inj h

def Rebind.lweaken {env : TypeEnv s} :
  Rebind env Rename.succ (env.extend_lock) where
  var := fun _ => rfl
  var_peaks := fun _ => rfl
  tvar := fun _ => rfl
  cvar := fun _ => rfl
  cvar_injective := fun _ _ h => BVar.there.inj h

theorem PeakSet.rename_id {s : Sig} {ps : PeakSet s} : ps.rename Rename.id = ps := by
  cases ps; simp only [PeakSet.rename, CaptureSet.rename_id]

theorem PeakSet.rename_comp {s1 s2 s3 : Sig} {ps : PeakSet s1}
    {f : Rename s1 s2} {g : Rename s2 s3} :
    (ps.rename f).rename g = ps.rename (f.comp g) := by
  cases ps; simp only [PeakSet.rename, CaptureSet.rename_comp]

def Rebind.refl {env : TypeEnv s} : Rebind env Rename.id env where
  var := fun _ => rfl
  var_peaks := fun _ => PeakSet.rename_id
  tvar := fun _ => rfl
  cvar := fun _ => rfl
  cvar_injective := fun _ _ h => h

def Rebind.comp {s1 s2 s3 : Sig} {env1 : TypeEnv s1} {env2 : TypeEnv s2} {env3 : TypeEnv s3}
    {f : Rename s1 s2} {g : Rename s2 s3}
    (ρ1 : Rebind env1 f env2) (ρ2 : Rebind env2 g env3) :
    Rebind env1 (f.comp g) env3 where
  var := fun x => (ρ1.var x).trans (ρ2.var (f.var x))
  var_peaks := fun x => by
    rw [← PeakSet.rename_comp, ρ1.var_peaks x]
    exact ρ2.var_peaks (f.var x)
  tvar := fun x => (ρ1.tvar x).trans (ρ2.tvar (f.var x))
  cvar := fun x => (ρ1.cvar x).trans (ρ2.cvar (f.var x))
  cvar_injective := fun x y h => ρ1.cvar_injective x y (ρ2.cvar_injective _ _ h)

/-- The `n`-fold capture-variable weakening `Rebind`: an environment embeds into its
    `TypeEnv.extend_cvars`-extension along `Rename.weakenCVars n`. -/
def Rebind.cweakenCVars {s : Sig} {env : TypeEnv s} {m : Memory} {a : Authority} :
    {n : Nat} → {CS : List.Vector (CaptureSet {}) n} →
    Rebind env (Rename.weakenCVars n) (TypeEnv.extend_cvars env m a CS)
  | 0, _ => Rebind.refl
  | _ + 1, CS =>
    (Rebind.cweakenCVars (CS := List.Vector.tail CS)).comp Rebind.cweaken

/-- Authority is denotationally inert: `val_denot`/`exi_val_denot` read the
environment only through `lookup_*`/`from_TypeEnv`, which discard the authority
tag. Hence the identity rename is a `Rebind` between two `extend_cvar` binders
differing only in authority. -/
def Rebind.auth_irrel {env : TypeEnv s} {cs : CaptureSet {}} {cap : CapabilitySet}
  {a1 a2 : Authority} :
  Rebind (env.extend_cvar cs cap a1) Rename.id (env.extend_cvar cs cap a2) where
  var := fun x => by cases x with | there y => rfl
  var_peaks := fun x => by cases x with | there y => exact PeakSet.rename_id
  tvar := fun x => by cases x with | there y => rfl
  cvar := fun x => by cases x <;> rfl
  cvar_injective := fun _ _ h => h

/-- Re-tagging the topmost `extend_cvar` binder leaves `val_denot` unchanged. -/
theorem val_denot_auth_irrel {env : TypeEnv s} {cs : CaptureSet {}}
  {cap : CapabilitySet} {a1 a2 : Authority} (T : Ty .capt (s,C)) :
  IDenot.Equiv (Ty.val_denot (env.extend_cvar cs cap a1) T)
    (Ty.val_denot (env.extend_cvar cs cap a2) T) := by
  have h := rebind_val_denot (Rebind.auth_irrel (env := env) (cs := cs)
    (cap := cap) (a1 := a1) (a2 := a2)) T
  rwa [Ty.rename_id] at h

/-- `Rebind.auth_irrel` iterated over the `n` binders of an `extend_cvars`: the
identity rename is a `Rebind` between two evidence-extensions that differ only in
the authority tag of *every* one of the `n` binders. -/
def Rebind.auth_irrel_cvars {s : Sig} {env : TypeEnv s} {m : Memory}
    {a1 a2 : Authority} :
    {n : Nat} → {CS : List.Vector (CaptureSet {}) n} →
    Rebind (TypeEnv.extend_cvars env m a1 CS) (Rename.id.liftCVars n)
      (TypeEnv.extend_cvars env m a2 CS)
  | 0, _ => Rebind.refl
  | _ + 1, CS =>
    ((Rebind.auth_irrel_cvars (CS := List.Vector.tail CS)).liftCVar (List.Vector.head CS)
        (cap := (List.Vector.head CS).ground_denot m) (a := a1)).comp Rebind.auth_irrel

/-- Re-tagging the authority of *all* `n` evidence binders leaves `val_denot`
unchanged (authority is denotationally inert). -/
theorem val_denot_auth_irrel_cvars {s : Sig} {env : TypeEnv s} {m : Memory}
    {a1 a2 : Authority} {n : Nat} {CS : List.Vector (CaptureSet {}) n}
    (T : Ty .capt (Sig.extendCVars s n)) :
    IDenot.Equiv (Ty.val_denot (TypeEnv.extend_cvars env m a1 CS) T)
      (Ty.val_denot (TypeEnv.extend_cvars env m a2 CS) T) := by
  have h := rebind_val_denot (Rebind.auth_irrel_cvars (env := env) (m := m)
    (a1 := a1) (a2 := a2) (CS := CS)) T
  rw [Rename.liftCVars_id, Ty.rename_id] at h
  exact h

theorem typed_env_satisfy_rebind
  {env1 : TypeEnv s1} {env2 : TypeEnv s2} {f : Rename s1 s2}
  {Ψ : ModalCtx s1} {m : Memory}
  (ρ : Rebind env1 f env2)
  (hsat : TypeEnv.Satisfy env1 Ψ m) :
  TypeEnv.Satisfy env2 (Ψ.rename f) m := by
  exact (rebind_satisfy_iff ρ Ψ m).1 hsat

theorem typed_env_lookup_lock_satisfy
  (hlookup : Ctx.LookupLock Γ ℓ Ψ)
  (ht : EnvTyping Γ env k st m) :
  env.Satisfy Ψ m := by
  induction hlookup generalizing m with
  | here =>
    rename_i Γ0 Ψ0
    cases env with
    | extend env0 info =>
      cases info with
      | lock =>
        simp only [EnvTyping] at ht
        exact typed_env_satisfy_rebind (Rebind.lweaken (env := env0)) ht.1
  | there hlookup ih =>
    rename_i Ψ0 b
    cases b with
    | var T =>
      cases env with
      | extend env0 info =>
        cases info with
        | var n ps =>
          simp only [EnvTyping] at ht
          exact typed_env_satisfy_rebind
            (Rebind.weaken (env := env0) (x := n) (ps := ps))
            (ih ht.2.2)
    | tvar S =>
      cases env with
      | extend env0 info =>
        cases info with
        | tvar d =>
          simp only [EnvTyping] at ht
          exact typed_env_satisfy_rebind
            (Rebind.tweaken (env := env0) (d := d))
            (ih ht.2.2.2.2.2)
    | cvar B =>
      cases env with
      | extend env0 info =>
        cases info with
        | cvar a cs cap =>
          simp only [EnvTyping] at ht
          exact typed_env_satisfy_rebind
            (Rebind.cweaken (env := env0) (cs := cs) (cap := cap))
            (ih ht.2.2.2.2.2.2)
    | lock Ψ1 =>
      cases env with
      | extend env0 info =>
        cases info with
        | lock =>
          simp only [EnvTyping] at ht
          exact typed_env_satisfy_rebind (Rebind.lweaken (env := env0))
            (ih ht.2)

lemma weaken_val_denot {env : TypeEnv s} {T : Ty .capt s} {x : Nat} {ps : PeakSet s} :
  IDenot.Equiv (Ty.val_denot env T)
    (Ty.val_denot (env.extend_var x ps) (T.rename Rename.succ)) := by
  apply rebind_val_denot (ρ:=Rebind.weaken) (T:=T)

lemma weaken_exi_val_denot {env : TypeEnv s} {T : Ty .exi s} {x : Nat} {ps : PeakSet s} :
  IDenot.Equiv (Ty.exi_val_denot env T)
    (Ty.exi_val_denot (env.extend_var x ps) (T.rename Rename.succ)) := by
  apply rebind_exi_val_denot (ρ:=Rebind.weaken) (T:=T)

lemma tweaken_val_denot {env : TypeEnv s} {T : Ty .capt s} :
  IDenot.Equiv (Ty.val_denot env T)
    (Ty.val_denot (env.extend_tvar d) (T.rename Rename.succ)) := by
  apply rebind_val_denot (ρ:=Rebind.tweaken) (T:=T)

lemma tweaken_exi_val_denot {env : TypeEnv s} {T : Ty .exi s} :
  IDenot.Equiv (Ty.exi_val_denot env T)
    (Ty.exi_val_denot (env.extend_tvar d) (T.rename Rename.succ)) := by
  apply rebind_exi_val_denot (ρ:=Rebind.tweaken) (T:=T)

lemma cweaken_val_denot {env : TypeEnv s} {cs : CaptureSet {}} {cap : CapabilitySet}
  {a : Authority} {T : Ty .capt s} :
  IDenot.Equiv (Ty.val_denot env T)
    (Ty.val_denot (env.extend_cvar cs cap a) (T.rename Rename.succ)) := by
  apply rebind_val_denot (ρ:=Rebind.cweaken) (T:=T)

lemma cweaken_exi_val_denot {env : TypeEnv s} {cs : CaptureSet {}} {cap : CapabilitySet}
  {a : Authority} {T : Ty .exi s} :
  IDenot.Equiv (Ty.exi_val_denot env T)
    (Ty.exi_val_denot (env.extend_cvar cs cap a) (T.rename Rename.succ)) := by
  apply rebind_exi_val_denot (ρ:=Rebind.cweaken) (T:=T)

lemma cweakenCVars_exi_val_denot {env : TypeEnv s} {m : Memory} {a : Authority}
  {n : Nat} {CS : List.Vector (CaptureSet {}) n} {T : Ty .exi s} :
  IDenot.Equiv (Ty.exi_val_denot env T)
    (Ty.exi_val_denot (TypeEnv.extend_cvars env m a CS) (T.rename (Rename.weakenCVars n))) := by
  apply rebind_exi_val_denot (ρ:=Rebind.cweakenCVars (m:=m) (a:=a)) (T:=T)

lemma lweaken_val_denot {env : TypeEnv s} {T : Ty .capt s} :
  IDenot.Equiv (Ty.val_denot env T)
    (Ty.val_denot (env.extend_lock) (T.rename Rename.succ)) := by
  apply rebind_val_denot (ρ:=Rebind.lweaken) (T:=T)

lemma lweaken_exi_val_denot {env : TypeEnv s} {T : Ty .exi s} :
  IDenot.Equiv (Ty.exi_val_denot env T)
    (Ty.exi_val_denot (env.extend_lock) (T.rename Rename.succ)) := by
  apply rebind_exi_val_denot (ρ:=Rebind.lweaken) (T:=T)

end CoreCapybara
