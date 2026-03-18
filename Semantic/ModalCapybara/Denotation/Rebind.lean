import Semantic.ModalCapybara.Denotation.Core
namespace ModalCapybara

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
      simp only [TypeEnv.extend_var, TypeEnv.lookup_var]
      unfold PeakSet.rename
      congr 1
      rw [CaptureSet.rename_comp, Rename.succ_lift_comm,
          ← CaptureSet.rename_comp]
      exact congrArg (CaptureSet.rename · Rename.succ)
        (congrArg PeakSet.cs hps)
    | .there y => by
      simp only [TypeEnv.extend_var, TypeEnv.lookup_var]
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
      simp only [TypeEnv.extend_tvar, TypeEnv.lookup_var]
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
  (ρ : Rebind env1 f env2) (cs : CaptureSet {}) (cap : CapabilitySet := .empty) :
  Rebind (env1.extend_cvar cs cap) (f.lift) (env2.extend_cvar cs cap) where
  var := fun
    | .there y => by
      simp only [TypeEnv.extend_cvar, Rename.lift, TypeEnv.lookup_var]
      exact ρ.var y
  var_peaks := fun
    | .there y => by
      simp only [TypeEnv.extend_cvar, TypeEnv.lookup_var]
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

theorem rebind_resolved_capture_set {C : CaptureSet s1}
  (ρ : Rebind env1 f env2) :
  C.subst (Subst.from_TypeEnv env1) =
    (C.rename f).subst (Subst.from_TypeEnv env2) := by
  induction C with
  | empty =>
    simp [CaptureSet.subst, CaptureSet.rename]
  | union C1 C2 ih1 ih2 =>
    simp [CaptureSet.subst, CaptureSet.rename, ih1, ih2]
  | var m x =>
    cases x with
    | free n =>
      simp [CaptureSet.subst, CaptureSet.rename, Var.subst, Var.rename]
    | bound x =>
      have h := ρ.var x
      simp [CaptureSet.subst, CaptureSet.rename, Var.subst, Var.rename,
            Subst.from_TypeEnv]
      rw [<-h]
  | cvar m x =>
    have h := ρ.cvar x
    simp [CaptureSet.subst, CaptureSet.rename, Subst.from_TypeEnv]
    rw [<-h]

/- Rebinding for CaptureSet.denot -/
theorem rebind_captureset_denot
  {s1 s2 : Sig} {env1 : TypeEnv s1} {f : Rename s1 s2} {env2 : TypeEnv s2}
  (ρ : Rebind env1 f env2) (C : CaptureSet s1) :
  CaptureSet.denot env1 C = CaptureSet.denot env2 (C.rename f) := by
  -- Use rebind_resolved_capture_set
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
      rw [CaptureSet.applyMut_rename, h]

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
  {m : Mutability} {c : BVar s2 .cvar}
  (hsub : (.cvar m c) ⊆ cs.rename f) :
  ∃ c', f.var c' = c ∧ (.cvar m c') ⊆ cs := by
  induction hpo with
  | empty =>
    simp [CaptureSet.rename] at hsub
    cases hsub
  | cvar =>
    simp [CaptureSet.rename] at hsub
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
  (ρ : Rebind env1 f env2) (Ψ : SepCtx s1) (m : Memory) :
  TypeEnv.Satisfy env1 Ψ m ↔ TypeEnv.Satisfy env2 (Ψ.rename f) m := by
  constructor
  · intro hsat
    constructor
    · intro C mode hhas
      obtain ⟨C0, rfl, hhas0⟩ := SepCtx.Has.rename_inv hhas
      simpa only [rebind_resolved_capture_set (ρ := ρ) (C := C0)] using
        hsat.wf C0 mode hhas0
    · intro C mode hhas
      obtain ⟨C0, rfl, hhas0⟩ := SepCtx.Has.rename_inv hhas
      simpa only [rebind_captureset_denot (ρ := ρ) (C := C0)] using
        hsat.kind C0 mode hhas0
    · intro C1 m1 C2 m2 hdistinct
      obtain ⟨D1, D2, rfl, rfl, hdistinct0⟩ := SepCtx.HasTwoDistinct.rename_inv hdistinct
      simpa only [rebind_captureset_denot (ρ := ρ) (C := D1),
        rebind_captureset_denot (ρ := ρ) (C := D2)] using
        hsat.sep D1 m1 D2 m2 hdistinct0
  · intro hsat
    constructor
    · intro C mode hhas
      have hhas' := hhas.rename (f := f)
      simpa only [rebind_resolved_capture_set (ρ := ρ) (C := C)] using
        hsat.wf (C.rename f) mode hhas'
    · intro C mode hhas
      have hhas' := hhas.rename (f := f)
      simpa only [rebind_captureset_denot (ρ := ρ) (C := C)] using
        hsat.kind (C.rename f) mode hhas'
    · intro C1 m1 C2 m2 hdistinct
      have hdistinct' := hdistinct.rename (f := f)
      simpa only [rebind_captureset_denot (ρ := ρ) (C := C1),
        rebind_captureset_denot (ρ := ρ) (C := C2)] using
        hsat.sep (C1.rename f) m1 (C2.rename f) m2 hdistinct'

set_option maxHeartbeats 1000000 in
-- The mutual rebind denotation definitions trigger heavy reducibility checks after the
-- modal branch started carrying higher-order assumption transport.
mutual

def rebind_val_denot
  {s1 s2 : Sig} {env1 : TypeEnv s1} {f : Rename s1 s2} {env2 : TypeEnv s2}
  (ρ : Rebind env1 f env2) (T : Ty .capt s1) :
  Ty.val_denot env1 T ≈ Ty.val_denot env2 (T.rename f) :=
  match T with
  | .top => by
    intro m e
    simp [Ty.val_denot, Ty.rename]
  | .tvar X => by
    have h := ρ.tvar X
    intro m e
    simp [Ty.val_denot, Ty.rename, h]
  | .unit => by
    intro m e
    simp [Ty.val_denot, Ty.rename]
  | .bool => by
    intro m e
    simp [Ty.val_denot, Ty.rename]
  | .cap cs => by
    intro m e
    simp only [Ty.val_denot, Ty.rename]
    rw [← rebind_resolved_capture_set ρ]
    rw [← rebind_captureset_denot ρ cs]
  | .cell cs => by
    intro m e
    simp only [Ty.val_denot, Ty.rename]
    rw [← rebind_resolved_capture_set ρ]
    rw [← rebind_captureset_denot ρ cs]
  | .reader cs => by
    intro m e
    simp only [Ty.val_denot, Ty.rename]
    rw [← rebind_resolved_capture_set ρ]
    rw [← rebind_captureset_denot ρ cs]
  | .arrow T1 cs T2 => by
    have ih1 := rebind_val_denot ρ T1
    intro m e
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
      intro arg m' hsub harg
      let R0 := expand_captures m.heap cs'
      let ps1 := compute_peakset env1 T1.captureSet
      let ps2 := compute_peakset env2 (T1.rename f).captureSet
      have ih2 := rebind_exi_exp_denot (ρ.liftVar (x:=arg) ps1 ps2 hps) T2 R0
      have harg' := (ih1 m' (.var (.free arg))).mpr harg
      specialize hd arg m' hsub harg'
      exact (ih2 m' _).mp hd
    · intro ⟨hwf_e, hwf_cs, cs', T0, t0, hr, hwf_cs', hR0_sub, hd⟩
      refine ⟨hwf_e, hwf_cs, cs', T0, t0, hr, hwf_cs', hR0_sub, ?_⟩
      intro arg m' hsub harg
      let R0 := expand_captures m.heap cs'
      let ps1 := compute_peakset env1 T1.captureSet
      let ps2 := compute_peakset env2 (T1.rename f).captureSet
      have ih2 := rebind_exi_exp_denot (ρ.liftVar (x:=arg) ps1 ps2 hps) T2 R0
      have harg' := (ih1 m' (.var (.free arg))).mp harg
      specialize hd arg m' hsub harg'
      exact (ih2 m' _).mpr hd
  | .poly T1 cs T2 => by
    have ih1 := rebind_val_denot ρ T1
    intro m e
    simp only [Ty.val_denot, Ty.rename]
    rw [← rebind_resolved_capture_set ρ]
    rw [← rebind_captureset_denot ρ cs]
    constructor
    · intro ⟨hwf_e, hwf_cs, cs', S0, t0, hr, hwf_cs', hR0_sub, hd⟩
      refine ⟨hwf_e, hwf_cs, cs', S0, t0, hr, hwf_cs', hR0_sub, ?_⟩
      intro m' denot hsub hproper himply_simple_ans himply hpure
      let R0 := expand_captures m.heap cs'
      have ih2 := rebind_exi_exp_denot (ρ.liftTVar (d:=denot)) T2 R0
      have himply' : denot.ImplyAfter m' (Ty.val_denot env1 T1) := by
        intro m'' hsub' e' hdenot
        exact (ih1 m'' e').mpr (himply m'' hsub' e' hdenot)
      specialize hd m' denot hsub hproper himply_simple_ans himply' hpure
      exact (ih2 m' _).mp hd
    · intro ⟨hwf_e, hwf_cs, cs', S0, t0, hr, hwf_cs', hR0_sub, hd⟩
      refine ⟨hwf_e, hwf_cs, cs', S0, t0, hr, hwf_cs', hR0_sub, ?_⟩
      intro m' denot hsub hproper himply_simple_ans himply hpure
      let R0 := expand_captures m.heap cs'
      have ih2 := rebind_exi_exp_denot (ρ.liftTVar (d:=denot)) T2 R0
      have himply' : denot.ImplyAfter m' (Ty.val_denot env2 (T1.rename f)) := by
        intro m'' hsub' e' hdenot
        exact (ih1 m'' e').mp (himply m'' hsub' e' hdenot)
      specialize hd m' denot hsub hproper himply_simple_ans himply' hpure
      exact (ih2 m' _).mpr hd
  | .cpoly B cs T => by
    have hB := rebind_capturebound_denot ρ B
    intro m e
    simp only [Ty.val_denot, Ty.rename]
    rw [← rebind_resolved_capture_set ρ]
    rw [← rebind_captureset_denot ρ cs]
    rw [hB]
    constructor
    · intro ⟨hwf_e, hwf_cs, cs', B0, t0, hr, hwf_cs', hR0_sub, hd⟩
      refine ⟨hwf_e, hwf_cs, cs', B0, t0, hr, hwf_cs', hR0_sub, ?_⟩
      intro m' CS hwf_CS hsub hsub_bound
      let R0 := expand_captures m.heap cs'
      have ih2 := rebind_exi_exp_denot (ρ.liftCVar CS (cap := CS.ground_denot m')) T R0
      specialize hd m' CS hwf_CS hsub hsub_bound
      exact (ih2 m' _).mp hd
    · intro ⟨hwf_e, hwf_cs, cs', B0, t0, hr, hwf_cs', hR0_sub, hd⟩
      refine ⟨hwf_e, hwf_cs, cs', B0, t0, hr, hwf_cs', hR0_sub, ?_⟩
      intro m' CS hwf_CS hsub hsub_bound
      let R0 := expand_captures m.heap cs'
      have ih2 := rebind_exi_exp_denot (ρ.liftCVar CS (cap := CS.ground_denot m')) T R0
      specialize hd m' CS hwf_CS hsub hsub_bound
      exact (ih2 m' _).mpr hd
  | .modal cs Ψ T => by
    intro m e
    simp only [Ty.val_denot, Ty.rename]
    rw [← rebind_resolved_capture_set ρ]
    rw [← rebind_captureset_denot ρ cs]
    constructor
    · rintro ⟨hwf_e, hwf_cs, cs0, sepctx0, t0, hres, hwf_cs0, hwf_sepctx0,
        hsat, hR0_sub, hbody⟩
      refine ⟨hwf_e, hwf_cs, cs0, sepctx0, t0, hres, hwf_cs0, hwf_sepctx0, ?_, hR0_sub, ?_⟩
      · intro m' hsub hsat'
        exact hsat m' hsub ((rebind_satisfy_iff ρ Ψ m').mpr hsat')
      · intro m' hsub hkind hsep
        let R0 := expand_captures m.heap cs0
        have ih := rebind_exi_exp_denot ρ T R0
        exact (ih m' _).mp (hbody m' hsub hkind hsep)
    · rintro ⟨hwf_e, hwf_cs, cs0, sepctx0, t0, hres, hwf_cs0, hwf_sepctx0,
        hsat, hR0_sub, hbody⟩
      refine ⟨hwf_e, hwf_cs, cs0, sepctx0, t0, hres, hwf_cs0, hwf_sepctx0, ?_, hR0_sub, ?_⟩
      · intro m' hsub hsat'
        exact hsat m' hsub ((rebind_satisfy_iff ρ Ψ m').mp hsat')
      · intro m' hsub hkind hsep
        let R0 := expand_captures m.heap cs0
        have ih := rebind_exi_exp_denot ρ T R0
        exact (ih m' _).mpr (hbody m' hsub hkind hsep)

def rebind_exi_val_denot
  {s1 s2 : Sig} {env1 : TypeEnv s1} {f : Rename s1 s2} {env2 : TypeEnv s2}
  (ρ : Rebind env1 f env2) (T : Ty .exi s1) :
  Ty.exi_val_denot env1 T ≈ Ty.exi_val_denot env2 (T.rename f) :=
  match T with
  | .typ T => by
    have ih := rebind_val_denot ρ T
    intro m e
    simp [Ty.exi_val_denot, Ty.rename]
    exact ih m e
  | .exi T => by
    intro m e
    simp only [Ty.exi_val_denot, Ty.rename]
    -- Both sides are match expressions on resolve m.heap e
    cases hresolve : resolve m.heap e
    · -- resolve = none
      simp
    · -- resolve = some e'
      rename_i e'
      cases e'
      case pack =>
        rename_i CS y
        simp
        -- Goal: CS.WfInHeap m.heap → (... ↔ ...)
        intro _hwf
        have ih := rebind_val_denot (ρ.liftCVar CS (cap := CS.ground_denot m)) T
        exact ih m (Exp.var y)
      all_goals {
        -- resolve returned non-pack
        simp
      }

def rebind_exp_denot
  {s1 s2 : Sig} {env1 : TypeEnv s1} {f : Rename s1 s2} {env2 : TypeEnv s2}
  (ρ : Rebind env1 f env2) (T : Ty .capt s1) (R : CapabilitySet) :
  Ty.exp_denot env1 T R ≈ Ty.exp_denot env2 (T.rename f) R := by
  have ih := rebind_val_denot ρ T
  intro m e
  simp [Ty.exp_denot]
  constructor
  · intro h
    apply eval_post_monotonic _ h
    apply Denot.imply_to_entails
    exact (Denot.equiv_to_imply ih).1
  · intro h
    apply eval_post_monotonic _ h
    apply Denot.imply_to_entails
    exact (Denot.equiv_to_imply ih).2

def rebind_exi_exp_denot
  {s1 s2 : Sig} {env1 : TypeEnv s1} {f : Rename s1 s2} {env2 : TypeEnv s2}
  (ρ : Rebind env1 f env2) (T : Ty .exi s1) (R : CapabilitySet) :
  Ty.exi_exp_denot env1 T R ≈ Ty.exi_exp_denot env2 (T.rename f) R := by
  have ih := rebind_exi_val_denot ρ T
  intro m e
  simp [Ty.exi_exp_denot]
  constructor
  · intro h
    apply eval_post_monotonic _ h
    apply Denot.imply_to_entails
    exact (Denot.equiv_to_imply ih).1
  · intro h
    apply eval_post_monotonic _ h
    apply Denot.imply_to_entails
    exact (Denot.equiv_to_imply ih).2

end

def Rebind.weaken {env : TypeEnv s} {x : Nat} {ps : PeakSet s} :
  Rebind env Rename.succ (env.extend_var x ps) where
  var := fun _ => rfl
  var_peaks := fun _ => rfl
  tvar := fun _ => rfl
  cvar := fun _ => rfl
  cvar_injective := fun _ _ h => BVar.there.inj h

def Rebind.tweaken {env : TypeEnv s} {d : Denot} :
  Rebind env Rename.succ (env.extend_tvar d) where
  var := fun _ => rfl
  var_peaks := fun _ => rfl
  tvar := fun _ => rfl
  cvar := fun _ => rfl
  cvar_injective := fun _ _ h => BVar.there.inj h

def Rebind.cweaken {env : TypeEnv s} {cs : CaptureSet {}} {cap : CapabilitySet} :
  Rebind env Rename.succ (env.extend_cvar cs cap) where
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

theorem typed_env_satisfy_rebind
  {env1 : TypeEnv s1} {env2 : TypeEnv s2} {f : Rename s1 s2}
  {Ψ : SepCtx s1} {m : Memory}
  (ρ : Rebind env1 f env2)
  (hsat : TypeEnv.Satisfy env1 Ψ m) :
  TypeEnv.Satisfy env2 (Ψ.rename f) m := by
  constructor
  · intro C mode hhas
    obtain ⟨C0, rfl, hhas0⟩ := SepCtx.Has.rename_inv hhas
    simpa only [rebind_resolved_capture_set (ρ := ρ) (C := C0)] using
      hsat.wf C0 mode hhas0
  · intro C mode hhas
    obtain ⟨C0, rfl, hhas0⟩ := SepCtx.Has.rename_inv hhas
    simpa only [rebind_captureset_denot (ρ := ρ) (C := C0)] using
      hsat.kind C0 mode hhas0
  · intro C1 m1 C2 m2 hdistinct
    obtain ⟨D1, D2, rfl, rfl, hdistinct0⟩ := SepCtx.HasTwoDistinct.rename_inv hdistinct
    simpa only [rebind_captureset_denot (ρ := ρ) (C := D1),
      rebind_captureset_denot (ρ := ρ) (C := D2)] using
      hsat.sep D1 m1 D2 m2 hdistinct0

theorem typed_env_lookup_lock_satisfy
  (hlookup : Ctx.LookupLock Γ ℓ Ψ)
  (ht : EnvTyping Γ env m) :
  env.Satisfy Ψ m := by
  induction hlookup generalizing m with
  | here =>
    rename_i Γ0 Ψ0
    cases env with
    | extend env0 info =>
      cases info with
      | lock =>
        simp [EnvTyping] at ht
        exact typed_env_satisfy_rebind (Rebind.lweaken (env := env0)) ht.1
  | there hlookup ih =>
    rename_i Ψ0 b
    cases b with
    | var T =>
      cases env with
      | extend env0 info =>
        cases info with
        | var n ps =>
          simp [EnvTyping] at ht
          exact typed_env_satisfy_rebind
            (Rebind.weaken (env := env0) (x := n) (ps := ps))
            (ih ht.2.2)
    | tvar S =>
      cases env with
      | extend env0 info =>
        cases info with
        | tvar d =>
          simp [EnvTyping] at ht
          exact typed_env_satisfy_rebind
            (Rebind.tweaken (env := env0) (d := d))
            (ih ht.2.2.2.2.2)
    | cvar B =>
      cases env with
      | extend env0 info =>
        cases info with
        | cvar cs cap =>
          simp [EnvTyping] at ht
          exact typed_env_satisfy_rebind
            (Rebind.cweaken (env := env0) (cs := cs) (cap := cap))
            (ih ht.2.2.2.2)
    | lock Ψ1 =>
      cases env with
      | extend env0 info =>
        cases info with
        | lock =>
          simp [EnvTyping] at ht
          exact typed_env_satisfy_rebind (Rebind.lweaken (env := env0))
            (ih ht.2)

lemma weaken_val_denot {env : TypeEnv s} {T : Ty .capt s} {x : Nat} {ps : PeakSet s} :
  Ty.val_denot env T ≈ Ty.val_denot (env.extend_var x ps) (T.rename Rename.succ) := by
  apply rebind_val_denot (ρ:=Rebind.weaken) (T:=T)

lemma weaken_exi_val_denot {env : TypeEnv s} {T : Ty .exi s} {x : Nat} {ps : PeakSet s} :
  Ty.exi_val_denot env T ≈ Ty.exi_val_denot (env.extend_var x ps) (T.rename Rename.succ) := by
  apply rebind_exi_val_denot (ρ:=Rebind.weaken) (T:=T)

lemma tweaken_val_denot {env : TypeEnv s} {T : Ty .capt s} :
  Ty.val_denot env T ≈ Ty.val_denot (env.extend_tvar d) (T.rename Rename.succ) := by
  apply rebind_val_denot (ρ:=Rebind.tweaken) (T:=T)

lemma tweaken_exi_val_denot {env : TypeEnv s} {T : Ty .exi s} :
  Ty.exi_val_denot env T ≈ Ty.exi_val_denot (env.extend_tvar d) (T.rename Rename.succ) := by
  apply rebind_exi_val_denot (ρ:=Rebind.tweaken) (T:=T)

lemma cweaken_val_denot {env : TypeEnv s} {cs : CaptureSet {}} {cap : CapabilitySet}
  {T : Ty .capt s} :
  Ty.val_denot env T ≈
    Ty.val_denot (env.extend_cvar cs cap) (T.rename Rename.succ) := by
  apply rebind_val_denot (ρ:=Rebind.cweaken) (T:=T)

lemma cweaken_exi_val_denot {env : TypeEnv s} {cs : CaptureSet {}} {cap : CapabilitySet}
  {T : Ty .exi s} :
  Ty.exi_val_denot env T ≈
    Ty.exi_val_denot (env.extend_cvar cs cap) (T.rename Rename.succ) := by
  apply rebind_exi_val_denot (ρ:=Rebind.cweaken) (T:=T)

lemma lweaken_val_denot {env : TypeEnv s} {T : Ty .capt s} :
  Ty.val_denot env T ≈ Ty.val_denot (env.extend_lock) (T.rename Rename.succ) := by
  apply rebind_val_denot (ρ:=Rebind.lweaken) (T:=T)

lemma lweaken_exi_val_denot {env : TypeEnv s} {T : Ty .exi s} :
  Ty.exi_val_denot env T ≈ Ty.exi_val_denot (env.extend_lock) (T.rename Rename.succ) := by
  apply rebind_exi_val_denot (ρ:=Rebind.lweaken) (T:=T)

end ModalCapybara
