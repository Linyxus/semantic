import Semantic.CC.Denotation.Core
namespace CC

structure Rebind (env1 : TypeEnv s1) (f : Rename s1 s2) (env2 : TypeEnv s2) : Prop where
  var :
    ∀ (x : BVar s1 k),
      env1.lookup x = env2.lookup (f.var x)

def Rebind.liftVar
  (ρ : Rebind env1 f env2) :
  Rebind (env1.extend_var x R) (f.lift) (env2.extend_var x R) where
  var := fun
    | .here => rfl
    | .there y => by
      simp [TypeEnv.extend_var, Rename.lift, TypeEnv.lookup]
      exact ρ.var y

def Rebind.liftTVar
  (ρ : Rebind env1 f env2) :
  Rebind (env1.extend_tvar d) (f.lift) (env2.extend_tvar d) where
  var := fun
    | .here => rfl
    | .there y => by
      simp [TypeEnv.extend_tvar, Rename.lift, TypeEnv.lookup]
      exact ρ.var y

def Rebind.liftCVar
  (ρ : Rebind env1 f env2) :
  Rebind (env1.extend_cvar c) (f.lift) (env2.extend_cvar c) where
  var := fun
    | .here => rfl
    | .there y => by
      simp [TypeEnv.extend_cvar, Rename.lift, TypeEnv.lookup]
      exact ρ.var y

/- Rebinding for CaptureSet.denot -/
theorem rebind_captureset_denot
  {s1 s2 : Sig} {env1 : TypeEnv s1} {f : Rename s1 s2} {env2 : TypeEnv s2}
  (ρ : Rebind env1 f env2) (C : CaptureSet s1) :
  CaptureSet.denot env1 C = CaptureSet.denot env2 (C.rename f) := by
  induction C
  case empty => rfl
  case union C1 C2 ih1 ih2 =>
    simp [CaptureSet.denot, CaptureSet.rename, ih1, ih2]
  case var x =>
    cases x
    case bound x =>
      simp [CaptureSet.denot, CaptureSet.rename, Var.rename]
      have h := ρ.var x
      cases k : env1.lookup x
      case var n1 =>
        simp [k] at h
        simp [TypeEnv.lookup_var, k, h]
    case free n =>
      simp [CaptureSet.denot, CaptureSet.rename, Var.rename]
  case cvar c =>
    simp [CaptureSet.denot, CaptureSet.rename]
    have h := ρ.var c
    cases k : env1.lookup c
    case cvar c0 =>
      simp [k] at h
      simp [TypeEnv.lookup_cvar, k, h]

theorem rebind_capturebound_denot
  {s1 s2 : Sig} {env1 : TypeEnv s1} {f : Rename s1 s2} {env2 : TypeEnv s2}
  (ρ : Rebind env1 f env2) (B : CaptureBound s1) :
  CaptureBound.denot env1 B = CaptureBound.denot env2 (B.rename f) := by
  cases B
  case unbound => rfl
  case bound C =>
    simp [CaptureBound.denot, CaptureBound.rename]
    exact rebind_captureset_denot ρ C

mutual

def rebind_shape_val_denot
  {s1 s2 : Sig} {env1 : TypeEnv s1} {f : Rename s1 s2} {env2 : TypeEnv s2}
  (ρ : Rebind env1 f env2) (T : Ty .shape s1) :
  Ty.shape_val_denot env1 T ≈ Ty.shape_val_denot env2 (T.rename f) :=
  match T with
  | .top => by
    apply PreDenot.eq_to_equiv
    funext A
    simp [Ty.shape_val_denot, Ty.rename]
  | .tvar X => by
    apply PreDenot.eq_to_equiv
    have h := ρ.var X
    cases k : env1.lookup X
    case tvar d =>
      simp [k] at h
      simp [Ty.shape_val_denot, Ty.rename, TypeEnv.lookup_tvar, k, h]
  | .unit => by
    apply PreDenot.eq_to_equiv
    funext A
    simp [Ty.shape_val_denot, Ty.rename]
  | .cap => by
    intro A s0 e0
    simp [Ty.shape_val_denot, Ty.rename]
  | .arrow T1 T2 => by
    have ih1 := rebind_capt_val_denot ρ T1
    intro A s0 e0
    simp [Ty.shape_val_denot, Ty.rename]
    constructor
    · intro h
      obtain ⟨cs, T0, t0, hr, hd⟩ := h
      use cs, T0, t0
      apply And.intro hr
      intro arg H' hsub harg
      cases T1
      case capt C S =>
        have ih2 := rebind_exi_exp_denot (ρ.liftVar (x:=arg) (R:=reachability_of_loc H' arg)) T2
        have harg' := (ih1 _ _).mpr harg
        specialize hd arg H' hsub harg'
        -- The capability set (A ∪ reachability_of_loc H' arg) is environment-invariant
        exact (ih2 (A ∪ (reachability_of_loc H' arg)) H' _).mp hd
    · intro h
      obtain ⟨cs0, T0, t0, hr, hd⟩ := h
      use cs0, T0, t0
      apply And.intro hr
      intro arg H' hsub harg
      cases T1
      case capt C S =>
        have ih2 := rebind_exi_exp_denot (ρ.liftVar (x:=arg) (R:=reachability_of_loc H' arg)) T2
        have harg' := (ih1 _ _).mp harg
        specialize hd arg H' hsub harg'
        -- The capability set (A ∪ reachability_of_loc H' arg) is environment-invariant
        exact (ih2 (A ∪ (reachability_of_loc H' arg)) H' _).mpr hd
  | .poly T1 T2 => by
    have ih1 := rebind_shape_val_denot ρ T1
    intro A s0 e0
    simp [Ty.shape_val_denot, Ty.rename]
    constructor
    · intro h
      obtain ⟨cs0, S0, t0, hr, hd⟩ := h
      use cs0, S0, t0
      apply And.intro hr
      intro H' denot hsub hproper himply
      have ih2 := rebind_exi_exp_denot (ρ.liftTVar (d:=denot)) T2
      have himply' : denot.ImplyAfter H' (Ty.shape_val_denot env1 T1) := by
        intro H'' hsub' A' e hdenot
        exact (ih1 _ _ _).mpr (himply H'' hsub' A' e hdenot)
      specialize hd H' denot hsub hproper himply'
      exact (ih2 A H' _).mp hd
    · intro h
      obtain ⟨cs0, S0, t0, hr, hd⟩ := h
      use cs0, S0, t0
      apply And.intro hr
      intro H' denot hsub hproper himply
      have ih2 := rebind_exi_exp_denot (ρ.liftTVar (d:=denot)) T2
      have himply' : denot.ImplyAfter H' (Ty.shape_val_denot env2 (T1.rename f)) := by
        intro H'' hsub' A' e hdenot
        exact (ih1 _ _ _).mp (himply H'' hsub' A' e hdenot)
      specialize hd H' denot hsub hproper himply'
      exact (ih2 A H' _).mpr hd
  | .cpoly B T => by
    have hB := rebind_capturebound_denot ρ B
    intro A s0 e0
    simp [Ty.shape_val_denot, Ty.rename, hB]
    constructor
    · intro h
      obtain ⟨cs0, B0, t0, hr, hd⟩ := h
      use cs0, B0, t0
      apply And.intro hr
      intro H' CS hsub hsub_bound
      let A0 := CS.denot TypeEnv.empty
      have ih2 := rebind_exi_exp_denot (ρ.liftCVar (c:=A0)) T
      specialize hd H' CS hsub hsub_bound
      exact (ih2 A H' _).mp hd
    · intro h
      obtain ⟨cs0, B0, t0, hr, hd⟩ := h
      use cs0, B0, t0
      apply And.intro hr
      intro H' CS hsub hsub_bound
      let A0 := CS.denot TypeEnv.empty
      have ih2 := rebind_exi_exp_denot (ρ.liftCVar (c:=A0)) T
      specialize hd H' CS hsub hsub_bound
      exact (ih2 A H' _).mpr hd

def rebind_capt_val_denot
  {s1 s2 : Sig} {env1 : TypeEnv s1} {f : Rename s1 s2} {env2 : TypeEnv s2}
  (ρ : Rebind env1 f env2) (T : Ty .capt s1) :
  Ty.capt_val_denot env1 T ≈ Ty.capt_val_denot env2 (T.rename f) :=
  match T with
  | .capt C S => by
    have hC := rebind_captureset_denot ρ C
    have hS := rebind_shape_val_denot ρ S
    intro s e
    simp [Ty.capt_val_denot, Ty.rename]
    rw [← hC]
    intro hwf
    exact hS (C.denot env1) s e

def rebind_exi_val_denot
  {s1 s2 : Sig} {env1 : TypeEnv s1} {f : Rename s1 s2} {env2 : TypeEnv s2}
  (ρ : Rebind env1 f env2) (T : Ty .exi s1) :
  Ty.exi_val_denot env1 T ≈ Ty.exi_val_denot env2 (T.rename f) :=
  match T with
  | .typ T => by
    have ih := rebind_capt_val_denot ρ T
    intro s e
    simp [Ty.exi_val_denot, Ty.rename]
    exact ih s e
  | .exi T => by
    intro s e
    simp [Ty.exi_val_denot, Ty.rename]
    constructor
    · intro h
      obtain ⟨A, hval⟩ := h
      use A
      have ih := rebind_capt_val_denot (ρ.liftCVar (c:=A)) T
      exact (ih s e).mp hval
    · intro h
      obtain ⟨A, hval⟩ := h
      use A
      have ih := rebind_capt_val_denot (ρ.liftCVar (c:=A)) T
      exact (ih s e).mpr hval

def rebind_capt_exp_denot
  {s1 s2 : Sig} {env1 : TypeEnv s1} {f : Rename s1 s2} {env2 : TypeEnv s2}
  (ρ : Rebind env1 f env2) (T : Ty .capt s1) :
  Ty.capt_exp_denot env1 T ≈ Ty.capt_exp_denot env2 (T.rename f) := by
  have ih := rebind_capt_val_denot ρ T
  intro A s e
  simp [Ty.capt_exp_denot]
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
  (ρ : Rebind env1 f env2) (T : Ty .exi s1) :
  Ty.exi_exp_denot env1 T ≈ Ty.exi_exp_denot env2 (T.rename f) := by
  have ih := rebind_exi_val_denot ρ T
  intro A s e
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

def Rebind.weaken {env : TypeEnv s} {x : Nat} {R : CapabilitySet} :
  Rebind env Rename.succ (env.extend_var x R) where
  var := fun _ => rfl

def Rebind.tweaken {env : TypeEnv s} {d : PreDenot} :
  Rebind env Rename.succ (env.extend_tvar d) where
  var := fun _ => rfl

def Rebind.cweaken {env : TypeEnv s} {c : CapabilitySet} :
  Rebind env Rename.succ (env.extend_cvar c) where
  var := fun _ => rfl

lemma weaken_shape_val_denot {env : TypeEnv s} {T : Ty .shape s} :
  Ty.shape_val_denot env T ≈ Ty.shape_val_denot (env.extend_var x R) (T.rename Rename.succ) := by
  apply rebind_shape_val_denot (ρ:=Rebind.weaken) (T:=T)

lemma weaken_capt_val_denot {env : TypeEnv s} {T : Ty .capt s} :
  Ty.capt_val_denot env T ≈ Ty.capt_val_denot (env.extend_var x R) (T.rename Rename.succ) := by
  apply rebind_capt_val_denot (ρ:=Rebind.weaken) (T:=T)

lemma weaken_exi_val_denot {env : TypeEnv s} {T : Ty .exi s} :
  Ty.exi_val_denot env T ≈ Ty.exi_val_denot (env.extend_var x R) (T.rename Rename.succ) := by
  apply rebind_exi_val_denot (ρ:=Rebind.weaken) (T:=T)

lemma tweaken_shape_val_denot {env : TypeEnv s} {T : Ty .shape s} :
  Ty.shape_val_denot env T ≈ Ty.shape_val_denot (env.extend_tvar d) (T.rename Rename.succ) := by
  apply rebind_shape_val_denot (ρ:=Rebind.tweaken) (T:=T)

lemma tweaken_capt_val_denot {env : TypeEnv s} {T : Ty .capt s} :
  Ty.capt_val_denot env T ≈ Ty.capt_val_denot (env.extend_tvar d) (T.rename Rename.succ) := by
  apply rebind_capt_val_denot (ρ:=Rebind.tweaken) (T:=T)

lemma tweaken_exi_val_denot {env : TypeEnv s} {T : Ty .exi s} :
  Ty.exi_val_denot env T ≈ Ty.exi_val_denot (env.extend_tvar d) (T.rename Rename.succ) := by
  apply rebind_exi_val_denot (ρ:=Rebind.tweaken) (T:=T)

lemma cweaken_shape_val_denot {env : TypeEnv s} {T : Ty .shape s} :
  Ty.shape_val_denot env T ≈ Ty.shape_val_denot (env.extend_cvar c) (T.rename Rename.succ) := by
  apply rebind_shape_val_denot (ρ:=Rebind.cweaken) (T:=T)

lemma cweaken_capt_val_denot {env : TypeEnv s} {T : Ty .capt s} :
  Ty.capt_val_denot env T ≈ Ty.capt_val_denot (env.extend_cvar c) (T.rename Rename.succ) := by
  apply rebind_capt_val_denot (ρ:=Rebind.cweaken) (T:=T)

lemma cweaken_exi_val_denot {env : TypeEnv s} {T : Ty .exi s} :
  Ty.exi_val_denot env T ≈ Ty.exi_val_denot (env.extend_cvar c) (T.rename Rename.succ) := by
  apply rebind_exi_val_denot (ρ:=Rebind.cweaken) (T:=T)

end CC
