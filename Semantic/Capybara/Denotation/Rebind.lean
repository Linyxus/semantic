import Semantic.Capybara.Denotation.Core
namespace Capybara

structure Rebind (env1 : TypeEnv s1) (f : Rename s1 s2) (env2 : TypeEnv s2) : Prop where
  var :
    ∀ (x : BVar s1 .var),
      (env1.lookup_var x).1 = (env2.lookup_var (f.var x)).1
  tvar :
    ∀ (x : BVar s1 .tvar),
      env1.lookup_tvar x = env2.lookup_tvar (f.var x)
  cvar :
    ∀ (x : BVar s1 .cvar),
      env1.lookup_cvar x = env2.lookup_cvar (f.var x)

def Rebind.liftVar
  {s1 s2 : Sig} {env1 : TypeEnv s1} {env2 : TypeEnv s2} {f : Rename s1 s2}
  (ρ : Rebind env1 f env2) {x : Nat} (ps1 : PeakSet s1) (ps2 : PeakSet s2) :
  Rebind (env1.extend_var x ps1) (f.lift) (env2.extend_var x ps2) where
  var := fun
    | .here => rfl
    | .there y => by
      simp only [TypeEnv.extend_var, Rename.lift, TypeEnv.lookup_var]
      exact ρ.var y
  tvar := fun
    | .there y => by
      simp only [TypeEnv.extend_var, Rename.lift, TypeEnv.lookup_tvar]
      exact ρ.tvar y
  cvar := fun
    | .there y => by
      simp only [TypeEnv.extend_var, Rename.lift, TypeEnv.lookup_cvar]
      exact ρ.cvar y

def Rebind.liftTVar
  (ρ : Rebind env1 f env2) :
  Rebind (env1.extend_tvar d) (f.lift) (env2.extend_tvar d) where
  var := fun
    | .there y => by
      simp only [TypeEnv.extend_tvar, Rename.lift, TypeEnv.lookup_var]
      exact ρ.var y
  tvar := fun
    | .here => rfl
    | .there y => by
      simp only [TypeEnv.extend_tvar, Rename.lift, TypeEnv.lookup_tvar]
      exact ρ.tvar y
  cvar := fun
    | .there y => by
      simp only [TypeEnv.extend_tvar, Rename.lift, TypeEnv.lookup_cvar]
      exact ρ.cvar y

def Rebind.liftCVar
  (ρ : Rebind env1 f env2) (cs : CaptureSet {}) :
  Rebind (env1.extend_cvar cs) (f.lift) (env2.extend_cvar cs) where
  var := fun
    | .there y => by
      simp only [TypeEnv.extend_cvar, Rename.lift, TypeEnv.lookup_var]
      exact ρ.var y
  tvar := fun
    | .there y => by
      simp only [TypeEnv.extend_cvar, Rename.lift, TypeEnv.lookup_tvar]
      exact ρ.tvar y
  cvar := fun
    | .here => rfl
    | .there y => by
      simp only [TypeEnv.extend_cvar, Rename.lift, TypeEnv.lookup_cvar]
      exact ρ.cvar y

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

-- Mutability.denot doesn't depend on environment, so rebinding is trivial
theorem rebind_mutability_denot (B : Mutability) :
  B.denot = B.denot := rfl

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
    constructor
    · intro ⟨hwf_e, hwf_cs, cs', T0, t0, hr, hwf_cs', hR0_sub, hd⟩
      refine ⟨hwf_e, hwf_cs, cs', T0, t0, hr, hwf_cs', hR0_sub, ?_⟩
      intro arg m' hsub harg
      -- Use the computed peaksets for the rebind
      let ps1 := compute_peakset env1 T1.captureSet
      let ps2 := compute_peakset env2 (T1.rename f).captureSet
      have ih2 := rebind_exi_exp_denot (ρ.liftVar (x:=arg) ps1 ps2) T2
        (cs.rename Rename.succ ∪ .var .epsilon (.bound .here))
      have harg' := (ih1 m' (.var (.free arg))).mpr harg
      specialize hd arg m' hsub harg'
      -- Use CaptureSet.weaken_rename_comm to show capture sets are equal
      have hcs_eq : ((cs.rename Rename.succ ∪ .var .epsilon (.bound .here)).rename f.lift) =
                    ((cs.rename f).rename Rename.succ ∪ .var .epsilon (.bound .here)) := by
        conv_lhs => simp only [CaptureSet.rename]
        rw [CaptureSet.weaken_rename_comm]
        simp only [Var.rename, Rename.lift]; rfl
      rw [hcs_eq] at ih2
      exact (ih2 m' _).mp hd
    · intro ⟨hwf_e, hwf_cs, cs', T0, t0, hr, hwf_cs', hR0_sub, hd⟩
      refine ⟨hwf_e, hwf_cs, cs', T0, t0, hr, hwf_cs', hR0_sub, ?_⟩
      intro arg m' hsub harg
      let ps1 := compute_peakset env1 T1.captureSet
      let ps2 := compute_peakset env2 (T1.rename f).captureSet
      have ih2 := rebind_exi_exp_denot (ρ.liftVar (x:=arg) ps1 ps2) T2
        (cs.rename Rename.succ ∪ .var .epsilon (.bound .here))
      have harg' := (ih1 m' (.var (.free arg))).mp harg
      specialize hd arg m' hsub harg'
      have hcs_eq : ((cs.rename Rename.succ ∪ .var .epsilon (.bound .here)).rename f.lift) =
                    ((cs.rename f).rename Rename.succ ∪ .var .epsilon (.bound .here)) := by
        conv_lhs => simp only [CaptureSet.rename]
        rw [CaptureSet.weaken_rename_comm]
        simp only [Var.rename, Rename.lift]; rfl
      rw [hcs_eq] at ih2
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
      intro m' denot hsub hproper himply hpure
      have ih2 := rebind_exi_exp_denot (ρ.liftTVar (d:=denot)) T2
        (cs.rename (Rename.succ (k:=.tvar)))
      have himply' : denot.ImplyAfter m' (Ty.val_denot env1 T1) := by
        intro m'' hsub' e' hdenot
        exact (ih1 m'' e').mpr (himply m'' hsub' e' hdenot)
      specialize hd m' denot hsub hproper himply' hpure
      have hcs_eq : (cs.rename (Rename.succ (k:=.tvar))).rename (f.lift (k:=.tvar)) =
                    (cs.rename f).rename (Rename.succ (k:=.tvar)) :=
        CaptureSet.weaken_rename_comm
      rw [hcs_eq] at ih2
      exact (ih2 m' _).mp hd
    · intro ⟨hwf_e, hwf_cs, cs', S0, t0, hr, hwf_cs', hR0_sub, hd⟩
      refine ⟨hwf_e, hwf_cs, cs', S0, t0, hr, hwf_cs', hR0_sub, ?_⟩
      intro m' denot hsub hproper himply hpure
      have ih2 := rebind_exi_exp_denot (ρ.liftTVar (d:=denot)) T2
        (cs.rename (Rename.succ (k:=.tvar)))
      have himply' : denot.ImplyAfter m' (Ty.val_denot env2 (T1.rename f)) := by
        intro m'' hsub' e' hdenot
        exact (ih1 m'' e').mp (himply m'' hsub' e' hdenot)
      specialize hd m' denot hsub hproper himply' hpure
      have hcs_eq : (cs.rename (Rename.succ (k:=.tvar))).rename (f.lift (k:=.tvar)) =
                    (cs.rename f).rename (Rename.succ (k:=.tvar)) :=
        CaptureSet.weaken_rename_comm
      rw [hcs_eq] at ih2
      exact (ih2 m' _).mpr hd
  | .cpoly B cs T => by
    intro m e
    simp only [Ty.val_denot, Ty.rename]
    rw [← rebind_resolved_capture_set ρ]
    rw [← rebind_captureset_denot ρ cs]
    constructor
    · intro ⟨hwf_e, hwf_cs, cs', B0, t0, hr, hwf_cs', hR0_sub, hd⟩
      refine ⟨hwf_e, hwf_cs, cs', B0, t0, hr, hwf_cs', hR0_sub, ?_⟩
      intro m' CS hwf_CS hsub hsub_bound
      have ih2 := rebind_exi_exp_denot (ρ.liftCVar CS) T
        (cs.rename (Rename.succ (k:=.cvar)))
      specialize hd m' CS hwf_CS hsub hsub_bound
      have hcs_eq : (cs.rename (Rename.succ (k:=.cvar))).rename (f.lift (k:=.cvar)) =
                    (cs.rename f).rename (Rename.succ (k:=.cvar)) :=
        CaptureSet.weaken_rename_comm
      rw [hcs_eq] at ih2
      exact (ih2 m' _).mp hd
    · intro ⟨hwf_e, hwf_cs, cs', B0, t0, hr, hwf_cs', hR0_sub, hd⟩
      refine ⟨hwf_e, hwf_cs, cs', B0, t0, hr, hwf_cs', hR0_sub, ?_⟩
      intro m' CS hwf_CS hsub hsub_bound
      have ih2 := rebind_exi_exp_denot (ρ.liftCVar CS) T
        (cs.rename (Rename.succ (k:=.cvar)))
      specialize hd m' CS hwf_CS hsub hsub_bound
      have hcs_eq : (cs.rename (Rename.succ (k:=.cvar))).rename (f.lift (k:=.cvar)) =
                    (cs.rename f).rename (Rename.succ (k:=.cvar)) :=
        CaptureSet.weaken_rename_comm
      rw [hcs_eq] at ih2
      exact (ih2 m' _).mpr hd

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
        have ih := rebind_val_denot (ρ.liftCVar CS) T
        exact ih m (Exp.var y)
      all_goals {
        -- resolve returned non-pack
        simp
      }

def rebind_exp_denot
  {s1 s2 : Sig} {env1 : TypeEnv s1} {f : Rename s1 s2} {env2 : TypeEnv s2}
  (ρ : Rebind env1 f env2) (T : Ty .capt s1) (cs : CaptureSet s1) :
  Ty.exp_denot env1 T cs ≈ Ty.exp_denot env2 (T.rename f) (cs.rename f) := by
  have ih := rebind_val_denot ρ T
  have hcs := rebind_captureset_denot ρ cs
  intro m e
  simp [Ty.exp_denot]
  rw [← hcs]
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
  (ρ : Rebind env1 f env2) (T : Ty .exi s1) (cs : CaptureSet s1) :
  Ty.exi_exp_denot env1 T cs ≈ Ty.exi_exp_denot env2 (T.rename f) (cs.rename f) := by
  have ih := rebind_exi_val_denot ρ T
  have hcs := rebind_captureset_denot ρ cs
  intro m e
  simp [Ty.exi_exp_denot]
  rw [← hcs]
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
  tvar := fun _ => rfl
  cvar := fun _ => rfl

def Rebind.tweaken {env : TypeEnv s} {d : Denot} :
  Rebind env Rename.succ (env.extend_tvar d) where
  var := fun _ => rfl
  tvar := fun _ => rfl
  cvar := fun _ => rfl

def Rebind.cweaken {env : TypeEnv s} {cs : CaptureSet {}} :
  Rebind env Rename.succ (env.extend_cvar cs) where
  var := fun _ => rfl
  tvar := fun _ => rfl
  cvar := fun _ => rfl

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

lemma cweaken_val_denot {env : TypeEnv s} {cs : CaptureSet {}}
  {T : Ty .capt s} :
  Ty.val_denot env T ≈
    Ty.val_denot (env.extend_cvar cs) (T.rename Rename.succ) := by
  apply rebind_val_denot (ρ:=Rebind.cweaken) (T:=T)

lemma cweaken_exi_val_denot {env : TypeEnv s} {cs : CaptureSet {}}
  {T : Ty .exi s} :
  Ty.exi_val_denot env T ≈
    Ty.exi_val_denot (env.extend_cvar cs) (T.rename Rename.succ) := by
  apply rebind_exi_val_denot (ρ:=Rebind.cweaken) (T:=T)

end Capybara
