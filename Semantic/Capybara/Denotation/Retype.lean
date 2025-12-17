import Semantic.Capybara.Denotation.Core
import Semantic.Capybara.Denotation.Rebind
namespace Capybara

/-- Interpret a variable in an environment to get its free variable index. -/
def interp_var (env : TypeEnv s) (x : Var .var s) : Nat :=
  match x with
  | .free n => n
  | .bound x => (env.lookup_var x).1

structure Retype (env1 : TypeEnv s1) (σ : Subst s1 s2) (env2 : TypeEnv s2) where
  var :
    ∀ (x : BVar s1 .var),
      (env1.lookup_var x).1 = interp_var env2 (σ.var x)

  tvar :
    ∀ (X : BVar s1 .tvar),
      env1.lookup_tvar X ≈ Ty.val_denot env2 (σ.tvar X).core

  cvar :
    ∀ (C : BVar s1 .cvar),
      env1.lookup_cvar C = (σ.cvar C).subst (Subst.from_TypeEnv env2)

lemma weaken_interp_var {x : Var .var s} {ps : PeakSet s} :
  interp_var env x = interp_var (env.extend_var n ps) (x.rename Rename.succ) := by
  cases x <;> rfl

lemma tweaken_interp_var {x : Var .var s} :
  interp_var env x = interp_var (env.extend_tvar d) (x.rename Rename.succ) := by
  cases x <;> rfl

lemma cweaken_interp_var {cs : CaptureSet {}} {x : Var .var s} :
  interp_var env x = interp_var (env.extend_cvar cs) (x.rename Rename.succ) := by
  cases x <;> rfl

theorem Retype.liftVar
  {x : Nat} {ps1 : PeakSet s1} {ps2 : PeakSet s2}
  (ρ : Retype env1 σ env2) :
  Retype (env1.extend_var x ps1) (σ.lift) (env2.extend_var x ps2) where
  var := fun
    | .here => rfl
    | .there y => by
      conv =>
        lhs
        simp only [TypeEnv.extend_var, TypeEnv.lookup_var]
      conv =>
        rhs
        simp only [Subst.lift]
        simp only [<-weaken_interp_var (ps:=ps2)]
      exact ρ.var y
  tvar := fun
    | .there X => by
      conv =>
        lhs
        simp only [TypeEnv.extend_var, TypeEnv.lookup_tvar]
      conv =>
        rhs
        simp only [Subst.lift]
      apply Denot.equiv_trans _ _ _ (ρ.tvar X)
      apply weaken_val_denot (ps:=ps2)
  cvar := fun
    | .there C => by
      simp only [TypeEnv.extend_var, Subst.lift, TypeEnv.lookup_cvar]
      rw [ρ.cvar C]
      apply rebind_resolved_capture_set (Rebind.weaken (ps:=ps2))

theorem Retype.liftTVar
  {d : Denot}
  (ρ : Retype env1 σ env2) :
  Retype (env1.extend_tvar d) (σ.lift) (env2.extend_tvar d) where
  var := fun
    | .there x => by
      conv => lhs; simp [TypeEnv.extend_tvar, TypeEnv.lookup_var]
      conv => rhs; simp [Subst.lift, <-tweaken_interp_var]
      exact ρ.var x
  tvar := fun
    | .here => by
      -- LHS: (env1.extend_tvar d).lookup_tvar .here = d
      -- RHS: Ty.val_denot (env2.extend_tvar d) (σ.lift.tvar .here).core
      --    = Ty.val_denot (env2.extend_tvar d) (.tvar .here)
      --    = (env2.extend_tvar d).lookup_tvar .here = d
      apply Denot.eq_to_equiv
      simp [TypeEnv.extend_tvar, TypeEnv.lookup_tvar, Subst.lift,
            PureTy.tvar, Ty.val_denot]
    | .there X => by
      conv =>
        lhs
        simp [TypeEnv.extend_tvar, TypeEnv.lookup_tvar]
      conv =>
        rhs
        simp [Subst.lift]
      apply Denot.equiv_trans _ _ _ (ρ.tvar X)
      apply tweaken_val_denot
  cvar := fun
    | .there C => by
      simp [TypeEnv.extend_tvar, Subst.lift]
      change env1.lookup_cvar C = _
      rw [ρ.cvar C]
      apply rebind_resolved_capture_set Rebind.tweaken

theorem Retype.liftCVar
  {cs : CaptureSet {}}
  (ρ : Retype env1 σ env2) :
  Retype (env1.extend_cvar cs) (σ.lift) (env2.extend_cvar cs) where
  var := fun
    | .there x => by
      conv => lhs; simp [TypeEnv.extend_cvar, TypeEnv.lookup_var]
      conv => rhs; simp [Subst.lift, <-cweaken_interp_var]
      exact ρ.var x
  tvar := fun
    | .there X => by
      conv =>
        lhs
        simp [TypeEnv.extend_cvar, TypeEnv.lookup_tvar]
      conv =>
        rhs
        simp [Subst.lift]
      apply Denot.equiv_trans _ _ _ (ρ.tvar X)
      apply cweaken_val_denot
  cvar := fun
    | .here => by
      simp [TypeEnv.extend_cvar, TypeEnv.lookup_cvar, Subst.lift,
        CaptureSet.subst, Subst.from_TypeEnv]
    | .there C => by
      simp [TypeEnv.extend_cvar, Subst.lift]
      change env1.lookup_cvar C = _
      rw [ρ.cvar C]
      apply rebind_resolved_capture_set Rebind.cweaken

-- Mutability.denot doesn't depend on environment, so retyping is trivial
def retype_mutability_denot (B : Mutability) :
  B.denot = B.denot := rfl

def retype_resolved_capture_set
  {s1 s2 : Sig} {env1 : TypeEnv s1} {σ : Subst s1 s2} {env2 : TypeEnv s2}
  (ρ : Retype env1 σ env2) (C : CaptureSet s1) :
  C.subst (Subst.from_TypeEnv env1) = (C.subst σ).subst (Subst.from_TypeEnv env2) := by
  induction C
  case empty => rfl
  case union C1 C2 ih1 ih2 =>
    simp [CaptureSet.subst, ih1, ih2]
  case var x =>
    cases x
    case bound x =>
      simp [CaptureSet.subst, Var.subst]
      have := ρ.var x
      cases hσ : σ.var x
      case bound y =>
        simp [Subst.from_TypeEnv, interp_var] at this ⊢
        rw [hσ] at this
        simp at this
        rw [this]
      case free n =>
        simp [Subst.from_TypeEnv, interp_var] at this ⊢
        rw [hσ] at this
        simp at this
        rw [this]
    case free n =>
      simp [CaptureSet.subst, Var.subst]
  case cvar m C =>
    simp [CaptureSet.subst]
    cases m
    · -- epsilon case: applyMut .epsilon is identity
      exact ρ.cvar C
    · -- ro case: applyMut .ro applies applyRO
      conv => lhs; simp only [Subst.from_TypeEnv]; rw [ρ.cvar C]
      simp [CaptureSet.applyRO_subst]

def retype_captureset_denot
  {s1 s2 : Sig} {env1 : TypeEnv s1} {σ : Subst s1 s2} {env2 : TypeEnv s2}
  (ρ : Retype env1 σ env2) (C : CaptureSet s1) :
  CaptureSet.denot env1 C = CaptureSet.denot env2 (C.subst σ) := by
  unfold CaptureSet.denot
  congr 1
  exact retype_resolved_capture_set ρ C

mutual

def retype_val_denot
  {s1 s2 : Sig} {env1 : TypeEnv s1} {σ : Subst s1 s2} {env2 : TypeEnv s2}
  (ρ : Retype env1 σ env2) (T : Ty .capt s1) :
  Ty.val_denot env1 T ≈ Ty.val_denot env2 (T.subst σ) :=
  match T with
  | .top => by
    intro m e
    simp [Ty.val_denot, Ty.subst]
  | .tvar X => by
    have h := ρ.tvar X
    intro m e
    simp [Ty.val_denot, Ty.subst]
    exact h m e
  | .unit => by
    intro m e
    simp [Ty.val_denot, Ty.subst]
  | .bool => by
    intro m e
    simp [Ty.val_denot, Ty.subst]
  | .cap cs => by
    intro m e
    simp only [Ty.val_denot, Ty.subst]
    rw [← retype_resolved_capture_set ρ]
    rw [← retype_captureset_denot ρ cs]
  | .cell cs => by
    intro m e
    simp only [Ty.val_denot, Ty.subst]
    rw [← retype_resolved_capture_set ρ]
    rw [← retype_captureset_denot ρ cs]
  | .reader cs => by
    intro m e
    simp only [Ty.val_denot, Ty.subst]
    rw [← retype_resolved_capture_set ρ]
    rw [← retype_captureset_denot ρ cs]
  | .arrow T1 cs T2 => by
    have ih1 := retype_val_denot ρ T1
    intro m e
    simp only [Ty.val_denot, Ty.subst]
    rw [← retype_resolved_capture_set ρ]
    rw [← retype_captureset_denot ρ cs]
    constructor
    · intro ⟨hwf_e, hwf_cs, cs', T0, t0, hr, hwf_cs', hR0_sub, hd⟩
      refine ⟨hwf_e, hwf_cs, cs', T0, t0, hr, hwf_cs', hR0_sub, ?_⟩
      intro arg m' hsub harg
      -- Use the computed peaksets for the retype
      let ps1 := compute_peakset env1 T1.captureSet
      let ps2 := compute_peakset env2 (T1.subst σ).captureSet
      have ih2 := retype_exi_exp_denot (ρ.liftVar (x:=arg) (ps1:=ps1) (ps2:=ps2)) T2
        (cs.rename Rename.succ ∪ .var .epsilon (.bound .here))
      have harg' := (ih1 m' (.var (.free arg))).mpr harg
      specialize hd arg m' hsub harg'
      -- Use CaptureSet.weaken_subst_comm_base.symm to show capture sets are equal
      have hcs_eq : ((cs.rename Rename.succ ∪ .var .epsilon (.bound .here)).subst σ.lift) =
                    ((cs.subst σ).rename Rename.succ ∪ .var .epsilon (.bound .here)) := by
        conv_lhs => simp only [CaptureSet.subst]
        rw [CaptureSet.weaken_subst_comm_base.symm]
        simp only [Var.subst, Subst.lift]; rfl
      rw [hcs_eq] at ih2
      exact (ih2 m' _).mp hd
    · intro ⟨hwf_e, hwf_cs, cs', T0, t0, hr, hwf_cs', hR0_sub, hd⟩
      refine ⟨hwf_e, hwf_cs, cs', T0, t0, hr, hwf_cs', hR0_sub, ?_⟩
      intro arg m' hsub harg
      let ps1 := compute_peakset env1 T1.captureSet
      let ps2 := compute_peakset env2 (T1.subst σ).captureSet
      have ih2 := retype_exi_exp_denot (ρ.liftVar (x:=arg) (ps1:=ps1) (ps2:=ps2)) T2
        (cs.rename Rename.succ ∪ .var .epsilon (.bound .here))
      have harg' := (ih1 m' (.var (.free arg))).mp harg
      specialize hd arg m' hsub harg'
      have hcs_eq : ((cs.rename Rename.succ ∪ .var .epsilon (.bound .here)).subst σ.lift) =
                    ((cs.subst σ).rename Rename.succ ∪ .var .epsilon (.bound .here)) := by
        conv_lhs => simp only [CaptureSet.subst]
        rw [CaptureSet.weaken_subst_comm_base.symm]
        simp only [Var.subst, Subst.lift]; rfl
      rw [hcs_eq] at ih2
      exact (ih2 m' _).mpr hd
  | .poly T1 cs T2 => by
    have ih1 := retype_val_denot ρ T1
    intro m e
    simp only [Ty.val_denot, Ty.subst]
    rw [← retype_resolved_capture_set ρ]
    rw [← retype_captureset_denot ρ cs]
    constructor
    · intro ⟨hwf_e, hwf_cs, cs', S0, t0, hr, hwf_cs', hR0_sub, hd⟩
      refine ⟨hwf_e, hwf_cs, cs', S0, t0, hr, hwf_cs', hR0_sub, ?_⟩
      intro m' denot hsub hproper himply
      have ih2 := retype_exi_exp_denot (ρ.liftTVar (d:=denot)) T2
        (cs.rename (Rename.succ (k:=.tvar)))
      have himply' : denot.ImplyAfter m' (Ty.val_denot env1 T1) := by
        intro m'' hsub' e' hdenot
        exact (ih1 m'' e').mpr (himply m'' hsub' e' hdenot)
      specialize hd m' denot hsub hproper himply'
      have hcs_eq : (cs.rename (Rename.succ (k:=.tvar))).subst (σ.lift (k:=.tvar)) =
                    (cs.subst σ).rename (Rename.succ (k:=.tvar)) :=
        CaptureSet.weaken_subst_comm_base.symm
      rw [hcs_eq] at ih2
      exact (ih2 m' _).mp hd
    · intro ⟨hwf_e, hwf_cs, cs', S0, t0, hr, hwf_cs', hR0_sub, hd⟩
      refine ⟨hwf_e, hwf_cs, cs', S0, t0, hr, hwf_cs', hR0_sub, ?_⟩
      intro m' denot hsub hproper himply
      have ih2 := retype_exi_exp_denot (ρ.liftTVar (d:=denot)) T2
        (cs.rename (Rename.succ (k:=.tvar)))
      have himply' : denot.ImplyAfter m' (Ty.val_denot env2 (T1.subst σ)) := by
        intro m'' hsub' e' hdenot
        exact (ih1 m'' e').mp (himply m'' hsub' e' hdenot)
      specialize hd m' denot hsub hproper himply'
      have hcs_eq : (cs.rename (Rename.succ (k:=.tvar))).subst (σ.lift (k:=.tvar)) =
                    (cs.subst σ).rename (Rename.succ (k:=.tvar)) :=
        CaptureSet.weaken_subst_comm_base.symm
      rw [hcs_eq] at ih2
      exact (ih2 m' _).mpr hd
  | .cpoly B cs T => by
    intro m e
    simp only [Ty.val_denot, Ty.subst]
    rw [← retype_resolved_capture_set ρ]
    rw [← retype_captureset_denot ρ cs]
    constructor
    · intro ⟨hwf_e, hwf_cs, cs', B0, t0, hr, hwf_cs', hR0_sub, hd⟩
      refine ⟨hwf_e, hwf_cs, cs', B0, t0, hr, hwf_cs', hR0_sub, ?_⟩
      intro m' CS hwf_CS hsub hsub_bound
      have ih2 := retype_exi_exp_denot (ρ.liftCVar (cs:=CS)) T
        (cs.rename (Rename.succ (k:=.cvar)))
      specialize hd m' CS hwf_CS hsub hsub_bound
      have hcs_eq : (cs.rename (Rename.succ (k:=.cvar))).subst (σ.lift (k:=.cvar)) =
                    (cs.subst σ).rename (Rename.succ (k:=.cvar)) :=
        CaptureSet.weaken_subst_comm_base.symm
      rw [hcs_eq] at ih2
      exact (ih2 m' _).mp hd
    · intro ⟨hwf_e, hwf_cs, cs', B0, t0, hr, hwf_cs', hR0_sub, hd⟩
      refine ⟨hwf_e, hwf_cs, cs', B0, t0, hr, hwf_cs', hR0_sub, ?_⟩
      intro m' CS hwf_CS hsub hsub_bound
      have ih2 := retype_exi_exp_denot (ρ.liftCVar (cs:=CS)) T
        (cs.rename (Rename.succ (k:=.cvar)))
      specialize hd m' CS hwf_CS hsub hsub_bound
      have hcs_eq : (cs.rename (Rename.succ (k:=.cvar))).subst (σ.lift (k:=.cvar)) =
                    (cs.subst σ).rename (Rename.succ (k:=.cvar)) :=
        CaptureSet.weaken_subst_comm_base.symm
      rw [hcs_eq] at ih2
      exact (ih2 m' _).mpr hd

def retype_exi_val_denot
  {s1 s2 : Sig} {env1 : TypeEnv s1} {σ : Subst s1 s2} {env2 : TypeEnv s2}
  (ρ : Retype env1 σ env2) (T : Ty .exi s1) :
  Ty.exi_val_denot env1 T ≈ Ty.exi_val_denot env2 (T.subst σ) :=
  match T with
  | .typ T => by
    have ih := retype_val_denot ρ T
    intro s e
    simp [Ty.exi_val_denot, Ty.subst]
    exact ih s e
  | .exi T => by
    intro s e
    simp only [Ty.exi_val_denot, Ty.subst]
    -- Both sides are match expressions on resolve s.heap e
    cases hresolve : resolve s.heap e
    · -- resolve = none
      simp
    · -- resolve = some e'
      rename_i e'
      cases e'
      case pack =>
        rename_i CS y
        simp
        -- Goal: CS.WfInHeap s.heap → (... ↔ ...)
        intro _hwf
        have ih := retype_val_denot (ρ.liftCVar (cs:=CS)) T
        exact ih s (Exp.var y)
      all_goals {
        -- resolve returned non-pack
        simp
      }

def retype_exp_denot
  {s1 s2 : Sig} {env1 : TypeEnv s1} {σ : Subst s1 s2} {env2 : TypeEnv s2}
  (ρ : Retype env1 σ env2) (T : Ty .capt s1) (cs : CaptureSet s1) :
  Ty.exp_denot env1 T cs ≈ Ty.exp_denot env2 (T.subst σ) (cs.subst σ) := by
  have ih := retype_val_denot ρ T
  have hcs := retype_captureset_denot ρ cs
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

def retype_exi_exp_denot
  {s1 s2 : Sig} {env1 : TypeEnv s1} {σ : Subst s1 s2} {env2 : TypeEnv s2}
  (ρ : Retype env1 σ env2) (T : Ty .exi s1) (cs : CaptureSet s1) :
  Ty.exi_exp_denot env1 T cs ≈ Ty.exi_exp_denot env2 (T.subst σ) (cs.subst σ) := by
  have ih := retype_exi_val_denot ρ T
  have hcs := retype_captureset_denot ρ cs
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

def Retype.open_arg {env : TypeEnv s} {y : Var .var s} {ps : PeakSet s} :
  Retype
    (env.extend_var (interp_var env y) ps)
    (Subst.openVar y)
    env where
  var := fun x => by cases x <;> rfl
  tvar := fun
    | .there X => by
      -- LHS: (env.extend_var _ ps).lookup_tvar (.there X) = env.lookup_tvar X
      -- RHS: Ty.val_denot env ((Subst.openVar y).tvar (.there X)).core
      --    = Ty.val_denot env (PureTy.tvar X).core
      --    = Ty.val_denot env (.tvar X)
      --    = env.lookup_tvar X
      apply Denot.eq_to_equiv
      simp [TypeEnv.extend_var, TypeEnv.lookup_tvar, Subst.openVar,
            PureTy.tvar, Ty.val_denot]
  cvar := fun
    | .there C => by
      simp [TypeEnv.extend_var, Subst.openVar, TypeEnv.lookup_cvar,
        CaptureSet.subst, Subst.from_TypeEnv]

theorem open_arg_val_denot
    {env : TypeEnv s} {y : Var .var s} {ps : PeakSet s} {T : Ty .capt (s,x)} :
  Ty.val_denot (env.extend_var (interp_var env y) ps) T ≈
    Ty.val_denot env (T.subst (Subst.openVar y)) := by
  apply retype_val_denot Retype.open_arg

theorem open_arg_exi_val_denot
    {env : TypeEnv s} {y : Var .var s} {ps : PeakSet s} {T : Ty .exi (s,x)} :
  Ty.exi_val_denot (env.extend_var (interp_var env y) ps) T ≈
    Ty.exi_val_denot env (T.subst (Subst.openVar y)) := by
  apply retype_exi_val_denot Retype.open_arg

theorem open_arg_exi_exp_denot
    {env : TypeEnv s} {y : Var .var s} {ps : PeakSet s}
    {T : Ty .exi (s,x)} {cs : CaptureSet (s,x)} :
  Ty.exi_exp_denot (env.extend_var (interp_var env y) ps) T cs ≈
    Ty.exi_exp_denot env (T.subst (Subst.openVar y)) (cs.subst (Subst.openVar y)) := by
  apply retype_exi_exp_denot Retype.open_arg

def Retype.open_targ {env : TypeEnv s} {S : PureTy s} :
  Retype
    (env.extend_tvar (Ty.val_denot env S.core))
    (Subst.openTVar S)
    env where
  var := fun x => by cases x; rfl
  tvar := fun
    | .here => by
      -- LHS: (env.extend_tvar _).lookup_tvar .here = Ty.val_denot env S.core
      -- RHS: Ty.val_denot env ((Subst.openTVar S).tvar .here).core
      --    = Ty.val_denot env S.core
      apply Denot.eq_to_equiv
      simp [TypeEnv.extend_tvar, TypeEnv.lookup_tvar, Subst.openTVar]
    | .there X => by
      -- LHS: (env.extend_tvar _).lookup_tvar (.there X) = env.lookup_tvar X
      -- RHS: Ty.val_denot env ((Subst.openTVar S).tvar (.there X)).core
      --    = Ty.val_denot env (PureTy.tvar X).core = env.lookup_tvar X
      apply Denot.eq_to_equiv
      simp [TypeEnv.extend_tvar, TypeEnv.lookup_tvar, Subst.openTVar,
            PureTy.tvar, Ty.val_denot]
  cvar := fun
    | .there C => by
      simp [TypeEnv.extend_tvar, Subst.openTVar, TypeEnv.lookup_cvar,
        CaptureSet.subst, Subst.from_TypeEnv]

theorem open_targ_val_denot {env : TypeEnv s} {S : PureTy s} {T : Ty .capt (s,X)} :
  Ty.val_denot (env.extend_tvar (Ty.val_denot env S.core)) T ≈
    Ty.val_denot env (T.subst (Subst.openTVar S)) := by
  apply retype_val_denot Retype.open_targ

theorem open_targ_exi_val_denot {env : TypeEnv s} {S : PureTy s} {T : Ty .exi (s,X)} :
  Ty.exi_val_denot (env.extend_tvar (Ty.val_denot env S.core)) T ≈
    Ty.exi_val_denot env (T.subst (Subst.openTVar S)) := by
  apply retype_exi_val_denot Retype.open_targ

theorem open_targ_exi_exp_denot
    {env : TypeEnv s} {S : PureTy s} {T : Ty .exi (s,X)} {cs : CaptureSet (s,X)} :
  Ty.exi_exp_denot (env.extend_tvar (Ty.val_denot env S.core)) T cs ≈
    Ty.exi_exp_denot env (T.subst (Subst.openTVar S)) (cs.subst (Subst.openTVar S)) := by
  apply retype_exi_exp_denot Retype.open_targ

def Retype.open_carg {env : TypeEnv s} {C : CaptureSet s} :
  Retype
    (env.extend_cvar (C.subst (Subst.from_TypeEnv env)))
    (Subst.openCVar C)
    env where
  var := fun x => by cases x; rfl
  tvar := fun
    | .there X => by
      -- LHS: (env.extend_cvar _).lookup_tvar (.there X) = env.lookup_tvar X
      -- RHS: Ty.val_denot env ((Subst.openCVar C).tvar (.there X)).core
      --    = Ty.val_denot env (PureTy.tvar X).core = env.lookup_tvar X
      apply Denot.eq_to_equiv
      simp [TypeEnv.lookup_tvar, Subst.openCVar, TypeEnv.extend_cvar,
            PureTy.tvar, Ty.val_denot]
  cvar := fun
    | .here => by
      simp [TypeEnv.lookup_cvar, Subst.openCVar, TypeEnv.extend_cvar]
    | .there C => by
      simp [Subst.openCVar, TypeEnv.lookup_cvar, TypeEnv.extend_cvar,
        CaptureSet.subst, Subst.from_TypeEnv]

theorem open_carg_val_denot {env : TypeEnv s} {C : CaptureSet s} {T : Ty .capt (s,C)} :
  Ty.val_denot (env.extend_cvar (C.subst (Subst.from_TypeEnv env))) T ≈
    Ty.val_denot env (T.subst (Subst.openCVar C)) := by
  apply retype_val_denot Retype.open_carg

theorem open_carg_exi_val_denot {env : TypeEnv s} {C : CaptureSet s} {T : Ty .exi (s,C)} :
  Ty.exi_val_denot (env.extend_cvar (C.subst (Subst.from_TypeEnv env))) T ≈
    Ty.exi_val_denot env (T.subst (Subst.openCVar C)) := by
  apply retype_exi_val_denot Retype.open_carg

theorem open_carg_exi_exp_denot
    {env : TypeEnv s} {C : CaptureSet s} {T : Ty .exi (s,C)} {cs : CaptureSet (s,C)} :
  Ty.exi_exp_denot (env.extend_cvar (C.subst (Subst.from_TypeEnv env))) T cs ≈
    Ty.exi_exp_denot env (T.subst (Subst.openCVar C)) (cs.subst (Subst.openCVar C)) := by
  apply retype_exi_exp_denot Retype.open_carg

end Capybara
