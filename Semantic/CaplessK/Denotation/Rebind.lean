import Semantic.CaplessK.Denotation.Core
namespace CaplessK

structure Rebind (env1 : TypeEnv s1) (f : Rename s1 s2) (env2 : TypeEnv s2) : Prop where
  var :
    ∀ (x : BVar s1 k),
      env1.lookup x = env2.lookup (f.var x)

def Rebind.liftVar
  (ρ : Rebind env1 f env2) :
  Rebind (env1.extend_var x) (f.lift) (env2.extend_var x) where
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
  (ρ : Rebind env1 f env2) (cs : CaptureSet {}) :
  Rebind (env1.extend_cvar cs) (f.lift) (env2.extend_cvar cs) where
  var := fun
    | .here => rfl
    | .there y => by
      simp [TypeEnv.extend_cvar, Rename.lift, TypeEnv.lookup]
      exact ρ.var y

theorem rebind_resolved_capture_set {C : CaptureSet s1}
  (ρ : Rebind env1 f env2) :
  C.subst (Subst.from_TypeEnv env1) =
    (C.rename f).subst (Subst.from_TypeEnv env2) := by
  induction C with
  | empty =>
    simp [CaptureSet.subst, CaptureSet.rename]
  | union C1 C2 ih1 ih2 =>
    simp [CaptureSet.subst, CaptureSet.rename, ih1, ih2]
  | var x =>
    cases x with
    | free n =>
      simp [CaptureSet.subst, CaptureSet.rename, Var.subst, Var.rename]
    | bound x =>
      have h := ρ.var x
      cases k : env1.lookup x with
      | var n =>
        rw [k] at h
        simp [CaptureSet.subst, CaptureSet.rename, Var.subst, Var.rename,
              Subst.from_TypeEnv, TypeEnv.lookup_var, k]
        rw [<-h]
  | cvar x =>
    have h := ρ.var x
    cases k1 : env1.lookup x with
    | cvar cs1 =>
      rw [k1] at h
      cases k2 : env2.lookup (f.var x) with
      | cvar cs2 =>
        rw [k2] at h
        cases h
        simp [CaptureSet.subst, CaptureSet.rename, Subst.from_TypeEnv,
              TypeEnv.lookup_cvar, k1, k2]

/- Rebinding for CaptureSet.denot -/
theorem rebind_captureset_denot
  {s1 s2 : Sig} {ctx1 : DenotCtx s1} {f : Rename s1 s2} {ctx2 : DenotCtx s2}
  (ρ : Rebind ctx1.env f ctx2.env) (C : CaptureSet s1) :
  CaptureSet.denot ctx1 C = CaptureSet.denot ctx2 (C.rename f) := by
  -- Use rebind_resolved_capture_set
  unfold CaptureSet.denot
  congr 1
  exact rebind_resolved_capture_set ρ

theorem rebind_capturebound_denot
  {s1 s2 : Sig} {ctx1 : DenotCtx s1} {f : Rename s1 s2} {ctx2 : DenotCtx s2}
  (ρ : Rebind ctx1.env f ctx2.env) (B : CaptureBound s1) :
  CaptureBound.denot ctx1 B = CaptureBound.denot ctx2 (B.rename f) := by
  cases B
  case unbound => rfl
  case bound C =>
    simp [CaptureBound.denot, CaptureBound.rename]
    funext m
    congr 1
    exact congrFun (rebind_captureset_denot ρ C) m

mutual

def rebind_shape_val_denot
  {s1 s2 : Sig} {ctx1 : DenotCtx s1} {f : Rename s1 s2} {ctx2 : DenotCtx s2}
  (ρ : Rebind ctx1.env f ctx2.env) (T : Ty .shape s1) :
  Ty.shape_val_denot ctx1 T ≈ Ty.shape_val_denot ctx2 (T.rename f) :=
  match T with
  | .top => by
    apply PreDenot.eq_to_equiv
    funext A
    simp [Ty.shape_val_denot, Ty.rename]
  | .tvar X => by
    apply PreDenot.eq_to_equiv
    have h := ρ.var X
    cases k : ctx1.env.lookup X
    case tvar d =>
      simp [k] at h
      simp [Ty.shape_val_denot, Ty.rename, DenotCtx.lookup_tvar,
            TypeEnv.lookup_tvar, k, h]
  | .unit => by
    apply PreDenot.eq_to_equiv
    funext A
    simp [Ty.shape_val_denot, Ty.rename]
  | .cap => by
    intro A s0 e0
    simp [Ty.shape_val_denot, Ty.rename]
  | .bool => by
    apply PreDenot.eq_to_equiv
    funext A
    simp [Ty.shape_val_denot, Ty.rename]
  | .cell => by
    intro A s0 e0
    simp [Ty.shape_val_denot, Ty.rename]
  | .arrow T1 T2 => by
    have ih1 := rebind_capt_val_denot ρ T1
    intro A s0 e0
    simp [Ty.shape_val_denot, Ty.rename]
    intro hwf_e
    constructor
    · intro h
      obtain ⟨cs, T0, t0, hr, hwf, hR0_sub, hd⟩ := h
      use cs, T0, t0
      constructor
      · exact hr
      · constructor
        · exact hwf
        · constructor
          · exact hR0_sub
          · intro arg H' hsub harg
            cases T1
            case capt C S =>
              have ih2 := rebind_exi_exp_denot (ρ.liftVar (x:=arg)) T2
              have harg' := (ih1 _ _).mpr harg
              specialize hd arg H' hsub harg'
              -- The capability set uses expand_captures
              exact (ih2 (expand_captures s0.heap cs ∪
                         (reachability_of_loc H'.heap arg)) H' _).mp hd
    · intro h
      obtain ⟨cs0, T0, t0, hr, hwf, hR0_sub, hd⟩ := h
      use cs0, T0, t0
      constructor
      · exact hr
      · constructor
        · exact hwf
        · constructor
          · exact hR0_sub
          · intro arg H' hsub harg
            cases T1
            case capt C S =>
              have ih2 := rebind_exi_exp_denot (ρ.liftVar (x:=arg)) T2
              have harg' := (ih1 _ _).mp harg
              specialize hd arg H' hsub harg'
              -- The capability set uses expand_captures
              exact (ih2 (expand_captures s0.heap cs0 ∪
                         (reachability_of_loc H'.heap arg)) H' _).mpr hd
  | .poly T1 T2 => by
    have ih1 := rebind_shape_val_denot ρ T1
    intro A s0 e0
    simp [Ty.shape_val_denot, Ty.rename]
    intro hwf_e
    constructor
    · intro h
      obtain ⟨cs0, S0, t0, hr, hwf, hR0_sub, hd⟩ := h
      use cs0, S0, t0
      constructor
      · exact hr
      · constructor
        · exact hwf
        · constructor
          · exact hR0_sub
          · intro H' denot hsub hproper himply
            have ih2 := rebind_exi_exp_denot (ρ.liftTVar (d:=denot)) T2
            have himply' : denot.ImplyAfter H' (Ty.shape_val_denot ctx1 T1) := by
              intro H'' hsub' A' e hdenot
              exact (ih1 _ _ _).mpr (himply H'' hsub' A' e hdenot)
            specialize hd H' denot hsub hproper himply'
            exact (ih2 (expand_captures s0.heap cs0) H' _).mp hd
    · intro h
      obtain ⟨cs0, S0, t0, hr, hwf, hR0_sub, hd⟩ := h
      use cs0, S0, t0
      constructor
      · exact hr
      · constructor
        · exact hwf
        · constructor
          · exact hR0_sub
          · intro H' denot hsub hproper himply
            have ih2 := rebind_exi_exp_denot (ρ.liftTVar (d:=denot)) T2
            have himply' : denot.ImplyAfter H' (Ty.shape_val_denot ctx2 (T1.rename f)) := by
              intro H'' hsub' A' e hdenot
              exact (ih1 _ _ _).mp (himply H'' hsub' A' e hdenot)
            specialize hd H' denot hsub hproper himply'
            exact (ih2 (expand_captures s0.heap cs0) H' _).mpr hd
  | .cpoly B T => by
    have hB := rebind_capturebound_denot ρ B
    intro A s0 e0
    simp [Ty.shape_val_denot, Ty.rename, hB]
    intro hwf_e
    constructor
    · intro h
      obtain ⟨cs0, B0, t0, hr, hwf, hR0_sub, hd⟩ := h
      use cs0, B0, t0
      constructor
      · exact hr
      · constructor
        · exact hwf
        · constructor
          · exact hR0_sub
          · intro H' CS hwf hsub hsub_bound
            have ih2 := rebind_exi_exp_denot (ρ.liftCVar CS) T
            specialize hd H' CS hwf hsub hsub_bound
            exact (ih2 (expand_captures s0.heap cs0) H' _).mp hd
    · intro h
      obtain ⟨cs0, B0, t0, hr, hwf, hR0_sub, hd⟩ := h
      use cs0, B0, t0
      constructor
      · exact hr
      · constructor
        · exact hwf
        · constructor
          · exact hR0_sub
          · intro H' CS hwf hsub hsub_bound
            have ih2 := rebind_exi_exp_denot (ρ.liftCVar CS) T
            specialize hd H' CS hwf hsub hsub_bound
            exact (ih2 (expand_captures s0.heap cs0) H' _).mpr hd
  | .label T => by
    apply PreDenot.eq_to_equiv
    funext A
    simp [Ty.shape_val_denot, Ty.rename]

def rebind_capt_val_denot
  {s1 s2 : Sig} {ctx1 : DenotCtx s1} {f : Rename s1 s2} {ctx2 : DenotCtx s2}
  (ρ : Rebind ctx1.env f ctx2.env) (T : Ty .capt s1) :
  Ty.capt_val_denot ctx1 T ≈ Ty.capt_val_denot ctx2 (T.rename f) :=
  match T with
  | .capt C S => by
    have hC := rebind_captureset_denot ρ C
    have hS := rebind_shape_val_denot ρ S
    intro s e
    simp [Ty.capt_val_denot, Ty.rename]
    rw [← hC]
    intro hwf_e hwf
    constructor
    · intro ⟨hwf_C, hshape⟩
      constructor
      · -- Need: ((C.rename f).subst (Subst.from_DenotCtx ctx2)).WfInHeap s.heap
        -- Have: (C.subst (Subst.from_DenotCtx ctx1)).WfInHeap s.heap
        -- These are equal by rebind_resolved_capture_set
        simp only [Subst.from_DenotCtx]
        rw [<-rebind_resolved_capture_set ρ]
        exact hwf_C
      · exact (hS (C.denot ctx1 s) s e).mp hshape
    · intro ⟨hwf_C, hshape⟩
      constructor
      · -- Symmetric case
        simp only [Subst.from_DenotCtx]
        rw [rebind_resolved_capture_set ρ]
        exact hwf_C
      · exact (hS (C.denot ctx1 s) s e).mpr hshape

def rebind_exi_val_denot
  {s1 s2 : Sig} {ctx1 : DenotCtx s1} {f : Rename s1 s2} {ctx2 : DenotCtx s2}
  (ρ : Rebind ctx1.env f ctx2.env) (T : Ty .exi s1) :
  Ty.exi_val_denot ctx1 T ≈ Ty.exi_val_denot ctx2 (T.rename f) :=
  match T with
  | .typ T => by
    have ih := rebind_capt_val_denot ρ T
    intro s e
    simp [Ty.exi_val_denot, Ty.rename]
    exact ih s e
  | .exi T => by
    intro s e
    simp only [Ty.exi_val_denot, Ty.rename]
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
        have ih := rebind_capt_val_denot (ρ.liftCVar CS) T
        exact ih s (Exp.var y)
      all_goals {
        -- resolve returned non-pack
        simp
      }

def rebind_exi_exp_denot
  {s1 s2 : Sig} {ctx1 : DenotCtx s1} {f : Rename s1 s2} {ctx2 : DenotCtx s2}
  (ρ : Rebind ctx1.env f ctx2.env) (T : Ty .exi s1) :
  Ty.exi_exp_denot ctx1 T ≈ Ty.exi_exp_denot ctx2 (T.rename f) := by
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

def Rebind.weaken {env : TypeEnv s} {x : Nat} :
  Rebind env Rename.succ (env.extend_var x) where
  var := fun _ => rfl

def Rebind.tweaken {env : TypeEnv s} {d : PreDenot} :
  Rebind env Rename.succ (env.extend_tvar d) where
  var := fun _ => rfl

def Rebind.cweaken {env : TypeEnv s} {cs : CaptureSet {}} :
  Rebind env Rename.succ (env.extend_cvar cs) where
  var := fun _ => rfl

lemma weaken_shape_val_denot {ctx : DenotCtx s} {T : Ty .shape s} :
  Ty.shape_val_denot ctx T ≈
    Ty.shape_val_denot (ctx.extend_var x) (T.rename Rename.succ) := by
  apply rebind_shape_val_denot (ρ:=Rebind.weaken) (T:=T)

lemma weaken_capt_val_denot {ctx : DenotCtx s} {T : Ty .capt s} :
  Ty.capt_val_denot ctx T ≈
    Ty.capt_val_denot (ctx.extend_var x) (T.rename Rename.succ) := by
  apply rebind_capt_val_denot (ρ:=Rebind.weaken) (T:=T)

lemma weaken_exi_val_denot {ctx : DenotCtx s} {T : Ty .exi s} :
  Ty.exi_val_denot ctx T ≈
    Ty.exi_val_denot (ctx.extend_var x) (T.rename Rename.succ) := by
  apply rebind_exi_val_denot (ρ:=Rebind.weaken) (T:=T)

lemma tweaken_shape_val_denot {ctx : DenotCtx s} {T : Ty .shape s} :
  Ty.shape_val_denot ctx T ≈
    Ty.shape_val_denot (ctx.extend_tvar d) (T.rename Rename.succ) := by
  apply rebind_shape_val_denot (ρ:=Rebind.tweaken) (T:=T)

lemma tweaken_capt_val_denot {ctx : DenotCtx s} {T : Ty .capt s} :
  Ty.capt_val_denot ctx T ≈
    Ty.capt_val_denot (ctx.extend_tvar d) (T.rename Rename.succ) := by
  apply rebind_capt_val_denot (ρ:=Rebind.tweaken) (T:=T)

lemma tweaken_exi_val_denot {ctx : DenotCtx s} {T : Ty .exi s} :
  Ty.exi_val_denot ctx T ≈
    Ty.exi_val_denot (ctx.extend_tvar d) (T.rename Rename.succ) := by
  apply rebind_exi_val_denot (ρ:=Rebind.tweaken) (T:=T)

lemma cweaken_shape_val_denot {ctx : DenotCtx s} {cs : CaptureSet {}}
  {T : Ty .shape s} :
  Ty.shape_val_denot ctx T ≈
    Ty.shape_val_denot (ctx.extend_cvar cs) (T.rename Rename.succ) := by
  apply rebind_shape_val_denot (ρ:=Rebind.cweaken) (T:=T)

lemma cweaken_capt_val_denot {ctx : DenotCtx s} {cs : CaptureSet {}}
  {T : Ty .capt s} :
  Ty.capt_val_denot ctx T ≈
    Ty.capt_val_denot (ctx.extend_cvar cs) (T.rename Rename.succ) := by
  apply rebind_capt_val_denot (ρ:=Rebind.cweaken) (T:=T)

lemma cweaken_exi_val_denot {ctx : DenotCtx s} {cs : CaptureSet {}}
  {T : Ty .exi s} :
  Ty.exi_val_denot ctx T ≈
    Ty.exi_val_denot (ctx.extend_cvar cs) (T.rename Rename.succ) := by
  apply rebind_exi_val_denot (ρ:=Rebind.cweaken) (T:=T)

end CaplessK
