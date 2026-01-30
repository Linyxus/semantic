import Semantic.CaplessK.Denotation.Core
import Semantic.CaplessK.Denotation.Rebind
namespace CaplessK

/-- Interpret a variable in an environment to get its free variable index. -/
def interp_var (env : TypeEnv s) (x : Var .var s) : Nat :=
  match x with
  | .free n => n
  | .bound x => env.lookup_var x

structure Retype (ctx1 : DenotCtx s1) (σ : Subst s1 s2) (ctx2 : DenotCtx s2) where
  var :
    ∀ (x : BVar s1 .var),
      ctx1.env.lookup_var x = interp_var ctx2.env (σ.var x)

  tvar :
    ∀ (X : BVar s1 .tvar),
      ctx1.env.lookup_tvar X ≈ Ty.shape_val_denot ctx2 (σ.tvar X)

  cvar :
    ∀ (C : BVar s1 .cvar) (K : CapKind),
      (ctx1.env.lookup_cvar C).proj K =
        (σ.cvar C K).subst (Subst.from_DenotCtx ctx2)

lemma weaken_interp_var {x : Var .var s} :
  interp_var env x = interp_var (env.extend_var n) (x.rename Rename.succ) := by
  cases x <;> rfl

lemma tweaken_interp_var {x : Var .var s} :
  interp_var env x = interp_var (env.extend_tvar d) (x.rename Rename.succ) := by
  cases x <;> rfl

lemma cweaken_interp_var {cs : CaptureSet {}} {x : Var .var s} :
  interp_var env x = interp_var (env.extend_cvar cs) (x.rename Rename.succ) := by
  cases x <;> rfl

theorem Retype.liftVar
  {x : Nat}
  (ρ : Retype ctx1 σ ctx2) :
  Retype (ctx1.extend_var x) (σ.lift) (ctx2.extend_var x) where
  var := fun
    | .here => rfl
    | .there y => by
      conv =>
        lhs
        simp [DenotCtx.extend_var, TypeEnv.extend_var, TypeEnv.lookup_var, TypeEnv.lookup]
      conv =>
        rhs
        simp [DenotCtx.extend_var, Subst.lift]
        simp [<-weaken_interp_var]
      exact ρ.var y
  tvar := fun
    | .there X => by
      conv =>
        lhs
        simp [DenotCtx.extend_var, TypeEnv.extend_var, TypeEnv.lookup_tvar, TypeEnv.lookup]
      conv =>
        rhs
        simp [Subst.lift]
      apply PreDenot.equiv_trans _ _ _ (ρ.tvar X)
      apply weaken_shape_val_denot
  cvar := fun
    | .there C => fun K => by
      simp only [DenotCtx.extend_var, TypeEnv.lookup_cvar_extend_var, Subst.lift]
      rw [ρ.cvar C K]
      apply rebind_resolved_capture_set Rebind.weaken

theorem Retype.liftTVar
  {d : PreDenot}
  (ρ : Retype ctx1 σ ctx2) :
  Retype (ctx1.extend_tvar d) (σ.lift) (ctx2.extend_tvar d) where
  var := fun
    | .there x => by
      conv => lhs; simp [DenotCtx.extend_tvar, TypeEnv.extend_tvar,
        TypeEnv.lookup_var, TypeEnv.lookup]
      conv => rhs; simp [DenotCtx.extend_tvar, Subst.lift, <-tweaken_interp_var]
      exact ρ.var x
  tvar := fun
    | .here => by
      conv => lhs; simp [DenotCtx.extend_tvar, TypeEnv.extend_tvar,
        TypeEnv.lookup_tvar, TypeEnv.lookup]
      conv =>
        rhs
        simp [Subst.lift, Ty.shape_val_denot, DenotCtx.lookup_tvar]
        simp [DenotCtx.extend_tvar, TypeEnv.extend_tvar,
          TypeEnv.lookup_tvar, TypeEnv.lookup]
      apply PreDenot.equiv_refl
    | .there X => by
      conv =>
        lhs
        simp [DenotCtx.extend_tvar, TypeEnv.extend_tvar,
          TypeEnv.lookup_tvar, TypeEnv.lookup]
      conv =>
        rhs
        simp [Subst.lift]
      apply PreDenot.equiv_trans _ _ _ (ρ.tvar X)
      apply tweaken_shape_val_denot
  cvar := fun
    | .there C => fun K => by
      simp only [DenotCtx.extend_tvar, TypeEnv.lookup_cvar_extend_tvar, Subst.lift]
      rw [ρ.cvar C K]
      apply rebind_resolved_capture_set Rebind.tweaken

theorem Retype.liftCVar
  {cs : CaptureSet {}}
  (ρ : Retype ctx1 σ ctx2) :
  Retype (ctx1.extend_cvar cs) (σ.lift) (ctx2.extend_cvar cs) where
  var := fun
    | .there x => by
      conv => lhs; simp [DenotCtx.extend_cvar, TypeEnv.extend_cvar,
        TypeEnv.lookup_var, TypeEnv.lookup]
      conv => rhs; simp [DenotCtx.extend_cvar, Subst.lift, <-cweaken_interp_var]
      exact ρ.var x
  tvar := fun
    | .there X => by
      conv =>
        lhs
        simp [DenotCtx.extend_cvar, TypeEnv.extend_cvar,
          TypeEnv.lookup_tvar, TypeEnv.lookup]
      conv =>
        rhs
        simp [Subst.lift]
      apply PreDenot.equiv_trans _ _ _ (ρ.tvar X)
      apply cweaken_shape_val_denot
  cvar := fun
    | .here => fun K => by
      simp only [DenotCtx.extend_cvar, TypeEnv.lookup_cvar_extend_cvar_here,
        Subst.lift, CaptureSet.subst,
        Subst.from_DenotCtx, Subst.from_TypeEnv, TypeEnv.lookup_cvar_extend_cvar_here]
    | .there C => fun K => by
      simp only [DenotCtx.extend_cvar, TypeEnv.lookup_cvar_extend_cvar_there,
        Subst.lift, Subst.from_DenotCtx]
      rw [ρ.cvar C K]
      apply rebind_resolved_capture_set Rebind.cweaken

mutual

def retype_shape_val_denot
  {s1 s2 : Sig} {ctx1 : DenotCtx s1} {σ : Subst s1 s2} {ctx2 : DenotCtx s2}
  (ρ : Retype ctx1 σ ctx2) (hh : ctx1.handlers = ctx2.handlers) (T : Ty .shape s1) :
  Ty.shape_val_denot ctx1 T ≈ Ty.shape_val_denot ctx2 (T.subst σ) :=
  match T with
  | .top => by
    apply PreDenot.eq_to_equiv
    simp [Ty.shape_val_denot, Ty.subst]
  | .tvar X => by
    simp only [Ty.shape_val_denot, Ty.subst, DenotCtx.lookup_tvar]
    exact ρ.tvar X
  | .unit => by
    apply PreDenot.eq_to_equiv
    simp [Ty.shape_val_denot, Ty.subst]
  | .cap => by
    apply PreDenot.eq_to_equiv
    simp [Ty.shape_val_denot, Ty.subst]
  | .bool => by
    apply PreDenot.eq_to_equiv
    simp [Ty.shape_val_denot, Ty.subst]
  | .cell => by
    apply PreDenot.eq_to_equiv
    simp [Ty.shape_val_denot, Ty.subst]
  | .arrow T1 T2 => by
    have ih1 := retype_capt_val_denot ρ hh T1
    intro A s0 e0
    simp [Ty.shape_val_denot, Ty.subst]
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
              have ih2 := retype_exi_exp_denot (ρ.liftVar (x:=arg)) hh T2
              have harg' := (ih1 H' (.var (.free arg))).mpr harg
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
              have ih2 := retype_exi_exp_denot (ρ.liftVar (x:=arg)) hh T2
              have harg' := (ih1 H' (.var (.free arg))).mp harg
              specialize hd arg H' hsub harg'
              -- The capability set uses expand_captures
              exact (ih2 (expand_captures s0.heap cs0 ∪
                         (reachability_of_loc H'.heap arg)) H' _).mpr hd
  | .poly T1 T2 => by
    have ih1 := retype_shape_val_denot ρ hh T1
    intro A s0 e0
    simp [Ty.shape_val_denot, Ty.subst]
    intro hwf_e
    constructor
    · intro h
      obtain ⟨cs, S0, t0, hr, hwf, hR0_sub, hd⟩ := h
      use cs, S0, t0
      constructor
      · exact hr
      · constructor
        · exact hwf
        · constructor
          · exact hR0_sub
          · intro H' denot hsub hproper himply
            have ih2 := retype_exi_exp_denot (ρ.liftTVar (d:=denot)) hh T2
            have himply' : denot.ImplyAfter H' (Ty.shape_val_denot ctx1 T1) := by
              intro H'' hsub' A' e hdenot
              exact (ih1 _ _ _).mpr (himply H'' hsub' A' e hdenot)
            specialize hd H' denot hsub hproper himply'
            exact (ih2 (expand_captures s0.heap cs) H' _).mp hd
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
            have ih2 := retype_exi_exp_denot (ρ.liftTVar (d:=denot)) hh T2
            have himply' : denot.ImplyAfter H' (Ty.shape_val_denot ctx2 (T1.subst σ)) := by
              intro H'' hsub' A' e hdenot
              exact (ih1 _ _ _).mp (himply H'' hsub' A' e hdenot)
            specialize hd H' denot hsub hproper himply'
            exact (ih2 (expand_captures s0.heap cs0) H' _).mpr hd
  | .cpoly B T => by
    have hB := retype_capturebound_denot ρ B
    intro A s0 e0
    simp [Ty.shape_val_denot, Ty.subst, hB]
    intro hwf_e
    constructor
    · intro h
      obtain ⟨cs, B0, t0, hr, hwf, hR0_sub, hd⟩ := h
      use cs, B0, t0
      constructor
      · exact hr
      · constructor
        · exact hwf
        · constructor
          · exact hR0_sub
          · intro H' CS hwf hsub hsub_bound
            have ih2 := retype_exi_exp_denot (ρ.liftCVar (cs:=CS)) hh T
            specialize hd H' CS hwf hsub hsub_bound
            exact (ih2 (expand_captures s0.heap cs) H' _).mp hd
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
            have ih2 := retype_exi_exp_denot (ρ.liftCVar (cs:=CS)) hh T
            specialize hd H' CS hwf hsub hsub_bound
            exact (ih2 (expand_captures s0.heap cs0) H' _).mpr hd
  | .label T => by
    apply PreDenot.eq_to_equiv
    simp [Ty.shape_val_denot, Ty.subst]

def retype_capturebound_denot
  {s1 s2 : Sig} {ctx1 : DenotCtx s1} {σ : Subst s1 s2} {ctx2 : DenotCtx s2}
  (ρ : Retype ctx1 σ ctx2) (B : CaptureBound s1) :
  CaptureBound.denot ctx1 B = CaptureBound.denot ctx2 (B.subst σ) := by
  cases B
  case unbound => rfl
  case bound C =>
    simp [CaptureBound.denot, CaptureBound.subst]
    funext m
    congr 1
    exact congrFun (retype_captureset_denot ρ C) m

def retype_resolved_capture_set
  {s1 s2 : Sig} {ctx1 : DenotCtx s1} {σ : Subst s1 s2} {ctx2 : DenotCtx s2}
  (ρ : Retype ctx1 σ ctx2) (C : CaptureSet s1) :
  C.subst (Subst.from_TypeEnv ctx1.env) = (C.subst σ).subst (Subst.from_TypeEnv ctx2.env) := by
  induction C
  case empty => rfl
  case union C1 C2 ih1 ih2 =>
    simp [CaptureSet.subst, ih1, ih2]
  case var x ck =>
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
  case cvar C ck =>
    simp [CaptureSet.subst]
    exact ρ.cvar C ck

def retype_captureset_denot
  {s1 s2 : Sig} {ctx1 : DenotCtx s1} {σ : Subst s1 s2} {ctx2 : DenotCtx s2}
  (ρ : Retype ctx1 σ ctx2) (C : CaptureSet s1) :
  CaptureSet.denot ctx1 C = CaptureSet.denot ctx2 (C.subst σ) := by
  unfold CaptureSet.denot
  congr 1
  exact retype_resolved_capture_set ρ C

def retype_capt_val_denot
  {s1 s2 : Sig} {ctx1 : DenotCtx s1} {σ : Subst s1 s2} {ctx2 : DenotCtx s2}
  (ρ : Retype ctx1 σ ctx2) (hh : ctx1.handlers = ctx2.handlers) (T : Ty .capt s1) :
  Ty.capt_val_denot ctx1 T ≈ Ty.capt_val_denot ctx2 (T.subst σ) :=
  match T with
  | .capt C S => by
    have hC := retype_captureset_denot ρ C
    have hS := retype_shape_val_denot ρ hh S
    intro s e
    simp [Ty.capt_val_denot, Ty.subst]
    rw [← hC]
    intro hwf_e hwf
    constructor
    · intro ⟨hwf_C, hshape⟩
      constructor
      · -- Use retype_resolved_capture_set to show equality of resolved capture sets
        simp only [Subst.from_DenotCtx]
        rw [←retype_resolved_capture_set ρ C]
        exact hwf_C
      · exact (hS (C.denot ctx1 s) s e).mp hshape
    · intro ⟨hwf_C, hshape⟩
      constructor
      · -- Use retype_resolved_capture_set to show equality of resolved capture sets
        simp only [Subst.from_DenotCtx]
        rw [retype_resolved_capture_set ρ C]
        exact hwf_C
      · exact (hS (C.denot ctx1 s) s e).mpr hshape

def retype_exi_val_denot
  {s1 s2 : Sig} {ctx1 : DenotCtx s1} {σ : Subst s1 s2} {ctx2 : DenotCtx s2}
  (ρ : Retype ctx1 σ ctx2) (hh : ctx1.handlers = ctx2.handlers) (T : Ty .exi s1) :
  Ty.exi_val_denot ctx1 T ≈ Ty.exi_val_denot ctx2 (T.subst σ) :=
  match T with
  | .typ T => by
    have ih := retype_capt_val_denot ρ hh T
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
        have ih := retype_capt_val_denot (ρ.liftCVar (cs:=CS)) hh T
        exact ih s (Exp.var y)
      all_goals {
        -- resolve returned non-pack
        simp
      }

def retype_exi_exp_denot
  {s1 s2 : Sig} {ctx1 : DenotCtx s1} {σ : Subst s1 s2} {ctx2 : DenotCtx s2}
  (ρ : Retype ctx1 σ ctx2) (hh : ctx1.handlers = ctx2.handlers) (T : Ty .exi s1) :
  Ty.exi_exp_denot ctx1 T ≈ Ty.exi_exp_denot ctx2 (T.subst σ) := by
  have ih := retype_exi_val_denot ρ hh T
  intro A s e
  simp [Ty.exi_exp_denot]
  constructor
  · intro h hws
    rw [← hh] at hws
    apply eval_post_monotonic _ (h hws)
    apply Denot.imply_to_entails
    rw [hh]
    exact ((Denot.equiv_to_imply ih).1).or_right _
  · intro h hws
    rw [hh] at hws
    apply eval_post_monotonic _ (h hws)
    apply Denot.imply_to_entails
    rw [← hh]
    exact ((Denot.equiv_to_imply ih).2).or_right _

end

def Retype.open_arg {ctx : DenotCtx s} {y : Var .var s} :
  Retype
    (ctx.extend_var (interp_var ctx.env y))
    (Subst.openVar y)
    ctx where
  var := fun x => by
    simp only [DenotCtx.extend_var]
    cases x <;> rfl
  tvar := fun
    | .there X => by
      conv =>
        lhs
        simp [DenotCtx.extend_var, TypeEnv.extend_var, TypeEnv.lookup_tvar, TypeEnv.lookup]
      conv =>
        rhs
        simp [Subst.openVar]
      apply PreDenot.eq_to_equiv
      simp [Ty.shape_val_denot, DenotCtx.lookup_tvar, TypeEnv.lookup_tvar]
  cvar := fun
    | .there C => fun K => by
      simp only [DenotCtx.extend_var, TypeEnv.extend_var, Subst.openVar, CaptureSet.subst,
        Subst.from_DenotCtx, Subst.from_TypeEnv, TypeEnv.lookup_cvar, TypeEnv.lookup]

theorem open_arg_shape_val_denot {ctx : DenotCtx s} {y : Var .var s} {T : Ty .shape (s,x)} :
  Ty.shape_val_denot (ctx.extend_var (interp_var ctx.env y)) T ≈
    Ty.shape_val_denot ctx (T.subst (Subst.openVar y)) := by
  exact retype_shape_val_denot Retype.open_arg rfl T

theorem open_arg_capt_val_denot {ctx : DenotCtx s} {y : Var .var s} {T : Ty .capt (s,x)} :
  Ty.capt_val_denot (ctx.extend_var (interp_var ctx.env y)) T ≈
    Ty.capt_val_denot ctx (T.subst (Subst.openVar y)) := by
  exact retype_capt_val_denot Retype.open_arg rfl T

theorem open_arg_exi_val_denot {ctx : DenotCtx s} {y : Var .var s} {T : Ty .exi (s,x)} :
  Ty.exi_val_denot (ctx.extend_var (interp_var ctx.env y)) T ≈
    Ty.exi_val_denot ctx (T.subst (Subst.openVar y)) := by
  exact retype_exi_val_denot Retype.open_arg rfl T

theorem open_arg_exi_exp_denot {ctx : DenotCtx s} {y : Var .var s} {T : Ty .exi (s,x)} :
  Ty.exi_exp_denot (ctx.extend_var (interp_var ctx.env y)) T ≈
    Ty.exi_exp_denot ctx (T.subst (Subst.openVar y)) := by
  exact retype_exi_exp_denot Retype.open_arg rfl T

def Retype.open_targ {ctx : DenotCtx s} {S : Ty .shape s} :
  Retype
    (ctx.extend_tvar (Ty.shape_val_denot ctx S))
    (Subst.openTVar S)
    ctx where
  var := fun x => by
    simp only [DenotCtx.extend_tvar]
    cases x; rfl
  tvar := fun
    | .here => by
      simp only [DenotCtx.extend_tvar]
      apply PreDenot.eq_to_equiv
      rfl
    | .there X => by
      apply PreDenot.eq_to_equiv
      simp [DenotCtx.extend_tvar, TypeEnv.extend_tvar,
        TypeEnv.lookup_tvar, TypeEnv.lookup]
      simp [Subst.openTVar, Ty.shape_val_denot, DenotCtx.lookup_tvar]
      rfl
  cvar := fun
    | .there C => fun K => by
      simp only [DenotCtx.extend_tvar, TypeEnv.extend_tvar, Subst.openTVar, CaptureSet.subst,
        Subst.from_DenotCtx, Subst.from_TypeEnv, TypeEnv.lookup_cvar, TypeEnv.lookup]

theorem open_targ_shape_val_denot {ctx : DenotCtx s} {S : Ty .shape s} {T : Ty .shape (s,X)} :
  Ty.shape_val_denot (ctx.extend_tvar (Ty.shape_val_denot ctx S)) T ≈
    Ty.shape_val_denot ctx (T.subst (Subst.openTVar S)) := by
  exact retype_shape_val_denot Retype.open_targ rfl T

theorem open_targ_capt_val_denot {ctx : DenotCtx s} {S : Ty .shape s} {T : Ty .capt (s,X)} :
  Ty.capt_val_denot (ctx.extend_tvar (Ty.shape_val_denot ctx S)) T ≈
    Ty.capt_val_denot ctx (T.subst (Subst.openTVar S)) := by
  exact retype_capt_val_denot Retype.open_targ rfl T

theorem open_targ_exi_val_denot {ctx : DenotCtx s} {S : Ty .shape s} {T : Ty .exi (s,X)} :
  Ty.exi_val_denot (ctx.extend_tvar (Ty.shape_val_denot ctx S)) T ≈
    Ty.exi_val_denot ctx (T.subst (Subst.openTVar S)) := by
  exact retype_exi_val_denot Retype.open_targ rfl T

theorem open_targ_exi_exp_denot {ctx : DenotCtx s} {S : Ty .shape s} {T : Ty .exi (s,X)} :
  Ty.exi_exp_denot (ctx.extend_tvar (Ty.shape_val_denot ctx S)) T ≈
    Ty.exi_exp_denot ctx (T.subst (Subst.openTVar S)) := by
  exact retype_exi_exp_denot Retype.open_targ rfl T

def Retype.open_carg {ctx : DenotCtx s} {C : CaptureSet s} :
  Retype
    (ctx.extend_cvar (C.subst (Subst.from_DenotCtx ctx)))
    (Subst.openCVar C)
    ctx where
  var := fun x => by
    simp only [DenotCtx.extend_cvar]
    cases x; rfl
  tvar := fun
    | .there X => by
      apply PreDenot.eq_to_equiv
      simp [DenotCtx.extend_cvar, TypeEnv.lookup_tvar, Subst.openCVar,
        TypeEnv.extend_cvar, TypeEnv.lookup, Ty.shape_val_denot, DenotCtx.lookup_tvar]
  cvar := fun
    | .here => fun K => by
      simp only [DenotCtx.extend_cvar, TypeEnv.lookup_cvar_extend_cvar_here,
        Subst.openCVar, Subst.from_DenotCtx, Subst.from_TypeEnv]
      exact CaptureSet.proj_subst_from_TypeEnv
    | .there c => fun K => by
      simp only [DenotCtx.extend_cvar, TypeEnv.lookup_cvar_extend_cvar_there,
        Subst.openCVar, CaptureSet.subst,
        Subst.from_DenotCtx, Subst.from_TypeEnv, TypeEnv.lookup_cvar_extend_cvar_there]

theorem open_carg_shape_val_denot {ctx : DenotCtx s} {C : CaptureSet s} {T : Ty .shape (s,C)} :
  Ty.shape_val_denot (ctx.extend_cvar (C.subst (Subst.from_DenotCtx ctx))) T ≈
    Ty.shape_val_denot ctx (T.subst (Subst.openCVar C)) := by
  exact retype_shape_val_denot Retype.open_carg rfl T

theorem open_carg_exi_val_denot {ctx : DenotCtx s} {C : CaptureSet s} {T : Ty .exi (s,C)} :
  Ty.exi_val_denot (ctx.extend_cvar (C.subst (Subst.from_DenotCtx ctx))) T ≈
    Ty.exi_val_denot ctx (T.subst (Subst.openCVar C)) := by
  exact retype_exi_val_denot Retype.open_carg rfl T

theorem open_carg_exi_exp_denot {ctx : DenotCtx s} {C : CaptureSet s} {T : Ty .exi (s,C)} :
  Ty.exi_exp_denot (ctx.extend_cvar (C.subst (Subst.from_DenotCtx ctx))) T ≈
    Ty.exi_exp_denot ctx (T.subst (Subst.openCVar C)) := by
  exact retype_exi_exp_denot Retype.open_carg rfl T

end CaplessK
