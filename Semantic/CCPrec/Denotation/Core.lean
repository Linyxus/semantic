import Semantic.CCPrec.Semantics
import Semantic.CCPrec.TypeSystem
import Semantic.Prelude

namespace CCPrec

/-- Denotation of types. -/
def Denot := Memory -> Exp {} -> Prop

/-- Pre-denotation. It takes a capability to form a denotation. -/
def PreDenot := CapabilitySet -> Denot

/-- Capture-denotation. Given any memory, it produces a set of capabilities. -/
def CapDenot := Memory -> CapabilitySet

/-- A bound on capability sets. It can either be a concrete set of the top element. -/
inductive CapabilityBound : Type where
| top : CapabilityBound
| set : CapabilitySet -> CapabilityBound

/-- Capture bound denotation. -/
def CapBoundDenot := Memory -> CapabilityBound

def Denot.as_mpost (d : Denot) : Mpost :=
  fun e m => d m e

def Denot.is_monotonic (d : Denot) : Prop :=
  ∀ {m1 m2 : Memory} {e},
    m2.subsumes m1 ->
    d m1 e ->
    d m2 e

def CapDenot.is_monotonic_for (cd : CapDenot) (cs : CaptureSet {}) : Prop :=
  ∀ {m1 m2 : Memory},
    cs.WfInHeap m1.heap ->
    m2.subsumes m1 ->
    cd m1 = cd m2

def Denot.is_transparent (d : Denot) : Prop :=
  ∀ {m : Memory} {x : Nat} {v},
    m.lookup x = some (.val v) ->
    d m v.unwrap ->
    d m (.var (.free x))

def Denot.is_bool_independent (d : Denot) : Prop :=
  ∀ {m : Memory},
    d m .btrue <-> d m .bfalse

def Denot.is_proper (d : Denot) : Prop :=
  d.is_monotonic ∧ d.is_transparent ∧ d.is_bool_independent

/-- For simple values, compute_reachability equals resolve_reachability. -/
theorem compute_reachability_eq_resolve_reachability
  (h : Heap) (v : Exp {}) (hv : v.IsSimpleVal) :
  compute_reachability h v hv = resolve_reachability h v := by
  cases hv <;> rfl

/-- Heap invariant: the reachability stored in a heap value equals the computed
    reachability for that value. -/
theorem Memory.reachability_invariant :
  ∀ (m : Memory) (x : Nat) (v : HeapVal),
    m.heap x = some (Cell.val v) ->
    v.reachability = compute_reachability m.heap v.unwrap v.isVal := fun m x v hx =>
  m.wf.wf_reach x v.unwrap v.isVal v.reachability hx

/-- Reachability of a heap location equals resolve_reachability of the stored value. -/
theorem reachability_of_loc_eq_resolve_reachability
  (m : Memory) (x : Nat) (v : HeapVal)
  (hx : m.heap x = some (Cell.val v)) :
  reachability_of_loc m.heap x = resolve_reachability m.heap v.unwrap := by
  -- reachability_of_loc m.heap x = v.reachability by definition
  unfold reachability_of_loc
  simp only [hx]
  -- v.reachability = compute_reachability m.heap v.unwrap v.isVal
  rw [Memory.reachability_invariant m x v hx]
  -- compute_reachability = resolve_reachability for simple values
  exact compute_reachability_eq_resolve_reachability m.heap v.unwrap v.isVal

/-- This pre-denotation actually enforces the reachability bound. -/
def PreDenot.is_reachability_safe (denot : PreDenot) : Prop :=
  ∀ R m e,
    denot R m e ->
    resolve_reachability m.heap e ⊆ R

/-- This pre-denotation is monotonic over reachability sets. -/
def PreDenot.is_reachability_monotonic (pd : PreDenot) : Prop :=
  ∀ R1 R2,
    R1 ⊆ R2 ->
    ∀ m e,
      pd R1 m e ->
      pd R2 m e

/-- This pre-denotation entails heap well-formedness. -/
def PreDenot.implies_wf (pd : PreDenot) : Prop :=
  ∀ R m e,
    pd R m e ->
    e.WfInHeap m.heap

/-- This pre-denotation is "tight" on reachability sets. -/
def PreDenot.is_tight (pd : PreDenot) : Prop :=
  ∀ R m fx,
    pd R m (.var (.free fx)) ->
    pd (reachability_of_loc m.heap fx) m (.var (.free fx))

/-- This is a proper pre-denotation. -/
def PreDenot.is_proper (pd : PreDenot) : Prop :=
  pd.is_reachability_safe
  ∧ pd.is_reachability_monotonic
  ∧ pd.implies_wf
  ∧ pd.is_tight
  ∧ ∀ C, (pd C).is_proper

lemma Denot.as_mpost_is_monotonic {d : Denot}
  (hmon : d.is_monotonic) :
  d.as_mpost.is_monotonic := by
  intro m1 m2 e hwf hsub h
  unfold Denot.as_mpost at h ⊢
  exact hmon hsub h

lemma Denot.as_mpost_is_bool_independent {d : Denot}
  (hbool : d.is_bool_independent) :
  d.as_mpost.is_bool_independent := by
  intro m
  simpa only [Denot.as_mpost] using hbool (m := m)

def Denot.Imply (d1 d2 : Denot) : Prop :=
  ∀ m e,
    (d1 m e) ->
    (d2 m e)

def PreDenot.Imply (pd1 pd2 : PreDenot) : Prop :=
  ∀ C,
    (pd1 C).Imply (pd2 C)

def Denot.ImplyAt (d1 : Denot) (m : Memory) (d2 : Denot) : Prop :=
  ∀ e, d1 m e -> d2 m e

def PreDenot.ImplyAt (pd1 pd2 : PreDenot) (m : Memory) : Prop :=
  ∀ C, (pd1 C).ImplyAt m (pd2 C)

def Denot.ImplyAfter (d1 : Denot) (m : Memory) (d2 : Denot) : Prop :=
  ∀ m', m'.subsumes m -> d1.ImplyAt m' d2

def PreDenot.ImplyAfter (pd1 : PreDenot) (m : Memory) (pd2 : PreDenot) : Prop :=
  ∀ C, (pd1 C).ImplyAfter m (pd2 C)

theorem Denot.imply_implyat {d1 d2 : Denot}
  (himp : d1.Imply d2) :
  d1.ImplyAt m d2 := by
  intro e h1
  apply himp m e h1

theorem Denot.implyat_trans
  {d1 d2 : Denot}
  (himp1 : d1.ImplyAt m d2)
  (himp2 : d2.ImplyAt m d3) :
  d1.ImplyAt m d3 := by
  intro e h1
  apply himp2 e (himp1 e h1)

lemma Denot.imply_after_to_m_entails_after {d1 d2 : Denot}
  {m : Memory}
  (himp : d1.ImplyAfter m d2) :
  d1.as_mpost.entails_after m d2.as_mpost := by
  intro m' hsub
  unfold Mpost.entails_at Denot.as_mpost
  intro e h1
  apply himp m' hsub e h1

lemma Denot.imply_after_subsumes {d1 d2 : Denot}
  (himp : d1.ImplyAfter m1 d2)
  (hmem : m2.subsumes m1) :
  d1.ImplyAfter m2 d2 := by
  intro M hs
  apply himp M
  apply Memory.subsumes_trans hs hmem

lemma Denot.imply_after_to_imply_at {d1 d2 : Denot}
  (himp : d1.ImplyAfter m d2) :
  d1.ImplyAt m d2 := by
  intro e h1
  apply himp m (Memory.subsumes_refl m) e h1

lemma Denot.imply_after_trans {d1 d2 d3 : Denot}
  (himp1 : d1.ImplyAfter m d2)
  (himp2 : d2.ImplyAfter m d3) :
  d1.ImplyAfter m d3 := by
  intro m' hsub e h1
  apply himp2 m' hsub
  apply himp1 m' hsub e h1

lemma Denot.apply_imply_at {d1 d2 : Denot}
  (ht : d1 m e)
  (himp : d1.ImplyAt m d2) :
  d2 m e := by
  apply himp e ht

inductive TypeInfo : Kind -> Type where
| var : Nat -> TypeInfo .var
| tvar : PreDenot -> TypeInfo .tvar
| cvar : CaptureSet {} -> TypeInfo .cvar

inductive TypeEnv : Sig -> Type where
| empty : TypeEnv {}
| extend :
  TypeEnv s ->
  TypeInfo k ->
  TypeEnv (s,,k)

def TypeEnv.extend_var (Γ : TypeEnv s) (x : Nat) : TypeEnv (s,x) :=
  Γ.extend (.var x)

def TypeEnv.extend_tvar (Γ : TypeEnv s) (T : PreDenot) : TypeEnv (s,X) :=
  Γ.extend (.tvar T)

def TypeEnv.extend_cvar
  (Γ : TypeEnv s) (ground : CaptureSet {}) :
  TypeEnv (s,C) :=
  Γ.extend (.cvar ground)

def TypeEnv.lookup : (Γ : TypeEnv s) -> (x : BVar s k) -> TypeInfo k
| .extend _ info, .here => info
| .extend Γ _,    .there x => Γ.lookup x

def TypeEnv.lookup_var (Γ : TypeEnv s) (x : BVar s .var) : Nat :=
  match Γ.lookup x with
  | .var y => y

def TypeEnv.lookup_tvar (Γ : TypeEnv s) (x : BVar s .tvar) : PreDenot :=
  match Γ.lookup x with
  | .tvar T => T

def TypeEnv.lookup_cvar (Γ : TypeEnv s) (x : BVar s .cvar) : CaptureSet {} :=
  match Γ.lookup x with
  | .cvar cs => cs

def Subst.from_TypeEnv (env : TypeEnv s) : Subst s {} where
  var := fun x => .free (env.lookup_var x)
  tvar := fun _ => .top
  cvar := fun c => env.lookup_cvar c

theorem Subst.from_TypeEnv_empty :
  Subst.from_TypeEnv TypeEnv.empty = Subst.id := by
  apply Subst.funext
  · intro x; cases x
  · intro X; cases X
  · intro C; cases C

/-- Compute denotation for a ground capture set. -/
def CaptureSet.ground_denot : CaptureSet {} -> CapDenot
| .empty => fun _ => {}
| .union cs1 cs2 => fun m =>
  (cs1.ground_denot m) ∪ (cs2.ground_denot m)
| .var (.free x) => fun m => reachability_of_loc m.heap x

def CaptureSet.denot (ρ : TypeEnv s) (cs : CaptureSet s) : CapDenot :=
  (cs.subst (Subst.from_TypeEnv ρ)).ground_denot

def CaptureBound.denot : TypeEnv s -> CaptureBound s -> CapBoundDenot
| _, .unbound => fun _ => .top
| env, .bound cs => fun m => .set (cs.denot env m)

inductive CapabilitySet.BoundedBy : CapabilitySet -> CapabilityBound -> Prop where
| top :
  CapabilitySet.BoundedBy C CapabilityBound.top
| set :
  C1 ⊆ C2 ->
  CapabilitySet.BoundedBy C1 (CapabilityBound.set C2)

inductive CapabilityBound.SubsetEq : CapabilityBound -> CapabilityBound -> Prop where
| refl :
  CapabilityBound.SubsetEq B B
| set :
  C1 ⊆ C2 ->
  CapabilityBound.SubsetEq (CapabilityBound.set C1) (CapabilityBound.set C2)
| top :
  CapabilityBound.SubsetEq B CapabilityBound.top

instance : HasSubset CapabilityBound where
  Subset := CapabilityBound.SubsetEq

theorem CapabilitySet.BoundedBy.trans
  {C : CapabilitySet} {B1 B2 : CapabilityBound}
  (hbound : CapabilitySet.BoundedBy C B1)
  (hsub : B1 ⊆ B2) :
  CapabilitySet.BoundedBy C B2 := by
  cases hsub with
  | refl => exact hbound
  | set hsub_set =>
    cases hbound with
    | set hbound_set =>
      exact CapabilitySet.BoundedBy.set
        (CapabilitySet.Subset.trans hbound_set hsub_set)
  | top => exact CapabilitySet.BoundedBy.top

mutual

def Ty.shape_val_denot : TypeEnv s -> Ty .shape s -> PreDenot
| _, .top => fun R m e =>
  e.WfInHeap m.heap ∧ resolve_reachability m.heap e ⊆ R
| env, .tvar X => env.lookup_tvar X
| _, .unit => fun _ m e => resolve m.heap e = some .unit
| _, .cap => fun A m e =>
  e.WfInHeap m.heap ∧
  ∃ label : Nat,
    e = .var (.free label) ∧
    m.lookup label = some (.capability .basic) ∧
    label ∈ A
| _, .bool => fun _ m e =>
  resolve m.heap e = some .btrue ∨ resolve m.heap e = some .bfalse
| _, .cell => fun R m e =>
  ∃ l b0,
    e = .var (.free l) ∧
    m.lookup l = some (.capability (.mcell b0)) ∧
    l ∈ R
| env, .arrow T1 T2 => fun A m e =>
  e.WfInHeap m.heap ∧
  ∃ cs T0 t0,
    resolve m.heap e = some (.abs cs T0 t0) ∧
    cs.WfInHeap m.heap ∧
    let R0 := expand_captures m.heap cs
    R0 ⊆ A ∧
    (∀ (arg : Nat) (m' : Memory),
      m'.subsumes m ->
      Ty.capt_val_denot env T1 m' (.var (.free arg)) ->
      -- In precise capabilities, we don't include arg's reachability in the authority
      Ty.exi_exp_denot
        (env.extend_var arg)
        T2 R0 m' (t0.subst (Subst.openVar (.free arg))))
| env, .poly T1 T2 => fun A m e =>
  e.WfInHeap m.heap ∧
  ∃ cs S0 t0,
    resolve m.heap e = some (.tabs cs S0 t0) ∧
    cs.WfInHeap m.heap ∧
    let R0 := expand_captures m.heap cs
    R0 ⊆ A ∧
    (∀ (m' : Memory) (denot : PreDenot),
      m'.subsumes m ->
      denot.is_proper ->
      denot.ImplyAfter m' (Ty.shape_val_denot env T1) ->
      Ty.exi_exp_denot
        (env.extend_tvar denot)
        T2 R0 m' (t0.subst (Subst.openTVar .top)))
| env, .cpoly B T => fun A m e =>
  e.WfInHeap m.heap ∧
  ∃ cs B0 t0,
    resolve m.heap e = some (.cabs cs B0 t0) ∧
    cs.WfInHeap m.heap ∧
    let R0 := expand_captures m.heap cs
    R0 ⊆ A ∧
    (∀ (m' : Memory) (CS : CaptureSet {}),
      CS.WfInHeap m'.heap ->
      let A0 := CS.denot TypeEnv.empty
      m'.subsumes m ->
      ((A0 m').BoundedBy (B.denot env m')) ->
      Ty.exi_exp_denot
        (env.extend_cvar CS)
        T R0 m' (t0.subst (Subst.openCVar CS)))

def Ty.capt_val_denot : TypeEnv s -> Ty .capt s -> Denot
| ρ, .capt C S => fun mem exp =>
  exp.IsSimpleAns ∧
  exp.WfInHeap mem.heap ∧
  (C.subst (Subst.from_TypeEnv ρ)).WfInHeap mem.heap ∧
  Ty.shape_val_denot ρ S (C.denot ρ mem) mem exp

def Ty.exi_val_denot : TypeEnv s -> Ty .exi s -> Denot
| ρ, .typ T => Ty.capt_val_denot ρ T
| ρ, .exi T => fun m e =>
  match resolve m.heap e with
  | some (.pack CS x) =>
    CS.WfInHeap m.heap ∧
    Ty.capt_val_denot (ρ.extend_cvar CS) T m (.var x)
  | _ => False

def Ty.capt_exp_denot : TypeEnv s -> Ty .capt s -> PreDenot
| ρ, T => fun A m (e : Exp {}) =>
  Eval A m e (Ty.capt_val_denot ρ T).as_mpost

def Ty.exi_exp_denot : TypeEnv s -> Ty .exi s -> PreDenot
| ρ, T => fun A m (e : Exp {}) =>
  Eval A m e (Ty.exi_val_denot ρ T).as_mpost

end

@[simp]
instance instCaptHasDenotation :
  HasDenotation (Ty .capt s) (TypeEnv s) Denot where
  interp := Ty.capt_val_denot

@[simp]
instance instCaptHasExpDenotation :
  HasExpDenotation (Ty .capt s) (TypeEnv s) PreDenot where
  interp := Ty.capt_exp_denot

@[simp]
instance instExiHasDenotation :
  HasDenotation (Ty .exi s) (TypeEnv s) Denot where
  interp := Ty.exi_val_denot

@[simp]
instance instExiHasExpDenotation :
  HasExpDenotation (Ty .exi s) (TypeEnv s) PreDenot where
  interp := Ty.exi_exp_denot

@[simp]
instance instShapeHasDenotation :
  HasDenotation (Ty .shape s) (TypeEnv s) PreDenot where
  interp := Ty.shape_val_denot

@[simp]
instance instCaptureSetHasDenotation :
  HasDenotation (CaptureSet s) (TypeEnv s) CapDenot where
  interp := CaptureSet.denot

@[simp]
instance instCaptureBoundHasDenotation :
  HasDenotation (CaptureBound s) (TypeEnv s) CapBoundDenot where
  interp := CaptureBound.denot

/-- Unfolding lemma for capturing-type denotation. -/
theorem capt_val_denot_capt
  (env : TypeEnv s) (C : CaptureSet s) (S : Ty .shape s) :
    ⟦Ty.capt C S⟧_[env] = fun mem exp =>
    exp.IsSimpleAns ∧
    exp.WfInHeap mem.heap ∧
    (C.subst (Subst.from_TypeEnv env)).WfInHeap mem.heap ∧
    Ty.shape_val_denot env S (C.denot env mem) mem exp := by
  change Ty.capt_val_denot env (Ty.capt C S) = _
  exact Ty.capt_val_denot.eq_1 env C S

/-- Unfolding lemma for shape-type denotation (cap case). -/
theorem shape_val_denot_cap (env : TypeEnv s) :
    ⟦(Ty.cap : Ty .shape s)⟧_[env] = fun A m e =>
    e.WfInHeap m.heap ∧
    ∃ label : Nat,
      e = .var (.free label) ∧
      m.lookup label = some (.capability .basic) ∧
      label ∈ A := by
  change Ty.shape_val_denot env Ty.cap = _
  exact Ty.shape_val_denot.eq_4 env

def EnvTyping : Ctx s -> TypeEnv s -> Memory -> Prop
| .empty, .empty, _ => True
| .push Γ (.var T), .extend env (.var n), m =>
  ⟦T⟧_[env] m (.var (.free n)) ∧
  EnvTyping Γ env m
| .push Γ (.tvar S), .extend env (.tvar denot), m =>
  denot.is_proper ∧
  denot.ImplyAfter m ⟦S⟧_[env] ∧
  EnvTyping Γ env m
| .push Γ (.cvar B), .extend env (.cvar cs), m =>
  (cs.WfInHeap m.heap) ∧
  ((B.subst (Subst.from_TypeEnv env)).WfInHeap m.heap) ∧
  ((cs.ground_denot m).BoundedBy (⟦B⟧_[env] m)) ∧
  EnvTyping Γ env m

def SemanticTyping (C : CaptureSet s) (Γ : Ctx s) (e : Exp s) (E : Ty .exi s) : Prop :=
  ∀ ρ m,
    EnvTyping Γ ρ m ->
    ⟦E⟧e_[ρ] (C.denot ρ m) m (e.subst (Subst.from_TypeEnv ρ))

notation:65 C " # " Γ " ⊨ " e " : " T => SemanticTyping C Γ e T

theorem Subst.from_TypeEnv_weaken_open {s : Sig} {env : TypeEnv s} {n : Nat} :
  (Subst.from_TypeEnv env).lift.comp (Subst.openVar (.free n)) =
    Subst.from_TypeEnv (env.extend_var n) := by
  apply Subst.funext
  · intro y
    cases y <;> rfl
  · intro X
    cases X
    rfl
  · intro C
    cases C with
    | there C' =>
      simpa only [Subst.from_TypeEnv, Subst.lift, Subst.comp, Subst.openVar,
        TypeEnv.lookup_cvar, TypeEnv.lookup] using CaptureSet.weaken_openVar

theorem Exp.from_TypeEnv_weaken_open {s : Sig} {env : TypeEnv s} {n : Nat}
    {e : Exp (Sig.extend_var s)} :
  (e.subst (Subst.from_TypeEnv env).lift).subst (Subst.openVar (.free n)) =
    e.subst (Subst.from_TypeEnv (env.extend_var n)) := by
  rw [Exp.subst_comp]
  exact congrArg _ Subst.from_TypeEnv_weaken_open

theorem Subst.from_TypeEnv_weaken_open_tvar {env : TypeEnv s} {d : PreDenot} :
  (Subst.from_TypeEnv env).lift.comp (Subst.openTVar .top) =
    Subst.from_TypeEnv (env.extend_tvar d) := by
  apply Subst.funext
  · intro x
    cases x
    rfl
  · intro X
    cases X
    case here => rfl
    case there X' =>
      simp [Subst.comp, Subst.lift, Subst.from_TypeEnv, Subst.openTVar,
        TypeEnv.extend_tvar, Ty.subst, Ty.rename]
  · intro C
    cases C with
    | there C' =>
      simpa only [Subst.from_TypeEnv, Subst.lift, Subst.comp, Subst.openTVar,
        TypeEnv.lookup_cvar, TypeEnv.lookup] using CaptureSet.weaken_openTVar

theorem Exp.from_TypeEnv_weaken_open_tvar
  {env : TypeEnv s} {d : PreDenot} {e : Exp (s,X)} :
  (e.subst (Subst.from_TypeEnv env).lift).subst (Subst.openTVar .top) =
    e.subst (Subst.from_TypeEnv (env.extend_tvar d)) := by
  rw [Exp.subst_comp]
  exact congrArg _ Subst.from_TypeEnv_weaken_open_tvar

theorem Subst.from_TypeEnv_weaken_open_cvar
  {env : TypeEnv s} {cs : CaptureSet {}} :
  (Subst.from_TypeEnv env).lift.comp (Subst.openCVar cs) =
    Subst.from_TypeEnv (env.extend_cvar cs) := by
  apply Subst.funext
  · intro x
    cases x
    rfl
  · intro X
    cases X
    rfl
  · intro C
    cases C
    case here => rfl
    case there C' =>
      simpa only [Subst.comp, Subst.lift, Subst.from_TypeEnv, Subst.openCVar,
        TypeEnv.lookup_cvar, TypeEnv.lookup] using CaptureSet.weaken_openCVar

theorem Exp.from_TypeEnv_weaken_open_cvar
  {env : TypeEnv s} {cs : CaptureSet {}} {e : Exp (s,C)} :
  (e.subst (Subst.from_TypeEnv env).lift).subst (Subst.openCVar cs) =
    e.subst (Subst.from_TypeEnv (env.extend_cvar cs)) := by
  rw [Exp.subst_comp]
  exact congrArg _ Subst.from_TypeEnv_weaken_open_cvar

theorem Subst.from_TypeEnv_weaken_unpack :
  (Subst.from_TypeEnv ρ).lift.lift.comp (Subst.unpack cs (.free x)) =
    Subst.from_TypeEnv ((ρ.extend_cvar cs).extend_var x) := by
  apply Subst.funext
  · -- var case
    intro y
    cases y
    case here =>
      -- LHS: unpack maps .here to .free x, which is unchanged by subst
      -- RHS: from_TypeEnv of extend_var maps .here to .free x
      rfl
    case there y' =>
      cases y'
      case there v =>
        simp only [Subst.comp, Subst.unpack, Var.subst]
        rw [Subst.lift_there_var_eq]
        rw [Subst.lift_there_var_eq]
        simp [Subst.from_TypeEnv, Var.rename, TypeEnv.lookup_var]
        rfl
  · -- tvar case
    intro X
    cases X
    case there X' =>
      cases X'
      case there X0 =>
        -- Both sides map to .top
        rfl
  · -- cvar case
    intro c
    cases c
    case there c' =>
      cases c'
      case here =>
        -- LHS: comp maps .there .here through unpack then lift.lift
        -- unpack.cvar (.there .here) = cs
        -- Then cs.subst lift.lift, but cs : CaptureSet {} has no bound vars
        simp only [Subst.comp, Subst.unpack]
        -- Need to show: (lift.lift.cvar (.there .here)).subst unpack = cs
        -- This is unpack.cvar (.there .here) = cs by definition
        rw [Subst.lift_there_cvar_eq]
        simp [Subst.lift, CaptureSet.subst, CaptureSet.rename]
        -- Goal: match Rename.succ.var .here with | .here.there => cs | ... = cs
        -- Rename.succ.var .here = .here.there by definition
        rfl
      case there c0 =>
        have helper : ∀ (g : CaptureSet {}),
            ((g.rename Rename.succ).rename Rename.succ).subst
              (Subst.unpack cs (.free x)) = g := by
          intro g
          induction g with
          | empty => rfl
          | union g1 g2 ih1 ih2 =>
            change CaptureSet.subst _ _ = _
            simp only [CaptureSet.rename, CaptureSet.subst]
            rw [ih1, ih2]
          | var v =>
            cases v with
            | bound bv => cases bv
            | free n => rfl
          | cvar cv => cases cv
        change CaptureSet.subst (CaptureSet.rename (CaptureSet.rename (ρ.lookup_cvar c0)
          Rename.succ) Rename.succ) (Subst.unpack cs (.free x)) = _
        rw [helper (ρ.lookup_cvar c0)]
        rfl
        /-
        simp [Subst.comp, Subst.unpack]
        rw [Subst.lift_there_cvar_eq]
        rw [Subst.lift_there_cvar_eq]
        simp only [Subst.from_TypeEnv, TypeEnv.extend_var, TypeEnv.extend_cvar,
          TypeEnv.lookup_cvar, TypeEnv.lookup]
        generalize (match ρ.lookup c0 with | TypeInfo.cvar cs => cs) = ground_cs
        -- Goal: double rename + subst on ground_cs equals ground_cs
        induction ground_cs with
        | empty => rfl  -- .empty.rename.rename.subst = .empty
        | union cs1 cs2 ih1 ih2 =>
          -- .union case: distribute rename/subst over both sides
          simp only [CaptureSet.rename, CaptureSet.subst, ih1, ih2]
        | var v =>
          cases v with
          | bound bv => cases bv  -- Impossible: no bound vars in {}
          | free n =>
            -- .var (.free n).rename.rename.subst = .var (.free n)
            rfl
        | cvar cv => cases cv  -- Impossible: no capture vars in {}
        -/

/--
If a TypeEnv is typed with EnvTyping, then the substitution obtained from it
via `Subst.from_TypeEnv` is well-formed in the heap.

This is a key lemma connecting the semantic typing judgment to syntactic well-formedness.
Since `EnvTyping` ensures each variable location in the environment exists in memory,
the substitution that maps variables to these locations must be well-formed.
-/
theorem from_TypeEnv_wf_in_heap
  {Γ : Ctx s} {ρ : TypeEnv s} {m : Memory}
  (htyping : EnvTyping Γ ρ m) :
  (Subst.from_TypeEnv ρ).WfInHeap m.heap := by
  induction Γ with
  | empty =>
    -- Base case: empty context has no variables
    cases ρ with
    | empty =>
      constructor
      · intro x; cases x
      · intro X; cases X
      · intro C; cases C
  | push Γ' k ih =>
    -- Inductive case: handle each kind of binding
    cases ρ with
    | extend ρ' info =>
      cases k with
      | var T =>
        -- Variable binding: extract well-formedness from typing
        cases info with
        | var n =>
          unfold EnvTyping at htyping
          have ⟨htype, htyping'⟩ := htyping
          -- htype : ⟦T⟧_[ρ'] m (.var (.free n))
          cases T with
          | capt C S =>
            rw [capt_val_denot_capt] at htype
            have ⟨_, hwf, _, _⟩ := htype
            cases hwf with
            | wf_var hwf_var =>
              have ih_wf := ih htyping'
              constructor
              · intro x
                cases x with
                | here => exact hwf_var
                | there x' => exact ih_wf.wf_var x'
              · intro X
                cases X with
                | there X' => exact ih_wf.wf_tvar X'
              · intro C_var
                cases C_var with
                | there C' => exact ih_wf.wf_cvar C'
      | tvar S =>
        -- Type variable binding: doesn't affect term variable substitution
        cases info with
        | tvar denot =>
          change denot.is_proper ∧ denot.ImplyAfter m ⟦S⟧_[ρ'] ∧ EnvTyping Γ' ρ' m at htyping
          have htyping' := htyping.2.2
          have ih_wf := ih htyping'
          constructor
          · intro x
            cases x with
            | there x' =>
              simpa only [Subst.from_TypeEnv, TypeEnv.lookup_var, TypeEnv.lookup] using
                ih_wf.wf_var x'
          · intro X
            cases X with
            | here =>
              simpa only [Subst.from_TypeEnv] using Ty.WfInHeap.wf_top
            | there X' =>
              simpa only [Subst.from_TypeEnv] using ih_wf.wf_tvar X'
          · intro C_var
            cases C_var with
            | there C' =>
              simpa only [Subst.from_TypeEnv] using ih_wf.wf_cvar C'
      | cvar B =>
        -- Capture variable binding: doesn't affect term variable substitution
        cases info with
        | cvar cs =>
          change cs.WfInHeap m.heap ∧
              (B.subst (Subst.from_TypeEnv ρ')).WfInHeap m.heap ∧
              (cs.ground_denot m).BoundedBy (⟦B⟧_[ρ'] m) ∧
              EnvTyping Γ' ρ' m at htyping
          have hwf := htyping.1
          have htyping' := htyping.2.2.2
          have ih_wf := ih htyping'
          constructor
          · intro x
            cases x with
            | there x' =>
              simpa only [Subst.from_TypeEnv, TypeEnv.lookup_var, TypeEnv.lookup] using
                ih_wf.wf_var x'
          · intro X
            cases X with
            | there X' =>
              simpa only [Subst.from_TypeEnv] using ih_wf.wf_tvar X'
          · intro C_var
            cases C_var with
            | here =>
              simpa only [Subst.from_TypeEnv, TypeEnv.lookup_cvar, TypeEnv.lookup] using hwf
            | there C' =>
              simpa only [Subst.from_TypeEnv] using ih_wf.wf_cvar C'

def Denot.Equiv (d1 d2 : Denot) : Prop :=
  ∀ m e,
    (d1 m e) ↔ (d2 m e)

instance Denot.instHasEquiv : HasEquiv Denot where
  Equiv := Denot.Equiv

def Denot.equiv_refl (d : Denot) : d ≈ d := by
  intro m e
  constructor
  · intro h
    exact h
  · intro h
    exact h

def Denot.equiv_symm (d1 d2 : Denot) : d1 ≈ d2 -> d2 ≈ d1 := by
  intro h m e
  constructor
  · intro h0
    apply (h m e).mpr h0
  · intro h0
    apply (h m e).mp h0

def Denot.equiv_trans (d1 d2 d3 : Denot) : d1 ≈ d2 -> d2 ≈ d3 -> d1 ≈ d3 := by
  intro h12 h23 m e
  have h1 := h12 m e
  have h2 := h23 m e
  grind

theorem Denot.eq_to_equiv (d1 d2 : Denot) : d1 = d2 -> d1 ≈ d2 := by
  intro h m e
  grind

theorem Denot.equiv_ltr {d1 d2 : Denot}
  (heqv : d1 ≈ d2)
  (h1 : d1 m e) :
  d2 m e := by
  apply (heqv m e).mp h1

theorem Denot.equiv_rtl {d1 d2 : Denot}
  (heqv : d1 ≈ d2)
  (h2 : d2 m e) :
  d1 m e := by
  apply (heqv m e).mpr h2

theorem Denot.equiv_to_imply {d1 d2 : Denot}
  (heqv : d1 ≈ d2) :
  (d1.Imply d2) ∧ (d2.Imply d1) := by
  constructor
  · intro m e h
    apply (heqv m e).mp h
  · intro m e h
    apply (heqv m e).mpr h

theorem Denot.equiv_to_imply_l {d1 d2 : Denot}
  (heqv : d1 ≈ d2) :
  d1.Imply d2 := (Denot.equiv_to_imply heqv).1

theorem Denot.equiv_to_imply_r {d1 d2 : Denot}
  (heqv : d1 ≈ d2) :
  d2.Imply d1 := (Denot.equiv_to_imply heqv).2

theorem Denot.imply_to_entails (d1 d2 : Denot)
  (himp : d1.Imply d2) :
  d1.as_mpost.entails d2.as_mpost := by
  intro m e h1
  apply himp m e h1

/- Equivalence for PreDenot -/
def PreDenot.Equiv (pd1 pd2 : PreDenot) : Prop :=
  ∀ A, (pd1 A) ≈ (pd2 A)

instance PreDenot.instHasEquiv : HasEquiv PreDenot where
  Equiv := PreDenot.Equiv

theorem PreDenot.equiv_def {pd1 pd2 : PreDenot} :
  pd1 ≈ pd2 ↔ ∀ A m e, (pd1 A m e) ↔ (pd2 A m e) := by
  constructor
  · intro h A m e
    exact (h A) m e
  · intro h A m e
    exact h A m e

theorem PreDenot.eq_to_equiv {pd1 pd2 : PreDenot} (h : pd1 = pd2) : pd1 ≈ pd2 := by
  intro A m e
  rw [h]

theorem PreDenot.equiv_refl (pd : PreDenot) : pd ≈ pd := by
  intro A
  apply Denot.equiv_refl

theorem PreDenot.equiv_symm (pd1 pd2 : PreDenot) : pd1 ≈ pd2 -> pd2 ≈ pd1 := by
  intro h A
  apply Denot.equiv_symm
  exact h A

theorem PreDenot.equiv_trans (pd1 pd2 pd3 : PreDenot) : pd1 ≈ pd2 -> pd2 ≈ pd3 -> pd1 ≈ pd3 := by
  intro h12 h23 A
  apply Denot.equiv_trans _ (pd2 A) _
  · exact h12 A
  · exact h23 A

theorem Denot.imply_refl (d : Denot) : d.Imply d := by
  intro m e h
  exact h

theorem Denot.imply_trans {d1 d2 d3 : Denot}
  (h1 : d1.Imply d2)
  (h2 : d2.Imply d3) :
  d1.Imply d3 := by
  intro m e h
  aesop

theorem resolve_var_heap_some
  (hheap : heap x = some (.val v)) :
  resolve heap (.var (.free x)) = some v.unwrap := by
  simp [resolve, hheap]

theorem resolve_val
  (hval : v.IsVal) :
  resolve heap v = some v := by
  cases hval <;> rfl

theorem resolve_var_heap_trans
  (hheap : heap x = some (.val v)) :
  resolve heap (.var (.free x)) = resolve heap (v.unwrap) := by
  rw [resolve_var_heap_some hheap]
  rw [resolve_val v.isVal.to_IsVal]

theorem resolve_var_or_val
  (hv : resolve store e = some v) :
  (∃ x, e = .var x) ∨ e = v := by
  cases e
  all_goals try (solve | aesop | simp [resolve] at hv; aesop)

theorem resolve_ans_to_val
  (hv : resolve store e = some v)
  (hans : v.IsAns) :
  e.IsAns := by
  cases (resolve_var_or_val hv)
  case inl h =>
    have ⟨x, h⟩ := h
    rw [h]
    apply Exp.IsAns.is_var
  case inr h => aesop

def PreDenot.is_monotonic (pd : PreDenot) : Prop :=
  ∀ C, (pd C).is_monotonic

def PreDenot.is_transparent (pd : PreDenot) : Prop :=
  ∀ C, (pd C).is_transparent

def PreDenot.is_bool_independent (pd : PreDenot) : Prop :=
  ∀ C, (pd C).is_bool_independent

structure TypeEnv.IsMonotonic (env : TypeEnv s) : Prop where
  tvar : ∀ (X : BVar s .tvar),
    (env.lookup_tvar X).is_monotonic

def TypeEnv.is_transparent (env : TypeEnv s) : Prop :=
  ∀ (X : BVar s .tvar),
    (env.lookup_tvar X).is_transparent

def TypeEnv.is_bool_independent (env : TypeEnv s) : Prop :=
  ∀ (X : BVar s .tvar),
    (env.lookup_tvar X).is_bool_independent

def TypeEnv.is_reachability_safe (env : TypeEnv s) : Prop :=
  ∀ (X : BVar s .tvar),
    (env.lookup_tvar X).is_reachability_safe

def TypeEnv.is_reachability_monotonic (env : TypeEnv s) : Prop :=
  ∀ (X : BVar s .tvar),
    (env.lookup_tvar X).is_reachability_monotonic

def TypeEnv.is_implying_wf (env : TypeEnv s) : Prop :=
  ∀ (X : BVar s .tvar),
    (env.lookup_tvar X).implies_wf

def TypeEnv.is_tight (env : TypeEnv s) : Prop :=
  ∀ (X : BVar s .tvar),
    (env.lookup_tvar X).is_tight

theorem typed_env_is_monotonic
  (ht : EnvTyping Γ env mem) :
  env.IsMonotonic := by
  induction Γ with
  | empty =>
    cases env with
    | empty =>
      constructor
      · intro x; cases x
  | push Γ k ih =>
    cases env with
    | extend env' info =>
      cases k with
      | var T =>
        cases info with
        | var n =>
          change ⟦T⟧_[env'] mem (.var (.free n)) ∧ EnvTyping Γ env' mem at ht
          have ht' := ht.2
          have ih_result := ih ht'
          constructor
          · intro x
            cases x with
            | there x =>
              change (env'.lookup_tvar x).is_monotonic
              exact ih_result.tvar x
      | tvar S =>
        cases info with
        | tvar d =>
          change d.is_proper ∧ d.ImplyAfter mem ⟦S⟧_[env'] ∧ EnvTyping Γ env' mem at ht
          have hproper := ht.1
          have ht' := ht.2.2
          have ih_result := ih ht'
          constructor
          · intro x
            cases x with
            | here =>
              change d.is_monotonic
              intro C
              exact (hproper.2.2.2.2 C).1
            | there x =>
              change (env'.lookup_tvar x).is_monotonic
              exact ih_result.tvar x
      | cvar B =>
        cases info with
        | cvar cs =>
          change cs.WfInHeap mem.heap ∧
              (B.subst (Subst.from_TypeEnv env')).WfInHeap mem.heap ∧
              (cs.ground_denot mem).BoundedBy (⟦B⟧_[env'] mem) ∧
              EnvTyping Γ env' mem at ht
          have ht' := ht.2.2.2
          have ih_result := ih ht'
          constructor
          · intro x
            cases x with
            | there x =>
              change (env'.lookup_tvar x).is_monotonic
              exact ih_result.tvar x

theorem typed_env_is_transparent
  (ht : EnvTyping Γ env mem) :
  env.is_transparent := by
  induction Γ with
  | empty =>
    cases env with
    | empty =>
      intro x
      cases x
  | push Γ k ih =>
    cases env with
    | extend env' info =>
      cases k with
      | var T =>
        cases info with
        | var n =>
          change ⟦T⟧_[env'] mem (.var (.free n)) ∧ EnvTyping Γ env' mem at ht
          have ht' := ht.2
          have ih_result := ih ht'
          intro x
          cases x with
          | there x =>
            change (env'.lookup_tvar x).is_transparent
            exact ih_result x
      | tvar S =>
        cases info with
        | tvar d =>
          change d.is_proper ∧ d.ImplyAfter mem ⟦S⟧_[env'] ∧ EnvTyping Γ env' mem at ht
          have hproper := ht.1
          have ht' := ht.2.2
          have ih_result := ih ht'
          intro x
          cases x with
          | here =>
            change d.is_transparent
            intro C
            exact (hproper.2.2.2.2 C).2.1
          | there x =>
            change (env'.lookup_tvar x).is_transparent
            exact ih_result x
      | cvar B =>
        cases info with
        | cvar cs =>
          change cs.WfInHeap mem.heap ∧
              (B.subst (Subst.from_TypeEnv env')).WfInHeap mem.heap ∧
              (cs.ground_denot mem).BoundedBy (⟦B⟧_[env'] mem) ∧
              EnvTyping Γ env' mem at ht
          have ht' := ht.2.2.2
          have ih_result := ih ht'
          intro x
          cases x with
          | there x =>
            change (env'.lookup_tvar x).is_transparent
            exact ih_result x

theorem typed_env_is_bool_independent
  (ht : EnvTyping Γ env mem) :
  env.is_bool_independent := by
  induction Γ with
  | empty =>
    cases env with
    | empty =>
      intro x
      cases x
  | push Γ k ih =>
    cases env with
    | extend env' info =>
      cases k with
      | var T =>
        cases info with
        | var n =>
          change ⟦T⟧_[env'] mem (.var (.free n)) ∧ EnvTyping Γ env' mem at ht
          have ht' := ht.2
          have ih_result := ih ht'
          intro x
          cases x with
          | there x =>
            change (env'.lookup_tvar x).is_bool_independent
            exact ih_result x
      | tvar S =>
        cases info with
        | tvar d =>
          change d.is_proper ∧ d.ImplyAfter mem ⟦S⟧_[env'] ∧ EnvTyping Γ env' mem at ht
          have hproper := ht.1
          have ht' := ht.2.2
          have ih_result := ih ht'
          intro x
          cases x with
          | here =>
            change d.is_bool_independent
            intro C
            exact (hproper.2.2.2.2 C).2.2
          | there x =>
            change (env'.lookup_tvar x).is_bool_independent
            exact ih_result x
      | cvar B =>
        cases info with
        | cvar cs =>
          change cs.WfInHeap mem.heap ∧
              (B.subst (Subst.from_TypeEnv env')).WfInHeap mem.heap ∧
              (cs.ground_denot mem).BoundedBy (⟦B⟧_[env'] mem) ∧
              EnvTyping Γ env' mem at ht
          have ht' := ht.2.2.2
          have ih_result := ih ht'
          intro x
          cases x with
          | there x =>
            change (env'.lookup_tvar x).is_bool_independent
            exact ih_result x

theorem typed_env_is_reachability_safe
  (ht : EnvTyping Γ env mem) :
  env.is_reachability_safe := by
  induction Γ with
  | empty =>
    cases env with
    | empty =>
      intro x
      cases x
  | push Γ k ih =>
    cases env with
    | extend env' info =>
      cases k with
      | var T =>
        cases info with
        | var n =>
          change ⟦T⟧_[env'] mem (.var (.free n)) ∧ EnvTyping Γ env' mem at ht
          have ht' := ht.2
          have ih_result := ih ht'
          intro x
          cases x with
          | there x =>
            change (env'.lookup_tvar x).is_reachability_safe
            exact ih_result x
      | tvar S =>
        cases info with
        | tvar d =>
          change d.is_proper ∧ d.ImplyAfter mem ⟦S⟧_[env'] ∧ EnvTyping Γ env' mem at ht
          have hproper := ht.1
          have ht' := ht.2.2
          have ih_result := ih ht'
          intro x
          cases x with
          | here =>
            change d.is_reachability_safe
            exact hproper.1
          | there x =>
            change (env'.lookup_tvar x).is_reachability_safe
            exact ih_result x
      | cvar B =>
        cases info with
        | cvar cs =>
          change cs.WfInHeap mem.heap ∧
              (B.subst (Subst.from_TypeEnv env')).WfInHeap mem.heap ∧
              (cs.ground_denot mem).BoundedBy (⟦B⟧_[env'] mem) ∧
              EnvTyping Γ env' mem at ht
          have ht' := ht.2.2.2
          have ih_result := ih ht'
          intro x
          cases x with
          | there x =>
            change (env'.lookup_tvar x).is_reachability_safe
            exact ih_result x

theorem typed_env_is_reachability_monotonic
  (ht : EnvTyping Γ env mem) :
  env.is_reachability_monotonic := by
  induction Γ with
  | empty =>
    cases env with
    | empty =>
      intro x
      cases x
  | push Γ k ih =>
    cases env with
    | extend env' info =>
      cases k with
      | var T =>
        cases info with
        | var n =>
          change ⟦T⟧_[env'] mem (.var (.free n)) ∧ EnvTyping Γ env' mem at ht
          have ht' := ht.2
          have ih_result := ih ht'
          intro x
          cases x with
          | there x =>
            change (env'.lookup_tvar x).is_reachability_monotonic
            exact ih_result x
      | tvar S =>
        cases info with
        | tvar d =>
          change d.is_proper ∧ d.ImplyAfter mem ⟦S⟧_[env'] ∧ EnvTyping Γ env' mem at ht
          have hproper := ht.1
          have ht' := ht.2.2
          have ih_result := ih ht'
          intro x
          cases x with
          | here =>
            change d.is_reachability_monotonic
            exact hproper.2.1
          | there x =>
            change (env'.lookup_tvar x).is_reachability_monotonic
            exact ih_result x
      | cvar B =>
        cases info with
        | cvar cs =>
          change cs.WfInHeap mem.heap ∧
              (B.subst (Subst.from_TypeEnv env')).WfInHeap mem.heap ∧
              (cs.ground_denot mem).BoundedBy (⟦B⟧_[env'] mem) ∧
              EnvTyping Γ env' mem at ht
          have ht' := ht.2.2.2
          have ih_result := ih ht'
          intro x
          cases x with
          | there x =>
            change (env'.lookup_tvar x).is_reachability_monotonic
            exact ih_result x

theorem typed_env_is_implying_wf
  (ht : EnvTyping Γ env mem) :
  env.is_implying_wf := by
  induction Γ with
  | empty =>
    cases env with
    | empty =>
      intro x
      cases x
  | push Γ k ih =>
    cases env with
    | extend env' info =>
      cases k with
      | var T =>
        cases info with
        | var n =>
          change ⟦T⟧_[env'] mem (.var (.free n)) ∧ EnvTyping Γ env' mem at ht
          have ht' := ht.2
          have ih_result := ih ht'
          intro x
          cases x with
          | there x =>
            change (env'.lookup_tvar x).implies_wf
            exact ih_result x
      | tvar S =>
        cases info with
        | tvar d =>
          change d.is_proper ∧ d.ImplyAfter mem ⟦S⟧_[env'] ∧ EnvTyping Γ env' mem at ht
          have hproper := ht.1
          have ht' := ht.2.2
          have ih_result := ih ht'
          intro x
          cases x with
          | here =>
            change d.implies_wf
            exact hproper.2.2.1
          | there x =>
            change (env'.lookup_tvar x).implies_wf
            exact ih_result x
      | cvar B =>
        cases info with
        | cvar cs =>
          change cs.WfInHeap mem.heap ∧
              (B.subst (Subst.from_TypeEnv env')).WfInHeap mem.heap ∧
              (cs.ground_denot mem).BoundedBy (⟦B⟧_[env'] mem) ∧
              EnvTyping Γ env' mem at ht
          have ht' := ht.2.2.2
          have ih_result := ih ht'
          intro x
          cases x with
          | there x =>
            change (env'.lookup_tvar x).implies_wf
            exact ih_result x

theorem typed_env_is_tight
  (ht : EnvTyping Γ env mem) :
  env.is_tight := by
  induction Γ with
  | empty =>
    cases env with
    | empty =>
      intro X
      cases X
  | push Γ k ih =>
    cases env with
    | extend env' info =>
      cases k with
      | var T =>
        cases info with
        | var n =>
          change ⟦T⟧_[env'] mem (.var (.free n)) ∧ EnvTyping Γ env' mem at ht
          have ht' := ht.2
          have ih_result := ih ht'
          intro X
          cases X with
          | there X' =>
            change (env'.lookup_tvar X').is_tight
            exact ih_result X'
      | tvar S =>
        cases info with
        | tvar d =>
          change d.is_proper ∧ d.ImplyAfter mem ⟦S⟧_[env'] ∧ EnvTyping Γ env' mem at ht
          have hproper := ht.1
          have ht' := ht.2.2
          have ih_result := ih ht'
          intro X
          cases X with
          | here =>
            change d.is_tight
            exact hproper.2.2.2.1
          | there X' =>
            change (env'.lookup_tvar X').is_tight
            exact ih_result X'
      | cvar B =>
        cases info with
        | cvar cs =>
          change cs.WfInHeap mem.heap ∧
              (B.subst (Subst.from_TypeEnv env')).WfInHeap mem.heap ∧
              (cs.ground_denot mem).BoundedBy (⟦B⟧_[env'] mem) ∧
              EnvTyping Γ env' mem at ht
          have ht' := ht.2.2.2
          have ih_result := ih ht'
          intro X
          cases X with
          | there X' =>
            change (env'.lookup_tvar X').is_tight
            exact ih_result X'

theorem shape_val_denot_is_transparent {env : TypeEnv s}
  (henv : TypeEnv.is_transparent env)
  (T : Ty .shape s) :
  (Ty.shape_val_denot env T).is_transparent := by
  cases T with
  | top =>
    intro C m x v hx ht
    simp only [Ty.shape_val_denot] at ht ⊢
    -- ht : v.unwrap.WfInHeap m.heap ∧ resolve_reachability m.heap v.unwrap ⊆ C
    -- Goal: (.var (.free x)).WfInHeap m.heap ∧ resolve_reachability m.heap (.var (.free x)) ⊆ C
    constructor
    · -- Prove: (.var (.free x)).WfInHeap m.heap
      apply Exp.WfInHeap.wf_var
      apply Var.WfInHeap.wf_free
      exact hx
    · -- Prove: resolve_reachability m.heap (.var (.free x)) ⊆ C
      simp only [resolve_reachability]
      -- Goal: reachability_of_loc m.heap x ⊆ C
      -- Extract heap location from memory lookup
      have hx_heap : m.heap x = some (Cell.val v) := by
        simpa only [Memory.lookup] using hx
      -- Use heap invariant to connect stored reachability with resolve_reachability
      rw [reachability_of_loc_eq_resolve_reachability m x v hx_heap]
      -- Now goal is: resolve_reachability m.heap v.unwrap ⊆ C, which is ht.2
      exact ht.2
  | tvar X =>
    intro C m x v hx ht
    simpa only [Ty.shape_val_denot] using
      henv X C hx (by simpa only [Ty.shape_val_denot] using ht)
  | unit =>
    intro C m x v hx ht
    simp only [Ty.shape_val_denot] at ht ⊢
    have hx' : m.heap x = some (.val v) := by
      simpa only [Memory.lookup] using hx
    rw [resolve_var_heap_trans hx']
    exact ht
  | cap =>
    intro C m x v hx ht
    simp only [Ty.shape_val_denot] at ht ⊢
    have ⟨_, label, hlabel, hcap, hmem⟩ := ht
    -- v.unwrap = .var (.free label), but v.isVal says it's a simple value
    -- Variables are not simple values, so this is a contradiction
    have hval := v.isVal
    rw [hlabel] at hval
    cases hval
  | arrow T1 T2 =>
    intro C m x v hx ht
    simp only [Ty.shape_val_denot] at ht ⊢
    have hx' : m.heap x = some (.val v) := by
      simpa only [Memory.lookup] using hx
    have heq := resolve_var_heap_trans hx'
    rw [heq]
    -- Split ht into well-formedness and existential parts
    have ⟨hwf_unwrap, hexists⟩ := ht
    constructor
    · -- Prove (Exp.var (Var.free x)).WfInHeap m.heap
      constructor
      constructor
      exact hx'
    · -- The existential part remains the same
      exact hexists
  | bool =>
    intro C m x v hx ht
    simp only [Ty.shape_val_denot] at ht ⊢
    rw [resolve_var_heap_trans (by simpa only [Memory.lookup] using hx)]
    exact ht
  | cell =>
    intro C m x v hx ht
    simp only [Ty.shape_val_denot] at ht ⊢
    obtain ⟨l, b0, heq, hlookup_and_mem⟩ := ht
    -- v.unwrap = .var (.free l), but v.isVal says it's a simple value
    -- Variables are not simple values, so this is a contradiction
    have hval := v.isVal
    rw [heq] at hval
    cases hval
  | poly T1 T2 =>
    intro C m x v hx ht
    simp only [Ty.shape_val_denot] at ht ⊢
    have hx' : m.heap x = some (.val v) := by
      simpa only [Memory.lookup] using hx
    have heq := resolve_var_heap_trans hx'
    rw [heq]
    -- Split ht into well-formedness and existential parts
    have ⟨hwf_unwrap, hexists⟩ := ht
    constructor
    · -- Prove (Exp.var (Var.free x)).WfInHeap m.heap
      constructor
      constructor
      exact hx'
    · -- The existential part remains the same
      exact hexists
  | cpoly B T =>
    intro C m x v hx ht
    simp only [Ty.shape_val_denot] at ht ⊢
    have hx' : m.heap x = some (.val v) := by
      simpa only [Memory.lookup] using hx
    have heq := resolve_var_heap_trans hx'
    rw [heq]
    -- Split ht into well-formedness and existential parts
    have ⟨hwf_unwrap, hexists⟩ := ht
    constructor
    · -- Prove (Exp.var (Var.free x)).WfInHeap m.heap
      constructor
      constructor
      exact hx'
    · -- The existential part remains the same
      exact hexists

theorem shape_val_denot_is_bool_independent {env : TypeEnv s}
  (henv : env.is_bool_independent)
  (T : Ty .shape s) :
  ∀ C, (Ty.shape_val_denot env T C).is_bool_independent := by
  intro C m
  cases T with
  | top =>
    simp only [Ty.shape_val_denot, resolve_reachability]
    constructor
    · intro _
      constructor
      · exact Exp.WfInHeap.wf_bfalse
      · exact CapabilitySet.empty_subset
    · intro _
      constructor
      · exact Exp.WfInHeap.wf_btrue
      · exact CapabilitySet.empty_subset
  | tvar X =>
    simpa only [Ty.shape_val_denot] using henv X C (m := m)
  | unit =>
    simp only [Ty.shape_val_denot, resolve]
    constructor
    · intro h
      cases h
    · intro h
      cases h
  | cap =>
    simp only [Ty.shape_val_denot]
    constructor
    · intro h
      rcases h with ⟨_, label, hEq, _, _⟩
      cases hEq
    · intro h
      rcases h with ⟨_, label, hEq, _, _⟩
      cases hEq
  | bool =>
    simp only [Ty.shape_val_denot, resolve]
    constructor
    · intro _
      exact Or.inr trivial
    · intro _
      exact Or.inl trivial
  | cell =>
    simp only [Ty.shape_val_denot]
    constructor
    · intro h
      rcases h with ⟨_, _, hEq, _, _⟩
      cases hEq
    · intro h
      rcases h with ⟨_, _, hEq, _, _⟩
      cases hEq
  | arrow T1 T2 =>
    simp only [Ty.shape_val_denot, resolve]
    constructor
    · intro h
      rcases h with ⟨_, _, _, _, hres, _, _⟩
      cases hres
    · intro h
      rcases h with ⟨_, _, _, _, hres, _, _⟩
      cases hres
  | poly T1 T2 =>
    simp only [Ty.shape_val_denot, resolve]
    constructor
    · intro h
      rcases h with ⟨_, _, _, _, hres, _, _⟩
      cases hres
    · intro h
      rcases h with ⟨_, _, _, _, hres, _, _⟩
      cases hres
  | cpoly B T =>
    simp only [Ty.shape_val_denot, resolve]
    constructor
    · intro h
      rcases h with ⟨_, _, _, _, hres, _, _⟩
      cases hres
    · intro h
      rcases h with ⟨_, _, _, _, hres, _, _⟩
      cases hres

theorem capt_val_denot_is_transparent {env : TypeEnv s}
  (henv : TypeEnv.is_transparent env)
  (T : Ty .capt s) :
  (Ty.capt_val_denot env T).is_transparent := by
  cases T with
  | capt C S =>
    intro m x v hx ht
    simp only [Ty.capt_val_denot] at ht ⊢
    have ⟨hsv, hwf, hwf_C, hshape⟩ := ht
    split_ands
    · apply Exp.IsSimpleAns.is_var
    · -- Prove: (.var (.free x)).WfInHeap m.heap
      -- A variable is well-formed if it points to something in the heap
      apply Exp.WfInHeap.wf_var
      apply Var.WfInHeap.wf_free
      exact hx
    · -- Prove: C.WfInHeap m.heap
      exact hwf_C
    · -- Prove: shape_val_denot env S (C.denot env m) m (.var (.free x))
      exact shape_val_denot_is_transparent henv S (C.denot env m) hx hshape

theorem exi_val_denot_is_transparent {env : TypeEnv s}
  (henv : TypeEnv.is_transparent env)
  (T : Ty .exi s) :
  (Ty.exi_val_denot env T).is_transparent := by
  cases T with
  | typ T =>
    intro m x v hx ht
    simp only [Ty.exi_val_denot] at ht ⊢
    exact capt_val_denot_is_transparent henv T hx ht
  | exi T =>
    intro m x v hx ht
    simp only [Ty.exi_val_denot] at ht ⊢
    rw [resolve_var_heap_trans (by simpa only [Memory.lookup] using hx)]
    exact ht

theorem ground_denot_is_monotonic {C : CaptureSet {}} :
  (C.ground_denot).is_monotonic_for C := by
  unfold CapDenot.is_monotonic_for
  intro m1 m2 hwf hsub
  induction C with
  | empty =>
    -- Empty set denotes {} at all memories
    rfl
  | union cs1 cs2 ih1 ih2 =>
    -- Union: use IH on both components
    unfold CaptureSet.ground_denot
    cases hwf with
    | wf_union hwf1 hwf2 =>
      rw [ih1 hwf1, ih2 hwf2]
  | var v =>
    cases v with
    | bound x => cases x  -- No bound variables in empty signature
    | free x =>
      -- Free variable: use reachability_of_loc_monotonic
      unfold CaptureSet.ground_denot
      cases hwf with
      | wf_var_free hex =>
        exact (reachability_of_loc_monotonic hsub x hex).symm
  | cvar c => cases c  -- No capture variables in empty signature

theorem capture_set_denot_is_monotonic {C : CaptureSet s} :
  (C.denot ρ).is_monotonic_for (C.subst (Subst.from_TypeEnv ρ)) := by
  unfold CapDenot.is_monotonic_for
  intro m1 m2 hwf hsub
  induction C with
  | empty =>
    -- Empty set denotes {} at all memories
    rfl
  | union C1 C2 ih1 ih2 =>
    -- Union: use IH on both components
    change CaptureSet.WfInHeap
        ((CaptureSet.subst C1 (Subst.from_TypeEnv ρ)) ∪
          CaptureSet.subst C2 (Subst.from_TypeEnv ρ)) m1.heap at hwf
    change
      CaptureSet.ground_denot (CaptureSet.subst C1 (Subst.from_TypeEnv ρ)) m1 ∪
        CaptureSet.ground_denot (CaptureSet.subst C2 (Subst.from_TypeEnv ρ)) m1 =
      CaptureSet.ground_denot (CaptureSet.subst C1 (Subst.from_TypeEnv ρ)) m2 ∪
        CaptureSet.ground_denot (CaptureSet.subst C2 (Subst.from_TypeEnv ρ)) m2
    cases hwf with
    | wf_union hwf1 hwf2 =>
      have e1 : CaptureSet.ground_denot (CaptureSet.subst C1 (Subst.from_TypeEnv ρ)) m1 =
          CaptureSet.ground_denot (CaptureSet.subst C1 (Subst.from_TypeEnv ρ)) m2 := by
        simpa [CaptureSet.denot] using ih1 hwf1
      have e2 : CaptureSet.ground_denot (CaptureSet.subst C2 (Subst.from_TypeEnv ρ)) m1 =
          CaptureSet.ground_denot (CaptureSet.subst C2 (Subst.from_TypeEnv ρ)) m2 := by
        simpa [CaptureSet.denot] using ih2 hwf2
      rw [e1, e2]
  | var v =>
    cases v with
    | bound x =>
      -- Bound variable: after substitution becomes free variable
      change CaptureSet.WfInHeap (CaptureSet.var (.free (ρ.lookup_var x))) m1.heap at hwf
      change reachability_of_loc m1.heap (ρ.lookup_var x) =
          reachability_of_loc m2.heap (ρ.lookup_var x)
      cases hwf with
      | wf_var_free hex =>
        -- hex : m1.heap (ρ.lookup_var x) = some _
        -- Memory.lookup is definitionally equal to heap access
        exact (reachability_of_loc_monotonic hsub (ρ.lookup_var x) hex).symm
    | free x =>
      -- Free variable: stays as free variable
      change CaptureSet.WfInHeap (CaptureSet.var (.free x)) m1.heap at hwf
      change reachability_of_loc m1.heap x = reachability_of_loc m2.heap x
      cases hwf with
      | wf_var_free hex =>
        -- hex : m1.heap x = some _
        -- Memory.lookup is definitionally equal to heap access
        exact (reachability_of_loc_monotonic hsub x hex).symm
  | cvar c =>
    -- Capture variable: after substitution becomes ground capture set
    change CaptureSet.WfInHeap (ρ.lookup_cvar c) m1.heap at hwf
    change CaptureSet.ground_denot (ρ.lookup_cvar c) m1 =
        CaptureSet.ground_denot (ρ.lookup_cvar c) m2
    -- Need: (ρ.lookup_cvar c).ground_denot m1 = (ρ.lookup_cvar c).ground_denot m2
    -- This follows from ground_denot_is_monotonic
    exact ground_denot_is_monotonic hwf hsub

theorem capture_bound_denot_is_monotonic {B : CaptureBound s}
  (hwf : (B.subst (Subst.from_TypeEnv ρ)).WfInHeap m1.heap)
  (hsub : m2.subsumes m1) :
  B.denot ρ m1 = B.denot ρ m2 := by
  cases B with
  | unbound =>
    -- Unbound denotes CapabilitySet.any at all memories
    unfold CaptureBound.denot
    rfl
  | bound cs =>
    -- Bounded case: use capture_set_denot_is_monotonic
    change
      CaptureBound.WfInHeap (.bound (CaptureSet.subst cs (Subst.from_TypeEnv ρ))) m1.heap at hwf
    cases hwf with
    | wf_bound hwf_cs =>
      change CapabilityBound.set (CaptureSet.denot ρ cs m1) =
          CapabilityBound.set (CaptureSet.denot ρ cs m2)
      exact congrArg CapabilityBound.set
        (capture_set_denot_is_monotonic (ρ := ρ) (C := cs) hwf_cs hsub)

mutual

def shape_val_denot_is_monotonic {env : TypeEnv s}
  (henv : env.IsMonotonic)
  (T : Ty .shape s) :
  (Ty.shape_val_denot env T).is_monotonic := by
  intro C
  cases T with
  | top =>
    intro m1 m2 e hmem ht
    simp only [Ty.shape_val_denot] at ht ⊢
    -- ht : e.WfInHeap m1.heap ∧ resolve_reachability m1.heap e ⊆ C
    -- Goal: e.WfInHeap m2.heap ∧ resolve_reachability m2.heap e ⊆ C
    constructor
    · -- Prove: e.WfInHeap m2.heap
      exact Exp.wf_monotonic hmem ht.1
    · -- Prove: resolve_reachability m2.heap e ⊆ C
      -- Use resolve_reachability_monotonic to show they're equal
      have heq := resolve_reachability_monotonic hmem e ht.1
      rw [heq]
      exact ht.2
  | tvar X =>
    intro m1 m2 e hmem ht
    simp only [Ty.shape_val_denot] at ht ⊢
    exact henv.tvar X C hmem ht
  | unit =>
    intro m1 m2 e hmem ht
    simp only [Ty.shape_val_denot] at ht ⊢
    exact resolve_monotonic hmem ht
  | cap =>
    intro m1 m2 e hmem ht
    simp only [Ty.shape_val_denot] at ht ⊢
    have ⟨hwf_e, label, heq, hcap, hmemin⟩ := ht
    constructor
    · -- Prove e.WfInHeap m2.heap
      exact Exp.wf_monotonic hmem hwf_e
    · use label
      constructor
      · exact heq
      · constructor
        · have hsub : m2.heap.subsumes m1.heap := hmem
          obtain ⟨c', hc', hsub_c⟩ := hsub label (Cell.capability .basic) hcap
          -- For basic capability cells, subsumption requires equality
          have hEq : c' = Cell.capability .basic := by
            simpa only [Cell.subsumes] using hsub_c
          subst hEq
          simpa only [Memory.lookup] using hc'
        · exact hmemin
  | bool =>
    intro m1 m2 e hmem ht
    simp only [Ty.shape_val_denot] at ht ⊢
    cases ht with
    | inl htrue =>
      left
      exact resolve_monotonic hmem htrue
    | inr hfalse =>
      right
      exact resolve_monotonic hmem hfalse
  | cell =>
    intro m1 m2 e hmem ht
    simp only [Ty.shape_val_denot] at ht ⊢
    obtain ⟨l, b0, heq, hlookup, hmem_l⟩ := ht
    -- m2.lookup l = some (.capability (.mcell ...))
    have hsub : m2.heap.subsumes m1.heap := hmem
    have hlookup' : m1.heap l = some (Cell.capability (.mcell b0)) := by
      exact hlookup
    obtain ⟨c', hc', hsub_c⟩ := hsub l (Cell.capability (.mcell b0)) hlookup'
    -- For mcell capability cells, subsumption is always True (mcell subsumes mcell)
    cases c'
    case val v =>
      simp only [Cell.subsumes] at hsub_c
      cases hsub_c
    case masked =>
      simp only [Cell.subsumes] at hsub_c
      cases hsub_c
    case capability info =>
      cases info
      case basic =>
        simp only [Cell.subsumes] at hsub_c
        cases hsub_c
      case mcell b' =>
        -- Cell.subsumes says mcell-to-mcell is True
        -- The boolean value b' might differ from b0, which is fine
        refine ⟨l, b', heq, ?_, hmem_l⟩
        simpa only [Memory.lookup] using hc'
  | arrow T1 T2 =>
    intro m1 m2 e hmem ht
    simp only [Ty.shape_val_denot] at ht ⊢
    have ⟨hwf_e, cs, T0, t0, hr, hwf_cs, hR0_sub, hfun⟩ := ht
    constructor
    · -- Prove e.WfInHeap m2.heap
      exact Exp.wf_monotonic hmem hwf_e
    · use cs, T0, t0
      constructor
      · cases e with
        | var x =>
          cases x with
          | free fx =>
            simp only [resolve] at hr ⊢
            split at hr <;> try (cases hr)
            rename_i v heq
            have hsub : m2.heap.subsumes m1.heap := hmem
            obtain ⟨v', hv', hsub_v⟩ := hsub fx (Cell.val v) heq
            -- For value cells, subsumption requires equality
            simp only [Cell.subsumes] at hsub_v
            subst hsub_v
            simp only [hv', hr]
          | bound bx => cases bx
        | abs _ _ _ => simp only [resolve] at hr ⊢; exact hr
        | tabs _ _ _ => cases hr
        | cabs _ _ _ => cases hr
        | pack _ _ => cases hr
        | unit => cases hr
        | unpack _ _ => cases hr
        | app _ _ => cases hr
        | tapp _ _ => cases hr
        | capp _ _ => cases hr
        | letin _ _ => cases hr
        | btrue => cases hr
        | bfalse => cases hr
        | read _ => cases hr
        | write _ _ => cases hr
        | cond _ _ _ => cases hr
      · constructor
        · exact CaptureSet.wf_monotonic hmem hwf_cs
        · constructor
          · -- Prove: expand_captures m2.heap cs ⊆ C
            have heq := expand_captures_monotonic hmem cs hwf_cs
            rw [heq]
            exact hR0_sub
          · intro arg m' hs' harg
            have hs0 := Memory.subsumes_trans hs' hmem
            -- Use convert with expand_captures monotonicity
            have heq' := expand_captures_monotonic hmem cs hwf_cs
            convert hfun arg m' hs0 harg using 2
  | poly T1 T2 =>
    intro m1 m2 e hmem ht
    simp only [Ty.shape_val_denot] at ht ⊢
    have ⟨hwf_e, cs, S0, t0, hr, hwf_cs, hR0_sub, hfun⟩ := ht
    constructor
    · -- Prove e.WfInHeap m2.heap
      exact Exp.wf_monotonic hmem hwf_e
    · use cs, S0, t0
      constructor
      · cases e with
        | var x =>
          cases x with
          | free fx =>
            simp only [resolve] at hr ⊢
            split at hr <;> try (cases hr)
            rename_i v heq
            have hsub : m2.heap.subsumes m1.heap := hmem
            obtain ⟨v', hv', hsub_v⟩ := hsub fx (Cell.val v) heq
            -- For value cells, subsumption requires equality
            simp only [Cell.subsumes] at hsub_v
            subst hsub_v
            simp only [hv', hr]
          | bound bx => cases bx
        | tabs _ _ _ => simp only [resolve] at hr ⊢; exact hr
        | abs _ _ _ => cases hr
        | cabs _ _ _ => cases hr
        | pack _ _ => cases hr
        | unit => cases hr
        | unpack _ _ => cases hr
        | app _ _ => cases hr
        | tapp _ _ => cases hr
        | capp _ _ => cases hr
        | letin _ _ => cases hr
        | btrue => cases hr
        | bfalse => cases hr
        | read _ => cases hr
        | write _ _ => cases hr
        | cond _ _ _ => cases hr
      · constructor
        · exact CaptureSet.wf_monotonic hmem hwf_cs
        · constructor
          · -- Prove: expand_captures m2.heap cs ⊆ C
            have heq := expand_captures_monotonic hmem cs hwf_cs
            rw [heq]
            exact hR0_sub
          · intro m' denot msub hdenot_proper himply
            have henv' : (env.extend_tvar denot).IsMonotonic := by
              constructor
              · intro X
                cases X with
                | here =>
                  change denot.is_monotonic
                  intro C
                  exact (hdenot_proper.2.2.2.2 C).1
                | there X' =>
                  change (env.lookup_tvar X').is_monotonic
                  exact henv.tvar X'
            -- Use convert with expand_captures monotonicity
            have heq' := expand_captures_monotonic hmem cs hwf_cs
            convert hfun m' denot (Memory.subsumes_trans msub hmem) hdenot_proper himply using 2
  | cpoly B T =>
    intro m1 m2 e hmem ht
    simp only [Ty.shape_val_denot] at ht ⊢
    have ⟨hwf_e, cs, B0, t0, hr, hwf_cs, hR0_sub, hfun⟩ := ht
    constructor
    · -- Prove e.WfInHeap m2.heap
      exact Exp.wf_monotonic hmem hwf_e
    · use cs, B0, t0
      constructor
      · cases e with
        | var x =>
          cases x with
          | free fx =>
            simp only [resolve] at hr ⊢
            split at hr <;> try (cases hr)
            rename_i v heq
            have hsub : m2.heap.subsumes m1.heap := hmem
            obtain ⟨v', hv', hsub_v⟩ := hsub fx (Cell.val v) heq
            -- For value cells, subsumption requires equality
            simp only [Cell.subsumes] at hsub_v
            subst hsub_v
            simp only [hv', hr]
          | bound bx => cases bx
        | cabs _ _ _ => simp only [resolve] at hr ⊢; exact hr
        | abs _ _ _ => cases hr
        | tabs _ _ _ => cases hr
        | pack _ _ => cases hr
        | unit => cases hr
        | unpack _ _ => cases hr
        | app _ _ => cases hr
        | tapp _ _ => cases hr
        | capp _ _ => cases hr
        | letin _ _ => cases hr
        | btrue => cases hr
        | bfalse => cases hr
        | read _ => cases hr
        | write _ _ => cases hr
        | cond _ _ _ => cases hr
      · constructor
        · exact CaptureSet.wf_monotonic hmem hwf_cs
        · constructor
          · -- Prove: expand_captures m2.heap cs ⊆ C
            have heq := expand_captures_monotonic hmem cs hwf_cs
            rw [heq]
            exact hR0_sub
          · intro m' CS hwf msub hA0
            -- Use convert with expand_captures monotonicity
            have heq' := expand_captures_monotonic hmem cs hwf_cs
            convert hfun m' CS hwf (Memory.subsumes_trans msub hmem) hA0 using 2

def capt_val_denot_is_monotonic {env : TypeEnv s}
  (henv : env.IsMonotonic)
  (T : Ty .capt s) :
  (Ty.capt_val_denot env T).is_monotonic := by
  cases T with
  | capt C S =>
    intro m1 m2 e hmem ht
    simp only [Ty.capt_val_denot] at ht ⊢
    have ⟨hsv, hwf, hwf_C, hshape⟩ := ht
    split_ands
    · exact hsv
    · -- Prove: e.WfInHeap m2.heap
      exact Exp.wf_monotonic hmem hwf
    · -- Prove: C.WfInHeap m2.heap
      exact CaptureSet.wf_monotonic hmem hwf_C
    · -- Prove: shape_val_denot env S (C.denot env m2) m2 e
      have h := capture_set_denot_is_monotonic hwf_C hmem
      rw [<-h]
      exact shape_val_denot_is_monotonic henv S (C.denot env m1) hmem hshape

def exi_val_denot_is_monotonic {env : TypeEnv s}
  (henv : env.IsMonotonic)
  (T : Ty .exi s) :
  (Ty.exi_val_denot env T).is_monotonic := by
  cases T with
  | typ T =>
    intro m1 m2 e hmem ht
    simp only [Ty.exi_val_denot] at ht ⊢
    exact capt_val_denot_is_monotonic henv T hmem ht
  | exi T =>
    intro m1 m2 e hmem ht
    simp only [Ty.exi_val_denot] at ht ⊢
    -- ht: match (resolve m1.heap e) with some (pack CS x) => ... | _ => False
    -- Goal: match (resolve m2.heap e) with some (pack CS x) => ... | _ => False
    cases hresolve1 : resolve m1.heap e
    · -- resolve m1.heap e = none, so ht is False
      simp [hresolve1] at ht
    · -- resolve m1.heap e = some e'
      rename_i e'
      cases e'
      case pack =>
        -- resolve m1.heap e = some (pack CS y)
        rename_i CS y
        simp only [hresolve1] at ht
        -- ht now says: CS.WfInHeap m1.heap ∧ Ty.capt_val_denot (env.extend_cvar CS) T m1 (var y)
        obtain ⟨hwf_CS_m1, ht_body⟩ := ht
        -- Use resolve_monotonic to show resolve m2.heap e = some (pack CS y)
        have hresolve2 : resolve m2.heap e = some (Exp.pack CS y) := by
          apply resolve_monotonic hmem hresolve1
        rw [hresolve2]
        -- Now need to show:
        -- CS.WfInHeap m2.heap ∧ Ty.capt_val_denot (env.extend_cvar CS) T m2 (var y)
        constructor
        · -- Well-formedness is monotonic
          exact CaptureSet.wf_monotonic hmem hwf_CS_m1
        · -- Use monotonicity of capt_val_denot
          have henv' : (env.extend_cvar CS).IsMonotonic := by
            constructor
            · intro X
              cases X with
              | there X' =>
                change (env.lookup_tvar X').is_monotonic
                exact henv.tvar X'
          exact capt_val_denot_is_monotonic henv' T hmem ht_body
      all_goals {
        -- resolve returned non-pack, so ht is False
        simp only [hresolve1] at ht
      }

def capt_val_denot_is_bool_independent {env : TypeEnv s}
  (henv : TypeEnv.is_bool_independent env)
  (T : Ty .capt s) :
  (Ty.capt_val_denot env T).is_bool_independent := by
  cases T with
  | capt C S =>
    intro m
    simp only [Ty.capt_val_denot]
    constructor
    · intro ⟨hsimple, hwf, hwf_C, hshape⟩
      constructor
      · apply Exp.IsSimpleAns.is_simple_val
        apply Exp.IsSimpleVal.bfalse
      · constructor
        · apply Exp.WfInHeap.wf_bfalse
        · constructor
          · exact hwf_C
          · exact (shape_val_denot_is_bool_independent henv S (C.denot env m)).mp hshape
    · intro ⟨hsimple, hwf, hwf_C, hshape⟩
      constructor
      · apply Exp.IsSimpleAns.is_simple_val
        apply Exp.IsSimpleVal.btrue
      · constructor
        · apply Exp.WfInHeap.wf_btrue
        · constructor
          · exact hwf_C
          · exact (shape_val_denot_is_bool_independent henv S (C.denot env m)).mpr hshape

def exi_val_denot_is_bool_independent {env : TypeEnv s}
  (henv : TypeEnv.is_bool_independent env)
  (T : Ty .exi s) :
  (Ty.exi_val_denot env T).is_bool_independent := by
  cases T with
  | typ T =>
    intro m
    simpa only [Ty.exi_val_denot] using capt_val_denot_is_bool_independent henv T (m := m)
  | exi T =>
    intro m
    simp only [Ty.exi_val_denot]
    -- For btrue and bfalse, resolve returns some btrue/bfalse, which are not pack
    -- So both sides evaluate to False
    simp [resolve]

def capt_exp_denot_is_monotonic {env : TypeEnv s}
  (henv_mono : env.IsMonotonic)
  (henv_bool : env.is_bool_independent)
  (T : Ty .capt s) :
  ∀ {C : CapabilitySet} {m1 m2 : Memory} {e : Exp {}},
    Exp.WfInHeap e m1.heap ->
    m2.subsumes m1 ->
    (Ty.capt_exp_denot env T) C m1 e ->
    (Ty.capt_exp_denot env T) C m2 e := by
  intro C m1 m2 e hwf hmem ht
  simp only [Ty.capt_exp_denot] at ht ⊢
  apply eval_monotonic
  · apply Denot.as_mpost_is_monotonic
    exact capt_val_denot_is_monotonic henv_mono T
  · apply Denot.as_mpost_is_bool_independent
    exact capt_val_denot_is_bool_independent henv_bool T
  · exact hmem
  · exact hwf
  · exact ht

def exi_exp_denot_is_monotonic {env : TypeEnv s}
  (henv_mono : env.IsMonotonic)
  (henv_bool : env.is_bool_independent)
  (T : Ty .exi s) :
  ∀ {C : CapabilitySet} {m1 m2 : Memory} {e : Exp {}},
    Exp.WfInHeap e m1.heap ->
    m2.subsumes m1 ->
    (Ty.exi_exp_denot env T) C m1 e ->
    (Ty.exi_exp_denot env T) C m2 e := by
  intro C m1 m2 e hwf hmem ht
  simp only [Ty.exi_exp_denot] at ht ⊢
  apply eval_monotonic
  · apply Denot.as_mpost_is_monotonic
    exact exi_val_denot_is_monotonic henv_mono T
  · apply Denot.as_mpost_is_bool_independent
    exact exi_val_denot_is_bool_independent henv_bool T
  · exact hmem
  · exact hwf
  · exact ht

end

theorem env_typing_monotonic
  (ht : EnvTyping Γ env mem1)
  (hmem : mem2.subsumes mem1) :
  EnvTyping Γ env mem2 := by
  induction Γ with
  | empty =>
    cases env with
    | empty => trivial
  | push Γ k ih =>
    cases env with
    | extend env' info =>
      cases k with
      | var T =>
        cases info with
        | var n =>
          -- Unfold EnvTyping to get the conjunction
          unfold EnvTyping at ht ⊢
          have ⟨hval, ht'⟩ := ht
          constructor
          · -- Prove: ⟦T⟧_[env', φ] mem2 (.var (.free n))
            have henv := typed_env_is_monotonic ht'
            exact capt_val_denot_is_monotonic henv T hmem hval
          · -- Prove: EnvTyping Γ env' mem2
            exact ih ht'
      | tvar S =>
        cases info with
        | tvar d =>
          change d.is_proper ∧ d.ImplyAfter mem1 ⟦S⟧_[env'] ∧ EnvTyping Γ env' mem1 at ht
          change d.is_proper ∧ d.ImplyAfter mem2 ⟦S⟧_[env'] ∧ EnvTyping Γ env' mem2
          have hproper := ht.1
          have himply := ht.2.1
          have ht' := ht.2.2
          constructor
          · exact hproper
          · constructor
            · intro C
              apply Denot.imply_after_subsumes (himply C) hmem
            · exact ih ht'
      | cvar B =>
        cases info with
        | cvar cs =>
          change cs.WfInHeap mem1.heap ∧
              (B.subst (Subst.from_TypeEnv env')).WfInHeap mem1.heap ∧
              (cs.ground_denot mem1).BoundedBy (⟦B⟧_[env'] mem1) ∧
              EnvTyping Γ env' mem1 at ht
          change cs.WfInHeap mem2.heap ∧
              (B.subst (Subst.from_TypeEnv env')).WfInHeap mem2.heap ∧
              (cs.ground_denot mem2).BoundedBy (⟦B⟧_[env'] mem2) ∧
              EnvTyping Γ env' mem2
          have hwf := ht.1
          have hwf_bound := ht.2.1
          have hsub := ht.2.2.1
          have ht' := ht.2.2.2
          constructor
          · -- Prove: cs.WfInHeap mem2.heap
            exact CaptureSet.wf_monotonic hmem hwf
          · constructor
            · -- Prove: (B.subst (Subst.from_TypeEnv env')).WfInHeap mem2.heap
              exact CaptureBound.wf_monotonic hmem hwf_bound
            · constructor
              · -- Need: cs.ground_denot mem2 ⊆ ⟦B⟧_[env'] mem2
                -- Have: cs.ground_denot mem1 ⊆ ⟦B⟧_[env'] mem1
                -- Get cs.ground_denot mem1 = cs.ground_denot mem2
                have h_denot_eq := ground_denot_is_monotonic hwf hmem
                -- Get ⟦B⟧_[env'] mem1 = ⟦B⟧_[env'] mem2
                have h_bound_eq : B.denot env' mem1 = B.denot env' mem2 :=
                  capture_bound_denot_is_monotonic hwf_bound hmem
                -- Combine the equalities
                have : (cs.ground_denot mem2).BoundedBy (⟦B⟧_[env'] mem2) := by
                  have h_bound_eq' : ⟦B⟧_[env'] mem2 = B.denot env' mem1 := by
                    change B.denot env' mem2 = B.denot env' mem1
                    exact h_bound_eq.symm
                  rw [← h_denot_eq, h_bound_eq']
                  exact hsub
                exact this
              · exact ih ht'

/-- Semantic subcapturing. -/
def SemSubcapt (Γ : Ctx s) (C1 C2 : CaptureSet s) : Prop :=
  ∀ env m,
    EnvTyping Γ env m ->
    C1.denot env m ⊆ C2.denot env m

def SemSubtyp {k : TySort} (Γ : Ctx s) (T1 T2 : Ty k s) : Prop :=
  match k with
  | .shape =>
    ∀ env H, EnvTyping Γ env H ->
      (Ty.shape_val_denot env T1).ImplyAfter H (Ty.shape_val_denot env T2)
  | .capt =>
    ∀ env H, EnvTyping Γ env H ->
      (Ty.capt_val_denot env T1).ImplyAfter H (Ty.capt_val_denot env T2)
  | .exi =>
    ∀ env H, EnvTyping Γ env H ->
      (Ty.exi_val_denot env T1).ImplyAfter H (Ty.exi_val_denot env T2)

theorem shape_val_denot_is_reachability_safe {env : TypeEnv s}
  (hts : env.is_reachability_safe)
  (T : Ty .shape s) :
  (Ty.shape_val_denot env T).is_reachability_safe := by
  intro R m e hdenot
  cases T with
  | top =>
    -- For .top, the denotation already includes resolve_reachability m.heap e ⊆ R
    simp only [Ty.shape_val_denot] at hdenot
    exact hdenot.2
  | tvar X =>
    -- For .tvar, use the hypothesis that env is reachability safe
    exact hts X R m e (by simpa only [Ty.shape_val_denot] using hdenot)
  | bool =>
    have hdenot' :
        resolve m.heap e = some Exp.btrue ∨ resolve m.heap e = some Exp.bfalse := by
      simpa only [Ty.shape_val_denot] using hdenot
    cases e with
    | btrue =>
      -- Bool literals have empty reachability
      change ({} : CapabilitySet) ⊆ R
      exact CapabilitySet.Subset.empty
    | bfalse =>
      change ({} : CapabilitySet) ⊆ R
      exact CapabilitySet.Subset.empty
    | var x =>
      cases x with
      | bound bx => cases bx
      | free fx =>
        change reachability_of_loc m.heap fx ⊆ R
        cases hcell : m.heap fx with
        | none =>
          cases hdenot' with
          | inl hb =>
            have hbad : (none : Option (Exp {})) = some Exp.btrue := by
              simpa only [resolve, hcell] using hb
            cases hbad
          | inr hb =>
            have hbad : (none : Option (Exp {})) = some Exp.bfalse := by
              simpa only [resolve, hcell] using hb
            cases hbad
        | some cell =>
          cases cell with
          | capability =>
            cases hdenot' with
            | inl hb =>
              have hbad : (none : Option (Exp {})) = some Exp.btrue := by
                simpa only [resolve, hcell] using hb
              cases hbad
            | inr hb =>
              have hbad : (none : Option (Exp {})) = some Exp.bfalse := by
                simpa only [resolve, hcell] using hb
              cases hbad
          | masked =>
            cases hdenot' with
            | inl hb =>
              have hbad : (none : Option (Exp {})) = some Exp.btrue := by
                simpa only [resolve, hcell] using hb
              cases hbad
            | inr hb =>
              have hbad : (none : Option (Exp {})) = some Exp.bfalse := by
                simpa only [resolve, hcell] using hb
              cases hbad
          | val hv =>
            cases hv with
            | mk vexp hv_simple hreach_val =>
              have hreach :=
                Memory.reachability_invariant m fx ⟨vexp, hv_simple, hreach_val⟩
                  (by simp [hcell])
              have hresolve :
                  some vexp = some Exp.btrue ∨ some vexp = some Exp.bfalse := by
                cases hdenot' with
                | inl hb =>
                  exact Or.inl (by simpa only [resolve, hcell] using hb)
                | inr hb =>
                  exact Or.inr (by simpa only [resolve, hcell] using hb)
              cases hv_simple with
              | abs =>
                cases hresolve with
                | inl hbad => cases hbad
                | inr hbad => cases hbad
              | tabs =>
                cases hresolve with
                | inl hbad => cases hbad
                | inr hbad => cases hbad
              | cabs =>
                cases hresolve with
                | inl hbad => cases hbad
                | inr hbad => cases hbad
              | unit =>
                cases hresolve with
                | inl hbad => cases hbad
                | inr hbad => cases hbad
              | btrue =>
                have hreach_empty : hreach_val = {} := by
                  simpa [compute_reachability] using hreach
                rw [reachability_of_loc, hcell, hreach_empty]
                exact CapabilitySet.Subset.empty
              | bfalse =>
                have hreach_empty : hreach_val = {} := by
                  simpa [compute_reachability] using hreach
                rw [reachability_of_loc, hcell, hreach_empty]
                exact CapabilitySet.Subset.empty
    | _ =>
      simp [Ty.shape_val_denot, resolve] at hdenot
  | cell =>
    simp only [Ty.shape_val_denot] at hdenot
    obtain ⟨l, b0, heq, hlookup, hmem⟩ := hdenot
    -- e is a variable pointing to an mcell capability
    rw [heq]
    change reachability_of_loc m.heap l ⊆ R
    -- reachability_of_loc m.heap l = {l} for mcell capabilities
    have hlookup' : m.heap l = some (Cell.capability (.mcell b0)) := by
      change m.heap l = some (Cell.capability (.mcell b0)) at hlookup
      exact hlookup
    rw [reachability_of_loc, hlookup']
    -- Goal: {l} ⊆ R, which follows from l ∈ R
    exact CapabilitySet.mem_imp_singleton_subset hmem
  | unit =>
    have hdenot' : resolve m.heap e = some .unit := by
      simpa only [Ty.shape_val_denot] using hdenot
    cases e with
    | unit =>
      change ({} : CapabilitySet) ⊆ R
      exact CapabilitySet.Subset.empty
    | var x =>
      cases x with
      | free fx =>
        change reachability_of_loc m.heap fx ⊆ R
        cases hfx : m.heap fx with
        | none =>
          have hbad : (none : Option (Exp {})) = some .unit := by
            simpa only [resolve, hfx] using hdenot'
          cases hbad
        | some cell =>
          cases cell with
          | capability =>
            have hbad : (none : Option (Exp {})) = some .unit := by
              simpa only [resolve, hfx] using hdenot'
            cases hbad
          | masked =>
            have hbad : (none : Option (Exp {})) = some .unit := by
              simpa only [resolve, hfx] using hdenot'
            cases hbad
          | val v =>
            cases v with
            | mk vexp hv_simple hreach_val =>
              have hresolve : some vexp = some .unit := by
                simpa only [resolve, hfx] using hdenot'
              have hreach :=
                Memory.reachability_invariant m fx ⟨vexp, hv_simple, hreach_val⟩
                  (by simp [hfx])
              cases hv_simple with
              | abs =>
                cases hresolve
              | tabs =>
                cases hresolve
              | cabs =>
                cases hresolve
              | unit =>
                have hreach_empty : hreach_val = {} := by
                  simpa [compute_reachability] using hreach
                rw [reachability_of_loc, hfx, hreach_empty]
                exact CapabilitySet.Subset.empty
              | btrue =>
                cases hresolve
              | bfalse =>
                cases hresolve
      | bound bx => cases bx
    | _ =>
      cases hdenot'
  | cap =>
    have hdenot' :
        e.WfInHeap m.heap ∧
          ∃ label : Nat,
            e = .var (.free label) ∧
              m.lookup label = some (.capability .basic) ∧
              label ∈ R := by
      simpa only [Ty.shape_val_denot] using hdenot
    have ⟨hwf_e, label, heq, hcap, hmem⟩ := hdenot'
    -- hdenot says: e = .var (.free label) ∧ label ∈ R
    rw [heq]
    change reachability_of_loc m.heap label ⊆ R
    -- Need: reachability_of_loc m.heap label ⊆ R
    -- From hcap: m.lookup label = some (Cell.capability .basic)
    -- So: reachability_of_loc m.heap label = {label}
    have hcap' : m.heap label = some (Cell.capability .basic) := by
      change m.heap label = some (Cell.capability .basic) at hcap
      exact hcap
    rw [reachability_of_loc, hcap']
    -- Goal: {label} ⊆ R, which follows from label ∈ R
    exact CapabilitySet.mem_imp_singleton_subset hmem
  | arrow T1 T2 =>
    have hdenot' :
        e.WfInHeap m.heap ∧
          ∃ cs T0 t0,
            resolve m.heap e = some (.abs cs T0 t0) ∧
            cs.WfInHeap m.heap ∧
            let R0 := expand_captures m.heap cs
            R0 ⊆ R ∧
              ∀ (arg : Nat) (m' : Memory),
                m'.subsumes m ->
                Ty.capt_val_denot env T1 m' (.var (.free arg)) ->
                Ty.exi_exp_denot
                  (env.extend_var arg)
                  T2 R0 m' (t0.subst (Subst.openVar (.free arg))) := by
      simpa only [Ty.shape_val_denot] using hdenot
    have ⟨hwf_e, cs, T0, t0, hres, hwf_cs, hR0_sub, _⟩ := hdenot'
    cases e with
    | abs cs' T0' t0' =>
      change expand_captures m.heap cs' ⊆ R
      have hres' : some (Exp.abs cs' T0' t0') = some (Exp.abs cs T0 t0) := by
        simpa only [resolve] using hres
      cases hres'
      exact hR0_sub
    | var x =>
      cases x with
      | free fx =>
        change reachability_of_loc m.heap fx ⊆ R
        cases hfx : m.heap fx with
        | none =>
          have hbad : (none : Option (Exp {})) = some (Exp.abs cs T0 t0) := by
            simpa only [resolve, hfx] using hres
          cases hbad
        | some cell =>
          cases cell with
          | capability =>
            have hbad : (none : Option (Exp {})) = some (Exp.abs cs T0 t0) := by
              simpa only [resolve, hfx] using hres
            cases hbad
          | masked =>
            have hbad : (none : Option (Exp {})) = some (Exp.abs cs T0 t0) := by
              simpa only [resolve, hfx] using hres
            cases hbad
          | val v =>
            have hres' : some v.unwrap = some (Exp.abs cs T0 t0) := by
              simpa only [resolve, hfx] using hres
            have hv_heap : m.heap fx = some (Cell.val v) := hfx
            rw [reachability_of_loc_eq_resolve_reachability m fx v hv_heap]
            injection hres' with hunwrap
            rw [hunwrap]
            change expand_captures m.heap cs ⊆ R
            exact hR0_sub
      | bound bx => cases bx
    | _ => cases hres
  | poly T1 T2 =>
    have hdenot' :
        e.WfInHeap m.heap ∧
          ∃ cs S0 t0,
            resolve m.heap e = some (.tabs cs S0 t0) ∧
            cs.WfInHeap m.heap ∧
            let R0 := expand_captures m.heap cs
            R0 ⊆ R ∧
              ∀ (m' : Memory) (denot : PreDenot),
                m'.subsumes m ->
                denot.is_proper ->
                denot.ImplyAfter m' (Ty.shape_val_denot env T1) ->
                Ty.exi_exp_denot
                  (env.extend_tvar denot)
                  T2 R0 m' (t0.subst (Subst.openTVar .top)) := by
      simpa only [Ty.shape_val_denot] using hdenot
    have ⟨hwf_e, cs, S0, t0, hres, hwf_cs, hR0_sub, _⟩ := hdenot'
    cases e with
    | tabs cs' S0' t0' =>
      change expand_captures m.heap cs' ⊆ R
      have hres' : some (Exp.tabs cs' S0' t0') = some (Exp.tabs cs S0 t0) := by
        simpa only [resolve] using hres
      cases hres'
      exact hR0_sub
    | var x =>
      cases x with
      | free fx =>
        change reachability_of_loc m.heap fx ⊆ R
        cases hfx : m.heap fx with
        | none =>
          have hbad : (none : Option (Exp {})) = some (Exp.tabs cs S0 t0) := by
            simpa only [resolve, hfx] using hres
          cases hbad
        | some cell =>
          cases cell with
          | capability =>
            have hbad : (none : Option (Exp {})) = some (Exp.tabs cs S0 t0) := by
              simpa only [resolve, hfx] using hres
            cases hbad
          | masked =>
            have hbad : (none : Option (Exp {})) = some (Exp.tabs cs S0 t0) := by
              simpa only [resolve, hfx] using hres
            cases hbad
          | val v =>
            have hres' : some v.unwrap = some (Exp.tabs cs S0 t0) := by
              simpa only [resolve, hfx] using hres
            have hv_heap : m.heap fx = some (Cell.val v) := hfx
            rw [reachability_of_loc_eq_resolve_reachability m fx v hv_heap]
            injection hres' with hunwrap
            rw [hunwrap]
            change expand_captures m.heap cs ⊆ R
            exact hR0_sub
      | bound bx => cases bx
    | _ => cases hres
  | cpoly B T =>
    have hdenot' :
        e.WfInHeap m.heap ∧
          ∃ cs B0 t0,
            resolve m.heap e = some (.cabs cs B0 t0) ∧
            cs.WfInHeap m.heap ∧
            let R0 := expand_captures m.heap cs
            R0 ⊆ R ∧
              ∀ (m' : Memory) (CS : CaptureSet {}),
                CS.WfInHeap m'.heap ->
                let A0 := CS.denot TypeEnv.empty
                m'.subsumes m ->
                (A0 m').BoundedBy (B.denot env m') ->
                Ty.exi_exp_denot
                  (env.extend_cvar CS)
                  T R0 m' (t0.subst (Subst.openCVar CS)) := by
      simpa only [Ty.shape_val_denot] using hdenot
    have ⟨hwf_e, cs, B0, t0, hres, hwf_cs, hR0_sub, _⟩ := hdenot'
    cases e with
    | cabs cs' B0' t0' =>
      change expand_captures m.heap cs' ⊆ R
      have hres' : some (Exp.cabs cs' B0' t0') = some (Exp.cabs cs B0 t0) := by
        simpa only [resolve] using hres
      cases hres'
      exact hR0_sub
    | var x =>
      cases x with
      | free fx =>
        change reachability_of_loc m.heap fx ⊆ R
        cases hfx : m.heap fx with
        | none =>
          have hbad : (none : Option (Exp {})) = some (Exp.cabs cs B0 t0) := by
            simpa only [resolve, hfx] using hres
          cases hbad
        | some cell =>
          cases cell with
          | capability =>
            have hbad : (none : Option (Exp {})) = some (Exp.cabs cs B0 t0) := by
              simpa only [resolve, hfx] using hres
            cases hbad
          | masked =>
            have hbad : (none : Option (Exp {})) = some (Exp.cabs cs B0 t0) := by
              simpa only [resolve, hfx] using hres
            cases hbad
          | val v =>
            have hres' : some v.unwrap = some (Exp.cabs cs B0 t0) := by
              simpa only [resolve, hfx] using hres
            have hv_heap : m.heap fx = some (Cell.val v) := hfx
            rw [reachability_of_loc_eq_resolve_reachability m fx v hv_heap]
            injection hres' with hunwrap
            rw [hunwrap]
            change expand_captures m.heap cs ⊆ R
            exact hR0_sub
      | bound bx => cases bx
    | _ => cases hres

theorem shape_val_denot_is_reachability_monotonic {env : TypeEnv s}
  (hts : env.is_reachability_monotonic)
  (T : Ty .shape s) :
  (Ty.shape_val_denot env T).is_reachability_monotonic := by
  intro R1 R2 hsub m e hdenot
  cases T with
  | top =>
    have hdenot' : e.WfInHeap m.heap ∧ resolve_reachability m.heap e ⊆ R1 := by
      simpa only [Ty.shape_val_denot] using hdenot
    have hgoal : e.WfInHeap m.heap ∧ resolve_reachability m.heap e ⊆ R2 := by
      constructor
      · exact hdenot'.1
      · exact CapabilitySet.Subset.trans hdenot'.2 hsub
    simpa only [Ty.shape_val_denot] using hgoal
  | tvar X =>
    simpa only [Ty.shape_val_denot] using
      hts X R1 R2 hsub m e (by simpa only [Ty.shape_val_denot] using hdenot)
  | bool =>
    simpa only [Ty.shape_val_denot] using hdenot
  | cell =>
    simp only [Ty.shape_val_denot] at hdenot ⊢
    obtain ⟨l, b0, heq, hlookup, hmem⟩ := hdenot
    use l, b0
    exact ⟨heq, hlookup, CapabilitySet.subset_preserves_mem hsub hmem⟩
  | unit =>
    simpa only [Ty.shape_val_denot] using hdenot
  | cap =>
    have hdenot' :
        e.WfInHeap m.heap ∧
          ∃ label : Nat,
            e = .var (.free label) ∧
              m.lookup label = some (.capability .basic) ∧
              label ∈ R1 := by
      simpa only [Ty.shape_val_denot] using hdenot
    have ⟨hwf_e, label, heq, hcap, hmem⟩ := hdenot'
    have hgoal :
        e.WfInHeap m.heap ∧
          ∃ label : Nat,
            e = .var (.free label) ∧
              m.lookup label = some (.capability .basic) ∧
              label ∈ R2 := by
      constructor
      · exact hwf_e
      · exact ⟨label, heq, hcap, CapabilitySet.subset_preserves_mem hsub hmem⟩
    simpa only [Ty.shape_val_denot] using hgoal
  | arrow T1 T2 =>
    have hdenot' :
        e.WfInHeap m.heap ∧
          ∃ cs T0 t0,
            resolve m.heap e = some (.abs cs T0 t0) ∧
            cs.WfInHeap m.heap ∧
            let R0 := expand_captures m.heap cs
            R0 ⊆ R1 ∧
              ∀ (arg : Nat) (m' : Memory),
                m'.subsumes m ->
                Ty.capt_val_denot env T1 m' (.var (.free arg)) ->
                Ty.exi_exp_denot
                  (env.extend_var arg)
                  T2 R0 m' (t0.subst (Subst.openVar (.free arg))) := by
      simpa only [Ty.shape_val_denot] using hdenot
    have ⟨hwf_e, cs, T0, t0, hres, hwf_cs, hR0_R1, hfun⟩ := hdenot'
    have hgoal :
        e.WfInHeap m.heap ∧
          ∃ cs T0 t0,
            resolve m.heap e = some (.abs cs T0 t0) ∧
            cs.WfInHeap m.heap ∧
            let R0 := expand_captures m.heap cs
            R0 ⊆ R2 ∧
              ∀ (arg : Nat) (m' : Memory),
                m'.subsumes m ->
                Ty.capt_val_denot env T1 m' (.var (.free arg)) ->
                Ty.exi_exp_denot
                  (env.extend_var arg)
                  T2 R0 m' (t0.subst (Subst.openVar (.free arg))) := by
      constructor
      · exact hwf_e
      · refine ⟨cs, T0, t0, hres, hwf_cs, ?_⟩
        exact ⟨CapabilitySet.Subset.trans hR0_R1 hsub, hfun⟩
    simpa only [Ty.shape_val_denot] using hgoal
  | poly T1 T2 =>
    have hdenot' :
        e.WfInHeap m.heap ∧
          ∃ cs T0 t0,
            resolve m.heap e = some (.tabs cs T0 t0) ∧
            cs.WfInHeap m.heap ∧
            let R0 := expand_captures m.heap cs
            R0 ⊆ R1 ∧
              ∀ (m' : Memory) (denot : PreDenot),
                m'.subsumes m ->
                denot.is_proper ->
                denot.ImplyAfter m' (Ty.shape_val_denot env T1) ->
                Ty.exi_exp_denot
                  (env.extend_tvar denot)
                  T2 R0 m' (t0.subst (Subst.openTVar .top)) := by
      simpa only [Ty.shape_val_denot] using hdenot
    have ⟨hwf_e, cs, T0, t0, hres, hwf_cs, hR0_R1, hfun⟩ := hdenot'
    have hgoal :
        e.WfInHeap m.heap ∧
          ∃ cs T0 t0,
            resolve m.heap e = some (.tabs cs T0 t0) ∧
            cs.WfInHeap m.heap ∧
            let R0 := expand_captures m.heap cs
            R0 ⊆ R2 ∧
              ∀ (m' : Memory) (denot : PreDenot),
                m'.subsumes m ->
                denot.is_proper ->
                denot.ImplyAfter m' (Ty.shape_val_denot env T1) ->
                Ty.exi_exp_denot
                  (env.extend_tvar denot)
                  T2 R0 m' (t0.subst (Subst.openTVar .top)) := by
      constructor
      · exact hwf_e
      · refine ⟨cs, T0, t0, hres, hwf_cs, ?_⟩
        exact ⟨CapabilitySet.Subset.trans hR0_R1 hsub, hfun⟩
    simpa only [Ty.shape_val_denot] using hgoal
  | cpoly B T =>
    have hdenot' :
        e.WfInHeap m.heap ∧
          ∃ cs B0 t0,
            resolve m.heap e = some (.cabs cs B0 t0) ∧
            cs.WfInHeap m.heap ∧
            let R0 := expand_captures m.heap cs
            R0 ⊆ R1 ∧
              ∀ (m' : Memory) (CS : CaptureSet {}),
                CS.WfInHeap m'.heap ->
                let A0 := CS.denot TypeEnv.empty
                m'.subsumes m ->
                (A0 m').BoundedBy (B.denot env m') ->
                Ty.exi_exp_denot
                  (env.extend_cvar CS)
                  T R0 m' (t0.subst (Subst.openCVar CS)) := by
      simpa only [Ty.shape_val_denot] using hdenot
    have ⟨hwf_e, cs, B0, t0, hres, hwf_cs, hR0_R1, hfun⟩ := hdenot'
    have hgoal :
        e.WfInHeap m.heap ∧
          ∃ cs B0 t0,
            resolve m.heap e = some (.cabs cs B0 t0) ∧
            cs.WfInHeap m.heap ∧
            let R0 := expand_captures m.heap cs
            R0 ⊆ R2 ∧
              ∀ (m' : Memory) (CS : CaptureSet {}),
                CS.WfInHeap m'.heap ->
                let A0 := CS.denot TypeEnv.empty
                m'.subsumes m ->
                (A0 m').BoundedBy (B.denot env m') ->
                Ty.exi_exp_denot
                  (env.extend_cvar CS)
                  T R0 m' (t0.subst (Subst.openCVar CS)) := by
      constructor
      · exact hwf_e
      · refine ⟨cs, B0, t0, hres, hwf_cs, ?_⟩
        exact ⟨CapabilitySet.Subset.trans hR0_R1 hsub, hfun⟩
    simpa only [Ty.shape_val_denot] using hgoal

/-- If the type environment is well-typed, then the denotation of any shape type is proper.
    A PreDenot is proper if it is reachability-safe, monotonic, and transparent. This theorem
    combines the reachability safety, monotonicity, and transparency results for shape type
    denotations. -/
lemma wf_from_resolve_unit
  {m : Memory} {e : Exp {}}
  (hresolve : resolve m.heap e = some .unit) :
  e.WfInHeap m.heap := by
  cases e with
  | var x =>
    cases x with
    | free fx =>
      cases hfx : m.heap fx with
      | none =>
        have hbad : (none : Option (Exp {})) = some .unit := by
          simpa only [resolve, hfx] using hresolve
        cases hbad
      | some cell =>
        cases cell with
        | capability =>
          have hbad : (none : Option (Exp {})) = some .unit := by
            simpa only [resolve, hfx] using hresolve
          cases hbad
        | masked =>
          have hbad : (none : Option (Exp {})) = some .unit := by
            simpa only [resolve, hfx] using hresolve
          cases hbad
        | val v =>
          apply Exp.WfInHeap.wf_var
          apply Var.WfInHeap.wf_free
          exact hfx
    | bound bx => cases bx
  | unit =>
    apply Exp.WfInHeap.wf_unit
  | _ =>
    cases hresolve

theorem shape_val_denot_implies_wf {env : TypeEnv s}
  (hts : env.is_implying_wf)
  (T : Ty .shape s) :
  (Ty.shape_val_denot env T).implies_wf := by
  intro R m e hdenot
  cases T with
  | top =>
    have hdenot' : e.WfInHeap m.heap ∧ resolve_reachability m.heap e ⊆ R := by
      simpa only [Ty.shape_val_denot] using hdenot
    exact hdenot'.1
  | tvar X =>
    simpa only [Ty.shape_val_denot] using
      hts X R m e (by simpa only [Ty.shape_val_denot] using hdenot)
  | bool =>
    have hdenot' :
        resolve m.heap e = some Exp.btrue ∨ resolve m.heap e = some Exp.bfalse := by
      simpa only [Ty.shape_val_denot] using hdenot
    cases e with
    | btrue => exact Exp.WfInHeap.wf_btrue
    | bfalse => exact Exp.WfInHeap.wf_bfalse
    | var x =>
      cases x with
      | bound bx => cases bx
      | free fx =>
        cases hcell : m.heap fx with
        | none =>
          cases hdenot' with
          | inl hb =>
            have hbad : (none : Option (Exp {})) = some Exp.btrue := by
              simpa only [resolve, hcell] using hb
            cases hbad
          | inr hb =>
            have hbad : (none : Option (Exp {})) = some Exp.bfalse := by
              simpa only [resolve, hcell] using hb
            cases hbad
        | some cell =>
          cases cell with
          | val hv =>
            apply Exp.WfInHeap.wf_var
            apply Var.WfInHeap.wf_free
            simpa [Memory.lookup] using hcell
          | capability =>
            cases hdenot' with
            | inl hb =>
              have hbad : (none : Option (Exp {})) = some Exp.btrue := by
                simpa only [resolve, hcell] using hb
              cases hbad
            | inr hb =>
              have hbad : (none : Option (Exp {})) = some Exp.bfalse := by
                simpa only [resolve, hcell] using hb
              cases hbad
          | masked =>
            cases hdenot' with
            | inl hb =>
              have hbad : (none : Option (Exp {})) = some Exp.btrue := by
                simpa only [resolve, hcell] using hb
              cases hbad
            | inr hb =>
              have hbad : (none : Option (Exp {})) = some Exp.bfalse := by
                simpa only [resolve, hcell] using hb
              cases hbad
    | _ =>
      simp [Ty.shape_val_denot, resolve] at hdenot
  | unit =>
    have hdenot' : resolve m.heap e = some .unit := by
      simpa only [Ty.shape_val_denot] using hdenot
    exact wf_from_resolve_unit hdenot'
  | cell =>
    simp only [Ty.shape_val_denot] at hdenot
    obtain ⟨l, b0, heq, hlookup, _⟩ := hdenot
    -- e is a variable, so it's well-formed if it's in the heap
    rw [heq]
    apply Exp.WfInHeap.wf_var
    apply Var.WfInHeap.wf_free
    · simp only [Memory.lookup] at hlookup
      change m.heap l = some (Cell.capability (.mcell b0)) at hlookup
      exact hlookup
  | cap =>
    have hdenot' :
        e.WfInHeap m.heap ∧
          ∃ label : Nat,
            e = .var (.free label) ∧
              m.lookup label = some (.capability .basic) ∧
              label ∈ R := by
      simpa only [Ty.shape_val_denot] using hdenot
    exact hdenot'.1
  | arrow T1 T2 =>
    have hdenot' :
        e.WfInHeap m.heap ∧
          ∃ cs T0 t0,
            resolve m.heap e = some (.abs cs T0 t0) ∧
            cs.WfInHeap m.heap ∧
            let R0 := expand_captures m.heap cs
            R0 ⊆ R ∧
              ∀ (arg : Nat) (m' : Memory),
                m'.subsumes m ->
                Ty.capt_val_denot env T1 m' (.var (.free arg)) ->
                Ty.exi_exp_denot
                  (env.extend_var arg)
                  T2 R0 m' (t0.subst (Subst.openVar (.free arg))) := by
      simpa only [Ty.shape_val_denot] using hdenot
    exact hdenot'.1
  | poly T1 T2 =>
    have hdenot' :
        e.WfInHeap m.heap ∧
          ∃ cs S0 t0,
            resolve m.heap e = some (.tabs cs S0 t0) ∧
            cs.WfInHeap m.heap ∧
            let R0 := expand_captures m.heap cs
            R0 ⊆ R ∧
              ∀ (m' : Memory) (denot : PreDenot),
                m'.subsumes m ->
                denot.is_proper ->
                denot.ImplyAfter m' (Ty.shape_val_denot env T1) ->
                Ty.exi_exp_denot
                  (env.extend_tvar denot)
                  T2 R0 m' (t0.subst (Subst.openTVar .top)) := by
      simpa only [Ty.shape_val_denot] using hdenot
    exact hdenot'.1
  | cpoly B T =>
    have hdenot' :
        e.WfInHeap m.heap ∧
          ∃ cs B0 t0,
            resolve m.heap e = some (.cabs cs B0 t0) ∧
            cs.WfInHeap m.heap ∧
            let R0 := expand_captures m.heap cs
            R0 ⊆ R ∧
              ∀ (m' : Memory) (CS : CaptureSet {}),
                CS.WfInHeap m'.heap ->
                let A0 := CS.denot TypeEnv.empty
                m'.subsumes m ->
                (A0 m').BoundedBy (B.denot env m') ->
                Ty.exi_exp_denot
                  (env.extend_cvar CS)
                  T R0 m' (t0.subst (Subst.openCVar CS)) := by
      simpa only [Ty.shape_val_denot] using hdenot
    exact hdenot'.1

theorem shape_val_denot_is_tight {env : TypeEnv s}
  (hts : env.is_tight) :
  (Ty.shape_val_denot env T).is_tight := by
  intro R m fx ht
  cases T with
  | top =>
    simp only [Ty.shape_val_denot, resolve_reachability] at ht ⊢
    constructor
    · exact ht.1
    · exact CapabilitySet.Subset.refl
  | tvar X =>
    simpa only [Ty.shape_val_denot] using
      hts X R m fx (by simpa only [Ty.shape_val_denot] using ht)
  | bool =>
    simpa only [Ty.shape_val_denot] using ht
  | unit =>
    simpa only [Ty.shape_val_denot] using ht
  | cell =>
    simp only [Ty.shape_val_denot] at ht ⊢
    obtain ⟨l, b0, heq, hlookup, hmem⟩ := ht
    -- From heq: .var (.free fx) = .var (.free l), so fx = l
    have hfx_eq_l : fx = l := by
      injection heq with _ h
      injection h
    subst hfx_eq_l
    -- Need: fx ∈ reachability_of_loc m.heap fx
    -- reachability_of_loc m.heap fx = {fx} for mcell capabilities
    use fx, b0
    constructor
    · rfl
    · constructor
      · exact hlookup
      · have hlookup' : m.heap fx = some (Cell.capability (.mcell b0)) := by
          change m.heap fx = some (Cell.capability (.mcell b0)) at hlookup
          exact hlookup
        rw [reachability_of_loc, hlookup']
        exact CapabilitySet.mem.here
  | cap =>
    have ht' :
        ((.var (.free fx) : Exp {})).WfInHeap m.heap ∧
          ∃ label : Nat,
            (.var (.free fx) : Exp {}) = .var (.free label) ∧
              m.lookup label = some (.capability .basic) ∧
              label ∈ R := by
      simpa only [Ty.shape_val_denot] using ht
    obtain ⟨hwf, label, heq, hmem, hin⟩ := ht'
    have hfx_eq_label : fx = label := by
      injection heq with _ h
      injection h
    subst hfx_eq_label
    have hlookup' : m.heap fx = some (Cell.capability .basic) := by
      change m.heap fx = some (Cell.capability .basic) at hmem
      exact hmem
    have htight :
        ((.var (.free fx) : Exp {})).WfInHeap m.heap ∧
          ∃ label : Nat,
            (.var (.free fx) : Exp {}) = .var (.free label) ∧
              m.lookup label = some (.capability .basic) ∧
              label ∈ reachability_of_loc m.heap fx := by
      constructor
      · exact hwf
      · refine ⟨fx, rfl, hmem, ?_⟩
        rw [reachability_of_loc, hlookup']
        exact CapabilitySet.mem.here
    simpa only [Ty.shape_val_denot] using htight
  | arrow T1 T2 =>
    have ht' :
        ((.var (.free fx) : Exp {})).WfInHeap m.heap ∧
          ∃ cs T0 t0,
            resolve m.heap (.var (.free fx)) = some (Exp.abs cs T0 t0) ∧
            cs.WfInHeap m.heap ∧
            let R0 := expand_captures m.heap cs
            R0 ⊆ R ∧
              ∀ (arg : Nat) (m' : Memory),
                m'.subsumes m ->
                Ty.capt_val_denot env T1 m' (.var (.free arg)) ->
                Ty.exi_exp_denot
                  (env.extend_var arg)
                  T2 R0 m' (t0.subst (Subst.openVar (.free arg))) := by
      simpa only [Ty.shape_val_denot] using ht
    have ⟨hwf, cs, T0, t0, hresolve, hwf_cs, hR0_sub, hbody⟩ := ht'
    have hR0_sub' : expand_captures m.heap cs ⊆ reachability_of_loc m.heap fx := by
      have hstored : ∃ v, m.heap fx = some (Cell.val v) ∧ v.unwrap = Exp.abs cs T0 t0 := by
        cases heq : m.heap fx with
        | none =>
          have hbad : (none : Option (Exp {})) = some (Exp.abs cs T0 t0) := by
            simpa only [resolve, heq] using hresolve
          cases hbad
        | some cell =>
          cases cell with
          | capability =>
            have hbad : (none : Option (Exp {})) = some (Exp.abs cs T0 t0) := by
              simpa only [resolve, heq] using hresolve
            cases hbad
          | masked =>
            have hbad : (none : Option (Exp {})) = some (Exp.abs cs T0 t0) := by
              simpa only [resolve, heq] using hresolve
            cases hbad
          | val v =>
            have hunwrap : some v.unwrap = some (Exp.abs cs T0 t0) := by
              simpa only [resolve, heq] using hresolve
            injection hunwrap with hunwrap'
            exact ⟨v, rfl, hunwrap'⟩
      obtain ⟨v, hv, hunwrap⟩ := hstored
      rw [reachability_of_loc_eq_resolve_reachability m fx v hv, hunwrap]
      exact CapabilitySet.Subset.refl
    have htight :
        ((.var (.free fx) : Exp {})).WfInHeap m.heap ∧
          ∃ cs T0 t0,
            resolve m.heap (.var (.free fx)) = some (Exp.abs cs T0 t0) ∧
            cs.WfInHeap m.heap ∧
            let R0 := expand_captures m.heap cs
            R0 ⊆ reachability_of_loc m.heap fx ∧
              ∀ (arg : Nat) (m' : Memory),
                m'.subsumes m ->
                Ty.capt_val_denot env T1 m' (.var (.free arg)) ->
                Ty.exi_exp_denot
                  (env.extend_var arg)
                  T2 R0 m' (t0.subst (Subst.openVar (.free arg))) := by
      constructor
      · exact hwf
      · refine ⟨cs, T0, t0, hresolve, hwf_cs, ?_⟩
        exact ⟨hR0_sub', hbody⟩
    simpa only [Ty.shape_val_denot] using htight
  | poly T1 T2 =>
    have ht' :
        ((.var (.free fx) : Exp {})).WfInHeap m.heap ∧
          ∃ cs S0 t0,
            resolve m.heap (.var (.free fx)) = some (Exp.tabs cs S0 t0) ∧
            cs.WfInHeap m.heap ∧
            let R0 := expand_captures m.heap cs
            R0 ⊆ R ∧
              ∀ (m' : Memory) (denot : PreDenot),
                m'.subsumes m ->
                denot.is_proper ->
                denot.ImplyAfter m' (Ty.shape_val_denot env T1) ->
                Ty.exi_exp_denot
                  (env.extend_tvar denot)
                  T2 R0 m' (t0.subst (Subst.openTVar .top)) := by
      simpa only [Ty.shape_val_denot] using ht
    have ⟨hwf, cs, S0, t0, hresolve, hwf_cs, hR0_sub, hbody⟩ := ht'
    have hR0_sub' : expand_captures m.heap cs ⊆ reachability_of_loc m.heap fx := by
      have hstored : ∃ v, m.heap fx = some (Cell.val v) ∧ v.unwrap = Exp.tabs cs S0 t0 := by
        cases heq : m.heap fx with
        | none =>
          have hbad : (none : Option (Exp {})) = some (Exp.tabs cs S0 t0) := by
            simpa only [resolve, heq] using hresolve
          cases hbad
        | some cell =>
          cases cell with
          | capability =>
            have hbad : (none : Option (Exp {})) = some (Exp.tabs cs S0 t0) := by
              simpa only [resolve, heq] using hresolve
            cases hbad
          | masked =>
            have hbad : (none : Option (Exp {})) = some (Exp.tabs cs S0 t0) := by
              simpa only [resolve, heq] using hresolve
            cases hbad
          | val v =>
            have hunwrap : some v.unwrap = some (Exp.tabs cs S0 t0) := by
              simpa only [resolve, heq] using hresolve
            injection hunwrap with hunwrap'
            exact ⟨v, rfl, hunwrap'⟩
      obtain ⟨v, hv, hunwrap⟩ := hstored
      rw [reachability_of_loc_eq_resolve_reachability m fx v hv, hunwrap]
      exact CapabilitySet.Subset.refl
    have htight :
        ((.var (.free fx) : Exp {})).WfInHeap m.heap ∧
          ∃ cs S0 t0,
            resolve m.heap (.var (.free fx)) = some (Exp.tabs cs S0 t0) ∧
            cs.WfInHeap m.heap ∧
            let R0 := expand_captures m.heap cs
            R0 ⊆ reachability_of_loc m.heap fx ∧
              ∀ (m' : Memory) (denot : PreDenot),
                m'.subsumes m ->
                denot.is_proper ->
                denot.ImplyAfter m' (Ty.shape_val_denot env T1) ->
                Ty.exi_exp_denot
                  (env.extend_tvar denot)
                  T2 R0 m' (t0.subst (Subst.openTVar .top)) := by
      constructor
      · exact hwf
      · refine ⟨cs, S0, t0, hresolve, hwf_cs, ?_⟩
        exact ⟨hR0_sub', hbody⟩
    simpa only [Ty.shape_val_denot] using htight
  | cpoly B T =>
    have ht' :
        ((.var (.free fx) : Exp {})).WfInHeap m.heap ∧
          ∃ cs B0 t0,
            resolve m.heap (.var (.free fx)) = some (Exp.cabs cs B0 t0) ∧
            cs.WfInHeap m.heap ∧
            let R0 := expand_captures m.heap cs
            R0 ⊆ R ∧
              ∀ (m' : Memory) (CS : CaptureSet {}),
                CS.WfInHeap m'.heap ->
                let A0 := CS.denot TypeEnv.empty
                m'.subsumes m ->
                (A0 m').BoundedBy (B.denot env m') ->
                Ty.exi_exp_denot
                  (env.extend_cvar CS)
                  T R0 m' (t0.subst (Subst.openCVar CS)) := by
      simpa only [Ty.shape_val_denot] using ht
    have ⟨hwf, cs, B0, t0, hresolve, hwf_cs, hR0_sub, hbody⟩ := ht'
    have hR0_sub' : expand_captures m.heap cs ⊆ reachability_of_loc m.heap fx := by
      have hstored : ∃ v, m.heap fx = some (Cell.val v) ∧ v.unwrap = Exp.cabs cs B0 t0 := by
        cases heq : m.heap fx with
        | none =>
          have hbad : (none : Option (Exp {})) = some (Exp.cabs cs B0 t0) := by
            simpa only [resolve, heq] using hresolve
          cases hbad
        | some cell =>
          cases cell with
          | capability =>
            have hbad : (none : Option (Exp {})) = some (Exp.cabs cs B0 t0) := by
              simpa only [resolve, heq] using hresolve
            cases hbad
          | masked =>
            have hbad : (none : Option (Exp {})) = some (Exp.cabs cs B0 t0) := by
              simpa only [resolve, heq] using hresolve
            cases hbad
          | val v =>
            have hunwrap : some v.unwrap = some (Exp.cabs cs B0 t0) := by
              simpa only [resolve, heq] using hresolve
            injection hunwrap with hunwrap'
            exact ⟨v, rfl, hunwrap'⟩
      obtain ⟨v, hv, hunwrap⟩ := hstored
      rw [reachability_of_loc_eq_resolve_reachability m fx v hv, hunwrap]
      exact CapabilitySet.Subset.refl
    have htight :
        ((.var (.free fx) : Exp {})).WfInHeap m.heap ∧
          ∃ cs B0 t0,
            resolve m.heap (.var (.free fx)) = some (Exp.cabs cs B0 t0) ∧
            cs.WfInHeap m.heap ∧
            let R0 := expand_captures m.heap cs
            R0 ⊆ reachability_of_loc m.heap fx ∧
              ∀ (m' : Memory) (CS : CaptureSet {}),
                CS.WfInHeap m'.heap ->
                let A0 := CS.denot TypeEnv.empty
                m'.subsumes m ->
                (A0 m').BoundedBy (B.denot env m') ->
                Ty.exi_exp_denot
                  (env.extend_cvar CS)
                  T R0 m' (t0.subst (Subst.openCVar CS)) := by
      constructor
      · exact hwf
      · refine ⟨cs, B0, t0, hresolve, hwf_cs, ?_⟩
        exact ⟨hR0_sub', hbody⟩
    simpa only [Ty.shape_val_denot] using htight

theorem shape_val_denot_is_proper {env : TypeEnv s} {S : Ty .shape s}
  (hts : EnvTyping Γ env m) :
  (Ty.shape_val_denot env S).is_proper := by
  constructor
  · -- Prove: (Ty.shape_val_denot env S).is_reachability_safe
    exact shape_val_denot_is_reachability_safe (typed_env_is_reachability_safe hts) S
  · constructor
    · -- Prove: (Ty.shape_val_denot env S).is_reachability_monotonic
      exact shape_val_denot_is_reachability_monotonic
        (typed_env_is_reachability_monotonic hts) S
    · constructor
      · -- Prove: (Ty.shape_val_denot env S).implies_wf
        exact shape_val_denot_implies_wf (typed_env_is_implying_wf hts) S
      · constructor
        · -- Prove: (Ty.shape_val_denot env S).is_tight
          exact shape_val_denot_is_tight (typed_env_is_tight hts)
        · -- Prove: ∀ C, ((Ty.shape_val_denot env S) C).is_proper
          intro C
          constructor
          · exact shape_val_denot_is_monotonic (typed_env_is_monotonic hts) S C
          · constructor
            · exact shape_val_denot_is_transparent (typed_env_is_transparent hts) S C
            · exact shape_val_denot_is_bool_independent (typed_env_is_bool_independent hts) S C

theorem capt_denot_implyafter_lift
  (himp : (Ty.capt_val_denot env T1).ImplyAfter H (Ty.capt_val_denot env T2)) :
  (Ty.capt_exp_denot env T1).ImplyAfter H (Ty.capt_exp_denot env T2) := by
  intro C m' hsub e heval
  have heval' : Eval C m' e (Ty.capt_val_denot env T1).as_mpost := by
    simpa only [Ty.capt_exp_denot] using heval
  change Eval C m' e (Ty.capt_val_denot env T2).as_mpost
  apply eval_post_monotonic_general _ heval'
  have himp' := Denot.imply_after_to_m_entails_after himp
  exact Mpost.entails_after_subsumes himp' hsub

theorem exi_denot_implyafter_lift
  (himp : (Ty.exi_val_denot env T1).ImplyAfter H (Ty.exi_val_denot env T2)) :
  (Ty.exi_exp_denot env T1).ImplyAfter H (Ty.exi_exp_denot env T2) := by
  intro C m' hsub e heval
  have heval' : Eval C m' e (Ty.exi_val_denot env T1).as_mpost := by
    simpa only [Ty.exi_exp_denot] using heval
  have hgoal : Eval C m' e (Ty.exi_val_denot env T2).as_mpost := by
    apply eval_post_monotonic_general _ heval'
    have himp' := Denot.imply_after_to_m_entails_after himp
    exact Mpost.entails_after_subsumes himp' hsub
  simpa only [Ty.exi_exp_denot] using hgoal

end CCPrec
