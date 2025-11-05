import Semantic.CC.Semantics
import Semantic.CC.TypeSystem
import Semantic.Prelude

namespace CC

def resolve : Heap -> Exp {} -> Option (Exp {})
| s, .var (.free x) =>
  match s x with
  | some (.val v) => some v.unwrap
  | _ => none
| s, .var (.bound x) => by cases x
| _, other => some other

theorem resolve_monotonic {m1 m2 : Memory}
  (hsub : m2.subsumes m1)
  (hres : resolve m1.heap e = some v) :
  resolve m2.heap e = some v := by
  -- Case on the expression e
  cases e
  case var x =>
    -- Case on whether x is bound or free
    cases x
    case bound bv =>
      -- Bound variables in empty signature are impossible
      cases bv
    case free fx =>
      -- Free variable case: resolve looks up in heap
      simp only [resolve] at hres ⊢
      -- hres tells us what m1.heap fx is
      cases hfx : m1.heap fx
      · -- m1.heap fx = none, contradiction with hres
        simp [hfx] at hres
      · -- m1.heap fx = some cell
        rename_i cell
        simp [hfx] at hres
        cases cell
        case val heapval =>
          simp at hres
          -- hres now says: heapval.unwrap = v
          -- From hsub, m2.heap fx must also be some (Cell.val heapval)
          have : m2.heap fx = some (Cell.val heapval) := by
            simp [Memory.subsumes, Heap.subsumes] at hsub
            exact hsub fx (Cell.val heapval) hfx
          simp [this]
          exact hres
        case capability =>
          -- m1.heap fx = some Cell.capability, so resolve returns none
          simp at hres
  all_goals {
    -- For all other expression constructors (pack, abs, tabs, etc.)
    -- resolve returns the expression itself unchanged
    simp [resolve] at hres ⊢
    exact hres
  }

/-- Denotation of types. -/
def Denot := Memory -> Exp {} -> Prop

/-- Pre-denotation. It takes a capability to form a denotation. -/
def PreDenot := CapabilitySet -> Denot

/-- Capture-denotation. Given any memory, it produces a set of capabilities. -/
def CapDenot := Memory -> CapabilitySet

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

def Denot.is_proper (d : Denot) : Prop :=
  d.is_monotonic ∧ d.is_transparent

def resolve_reachability (H : Heap) (e : Exp {}) : CapabilitySet :=
  match e with
  | .var (.free x) => reachability_of_loc H x
  | .abs cs _ _ => expand_captures H cs
  | .tabs cs _ _ => expand_captures H cs
  | .cabs cs _ _ => expand_captures H cs
  | _ => {}  -- Other expressions have no reachability

theorem resolve_reachability_monotonic
  {m1 m2 : Memory}
  (hsub : m2.subsumes m1)
  (e : Exp {})
  (hwf : e.WfInHeap m1.heap) :
  resolve_reachability m2.heap e = resolve_reachability m1.heap e := by
  cases e with
  | var x =>
    cases x with
    | free fx =>
      simp [resolve_reachability]
      cases hwf with
      | wf_var hwf_x =>
        cases hwf_x with
        | wf_free hex =>
          exact reachability_of_loc_monotonic hsub fx hex
    | bound bx => cases bx
  | abs cs _ _ =>
    simp [resolve_reachability]
    cases hwf with
    | wf_abs hwf_cs _ _ =>
      exact expand_captures_monotonic hsub cs hwf_cs
  | tabs cs _ _ =>
    simp [resolve_reachability]
    cases hwf with
    | wf_tabs hwf_cs _ _ =>
      exact expand_captures_monotonic hsub cs hwf_cs
  | cabs cs _ _ =>
    simp [resolve_reachability]
    cases hwf with
    | wf_cabs hwf_cs _ _ =>
      exact expand_captures_monotonic hsub cs hwf_cs
  | pack _ _ => simp [resolve_reachability]
  | unit => simp [resolve_reachability]
  | app _ _ => simp [resolve_reachability]
  | tapp _ _ => simp [resolve_reachability]
  | capp _ _ => simp [resolve_reachability]
  | letin _ _ => simp [resolve_reachability]
  | unpack _ _ => simp [resolve_reachability]

/-- For simple values, compute_reachability equals resolve_reachability. -/
theorem compute_reachability_eq_resolve_reachability
  (h : Heap) (v : Exp {}) (hv : v.IsSimpleVal) :
  compute_reachability h v hv = resolve_reachability h v := by
  cases hv <;> rfl

/-- Heap invariant: the reachability stored in a heap value equals the computed
    reachability for that value.

    This invariant is maintained by the operational semantics, which always uses
    `compute_reachability` when creating heap values (see eval_letin in BigStep.lean).

    This is a fundamental property connecting operational reachability (stored in
    the heap) with denotational reachability (computed from expression structure). -/
axiom Memory.reachability_invariant :
  ∀ (m : Memory) (x : Nat) (v : HeapVal),
    m.heap x = some (Cell.val v) ->
    v.reachability = compute_reachability m.heap v.unwrap v.isVal

/-- Reachability of a heap location equals resolve_reachability of the stored value. -/
theorem reachability_of_loc_eq_resolve_reachability
  (m : Memory) (x : Nat) (v : HeapVal)
  (hx : m.heap x = some (Cell.val v)) :
  reachability_of_loc m.heap x = resolve_reachability m.heap v.unwrap := by
  -- reachability_of_loc m.heap x = v.reachability by definition
  unfold reachability_of_loc
  simp [hx]
  -- v.reachability = compute_reachability m.heap v.unwrap v.isVal
  rw [Memory.reachability_invariant m x v hx]
  -- compute_reachability = resolve_reachability for simple values
  exact compute_reachability_eq_resolve_reachability m.heap v.unwrap v.isVal

def PreDenot.is_reachability_safe (denot : PreDenot) : Prop :=
  ∀ R m e,
    denot R m e ->
    resolve_reachability m.heap e ⊆ R

def PreDenot.is_reachability_monotonic (pd : PreDenot) : Prop :=
  ∀ R1 R2,
    R1 ⊆ R2 ->
    ∀ m e,
      pd R1 m e ->
      pd R2 m e

def PreDenot.implies_wf (pd : PreDenot) : Prop :=
  ∀ R m e,
    pd R m e ->
    e.WfInHeap m.heap

def PreDenot.is_proper (pd : PreDenot) : Prop :=
  pd.is_reachability_safe
  ∧ pd.is_reachability_monotonic
  ∧ pd.implies_wf
  ∧ ∀ C, (pd C).is_proper

lemma Denot.as_mpost_is_monotonic {d : Denot}
  (hmon : d.is_monotonic) :
  d.as_mpost.is_monotonic := by
  intro m1 m2 e hwf hsub h
  unfold Denot.as_mpost at h ⊢
  exact hmon hsub h

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

def CaptureBound.denot : TypeEnv s -> CaptureBound s -> CapDenot
| _, .unbound => fun _ => CapabilitySet.any
| env, .bound cs => cs.denot env

mutual

def Ty.shape_val_denot : TypeEnv s -> Ty .shape s -> PreDenot
| _, .top => fun R m e =>
  e.WfInHeap m.heap ∧ resolve_reachability m.heap e ⊆ R
| env, .tvar X => env.lookup_tvar X
| _, .unit => fun _ m e => resolve m.heap e = some .unit
| _, .cap => fun A m e =>
  ∃ label : Nat,
    e = .var (.free label) ∧
    m.lookup label = some .capability ∧
    label ∈ A
| env, .arrow T1 T2 => fun A m e =>
  ∃ cs T0 t0,
    resolve m.heap e = some (.abs cs T0 t0) ∧
    cs.WfInHeap m.heap ∧
    let R0 := expand_captures m.heap cs
    R0 ⊆ A ∧
    (∀ (arg : Nat) (m' : Memory),
      m'.subsumes m ->
      Ty.capt_val_denot env T1 m' (.var (.free arg)) ->
      Ty.exi_exp_denot
        (env.extend_var arg)
        T2 (R0 ∪ (reachability_of_loc m'.heap arg)) m' (t0.subst (Subst.openVar (.free arg))))
| env, .poly T1 T2 => fun A m e =>
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
  ∃ cs B0 t0,
    resolve m.heap e = some (.cabs cs B0 t0) ∧
    cs.WfInHeap m.heap ∧
    let R0 := expand_captures m.heap cs
    R0 ⊆ A ∧
    (∀ (m' : Memory) (CS : CaptureSet {}),
      CS.WfInHeap m'.heap ->
      let A0 := CS.denot TypeEnv.empty
      m'.subsumes m ->
      (A0 m' ⊆ B.denot env m') ->
      Ty.exi_exp_denot
        (env.extend_cvar CS)
        T R0 m' (t0.subst (Subst.openCVar CS)))

def Ty.capt_val_denot : TypeEnv s -> Ty .capt s -> Denot
| ρ, .capt C S => fun mem exp =>
  exp.WfInHeap mem.heap ∧
  (C.subst (Subst.from_TypeEnv ρ)).WfInHeap mem.heap ∧
  Ty.shape_val_denot ρ S (C.denot ρ mem) mem exp

def Ty.exi_val_denot : TypeEnv s -> Ty .exi s -> Denot
| ρ, .typ T => Ty.capt_val_denot ρ T
| ρ, .exi T => fun m e =>
  match resolve m.heap e with
  | some (.pack CS x) => Ty.capt_val_denot (ρ.extend_cvar CS) T m (.var x)
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
  HasDenotation (CaptureBound s) (TypeEnv s) CapDenot where
  interp := CaptureBound.denot

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
  (cs.ground_denot m ⊆ ⟦B⟧_[env] m) ∧
  EnvTyping Γ env m

def SemanticTyping (C : CaptureSet s) (Γ : Ctx s) (e : Exp s) (E : Ty .exi s) : Prop :=
  ∀ ρ m,
    EnvTyping Γ ρ m ->
    ⟦E⟧e_[ρ] (C.denot ρ m) m (e.subst (Subst.from_TypeEnv ρ))

notation:65 C " # " Γ " ⊨ " e " : " T => SemanticTyping C Γ e T

theorem Subst.from_TypeEnv_weaken_open {env : TypeEnv s} {x : Nat} :
  (Subst.from_TypeEnv env).lift.comp (Subst.openVar (.free x)) =
    Subst.from_TypeEnv (env.extend_var x) := by
  apply Subst.funext
  · intro y
    cases y <;> rfl
  · intro X
    cases X
    rfl
  · intro C
    cases C with
    | there C' =>
      simp [Subst.from_TypeEnv, Subst.lift, Subst.comp, Subst.openVar,
        TypeEnv.extend_var, TypeEnv.lookup_cvar, TypeEnv.lookup]
      exact CaptureSet.weaken_openVar

theorem Exp.from_TypeEnv_weaken_open {e : Exp (s,x)} :
  (e.subst (Subst.from_TypeEnv env).lift).subst (Subst.openVar (.free x)) =
    e.subst (Subst.from_TypeEnv (env.extend_var x)) := by
  rw [Exp.subst_comp]
  rw [Subst.from_TypeEnv_weaken_open]

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
      simp [Subst.from_TypeEnv, Subst.lift, Subst.comp, Subst.openTVar,
        TypeEnv.extend_tvar, TypeEnv.lookup_cvar, TypeEnv.lookup]
      exact CaptureSet.weaken_openTVar

theorem Exp.from_TypeEnv_weaken_open_tvar
  {env : TypeEnv s} {d : PreDenot} {e : Exp (s,X)} :
  (e.subst (Subst.from_TypeEnv env).lift).subst (Subst.openTVar .top) =
    e.subst (Subst.from_TypeEnv (env.extend_tvar d)) := by
  rw [Exp.subst_comp]
  rw [Subst.from_TypeEnv_weaken_open_tvar]

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
      simp [Subst.comp, Subst.lift, Subst.from_TypeEnv, Subst.openCVar,
        TypeEnv.extend_cvar, TypeEnv.lookup_cvar, TypeEnv.lookup]
      exact CaptureSet.weaken_openCVar

theorem Exp.from_TypeEnv_weaken_open_cvar
  {env : TypeEnv s} {cs : CaptureSet {}} {e : Exp (s,C)} :
  (e.subst (Subst.from_TypeEnv env).lift).subst (Subst.openCVar cs) =
    e.subst (Subst.from_TypeEnv (env.extend_cvar cs)) := by
  rw [Exp.subst_comp]
  rw [Subst.from_TypeEnv_weaken_open_cvar]

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
        -- LHS: unpack maps .there (.there v) to .bound v,
        --      subst applies lift.lift.var v
        -- Need to show: lift.lift.var v = .free (ρ.lookup_var v)
        simp [Subst.comp, Subst.unpack, Var.subst]
        -- Now show lift.lift.var (.there (.there v)) for from_TypeEnv evaluates correctly
        rw [Subst.lift_there_var_eq]
        rw [Subst.lift_there_var_eq]
        simp [Subst.from_TypeEnv, Var.rename, TypeEnv.lookup_var]
        simp [TypeEnv.extend_var, TypeEnv.extend_cvar, TypeEnv.lookup]
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
        simp [Subst.comp, Subst.unpack]
        -- Need to show: (lift.lift.cvar (.there .here)).subst unpack = cs
        -- This is unpack.cvar (.there .here) = cs by definition
        rw [Subst.lift_there_cvar_eq]
        simp [Subst.lift, CaptureSet.subst, CaptureSet.rename]
        -- Goal: match Rename.succ.var .here with | .here.there => cs | ... = cs
        -- Rename.succ.var .here = .here.there by definition
        rfl
      case there c0 =>
        -- LHS: comp maps .there (.there c0) through unpack then lift.lift
        simp [Subst.comp, Subst.unpack]
        rw [Subst.lift_there_cvar_eq]
        rw [Subst.lift_there_cvar_eq]
        -- Generalize before simplifying
        simp only [Subst.from_TypeEnv, TypeEnv.extend_var, TypeEnv.extend_cvar,
          TypeEnv.lookup_cvar, TypeEnv.lookup]
        -- Now the goal has ρ.lookup_cvar c0 expanded to match expression
        -- Let's generalize this ground capture set
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
            simp [instCaptHasDenotation, Ty.capt_val_denot] at htype
            have ⟨hwf, _, _⟩ := htype
            -- hwf : (.var (.free n)).WfInHeap m.heap
            cases hwf with
            | wf_var hwf_var =>
              -- hwf_var : Var.WfInHeap (.free n) m.heap
              have ih_wf := ih htyping'
              constructor
              · intro x
                cases x with
                | here =>
                  simp [Subst.from_TypeEnv, TypeEnv.lookup_var, TypeEnv.lookup]
                  exact hwf_var
                | there x' =>
                  simp [Subst.from_TypeEnv, TypeEnv.lookup_var, TypeEnv.lookup]
                  exact ih_wf.wf_var x'
              · intro X
                cases X with
                | there X' =>
                  simp [Subst.from_TypeEnv]
                  exact ih_wf.wf_tvar X'
              · intro C_var
                cases C_var with
                | there C' =>
                  simp [Subst.from_TypeEnv]
                  exact ih_wf.wf_cvar C'
      | tvar S =>
        -- Type variable binding: doesn't affect term variable substitution
        cases info with
        | tvar denot =>
          unfold EnvTyping at htyping
          have ⟨_, _, htyping'⟩ := htyping
          have ih_wf := ih htyping'
          constructor
          · intro x
            cases x with
            | there x' =>
              simp [Subst.from_TypeEnv, TypeEnv.lookup_var, TypeEnv.lookup]
              exact ih_wf.wf_var x'
          · intro X
            cases X with
            | here =>
              simp [Subst.from_TypeEnv]
              apply Ty.WfInHeap.wf_top
            | there X' =>
              simp [Subst.from_TypeEnv]
              exact ih_wf.wf_tvar X'
          · intro C_var
            cases C_var with
            | there C' =>
              simp [Subst.from_TypeEnv]
              exact ih_wf.wf_cvar C'
      | cvar B =>
        -- Capture variable binding: doesn't affect term variable substitution
        cases info with
        | cvar cs =>
          unfold EnvTyping at htyping
          have ⟨hwf, hwf_bound, hsub, htyping'⟩ := htyping
          have ih_wf := ih htyping'
          constructor
          · intro x
            cases x with
            | there x' =>
              simp [Subst.from_TypeEnv, TypeEnv.lookup_var, TypeEnv.lookup]
              exact ih_wf.wf_var x'
          · intro X
            cases X with
            | there X' =>
              simp [Subst.from_TypeEnv]
              exact ih_wf.wf_tvar X'
          · intro C_var
            cases C_var with
            | here =>
              simp [Subst.from_TypeEnv, TypeEnv.lookup_cvar, TypeEnv.lookup]
              exact hwf
            | there C' =>
              simp [Subst.from_TypeEnv]
              exact ih_wf.wf_cvar C'

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
  intro h
  intro m e
  constructor
  · intro h0
    apply (h m e).mpr h0
  · intro h0
    apply (h m e).mp h0

def Denot.equiv_trans (d1 d2 d3 : Denot) : d1 ≈ d2 -> d2 ≈ d3 -> d1 ≈ d3 := by
  intro h12
  intro h23
  intro m e
  have h1 := h12 m e
  have h2 := h23 m e
  grind

theorem Denot.eq_to_equiv (d1 d2 : Denot) : d1 = d2 -> d1 ≈ d2 := by
  intro h
  intro m e
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
  · intro h A
    intro m e
    exact h A m e

theorem PreDenot.eq_to_equiv {pd1 pd2 : PreDenot} (h : pd1 = pd2) : pd1 ≈ pd2 := by
  intro A
  intro m e
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

structure TypeEnv.IsMonotonic (env : TypeEnv s) : Prop where
  tvar : ∀ (X : BVar s .tvar),
    (env.lookup_tvar X).is_monotonic

def TypeEnv.is_transparent (env : TypeEnv s) : Prop :=
  ∀ (X : BVar s .tvar),
    (env.lookup_tvar X).is_transparent

def TypeEnv.is_reachability_safe (env : TypeEnv s) : Prop :=
  ∀ (X : BVar s .tvar),
    (env.lookup_tvar X).is_reachability_safe

def TypeEnv.is_reachability_monotonic (env : TypeEnv s) : Prop :=
  ∀ (X : BVar s .tvar),
    (env.lookup_tvar X).is_reachability_monotonic

def TypeEnv.is_implying_wf (env : TypeEnv s) : Prop :=
  ∀ (X : BVar s .tvar),
    (env.lookup_tvar X).implies_wf

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
          simp [EnvTyping] at ht
          have ⟨_, ht'⟩ := ht
          have ih_result := ih ht'
          constructor
          · intro x
            cases x with
            | there x =>
              simp [TypeEnv.lookup_tvar, TypeEnv.lookup]
              exact ih_result.tvar x
      | tvar S =>
        cases info with
        | tvar d =>
          simp [EnvTyping] at ht
          have ⟨hproper, _, ht'⟩ := ht
          have ih_result := ih ht'
          constructor
          · intro x
            cases x with
            | here =>
              simp [TypeEnv.lookup_tvar, TypeEnv.lookup]
              -- hproper says d.is_proper
              -- We need d.is_monotonic
              intro C
              exact (hproper.2.2.2 C).1
            | there x =>
              simp [TypeEnv.lookup_tvar, TypeEnv.lookup]
              exact ih_result.tvar x
      | cvar B =>
        cases info with
        | cvar cs =>
          simp [EnvTyping] at ht
          have ⟨hwf, hwf_bound, hsub, ht'⟩ := ht
          have ih_result := ih ht'
          constructor
          · intro x
            cases x with
            | there x =>
              simp [TypeEnv.lookup_tvar, TypeEnv.lookup]
              exact ih_result.tvar x

theorem typed_env_is_transparent
  (ht : EnvTyping Γ env mem) :
  env.is_transparent := by
  induction Γ with
  | empty =>
    cases env with
    | empty =>
      simp [TypeEnv.is_transparent]
      intro x
      cases x
  | push Γ k ih =>
    cases env with
    | extend env' info =>
      cases k with
      | var T =>
        cases info with
        | var n =>
          simp [EnvTyping] at ht
          have ⟨_, ht'⟩ := ht
          have ih_result := ih ht'
          simp [TypeEnv.is_transparent] at ih_result ⊢
          intro x
          cases x with
          | there x =>
            simp [TypeEnv.lookup_tvar, TypeEnv.lookup]
            exact ih_result x
      | tvar S =>
        cases info with
        | tvar d =>
          simp [EnvTyping] at ht
          have ⟨hproper, _, ht'⟩ := ht
          have ih_result := ih ht'
          simp [TypeEnv.is_transparent] at ih_result ⊢
          intro x
          cases x with
          | here =>
            simp [TypeEnv.lookup_tvar, TypeEnv.lookup]
            -- hproper says d.is_proper
            -- We need d.is_transparent
            intro C
            exact (hproper.2.2.2 C).2
          | there x =>
            simp [TypeEnv.lookup_tvar, TypeEnv.lookup]
            exact ih_result x
      | cvar B =>
        cases info with
        | cvar cs =>
          simp [EnvTyping] at ht
          have ⟨hwf, hwf_bound, hsub, ht'⟩ := ht
          have ih_result := ih ht'
          simp [TypeEnv.is_transparent] at ih_result ⊢
          intro x
          cases x with
          | there x =>
            simp [TypeEnv.lookup_tvar, TypeEnv.lookup]
            exact ih_result x

theorem typed_env_is_reachability_safe
  (ht : EnvTyping Γ env mem) :
  env.is_reachability_safe := by
  induction Γ with
  | empty =>
    cases env with
    | empty =>
      simp [TypeEnv.is_reachability_safe]
      intro x
      cases x
  | push Γ k ih =>
    cases env with
    | extend env' info =>
      cases k with
      | var T =>
        cases info with
        | var n =>
          simp [EnvTyping] at ht
          have ⟨_, ht'⟩ := ht
          have ih_result := ih ht'
          simp [TypeEnv.is_reachability_safe] at ih_result ⊢
          intro x
          cases x with
          | there x =>
            simp [TypeEnv.lookup_tvar, TypeEnv.lookup]
            exact ih_result x
      | tvar S =>
        cases info with
        | tvar d =>
          simp [EnvTyping] at ht
          have ⟨hproper, _, ht'⟩ := ht
          have ih_result := ih ht'
          simp [TypeEnv.is_reachability_safe] at ih_result ⊢
          intro x
          cases x with
          | here =>
            simp [TypeEnv.lookup_tvar, TypeEnv.lookup]
            -- hproper says d.is_proper, which is d.is_reachability_safe ∧ ∀ C, (d C).is_proper
            -- We need d.is_reachability_safe
            exact hproper.1
          | there x =>
            simp [TypeEnv.lookup_tvar, TypeEnv.lookup]
            exact ih_result x
      | cvar B =>
        cases info with
        | cvar cs =>
          simp [EnvTyping] at ht
          have ⟨hwf, hwf_bound, hsub, ht'⟩ := ht
          have ih_result := ih ht'
          simp [TypeEnv.is_reachability_safe] at ih_result ⊢
          intro x
          cases x with
          | there x =>
            simp [TypeEnv.lookup_tvar, TypeEnv.lookup]
            exact ih_result x

theorem typed_env_is_reachability_monotonic
  (ht : EnvTyping Γ env mem) :
  env.is_reachability_monotonic := by
  induction Γ with
  | empty =>
    cases env with
    | empty =>
      simp [TypeEnv.is_reachability_monotonic]
      intro x
      cases x
  | push Γ k ih =>
    cases env with
    | extend env' info =>
      cases k with
      | var T =>
        cases info with
        | var n =>
          simp [EnvTyping] at ht
          have ⟨_, ht'⟩ := ht
          have ih_result := ih ht'
          simp [TypeEnv.is_reachability_monotonic] at ih_result ⊢
          intro x
          cases x with
          | there x =>
            simp [TypeEnv.lookup_tvar, TypeEnv.lookup]
            exact ih_result x
      | tvar S =>
        cases info with
        | tvar d =>
          simp [EnvTyping] at ht
          have ⟨hproper, _, ht'⟩ := ht
          have ih_result := ih ht'
          simp [TypeEnv.is_reachability_monotonic] at ih_result ⊢
          intro x
          cases x with
          | here =>
            simp [TypeEnv.lookup_tvar, TypeEnv.lookup]
            -- hproper says d.is_proper
            -- We need d.is_reachability_monotonic, which is hproper.2.1
            exact hproper.2.1
          | there x =>
            simp [TypeEnv.lookup_tvar, TypeEnv.lookup]
            exact ih_result x
      | cvar B =>
        cases info with
        | cvar cs =>
          simp [EnvTyping] at ht
          have ⟨hwf, hwf_bound, hsub, ht'⟩ := ht
          have ih_result := ih ht'
          simp [TypeEnv.is_reachability_monotonic] at ih_result ⊢
          intro x
          cases x with
          | there x =>
            simp [TypeEnv.lookup_tvar, TypeEnv.lookup]
            exact ih_result x

theorem typed_env_is_implying_wf
  (ht : EnvTyping Γ env mem) :
  env.is_implying_wf := by
  induction Γ with
  | empty =>
    cases env with
    | empty =>
      simp [TypeEnv.is_implying_wf]
      intro x
      cases x
  | push Γ k ih =>
    cases env with
    | extend env' info =>
      cases k with
      | var T =>
        cases info with
        | var n =>
          simp [EnvTyping] at ht
          have ⟨_, ht'⟩ := ht
          have ih_result := ih ht'
          simp [TypeEnv.is_implying_wf] at ih_result ⊢
          intro x
          cases x with
          | there x =>
            simp [TypeEnv.lookup_tvar, TypeEnv.lookup]
            exact ih_result x
      | tvar S =>
        cases info with
        | tvar d =>
          simp [EnvTyping] at ht
          have ⟨hproper, _, ht'⟩ := ht
          have ih_result := ih ht'
          simp [TypeEnv.is_implying_wf] at ih_result ⊢
          intro x
          cases x with
          | here =>
            simp [TypeEnv.lookup_tvar, TypeEnv.lookup]
            -- hproper says d.is_proper
            -- We need d.implies_wf
            exact hproper.2.2.1
          | there x =>
            simp [TypeEnv.lookup_tvar, TypeEnv.lookup]
            exact ih_result x
      | cvar B =>
        cases info with
        | cvar cs =>
          simp [EnvTyping] at ht
          have ⟨hwf, hwf_bound, hsub, ht'⟩ := ht
          have ih_result := ih ht'
          simp [TypeEnv.is_implying_wf] at ih_result ⊢
          intro x
          cases x with
          | there x =>
            simp [TypeEnv.lookup_tvar, TypeEnv.lookup]
            exact ih_result x

theorem shape_val_denot_is_transparent {env : TypeEnv s}
  (henv : TypeEnv.is_transparent env)
  (T : Ty .shape s) :
  (Ty.shape_val_denot env T).is_transparent := by
  cases T with
  | top =>
    intro C m x v hx ht
    simp [Ty.shape_val_denot] at ht ⊢
    -- ht : v.unwrap.WfInHeap m.heap ∧ resolve_reachability m.heap v.unwrap ⊆ C
    -- Goal: (.var (.free x)).WfInHeap m.heap ∧ resolve_reachability m.heap (.var (.free x)) ⊆ C
    constructor
    · -- Prove: (.var (.free x)).WfInHeap m.heap
      apply Exp.WfInHeap.wf_var
      apply Var.WfInHeap.wf_free
      exact hx
    · -- Prove: resolve_reachability m.heap (.var (.free x)) ⊆ C
      simp [resolve_reachability]
      -- Goal: reachability_of_loc m.heap x ⊆ C
      -- Extract heap location from memory lookup
      have hx_heap : m.heap x = some (Cell.val v) := by
        simp [Memory.lookup] at hx
        exact hx
      -- Use heap invariant to connect stored reachability with resolve_reachability
      rw [reachability_of_loc_eq_resolve_reachability m x v hx_heap]
      -- Now goal is: resolve_reachability m.heap v.unwrap ⊆ C, which is ht.2
      exact ht.2
  | tvar X =>
    intro C
    simp [Ty.shape_val_denot]
    exact henv X C
  | unit =>
    intro C m x v hx ht
    simp [Ty.shape_val_denot] at ht ⊢
    have hx' : m.heap x = some (.val v) := by
      simp [Memory.lookup] at hx
      exact hx
    rw [resolve_var_heap_trans hx']
    exact ht
  | cap =>
    intro C m x v hx ht
    simp [Ty.shape_val_denot] at ht ⊢
    have ⟨label, hlabel, hcap, hmem⟩ := ht
    -- v.unwrap = .var (.free label), but v.isVal says it's a simple value
    -- Variables are not simple values, so this is a contradiction
    have hval := v.isVal
    rw [hlabel] at hval
    cases hval
  | arrow T1 T2 =>
    intro C m x v hx ht
    simp [Ty.shape_val_denot] at ht ⊢
    have hx' : m.heap x = some (.val v) := by
      simp [Memory.lookup] at hx
      exact hx
    have heq := resolve_var_heap_trans hx'
    rw [heq]
    exact ht
  | poly T1 T2 =>
    intro C m x v hx ht
    simp [Ty.shape_val_denot] at ht ⊢
    have hx' : m.heap x = some (.val v) := by
      simp [Memory.lookup] at hx
      exact hx
    have heq := resolve_var_heap_trans hx'
    rw [heq]
    exact ht
  | cpoly B T =>
    intro C m x v hx ht
    simp [Ty.shape_val_denot] at ht ⊢
    have hx' : m.heap x = some (.val v) := by
      simp [Memory.lookup] at hx
      exact hx
    have heq := resolve_var_heap_trans hx'
    rw [heq]
    exact ht

theorem capt_val_denot_is_transparent {env : TypeEnv s}
  (henv : TypeEnv.is_transparent env)
  (T : Ty .capt s) :
  (Ty.capt_val_denot env T).is_transparent := by
  cases T with
  | capt C S =>
    intro m x v hx ht
    simp [Ty.capt_val_denot] at ht ⊢
    have ⟨hwf, hwf_C, hshape⟩ := ht
    constructor
    · -- Prove: (.var (.free x)).WfInHeap m.heap
      -- A variable is well-formed if it points to something in the heap
      apply Exp.WfInHeap.wf_var
      apply Var.WfInHeap.wf_free
      exact hx
    · constructor
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
    simp [Ty.exi_val_denot]
    exact capt_val_denot_is_transparent henv T
  | exi T =>
    intro m x v hx ht
    simp only [Ty.exi_val_denot] at ht ⊢
    -- ht: match (resolve m.heap v.unwrap) with some (pack CS x) => ...
    -- Goal: match (resolve m.heap (var (free x))) with some (pack CS x) => ...
    -- Since m.heap x = some (Cell.val v), resolve (var (free x)) = some v.unwrap
    have hlookup : m.heap x = some (Cell.val v) := by simp [Memory.lookup] at hx; exact hx
    -- Rewrite resolve m.heap (var (free x))
    change match resolve m.heap (.var (.free x)) with
      | some (.pack CS x) => Ty.capt_val_denot (env.extend_cvar CS) T m (.var x)
      | _ => False
    simp only [resolve, hlookup]
    -- Now goal is: match (some v.unwrap) with ...
    -- Need to show this equals match (resolve m.heap v.unwrap) with ...
    cases hresolve : resolve m.heap v.unwrap
    · -- resolve returned none - contradiction with ht
      simp [hresolve] at ht
    · -- resolve returned some e'
      rename_i e'
      cases e'
      case pack =>
        -- resolve returned some (pack CS' y')
        rename_i CS' y'
        simp [hresolve] at ht
        -- ht now says: Ty.capt_val_denot (env.extend_cvar CS') T m (var y')
        -- Need to show v.unwrap = pack CS' y'
        cases hunwrap : v.unwrap <;> rw [hunwrap] at hresolve
        case var =>
          cases v
          simp at hunwrap
          subst hunwrap
          rename_i h_isval
          cases h_isval
        case pack =>
          -- pack case
          rename_i CS'' y''
          simp [resolve] at hresolve
          -- hresolve now says: CS'' = CS' ∧ y'' = y'
          obtain ⟨hCS, hy⟩ := hresolve
          subst hCS hy
          simp
          exact ht
        all_goals {
          -- For other constructors (abs, tabs, etc.)
          simp [resolve] at hresolve
          -- hresolve says some (this constructor) = some (pack ...), contradiction
        }
      all_goals {
        -- resolve returned something other than pack - contradiction with ht
        simp [hresolve] at ht
      }

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
    simp at hwf
    cases hwf with
    | wf_union hwf1 hwf2 =>
      rw [ih1 hwf1, ih2 hwf2]
  | var v =>
    cases v with
    | bound x => cases x  -- No bound variables in empty signature
    | free x =>
      -- Free variable: use reachability_of_loc_monotonic
      unfold CaptureSet.ground_denot
      simp at hwf
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
    unfold CaptureSet.denot
    simp [CaptureSet.subst, CaptureSet.ground_denot] at hwf ⊢
    cases hwf with
    | wf_union hwf1 hwf2 =>
      -- Goal after simp is a conjunction
      constructor
      · exact ih1 hwf1
      · exact ih2 hwf2
  | var v =>
    cases v with
    | bound x =>
      -- Bound variable: after substitution becomes free variable
      unfold CaptureSet.denot
      simp [CaptureSet.subst, Subst.from_TypeEnv] at hwf
      simp [CaptureSet.subst, Subst.from_TypeEnv]
      unfold CaptureSet.ground_denot
      cases hwf with
      | wf_var_free hex =>
        -- hex : m1.heap (ρ.lookup_var x) = some _
        -- Memory.lookup is definitionally equal to heap access
        exact (reachability_of_loc_monotonic hsub (ρ.lookup_var x) hex).symm
    | free x =>
      -- Free variable: stays as free variable
      unfold CaptureSet.denot
      simp [CaptureSet.subst] at hwf
      simp [CaptureSet.subst]
      unfold CaptureSet.ground_denot
      cases hwf with
      | wf_var_free hex =>
        -- hex : m1.heap x = some _
        -- Memory.lookup is definitionally equal to heap access
        exact (reachability_of_loc_monotonic hsub x hex).symm
  | cvar c =>
    -- Capture variable: after substitution becomes ground capture set
    unfold CaptureSet.denot
    simp [CaptureSet.subst, Subst.from_TypeEnv]
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
    unfold CaptureBound.denot
    -- Extract well-formedness of the capture set from hwf
    simp [CaptureBound.subst] at hwf
    cases hwf with
    | wf_bound hwf_cs =>
      exact capture_set_denot_is_monotonic hwf_cs hsub

mutual

def shape_val_denot_is_monotonic {env : TypeEnv s}
  (henv : env.IsMonotonic)
  (T : Ty .shape s) :
  (Ty.shape_val_denot env T).is_monotonic := by
  intro C
  cases T with
  | top =>
    intro m1 m2 e hmem ht
    simp [Ty.shape_val_denot] at ht ⊢
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
    simp [Ty.shape_val_denot]
    exact henv.tvar X C
  | unit =>
    intro m1 m2 e hmem ht
    simp [Ty.shape_val_denot] at ht ⊢
    cases e with
    | var x =>
      cases x with
      | free fx =>
        simp [resolve] at ht ⊢
        cases hres : m1.heap fx with
        | none => simp [hres] at ht
        | some v =>
          simp [hres] at ht
          have hsub : m2.heap.subsumes m1.heap := hmem
          have := hsub fx v hres
          simp [this, ht]
      | bound bx => cases bx
    | unit => simp [resolve] at ht ⊢
    | abs _ _ _ => simp [resolve] at ht
    | tabs _ _ _ => simp [resolve] at ht
    | cabs _ _ _ => simp [resolve] at ht
    | pack _ _ => simp [resolve] at ht
    | unpack _ _ => simp [resolve] at ht
    | app _ _ => simp [resolve] at ht
    | tapp _ _ => simp [resolve] at ht
    | capp _ _ => simp [resolve] at ht
    | letin _ _ => simp [resolve] at ht
  | cap =>
    intro m1 m2 e hmem ht
    simp [Ty.shape_val_denot] at ht ⊢
    have ⟨label, heq, hcap, hmemin⟩ := ht
    use label
    constructor
    · exact heq
    · constructor
      · have hsub : m2.heap.subsumes m1.heap := hmem
        have := hsub label .capability hcap
        simp [Memory.lookup]
        exact this
      · exact hmemin
  | arrow T1 T2 =>
    intro m1 m2 e hmem ht
    simp [Ty.shape_val_denot] at ht ⊢
    have ⟨cs, T0, t0, hr, hwf_cs, hR0_sub, hfun⟩ := ht
    use cs, T0, t0
    constructor
    · cases e with
      | var x =>
        cases x with
        | free fx =>
          simp [resolve] at hr ⊢
          cases hres : m1.heap fx with
          | none => simp [hres] at hr
          | some v =>
            simp [hres] at hr
            have hsub : m2.heap.subsumes m1.heap := hmem
            have := hsub fx v hres
            simp [this, hr]
        | bound bx => cases bx
      | abs _ _ _ => simp [resolve] at hr ⊢; exact hr
      | tabs _ _ _ => simp [resolve] at hr
      | cabs _ _ _ => simp [resolve] at hr
      | pack _ _ => simp [resolve] at hr
      | unit => simp [resolve] at hr
      | unpack _ _ => simp [resolve] at hr
      | app _ _ => simp [resolve] at hr
      | tapp _ _ => simp [resolve] at hr
      | capp _ _ => simp [resolve] at hr
      | letin _ _ => simp [resolve] at hr
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
    simp [Ty.shape_val_denot] at ht ⊢
    have ⟨cs, S0, t0, hr, hwf_cs, hR0_sub, hfun⟩ := ht
    use cs, S0, t0
    constructor
    · cases e with
      | var x =>
        cases x with
        | free fx =>
          simp [resolve] at hr ⊢
          cases hres : m1.heap fx with
          | none => simp [hres] at hr
          | some v =>
            simp [hres] at hr
            have hsub : m2.heap.subsumes m1.heap := hmem
            have := hsub fx v hres
            simp [this, hr]
        | bound bx => cases bx
      | tabs _ _ _ => simp [resolve] at hr ⊢; exact hr
      | abs _ _ _ => simp [resolve] at hr
      | cabs _ _ _ => simp [resolve] at hr
      | pack _ _ => simp [resolve] at hr
      | unit => simp [resolve] at hr
      | unpack _ _ => simp [resolve] at hr
      | app _ _ => simp [resolve] at hr
      | tapp _ _ => simp [resolve] at hr
      | capp _ _ => simp [resolve] at hr
      | letin _ _ => simp [resolve] at hr
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
                simp [TypeEnv.extend_tvar, TypeEnv.lookup_tvar, TypeEnv.lookup]
                intro C
                exact (hdenot_proper.2.2.2 C).1
              | there X' =>
                simp [TypeEnv.extend_tvar, TypeEnv.lookup_tvar, TypeEnv.lookup]
                exact henv.tvar X'
          -- Use convert with expand_captures monotonicity
          have heq' := expand_captures_monotonic hmem cs hwf_cs
          convert hfun m' denot (Memory.subsumes_trans msub hmem) hdenot_proper himply using 2
  | cpoly B T =>
    intro m1 m2 e hmem ht
    simp [Ty.shape_val_denot] at ht ⊢
    have ⟨cs, B0, t0, hr, hwf_cs, hR0_sub, hfun⟩ := ht
    use cs, B0, t0
    constructor
    · cases e with
      | var x =>
        cases x with
        | free fx =>
          simp [resolve] at hr ⊢
          cases hres : m1.heap fx with
          | none => simp [hres] at hr
          | some v =>
            simp [hres] at hr
            have hsub : m2.heap.subsumes m1.heap := hmem
            have := hsub fx v hres
            simp [this, hr]
        | bound bx => cases bx
      | cabs _ _ _ => simp [resolve] at hr ⊢; exact hr
      | abs _ _ _ => simp [resolve] at hr
      | tabs _ _ _ => simp [resolve] at hr
      | pack _ _ => simp [resolve] at hr
      | unit => simp [resolve] at hr
      | unpack _ _ => simp [resolve] at hr
      | app _ _ => simp [resolve] at hr
      | tapp _ _ => simp [resolve] at hr
      | capp _ _ => simp [resolve] at hr
      | letin _ _ => simp [resolve] at hr
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
    simp [Ty.capt_val_denot] at ht ⊢
    have ⟨hwf, hwf_C, hshape⟩ := ht
    constructor
    · -- Prove: e.WfInHeap m2.heap
      exact Exp.wf_monotonic hmem hwf
    · constructor
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
    simp [Ty.exi_val_denot]
    exact capt_val_denot_is_monotonic henv T
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
        simp [hresolve1] at ht
        -- ht now says: Ty.capt_val_denot (env.extend_cvar CS) T m1 (var y)
        -- Use resolve_monotonic to show resolve m2.heap e = some (pack CS y)
        have hresolve2 : resolve m2.heap e = some (Exp.pack CS y) := by
          apply resolve_monotonic hmem hresolve1
        simp [hresolve2]
        -- Now need to show: Ty.capt_val_denot (env.extend_cvar CS) T m2 (var y)
        -- Use monotonicity of capt_val_denot
        have henv' : (env.extend_cvar CS).IsMonotonic := by
          constructor
          · intro X
            cases X with
            | there X' =>
              simp [TypeEnv.extend_cvar, TypeEnv.lookup_tvar, TypeEnv.lookup]
              exact henv.tvar X'
        exact capt_val_denot_is_monotonic henv' T hmem ht
      all_goals {
        -- resolve returned non-pack, so ht is False
        simp [hresolve1] at ht
      }

def capt_exp_denot_is_monotonic {env : TypeEnv s}
  (henv : env.IsMonotonic)
  (T : Ty .capt s) :
  ∀ {C : CapabilitySet} {m1 m2 : Memory} {e : Exp {}},
    Exp.WfInHeap e m1.heap ->
    m2.subsumes m1 ->
    (Ty.capt_exp_denot env T) C m1 e ->
    (Ty.capt_exp_denot env T) C m2 e := by
  intro C m1 m2 e hwf hmem ht
  simp [Ty.capt_exp_denot] at ht ⊢
  apply eval_monotonic
  · apply Denot.as_mpost_is_monotonic
    exact capt_val_denot_is_monotonic henv T
  · exact hmem
  · exact hwf
  · exact ht

def exi_exp_denot_is_monotonic {env : TypeEnv s}
  (henv : env.IsMonotonic)
  (T : Ty .exi s) :
  ∀ {C : CapabilitySet} {m1 m2 : Memory} {e : Exp {}},
    Exp.WfInHeap e m1.heap ->
    m2.subsumes m1 ->
    (Ty.exi_exp_denot env T) C m1 e ->
    (Ty.exi_exp_denot env T) C m2 e := by
  intro C m1 m2 e hwf hmem ht
  simp [Ty.exi_exp_denot] at ht ⊢
  apply eval_monotonic
  · apply Denot.as_mpost_is_monotonic
    exact exi_val_denot_is_monotonic henv T
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
          simp [EnvTyping] at ht ⊢
          have ⟨hproper, himply, ht'⟩ := ht
          constructor
          · exact hproper
          · constructor
            · intro C
              apply Denot.imply_after_subsumes (himply C) hmem
            · exact ih ht'
      | cvar B =>
        cases info with
        | cvar cs =>
          simp [EnvTyping] at ht ⊢
          have ⟨hwf, hwf_bound, hsub, ht'⟩ := ht
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
                rw [<-h_denot_eq, <-h_bound_eq]
                exact hsub
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

-- theorem denot_implyat_lift
--   (himp : (Ty.shape_val_denot env T1).ImplyAfter H (Ty.shape_val_denot env T2)) :
--   (Ty.capt_exp_denot env (.capt C T1)).ImplyAfter H (Ty.capt_exp_denot env (.capt C T2)) := by
--   intro A
--   intro H' hsub e h1
--   simp [Ty.capt_exp_denot] at h1 ⊢
--   apply eval_post_monotonic_general _ h1
--   apply Hpost.entails_after_subsumes <;> try exact hsub
--   simp [Ty.capt_val_denot]
--   intro h'' hsub' e' he'
--   apply (himp (C.denot env)) h'' hsub' e' he'

theorem shape_val_denot_is_reachability_safe {env : TypeEnv s}
  (hts : env.is_reachability_safe)
  (T : Ty .shape s) :
  (Ty.shape_val_denot env T).is_reachability_safe := by
  intro R m e hdenot
  cases T with
  | top =>
    -- For .top, the denotation already includes resolve_reachability m.heap e ⊆ R
    simp [Ty.shape_val_denot] at hdenot
    exact hdenot.2
  | tvar X =>
    -- For .tvar, use the hypothesis that env is reachability safe
    simp [Ty.shape_val_denot] at hdenot
    exact hts X R m e hdenot
  | unit =>
    -- For .unit, resolve_reachability returns empty set or reachability from heap
    simp [Ty.shape_val_denot] at hdenot
    -- hdenot : resolve m.heap e = some .unit
    -- Need: resolve_reachability m.heap e ⊆ R
    cases e with
    | unit =>
      simp [resolve_reachability]
      exact CapabilitySet.Subset.empty
    | var x =>
      cases x with
      | free fx =>
        simp [resolve_reachability]
        -- reachability_of_loc for unit values is empty
        simp [resolve] at hdenot
        cases hfx : m.heap fx <;> simp [hfx] at hdenot
        case some cell =>
          cases cell <;> simp at hdenot
          case val v =>
            cases hv : v.unwrap <;> simp [hv] at hdenot
            case unit =>
              -- For unit, reachability is v.reachability which should be empty
              simp [reachability_of_loc, hfx]
              -- Use heap invariant to show v.reachability = compute_reachability = {}
              have hinv := Memory.reachability_invariant m fx v (by simp [hfx])
              simp [hv] at hinv
              -- compute_reachability for unit is {}
              rw [hinv]
              simp [compute_reachability]
              exact CapabilitySet.Subset.empty
      | bound bx => cases bx
    | _ =>
      simp [resolve] at hdenot
  | cap =>
    -- For .cap, e is a variable pointing to a capability
    simp [Ty.shape_val_denot] at hdenot
    have ⟨label, heq, hcap, hmem⟩ := hdenot
    -- hdenot says: e = .var (.free label) ∧ label ∈ R
    rw [heq]
    simp [resolve_reachability]
    -- Need: reachability_of_loc m.heap label ⊆ R
    -- From hcap: m.lookup label = some .capability
    -- So: reachability_of_loc m.heap label = {label}
    have hcap' : m.heap label = some .capability := by
      simp [Memory.lookup] at hcap
      exact hcap
    simp [reachability_of_loc, hcap']
    -- Goal: {label} ⊆ R, which follows from label ∈ R
    exact CapabilitySet.mem_imp_singleton_subset hmem
  | arrow T1 T2 =>
    -- For arrow types, e resolves to an abstraction with capture set cs
    simp [Ty.shape_val_denot] at hdenot
    have ⟨cs, T0, t0, hres, hwf_cs, hR0_sub, _⟩ := hdenot
    -- Need: resolve_reachability m.heap e ⊆ R
    -- From hdenot: R0 = expand_captures m.heap cs and R0 ⊆ R
    cases e with
    | abs cs' T0' t0' =>
      simp [resolve, resolve_reachability] at hres ⊢
      obtain ⟨rfl, rfl, rfl⟩ := hres
      exact hR0_sub
    | var x =>
      cases x with
      | free fx =>
        simp [resolve] at hres
        cases hfx : m.heap fx with
        | none => simp [hfx] at hres
        | some cell =>
          simp [hfx] at hres
          cases cell with
          | capability => simp at hres
          | val v =>
            simp at hres
            cases hunwrap : v.unwrap <;> simp [hunwrap] at hres
            case abs cs' T0' t0' =>
              obtain ⟨rfl, rfl, rfl⟩ := hres
              -- Need: reachability_of_loc m.heap fx ⊆ R
              -- From heap invariant: reachability_of_loc m.heap fx = v.reachability
              -- And v.reachability = expand_captures m.heap cs' (for abs values)
              simp [resolve_reachability]
              have hv_heap : m.heap fx = some (Cell.val v) := hfx
              rw [reachability_of_loc_eq_resolve_reachability m fx v hv_heap]
              simp [resolve_reachability, hunwrap]
              exact hR0_sub
      | bound bx => cases bx
    | _ => simp [resolve] at hres
  | poly T1 T2 =>
    -- Similar to arrow case
    simp [Ty.shape_val_denot] at hdenot
    have ⟨cs, S0, t0, hres, hwf_cs, hR0_sub, _⟩ := hdenot
    cases e with
    | tabs cs' S0' t0' =>
      simp [resolve, resolve_reachability] at hres ⊢
      obtain ⟨rfl, rfl, rfl⟩ := hres
      exact hR0_sub
    | var x =>
      cases x with
      | free fx =>
        simp [resolve] at hres
        cases hfx : m.heap fx with
        | none => simp [hfx] at hres
        | some cell =>
          simp [hfx] at hres
          cases cell with
          | capability => simp at hres
          | val v =>
            simp at hres
            cases hunwrap : v.unwrap <;> simp [hunwrap] at hres
            case tabs cs' S0' t0' =>
              obtain ⟨rfl, rfl, rfl⟩ := hres
              simp [resolve_reachability]
              have hv_heap : m.heap fx = some (Cell.val v) := hfx
              rw [reachability_of_loc_eq_resolve_reachability m fx v hv_heap]
              simp [resolve_reachability, hunwrap]
              exact hR0_sub
      | bound bx => cases bx
    | _ => simp [resolve] at hres
  | cpoly B T =>
    -- Similar to arrow case
    simp [Ty.shape_val_denot] at hdenot
    have ⟨cs, B0, t0, hres, hwf_cs, hR0_sub, _⟩ := hdenot
    cases e with
    | cabs cs' B0' t0' =>
      simp [resolve, resolve_reachability] at hres ⊢
      obtain ⟨rfl, rfl, rfl⟩ := hres
      exact hR0_sub
    | var x =>
      cases x with
      | free fx =>
        simp [resolve] at hres
        cases hfx : m.heap fx with
        | none => simp [hfx] at hres
        | some cell =>
          simp [hfx] at hres
          cases cell with
          | capability => simp at hres
          | val v =>
            simp at hres
            cases hunwrap : v.unwrap <;> simp [hunwrap] at hres
            case cabs cs' B0' t0' =>
              obtain ⟨rfl, rfl, rfl⟩ := hres
              simp [resolve_reachability]
              have hv_heap : m.heap fx = some (Cell.val v) := hfx
              rw [reachability_of_loc_eq_resolve_reachability m fx v hv_heap]
              simp [resolve_reachability, hunwrap]
              exact hR0_sub
      | bound bx => cases bx
    | _ => simp [resolve] at hres

theorem shape_val_denot_is_reachability_monotonic {env : TypeEnv s}
  (hts : env.is_reachability_monotonic)
  (T : Ty .shape s) :
  (Ty.shape_val_denot env T).is_reachability_monotonic := by
  intro R1 R2 hsub m e hdenot
  cases T with
  | top =>
    simp [Ty.shape_val_denot] at hdenot ⊢
    constructor
    · exact hdenot.1
    · exact CapabilitySet.Subset.trans hdenot.2 hsub
  | tvar X =>
    -- For type variables, use the environment's reachability monotonicity
    simp [Ty.shape_val_denot] at hdenot ⊢
    exact hts X R1 R2 hsub m e hdenot
  | unit =>
    simp [Ty.shape_val_denot] at hdenot ⊢
    exact hdenot
  | cap =>
    simp [Ty.shape_val_denot] at hdenot ⊢
    have ⟨label, heq, hcap, hmem⟩ := hdenot
    exists label, heq, hcap
    exact CapabilitySet.subset_preserves_mem hsub hmem
  | arrow T1 T2 =>
    simp [Ty.shape_val_denot] at hdenot ⊢
    have ⟨cs, T0, t0, hres, hwf_cs, hR0_sub, hfun⟩ := hdenot
    exists cs, T0, t0, hres, hwf_cs
    constructor
    · exact CapabilitySet.Subset.trans hR0_sub hsub
    · exact hfun
  | poly T1 T2 =>
    simp [Ty.shape_val_denot] at hdenot ⊢
    have ⟨cs, T0, t0, hres, hwf_cs, hR0_sub, hfun⟩ := hdenot
    exists cs, T0, t0, hres, hwf_cs
    constructor
    · exact CapabilitySet.Subset.trans hR0_sub hsub
    · exact hfun
  | cpoly B T =>
    simp [Ty.shape_val_denot] at hdenot ⊢
    have ⟨cs, B0, t0, hres, hwf_cs, hR0_sub, hfun⟩ := hdenot
    exists cs, B0, t0, hres, hwf_cs
    constructor
    · exact CapabilitySet.Subset.trans hR0_sub hsub
    · exact hfun

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
      simp [resolve] at hresolve
      cases hfx : m.heap fx with
      | none => simp [hfx] at hresolve
      | some cell =>
        simp [hfx] at hresolve
        cases cell with
        | capability => simp at hresolve
        | val v =>
          simp at hresolve
          apply Exp.WfInHeap.wf_var
          apply Var.WfInHeap.wf_free
          exact hfx
    | bound bx => cases bx
  | unit =>
    apply Exp.WfInHeap.wf_unit
  | _ => simp [resolve] at hresolve

theorem resolve_implies_wf {m : Memory}
  (hres : resolve m.heap e = some hv) :
  e.WfInHeap m.heap := by
  cases e <;> try (solve | cases hres)
  case var x0 =>
    cases x0
    case bound b => cases b
    case free f => sorry
  all_goals sorry

theorem shape_val_denot_implies_wf {env : TypeEnv s}
  (hts : env.is_implying_wf)
  (T : Ty .shape s) :
  (Ty.shape_val_denot env T).implies_wf := by
  intro R m e hdenot
  cases T with
  | top =>
    simp [Ty.shape_val_denot] at hdenot
    exact hdenot.1
  | tvar X =>
    simp [Ty.shape_val_denot] at hdenot
    exact hts X R m e hdenot
  | unit =>
    simp [Ty.shape_val_denot] at hdenot
    exact wf_from_resolve_unit hdenot
  | cap =>
    simp [Ty.shape_val_denot] at hdenot
    have ⟨label, heq, hlookup, _⟩ := hdenot
    rw [heq]
    apply Exp.WfInHeap.wf_var
    apply Var.WfInHeap.wf_free
    simp [Memory.lookup] at hlookup
    exact hlookup
  | arrow T1 T2 =>
    simp [Ty.shape_val_denot] at hdenot
    have ⟨cs, T0, t0, hresolve, hwf_cs, _⟩ := hdenot
    apply resolve_implies_wf hresolve
  | poly T1 T2 =>
    simp [Ty.shape_val_denot] at hdenot
    have ⟨cs, S0, t0, hresolve, hwf_cs, _⟩ := hdenot
    apply resolve_implies_wf hresolve
  | cpoly B T =>
    simp [Ty.shape_val_denot] at hdenot
    have ⟨cs, B0, t0, hresolve, hwf_cs, _⟩ := hdenot
    apply resolve_implies_wf hresolve

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
      · -- Prove: ∀ C, ((Ty.shape_val_denot env S) C).is_proper
        intro C
        constructor
        · exact shape_val_denot_is_monotonic (typed_env_is_monotonic hts) S C
        · exact shape_val_denot_is_transparent (typed_env_is_transparent hts) S C

theorem capt_denot_implyafter_lift
  (himp : (Ty.capt_val_denot env T1).ImplyAfter H (Ty.capt_val_denot env T2)) :
  (Ty.capt_exp_denot env T1).ImplyAfter H (Ty.capt_exp_denot env T2) := by
  intro C m' hsub e heval
  simp [Ty.capt_exp_denot] at heval ⊢
  -- heval : Eval C m' e (capt_val_denot env T1).as_mpost
  -- Goal: Eval C m' e (capt_val_denot env T2).as_mpost
  apply eval_post_monotonic_general _ heval
  -- Need: (capt_val_denot env T1).as_mpost.entails_after m' (capt_val_denot env T2).as_mpost
  have himp' := Denot.imply_after_to_m_entails_after himp
  exact Mpost.entails_after_subsumes himp' hsub

theorem exi_denot_implyafter_lift
  (himp : (Ty.exi_val_denot env T1).ImplyAfter H (Ty.exi_val_denot env T2)) :
  (Ty.exi_exp_denot env T1).ImplyAfter H (Ty.exi_exp_denot env T2) := by
  intro C m' hsub e heval
  simp [Ty.exi_exp_denot] at heval ⊢
  -- heval : Eval C m' e (exi_val_denot env T1).as_mpost
  -- Goal: Eval C m' e (exi_val_denot env T2).as_mpost
  apply eval_post_monotonic_general _ heval
  -- Need: (exi_val_denot env T1).as_mpost.entails_after m' (exi_val_denot env T2).as_mpost
  have himp' := Denot.imply_after_to_m_entails_after himp
  exact Mpost.entails_after_subsumes himp' hsub

end CC
