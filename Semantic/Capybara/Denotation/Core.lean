import Semantic.Capybara.Semantics
import Semantic.Capybara.TypeSystem
import Semantic.Prelude

namespace Capybara

/-- Denotation of types. -/
def Denot := Memory -> Exp {} -> Prop

/-- Pre-denotation. It takes a capability to form a denotation. -/
def PreDenot := CapabilitySet -> Denot

/-- Capture-denotation. Given any memory, it produces a set of capabilities. -/
def CapDenot := Memory -> CapabilitySet

/-- A bound on capability sets. It can either be a concrete set of the top element. -/
inductive CapabilityBound : Type where
| top : Mutability -> CapabilityBound

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
  cases hv with
  | abs => rfl
  | tabs => rfl
  | cabs => rfl
  | unit => rfl
  | btrue => rfl
  | bfalse => rfl
  | reader =>
    rename_i x
    cases x with
    | free loc => rfl
    | bound bx => cases bx

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
  simp [hx]
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
  simp [Denot.as_mpost]
  exact hbool

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

/-- Type information for each kind of variable bindings in type context. -/
inductive TypeInfo : Sig -> Kind -> Type where
/-- Type information for a variable is a store location plus a peak set. -/
| var : Nat -> PeakSet s -> TypeInfo s .var
/-- Type information for a type variable is a pre-denotation. -/
| tvar : PreDenot -> TypeInfo s .tvar
/-- Type information for a capture variable is a ground capture set. -/
| cvar : CaptureSet {} -> TypeInfo s .cvar

inductive TypeEnv : Sig -> Type where
| empty : TypeEnv {}
| extend :
  TypeEnv s ->
  TypeInfo s k ->
  TypeEnv (s,,k)

def TypeEnv.extend_var (Γ : TypeEnv s) (x : Nat) (ps : PeakSet s) : TypeEnv (s,x) :=
  Γ.extend (.var x ps)

def TypeEnv.extend_tvar (Γ : TypeEnv s) (T : PreDenot) : TypeEnv (s,X) :=
  Γ.extend (.tvar T)

def TypeEnv.extend_cvar
  (Γ : TypeEnv s) (ground : CaptureSet {}) :
  TypeEnv (s,C) :=
  Γ.extend (.cvar ground)


def TypeEnv.lookup_var : (Γ : TypeEnv s) -> (x : BVar s .var) -> (Nat × PeakSet s)
| .extend _ (.var n ps), .here => (n, ps.rename Rename.succ)
| .extend Γ _, .there x =>
  match Γ.lookup_var x with
  | (n, ps) => (n, ps.rename Rename.succ)

def TypeEnv.lookup_tvar : (Γ : TypeEnv s) -> (x : BVar s .tvar) -> PreDenot
| .extend _ (.tvar T), .here => T
| .extend Γ _, .there x => Γ.lookup_tvar x

def TypeEnv.lookup_cvar : (Γ : TypeEnv s) -> (x : BVar s .cvar) -> CaptureSet {}
| .extend _ (.cvar cs), .here => cs
| .extend Γ _, .there x => Γ.lookup_cvar x

def Subst.from_TypeEnv (env : TypeEnv s) : Subst s {} where
  var := fun x => .free (env.lookup_var x).1
  tvar := fun _ => .top
  cvar := fun c => env.lookup_cvar c

theorem Subst.from_TypeEnv_empty :
  Subst.from_TypeEnv TypeEnv.empty = Subst.id := by
  apply Subst.funext
  · intro x; cases x
  · intro X; cases X
  · intro C; cases C

def compute_peaks (ρ : TypeEnv s) : CaptureSet s -> CaptureSet s
| .empty => .empty
| .union cs1 cs2 => (compute_peaks ρ cs1).union (compute_peaks ρ cs2)
| .cvar m c => .cvar m c
| .var m (.bound x) => (ρ.lookup_var x).2.cs.applyMut m
| .var _ (.free _) => .empty

theorem compute_peaks_is_peak (ρ : TypeEnv s) (cs : CaptureSet s)
  : (compute_peaks ρ cs).PeaksOnly := by
  induction cs with
  | empty =>
    simp [compute_peaks]
    constructor
  | union _ _ ih1 ih2 =>
    simp [compute_peaks]
    exact .union ih1 ih2
  | cvar =>
    simp [compute_peaks]
    constructor
  | var m x =>
    cases x
    case bound b =>
      simp [compute_peaks]
      exact (ρ.lookup_var b).2.h.applyMut m
    case free f =>
      simp [compute_peaks]
      constructor


def compute_peakset (ρ : TypeEnv s) (cs : CaptureSet s) : PeakSet s :=
  ⟨compute_peaks ρ cs, compute_peaks_is_peak ρ cs⟩

/-- Compute denotation for a ground capture set.
    Applies the mutability from each captured variable to the result. -/
def CaptureSet.ground_denot : CaptureSet {} -> CapDenot
| .empty => fun _ => {}
| .union cs1 cs2 => fun m =>
  (cs1.ground_denot m) ∪ (cs2.ground_denot m)
| .var m' (.free x) => fun m => (reachability_of_loc m.heap x).applyMut m'

def CaptureSet.denot (ρ : TypeEnv s) (cs : CaptureSet s) : CapDenot :=
  (cs.subst (Subst.from_TypeEnv ρ)).ground_denot

def Mutability.denot : Mutability -> CapBoundDenot
| m => fun _ => .top m

inductive CapabilitySet.BoundedBy : CapabilitySet -> CapabilityBound -> Prop where
| top :
  C.HasKind m ->
  CapabilitySet.BoundedBy C (.top m)

inductive CapabilityBound.SubsetEq : CapabilityBound -> CapabilityBound -> Prop where
| refl :
  CapabilityBound.SubsetEq B B
| top_top :
  m1 ≤ m2 ->
  CapabilityBound.SubsetEq (.top m1) (.top m2)

instance : HasSubset CapabilityBound where
  Subset := CapabilityBound.SubsetEq

theorem CapabilitySet.BoundedBy.trans
  {C : CapabilitySet} {B1 B2 : CapabilityBound}
  (hbound : CapabilitySet.BoundedBy C B1)
  (hsub : B1 ⊆ B2) :
  CapabilitySet.BoundedBy C B2 := by
  cases hsub with
  | refl => exact hbound
  | top_top hle =>
    cases hbound with
    | top hkind =>
      exact CapabilitySet.BoundedBy.top (CapabilitySet.HasKind.weaken hkind hle)


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
    A.covers .epsilon label
| _, .reader => fun A m e =>
  e.WfInHeap m.heap ∧
  ∃ (label : Nat) (b0 : Bool),
    resolve m.heap e = some (.reader (.free label)) ∧
    m.lookup label = some (.capability (.mcell b0)) ∧
    A.covers .ro label
| _, .bool => fun _ m e =>
  resolve m.heap e = some .btrue ∨ resolve m.heap e = some .bfalse
| _, .cell => fun R m e =>
  ∃ l b0,
    e = .var (.free l) ∧
    m.lookup l = some (.capability (.mcell b0)) ∧
    R.covers .epsilon l
| env, .arrow T1 T2 => fun A m e =>
  e.WfInHeap m.heap ∧
  ∃ cs T0 t0,
    resolve m.heap e = some (.abs cs T0 t0) ∧
    cs.WfInHeap m.heap ∧
    let R0 := expand_captures m.heap cs
    R0 ⊆ A ∧
    (∀ (arg : Nat) (ps : PeakSet s) (m' : Memory),
      m'.subsumes m ->
      Ty.capt_val_denot env T1 m' (.var (.free arg)) ->
      Ty.exi_exp_denot
        (env.extend_var arg ps)
        T2 (R0 ∪ (reachability_of_loc m'.heap arg)) m' (t0.subst (Subst.openVar (.free arg))))
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
      ((A0 m').BoundedBy (B.denot m')) ->
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
instance instMutabilityHasDenotation :
  HasDenotation Mutability Unit CapBoundDenot where
  interp := fun () m => m.denot

def EnvTyping : Ctx s -> TypeEnv s -> Memory -> Prop
| .empty, .empty, _ => True
| .push Γ (.var T), .extend env (.var n ps), m =>
  ⟦T⟧_[env] m (.var (.free n)) ∧
  ps = T.captureSet.peakset Γ ∧
  EnvTyping Γ env m
| .push Γ (.tvar S), .extend env (.tvar denot), m =>
  denot.is_proper ∧
  denot.ImplyAfter m ⟦S⟧_[env] ∧
  EnvTyping Γ env m
| .push Γ (.cvar B), .extend env (.cvar cs), m =>
  (cs.WfInHeap m.heap) ∧
  ((cs.ground_denot m).BoundedBy (B.denot m)) ∧
  EnvTyping Γ env m

theorem compute_peaks_correct (h : EnvTyping Γ ρ m) :
  ∀ C, CaptureSet.peaks Γ C = compute_peaks ρ C := by
  intro C
  induction C
  case empty => simp [CaptureSet.peaks, compute_peaks]
  case union ih1 ih2 => sorry
  case cvar m c => simp [CaptureSet.peaks, compute_peaks]
  case var m c => sorry

theorem compute_peakset_correct (h : EnvTyping Γ ρ m) :
  ∀ C, C.peakset Γ = compute_peakset ρ C := sorry

def SemanticTyping (C : CaptureSet s) (Γ : Ctx s) (e : Exp s) (E : Ty .exi s) : Prop :=
  ∀ ρ m,
    EnvTyping Γ ρ m ->
    ⟦E⟧e_[ρ] (C.denot ρ m) m (e.subst (Subst.from_TypeEnv ρ))

notation:65 C " # " Γ " ⊨ " e " : " T => SemanticTyping C Γ e T

theorem Subst.from_TypeEnv_weaken_open {env : TypeEnv s} {x : Nat} {ps : PeakSet s} :
  (Subst.from_TypeEnv env).lift.comp (Subst.openVar (.free x)) =
    Subst.from_TypeEnv (env.extend_var x ps) := by
  apply Subst.funext
  · intro y
    cases y with
    | here => rfl
    | there y' =>
      simp [Subst.from_TypeEnv, Subst.lift, Subst.comp, Subst.openVar,
        TypeEnv.extend_var, TypeEnv.lookup_var, Var.rename, Var.subst]
  · intro X
    cases X
    rfl
  · intro C
    cases C with
    | there C' =>
      simp [Subst.from_TypeEnv, Subst.lift, Subst.comp, Subst.openVar,
        TypeEnv.extend_var, TypeEnv.lookup_cvar]
      exact CaptureSet.weaken_openVar

theorem Exp.from_TypeEnv_weaken_open {e : Exp (s,x)} {ps : PeakSet s} :
  (e.subst (Subst.from_TypeEnv env).lift).subst (Subst.openVar (.free x)) =
    e.subst (Subst.from_TypeEnv (env.extend_var x ps)) := by
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
        TypeEnv.extend_tvar, TypeEnv.lookup_cvar]
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
    case here =>
      simp only [Subst.comp, Subst.lift, Subst.from_TypeEnv, Subst.openCVar,
        TypeEnv.extend_cvar, TypeEnv.lookup_cvar, CaptureSet.subst]
      rfl
    case there C' =>
      simp [Subst.comp, Subst.lift, Subst.from_TypeEnv, Subst.openCVar,
        TypeEnv.extend_cvar, TypeEnv.lookup_cvar]
      exact CaptureSet.weaken_openCVar

theorem Exp.from_TypeEnv_weaken_open_cvar
  {env : TypeEnv s} {cs : CaptureSet {}} {e : Exp (s,C)} :
  (e.subst (Subst.from_TypeEnv env).lift).subst (Subst.openCVar cs) =
    e.subst (Subst.from_TypeEnv (env.extend_cvar cs)) := by
  rw [Exp.subst_comp]
  rw [Subst.from_TypeEnv_weaken_open_cvar]

theorem Subst.from_TypeEnv_weaken_unpack {ps : PeakSet (s,C)} :
  (Subst.from_TypeEnv ρ).lift.lift.comp (Subst.unpack cs (.free x)) =
    Subst.from_TypeEnv ((ρ.extend_cvar cs).extend_var x ps) := by
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
        simp [Subst.from_TypeEnv, Var.rename, TypeEnv.extend_var, TypeEnv.extend_cvar,
          TypeEnv.lookup_var]
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
        rfl
      case there c0 =>
        -- LHS: comp maps .there (.there c0) through unpack then lift.lift
        simp [Subst.comp, Subst.unpack]
        rw [Subst.lift_there_cvar_eq]
        rw [Subst.lift_there_cvar_eq]
        -- Generalize before simplifying
        simp only [Subst.from_TypeEnv, TypeEnv.extend_var, TypeEnv.extend_cvar,
          TypeEnv.lookup_cvar]
        -- Now the goal has ρ.lookup_cvar c0 expanded to match expression
        -- Let's generalize this ground capture set
        generalize ρ.lookup_cvar c0 = ground_cs
        -- Goal: double rename + subst on ground_cs equals ground_cs
        induction ground_cs with
        | empty => rfl  -- .empty.rename.rename.subst = .empty
        | union cs1 cs2 ih1 ih2 =>
          -- .union case: distribute rename/subst over both sides
          simp only [CaptureSet.rename, CaptureSet.subst, ih1, ih2]
        | var m v =>
          cases v with
          | bound bv => cases bv  -- Impossible: no bound vars in {}
          | free n =>
            -- .var (.free n).rename.rename.subst = .var (.free n)
            rfl
        | cvar m cv => cases cv  -- Impossible: no capture vars in {}

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
        | var n ps =>
          unfold EnvTyping at htyping
          obtain ⟨htype, _, htyping'⟩ := htyping
          -- htype : ⟦T⟧_[ρ'] m (.var (.free n))
          cases T with
          | capt C S =>
            simp [instCaptHasDenotation, Ty.capt_val_denot] at htype
            have ⟨_, hwf, _, _⟩ := htype
            -- hwf : (.var (.free n)).WfInHeap m.heap
            cases hwf with
            | wf_var hwf_var =>
              -- hwf_var : Var.WfInHeap (.free n) m.heap
              have ih_wf := ih htyping'
              constructor
              · intro x
                cases x with
                | here =>
                  simp [Subst.from_TypeEnv, TypeEnv.lookup_var]
                  exact hwf_var
                | there x' =>
                  simp [Subst.from_TypeEnv, TypeEnv.lookup_var]
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
              simp [Subst.from_TypeEnv, TypeEnv.lookup_var]
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
          have ⟨hwf, hsub, htyping'⟩ := htyping
          have ih_wf := ih htyping'
          constructor
          · intro x
            cases x with
            | there x' =>
              simp [Subst.from_TypeEnv, TypeEnv.lookup_var]
              exact ih_wf.wf_var x'
          · intro X
            cases X with
            | there X' =>
              simp [Subst.from_TypeEnv]
              exact ih_wf.wf_tvar X'
          · intro C_var
            cases C_var with
            | here =>
              simp [Subst.from_TypeEnv, TypeEnv.lookup_cvar]
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
        | var n ps =>
          simp [EnvTyping] at ht
          obtain ⟨_, _, ht'⟩ := ht
          have ih_result := ih ht'
          constructor
          · intro x
            cases x with
            | there x =>
              simp [TypeEnv.lookup_tvar]
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
              simp [TypeEnv.lookup_tvar]
              -- hproper says d.is_proper
              -- We need d.is_monotonic
              intro C
              exact (hproper.2.2.2.2 C).1
            | there x =>
              simp [TypeEnv.lookup_tvar]
              exact ih_result.tvar x
      | cvar B =>
        cases info with
        | cvar cs =>
          simp [EnvTyping] at ht
          have ⟨hwf, hsub, ht'⟩ := ht
          have ih_result := ih ht'
          constructor
          · intro x
            cases x with
            | there x =>
              simp [TypeEnv.lookup_tvar]
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
        | var n ps =>
          simp [EnvTyping] at ht
          obtain ⟨_, _, ht'⟩ := ht
          have ih_result := ih ht'
          simp [TypeEnv.is_transparent] at ih_result ⊢
          intro x
          cases x with
          | there x =>
            simp [TypeEnv.lookup_tvar]
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
            simp [TypeEnv.lookup_tvar]
            -- hproper says d.is_proper
            -- We need d.is_transparent
            intro C
            exact (hproper.2.2.2.2 C).2.1
          | there x =>
            simp [TypeEnv.lookup_tvar]
            exact ih_result x
      | cvar B =>
        cases info with
        | cvar cs =>
          simp [EnvTyping] at ht
          have ⟨hwf, hsub, ht'⟩ := ht
          have ih_result := ih ht'
          simp [TypeEnv.is_transparent] at ih_result ⊢
          intro x
          cases x with
          | there x =>
            simp [TypeEnv.lookup_tvar]
            exact ih_result x

theorem typed_env_is_bool_independent
  (ht : EnvTyping Γ env mem) :
  env.is_bool_independent := by
  induction Γ with
  | empty =>
    cases env with
    | empty =>
      simp [TypeEnv.is_bool_independent]
      intro x
      cases x
  | push Γ k ih =>
    cases env with
    | extend env' info =>
      cases k with
      | var T =>
        cases info with
        | var n ps =>
          simp [EnvTyping] at ht
          obtain ⟨_, _, ht'⟩ := ht
          have ih_result := ih ht'
          simp [TypeEnv.is_bool_independent] at ih_result ⊢
          intro x
          cases x with
          | there x =>
            simp [TypeEnv.lookup_tvar]
            exact ih_result x
      | tvar S =>
        cases info with
        | tvar d =>
          simp [EnvTyping] at ht
          have ⟨hproper, _, ht'⟩ := ht
          have ih_result := ih ht'
          simp [TypeEnv.is_bool_independent] at ih_result ⊢
          intro x
          cases x with
          | here =>
            simp [TypeEnv.lookup_tvar]
            -- hproper says d.is_proper
            -- We need d.is_bool_independent
            intro C
            exact (hproper.2.2.2.2 C).2.2
          | there x =>
            simp [TypeEnv.lookup_tvar]
            exact ih_result x
      | cvar B =>
        cases info with
        | cvar cs =>
          simp [EnvTyping] at ht
          have ⟨hwf, hsub, ht'⟩ := ht
          have ih_result := ih ht'
          simp [TypeEnv.is_bool_independent] at ih_result ⊢
          intro x
          cases x with
          | there x =>
            simp [TypeEnv.lookup_tvar]
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
        | var n ps =>
          simp [EnvTyping] at ht
          obtain ⟨_, _, ht'⟩ := ht
          have ih_result := ih ht'
          simp [TypeEnv.is_reachability_safe] at ih_result ⊢
          intro x
          cases x with
          | there x =>
            simp [TypeEnv.lookup_tvar]
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
            simp [TypeEnv.lookup_tvar]
            -- hproper says d.is_proper, which is d.is_reachability_safe ∧ ∀ C, (d C).is_proper
            -- We need d.is_reachability_safe
            exact hproper.1
          | there x =>
            simp [TypeEnv.lookup_tvar]
            exact ih_result x
      | cvar B =>
        cases info with
        | cvar cs =>
          simp [EnvTyping] at ht
          have ⟨hwf, hsub, ht'⟩ := ht
          have ih_result := ih ht'
          simp [TypeEnv.is_reachability_safe] at ih_result ⊢
          intro x
          cases x with
          | there x =>
            simp [TypeEnv.lookup_tvar]
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
        | var n ps =>
          simp [EnvTyping] at ht
          obtain ⟨_, _, ht'⟩ := ht
          have ih_result := ih ht'
          simp [TypeEnv.is_reachability_monotonic] at ih_result ⊢
          intro x
          cases x with
          | there x =>
            simp [TypeEnv.lookup_tvar]
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
            simp [TypeEnv.lookup_tvar]
            -- hproper says d.is_proper
            -- We need d.is_reachability_monotonic, which is hproper.2.1
            exact hproper.2.1
          | there x =>
            simp [TypeEnv.lookup_tvar]
            exact ih_result x
      | cvar B =>
        cases info with
        | cvar cs =>
          simp [EnvTyping] at ht
          have ⟨hwf, hsub, ht'⟩ := ht
          have ih_result := ih ht'
          simp [TypeEnv.is_reachability_monotonic] at ih_result ⊢
          intro x
          cases x with
          | there x =>
            simp [TypeEnv.lookup_tvar]
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
        | var n ps =>
          simp [EnvTyping] at ht
          obtain ⟨_, _, ht'⟩ := ht
          have ih_result := ih ht'
          simp [TypeEnv.is_implying_wf] at ih_result ⊢
          intro x
          cases x with
          | there x =>
            simp [TypeEnv.lookup_tvar]
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
            simp [TypeEnv.lookup_tvar]
            -- hproper says d.is_proper
            -- We need d.implies_wf
            exact hproper.2.2.1
          | there x =>
            simp [TypeEnv.lookup_tvar]
            exact ih_result x
      | cvar B =>
        cases info with
        | cvar cs =>
          simp [EnvTyping] at ht
          have ⟨hwf, hsub, ht'⟩ := ht
          have ih_result := ih ht'
          simp [TypeEnv.is_implying_wf] at ih_result ⊢
          intro x
          cases x with
          | there x =>
            simp [TypeEnv.lookup_tvar]
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
        | var n ps =>
          simp [EnvTyping] at ht
          obtain ⟨_, _, ht'⟩ := ht
          have ih_result := ih ht'
          intro X
          cases X with
          | there X' =>
            simp [TypeEnv.lookup_tvar]
            exact ih_result X'
      | tvar S =>
        cases info with
        | tvar d =>
          simp [EnvTyping] at ht
          have ⟨hproper, _, ht'⟩ := ht
          have ih_result := ih ht'
          intro X
          cases X with
          | here =>
            simp [TypeEnv.lookup_tvar]
            -- hproper says d.is_proper
            -- We need d.is_tight
            exact hproper.2.2.2.1
          | there X' =>
            simp [TypeEnv.lookup_tvar]
            exact ih_result X'
      | cvar B =>
        cases info with
        | cvar cs =>
          simp [EnvTyping] at ht
          have ⟨_, _, ht'⟩ := ht
          have ih_result := ih ht'
          intro X
          cases X with
          | there X' =>
            simp [TypeEnv.lookup_tvar]
            exact ih_result X'

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
    have ⟨_, label, hlabel, hcap, hmem⟩ := ht
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
    -- Destructure the heap value to access its components
    cases v with
    | mk vexp hv_simple hreach =>
      -- rewrite the lookup in terms of the heap
      have hlookup : m.heap x = some (Cell.val ⟨vexp, hv_simple, hreach⟩) := by
        simpa [Memory.lookup] using hx
      have hres_self : resolve m.heap vexp = some vexp := by
        cases hv_simple <;> simp [resolve]
      -- From the denotation, vexp must be a boolean literal
      have hbool : vexp = .btrue ∨ vexp = .bfalse := by
        simpa [Ty.shape_val_denot, hres_self] using ht
      -- Finish by rewriting with hbool
      cases hbool with
      | inl hb =>
        simp [Ty.shape_val_denot, resolve, hlookup, hb]
      | inr hb =>
        simp [Ty.shape_val_denot, resolve, hlookup, hb]
  | cell =>
    intro C m x v hx ht
    simp only [Ty.shape_val_denot] at ht ⊢
    obtain ⟨l, b0, heq, hlookup_and_mem⟩ := ht
    -- v.unwrap = .var (.free l), but v.isVal says it's a simple value
    -- Variables are not simple values, so this is a contradiction
    have hval := v.isVal
    rw [heq] at hval
    cases hval
  | reader =>
    intro C m x v hx ht
    simp only [Ty.shape_val_denot] at ht ⊢
    obtain ⟨hwf, label, b0, hres, hlookup, hcov⟩ := ht
    have hx' : m.heap x = some (.val v) := by
      simp [Memory.lookup] at hx
      exact hx
    have heq := resolve_var_heap_trans hx'
    rw [heq]
    refine ⟨?_, label, b0, hres, hlookup, hcov⟩
    -- Prove (Exp.var (Var.free x)).WfInHeap m.heap
    constructor
    constructor
    exact hx'
  | poly T1 T2 =>
    intro C m x v hx ht
    simp [Ty.shape_val_denot] at ht ⊢
    have hx' : m.heap x = some (.val v) := by
      simp [Memory.lookup] at hx
      exact hx
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
    simp [Ty.shape_val_denot] at ht ⊢
    have hx' : m.heap x = some (.val v) := by
      simp [Memory.lookup] at hx
      exact hx
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
    simp [Ty.shape_val_denot, resolve_reachability]
    intro _
    constructor <;> intro
    · apply Exp.WfInHeap.wf_bfalse
    · apply Exp.WfInHeap.wf_btrue
  | tvar X =>
    simp [Ty.shape_val_denot]
    exact henv X C
  | unit =>
    simp [Ty.shape_val_denot, resolve]
  | cap =>
    simp [Ty.shape_val_denot]
  | bool =>
    simp [Ty.shape_val_denot, resolve]
  | cell =>
    simp [Ty.shape_val_denot]
  | reader =>
    -- btrue and bfalse cannot resolve to a reader, so both sides are False
    simp [Ty.shape_val_denot, resolve]
  | arrow T1 T2 =>
    simp [Ty.shape_val_denot, resolve]
  | poly T1 T2 =>
    simp [Ty.shape_val_denot, resolve]
  | cpoly B T =>
    simp [Ty.shape_val_denot, resolve]

theorem capt_val_denot_is_transparent {env : TypeEnv s}
  (henv : TypeEnv.is_transparent env)
  (T : Ty .capt s) :
  (Ty.capt_val_denot env T).is_transparent := by
  cases T with
  | capt C S =>
    intro m x v hx ht
    simp [Ty.capt_val_denot] at ht ⊢
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
      | some (.pack CS x) =>
        CS.WfInHeap m.heap ∧ Ty.capt_val_denot (env.extend_cvar CS) T m (.var x)
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
    unfold CaptureSet.ground_denot
    rfl
  | union cs1 cs2 ih1 ih2 =>
    -- Union: use IH on both components
    unfold CaptureSet.ground_denot
    simp at hwf
    cases hwf with
    | wf_union hwf1 hwf2 =>
      rw [ih1 hwf1, ih2 hwf2]
  | var m v =>
    cases v with
    | bound x => cases x  -- No bound variables in empty signature
    | free x =>
      -- Free variable: use reachability_of_loc_monotonic
      unfold CaptureSet.ground_denot
      simp at hwf
      cases hwf with
      | wf_var_free hex =>
        exact congrArg (CapabilitySet.applyMut m) (reachability_of_loc_monotonic hsub x hex).symm
  | cvar m c => cases c  -- No capture variables in empty signature

theorem capture_set_denot_is_monotonic {C : CaptureSet s} :
  (C.denot ρ).is_monotonic_for (C.subst (Subst.from_TypeEnv ρ)) := by
  unfold CapDenot.is_monotonic_for
  intro m1 m2 hwf hsub
  induction C with
  | empty =>
    -- Empty set denotes {} at all memories
    unfold CaptureSet.denot
    simp [CaptureSet.subst, CaptureSet.ground_denot]
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
  | var m v =>
    cases v with
    | bound x =>
      -- Bound variable: after substitution becomes free variable
      unfold CaptureSet.denot
      simp [CaptureSet.subst, Subst.from_TypeEnv] at hwf
      simp [CaptureSet.subst, Subst.from_TypeEnv]
      unfold CaptureSet.ground_denot
      cases hwf with
      | wf_var_free hex =>
        -- hex : m1.heap (ρ.lookup_var x).1 = some _
        -- Memory.lookup is definitionally equal to heap access
        have h := reachability_of_loc_monotonic hsub (ρ.lookup_var x).1 hex
        exact congrArg (CapabilitySet.applyMut m) h.symm
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
        exact congrArg (CapabilitySet.applyMut m) (reachability_of_loc_monotonic hsub x hex).symm
  | cvar m c =>
    -- Capture variable: after substitution becomes ground capture set
    unfold CaptureSet.denot
    simp [CaptureSet.subst, Subst.from_TypeEnv]
    -- Need: (ρ.lookup_cvar c).ground_denot m1 = (ρ.lookup_cvar c).ground_denot m2
    -- This follows from ground_denot_is_monotonic
    exact ground_denot_is_monotonic hwf hsub

/-- ground_denot of applyRO is a subset: C.applyRO.ground_denot m ⊆ C.ground_denot m -/
theorem ground_denot_applyRO_subset {C : CaptureSet {}} {m : Memory} :
  C.applyRO.ground_denot m ⊆ C.ground_denot m := by
  induction C with
  | empty =>
    simp only [CaptureSet.applyRO, CaptureSet.ground_denot]
    exact CapabilitySet.Subset.refl
  | union C1 C2 ih1 ih2 =>
    simp only [CaptureSet.applyRO, CaptureSet.ground_denot]
    apply CapabilitySet.Subset.union_left
    · exact CapabilitySet.Subset.trans ih1 CapabilitySet.Subset.union_right_left
    · exact CapabilitySet.Subset.trans ih2 CapabilitySet.Subset.union_right_right
  | var m' v =>
    cases v with
    | bound x => cases x
    | free x =>
      simp only [CaptureSet.applyRO, CaptureSet.ground_denot]
      exact CapabilitySet.applyRO_subset_applyMut
  | cvar m' c => cases c

/-- Key lemma: (C.ground_denot m).applyRO = C.applyRO.ground_denot m -/
theorem ground_denot_applyRO_comm {C : CaptureSet {}} {m : Memory} :
  (C.ground_denot m).applyRO = C.applyRO.ground_denot m := by
  induction C with
  | empty => rfl
  | union C1 C2 ih1 ih2 =>
    simp only [CaptureSet.applyRO, CaptureSet.ground_denot, CapabilitySet.applyRO, ih1, ih2]
    rfl
  | var m' v =>
    cases v with
    | bound x => cases x
    | free x =>
      simp only [CaptureSet.applyRO, CaptureSet.ground_denot]
      -- LHS: ((reachability_of_loc m.heap x).applyMut m').applyRO
      -- RHS: (reachability_of_loc m.heap x).applyMut .ro = (reachability_of_loc m.heap x).applyRO
      cases m' <;> simp [CapabilitySet.applyMut, CapabilitySet.applyRO_applyRO]
  | cvar m' c => cases c

/-- ground_denot of applyRO is monotonic: if C1 ⊆ C2 then C1.applyRO ⊆ C2.applyRO -/
theorem ground_denot_applyRO_mono {C1 C2 : CaptureSet {}} {m : Memory}
  (hsub : C1.ground_denot m ⊆ C2.ground_denot m) :
  C1.applyRO.ground_denot m ⊆ C2.applyRO.ground_denot m := by
  rw [← ground_denot_applyRO_comm, ← ground_denot_applyRO_comm]
  exact CapabilitySet.applyRO_mono hsub

theorem mutability_denot_is_monotonic {B : Mutability} :
  B.denot m1 = B.denot m2 := by
  -- Mutability denotes .top at all memories, so trivially monotonic
  rfl

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
          obtain ⟨v', hv', hsub_v⟩ := hsub fx v hres
          -- For value cells, subsumption requires equality
          cases v with
          | val val_v =>
            simp [Cell.subsumes] at hsub_v
            subst hsub_v
            simpa [hv'] using ht
          | capability _ => cases ht
          | masked => cases ht
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
    | btrue => simp [resolve] at ht
    | bfalse => simp [resolve] at ht
    | read _ => simp [resolve] at ht
    | write _ _ => simp [resolve] at ht
    | cond _ _ _ => simp [resolve] at ht
    | par _ _ => simp [resolve] at ht
    | reader _ => simp [resolve] at ht
  | cap =>
    intro m1 m2 e hmem ht
    simp [Ty.shape_val_denot] at ht ⊢
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
          simp [Cell.subsumes] at hsub_c
          subst hsub_c
          simp [Memory.lookup]
          exact hc'
        · exact hmemin
  | bool =>
    intro m1 m2 e hmem ht
    simp [Ty.shape_val_denot] at ht ⊢
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
    simp [Memory.lookup] at hlookup
    obtain ⟨c', hc', hsub_c⟩ := hsub l (Cell.capability (.mcell b0)) hlookup
    -- For mcell capability cells, subsumption is always True (mcell subsumes mcell)
    cases c' with
    | val v => simp [Cell.subsumes] at hsub_c
    | masked => simp [Cell.subsumes] at hsub_c
    | capability info =>
      cases info with
      | basic => simp [Cell.subsumes] at hsub_c
      | mcell b' =>
        -- Cell.subsumes says mcell-to-mcell is True
        -- The boolean value b' might differ from b0, which is fine
        refine ⟨l, b', heq, ?_, hmem_l⟩
        simp [Memory.lookup]
        exact hc'
  | reader =>
    intro m1 m2 e hmem ht
    simp only [Ty.shape_val_denot] at ht ⊢
    obtain ⟨hwf_e, label, b0, hres, hlookup, hcov⟩ := ht
    constructor
    · exact Exp.wf_monotonic hmem hwf_e
    · -- The mcell at label may have a different boolean in m2
      have hsub : m2.heap.subsumes m1.heap := hmem
      simp [Memory.lookup] at hlookup
      obtain ⟨c', hc', hsub_c⟩ := hsub label (Cell.capability (.mcell b0)) hlookup
      cases c' with
      | val v => simp [Cell.subsumes] at hsub_c
      | masked => simp [Cell.subsumes] at hsub_c
      | capability info =>
        cases info with
        | basic => simp [Cell.subsumes] at hsub_c
        | mcell b' =>
          refine ⟨label, b', ?_, ?_, hcov⟩
          · exact resolve_monotonic hmem hres
          · simp [Memory.lookup]; exact hc'
  | arrow T1 T2 =>
    intro m1 m2 e hmem ht
    simp [Ty.shape_val_denot] at ht ⊢
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
            simp [resolve] at hr ⊢
            split at hr <;> try (cases hr)
            rename_i v heq
            have hsub : m2.heap.subsumes m1.heap := hmem
            obtain ⟨v', hv', hsub_v⟩ := hsub fx (Cell.val v) heq
            -- For value cells, subsumption requires equality
            simp [Cell.subsumes] at hsub_v
            subst hsub_v
            simp [hv', hr]
          | bound bx => cases bx
        | abs _ _ _ => simp [resolve] at hr ⊢; exact hr
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
        | par _ _ => cases hr
        | reader _ => cases hr
      · constructor
        · exact CaptureSet.wf_monotonic hmem hwf_cs
        · constructor
          · -- Prove: expand_captures m2.heap cs ⊆ C
            have heq := expand_captures_monotonic hmem cs hwf_cs
            rw [heq]
            exact hR0_sub
          · intro arg ps m' hs' harg
            have hs0 := Memory.subsumes_trans hs' hmem
            -- Use convert with expand_captures monotonicity
            have heq' := expand_captures_monotonic hmem cs hwf_cs
            convert hfun arg ps m' hs0 harg using 2
  | poly T1 T2 =>
    intro m1 m2 e hmem ht
    simp [Ty.shape_val_denot] at ht ⊢
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
            simp [resolve] at hr ⊢
            split at hr <;> try (cases hr)
            rename_i v heq
            have hsub : m2.heap.subsumes m1.heap := hmem
            obtain ⟨v', hv', hsub_v⟩ := hsub fx (Cell.val v) heq
            -- For value cells, subsumption requires equality
            simp [Cell.subsumes] at hsub_v
            subst hsub_v
            simp [hv', hr]
          | bound bx => cases bx
        | tabs _ _ _ => simp [resolve] at hr ⊢; exact hr
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
        | par _ _ => cases hr
        | reader _ => cases hr
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
                  simp [TypeEnv.extend_tvar, TypeEnv.lookup_tvar]
                  intro C
                  exact (hdenot_proper.2.2.2.2 C).1
                | there X' =>
                  simp [TypeEnv.extend_tvar, TypeEnv.lookup_tvar]
                  exact henv.tvar X'
            -- Use convert with expand_captures monotonicity
            have heq' := expand_captures_monotonic hmem cs hwf_cs
            convert hfun m' denot (Memory.subsumes_trans msub hmem) hdenot_proper himply using 2
  | cpoly B T =>
    intro m1 m2 e hmem ht
    simp [Ty.shape_val_denot] at ht ⊢
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
            simp [resolve] at hr ⊢
            split at hr <;> try (cases hr)
            rename_i v heq
            have hsub : m2.heap.subsumes m1.heap := hmem
            obtain ⟨v', hv', hsub_v⟩ := hsub fx (Cell.val v) heq
            -- For value cells, subsumption requires equality
            simp [Cell.subsumes] at hsub_v
            subst hsub_v
            simp [hv', hr]
          | bound bx => cases bx
        | cabs _ _ _ => simp [resolve] at hr ⊢; exact hr
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
        | par _ _ => cases hr
        | reader _ => cases hr
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
        -- ht now says: CS.WfInHeap m1.heap ∧ Ty.capt_val_denot (env.extend_cvar CS) T m1 (var y)
        obtain ⟨hwf_CS_m1, ht_body⟩ := ht
        -- Use resolve_monotonic to show resolve m2.heap e = some (pack CS y)
        have hresolve2 : resolve m2.heap e = some (Exp.pack CS y) := by
          apply resolve_monotonic hmem hresolve1
        simp [hresolve2]
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
                simp [TypeEnv.extend_cvar, TypeEnv.lookup_tvar]
                exact henv.tvar X'
          exact capt_val_denot_is_monotonic henv' T hmem ht_body
      all_goals {
        -- resolve returned non-pack, so ht is False
        simp [hresolve1] at ht
      }

def capt_val_denot_is_bool_independent {env : TypeEnv s}
  (henv : TypeEnv.is_bool_independent env)
  (T : Ty .capt s) :
  (Ty.capt_val_denot env T).is_bool_independent := by
  cases T with
  | capt C S =>
    intro m
    simp [Ty.capt_val_denot]
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
    simp [Ty.exi_val_denot]
    exact capt_val_denot_is_bool_independent henv T
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
  simp [Ty.capt_exp_denot] at ht ⊢
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
  simp [Ty.exi_exp_denot] at ht ⊢
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
        | var n ps =>
          -- Unfold EnvTyping to get the conjunction
          unfold EnvTyping at ht ⊢
          obtain ⟨hval, hps, ht'⟩ := ht
          constructor
          · -- Prove: ⟦T⟧_[env', φ] mem2 (.var (.free n))
            have henv := typed_env_is_monotonic ht'
            exact capt_val_denot_is_monotonic henv T hmem hval
          · -- Prove: peakset consistency and EnvTyping Γ env' mem2
            constructor
            · simpa using hps
            · exact ih ht'
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
          have ⟨hwf, hsub, ht'⟩ := ht
          constructor
          · -- Prove: cs.WfInHeap mem2.heap
            exact CaptureSet.wf_monotonic hmem hwf
          · constructor
            · -- Need: cs.ground_denot mem2 ⊆ B.denot mem2
              -- Have: cs.ground_denot mem1 ⊆ B.denot mem1
              -- Get cs.ground_denot mem1 = cs.ground_denot mem2
              have h_denot_eq := ground_denot_is_monotonic hwf hmem
              -- Get B.denot mem1 = B.denot mem2 (trivially true for Mutability)
              have h_bound_eq : B.denot mem1 = B.denot mem2 :=
                mutability_denot_is_monotonic
              -- Combine the equalities
              rw [<-h_denot_eq, <-h_bound_eq]
              exact hsub
            · exact ih ht'

/-- Semantic subcapturing. -/
def SemSubcapt (Γ : Ctx s) (C1 C2 : CaptureSet s) : Prop :=
  ∀ env m,
    EnvTyping Γ env m ->
    C1.denot env m ⊆ C2.denot env m

def SemHasKind (Γ : Ctx s) (C : CaptureSet s) (mode : Mutability) : Prop :=
  ∀ env m,
    EnvTyping Γ env m ->
    CapabilitySet.HasKind (C.denot env m) mode

def SemSubbound (_Γ : Ctx s) (B1 B2 : Mutability) : Prop :=
  ∀ m,
    B1.denot m ⊆ B2.denot m

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
    simp [Ty.shape_val_denot] at hdenot
    exact hdenot.2
  | tvar X =>
    -- For .tvar, use the hypothesis that env is reachability safe
    simp [Ty.shape_val_denot] at hdenot
    exact hts X R m e hdenot
  | bool =>
    simp [Ty.shape_val_denot] at hdenot
    cases e with
    | btrue =>
      -- Bool literals have empty reachability
      simp [resolve_reachability]
      exact CapabilitySet.Subset.empty
    | bfalse =>
      simp [resolve_reachability]
      exact CapabilitySet.Subset.empty
    | var x =>
      cases x with
      | bound bx => cases bx
      | free fx =>
        -- The heap cell for fx must contain a boolean value
        cases hcell : m.heap fx with
        | none =>
          simp [resolve, hcell] at hdenot
        | some cell =>
          cases cell with
          | capability =>
            simp [resolve, hcell] at hdenot
          | masked =>
            simp [resolve, hcell] at hdenot
          | val hv =>
            cases hv with
            | mk vexp hv_simple hreach_val =>
              have hreach :=
                Memory.reachability_invariant m fx ⟨vexp, hv_simple, hreach_val⟩
                  (by simp [hcell])
              cases hv_simple with
              | abs =>
                simp [resolve, hcell] at hdenot ⊢
              | tabs =>
                simp [resolve, hcell] at hdenot ⊢
              | cabs =>
                simp [resolve, hcell] at hdenot ⊢
              | unit =>
                simp [resolve, hcell] at hdenot ⊢
              | btrue =>
                have hreach_empty : hreach_val = {} := by
                  simpa [compute_reachability] using hreach
                simp [resolve_reachability, reachability_of_loc, hcell, hreach_empty]
                exact CapabilitySet.Subset.empty
              | bfalse =>
                have hreach_empty : hreach_val = {} := by
                  simpa [compute_reachability] using hreach
                simp [resolve_reachability, reachability_of_loc, hcell, hreach_empty]
                exact CapabilitySet.Subset.empty
              | reader =>
                simp [resolve, hcell] at hdenot ⊢
    | _ =>
      -- Other expressions cannot resolve to a boolean
      simp [resolve] at hdenot
  | cell =>
    simp only [Ty.shape_val_denot] at hdenot
    obtain ⟨l, b0, heq, hlookup, hmem⟩ := hdenot
    -- e is a variable pointing to an mcell capability
    rw [heq]
    simp [resolve_reachability]
    -- reachability_of_loc m.heap l = {l} for mcell capabilities
    have hlookup' : m.heap l = some (Cell.capability (.mcell b0)) := by
      simp [Memory.lookup] at hlookup
      exact hlookup
    simp [reachability_of_loc, hlookup']
    -- Goal: singleton .epsilon l ⊆ R, which follows from R.covers .epsilon l
    exact CapabilitySet.covers_eps_imp_singleton_eps_subset hmem
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
  | reader =>
    -- For .reader, e resolves to a reader pointing to a location with an mcell
    simp only [Ty.shape_val_denot] at hdenot
    obtain ⟨hwf_e, label, b0, hres, hlookup, hcov⟩ := hdenot
    -- resolve_reachability for a reader value is singleton .ro label
    -- Need: resolve_reachability m.heap e ⊆ R
    cases e with
    | reader x =>
      cases x with
      | free loc =>
        simp [resolve] at hres
        obtain ⟨rfl⟩ := hres
        simp [resolve_reachability]
        exact CapabilitySet.covers_imp_singleton_subset hcov
      | bound bx => cases bx
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
          | masked => simp at hres
          | val v =>
            simp at hres
            cases hunwrap : v.unwrap <;> simp [hunwrap] at hres
            case reader x =>
              cases x with
              | free loc =>
                obtain ⟨rfl⟩ := hres
                simp [resolve_reachability]
                have hv_heap : m.heap fx = some (Cell.val v) := hfx
                rw [reachability_of_loc_eq_resolve_reachability m fx v hv_heap]
                simp [resolve_reachability, hunwrap]
                exact CapabilitySet.covers_imp_singleton_subset hcov
              | bound bx => cases bx
      | bound bx => cases bx
    | _ => cases hres
  | cap =>
    -- For .cap, e is a variable pointing to a capability
    simp [Ty.shape_val_denot] at hdenot
    have ⟨hwf_e, label, heq, hcap, hmem⟩ := hdenot
    -- hdenot says: e = .var (.free label) ∧ label ∈ R
    rw [heq]
    simp [resolve_reachability]
    -- Need: reachability_of_loc m.heap label ⊆ R
    -- From hcap: m.lookup label = some (Cell.capability .basic)
    -- So: reachability_of_loc m.heap label = {label}
    have hcap' : m.heap label = some (Cell.capability .basic) := by
      simp [Memory.lookup] at hcap
      exact hcap
    simp [reachability_of_loc, hcap']
    -- Goal: singleton .epsilon label ⊆ R, which follows from R.covers .epsilon label
    exact CapabilitySet.covers_eps_imp_singleton_eps_subset hmem
  | arrow T1 T2 =>
    -- For arrow types, e resolves to an abstraction with capture set cs
    simp [Ty.shape_val_denot] at hdenot
    have ⟨hwf_e, cs, T0, t0, hres, hwf_cs, hR0_sub, _⟩ := hdenot
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
          | masked => simp at hres
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
    | _ => cases hres
  | poly T1 T2 =>
    -- Similar to arrow case
    simp [Ty.shape_val_denot] at hdenot
    have ⟨hwf_e, cs, S0, t0, hres, hwf_cs, hR0_sub, _⟩ := hdenot
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
          | masked => simp at hres
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
    | _ => cases hres
  | cpoly B T =>
    -- Similar to arrow case
    simp [Ty.shape_val_denot] at hdenot
    have ⟨hwf_e, cs, B0, t0, hres, hwf_cs, hR0_sub, _⟩ := hdenot
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
          | masked => simp at hres
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
    | _ => cases hres

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
  | bool =>
    simp [Ty.shape_val_denot] at hdenot ⊢
    exact hdenot
  | cell =>
    simp only [Ty.shape_val_denot] at hdenot ⊢
    obtain ⟨l, b0, heq, hlookup, hmem⟩ := hdenot
    use l, b0
    exact ⟨heq, hlookup, CapabilitySet.subset_preserves_covers hsub hmem⟩
  | reader =>
    simp only [Ty.shape_val_denot] at hdenot ⊢
    obtain ⟨hwf_e, label, b0, hres, hlookup, hcov⟩ := hdenot
    constructor
    · exact hwf_e
    · use label, b0
      exact ⟨hres, hlookup, CapabilitySet.subset_preserves_covers hsub hcov⟩
  | unit =>
    simp [Ty.shape_val_denot] at hdenot ⊢
    exact hdenot
  | cap =>
    simp [Ty.shape_val_denot] at hdenot ⊢
    have ⟨hwf_e, label, heq, hcap, hmem⟩ := hdenot
    constructor
    · exact hwf_e
    · exists label, heq, hcap
      exact CapabilitySet.subset_preserves_covers hsub hmem
  | arrow T1 T2 =>
    simp [Ty.shape_val_denot] at hdenot ⊢
    have ⟨hwf_e, cs, T0, t0, hres, hwf_cs, hR0_R1, hfun⟩ := hdenot
    constructor
    · exact hwf_e
    · exists cs, T0, t0, hres, hwf_cs
      constructor
      · exact CapabilitySet.Subset.trans hR0_R1 hsub
      · exact hfun
  | poly T1 T2 =>
    simp [Ty.shape_val_denot] at hdenot ⊢
    have ⟨hwf_e, cs, T0, t0, hres, hwf_cs, hR0_R1, hfun⟩ := hdenot
    constructor
    · exact hwf_e
    · exists cs, T0, t0, hres, hwf_cs
      constructor
      · exact CapabilitySet.Subset.trans hR0_R1 hsub
      · exact hfun
  | cpoly B T =>
    simp [Ty.shape_val_denot] at hdenot ⊢
    have ⟨hwf_e, cs, B0, t0, hres, hwf_cs, hR0_R1, hfun⟩ := hdenot
    constructor
    · exact hwf_e
    · exists cs, B0, t0, hres, hwf_cs
      constructor
      · exact CapabilitySet.Subset.trans hR0_R1 hsub
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
        | masked => simp at hresolve
        | val v =>
          simp at hresolve
          apply Exp.WfInHeap.wf_var
          apply Var.WfInHeap.wf_free
          exact hfx
    | bound bx => cases bx
  | unit =>
    apply Exp.WfInHeap.wf_unit
  | _ => simp [resolve] at hresolve

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
  | bool =>
    simp [Ty.shape_val_denot] at hdenot
    cases e with
    | btrue => exact Exp.WfInHeap.wf_btrue
    | bfalse => exact Exp.WfInHeap.wf_bfalse
    | var x =>
      cases x with
      | bound bx => cases bx
      | free fx =>
        cases hcell : m.heap fx with
        | none =>
          simp [resolve, hcell] at hdenot
        | some cell =>
          cases cell with
          | val hv =>
            apply Exp.WfInHeap.wf_var
            apply Var.WfInHeap.wf_free
            simpa [Memory.lookup] using hcell
          | capability =>
            simp [resolve, hcell] at hdenot
          | masked =>
            simp [resolve, hcell] at hdenot
    | _ =>
      simp [resolve] at hdenot
  | unit =>
    simp [Ty.shape_val_denot] at hdenot
    exact wf_from_resolve_unit hdenot
  | cell =>
    simp only [Ty.shape_val_denot] at hdenot
    obtain ⟨l, b0, heq, hlookup, _⟩ := hdenot
    -- e is a variable, so it's well-formed if it's in the heap
    rw [heq]
    apply Exp.WfInHeap.wf_var
    apply Var.WfInHeap.wf_free
    · simp [Memory.lookup] at hlookup
      exact hlookup
  | reader =>
    simp only [Ty.shape_val_denot] at hdenot
    exact hdenot.1
  | cap =>
    simp [Ty.shape_val_denot] at hdenot
    have ⟨hwf_e, label, heq, hlookup, _⟩ := hdenot
    exact hwf_e
  | arrow T1 T2 =>
    simp [Ty.shape_val_denot] at hdenot
    have ⟨hwf_e, cs, T0, t0, hresolve, hwf_cs, _⟩ := hdenot
    exact hwf_e
  | poly T1 T2 =>
    simp [Ty.shape_val_denot] at hdenot
    have ⟨hwf_e, cs, S0, t0, hresolve, hwf_cs, _⟩ := hdenot
    exact hwf_e
  | cpoly B T =>
    simp [Ty.shape_val_denot] at hdenot
    have ⟨hwf_e, cs, B0, t0, hresolve, hwf_cs, _⟩ := hdenot
    exact hwf_e

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
    simp [Ty.shape_val_denot] at ht ⊢
    exact hts X R m fx ht
  | bool =>
    simp [Ty.shape_val_denot] at ht ⊢
    exact ht
  | unit =>
    simp [Ty.shape_val_denot] at ht ⊢
    exact ht
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
      · simp [Memory.lookup] at hlookup
        simp [reachability_of_loc, hlookup]
        exact CapabilitySet.covers.here Mutability.Le.refl
  | reader =>
    simp only [Ty.shape_val_denot] at ht ⊢
    obtain ⟨hwf, label, b0, hres, hlookup, hcov⟩ := ht
    constructor
    · exact hwf
    · use label, b0
      constructor
      · exact hres
      · constructor
        · exact hlookup
        · -- Need: reachability_of_loc m.heap fx .covers .ro label
          -- Since resolve m.heap (.var (.free fx)) = some (.reader (.free label)),
          -- the heap value unwraps to .reader (.free label)
          -- So reachability_of_loc m.heap fx = singleton .ro label
          have : ∃ v, m.heap fx = some (Cell.val v) ∧ v.unwrap = .reader (.free label) := by
            unfold resolve at hres
            cases heq : m.heap fx
            · simp [heq] at hres
            · next cell =>
              cases cell <;> simp [heq] at hres
              exact ⟨_, rfl, hres⟩
          obtain ⟨v, hv, hunwrap⟩ := this
          have heq := reachability_of_loc_eq_resolve_reachability m fx v hv
          rw [heq, hunwrap]
          simp [resolve_reachability]
          exact CapabilitySet.covers.here Mutability.Le.refl
  | cap =>
    simp [Ty.shape_val_denot, reachability_of_loc, Memory.lookup] at ht ⊢
    obtain ⟨hwf, hmem, hin⟩ := ht
    constructor
    · exact hwf
    · constructor
      · exact hmem
      · simp [hmem]
        exact CapabilitySet.covers.here Mutability.Le.refl
  | arrow T1 T2 =>
    simp [Ty.shape_val_denot] at ht ⊢
    have ⟨hwf, cs, T0, t0, hresolve, hwf_cs, hR0_sub, hbody⟩ := ht
    constructor
    · exact hwf
    · use cs, T0, t0
      constructor
      · exact hresolve
      · constructor
        · exact hwf_cs
        · constructor
          · -- Need to show: expand_captures m.heap cs ⊆ reachability_of_loc m.heap fx
            -- Extract the heap value from resolve
            have : ∃ v, m.heap fx = some (Cell.val v) ∧ v.unwrap = Exp.abs cs T0 t0 := by
              unfold resolve at hresolve
              cases heq : m.heap fx
              · simp [heq] at hresolve
              · next cell =>
                cases cell <;> simp [heq] at hresolve
                exact ⟨_, rfl, hresolve⟩
            obtain ⟨v, hv, hunwrap⟩ := this
            -- Use the equality: reachability_of_loc = resolve_reachability of unwrapped value
            have heq := reachability_of_loc_eq_resolve_reachability m fx v hv
            rw [heq, hunwrap]
            simp [resolve_reachability]
            exact CapabilitySet.Subset.refl
          · exact hbody
  | poly T1 T2 =>
    simp [Ty.shape_val_denot] at ht ⊢
    have ⟨hwf, cs, S0, t0, hresolve, hwf_cs, hR0_sub, hbody⟩ := ht
    constructor
    · exact hwf
    · use cs, S0, t0
      constructor
      · exact hresolve
      · constructor
        · exact hwf_cs
        · constructor
          · -- Need to show: expand_captures m.heap cs ⊆ reachability_of_loc m.heap fx
            -- Extract the heap value from resolve
            have : ∃ v, m.heap fx = some (Cell.val v) ∧ v.unwrap = Exp.tabs cs S0 t0 := by
              unfold resolve at hresolve
              cases heq : m.heap fx
              · simp [heq] at hresolve
              · next cell =>
                cases cell <;> simp [heq] at hresolve
                exact ⟨_, rfl, hresolve⟩
            obtain ⟨v, hv, hunwrap⟩ := this
            -- Use the equality: reachability_of_loc = resolve_reachability of unwrapped value
            have heq := reachability_of_loc_eq_resolve_reachability m fx v hv
            rw [heq, hunwrap]
            simp [resolve_reachability]
            exact CapabilitySet.Subset.refl
          · exact hbody
  | cpoly B T =>
    simp [Ty.shape_val_denot] at ht ⊢
    have ⟨hwf, cs, B0, t0, hresolve, hwf_cs, hR0_sub, hbody⟩ := ht
    constructor
    · exact hwf
    · use cs, B0, t0
      constructor
      · exact hresolve
      · constructor
        · exact hwf_cs
        · constructor
          · -- Need to show: expand_captures m.heap cs ⊆ reachability_of_loc m.heap fx
            -- Extract the heap value from resolve
            have : ∃ v, m.heap fx = some (Cell.val v) ∧ v.unwrap = Exp.cabs cs B0 t0 := by
              unfold resolve at hresolve
              cases heq : m.heap fx
              · simp [heq] at hresolve
              · next cell =>
                cases cell <;> simp [heq] at hresolve
                exact ⟨_, rfl, hresolve⟩
            obtain ⟨v, hv, hunwrap⟩ := this
            -- Use the equality: reachability_of_loc = resolve_reachability of unwrapped value
            have heq := reachability_of_loc_eq_resolve_reachability m fx v hv
            rw [heq, hunwrap]
            simp [resolve_reachability]
            exact CapabilitySet.Subset.refl
          · exact hbody

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

end Capybara
