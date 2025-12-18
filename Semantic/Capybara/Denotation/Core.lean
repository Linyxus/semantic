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

/-- The denotation entails heap well-formedness. -/
def Denot.implies_wf (d : Denot) : Prop :=
  ∀ m e, d m e -> e.WfInHeap m.heap

-- NOTE: The following definitions are no longer needed after the type hierarchy collapse.
-- The capability set bound is now derived from the type's capture set, making these
-- properties trivially true. They are kept commented out for reference.
--
-- def Denot.is_reachability_safe (d : Denot) : Prop := True
-- def Denot.is_reachability_monotonic (d : Denot) : Prop := True
-- def Denot.is_tight (d : Denot) : Prop := True

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
/-- Type information for a type variable is a denotation. -/
| tvar : Denot -> TypeInfo s .tvar
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

def TypeEnv.extend_tvar (Γ : TypeEnv s) (T : Denot) : TypeEnv (s,X) :=
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

def TypeEnv.lookup_tvar : (Γ : TypeEnv s) -> (x : BVar s .tvar) -> Denot
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

/-- Whether this denotation enforces purity of the value. -/
def Denot.enforce_pure (d : Denot) : Prop :=
  ∀ m e,
    d m e ->
    resolve_reachability m.heap e ⊆ .empty

mutual

/-- Value denotation for capturing types. -/
def Ty.val_denot : TypeEnv s -> Ty .capt s -> Denot
| _, .top => fun m e =>
  e.WfInHeap m.heap ∧ resolve_reachability m.heap e ⊆ .empty
| env, .tvar X => env.lookup_tvar X
| _, .unit => fun m e =>
  resolve m.heap e = some .unit
| _, .bool => fun m e =>
  resolve m.heap e = some .btrue ∨ resolve m.heap e = some .bfalse
| env, .cap cs => fun m e =>
  e.WfInHeap m.heap ∧
  (cs.subst (Subst.from_TypeEnv env)).WfInHeap m.heap ∧
  ∃ label : Nat,
    e = .var (.free label) ∧
    m.lookup label = some (.capability .basic) ∧
    (cs.denot env m).covers .epsilon label
| env, .reader cs => fun m e =>
  e.WfInHeap m.heap ∧
  (cs.subst (Subst.from_TypeEnv env)).WfInHeap m.heap ∧
  ∃ (label : Nat) (b0 : Bool),
    resolve m.heap e = some (.reader (.free label)) ∧
    m.lookup label = some (.capability (.mcell b0)) ∧
    (cs.denot env m).covers .ro label
| env, .cell cs => fun m e =>
  (cs.subst (Subst.from_TypeEnv env)).WfInHeap m.heap ∧
  ∃ l b0,
    e = .var (.free l) ∧
    m.lookup l = some (.capability (.mcell b0)) ∧
    (cs.denot env m).covers .epsilon l
| env, .arrow T1 cs T2 => fun m e =>
  e.WfInHeap m.heap ∧
  (cs.subst (Subst.from_TypeEnv env)).WfInHeap m.heap ∧
  ∃ cs' T0 t0,
    resolve m.heap e = some (.abs cs' T0 t0) ∧
    cs'.WfInHeap m.heap ∧
    let R0 := expand_captures m.heap cs'
    R0 ⊆ (cs.denot env m) ∧
    (∀ (arg : Nat) (m' : Memory),
      m'.subsumes m ->
      Ty.val_denot env T1 m' (.var (.free arg)) ->
      Ty.exi_exp_denot
        (env.extend_var arg (compute_peakset env T1.captureSet))
        T2
        (cs.rename Rename.succ ∪ (.var .epsilon (.bound .here)))
        m' (t0.subst (Subst.openVar (.free arg))))
| env, .poly T1 cs T2 => fun m e =>
  e.WfInHeap m.heap ∧
  (cs.subst (Subst.from_TypeEnv env)).WfInHeap m.heap ∧
  ∃ cs' S0 t0,
    resolve m.heap e = some (.tabs cs' S0 t0) ∧
    cs'.WfInHeap m.heap ∧
    let R0 := expand_captures m.heap cs'
    R0 ⊆ (cs.denot env m) ∧
    (∀ (m' : Memory) (denot : Denot),
      m'.subsumes m ->
      denot.is_proper ->
      denot.ImplyAfter m' (Ty.val_denot env T1) ->
      denot.enforce_pure ->
      Ty.exi_exp_denot
        (env.extend_tvar denot)
        T2
        (cs.rename Rename.succ)
        m' (t0.subst (Subst.openTVar .top)))
| env, .cpoly B cs T => fun m e =>
  e.WfInHeap m.heap ∧
  (cs.subst (Subst.from_TypeEnv env)).WfInHeap m.heap ∧
  ∃ cs' B0 t0,
    resolve m.heap e = some (.cabs cs' B0 t0) ∧
    cs'.WfInHeap m.heap ∧
    let R0 := expand_captures m.heap cs'
    R0 ⊆ (cs.denot env m) ∧
    (∀ (m' : Memory) (CS : CaptureSet {}),
      CS.WfInHeap m'.heap ->
      let A0 := CS.denot TypeEnv.empty
      m'.subsumes m ->
      ((A0 m').BoundedBy (B.denot m')) ->
      Ty.exi_exp_denot
        (env.extend_cvar CS)
        T
        (cs.rename Rename.succ)
        m' (t0.subst (Subst.openCVar CS)))

/-- Value denotation for existential types. -/
def Ty.exi_val_denot : TypeEnv s -> Ty .exi s -> Denot
| ρ, .typ T => Ty.val_denot ρ T
| ρ, .exi T => fun m e =>
  match resolve m.heap e with
  | some (.pack CS x) =>
    CS.WfInHeap m.heap ∧
    Ty.val_denot (ρ.extend_cvar CS) T m (.var x)
  | _ => False

/-- Expression denotation for capturing types.
    Takes an explicit capture set (the use set from the typing judgment). -/
def Ty.exp_denot : TypeEnv s -> Ty .capt s -> CaptureSet s -> Denot
| ρ, T, cs => fun m (e : Exp {}) =>
  Eval (cs.denot ρ m) m e (Ty.val_denot ρ T).as_mpost

/-- Expression denotation for existential types.
    Takes an explicit capture set (the use set from the typing judgment). -/
def Ty.exi_exp_denot : TypeEnv s -> Ty .exi s -> CaptureSet s -> Denot
| ρ, T, cs => fun m (e : Exp {}) =>
  Eval (cs.denot ρ m) m e (Ty.exi_val_denot ρ T).as_mpost

end

@[simp]
instance instCaptHasDenotation :
  HasDenotation (Ty .capt s) (TypeEnv s) Denot where
  interp := Ty.val_denot

@[simp]
instance instExiHasDenotation :
  HasDenotation (Ty .exi s) (TypeEnv s) Denot where
  interp := Ty.exi_val_denot

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
  denot.implies_wf ∧
  denot.ImplyAfter m ⟦S.core⟧_[env] ∧
  denot.enforce_pure ∧
  EnvTyping Γ env m
| .push Γ (.cvar B), .extend env (.cvar cs), m =>
  (cs.WfInHeap m.heap) ∧
  ((cs.ground_denot m).BoundedBy (B.denot m)) ∧
  EnvTyping Γ env m

/-- Helper lemma: For bound variables, `CaptureSet.peaks` equals `compute_peaks`. -/
theorem peaks_var_bound_eq {s : Sig} {Γ : Ctx s} {ρ : TypeEnv s}
    (h : EnvTyping Γ ρ mem) (x : BVar s .var) (m0 : Mutability) :
    CaptureSet.peaks Γ (.var m0 (.bound x)) = (ρ.lookup_var x).2.cs.applyMut m0 := by
  match s, Γ, ρ, x with
  | _, .push Γ' (.var T), .extend ρ' (.var n ps), .here =>
    simp only [EnvTyping] at h
    obtain ⟨_, hps, _⟩ := h
    -- hps : ps = CaptureSet.peakset Γ' T.captureSet
    simp only [CaptureSet.peaks, TypeEnv.lookup_var, PeakSet.rename]
    -- Goal: applyMut m0 ((peaks Γ' T.captureSet).rename ...) = applyMut m0 (ps.cs.rename ...)
    rw [hps]
    simp only [CaptureSet.peakset]
  | _, .push Γ' (.var T), .extend ρ' (.var n ps), .there x' =>
    simp only [EnvTyping] at h
    obtain ⟨_, _, h'⟩ := h
    simp only [CaptureSet.peaks, TypeEnv.lookup_var, PeakSet.rename]
    rw [peaks_var_bound_eq h' x' m0]
    exact CaptureSet.applyMut_rename
  | _, .push Γ' (.tvar S), .extend ρ' (.tvar denot), .there x' =>
    simp only [EnvTyping] at h
    obtain ⟨_, _, _, _, h'⟩ := h
    simp only [CaptureSet.peaks, TypeEnv.lookup_var, PeakSet.rename]
    rw [peaks_var_bound_eq h' x' m0]
    exact CaptureSet.applyMut_rename
  | _, .push Γ' (.cvar B), .extend ρ' (.cvar cs), .there x' =>
    simp only [EnvTyping] at h
    obtain ⟨_, _, h'⟩ := h
    simp only [CaptureSet.peaks, TypeEnv.lookup_var, PeakSet.rename]
    rw [peaks_var_bound_eq h' x' m0]
    exact CaptureSet.applyMut_rename
termination_by sizeOf x

theorem compute_peaks_correct (h : EnvTyping Γ ρ m) :
  ∀ C, CaptureSet.peaks Γ C = compute_peaks ρ C := by
  intro C
  induction C
  case empty => simp [CaptureSet.peaks, compute_peaks]
  case union ih1 ih2 =>
    simp only [CaptureSet.peaks, compute_peaks, Union.union]
    rw [ih1, ih2]
  case cvar m c => simp [CaptureSet.peaks, compute_peaks]
  case var m c =>
    cases c with
    | free n => simp [CaptureSet.peaks, compute_peaks]
    | bound x =>
      -- Use the helper lemma
      simp only [compute_peaks]
      exact peaks_var_bound_eq h x m

theorem compute_peakset_correct (h : EnvTyping Γ ρ m) :
  ∀ C, C.peakset Γ = compute_peakset ρ C := by
  intro C
  -- peakset Γ C = ⟨peaks Γ C, peaks_peaksOnly Γ C⟩
  -- compute_peakset ρ C = ⟨compute_peaks ρ C, compute_peaks_is_peak ρ C⟩
  -- By compute_peaks_correct: peaks Γ C = compute_peaks ρ C
  simp only [CaptureSet.peakset, compute_peakset]
  -- Two PeakSet values with equal cs fields are equal (proof irrelevance)
  congr 1
  exact compute_peaks_correct h C

def SemanticTyping (C : CaptureSet s) (Γ : Ctx s) (e : Exp s) (E : Ty .exi s) : Prop :=
  ∀ ρ m,
    EnvTyping Γ ρ m ->
    Ty.exi_exp_denot ρ E C m (e.subst (Subst.from_TypeEnv ρ))

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

theorem Subst.from_TypeEnv_weaken_open_tvar {env : TypeEnv s} {d : Denot} :
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
      simp only [Subst.comp, Subst.lift, Subst.from_TypeEnv, TypeEnv.extend_tvar]
      -- Goal: (PureTy.top.rename Rename.succ).subst (Subst.openTVar PureTy.top) = PureTy.top
      -- PureTy.top.rename Rename.succ = PureTy.top (since .top has no bound vars)
      -- PureTy.top.subst _ = PureTy.top (since .top has no bound vars)
      simp only [PureTy.rename, PureTy.subst, PureTy.top, Ty.rename, Ty.subst]
  · intro C
    cases C with
    | there C' =>
      simp [Subst.from_TypeEnv, Subst.lift, Subst.comp, Subst.openTVar,
        TypeEnv.extend_tvar, TypeEnv.lookup_cvar]
      exact CaptureSet.weaken_openTVar

theorem Exp.from_TypeEnv_weaken_open_tvar
  {env : TypeEnv s} {d : Denot} {e : Exp (s,X)} :
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

/-- All type variable denotations in the environment imply well-formedness. -/
def TypeEnv.is_implying_wf (env : TypeEnv s) : Prop :=
  ∀ (X : BVar s .tvar),
    (env.lookup_tvar X).implies_wf

/-- An environment typing implies that all type variable denotations imply well-formedness. -/
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
          have ⟨_, himplies, _, _, ht'⟩ := ht
          have ih_result := ih ht'
          simp [TypeEnv.is_implying_wf] at ih_result ⊢
          intro x
          cases x with
          | here =>
            simp [TypeEnv.lookup_tvar]
            exact himplies
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

/-- All type variable denotations in the environment enforce purity. -/
def TypeEnv.is_enforcing_pure (env : TypeEnv s) : Prop :=
  ∀ (X : BVar s .tvar),
    (env.lookup_tvar X).enforce_pure

/-- An environment typing implies that all type variable denotations enforce purity. -/
theorem typed_env_enforces_pure
  (ht : EnvTyping Γ env mem) :
  env.is_enforcing_pure := by
  induction Γ with
  | empty =>
    cases env with
    | empty =>
      simp [TypeEnv.is_enforcing_pure]
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
          simp [TypeEnv.is_enforcing_pure] at ih_result ⊢
          intro x
          cases x with
          | there x =>
            simp [TypeEnv.lookup_tvar]
            exact ih_result x
      | tvar S =>
        cases info with
        | tvar d =>
          simp [EnvTyping] at ht
          have ⟨_, _, _, hpure, ht'⟩ := ht
          have ih_result := ih ht'
          simp [TypeEnv.is_enforcing_pure] at ih_result ⊢
          intro x
          cases x with
          | here =>
            simp [TypeEnv.lookup_tvar]
            exact hpure
          | there x =>
            simp [TypeEnv.lookup_tvar]
            exact ih_result x
      | cvar B =>
        cases info with
        | cvar cs =>
          simp [EnvTyping] at ht
          have ⟨hwf, hsub, ht'⟩ := ht
          have ih_result := ih ht'
          simp [TypeEnv.is_enforcing_pure] at ih_result ⊢
          intro x
          cases x with
          | there x =>
            simp [TypeEnv.lookup_tvar]
            exact ih_result x

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
          -- Extract well-formedness from the denotation
          -- For all type constructors, val_denot implies WfInHeap
          have hwf : Exp.WfInHeap (s := {}) (.var (.free n)) m.heap := by
            simp only [instCaptHasDenotation] at htype
            cases T with
            | top =>
              unfold Ty.val_denot at htype
              exact htype.1
            | tvar X =>
              -- For tvar, we need the denotation to be proper
              -- This is guaranteed by EnvTyping for the lookup_tvar
              unfold Ty.val_denot at htype
              have himplying := typed_env_is_implying_wf htyping'
              unfold TypeEnv.is_implying_wf at himplying
              exact himplying X m (.var (.free n)) htype
            | unit =>
              unfold Ty.val_denot at htype
              simp only [resolve] at htype
              split at htype <;> try contradiction
              rename_i hsome
              exact Exp.WfInHeap.wf_var (Var.WfInHeap.wf_free hsome)
            | bool =>
              unfold Ty.val_denot at htype
              cases htype with
              | inl h =>
                simp only [resolve] at h
                split at h <;> try contradiction
                rename_i hsome
                exact Exp.WfInHeap.wf_var (Var.WfInHeap.wf_free hsome)
              | inr h =>
                simp only [resolve] at h
                split at h <;> try contradiction
                rename_i hsome
                exact Exp.WfInHeap.wf_var (Var.WfInHeap.wf_free hsome)
            | cap cs =>
              unfold Ty.val_denot at htype
              exact htype.1
            | reader cs =>
              unfold Ty.val_denot at htype
              exact htype.1
            | cell cs =>
              unfold Ty.val_denot at htype
              obtain ⟨_, l, _, hl, hlookup, _⟩ := htype
              cases hl
              simp [Memory.lookup] at hlookup
              exact Exp.WfInHeap.wf_var (Var.WfInHeap.wf_free hlookup)
            | arrow T1 cs T2 =>
              unfold Ty.val_denot at htype
              exact htype.1
            | poly T1 cs T2 =>
              unfold Ty.val_denot at htype
              exact htype.1
            | cpoly B cs T' =>
              unfold Ty.val_denot at htype
              exact htype.1
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
          have ⟨_, _, _, _, htyping'⟩ := htyping
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

-- NOTE: The following TypeEnv properties are no longer needed after the type hierarchy collapse.
-- They relied on Denot.is_reachability_safe, Denot.is_reachability_monotonic, and Denot.is_tight
-- which are now trivially true.
--
-- def TypeEnv.is_reachability_safe (env : TypeEnv s) : Prop :=
--   ∀ (X : BVar s .tvar), (env.lookup_tvar X).is_reachability_safe
-- def TypeEnv.is_reachability_monotonic (env : TypeEnv s) : Prop :=
--   ∀ (X : BVar s .tvar), (env.lookup_tvar X).is_reachability_monotonic
-- def TypeEnv.is_tight (env : TypeEnv s) : Prop :=
--   ∀ (X : BVar s .tvar), (env.lookup_tvar X).is_tight

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
          have ⟨hproper, _, _, _, ht'⟩ := ht
          have ih_result := ih ht'
          constructor
          · intro x
            cases x with
            | here =>
              simp [TypeEnv.lookup_tvar]
              -- hproper says d.is_proper
              -- We need d.is_monotonic
              -- Denot.is_proper = is_monotonic ∧ is_transparent ∧ is_bool_independent
              exact hproper.1
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
          have ⟨hproper, _, _, _, ht'⟩ := ht
          have ih_result := ih ht'
          simp [TypeEnv.is_transparent] at ih_result ⊢
          intro x
          cases x with
          | here =>
            simp [TypeEnv.lookup_tvar]
            -- hproper says d.is_proper
            -- We need d.is_transparent
            -- Denot.is_proper = is_monotonic ∧ is_transparent ∧ is_bool_independent
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
          have ⟨hproper, _, _, _, ht'⟩ := ht
          have ih_result := ih ht'
          simp [TypeEnv.is_bool_independent] at ih_result ⊢
          intro x
          cases x with
          | here =>
            simp [TypeEnv.lookup_tvar]
            -- hproper says d.is_proper
            -- We need d.is_bool_independent
            -- Denot.is_proper = is_monotonic ∧ is_transparent ∧ is_bool_independent
            exact hproper.2.2
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

-- NOTE: The following theorems are no longer needed after the type hierarchy collapse.
-- They relied on TypeEnv.is_reachability_safe, TypeEnv.is_reachability_monotonic,
-- and TypeEnv.is_tight which are now trivially provable.
--
-- theorem typed_env_is_reachability_safe
--   (ht : EnvTyping Γ env mem) : env.is_reachability_safe := ...
-- theorem typed_env_is_reachability_monotonic
--   (ht : EnvTyping Γ env mem) : env.is_reachability_monotonic := ...
-- theorem typed_env_is_tight
--   (ht : EnvTyping Γ env mem) : env.is_tight := ...

theorem val_denot_is_transparent {env : TypeEnv s}
  (henv : TypeEnv.is_transparent env)
  (T : Ty .capt s) :
  (Ty.val_denot env T).is_transparent := by
  cases T with
  | top =>
    intro m x v hx ht
    unfold Ty.val_denot at ht ⊢
    have hx_heap : m.heap x = some (Cell.val v) := by
      simp [Memory.lookup] at hx
      exact hx
    constructor
    · apply Exp.WfInHeap.wf_var
      apply Var.WfInHeap.wf_free
      exact hx_heap
    · -- resolve_reachability of var equals resolve_reachability of stored value
      have heq : resolve_reachability m.heap (.var (.free x)) =
                 resolve_reachability m.heap v.unwrap :=
        reachability_of_loc_eq_resolve_reachability m x v hx_heap
      rw [heq]
      exact ht.2
  | tvar X =>
    unfold Ty.val_denot
    exact henv X
  | unit =>
    intro m x v hx ht
    unfold Ty.val_denot at ht ⊢
    have hx' : m.heap x = some (.val v) := by
      simp [Memory.lookup] at hx
      exact hx
    rw [resolve_var_heap_trans hx']
    exact ht
  | cap cs =>
    intro m x v hx ht
    unfold Ty.val_denot at ht ⊢
    have ⟨_, _, label, hlabel, hcap, hmem⟩ := ht
    -- v.unwrap = .var (.free label), but v.isVal says it's a simple value
    -- Variables are not simple values, so this is a contradiction
    have hval := v.isVal
    rw [hlabel] at hval
    cases hval
  | arrow T1 cs T2 =>
    intro m x v hx ht
    unfold Ty.val_denot at ht ⊢
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
    intro m x v hx ht
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
        unfold Ty.val_denot at ht
        simpa [hres_self] using ht
      -- Finish by rewriting with hbool
      unfold Ty.val_denot
      cases hbool with
      | inl hb =>
        simp [resolve, hlookup, hb]
      | inr hb =>
        simp [resolve, hlookup, hb]
  | cell cs =>
    intro m x v hx ht
    unfold Ty.val_denot at ht ⊢
    obtain ⟨_, l, b0, heq, hlookup_and_mem⟩ := ht
    -- v.unwrap = .var (.free l), but v.isVal says it's a simple value
    -- Variables are not simple values, so this is a contradiction
    have hval := v.isVal
    rw [heq] at hval
    cases hval
  | reader cs =>
    intro m x v hx ht
    unfold Ty.val_denot at ht ⊢
    obtain ⟨hwf, hwf_cs, label, b0, hres, hlookup, hcov⟩ := ht
    have hx' : m.heap x = some (.val v) := by
      simp [Memory.lookup] at hx
      exact hx
    have heq := resolve_var_heap_trans hx'
    rw [heq]
    refine ⟨?_, hwf_cs, label, b0, hres, hlookup, hcov⟩
    -- Prove (Exp.var (Var.free x)).WfInHeap m.heap
    constructor
    constructor
    exact hx'
  | poly T1 cs T2 =>
    intro m x v hx ht
    unfold Ty.val_denot at ht ⊢
    have hx' : m.heap x = some (.val v) := by
      simp [Memory.lookup] at hx
      exact hx
    have heq := resolve_var_heap_trans hx'
    rw [heq]
    -- Split ht into well-formedness and existential parts
    have ⟨hwf_unwrap, hwf_cs, hexists⟩ := ht
    constructor
    · -- Prove (Exp.var (Var.free x)).WfInHeap m.heap
      constructor
      constructor
      exact hx'
    constructor
    · exact hwf_cs
    · -- The existential part remains the same
      exact hexists
  | cpoly B cs T =>
    intro m x v hx ht
    unfold Ty.val_denot at ht ⊢
    have hx' : m.heap x = some (.val v) := by
      simp [Memory.lookup] at hx
      exact hx
    have heq := resolve_var_heap_trans hx'
    rw [heq]
    -- Split ht into well-formedness and existential parts
    have ⟨hwf_unwrap, hwf_cs, hexists⟩ := ht
    constructor
    · -- Prove (Exp.var (Var.free x)).WfInHeap m.heap
      constructor
      constructor
      exact hx'
    constructor
    · exact hwf_cs
    · -- The existential part remains the same
      exact hexists

theorem val_denot_is_bool_independent {env : TypeEnv s}
  (henv : env.is_bool_independent)
  (T : Ty .capt s) :
  (Ty.val_denot env T).is_bool_independent := by
  intro m
  cases T with
  | top =>
    unfold Ty.val_denot
    constructor <;> intro
    · constructor
      · apply Exp.WfInHeap.wf_bfalse
      · simp [resolve_reachability]; exact CapabilitySet.Subset.refl
    · constructor
      · apply Exp.WfInHeap.wf_btrue
      · simp [resolve_reachability]; exact CapabilitySet.Subset.refl
  | tvar X =>
    unfold Ty.val_denot
    exact henv X
  | unit =>
    unfold Ty.val_denot
    simp [resolve]
  | cap cs =>
    unfold Ty.val_denot
    simp
  | bool =>
    unfold Ty.val_denot
    simp [resolve]
  | cell cs =>
    unfold Ty.val_denot
    simp
  | reader cs =>
    -- btrue and bfalse cannot resolve to a reader, so both sides are False
    unfold Ty.val_denot
    simp [resolve]
  | arrow T1 cs T2 =>
    unfold Ty.val_denot
    simp [resolve]
  | poly T1 cs T2 =>
    unfold Ty.val_denot
    simp [resolve]
  | cpoly B cs T =>
    unfold Ty.val_denot
    simp [resolve]

theorem exi_val_denot_is_transparent {env : TypeEnv s}
  (henv : TypeEnv.is_transparent env)
  (T : Ty .exi s) :
  (Ty.exi_val_denot env T).is_transparent := by
  cases T with
  | typ T =>
    unfold Ty.exi_val_denot
    exact val_denot_is_transparent henv T
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
        CS.WfInHeap m.heap ∧ Ty.val_denot (env.extend_cvar CS) T m (.var x)
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
        -- ht now says: Ty.val_denot (env.extend_cvar CS') T m (var y')
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

def val_denot_is_monotonic {env : TypeEnv s}
  (henv : env.IsMonotonic)
  (T : Ty .capt s) :
  (Ty.val_denot env T).is_monotonic := by
  cases T with
  | top =>
    intro m1 m2 e hmem ht
    unfold Ty.val_denot at ht ⊢
    constructor
    · exact Exp.wf_monotonic hmem ht.1
    · rw [resolve_reachability_monotonic hmem e ht.1]
      exact ht.2
  | tvar X =>
    unfold Ty.val_denot
    exact henv.tvar X
  | unit =>
    intro m1 m2 e hmem ht
    unfold Ty.val_denot at ht ⊢
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
  | cap cs =>
    intro m1 m2 e hmem ht
    unfold Ty.val_denot at ht ⊢
    have ⟨hwf_e, hwf_cs, label, heq, hcap, hmemin⟩ := ht
    constructor
    · -- Prove e.WfInHeap m2.heap
      exact Exp.wf_monotonic hmem hwf_e
    constructor
    · -- Prove (cs.subst ...).WfInHeap m2.heap
      exact CaptureSet.wf_monotonic hmem hwf_cs
    · use label
      constructor
      · exact heq
      constructor
      · have hsub : m2.heap.subsumes m1.heap := hmem
        obtain ⟨c', hc', hsub_c⟩ := hsub label (Cell.capability .basic) hcap
        -- For basic capability cells, subsumption requires equality
        simp [Cell.subsumes] at hsub_c
        subst hsub_c
        simp [Memory.lookup]
        exact hc'
      · -- Need to show: (cs.denot env m2).covers .epsilon label
        -- hmemin : (cs.denot env m1).covers .epsilon label
        -- hwf_cs : (cs.subst ...).WfInHeap m1.heap
        have hcs_eq := capture_set_denot_is_monotonic (C := cs) (ρ := env) hwf_cs hmem
        rw [← hcs_eq]
        exact hmemin
  | bool =>
    intro m1 m2 e hmem ht
    unfold Ty.val_denot at ht ⊢
    cases ht with
    | inl htrue =>
      left
      exact resolve_monotonic hmem htrue
    | inr hfalse =>
      right
      exact resolve_monotonic hmem hfalse
  | cell cs =>
    intro m1 m2 e hmem ht
    unfold Ty.val_denot at ht ⊢
    obtain ⟨hwf_cs, l, b0, heq, hlookup, hcov⟩ := ht
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
        constructor
        · exact CaptureSet.wf_monotonic hmem hwf_cs
        refine ⟨l, b', heq, ?_, ?_⟩
        · simp [Memory.lookup]; exact hc'
        · -- Use capture_set_denot_is_monotonic for equality
          have hcs_eq := capture_set_denot_is_monotonic (C := cs) (ρ := env) hwf_cs hmem
          rw [← hcs_eq]
          exact hcov
  | reader cs =>
    intro m1 m2 e hmem ht
    unfold Ty.val_denot at ht ⊢
    obtain ⟨hwf_e, hwf_cs, label, b0, hres, hlookup, hcov⟩ := ht
    constructor
    · exact Exp.wf_monotonic hmem hwf_e
    constructor
    · exact CaptureSet.wf_monotonic hmem hwf_cs
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
          refine ⟨label, b', ?_, ?_, ?_⟩
          · exact resolve_monotonic hmem hres
          · simp [Memory.lookup]; exact hc'
          · -- Use capture_set_denot_is_monotonic for equality
            have hcs_eq := capture_set_denot_is_monotonic (C := cs) (ρ := env) hwf_cs hmem
            rw [← hcs_eq]
            exact hcov
  | arrow T1 cs T2 =>
    intro m1 m2 e hmem ht
    unfold Ty.val_denot at ht ⊢
    have ⟨hwf_e, hwf_cs, cs', T0, t0, hr, hwf_cs', hR0_sub, hfun⟩ := ht
    constructor
    · -- Prove e.WfInHeap m2.heap
      exact Exp.wf_monotonic hmem hwf_e
    constructor
    · exact CaptureSet.wf_monotonic hmem hwf_cs
    · use cs', T0, t0
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
        · exact CaptureSet.wf_monotonic hmem hwf_cs'
        · constructor
          · -- Prove: expand_captures m2.heap cs' ⊆ cs.denot env m2
            have hcs_eq := capture_set_denot_is_monotonic (C := cs) (ρ := env) hwf_cs hmem
            have hcs'_eq := expand_captures_monotonic hmem cs' hwf_cs'
            rw [← hcs_eq, hcs'_eq]
            exact hR0_sub
          · intro arg m' hs' harg
            have hs0 := Memory.subsumes_trans hs' hmem
            exact hfun arg m' hs0 harg
  | poly T1 cs T2 =>
    intro m1 m2 e hmem ht
    unfold Ty.val_denot at ht ⊢
    have ⟨hwf_e, hwf_cs, cs', S0, t0, hr, hwf_cs', hR0_sub, hfun⟩ := ht
    constructor
    · -- Prove e.WfInHeap m2.heap
      exact Exp.wf_monotonic hmem hwf_e
    constructor
    · exact CaptureSet.wf_monotonic hmem hwf_cs
    · use cs', S0, t0
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
        · exact CaptureSet.wf_monotonic hmem hwf_cs'
        · constructor
          · -- Prove: expand_captures m2.heap cs' ⊆ cs.denot env m2
            have hcs_eq := capture_set_denot_is_monotonic (C := cs) (ρ := env) hwf_cs hmem
            have hcs'_eq := expand_captures_monotonic hmem cs' hwf_cs'
            rw [← hcs_eq, hcs'_eq]
            exact hR0_sub
          · intro m' denot msub hdenot_proper himply
            have hs0 := Memory.subsumes_trans msub hmem
            exact hfun m' denot hs0 hdenot_proper himply
  | cpoly B cs T =>
    intro m1 m2 e hmem ht
    unfold Ty.val_denot at ht ⊢
    have ⟨hwf_e, hwf_cs, cs', B0, t0, hr, hwf_cs', hR0_sub, hfun⟩ := ht
    constructor
    · -- Prove e.WfInHeap m2.heap
      exact Exp.wf_monotonic hmem hwf_e
    constructor
    · exact CaptureSet.wf_monotonic hmem hwf_cs
    · use cs', B0, t0
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
        · exact CaptureSet.wf_monotonic hmem hwf_cs'
        · constructor
          · -- Prove: expand_captures m2.heap cs' ⊆ cs.denot env m2
            have hcs_eq := capture_set_denot_is_monotonic (C := cs) (ρ := env) hwf_cs hmem
            have hcs'_eq := expand_captures_monotonic hmem cs' hwf_cs'
            rw [← hcs_eq, hcs'_eq]
            exact hR0_sub
          · intro m' CS hwf _ msub hbounded
            have hs0 := Memory.subsumes_trans msub hmem
            exact hfun m' CS hwf hs0 hbounded

def exi_val_denot_is_monotonic {env : TypeEnv s}
  (henv : env.IsMonotonic)
  (T : Ty .exi s) :
  (Ty.exi_val_denot env T).is_monotonic := by
  cases T with
  | typ T =>
    unfold Ty.exi_val_denot
    exact val_denot_is_monotonic henv T
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
        -- ht now says: CS.WfInHeap m1.heap ∧ Ty.val_denot (env.extend_cvar CS) T m1 (var y)
        obtain ⟨hwf_CS_m1, ht_body⟩ := ht
        -- Use resolve_monotonic to show resolve m2.heap e = some (pack CS y)
        have hresolve2 : resolve m2.heap e = some (Exp.pack CS y) := by
          apply resolve_monotonic hmem hresolve1
        simp [hresolve2]
        -- Now need to show:
        -- CS.WfInHeap m2.heap ∧ Ty.val_denot (env.extend_cvar CS) T m2 (var y)
        constructor
        · -- Well-formedness is monotonic
          exact CaptureSet.wf_monotonic hmem hwf_CS_m1
        · -- Use monotonicity of val_denot
          have henv' : (env.extend_cvar CS).IsMonotonic := by
            constructor
            · intro X
              cases X with
              | there X' =>
                simp [TypeEnv.extend_cvar, TypeEnv.lookup_tvar]
                exact henv.tvar X'
          exact val_denot_is_monotonic henv' T hmem ht_body
      all_goals {
        -- resolve returned non-pack, so ht is False
        simp [hresolve1] at ht
      }

def exi_val_denot_is_bool_independent {env : TypeEnv s}
  (henv : TypeEnv.is_bool_independent env)
  (T : Ty .exi s) :
  (Ty.exi_val_denot env T).is_bool_independent := by
  cases T with
  | typ T =>
    simp [Ty.exi_val_denot]
    exact val_denot_is_bool_independent henv T
  | exi T =>
    intro m
    simp only [Ty.exi_val_denot]
    -- For btrue and bfalse, resolve returns some btrue/bfalse, which are not pack
    -- So both sides evaluate to False
    simp [resolve]

/-- Ported from old capt_exp_denot_is_monotonic.
    Now an alias for exp_denot_is_monotonic since the type hierarchy is collapsed.
    Note: With CaptureSet instead of CapabilitySet, we need well-formedness to ensure
    the capture set denotation is invariant under memory subsumption. -/
def capt_exp_denot_is_monotonic {env : TypeEnv s}
  (henv_mono : env.IsMonotonic)
  (henv_bool : env.is_bool_independent)
  (T : Ty .capt s) :
  ∀ {cs : CaptureSet s} {m1 m2 : Memory} {e : Exp {}},
    (cs.subst (Subst.from_TypeEnv env)).WfInHeap m1.heap ->
    Exp.WfInHeap e m1.heap ->
    m2.subsumes m1 ->
    (Ty.exp_denot env T cs) m1 e ->
    (Ty.exp_denot env T cs) m2 e := by
  intro cs m1 m2 e hwf_cs hwf hmem ht
  simp only [Ty.exp_denot] at ht ⊢
  -- Use capture set well-formedness to show cs.denot env m1 = cs.denot env m2
  have hcs_eq : cs.denot env m1 = cs.denot env m2 := by
    unfold CaptureSet.denot
    exact ground_denot_is_monotonic hwf_cs hmem
  rw [← hcs_eq]
  apply eval_monotonic
  · apply Denot.as_mpost_is_monotonic
    exact val_denot_is_monotonic henv_mono T
  · apply Denot.as_mpost_is_bool_independent
    exact val_denot_is_bool_independent henv_bool T
  · exact hmem
  · exact hwf
  · exact ht

/-- Ported from old exi_exp_denot_is_monotonic.
    Updated to use CaptureSet instead of CapabilitySet since type hierarchy is collapsed.
    Note: With CaptureSet instead of CapabilitySet, we need well-formedness to ensure
    the capture set denotation is invariant under memory subsumption. -/
def exi_exp_denot_is_monotonic {env : TypeEnv s}
  (henv_mono : env.IsMonotonic)
  (henv_bool : env.is_bool_independent)
  (T : Ty .exi s) :
  ∀ {cs : CaptureSet s} {m1 m2 : Memory} {e : Exp {}},
    (cs.subst (Subst.from_TypeEnv env)).WfInHeap m1.heap ->
    Exp.WfInHeap e m1.heap ->
    m2.subsumes m1 ->
    (Ty.exi_exp_denot env T cs) m1 e ->
    (Ty.exi_exp_denot env T cs) m2 e := by
  intro cs m1 m2 e hwf_cs hwf hmem ht
  simp only [Ty.exi_exp_denot] at ht ⊢
  -- Use capture set well-formedness to show cs.denot env m1 = cs.denot env m2
  have hcs_eq : cs.denot env m1 = cs.denot env m2 := by
    unfold CaptureSet.denot
    exact ground_denot_is_monotonic hwf_cs hmem
  rw [← hcs_eq]
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
            exact val_denot_is_monotonic henv T hmem hval
          · -- Prove: peakset consistency and EnvTyping Γ env' mem2
            constructor
            · simpa using hps
            · exact ih ht'
      | tvar S =>
        cases info with
        | tvar d =>
          simp [EnvTyping] at ht ⊢
          have ⟨hproper, himply_wf, himply, hpure, ht'⟩ := ht
          constructor
          · exact hproper
          · constructor
            · exact himply_wf
            · constructor
              · apply Denot.imply_after_subsumes himply hmem
              · constructor
                · exact hpure
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

/-- Semantic subtyping relation. Ported from old version.
    The .shape case is now merged into .capt since the type hierarchy is collapsed. -/
def SemSubtyp {k : TySort} (Γ : Ctx s) (T1 T2 : Ty k s) : Prop :=
  match k with
  | .capt =>
    ∀ env H, EnvTyping Γ env H ->
      (Ty.val_denot env T1).ImplyAfter H (Ty.val_denot env T2)
  | .exi =>
    ∀ env H, EnvTyping Γ env H ->
      (Ty.exi_val_denot env T1).ImplyAfter H (Ty.exi_val_denot env T2)

-- NOTE: The following theorems are no longer needed after the type hierarchy collapse.
-- They relied on Denot.is_reachability_safe and Denot.is_reachability_monotonic which are now
-- trivially True.
--
-- theorem val_denot_is_reachability_safe {env : TypeEnv s}
--   (_hts : env.is_reachability_safe) (T : Ty .capt s) :
--   (Ty.val_denot env T).is_reachability_safe := trivial
-- theorem shape_val_denot_is_reachability_safe {env : TypeEnv s}
--   (hts : env.is_reachability_safe) (T : Ty .capt s) :
--   (Ty.val_denot env T).is_reachability_safe := val_denot_is_reachability_safe hts T
-- theorem val_denot_is_reachability_monotonic {env : TypeEnv s}
--   (_hts : env.is_reachability_monotonic) (T : Ty .capt s) :
--   (Ty.val_denot env T).is_reachability_monotonic := trivial
-- theorem shape_val_denot_is_reachability_monotonic {env : TypeEnv s}
--   (hts : env.is_reachability_monotonic) (T : Ty .capt s) :
--   (Ty.val_denot env T).is_reachability_monotonic := val_denot_is_reachability_monotonic hts T

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

/-- Ported from old shape_val_denot_implies_wf.
    For Denot (not PreDenot), implies_wf says d m e → e.WfInHeap m.heap. -/
theorem val_denot_implies_wf {env : TypeEnv s}
  (hts : env.is_implying_wf)
  (T : Ty .capt s) :
  (Ty.val_denot env T).implies_wf := by
  intro m e hdenot
  cases T with
  | top =>
    simp [Ty.val_denot] at hdenot
    exact hdenot.1
  | tvar X =>
    simp [Ty.val_denot] at hdenot
    exact hts X m e hdenot
  | bool =>
    simp [Ty.val_denot] at hdenot
    cases hdenot with
    | inl h =>
      cases e with
      | btrue => exact Exp.WfInHeap.wf_btrue
      | var x =>
        cases x with
        | bound bx => cases bx
        | free fx =>
          simp [resolve] at h
          cases hcell : m.heap fx with
          | none => simp [hcell] at h
          | some cell =>
            cases cell with
            | val hv =>
              apply Exp.WfInHeap.wf_var
              apply Var.WfInHeap.wf_free
              simpa [Memory.lookup] using hcell
            | _ => simp [hcell] at h
      | _ => simp [resolve] at h
    | inr h =>
      cases e with
      | bfalse => exact Exp.WfInHeap.wf_bfalse
      | var x =>
        cases x with
        | bound bx => cases bx
        | free fx =>
          simp [resolve] at h
          cases hcell : m.heap fx with
          | none => simp [hcell] at h
          | some cell =>
            cases cell with
            | val hv =>
              apply Exp.WfInHeap.wf_var
              apply Var.WfInHeap.wf_free
              simpa [Memory.lookup] using hcell
            | _ => simp [hcell] at h
      | _ => simp [resolve] at h
  | unit =>
    simp [Ty.val_denot] at hdenot
    exact wf_from_resolve_unit hdenot
  | cell cs =>
    simp only [Ty.val_denot] at hdenot
    obtain ⟨_, l, b0, heq, hlookup, _⟩ := hdenot
    rw [heq]
    apply Exp.WfInHeap.wf_var
    apply Var.WfInHeap.wf_free
    · simp [Memory.lookup] at hlookup
      exact hlookup
  | reader cs =>
    simp only [Ty.val_denot] at hdenot
    exact hdenot.1
  | cap cs =>
    simp [Ty.val_denot] at hdenot
    exact hdenot.1
  | arrow T1 cs T2 =>
    simp [Ty.val_denot] at hdenot
    exact hdenot.1
  | poly T1 cs T2 =>
    simp [Ty.val_denot] at hdenot
    exact hdenot.1
  | cpoly B cs T =>
    simp [Ty.val_denot] at hdenot
    exact hdenot.1

-- NOTE: The following theorems are no longer needed after the type hierarchy collapse.
-- They relied on Denot.is_tight which is now trivially True.
--
-- theorem val_denot_is_tight {env : TypeEnv s}
--   (_hts : env.is_tight) (T : Ty .capt s) :
--   (Ty.val_denot env T).is_tight := trivial
-- theorem shape_val_denot_is_tight {env : TypeEnv s}
--   (hts : env.is_tight) (T : Ty .capt s) :
--   (Ty.val_denot env T).is_tight := val_denot_is_tight hts T

/-- Ported from old shape_val_denot_is_proper.
    Now uses Denot.is_proper which is simpler (monotonic ∧ transparent ∧ bool_independent). -/
theorem val_denot_is_proper {env : TypeEnv s} {T : Ty .capt s}
  (hts : EnvTyping Γ env m) :
  (Ty.val_denot env T).is_proper := by
  constructor
  · -- Prove: (Ty.val_denot env T).is_monotonic
    exact val_denot_is_monotonic (typed_env_is_monotonic hts) T
  · constructor
    · -- Prove: (Ty.val_denot env T).is_transparent
      exact val_denot_is_transparent (typed_env_is_transparent hts) T
    · -- Prove: (Ty.val_denot env T).is_bool_independent
      exact val_denot_is_bool_independent (typed_env_is_bool_independent hts) T

theorem val_denot_implyafter_lift {cs : CaptureSet s}
  (himp : (Ty.val_denot env T1).ImplyAfter H (Ty.val_denot env T2)) :
  (Ty.exp_denot env T1 cs).ImplyAfter H (Ty.exp_denot env T2 cs) := by
  intro m' hsub e heval
  simp [Ty.exp_denot] at heval ⊢
  apply eval_post_monotonic_general _ heval
  have himp' := Denot.imply_after_to_m_entails_after himp
  exact Mpost.entails_after_subsumes himp' hsub

/-- Ported from old exi_denot_implyafter_lift.
    Updated to use new exp_denot signature with CaptureSet. -/
theorem exi_denot_implyafter_lift {cs : CaptureSet s}
  (himp : (Ty.exi_val_denot env T1).ImplyAfter H (Ty.exi_val_denot env T2)) :
  (Ty.exi_exp_denot env T1 cs).ImplyAfter H (Ty.exi_exp_denot env T2 cs) := by
  intro m' hsub e heval
  simp [Ty.exi_exp_denot] at heval ⊢
  apply eval_post_monotonic_general _ heval
  have himp' := Denot.imply_after_to_m_entails_after himp
  exact Mpost.entails_after_subsumes himp' hsub

set_option maxHeartbeats 400000 in
-- This is a large case analysis proof.
theorem val_denot_enforces_captures {T : Ty .capt s}
  (hts : EnvTyping Γ env m) :
  ∀ e, (Ty.val_denot env T) m e ->
    resolve_reachability m.heap e ⊆ (T.captureSet).denot env m := by
  intro e ht
  cases T with
  | top =>
    -- captureSet = .empty, denotation gives resolve_reachability ⊆ .empty
    simp only [Ty.captureSet, CaptureSet.denot, CaptureSet.subst, CaptureSet.ground_denot]
    simp only [Ty.val_denot] at ht
    exact ht.2
  | tvar X =>
    -- captureSet = .empty, type variable denotation enforces purity
    simp only [Ty.captureSet, CaptureSet.denot, CaptureSet.subst, CaptureSet.ground_denot]
    simp only [Ty.val_denot] at ht
    -- From EnvTyping, we know the type variable denotation enforces purity
    have hpure := typed_env_enforces_pure hts X
    simp only [Denot.enforce_pure] at hpure
    exact hpure m e ht
  | unit =>
    -- captureSet = .empty, unit has empty reachability
    simp only [Ty.captureSet, CaptureSet.denot, CaptureSet.subst, CaptureSet.ground_denot]
    simp only [Ty.val_denot] at ht
    -- resolve m.heap e = some .unit
    cases e with
    | unit =>
      simp [resolve_reachability]
      exact CapabilitySet.Subset.refl
    | var x =>
      cases x with
      | free fx =>
        simp [resolve] at ht
        cases hcell : m.heap fx with
        | none => simp [hcell] at ht
        | some cell =>
          simp [hcell] at ht
          cases cell with
          | val v =>
            simp at ht
            -- v.unwrap = .unit
            simp [resolve_reachability]
            rw [reachability_of_loc_eq_resolve_reachability m fx v hcell]
            cases hv : v.unwrap
            all_goals simp_all [resolve_reachability]
            all_goals exact CapabilitySet.Subset.refl
          | _ => simp at ht
      | bound bx => cases bx
    | _ => simp [resolve] at ht
  | bool =>
    -- captureSet = .empty, bool has empty reachability
    simp only [Ty.captureSet, CaptureSet.denot, CaptureSet.subst, CaptureSet.ground_denot]
    simp only [Ty.val_denot] at ht
    cases e with
    | btrue =>
      simp [resolve_reachability]
      exact CapabilitySet.Subset.refl
    | bfalse =>
      simp [resolve_reachability]
      exact CapabilitySet.Subset.refl
    | var x =>
      cases x with
      | free fx =>
        simp [resolve] at ht
        cases hcell : m.heap fx with
        | none => simp [hcell] at ht
        | some cell =>
          simp [hcell] at ht
          cases cell with
          | val v =>
            simp at ht
            simp [resolve_reachability]
            rw [reachability_of_loc_eq_resolve_reachability m fx v hcell]
            cases hv : v.unwrap
            all_goals simp_all [resolve_reachability]
            all_goals exact CapabilitySet.Subset.refl
          | _ => simp at ht
      | bound bx => cases bx
    | _ => simp [resolve] at ht
  | cap cs =>
    -- captureSet = cs, e = .var (.free label), covers .epsilon label
    simp only [Ty.captureSet]
    simp only [Ty.val_denot] at ht
    obtain ⟨_, _, label, heq, hlookup, hcov⟩ := ht
    subst heq
    simp only [resolve_reachability, Memory.lookup] at hlookup ⊢
    simp [reachability_of_loc, hlookup]
    exact CapabilitySet.covers_eps_imp_singleton_eps_subset hcov
  | cell cs =>
    -- captureSet = cs, e = .var (.free l), covers .epsilon l
    simp only [Ty.captureSet]
    simp only [Ty.val_denot] at ht
    obtain ⟨_, l, _, heq, hlookup, hcov⟩ := ht
    subst heq
    simp only [resolve_reachability, Memory.lookup] at hlookup ⊢
    simp [reachability_of_loc, hlookup]
    exact CapabilitySet.covers_eps_imp_singleton_eps_subset hcov
  | reader cs =>
    -- captureSet = cs, resolve e = .reader (.free label), covers .ro label
    simp only [Ty.captureSet]
    simp only [Ty.val_denot] at ht
    obtain ⟨_, _, label, _, hres, hlookup, hcov⟩ := ht
    -- resolve_reachability for expression that resolves to .reader
    cases e with
    | reader x =>
      cases x with
      | free fx =>
        simp [resolve] at hres
        cases hres
        simp [resolve_reachability]
        exact CapabilitySet.covers_imp_singleton_subset hcov
      | bound bx => cases bx
    | var x =>
      cases x with
      | free fx =>
        simp [resolve] at hres
        cases hcell : m.heap fx with
        | none => simp [hcell] at hres
        | some cell =>
          simp [hcell] at hres
          cases cell with
          | val v =>
            simp at hres
            simp [resolve_reachability]
            rw [reachability_of_loc_eq_resolve_reachability m fx v hcell]
            cases hv : v.unwrap
            all_goals simp_all [resolve_reachability]
            exact CapabilitySet.covers_imp_singleton_subset hcov
          | _ => simp at hres
      | bound bx => cases bx
    | _ => simp [resolve] at hres
  | arrow T1 cs T2 =>
    -- captureSet = cs, expand_captures cs' ⊆ cs.denot
    simp only [Ty.captureSet]
    simp only [Ty.val_denot] at ht
    obtain ⟨_, _, cs', _, t0, hres, _, hR0_sub, _⟩ := ht
    cases e with
    | abs cs0 _ _ =>
      simp only [resolve, Option.some.injEq, Exp.abs.injEq] at hres
      obtain ⟨rfl, _, _⟩ := hres
      simp [resolve_reachability]
      exact hR0_sub
    | var x =>
      cases x with
      | free fx =>
        simp [resolve] at hres
        cases hcell : m.heap fx with
        | none => simp [hcell] at hres
        | some cell =>
          simp [hcell] at hres
          cases cell with
          | val v =>
            simp at hres
            simp [resolve_reachability]
            rw [reachability_of_loc_eq_resolve_reachability m fx v hcell]
            cases hv : v.unwrap <;> simp_all [resolve_reachability]
          | _ => simp at hres
      | bound bx => cases bx
    | _ => simp [resolve] at hres
  | poly T1 cs T2 =>
    -- captureSet = cs, expand_captures cs' ⊆ cs.denot
    simp only [Ty.captureSet]
    simp only [Ty.val_denot] at ht
    obtain ⟨_, _, cs', _, t0, hres, _, hR0_sub, _⟩ := ht
    cases e with
    | tabs cs0 _ _ =>
      simp only [resolve, Option.some.injEq, Exp.tabs.injEq] at hres
      obtain ⟨rfl, _, _⟩ := hres
      simp [resolve_reachability]
      exact hR0_sub
    | var x =>
      cases x with
      | free fx =>
        simp [resolve] at hres
        cases hcell : m.heap fx with
        | none => simp [hcell] at hres
        | some cell =>
          simp [hcell] at hres
          cases cell with
          | val v =>
            simp at hres
            simp [resolve_reachability]
            rw [reachability_of_loc_eq_resolve_reachability m fx v hcell]
            cases hv : v.unwrap <;> simp_all [resolve_reachability]
          | _ => simp at hres
      | bound bx => cases bx
    | _ => simp [resolve] at hres
  | cpoly B cs T =>
    -- captureSet = cs, expand_captures cs' ⊆ cs.denot
    simp only [Ty.captureSet]
    simp only [Ty.val_denot] at ht
    obtain ⟨_, _, cs', _, t0, hres, _, hR0_sub, _⟩ := ht
    cases e with
    | cabs cs0 _ _ =>
      simp only [resolve, Option.some.injEq, Exp.cabs.injEq] at hres
      obtain ⟨rfl, _, _⟩ := hres
      simp [resolve_reachability]
      exact hR0_sub
    | var x =>
      cases x with
      | free fx =>
        simp [resolve] at hres
        cases hcell : m.heap fx with
        | none => simp [hcell] at hres
        | some cell =>
          simp [hcell] at hres
          cases cell with
          | val v =>
            simp at hres
            simp [resolve_reachability]
            rw [reachability_of_loc_eq_resolve_reachability m fx v hcell]
            cases hv : v.unwrap <;> simp_all [resolve_reachability]
          | _ => simp at hres
      | bound bx => cases bx
    | _ => simp [resolve] at hres

theorem val_denot_refine {env : TypeEnv s} {T : Ty .capt s} {x : Var .var s}
  (hdenot : (Ty.val_denot env T) m (.var (x.subst (Subst.from_TypeEnv env)))) :
  (Ty.val_denot env (T.refineCaptureSet (.var .epsilon x)))
    m
    (.var (x.subst (Subst.from_TypeEnv env))) := by
  cases T with
  | top =>
    simp only [Ty.refineCaptureSet, Ty.val_denot] at hdenot ⊢
    exact hdenot
  | tvar X =>
    simp only [Ty.refineCaptureSet, Ty.val_denot] at hdenot ⊢
    exact hdenot
  | unit =>
    simp only [Ty.refineCaptureSet, Ty.val_denot] at hdenot ⊢
    exact hdenot
  | bool =>
    simp only [Ty.refineCaptureSet, Ty.val_denot] at hdenot ⊢
    exact hdenot
  | arrow T1 cs T2 =>
    simp only [Ty.refineCaptureSet, Ty.val_denot] at hdenot ⊢
    obtain ⟨hwf_e, hwf_cs, cs', x0, t0, hres, hwf_cs', hR0_sub, hbody⟩ := hdenot
    refine ⟨hwf_e, ?_, cs', x0, t0, hres, hwf_cs', ?_, ?_⟩
    · -- WfInHeap for (.var .epsilon x).subst
      simp only [CaptureSet.subst]
      cases hwf_e with
      | wf_var hwf_var =>
        exact CaptureSet.wf_of_var hwf_var
    · -- expand_captures m.heap cs' ⊆ (.var .epsilon x).denot env m
      -- Key: use wf_reach to show expand_captures = reachability_of_loc
      simp only [resolve] at hres
      cases hv : x.subst (Subst.from_TypeEnv env) with
      | free n =>
        simp only [hv] at hres hwf_e ⊢
        cases hcell : m.heap n with
        | none => simp [hcell] at hres
        | some cell =>
          simp [hcell] at hres
          cases cell with
          | val v =>
            simp at hres
            -- hres : v.unwrap = .abs cs' x0 t0
            -- By wf_reach: v.reachability = compute_reachability m.heap v.unwrap v.isVal
            have hwf_reach := m.wf.wf_reach n v.unwrap v.isVal v.reachability hcell
            -- Transport v.isVal along hres to get IsSimpleVal for the abs
            have habs_isval : (Exp.abs cs' x0 t0).IsSimpleVal := hres ▸ v.isVal
            -- compute_reachability for abs is expand_captures
            have hcomp : compute_reachability m.heap v.unwrap v.isVal = expand_captures m.heap cs' := by
              calc compute_reachability m.heap v.unwrap v.isVal
                  = compute_reachability m.heap (Exp.abs cs' x0 t0) habs_isval := by simp only [hres]
                _ = expand_captures m.heap cs' := rfl
            -- reachability_of_loc = v.reachability
            have hreach_loc : reachability_of_loc m.heap n = v.reachability := by
              simp only [reachability_of_loc, hcell]
            -- Chain: expand_captures = compute_reachability = v.reachability = reachability_of_loc
            have heq : expand_captures m.heap cs' = reachability_of_loc m.heap n := by
              rw [hreach_loc, hwf_reach, hcomp]
            -- (.var .epsilon x).denot env m = reachability_of_loc m.heap n
            simp only [CaptureSet.denot, CaptureSet.subst, hv, CaptureSet.ground_denot,
                       CapabilitySet.applyMut]
            rw [heq]
            exact CapabilitySet.Subset.refl
          | capability _ => simp at hres
          | masked => simp at hres
      | bound bx => cases bx
    · -- Body condition
      -- The body uses tracking set (.var .epsilon x).rename instead of cs.rename
      -- This requires showing the body only uses capabilities from (.var .epsilon x)
      sorry
  | poly T1 cs T2 =>
    simp only [Ty.refineCaptureSet, Ty.val_denot] at hdenot ⊢
    obtain ⟨hwf_e, hwf_cs, cs', x0, t0, hres, hwf_cs', hR0_sub, hbody⟩ := hdenot
    refine ⟨hwf_e, ?_, cs', x0, t0, hres, hwf_cs', ?_, ?_⟩
    · -- WfInHeap for (.var .epsilon x).subst
      simp only [CaptureSet.subst]
      cases hwf_e with
      | wf_var hwf_var =>
        exact CaptureSet.wf_of_var hwf_var
    · -- expand_captures ⊆ (.var .epsilon x).denot - same reasoning as arrow
      simp only [resolve] at hres
      cases hv : x.subst (Subst.from_TypeEnv env) with
      | free n =>
        simp only [hv] at hres hwf_e ⊢
        cases hcell : m.heap n with
        | none => simp [hcell] at hres
        | some cell =>
          simp [hcell] at hres
          cases cell with
          | val v =>
            simp at hres
            have hwf_reach := m.wf.wf_reach n v.unwrap v.isVal v.reachability hcell
            have htabs_isval : (Exp.tabs cs' x0 t0).IsSimpleVal := hres ▸ v.isVal
            have hcomp : compute_reachability m.heap v.unwrap v.isVal = expand_captures m.heap cs' := by
              calc compute_reachability m.heap v.unwrap v.isVal
                  = compute_reachability m.heap (Exp.tabs cs' x0 t0) htabs_isval := by simp only [hres]
                _ = expand_captures m.heap cs' := rfl
            have hreach_loc : reachability_of_loc m.heap n = v.reachability := by
              simp only [reachability_of_loc, hcell]
            have heq : expand_captures m.heap cs' = reachability_of_loc m.heap n := by
              rw [hreach_loc, hwf_reach, hcomp]
            simp only [CaptureSet.denot, CaptureSet.subst, hv, CaptureSet.ground_denot,
                       CapabilitySet.applyMut]
            rw [heq]; exact CapabilitySet.Subset.refl
          | capability _ => simp at hres
          | masked => simp at hres
      | bound bx => cases bx
    · -- Body condition
      sorry
  | cpoly B cs T =>
    simp only [Ty.refineCaptureSet, Ty.val_denot] at hdenot ⊢
    obtain ⟨hwf_e, hwf_cs, cs', x0, t0, hres, hwf_cs', hR0_sub, hbody⟩ := hdenot
    refine ⟨hwf_e, ?_, cs', x0, t0, hres, hwf_cs', ?_, ?_⟩
    · simp only [CaptureSet.subst]
      cases hwf_e with
      | wf_var hwf_var =>
        exact CaptureSet.wf_of_var hwf_var
    · simp only [resolve] at hres
      cases hv : x.subst (Subst.from_TypeEnv env) with
      | free n =>
        simp only [hv] at hres hwf_e ⊢
        cases hcell : m.heap n with
        | none => simp [hcell] at hres
        | some cell =>
          simp [hcell] at hres
          cases cell with
          | val v =>
            simp at hres
            have hwf_reach := m.wf.wf_reach n v.unwrap v.isVal v.reachability hcell
            have hcabs_isval : (Exp.cabs cs' x0 t0).IsSimpleVal := hres ▸ v.isVal
            have hcomp : compute_reachability m.heap v.unwrap v.isVal = expand_captures m.heap cs' := by
              calc compute_reachability m.heap v.unwrap v.isVal
                  = compute_reachability m.heap (Exp.cabs cs' x0 t0) hcabs_isval := by simp only [hres]
                _ = expand_captures m.heap cs' := rfl
            have hreach_loc : reachability_of_loc m.heap n = v.reachability := by
              simp only [reachability_of_loc, hcell]
            have heq : expand_captures m.heap cs' = reachability_of_loc m.heap n := by
              rw [hreach_loc, hwf_reach, hcomp]
            simp only [CaptureSet.denot, CaptureSet.subst, hv, CaptureSet.ground_denot,
                       CapabilitySet.applyMut]
            rw [heq]; exact CapabilitySet.Subset.refl
          | capability _ => simp at hres
          | masked => simp at hres
      | bound bx => cases bx
    · -- Body condition
      sorry
  | cap cs =>
    simp only [Ty.refineCaptureSet, Ty.val_denot] at hdenot ⊢
    obtain ⟨hwf_e, hwf_cs, label, heq, hlookup, hcov⟩ := hdenot
    -- heq : Exp.var (x.subst ...) = Exp.var (Var.free label)
    -- Extract variable equality via injection
    simp only [Exp.var.injEq] at heq
    -- Now heq : x.subst (Subst.from_TypeEnv env) = Var.free label
    refine ⟨hwf_e, ?_, label, ?_, hlookup, ?_⟩
    · -- WfInHeap for (.var .epsilon x).subst
      simp only [CaptureSet.subst]
      cases hwf_e with
      | wf_var hwf_var =>
        exact CaptureSet.wf_of_var hwf_var
    · -- e = .var (.free label)
      simp only [heq]
    · -- covers .epsilon label ((.var .epsilon x).denot env m)
      simp only [CaptureSet.denot, CaptureSet.subst, heq, CaptureSet.ground_denot, CapabilitySet.applyMut]
      -- reachability_of_loc for capability cell is singleton .epsilon label
      simp [Memory.lookup] at hlookup
      cases hcell : m.heap label with
      | none => simp [hcell] at hlookup
      | some cell =>
        simp [reachability_of_loc, hcell]
        cases cell with
        | val v => simp [hcell] at hlookup
        | capability cap =>
          exact CapabilitySet.covers.here Mutability.Le.refl
        | masked => simp [hcell] at hlookup
  | cell cs =>
    simp only [Ty.refineCaptureSet, Ty.val_denot] at hdenot ⊢
    obtain ⟨hwf_cs, label, b0, heq, hlookup, hcov⟩ := hdenot
    -- heq : Exp.var (x.subst ...) = Exp.var (Var.free label)
    simp only [Exp.var.injEq] at heq
    refine ⟨?_, label, b0, ?_, hlookup, ?_⟩
    · -- WfInHeap for (.var .epsilon x).subst
      simp only [CaptureSet.subst]
      -- x.subst gives us (.free label), which is well-formed
      rw [heq]
      exact CaptureSet.WfInHeap.wf_var_free (by simp [Memory.lookup] at hlookup; exact hlookup)
    · -- e = .var (.free label)
      simp only [heq]
    · -- covers .epsilon label ((.var .epsilon x).denot env m)
      simp only [CaptureSet.denot, CaptureSet.subst, heq, CaptureSet.ground_denot, CapabilitySet.applyMut]
      simp [Memory.lookup] at hlookup
      cases hcell : m.heap label with
      | none => simp [hcell] at hlookup
      | some cell =>
        simp [reachability_of_loc, hcell]
        cases cell with
        | val v => simp [hcell] at hlookup
        | capability cap =>
          exact CapabilitySet.covers.here Mutability.Le.refl
        | masked => simp [hcell] at hlookup
  | reader cs =>
    simp only [Ty.refineCaptureSet, Ty.val_denot] at hdenot ⊢
    obtain ⟨hwf_e, hwf_cs, loc, label, hres, hlookup, hcov⟩ := hdenot
    refine ⟨hwf_e, ?_, loc, label, hres, hlookup, ?_⟩
    · -- WfInHeap for (.var .epsilon x).subst
      simp only [CaptureSet.subst]
      cases hwf_e with
      | wf_var hwf_var =>
        exact CaptureSet.wf_of_var hwf_var
    · -- Need: covers .ro label ((.var .epsilon x).denot env m)
      simp only [CaptureSet.denot, CaptureSet.subst, CaptureSet.ground_denot, CapabilitySet.applyMut]
      -- The expression e = .var (x.subst ...) resolves to .reader (.free label)
      -- x.subst gives us the location, and reachability_of_loc gives the reachability
      simp only [resolve] at hres
      cases hv : x.subst (Subst.from_TypeEnv env) with
      | free n =>
        simp only [hv] at hres hwf_e ⊢
        cases hcell : m.heap n with
        | none => simp [hcell] at hres
        | some cell =>
          simp [hcell] at hres
          cases cell with
          | val v =>
            simp at hres
            -- v.unwrap = .reader (.free loc)
            -- By wf_reach: v.reachability = compute_reachability = .cap .ro loc
            have hwf_reach := m.wf.wf_reach n v.unwrap v.isVal v.reachability hcell
            have hreader_isval : (Exp.reader (Var.free loc)).IsSimpleVal := hres ▸ v.isVal
            have hcomp : compute_reachability m.heap v.unwrap v.isVal = .cap .ro loc := by
              calc compute_reachability m.heap v.unwrap v.isVal
                  = compute_reachability m.heap (Exp.reader (Var.free loc)) hreader_isval := by simp only [hres]
                _ = .cap .ro loc := rfl
            have hreach_loc : reachability_of_loc m.heap n = v.reachability := by
              simp only [reachability_of_loc, hcell]
            have heq : reachability_of_loc m.heap n = .cap .ro loc := by
              rw [hreach_loc, hwf_reach, hcomp]
            -- ground_denot for (.var .epsilon (Var.free n)) = reachability_of_loc m.heap n
            simp only [CaptureSet.ground_denot, CapabilitySet.applyMut]
            rw [heq]
            exact CapabilitySet.covers.here Mutability.Le.refl
          | capability _ => simp at hres
          | masked => simp at hres
      | bound bx => cases bx

end Capybara
