import Semantic.Consume.Semantics
import Semantic.Consume.TypeSystem
import Semantic.Prelude

namespace Consume

/-- Denotation of types. -/
def Denot := Memory -> Exp {} -> Prop

/-- Pre-denotation. It takes a capability to form a denotation. -/
def PreDenot := CapabilitySet -> Denot

/-- Capture-denotation. Given any memory, it produces a set of capabilities. -/
def CapDenot := Memory -> CapabilitySet

/-- A bound on capability sets. -/
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

/-- The denotation entails heap well-formedness. -/
def Denot.implies_wf (d : Denot) : Prop :=
  ∀ m e, d m e -> e.WfInHeap m.heap

/-- The denotation entails that the expression is a simple answer (value or variable). -/
def Denot.implies_simple_ans (d : Denot) : Prop :=
  ∀ m e, d m e -> e.IsSimpleAns

/-- The denotation is proper if it is monotonic, transparent,
  bool-independent, and implies heap well-formedness. -/
def Denot.is_proper (d : Denot) : Prop :=
  d.is_monotonic
  ∧ d.is_transparent
  ∧ d.is_bool_independent
  ∧ d.implies_wf

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
  rw [hx]
  change v.reachability = resolve_reachability m.heap v.unwrap
  -- v.reachability = compute_reachability m.heap v.unwrap v.isVal
  rw [Memory.reachability_invariant m x v hx]
  -- compute_reachability = resolve_reachability for simple values
  exact compute_reachability_eq_resolve_reachability m.heap v.unwrap v.isVal

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
  change d m .btrue <-> d m .bfalse
  exact hbool

def Denot.Imply (d1 d2 : Denot) : Prop :=
  ∀ m e,
    (d1 m e) ->
    (d2 m e)

def Denot.ImplyAt (d1 : Denot) (m : Memory) (d2 : Denot) : Prop :=
  ∀ e, d1 m e -> d2 m e

def Denot.ImplyAfter (d1 : Denot) (m : Memory) (d2 : Denot) : Prop :=
  ∀ m', m'.subsumes m -> d1.ImplyAt m' d2

theorem Denot.imply_implyat {d1 d2 : Denot}
  (himp : d1.Imply d2) : d1.ImplyAt m d2 := fun e h => himp m e h

theorem Denot.implyat_trans
  {d1 d2 : Denot}
  (himp1 : d1.ImplyAt m d2)
  (himp2 : d2.ImplyAt m d3) : d1.ImplyAt m d3 :=
  fun e h => himp2 e (himp1 e h)

lemma Denot.imply_after_to_m_entails_after {d1 d2 : Denot} {m : Memory}
  (himp : d1.ImplyAfter m d2) : d1.as_mpost.entails_after m d2.as_mpost :=
  fun m' hsub e h1 => himp m' hsub e h1

lemma Denot.imply_after_subsumes {d1 d2 : Denot}
  (himp : d1.ImplyAfter m1 d2) (hmem : m2.subsumes m1) : d1.ImplyAfter m2 d2 :=
  fun M hs => himp M (Memory.subsumes_trans hs hmem)

lemma Denot.imply_after_to_imply_at {d1 d2 : Denot}
  (himp : d1.ImplyAfter m d2) : d1.ImplyAt m d2 :=
  fun e h1 => himp m (Memory.subsumes_refl m) e h1

lemma Denot.imply_after_trans {d1 d2 d3 : Denot}
  (himp1 : d1.ImplyAfter m d2) (himp2 : d2.ImplyAfter m d3) : d1.ImplyAfter m d3 :=
  fun m' hsub e h1 => himp2 m' hsub e (himp1 m' hsub e h1)

lemma Denot.apply_imply_at {d1 d2 : Denot}
  (ht : d1 m e) (himp : d1.ImplyAt m d2) : d2 m e := himp e ht

/-- Type information for each kind of variable bindings in type context. -/
inductive TypeInfo : Sig -> Kind -> Type where
/-- Type information for a variable is a store location plus a peak set. -/
| var :
  Nat ->
  PeakSet s ->
  TypeInfo s .var
/-- Type information for a type variable is a denotation. -/
| tvar :
  Denot ->
  TypeInfo s .tvar
/-- Type information for a capture variable is a ground capture set. -/
| cvar :
  CaptureSet {} ->
  CapabilitySet ->
  TypeInfo s .cvar

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
  (Γ : TypeEnv s) (ground : CaptureSet {}) (cap : CapabilitySet := .empty) :
  TypeEnv (s,C) :=
  Γ.extend (.cvar ground cap)

def TypeEnv.lookup_var : (Γ : TypeEnv s) -> (x : BVar s .var) -> (Nat × PeakSet s)
| .extend _ (.var n ps), .here => (n, ps.rename Rename.succ)
| .extend Γ _, .there x =>
  match Γ.lookup_var x with
  | (n, ps) => (n, ps.rename Rename.succ)

def TypeEnv.lookup_tvar : (Γ : TypeEnv s) -> (x : BVar s .tvar) -> Denot
| .extend _ (.tvar T), .here => T
| .extend Γ _, .there x => Γ.lookup_tvar x

def TypeEnv.lookup_cvar : (Γ : TypeEnv s) -> (x : BVar s .cvar) -> CaptureSet {} × CapabilitySet
| .extend _ (.cvar cs cap), .here => (cs, cap)
| .extend Γ _, .there x => Γ.lookup_cvar x

def Subst.from_TypeEnv (env : TypeEnv s) : Subst s {} where
  var := fun x => .free (env.lookup_var x).1
  tvar := fun _ => .top
  cvar := fun c => (env.lookup_cvar c).1

def TypeEnv.WfInHeap (env : TypeEnv s) (H : Heap) : Prop :=
  (Subst.from_TypeEnv env).WfInHeap H

theorem Subst.from_TypeEnv_empty :
  Subst.from_TypeEnv TypeEnv.empty = Subst.id := by
  apply Subst.funext
  · intro x; cases x
  · intro X; cases X
  · intro C; cases C

/-- The substitution from TypeEnv is independent of the cap parameter in extend_cvar. -/
theorem Subst.from_TypeEnv_extend_cvar_cap_irrelevant
  {env : TypeEnv s} {cs : CaptureSet {}} {cap cap' : CapabilitySet} :
  Subst.from_TypeEnv (env.extend_cvar cs cap) =
  Subst.from_TypeEnv (env.extend_cvar cs cap') := by
  apply Subst.funext
  · intro x
    cases x with
    | there x => rfl
  · intro X
    cases X with
    | there X => rfl
  · intro C
    cases C with
    | here => rfl
    | there C => rfl

/-- Cap-irrelevance extends to environments further extended with extend_var. -/
theorem Subst.from_TypeEnv_extend_cvar_extend_var_cap_irrelevant
  {env : TypeEnv s} {cs : CaptureSet {}} {cap cap' : CapabilitySet}
  {x : Nat} {ps : PeakSet (s,C)} :
  Subst.from_TypeEnv ((env.extend_cvar cs cap).extend_var x ps) =
  Subst.from_TypeEnv ((env.extend_cvar cs cap').extend_var x ps) := by
  apply Subst.funext
  · intro y
    cases y with
    | here => rfl
    | there y =>
      cases y with
      | there y' => rfl
  · intro X
    cases X with
    | there X =>
      cases X with
      | there X' => rfl
  · intro C
    cases C with
    | there C =>
      cases C with
      | here => rfl
      | there C' => rfl

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
    exact .empty
  | union _ _ ih1 ih2 =>
    exact .union ih1 ih2
  | cvar =>
    exact .cvar
  | var m x =>
    cases x
    case bound b =>
      exact (ρ.lookup_var b).2.h.applyMut m
    case free f =>
      exact .empty


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

/-- The denotational `ground_denot` and operational `reachability` are pointwise equal:
    they share identical recursive definitions. -/
theorem CaptureSet.ground_denot_eq_reachability (cs : CaptureSet {}) (m : Memory) :
    cs.ground_denot m = cs.reachability m := by
  induction cs with
  | empty => rfl
  | var m0 x =>
    cases x with
    | bound bx => cases bx
    | free _ => rfl
  | cvar _ C => cases C
  | union cs1 cs2 ih1 ih2 =>
    change cs1.ground_denot m ∪ cs2.ground_denot m = _
    rw [ih1, ih2]
    rfl

def CaptureBound.denot : TypeEnv s -> CaptureBound s -> CapBoundDenot
| _, .unbound => fun _ => .top
| env, .bound cs => fun m => .set (cs.denot env m)

inductive CapabilitySet.BoundedBy : CapabilitySet -> CapabilityBound -> Prop where
| top :
  CapabilitySet.BoundedBy C .top
| set :
  C1 ⊆ C2 ->
  CapabilitySet.BoundedBy C1 (.set C2)

inductive CapabilityBound.SubsetEq : CapabilityBound -> CapabilityBound -> Prop where
| refl :
  CapabilityBound.SubsetEq B B
| set :
  C1 ⊆ C2 ->
  CapabilityBound.SubsetEq (.set C1) (.set C2)
| top :
  CapabilityBound.SubsetEq B .top

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
      exact CapabilitySet.BoundedBy.set (CapabilitySet.Subset.trans hbound_set hsub_set)
  | top => exact CapabilitySet.BoundedBy.top

/-- Whether this denotation enforces purity of the value. -/
def Denot.enforce_pure (d : Denot) : Prop :=
  ∀ m e,
    d m e ->
    resolve_reachability m.heap e ⊆ .empty

/-- `m'.preserves_liveness m R` says that every live mcell in `m` whose
    location is covered by capability set `R` (at any mutability) is still
    a live mcell in `m'` (with the same boolean value). It rules out
    `live → dead` transitions during evaluation on locations within `R` but
    allows new allocations and writes (boolean changes). This is the key
    invariant satisfied by function bodies: the `lock` in their typing
    context disables every consume peak of the body's budget `R0`, so no
    mcell reachable from `R0` can be dropped. Locations outside `R` carry
    no obligation, since the body cannot touch them anyway. -/
def Memory.preserves_liveness (m' m : Memory) (R : CapabilitySet) : Prop :=
  ∀ l b mu,
    R.covers mu l →
    m.heap l = some (.capability (.mcell b .live)) →
    m'.heap l = some (.capability (.mcell b .live))

/-- Reflexivity: a memory trivially preserves its own liveness. -/
theorem Memory.preserves_liveness_refl (m : Memory) (R : CapabilitySet) :
    m.preserves_liveness m R := by
  intro _ _ _ _ h
  exact h

/-- Transitivity (with the same reachability set). -/
theorem Memory.preserves_liveness_trans
    {m1 m2 m3 : Memory} {R : CapabilitySet}
    (h12 : m2.preserves_liveness m1 R)
    (h23 : m3.preserves_liveness m2 R) :
    m3.preserves_liveness m1 R := by
  intro l b mu hmu h
  exact h23 l b mu hmu (h12 l b mu hmu h)

mutual

/-- Value denotation for capturing types. -/
def Ty.val_denot : TypeEnv s -> Ty .capt s -> Denot
| _, .top => fun m e =>
  e.IsSimpleAns ∧ e.WfInHeap m.heap ∧ resolve_reachability m.heap e ⊆ .empty
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
  ∃ (label : Nat) (b0 : Bool) (ℓ0 : Liveness),
    resolve m.heap e = some (.reader (.free label)) ∧
    m.lookup label = some (.capability (.mcell b0 ℓ0)) ∧
    (cs.denot env m).covers .ro label
| env, .cell cs => fun m e =>
  (cs.subst (Subst.from_TypeEnv env)).WfInHeap m.heap ∧
  ∃ l b0 ℓ0,
    e = .var (.free l) ∧
    m.lookup l = some (.capability (.mcell b0 ℓ0)) ∧
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
      m'.is_compatible R0 ->
      Ty.val_denot env T1 m' (.var (.free arg)) ->
      Eval R0 m' (t0.subst (Subst.openVar (.free arg)))
        (fun v m'' =>
          Ty.exi_val_denot
            (env.extend_var arg (compute_peakset env T1.captureSet)) T2 m'' v
          ∧ m''.preserves_liveness m' R0))
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
      m'.is_compatible R0 ->
      denot.is_proper ->
      denot.implies_simple_ans ->
      denot.ImplyAfter m' (Ty.val_denot env T1) ->
      denot.enforce_pure ->
      Eval R0 m' (t0.subst (Subst.openTVar .top))
        (fun v m'' =>
          Ty.exi_val_denot (env.extend_tvar denot) T2 m'' v
          ∧ m''.preserves_liveness m' R0))
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
      m'.is_compatible R0 ->
      ((A0 m').BoundedBy (B.denot env m')) ->
      Eval R0 m' (t0.subst (Subst.openCVar CS))
        (fun v m'' =>
          Ty.exi_val_denot
            (env.extend_cvar CS (cap := CS.ground_denot m')) T m'' v
          ∧ m''.preserves_liveness m' R0))

/-- Value denotation for existential types. -/
def Ty.exi_val_denot : TypeEnv s -> Ty .exi s -> Denot
| ρ, .typ T => Ty.val_denot ρ T
| ρ, .exi T => fun m e =>
  match resolve m.heap e with
  | some (.pack CS x) =>
    CS.WfInHeap m.heap ∧
    Ty.val_denot (ρ.extend_cvar CS (cap := CS.ground_denot m)) T m (.var x)
  | _ => False

/-- Expression denotation for capturing types.
    Takes an explicit capture set (the use set from the typing judgment). -/
def Ty.exp_denot : TypeEnv s -> Ty .capt s -> PreDenot
| ρ, T, R => fun m (e : Exp {}) =>
  Eval R m e (Ty.val_denot ρ T).as_mpost

/-- Expression denotation for existential types.
    Takes an explicit capture set (the use set from the typing judgment). -/
def Ty.exi_exp_denot : TypeEnv s -> Ty .exi s -> PreDenot
| ρ, T, R => fun m (e : Exp {}) =>
  Eval R m e (Ty.exi_val_denot ρ T).as_mpost

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
instance instCaptureBoundHasDenotation :
  HasDenotation (CaptureBound s) (TypeEnv s) CapBoundDenot where
  interp := CaptureBound.denot


def EnvTyping : Ctx s -> TypeEnv s -> Memory -> Prop
| .empty, .empty, _ => True
| .push Γ (.var T), .extend env (.var n ps), m =>
  ⟦T⟧_[env] m (.var (.free n)) ∧
  ps = T.captureSet.peakset Γ ∧
  EnvTyping Γ env m
| .push Γ (.tvar S), .extend env (.tvar denot), m =>
  denot.is_proper ∧
  denot.implies_wf ∧
  denot.implies_simple_ans ∧
  denot.ImplyAfter m ⟦S.core⟧_[env] ∧
  denot.enforce_pure ∧
  EnvTyping Γ env m
| .push Γ (.cvar _ B), .extend env (.cvar cs cap), m =>
  (cs.WfInHeap m.heap) ∧
  ((B.subst (Subst.from_TypeEnv env)).WfInHeap m.heap) ∧
  (cap.BoundedBy (B.denot env m)) ∧
  cap = cs.ground_denot m ∧
  EnvTyping Γ env m
| .lock Γ, env, m => EnvTyping Γ env m

/-- Helper lemma: For bound variables, `CaptureSet.peaks` equals `compute_peaks`. -/
theorem peaks_var_bound_eq {s : Sig} {Γ : Ctx s} {ρ : TypeEnv s}
    (h : EnvTyping Γ ρ mem) (x : BVar s .var) (m0 : Mutability) :
    CaptureSet.peaksVarBound Γ m0 x = (ρ.lookup_var x).2.cs.applyMut m0 := by
  match s, Γ, ρ, x with
  | _, .push Γ' (.var T), .extend ρ' (.var n ps), .here =>
    simp only [EnvTyping] at h
    obtain ⟨_, hps, _⟩ := h
    rw [CaptureSet.peaksVarBound]
    change CaptureSet.applyMut m0 ((CaptureSet.peaks Γ' T.captureSet).rename Rename.succ) =
      CaptureSet.applyMut m0 (ps.cs.rename Rename.succ)
    rw [hps]
    rfl
  | _, .push Γ' (.var T), .extend ρ' (.var n ps), .there x' =>
    simp only [EnvTyping] at h
    obtain ⟨_, _, h'⟩ := h
    rw [CaptureSet.peaksVarBound]
    rw [peaks_var_bound_eq h' x' m0]
    exact CaptureSet.applyMut_rename
  | _, .push Γ' (.tvar S), .extend ρ' (.tvar denot), .there x' =>
    simp only [EnvTyping] at h
    obtain ⟨_, _, _, _, _, h'⟩ := h
    rw [CaptureSet.peaksVarBound]
    rw [peaks_var_bound_eq h' x' m0]
    exact CaptureSet.applyMut_rename
  | _, .push Γ' (.cvar _ B), .extend ρ' (.cvar cs _), .there x' =>
    simp only [EnvTyping] at h
    obtain ⟨_, _, _, _, h'⟩ := h
    rw [CaptureSet.peaksVarBound]
    rw [peaks_var_bound_eq h' x' m0]
    exact CaptureSet.applyMut_rename
  | _, .lock Γ', ρ, x =>
    simp only [EnvTyping] at h
    rw [CaptureSet.peaksVarBound]
    exact peaks_var_bound_eq h x m0
termination_by sizeOf Γ

theorem compute_peaks_correct (h : EnvTyping Γ ρ m) :
  ∀ C, CaptureSet.peaks Γ C = compute_peaks ρ C := by
  intro C
  induction C
  case empty => simp only [CaptureSet.peaks, compute_peaks]
  case union ih1 ih2 =>
    simp only [CaptureSet.peaks, compute_peaks, Union.union]
    rw [ih1, ih2]
  case cvar m c => simp only [CaptureSet.peaks, compute_peaks]
  case var m c =>
    cases c with
    | free n =>
      simp only [CaptureSet.peaks, compute_peaks]
      rfl
    | bound x =>
      -- Use the helper lemma
      simp only [compute_peaks]
      rw [CaptureSet.peaks]
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

/-- `m.is_access_compat Γ ρ C` says that every `.access`-mode peak of `C`
    (under `Γ`) has its denoted capability set live in `m`. Operationally:
    cells reachable through `C`'s access bindings are not dropped. This is
    the post-condition that flows from a `SemanticTyping`: `.access`-marked
    capabilities remain live in the result memory (because evaluation under
    `C`'s budget can only drop `.consume`-marked cells). -/
def Memory.is_access_compat
    {s : Sig} (m : Memory) (Γ : Ctx s) (ρ : TypeEnv s) (C : CaptureSet s) : Prop :=
  ∀ mu c,
    (CaptureSet.cvar mu c) ⊆ C.peaks Γ →
    AccessiblePeak Γ c →
    m.is_compatible (((ρ.lookup_cvar c).2).applyMut mu)

/-- `m.preserves_empty_mcells m' Γ ρ` says that for every `.empty`-mode cvar
    binding in `Γ`, the mcells in its denoted capability set keep their exact
    state (boolean and liveness) from `m` to `m'`. This captures the frame
    intuition for cells that the current expression cannot see at all
    (`.empty` mode), so it must not modify them. -/
def Memory.preserves_empty_mcells
    {s : Sig} (m m' : Memory) (Γ : Ctx s) (ρ : TypeEnv s) : Prop :=
  ∀ c B locked,
    Γ.LookupCVar c UseMode.empty B locked →
    ∀ mu l b ℓ,
      CapabilitySet.hasmem mu l ((ρ.lookup_cvar c).2) →
      m.heap l = some (.capability (.mcell b ℓ)) →
      m'.heap l = some (.capability (.mcell b ℓ))

/-- `is_access_compat` is vacuous when `C = ∅`, since `(∅ : CaptureSet s).peaks Γ`
    has no cvar elements. -/
theorem Memory.is_access_compat_empty
    {s : Sig} (m : Memory) (Γ : Ctx s) (ρ : TypeEnv s) :
    m.is_access_compat Γ ρ (∅ : CaptureSet s) := by
  intro mu c hsub _
  -- (∅ : CaptureSet s).peaks Γ reduces to .empty.
  rw [show (∅ : CaptureSet s) = CaptureSet.empty from rfl, CaptureSet.peaks.eq_1] at hsub
  cases hsub

/-- Reflexivity: a memory trivially preserves its own `.empty`-mode mcells. -/
theorem Memory.preserves_empty_mcells_refl
    {s : Sig} (m : Memory) (Γ : Ctx s) (ρ : TypeEnv s) :
    m.preserves_empty_mcells m Γ ρ := by
  intro _ _ _ _ _ _ _ _ _ hheap
  exact hheap

/-- Transitivity: preservation composes through an intermediate memory. -/
theorem Memory.preserves_empty_mcells_trans
    {s : Sig} {m1 m2 m3 : Memory} {Γ : Ctx s} {ρ : TypeEnv s}
    (h12 : m1.preserves_empty_mcells m2 Γ ρ)
    (h23 : m2.preserves_empty_mcells m3 Γ ρ) :
    m1.preserves_empty_mcells m3 Γ ρ := by
  intro c B locked hlookup mu l b ℓ hmem hheap
  exact h23 c B locked hlookup mu l b ℓ hmem (h12 c B locked hlookup mu l b ℓ hmem hheap)

/-- Semantic typing.
    *Pre*: every cell reached via `C` (whether `.access` or `.consume`) must be
    live at the start (`m.is_compatible (C.denot ρ m)`).
    *Post*: in any reachable result memory `m'`,
      (1) every `.access`-mode peak of `C` is still live (`is_access_compat`),
      (2) every `.empty`-mode cvar binding in `Γ` has its mcells unchanged
          from `m` to `m'` (`preserves_empty_mcells`).
    The `.consume`-mode peaks of `C` may have been dropped during evaluation,
    so we make no liveness claim about them in the result. -/
def SemanticTyping (C : CaptureSet s) (Γ : Ctx s) (e : Exp s) (E : Ty .exi s) : Prop :=
  ∀ ρ m,
    EnvTyping Γ ρ m →
    m.is_compatible (C.denot ρ m) →
    Eval (C.denot ρ m) m (e.subst (Subst.from_TypeEnv ρ))
      (fun v m' => Ty.exi_val_denot ρ E m' v
                 ∧ m'.is_access_compat Γ ρ C
                 ∧ Memory.preserves_empty_mcells m m' Γ ρ)

notation:65 C " # " Γ " ⊨ " e " : " T => SemanticTyping C Γ e T

theorem Subst.from_TypeEnv_weaken_open {env : TypeEnv s} {x : Nat} {ps : PeakSet s} :
  (Subst.from_TypeEnv env).lift.comp (Subst.openVar (.free x)) =
    Subst.from_TypeEnv (env.extend_var x ps) := by
  apply Subst.funext
  · intro y
    cases y with
    | here => rfl
    | there y' => rfl
  · intro X
    cases X
    rfl
  · intro C
    cases C with
    | there C' =>
      change (((Subst.from_TypeEnv env).lift).cvar (.there C')).subst (Subst.openVar (.free x)) =
        (env.lookup_cvar C').1
      rw [Subst.lift_there_cvar_eq]
      exact CaptureSet.weaken_openVar

theorem Exp.from_TypeEnv_weaken_open {s : Sig} {env : TypeEnv s} {n : Nat}
    {e : Exp (Sig.extend_var s)} {ps : PeakSet s} :
  (e.subst (Subst.from_TypeEnv env).lift).subst (Subst.openVar (.free n)) =
    e.subst (Subst.from_TypeEnv (env.extend_var n ps)) := by
  rw [Exp.subst_comp]
  exact congrArg _ Subst.from_TypeEnv_weaken_open

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
    case there X' => rfl
  · intro C
    cases C with
    | there C' =>
      change (((Subst.from_TypeEnv env).lift).cvar (.there C')).subst (Subst.openTVar .top) =
        (env.lookup_cvar C').1
      rw [Subst.lift_there_cvar_eq]
      exact CaptureSet.weaken_openTVar

theorem Exp.from_TypeEnv_weaken_open_tvar
  {s : Sig} {env : TypeEnv s} {d : Denot} {e : Exp (Sig.extend_tvar s)} :
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
    case here =>
      rfl
    case there C' =>
      change (((Subst.from_TypeEnv env).lift).cvar (.there C')).subst (Subst.openCVar cs) =
        (env.lookup_cvar C').1
      rw [Subst.lift_there_cvar_eq]
      exact CaptureSet.weaken_openCVar

theorem Exp.from_TypeEnv_weaken_open_cvar
  {s : Sig} {env : TypeEnv s} {cs : CaptureSet {}} {e : Exp (Sig.extend_cvar s)} :
  (e.subst (Subst.from_TypeEnv env).lift).subst (Subst.openCVar cs) =
    e.subst (Subst.from_TypeEnv (env.extend_cvar cs)) := by
  rw [Exp.subst_comp]
  exact congrArg _ Subst.from_TypeEnv_weaken_open_cvar

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
        change (((Subst.from_TypeEnv ρ).lift.lift).var (.there (.there v))).subst
          (Subst.unpack cs (.free x)) = .free (ρ.lookup_var v).1
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
        -- Need to show: (lift.lift.cvar (.there .here)).subst unpack = cs
        -- This is unpack.cvar (.there .here) = cs by definition
        change (((Subst.from_TypeEnv ρ).lift.lift).cvar (.there (.here))).subst
          (Subst.unpack cs (.free x)) = cs
        rfl
      case there c0 =>
        have helper : ∀ (g : CaptureSet {}),
            ((g.rename Rename.succ).rename Rename.succ).subst
              (Subst.unpack cs (.free x)) = g := by
          intro g
          induction g with
          | empty => rfl
          | union g1 g2 ih1 ih2 =>
            show CaptureSet.subst _ _ = _
            simp only [CaptureSet.rename, CaptureSet.subst]
            rw [ih1, ih2]
          | var m v =>
            cases v with
            | bound bv => cases bv
            | free n => rfl
          | cvar m cv => cases cv
        change CaptureSet.subst (CaptureSet.rename (CaptureSet.rename (ρ.lookup_cvar c0).1
          Rename.succ) Rename.succ) (Subst.unpack cs (.free x)) = _
        rw [helper (ρ.lookup_cvar c0).1]
        rfl

/-- All type variable denotations in the environment imply well-formedness. -/
def TypeEnv.is_implying_wf (env : TypeEnv s) : Prop :=
  ∀ (X : BVar s .tvar),
    (env.lookup_tvar X).implies_wf

/-- All type variable denotations in the environment imply simple answer. -/
def TypeEnv.is_implying_simple_ans (env : TypeEnv s) : Prop :=
  ∀ (X : BVar s .tvar),
    (env.lookup_tvar X).implies_simple_ans

/-- An environment typing implies that all type variable denotations imply simple answer. -/
theorem typed_env_is_implying_simple_ans
  (ht : EnvTyping Γ env mem) :
  env.is_implying_simple_ans := by
  induction Γ with
  | empty =>
    cases env with
    | empty =>
      unfold TypeEnv.is_implying_simple_ans
      intro x
      cases x
  | push Γ k ih =>
    cases env with
    | extend env' info =>
      cases k with
      | var T =>
        cases info with
        | var n ps =>
          change
            ⟦T⟧_[env'] mem (.var (.free n)) ∧
              ps = T.captureSet.peakset Γ ∧
              EnvTyping Γ env' mem at ht
          obtain ⟨_, _, ht'⟩ := ht
          have ih_result := ih ht'
          unfold TypeEnv.is_implying_simple_ans at ih_result ⊢
          intro x
          cases x with
          | there x =>
            exact ih_result x
      | tvar S =>
        cases info with
        | tvar d =>
          change
            d.is_proper ∧
              d.implies_wf ∧
              d.implies_simple_ans ∧
              d.ImplyAfter mem ⟦S.core⟧_[env'] ∧
              d.enforce_pure ∧
              EnvTyping Γ env' mem at ht
          have ⟨_, _, himplies, _, _, ht'⟩ := ht
          have ih_result := ih ht'
          unfold TypeEnv.is_implying_simple_ans at ih_result ⊢
          intro x
          cases x with
          | here =>
            exact himplies
          | there x =>
            exact ih_result x
      | cvar useM B =>
        cases info with
        | cvar cs cap =>
          change
            cs.WfInHeap mem.heap ∧
              (B.subst (Subst.from_TypeEnv env')).WfInHeap mem.heap ∧
              cap.BoundedBy (B.denot env' mem) ∧
              cap = cs.ground_denot mem ∧
              EnvTyping Γ env' mem at ht
          have ⟨hwf, _, hsub, _, ht'⟩ := ht
          have ih_result := ih ht'
          unfold TypeEnv.is_implying_simple_ans at ih_result ⊢
          intro x
          cases x with
          | there x =>
            exact ih_result x
  | lock Γ' ih =>
    change EnvTyping Γ' env mem at ht
    exact ih ht

/-- An environment typing implies that all type variable denotations imply well-formedness. -/
theorem typed_env_is_implying_wf
  (ht : EnvTyping Γ env mem) :
  env.is_implying_wf := by
  induction Γ with
  | empty =>
    cases env with
    | empty =>
      unfold TypeEnv.is_implying_wf
      intro x
      cases x
  | push Γ k ih =>
    cases env with
    | extend env' info =>
      cases k with
      | var T =>
        cases info with
        | var n ps =>
          change
            ⟦T⟧_[env'] mem (.var (.free n)) ∧
              ps = T.captureSet.peakset Γ ∧
              EnvTyping Γ env' mem at ht
          obtain ⟨_, _, ht'⟩ := ht
          have ih_result := ih ht'
          unfold TypeEnv.is_implying_wf at ih_result ⊢
          intro x
          cases x with
          | there x =>
            exact ih_result x
      | tvar S =>
        cases info with
        | tvar d =>
          change
            d.is_proper ∧
              d.implies_wf ∧
              d.implies_simple_ans ∧
              d.ImplyAfter mem ⟦S.core⟧_[env'] ∧
              d.enforce_pure ∧
              EnvTyping Γ env' mem at ht
          have ⟨_, himplies, _, _, _, ht'⟩ := ht
          have ih_result := ih ht'
          unfold TypeEnv.is_implying_wf at ih_result ⊢
          intro x
          cases x with
          | here =>
            exact himplies
          | there x =>
            exact ih_result x
      | cvar useM B =>
        cases info with
        | cvar cs cap =>
          change
            cs.WfInHeap mem.heap ∧
              (B.subst (Subst.from_TypeEnv env')).WfInHeap mem.heap ∧
              cap.BoundedBy (B.denot env' mem) ∧
              cap = cs.ground_denot mem ∧
              EnvTyping Γ env' mem at ht
          have ⟨hwf, _, hsub, _, ht'⟩ := ht
          have ih_result := ih ht'
          unfold TypeEnv.is_implying_wf at ih_result ⊢
          intro x
          cases x with
          | there x =>
            exact ih_result x
  | lock Γ' ih =>
    change EnvTyping Γ' env mem at ht
    exact ih ht

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
      unfold TypeEnv.is_enforcing_pure
      intro x
      cases x
  | push Γ k ih =>
    cases env with
    | extend env' info =>
      cases k with
      | var T =>
        cases info with
        | var n ps =>
          change
            ⟦T⟧_[env'] mem (.var (.free n)) ∧
              ps = T.captureSet.peakset Γ ∧
              EnvTyping Γ env' mem at ht
          obtain ⟨_, _, ht'⟩ := ht
          have ih_result := ih ht'
          unfold TypeEnv.is_enforcing_pure at ih_result ⊢
          intro x
          cases x with
          | there x =>
            exact ih_result x
      | tvar S =>
        cases info with
        | tvar d =>
          change
            d.is_proper ∧
              d.implies_wf ∧
              d.implies_simple_ans ∧
              d.ImplyAfter mem ⟦S.core⟧_[env'] ∧
              d.enforce_pure ∧
              EnvTyping Γ env' mem at ht
          have ⟨_, _, _, _, hpure, ht'⟩ := ht
          have ih_result := ih ht'
          unfold TypeEnv.is_enforcing_pure at ih_result ⊢
          intro x
          cases x with
          | here =>
            exact hpure
          | there x =>
            exact ih_result x
      | cvar useM B =>
        cases info with
        | cvar cs cap =>
          change
            cs.WfInHeap mem.heap ∧
              (B.subst (Subst.from_TypeEnv env')).WfInHeap mem.heap ∧
              cap.BoundedBy (B.denot env' mem) ∧
              cap = cs.ground_denot mem ∧
              EnvTyping Γ env' mem at ht
          have ⟨hwf, _, hsub, _, ht'⟩ := ht
          have ih_result := ih ht'
          unfold TypeEnv.is_enforcing_pure at ih_result ⊢
          intro x
          cases x with
          | there x =>
            exact ih_result x
  | lock Γ' ih =>
    change EnvTyping Γ' env mem at ht
    exact ih ht

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
            change Ty.val_denot _ _ _ _ at htype
            cases T with
            | top =>
              unfold Ty.val_denot at htype
              exact htype.2.1
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
              obtain ⟨_, l, _, _, hl, hlookup, _⟩ := htype
              cases hl
              change m.heap n = some (.capability (.mcell _ _)) at hlookup
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
                change Var.WfInHeap (.free n) m.heap
                exact hwf_var
              | there x' =>
                change Var.WfInHeap (.free (ρ'.lookup_var x').1) m.heap
                exact ih_wf.wf_var x'
            · intro X
              cases X with
              | there X' =>
                change PureTy.WfInHeap ((Subst.from_TypeEnv ρ').tvar X') m.heap
                exact ih_wf.wf_tvar X'
            · intro C_var
              cases C_var with
              | there C' =>
                change CaptureSet.WfInHeap (ρ'.lookup_cvar C').1 m.heap
                exact ih_wf.wf_cvar C'
      | tvar S =>
        -- Type variable binding: doesn't affect term variable substitution
        cases info with
        | tvar denot =>
          unfold EnvTyping at htyping
          have ⟨_, _, _, _, _, htyping'⟩ := htyping
          have ih_wf := ih htyping'
          constructor
          · intro x
            cases x with
            | there x' =>
              change Var.WfInHeap (.free (ρ'.lookup_var x').1) m.heap
              exact ih_wf.wf_var x'
          · intro X
            cases X with
            | here =>
              change PureTy.WfInHeap .top m.heap
              apply Ty.WfInHeap.wf_top
            | there X' =>
              change PureTy.WfInHeap ((Subst.from_TypeEnv ρ').tvar X') m.heap
              exact ih_wf.wf_tvar X'
          · intro C_var
            cases C_var with
            | there C' =>
              change CaptureSet.WfInHeap (ρ'.lookup_cvar C').1 m.heap
              exact ih_wf.wf_cvar C'
      | cvar useM B =>
        -- Capture variable binding: doesn't affect term variable substitution
        cases info with
        | cvar cs cap =>
          unfold EnvTyping at htyping
          have ⟨hwf, _, hsub, _, htyping'⟩ := htyping
          have ih_wf := ih htyping'
          constructor
          · intro x
            cases x with
            | there x' =>
              change Var.WfInHeap (.free (ρ'.lookup_var x').1) m.heap
              exact ih_wf.wf_var x'
          · intro X
            cases X with
            | there X' =>
              change PureTy.WfInHeap ((Subst.from_TypeEnv ρ').tvar X') m.heap
              exact ih_wf.wf_tvar X'
          · intro C_var
            cases C_var with
            | here =>
              change CaptureSet.WfInHeap cs m.heap
              exact hwf
            | there C' =>
              change CaptureSet.WfInHeap (ρ'.lookup_cvar C').1 m.heap
              exact ih_wf.wf_cvar C'
  | lock Γ' ih =>
    change EnvTyping Γ' ρ m at htyping
    exact ih htyping

def Denot.Equiv (d1 d2 : Denot) : Prop :=
  ∀ m e,
    (d1 m e) ↔ (d2 m e)

instance Denot.instHasEquiv : HasEquiv Denot where
  Equiv := Denot.Equiv

def Denot.equiv_refl (d : Denot) : d ≈ d := fun _ _ => Iff.rfl

def Denot.equiv_symm (d1 d2 : Denot) : d1 ≈ d2 -> d2 ≈ d1 :=
  fun h m e => .symm (h m e)

def Denot.equiv_trans (d1 d2 d3 : Denot) :
    d1 ≈ d2 -> d2 ≈ d3 -> d1 ≈ d3 :=
  fun h12 h23 m e => .trans (h12 m e) (h23 m e)

theorem Denot.eq_to_equiv (d1 d2 : Denot) : d1 = d2 -> d1 ≈ d2 := by
  intro h m e; grind

theorem Denot.equiv_ltr {d1 d2 : Denot}
  (heqv : d1 ≈ d2) (h1 : d1 m e) : d2 m e := (heqv m e).mp h1

theorem Denot.equiv_rtl {d1 d2 : Denot}
  (heqv : d1 ≈ d2) (h2 : d2 m e) : d1 m e := (heqv m e).mpr h2

theorem Denot.equiv_to_imply {d1 d2 : Denot}
  (heqv : d1 ≈ d2) : (d1.Imply d2) ∧ (d2.Imply d1) :=
  ⟨fun _ _ => (heqv _ _).mp, fun _ _ => (heqv _ _).mpr⟩

theorem Denot.equiv_to_imply_l {d1 d2 : Denot}
  (heqv : d1 ≈ d2) : d1.Imply d2 := (Denot.equiv_to_imply heqv).1

theorem Denot.equiv_to_imply_r {d1 d2 : Denot}
  (heqv : d1 ≈ d2) : d2.Imply d1 := (Denot.equiv_to_imply heqv).2

theorem Denot.imply_to_entails (d1 d2 : Denot)
  (himp : d1.Imply d2) : d1.as_mpost.entails d2.as_mpost :=
  fun _ _ => himp _ _

theorem Denot.imply_refl (d : Denot) : d.Imply d := fun _ _ => id

theorem Denot.imply_trans {d1 d2 d3 : Denot}
  (h1 : d1.Imply d2) (h2 : d2.Imply d3) : d1.Imply d3 :=
  fun m e h => h2 m e (h1 m e h)

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

structure TypeEnv.IsMonotonic (env : TypeEnv s) : Prop where
  tvar : ∀ (X : BVar s .tvar),
    (env.lookup_tvar X).is_monotonic

def TypeEnv.is_transparent (env : TypeEnv s) : Prop :=
  ∀ (X : BVar s .tvar),
    (env.lookup_tvar X).is_transparent

def TypeEnv.is_bool_independent (env : TypeEnv s) : Prop :=
  ∀ (X : BVar s .tvar),
    (env.lookup_tvar X).is_bool_independent

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
          change
            ⟦T⟧_[env'] mem (.var (.free n)) ∧
              ps = T.captureSet.peakset Γ ∧
              EnvTyping Γ env' mem at ht
          obtain ⟨_, _, ht'⟩ := ht
          have ih_result := ih ht'
          constructor
          · intro x
            cases x with
            | there x =>
              exact ih_result.tvar x
      | tvar S =>
        cases info with
        | tvar d =>
          change
            d.is_proper ∧
              d.implies_wf ∧
              d.implies_simple_ans ∧
              d.ImplyAfter mem ⟦S.core⟧_[env'] ∧
              d.enforce_pure ∧
              EnvTyping Γ env' mem at ht
          have ⟨hproper, _, _, _, _, ht'⟩ := ht
          have ih_result := ih ht'
          constructor
          · intro x
            cases x with
            | here =>
              -- hproper says d.is_proper
              -- We need d.is_monotonic
              -- Denot.is_proper = is_monotonic ∧ is_transparent ∧ is_bool_independent
              exact hproper.1
            | there x =>
              exact ih_result.tvar x
      | cvar useM B =>
        cases info with
        | cvar cs cap =>
          change
            cs.WfInHeap mem.heap ∧
              (B.subst (Subst.from_TypeEnv env')).WfInHeap mem.heap ∧
              cap.BoundedBy (B.denot env' mem) ∧
              cap = cs.ground_denot mem ∧
              EnvTyping Γ env' mem at ht
          have ⟨hwf, _, hsub, _, ht'⟩ := ht
          have ih_result := ih ht'
          constructor
          · intro x
            cases x with
            | there x =>
              exact ih_result.tvar x
  | lock Γ' ih =>
    change EnvTyping Γ' env mem at ht
    exact ih ht

theorem typed_env_is_transparent
  (ht : EnvTyping Γ env mem) :
  env.is_transparent := by
  induction Γ with
  | empty =>
    cases env with
    | empty =>
      unfold TypeEnv.is_transparent
      intro x
      cases x
  | push Γ k ih =>
    cases env with
    | extend env' info =>
      cases k with
      | var T =>
        cases info with
        | var n ps =>
          change
            ⟦T⟧_[env'] mem (.var (.free n)) ∧
              ps = T.captureSet.peakset Γ ∧
              EnvTyping Γ env' mem at ht
          obtain ⟨_, _, ht'⟩ := ht
          have ih_result := ih ht'
          unfold TypeEnv.is_transparent at ih_result ⊢
          intro x
          cases x with
          | there x =>
            exact ih_result x
      | tvar S =>
        cases info with
        | tvar d =>
          change
            d.is_proper ∧
              d.implies_wf ∧
              d.implies_simple_ans ∧
              d.ImplyAfter mem ⟦S.core⟧_[env'] ∧
              d.enforce_pure ∧
              EnvTyping Γ env' mem at ht
          have ⟨hproper, _, _, _, _, ht'⟩ := ht
          have ih_result := ih ht'
          unfold TypeEnv.is_transparent at ih_result ⊢
          intro x
          cases x with
          | here =>
            -- hproper says d.is_proper
            -- We need d.is_transparent
            -- Denot.is_proper = is_monotonic ∧ is_transparent ∧ is_bool_independent
            exact hproper.2.1
          | there x =>
            exact ih_result x
      | cvar useM B =>
        cases info with
        | cvar cs cap =>
          change
            cs.WfInHeap mem.heap ∧
              (B.subst (Subst.from_TypeEnv env')).WfInHeap mem.heap ∧
              cap.BoundedBy (B.denot env' mem) ∧
              cap = cs.ground_denot mem ∧
              EnvTyping Γ env' mem at ht
          have ⟨hwf, _, hsub, _, ht'⟩ := ht
          have ih_result := ih ht'
          unfold TypeEnv.is_transparent at ih_result ⊢
          intro x
          cases x with
          | there x =>
            exact ih_result x
  | lock Γ' ih =>
    change EnvTyping Γ' env mem at ht
    exact ih ht

theorem typed_env_is_bool_independent
  (ht : EnvTyping Γ env mem) :
  env.is_bool_independent := by
  induction Γ with
  | empty =>
    cases env with
    | empty =>
      unfold TypeEnv.is_bool_independent
      intro x
      cases x
  | push Γ k ih =>
    cases env with
    | extend env' info =>
      cases k with
      | var T =>
        cases info with
        | var n ps =>
          change
            ⟦T⟧_[env'] mem (.var (.free n)) ∧
              ps = T.captureSet.peakset Γ ∧
              EnvTyping Γ env' mem at ht
          obtain ⟨_, _, ht'⟩ := ht
          have ih_result := ih ht'
          unfold TypeEnv.is_bool_independent at ih_result ⊢
          intro x
          cases x with
          | there x =>
            exact ih_result x
      | tvar S =>
        cases info with
        | tvar d =>
          change
            d.is_proper ∧
              d.implies_wf ∧
              d.implies_simple_ans ∧
              d.ImplyAfter mem ⟦S.core⟧_[env'] ∧
              d.enforce_pure ∧
              EnvTyping Γ env' mem at ht
          have ⟨hproper, _, _, _, _, ht'⟩ := ht
          have ih_result := ih ht'
          unfold TypeEnv.is_bool_independent at ih_result ⊢
          intro x
          cases x with
          | here =>
            -- hproper says d.is_proper
            -- We need d.is_bool_independent
            -- Denot.is_proper = is_monotonic ∧ is_transparent ∧ is_bool_independent ∧ implies_wf
            exact hproper.2.2.1
          | there x =>
            exact ih_result x
      | cvar useM B =>
        cases info with
        | cvar cs cap =>
          change
            cs.WfInHeap mem.heap ∧
              (B.subst (Subst.from_TypeEnv env')).WfInHeap mem.heap ∧
              cap.BoundedBy (B.denot env' mem) ∧
              cap = cs.ground_denot mem ∧
              EnvTyping Γ env' mem at ht
          have ⟨hwf, _, hsub, _, ht'⟩ := ht
          have ih_result := ih ht'
          unfold TypeEnv.is_bool_independent at ih_result ⊢
          intro x
          cases x with
          | there x =>
            exact ih_result x
  | lock Γ' ih =>
    change EnvTyping Γ' env mem at ht
    exact ih ht

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
      change m.heap x = some (Cell.val v) at hx
      exact hx
    constructor
    · exact Exp.IsSimpleAns.is_var
    constructor
    · apply Exp.WfInHeap.wf_var
      apply Var.WfInHeap.wf_free
      exact hx_heap
    · -- resolve_reachability of var equals resolve_reachability of stored value
      have heq : resolve_reachability m.heap (.var (.free x)) =
                 resolve_reachability m.heap v.unwrap :=
        reachability_of_loc_eq_resolve_reachability m x v hx_heap
      rw [heq]
      exact ht.2.2
  | tvar X =>
    unfold Ty.val_denot
    exact henv X
  | unit =>
    intro m x v hx ht
    unfold Ty.val_denot at ht ⊢
    have hx' : m.heap x = some (.val v) := by
      change m.heap x = some (.val v) at hx
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
      change m.heap x = some (.val v) at hx
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
    obtain ⟨_, l, b0, ℓ0, heq, hlookup_and_mem⟩ := ht
    -- v.unwrap = .var (.free l), but v.isVal says it's a simple value
    -- Variables are not simple values, so this is a contradiction
    have hval := v.isVal
    rw [heq] at hval
    cases hval
  | reader cs =>
    intro m x v hx ht
    unfold Ty.val_denot at ht ⊢
    obtain ⟨hwf, hwf_cs, label, b0, ℓ0, hres, hlookup, hcov⟩ := ht
    have hx' : m.heap x = some (.val v) := by
      change m.heap x = some (.val v) at hx
      exact hx
    have heq := resolve_var_heap_trans hx'
    rw [heq]
    refine ⟨?_, hwf_cs, label, b0, ℓ0, hres, hlookup, hcov⟩
    -- Prove (Exp.var (Var.free x)).WfInHeap m.heap
    constructor
    constructor
    exact hx'
  | poly T1 cs T2 =>
    intro m x v hx ht
    unfold Ty.val_denot at ht ⊢
    have hx' : m.heap x = some (.val v) := by
      change m.heap x = some (.val v) at hx
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
      change m.heap x = some (.val v) at hx
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
    · refine ⟨?_, ?_, ?_⟩
      · exact Exp.IsSimpleAns.is_simple_val Exp.IsSimpleVal.bfalse
      · exact Exp.WfInHeap.wf_bfalse
      · exact CapabilitySet.Subset.refl
    · refine ⟨?_, ?_, ?_⟩
      · exact Exp.IsSimpleAns.is_simple_val Exp.IsSimpleVal.btrue
      · exact Exp.WfInHeap.wf_btrue
      · exact CapabilitySet.Subset.refl
  | tvar X =>
    unfold Ty.val_denot
    exact henv X
  | unit =>
    unfold Ty.val_denot
    constructor <;> intro h <;> cases h
  | cap cs =>
    unfold Ty.val_denot
    constructor <;> intro h
    · rcases h with ⟨_, _, label, heq, _, _⟩
      cases heq
    · rcases h with ⟨_, _, label, heq, _, _⟩
      cases heq
  | bool =>
    unfold Ty.val_denot
    constructor
    · intro _
      exact Or.inr rfl
    · intro _
      exact Or.inl rfl
  | cell cs =>
    unfold Ty.val_denot
    constructor <;> intro h
    · rcases h with ⟨_, l, b0, ℓ0, heq, _, _⟩
      cases heq
    · rcases h with ⟨_, l, b0, ℓ0, heq, _, _⟩
      cases heq
  | reader cs =>
    -- btrue and bfalse cannot resolve to a reader, so both sides are False
    unfold Ty.val_denot
    constructor <;> intro h
    · rcases h with ⟨_, _, _, _, _, hres, _, _⟩
      cases hres
    · rcases h with ⟨_, _, _, _, _, hres, _, _⟩
      cases hres
  | arrow T1 cs T2 =>
    unfold Ty.val_denot
    constructor <;> intro h
    · rcases h with ⟨_, _, _, _, _, hres, _, _, _⟩
      cases hres
    · rcases h with ⟨_, _, _, _, _, hres, _, _, _⟩
      cases hres
  | poly T1 cs T2 =>
    unfold Ty.val_denot
    constructor <;> intro h
    · rcases h with ⟨_, _, _, _, _, hres, _, _, _⟩
      cases hres
    · rcases h with ⟨_, _, _, _, _, hres, _, _, _⟩
      cases hres
  | cpoly B cs T =>
    unfold Ty.val_denot
    constructor <;> intro h
    · rcases h with ⟨_, _, _, _, _, hres, _, _, _⟩
      cases hres
    · rcases h with ⟨_, _, _, _, _, hres, _, _, _⟩
      cases hres

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
    have hlookup : m.heap x = some (Cell.val v) := by
      change m.heap x = some (Cell.val v) at hx
      exact hx
    -- Rewrite resolve m.heap (var (free x))
    change match resolve m.heap (.var (.free x)) with
      | some (.pack CS x) =>
        CS.WfInHeap m.heap ∧
          Ty.val_denot (env.extend_cvar CS (cap := CS.ground_denot m)) T m (.var x)
      | _ => False
    simp only [resolve, hlookup]
    -- Now goal is: match (some v.unwrap) with ...
    -- Need to show this equals match (resolve m.heap v.unwrap) with ...
    cases hresolve : resolve m.heap v.unwrap
    · -- resolve returned none - contradiction with ht
      rw [hresolve] at ht
      cases ht
    · -- resolve returned some e'
      rename_i e'
      cases e'
      case pack =>
        -- resolve returned some (pack CS' y')
        rename_i CS' y'
        rw [hresolve] at ht
        -- ht now says: Ty.val_denot (env.extend_cvar CS') T m (var y')
        -- Need to show v.unwrap = pack CS' y'
        cases hunwrap : v.unwrap <;> rw [hunwrap] at hresolve
        case var =>
          cases v with
          | mk unwrap isVal reachability =>
            cases isVal <;> cases hunwrap
        case pack =>
          -- pack case
          rename_i CS'' y''
          simp only [List.empty_eq] at hresolve
          injection hresolve with hy
          cases hy
          exact ht
        all_goals {
          -- For other constructors (abs, tabs, etc.)
          simp [resolve] at hresolve
          -- hresolve says some (this constructor) = some (pack ...), contradiction
        }
      all_goals {
        -- resolve returned something other than pack - contradiction with ht
        rw [hresolve] at ht
        cases ht
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
    cases hwf with
    | wf_union hwf1 hwf2 =>
      rw [ih1 hwf1, ih2 hwf2]
  | var m v =>
    cases v with
    | bound x => cases x  -- No bound variables in empty signature
    | free x =>
      -- Free variable: use reachability_of_loc_monotonic
      unfold CaptureSet.ground_denot
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
    rfl
  | union C1 C2 ih1 ih2 =>
    -- Union: use IH on both components
    change CaptureSet.WfInHeap
      ((CaptureSet.subst C1 (Subst.from_TypeEnv ρ)).union
        (CaptureSet.subst C2 (Subst.from_TypeEnv ρ))) m1.heap at hwf
    cases hwf with
    | wf_union hwf1 hwf2 =>
      have e1 := ih1 hwf1
      have e2 := ih2 hwf2
      unfold CaptureSet.denot at e1 e2
      change
        (C1.subst (Subst.from_TypeEnv ρ)).ground_denot m1 ∪
          (C2.subst (Subst.from_TypeEnv ρ)).ground_denot m1 =
        ((C1.subst (Subst.from_TypeEnv ρ)).ground_denot m2 ∪
          (C2.subst (Subst.from_TypeEnv ρ)).ground_denot m2)
      exact congrArg₂ Union.union e1 e2
  | var m v =>
    cases v with
    | bound x =>
      -- Bound variable: after substitution becomes free variable
      unfold CaptureSet.denot
      change CaptureSet.WfInHeap (.var m (.free (ρ.lookup_var x).1)) m1.heap at hwf
      change (CaptureSet.ground_denot (.var m (.free (ρ.lookup_var x).1))) m1 =
        (CaptureSet.ground_denot (.var m (.free (ρ.lookup_var x).1))) m2
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
      change CaptureSet.WfInHeap (.var m (.free x)) m1.heap at hwf
      change (CaptureSet.ground_denot (.var m (.free x))) m1 =
        (CaptureSet.ground_denot (.var m (.free x))) m2
      unfold CaptureSet.ground_denot
      cases hwf with
      | wf_var_free hex =>
        -- hex : m1.heap x = some _
        -- Memory.lookup is definitionally equal to heap access
        exact congrArg (CapabilitySet.applyMut m) (reachability_of_loc_monotonic hsub x hex).symm
  | cvar m c =>
    -- Capture variable: after substitution becomes ground capture set
    unfold CaptureSet.denot
    change CaptureSet.ground_denot (((ρ.lookup_cvar c).1).applyMut m) m1 =
      CaptureSet.ground_denot (((ρ.lookup_cvar c).1).applyMut m) m2
    -- Need: (ρ.lookup_cvar c).ground_denot m1 = (ρ.lookup_cvar c).ground_denot m2
    -- This follows from ground_denot_is_monotonic
    exact ground_denot_is_monotonic hwf hsub

theorem capture_bound_denot_is_monotonic {B : CaptureBound s}
  (hwf : (B.subst (Subst.from_TypeEnv ρ)).WfInHeap m1.heap)
  (hsub : m2.subsumes m1) :
  B.denot ρ m1 = B.denot ρ m2 := by
  cases B with
  | unbound =>
    unfold CaptureBound.denot
    rfl
  | bound cs =>
    unfold CaptureBound.denot
    cases hwf with
    | wf_bound hwf_cs =>
      change CapabilityBound.set (cs.denot ρ m1) = CapabilityBound.set (cs.denot ρ m2)
      rw [capture_set_denot_is_monotonic hwf_cs hsub]

/-- ground_denot of applyRO is a subset: C.applyRO.ground_denot m ⊆ C.ground_denot m -/
theorem ground_denot_applyRO_subset {C : CaptureSet {}} {m : Memory} :
  C.applyRO.ground_denot m ⊆ C.ground_denot m := by
  induction C with
  | empty =>
    simp only [CaptureSet.applyRO, CaptureSet.ground_denot]
    exact CapabilitySet.Subset.refl
  | union C1 C2 ih1 ih2 =>
    simp only [CaptureSet.applyRO, CaptureSet.ground_denot]
    exact CapabilitySet.Subset.union_left
      (CapabilitySet.Subset.trans ih1 CapabilitySet.Subset.union_right_left)
      (CapabilitySet.Subset.trans ih2 CapabilitySet.Subset.union_right_right)
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
      cases m' with
      | epsilon => rfl
      | ro =>
        unfold CapabilitySet.applyMut
        rw [CapabilitySet.applyRO_applyRO]
  | cvar m' c => cases c

/-- ground_denot of applyRO is monotonic: if C1 ⊆ C2 then C1.applyRO ⊆ C2.applyRO -/
theorem ground_denot_applyRO_mono {C1 C2 : CaptureSet {}} {m : Memory}
  (hsub : C1.ground_denot m ⊆ C2.ground_denot m) :
  C1.applyRO.ground_denot m ⊆ C2.applyRO.ground_denot m := by
  rw [← ground_denot_applyRO_comm, ← ground_denot_applyRO_comm]
  exact CapabilitySet.applyRO_mono hsub

mutual

def val_denot_is_monotonic {env : TypeEnv s}
  (henv : env.IsMonotonic)
  (T : Ty .capt s) :
  (Ty.val_denot env T).is_monotonic := by
  cases T with
  | top =>
    intro m1 m2 e hmem ht
    unfold Ty.val_denot at ht ⊢
    refine ⟨ht.1, ?_, ?_⟩
    · exact Exp.wf_monotonic hmem ht.2.1
    · rw [resolve_reachability_monotonic hmem e ht.2.1]
      exact ht.2.2
  | tvar X =>
    unfold Ty.val_denot
    exact henv.tvar X
  | unit =>
    intro m1 m2 e hmem ht
    unfold Ty.val_denot at ht ⊢
    exact resolve_monotonic hmem ht
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
        cases c' with
        | val v =>
          unfold Cell.subsumes at hsub_c
          cases hsub_c
        | masked =>
          unfold Cell.subsumes at hsub_c
          cases hsub_c
        | capability info =>
          cases info with
          | basic =>
            change m2.heap label = some (Cell.capability .basic)
            exact hc'
          | mcell b =>
            unfold Cell.subsumes at hsub_c
            cases hsub_c
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
    | inl htrue => exact Or.inl (resolve_monotonic hmem htrue)
    | inr hfalse => exact Or.inr (resolve_monotonic hmem hfalse)
  | cell cs =>
    intro m1 m2 e hmem ht
    unfold Ty.val_denot at ht ⊢
    obtain ⟨hwf_cs, l, b0, ℓ0, heq, hlookup, hcov⟩ := ht
    have hsub : m2.heap.subsumes m1.heap := hmem
    change m1.heap l = some (Cell.capability (.mcell b0 ℓ0)) at hlookup
    obtain ⟨c', hc', hsub_c⟩ := hsub l (Cell.capability (.mcell b0 ℓ0)) hlookup
    cases c' with
    | val v =>
      change Cell.val v = Cell.capability (.mcell b0 ℓ0) at hsub_c
      cases hsub_c
    | masked =>
      change Cell.masked = Cell.capability (.mcell b0 ℓ0) at hsub_c
      cases hsub_c
    | capability info =>
      cases info with
      | basic =>
        change Cell.capability .basic = Cell.capability (.mcell b0 ℓ0) at hsub_c
        cases hsub_c
      | mcell b' ℓ' =>
        -- Subsumption may bump the liveness forward (live → dead); both bool
        -- and liveness slots are existentially bound in the denotation.
        constructor
        · exact CaptureSet.wf_monotonic hmem hwf_cs
        refine ⟨l, b', ℓ', heq, ?_, ?_⟩
        · change m2.heap l = some (Cell.capability (.mcell b' ℓ'))
          exact hc'
        · have hcs_eq := capture_set_denot_is_monotonic (C := cs) (ρ := env) hwf_cs hmem
          rw [← hcs_eq]
          exact hcov
  | reader cs =>
    intro m1 m2 e hmem ht
    unfold Ty.val_denot at ht ⊢
    obtain ⟨hwf_e, hwf_cs, label, b0, ℓ0, hres, hlookup, hcov⟩ := ht
    constructor
    · exact Exp.wf_monotonic hmem hwf_e
    constructor
    · exact CaptureSet.wf_monotonic hmem hwf_cs
    · have hsub : m2.heap.subsumes m1.heap := hmem
      change m1.heap label = some (Cell.capability (.mcell b0 ℓ0)) at hlookup
      obtain ⟨c', hc', hsub_c⟩ := hsub label (Cell.capability (.mcell b0 ℓ0)) hlookup
      cases c' with
      | val v =>
        change Cell.val v = Cell.capability (.mcell b0 ℓ0) at hsub_c
        cases hsub_c
      | masked =>
        change Cell.masked = Cell.capability (.mcell b0 ℓ0) at hsub_c
        cases hsub_c
      | capability info =>
        cases info with
        | basic =>
          change Cell.capability .basic = Cell.capability (.mcell b0 ℓ0) at hsub_c
          cases hsub_c
        | mcell b' ℓ' =>
          refine ⟨label, b', ℓ', ?_, ?_, ?_⟩
          · exact resolve_monotonic hmem hres
          · change m2.heap label = some (Cell.capability (.mcell b' ℓ'))
            exact hc'
          · have hcs_eq := capture_set_denot_is_monotonic (C := cs) (ρ := env) hwf_cs hmem
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
      · exact resolve_monotonic hmem hr
      · constructor
        · exact CaptureSet.wf_monotonic hmem hwf_cs'
        · constructor
          · have hcs_eq := capture_set_denot_is_monotonic (C := cs) (ρ := env) hwf_cs hmem
            have hcs'_eq := expand_captures_monotonic hmem cs' hwf_cs'
            rw [← hcs_eq, hcs'_eq]
            exact hR0_sub
          · intro arg m' hs' hcompat harg
            have hs0 := Memory.subsumes_trans hs' hmem
            have hcs'_eq := expand_captures_monotonic hmem cs' hwf_cs'
            rw [hcs'_eq]
            rw [hcs'_eq] at hcompat
            exact hfun arg m' hs0 hcompat harg
  | poly T1 cs T2 =>
    intro m1 m2 e hmem ht
    unfold Ty.val_denot at ht ⊢
    have ⟨hwf_e, hwf_cs, cs', S0, t0, hr, hwf_cs', hR0_sub, hfun⟩ := ht
    constructor
    · exact Exp.wf_monotonic hmem hwf_e
    constructor
    · exact CaptureSet.wf_monotonic hmem hwf_cs
    · use cs', S0, t0
      constructor
      · exact resolve_monotonic hmem hr
      · constructor
        · exact CaptureSet.wf_monotonic hmem hwf_cs'
        · constructor
          · have hcs_eq := capture_set_denot_is_monotonic (C := cs) (ρ := env) hwf_cs hmem
            have hcs'_eq := expand_captures_monotonic hmem cs' hwf_cs'
            rw [← hcs_eq, hcs'_eq]
            exact hR0_sub
          · intro m' denot msub hcompat hdenot_proper himply
            have hs0 := Memory.subsumes_trans msub hmem
            have hcs'_eq := expand_captures_monotonic hmem cs' hwf_cs'
            rw [hcs'_eq]
            rw [hcs'_eq] at hcompat
            exact hfun m' denot hs0 hcompat hdenot_proper himply
  | cpoly B cs T =>
    intro m1 m2 e hmem ht
    unfold Ty.val_denot at ht ⊢
    have ⟨hwf_e, hwf_cs, cs', B0, t0, hr, hwf_cs', hR0_sub, hfun⟩ := ht
    constructor
    · exact Exp.wf_monotonic hmem hwf_e
    constructor
    · exact CaptureSet.wf_monotonic hmem hwf_cs
    · use cs', B0, t0
      constructor
      · exact resolve_monotonic hmem hr
      · constructor
        · exact CaptureSet.wf_monotonic hmem hwf_cs'
        · constructor
          · have hcs_eq := capture_set_denot_is_monotonic (C := cs) (ρ := env) hwf_cs hmem
            have hcs'_eq := expand_captures_monotonic hmem cs' hwf_cs'
            rw [← hcs_eq, hcs'_eq]
            exact hR0_sub
          · intro m' CS hwf _ msub hcompat hbounded
            have hs0 := Memory.subsumes_trans msub hmem
            have hcs'_eq := expand_captures_monotonic hmem cs' hwf_cs'
            rw [hcs'_eq]
            rw [hcs'_eq] at hcompat
            exact hfun m' CS hwf hs0 hcompat hbounded

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
      rw [hresolve1] at ht
      cases ht
    · -- resolve m1.heap e = some e'
      rename_i e'
      cases e'
      case pack =>
        -- resolve m1.heap e = some (pack CS y)
        rename_i CS y
        rw [hresolve1] at ht
        -- ht now says: CS.WfInHeap m1.heap ∧
        --   Ty.val_denot (env.extend_cvar CS (cap := CS.ground_denot m1)) T m1 (var y)
        obtain ⟨hwf_CS_m1, ht_body⟩ := ht
        -- Use resolve_monotonic to show resolve m2.heap e = some (pack CS y)
        have hresolve2 : resolve m2.heap e = some (Exp.pack CS y) := by
          apply resolve_monotonic hmem hresolve1
        rw [hresolve2]
        -- Now need to show: CS.WfInHeap m2.heap ∧
        --   Ty.val_denot (env.extend_cvar CS (cap := CS.ground_denot m2)) T m2 (var y)
        constructor
        · -- Well-formedness is monotonic
          exact CaptureSet.wf_monotonic hmem hwf_CS_m1
        · -- Use monotonicity of val_denot
          -- First show ground_denot is monotonic
          have hcap_eq : CS.ground_denot m1 = CS.ground_denot m2 :=
            ground_denot_is_monotonic hwf_CS_m1 hmem
          have henv' : (env.extend_cvar CS (cap := CS.ground_denot m1)).IsMonotonic := by
            constructor
            · intro X
              cases X with
              | there X' =>
                exact henv.tvar X'
          rw [← hcap_eq]
          exact val_denot_is_monotonic henv' T hmem ht_body
      all_goals {
        -- resolve returned non-pack, so ht is False
        rw [hresolve1] at ht
        cases ht
      }

def exi_val_denot_is_bool_independent {env : TypeEnv s}
  (henv : TypeEnv.is_bool_independent env)
  (T : Ty .exi s) :
  (Ty.exi_val_denot env T).is_bool_independent := by
  cases T with
  | typ T =>
    unfold Ty.exi_val_denot
    exact val_denot_is_bool_independent henv T
  | exi T =>
    intro m
    unfold Ty.exi_val_denot
    change False <-> False
    constructor <;> intro h <;> cases h

/-- Expression denotation is monotonic with respect to memory subsumption.
    The new `is_compatible` premise is the budget-side liveness invariant
    that `eval_monotonic` now requires: capabilities in `R` whose realisations
    are mcells must be `.live` in `m2`. -/
def exp_denot_is_monotonic {env : TypeEnv s}
  (henv_mono : env.IsMonotonic)
  (henv_bool : env.is_bool_independent)
  (T : Ty .capt s) :
  ∀ {R : CapabilitySet} {m1 m2 : Memory} {e : Exp {}},
    Exp.WfInHeap e m1.heap ->
    m2.subsumes m1 ->
    m2.is_compatible R ->
    (Ty.exp_denot env T R) m1 e ->
    (Ty.exp_denot env T R) m2 e := by
  intro R m1 m2 e hwf hmem hcompat ht
  simp only [Ty.exp_denot] at ht ⊢
  apply eval_monotonic
  · apply Denot.as_mpost_is_monotonic
    exact val_denot_is_monotonic henv_mono T
  · apply Denot.as_mpost_is_bool_independent
    exact val_denot_is_bool_independent henv_bool T
  · exact hmem
  · exact hcompat
  · exact hwf
  · exact ht

/-- Existential expression denotation is monotonic with respect to memory subsumption. -/
def exi_exp_denot_is_monotonic {env : TypeEnv s}
  (henv_mono : env.IsMonotonic)
  (henv_bool : env.is_bool_independent)
  (T : Ty .exi s) :
  ∀ {R : CapabilitySet} {m1 m2 : Memory} {e : Exp {}},
    Exp.WfInHeap e m1.heap ->
    m2.subsumes m1 ->
    m2.is_compatible R ->
    (Ty.exi_exp_denot env T R) m1 e ->
    (Ty.exi_exp_denot env T R) m2 e := by
  intro R m1 m2 e hwf hmem hcompat ht
  simp only [Ty.exi_exp_denot] at ht ⊢
  apply eval_monotonic
  · apply Denot.as_mpost_is_monotonic
    exact exi_val_denot_is_monotonic henv_mono T
  · apply Denot.as_mpost_is_bool_independent
    exact exi_val_denot_is_bool_independent henv_bool T
  · exact hmem
  · exact hcompat
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
          change
            d.is_proper ∧
              d.implies_wf ∧
              d.implies_simple_ans ∧
              d.ImplyAfter mem1 ⟦S.core⟧_[env'] ∧
              d.enforce_pure ∧
              EnvTyping Γ env' mem1 at ht
          change
            d.is_proper ∧
              d.implies_wf ∧
              d.implies_simple_ans ∧
              d.ImplyAfter mem2 ⟦S.core⟧_[env'] ∧
              d.enforce_pure ∧
              EnvTyping Γ env' mem2
          have ⟨hproper, himply_wf, himply_simple_ans, himply, hpure, ht'⟩ := ht
          constructor
          · exact hproper
          · constructor
            · exact himply_wf
            · constructor
              · exact himply_simple_ans
              · constructor
                · apply Denot.imply_after_subsumes himply hmem
                · constructor
                  · exact hpure
                  · exact ih ht'
      | cvar useM B =>
        cases info with
        | cvar cs cap =>
          change
            cs.WfInHeap mem1.heap ∧
              (B.subst (Subst.from_TypeEnv env')).WfInHeap mem1.heap ∧
              cap.BoundedBy (B.denot env' mem1) ∧
              cap = cs.ground_denot mem1 ∧
              EnvTyping Γ env' mem1 at ht
          change
            cs.WfInHeap mem2.heap ∧
              (B.subst (Subst.from_TypeEnv env')).WfInHeap mem2.heap ∧
              cap.BoundedBy (B.denot env' mem2) ∧
              cap = cs.ground_denot mem2 ∧
              EnvTyping Γ env' mem2
          have ⟨hwf, hwf_bound, hsub, hcap, ht'⟩ := ht
          constructor
          · -- Prove: cs.WfInHeap mem2.heap
            exact CaptureSet.wf_monotonic hmem hwf
          constructor
          · exact CaptureBound.wf_monotonic hmem hwf_bound
          constructor
          · have h_denot_eq := ground_denot_is_monotonic hwf hmem
            have h_bound_eq : B.denot env' mem1 = B.denot env' mem2 :=
              capture_bound_denot_is_monotonic hwf_bound hmem
            rw [hcap, h_denot_eq] at hsub
            rw [← h_bound_eq]
            simpa [hcap, h_denot_eq] using hsub
          constructor
          · rw [hcap, ground_denot_is_monotonic hwf hmem]
          · exact ih ht'
  | lock Γ' ih =>
    change EnvTyping Γ' env mem1 at ht
    change EnvTyping Γ' env mem2
    exact ih ht

/-- Semantic subcapturing. -/
def SemSubcapt (Γ : Ctx s) (C1 C2 : CaptureSet s) : Prop :=
  ∀ env m,
    EnvTyping Γ env m ->
    C1.denot env m ⊆ C2.denot env m

/-- Semantic capture kinding. -/
def SemHasKind (Γ : Ctx s) (C : CaptureSet s) (mode : Mutability) : Prop :=
  ∀ env m,
    EnvTyping Γ env m ->
    CapabilitySet.HasKind (C.denot env m) mode

set_option linter.unusedVariables false in
/-- Semantic sub-bounding -/
def SemSubbound (Γ : Ctx s) (B1 B2 : CaptureBound s) : Prop :=
  ∀ env m,
    EnvTyping Γ env m ->
    B1.denot env m ⊆ B2.denot env m

/-- Semantic separation check. -/
def SemSepCheck (Γ : Ctx s) (C1 C2 : CaptureSet s) : Prop :=
  ∀ env H,
    EnvTyping Γ env H ->
    CapabilitySet.Noninterference (C1.denot env H) (C2.denot env H)

/-- Semantic subtyping relation. -/
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

/-- If resolve succeeds with a simple value, the expression is a simple answer.
    This works because resolve returns the expression itself for non-variables,
    or looks up the stored value for variables. -/
lemma simple_ans_from_resolve
  {H : Heap} {e : Exp {}} {v : Exp {}}
  (hresolve : resolve H e = some v)
  (hv : v.IsSimpleVal) :
  e.IsSimpleAns := by
  cases e with
  | var _ => exact Exp.IsSimpleAns.is_var
  | unit => exact Exp.IsSimpleAns.is_simple_val Exp.IsSimpleVal.unit
  | btrue => exact Exp.IsSimpleAns.is_simple_val Exp.IsSimpleVal.btrue
  | bfalse => exact Exp.IsSimpleAns.is_simple_val Exp.IsSimpleVal.bfalse
  | abs _ _ _ => exact Exp.IsSimpleAns.is_simple_val Exp.IsSimpleVal.abs
  | tabs _ _ _ => exact Exp.IsSimpleAns.is_simple_val Exp.IsSimpleVal.tabs
  | cabs _ _ _ => exact Exp.IsSimpleAns.is_simple_val Exp.IsSimpleVal.cabs
  | reader _ => exact Exp.IsSimpleAns.is_simple_val Exp.IsSimpleVal.reader
  | _ =>
    cases hresolve
    cases hv

lemma wf_from_resolve_unit
  {m : Memory} {e : Exp {}}
  (hresolve : resolve m.heap e = some .unit) :
  e.WfInHeap m.heap := by
  cases e with
  | var x =>
    cases x with
    | free fx =>
      simp only [resolve, List.empty_eq] at hresolve
      cases hfx : m.heap fx with
      | none => simp [hfx] at hresolve
      | some cell =>
        simp only [hfx] at hresolve
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
  | _ => cases hresolve

/-- Ported from old shape_val_denot_implies_wf.
    For Denot (not PreDenot), implies_wf says d m e → e.WfInHeap m.heap. -/
theorem val_denot_implies_wf {env : TypeEnv s}
  (hts : env.is_implying_wf)
  (T : Ty .capt s) :
  (Ty.val_denot env T).implies_wf := by
  intro m e hdenot
  cases T with
  | top =>
    simp only [Ty.val_denot, List.empty_eq] at hdenot
    exact hdenot.2.1
  | tvar X =>
    simp only [Ty.val_denot] at hdenot
    exact hts X m e hdenot
  | bool =>
    simp only [Ty.val_denot, List.empty_eq] at hdenot
    cases hdenot with
    | inl h =>
      cases e with
      | btrue => exact Exp.WfInHeap.wf_btrue
      | var x =>
        cases x with
        | bound bx => cases bx
        | free fx =>
          simp only [resolve, List.empty_eq] at h
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
          simp only [resolve, List.empty_eq] at h
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
    simp only [Ty.val_denot, List.empty_eq] at hdenot
    exact wf_from_resolve_unit hdenot
  | cell cs =>
    simp only [Ty.val_denot] at hdenot
    obtain ⟨_, l, b0, ℓ0, heq, hlookup, _⟩ := hdenot
    rw [heq]
    apply Exp.WfInHeap.wf_var
    apply Var.WfInHeap.wf_free
    · simpa only [Memory.lookup] using hlookup
  | reader cs =>
    simp only [Ty.val_denot] at hdenot
    exact hdenot.1
  | cap cs =>
    simp only [Ty.val_denot, List.empty_eq] at hdenot
    exact hdenot.1
  | arrow T1 cs T2 =>
    simp only [Ty.val_denot, List.empty_eq] at hdenot
    exact hdenot.1
  | poly T1 cs T2 =>
    simp only [Ty.val_denot, List.empty_eq] at hdenot
    exact hdenot.1
  | cpoly B cs T =>
    simp only [Ty.val_denot, List.empty_eq] at hdenot
    exact hdenot.1

/-- Value denotation implies simple answer for all types. -/
theorem val_denot_implies_simple_ans {env : TypeEnv s}
  (hts : env.is_implying_simple_ans)
  (T : Ty .capt s) :
  (Ty.val_denot env T).implies_simple_ans := by
  intro m e hdenot
  cases T with
  | top =>
    simp only [Ty.val_denot, List.empty_eq] at hdenot
    exact hdenot.1
  | tvar X =>
    simp only [Ty.val_denot] at hdenot
    exact hts X m e hdenot
  | bool =>
    simp only [Ty.val_denot, List.empty_eq] at hdenot
    cases hdenot with
    | inl h => exact simple_ans_from_resolve h Exp.IsSimpleVal.btrue
    | inr h => exact simple_ans_from_resolve h Exp.IsSimpleVal.bfalse
  | unit =>
    simp only [Ty.val_denot, List.empty_eq] at hdenot
    exact simple_ans_from_resolve hdenot Exp.IsSimpleVal.unit
  | cell cs =>
    simp only [Ty.val_denot] at hdenot
    obtain ⟨_, l, _, _, heq, _, _⟩ := hdenot
    rw [heq]
    exact Exp.IsSimpleAns.is_var
  | reader cs =>
    simp only [Ty.val_denot] at hdenot
    obtain ⟨_, _, _, _, _, hres, _, _⟩ := hdenot
    exact simple_ans_from_resolve hres Exp.IsSimpleVal.reader
  | cap cs =>
    simp only [Ty.val_denot, List.empty_eq] at hdenot
    obtain ⟨_, _, _, heq, _, _⟩ := hdenot
    rw [heq]
    exact Exp.IsSimpleAns.is_var
  | arrow T1 cs T2 =>
    simp only [Ty.val_denot, List.empty_eq] at hdenot
    obtain ⟨_, _, _, _, _, hres, _⟩ := hdenot
    exact simple_ans_from_resolve hres Exp.IsSimpleVal.abs
  | poly T1 cs T2 =>
    simp only [Ty.val_denot, List.empty_eq] at hdenot
    obtain ⟨_, _, _, _, _, hres, _⟩ := hdenot
    exact simple_ans_from_resolve hres Exp.IsSimpleVal.tabs
  | cpoly B cs T =>
    simp only [Ty.val_denot, List.empty_eq] at hdenot
    obtain ⟨_, _, _, _, _, hres, _⟩ := hdenot
    exact simple_ans_from_resolve hres Exp.IsSimpleVal.cabs

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
    Now uses Denot.is_proper (monotonic ∧ transparent ∧ bool_independent ∧ implies_wf). -/
theorem val_denot_is_proper {env : TypeEnv s} {T : Ty .capt s}
  (hts : EnvTyping Γ env m) :
  (Ty.val_denot env T).is_proper := by
  constructor
  · -- Prove: (Ty.val_denot env T).is_monotonic
    exact val_denot_is_monotonic (typed_env_is_monotonic hts) T
  · constructor
    · -- Prove: (Ty.val_denot env T).is_transparent
      exact val_denot_is_transparent (typed_env_is_transparent hts) T
    · constructor
      · -- Prove: (Ty.val_denot env T).is_bool_independent
        exact val_denot_is_bool_independent (typed_env_is_bool_independent hts) T
      · -- Prove: (Ty.val_denot env T).implies_wf
        exact val_denot_implies_wf (typed_env_is_implying_wf hts) T

theorem val_denot_implyafter_lift {R : CapabilitySet}
  (himp : (Ty.val_denot env T1).ImplyAfter H (Ty.val_denot env T2)) :
  (Ty.exp_denot env T1 R).ImplyAfter H (Ty.exp_denot env T2 R) := by
  intro m' hsub e heval
  simp only [Ty.exp_denot] at heval ⊢
  apply eval_post_monotonic_general _ heval
  have himp' := Denot.imply_after_to_m_entails_after himp
  exact Mpost.entails_after_subsumes himp' hsub

/-- Existential expression denotation implication lift. -/
theorem exi_denot_implyafter_lift {R : CapabilitySet}
  (himp : (Ty.exi_val_denot env T1).ImplyAfter H (Ty.exi_val_denot env T2)) :
  (Ty.exi_exp_denot env T1 R).ImplyAfter H (Ty.exi_exp_denot env T2 R) := by
  intro m' hsub e heval
  simp only [Ty.exi_exp_denot] at heval ⊢
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
    exact ht.2.2
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
      simp only [resolve_reachability]
      exact CapabilitySet.Subset.refl
    | var x =>
      cases x with
      | free fx =>
        simp only [resolve, List.empty_eq] at ht
        cases hcell : m.heap fx with
        | none => simp [hcell] at ht
        | some cell =>
          simp only [hcell] at ht
          cases cell with
          | val v =>
            -- v.unwrap = .unit
            have hunit : v.unwrap = .unit := by
              simpa using ht
            have hsimple : v.unwrap.IsSimpleVal := v.isVal
            simp only [resolve_reachability]
            rw [reachability_of_loc_eq_resolve_reachability m fx v hcell]
            cases hv : v.unwrap with
            | var x =>
              have hsimple' : (Exp.var x).IsSimpleVal := by
                simpa [hv] using hsimple
              cases hsimple'
            | abs cs T t =>
              have hunit' := hunit
              simp [hv] at hunit'
            | tabs cs S t =>
              have hunit' := hunit
              simp [hv] at hunit'
            | cabs cs B t =>
              have hunit' := hunit
              simp [hv] at hunit'
            | reader x =>
              have hunit' := hunit
              simp [hv] at hunit'
            | alloc x =>
              have hsimple' : (Exp.alloc x).IsSimpleVal := by
                simpa [hv] using hsimple
              cases hsimple'
            | drop x =>
              have hsimple' : (Exp.drop x).IsSimpleVal := by
                simpa [hv] using hsimple
              cases hsimple'
            | pack cs x =>
              have hsimple' : (Exp.pack cs x).IsSimpleVal := by
                simpa [hv] using hsimple
              cases hsimple'
            | app x y =>
              have hsimple' : (Exp.app x y).IsSimpleVal := by
                simpa [hv] using hsimple
              cases hsimple'
            | tapp x T =>
              have hsimple' : (Exp.tapp x T).IsSimpleVal := by
                simpa [hv] using hsimple
              cases hsimple'
            | capp x cs =>
              have hsimple' : (Exp.capp x cs).IsSimpleVal := by
                simpa [hv] using hsimple
              cases hsimple'
            | letin e1 e2 =>
              have hsimple' : (Exp.letin e1 e2).IsSimpleVal := by
                simpa [hv] using hsimple
              cases hsimple'
            | unpack e1 e2 =>
              have hsimple' : (Exp.unpack e1 e2).IsSimpleVal := by
                simpa [hv] using hsimple
              cases hsimple'
            | unit =>
              simp only [resolve_reachability]
              exact CapabilitySet.Subset.refl
            | btrue =>
              have hunit' := hunit
              simp [hv] at hunit'
            | bfalse =>
              have hunit' := hunit
              simp [hv] at hunit'
            | read x =>
              have hsimple' : (Exp.read x).IsSimpleVal := by
                simpa [hv] using hsimple
              cases hsimple'
            | write x y =>
              have hsimple' : (Exp.write x y).IsSimpleVal := by
                simpa [hv] using hsimple
              cases hsimple'
            | cond x e1 e2 =>
              have hsimple' : (Exp.cond x e1 e2).IsSimpleVal := by
                simpa [hv] using hsimple
              cases hsimple'
          | _ => simp at ht
      | bound bx => cases bx
    | _ => simp [resolve] at ht
  | bool =>
    -- captureSet = .empty, bool has empty reachability
    simp only [Ty.captureSet, CaptureSet.denot, CaptureSet.subst, CaptureSet.ground_denot]
    simp only [Ty.val_denot] at ht
    cases e with
    | btrue =>
      simp only [resolve_reachability]
      exact CapabilitySet.Subset.refl
    | bfalse =>
      simp only [resolve_reachability]
      exact CapabilitySet.Subset.refl
    | var x =>
      cases x with
      | free fx =>
        simp only [resolve, List.empty_eq] at ht
        cases hcell : m.heap fx with
        | none => simp [hcell] at ht
        | some cell =>
          simp only [hcell] at ht
          cases cell with
          | val v =>
            have hbool : v.unwrap = .btrue ∨ v.unwrap = .bfalse := by
              simpa using ht
            have hsimple : v.unwrap.IsSimpleVal := v.isVal
            simp only [resolve_reachability]
            rw [reachability_of_loc_eq_resolve_reachability m fx v hcell]
            cases hv : v.unwrap with
            | var x =>
              have hsimple' : (Exp.var x).IsSimpleVal := by
                simpa [hv] using hsimple
              cases hsimple'
            | abs cs T t =>
              have hbool' := hbool
              simp [hv] at hbool'
            | tabs cs S t =>
              have hbool' := hbool
              simp [hv] at hbool'
            | cabs cs B t =>
              have hbool' := hbool
              simp [hv] at hbool'
            | reader x =>
              have hbool' := hbool
              simp [hv] at hbool'
            | alloc x =>
              have hsimple' : (Exp.alloc x).IsSimpleVal := by
                simpa [hv] using hsimple
              cases hsimple'
            | drop x =>
              have hsimple' : (Exp.drop x).IsSimpleVal := by
                simpa [hv] using hsimple
              cases hsimple'
            | pack cs x =>
              have hsimple' : (Exp.pack cs x).IsSimpleVal := by
                simpa [hv] using hsimple
              cases hsimple'
            | app x y =>
              have hsimple' : (Exp.app x y).IsSimpleVal := by
                simpa [hv] using hsimple
              cases hsimple'
            | tapp x T =>
              have hsimple' : (Exp.tapp x T).IsSimpleVal := by
                simpa [hv] using hsimple
              cases hsimple'
            | capp x cs =>
              have hsimple' : (Exp.capp x cs).IsSimpleVal := by
                simpa [hv] using hsimple
              cases hsimple'
            | letin e1 e2 =>
              have hsimple' : (Exp.letin e1 e2).IsSimpleVal := by
                simpa [hv] using hsimple
              cases hsimple'
            | unpack e1 e2 =>
              have hsimple' : (Exp.unpack e1 e2).IsSimpleVal := by
                simpa [hv] using hsimple
              cases hsimple'
            | unit =>
              have hbool' := hbool
              simp [hv] at hbool'
            | btrue =>
              simp only [resolve_reachability]
              exact CapabilitySet.Subset.refl
            | bfalse =>
              simp only [resolve_reachability]
              exact CapabilitySet.Subset.refl
            | read x =>
              have hsimple' : (Exp.read x).IsSimpleVal := by
                simpa [hv] using hsimple
              cases hsimple'
            | write x y =>
              have hsimple' : (Exp.write x y).IsSimpleVal := by
                simpa [hv] using hsimple
              cases hsimple'
            | cond x e1 e2 =>
              have hsimple' : (Exp.cond x e1 e2).IsSimpleVal := by
                simpa [hv] using hsimple
              cases hsimple'
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
    simp only [reachability_of_loc, hlookup]
    exact CapabilitySet.covers_eps_imp_singleton_eps_subset hcov
  | cell cs =>
    -- captureSet = cs, e = .var (.free l), covers .epsilon l
    simp only [Ty.captureSet]
    simp only [Ty.val_denot] at ht
    obtain ⟨_, l, _, _, heq, hlookup, hcov⟩ := ht
    subst heq
    simp only [resolve_reachability, Memory.lookup] at hlookup ⊢
    simp only [reachability_of_loc, hlookup]
    exact CapabilitySet.covers_eps_imp_singleton_eps_subset hcov
  | reader cs =>
    -- captureSet = cs, resolve e = .reader (.free label), covers .ro label
    simp only [Ty.captureSet]
    simp only [Ty.val_denot] at ht
    obtain ⟨_, _, label, _, _, hres, hlookup, hcov⟩ := ht
    -- resolve_reachability for expression that resolves to .reader
    cases e with
    | reader x =>
      cases x with
      | free fx =>
        change some (Exp.reader (.free fx)) = some (Exp.reader (.free label)) at hres
        cases hres
        simp only [resolve_reachability]
        exact CapabilitySet.covers_imp_singleton_subset hcov
      | bound bx => cases bx
    | var x =>
      cases x with
      | free fx =>
        simp only [resolve, List.empty_eq] at hres
        cases hcell : m.heap fx with
        | none => simp [hcell] at hres
        | some cell =>
          simp only [hcell] at hres
          cases cell with
          | val v =>
            have hreader : v.unwrap = .reader (.free label) := by
              simpa only [Option.some.injEq] using hres
            simp only [resolve_reachability]
            rw [reachability_of_loc_eq_resolve_reachability m fx v hcell]
            rw [hreader]
            simp only [resolve_reachability]
            exact CapabilitySet.covers_imp_singleton_subset hcov
          | _ => simp at hres
      | bound bx => cases bx
    | _ => simp [resolve] at hres
  | arrow T1 cs T2 =>
    simp only [Ty.captureSet]
    simp only [Ty.val_denot] at ht
    obtain ⟨_, _, cs', _, t0, hres, _, hR0_sub, _⟩ := ht
    cases e with
    | abs cs0 _ _ =>
      simp only [resolve, Option.some.injEq, Exp.abs.injEq] at hres
      obtain ⟨rfl, _, _⟩ := hres
      simp only [resolve_reachability]
      exact hR0_sub
    | var x =>
      cases x with
      | free fx =>
        simp only [resolve, List.empty_eq] at hres
        cases hcell : m.heap fx with
        | none => simp [hcell] at hres
        | some cell =>
          simp only [hcell] at hres
          cases cell with
          | val v =>
            have hval := by simpa [resolve, hcell] using hres
            simp only [resolve_reachability]
            rw [reachability_of_loc_eq_resolve_reachability m fx v hcell]
            rw [hval]
            simp only [resolve_reachability]
            exact hR0_sub
          | _ => simp at hres
      | bound bx => cases bx
    | _ => simp [resolve] at hres
  | poly T1 cs T2 =>
    simp only [Ty.captureSet]
    simp only [Ty.val_denot] at ht
    obtain ⟨_, _, cs', _, t0, hres, _, hR0_sub, _⟩ := ht
    cases e with
    | tabs cs0 _ _ =>
      simp only [resolve, Option.some.injEq, Exp.tabs.injEq] at hres
      obtain ⟨rfl, _, _⟩ := hres
      simp only [resolve_reachability]
      exact hR0_sub
    | var x =>
      cases x with
      | free fx =>
        simp only [resolve, List.empty_eq] at hres
        cases hcell : m.heap fx with
        | none => simp [hcell] at hres
        | some cell =>
          simp only [hcell] at hres
          cases cell with
          | val v =>
            have hval := by simpa [resolve, hcell] using hres
            simp only [resolve_reachability]
            rw [reachability_of_loc_eq_resolve_reachability m fx v hcell]
            rw [hval]
            simp only [resolve_reachability]
            exact hR0_sub
          | _ => simp at hres
      | bound bx => cases bx
    | _ => simp [resolve] at hres
  | cpoly B cs T =>
    simp only [Ty.captureSet]
    simp only [Ty.val_denot] at ht
    obtain ⟨_, _, cs', _, t0, hres, _, hR0_sub, _⟩ := ht
    cases e with
    | cabs cs0 _ _ =>
      simp only [resolve, Option.some.injEq, Exp.cabs.injEq] at hres
      obtain ⟨rfl, _, _⟩ := hres
      simp only [resolve_reachability]
      exact hR0_sub
    | var x =>
      cases x with
      | free fx =>
        simp only [resolve, List.empty_eq] at hres
        cases hcell : m.heap fx with
        | none => simp [hcell] at hres
        | some cell =>
          simp only [hcell] at hres
          cases cell with
          | val v =>
            have hval := by simpa [resolve, hcell] using hres
            simp only [resolve_reachability]
            rw [reachability_of_loc_eq_resolve_reachability m fx v hcell]
            rw [hval]
            simp only [resolve_reachability]
            exact hR0_sub
          | _ => simp at hres
      | bound bx => cases bx
    | _ => simp [resolve] at hres
theorem val_denot_refine {env : TypeEnv s} {T : Ty .capt s} {x : Var .var s}
  (hdenot : (Ty.val_denot env T) m (.var (x.subst (Subst.from_TypeEnv env))))
  (hpeaks : compute_peaks env T.captureSet = compute_peaks env (.var .epsilon x)) :
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
          simp only [hcell] at hres
          cases cell with
          | val v =>
            have hres' : v.unwrap = .abs cs' x0 t0 := by
              simpa only [Option.some.injEq] using hres
            -- hres : v.unwrap = .abs cs' x0 t0
            -- By wf_reach: v.reachability = compute_reachability m.heap v.unwrap v.isVal
            have hwf_reach := m.wf.wf_reach n v.unwrap v.isVal v.reachability hcell
            -- Transport v.isVal along hres to get IsSimpleVal for the abs
            have habs_isval : (Exp.abs cs' x0 t0).IsSimpleVal := hres' ▸ v.isVal
            -- compute_reachability for abs is expand_captures
            have hcomp :
                compute_reachability m.heap v.unwrap v.isVal = expand_captures m.heap cs' := by
              calc compute_reachability m.heap v.unwrap v.isVal
                  = compute_reachability m.heap (Exp.abs cs' x0 t0) habs_isval := by
                      simp only [hres']
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
      intro arg m' hsub hval
      exact hbody arg m' hsub hval
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
          simp only [hcell] at hres
          cases cell with
          | val v =>
            have hres' : v.unwrap = .tabs cs' x0 t0 := by
              simpa only [Option.some.injEq] using hres
            have hwf_reach := m.wf.wf_reach n v.unwrap v.isVal v.reachability hcell
            have htabs_isval : (Exp.tabs cs' x0 t0).IsSimpleVal := hres' ▸ v.isVal
            have hcomp :
                compute_reachability m.heap v.unwrap v.isVal = expand_captures m.heap cs' := by
              calc compute_reachability m.heap v.unwrap v.isVal
                  = compute_reachability m.heap (Exp.tabs cs' x0 t0) htabs_isval := by
                      simp only [hres']
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
      intro m' denot hsub hprop himply_simple himply hpure
      exact hbody m' denot hsub hprop himply_simple himply hpure
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
          simp only [hcell] at hres
          cases cell with
          | val v =>
            have hres' : v.unwrap = .cabs cs' x0 t0 := by
              simpa only [Option.some.injEq] using hres
            have hwf_reach := m.wf.wf_reach n v.unwrap v.isVal v.reachability hcell
            have hcabs_isval : (Exp.cabs cs' x0 t0).IsSimpleVal := hres' ▸ v.isVal
            have hcomp :
                compute_reachability m.heap v.unwrap v.isVal = expand_captures m.heap cs' := by
              calc compute_reachability m.heap v.unwrap v.isVal
                  = compute_reachability m.heap (Exp.cabs cs' x0 t0) hcabs_isval := by
                      simp only [hres']
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
      intro m' CS hwf hsub hbdd
      exact hbody m' CS hwf hsub hbdd
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
      simp only [CaptureSet.denot, CaptureSet.subst, heq,
                 CaptureSet.ground_denot, CapabilitySet.applyMut]
      -- reachability_of_loc for capability cell is singleton .epsilon label
      have hlookup' : m.heap label = some (.capability .basic) := by
        simpa only [Memory.lookup] using hlookup
      cases hcell : m.heap label with
      | none => simp [hcell] at hlookup'
      | some cell =>
        simp only [reachability_of_loc, hcell]
        cases cell with
        | val v => simp [hcell] at hlookup'
        | capability cap =>
          exact CapabilitySet.covers.here Mutability.Le.refl
        | masked => simp [hcell] at hlookup'
  | cell cs =>
    simp only [Ty.refineCaptureSet, Ty.val_denot] at hdenot ⊢
    obtain ⟨hwf_cs, label, b0, ℓ0, heq, hlookup, hcov⟩ := hdenot
    -- heq : Exp.var (x.subst ...) = Exp.var (Var.free label)
    simp only [Exp.var.injEq] at heq
    refine ⟨?_, label, b0, ℓ0, ?_, hlookup, ?_⟩
    · -- WfInHeap for (.var .epsilon x).subst
      simp only [CaptureSet.subst]
      -- x.subst gives us (.free label), which is well-formed
      rw [heq]
      exact CaptureSet.WfInHeap.wf_var_free (by simpa only [Memory.lookup] using hlookup)
    · -- e = .var (.free label)
      simp only [heq]
    · -- covers .epsilon label ((.var .epsilon x).denot env m)
      simp only [CaptureSet.denot, CaptureSet.subst, heq,
                 CaptureSet.ground_denot, CapabilitySet.applyMut]
      have hlookup' : m.heap label = some (.capability (.mcell b0 ℓ0)) := by
        simpa only [Memory.lookup] using hlookup
      cases hcell : m.heap label with
      | none => simp [hcell] at hlookup'
      | some cell =>
        simp only [reachability_of_loc, hcell]
        cases cell with
        | val v => simp [hcell] at hlookup'
        | capability cap =>
          exact CapabilitySet.covers.here Mutability.Le.refl
        | masked => simp [hcell] at hlookup'
  | reader cs =>
    simp only [Ty.refineCaptureSet, Ty.val_denot] at hdenot ⊢
    obtain ⟨hwf_e, hwf_cs, loc, label, ℓ0, hres, hlookup, hcov⟩ := hdenot
    refine ⟨hwf_e, ?_, loc, label, ℓ0, hres, hlookup, ?_⟩
    · -- WfInHeap for (.var .epsilon x).subst
      simp only [CaptureSet.subst]
      cases hwf_e with
      | wf_var hwf_var =>
        exact CaptureSet.wf_of_var hwf_var
    · -- Need: covers .ro label ((.var .epsilon x).denot env m)
      simp only [CaptureSet.denot, CaptureSet.subst]
      -- The expression e = .var (x.subst ...) resolves to .reader (.free label)
      -- x.subst gives us the location, and reachability_of_loc gives the reachability
      simp only [resolve] at hres
      cases hv : x.subst (Subst.from_TypeEnv env) with
      | free n =>
        simp only [hv] at hres hwf_e ⊢
        cases hcell : m.heap n with
        | none => simp [hcell] at hres
        | some cell =>
          simp only [hcell] at hres
          cases cell with
          | val v =>
            have hres' : v.unwrap = .reader (.free loc) := by
              simpa only [Option.some.injEq] using hres
            -- v.unwrap = .reader (.free loc)
            -- By wf_reach: v.reachability = compute_reachability = .cap .ro loc
            have hwf_reach := m.wf.wf_reach n v.unwrap v.isVal v.reachability hcell
            have hreader_isval : (Exp.reader (Var.free loc)).IsSimpleVal := hres' ▸ v.isVal
            have hcomp :
                compute_reachability m.heap v.unwrap v.isVal = .cap .ro loc := by
              calc compute_reachability m.heap v.unwrap v.isVal
                  = compute_reachability m.heap (Exp.reader (Var.free loc)) hreader_isval := by
                      simp only [hres']
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

inductive CapabilitySet.IsEmpty : CapabilitySet -> Prop where
| empty : CapabilitySet.IsEmpty {}
| union :
  CapabilitySet.IsEmpty cs1 ->
  CapabilitySet.IsEmpty cs2 ->
  CapabilitySet.IsEmpty (cs1 ∪ cs2)

/-- Empty capability sets are subsets of the empty set. -/
theorem CapabilitySet.IsEmpty.subset_empty (h : CapabilitySet.IsEmpty cs) :
    cs ⊆ .empty := by
  induction h with
  | empty => exact CapabilitySet.Subset.refl
  | union _ _ ih1 ih2 => exact CapabilitySet.Subset.union_left ih1 ih2

/-- Subsets of empty capability sets are empty. -/
theorem CapabilitySet.IsEmpty.subset_of_subset
    (hempty : CapabilitySet.IsEmpty cs) (hsub : R ⊆ cs) : R ⊆ .empty :=
  CapabilitySet.Subset.trans hsub hempty.subset_empty

/-- Empty capture sets have empty ground denotations. -/
theorem CaptureSet.IsEmpty.ground_denot_empty {cs : CaptureSet {}}
  (h : cs.IsEmpty) : CapabilitySet.IsEmpty (cs.ground_denot m) := by
  induction h with
  | empty => exact CapabilitySet.IsEmpty.empty
  | union _ _ ih1 ih2 =>
    simp only [CaptureSet.ground_denot]
    exact CapabilitySet.IsEmpty.union ih1 ih2

/-- Empty capture sets have empty denotations. -/
theorem CaptureSet.IsEmpty.denot_empty {cs : CaptureSet s}
  (h : cs.IsEmpty) : CapabilitySet.IsEmpty (cs.denot env m) := by
  unfold CaptureSet.denot
  exact (h.subst _).ground_denot_empty

/-- covers cannot hold for a capability set that is empty (via IsEmpty). -/
theorem CapabilitySet.not_covers_of_isEmpty
    (h : CapabilitySet.IsEmpty cs) : ¬ CapabilitySet.covers m l cs := by
  intro hcov
  induction h with
  | empty => cases hcov
  | union _ _ ih1 ih2 =>
    cases hcov with
    | left hcov1 => exact ih1 hcov1
    | right hcov2 => exact ih2 hcov2

private theorem resolve_reachability_subset_of_resolve
    {m : Memory} {e v : Exp {}}
    (hresolve : resolve m.heap e = some v) :
    resolve_reachability m.heap e ⊆ resolve_reachability m.heap v := by
  cases e with
  | var x =>
    cases x with
    | bound bx =>
      cases bx
    | free fx =>
      simp only [resolve] at hresolve
      cases hcell : m.heap fx with
      | none =>
        simp only [hcell] at hresolve
        cases hresolve
      | some cell =>
        cases cell with
        | val hv =>
          simp only [hcell] at hresolve
          cases hresolve
          simp only [resolve_reachability]
          rw [reachability_of_loc_eq_resolve_reachability m fx hv hcell]
          exact CapabilitySet.Subset.refl
        | capability cap =>
          simp only [hcell] at hresolve
          cases hresolve
        | masked =>
          simp only [hcell] at hresolve
          cases hresolve
  | abs _ _ _ =>
    simp only [resolve] at hresolve
    cases hresolve
    exact CapabilitySet.Subset.refl
  | tabs _ _ _ =>
    simp only [resolve] at hresolve
    cases hresolve
    exact CapabilitySet.Subset.refl
  | cabs _ _ _ =>
    simp only [resolve] at hresolve
    cases hresolve
    exact CapabilitySet.Subset.refl
  | reader _ =>
    simp only [resolve] at hresolve
    cases hresolve
    exact CapabilitySet.Subset.refl
  | alloc _ =>
    simp only [resolve] at hresolve
    cases hresolve
    exact CapabilitySet.Subset.refl
  | drop _ =>
    simp only [resolve] at hresolve
    cases hresolve
    exact CapabilitySet.Subset.refl
  | pack _ _ =>
    simp only [resolve] at hresolve
    cases hresolve
    exact CapabilitySet.Subset.refl
  | app _ _ =>
    simp only [resolve] at hresolve
    cases hresolve
    exact CapabilitySet.Subset.refl
  | tapp _ _ =>
    simp only [resolve] at hresolve
    cases hresolve
    exact CapabilitySet.Subset.refl
  | capp _ _ =>
    simp only [resolve] at hresolve
    cases hresolve
    exact CapabilitySet.Subset.refl
  | letin _ _ =>
    simp only [resolve] at hresolve
    cases hresolve
    exact CapabilitySet.Subset.refl
  | unpack _ _ =>
    simp only [resolve] at hresolve
    cases hresolve
    exact CapabilitySet.Subset.refl
  | unit =>
    simp only [resolve] at hresolve
    cases hresolve
    exact CapabilitySet.Subset.refl
  | btrue =>
    simp only [resolve] at hresolve
    cases hresolve
    exact CapabilitySet.Subset.refl
  | bfalse =>
    simp only [resolve] at hresolve
    cases hresolve
    exact CapabilitySet.Subset.refl
  | read _ =>
    simp only [resolve] at hresolve
    cases hresolve
    exact CapabilitySet.Subset.refl
  | write _ _ =>
    simp only [resolve] at hresolve
    cases hresolve
    exact CapabilitySet.Subset.refl
  | cond _ _ _ =>
    simp only [resolve] at hresolve
    cases hresolve
    exact CapabilitySet.Subset.refl

theorem pure_ty_enforce_pure {T : Ty .capt s}
  (henv : env.is_enforcing_pure)
  (hpure : T.IsPureType) :
  (Ty.val_denot env T).enforce_pure := by
  intro m e hdenot
  unfold Ty.IsPureType at hpure
  cases T
  case top =>
    simp only [Ty.val_denot] at hdenot
    exact hdenot.2.2
  case tvar X =>
    simp only [Ty.val_denot] at hdenot
    exact henv X m e hdenot
  case unit =>
    simp only [Ty.val_denot] at hdenot
    exact CapabilitySet.Subset.trans
      (resolve_reachability_subset_of_resolve hdenot)
      (by
        simpa [resolve_reachability] using
          (CapabilitySet.Subset.refl : ({} : CapabilitySet) ⊆ {}))
  case bool =>
    simp only [Ty.val_denot] at hdenot
    cases hdenot with
    | inl htrue =>
      exact CapabilitySet.Subset.trans
        (resolve_reachability_subset_of_resolve htrue)
        (by
          simpa [resolve_reachability] using
            (CapabilitySet.Subset.refl : ({} : CapabilitySet) ⊆ {}))
    | inr hfalse =>
      exact CapabilitySet.Subset.trans
        (resolve_reachability_subset_of_resolve hfalse)
        (by
          simpa [resolve_reachability] using
            (CapabilitySet.Subset.refl : ({} : CapabilitySet) ⊆ {}))
  case cap cs =>
    simp only [Ty.captureSet] at hpure
    simp only [Ty.val_denot] at hdenot
    obtain ⟨_, _, label, _, _, hcov⟩ := hdenot
    exact absurd hcov (CapabilitySet.not_covers_of_isEmpty hpure.denot_empty)
  case cell cs =>
    simp only [Ty.captureSet] at hpure
    simp only [Ty.val_denot] at hdenot
    obtain ⟨_, label, _, _, _, _, hcov⟩ := hdenot
    exact absurd hcov (CapabilitySet.not_covers_of_isEmpty hpure.denot_empty)
  case reader cs =>
    simp only [Ty.captureSet] at hpure
    simp only [Ty.val_denot] at hdenot
    obtain ⟨_, _, label, _, _, _, _, hcov⟩ := hdenot
    exact absurd hcov (CapabilitySet.not_covers_of_isEmpty hpure.denot_empty)
  case arrow T1 cs T2 =>
    simp only [Ty.captureSet] at hpure
    simp only [Ty.val_denot] at hdenot
    obtain ⟨_, _, cs', _, _, hres, _, hR0_sub, _⟩ := hdenot
    have hR0_empty := hpure.denot_empty.subset_of_subset hR0_sub
    exact CapabilitySet.Subset.trans
      (resolve_reachability_subset_of_resolve hres)
      (by simpa [resolve_reachability] using hR0_empty)
  case poly T1 cs T2 =>
    simp only [Ty.captureSet] at hpure
    simp only [Ty.val_denot] at hdenot
    obtain ⟨_, _, cs', _, _, hres, _, hR0_sub, _⟩ := hdenot
    have hR0_empty := hpure.denot_empty.subset_of_subset hR0_sub
    exact CapabilitySet.Subset.trans
      (resolve_reachability_subset_of_resolve hres)
      (by simpa [resolve_reachability] using hR0_empty)
  case cpoly B cs T =>
    simp only [Ty.captureSet] at hpure
    simp only [Ty.val_denot] at hdenot
    obtain ⟨_, _, cs', _, _, hres, _, hR0_sub, _⟩ := hdenot
    have hR0_empty := hpure.denot_empty.subset_of_subset hR0_sub
    exact CapabilitySet.Subset.trans
      (resolve_reachability_subset_of_resolve hres)
      (by simpa [resolve_reachability] using hR0_empty)

end Consume
