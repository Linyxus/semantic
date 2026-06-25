import Semantic.CoreCapybara.Semantics
import Semantic.CoreCapybara.TypeSystem
import Semantic.Prelude

namespace CoreCapybara

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
  | reader => rename_i x; cases x with | free _ => rfl | bound bx => cases bx
  | _ => rfl

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
  unfold reachability_of_loc
  rw [hx]
  change v.reachability = resolve_reachability m.heap v.unwrap
  rw [Memory.reachability_invariant m x v hx]
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
  simpa only [Denot.as_mpost] using hbool (m := m)

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

/-- Trace-observing postcondition for an expression denotation: the result
  satisfies the value denotation `d`, and the recorded trace `t` respects the
  capability budget `R` (i.e. `TraceOk t R`). -/
def Denot.as_tpost (d : Denot) (R : CapabilitySet) : Tpost :=
  fun t e m => TraceOk t R ∧ d m e

lemma Denot.as_tpost_is_monotonic {d : Denot} {R : CapabilitySet}
  (hmon : d.is_monotonic) :
  (d.as_tpost R).is_monotonic := by
  intro t m1 m2 e hwf hsub h
  obtain ⟨htr, hd⟩ := h
  exact ⟨htr, hmon hsub hd⟩

lemma Denot.as_tpost_is_bool_independent {d : Denot} {R : CapabilitySet}
  (hbool : d.is_bool_independent) :
  (d.as_tpost R).is_bool_independent := by
  intro t m
  simp only [Denot.as_tpost]
  exact and_congr_right (fun _ => hbool (m := m))

lemma Denot.imply_after_to_t_entails_after {d1 d2 : Denot} {m : Memory} {R : CapabilitySet}
  (himp : d1.ImplyAfter m d2) :
  (d1.as_tpost R).entails_after m (d2.as_tpost R) :=
  fun m' hsub _t e h => ⟨h.1, himp m' hsub e h.2⟩

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
/-- Type information for a capture variable is its authority, a ground capture
set, and a capability set. The authority mirrors the context binding's authority
(tied by `EnvTyping`), letting the environment-separation invariant be stated on
environments alone. -/
| cvar :
  Authority ->
  CaptureSet {} ->
  CapabilitySet ->
  TypeInfo s .cvar
| lock :
  TypeInfo s .lock

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
  (Γ : TypeEnv s) (ground : CaptureSet {}) (cap : CapabilitySet := .empty)
  (a : Authority := .access_only) :
  TypeEnv (s,C) :=
  Γ.extend (.cvar a ground cap)

def TypeEnv.extend_lock (Γ : TypeEnv s) : TypeEnv (s,,.lock) :=
  Γ.extend .lock

def TypeEnv.lookup_var : (Γ : TypeEnv s) -> (x : BVar s .var) -> (Nat × PeakSet s)
| .extend _ (.var n ps), .here => (n, ps.rename Rename.succ)
| .extend Γ _, .there x =>
  match Γ.lookup_var x with
  | (n, ps) => (n, ps.rename Rename.succ)

def TypeEnv.lookup_tvar : (Γ : TypeEnv s) -> (x : BVar s .tvar) -> Denot
| .extend _ (.tvar T), .here => T
| .extend Γ _, .there x => Γ.lookup_tvar x

def TypeEnv.lookup_cvar : (Γ : TypeEnv s) -> (x : BVar s .cvar) -> CaptureSet {} × CapabilitySet
| .extend _ (.cvar _ cs cap), .here => (cs, cap)
| .extend Γ _, .there x => Γ.lookup_cvar x

/-- The authority recorded for a capture variable in the environment. -/
def TypeEnv.lookup_cvar_auth : (Γ : TypeEnv s) -> (x : BVar s .cvar) -> Authority
| .extend _ (.cvar a _ _), .here => a
| .extend Γ _, .there x => Γ.lookup_cvar_auth x

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

/-- The substitution from TypeEnv is independent of the cap and authority
parameters in extend_cvar. -/
theorem Subst.from_TypeEnv_extend_cvar_cap_irrelevant
  {env : TypeEnv s} {cs : CaptureSet {}} {cap cap' : CapabilitySet}
  {a a' : Authority} :
  Subst.from_TypeEnv (env.extend_cvar cs cap a) =
  Subst.from_TypeEnv (env.extend_cvar cs cap' a') := by
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
  {a a' : Authority}
  {x : Nat} {ps : PeakSet (s,C)} :
  Subst.from_TypeEnv ((env.extend_cvar cs cap a).extend_var x ps) =
  Subst.from_TypeEnv ((env.extend_cvar cs cap' a').extend_var x ps) := by
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
| .var m (.bound x) => (ρ.lookup_var x).2.cs.applyAccess m
| .var _ (.free _) => .empty

theorem compute_peaks_is_peak (ρ : TypeEnv s) (cs : CaptureSet s)
  : (compute_peaks ρ cs).PeaksOnly := by
  induction cs with
  | empty =>
    simp [compute_peaks]
    constructor
  | union _ _ ih1 ih2 =>
    simpa only [compute_peaks] using CaptureSet.PeaksOnly.union ih1 ih2
  | cvar =>
    simp [compute_peaks]
    constructor
  | var m x =>
    cases x
    case bound b =>
      simpa only [compute_peaks] using (ρ.lookup_var b).2.h.applyAccess m
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
| .var m' (.free x) => fun m => (reachability_of_loc m.heap x).applyAccess m'

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

/-- The `HasSepDom` property for a type environment. -/
def TypeEnv.HasSepDom (env : TypeEnv s) (dom : CaptureSet s) : Prop :=
  ∀ m1 c1 m2 c2,
    (.cvar m1 c1) ⊆ (compute_peaks env dom) ->
    (.cvar m2 c2) ⊆ (compute_peaks env dom) ->
    (c1 ≠ c2) ->
    CapabilitySet.Noninterference
      ((env.lookup_cvar c1).2.applyAccess m1)
      ((env.lookup_cvar c2).2.applyAccess m2)

/-- Whether this denotation enforces purity of the value. -/
def Denot.enforce_pure (d : Denot) : Prop :=
  ∀ m e,
    d m e ->
    resolve_reachability m.heap e ⊆ .empty

/-- `m'.preserves_liveness_full m` says: every mcell in `m` is still an mcell in
    `m'` with the same liveness component (the boolean component is unconstrained,
    so writes are allowed). The drop-frame condition without exceptions, as
    delivered by a function body whose typing context's `lock` disables every
    consume peak, so no cell can be dropped. -/
def Memory.preserves_liveness_full (m' m : Memory) : Prop :=
  ∀ l b ℓ,
    m.heap l = some (.capability (.mcell b ℓ)) →
    ∃ b', m'.heap l = some (.capability (.mcell b' ℓ))

/-- Reflexivity: a memory trivially preserves its own liveness. -/
theorem Memory.preserves_liveness_full_refl (m : Memory) :
    m.preserves_liveness_full m := by
  intro l b _ h
  exact ⟨b, h⟩

/-- Transitivity. -/
theorem Memory.preserves_liveness_full_trans
    {m1 m2 m3 : Memory}
    (h12 : m2.preserves_liveness_full m1)
    (h23 : m3.preserves_liveness_full m2) :
    m3.preserves_liveness_full m1 := by
  intro l b ℓ h
  obtain ⟨b1, h1⟩ := h12 l b ℓ h
  exact h23 l b1 ℓ h1

/-- Extending memory with a fresh mcell preserves the liveness of every old
    mcell: the freshness assumption guarantees `l` is not in the old heap, so
    only the new cell is added; old cells are unchanged. -/
theorem Memory.preserves_liveness_full_extend_mcell
    (m : Memory) (l : Nat) (b : Bool) (hfresh : m.heap l = none) :
    (m.extend_mcell l b hfresh).preserves_liveness_full m := by
  intro l' b' ℓ' h
  refine ⟨b', ?_⟩
  change (m.heap.extend_mcell l b) l' = some (.capability (.mcell b' ℓ'))
  unfold Heap.extend_mcell
  by_cases hl : l' = l
  · subst hl; rw [hfresh] at h; cases h
  · rw [if_neg hl]; exact h

/-- Updating an existing mcell with a new boolean (at the same liveness) does
    not change any cell's liveness: the updated cell keeps `ℓ`, all others are
    unchanged. -/
theorem Memory.preserves_liveness_full_update_mcell
    (m : Memory) (l : Nat) (b : Bool) (ℓ : Liveness)
    (hexists : ∃ b0, m.heap l = some (.capability (.mcell b0 ℓ))) :
    (m.update_mcell l b ℓ hexists).preserves_liveness_full m := by
  intro l' b' ℓ' h
  by_cases hl : l' = l
  · subst hl
    obtain ⟨b0, hb0⟩ := hexists
    rw [hb0] at h
    cases h
    refine ⟨b, ?_⟩
    change (m.heap.update_cell l' _) l' = _
    unfold Heap.update_cell; rw [if_pos rfl]
  · refine ⟨b', ?_⟩
    change (m.heap.update_cell l _) l' = _
    unfold Heap.update_cell; rw [if_neg hl]; exact h

structure TypeEnv.Satisfy (env : TypeEnv s) (ctx : ModalCtx s) (m : Memory) where
  wf_sep : ∀ C,
    ctx.sep.Has C ->
    (C.subst (Subst.from_TypeEnv env)).WfInHeap m.heap
  wf_mut : ∀ C mode,
    ctx.mutability.Has C mode ->
    (C.subst (Subst.from_TypeEnv env)).WfInHeap m.heap
  kind : ∀ C mode,
    ctx.mutability.Has C mode ->
    CapabilitySet.HasKind (C.denot env m) mode
  sep : ∀ C1 C2,
    ctx.sep.HasTwoDistinct C1 C2 ->
    CapabilitySet.Noninterference (C1.denot env m) (C2.denot env m)

/-- A capture variable is *dead* according to the (peaks-only) dead-set `K`:
it occurs in `K` at some access mode. Dead variables are the already-consumed
ones; they may legitimately alias other capture variables and are excused
from the environment-separation invariant. -/
def PeakSet.DeadIn (K : PeakSet s) (c : BVar s .cvar) : Prop :=
  ∃ a : Access, (CaptureSet.cvar a c) ⊆ K.cs

/-- Environment separation well-formedness: every pair of distinct droppable
capture variables has disjoint capability sets. This is the dead-set-free form
of `DropSepExcept` — with no dead-set to exempt consumed pairs, *all* distinct
droppable pairs must be separated. -/
def TypeEnv.EnvSepWf (env : TypeEnv s) : Prop :=
  ∀ (c1 c2 : BVar s .cvar),
    c1 ≠ c2 →
    env.lookup_cvar_auth c1 = .can_drop →
    env.lookup_cvar_auth c2 = .can_drop →
    CapabilitySet.disjoint (env.lookup_cvar c1).2 (env.lookup_cvar c2).2

/-- Pack-witness authority bound: if a computation that started at memory `m`
with budget `R` results in a pack value, then every location `l` reachable from
the pack's witness at mode `mu` is either covered by `R` at that same mode `mu`
and consumable (`.drop`) under `R`, or fresh (allocated after `m`). The `.drop`
half lets `unpack` see the witness as consumable; the `R.covers mu l` half lets
`unpack` cover the continuation's access touches of the witness (`.drop` alone
does not cover `.access` under `CapMode.Le`). -/
def pack_bound (R : CapabilitySet) (m : Memory) : Exp {} -> Memory -> Prop :=
  fun v m' => ∀ (cs : CaptureSet {}) (x : Var .var {}),
    v = .pack cs x ->
    ∀ mu l, (cs.reachability m').hasmem mu l ->
      (R.covers mu l ∧ R.hasmem .drop l) ∨ m.lookup l = none

/-- The unpacked existential witness is live in the result memory. Anti-monotonic
  (a more-dead memory can decay a witness cell), so it lives in the expression
  postcondition asserted at the actual pack-producing result memory, not in the
  monotonic value denotation `exi_val_denot`. Established at pack creation
  (`sem_typ_pack`/`sem_typ_alloc`) and consumed at `sem_typ_unpack`. Vacuous for
  non-pack values (cf. `pack_bound`). -/
def witness_live : Exp {} -> Memory -> Prop :=
  fun v m' => ∀ (cs : CaptureSet {}) (x : Var .var {}),
    v = .pack cs x -> m'.is_compatible (cs.reachability m')

theorem witness_live_of_ne_pack {m' : Memory} {v : Exp {}}
    (h : ∀ (cs : CaptureSet {}) (x : Var .var {}), v ≠ .pack cs x) :
    witness_live v m' :=
  fun cs x heq => absurd heq (h cs x)

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
    (cs.denot env m).covers (.access .epsilon) label
| env, .reader cs => fun m e =>
  e.WfInHeap m.heap ∧
  (cs.subst (Subst.from_TypeEnv env)).WfInHeap m.heap ∧
  ∃ (label : Nat) (b0 : Bool) (ℓ0 : Liveness),
    resolve m.heap e = some (.reader (.free label)) ∧
    m.lookup label = some (.capability (.mcell b0 ℓ0)) ∧
    (cs.denot env m).covers (.access .ro) label
| env, .cell cs => fun m e =>
  (cs.subst (Subst.from_TypeEnv env)).WfInHeap m.heap ∧
  ∃ l b0 ℓ0,
    e = .var (.free l) ∧
    m.lookup l = some (.capability (.mcell b0 ℓ0)) ∧
    (cs.denot env m).covers (.access .epsilon) l
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
      Ty.exi_exp_denot
        (env.extend_var arg (compute_peakset env T1.captureSet))
        T2
        R0
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
      m'.is_compatible R0 ->
      denot.is_proper ->
      denot.implies_simple_ans ->
      denot.ImplyAfter m' (Ty.val_denot env T1) ->
      denot.enforce_pure ->
      Ty.exi_exp_denot
        (env.extend_tvar denot)
        T2
        R0
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
      (CS.ground_denot m').drop_free ->
      let A0 := CS.denot TypeEnv.empty
      m'.subsumes m ->
      m'.is_compatible R0 ->
      ((A0 m').BoundedBy (B.denot env m')) ->
      Ty.exi_exp_denot
        (env.extend_cvar CS (cap := CS.ground_denot m'))
        T
        R0
        m' (t0.subst (Subst.openCVar CS)))
| env, .modal cs Ψ E => fun m e =>
  e.WfInHeap m.heap ∧
  (cs.subst (Subst.from_TypeEnv env)).WfInHeap m.heap ∧
  ∃ cs0 sepctx0 t0,
    resolve m.heap e = some (.boxed cs0 sepctx0 t0) ∧
    cs0.WfInHeap m.heap ∧
    sepctx0.WfInHeap m.heap ∧
    (∀ (m' : Memory),
      m'.subsumes m ->
      env.Satisfy Ψ m' ->
      TypeEnv.empty.Satisfy sepctx0 m') ∧
    let R0 := expand_captures m.heap cs0
    R0 ⊆ (cs.denot env m) ∧
    (∀ (m' : Memory),
      m'.subsumes m ->
      m'.is_compatible R0 ->
     (∀ C mode,
        Ψ.mutability.Has C mode ->
        CapabilitySet.HasKind (C.denot env m') mode) ->
     (∀ C1 C2,
        Ψ.sep.HasTwoDistinct C1 C2 ->
        CapabilitySet.Noninterference (C1.denot env m') (C2.denot env m')) ->
      Ty.exi_exp_denot env E R0 m' t0)

/-- Value denotation for existential types. -/
def Ty.exi_val_denot : TypeEnv s -> Ty .exi s -> Denot
| ρ, .typ T => Ty.val_denot ρ T
| ρ, .exi T => fun m e =>
  match resolve m.heap e with
  | some (.pack CS x) =>
    CS.WfInHeap m.heap ∧
    (CS.ground_denot m).drop_free ∧
    Ty.val_denot (ρ.extend_cvar CS (cap := CS.ground_denot m) (a := .can_drop)) T m (.var x)
  | _ => False

/-- Expression denotation for capturing types.
    Takes an explicit capture set (the use set from the typing judgment). -/
def Ty.exp_denot : TypeEnv s -> Ty .capt s -> PreDenot
| ρ, T, R => fun m (e : Exp {}) =>
  Eval m e ((Ty.val_denot ρ T).as_tpost R)

/-- Expression denotation for existential types.
    Takes an explicit capture set (the use set from the typing judgment).
    The postcondition carries, besides the value denotation, the pack-witness
    authority bound `pack_bound` relating any resulting pack value's witness to
    the budget `R` and starting memory `m`. -/
def Ty.exi_exp_denot : TypeEnv s -> Ty .exi s -> PreDenot
| ρ, T, R => fun m (e : Exp {}) =>
  Eval m e (fun t v m' =>
    TraceOk t R ∧ Ty.exi_val_denot ρ T m' v ∧ pack_bound R m v m' ∧ witness_live v m')

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
| .push Γ (.cvar a B), .extend env (.cvar a' cs cap), m =>
  (cs.WfInHeap m.heap) ∧
  ((B.subst (Subst.from_TypeEnv env)).WfInHeap m.heap) ∧
  (cap.BoundedBy (B.denot env m)) ∧
  cap = cs.ground_denot m ∧
  cap.drop_free ∧
  a' = a ∧
  EnvTyping Γ env m
| .push Γ (.lock sepctx), .extend env .lock, m =>
  env.Satisfy sepctx m ∧
  EnvTyping Γ env m

/-- From `EnvTyping`, every capture variable's stored capability is drop-free,
from the `cap.drop_free` conjunct of each cvar binding. -/
theorem envtyping_lookup_cvar_drop_free {s : Sig} {Γ : Ctx s} {env : TypeEnv s} {m : Memory}
    (hts : EnvTyping Γ env m) (c : BVar s .cvar) :
    (env.lookup_cvar c).2.drop_free := by
  induction Γ with
  | empty => cases c
  | push Γ' b ih =>
    cases b
    case var T =>
      match env with
      | .extend env' (.var n ps) =>
        simp only [EnvTyping] at hts
        obtain ⟨_, _, henv'⟩ := hts
        cases c with
        | there c' => exact ih henv' c'
    case tvar S =>
      match env with
      | .extend env' (.tvar d) =>
        simp only [EnvTyping] at hts
        obtain ⟨_, _, _, _, _, henv'⟩ := hts
        cases c with
        | there c' => exact ih henv' c'
    case cvar a B =>
      match env with
      | .extend env' (.cvar _ cs cap) =>
        simp only [EnvTyping] at hts
        obtain ⟨_, _, _, _, hdf, _, henv'⟩ := hts
        cases c with
        | here => exact hdf
        | there c' => exact ih henv' c'
    case lock Ψ =>
      match env with
      | .extend env' .lock =>
        simp only [EnvTyping] at hts
        obtain ⟨_, henv'⟩ := hts
        cases c with
        | there c' => exact ih henv' c'

/-- From `EnvTyping`, the authority recorded in the environment for each
capture variable matches the context binding's authority. -/
theorem envtyping_lookup_cvar_auth {s : Sig} {Γ : Ctx s} {env : TypeEnv s} {m : Memory}
    (hts : EnvTyping Γ env m) (c : BVar s .cvar) :
    env.lookup_cvar_auth c = Γ.lookup_authority c := by
  induction Γ with
  | empty => cases c
  | push Γ' b ih =>
    cases b
    case var T =>
      match env with
      | .extend env' (.var n ps) =>
        simp only [EnvTyping] at hts
        obtain ⟨_, _, henv'⟩ := hts
        cases c with
        | there c' => exact ih henv' c'
    case tvar S =>
      match env with
      | .extend env' (.tvar d) =>
        simp only [EnvTyping] at hts
        obtain ⟨_, _, _, _, _, henv'⟩ := hts
        cases c with
        | there c' => exact ih henv' c'
    case cvar a B =>
      match env with
      | .extend env' (.cvar a' cs cap) =>
        simp only [EnvTyping] at hts
        obtain ⟨_, _, _, _, _, hauth, henv'⟩ := hts
        cases c with
        | here => exact hauth
        | there c' => exact ih henv' c'
    case lock Ψ =>
      match env with
      | .extend env' .lock =>
        simp only [EnvTyping] at hts
        obtain ⟨_, henv'⟩ := hts
        cases c with
        | there c' => exact ih henv' c'

/-- For bound variables, `CaptureSet.peaks` equals `compute_peaks`. -/
theorem peaks_var_bound_eq {s : Sig} {Γ : Ctx s} {ρ : TypeEnv s}
    (h : EnvTyping Γ ρ mem) (x : BVar s .var) (m0 : Access) :
    CaptureSet.peaksVarBound Γ m0 x = (ρ.lookup_var x).2.cs.applyAccess m0 := by
  match s, Γ, ρ, x with
  | _, .push Γ' (.var T), .extend ρ' (.var n ps), .here =>
    simp only [EnvTyping] at h
    obtain ⟨_, hps, _⟩ := h
    rw [CaptureSet.peaksVarBound]
    change CaptureSet.applyAccess m0 ((CaptureSet.peaks Γ' T.captureSet).rename Rename.succ) = _
    change _ = CaptureSet.applyAccess m0 (ps.cs.rename Rename.succ)
    rw [hps]
    rfl
  | _, .push Γ' (.var T), .extend ρ' (.var n ps), .there x' =>
    simp only [EnvTyping] at h
    obtain ⟨_, _, h'⟩ := h
    rw [CaptureSet.peaksVarBound]
    rw [peaks_var_bound_eq h' x' m0]
    exact CaptureSet.applyAccess_rename
  | _, .push Γ' (.tvar S), .extend ρ' (.tvar denot), .there x' =>
    simp only [EnvTyping] at h
    obtain ⟨_, _, _, _, _, h'⟩ := h
    rw [CaptureSet.peaksVarBound]
    rw [peaks_var_bound_eq h' x' m0]
    exact CaptureSet.applyAccess_rename
  | _, .push Γ' (.cvar _ B), .extend ρ' (.cvar _ cs _), .there x' =>
    simp only [EnvTyping] at h
    obtain ⟨_, _, _, _, _, _, h'⟩ := h
    rw [CaptureSet.peaksVarBound]
    rw [peaks_var_bound_eq h' x' m0]
    exact CaptureSet.applyAccess_rename
  | _, .push Γ' (.lock _), .extend ρ' (.lock), .there x' =>
    simp only [EnvTyping] at h
    obtain ⟨_, h'⟩ := h
    rw [CaptureSet.peaksVarBound]
    rw [peaks_var_bound_eq h' x' m0]
    exact CaptureSet.applyAccess_rename
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
    | free n =>
      simp only [CaptureSet.peaks, compute_peaks]
      rfl
    | bound x =>
      simp only [compute_peaks]
      rw [CaptureSet.peaks]
      exact peaks_var_bound_eq h x m

theorem compute_peakset_correct (h : EnvTyping Γ ρ m) :
  ∀ C, C.peakset Γ = compute_peakset ρ C := by
  intro C
  simp only [CaptureSet.peakset, compute_peakset]
  congr 1
  exact compute_peaks_correct h C

/-- Semantic typing.

    The Eval budget is `C.denot ρ m`. Use/drop information lives on `C`'s `Access`
    qualifiers, and `ground_denot` applies them per peak (`.M m ↦ applyMut m` for
    the access budget, `.drop ↦ to_drop` for the drop budget), so `C` self-describes
    the entire budget.

    *Pre*: every cell in `C.denot ρ m` must be live at the start.
    *Post*: in any reachable result memory `m'`, the result satisfies `E`. -/
def SemanticTyping (C : CaptureSet s) (Γ : Ctx s) (e : Exp s) (E : Ty .exi s) : Prop :=
  ∀ ρ m,
    EnvTyping Γ ρ m ->
    ρ.EnvSepWf ->
    m.is_compatible (C.denot ρ m) ->
    Ty.exi_exp_denot ρ E (C.denot ρ m) m (e.subst (Subst.from_TypeEnv ρ))

notation:65 C " # " Γ " ⊨ " e " : " T => SemanticTyping {} C Γ e T

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
  · intro y
    cases y
    case here =>
      rfl
    case there y' =>
      cases y'
      case there v =>
        change (((Subst.from_TypeEnv ρ).lift.lift).var (.there (.there v))).subst
          (Subst.unpack cs (.free x)) = .free (ρ.lookup_var v).1
        rfl
  · intro X
    cases X
    case there X' =>
      cases X'
      case there X0 =>
        rfl
  · intro c
    cases c
    case there c' =>
      cases c'
      case here =>
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
            change CaptureSet.subst _ _ = _
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
          simp only [EnvTyping] at ht
          obtain ⟨_, _, ht'⟩ := ht
          unfold TypeEnv.is_implying_simple_ans
          intro x; cases x with
          | there x => exact ih ht' x
      | tvar S =>
        cases info with
        | tvar d =>
          simp only [EnvTyping] at ht
          obtain ⟨_, _, himplies, _, _, ht'⟩ := ht
          unfold TypeEnv.is_implying_simple_ans
          intro x; cases x with
          | here => exact himplies
          | there x => exact ih ht' x
      | cvar _ B =>
        cases info with
        | cvar a cs cap =>
          simp only [EnvTyping] at ht
          obtain ⟨_, _, _, _, _, _, ht'⟩ := ht
          unfold TypeEnv.is_implying_simple_ans
          intro x; cases x with
          | there x => exact ih ht' x
      | lock Ψ =>
        cases info with
        | lock =>
          simp only [EnvTyping] at ht
          obtain ⟨_, ht'⟩ := ht
          unfold TypeEnv.is_implying_simple_ans
          intro x; cases x with
          | there x => exact ih ht' x

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
          simp only [EnvTyping] at ht
          obtain ⟨_, _, ht'⟩ := ht
          unfold TypeEnv.is_implying_wf
          intro x; cases x with
          | there x => exact ih ht' x
      | tvar S =>
        cases info with
        | tvar d =>
          simp only [EnvTyping] at ht
          obtain ⟨_, himplies, _, _, _, ht'⟩ := ht
          unfold TypeEnv.is_implying_wf
          intro x; cases x with
          | here => exact himplies
          | there x => exact ih ht' x
      | cvar _ B =>
        cases info with
        | cvar a cs cap =>
          simp only [EnvTyping] at ht
          obtain ⟨_, _, _, _, _, _, ht'⟩ := ht
          unfold TypeEnv.is_implying_wf
          intro x; cases x with
          | there x => exact ih ht' x
      | lock Ψ =>
        cases info with
        | lock =>
          simp only [EnvTyping] at ht
          obtain ⟨_, ht'⟩ := ht
          unfold TypeEnv.is_implying_wf
          intro x; cases x with
          | there x => exact ih ht' x

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
          simp only [EnvTyping] at ht
          obtain ⟨_, _, ht'⟩ := ht
          unfold TypeEnv.is_enforcing_pure
          intro x; cases x with
          | there x => exact ih ht' x
      | tvar S =>
        cases info with
        | tvar d =>
          simp only [EnvTyping] at ht
          obtain ⟨_, _, _, _, hpure, ht'⟩ := ht
          unfold TypeEnv.is_enforcing_pure
          intro x; cases x with
          | here => exact hpure
          | there x => exact ih ht' x
      | cvar _ B =>
        cases info with
        | cvar a cs cap =>
          simp only [EnvTyping] at ht
          obtain ⟨_, _, _, _, _, _, ht'⟩ := ht
          unfold TypeEnv.is_enforcing_pure
          intro x; cases x with
          | there x => exact ih ht' x
      | lock Ψ =>
        cases info with
        | lock =>
          simp only [EnvTyping] at ht
          obtain ⟨_, ht'⟩ := ht
          unfold TypeEnv.is_enforcing_pure
          intro x; cases x with
          | there x => exact ih ht' x

/--
If a TypeEnv is typed with EnvTyping, then the substitution obtained from it
via `Subst.from_TypeEnv` is well-formed in the heap. Connects the semantic typing
judgment to syntactic well-formedness: `EnvTyping` ensures each variable location
exists in memory, so the substitution mapping variables to them is well-formed.
-/
theorem from_TypeEnv_wf_in_heap
  {Γ : Ctx s} {ρ : TypeEnv s} {m : Memory}
  (htyping : EnvTyping Γ ρ m) :
  (Subst.from_TypeEnv ρ).WfInHeap m.heap := by
  induction Γ with
  | empty =>
    cases ρ with
    | empty =>
      constructor
      · intro x; cases x
      · intro X; cases X
      · intro C; cases C
  | push Γ' k ih =>
    cases ρ with
    | extend ρ' info =>
      cases k with
      | var T =>
        cases info with
        | var n ps =>
          unfold EnvTyping at htyping
          obtain ⟨htype, _, htyping'⟩ := htyping
          have hwf : Exp.WfInHeap (s := {}) (.var (.free n)) m.heap := by
            change Ty.val_denot _ _ _ _ at htype
            cases T with
            | top => unfold Ty.val_denot at htype; exact htype.2.1
            | tvar X =>
              unfold Ty.val_denot at htype
              exact typed_env_is_implying_wf htyping' X m (.var (.free n)) htype
            | unit =>
              unfold Ty.val_denot at htype
              simp only [resolve] at htype
              split at htype <;> try contradiction
              rename_i hsome
              exact Exp.WfInHeap.wf_var (Var.WfInHeap.wf_free hsome)
            | bool =>
              unfold Ty.val_denot at htype
              rcases htype with h | h <;> {
                simp only [resolve] at h
                split at h <;> try contradiction
                rename_i hsome
                exact Exp.WfInHeap.wf_var (Var.WfInHeap.wf_free hsome)
              }
            | cell cs =>
              unfold Ty.val_denot at htype
              obtain ⟨_, l, _, _, hl, hlookup, _⟩ := htype
              cases hl
              exact Exp.WfInHeap.wf_var (Var.WfInHeap.wf_free
                (by simpa [Memory.lookup] using hlookup))
            | cap _ | reader _ | arrow _ _ _ | poly _ _ _ | cpoly _ _ _ | modal _ _ _ =>
              unfold Ty.val_denot at htype
              exact htype.1
          cases hwf with
          | wf_var hwf_var =>
            have ih_wf := ih htyping'
            constructor
            · intro x
              cases x with
              | here =>
                simpa only [Subst.from_TypeEnv, TypeEnv.lookup_var] using hwf_var
              | there x' =>
                simpa only [Subst.from_TypeEnv, TypeEnv.lookup_var] using ih_wf.wf_var x'
            · intro X
              cases X with
              | there X' =>
                simpa only [Subst.from_TypeEnv] using ih_wf.wf_tvar X'
            · intro C_var
              cases C_var with
              | there C' =>
                simpa only [Subst.from_TypeEnv] using ih_wf.wf_cvar C'
      | tvar S =>
        cases info with
        | tvar denot =>
          unfold EnvTyping at htyping
          have ⟨_, _, _, _, _, htyping'⟩ := htyping
          have ih_wf := ih htyping'
          constructor
          · intro x
            cases x with
            | there x' =>
              simpa only [Subst.from_TypeEnv, TypeEnv.lookup_var] using ih_wf.wf_var x'
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
      | cvar _ B =>
        cases info with
        | cvar a cs =>
          unfold EnvTyping at htyping
          have ⟨hwf, _, hsub, _, _, _, htyping'⟩ := htyping
          have ih_wf := ih htyping'
          constructor
          · intro x
            cases x with
            | there x' =>
              simpa only [Subst.from_TypeEnv, TypeEnv.lookup_var] using ih_wf.wf_var x'
          · intro X
            cases X with
            | there X' =>
              simpa only [Subst.from_TypeEnv] using ih_wf.wf_tvar X'
          · intro C_var
            cases C_var with
            | here =>
              simpa only [Subst.from_TypeEnv, TypeEnv.lookup_cvar] using hwf
            | there C' =>
              simpa only [Subst.from_TypeEnv] using ih_wf.wf_cvar C'
      | lock Ψ =>
        cases info with
        | lock =>
          simp only [EnvTyping] at htyping
          have ih_wf := ih htyping.2
          constructor
          · intro x
            cases x with
            | there x' =>
              simpa only [Subst.from_TypeEnv, TypeEnv.lookup_var] using ih_wf.wf_var x'
          · intro X
            cases X with
            | there X' =>
              simpa only [Subst.from_TypeEnv] using ih_wf.wf_tvar X'
          · intro C_var
            cases C_var with
            | there C' =>
              simpa only [Subst.from_TypeEnv] using ih_wf.wf_cvar C'

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
    exact Exp.IsAns.is_var
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
      · intro x
        cases x
  | push Γ k ih =>
    cases env with
    | extend env' info =>
      cases k with
      | var T =>
        cases info with
        | var n ps =>
          simp only [EnvTyping] at ht
          obtain ⟨_, _, ht'⟩ := ht
          constructor
          · intro x; cases x with
            | there x => exact (ih ht').tvar x
      | tvar S =>
        cases info with
        | tvar d =>
          simp only [EnvTyping] at ht
          obtain ⟨hproper, _, _, _, _, ht'⟩ := ht
          constructor
          · intro x; cases x with
            | here => exact hproper.1
            | there x => exact (ih ht').tvar x
      | cvar _ B =>
        cases info with
        | cvar a cs cap =>
          simp only [EnvTyping] at ht
          obtain ⟨_, _, _, _, _, _, ht'⟩ := ht
          constructor
          · intro x; cases x with
            | there x => exact (ih ht').tvar x
      | lock Ψ =>
        cases info with
        | lock =>
          simp only [EnvTyping] at ht
          obtain ⟨_, ht'⟩ := ht
          constructor
          · intro x; cases x with
            | there x => exact (ih ht').tvar x

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
          simp only [EnvTyping] at ht
          obtain ⟨_, _, ht'⟩ := ht
          unfold TypeEnv.is_transparent
          intro x; cases x with
          | there x => exact ih ht' x
      | tvar S =>
        cases info with
        | tvar d =>
          simp only [EnvTyping] at ht
          obtain ⟨hproper, _, _, _, _, ht'⟩ := ht
          unfold TypeEnv.is_transparent
          intro x; cases x with
          | here => exact hproper.2.1
          | there x => exact ih ht' x
      | cvar _ B =>
        cases info with
        | cvar a cs cap =>
          simp only [EnvTyping] at ht
          obtain ⟨_, _, _, _, _, _, ht'⟩ := ht
          unfold TypeEnv.is_transparent
          intro x; cases x with
          | there x => exact ih ht' x
      | lock Ψ =>
        cases info with
        | lock =>
          simp only [EnvTyping] at ht
          obtain ⟨_, ht'⟩ := ht
          unfold TypeEnv.is_transparent
          intro x; cases x with
          | there x => exact ih ht' x

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
          simp only [EnvTyping] at ht
          obtain ⟨_, _, ht'⟩ := ht
          unfold TypeEnv.is_bool_independent
          intro x; cases x with
          | there x => exact ih ht' x
      | tvar S =>
        cases info with
        | tvar d =>
          simp only [EnvTyping] at ht
          obtain ⟨hproper, _, _, _, _, ht'⟩ := ht
          unfold TypeEnv.is_bool_independent
          intro x; cases x with
          | here => exact hproper.2.2.1
          | there x => exact ih ht' x
      | cvar _ B =>
        cases info with
        | cvar a cs cap =>
          simp only [EnvTyping] at ht
          obtain ⟨_, _, _, _, _, _, ht'⟩ := ht
          unfold TypeEnv.is_bool_independent
          intro x; cases x with
          | there x => exact ih ht' x
      | lock Ψ =>
        cases info with
        | lock =>
          simp only [EnvTyping] at ht
          obtain ⟨_, ht'⟩ := ht
          unfold TypeEnv.is_bool_independent
          intro x; cases x with
          | there x => exact ih ht' x

theorem val_denot_is_transparent {env : TypeEnv s}
  (henv : TypeEnv.is_transparent env)
  (T : Ty .capt s) :
  (Ty.val_denot env T).is_transparent := by
  cases T with
  | top =>
    intro m x v hx ht
    unfold Ty.val_denot at ht ⊢
    have hx_heap : m.heap x = some (Cell.val v) := by simpa [Memory.lookup] using hx
    have heq : resolve_reachability m.heap (.var (.free x)) =
               resolve_reachability m.heap v.unwrap :=
      reachability_of_loc_eq_resolve_reachability m x v hx_heap
    exact ⟨Exp.IsSimpleAns.is_var, Exp.WfInHeap.wf_var (Var.WfInHeap.wf_free hx_heap),
      by rw [heq]; exact ht.2.2⟩
  | tvar X =>
    unfold Ty.val_denot
    exact henv X
  | unit =>
    intro m x v hx ht
    unfold Ty.val_denot at ht ⊢
    have hx' : m.heap x = some (.val v) := by
      simpa [Memory.lookup] using hx
    rw [resolve_var_heap_trans hx']
    exact ht
  | cap cs =>
    intro m x v hx ht
    unfold Ty.val_denot at ht ⊢
    have ⟨_, _, label, hlabel, hcap, hmem⟩ := ht
    -- Vacuous: the witness is a variable, contradicting v.isVal.
    have hval := v.isVal
    rw [hlabel] at hval
    cases hval
  | arrow T1 cs T2 =>
    intro m x v hx ht
    unfold Ty.val_denot at ht ⊢
    have hx' : m.heap x = some (.val v) := by simpa [Memory.lookup] using hx
    rw [resolve_var_heap_trans hx']
    exact ⟨Exp.WfInHeap.wf_var (Var.WfInHeap.wf_free hx'), ht.2⟩
  | bool =>
    intro m x v hx ht
    cases v with
    | mk vexp hv_simple hreach =>
      have hlookup : m.heap x = some (Cell.val ⟨vexp, hv_simple, hreach⟩) := by
        simpa [Memory.lookup] using hx
      have hres_self : resolve m.heap vexp = some vexp := by cases hv_simple <;> simp [resolve]
      have hbool : vexp = .btrue ∨ vexp = .bfalse := by
        unfold Ty.val_denot at ht; simpa [hres_self] using ht
      unfold Ty.val_denot
      rcases hbool with hb | hb <;> simp [resolve, hlookup, hb]
  | cell cs =>
    intro m x v hx ht
    unfold Ty.val_denot at ht ⊢
    obtain ⟨_, l, b0, ℓ0, heq, hlookup_and_mem⟩ := ht
    -- Vacuous: the witness is a variable, contradicting v.isVal.
    have hval := v.isVal
    rw [heq] at hval
    cases hval
  | reader cs =>
    intro m x v hx ht
    unfold Ty.val_denot at ht ⊢
    obtain ⟨_, hwf_cs, label, b0, ℓ0, hres, hlookup, hcov⟩ := ht
    have hx' : m.heap x = some (.val v) := by simpa [Memory.lookup] using hx
    rw [resolve_var_heap_trans hx']
    exact ⟨Exp.WfInHeap.wf_var (Var.WfInHeap.wf_free hx'), hwf_cs,
      label, b0, ℓ0, hres, hlookup, hcov⟩
  | poly T1 cs T2 | cpoly _ cs _ =>
    intro m x v hx ht
    unfold Ty.val_denot at ht ⊢
    have hx' : m.heap x = some (.val v) := by simpa [Memory.lookup] using hx
    rw [resolve_var_heap_trans hx']
    obtain ⟨_, hwf_cs, hexists⟩ := ht
    exact ⟨Exp.WfInHeap.wf_var (Var.WfInHeap.wf_free hx'), hwf_cs, hexists⟩
  | modal cs Ψ T =>
    intro m x v hx ht
    unfold Ty.val_denot at ht ⊢
    have hx' : m.heap x = some (.val v) := by simpa [Memory.lookup] using hx
    rw [resolve_var_heap_trans hx']
    obtain ⟨_, hwf_cs, cs', sepctx0, t0, hres, hwf_cs', hR0_sub⟩ := ht
    exact ⟨Exp.WfInHeap.wf_var (Var.WfInHeap.wf_free hx'), hwf_cs,
      cs', sepctx0, t0, hres, hwf_cs', hR0_sub⟩

theorem val_denot_is_bool_independent {env : TypeEnv s}
  (henv : env.is_bool_independent)
  (T : Ty .capt s) :
  (Ty.val_denot env T).is_bool_independent := by
  intro m
  cases T with
  | top =>
    unfold Ty.val_denot
    constructor <;> intro
    · exact ⟨Exp.IsSimpleAns.is_simple_val Exp.IsSimpleVal.bfalse, Exp.WfInHeap.wf_bfalse,
        by simpa [resolve_reachability] using CapabilitySet.Subset.refl⟩
    · exact ⟨Exp.IsSimpleAns.is_simple_val Exp.IsSimpleVal.btrue, Exp.WfInHeap.wf_btrue,
        by simpa [resolve_reachability] using CapabilitySet.Subset.refl⟩
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
  | modal cs Ψ T =>
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
    rw [resolve_var_heap_trans (by simpa only [Memory.lookup] using hx)]
    exact ht

theorem ground_denot_is_monotonic {C : CaptureSet {}} :
  (C.ground_denot).is_monotonic_for C := by
  unfold CapDenot.is_monotonic_for
  intro m1 m2 hwf hsub
  induction C with
  | empty =>
    unfold CaptureSet.ground_denot
    rfl
  | union cs1 cs2 ih1 ih2 =>
    unfold CaptureSet.ground_denot
    cases hwf with
    | wf_union hwf1 hwf2 =>
      rw [ih1 hwf1, ih2 hwf2]
  | var m v =>
    cases v with
    | bound x => cases x
    | free x =>
      unfold CaptureSet.ground_denot
      cases hwf with
      | wf_var_free hex =>
        exact congrArg (CapabilitySet.applyAccess m)
          (reachability_of_loc_monotonic hsub x hex).symm
  | cvar m c => cases c

theorem capture_set_denot_is_monotonic {C : CaptureSet s} :
  (C.denot ρ).is_monotonic_for (C.subst (Subst.from_TypeEnv ρ)) := by
  unfold CapDenot.is_monotonic_for
  intro m1 m2 hwf hsub
  induction C with
  | empty =>
    unfold CaptureSet.denot
    rfl
  | union C1 C2 ih1 ih2 =>
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
      unfold CaptureSet.denot
      change CaptureSet.WfInHeap (.var m (.free (ρ.lookup_var x).1)) m1.heap at hwf
      change (CaptureSet.ground_denot (.var m (.free (ρ.lookup_var x).1))) m1 =
        (CaptureSet.ground_denot (.var m (.free (ρ.lookup_var x).1))) m2
      unfold CaptureSet.ground_denot
      cases hwf with
      | wf_var_free hex =>
        exact congrArg (CapabilitySet.applyAccess m)
          (reachability_of_loc_monotonic hsub (ρ.lookup_var x).1 hex).symm
    | free x =>
      unfold CaptureSet.denot
      change CaptureSet.WfInHeap (.var m (.free x)) m1.heap at hwf
      change (CaptureSet.ground_denot (.var m (.free x))) m1 =
        (CaptureSet.ground_denot (.var m (.free x))) m2
      unfold CaptureSet.ground_denot
      cases hwf with
      | wf_var_free hex =>
        exact congrArg (CapabilitySet.applyAccess m)
          (reachability_of_loc_monotonic hsub x hex).symm
  | cvar m c =>
    unfold CaptureSet.denot
    change CaptureSet.ground_denot (((ρ.lookup_cvar c).1).applyAccess m) m1 =
      CaptureSet.ground_denot (((ρ.lookup_cvar c).1).applyAccess m) m2
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

theorem TypeEnv.Satisfy.monotonic
  {env : TypeEnv s} {ctx : ModalCtx s} {mem1 mem2 : Memory}
  (hsat : TypeEnv.Satisfy env ctx mem1)
  (hmem : mem2.subsumes mem1) :
  TypeEnv.Satisfy env ctx mem2 where
  wf_sep C hhas := CaptureSet.wf_monotonic hmem (hsat.wf_sep C hhas)
  wf_mut C mode hhas := CaptureSet.wf_monotonic hmem (hsat.wf_mut C mode hhas)
  kind C mode hhas := by
    rw [← capture_set_denot_is_monotonic (ρ := env) (C := C) (hsat.wf_mut C mode hhas) hmem]
    exact hsat.kind C mode hhas
  sep C1 C2 hdistinct := by
    rw [← capture_set_denot_is_monotonic (ρ := env) (C := C1) (hsat.wf_sep C1 hdistinct.left) hmem,
        ← capture_set_denot_is_monotonic (ρ := env) (C := C2) (hsat.wf_sep C2 hdistinct.right) hmem]
    exact hsat.sep C1 C2 hdistinct

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
      cases m' with
      | M mu => exact CapabilitySet.applyRO_subset_applyMut
      | drop => exact CapabilitySet.Subset.refl
  | cvar m' c => cases c

/-- (C.ground_denot m).applyRO = C.applyRO.ground_denot m -/
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
      exact CapabilitySet.applyAccess_applyRO
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
    obtain ⟨hwf_e, hwf_cs, label, heq, hcap, hmemin⟩ := ht
    have hcs_eq := capture_set_denot_is_monotonic (C := cs) (ρ := env) hwf_cs hmem
    have hsub : m2.heap.subsumes m1.heap := hmem
    obtain ⟨c', hc', hsub_c⟩ := hsub label (Cell.capability .basic) hcap
    cases c' with
    | val v => simp [Cell.subsumes] at hsub_c
    | masked => simp [Cell.subsumes] at hsub_c
    | capability info =>
      cases info with
      | mcell b => simp [Cell.subsumes] at hsub_c
      | basic =>
        exact ⟨Exp.wf_monotonic hmem hwf_e, CaptureSet.wf_monotonic hmem hwf_cs,
          label, heq, hc', by rw [← hcs_eq]; exact hmemin⟩
  | bool =>
    intro m1 m2 e hmem ht
    unfold Ty.val_denot at ht ⊢
    exact ht.imp (resolve_monotonic hmem) (resolve_monotonic hmem)
  | cell cs =>
    intro m1 m2 e hmem ht
    unfold Ty.val_denot at ht ⊢
    obtain ⟨hwf_cs, l, b0, ℓ0, heq, hlookup, hcov⟩ := ht
    have hsub : m2.heap.subsumes m1.heap := hmem
    obtain ⟨c', hc', hsub_c⟩ := hsub l (Cell.capability (.mcell b0 ℓ0)) hlookup
    cases c' with
    | val v => simp [Cell.subsumes] at hsub_c
    | masked => simp [Cell.subsumes] at hsub_c
    | capability info =>
      cases info with
      | basic => simp [Cell.subsumes] at hsub_c
      | mcell b' ℓ' =>
        -- Subsumption may bump the liveness forward (live → dead); both bool
        -- and liveness slots are existentially bound in the denotation.
        exact ⟨CaptureSet.wf_monotonic hmem hwf_cs, l, b', ℓ', heq, hc',
          by rw [← capture_set_denot_is_monotonic (C := cs) (ρ := env) hwf_cs hmem]; exact hcov⟩
  | reader cs =>
    intro m1 m2 e hmem ht
    unfold Ty.val_denot at ht ⊢
    obtain ⟨hwf_e, hwf_cs, label, b0, ℓ0, hres, hlookup, hcov⟩ := ht
    have hsub : m2.heap.subsumes m1.heap := hmem
    obtain ⟨c', hc', hsub_c⟩ := hsub label (Cell.capability (.mcell b0 ℓ0)) hlookup
    cases c' with
    | val v => simp [Cell.subsumes] at hsub_c
    | masked => simp [Cell.subsumes] at hsub_c
    | capability info =>
      cases info with
      | basic => simp [Cell.subsumes] at hsub_c
      | mcell b' ℓ' =>
        exact ⟨Exp.wf_monotonic hmem hwf_e, CaptureSet.wf_monotonic hmem hwf_cs,
          label, b', ℓ', resolve_monotonic hmem hres, hc',
          by rw [← capture_set_denot_is_monotonic (C := cs) (ρ := env) hwf_cs hmem]; exact hcov⟩
  | arrow T1 cs T2 =>
    intro m1 m2 e hmem ht
    unfold Ty.val_denot at ht ⊢
    obtain ⟨hwf_e, hwf_cs, cs', T0, t0, hr, hwf_cs', hR0_sub, hfun⟩ := ht
    have hcs_eq := capture_set_denot_is_monotonic (C := cs) (ρ := env) hwf_cs hmem
    have hcs'_eq := expand_captures_monotonic hmem cs' hwf_cs'
    refine ⟨Exp.wf_monotonic hmem hwf_e, CaptureSet.wf_monotonic hmem hwf_cs,
      cs', T0, t0, resolve_monotonic hmem hr, CaptureSet.wf_monotonic hmem hwf_cs',
      by rw [← hcs_eq, hcs'_eq]; exact hR0_sub,
      fun arg m' hs' hcompat harg => ?_⟩
    rw [hcs'_eq] at hcompat ⊢
    exact hfun arg m' (Memory.subsumes_trans hs' hmem) hcompat harg
  | poly T1 cs T2 =>
    intro m1 m2 e hmem ht
    unfold Ty.val_denot at ht ⊢
    obtain ⟨hwf_e, hwf_cs, cs', S0, t0, hr, hwf_cs', hR0_sub, hfun⟩ := ht
    have hcs_eq := capture_set_denot_is_monotonic (C := cs) (ρ := env) hwf_cs hmem
    have hcs'_eq := expand_captures_monotonic hmem cs' hwf_cs'
    refine ⟨Exp.wf_monotonic hmem hwf_e, CaptureSet.wf_monotonic hmem hwf_cs,
      cs', S0, t0, resolve_monotonic hmem hr, CaptureSet.wf_monotonic hmem hwf_cs',
      by rw [← hcs_eq, hcs'_eq]; exact hR0_sub,
      fun m' denot msub hcompat hdenot_proper himply => ?_⟩
    rw [hcs'_eq] at hcompat ⊢
    exact hfun m' denot (Memory.subsumes_trans msub hmem) hcompat hdenot_proper himply
  | cpoly B cs T =>
    intro m1 m2 e hmem ht
    unfold Ty.val_denot at ht ⊢
    obtain ⟨hwf_e, hwf_cs, cs', B0, t0, hr, hwf_cs', hR0_sub, hfun⟩ := ht
    have hcs_eq := capture_set_denot_is_monotonic (C := cs) (ρ := env) hwf_cs hmem
    have hcs'_eq := expand_captures_monotonic hmem cs' hwf_cs'
    refine ⟨Exp.wf_monotonic hmem hwf_e, CaptureSet.wf_monotonic hmem hwf_cs,
      cs', B0, t0, resolve_monotonic hmem hr, CaptureSet.wf_monotonic hmem hwf_cs',
      by rw [← hcs_eq, hcs'_eq]; exact hR0_sub,
      fun m' CS hwf_CS hdf msub hcompat hbounded => ?_⟩
    rw [hcs'_eq] at hcompat ⊢
    exact hfun m' CS hwf_CS hdf (Memory.subsumes_trans msub hmem) hcompat hbounded
  | modal cs Ψ T =>
    intro m1 m2 e hmem ht
    unfold Ty.val_denot at ht ⊢
    obtain ⟨hwf_e, hwf_cs, cs', sepctx0, t0, hr, hwf_cs',
            hwf_sepctx, hsat_impl, hR0_sub, hbody⟩ := ht
    have hcs_eq := capture_set_denot_is_monotonic (C := cs) (ρ := env) hwf_cs hmem
    have hcs'_eq := expand_captures_monotonic hmem cs' hwf_cs'
    exact ⟨Exp.wf_monotonic hmem hwf_e, CaptureSet.wf_monotonic hmem hwf_cs,
      cs', sepctx0, t0, resolve_monotonic hmem hr, CaptureSet.wf_monotonic hmem hwf_cs',
      ModalCtx.wf_monotonic hmem hwf_sepctx,
      fun m' hsubm' hsat => hsat_impl m' (Memory.subsumes_trans hsubm' hmem) hsat,
      by rw [← hcs_eq, hcs'_eq]; exact hR0_sub,
      fun m' hsubm' hcompat hkind hsep => by
        rw [hcs'_eq] at hcompat ⊢
        exact hbody m' (Memory.subsumes_trans hsubm' hmem) hcompat hkind hsep⟩

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
    cases hresolve1 : resolve m1.heap e
    · simp [hresolve1] at ht
    · rename_i e'
      cases e'
      case pack =>
        rename_i CS y
        rw [hresolve1] at ht
        obtain ⟨hwf_CS_m1, hdf_m1, ht_body⟩ := ht
        have hresolve2 : resolve m2.heap e = some (Exp.pack CS y) := by
          exact resolve_monotonic hmem hresolve1
        rw [hresolve2]
        have hcap_eq : CS.ground_denot m1 = CS.ground_denot m2 :=
          ground_denot_is_monotonic hwf_CS_m1 hmem
        have henv' : (env.extend_cvar CS (cap := CS.ground_denot m1)
            (a := .can_drop)).IsMonotonic :=
          ⟨fun X => by cases X with | there X' => exact henv.tvar X'⟩
        exact ⟨CaptureSet.wf_monotonic hmem hwf_CS_m1,
          by rw [← hcap_eq]; exact hdf_m1,
          by rw [← hcap_eq]; exact val_denot_is_monotonic henv' T hmem ht_body⟩
      all_goals {
        rw [hresolve1] at ht
        cases ht
      }

def exi_val_denot_is_bool_independent {env : TypeEnv s}
  (henv : TypeEnv.is_bool_independent env)
  (T : Ty .exi s) :
  (Ty.exi_val_denot env T).is_bool_independent := by
  cases T with
  | typ T =>
    intro m
    simpa only [Ty.exi_val_denot] using val_denot_is_bool_independent henv T (m := m)
  | exi T =>
    intro m
    unfold Ty.exi_val_denot
    exact ⟨False.elim, False.elim⟩

/-- Expression denotation is monotonic with respect to memory subsumption.
    The `is_compatible` premise is the budget-side liveness invariant for `R`:
    capabilities in `R` whose realisations are mcells must be `.live` in `m2`. -/
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
  refine eval_monotonic
    (Denot.as_tpost_is_monotonic (val_denot_is_monotonic henv_mono T))
    (Denot.as_tpost_is_bool_independent (val_denot_is_bool_independent henv_bool T))
    hmem ?_ hwf ht
  -- `hok`: an externally-touched cell live in `m1` stays live in `m2`.  By
  -- `TraceOk t R` (carried in the postcondition) such a cell is covered by `R`,
  -- and `m2.is_compatible R` keeps `R`'s mcells live.
  intro t v m _ hpost l b hlive htouch
  obtain ⟨mode, hcov⟩ := TraceOk.covers_of_extTouches hpost.1 htouch
  obtain ⟨mode', hmem_l, _⟩ := CapabilitySet.covers_imp_exists_hasmem hcov
  obtain ⟨c, hl2, hsub_c⟩ := hmem _ _ hlive
  cases c with
  | val => cases hsub_c
  | masked => cases hsub_c
  | capability info =>
    cases info with
    | basic => cases hsub_c
    | mcell b' ℓ' =>
      have hℓ' : ℓ' = .live := hcompat mode' l b' ℓ' hmem_l hl2
      subst hℓ'
      exact ⟨b', hl2⟩

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
          unfold EnvTyping at ht ⊢
          obtain ⟨hval, hps, ht'⟩ := ht
          exact ⟨val_denot_is_monotonic (typed_env_is_monotonic ht') T hmem hval,
            by simpa using hps, ih ht'⟩
      | tvar S =>
        cases info with
        | tvar d =>
          simp only [EnvTyping] at ht ⊢
          obtain ⟨hproper, himply_wf, himply_simple_ans, himply, hpure, ht'⟩ := ht
          exact ⟨hproper, himply_wf, himply_simple_ans,
            Denot.imply_after_subsumes himply hmem, hpure, ih ht'⟩
      | cvar _ B =>
        cases info with
        | cvar a cs cap =>
          simp only [EnvTyping] at ht ⊢
          obtain ⟨hwf, hwf_bound, hsub, hcap, hdf, hauth, ht'⟩ := ht
          have h_denot_eq := ground_denot_is_monotonic hwf hmem
          have h_bound_eq : B.denot env' mem1 = B.denot env' mem2 :=
            capture_bound_denot_is_monotonic hwf_bound hmem
          refine ⟨CaptureSet.wf_monotonic hmem hwf, CaptureBound.wf_monotonic hmem hwf_bound,
            ?_, by rw [hcap, h_denot_eq], hdf, hauth, ih ht'⟩
          rw [hcap, h_denot_eq] at hsub
          rw [← h_bound_eq]
          simpa [hcap, h_denot_eq] using hsub
      | lock Ψ =>
        cases info with
        | lock =>
          simp only [EnvTyping] at ht ⊢
          exact ⟨TypeEnv.Satisfy.monotonic ht.1 hmem, ih ht.2⟩

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

/-- Semantic separation check. The `EnvSepWf` premise is needed by the
`sep_droppable` rule: separation of two distinct droppable capture variables
is an environment invariant, not derivable from `EnvTyping` alone. The
`Γ.IsClosed` hypothesis serves the `sep_ro` rule's drop-freedom argument (peak
tracing requires closed types). -/
def SemSepCheck (Γ : Ctx s) (C1 C2 : CaptureSet s) : Prop :=
  Γ.IsClosed ->
  ∀ env H,
    EnvTyping Γ env H ->
    env.EnvSepWf ->
    CapabilitySet.Noninterference (C1.denot env H) (C2.denot env H)

/-- Semantic subtyping relation. Carries the environment-separation invariant
`EnvSepWf`, which `modal_modal` needs to interpret lock-stored `sep_droppable`
facts (via `fundamental_sepcheck_global`). The `exi` subtyping rule transports
denotations under a fresh capture binder; since authority is denotationally
inert (`val_denot_auth_irrel`), that binder is re-tagged `.access_only` so
`EnvSepWf` is preserved across it (`EnvSepWf.extend_cvar_access_only`). -/
def SemSubtyp {k : TySort} (Γ : Ctx s) (T1 T2 : Ty k s) : Prop :=
  match k with
  | .capt =>
    ∀ env H, EnvTyping Γ env H -> env.EnvSepWf ->
      (Ty.val_denot env T1).ImplyAfter H (Ty.val_denot env T2)
  | .exi =>
    ∀ env H, EnvTyping Γ env H -> env.EnvSepWf ->
      (Ty.exi_val_denot env T1).ImplyAfter H (Ty.exi_val_denot env T2)

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
  | boxed _ _ _ => exact Exp.IsSimpleAns.is_simple_val Exp.IsSimpleVal.boxed
  | reader _ => exact Exp.IsSimpleAns.is_simple_val Exp.IsSimpleVal.reader
  | _ => simp only [resolve] at hresolve; cases hresolve; cases hv

lemma wf_from_resolve_unit
  {m : Memory} {e : Exp {}}
  (hresolve : resolve m.heap e = some .unit) :
  e.WfInHeap m.heap := by
  cases e with
  | var x =>
    cases x with
    | free fx =>
      cases hfx : m.heap fx with
      | none => simp [resolve, hfx] at hresolve
      | some cell =>
        cases cell with
        | capability _ | masked => simp [resolve, hfx] at hresolve
        | val v => exact Exp.WfInHeap.wf_var (Var.WfInHeap.wf_free hfx)
    | bound bx => cases bx
  | unit => exact Exp.WfInHeap.wf_unit
  | _ => simp [resolve] at hresolve

lemma wf_from_resolve_btrue
  {m : Memory} {e : Exp {}}
  (hresolve : resolve m.heap e = some .btrue) :
  e.WfInHeap m.heap := by
  cases e with
  | var x =>
    cases x with
    | free fx =>
      cases hfx : m.heap fx with
      | none => simp [resolve, hfx] at hresolve
      | some cell =>
        cases cell with
        | val v => exact Exp.WfInHeap.wf_var (Var.WfInHeap.wf_free hfx)
        | capability _ => simp [resolve, hfx] at hresolve
        | masked => simp [resolve, hfx] at hresolve
    | bound bx => cases bx
  | btrue => exact Exp.WfInHeap.wf_btrue
  | _ => simp [resolve] at hresolve

lemma wf_from_resolve_bfalse
  {m : Memory} {e : Exp {}}
  (hresolve : resolve m.heap e = some .bfalse) :
  e.WfInHeap m.heap := by
  cases e with
  | var x =>
    cases x with
    | free fx =>
      cases hfx : m.heap fx with
      | none => simp [resolve, hfx] at hresolve
      | some cell =>
        cases cell with
        | val v => exact Exp.WfInHeap.wf_var (Var.WfInHeap.wf_free hfx)
        | capability _ => simp [resolve, hfx] at hresolve
        | masked => simp [resolve, hfx] at hresolve
    | bound bx => cases bx
  | bfalse => exact Exp.WfInHeap.wf_bfalse
  | _ => simp [resolve] at hresolve

/-- `implies_wf` for `val_denot`: `d m e → e.WfInHeap m.heap`. -/
theorem val_denot_implies_wf {env : TypeEnv s}
  (hts : env.is_implying_wf)
  (T : Ty .capt s) :
  (Ty.val_denot env T).implies_wf := by
  intro m e hdenot
  cases T with
  | top =>
    unfold Ty.val_denot at hdenot
    exact hdenot.2.1
  | tvar X =>
    unfold Ty.val_denot at hdenot
    exact hts X m e hdenot
  | bool =>
    unfold Ty.val_denot at hdenot
    cases hdenot with
    | inl h => exact wf_from_resolve_btrue h
    | inr h => exact wf_from_resolve_bfalse h
  | unit =>
    unfold Ty.val_denot at hdenot
    exact wf_from_resolve_unit hdenot
  | cell cs =>
    simp only [Ty.val_denot] at hdenot
    obtain ⟨_, l, b0, _, heq, hlookup, _⟩ := hdenot
    rw [heq]
    exact Exp.WfInHeap.wf_var (Var.WfInHeap.wf_free hlookup)
  | reader cs =>
    simp only [Ty.val_denot] at hdenot
    exact hdenot.1
  | cap cs =>
    unfold Ty.val_denot at hdenot
    exact hdenot.1
  | arrow T1 cs T2 =>
    unfold Ty.val_denot at hdenot
    exact hdenot.1
  | poly T1 cs T2 =>
    unfold Ty.val_denot at hdenot
    exact hdenot.1
  | cpoly B cs T =>
    unfold Ty.val_denot at hdenot
    exact hdenot.1
  | modal cs Ψ T =>
    unfold Ty.val_denot at hdenot
    exact hdenot.1

/-- Value denotation implies simple answer for all types. -/
theorem val_denot_implies_simple_ans {env : TypeEnv s}
  (hts : env.is_implying_simple_ans)
  (T : Ty .capt s) :
  (Ty.val_denot env T).implies_simple_ans := by
  intro m e hdenot
  cases T with
  | top =>
    unfold Ty.val_denot at hdenot
    exact hdenot.1
  | tvar X =>
    unfold Ty.val_denot at hdenot
    exact hts X m e hdenot
  | bool =>
    unfold Ty.val_denot at hdenot
    cases hdenot with
    | inl h => exact simple_ans_from_resolve h Exp.IsSimpleVal.btrue
    | inr h => exact simple_ans_from_resolve h Exp.IsSimpleVal.bfalse
  | unit =>
    unfold Ty.val_denot at hdenot
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
    unfold Ty.val_denot at hdenot
    obtain ⟨_, _, _, heq, _, _⟩ := hdenot
    rw [heq]
    exact Exp.IsSimpleAns.is_var
  | modal cs Ψ T =>
    unfold Ty.val_denot at hdenot
    rcases hdenot with ⟨_, _, _, _, _, hres, _, _⟩
    exact simple_ans_from_resolve hres Exp.IsSimpleVal.boxed
  | arrow T1 cs T2 =>
    unfold Ty.val_denot at hdenot
    obtain ⟨_, _, _, _, _, hres, _⟩ := hdenot
    exact simple_ans_from_resolve hres Exp.IsSimpleVal.abs
  | poly T1 cs T2 =>
    unfold Ty.val_denot at hdenot
    obtain ⟨_, _, _, _, _, hres, _⟩ := hdenot
    exact simple_ans_from_resolve hres Exp.IsSimpleVal.tabs
  | cpoly B cs T =>
    unfold Ty.val_denot at hdenot
    obtain ⟨_, _, _, _, _, hres, _⟩ := hdenot
    exact simple_ans_from_resolve hres Exp.IsSimpleVal.cabs

/-- `val_denot` is proper: monotonic ∧ transparent ∧ bool_independent ∧ implies_wf. -/
theorem val_denot_is_proper {env : TypeEnv s} {T : Ty .capt s}
  (hts : EnvTyping Γ env m) :
  (Ty.val_denot env T).is_proper :=
  ⟨val_denot_is_monotonic (typed_env_is_monotonic hts) T,
   val_denot_is_transparent (typed_env_is_transparent hts) T,
   val_denot_is_bool_independent (typed_env_is_bool_independent hts) T,
   val_denot_implies_wf (typed_env_is_implying_wf hts) T⟩

theorem val_denot_implyafter_lift {R : CapabilitySet}
  (himp : (Ty.val_denot env T1).ImplyAfter H (Ty.val_denot env T2)) :
  (Ty.exp_denot env T1 R).ImplyAfter H (Ty.exp_denot env T2 R) := by
  intro m' hsub e heval
  unfold Ty.exp_denot at heval ⊢
  exact eval_post_monotonic_general
    (Tpost.entails_after_subsumes (Denot.imply_after_to_t_entails_after himp) hsub) heval

/-- Existential expression denotation implication lift. The `pack_bound`
component of the postcondition is type-independent and carried through. -/
theorem exi_denot_implyafter_lift {R : CapabilitySet}
  (himp : (Ty.exi_val_denot env T1).ImplyAfter H (Ty.exi_val_denot env T2)) :
  (Ty.exi_exp_denot env T1 R).ImplyAfter H (Ty.exi_exp_denot env T2 R) := by
  intro m' hsub e heval
  unfold Ty.exi_exp_denot at heval ⊢
  refine eval_post_monotonic_general ?_ heval
  intro m'' hsub'' t v hpost
  exact ⟨hpost.1, himp m'' (Memory.subsumes_trans hsub'' hsub) v hpost.2.1,
    hpost.2.2.1, hpost.2.2.2⟩

private theorem resolve_reachability_subset_of_resolve_aux
    {m : Memory} {e v : Exp {}}
    (hresolve : resolve m.heap e = some v) :
    resolve_reachability m.heap e ⊆ resolve_reachability m.heap v := by
  cases e with
  | var x =>
    cases x with
    | bound bx => cases bx
    | free fx =>
      simp only [resolve] at hresolve
      cases hcell : m.heap fx with
      | none => simp only [hcell] at hresolve; cases hresolve
      | some cell =>
        cases cell with
        | val hv =>
          simp only [hcell] at hresolve
          cases hresolve
          simp only [resolve_reachability]
          rw [reachability_of_loc_eq_resolve_reachability m fx hv hcell]
          exact CapabilitySet.Subset.refl
        | capability cap => simp only [hcell] at hresolve; cases hresolve
        | masked => simp only [hcell] at hresolve; cases hresolve
  | _ =>
    simp only [resolve] at hresolve
    cases hresolve
    exact CapabilitySet.Subset.refl

set_option maxHeartbeats 400000 in
-- This is a large case analysis proof.
theorem val_denot_enforces_captures {T : Ty .capt s}
  (hts : EnvTyping Γ env m) :
  ∀ e, (Ty.val_denot env T) m e ->
    resolve_reachability m.heap e ⊆ (T.captureSet).denot env m := by
  intro e ht
  cases T with
  | top =>
    simp only [Ty.captureSet, CaptureSet.denot, CaptureSet.subst, CaptureSet.ground_denot]
    simp only [Ty.val_denot] at ht
    exact ht.2.2
  | tvar X =>
    simp only [Ty.captureSet, CaptureSet.denot, CaptureSet.subst, CaptureSet.ground_denot]
    simp only [Ty.val_denot] at ht
    have hpure := typed_env_enforces_pure hts X
    simp only [Denot.enforce_pure] at hpure
    exact hpure m e ht
  | unit =>
    simp only [Ty.captureSet, CaptureSet.denot, CaptureSet.subst, CaptureSet.ground_denot]
    simp only [Ty.val_denot] at ht
    cases e with
    | unit =>
      simp only [resolve_reachability]
      exact CapabilitySet.Subset.refl
    | var x =>
      cases x with
      | free fx =>
        have hsubset :
            resolve_reachability m.heap (.var (.free fx)) ⊆
              resolve_reachability m.heap .unit :=
          resolve_reachability_subset_of_resolve_aux ht
        simpa only [resolve_reachability] using hsubset
      | bound bx => cases bx
    | _ => simp [resolve] at ht
  | bool =>
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
        cases ht with
        | inl htrue =>
          have hsubset :
              resolve_reachability m.heap (.var (.free fx)) ⊆
                resolve_reachability m.heap .btrue :=
            resolve_reachability_subset_of_resolve_aux htrue
          simpa only [resolve_reachability] using hsubset
        | inr hfalse =>
          have hsubset :
              resolve_reachability m.heap (.var (.free fx)) ⊆
                resolve_reachability m.heap .bfalse :=
            resolve_reachability_subset_of_resolve_aux hfalse
          simpa only [resolve_reachability] using hsubset
      | bound bx => cases bx
    | _ => simp [resolve] at ht
  | cap cs =>
    simp only [Ty.captureSet]
    simp only [Ty.val_denot] at ht
    obtain ⟨_, _, label, heq, hlookup, hcov⟩ := ht
    subst heq
    simp only [resolve_reachability, Memory.lookup] at hlookup ⊢
    simp only [reachability_of_loc, hlookup]
    exact CapabilitySet.covers_eps_imp_singleton_eps_subset hcov
  | cell cs =>
    simp only [Ty.captureSet]
    simp only [Ty.val_denot] at ht
    obtain ⟨_, l, _, _, heq, hlookup, hcov⟩ := ht
    subst heq
    simp only [resolve_reachability, Memory.lookup] at hlookup ⊢
    simp only [reachability_of_loc, hlookup]
    exact CapabilitySet.covers_eps_imp_singleton_eps_subset hcov
  | reader cs =>
    simp only [Ty.captureSet]
    simp only [Ty.val_denot] at ht
    obtain ⟨_, _, label, _, _, hres, hlookup, hcov⟩ := ht
    cases e with
    | reader x =>
      cases x with
      | free fx =>
        simp only [resolve, List.empty_eq] at hres
        cases hres
        simp only [resolve_reachability]
        exact CapabilitySet.covers_imp_singleton_subset hcov
      | bound bx => cases bx
    | var x =>
      cases x with
      | free fx =>
        calc
          resolve_reachability m.heap (.var (.free fx))
              ⊆ resolve_reachability m.heap (.reader (.free label)) := by
                exact resolve_reachability_subset_of_resolve_aux hres
          _ ⊆ cs.denot env m := by
                simpa only [resolve_reachability] using
                  CapabilitySet.covers_imp_singleton_subset hcov
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
  | modal cs Ψ T =>
    simp only [Ty.captureSet]
    simp only [Ty.val_denot] at ht
    obtain ⟨_, _, cs', _, _, hres, _, _, _, hR0_sub, _⟩ := ht
    cases e with
    | boxed cs0 _ _ =>
      simp only [resolve, Option.some.injEq, Exp.boxed.injEq] at hres
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
  (hpeaks : compute_peaks env T.captureSet = compute_peaks env (.var (.M .epsilon) x)) :
  (Ty.val_denot env (T.refineCaptureSet (.var (.M .epsilon) x)))
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
            injection hres with hres
            have hwf_reach := m.wf.wf_reach n v.unwrap v.isVal v.reachability hcell
            have habs_isval : (Exp.abs cs' x0 t0).IsSimpleVal := hres ▸ v.isVal
            have hcomp :
                compute_reachability m.heap v.unwrap v.isVal = expand_captures m.heap cs' := by
              calc compute_reachability m.heap v.unwrap v.isVal
                  = compute_reachability m.heap (Exp.abs cs' x0 t0) habs_isval := by
                      simp only [hres]
                _ = expand_captures m.heap cs' := rfl
            have hreach_loc : reachability_of_loc m.heap n = v.reachability := by
              simp only [reachability_of_loc, hcell]
            have heq : expand_captures m.heap cs' = reachability_of_loc m.heap n := by
              rw [hreach_loc, hwf_reach, hcomp]
            simp only [CaptureSet.denot, CaptureSet.subst, hv, CaptureSet.ground_denot,
                       CapabilitySet.applyAccess_M, CapabilitySet.applyMut]
            rw [heq]
            exact CapabilitySet.Subset.refl
          | capability _ => simp at hres
          | masked => simp at hres
      | bound bx => cases bx
    · intro arg m' hsub hcompat
      exact hbody arg m' hsub hcompat
  | poly T1 cs T2 =>
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
            injection hres with hres
            have hwf_reach := m.wf.wf_reach n v.unwrap v.isVal v.reachability hcell
            have htabs_isval : (Exp.tabs cs' x0 t0).IsSimpleVal := hres ▸ v.isVal
            have hcomp :
                compute_reachability m.heap v.unwrap v.isVal = expand_captures m.heap cs' := by
              calc compute_reachability m.heap v.unwrap v.isVal
                  = compute_reachability m.heap (Exp.tabs cs' x0 t0) htabs_isval := by
                      simp only [hres]
                _ = expand_captures m.heap cs' := rfl
            have hreach_loc : reachability_of_loc m.heap n = v.reachability := by
              simp only [reachability_of_loc, hcell]
            have heq : expand_captures m.heap cs' = reachability_of_loc m.heap n := by
              rw [hreach_loc, hwf_reach, hcomp]
            simp only [CaptureSet.denot, CaptureSet.subst, hv, CaptureSet.ground_denot,
                       CapabilitySet.applyAccess_M, CapabilitySet.applyMut]
            rw [heq]; exact CapabilitySet.Subset.refl
          | capability _ => simp at hres
          | masked => simp at hres
      | bound bx => cases bx
    · intro m' denot hsub hcompat hprop himply_simple himply
      exact hbody m' denot hsub hcompat hprop himply_simple himply
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
            injection hres with hres
            have hwf_reach := m.wf.wf_reach n v.unwrap v.isVal v.reachability hcell
            have hcabs_isval : (Exp.cabs cs' x0 t0).IsSimpleVal := hres ▸ v.isVal
            have hcomp :
                compute_reachability m.heap v.unwrap v.isVal = expand_captures m.heap cs' := by
              calc compute_reachability m.heap v.unwrap v.isVal
                  = compute_reachability m.heap (Exp.cabs cs' x0 t0) hcabs_isval := by
                      simp only [hres]
                _ = expand_captures m.heap cs' := rfl
            have hreach_loc : reachability_of_loc m.heap n = v.reachability := by
              simp only [reachability_of_loc, hcell]
            have heq : expand_captures m.heap cs' = reachability_of_loc m.heap n := by
              rw [hreach_loc, hwf_reach, hcomp]
            simp only [CaptureSet.denot, CaptureSet.subst, hv, CaptureSet.ground_denot,
                       CapabilitySet.applyAccess_M, CapabilitySet.applyMut]
            rw [heq]; exact CapabilitySet.Subset.refl
          | capability _ => simp at hres
          | masked => simp at hres
      | bound bx => cases bx
    · intro m' CS hwf hdf hsub hcompat hbdd
      exact hbody m' CS hwf hdf hsub hcompat hbdd
  | modal cs Ψ T =>
    simp only [Ty.refineCaptureSet, Ty.val_denot] at hdenot ⊢
    obtain ⟨hwf_e, hwf_cs, cs', sepctx0, t0, hres, hwf_cs',
      hwf_sepctx, hsat_impl, hR0_sub, hbody⟩ := hdenot
    refine ⟨hwf_e, ?_, cs', sepctx0, t0, hres, hwf_cs', hwf_sepctx, hsat_impl, ?_, ?_⟩
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
            injection hres with hres
            have hwf_reach := m.wf.wf_reach n v.unwrap v.isVal v.reachability hcell
            have hboxed_isval : (Exp.boxed cs' sepctx0 t0).IsSimpleVal := hres ▸ v.isVal
            have hcomp :
                compute_reachability m.heap v.unwrap v.isVal = expand_captures m.heap cs' := by
              calc compute_reachability m.heap v.unwrap v.isVal
                  = compute_reachability m.heap (Exp.boxed cs' sepctx0 t0) hboxed_isval := by
                      simp only [hres]
                _ = expand_captures m.heap cs' := rfl
            have hreach_loc : reachability_of_loc m.heap n = v.reachability := by
              simp only [reachability_of_loc, hcell]
            have heq : expand_captures m.heap cs' = reachability_of_loc m.heap n := by
              rw [hreach_loc, hwf_reach, hcomp]
            simp only [CaptureSet.denot, CaptureSet.subst, hv, CaptureSet.ground_denot,
              CapabilitySet.applyAccess_M, CapabilitySet.applyMut]
            rw [heq]
            exact CapabilitySet.Subset.refl
          | capability _ => simp at hres
          | masked => simp at hres
      | bound bx => cases bx
    · intro m' hsub hcompat hkind hsep
      exact hbody m' hsub hcompat hkind hsep
  | cap cs =>
    simp only [Ty.refineCaptureSet, Ty.val_denot] at hdenot ⊢
    obtain ⟨hwf_e, hwf_cs, label, heq, hlookup, hcov⟩ := hdenot
    simp only [Exp.var.injEq] at heq
    refine ⟨hwf_e, ?_, label, ?_, hlookup, ?_⟩
    · simp only [CaptureSet.subst]
      cases hwf_e with
      | wf_var hwf_var =>
        exact CaptureSet.wf_of_var hwf_var
    · simp only [heq]
    · simp only [CaptureSet.denot, CaptureSet.subst, heq,
                 CaptureSet.ground_denot, CapabilitySet.applyAccess_M, CapabilitySet.applyMut]
      change m.heap label = some (Cell.capability .basic) at hlookup
      cases hcell : m.heap label with
      | none => simp [hcell] at hlookup
      | some cell =>
        simp only [reachability_of_loc, hcell]
        cases cell with
        | val v => simp [hcell] at hlookup
        | capability cap =>
          exact CapabilitySet.covers.here CapMode.Le.refl
        | masked => simp [hcell] at hlookup
  | cell cs =>
    simp only [Ty.refineCaptureSet, Ty.val_denot] at hdenot ⊢
    obtain ⟨hwf_cs, label, b0, ℓ0, heq, hlookup, hcov⟩ := hdenot
    simp only [Exp.var.injEq] at heq
    refine ⟨?_, label, b0, ℓ0, ?_, hlookup, ?_⟩
    · simp only [CaptureSet.subst]
      rw [heq]
      exact CaptureSet.WfInHeap.wf_var_free (by simpa only [Memory.lookup] using hlookup)
    · simp only [heq]
    · simp only [CaptureSet.denot, CaptureSet.subst, heq,
                 CaptureSet.ground_denot, CapabilitySet.applyAccess_M, CapabilitySet.applyMut]
      change m.heap label = some (Cell.capability (.mcell b0 ℓ0)) at hlookup
      cases hcell : m.heap label with
      | none => simp [hcell] at hlookup
      | some cell =>
        simp only [reachability_of_loc, hcell]
        cases cell with
        | val v => simp [hcell] at hlookup
        | capability cap =>
          exact CapabilitySet.covers.here CapMode.Le.refl
        | masked => simp [hcell] at hlookup
  | reader cs =>
    simp only [Ty.refineCaptureSet, Ty.val_denot] at hdenot ⊢
    obtain ⟨hwf_e, hwf_cs, loc, label, ℓ0, hres, hlookup, hcov⟩ := hdenot
    refine ⟨hwf_e, ?_, loc, label, ℓ0, hres, hlookup, ?_⟩
    · simp only [CaptureSet.subst]
      cases hwf_e with
      | wf_var hwf_var =>
        exact CaptureSet.wf_of_var hwf_var
    · simp only [CaptureSet.denot, CaptureSet.subst]
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
            injection hres with hres
            have hwf_reach := m.wf.wf_reach n v.unwrap v.isVal v.reachability hcell
            have hreader_isval : (Exp.reader (Var.free loc)).IsSimpleVal := hres ▸ v.isVal
            have hcomp :
                compute_reachability m.heap v.unwrap v.isVal = .cap (.access .ro) loc := by
              calc compute_reachability m.heap v.unwrap v.isVal
                  = compute_reachability m.heap (Exp.reader (Var.free loc)) hreader_isval := by
                      simp only [hres]
                _ = .cap (.access .ro) loc := rfl
            have hreach_loc : reachability_of_loc m.heap n = v.reachability := by
              simp only [reachability_of_loc, hcell]
            have heq : reachability_of_loc m.heap n = .cap (.access .ro) loc := by
              rw [hreach_loc, hwf_reach, hcomp]
            simp only [CaptureSet.ground_denot, CapabilitySet.applyAccess_M,
                       CapabilitySet.applyMut]
            rw [heq]
            exact CapabilitySet.covers.here CapMode.Le.refl
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
    resolve_reachability m.heap e ⊆ resolve_reachability m.heap v :=
  resolve_reachability_subset_of_resolve_aux hresolve

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
  case arrow T1 cs T2 | poly T1 cs T2 | cpoly B cs T =>
    simp only [Ty.captureSet] at hpure
    simp only [Ty.val_denot] at hdenot
    obtain ⟨_, _, cs', _, _, hres, _, hR0_sub, _⟩ := hdenot
    exact CapabilitySet.Subset.trans
      (resolve_reachability_subset_of_resolve hres)
      (by simpa [resolve_reachability] using hpure.denot_empty.subset_of_subset hR0_sub)
  case modal cs Ψ T =>
    simp only [Ty.captureSet] at hpure
    simp only [Ty.val_denot] at hdenot
    obtain ⟨_, _, cs', _, _, hres, _, _, _, hR0_sub, _⟩ := hdenot
    exact CapabilitySet.Subset.trans
      (resolve_reachability_subset_of_resolve hres)
      (by simpa [resolve_reachability] using hpure.denot_empty.subset_of_subset hR0_sub)

namespace TypeEnv.HasSepDom

theorem union_inv_left {env : TypeEnv s} {C1 C2 : CaptureSet s}
  (h : env.HasSepDom (C1 ∪ C2)) :
  env.HasSepDom C1 :=
  fun m1 c1 m2 c2 hsub1 hsub2 hne =>
    h m1 c1 m2 c2 (.union_right_left hsub1) (.union_right_left hsub2) hne

theorem union_inv_right {env : TypeEnv s} {C1 C2 : CaptureSet s}
  (h : env.HasSepDom (C1 ∪ C2)) :
  env.HasSepDom C2 :=
  fun m1 c1 m2 c2 hsub1 hsub2 hne =>
    h m1 c1 m2 c2 (.union_right_right hsub1) (.union_right_right hsub2) hne

theorem union_intro {env : TypeEnv s} {C1 C2 : CaptureSet s}
  (h1 : env.HasSepDom C1) (h2 : env.HasSepDom C2)
  (hcross : ∀ m1 c1 m2 c2,
    (.cvar m1 c1) ⊆ compute_peaks env C1 → (.cvar m2 c2) ⊆ compute_peaks env C2 → c1 ≠ c2 →
    CapabilitySet.Noninterference
      ((env.lookup_cvar c1).2.applyAccess m1)
      ((env.lookup_cvar c2).2.applyAccess m2)) :
  env.HasSepDom (C1 ∪ C2) := by
  intro m1 c1 m2 c2 hsub1 hsub2 hne
  cases hsub1 with
  | union_right_left hsub1' =>
    cases hsub2 with
    | union_right_left hsub2' =>
      exact h1 m1 c1 m2 c2 hsub1' hsub2' hne
    | union_right_right hsub2' =>
      exact hcross m1 c1 m2 c2 hsub1' hsub2' hne
  | union_right_right hsub1' =>
    cases hsub2 with
    | union_right_left hsub2' =>
      exact CapabilitySet.Noninterference.ni_symm (hcross m2 c2 m1 c1 hsub2' hsub1' (Ne.symm hne))
    | union_right_right hsub2' =>
      exact h2 m1 c1 m2 c2 hsub1' hsub2' hne

theorem union_comm {env : TypeEnv s} {C1 C2 : CaptureSet s}
  (h : env.HasSepDom (C2 ∪ C1)) :
  env.HasSepDom (C1 ∪ C2) := by
  intro m1 c1 m2 c2 hsub1 hsub2 hne
  apply h _ _ _ _ _ _ hne
  · cases hsub1 with
    | union_right_left h1 => exact CaptureSet.Subset.union_right_right h1
    | union_right_right h1 => exact CaptureSet.Subset.union_right_left h1
  · cases hsub2 with
    | union_right_left h2 => exact CaptureSet.Subset.union_right_right h2
    | union_right_right h2 => exact CaptureSet.Subset.union_right_left h2

theorem coveredby_mono {env : TypeEnv s} {C1 C2 : CaptureSet s}
  (h : env.HasSepDom C2)
  (hs : (compute_peaks env C1).CoveredBy (compute_peaks env C2)) :
  env.HasSepDom C1 := by
  intro m1 c1 m2 c2 hsub1 hsub2 hne
  obtain ⟨m1', hle1, hsub1'⟩ := CaptureSet.CoveredBy.cvar_subset_coveredby hsub1 hs
  obtain ⟨m2', hle2, hsub2'⟩ := CaptureSet.CoveredBy.cvar_subset_coveredby hsub2 hs
  have hni := h m1' c1 m2' c2 hsub1' hsub2' hne
  have hsub_cap1 :
      (env.lookup_cvar c1).2.applyAccess m1 ⊆ (env.lookup_cvar c1).2.applyAccess m1' := by
    cases hle1 with
    | M hm =>
      cases hm with
      | refl => exact CapabilitySet.Subset.refl
      | ro_eps =>
        simp only [CapabilitySet.applyAccess_M, CapabilitySet.applyMut]
        exact @CapabilitySet.applyRO_subset_applyMut _ .epsilon
    | drop => exact CapabilitySet.Subset.refl
  have hsub_cap2 :
      (env.lookup_cvar c2).2.applyAccess m2 ⊆ (env.lookup_cvar c2).2.applyAccess m2' := by
    cases hle2 with
    | M hm =>
      cases hm with
      | refl => exact CapabilitySet.Subset.refl
      | ro_eps =>
        simp only [CapabilitySet.applyAccess_M, CapabilitySet.applyMut]
        exact @CapabilitySet.applyRO_subset_applyMut _ .epsilon
    | drop => exact CapabilitySet.Subset.refl
  exact CapabilitySet.Noninterference.subset_right
    (CapabilitySet.Noninterference.subset_left hni hsub_cap1) hsub_cap2

end TypeEnv.HasSepDom

end CoreCapybara
