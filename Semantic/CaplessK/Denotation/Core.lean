import Semantic.CaplessK.Semantics
import Semantic.CaplessK.TypeSystem
import Semantic.Prelude

namespace CaplessK

/-- Denotation of types. -/
def Denot := Memory -> Exp {} -> Prop

def Denot.Or (d1 d2 : Denot) : Denot :=
  fun m e => d1 m e ∨ d2 m e

/-- Pre-denotation. It takes a capability to form a denotation. -/
def PreDenot := CapabilitySet -> Denot

/-- Capture-denotation. Given any memory, it produces a set of capabilities. -/
def CapDenot := Memory -> CapabilitySet

/-- A bound on capability sets. It can either be a concrete set of the top element. -/
inductive CapabilityBound : Type where
| top : CapKind -> CapabilityBound
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

lemma Denot.Or.is_monotonic {d1 d2 : Denot}
    (h1 : d1.is_monotonic) (h2 : d2.is_monotonic) :
    (d1.Or d2).is_monotonic := by
  intro m1 m2 e hmem hor
  cases hor with
  | inl h => exact Or.inl (h1 hmem h)
  | inr h => exact Or.inr (h2 hmem h)

lemma Denot.Or.is_bool_independent {d1 d2 : Denot}
    (h1 : d1.is_bool_independent) (h2 : d2.is_bool_independent) :
    (d1.Or d2).is_bool_independent := by
  intro m
  constructor
  · intro hor
    cases hor with
    | inl h => exact Or.inl (h1.mp h)
    | inr h => exact Or.inr (h2.mp h)
  · intro hor
    cases hor with
    | inl h => exact Or.inl (h1.mpr h)
    | inr h => exact Or.inr (h2.mpr h)

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

lemma Denot.Imply.or_right {d1 d2 : Denot}
    (himp : d1.Imply d2) (h : Denot) :
    (d1.Or h).Imply (d2.Or h) := by
  intro m e hor
  cases hor with
  | inl h1 => exact Or.inl (himp m e h1)
  | inr h2 => exact Or.inr h2

lemma Denot.ImplyAfter.or_right {d1 d2 : Denot} {H : Memory}
    (himp : d1.ImplyAfter H d2) (h : Denot) :
    (d1.Or h).ImplyAfter H (d2.Or h) := by
  intro m' hsub e hor
  cases hor with
  | inl h1 => exact Or.inl (himp m' hsub e h1)
  | inr h2 => exact Or.inr h2

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

/-- Context for computing denotation of types. -/
structure DenotCtx (s : Sig) where
  /-- Context for type environment. -/
  env : TypeEnv s
  /-- Handlers maps a label to a denotation, which specifies
    what value the handler of the label accepts. -/
  handlers : Finmap Nat Denot

def DenotCtx.extend_handlers (ctx : DenotCtx s) (l : Nat) (D : Denot) : DenotCtx s :=
  ⟨ctx.env, ctx.handlers.extend l D⟩

/-- Denotation for throw forms that can be handled by the given handlers. -/
def denot_of_handlers (handlers : Finmap Nat Denot) : Denot :=
  fun m e =>
    ∃ l D x,
      handlers.apply l = some D ∧
      e = .throw (.free l) x ∧
      D m (.var x)

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

def DenotCtx.extend_var (ctx : DenotCtx s) (x : Nat) : DenotCtx (s,x) :=
  ⟨ctx.env.extend_var x, ctx.handlers⟩

def DenotCtx.extend_tvar (ctx : DenotCtx s) (T : PreDenot) : DenotCtx (s,X) :=
  ⟨ctx.env.extend_tvar T, ctx.handlers⟩

def DenotCtx.extend_cvar (ctx : DenotCtx s) (ground : CaptureSet {}) : DenotCtx (s,C) :=
  ⟨ctx.env.extend_cvar ground, ctx.handlers⟩

def DenotCtx.lookup_var (ctx : DenotCtx s) (x : BVar s .var) : Nat :=
  ctx.env.lookup_var x

def DenotCtx.lookup_tvar (ctx : DenotCtx s) (x : BVar s .tvar) : PreDenot :=
  ctx.env.lookup_tvar x

def DenotCtx.lookup_cvar (ctx : DenotCtx s) (x : BVar s .cvar) : CaptureSet {} :=
  ctx.env.lookup_cvar x

def DenotCtx.empty : DenotCtx {} := ⟨TypeEnv.empty, Finmap.empty⟩

@[simp]
theorem TypeEnv.lookup_cvar_extend_var {Γ : TypeEnv s} {x : Nat} {c : BVar s .cvar} :
    (Γ.extend_var x).lookup_cvar (.there c) = Γ.lookup_cvar c := rfl

@[simp]
theorem TypeEnv.lookup_cvar_extend_tvar {Γ : TypeEnv s} {T : PreDenot} {c : BVar s .cvar} :
    (Γ.extend_tvar T).lookup_cvar (.there c) = Γ.lookup_cvar c := rfl

@[simp]
theorem TypeEnv.lookup_cvar_extend_cvar_here {Γ : TypeEnv s} {cs : CaptureSet {}} :
    (Γ.extend_cvar cs).lookup_cvar .here = cs := rfl

@[simp]
theorem TypeEnv.lookup_cvar_extend_cvar_there
    {Γ : TypeEnv s} {cs : CaptureSet {}} {c : BVar s .cvar} :
    (Γ.extend_cvar cs).lookup_cvar (.there c) = Γ.lookup_cvar c := rfl

def Subst.from_TypeEnv (env : TypeEnv s) : Subst s {} where
  var := fun x => .free (env.lookup_var x)
  tvar := fun _ => .top
  cvar := fun c K => (env.lookup_cvar c).proj K

def Subst.from_DenotCtx (ctx : DenotCtx s) : Subst s {} :=
  Subst.from_TypeEnv ctx.env

theorem Subst.from_DenotCtx_empty :
  Subst.from_DenotCtx DenotCtx.empty = Subst.id := by
  simp only [from_DenotCtx, DenotCtx.empty]
  apply Subst.funext
  · intro x; cases x
  · intro X; cases X
  · intro C; cases C

theorem Subst.from_TypeEnv_empty :
  Subst.from_TypeEnv TypeEnv.empty = Subst.id := by
  apply Subst.funext
  · intro x; cases x
  · intro X; cases X
  · intro C; cases C

/-- Projection commutes with substitution by from_TypeEnv. -/
theorem CaptureSet.proj_subst_from_TypeEnv {cs : CaptureSet s} {env : TypeEnv s} {K : CapKind} :
    (cs.subst (Subst.from_TypeEnv env)).proj K = (cs.proj K).subst (Subst.from_TypeEnv env) := by
  induction cs with
  | empty => rfl
  | union cs1 cs2 ih1 ih2 =>
    simp only [CaptureSet.subst, CaptureSet.proj, ih1, ih2]
  | var x K' =>
    cases x
    case bound x =>
      simp only [CaptureSet.subst, Var.subst, CaptureSet.proj]
    case free n =>
      simp only [CaptureSet.subst, Var.subst, CaptureSet.proj]
  | cvar c K' =>
    simp only [CaptureSet.subst, CaptureSet.proj, Subst.from_TypeEnv, CaptureSet.proj_proj]

/-- Compute denotation for a ground capture set. -/
def CaptureSet.ground_denot : CaptureSet {} -> CapDenot
| .empty => fun _ => {}
| .union cs1 cs2 => fun m =>
  (cs1.ground_denot m) ∪ (cs2.ground_denot m)
| .var (.free x) K =>
  fun m => (reachability_of_loc m.heap x).proj m.heap K

def CaptureSet.denot (ctx : DenotCtx s) (cs : CaptureSet s) : CapDenot :=
  (cs.subst (Subst.from_DenotCtx ctx)).ground_denot

/-- Ground denotation of a well-formed closed capture set is well-formed. -/
theorem CaptureSet.ground_denot_wf {cs : CaptureSet {}} {m : Memory}
    (hwf : cs.WfInHeap m.heap) :
    (cs.ground_denot m).WfInHeap m.heap := by
  induction cs with
  | empty =>
    intro l hl
    cases hl
  | union cs1 cs2 ih1 ih2 =>
    simp only [ground_denot]
    intro l hl
    cases hl with
    | left hmem1 =>
      cases hwf with
      | wf_union hwf1 hwf2 =>
        exact ih1 hwf1 l hmem1
    | right hmem2 =>
      cases hwf with
      | wf_union hwf1 hwf2 =>
        exact ih2 hwf2 l hmem2
  | var v K =>
    cases v with
    | free x =>
      simp only [ground_denot]
      intro l hl
      cases hwf with
      | wf_var_free hlookup =>
        have hwf_reach : (reachability_of_loc m.heap x).WfInHeap m.heap :=
          reachability_of_loc_locations_exist m.wf hlookup
        have hl_in_orig := CapabilitySet.subset_preserves_mem CapabilitySet.proj_subset_self hl
        exact hwf_reach l hl_in_orig
    | bound bv => cases bv
  | cvar c K => cases c

/-- Syntactic projection commutes with ground denotation via semantic projection. -/
theorem CaptureSet.ground_denot_proj_eq {cs : CaptureSet {}} {m : Memory} {K : CapKind} :
    (cs.proj K).ground_denot m = (cs.ground_denot m).proj m.heap K := by
  induction cs with
  | empty => rfl
  | union cs1 cs2 ih1 ih2 =>
    simp only [CaptureSet.proj, ground_denot, ih1, ih2, CapabilitySet.proj]
    rfl
  | var v K' =>
    cases v with
    | free x =>
      simp only [CaptureSet.proj, ground_denot]
      rw [← CapabilitySet.proj_proj]
    | bound bv => cases bv
  | cvar c K' => cases c

/-- Syntactic projection commutes with denotation via semantic projection. -/
theorem CaptureSet.denot_proj_eq {cs : CaptureSet s} {ctx : DenotCtx s} {m : Memory} {K : CapKind} :
    (cs.proj K).denot ctx m = (cs.denot ctx m).proj m.heap K := by
  simp only [CaptureSet.denot, Subst.from_DenotCtx]
  rw [← CaptureSet.proj_subst_from_TypeEnv]
  exact CaptureSet.ground_denot_proj_eq

def CaptureBound.denot : DenotCtx s -> CaptureBound s -> CapBoundDenot
| _, .unbound K => fun _ => .top K
| ctx, .bound cs => fun m => .set (cs.denot ctx m)

inductive CapabilitySet.BoundedBy : Heap -> CapabilitySet -> CapabilityBound -> Prop where
| top :
  CapabilitySet.HasKind H C K ->
  CapabilitySet.BoundedBy H C (CapabilityBound.top K)
| set :
  C1 ⊆ C2 ->
  CapabilitySet.BoundedBy H C1 (CapabilityBound.set C2)

inductive CapabilityBound.Subbound : Heap -> CapabilityBound -> CapabilityBound -> Prop where
| set :
  C1 ⊆ C2 ->
  CapabilityBound.Subbound H (CapabilityBound.set C1) (CapabilityBound.set C2)
| kind :
  CapabilitySet.HasKind H C K ->
  CapabilityBound.Subbound H (CapabilityBound.set C) (CapabilityBound.top K)
| subkind :
  CapKind.Subkind K1 K2 ->
  CapabilityBound.Subbound H (CapabilityBound.top K1) (CapabilityBound.top K2)

theorem CapabilitySet.BoundedBy.trans
  {H : Heap} {C : CapabilitySet} {B1 B2 : CapabilityBound}
  (hbound : CapabilitySet.BoundedBy H C B1)
  (hsub : CapabilityBound.Subbound H B1 B2) :
  CapabilitySet.BoundedBy H C B2 := by
  cases hsub with
  | set hsub_set =>
    cases hbound with
    | set hbound_set =>
      exact CapabilitySet.BoundedBy.set
        (CapabilitySet.Subset.trans hbound_set hsub_set)
  | kind hkind =>
    cases hbound with
    | set hsub_bound => exact CapabilitySet.BoundedBy.top (hkind.subset hsub_bound)
  | subkind hsub =>
    cases hbound with
    | top hkind => exact CapabilitySet.BoundedBy.top (hkind.subkind hsub)

/-- Given `H` a heap and `dom` a set of registered labels in `DenotCtx`,
  a capability set `C` is well-scoped if every label capability in it is registered in `dom`. -/
def CapabilitySet.WellScoped (H : Heap) (C : CapabilitySet) (dom : Finset Nat) : Prop :=
  ∀ l,
    l ∈ C ->
    (∃ K,
      H l = some (.capability (.label K))) ->
    l ∈ dom

/-- WellScoped is anti-monotonic in the capability set: a subset of a well-scoped set
    is also well-scoped. -/
theorem CapabilitySet.WellScoped.subset
    {C1 C2 : CapabilitySet} {H : Heap} {dom : Finset Nat}
    (hsub : C1 ⊆ C2) (hws : C2.WellScoped H dom) : C1.WellScoped H dom := by
  intro l hl hlab
  exact hws l (CapabilitySet.subset_preserves_mem hsub hl) hlab

/-- WellScoped transfers from a smaller heap to a bigger heap, given WfInHeap at the smaller heap.
    If all label capabilities in C are registered in dom w.r.t. the smaller heap H1,
    and C's elements exist in H1, and H2 subsumes H1,
    then C is also well-scoped w.r.t. H2. -/
theorem CapabilitySet.WellScoped.heap_mono
    {C : CapabilitySet} {H1 H2 : Heap} {dom : Finset Nat}
    (hws : C.WellScoped H1 dom) (hwf : C.WfInHeap H1) (hsub : Heap.subsumes H2 H1) :
    C.WellScoped H2 dom := by
  intro l hl ⟨K, hK⟩
  apply hws l hl
  obtain ⟨cell, hcell⟩ := hwf l hl
  obtain ⟨cell', hcell', hsub_cell⟩ := hsub l cell hcell
  have heq : cell' = .capability (.label K) := by
    have h1 := hcell'
    rw [h1] at hK
    exact Option.some.inj hK
  subst heq
  have : cell = .capability (.label K) := by
    revert hsub_cell; cases cell with
    | val _ => simp [Cell.subsumes]
    | capability info => cases info with
      | basic => simp [Cell.subsumes]
      | label => simp [Cell.subsumes]; intro h; exact h.symm
      | mcell => simp [Cell.subsumes]
    | masked _ => simp [Cell.subsumes]
  exact ⟨K, by subst this; exact hcell⟩

/-- BoundedBy is monotonic with respect to heap subsumption. -/
theorem CapabilitySet.BoundedBy.monotonic
  {H1 H2 : Heap} {C : CapabilitySet} {B : CapabilityBound}
  (hsub_heap : H2.subsumes H1)
  (hwf : C.WfInHeap H1)
  (hbound : CapabilitySet.BoundedBy H1 C B) :
  CapabilitySet.BoundedBy H2 C B := by
  cases hbound with
  | top hkind => exact .top (hkind.monotonic hsub_heap hwf)
  | set hsub => exact .set hsub

mutual

def Ty.shape_val_denot : DenotCtx s -> Ty .shape s -> PreDenot
| _, .top => fun R m e =>
  e.WfInHeap m.heap ∧ resolve_reachability m.heap e ⊆ R
| ctx, .tvar X => ctx.lookup_tvar X
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
| ctx, .label S => fun R m e =>
  ∃ l K D0,
    e = .var (.free l) ∧
    m.lookup l = some (.capability (.label K)) ∧
    ctx.handlers.apply l = some D0 ∧
    (shape_val_denot ctx S .empty).ImplyAfter m D0 ∧
    l ∈ R
| ctx, .arrow T1 T2 => fun A m e =>
  e.WfInHeap m.heap ∧
  ∃ cs T0 t0,
    resolve m.heap e = some (.abs cs T0 t0) ∧
    cs.WfInHeap m.heap ∧
    let R0 := expand_captures m.heap cs
    R0 ⊆ A ∧
    (∀ (arg : Nat) (m' : Memory),
      m'.subsumes m ->
      Ty.capt_val_denot ctx T1 m' (.var (.free arg)) ->
      Ty.exi_exp_denot
        (ctx.extend_var arg)
        T2 (R0 ∪ (reachability_of_loc m'.heap arg)) m' (t0.subst (Subst.openVar (.free arg))))
| ctx, .poly T1 T2 => fun A m e =>
  e.WfInHeap m.heap ∧
  ∃ cs S0 t0,
    resolve m.heap e = some (.tabs cs S0 t0) ∧
    cs.WfInHeap m.heap ∧
    let R0 := expand_captures m.heap cs
    R0 ⊆ A ∧
    (∀ (m' : Memory) (denot : PreDenot),
      m'.subsumes m ->
      denot.is_proper ->
      denot.ImplyAfter m' (Ty.shape_val_denot ctx T1) ->
      Ty.exi_exp_denot
        (ctx.extend_tvar denot)
        T2 R0 m' (t0.subst (Subst.openTVar .top)))
| ctx, .cpoly B T => fun A m e =>
  e.WfInHeap m.heap ∧
  ∃ cs B0 t0,
    resolve m.heap e = some (.cabs cs B0 t0) ∧
    cs.WfInHeap m.heap ∧
    let R0 := expand_captures m.heap cs
    R0 ⊆ A ∧
    (∀ (m' : Memory) (CS : CaptureSet {}),
      CS.WfInHeap m'.heap ->
      let A0 := CS.denot DenotCtx.empty
      m'.subsumes m ->
      (CapabilitySet.BoundedBy m'.heap (A0 m') (B.denot ctx m')) ->
      Ty.exi_exp_denot
        (ctx.extend_cvar CS)
        T R0 m' (t0.subst (Subst.openCVar CS)))

def Ty.capt_val_denot : DenotCtx s -> Ty .capt s -> Denot
| ctx, .capt C S => fun mem exp =>
  exp.IsSimpleAns ∧
  exp.WfInHeap mem.heap ∧
  (C.subst (Subst.from_DenotCtx ctx)).WfInHeap mem.heap ∧
  Ty.shape_val_denot ctx S (C.denot ctx mem) mem exp

def Ty.exi_val_denot : DenotCtx s -> Ty .exi s -> Denot
| ctx, .typ T => Ty.capt_val_denot ctx T
| ctx, .exi T => fun m e =>
  match resolve m.heap e with
  | some (.pack CS x) =>
    CS.WfInHeap m.heap ∧
    Ty.capt_val_denot (ctx.extend_cvar CS) T m (.var x)
  | _ => False

def Ty.exi_exp_denot : DenotCtx s -> Ty .exi s -> PreDenot
| ctx, T => fun A m (e : Exp {}) =>
  --A.WellScoped m.heap (ctx.handlers.dom) ->
  Eval A m e ((Ty.exi_val_denot ctx T).Or (denot_of_handlers ctx.handlers)).as_mpost

end

@[simp]
instance instCaptHasDenotation :
  HasDenotation (Ty .capt s) (DenotCtx s) Denot where
  interp := Ty.capt_val_denot

@[simp]
instance instExiHasDenotation :
  HasDenotation (Ty .exi s) (DenotCtx s) Denot where
  interp := Ty.exi_val_denot

@[simp]
instance instExiHasExpDenotation :
  HasExpDenotation (Ty .exi s) (DenotCtx s) PreDenot where
  interp := Ty.exi_exp_denot

@[simp]
instance instShapeHasDenotation :
  HasDenotation (Ty .shape s) (DenotCtx s) PreDenot where
  interp := Ty.shape_val_denot

@[simp]
instance instCaptureSetHasDenotation :
  HasDenotation (CaptureSet s) (DenotCtx s) CapDenot where
  interp := CaptureSet.denot

@[simp]
instance instCaptureBoundHasDenotation :
  HasDenotation (CaptureBound s) (DenotCtx s) CapBoundDenot where
  interp := CaptureBound.denot

def handlers_are_monotonic
  (handlers : Finmap Nat Denot) : Prop :=
  ∀ l D,
    handlers.apply l = some D ->
    D.is_monotonic

lemma denot_of_handlers_is_bool_independent (handlers : Finmap Nat Denot) :
    (denot_of_handlers handlers).is_bool_independent := by
  intro m
  constructor
  · intro ⟨_, _, _, _, heq, _⟩; cases heq
  · intro ⟨_, _, _, _, heq, _⟩; cases heq

lemma denot_of_handlers_is_monotonic (handlers : Finmap Nat Denot)
    (hmono : handlers_are_monotonic handlers) :
    (denot_of_handlers handlers).is_monotonic := by
  intro m1 m2 e hmem h
  obtain ⟨l, D, x, happly, heq, hD⟩ := h
  exact ⟨l, D, x, happly, heq, hmono l D happly hmem hD⟩

def EnvTyping : Ctx s -> DenotCtx s -> Memory -> Prop
| .empty, ⟨.empty, handlers⟩, _ => handlers_are_monotonic handlers
| .push Γ (.var T), ⟨.extend env (.var n), handlers⟩, m =>
  let ctx : DenotCtx _ := ⟨env, handlers⟩
  ⟦T⟧_[ctx] m (.var (.free n)) ∧
  EnvTyping Γ ctx m
| .push Γ (.tvar S), ⟨.extend env (.tvar denot), handlers⟩, m =>
  let ctx : DenotCtx _ := ⟨env, handlers⟩
  denot.is_proper ∧
  denot.ImplyAfter m ⟦S⟧_[ctx] ∧
  EnvTyping Γ ctx m
| .push Γ (.cvar B), ⟨.extend env (.cvar cs), handlers⟩, m =>
  let ctx : DenotCtx _ := ⟨env, handlers⟩
  (cs.WfInHeap m.heap) ∧
  ((B.subst (Subst.from_DenotCtx ctx)).WfInHeap m.heap) ∧
  (CapabilitySet.BoundedBy m.heap (cs.ground_denot m) (⟦B⟧_[ctx] m)) ∧
  EnvTyping Γ ctx m

def SemanticTyping (C : CaptureSet s) (Γ : Ctx s) (e : Exp s) (E : Ty .exi s) : Prop :=
  ∀ ctx m,
    EnvTyping Γ ctx m ->
    ⟦E⟧e_[ctx] (C.denot ctx m) m (e.subst (Subst.from_DenotCtx ctx))

notation:65 C " # " Γ " ⊨ " e " : " T => SemanticTyping C Γ e T

theorem Subst.from_DenotCtx_weaken_open {ctx : DenotCtx s} {x : Nat} :
  (Subst.from_DenotCtx ctx).lift.comp (Subst.openVar (.free x)) =
    Subst.from_DenotCtx (ctx.extend_var x) := by
  simp only [from_DenotCtx, DenotCtx.extend_var]
  apply Subst.funext
  · intro y
    cases y <;> rfl
  · intro X
    cases X
    rfl
  · intro C K
    cases C with
    | there C' =>
      simp [Subst.from_TypeEnv, Subst.lift, Subst.comp, Subst.openVar,
        TypeEnv.extend_var, TypeEnv.lookup_cvar, TypeEnv.lookup]
      exact CaptureSet.weaken_openVar

theorem Exp.from_DenotCtx_weaken_open {ctx : DenotCtx s} {e : Exp (s,x)} :
  (e.subst (Subst.from_DenotCtx ctx).lift).subst (Subst.openVar (.free x)) =
    e.subst (Subst.from_DenotCtx (ctx.extend_var x)) := by
  rw [Exp.subst_comp]
  rw [Subst.from_DenotCtx_weaken_open]

theorem Subst.from_DenotCtx_weaken_open_tvar {ctx : DenotCtx s} {d : PreDenot} :
  (Subst.from_DenotCtx ctx).lift.comp (Subst.openTVar .top) =
    Subst.from_DenotCtx (ctx.extend_tvar d) := by
  simp only [from_DenotCtx, DenotCtx.extend_tvar]
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
  · intro C K
    cases C with
    | there C' =>
      simp [Subst.from_TypeEnv, Subst.lift, Subst.comp, Subst.openTVar,
        TypeEnv.extend_tvar, TypeEnv.lookup_cvar, TypeEnv.lookup]
      exact CaptureSet.weaken_openTVar

theorem Exp.from_DenotCtx_weaken_open_tvar
  {ctx : DenotCtx s} {d : PreDenot} {e : Exp (s,X)} :
  (e.subst (Subst.from_DenotCtx ctx).lift).subst (Subst.openTVar .top) =
    e.subst (Subst.from_DenotCtx (ctx.extend_tvar d)) := by
  rw [Exp.subst_comp]
  rw [Subst.from_DenotCtx_weaken_open_tvar]

theorem Subst.from_DenotCtx_weaken_open_cvar
  {ctx : DenotCtx s} {cs : CaptureSet {}} :
  (Subst.from_DenotCtx ctx).lift.comp (Subst.openCVar cs) =
    Subst.from_DenotCtx (ctx.extend_cvar cs) := by
  simp only [from_DenotCtx, DenotCtx.extend_cvar]
  apply Subst.funext
  · intro x
    cases x
    rfl
  · intro X
    cases X
    rfl
  · intro C K
    cases C
    case here => rfl
    case there C' =>
      simp [Subst.comp, Subst.lift, Subst.from_TypeEnv, Subst.openCVar,
        TypeEnv.extend_cvar, TypeEnv.lookup_cvar, TypeEnv.lookup]
      exact CaptureSet.weaken_openCVar

theorem Exp.from_DenotCtx_weaken_open_cvar
  {ctx : DenotCtx s} {cs : CaptureSet {}} {e : Exp (s,C)} :
  (e.subst (Subst.from_DenotCtx ctx).lift).subst (Subst.openCVar cs) =
    e.subst (Subst.from_DenotCtx (ctx.extend_cvar cs)) := by
  rw [Exp.subst_comp]
  rw [Subst.from_DenotCtx_weaken_open_cvar]

theorem Subst.from_DenotCtx_weaken_unpack {ctx : DenotCtx s} :
  (Subst.from_DenotCtx ctx).lift.lift.comp (Subst.unpack cs (.free x)) =
    Subst.from_DenotCtx ((ctx.extend_cvar cs).extend_var x) := by
  simp only [from_DenotCtx, DenotCtx.extend_cvar, DenotCtx.extend_var]
  apply Subst.funext
  · -- var case
    intro y
    cases y
    case here => rfl
    case there y' =>
      cases y'
      case there v =>
        simp [Subst.comp, Subst.unpack, Var.subst]
        rw [Subst.lift_there_var_eq]
        rw [Subst.lift_there_var_eq]
        simp [Subst.from_TypeEnv, Var.rename, TypeEnv.lookup_var]
        simp [TypeEnv.extend_var, TypeEnv.extend_cvar, TypeEnv.lookup]
  · -- tvar case
    intro X
    cases X
    case there X' =>
      cases X'
      case there X0 => rfl
  · -- cvar case
    intro c K
    cases c
    case there c' =>
      cases c'
      case here =>
        simp [Subst.comp, Subst.unpack]
        simp [Subst.lift, CaptureSet.subst, CaptureSet.rename]
        rfl
      case there c0 =>
        simp [Subst.comp, Subst.unpack]
        simp only [Subst.from_TypeEnv, TypeEnv.extend_var, TypeEnv.extend_cvar,
          TypeEnv.lookup_cvar, TypeEnv.lookup, Subst.lift]
        generalize (match ctx.env.lookup c0 with | TypeInfo.cvar cs => cs) = ground_cs
        induction ground_cs with
        | empty => rfl
        | union cs1 cs2 ih1 ih2 =>
          simp only [CaptureSet.proj, CaptureSet.rename, CaptureSet.subst, ih1, ih2]
        | var v ck =>
          cases v with
          | bound bv => cases bv
          | free n => rfl
        | cvar cv ck => cases cv

theorem Subst.from_TypeEnv_weaken_open {env : TypeEnv s} {x : Nat} :
  (Subst.from_TypeEnv env).lift.comp (Subst.openVar (.free x)) =
    Subst.from_TypeEnv (env.extend_var x) := by
  apply Subst.funext
  · intro y
    cases y <;> rfl
  · intro X
    cases X
    rfl
  · intro C K
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
  · intro C K
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
  · intro C K
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
    intro c K
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
        simp [Subst.lift, CaptureSet.subst, CaptureSet.rename]
        -- Goal: match Rename.succ.var .here with | .here.there => cs | ... = cs
        -- Rename.succ.var .here = .here.there by definition
        rfl
      case there c0 =>
        -- LHS: comp maps .there (.there c0) through unpack then lift.lift
        simp [Subst.comp, Subst.unpack]
        -- Generalize before simplifying
        simp only [Subst.from_TypeEnv, TypeEnv.extend_var, TypeEnv.extend_cvar,
          TypeEnv.lookup_cvar, TypeEnv.lookup, Subst.lift]
        -- Now the goal has ρ.lookup_cvar c0 expanded to match expression
        -- Let's generalize this ground capture set
        generalize (match ρ.lookup c0 with | TypeInfo.cvar cs => cs) = ground_cs
        -- Goal: double rename + subst on ground_cs equals ground_cs
        induction ground_cs with
        | empty => rfl  -- .empty.rename.rename.subst = .empty
        | union cs1 cs2 ih1 ih2 =>
          -- .union case: distribute rename/subst over both sides
          simp only [CaptureSet.proj, CaptureSet.rename, CaptureSet.subst, ih1, ih2]
        | var v ck =>
          cases v with
          | bound bv => cases bv  -- Impossible: no bound vars in {}
          | free n =>
            -- .var (.free n).rename.rename.subst = .var (.free n)
            rfl
        | cvar cv ck => cases cv  -- Impossible: no capture vars in {}

/--
If a DenotCtx is typed with EnvTyping, then the substitution obtained from it
via `Subst.from_DenotCtx` is well-formed in the heap.

This is a key lemma connecting the semantic typing judgment to syntactic well-formedness.
Since `EnvTyping` ensures each variable location in the environment exists in memory,
the substitution that maps variables to these locations must be well-formed.
-/
theorem from_DenotCtx_wf_in_heap
  {Γ : Ctx s} {ctx : DenotCtx s} {m : Memory}
  (htyping : EnvTyping Γ ctx m) :
  (Subst.from_DenotCtx ctx).WfInHeap m.heap := by
  induction Γ with
  | empty =>
    -- Base case: empty context has no variables
    cases ctx with
    | mk env handlers =>
      cases env with
      | empty =>
        constructor
        · intro x; cases x
        · intro X; cases X
        · intro C K; cases C
  | push Γ' k ih =>
    -- Inductive case: handle each kind of binding
    cases ctx with
    | mk env handlers =>
      cases env with
      | extend ρ' info =>
        cases k with
        | var T =>
          -- Variable binding: extract well-formedness from typing
          cases info with
          | var n =>
            unfold EnvTyping at htyping
            have ⟨htype, htyping'⟩ := htyping
            -- htype : ⟦T⟧_[⟨ρ'⟩] m (.var (.free n))
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
                    simp [Subst.from_DenotCtx, Subst.from_TypeEnv,
                          TypeEnv.lookup_var, TypeEnv.lookup]
                    exact hwf_var
                  | there x' =>
                    simp [Subst.from_DenotCtx, Subst.from_TypeEnv,
                          TypeEnv.lookup_var, TypeEnv.lookup]
                    exact ih_wf.wf_var x'
                · intro X
                  cases X with
                  | there X' =>
                    simp [Subst.from_DenotCtx, Subst.from_TypeEnv]
                    exact ih_wf.wf_tvar X'
                · intro C_var K
                  cases C_var with
                  | there C' =>
                    simp [Subst.from_DenotCtx, Subst.from_TypeEnv]
                    exact ih_wf.wf_cvar C' K
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
                simp [Subst.from_DenotCtx, Subst.from_TypeEnv, TypeEnv.lookup_var, TypeEnv.lookup]
                exact ih_wf.wf_var x'
            · intro X
              cases X with
              | here =>
                simp [Subst.from_DenotCtx, Subst.from_TypeEnv]
                apply Ty.WfInHeap.wf_top
              | there X' =>
                simp [Subst.from_DenotCtx, Subst.from_TypeEnv]
                exact ih_wf.wf_tvar X'
            · intro C_var K
              cases C_var with
              | there C' =>
                simp [Subst.from_DenotCtx, Subst.from_TypeEnv]
                exact ih_wf.wf_cvar C' K
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
                simp [Subst.from_DenotCtx, Subst.from_TypeEnv, TypeEnv.lookup_var, TypeEnv.lookup]
                exact ih_wf.wf_var x'
            · intro X
              cases X with
              | there X' =>
                simp [Subst.from_DenotCtx, Subst.from_TypeEnv]
                exact ih_wf.wf_tvar X'
            · intro C_var K
              cases C_var with
              | here =>
                simp [Subst.from_DenotCtx, Subst.from_TypeEnv, TypeEnv.lookup_cvar, TypeEnv.lookup]
                exact CaptureSet.wf_proj hwf
              | there C' =>
                simp [Subst.from_DenotCtx, Subst.from_TypeEnv]
                exact ih_wf.wf_cvar C' K

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

structure DenotCtx.IsMonotonic (ctx : DenotCtx s) : Prop where
  tvar : ∀ (X : BVar s .tvar),
    (ctx.lookup_tvar X).is_monotonic

  handlers : handlers_are_monotonic ctx.handlers

def DenotCtx.is_transparent (ctx : DenotCtx s) : Prop :=
  ∀ (X : BVar s .tvar),
    (ctx.lookup_tvar X).is_transparent

def DenotCtx.is_bool_independent (ctx : DenotCtx s) : Prop :=
  ∀ (X : BVar s .tvar),
    (ctx.lookup_tvar X).is_bool_independent

def DenotCtx.is_reachability_safe (ctx : DenotCtx s) : Prop :=
  ∀ (X : BVar s .tvar),
    (ctx.lookup_tvar X).is_reachability_safe

def DenotCtx.is_reachability_monotonic (ctx : DenotCtx s) : Prop :=
  ∀ (X : BVar s .tvar),
    (ctx.lookup_tvar X).is_reachability_monotonic

def DenotCtx.is_implying_wf (ctx : DenotCtx s) : Prop :=
  ∀ (X : BVar s .tvar),
    (ctx.lookup_tvar X).implies_wf

def DenotCtx.is_tight (ctx : DenotCtx s) : Prop :=
  ∀ (X : BVar s .tvar),
    (ctx.lookup_tvar X).is_tight

theorem typed_env_is_monotonic
  (ht : EnvTyping Γ ctx mem) :
  ctx.IsMonotonic := by
  induction Γ with
  | empty =>
    cases ctx with
    | mk env handlers =>
      cases env with
      | empty =>
        constructor
        · intro x; cases x
        · exact ht
  | push Γ k ih =>
    cases ctx with
    | mk env handlers =>
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
                simp [DenotCtx.lookup_tvar, TypeEnv.lookup_tvar, TypeEnv.lookup]
                exact ih_result.tvar x
            · exact ih_result.handlers
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
                simp [DenotCtx.lookup_tvar, TypeEnv.lookup_tvar, TypeEnv.lookup]
                -- hproper says d.is_proper
                -- We need d.is_monotonic
                intro C
                exact (hproper.2.2.2.2 C).1
              | there x =>
                simp [DenotCtx.lookup_tvar, TypeEnv.lookup_tvar, TypeEnv.lookup]
                exact ih_result.tvar x
            · exact ih_result.handlers
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
                simp [DenotCtx.lookup_tvar, TypeEnv.lookup_tvar, TypeEnv.lookup]
                exact ih_result.tvar x
            · exact ih_result.handlers

theorem typed_env_is_transparent
  (ht : EnvTyping Γ ctx mem) :
  ctx.is_transparent := by
  induction Γ with
  | empty =>
    cases ctx with
    | mk env handlers =>
      cases env with
      | empty =>
        simp [DenotCtx.is_transparent, DenotCtx.lookup_tvar]
        intro x
        cases x
  | push Γ k ih =>
    cases ctx with
    | mk env handlers =>
      cases env with
      | extend env' info =>
        cases k with
        | var T =>
          cases info with
          | var n =>
            simp [EnvTyping] at ht
            have ⟨_, ht'⟩ := ht
            have ih_result := ih ht'
            simp [DenotCtx.is_transparent, DenotCtx.lookup_tvar] at ih_result ⊢
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
            simp [DenotCtx.is_transparent, DenotCtx.lookup_tvar] at ih_result ⊢
            intro x
            cases x with
            | here =>
              simp [TypeEnv.lookup_tvar, TypeEnv.lookup]
              -- hproper says d.is_proper
              -- We need d.is_transparent
              intro C
              exact (hproper.2.2.2.2 C).2.1
            | there x =>
              simp [TypeEnv.lookup_tvar, TypeEnv.lookup]
              exact ih_result x
        | cvar B =>
          cases info with
          | cvar cs =>
            simp [EnvTyping] at ht
            have ⟨hwf, hwf_bound, hsub, ht'⟩ := ht
            have ih_result := ih ht'
            simp [DenotCtx.is_transparent, DenotCtx.lookup_tvar] at ih_result ⊢
            intro x
            cases x with
            | there x =>
              simp [TypeEnv.lookup_tvar, TypeEnv.lookup]
              exact ih_result x

theorem typed_env_is_bool_independent
  (ht : EnvTyping Γ ctx mem) :
  ctx.is_bool_independent := by
  induction Γ with
  | empty =>
    cases ctx with
    | mk env handlers =>
      cases env with
      | empty =>
        simp [DenotCtx.is_bool_independent, DenotCtx.lookup_tvar]
        intro x
        cases x
  | push Γ k ih =>
    cases ctx with
    | mk env handlers =>
      cases env with
      | extend env' info =>
        cases k with
        | var T =>
          cases info with
          | var n =>
            simp [EnvTyping] at ht
            have ⟨_, ht'⟩ := ht
            have ih_result := ih ht'
            simp [DenotCtx.is_bool_independent, DenotCtx.lookup_tvar] at ih_result ⊢
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
            simp [DenotCtx.is_bool_independent, DenotCtx.lookup_tvar] at ih_result ⊢
            intro x
            cases x with
            | here =>
              simp [TypeEnv.lookup_tvar, TypeEnv.lookup]
              -- hproper says d.is_proper
              -- We need d.is_bool_independent
              intro C
              exact (hproper.2.2.2.2 C).2.2
            | there x =>
              simp [TypeEnv.lookup_tvar, TypeEnv.lookup]
              exact ih_result x
        | cvar B =>
          cases info with
          | cvar cs =>
            simp [EnvTyping] at ht
            have ⟨hwf, hwf_bound, hsub, ht'⟩ := ht
            have ih_result := ih ht'
            simp [DenotCtx.is_bool_independent, DenotCtx.lookup_tvar] at ih_result ⊢
            intro x
            cases x with
            | there x =>
              simp [TypeEnv.lookup_tvar, TypeEnv.lookup]
              exact ih_result x

theorem typed_env_is_reachability_safe
  (ht : EnvTyping Γ ctx mem) :
  ctx.is_reachability_safe := by
  induction Γ with
  | empty =>
    cases ctx with
    | mk env handlers =>
      cases env with
      | empty =>
        simp [DenotCtx.is_reachability_safe, DenotCtx.lookup_tvar]
        intro x
        cases x
  | push Γ k ih =>
    cases ctx with
    | mk env handlers =>
      cases env with
      | extend env' info =>
        cases k with
        | var T =>
          cases info with
          | var n =>
            simp [EnvTyping] at ht
            have ⟨_, ht'⟩ := ht
            have ih_result := ih ht'
            simp [DenotCtx.is_reachability_safe, DenotCtx.lookup_tvar] at ih_result ⊢
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
            simp [DenotCtx.is_reachability_safe, DenotCtx.lookup_tvar] at ih_result ⊢
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
            simp [DenotCtx.is_reachability_safe, DenotCtx.lookup_tvar] at ih_result ⊢
            intro x
            cases x with
            | there x =>
              simp [TypeEnv.lookup_tvar, TypeEnv.lookup]
              exact ih_result x

theorem typed_env_is_reachability_monotonic
  (ht : EnvTyping Γ ctx mem) :
  ctx.is_reachability_monotonic := by
  induction Γ with
  | empty =>
    cases ctx with
    | mk env handlers =>
      cases env with
      | empty =>
        simp [DenotCtx.is_reachability_monotonic, DenotCtx.lookup_tvar]
        intro x
        cases x
  | push Γ k ih =>
    cases ctx with
    | mk env handlers =>
      cases env with
      | extend env' info =>
        cases k with
        | var T =>
          cases info with
          | var n =>
            simp [EnvTyping] at ht
            have ⟨_, ht'⟩ := ht
            have ih_result := ih ht'
            simp [DenotCtx.is_reachability_monotonic, DenotCtx.lookup_tvar] at ih_result ⊢
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
            simp [DenotCtx.is_reachability_monotonic, DenotCtx.lookup_tvar] at ih_result ⊢
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
            simp [DenotCtx.is_reachability_monotonic, DenotCtx.lookup_tvar] at ih_result ⊢
            intro x
            cases x with
            | there x =>
              simp [TypeEnv.lookup_tvar, TypeEnv.lookup]
              exact ih_result x

theorem typed_env_is_implying_wf
  (ht : EnvTyping Γ ctx mem) :
  ctx.is_implying_wf := by
  induction Γ with
  | empty =>
    cases ctx with
    | mk env handlers =>
      cases env with
      | empty =>
        simp [DenotCtx.is_implying_wf, DenotCtx.lookup_tvar]
        intro x
        cases x
  | push Γ k ih =>
    cases ctx with
    | mk env handlers =>
      cases env with
      | extend env' info =>
        cases k with
        | var T =>
          cases info with
          | var n =>
            simp [EnvTyping] at ht
            have ⟨_, ht'⟩ := ht
            have ih_result := ih ht'
            simp [DenotCtx.is_implying_wf, DenotCtx.lookup_tvar] at ih_result ⊢
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
            simp [DenotCtx.is_implying_wf, DenotCtx.lookup_tvar] at ih_result ⊢
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
            simp [DenotCtx.is_implying_wf, DenotCtx.lookup_tvar] at ih_result ⊢
            intro x
            cases x with
            | there x =>
              simp [TypeEnv.lookup_tvar, TypeEnv.lookup]
              exact ih_result x

theorem typed_env_is_tight
  (ht : EnvTyping Γ ctx mem) :
  ctx.is_tight := by
  induction Γ with
  | empty =>
    cases ctx with
    | mk env handlers =>
      cases env with
      | empty =>
        intro X
        cases X
  | push Γ k ih =>
    cases ctx with
    | mk env handlers =>
      cases env with
      | extend env' info =>
        cases k with
        | var T =>
          cases info with
          | var n =>
            simp [EnvTyping] at ht
            have ⟨_, ht'⟩ := ht
            have ih_result := ih ht'
            intro X
            cases X with
            | there X' =>
              simp [DenotCtx.lookup_tvar, TypeEnv.lookup_tvar, TypeEnv.lookup]
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
              simp [DenotCtx.lookup_tvar, TypeEnv.lookup_tvar, TypeEnv.lookup]
              -- hproper says d.is_proper
              -- We need d.is_tight
              exact hproper.2.2.2.1
            | there X' =>
              simp [DenotCtx.lookup_tvar, TypeEnv.lookup_tvar, TypeEnv.lookup]
              exact ih_result X'
        | cvar B =>
          cases info with
          | cvar cs =>
            simp [EnvTyping] at ht
            have ⟨_, _, _, ht'⟩ := ht
            have ih_result := ih ht'
            intro X
            cases X with
            | there X' =>
              simp [DenotCtx.lookup_tvar, TypeEnv.lookup_tvar, TypeEnv.lookup]
              exact ih_result X'

theorem shape_val_denot_is_transparent {ctx : DenotCtx s}
  (henv : DenotCtx.is_transparent ctx)
  (T : Ty .shape s) :
  (Ty.shape_val_denot ctx T).is_transparent := by
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
    simp [Ty.shape_val_denot, DenotCtx.lookup_tvar]
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
  | label T =>
    intro C m x v hx ht
    simp only [Ty.shape_val_denot] at ht ⊢
    obtain ⟨l, K, _, heq, _⟩ := ht
    -- v.unwrap = .var (.free l), but v.isVal says it's a simple value
    -- Variables are not simple values, so this is a contradiction
    have hval := v.isVal
    rw [heq] at hval
    cases hval

theorem shape_val_denot_is_bool_independent {ctx : DenotCtx s}
  (henv : ctx.is_bool_independent)
  (T : Ty .shape s) :
  ∀ C, (Ty.shape_val_denot ctx T C).is_bool_independent := by
  intro C m
  cases T with
  | top =>
    simp [Ty.shape_val_denot, resolve_reachability]
    intro _
    constructor <;> intro
    · apply Exp.WfInHeap.wf_bfalse
    · apply Exp.WfInHeap.wf_btrue
  | tvar X =>
    simp [Ty.shape_val_denot, DenotCtx.lookup_tvar]
    exact henv X C
  | unit =>
    simp [Ty.shape_val_denot, resolve]
  | cap =>
    simp [Ty.shape_val_denot]
  | bool =>
    simp [Ty.shape_val_denot, resolve]
  | cell =>
    simp [Ty.shape_val_denot]
  | arrow T1 T2 =>
    simp [Ty.shape_val_denot, resolve]
  | poly T1 T2 =>
    simp [Ty.shape_val_denot, resolve]
  | cpoly B T =>
    simp [Ty.shape_val_denot, resolve]
  | label T =>
    simp [Ty.shape_val_denot]

theorem capt_val_denot_is_transparent {ctx : DenotCtx s}
  (henv : DenotCtx.is_transparent ctx)
  (T : Ty .capt s) :
  (Ty.capt_val_denot ctx T).is_transparent := by
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
    · -- Prove: shape_val_denot ctx S (C.denot ctx m) m (.var (.free x))
      exact shape_val_denot_is_transparent henv S (C.denot ctx m) hx hshape

theorem exi_val_denot_is_transparent {ctx : DenotCtx s}
  (henv : DenotCtx.is_transparent ctx)
  (T : Ty .exi s) :
  (Ty.exi_val_denot ctx T).is_transparent := by
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
        CS.WfInHeap m.heap ∧ Ty.capt_val_denot (ctx.extend_cvar CS) T m (.var x)
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
        -- ht now says: Ty.capt_val_denot (ctx.extend_cvar CS') T m (var y')
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
      -- Free variable: use reachability_of_loc_proj_monotonic
      unfold CaptureSet.ground_denot
      simp at hwf
      cases hwf with
      | wf_var_free hex =>
        -- Goal: (reachability_of_loc m1.heap x).proj m1.heap K
        --     = (reachability_of_loc m2.heap x).proj m2.heap K
        -- First, rewrite using reachability_of_loc_monotonic
        rw [reachability_of_loc_monotonic hsub x hex]
        -- Now: (reachability_of_loc m1.heap x).proj m1.heap K
        --    = (reachability_of_loc m1.heap x).proj m2.heap K
        -- Use reachability_of_loc_proj_monotonic
        exact (reachability_of_loc_proj_monotonic m1.wf hsub hex).symm
  | cvar c => cases c  -- No capture variables in empty signature

theorem capture_set_denot_is_monotonic {C : CaptureSet s} :
  (C.denot ρ).is_monotonic_for (C.subst (Subst.from_DenotCtx ρ)) := by
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
      simp only [CaptureSet.subst, Subst.from_DenotCtx, Subst.from_TypeEnv,
                 Var.subst, CaptureSet.ground_denot] at hwf ⊢
      cases hwf with
      | wf_var_free hex =>
        -- hex : m1.heap (ρ.env.lookup_var x) = some _
        rw [reachability_of_loc_monotonic hsub (ρ.env.lookup_var x) hex]
        exact (reachability_of_loc_proj_monotonic m1.wf hsub hex).symm
    | free x =>
      -- Free variable: stays as free variable
      unfold CaptureSet.denot
      simp only [CaptureSet.subst, Var.subst, CaptureSet.ground_denot] at hwf ⊢
      cases hwf with
      | wf_var_free hex =>
        -- hex : m1.heap x = some _
        rw [reachability_of_loc_monotonic hsub x hex]
        exact (reachability_of_loc_proj_monotonic m1.wf hsub hex).symm
  | cvar c =>
    -- Capture variable: after substitution becomes ground capture set
    unfold CaptureSet.denot
    simp [CaptureSet.subst]
    -- Need: (ρ.lookup_cvar c).ground_denot m1 = (ρ.lookup_cvar c).ground_denot m2
    -- This follows from ground_denot_is_monotonic
    exact ground_denot_is_monotonic hwf hsub

theorem capture_bound_denot_is_monotonic {B : CaptureBound s}
  (hwf : (B.subst (Subst.from_DenotCtx ρ)).WfInHeap m1.heap)
  (hsub : m2.subsumes m1) :
  B.denot ρ m1 = B.denot ρ m2 := by
  cases B with
  | unbound =>
    -- Unbound denotes CapabilitySet.any at all memories
    unfold CaptureBound.denot
    rfl
  | bound cs =>
    -- Bounded case: use capture_set_denot_is_monotonic
    simp only [CaptureBound.denot]
    -- Extract well-formedness of the capture set from hwf
    simp [CaptureBound.subst] at hwf
    cases hwf with
    | wf_bound hwf_cs =>
      rw [capture_set_denot_is_monotonic hwf_cs hsub]

mutual

def shape_val_denot_is_monotonic {ctx : DenotCtx s}
  (henv : ctx.IsMonotonic)
  (T : Ty .shape s) :
  (Ty.shape_val_denot ctx T).is_monotonic := by
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
      have heq := resolve_reachability_monotonic m1.wf hmem e ht.1
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
    | boundary _ _ _ => simp [resolve] at ht
    | throw _ _ => simp [resolve] at ht
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
      | label => simp [Cell.subsumes] at hsub_c
      | mcell b' =>
        -- Cell.subsumes says mcell-to-mcell is True
        -- The boolean value b' might differ from b0, which is fine
        refine ⟨l, b', heq, ?_, hmem_l⟩
        simp [Memory.lookup]
        exact hc'
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
        | boundary _ _ _ => cases hr
        | throw _ _ => cases hr
      · constructor
        · exact CaptureSet.wf_monotonic hmem hwf_cs
        · constructor
          · -- Prove: expand_captures m2.heap cs ⊆ C
            have heq := expand_captures_monotonic m1.wf hmem cs hwf_cs
            rw [heq]
            exact hR0_sub
          · intro arg m' hs' harg
            have hs0 := Memory.subsumes_trans hs' hmem
            -- Use convert with expand_captures monotonicity
            have heq' := expand_captures_monotonic m1.wf hmem cs hwf_cs
            convert hfun arg m' hs0 harg using 2
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
        | boundary _ _ _ => cases hr
        | throw _ _ => cases hr
      · constructor
        · exact CaptureSet.wf_monotonic hmem hwf_cs
        · constructor
          · -- Prove: expand_captures m2.heap cs ⊆ C
            have heq := expand_captures_monotonic m1.wf hmem cs hwf_cs
            rw [heq]
            exact hR0_sub
          · intro m' denot msub hdenot_proper himply
            have henv' : (ctx.extend_tvar denot).IsMonotonic := by
              constructor
              · intro X
                cases X with
                | here =>
                  simp [DenotCtx.lookup_tvar, DenotCtx.extend_tvar,
                        TypeEnv.extend_tvar, TypeEnv.lookup_tvar, TypeEnv.lookup]
                  intro C
                  exact (hdenot_proper.2.2.2.2 C).1
                | there X' =>
                  simp [DenotCtx.lookup_tvar, DenotCtx.extend_tvar,
                        TypeEnv.extend_tvar, TypeEnv.lookup_tvar, TypeEnv.lookup]
                  exact henv.tvar X'
              · exact henv.handlers
            -- Use convert with expand_captures monotonicity
            have heq' := expand_captures_monotonic m1.wf hmem cs hwf_cs
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
        | boundary _ _ _ => cases hr
        | throw _ _ => cases hr
      · constructor
        · exact CaptureSet.wf_monotonic hmem hwf_cs
        · constructor
          · -- Prove: expand_captures m2.heap cs ⊆ C
            have heq := expand_captures_monotonic m1.wf hmem cs hwf_cs
            rw [heq]
            exact hR0_sub
          · intro m' CS hwf msub hA0
            -- Use convert with expand_captures monotonicity
            have heq' := expand_captures_monotonic m1.wf hmem cs hwf_cs
            convert hfun m' CS hwf (Memory.subsumes_trans msub hmem) hA0 using 2
  | label T =>
    intro m1 m2 e hmem ht
    simp only [Ty.shape_val_denot] at ht ⊢
    obtain ⟨l, K, D0, heq, hcap, happly, himply, hmemin⟩ := ht
    refine ⟨l, K, D0, heq, ?_, happly, Denot.imply_after_subsumes himply hmem, hmemin⟩
    have hsub : m2.heap.subsumes m1.heap := hmem
    obtain ⟨c', hc', hsub_c⟩ := hsub l (Cell.capability (.label K)) hcap
    simp [Cell.subsumes] at hsub_c
    subst hsub_c
    simp [Memory.lookup]
    exact hc'

def capt_val_denot_is_monotonic {ctx : DenotCtx s}
  (henv : ctx.IsMonotonic)
  (T : Ty .capt s) :
  (Ty.capt_val_denot ctx T).is_monotonic := by
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
    · -- Prove: shape_val_denot ctx S (C.denot ctx m2) m2 e
      have h := capture_set_denot_is_monotonic hwf_C hmem
      rw [<-h]
      exact shape_val_denot_is_monotonic henv S (C.denot ctx m1) hmem hshape

def exi_val_denot_is_monotonic {ctx : DenotCtx s}
  (henv : ctx.IsMonotonic)
  (T : Ty .exi s) :
  (Ty.exi_val_denot ctx T).is_monotonic := by
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
        -- ht now says: CS.WfInHeap m1.heap ∧ Ty.capt_val_denot (ctx.extend_cvar CS) T m1 (var y)
        obtain ⟨hwf_CS_m1, ht_body⟩ := ht
        -- Use resolve_monotonic to show resolve m2.heap e = some (pack CS y)
        have hresolve2 : resolve m2.heap e = some (Exp.pack CS y) := by
          apply resolve_monotonic hmem hresolve1
        simp [hresolve2]
        -- Now need to show:
        -- CS.WfInHeap m2.heap ∧ Ty.capt_val_denot (ctx.extend_cvar CS) T m2 (var y)
        constructor
        · -- Well-formedness is monotonic
          exact CaptureSet.wf_monotonic hmem hwf_CS_m1
        · -- Use monotonicity of capt_val_denot
          have henv' : (ctx.extend_cvar CS).IsMonotonic := by
            constructor
            · intro X
              cases X with
              | there X' =>
                simp [DenotCtx.lookup_tvar, DenotCtx.extend_cvar,
                      TypeEnv.extend_cvar, TypeEnv.lookup_tvar, TypeEnv.lookup]
                exact henv.tvar X'
            · exact henv.handlers
          exact capt_val_denot_is_monotonic henv' T hmem ht_body
      all_goals {
        -- resolve returned non-pack, so ht is False
        simp [hresolve1] at ht
      }

def capt_val_denot_is_bool_independent {ctx : DenotCtx s}
  (henv : ctx.is_bool_independent)
  (T : Ty .capt s) :
  (Ty.capt_val_denot ctx T).is_bool_independent := by
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
          · exact (shape_val_denot_is_bool_independent henv S (C.denot ctx m)).mp hshape
    · intro ⟨hsimple, hwf, hwf_C, hshape⟩
      constructor
      · apply Exp.IsSimpleAns.is_simple_val
        apply Exp.IsSimpleVal.btrue
      · constructor
        · apply Exp.WfInHeap.wf_btrue
        · constructor
          · exact hwf_C
          · exact (shape_val_denot_is_bool_independent henv S (C.denot ctx m)).mpr hshape

def exi_val_denot_is_bool_independent {ctx : DenotCtx s}
  (henv : ctx.is_bool_independent)
  (T : Ty .exi s) :
  (Ty.exi_val_denot ctx T).is_bool_independent := by
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

def exi_exp_denot_is_monotonic {ctx : DenotCtx s}
  (henv_mono : ctx.IsMonotonic)
  (henv_bool : ctx.is_bool_independent)
  (T : Ty .exi s) :
  ∀ {C : CapabilitySet} {m1 m2 : Memory} {e : Exp {}},
    Exp.WfInHeap e m1.heap ->
    m2.subsumes m1 ->
    (Ty.exi_exp_denot ctx T) C m1 e ->
    (Ty.exi_exp_denot ctx T) C m2 e := by
  intro C m1 m2 e hwf hmem ht
  simp [Ty.exi_exp_denot] at ht ⊢
  apply eval_monotonic
  · apply Denot.as_mpost_is_monotonic
    apply Denot.Or.is_monotonic
    · exact exi_val_denot_is_monotonic henv_mono T
    · exact denot_of_handlers_is_monotonic ctx.handlers henv_mono.handlers
  · apply Denot.as_mpost_is_bool_independent
    apply Denot.Or.is_bool_independent
    · exact exi_val_denot_is_bool_independent henv_bool T
    · exact denot_of_handlers_is_bool_independent ctx.handlers
  · exact hmem
  · exact hwf
  · exact ht

end

theorem env_typing_monotonic
  (ht : EnvTyping Γ ctx mem1)
  (hmem : mem2.subsumes mem1) :
  EnvTyping Γ ctx mem2 := by
  induction Γ with
  | empty =>
    cases ctx with
    | mk env handlers =>
      cases env with
      | empty => trivial
  | push Γ k ih =>
    cases ctx with
    | mk env handlers =>
      cases env with
      | extend env' info =>
        cases k with
        | var T =>
          cases info with
          | var n =>
            -- Unfold EnvTyping to get the conjunction
            simp only [EnvTyping] at ht ⊢
            have ⟨hval, ht'⟩ := ht
            constructor
            · -- Prove: ⟦T⟧_[⟨env'⟩] mem2 (.var (.free n))
              have hctx := typed_env_is_monotonic ht'
              exact capt_val_denot_is_monotonic hctx T hmem hval
            · -- Prove: EnvTyping Γ ⟨env'⟩ mem2
              exact ih ht'
        | tvar S =>
          cases info with
          | tvar d =>
            simp only [EnvTyping] at ht ⊢
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
            simp only [EnvTyping] at ht ⊢
            have ⟨hwf, hwf_bound, hsub, ht'⟩ := ht
            constructor
            · -- Prove: cs.WfInHeap mem2.heap
              exact CaptureSet.wf_monotonic hmem hwf
            · constructor
              · -- Prove: (B.subst (Subst.from_DenotCtx ⟨env'⟩)).WfInHeap mem2.heap
                exact CaptureBound.wf_monotonic hmem hwf_bound
              · constructor
                · -- Need: BoundedBy mem2.heap (cs.ground_denot mem2) (⟦B⟧_[⟨env'⟩] mem2)
                  -- Have: BoundedBy mem1.heap (cs.ground_denot mem1) (⟦B⟧_[⟨env'⟩] mem1)
                  let ctx' : DenotCtx _ := ⟨env', handlers⟩
                  -- Get cs.ground_denot mem1 = cs.ground_denot mem2
                  have h_denot_eq := ground_denot_is_monotonic hwf hmem
                  -- Get ⟦B⟧_[ctx'] mem1 = ⟦B⟧_[ctx'] mem2
                  have h_bound_eq : ⟦B⟧_[ctx'] mem1 = ⟦B⟧_[ctx'] mem2 :=
                    capture_bound_denot_is_monotonic hwf_bound hmem
                  -- Combine the equalities and use monotonicity
                  rw [<-h_denot_eq, <-h_bound_eq]
                  have hwf_denot := CaptureSet.ground_denot_wf hwf
                  exact hsub.monotonic hmem hwf_denot
                · exact ih ht'

/-- Semantic subcapturing. -/
def SemSubcapt (Γ : Ctx s) (C1 C2 : CaptureSet s) : Prop :=
  ∀ env m,
    EnvTyping Γ env m ->
    C1.denot env m ⊆ C2.denot env m

def SemSubtyp {k : TySort} (Γ : Ctx s) (T1 T2 : Ty k s) : Prop :=
  match k with
  | .shape =>
    ∀ ctx H, EnvTyping Γ ctx H ->
      (Ty.shape_val_denot ctx T1).ImplyAfter H (Ty.shape_val_denot ctx T2)
  | .capt =>
    ∀ ctx H, EnvTyping Γ ctx H ->
      (Ty.capt_val_denot ctx T1).ImplyAfter H (Ty.capt_val_denot ctx T2)
  | .exi =>
    ∀ ctx H, EnvTyping Γ ctx H ->
      (Ty.exi_val_denot ctx T1).ImplyAfter H (Ty.exi_val_denot ctx T2)

theorem shape_val_denot_is_reachability_safe {ctx : DenotCtx s}
  (hts : ctx.is_reachability_safe)
  (T : Ty .shape s) :
  (Ty.shape_val_denot ctx T).is_reachability_safe := by
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
    -- Goal: {l} ⊆ R, which follows from l ∈ R
    exact CapabilitySet.mem_imp_singleton_subset hmem
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
    -- Goal: {label} ⊆ R, which follows from label ∈ R
    exact CapabilitySet.mem_imp_singleton_subset hmem
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
  | label T =>
    simp only [Ty.shape_val_denot] at hdenot
    obtain ⟨l, K, _, heq, hlookup, _, _, hmem⟩ := hdenot
    -- e is a variable pointing to a label capability
    rw [heq]
    simp [resolve_reachability]
    -- reachability_of_loc m.heap l = {l} for label capabilities
    have hlookup' : m.heap l = some (Cell.capability (.label K)) := by
      simp [Memory.lookup] at hlookup
      exact hlookup
    simp [reachability_of_loc, hlookup']
    -- Goal: {l} ⊆ R, which follows from l ∈ R
    exact CapabilitySet.mem_imp_singleton_subset hmem

theorem shape_val_denot_is_reachability_monotonic {ctx : DenotCtx s}
  (hts : ctx.is_reachability_monotonic)
  (T : Ty .shape s) :
  (Ty.shape_val_denot ctx T).is_reachability_monotonic := by
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
    exact ⟨heq, hlookup, CapabilitySet.subset_preserves_mem hsub hmem⟩
  | unit =>
    simp [Ty.shape_val_denot] at hdenot ⊢
    exact hdenot
  | cap =>
    simp [Ty.shape_val_denot] at hdenot ⊢
    have ⟨hwf_e, label, heq, hcap, hmem⟩ := hdenot
    constructor
    · exact hwf_e
    · exists label, heq, hcap
      exact CapabilitySet.subset_preserves_mem hsub hmem
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
  | label T =>
    simp only [Ty.shape_val_denot] at hdenot ⊢
    obtain ⟨l, K, D0, heq, hlookup, happly, himply, hmem⟩ := hdenot
    exact ⟨l, K, D0, heq, hlookup, happly, himply,
      CapabilitySet.subset_preserves_mem hsub hmem⟩

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

theorem shape_val_denot_implies_wf {ctx : DenotCtx s}
  (hts : ctx.is_implying_wf)
  (T : Ty .shape s) :
  (Ty.shape_val_denot ctx T).implies_wf := by
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
  | label T =>
    simp only [Ty.shape_val_denot] at hdenot
    obtain ⟨l, K, _, heq, hlookup, _⟩ := hdenot
    rw [heq]
    apply Exp.WfInHeap.wf_var
    apply Var.WfInHeap.wf_free
    · simp [Memory.lookup] at hlookup
      exact hlookup

theorem shape_val_denot_is_tight {ctx : DenotCtx s}
  (hts : ctx.is_tight) :
  (Ty.shape_val_denot ctx T).is_tight := by
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
        exact CapabilitySet.mem.here
  | cap =>
    simp [Ty.shape_val_denot, reachability_of_loc, Memory.lookup] at ht ⊢
    obtain ⟨hwf, hmem, hin⟩ := ht
    constructor
    · exact hwf
    · constructor
      · exact hmem
      · simp [hmem]
        exact CapabilitySet.mem.here
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
  | label T =>
    simp only [Ty.shape_val_denot, reachability_of_loc, Memory.lookup] at ht ⊢
    obtain ⟨l, K, D0, heq, hlookup, happly, himply, hmem⟩ := ht
    -- heq : .var (.free fx) = .var (.free l), so fx = l
    cases heq
    -- Now fx is replaced by l in all hypotheses
    refine ⟨fx, K, D0, rfl, hlookup, happly, himply, ?_⟩
    simp [hlookup]
    exact CapabilitySet.mem.here

theorem shape_val_denot_is_proper {ctx : DenotCtx s} {S : Ty .shape s}
  (hts : EnvTyping Γ ctx m) :
  (Ty.shape_val_denot ctx S).is_proper := by
  constructor
  · -- Prove: (Ty.shape_val_denot ctx S).is_reachability_safe
    exact shape_val_denot_is_reachability_safe (typed_env_is_reachability_safe hts) S
  · constructor
    · -- Prove: (Ty.shape_val_denot ctx S).is_reachability_monotonic
      exact shape_val_denot_is_reachability_monotonic
        (typed_env_is_reachability_monotonic hts) S
    · constructor
      · -- Prove: (Ty.shape_val_denot ctx S).implies_wf
        exact shape_val_denot_implies_wf (typed_env_is_implying_wf hts) S
      · constructor
        · -- Prove: (Ty.shape_val_denot ctx S).is_tight
          exact shape_val_denot_is_tight (typed_env_is_tight hts)
        · -- Prove: ∀ C, ((Ty.shape_val_denot ctx S) C).is_proper
          intro C
          constructor
          · exact shape_val_denot_is_monotonic (typed_env_is_monotonic hts) S C
          · constructor
            · exact shape_val_denot_is_transparent (typed_env_is_transparent hts) S C
            · exact shape_val_denot_is_bool_independent (typed_env_is_bool_independent hts) S C

theorem exi_denot_implyafter_lift
  (himp : (Ty.exi_val_denot ctx T1).ImplyAfter H (Ty.exi_val_denot ctx T2)) :
  (Ty.exi_exp_denot ctx T1).ImplyAfter H (Ty.exi_exp_denot ctx T2) := by
  intro C m' hsub e heval
  simp [Ty.exi_exp_denot] at heval ⊢
  apply eval_post_monotonic_general _ heval
  have himp_or := himp.or_right (denot_of_handlers ctx.handlers)
  have himp' := Denot.imply_after_to_m_entails_after himp_or
  exact Mpost.entails_after_subsumes himp' hsub

/-- Semantic HasKind: the denotation of C has kind K in the heap. -/
def SemHasKind (Γ : Ctx s) (C : CaptureSet s) (K : CapKind) : Prop :=
  ∀ env m,
    EnvTyping Γ env m ->
    CapabilitySet.HasKind m.heap (C.denot env m) K

end CaplessK
