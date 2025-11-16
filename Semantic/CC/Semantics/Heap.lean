import Semantic.CC.Syntax
import Semantic.CC.Substitution
import Mathlib.Data.Finset.Basic

namespace CC

/-- A set of capability labels, representing an "authority":
  they are the set of capabilities a program at most uses. -/
inductive CapabilitySet : Type where
| empty : CapabilitySet
| cap : Nat -> CapabilitySet
| union : CapabilitySet -> CapabilitySet -> CapabilitySet

namespace CapabilitySet

inductive mem : Nat -> CapabilitySet -> Prop where
| here : CapabilitySet.mem l (CapabilitySet.cap l)
| left {l C1 C2} :
  CapabilitySet.mem l C1 ->
  CapabilitySet.mem l (CapabilitySet.union C1 C2)
| right {l C1 C2} :
  CapabilitySet.mem l C2 ->
  CapabilitySet.mem l (CapabilitySet.union C1 C2)

@[simp]
instance instMembership : Membership Nat CapabilitySet :=
  ⟨fun C l => CapabilitySet.mem l C⟩

@[simp]
instance instEmptyCollection : EmptyCollection CapabilitySet :=
  ⟨CapabilitySet.empty⟩

@[simp]
instance instUnion : Union CapabilitySet :=
  ⟨CapabilitySet.union⟩

def singleton (l : Nat) : CapabilitySet :=
  .cap l

instance instSingleton : Singleton Nat CapabilitySet :=
  ⟨CapabilitySet.singleton⟩

inductive Subset : CapabilitySet -> CapabilitySet -> Prop where
| refl :
  Subset C C
| empty :
  Subset .empty C
| trans :
  Subset C1 C2 ->
  Subset C2 C3 ->
  Subset C1 C3
| union_left :
  Subset C1 C3 ->
  Subset C2 C3 ->
  Subset (C1 ∪ C2) C3
| union_right_left :
  Subset C1 (C1 ∪ C2)
| union_right_right :
  Subset C1 (C2 ∪ C1)

instance instHasSubset : HasSubset CapabilitySet :=
  ⟨CapabilitySet.Subset⟩

theorem subset_preserves_mem {C1 C2 : CapabilitySet} {x : Nat}
  (hsub : C1 ⊆ C2)
  (hmem : x ∈ C1) :
  x ∈ C2 := by
  induction hsub generalizing x
  case refl => exact hmem
  case trans ih1 ih2 => apply ih2 (ih1 hmem)
  case empty => cases hmem
  case union_left ih1 ih2 =>
    cases hmem
    case left h => exact ih1 h
    case right h => exact ih2 h
  case union_right_left => exact mem.left hmem
  case union_right_right => exact mem.right hmem

/-- If an element is in a set, then the singleton of that element is a subset of the set. -/
theorem mem_imp_singleton_subset {C : CapabilitySet} {x : Nat}
  (hmem : x ∈ C) :
  {x} ⊆ C := by
  -- We need to prove that the singleton {x} is a subset of C
  -- This requires case analysis on C and use of the subset constructors
  induction C with
  | empty => cases hmem
  | cap y =>
    -- C = {y}, and x ∈ {y}, so x = y
    cases hmem
    -- x = y, so {x} = {y} = C
    apply Subset.refl
  | union C1 C2 ih1 ih2 =>
    cases hmem with
    | left h =>
      -- x ∈ C1, so by IH: {x} ⊆ C1
      -- Need: {x} ⊆ (C1 ∪ C2)
      apply Subset.trans (ih1 h)
      apply Subset.union_right_left
    | right h =>
      -- x ∈ C2, so by IH: {x} ⊆ C2
      -- Need: {x} ⊆ (C1 ∪ C2)
      apply Subset.trans (ih2 h)
      apply Subset.union_right_right

end CapabilitySet

/-- A heap value.
    It must be a simple value, with a reachability set computed. -/
structure HeapVal where
  unwrap : Exp {}
  isVal : unwrap.IsSimpleVal
  reachability : CapabilitySet

/-- Convert IsSimpleVal to IsVal -/
theorem Exp.IsSimpleVal.to_IsVal {e : Exp s} (h : e.IsSimpleVal) : e.IsVal :=
  match e, h with
  | .abs _ _ _, .abs => .abs
  | .tabs _ _ _, .tabs => .tabs
  | .cabs _ _ _, .cabs => .cabs
  | .unit, .unit => .unit

-- A heap cell can either be a value or a capability
inductive Cell : Type where
| val : HeapVal -> Cell
| capability : Cell
| masked : Cell

-- A heap is a function from locations to cells
def Heap : Type := Nat -> Option Cell

def Heap.empty : Heap := fun _ => none

instance Heap.instEmptyCollection : EmptyCollection Heap := ⟨Heap.empty⟩

def Heap.extend (h : Heap) (l : Nat) (v : HeapVal) : Heap :=
  fun l' => if l' = l then some (.val v) else h l'

def Heap.extend_cap (h : Heap) (l : Nat) : Heap :=
  fun l' => if l' = l then some .capability else h l'

def Heap.subsumes (big small : Heap) : Prop :=
  ∀ l v, small l = some v -> big l = some v

theorem Heap.subsumes_refl (h : Heap) : h.subsumes h := by
  intros l v hlookup
  exact hlookup

/-- Heap predicate. -/
def Hprop := Heap -> Prop

/-- Postcondition. -/
def Hpost := Exp {} -> Hprop

/-- Monotonicity of postconditions. -/
def Hpost.is_monotonic (Q : Hpost) : Prop :=
  ∀ {h1 h2 : Heap} {e},
    h2.subsumes h1 ->
    Q e h1 ->
    Q e h2

def Hpost.entails (Q1 Q2 : Hpost) : Prop :=
  ∀ h e,
    Q1 e h ->
    Q2 e h

def Hpost.entails_refl (Q : Hpost) : Q.entails Q := by
  intros h e hQ
  exact hQ

def Heap.subsumes_trans {h1 h2 h3 : Heap}
  (h12 : h1.subsumes h2)
  (h23 : h2.subsumes h3) :
  h1.subsumes h3 := by
  intros l v hlookup
  apply h12 l v
  apply h23 l v
  exact hlookup

theorem Heap.extend_lookup_eq
  (h : Heap) (l : Nat) (v : HeapVal) :
  (h.extend l v) l = some (.val v) := by
  simp [Heap.extend]

theorem Heap.extend_subsumes {H : Heap} {l : Nat}
  (hfresh : H l = none) :
  (H.extend l v).subsumes H := by
  intro l' v' hlookup
  simp [Heap.extend]
  split
  next heq =>
    rw [heq] at hlookup
    rw [hfresh] at hlookup
    contradiction
  next => exact hlookup

inductive CaptureSet.WfInHeap : CaptureSet s -> Heap -> Prop where
| wf_empty :
  CaptureSet.WfInHeap {} H
| wf_union :
  CaptureSet.WfInHeap C1 H ->
  CaptureSet.WfInHeap C2 H ->
  CaptureSet.WfInHeap (C1 ∪ C2) H
| wf_var_free :
  H x = some val ->
  CaptureSet.WfInHeap (CaptureSet.var (.free x)) H
| wf_var_bound :
  CaptureSet.WfInHeap (CaptureSet.var (.bound x)) H
| wf_cvar :
  CaptureSet.WfInHeap (CaptureSet.cvar x) H

inductive Var.WfInHeap : Var k s -> Heap -> Prop where
| wf_bound :
  Var.WfInHeap (.bound x) H
| wf_free :
  H n = some val ->
  Var.WfInHeap (.free n) H

inductive CaptureBound.WfInHeap : CaptureBound s -> Heap -> Prop where
| wf_unbound :
  CaptureBound.WfInHeap .unbound H
| wf_bound :
  CaptureSet.WfInHeap cs H ->
  CaptureBound.WfInHeap (.bound cs) H

inductive Ty.WfInHeap : Ty sort s -> Heap -> Prop where
-- Shape types
| wf_top :
  Ty.WfInHeap .top H
| wf_tvar :
  Ty.WfInHeap (.tvar x) H
| wf_arrow :
  Ty.WfInHeap T1 H ->
  Ty.WfInHeap T2 H ->
  Ty.WfInHeap (.arrow T1 T2) H
| wf_poly :
  Ty.WfInHeap T1 H ->
  Ty.WfInHeap T2 H ->
  Ty.WfInHeap (.poly T1 T2) H
| wf_cpoly :
  CaptureBound.WfInHeap cb H ->
  Ty.WfInHeap T H ->
  Ty.WfInHeap (.cpoly cb T) H
| wf_unit :
  Ty.WfInHeap .unit H
| wf_cap :
  Ty.WfInHeap .cap H
-- Capturing types
| wf_capt :
  CaptureSet.WfInHeap cs H ->
  Ty.WfInHeap T H ->
  Ty.WfInHeap (.capt cs T) H
-- Existential types
| wf_exi :
  Ty.WfInHeap T H ->
  Ty.WfInHeap (.exi T) H
| wf_typ :
  Ty.WfInHeap T H ->
  Ty.WfInHeap (.typ T) H

inductive Exp.WfInHeap : Exp s -> Heap -> Prop where
| wf_var :
  Var.WfInHeap x H ->
  Exp.WfInHeap (.var x) H
| wf_abs :
  CaptureSet.WfInHeap cs H ->
  Ty.WfInHeap T H ->
  Exp.WfInHeap e H ->
  Exp.WfInHeap (.abs cs T e) H
| wf_tabs :
  CaptureSet.WfInHeap cs H ->
  Ty.WfInHeap T H ->
  Exp.WfInHeap e H ->
  Exp.WfInHeap (.tabs cs T e) H
| wf_cabs :
  CaptureSet.WfInHeap cs H ->
  CaptureBound.WfInHeap cb H ->
  Exp.WfInHeap e H ->
  Exp.WfInHeap (.cabs cs cb e) H
| wf_pack :
  CaptureSet.WfInHeap cs H ->
  Var.WfInHeap x H ->
  Exp.WfInHeap (.pack cs x) H
| wf_app :
  Var.WfInHeap x H ->
  Var.WfInHeap y H ->
  Exp.WfInHeap (.app x y) H
| wf_tapp :
  Var.WfInHeap x H ->
  Ty.WfInHeap T H ->
  Exp.WfInHeap (.tapp x T) H
| wf_capp :
  Var.WfInHeap x H ->
  CaptureSet.WfInHeap cs H ->
  Exp.WfInHeap (.capp x cs) H
| wf_letin :
  Exp.WfInHeap e1 H ->
  Exp.WfInHeap e2 H ->
  Exp.WfInHeap (.letin e1 e2) H
| wf_unpack :
  Exp.WfInHeap e1 H ->
  Exp.WfInHeap e2 H ->
  Exp.WfInHeap (.unpack e1 e2) H
| wf_unit :
  Exp.WfInHeap .unit H

-- Closedness implies well-formedness in any heap

/-- Closedness implies well-formedness for variables. -/
theorem Var.wf_of_closed {x : Var k s} {H : Heap}
  (hclosed : x.IsClosed) :
  Var.WfInHeap x H := by
  cases hclosed
  apply Var.WfInHeap.wf_bound

/-- Closedness implies well-formedness for capture sets. -/
theorem CaptureSet.wf_of_closed {cs : CaptureSet s} {H : Heap}
  (hclosed : cs.IsClosed) :
  CaptureSet.WfInHeap cs H := by
  induction hclosed with
  | empty => apply CaptureSet.WfInHeap.wf_empty
  | union _ _ ih1 ih2 => apply CaptureSet.WfInHeap.wf_union <;> assumption
  | cvar => apply CaptureSet.WfInHeap.wf_cvar
  | var_bound => apply CaptureSet.WfInHeap.wf_var_bound

/-- Closedness implies well-formedness for capture bounds. -/
theorem CaptureBound.wf_of_closed {cb : CaptureBound s} {H : Heap}
  (hclosed : cb.IsClosed) :
  CaptureBound.WfInHeap cb H := by
  cases hclosed with
  | unbound => apply CaptureBound.WfInHeap.wf_unbound
  | bound hcs => apply CaptureBound.WfInHeap.wf_bound; exact CaptureSet.wf_of_closed hcs

/-- Closedness implies well-formedness for types. -/
theorem Ty.wf_of_closed {T : Ty sort s} {H : Heap}
  (hclosed : T.IsClosed) :
  Ty.WfInHeap T H := by
  induction hclosed with
  | top => apply Ty.WfInHeap.wf_top
  | tvar => apply Ty.WfInHeap.wf_tvar
  | arrow _ _ ih1 ih2 => apply Ty.WfInHeap.wf_arrow <;> assumption
  | poly _ _ ih1 ih2 => apply Ty.WfInHeap.wf_poly <;> assumption
  | cpoly hcb _ ih =>
    apply Ty.WfInHeap.wf_cpoly
    · exact CaptureBound.wf_of_closed hcb
    · exact ih
  | unit => apply Ty.WfInHeap.wf_unit
  | cap => apply Ty.WfInHeap.wf_cap
  | capt hcs _ ih =>
    apply Ty.WfInHeap.wf_capt
    · exact CaptureSet.wf_of_closed hcs
    · exact ih
  | exi _ ih => apply Ty.WfInHeap.wf_exi; exact ih
  | typ _ ih => apply Ty.WfInHeap.wf_typ; exact ih

/-- Closedness implies well-formedness for expressions. -/
theorem Exp.wf_of_closed {e : Exp s} {H : Heap}
  (hclosed : e.IsClosed) :
  Exp.WfInHeap e H := by
  induction hclosed with
  | var hx => apply Exp.WfInHeap.wf_var; exact Var.wf_of_closed hx
  | abs hcs hT _ ih =>
    apply Exp.WfInHeap.wf_abs
    · exact CaptureSet.wf_of_closed hcs
    · exact Ty.wf_of_closed hT
    · exact ih
  | tabs hcs hT _ ih =>
    apply Exp.WfInHeap.wf_tabs
    · exact CaptureSet.wf_of_closed hcs
    · exact Ty.wf_of_closed hT
    · exact ih
  | cabs hcs hcb _ ih =>
    apply Exp.WfInHeap.wf_cabs
    · exact CaptureSet.wf_of_closed hcs
    · exact CaptureBound.wf_of_closed hcb
    · exact ih
  | pack hcs hx =>
    apply Exp.WfInHeap.wf_pack
    · exact CaptureSet.wf_of_closed hcs
    · exact Var.wf_of_closed hx
  | app hx hy =>
    apply Exp.WfInHeap.wf_app
    · exact Var.wf_of_closed hx
    · exact Var.wf_of_closed hy
  | tapp hx hT =>
    apply Exp.WfInHeap.wf_tapp
    · exact Var.wf_of_closed hx
    · exact Ty.wf_of_closed hT
  | capp hx hcs =>
    apply Exp.WfInHeap.wf_capp
    · exact Var.wf_of_closed hx
    · exact CaptureSet.wf_of_closed hcs
  | letin _ _ ih1 ih2 => apply Exp.WfInHeap.wf_letin <;> assumption
  | unpack _ _ ih1 ih2 => apply Exp.WfInHeap.wf_unpack <;> assumption
  | unit => apply Exp.WfInHeap.wf_unit

-- Monotonicity theorems: WfInHeap is preserved under heap subsumption

theorem Var.wf_monotonic
  {h1 h2 : Heap}
  (hsub : h2.subsumes h1)
  (hwf : Var.WfInHeap x h1) :
  Var.WfInHeap x h2 := by
  cases hwf with
  | wf_bound => apply Var.WfInHeap.wf_bound
  | wf_free hex =>
    apply Var.WfInHeap.wf_free
    apply hsub _ _ hex

theorem CaptureSet.wf_monotonic
  {h1 h2 : Heap}
  (hsub : h2.subsumes h1)
  (hwf : CaptureSet.WfInHeap cs h1) :
  CaptureSet.WfInHeap cs h2 := by
  induction hwf with
  | wf_empty => apply CaptureSet.WfInHeap.wf_empty
  | wf_union _ _ ih1 ih2 =>
    apply CaptureSet.WfInHeap.wf_union
    · exact ih1 hsub
    · exact ih2 hsub
  | wf_var_free hex =>
    apply CaptureSet.WfInHeap.wf_var_free
    apply hsub _ _ hex
  | wf_var_bound => apply CaptureSet.WfInHeap.wf_var_bound
  | wf_cvar => apply CaptureSet.WfInHeap.wf_cvar

theorem CaptureBound.wf_monotonic
  {h1 h2 : Heap}
  (hsub : h2.subsumes h1)
  (hwf : CaptureBound.WfInHeap cb h1) :
  CaptureBound.WfInHeap cb h2 := by
  cases hwf with
  | wf_unbound => apply CaptureBound.WfInHeap.wf_unbound
  | wf_bound hwf_cs =>
    apply CaptureBound.WfInHeap.wf_bound
    apply CaptureSet.wf_monotonic hsub hwf_cs

theorem Ty.wf_monotonic
  {h1 h2 : Heap}
  (hsub : h2.subsumes h1)
  (hwf : Ty.WfInHeap T h1) :
  Ty.WfInHeap T h2 := by
  induction hwf generalizing h2 with
  | wf_top => apply Ty.WfInHeap.wf_top
  | wf_tvar => apply Ty.WfInHeap.wf_tvar
  | wf_arrow _ _ ih1 ih2 =>
    apply Ty.WfInHeap.wf_arrow
    · exact ih1 hsub
    · exact ih2 hsub
  | wf_poly _ _ ih1 ih2 =>
    apply Ty.WfInHeap.wf_poly
    · exact ih1 hsub
    · exact ih2 hsub
  | wf_cpoly hwf_cb hwf_T ih_T =>
    apply Ty.WfInHeap.wf_cpoly
    · exact CaptureBound.wf_monotonic hsub hwf_cb
    · exact ih_T hsub
  | wf_unit => apply Ty.WfInHeap.wf_unit
  | wf_cap => apply Ty.WfInHeap.wf_cap
  | wf_capt hwf_cs hwf_T ih_T =>
    apply Ty.WfInHeap.wf_capt
    · exact CaptureSet.wf_monotonic hsub hwf_cs
    · exact ih_T hsub
  | wf_exi hwf ih => apply Ty.WfInHeap.wf_exi; exact ih hsub
  | wf_typ hwf ih => apply Ty.WfInHeap.wf_typ; exact ih hsub

theorem Exp.wf_monotonic
  {h1 h2 : Heap}
  (hsub : h2.subsumes h1)
  (hwf : Exp.WfInHeap e h1) :
  Exp.WfInHeap e h2 := by
  induction hwf generalizing h2 with
  | wf_var hwf_x =>
    apply Exp.WfInHeap.wf_var
    exact Var.wf_monotonic hsub hwf_x
  | wf_abs hwf_cs hwf_T hwf_e ih_e =>
    apply Exp.WfInHeap.wf_abs
    · exact CaptureSet.wf_monotonic hsub hwf_cs
    · exact Ty.wf_monotonic hsub hwf_T
    · exact ih_e hsub
  | wf_tabs hwf_cs hwf_T hwf_e ih_e =>
    apply Exp.WfInHeap.wf_tabs
    · exact CaptureSet.wf_monotonic hsub hwf_cs
    · exact Ty.wf_monotonic hsub hwf_T
    · exact ih_e hsub
  | wf_cabs hwf_cs hwf_cb hwf_e ih_e =>
    apply Exp.WfInHeap.wf_cabs
    · exact CaptureSet.wf_monotonic hsub hwf_cs
    · exact CaptureBound.wf_monotonic hsub hwf_cb
    · exact ih_e hsub
  | wf_pack hwf_cs hwf_x =>
    apply Exp.WfInHeap.wf_pack
    · exact CaptureSet.wf_monotonic hsub hwf_cs
    · exact Var.wf_monotonic hsub hwf_x
  | wf_app hwf_x hwf_y =>
    apply Exp.WfInHeap.wf_app
    · exact Var.wf_monotonic hsub hwf_x
    · exact Var.wf_monotonic hsub hwf_y
  | wf_tapp hwf_x hwf_T =>
    apply Exp.WfInHeap.wf_tapp
    · exact Var.wf_monotonic hsub hwf_x
    · exact Ty.wf_monotonic hsub hwf_T
  | wf_capp hwf_x hwf_cs =>
    apply Exp.WfInHeap.wf_capp
    · exact Var.wf_monotonic hsub hwf_x
    · exact CaptureSet.wf_monotonic hsub hwf_cs
  | wf_letin hwf1 hwf2 ih1 ih2 =>
    apply Exp.WfInHeap.wf_letin
    · exact ih1 hsub
    · exact ih2 hsub
  | wf_unpack hwf1 hwf2 ih1 ih2 =>
    apply Exp.WfInHeap.wf_unpack
    · exact ih1 hsub
    · exact ih2 hsub
  | wf_unit =>
    apply Exp.WfInHeap.wf_unit

-- Inversion theorems for Exp.WfInHeap

/-- Inversion for let-in: if `let x = e1 in e2` is well-formed,
    then both `e1` and `e2` are well-formed. -/
theorem Exp.wf_inv_letin
  {e1 : Exp s} {e2 : Exp (s,x)} {H : Heap}
  (hwf : Exp.WfInHeap (.letin e1 e2) H) :
  Exp.WfInHeap e1 H ∧ Exp.WfInHeap e2 H := by
  cases hwf with
  | wf_letin hwf1 hwf2 => exact ⟨hwf1, hwf2⟩

/-- Inversion for unpack: if `unpack e1 in e2` is well-formed,
    then both `e1` and `e2` are well-formed. -/
theorem Exp.wf_inv_unpack
  {e1 : Exp s} {e2 : Exp ((s,C),x)} {H : Heap}
  (hwf : Exp.WfInHeap (.unpack e1 e2) H) :
  Exp.WfInHeap e1 H ∧ Exp.WfInHeap e2 H := by
  cases hwf with
  | wf_unpack hwf1 hwf2 => exact ⟨hwf1, hwf2⟩

/-- Inversion for lambda abstraction: if `λ(cs) (x : T). e` is well-formed,
    then its capture set, type, and body are all well-formed. -/
theorem Exp.wf_inv_abs
  {cs : CaptureSet s} {T : Ty .capt s} {e : Exp (s,x)} {H : Heap}
  (hwf : Exp.WfInHeap (.abs cs T e) H) :
  CaptureSet.WfInHeap cs H ∧ Ty.WfInHeap T H ∧ Exp.WfInHeap e H := by
  cases hwf with
  | wf_abs hwf_cs hwf_T hwf_e => exact ⟨hwf_cs, hwf_T, hwf_e⟩

/-- Inversion for type abstraction: if `Λ(cs) (X <: T). e` is well-formed,
    then its capture set, type bound, and body are all well-formed. -/
theorem Exp.wf_inv_tabs
  {cs : CaptureSet s} {T : Ty .shape s} {e : Exp (s,X)} {H : Heap}
  (hwf : Exp.WfInHeap (.tabs cs T e) H) :
  CaptureSet.WfInHeap cs H ∧ Ty.WfInHeap T H ∧ Exp.WfInHeap e H := by
  cases hwf with
  | wf_tabs hwf_cs hwf_T hwf_e => exact ⟨hwf_cs, hwf_T, hwf_e⟩

/-- Inversion for capture abstraction: if `λ[cs] (C <: cb). e` is well-formed,
    then its capture set, capture bound, and body are all well-formed. -/
theorem Exp.wf_inv_cabs
  {cs : CaptureSet s} {cb : CaptureBound s} {e : Exp (s,C)} {H : Heap}
  (hwf : Exp.WfInHeap (.cabs cs cb e) H) :
  CaptureSet.WfInHeap cs H ∧ CaptureBound.WfInHeap cb H ∧ Exp.WfInHeap e H := by
  cases hwf with
  | wf_cabs hwf_cs hwf_cb hwf_e => exact ⟨hwf_cs, hwf_cb, hwf_e⟩

structure Subst.WfInHeap (s : Subst s1 s2) (H : Heap) where
  wf_var :
    ∀ x, Var.WfInHeap (s.var x) H

  wf_tvar :
    ∀ X, Ty.WfInHeap (s.tvar X) H

  wf_cvar :
    ∀ C, CaptureSet.WfInHeap (s.cvar C) H

/-- Lookup the reachability set of a location. -/
def reachability_of_loc
  (h : Heap)
  (l : Nat) :
  CapabilitySet :=
  match h l with
  | some .capability => {l}
  | some (.val ⟨_, _, R⟩) => R
  | some .masked => {l}
  | none => {}

/-- Resolve reachability of each element of the capture set. -/
def expand_captures
  (h : Heap)
  (cs : CaptureSet {}) :
  CapabilitySet :=
  match cs with
  | .empty => {}
  | .var (.free loc) => reachability_of_loc h loc
  | .union cs1 cs2 => expand_captures h cs1 ∪ expand_captures h cs2

/-- Compute reachability for a heap value. -/
def compute_reachability
  (h : Heap)
  (v : Exp {}) (hv : v.IsSimpleVal) :
  CapabilitySet :=
  match v with
  | .abs cs _ _ => expand_captures h cs
  | .tabs cs _ _ => expand_captures h cs
  | .cabs cs _ _ => expand_captures h cs
  | .unit => {}

theorem reachability_of_loc_monotonic
  {h1 h2 : Heap}
  (hsub : h2.subsumes h1)
  (l : Nat)
  (hex : h1 l = some v) :
  reachability_of_loc h2 l = reachability_of_loc h1 l := by
  have h2_eq : h2 l = some v := hsub l v hex
  simp only [reachability_of_loc] at hex h2_eq ⊢
  rw [hex, h2_eq]

/-- Expanding a capture set in a bigger heap yields the same result.
Proof by induction on cs. Requires all free locations in cs to exist in h1. -/
theorem expand_captures_monotonic
  {h1 h2 : Heap}
  (hsub : h2.subsumes h1)
  (cs : CaptureSet {})
  (hwf : CaptureSet.WfInHeap cs h1) :
  expand_captures h2 cs = expand_captures h1 cs := by
  induction cs with
  | empty =>
    -- Base case: empty capture set expands to empty in any heap
    rfl
  | var x =>
    cases x with
    | bound x =>
      -- Impossible: no bound variables in empty signature
      cases x
    | free loc =>
      -- Variable case: use reachability_of_loc_monotonic
      simp [expand_captures]
      -- Extract existence proof from well-formedness
      cases hwf with
      | wf_var_free hex =>
        -- We have hex : h1 loc = some cell_val
        exact reachability_of_loc_monotonic hsub loc hex
  | cvar C =>
    -- Impossible: no capability variables in empty signature
    cases C
  | union cs1 cs2 ih1 ih2 =>
    -- Union case: by induction on both components
    -- First, extract well-formedness for both components
    cases hwf with
    | wf_union hwf1 hwf2 =>
      simp [expand_captures, ih1 hwf1, ih2 hwf2]

/-- Computing reachability of a value in a bigger heap yields the same result.
Proof by cases on hv, using expand_captures_monotonic. -/
theorem compute_reachability_monotonic
  {h1 h2 : Heap}
  (hsub : h2.subsumes h1)
  (v : Exp {})
  (hv : v.IsSimpleVal)
  (hwf : Exp.WfInHeap v h1) :
  compute_reachability h2 v hv = compute_reachability h1 v hv := by
  -- Case analysis on the structure of the simple value
  cases hv with
  | abs =>
    -- Case: v = .abs cs T e
    -- compute_reachability h v = expand_captures h cs
    simp [compute_reachability]
    -- Extract well-formedness of the capture set
    cases hwf with
    | wf_abs hwf_cs _ _ =>
      exact expand_captures_monotonic hsub _ hwf_cs
  | tabs =>
    -- Case: v = .tabs cs T e
    simp [compute_reachability]
    cases hwf with
    | wf_tabs hwf_cs _ _ =>
      exact expand_captures_monotonic hsub _ hwf_cs
  | cabs =>
    -- Case: v = .cabs cs cb e
    simp [compute_reachability]
    cases hwf with
    | wf_cabs hwf_cs _ _ =>
      exact expand_captures_monotonic hsub _ hwf_cs
  | unit =>
    -- Case: v = .unit
    -- Both heaps yield empty capability set
    rfl

/-- A heap is well-formed if all values stored in it contain well-formed expressions. -/
structure Heap.WfHeap (H : Heap) : Prop where
  wf_val :
    ∀ l hv, H l = some (.val hv) -> Exp.WfInHeap hv.unwrap H
  wf_reach :
    ∀ l v hv R,
      H l = some (.val ⟨v, hv, R⟩) ->
        R = compute_reachability H v hv

/-- The empty heap is well-formed. -/
theorem Heap.wf_empty : Heap.WfHeap ∅ := by
  constructor
  · intro l hv hlookup; cases hlookup
  · intros _ _ _ _ hlookup; cases hlookup

/-- Extending a well-formed heap with a well-formed value preserves well-formedness. -/
theorem Heap.wf_extend
  {H : Heap} {l : Nat} {v : HeapVal}
  (hwf_H : H.WfHeap)
  (hwf_v : Exp.WfInHeap v.unwrap H)
  (hreach : v.reachability = compute_reachability H v.unwrap v.isVal)
  (hfresh : H l = none) :
  (H.extend l v).WfHeap := by
  constructor
  · -- wf_val case
    intro l' hv' hlookup
    unfold Heap.extend at hlookup
    split at hlookup
    case isTrue heq =>
      cases hlookup
      -- Use monotonicity to lift hwf_v from H to H.extend l v
      apply Exp.wf_monotonic
      · apply Heap.extend_subsumes
        exact hfresh
      · exact hwf_v
    case isFalse hneq =>
      apply Exp.wf_monotonic
      · apply Heap.extend_subsumes
        exact hfresh
      · exact hwf_H.wf_val l' hv' hlookup
  · -- wf_reach case
    intro l' v' hv' R' hlookup
    unfold Heap.extend at hlookup
    split at hlookup
    case isTrue heq =>
      cases hlookup
      -- Use monotonicity to show reachability is the same in extended heap
      rw [compute_reachability_monotonic (Heap.extend_subsumes hfresh) v' hv' hwf_v]
      exact hreach
    case isFalse hneq =>
      have heq := hwf_H.wf_reach l' v' hv' R' hlookup
      rw [heq]
      exact (compute_reachability_monotonic (Heap.extend_subsumes hfresh) v' hv'
        (hwf_H.wf_val l' _ hlookup)).symm

/-- If a heap is well-formed and we look up a value, the expression is well-formed. -/
theorem Heap.wf_lookup
  {H : Heap} {l : Nat} {hv : HeapVal}
  (hwf_H : H.WfHeap)
  (hlookup : H l = some (.val hv)) :
  Exp.WfInHeap hv.unwrap H :=
  hwf_H.wf_val l hv hlookup

-- Renaming preserves well-formedness

/-- Renaming preserves well-formedness of variables. -/
theorem Var.wf_rename
  {x : Var k s1}
  {f : Rename s1 s2}
  {H : Heap}
  (hwf : Var.WfInHeap x H) :
  Var.WfInHeap (x.rename f) H := by
  cases hwf with
  | wf_bound =>
    simp [Var.rename]
    apply Var.WfInHeap.wf_bound
  | wf_free hex =>
    simp [Var.rename]
    apply Var.WfInHeap.wf_free
    exact hex

/-- Renaming preserves well-formedness of capture sets. -/
theorem CaptureSet.wf_rename
  {cs : CaptureSet s1}
  {f : Rename s1 s2}
  {H : Heap}
  (hwf : CaptureSet.WfInHeap cs H) :
  CaptureSet.WfInHeap (cs.rename f) H := by
  induction hwf with
  | wf_empty =>
    simp [CaptureSet.rename]
    apply CaptureSet.WfInHeap.wf_empty
  | wf_union _ _ ih1 ih2 =>
    simp [CaptureSet.rename]
    apply CaptureSet.WfInHeap.wf_union
    · exact ih1
    · exact ih2
  | wf_var_free hex =>
    simp [CaptureSet.rename]
    apply CaptureSet.WfInHeap.wf_var_free
    exact hex
  | wf_var_bound =>
    simp [CaptureSet.rename]
    apply CaptureSet.WfInHeap.wf_var_bound
  | wf_cvar =>
    simp [CaptureSet.rename]
    apply CaptureSet.WfInHeap.wf_cvar

/-- Renaming preserves well-formedness of capture bounds. -/
theorem CaptureBound.wf_rename
  {cb : CaptureBound s1}
  {f : Rename s1 s2}
  {H : Heap}
  (hwf : CaptureBound.WfInHeap cb H) :
  CaptureBound.WfInHeap (cb.rename f) H := by
  cases hwf with
  | wf_unbound =>
    simp [CaptureBound.rename]
    apply CaptureBound.WfInHeap.wf_unbound
  | wf_bound hwf_cs =>
    simp [CaptureBound.rename]
    apply CaptureBound.WfInHeap.wf_bound
    exact CaptureSet.wf_rename hwf_cs

/-- Renaming preserves well-formedness of types. -/
theorem Ty.wf_rename
  {T : Ty sort s1}
  {f : Rename s1 s2}
  {H : Heap}
  (hwf : Ty.WfInHeap T H) :
  Ty.WfInHeap (T.rename f) H := by
  induction hwf generalizing s2 with
  | wf_top =>
    simp [Ty.rename]
    apply Ty.WfInHeap.wf_top
  | wf_tvar =>
    simp [Ty.rename]
    apply Ty.WfInHeap.wf_tvar
  | wf_arrow _ _ ih1 ih2 =>
    simp [Ty.rename]
    apply Ty.WfInHeap.wf_arrow
    · exact ih1
    · exact ih2
  | wf_poly _ _ ih1 ih2 =>
    simp [Ty.rename]
    apply Ty.WfInHeap.wf_poly
    · exact ih1
    · exact ih2
  | wf_cpoly hwf_cb _ ih_T =>
    simp [Ty.rename]
    apply Ty.WfInHeap.wf_cpoly
    · exact CaptureBound.wf_rename hwf_cb
    · exact ih_T
  | wf_unit =>
    simp [Ty.rename]
    apply Ty.WfInHeap.wf_unit
  | wf_cap =>
    simp [Ty.rename]
    apply Ty.WfInHeap.wf_cap
  | wf_capt hwf_cs _ ih_T =>
    simp [Ty.rename]
    apply Ty.WfInHeap.wf_capt
    · exact CaptureSet.wf_rename hwf_cs
    · exact ih_T
  | wf_exi _ ih =>
    simp [Ty.rename]
    apply Ty.WfInHeap.wf_exi
    exact ih
  | wf_typ _ ih =>
    simp [Ty.rename]
    apply Ty.WfInHeap.wf_typ
    exact ih

/-- Renaming preserves well-formedness of expressions. -/
theorem Exp.wf_rename
  {e : Exp s1}
  {f : Rename s1 s2}
  {H : Heap}
  (hwf : Exp.WfInHeap e H) :
  Exp.WfInHeap (e.rename f) H := by
  induction hwf generalizing s2 with
  | wf_var hwf_x =>
    simp [Exp.rename]
    apply Exp.WfInHeap.wf_var
    exact Var.wf_rename hwf_x
  | wf_abs hwf_cs hwf_T _ ih_e =>
    simp [Exp.rename]
    apply Exp.WfInHeap.wf_abs
    · exact CaptureSet.wf_rename hwf_cs
    · exact Ty.wf_rename hwf_T
    · exact ih_e
  | wf_tabs hwf_cs hwf_T _ ih_e =>
    simp [Exp.rename]
    apply Exp.WfInHeap.wf_tabs
    · exact CaptureSet.wf_rename hwf_cs
    · exact Ty.wf_rename hwf_T
    · exact ih_e
  | wf_cabs hwf_cs hwf_cb _ ih_e =>
    simp [Exp.rename]
    apply Exp.WfInHeap.wf_cabs
    · exact CaptureSet.wf_rename hwf_cs
    · exact CaptureBound.wf_rename hwf_cb
    · exact ih_e
  | wf_pack hwf_cs hwf_x =>
    simp [Exp.rename]
    apply Exp.WfInHeap.wf_pack
    · exact CaptureSet.wf_rename hwf_cs
    · exact Var.wf_rename hwf_x
  | wf_app hwf_x hwf_y =>
    simp [Exp.rename]
    apply Exp.WfInHeap.wf_app
    · exact Var.wf_rename hwf_x
    · exact Var.wf_rename hwf_y
  | wf_tapp hwf_x hwf_T =>
    simp [Exp.rename]
    apply Exp.WfInHeap.wf_tapp
    · exact Var.wf_rename hwf_x
    · exact Ty.wf_rename hwf_T
  | wf_capp hwf_x hwf_cs =>
    simp [Exp.rename]
    apply Exp.WfInHeap.wf_capp
    · exact Var.wf_rename hwf_x
    · exact CaptureSet.wf_rename hwf_cs
  | wf_letin _ _ ih1 ih2 =>
    simp [Exp.rename]
    apply Exp.WfInHeap.wf_letin
    · exact ih1
    · exact ih2
  | wf_unpack _ _ ih1 ih2 =>
    simp [Exp.rename]
    apply Exp.WfInHeap.wf_unpack
    · exact ih1
    · exact ih2
  | wf_unit =>
    simp [Exp.rename]
    apply Exp.WfInHeap.wf_unit

-- Substitution well-formedness preservation

/-- A well-formed variable yields a well-formed capture set. -/
theorem CaptureSet.wf_of_var
  {x : Var .var s}
  {H : Heap}
  (hwf : Var.WfInHeap x H) :
  CaptureSet.WfInHeap (.var x) H := by
  cases hwf with
  | wf_bound =>
    apply CaptureSet.WfInHeap.wf_var_bound
  | wf_free hex =>
    apply CaptureSet.WfInHeap.wf_var_free
    exact hex

/-- Lifting a well-formed substitution preserves well-formedness. -/
theorem Subst.wf_lift
  {σ : Subst s1 s2}
  {H : Heap}
  (hwf_σ : σ.WfInHeap H) :
  (σ.lift (k:=k)).WfInHeap H := by
  constructor
  · intro x
    cases x with
    | here =>
      simp [Subst.lift]
      apply Var.WfInHeap.wf_bound
    | there x =>
      simp [Subst.lift]
      apply Var.wf_rename
      exact hwf_σ.wf_var x
  · intro X
    cases X with
    | here =>
      simp [Subst.lift]
      apply Ty.WfInHeap.wf_tvar
    | there X =>
      simp [Subst.lift]
      apply Ty.wf_rename
      exact hwf_σ.wf_tvar X
  · intro C
    cases C with
    | here =>
      simp [Subst.lift]
      apply CaptureSet.WfInHeap.wf_cvar
    | there C =>
      simp [Subst.lift]
      apply CaptureSet.wf_rename
      exact hwf_σ.wf_cvar C

/-- Well-formed substitutions preserve well-formedness of variables. -/
theorem Var.wf_subst
  {x : Var .var s1}
  {σ : Subst s1 s2}
  {H : Heap}
  (hwf_x : Var.WfInHeap x H)
  (hwf_σ : σ.WfInHeap H) :
  Var.WfInHeap (x.subst σ) H := by
  cases x with
  | bound x =>
    simp [Var.subst]
    exact hwf_σ.wf_var x
  | free n =>
    simp [Var.subst]
    cases hwf_x with
    | wf_free hex =>
      apply Var.WfInHeap.wf_free
      exact hex

/-- Well-formed substitutions preserve well-formedness of capture sets. -/
theorem CaptureSet.wf_subst
  {cs : CaptureSet s1}
  {σ : Subst s1 s2}
  {H : Heap}
  (hwf_cs : CaptureSet.WfInHeap cs H)
  (hwf_σ : σ.WfInHeap H) :
  CaptureSet.WfInHeap (cs.subst σ) H := by
  induction hwf_cs with
  | wf_empty =>
    simp [CaptureSet.subst]
    apply CaptureSet.WfInHeap.wf_empty
  | wf_union _ _ ih1 ih2 =>
    simp [CaptureSet.subst]
    apply CaptureSet.WfInHeap.wf_union
    · exact ih1 hwf_σ
    · exact ih2 hwf_σ
  | wf_var_free hex =>
    simp [CaptureSet.subst]
    apply CaptureSet.WfInHeap.wf_var_free
    exact hex
  | wf_var_bound =>
    rename_i x H_wf
    simp [CaptureSet.subst]
    apply CaptureSet.wf_of_var
    apply Var.wf_subst
    · apply Var.WfInHeap.wf_bound
    · exact hwf_σ
  | wf_cvar =>
    simp [CaptureSet.subst]
    exact hwf_σ.wf_cvar _

/-- Well-formed substitutions preserve well-formedness of capture bounds. -/
theorem CaptureBound.wf_subst
  {cb : CaptureBound s1}
  {σ : Subst s1 s2}
  {H : Heap}
  (hwf_cb : CaptureBound.WfInHeap cb H)
  (hwf_σ : σ.WfInHeap H) :
  CaptureBound.WfInHeap (cb.subst σ) H := by
  cases hwf_cb with
  | wf_unbound =>
    simp [CaptureBound.subst]
    apply CaptureBound.WfInHeap.wf_unbound
  | wf_bound hwf_cs =>
    simp [CaptureBound.subst]
    apply CaptureBound.WfInHeap.wf_bound
    exact CaptureSet.wf_subst hwf_cs hwf_σ

/-- Well-formed substitutions preserve well-formedness of types. -/
theorem Ty.wf_subst
  {T : Ty sort s1}
  {σ : Subst s1 s2}
  {H : Heap}
  (hwf_T : Ty.WfInHeap T H)
  (hwf_σ : σ.WfInHeap H) :
  Ty.WfInHeap (T.subst σ) H := by
  induction hwf_T generalizing s2 with
  | wf_top =>
    simp [Ty.subst]
    apply Ty.WfInHeap.wf_top
  | wf_tvar =>
    simp [Ty.subst]
    exact hwf_σ.wf_tvar _
  | wf_arrow _ _ ih1 ih2 =>
    simp [Ty.subst]
    apply Ty.WfInHeap.wf_arrow
    · exact ih1 hwf_σ
    · exact ih2 (Subst.wf_lift hwf_σ)
  | wf_poly _ _ ih1 ih2 =>
    simp [Ty.subst]
    apply Ty.WfInHeap.wf_poly
    · exact ih1 hwf_σ
    · exact ih2 (Subst.wf_lift hwf_σ)
  | wf_cpoly hwf_cb _ ih_T =>
    simp [Ty.subst]
    apply Ty.WfInHeap.wf_cpoly
    · exact CaptureBound.wf_subst hwf_cb hwf_σ
    · exact ih_T (Subst.wf_lift hwf_σ)
  | wf_unit =>
    simp [Ty.subst]
    apply Ty.WfInHeap.wf_unit
  | wf_cap =>
    simp [Ty.subst]
    apply Ty.WfInHeap.wf_cap
  | wf_capt hwf_cs _ ih_T =>
    simp [Ty.subst]
    apply Ty.WfInHeap.wf_capt
    · exact CaptureSet.wf_subst hwf_cs hwf_σ
    · exact ih_T hwf_σ
  | wf_exi _ ih =>
    simp [Ty.subst]
    apply Ty.WfInHeap.wf_exi
    exact ih (Subst.wf_lift hwf_σ)
  | wf_typ _ ih =>
    simp [Ty.subst]
    apply Ty.WfInHeap.wf_typ
    exact ih hwf_σ

/-- Well-formed substitutions preserve well-formedness of expressions. -/
theorem Exp.wf_subst
  {e : Exp s1}
  {σ : Subst s1 s2}
  {H : Heap}
  (hwf_e : Exp.WfInHeap e H)
  (hwf_σ : σ.WfInHeap H) :
  Exp.WfInHeap (e.subst σ) H := by
  induction hwf_e generalizing s2 with
  | wf_var hwf_x =>
    simp [Exp.subst]
    apply Exp.WfInHeap.wf_var
    exact Var.wf_subst hwf_x hwf_σ
  | wf_abs hwf_cs hwf_T _ ih_e =>
    simp [Exp.subst]
    apply Exp.WfInHeap.wf_abs
    · exact CaptureSet.wf_subst hwf_cs hwf_σ
    · exact Ty.wf_subst hwf_T hwf_σ
    · exact ih_e (Subst.wf_lift hwf_σ)
  | wf_tabs hwf_cs hwf_T _ ih_e =>
    simp [Exp.subst]
    apply Exp.WfInHeap.wf_tabs
    · exact CaptureSet.wf_subst hwf_cs hwf_σ
    · exact Ty.wf_subst hwf_T hwf_σ
    · exact ih_e (Subst.wf_lift hwf_σ)
  | wf_cabs hwf_cs hwf_cb _ ih_e =>
    simp [Exp.subst]
    apply Exp.WfInHeap.wf_cabs
    · exact CaptureSet.wf_subst hwf_cs hwf_σ
    · exact CaptureBound.wf_subst hwf_cb hwf_σ
    · exact ih_e (Subst.wf_lift hwf_σ)
  | wf_pack hwf_cs hwf_x =>
    simp [Exp.subst]
    apply Exp.WfInHeap.wf_pack
    · exact CaptureSet.wf_subst hwf_cs hwf_σ
    · exact Var.wf_subst hwf_x hwf_σ
  | wf_app hwf_x hwf_y =>
    simp [Exp.subst]
    apply Exp.WfInHeap.wf_app
    · exact Var.wf_subst hwf_x hwf_σ
    · exact Var.wf_subst hwf_y hwf_σ
  | wf_tapp hwf_x hwf_T =>
    simp [Exp.subst]
    apply Exp.WfInHeap.wf_tapp
    · exact Var.wf_subst hwf_x hwf_σ
    · exact Ty.wf_subst hwf_T hwf_σ
  | wf_capp hwf_x hwf_cs =>
    simp [Exp.subst]
    apply Exp.WfInHeap.wf_capp
    · exact Var.wf_subst hwf_x hwf_σ
    · exact CaptureSet.wf_subst hwf_cs hwf_σ
  | wf_letin _ _ ih1 ih2 =>
    simp [Exp.subst]
    apply Exp.WfInHeap.wf_letin
    · exact ih1 hwf_σ
    · exact ih2 (Subst.wf_lift hwf_σ)
  | wf_unpack _ _ ih1 ih2 =>
    simp [Exp.subst]
    apply Exp.WfInHeap.wf_unpack
    · exact ih1 hwf_σ
    · exact ih2 (Subst.wf_lift (Subst.wf_lift hwf_σ))
  | wf_unit =>
    simp [Exp.subst]
    apply Exp.WfInHeap.wf_unit

-- Well-formedness of opening substitutions

/-- Opening substitution for variables is well-formed if the variable is well-formed. -/
theorem Subst.wf_openVar
  {x : Var .var s}
  {H : Heap}
  (hwf_x : Var.WfInHeap x H) :
  (Subst.openVar x).WfInHeap H := by
  constructor
  · intro y
    cases y with
    | here =>
      simp [Subst.openVar]
      exact hwf_x
    | there y0 =>
      simp [Subst.openVar]
      apply Var.WfInHeap.wf_bound
  · intro X
    cases X with
    | there X0 =>
      simp [Subst.openVar]
      apply Ty.WfInHeap.wf_tvar
  · intro C
    cases C with
    | there C0 =>
      simp [Subst.openVar]
      apply CaptureSet.WfInHeap.wf_cvar

/-- Opening substitution for type variables is well-formed if the type is well-formed. -/
theorem Subst.wf_openTVar
  {U : Ty .shape s}
  {H : Heap}
  (hwf_U : Ty.WfInHeap U H) :
  (Subst.openTVar U).WfInHeap H := by
  constructor
  · intro x
    cases x with
    | there x0 =>
      simp [Subst.openTVar]
      apply Var.WfInHeap.wf_bound
  · intro X
    cases X with
    | here =>
      simp [Subst.openTVar]
      exact hwf_U
    | there X0 =>
      simp [Subst.openTVar]
      apply Ty.WfInHeap.wf_tvar
  · intro C
    cases C with
    | there C0 =>
      simp [Subst.openTVar]
      apply CaptureSet.WfInHeap.wf_cvar

/-- Opening substitution for capture variables is well-formed if the capture set is well-formed. -/
theorem Subst.wf_openCVar
  {C : CaptureSet s}
  {H : Heap}
  (hwf_C : CaptureSet.WfInHeap C H) :
  (Subst.openCVar C).WfInHeap H := by
  constructor
  · intro x
    cases x with
    | there x0 =>
      simp [Subst.openCVar]
      apply Var.WfInHeap.wf_bound
  · intro X
    cases X with
    | there X0 =>
      simp [Subst.openCVar]
      apply Ty.WfInHeap.wf_tvar
  · intro C_var
    cases C_var with
    | here =>
      simp [Subst.openCVar]
      exact hwf_C
    | there C0 =>
      simp [Subst.openCVar]
      apply CaptureSet.WfInHeap.wf_cvar

/-- Unpack substitution is well-formed if both the capture set and variable are well-formed. -/
theorem Subst.wf_unpack
  {C : CaptureSet s}
  {x : Var .var s}
  {H : Heap}
  (hwf_C : CaptureSet.WfInHeap C H)
  (hwf_x : Var.WfInHeap x H) :
  (Subst.unpack C x).WfInHeap H := by
  constructor
  · intro y
    cases y with
    | here =>
      -- .here maps to x
      simp [Subst.unpack]
      exact hwf_x
    | there y' =>
      cases y' with
      | there y0 =>
        -- .there (.there y0) maps to .bound y0
        simp [Subst.unpack]
        apply Var.WfInHeap.wf_bound
  · intro X
    cases X with
    | there X' =>
      cases X' with
      | there X0 =>
        -- .there (.there X0) maps to .tvar X0
        simp [Subst.unpack]
        apply Ty.WfInHeap.wf_tvar
  · intro C_var
    cases C_var with
    | there C' =>
      cases C' with
      | here =>
        -- .there .here maps to C
        simp [Subst.unpack]
        exact hwf_C
      | there C0 =>
        -- .there (.there C0) maps to .cvar C0
        simp [Subst.unpack]
        apply CaptureSet.WfInHeap.wf_cvar

def Heap.HasFinDom (H : Heap) (L : Finset Nat) : Prop :=
  ∀ l, H l ≠ none <-> l ∈ L

def Heap.empty_has_fin_dom : Heap.HasFinDom ∅ ∅ := by
  intro l
  aesop

theorem Heap.extend_has_fin_dom {H : Heap} {dom : Finset Nat} {l : Nat} {v : HeapVal}
  (hdom : H.HasFinDom dom) (hfresh : H l = none) :
  (H.extend l v).HasFinDom (dom ∪ {l}) := by
  intro l'
  unfold Heap.extend
  split
  case isTrue heq =>
    subst heq
    constructor
    · intro _
      simp
    · intro _
      simp
  case isFalse hneq =>
    constructor
    · intro h
      have : l' ∈ dom := (hdom l').mp h
      simp [this, hneq]
    · intro h
      simp at h
      rcases h with h | h
      · -- h : l' = l, but we have hneq : ¬l' = l
        contradiction
      · -- h : l' ∈ dom
        exact (hdom l').mpr h

theorem Heap.extend_cap_has_fin_dom {H : Heap} {dom : Finset Nat} {l : Nat}
  (hdom : H.HasFinDom dom) (hfresh : H l = none) :
  (H.extend_cap l).HasFinDom (dom ∪ {l}) := by
  intro l'
  unfold Heap.extend_cap
  split
  case isTrue heq =>
    subst heq
    constructor
    · intro _
      simp
    · intro _
      simp
  case isFalse hneq =>
    constructor
    · intro h
      have : l' ∈ dom := (hdom l').mp h
      simp [this, hneq]
    · intro h
      simp at h
      rcases h with h | h
      · -- h : l' = l, but we have hneq : ¬l' = l
        contradiction
      · -- h : l' ∈ dom
        exact (hdom l').mpr h

/-- Memory is a well-formed heap. -/
structure Memory where
  heap : Heap
  wf : heap.WfHeap
  findom : ∃ dom, heap.HasFinDom dom

namespace Memory

/-- Create an empty memory. -/
def empty : Memory where
  heap := ∅
  wf := Heap.wf_empty
  findom := ⟨∅, Heap.empty_has_fin_dom⟩

/-- Lookup a value in memory. -/
def lookup (m : Memory) (l : Nat) : Option Cell :=
  m.heap l

/-- Extend memory with a new value.
    Requires proof that the value is well-formed and the location is fresh. -/
def extend (m : Memory) (l : Nat) (v : HeapVal)
  (hwf_v : Exp.WfInHeap v.unwrap m.heap)
  (hreach : v.reachability = compute_reachability m.heap v.unwrap v.isVal)
  (hfresh : m.heap l = none) : Memory where
  heap := m.heap.extend l v
  wf := Heap.wf_extend m.wf hwf_v hreach hfresh
  findom :=
    let ⟨dom, hdom⟩ := m.findom
    ⟨dom ∪ {l}, Heap.extend_has_fin_dom hdom hfresh⟩

/-- Heap extension with capability subsumes original heap. -/
theorem Heap.extend_cap_subsumes {H : Heap} {l : Nat}
  (hfresh : H l = none) :
  (H.extend_cap l).subsumes H := by
  intro l' v' hlookup
  unfold Heap.extend_cap
  split
  case isTrue heq =>
    subst heq
    rw [hfresh] at hlookup
    contradiction
  case isFalse => exact hlookup

/-- Extend memory with a capability cell. -/
def extend_cap (m : Memory) (l : Nat)
  (hfresh : m.heap l = none) : Memory where
  heap := m.heap.extend_cap l
  wf := by
    constructor
    · -- wf_val case
      intro l' hv' hlookup
      unfold Heap.extend_cap at hlookup
      split at hlookup
      case isTrue heq =>
        -- If l' = l, then we're looking up the capability, which can't be a val
        cases hlookup
      case isFalse hneq =>
        -- If l' ≠ l, then the lookup is from the original heap
        apply Exp.wf_monotonic (Heap.extend_cap_subsumes hfresh)
        exact m.wf.wf_val l' hv' hlookup
    · -- wf_reach case
      intro l' v' hv' R' hlookup
      unfold Heap.extend_cap at hlookup
      split at hlookup
      case isTrue heq =>
        -- If l' = l, then we're looking up the capability, which can't be a val
        cases hlookup
      case isFalse hneq =>
        -- If l' ≠ l, then the lookup is from the original heap
        have heq := m.wf.wf_reach l' v' hv' R' hlookup
        rw [heq]
        exact (compute_reachability_monotonic (Heap.extend_cap_subsumes hfresh) v' hv'
          (m.wf.wf_val l' _ hlookup)).symm
  findom :=
    let ⟨dom, hdom⟩ := m.findom
    ⟨dom ∪ {l}, Heap.extend_cap_has_fin_dom hdom hfresh⟩

/-- Extend memory with a value that's well-formed in the current heap.
    This is often more convenient than `extend` in practice. -/
def extend_val (m : Memory) (l : Nat) (v : HeapVal)
  (hwf_v : Exp.WfInHeap v.unwrap m.heap)
  (hreach : v.reachability = compute_reachability m.heap v.unwrap v.isVal)
  (hfresh : m.heap l = none) : Memory where
  heap := m.heap.extend l v
  wf := Heap.wf_extend m.wf hwf_v hreach hfresh
  findom :=
    let ⟨dom, hdom⟩ := m.findom
    ⟨dom ∪ {l}, Heap.extend_has_fin_dom hdom hfresh⟩

/-- Memory subsumption: m1 subsumes m2 if m1's heap subsumes m2's heap. -/
def subsumes (m1 m2 : Memory) : Prop :=
  m1.heap.subsumes m2.heap

/-- Reflexivity of memory subsumption. -/
theorem subsumes_refl (m : Memory) : m.subsumes m :=
  Heap.subsumes_refl m.heap

/-- Transitivity of memory subsumption. -/
theorem subsumes_trans {m1 m2 m3 : Memory}
  (h12 : m1.subsumes m2)
  (h23 : m2.subsumes m3) :
  m1.subsumes m3 :=
  Heap.subsumes_trans h12 h23

/-- Looking up from a memory after extension at the same location returns the value. -/
theorem extend_lookup_eq (m : Memory) (l : Nat) (v : HeapVal)
  (hwf_v : Exp.WfInHeap v.unwrap m.heap)
  (hreach : v.reachability = compute_reachability m.heap v.unwrap v.isVal)
  (hfresh : m.heap l = none) :
  (m.extend l v hwf_v hreach hfresh).lookup l = some (.val v) := by
  simp [lookup, extend, Heap.extend]

/-- Extension subsumes the original memory. -/
theorem extend_subsumes (m : Memory) (l : Nat) (v : HeapVal)
  (hwf_v : Exp.WfInHeap v.unwrap m.heap)
  (hreach : v.reachability = compute_reachability m.heap v.unwrap v.isVal)
  (hfresh : m.heap l = none) :
  (m.extend l v hwf_v hreach hfresh).subsumes m := by
  simp [subsumes, extend]
  exact Heap.extend_subsumes hfresh

/-- Extension with extend_val subsumes the original memory. -/
theorem extend_val_subsumes (m : Memory) (l : Nat) (v : HeapVal)
  (hwf_v : Exp.WfInHeap v.unwrap m.heap)
  (hreach : v.reachability = compute_reachability m.heap v.unwrap v.isVal)
  (hfresh : m.heap l = none) :
  (m.extend_val l v hwf_v hreach hfresh).subsumes m := by
  simp [subsumes, extend_val]
  exact Heap.extend_subsumes hfresh

/-- Capability extension subsumes the original memory. -/
theorem extend_cap_subsumes (m : Memory) (l : Nat)
  (hfresh : m.heap l = none) :
  (m.extend_cap l hfresh).subsumes m := by
  simp [subsumes, extend_cap]
  intro l' v' hlookup
  unfold Heap.extend_cap
  split
  case isTrue heq =>
    rw [heq] at hlookup
    rw [hfresh] at hlookup
    contradiction
  case isFalse => exact hlookup

/-- Well-formedness is preserved under memory subsumption. -/
theorem wf_monotonic {e : Exp {}} {m1 m2 : Memory}
  (hsub : m2.subsumes m1)
  (hwf : Exp.WfInHeap e m1.heap) :
  Exp.WfInHeap e m2.heap :=
  Exp.wf_monotonic hsub hwf

/-- Looking up a value from a memory yields a well-formed expression. -/
theorem wf_lookup {m : Memory} {l : Nat} {hv : HeapVal}
  (hlookup : m.lookup l = some (.val hv)) :
  Exp.WfInHeap hv.unwrap m.heap :=
  Heap.wf_lookup m.wf hlookup

end Memory

/-- Memory predicate. -/
def Mprop := Memory -> Prop

/-- Memory postcondition. -/
def Mpost := Exp {} -> Mprop

/-- Monotonicity of memory postconditions. -/
def Mpost.is_monotonic (Q : Mpost) : Prop :=
  ∀ {m1 m2 : Memory} {e},
    (hwf_e : e.WfInHeap m1.heap) ->
    m2.subsumes m1 ->
    Q e m1 ->
    Q e m2

def Mpost.entails (Q1 Q2 : Mpost) : Prop :=
  ∀ m e,
    Q1 e m ->
    Q2 e m

def Mpost.entails_refl (Q : Mpost) : Q.entails Q := by
  intros m e hQ
  exact hQ

theorem Memory.exists_fresh (m : Memory) :
  ∃ l : Nat, m.lookup l = none := by
  -- Extract the finite domain
  obtain ⟨dom, hdom⟩ := m.findom
  -- Choose a location outside the domain
  use dom.sup id + 1
  -- Show it's not in the domain
  unfold Memory.lookup
  by_contra h
  -- If m.heap (dom.sup id + 1) ≠ none, then it must be in dom
  have : dom.sup id + 1 ∈ dom := (hdom (dom.sup id + 1)).mp h
  -- But dom.sup id + 1 > dom.sup id ≥ all elements in dom
  have hbound : ∀ x ∈ dom, x ≤ dom.sup id := by
    intro x hx
    exact Finset.le_sup (f := id) hx
  have : dom.sup id + 1 ≤ dom.sup id := hbound _ this
  omega

/-- A heap has a capability domain if all capabilities on this heap
    lives in the given domain. -/
def Heap.HasCapDom (H : Heap) (d : Finset Nat) : Prop :=
  ∀ l, H l = some .capability <-> l ∈ d

/-- Masks capabilities in the heap outside of the given domain. -/
def Heap.mask_caps (H : Heap) (d : Finset Nat) : Heap :=
  fun l =>
    match H l with
    | some .capability =>
      if l ∈ d then some .capability else some .masked
    | some v => some v
    | none => none

/-- Turns a capability set into a finite set of natural numbers. -/
def CapabilitySet.to_finset : CapabilitySet -> Finset Nat
| .empty => {}
| .union cs1 cs2 => cs1.to_finset ∪ cs2.to_finset
| .cap x => {x}

end CC
