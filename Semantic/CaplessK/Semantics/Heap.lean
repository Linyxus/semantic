import Semantic.CaplessK.Syntax
import Semantic.CaplessK.Substitution
import Mathlib.Data.Finset.Basic

namespace CaplessK

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

-- Subset lemmas

theorem subset_refl {C : CapabilitySet} : C ⊆ C := Subset.refl

theorem subset_trans {C1 C2 C3 : CapabilitySet} (h1 : C1 ⊆ C2) (h2 : C2 ⊆ C3) : C1 ⊆ C3 :=
  Subset.trans h1 h2

theorem empty_subset : (.empty : CapabilitySet) ⊆ C := Subset.empty

theorem union_subset_of_subset_of_subset {C1 C2 C : CapabilitySet}
  (h1 : C1 ⊆ C)
  (h2 : C2 ⊆ C) :
  (C1 ∪ C2) ⊆ C := Subset.union_left h1 h2

theorem subset_union_left {C1 C2 : CapabilitySet} : C1 ⊆ (C1 ∪ C2) := Subset.union_right_left

theorem subset_union_right {C1 C2 : CapabilitySet} : C2 ⊆ (C1 ∪ C2) := Subset.union_right_right

-- Equivalence relation: two sets are equivalent iff they have the same members
def equiv (C1 C2 : CapabilitySet) : Prop :=
  ∀ x, x ∈ C1 ↔ x ∈ C2

infix:50 " ≈ " => equiv

theorem equiv_refl : C ≈ C := fun _ => Iff.rfl

theorem equiv_symm (h : C1 ≈ C2) : C2 ≈ C1 := fun x => (h x).symm

theorem equiv_trans (h1 : C1 ≈ C2) (h2 : C2 ≈ C3) : C1 ≈ C3 :=
  fun x => (h1 x).trans (h2 x)

-- Empty union equivalences
theorem empty_union_equiv : (∅ ∪ C) ≈ C := by
  intro x
  constructor
  · intro hmem
    cases hmem with
    | left h => cases h
    | right h => exact h
  · intro hmem
    exact mem.right hmem

theorem union_empty_equiv : (C ∪ ∅) ≈ C := by
  intro x
  constructor
  · intro hmem
    cases hmem with
    | left h => exact h
    | right h => cases h
  · intro hmem
    exact mem.left hmem

-- Subset implies membership preservation (already have subset_preserves_mem)

-- Syntactic subset implies semantic containment
-- (already proven as subset_preserves_mem)

-- For equivalence: if C1 ≈ C2, then syntactically they may differ but
-- semantically they're the same. We can build a syntactic subset proof
-- by induction on the structure.

-- Union associativity equivalence
theorem union_assoc_equiv : ((C1 ∪ C2) ∪ C3) ≈ (C1 ∪ (C2 ∪ C3)) := by
  intro x
  constructor
  · intro hmem
    cases hmem with
    | left h =>
      cases h with
      | left h1 => exact mem.left h1
      | right h2 => exact mem.right (mem.left h2)
    | right h3 => exact mem.right (mem.right h3)
  · intro hmem
    cases hmem with
    | left h1 => exact mem.left (mem.left h1)
    | right h =>
      cases h with
      | left h2 => exact mem.left (mem.right h2)
      | right h3 => exact mem.right h3

/-- Helper: If all elements of C1 are in C2, and C2 ⊆ C, then C1 ⊆ C2.
    This is proven by structural induction on C1. -/
private theorem subset_of_mem_transfer {C1 C2 : CapabilitySet}
  (hmem : ∀ x, x ∈ C1 → x ∈ C2) :
  C1 ⊆ C2 := by
  induction C1 with
  | empty => exact Subset.empty
  | cap x =>
    have hx : x ∈ C2 := hmem x mem.here
    exact mem_imp_singleton_subset hx
  | union C1a C1b ih1 ih2 =>
    apply Subset.union_left
    · apply ih1
      intro y hy
      exact hmem y (mem.left hy)
    · apply ih2
      intro y hy
      exact hmem y (mem.right hy)

/-- If C1 ≈ C2 and C2 ⊆ C, then C1 ⊆ C.
    This allows transferring subset through equivalence. -/
theorem subset_of_equiv_subset {C1 C2 C : CapabilitySet}
  (heq : C1 ≈ C2)
  (hsub : C2 ⊆ C) :
  C1 ⊆ C := by
  -- First show C1 ⊆ C2 using the equivalence
  have hsub12 : C1 ⊆ C2 := subset_of_mem_transfer (fun x hx => (heq x).mp hx)
  -- Then use transitivity
  exact Subset.trans hsub12 hsub

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
  | .btrue, .btrue => .btrue
  | .bfalse, .bfalse => .bfalse

/-- Underlying info of a capability. -/
inductive CapabilityInfo : Type where
| basic : CapabilityInfo
| mcell : Bool -> CapabilityInfo
| label : Classifier -> CapabilityInfo

/-- Retrieve the classifier of a capability. -/
def CapabilityInfo.classifier : CapabilityInfo -> Classifier
| .basic => .top
| .mcell _ => .top
| .label k => k

/-- A heap cell. -/
inductive Cell : Type where
| val : HeapVal -> Cell
| capability : CapabilityInfo -> Cell
| masked : Cell

-- A heap is a function from locations to cells
def Heap : Type := Nat -> Option Cell

def Heap.empty : Heap := fun _ => none

instance Heap.instEmptyCollection : EmptyCollection Heap := ⟨Heap.empty⟩

def Heap.extend (h : Heap) (l : Nat) (v : HeapVal) : Heap :=
  fun l' => if l' = l then some (.val v) else h l'

def Heap.extend_cap (h : Heap) (l : Nat) : Heap :=
  fun l' => if l' = l then some (.capability .basic) else h l'

/-- Update a cell in the heap with a new cell value. -/
def Heap.update_cell (h : Heap) (l : Nat) (c : Cell) : Heap :=
  fun l' => if l' = l then some c else h l'

/-- Auxiliary relation: one cell subsumes another.
    For mutable cells, the boolean value is irrelevant. -/
def Cell.subsumes : Cell -> Cell -> Prop
| .capability (.mcell _), .capability (.mcell _) => True
| c1, c2 => c1 = c2

theorem Cell.subsumes_refl (c : Cell) : c.subsumes c := by
  cases c <;> simp [Cell.subsumes]
  case capability info =>
    cases info <;> simp

theorem Cell.subsumes_trans {c1 c2 c3 : Cell}
  (h12 : c1.subsumes c2) (h23 : c2.subsumes c3) : c1.subsumes c3 := by
  cases c1 <;> cases c2 <;> cases c3 <;> simp [Cell.subsumes] at h12 h23 ⊢
  all_goals try (subst h12; subst h23; rfl)
  case capability.capability.capability info1 info2 info3 =>
    cases info1 <;> cases info2 <;> cases info3 <;> simp at h12 h23 ⊢
    all_goals (subst h12; subst h23; rfl)

def Heap.subsumes (big small : Heap) : Prop :=
  ∀ l v, small l = some v -> ∃ v', big l = some v' ∧ v'.subsumes v

theorem Heap.subsumes_refl (h : Heap) : h.subsumes h := by
  intros l v hlookup
  exists v
  constructor
  · exact hlookup
  · cases v <;> simp [Cell.subsumes]
    case capability info =>
      cases info <;> simp

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
  obtain ⟨v2, hv2, hsub23⟩ := h23 l v hlookup
  obtain ⟨v1, hv1, hsub12⟩ := h12 l v2 hv2
  exists v1
  constructor
  · exact hv1
  · exact Cell.subsumes_trans hsub12 hsub23

/-- Updating an mcell with another mcell creates a heap that subsumes the original. -/
theorem Heap.update_mcell_subsumes (h : Heap) (l : Nat)
  (hexists : ∃ b0, h l = some (.capability (.mcell b0))) (b : Bool) :
  (h.update_cell l (.capability (.mcell b))).subsumes h := by
  intro l' v hlookup
  unfold Heap.update_cell
  split
  case isTrue heq =>
    -- l' = l
    subst heq
    obtain ⟨b0, hb0⟩ := hexists
    rw [hb0] at hlookup
    cases hlookup
    simp [Cell.subsumes]
  case isFalse hneq =>
    -- l' ≠ l
    exists v
    constructor
    · exact hlookup
    · exact Cell.subsumes_refl v

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
  next =>
    exists v'
    exact ⟨hlookup, Cell.subsumes_refl v'⟩

inductive CaptureSet.WfInHeap : CaptureSet s -> Heap -> Prop where
| wf_empty :
  CaptureSet.WfInHeap {} H
| wf_union :
  CaptureSet.WfInHeap C1 H ->
  CaptureSet.WfInHeap C2 H ->
  CaptureSet.WfInHeap (C1 ∪ C2) H
| wf_var_free :
  H x = some val ->
  CaptureSet.WfInHeap (CaptureSet.var (.free x) K) H
| wf_var_bound :
  CaptureSet.WfInHeap (CaptureSet.var (.bound x) K) H
| wf_cvar :
  CaptureSet.WfInHeap (CaptureSet.cvar x K) H

inductive Var.WfInHeap : Var k s -> Heap -> Prop where
| wf_bound :
  Var.WfInHeap (.bound x) H
| wf_free :
  H n = some val ->
  Var.WfInHeap (.free n) H

inductive CaptureBound.WfInHeap : CaptureBound s -> Heap -> Prop where
| wf_unbound :
  CaptureBound.WfInHeap (.unbound K) H
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
| wf_bool :
  Ty.WfInHeap .bool H
| wf_cell :
  Ty.WfInHeap .cell H
| wf_label :
  Ty.WfInHeap T H ->
  Ty.WfInHeap (.label T) H
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
| wf_btrue :
  Exp.WfInHeap .btrue H
| wf_bfalse :
  Exp.WfInHeap .bfalse H
| wf_read :
  Var.WfInHeap x H ->
  Exp.WfInHeap (.read x) H
| wf_write :
  Var.WfInHeap x H ->
  Var.WfInHeap y H ->
  Exp.WfInHeap (.write x y) H
| wf_cond :
  Var.WfInHeap x H ->
  Exp.WfInHeap e2 H ->
  Exp.WfInHeap e3 H ->
  Exp.WfInHeap (.cond x e2 e3) H
| wf_boundary :
  Ty.WfInHeap T H ->
  Exp.WfInHeap e H ->
  Exp.WfInHeap (.boundary k T e) H

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
  | bool => apply Ty.WfInHeap.wf_bool
  | cell => apply Ty.WfInHeap.wf_cell
  | label _ ih => apply Ty.WfInHeap.wf_label; exact ih
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
  | btrue => apply Exp.WfInHeap.wf_btrue
  | bfalse => apply Exp.WfInHeap.wf_bfalse
  | read hx =>
    apply Exp.WfInHeap.wf_read
    exact Var.wf_of_closed hx
  | write hx hy =>
    apply Exp.WfInHeap.wf_write
    · exact Var.wf_of_closed hx
    · exact Var.wf_of_closed hy
  | cond hx _ _ ih2 ih3 =>
    apply Exp.WfInHeap.wf_cond
    · exact Var.wf_of_closed hx
    · assumption
    · assumption
  | boundary hT _ ih =>
    apply Exp.WfInHeap.wf_boundary
    · exact Ty.wf_of_closed hT
    · exact ih

-- Monotonicity theorems: WfInHeap is preserved under heap subsumption

theorem Var.wf_monotonic
  {h1 h2 : Heap}
  (hsub : h2.subsumes h1)
  (hwf : Var.WfInHeap x h1) :
  Var.WfInHeap x h2 := by
  cases hwf with
  | wf_bound => apply Var.WfInHeap.wf_bound
  | wf_free hex =>
    obtain ⟨v', hv', _⟩ := hsub _ _ hex
    apply Var.WfInHeap.wf_free
    exact hv'

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
    obtain ⟨v', hv', _⟩ := hsub _ _ hex
    apply CaptureSet.WfInHeap.wf_var_free
    exact hv'
  | wf_var_bound => apply CaptureSet.WfInHeap.wf_var_bound
  | wf_cvar => apply CaptureSet.WfInHeap.wf_cvar

theorem CaptureSet.wf_proj
  {cs : CaptureSet s} {H : Heap} {K : CapKind}
  (hwf : CaptureSet.WfInHeap cs H) :
  CaptureSet.WfInHeap (cs.proj K) H := by
  induction hwf with
  | wf_empty => apply CaptureSet.WfInHeap.wf_empty
  | wf_union _ _ ih1 ih2 =>
    apply CaptureSet.WfInHeap.wf_union
    · exact ih1
    · exact ih2
  | wf_var_free hex => apply CaptureSet.WfInHeap.wf_var_free hex
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
  | wf_bool => apply Ty.WfInHeap.wf_bool
  | wf_cell => apply Ty.WfInHeap.wf_cell
  | wf_label _ ih => apply Ty.WfInHeap.wf_label; exact ih hsub
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
  | wf_btrue =>
    apply Exp.WfInHeap.wf_btrue
  | wf_bfalse =>
    apply Exp.WfInHeap.wf_bfalse
  | wf_read hwf_x =>
    apply Exp.WfInHeap.wf_read
    exact Var.wf_monotonic hsub hwf_x
  | wf_write hwf_x hwf_y =>
    apply Exp.WfInHeap.wf_write
    · exact Var.wf_monotonic hsub hwf_x
    · exact Var.wf_monotonic hsub hwf_y
  | wf_cond hwf_x hwf2 hwf3 ih2 ih3 =>
    apply Exp.WfInHeap.wf_cond
    · exact Var.wf_monotonic hsub hwf_x
    · exact ih2 hsub
    · exact ih3 hsub
  | wf_boundary hwf_T hwf_e ih_e =>
    apply Exp.WfInHeap.wf_boundary
    · exact Ty.wf_monotonic hsub hwf_T
    · exact ih_e hsub

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

/-- Inversion for conditionals. -/
theorem Exp.wf_inv_cond
  {x : Var .var s} {e2 e3 : Exp s} {H : Heap}
  (hwf : Exp.WfInHeap (.cond x e2 e3) H) :
  Var.WfInHeap x H ∧ Exp.WfInHeap e2 H ∧ Exp.WfInHeap e3 H := by
  cases hwf with
  | wf_cond hwf_x hwf2 hwf3 => exact ⟨hwf_x, hwf2, hwf3⟩

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
    ∀ C K, CaptureSet.WfInHeap (s.cvar C K) H

/-- Lookup the reachability set of a location. -/
def reachability_of_loc
  (h : Heap)
  (l : Nat) :
  CapabilitySet :=
  match h l with
  | some (.capability _) => {l}
  | some (.val ⟨_, _, R⟩) => R
  | some .masked => {l}
  | none => {}

/-- Get the classifier of a heap location. Returns none if
  the location is not in the heap. -/
def classifier_of_loc : Heap -> Nat -> Option Classifier
| H, l =>
  match H l with
  | some (.capability info) => some info.classifier
  | some _ => some .top
  | _ => none

/-- Project a capability at a given location under a capability kind.
    Returns whether the capability is kept by the projection. -/
def proj_capability (H : Heap) (l : Nat) (K : CapKind) : Bool :=
  match classifier_of_loc H l with
  | some k =>
    CapKind.subkind (.classifier k) K
  | _ => false

/-- Project a capability set under a capability kind. -/
def CapabilitySet.proj
  (C : CapabilitySet)
  (H : Heap) (K : CapKind) : CapabilitySet :=
  match C with
  | .empty => .empty
  | .union cs1 cs2 => .union (cs1.proj H K) (cs2.proj H K)
  | .cap l =>
    if proj_capability H l K then
      .cap l
    else
      .empty

/-- Resolve reachability of each element of the capture set. -/
def expand_captures
  (h : Heap)
  (cs : CaptureSet {}) :
  CapabilitySet :=
  match cs with
  | .empty => {}
  | .var (.free loc) K => (reachability_of_loc h loc).proj h K
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
  | .btrue => {}
  | .bfalse => {}

def resolve : Heap -> Exp {} -> Option (Exp {})
| s, .var (.free x) =>
  match s x with
  | some (.val v) => some v.unwrap
  | _ => none
| s, .var (.bound x) => by cases x
| _, other => some other

def resolve_reachability (H : Heap) (e : Exp {}) : CapabilitySet :=
  match e with
  | .var (.free x) => reachability_of_loc H x
  | .abs cs _ _ => expand_captures H cs
  | .tabs cs _ _ => expand_captures H cs
  | .cabs cs _ _ => expand_captures H cs
  | _ => {}  -- Other expressions have no reachability

theorem resolve_monotonic {H1 H2 : Heap}
  (hsub : H2.subsumes H1)
  (hres : resolve H1 e = some v) :
  resolve H2 e = some v := by
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
      cases hfx : H1 fx
      · -- m1.heap fx = none, contradiction with hres
        simp [hfx] at hres
      · -- m1.heap fx = some cell
        rename_i cell
        simp [hfx] at hres
        cases cell
        case val heapval =>
          simp at hres
          -- hres now says: heapval.unwrap = v
          -- Need to show resolve m2.heap (.var (.free fx)) = some v
          -- We know hsub : H2.subsumes H1
          obtain ⟨v', hv', hsub_v⟩ := hsub fx (.val heapval) hfx
          -- For val cells, subsumes requires equality
          simp [Cell.subsumes] at hsub_v
          subst hsub_v
          simp [hv', hres]
        case capability =>
          -- resolve yields none on capabilities; contradiction with hres
          simp at hres
        case masked =>
          -- resolve yields none on masked cells; contradiction
          simp at hres
    -- For .var (.bound _), already contradicted; done
  -- For other expressions, resolve returns them unchanged
  all_goals
    simp [resolve] at hres
    simp [resolve, hres]

theorem reachability_of_loc_monotonic
  {h1 h2 : Heap}
  (hsub : h2.subsumes h1)
  (l : Nat)
  (hex : h1 l = some v) :
  reachability_of_loc h2 l = reachability_of_loc h1 l := by
  obtain ⟨v', h2_eq, hsub_v⟩ := hsub l v hex
  simp only [reachability_of_loc, hex, h2_eq]
  -- Need to show that subsumes preserves the capability structure
  cases v <;> cases v' <;> simp [Cell.subsumes] at hsub_v
  all_goals try (subst hsub_v; rfl)
  -- For capability and masked cells, both sides return {l}
  all_goals rfl

def CapabilitySet.WfInHeap (C : CapabilitySet) (H : Heap) : Prop :=
  ∀ l, l ∈ C -> ∃ v, H l = some v

/-- A heap is well-formed if all values stored in it contain well-formed expressions
    and correct reachability sets. -/
structure Heap.WfHeap (H : Heap) : Prop where
  wf_val :
    ∀ l hv, H l = some (.val hv) -> Exp.WfInHeap hv.unwrap H
  wf_reach :
    ∀ l v hv R,
      H l = some (.val ⟨v, hv, R⟩) ->
        R = compute_reachability H v hv
  wf_reachability :
    ∀ l hv,
      H l = some (.val hv) →
      hv.reachability.WfInHeap H

/-- proj_capability is preserved under heap subsumption for existing locations. -/
theorem proj_capability_subsumes
    {H1 H2 : Heap}
    (hsub : H2.subsumes H1)
    {l : Nat} {v : Cell}
    (hex : H1 l = some v) :
    proj_capability H2 l K = proj_capability H1 l K := by
  obtain ⟨v', hv', hsub_v⟩ := hsub l v hex
  -- First show classifier_of_loc is preserved
  have hclass : classifier_of_loc H2 l = classifier_of_loc H1 l := by
    simp only [classifier_of_loc, hex, hv']
    cases v with
    | capability info =>
      cases v' with
      | capability info' =>
        cases info <;> cases info' <;> simp [Cell.subsumes] at hsub_v
        · rfl  -- basic.basic
        · rfl  -- mcell.mcell
        · simp [CapabilityInfo.classifier, hsub_v]  -- label.label
      | val _ => simp [Cell.subsumes] at hsub_v
      | masked => simp [Cell.subsumes] at hsub_v
    | val _ =>
      cases v' with
      | val _ => rfl
      | capability _ => simp [Cell.subsumes] at hsub_v
      | masked => simp [Cell.subsumes] at hsub_v
    | masked =>
      cases v' with
      | masked => rfl
      | capability _ => simp [Cell.subsumes] at hsub_v
      | val _ => simp [Cell.subsumes] at hsub_v
  -- Now use it to show proj_capability is preserved
  unfold proj_capability
  rw [hclass]

/-- Projection is preserved under heap subsumption for capability sets
    where all locations exist in the smaller heap. -/
theorem CapabilitySet.proj_subsumes
    {H1 H2 : Heap}
    (hsub : H2.subsumes H1)
    {C : CapabilitySet}
    (hwf : ∀ l, l ∈ C → ∃ v, H1 l = some v) :
    C.proj H2 K = C.proj H1 K := by
  induction C with
  | empty => rfl
  | cap l =>
    simp only [proj]
    have ⟨v, hv⟩ := hwf l .here
    rw [proj_capability_subsumes hsub hv]
  | union c1 c2 ih1 ih2 =>
    simp only [proj]
    have hwf1 : ∀ l, l ∈ c1 → ∃ v, H1 l = some v := fun l hm => hwf l (.left hm)
    have hwf2 : ∀ l, l ∈ c2 → ∃ v, H1 l = some v := fun l hm => hwf l (.right hm)
    rw [ih1 hwf1, ih2 hwf2]

/-- All locations in a HeapVal's stored reachability exist in a well-formed heap. -/
theorem heap_val_reachability_wf
    {H : Heap}
    (hwf : H.WfHeap)
    {l : Nat} {hv : HeapVal}
    (hex : H l = some (.val hv)) :
    ∀ l', l' ∈ hv.reachability → ∃ v', H l' = some v' :=
  hwf.wf_reachability l hv hex

/-- Reachability projection is preserved under heap subsumption.
    This combines reachability_of_loc_monotonic with proj_subsumes. -/
theorem reachability_of_loc_proj_monotonic
    {H1 H2 : Heap}
    (hwf : H1.WfHeap)
    (hsub : H2.subsumes H1)
    {l : Nat} {v : Cell}
    (hex : H1 l = some v) :
    (reachability_of_loc H1 l).proj H2 K = (reachability_of_loc H1 l).proj H1 K := by
  simp only [reachability_of_loc, hex]
  cases v with
  | capability info =>
    -- Singleton case: {l} where l exists in H1
    apply CapabilitySet.proj_subsumes hsub
    intro l' hl'
    cases hl' with
    | here => exact ⟨_, hex⟩
  | val hv =>
    -- Stored reachability R case: hv.reachability
    apply CapabilitySet.proj_subsumes hsub
    -- Need: ∀ l', l' ∈ hv.reachability → ∃ v', H1 l' = some v'
    exact heap_val_reachability_wf hwf hex
  | masked =>
    -- Singleton case: {l} where l exists in H1
    apply CapabilitySet.proj_subsumes hsub
    intro l' hl'
    cases hl' with
    | here => exact ⟨_, hex⟩

/-- Expanding a capture set in a bigger heap yields the same result.
Proof by induction on cs. Requires all free locations in cs to exist in h1
and h1 to be well-formed. -/
theorem expand_captures_monotonic
  {h1 h2 : Heap}
  (hwf_heap : h1.WfHeap)
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
      -- Variable case: combine reachability_of_loc_monotonic with proj preservation
      simp only [expand_captures]
      rename_i K
      -- Extract existence proof from well-formedness
      cases hwf with
      | wf_var_free hex =>
        -- We have hex : h1 loc = some cell_val
        -- First, raw reachability is preserved
        rw [reachability_of_loc_monotonic hsub loc hex]
        -- Then, projection is preserved under subsumption
        exact reachability_of_loc_proj_monotonic hwf_heap hsub hex
  | cvar C =>
    -- Impossible: no capability variables in empty signature
    cases C
  | union cs1 cs2 ih1 ih2 =>
    -- Union case: by induction on both components
    -- First, extract well-formedness for both components
    cases hwf with
    | wf_union hwf1 hwf2 =>
      simp [expand_captures, ih1 hwf1, ih2 hwf2]

/-- Projection preserves location existence: if all locations in C exist in H,
    then all locations in C.proj H K also exist in H. -/
theorem CapabilitySet.proj_locations_exist
    {H : Heap} {C : CapabilitySet}
    (hex : ∀ l, l ∈ C → ∃ v, H l = some v) :
    ∀ l, l ∈ C.proj H K → ∃ v, H l = some v := by
  induction C with
  | empty =>
    intro l hl
    cases hl
  | cap loc =>
    intro l hl
    simp only [proj] at hl
    split at hl
    case isTrue =>
      cases hl
      exact hex loc .here
    case isFalse =>
      cases hl
  | union c1 c2 ih1 ih2 =>
    intro l hl
    simp only [proj] at hl
    cases hl with
    | left hm => exact ih1 (fun l hm => hex l (.left hm)) l hm
    | right hm => exact ih2 (fun l hm => hex l (.right hm)) l hm

/-- Reachability of a location produces only existing locations.
    This is the key lemma: reachability_of_loc returns {l} for caps/masked (which exist),
    stored reachability R for values (which exist by wf_reachability), or {} for none. -/
theorem reachability_of_loc_locations_exist
    {H : Heap}
    (hwf : H.WfHeap)
    {loc : Nat} {v : Cell}
    (hex : H loc = some v) :
    ∀ l, l ∈ reachability_of_loc H loc → ∃ v', H l = some v' := by
  intro l hl
  simp only [reachability_of_loc, hex] at hl
  cases v with
  | capability _ =>
    -- reachability_of_loc returns {loc}, and loc exists
    cases hl
    exact ⟨_, hex⟩
  | val hv =>
    -- reachability_of_loc returns hv.reachability
    -- By wf_reachability, all locations in hv.reachability exist
    exact hwf.wf_reachability loc hv hex l hl
  | masked =>
    -- reachability_of_loc returns {loc}, and loc exists
    cases hl
    exact ⟨_, hex⟩

/-- expand_captures produces only existing locations for well-formed capture sets. -/
theorem expand_captures_locations_exist
    {H : Heap}
    (hwf : H.WfHeap)
    {cs : CaptureSet {}}
    (hwf_cs : cs.WfInHeap H) :
    ∀ l, l ∈ expand_captures H cs → ∃ v, H l = some v := by
  induction cs with
  | empty =>
    intro l hl
    cases hl
  | var x =>
    cases x with
    | bound bx => cases bx
    | free loc =>
      intro l hl
      simp only [expand_captures] at hl
      cases hwf_cs with
      | wf_var_free hex =>
        -- expand_captures returns (reachability_of_loc H loc).proj H K
        -- First, reachability_of_loc produces existing locations
        -- Then, proj preserves this property
        apply CapabilitySet.proj_locations_exist _ l hl
        exact reachability_of_loc_locations_exist hwf hex
  | cvar c => cases c
  | union cs1 cs2 ih1 ih2 =>
    cases hwf_cs with
    | wf_union hwf1 hwf2 =>
      intro l hl
      simp only [expand_captures] at hl
      cases hl with
      | left hm => exact ih1 hwf1 l hm
      | right hm => exact ih2 hwf2 l hm

/-- compute_reachability produces only existing locations for well-formed expressions. -/
theorem compute_reachability_locations_exist
    {H : Heap}
    (hwf : H.WfHeap)
    {v : Exp {}} {hv : v.IsSimpleVal}
    (hwf_v : v.WfInHeap H) :
    ∀ l, l ∈ compute_reachability H v hv → ∃ v', H l = some v' := by
  cases hv with
  | abs =>
    simp only [compute_reachability]
    cases hwf_v with
    | wf_abs hwf_cs _ _ =>
      exact expand_captures_locations_exist hwf hwf_cs
  | tabs =>
    simp only [compute_reachability]
    cases hwf_v with
    | wf_tabs hwf_cs _ _ =>
      exact expand_captures_locations_exist hwf hwf_cs
  | cabs =>
    simp only [compute_reachability]
    cases hwf_v with
    | wf_cabs hwf_cs _ _ =>
      exact expand_captures_locations_exist hwf hwf_cs
  | unit => intro l hl; cases hl
  | btrue => intro l hl; cases hl
  | bfalse => intro l hl; cases hl

theorem resolve_reachability_monotonic
  {H1 H2 : Heap}
  (hwf_heap : H1.WfHeap)
  (hsub : H2.subsumes H1)
  (e : Exp {})
  (hwf : e.WfInHeap H1) :
  resolve_reachability H2 e = resolve_reachability H1 e := by
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
      exact expand_captures_monotonic hwf_heap hsub cs hwf_cs
  | tabs cs _ _ =>
    simp [resolve_reachability]
    cases hwf with
    | wf_tabs hwf_cs _ _ =>
      exact expand_captures_monotonic hwf_heap hsub cs hwf_cs
  | cabs cs _ _ =>
    simp [resolve_reachability]
    cases hwf with
    | wf_cabs hwf_cs _ _ =>
      exact expand_captures_monotonic hwf_heap hsub cs hwf_cs
  | pack _ _ =>
    simp [resolve_reachability]
  | unit =>
    simp [resolve_reachability]
  | btrue =>
    simp [resolve_reachability]
  | bfalse =>
    simp [resolve_reachability]
  | app _ _ =>
    simp [resolve_reachability]
  | tapp _ _ =>
    simp [resolve_reachability]
  | capp _ _ =>
    simp [resolve_reachability]
  | letin _ _ =>
    simp [resolve_reachability]
  | unpack _ _ =>
    simp [resolve_reachability]
  | read _ =>
    simp [resolve_reachability]
  | write _ _ =>
    simp [resolve_reachability]
  | cond _ _ _ =>
    simp [resolve_reachability]
  | boundary _ _ _ =>
    simp [resolve_reachability]

/-- Computing reachability of a value in a bigger heap yields the same result.
Proof by cases on hv, using expand_captures_monotonic. -/
theorem compute_reachability_monotonic
  {h1 h2 : Heap}
  (hwf_heap : h1.WfHeap)
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
      exact expand_captures_monotonic hwf_heap hsub _ hwf_cs
  | tabs =>
    -- Case: v = .tabs cs T e
    simp [compute_reachability]
    cases hwf with
    | wf_tabs hwf_cs _ _ =>
      exact expand_captures_monotonic hwf_heap hsub _ hwf_cs
  | cabs =>
    -- Case: v = .cabs cs cb e
    simp [compute_reachability]
    cases hwf with
    | wf_cabs hwf_cs _ _ =>
      exact expand_captures_monotonic hwf_heap hsub _ hwf_cs
  | unit =>
    -- Case: v = .unit
    -- Both heaps yield empty capability set
    rfl
  | btrue =>
    -- Boolean literals carry no reachability
    rfl
  | bfalse =>
    -- Boolean literals carry no reachability
    rfl

/-- Updating an mcell preserves reachability_of_loc for all locations. -/
theorem reachability_of_loc_update_mcell (h : Heap) (l : Nat)
  (hexists : ∃ b0, h l = some (.capability (.mcell b0))) (b : Bool) (l' : Nat) :
  reachability_of_loc (h.update_cell l (.capability (.mcell b))) l' =
  reachability_of_loc h l' := by
  unfold reachability_of_loc Heap.update_cell
  by_cases heq : l' = l
  · -- l' = l case
    subst heq
    obtain ⟨b0, hb0⟩ := hexists
    simp [hb0]
  · -- l' ≠ l case
    simp [heq]

/-- Updating an mcell preserves proj_capability for all locations.
    The key insight is that mcell's classifier is always .top, so changing
    the boolean doesn't affect the classifier. -/
theorem proj_capability_update_mcell (h : Heap) (l : Nat)
  (hexists : ∃ b0, h l = some (.capability (.mcell b0))) (b : Bool) (l' : Nat) (K : CapKind) :
  proj_capability (h.update_cell l (.capability (.mcell b))) l' K =
  proj_capability h l' K := by
  -- First show classifier_of_loc is preserved
  have hclass : classifier_of_loc (h.update_cell l (.capability (.mcell b))) l' =
                classifier_of_loc h l' := by
    by_cases heq : l' = l
    · -- l' = l case: both mcells have classifier .top
      subst heq
      obtain ⟨b0, hb0⟩ := hexists
      simp only [classifier_of_loc, Heap.update_cell, ↓reduceIte, hb0, CapabilityInfo.classifier]
    · -- l' ≠ l case: lookup unchanged
      simp only [classifier_of_loc, Heap.update_cell, heq, ↓reduceIte]
  simp only [proj_capability, hclass]

/-- Updating an mcell preserves projection of capability sets. -/
theorem CapabilitySet.proj_update_mcell (h : Heap) (l : Nat)
  (hexists : ∃ b0, h l = some (.capability (.mcell b0))) (b : Bool)
  (C : CapabilitySet) (K : CapKind) :
  C.proj (h.update_cell l (.capability (.mcell b))) K = C.proj h K := by
  induction C with
  | empty => rfl
  | cap l' =>
    simp only [proj]
    rw [proj_capability_update_mcell h l hexists b l' K]
  | union c1 c2 ih1 ih2 =>
    simp only [proj, ih1, ih2]

/-- Updating an mcell preserves expand_captures. -/
theorem expand_captures_update_mcell (h : Heap) (l : Nat)
  (hexists : ∃ b0, h l = some (.capability (.mcell b0))) (b : Bool) (cs : CaptureSet {}) :
  expand_captures (h.update_cell l (.capability (.mcell b))) cs =
  expand_captures h cs := by
  induction cs with
  | empty => rfl
  | var x =>
    cases x with
    | bound bv => cases bv
    | free loc =>
      simp only [expand_captures]
      rename_i K
      -- Goal: (reachability_of_loc h' loc).proj h' K = (reachability_of_loc h loc).proj h K
      -- where h' = h.update_cell l (.capability (.mcell b))
      rw [reachability_of_loc_update_mcell h l hexists b loc]
      exact CapabilitySet.proj_update_mcell h l hexists b _ K
  | union cs1 cs2 ih1 ih2 =>
    simp [expand_captures, ih1, ih2]
  | cvar c => cases c

/-- Updating an mcell preserves compute_reachability. -/
theorem compute_reachability_update_mcell (h : Heap) (l : Nat)
  (hexists : ∃ b0, h l = some (.capability (.mcell b0))) (b : Bool)
  (v : Exp {}) (hv : v.IsSimpleVal) :
  compute_reachability (h.update_cell l (.capability (.mcell b))) v hv =
  compute_reachability h v hv := by
  cases hv with
  | abs => simp [compute_reachability]; exact expand_captures_update_mcell h l hexists b _
  | tabs => simp [compute_reachability]; exact expand_captures_update_mcell h l hexists b _
  | cabs => simp [compute_reachability]; exact expand_captures_update_mcell h l hexists b _
  | unit => rfl
  | btrue => rfl
  | bfalse => rfl

/-- The empty heap is well-formed. -/
theorem Heap.wf_empty : Heap.WfHeap ∅ := by
  constructor
  · intro l hv hlookup; cases hlookup
  · intros _ _ _ _ hlookup; cases hlookup
  · intro l hv hlookup; cases hlookup

/-- Extending a well-formed heap with a well-formed value preserves well-formedness. -/
theorem Heap.wf_extend
  {H : Heap} {l : Nat} {v : HeapVal}
  (hwf_H : H.WfHeap)
  (hwf_v : Exp.WfInHeap v.unwrap H)
  (hreach : v.reachability = compute_reachability H v.unwrap v.isVal)
  (hreach_wf : v.reachability.WfInHeap H)
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
      rw [compute_reachability_monotonic hwf_H (Heap.extend_subsumes hfresh) v' hv' hwf_v]
      exact hreach
    case isFalse hneq =>
      have heq := hwf_H.wf_reach l' v' hv' R' hlookup
      rw [heq]
      exact (compute_reachability_monotonic hwf_H (Heap.extend_subsumes hfresh) v' hv'
        (hwf_H.wf_val l' _ hlookup)).symm
  · -- wf_reachability case
    intro l' hv' hlookup
    unfold Heap.extend at hlookup
    split at hlookup
    case isTrue heq =>
      -- l' = l, so hv' = v
      cases hlookup
      intro l'' hl''
      -- l'' is in v.reachability, so it exists in H by hreach_wf
      obtain ⟨cell, hcell⟩ := hreach_wf l'' hl''
      -- Since l'' exists in H and l is fresh, l'' ≠ l
      have hneq : l'' ≠ l := fun h => by rw [h] at hcell; exact Option.noConfusion (hfresh ▸ hcell)
      -- So (H.extend l v) l'' = H l''
      use cell
      simp only [Heap.extend, hneq, ↓reduceIte]
      exact hcell
    case isFalse hneq =>
      -- l' ≠ l, so the lookup is in the original heap H
      intro l'' hl''
      obtain ⟨cell, hcell⟩ := hwf_H.wf_reachability l' hv' hlookup l'' hl''
      -- Since l'' exists in H and l is fresh, l'' ≠ l
      have hneq' : l'' ≠ l := fun h => by rw [h] at hcell; exact Option.noConfusion (hfresh ▸ hcell)
      -- So (H.extend l v) l'' = H l''
      use cell
      simp only [Heap.extend, hneq', ↓reduceIte]
      exact hcell

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
  | wf_bool =>
    simp [Ty.rename]
    apply Ty.WfInHeap.wf_bool
  | wf_cell =>
    simp [Ty.rename]
    apply Ty.WfInHeap.wf_cell
  | wf_label _ ih =>
    simp [Ty.rename]
    apply Ty.WfInHeap.wf_label
    exact ih
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
  | wf_btrue =>
    simp [Exp.rename]
    apply Exp.WfInHeap.wf_btrue
  | wf_bfalse =>
    simp [Exp.rename]
    apply Exp.WfInHeap.wf_bfalse
  | wf_read hwf_x =>
    simp [Exp.rename]
    apply Exp.WfInHeap.wf_read
    exact Var.wf_rename hwf_x
  | wf_write hwf_x hwf_y =>
    simp [Exp.rename]
    apply Exp.WfInHeap.wf_write
    · exact Var.wf_rename hwf_x
    · exact Var.wf_rename hwf_y
  | wf_cond hwf_x _ _ ih2 ih3 =>
    simp [Exp.rename]
    apply Exp.WfInHeap.wf_cond
    · exact Var.wf_rename hwf_x
    · exact ih2
    · exact ih3
  | wf_boundary hwf_T _ ih_e =>
    simp [Exp.rename]
    apply Exp.WfInHeap.wf_boundary
    · exact Ty.wf_rename hwf_T
    · exact ih_e

-- Substitution well-formedness preservation

/-- A well-formed variable yields a well-formed capture set. -/
theorem CaptureSet.wf_of_var
  {x : Var .var s}
  {K : CapKind}
  {H : Heap}
  (hwf : Var.WfInHeap x H) :
  CaptureSet.WfInHeap (.var x K) H := by
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
  · intro C K
    cases C with
    | here =>
      simp [Subst.lift]
      apply CaptureSet.WfInHeap.wf_cvar
    | there C =>
      simp [Subst.lift]
      apply CaptureSet.wf_rename
      exact hwf_σ.wf_cvar C K

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
  | @wf_cvar x K _ =>
    simp [CaptureSet.subst]
    exact hwf_σ.wf_cvar x K

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
  | wf_bool =>
    simp [Ty.subst]
    apply Ty.WfInHeap.wf_bool
  | wf_cell =>
    simp [Ty.subst]
    apply Ty.WfInHeap.wf_cell
  | wf_label _ ih =>
    simp [Ty.subst]
    apply Ty.WfInHeap.wf_label
    exact ih hwf_σ
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
  | wf_btrue =>
    simp [Exp.subst]
    apply Exp.WfInHeap.wf_btrue
  | wf_bfalse =>
    simp [Exp.subst]
    apply Exp.WfInHeap.wf_bfalse
  | wf_read hwf_x =>
    simp [Exp.subst]
    apply Exp.WfInHeap.wf_read
    exact Var.wf_subst hwf_x hwf_σ
  | wf_write hwf_x hwf_y =>
    simp [Exp.subst]
    apply Exp.WfInHeap.wf_write
    · exact Var.wf_subst hwf_x hwf_σ
    · exact Var.wf_subst hwf_y hwf_σ
  | wf_cond hwf_x hwf2 hwf3 ih2 ih3 =>
    simp [Exp.subst]
    apply Exp.WfInHeap.wf_cond
    · exact Var.wf_subst hwf_x hwf_σ
    · exact ih2 hwf_σ
    · exact ih3 hwf_σ
  | wf_boundary hwf_T _ ih_e =>
    simp [Exp.subst]
    apply Exp.WfInHeap.wf_boundary
    · exact Ty.wf_subst hwf_T hwf_σ
    · exact ih_e (Subst.wf_lift (Subst.wf_lift hwf_σ))

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
  · intro C K
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
  · intro C K
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
  · intro C_var K
    cases C_var with
    | here =>
      simp [Subst.openCVar]
      exact CaptureSet.wf_proj hwf_C
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
  · intro C_var K
    cases C_var with
    | there C' =>
      cases C' with
      | here =>
        -- .there .here maps to C
        simp [Subst.unpack]
        exact CaptureSet.wf_proj hwf_C
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
  (hreach_wf : v.reachability.WfInHeap m.heap)
  (hfresh : m.heap l = none) : Memory where
  heap := m.heap.extend l v
  wf := Heap.wf_extend m.wf hwf_v hreach hreach_wf hfresh
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
  case isFalse =>
    exists v'
    exact ⟨hlookup, Cell.subsumes_refl v'⟩

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
        exact (compute_reachability_monotonic m.wf (Heap.extend_cap_subsumes hfresh) v' hv'
          (m.wf.wf_val l' _ hlookup)).symm
    · -- wf_reachability case
      intro l' hv' hlookup
      unfold Heap.extend_cap at hlookup
      split at hlookup
      case isTrue heq =>
        -- If l' = l, then we're looking up the capability, which can't be a val
        cases hlookup
      case isFalse hneq =>
        -- If l' ≠ l, then the lookup is from the original heap
        intro l'' hl''
        obtain ⟨info, hinfo⟩ := m.wf.wf_reachability l' hv' hlookup l'' hl''
        -- Since l'' exists in m.heap and l is fresh, l'' ≠ l
        have hneq' : l'' ≠ l := fun h => by
          rw [h] at hinfo; exact Option.noConfusion (hfresh ▸ hinfo)
        -- So (m.heap.extend_cap l) l'' = m.heap l''
        use info
        simp only [Heap.extend_cap, hneq', ↓reduceIte]
        exact hinfo
  findom :=
    let ⟨dom, hdom⟩ := m.findom
    ⟨dom ∪ {l}, Heap.extend_cap_has_fin_dom hdom hfresh⟩

/-- Extend memory with a value that's well-formed in the current heap.
    This is often more convenient than `extend` in practice. -/
def extend_val (m : Memory) (l : Nat) (v : HeapVal)
  (hwf_v : Exp.WfInHeap v.unwrap m.heap)
  (hreach : v.reachability = compute_reachability m.heap v.unwrap v.isVal)
  (hreach_wf : v.reachability.WfInHeap m.heap)
  (hfresh : m.heap l = none) : Memory where
  heap := m.heap.extend l v
  wf := Heap.wf_extend m.wf hwf_v hreach hreach_wf hfresh
  findom :=
    let ⟨dom, hdom⟩ := m.findom
    ⟨dom ∪ {l}, Heap.extend_has_fin_dom hdom hfresh⟩

/-- Update a mutable cell in memory with a new boolean value.
    Requires proof that the location contains a mutable cell. -/
def update_mcell (m : Memory) (l : Nat) (b : Bool)
  (hexists : ∃ b0, m.heap l = some (.capability (.mcell b0))) : Memory where
  heap := m.heap.update_cell l (.capability (.mcell b))
  wf := by
    constructor
    · -- wf_val case: updating a capability doesn't affect value well-formedness
      intro l' hv' hlookup
      unfold Heap.update_cell at hlookup
      split at hlookup
      case isTrue heq =>
        -- If l' = l, then we're looking up the updated mcell, which can't be a val
        cases hlookup
      case isFalse hneq =>
        -- If l' ≠ l, then the lookup is from the original heap
        -- Well-formedness is preserved because updating a capability doesn't affect values
        -- First, get well-formedness from the original heap
        have hwf_orig : hv'.unwrap.WfInHeap m.heap := m.wf.wf_val l' hv' hlookup
        -- Show that the updated heap subsumes the original heap
        have hsub : (m.heap.update_cell l (.capability (.mcell b))).subsumes m.heap :=
          Heap.update_mcell_subsumes m.heap l hexists b
        -- Apply monotonicity
        exact Exp.wf_monotonic hsub hwf_orig
    · -- wf_reach case: updating a capability doesn't affect reachability computation
      intro l' v' hv' R' hlookup
      unfold Heap.update_cell at hlookup
      split at hlookup
      case isTrue heq =>
        -- If l' = l, then we're looking up the updated mcell, which can't be a val
        cases hlookup
      case isFalse hneq =>
        -- If l' ≠ l, then the lookup is from the original heap
        -- Reachability should be invariant under updating mcells
        -- Get reachability from the original heap
        have hreach_orig : R' = compute_reachability m.heap v' hv' :=
          m.wf.wf_reach l' v' hv' R' hlookup
        -- Show that compute_reachability is preserved
        rw [hreach_orig]
        exact (compute_reachability_update_mcell m.heap l hexists b v' hv').symm
    · -- wf_reachability case: updating a capability doesn't affect which locations exist
      intro l' hv' hlookup
      unfold Heap.update_cell at hlookup
      split at hlookup
      case isTrue heq =>
        -- If l' = l, then we're looking up the updated mcell, which can't be a val
        cases hlookup
      case isFalse hneq =>
        -- If l' ≠ l, then the lookup is from the original heap
        intro l'' hl''
        obtain ⟨cell, hcell⟩ := m.wf.wf_reachability l' hv' hlookup l'' hl''
        -- Check if l'' = l or l'' ≠ l
        by_cases h : l'' = l
        · -- l'' = l, so the updated heap has (.capability (.mcell b)) at l''
          use .capability (.mcell b)
          simp only [Heap.update_cell, h, ↓reduceIte]
        · -- l'' ≠ l, so the cell is unchanged
          use cell
          simp only [Heap.update_cell, h, ↓reduceIte]
          exact hcell
  findom := by
    -- Domain remains unchanged when updating an existing cell
    obtain ⟨dom, hdom⟩ := m.findom
    exists dom
    intro l'
    constructor
    · -- Forward direction: if l' has a value in updated heap, it's in domain
      intro hne_none
      unfold Heap.update_cell at hne_none
      split at hne_none
      case isTrue heq =>
        -- l' = l, and l is in the domain (since it had a cell)
        obtain ⟨b0, hb0⟩ := hexists
        rw [←heq] at hb0
        apply (hdom l').mp
        intro hcontra
        rw [hb0] at hcontra
        cases hcontra
      case isFalse hneq =>
        -- l' ≠ l, so the value came from original heap
        exact (hdom l').mp hne_none
    · -- Backward direction
      intro hin_dom
      unfold Heap.update_cell
      split
      case isTrue => simp
      case isFalse => exact (hdom l').mpr hin_dom

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

/-- Updating a mutable cell creates a memory that subsumes the original. -/
theorem update_mcell_subsumes (m : Memory) (l : Nat) (b : Bool)
  (hexists : ∃ b0, m.heap l = some (.capability (.mcell b0))) :
  (m.update_mcell l b hexists).subsumes m := by
  unfold subsumes update_mcell Heap.subsumes
  intro l' v hlookup
  simp [Heap.update_cell]
  split
  case isTrue heq =>
    -- l' = l, so we're looking up the updated cell
    subst heq
    obtain ⟨b0, hb0⟩ := hexists
    rw [hb0] at hlookup
    exists (.capability (.mcell b))
    constructor
    · simp
    · cases hlookup
      simp [Cell.subsumes]
  case isFalse hneq =>
    -- l' ≠ l, so the lookup is from the original heap
    exists v
    constructor
    · exact hlookup
    · exact Cell.subsumes_refl v

/-- Updating mcells in subsuming memories preserves subsumption. -/
theorem update_mcell_subsumes_compat {m1 m2 : Memory} (l : Nat) (b : Bool)
  (hexists1 : ∃ b0, m1.heap l = some (.capability (.mcell b0)))
  (hexists2 : ∃ b0, m2.heap l = some (.capability (.mcell b0)))
  (hsub : m2.subsumes m1) :
  (m2.update_mcell l b hexists2).subsumes (m1.update_mcell l b hexists1) := by
  unfold subsumes update_mcell Heap.subsumes
  intro l' v hlookup
  simp [Heap.update_cell] at hlookup ⊢
  split at hlookup
  case isTrue heq =>
    -- l' = l, so we're looking up the updated cell in m1
    subst heq
    cases hlookup
    split
    · -- l = l in m2 as well
      simp [Cell.subsumes]
    · contradiction
  case isFalse hneq =>
    -- l' ≠ l, so the lookup is from the original m1
    split
    case isTrue heq =>
      -- l' = l, but hneq says l' ≠ l
      subst heq
      contradiction
    case isFalse =>
      -- l' ≠ l in both, so use subsumption of original memories
      exact hsub l' v hlookup

/-- Looking up from a memory after extension at the same location returns the value. -/
theorem extend_lookup_eq (m : Memory) (l : Nat) (v : HeapVal)
  (hwf_v : Exp.WfInHeap v.unwrap m.heap)
  (hreach : v.reachability = compute_reachability m.heap v.unwrap v.isVal)
  (hreach_wf : v.reachability.WfInHeap m.heap)
  (hfresh : m.heap l = none) :
  (m.extend l v hwf_v hreach hreach_wf hfresh).lookup l = some (.val v) := by
  simp [lookup, extend, Heap.extend]

/-- Extension subsumes the original memory. -/
theorem extend_subsumes (m : Memory) (l : Nat) (v : HeapVal)
  (hwf_v : Exp.WfInHeap v.unwrap m.heap)
  (hreach : v.reachability = compute_reachability m.heap v.unwrap v.isVal)
  (hreach_wf : v.reachability.WfInHeap m.heap)
  (hfresh : m.heap l = none) :
  (m.extend l v hwf_v hreach hreach_wf hfresh).subsumes m := by
  simp [subsumes, extend]
  exact Heap.extend_subsumes hfresh

/-- Extension with extend_val subsumes the original memory. -/
theorem extend_val_subsumes (m : Memory) (l : Nat) (v : HeapVal)
  (hwf_v : Exp.WfInHeap v.unwrap m.heap)
  (hreach : v.reachability = compute_reachability m.heap v.unwrap v.isVal)
  (hreach_wf : v.reachability.WfInHeap m.heap)
  (hfresh : m.heap l = none) :
  (m.extend_val l v hwf_v hreach hreach_wf hfresh).subsumes m := by
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
  case isFalse =>
    exists v'
    exact ⟨hlookup, Cell.subsumes_refl v'⟩

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

def Mpost.is_bool_independent (Q : Mpost) : Prop :=
  ∀ {m : Memory},
    Q (.btrue) m <-> Q (.bfalse) m

/-- Entailment between memory postconditions. -/
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
  ∀ l, (∃ info, H l = some (.capability info)) <-> l ∈ d

/-- Masks capabilities in the heap outside of the given domain. -/
def Heap.mask_caps (H : Heap) (d : Finset Nat) : Heap :=
  fun l =>
    match H l with
    | some (.capability info) =>
      if l ∈ d then some (.capability info) else some .masked
    | some v => some v
    | none => none

/-- Turns a capability set into a finite set of natural numbers. -/
def CapabilitySet.to_finset : CapabilitySet -> Finset Nat
| .empty => {}
| .union cs1 cs2 => cs1.to_finset ∪ cs2.to_finset
| .cap x => {x}

theorem proj_capability_true_of_capability
    {H : Heap} {l : Nat} {info : CapabilityInfo} {K : CapKind}
    (hex : H l = some (.capability info)) :
    proj_capability H l K = (CapKind.classifier info.classifier).subkind K := by
  simp only [proj_capability, classifier_of_loc, hex]

theorem proj_capability_of_true
    {H : Heap} {l : Nat} {K : CapKind}
    (h : proj_capability H l K = true) :
    ∃ k, classifier_of_loc H l = some k ∧
      (CapKind.classifier k).Subkind K := by
  simp only [proj_capability] at h
  split at h
  case h_1 k hk =>
    exact ⟨k, hk, CapKind.subkind_iff_Subkind.mp h⟩
  case h_2 =>
    simp at h

/-- Classifier subkinding is preserved under intersection. -/
theorem classifier_subkind_intersect
    {k : Classifier} {K1 K2 : CapKind} :
    (CapKind.classifier k).Subkind K1 ∧ (CapKind.classifier k).Subkind K2 ↔
    (CapKind.classifier k).Subkind (K1.intersect K2) := by
  rw [CapKind.Subkind.semantics, CapKind.Subkind.semantics, CapKind.Subkind.semantics]
  constructor
  · intro ⟨h1, h2⟩
    intro c hc
    have hc1 := h1 c hc
    have hc2 := h2 c hc
    exact CapKind.Intersect.contains (CapKind.Intersect.lawful K1 K2) hc1 hc2
  · intro h
    constructor
    · intro c hc
      have hc' := h c hc
      exact (CapKind.Intersect.contains_inv (CapKind.Intersect.lawful K1 K2) hc').1
    · intro c hc
      have hc' := h c hc
      exact (CapKind.Intersect.contains_inv (CapKind.Intersect.lawful K1 K2) hc').2

/-- proj_capability is compatible with intersection (Bool version). -/
theorem proj_capability_intersect
    {H : Heap} {l : Nat} {K1 K2 : CapKind} :
    (proj_capability H l K1 = true ∧ proj_capability H l K2 = true) ↔
    proj_capability H l (K1.intersect K2) = true := by
  simp only [proj_capability]
  split
  case h_1 k hk =>
    -- Convert Bool = true to Subkind using subkind_iff_Subkind
    constructor
    · intro ⟨h1, h2⟩
      have hs1 := CapKind.subkind_iff_Subkind.mp h1
      have hs2 := CapKind.subkind_iff_Subkind.mp h2
      exact CapKind.subkind_iff_Subkind.mpr (classifier_subkind_intersect.mp ⟨hs1, hs2⟩)
    · intro h
      have hs := CapKind.subkind_iff_Subkind.mp h
      have ⟨hs1, hs2⟩ := classifier_subkind_intersect.mpr hs
      exact ⟨CapKind.subkind_iff_Subkind.mpr hs1, CapKind.subkind_iff_Subkind.mpr hs2⟩
  case h_2 =>
    simp

/-- Double projection equals single projection with intersection. -/
theorem CapabilitySet.proj_proj
    {C : CapabilitySet} {H : Heap} {K1 K2 : CapKind} :
    (C.proj H K1).proj H K2 = C.proj H (K1.intersect K2) := by
  induction C with
  | empty => rfl
  | cap l =>
    simp only [proj]
    split
    case isTrue h1 =>
      -- h1: proj_capability H l K1 = true
      simp only [proj]
      split
      case isTrue h2 =>
        -- h2: proj_capability H l K2 = true
        have h3 := proj_capability_intersect.mp ⟨h1, h2⟩
        simp only [h3, ite_true]
      case isFalse h2 =>
        -- h2: ¬(proj_capability H l K2 = true)
        split
        case isTrue h3 =>
          have hcontra := proj_capability_intersect.mpr h3
          exact absurd hcontra.2 h2
        case isFalse => rfl
    case isFalse h1 =>
      -- h1: ¬(proj_capability H l K1 = true)
      simp only [proj]
      split
      case isTrue h2 =>
        have hcontra := proj_capability_intersect.mpr h2
        exact absurd hcontra.1 h1
      case isFalse => rfl
  | union c1 c2 ih1 ih2 =>
    simp only [proj, ih1, ih2]

theorem CapabilitySet.proj_top {C : CapabilitySet} {H : Heap}
    (hwf : C.WfInHeap H) :
    C.proj H .top = C := by
  induction C with
  | empty => rfl
  | cap l =>
    have ⟨cell, hex⟩ := hwf l .here
    simp only [proj, proj_capability, classifier_of_loc, hex]
    -- classifier_of_loc returns some _ for any cell, and any k is subkind of .top
    cases cell <;> simp only [CapKind.subkind_top', ↓reduceIte]
  | union c1 c2 ih1 ih2 =>
    have hwf1 : c1.WfInHeap H := fun l hm => hwf l (.left hm)
    have hwf2 : c2.WfInHeap H := fun l hm => hwf l (.right hm)
    simp only [proj, ih1 hwf1, ih2 hwf2]

theorem CapabilitySet.proj_subkind
    {C : CapabilitySet} {H : Heap}
    (hs : CapKind.Subkind K1 K2) :
    C.proj H K1 ⊆ C.proj H K2 := by
  induction C with
  | empty => exact Subset.empty
  | cap l =>
    simp only [proj]
    cases h1 : proj_capability H l K1 with
    | false => simp; exact Subset.empty
    | true =>
      have ⟨k, hk, hsub1⟩ := proj_capability_of_true h1
      have h2 : proj_capability H l K2 = true := by
        simp only [proj_capability, hk]
        exact CapKind.subkind_iff_Subkind.mpr (hsub1.trans hs)
      simp only [h2, ite_true]
      exact Subset.refl
  | union c1 c2 ih1 ih2 =>
    simp only [proj]
    apply Subset.union_left
    · exact Subset.trans ih1 Subset.union_right_left
    · exact Subset.trans ih2 Subset.union_right_right

/-- Projection is monotonic with respect to subset. -/
theorem CapabilitySet.proj_subset_mono
    {C1 C2 : CapabilitySet} {H : Heap} {K : CapKind}
    (hsub : C1 ⊆ C2) :
    C1.proj H K ⊆ C2.proj H K := by
  induction hsub with
  | refl => exact Subset.refl
  | empty => exact Subset.empty
  | trans _ _ ih1 ih2 => exact Subset.trans ih1 ih2
  | union_left _ _ ih1 ih2 =>
    simp only [proj]
    apply Subset.union_left ih1 ih2
  | union_right_left =>
    simp only [proj]
    exact Subset.union_right_left
  | union_right_right =>
    simp only [proj]
    exact Subset.union_right_right

/-- Classifier is preserved under cell subsumption for capability cells. -/
theorem Cell.subsumes_classifier_eq
    {c1 c2 : Cell}
    (hsub : c1.subsumes c2)
    (hcap1 : c1 = .capability info1)
    (hcap2 : c2 = .capability info2) :
    info1.classifier = info2.classifier := by
  subst hcap1 hcap2
  cases info1 <;> cases info2 <;> simp [Cell.subsumes] at hsub
  all_goals simp [CapabilityInfo.classifier]
  all_goals try (subst hsub; rfl)

/-- Classifier is preserved under heap subsumption for existing locations. -/
theorem classifier_of_loc_subsumes
    {H1 H2 : Heap}
    (hsub : H2.subsumes H1)
    {l : Nat} {v : Cell}
    (hex : H1 l = some v) :
    classifier_of_loc H2 l = classifier_of_loc H1 l := by
  obtain ⟨v', hv', hvsub⟩ := hsub l v hex
  simp only [classifier_of_loc, hex, hv']
  cases v with
  | capability info1 =>
    cases v' with
    | capability info2 =>
      simp only [Cell.subsumes_classifier_eq hvsub rfl rfl]
    | val _ => simp [Cell.subsumes] at hvsub
    | masked => simp [Cell.subsumes] at hvsub
  | val hv =>
    cases v' with
    | val _ => simp [Cell.subsumes] at hvsub; subst hvsub; rfl
    | capability _ => simp [Cell.subsumes] at hvsub
    | masked => simp [Cell.subsumes] at hvsub
  | masked =>
    cases v' with
    | masked => rfl
    | capability _ => simp [Cell.subsumes] at hvsub
    | val _ => simp [Cell.subsumes] at hvsub

end CaplessK
