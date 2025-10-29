import Semantic.CC.Syntax
import Semantic.CC.Substitution

namespace CC

/-- A set of capability labels, representing an "authority":
  they are the set of capabilities a program at most uses. -/
inductive CapabilitySet : Type where
| empty : CapabilitySet
| cap : Nat -> CapabilitySet
| union : CapabilitySet -> CapabilitySet -> CapabilitySet
| any : CapabilitySet

namespace CapabilitySet

inductive mem : Nat -> CapabilitySet -> Prop where
| here : CapabilitySet.mem l (CapabilitySet.cap l)
| here_any : CapabilitySet.mem l CapabilitySet.any
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
| top :
  Subset C .any
| union_left :
  Subset C1 C3 ->
  Subset C2 C3 ->
  Subset (C1 ∪ C2) C3
| union_right_left :
  Subset C1 C3 ->
  Subset C1 (C2 ∪ C3)
| union_right_right :
  Subset C1 C3 ->
  Subset C1 (C3 ∪ C2)

instance instHasSubset : HasSubset CapabilitySet :=
  ⟨CapabilitySet.Subset⟩

end CapabilitySet

/-- A heap value.
    It must be a simple value, with a reachability set computed. -/
structure HeapVal where
  unwrap : Exp {}
  isVal : unwrap.IsSimpleVal
  reachability : CapabilitySet

-- A heap cell can either be a value or a capability
inductive Cell : Type where
| val : HeapVal -> Cell
| capability : Cell

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

end CC
