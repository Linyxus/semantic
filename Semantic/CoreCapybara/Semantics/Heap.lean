import Semantic.CoreCapybara.Syntax
import Semantic.CoreCapybara.Substitution
import Mathlib.Data.Finset.Basic

namespace CoreCapybara

inductive CapMode : Type where
| access : Mutability -> CapMode
| drop : CapMode

namespace CapMode

/-- Partial order on capability modes: access modes are ordered by their
    underlying mutability; `.drop` is comparable only to itself. -/
inductive Le : CapMode -> CapMode -> Prop where
| access {m1 m2 : Mutability} : m1 ≤ m2 -> Le (.access m1) (.access m2)
| drop : Le .drop .drop

instance instLE : LE CapMode := ⟨CapMode.Le⟩

theorem Le.refl {m : CapMode} : m ≤ m := by
  cases m with
  | access _ => exact .access Mutability.Le.refl
  | drop => exact .drop

theorem Le.trans {m1 m2 m3 : CapMode} (h1 : m1 ≤ m2) (h2 : m2 ≤ m3) : m1 ≤ m3 := by
  cases h1 with
  | access h1' =>
    cases h2 with
    | access h2' => exact .access (Mutability.Le.trans h1' h2')
  | drop => cases h2; exact .drop

/-- Read-only image of a mode: access modes become `.access .ro`, drop is fixed. -/
def applyRO : CapMode -> CapMode
| .access _ => .access .ro
| .drop => .drop

@[simp]
theorem applyRO_idempotent {m : CapMode} : m.applyRO.applyRO = m.applyRO := by
  cases m <;> rfl

theorem applyRO_le {m : CapMode} : m.applyRO ≤ m := by
  cases m with
  | access m' => exact .access Mutability.Le.ro_le
  | drop => exact .drop

/-- Boolean equality on capability modes. -/
def beq : CapMode → CapMode → Bool
| .access .epsilon, .access .epsilon => true
| .access .ro, .access .ro => true
| .drop, .drop => true
| _, _ => false

theorem beq_iff_eq : ∀ {m1 m2 : CapMode}, m1.beq m2 = true ↔ m1 = m2
  | .access .epsilon, .access .epsilon => by simp only [beq]
  | .access .epsilon, .access .ro      => by simp only [beq]; exact ⟨nofun, nofun⟩
  | .access .ro,      .access .epsilon => by simp only [beq]; exact ⟨nofun, nofun⟩
  | .access .ro,      .access .ro      => by simp only [beq]
  | .access .epsilon, .drop            => by simp only [beq]; exact ⟨nofun, nofun⟩
  | .access .ro,      .drop            => by simp only [beq]; exact ⟨nofun, nofun⟩
  | .drop,            .access .epsilon => by simp only [beq]; exact ⟨nofun, nofun⟩
  | .drop,            .access .ro      => by simp only [beq]; exact ⟨nofun, nofun⟩
  | .drop,            .drop            => by simp only [beq]

/-- Boolean check for `m1 ≤ m2`. Reflects `CapMode.Le`. -/
def leBool : CapMode → CapMode → Bool
| .access .epsilon, .access .epsilon => true
| .access .ro,      .access .epsilon => true
| .access .ro,      .access .ro      => true
| .drop,            .drop            => true
| _, _ => false

theorem leBool_iff_le : ∀ {m1 m2 : CapMode}, m1.leBool m2 = true ↔ m1 ≤ m2
  | .access .epsilon, .access .epsilon => by
      simp only [leBool]
      exact ⟨fun _ => .access .refl, fun _ => trivial⟩
  | .access .epsilon, .access .ro      => by
      simp only [leBool]
      refine ⟨nofun, fun h => ?_⟩
      cases h; rename_i h; cases h
  | .access .ro,      .access .epsilon => by
      simp only [leBool]
      exact ⟨fun _ => .access .ro_eps, fun _ => trivial⟩
  | .access .ro,      .access .ro      => by
      simp only [leBool]
      exact ⟨fun _ => .access .refl, fun _ => trivial⟩
  | .access .epsilon, .drop            => by
      simp only [leBool]; exact ⟨nofun, nofun⟩
  | .access .ro,      .drop            => by
      simp only [leBool]; exact ⟨nofun, nofun⟩
  | .drop,            .access .epsilon => by
      simp only [leBool]; exact ⟨nofun, nofun⟩
  | .drop,            .access .ro      => by
      simp only [leBool]; exact ⟨nofun, nofun⟩
  | .drop,            .drop            => by
      simp only [leBool]
      exact ⟨fun _ => .drop, fun _ => trivial⟩

end CapMode

/-- A set of capability labels, representing an "authority":
  they are the set of capabilities a program at most uses. -/
inductive CapabilitySet : Type where
| empty : CapabilitySet
| cap : CapMode -> Nat -> CapabilitySet
| union : CapabilitySet -> CapabilitySet -> CapabilitySet

namespace CapabilitySet

/-- `covers m l C` means capability set `C` covers location `l` with at least
    cap mode `m`.  Access modes follow the underlying mutability ordering;
    `.drop` is only covered by `.drop`. -/
inductive covers : CapMode -> Nat -> CapabilitySet -> Prop where
| here : m1 ≤ m2 -> CapabilitySet.covers m1 l (CapabilitySet.cap m2 l)
| left {m l C1 C2} :
  CapabilitySet.covers m l C1 ->
  CapabilitySet.covers m l (CapabilitySet.union C1 C2)
| right {m l C1 C2} :
  CapabilitySet.covers m l C2 ->
  CapabilitySet.covers m l (CapabilitySet.union C1 C2)

/-- `hasmem m l C` means capability set `C` contains capability `(m, l)` exactly. -/
inductive hasmem : CapMode -> Nat -> CapabilitySet -> Prop where
| here : CapabilitySet.hasmem m l (CapabilitySet.cap m l)
| left {m l C1 C2} :
  CapabilitySet.hasmem m l C1 ->
  CapabilitySet.hasmem m l (CapabilitySet.union C1 C2)
| right {m l C1 C2} :
  CapabilitySet.hasmem m l C2 ->
  CapabilitySet.hasmem m l (CapabilitySet.union C1 C2)

/-- Nothing is a member of the empty capability set. -/
theorem not_hasmem_empty : ¬ hasmem m l .empty := by
  intro h
  cases h

/-- Nothing is covered by the empty capability set. -/
theorem not_covers_empty : ¬ covers m l .empty := by
  intro h
  cases h

/-- Exact membership implies coverage with the same mode. -/
theorem hasmem_implies_covers : hasmem m l C -> covers m l C := by
  intro h
  induction h with
  | here => exact .here CapMode.Le.refl
  | left _ ih => exact .left ih
  | right _ ih => exact .right ih

/-- Coverage can be weakened to a smaller mode. -/
theorem covers_weaken (h : covers m1 l C) (hle : m2 ≤ m1) : covers m2 l C := by
  induction h with
  | here hle' => exact .here (CapMode.Le.trans hle hle')
  | left _ ih => exact .left ih
  | right _ ih => exact .right ih

/-- Membership with greater mutability implies coverage. -/
theorem covers_of_hasmem_le (h : hasmem m2 l C) (hle : m1 ≤ m2) : covers m1 l C := by
  exact covers_weaken (hasmem_implies_covers h) hle

/-- Characterization of membership in a singleton. -/
theorem hasmem_cap_iff {m m' : CapMode} :
    hasmem m l (.cap m' l') ↔ m = m' ∧ l = l' := by
  constructor
  · intro h
    cases h
    exact ⟨rfl, rfl⟩
  · intro ⟨hm, hl⟩
    subst hm hl
    exact .here

/-- Characterization of coverage in a singleton. -/
theorem covers_cap_iff {m m' : CapMode} :
    covers m l (.cap m' l') ↔ m ≤ m' ∧ l = l' := by
  constructor
  · intro h
    cases h
    rename_i hle
    exact ⟨hle, rfl⟩
  · intro ⟨hle, hl⟩
    subst hl
    exact .here hle

@[simp]
instance instEmptyCollection : EmptyCollection CapabilitySet :=
  ⟨CapabilitySet.empty⟩

@[simp]
instance instUnion : Union CapabilitySet :=
  ⟨CapabilitySet.union⟩

/-- Membership in a union is membership in either component. -/
theorem hasmem_union_iff : hasmem m l (C1 ∪ C2) ↔ hasmem m l C1 ∨ hasmem m l C2 := by
  constructor
  · intro h
    cases h with
    | left h => exact Or.inl h
    | right h => exact Or.inr h
  · intro h
    cases h with
    | inl h => exact .left h
    | inr h => exact .right h

/-- Coverage by a union is coverage by either component. -/
theorem covers_union_iff : covers m l (C1 ∪ C2) ↔ covers m l C1 ∨ covers m l C2 := by
  constructor
  · intro h
    cases h with
    | left h => exact Or.inl h
    | right h => exact Or.inr h
  · intro h
    cases h with
    | inl h => exact .left h
    | inr h => exact .right h

/-- Membership is preserved when extending to a union on the left. -/
theorem hasmem_union_left (h : hasmem m l C1) : hasmem m l (C1 ∪ C2) :=
  .left h

/-- Membership is preserved when extending to a union on the right. -/
theorem hasmem_union_right (h : hasmem m l C2) : hasmem m l (C1 ∪ C2) :=
  .right h

/-- Coverage is preserved when extending to a union on the left. -/
theorem covers_union_left (h : covers m l C1) : covers m l (C1 ∪ C2) :=
  .left h

/-- Coverage is preserved when extending to a union on the right. -/
theorem covers_union_right (h : covers m l C2) : covers m l (C1 ∪ C2) :=
  .right h

/-- A singleton capability at mutability `m` (always in access mode). -/
def singleton (m : Mutability) (l : Nat) : CapabilitySet :=
  .cap (.access m) l

instance instSingleton : Singleton Nat CapabilitySet :=
  ⟨CapabilitySet.singleton .ro⟩

/-- Apply read-only mutability to all elements in a capability set.
    Access caps are demoted to `.access .ro`; drop caps are preserved. -/
def applyRO : CapabilitySet -> CapabilitySet
| .empty => .empty
| .cap m l => .cap m.applyRO l
| .union C1 C2 => .union C1.applyRO C2.applyRO

/-- Apply a mutability to all elements in a capability set.
    epsilon is identity, ro applies read-only. -/
def applyMut (m : Mutability) (C : CapabilitySet) : CapabilitySet :=
  match m with
  | .epsilon => C
  | .ro => C.applyRO

/-- Replace every cap mode in `C` with `.drop`. -/
def to_drop : CapabilitySet -> CapabilitySet
| .empty => .empty
| .cap _ l => .cap .drop l
| .union C1 C2 => .union C1.to_drop C2.to_drop

/-- Apply an access mode to all elements: a mutability acts via `applyMut`,
    and `.drop` retags every cap with `.drop` (real consume authority) via
    `to_drop`. -/
def applyAccess (a : Access) (C : CapabilitySet) : CapabilitySet :=
  match a with
  | .M m => C.applyMut m
  | .drop => C.to_drop

@[simp] theorem applyAccess_M {m : Mutability} {C : CapabilitySet} :
    C.applyAccess (.M m) = C.applyMut m := rfl
@[simp] theorem applyAccess_drop {C : CapabilitySet} :
    C.applyAccess .drop = C.to_drop := rfl

/-- Decidable check that `(mu, l)` is covered by `C` (i.e. there is some
    `(mu', l)` in `C` with `mu ≤ mu'`). -/
def coversCap (mu : CapMode) (l : Nat) : CapabilitySet → Bool
| .empty => false
| .cap mu' l' => mu.leBool mu' && decide (l = l')
| .union C1 C2 => coversCap mu l C1 || coversCap mu l C2

/-- Covers-based intersection with mode-meet semantics: keep caps from `C1`
    at locations also represented in `C2`, weakening the mode if `C2` doesn't
    cover the requested mode but does cover its read-only image. E.g. for
    `(.access .ε, l)` in `C1` and only `(.access .ro, l)` in `C2`, the survivor
    is `(.access .ro, l)`. This mode-meet is what makes `intersect` monotone in
    its left argument under `Subset` (which includes `cap_ro : .ro ⊆ .ε`). -/
def intersect : CapabilitySet → CapabilitySet → CapabilitySet
| .empty, _ => .empty
| .cap mu l, C2 =>
    if C2.coversCap mu l then .cap mu l
    else if C2.coversCap mu.applyRO l then .cap mu.applyRO l
    else .empty
| .union C1a C1b, C2 => .union (intersect C1a C2) (intersect C1b C2)

instance : Inter CapabilitySet := ⟨intersect⟩

/-- applyRO is idempotent. -/
@[simp]
theorem applyRO_applyRO {C : CapabilitySet} : C.applyRO.applyRO = C.applyRO := by
  induction C with
  | empty => rfl
  | cap m l => simp only [applyRO, CapMode.applyRO_idempotent]
  | union C1 C2 ih1 ih2 => simp only [applyRO, ih1, ih2]

/-- `applyRO` fixes `to_drop`: every cap is already `.drop`, and `applyRO`
    preserves `.drop`. -/
@[simp]
theorem to_drop_applyRO {C : CapabilitySet} : C.to_drop.applyRO = C.to_drop := by
  induction C with
  | empty => rfl
  | cap m l => rfl
  | union C1 C2 ih1 ih2 => simp only [to_drop, applyRO, ih1, ih2]

/-- `to_drop` is idempotent. -/
@[simp]
theorem to_drop_to_drop {C : CapabilitySet} : C.to_drop.to_drop = C.to_drop := by
  induction C with
  | empty => rfl
  | cap m l => rfl
  | union C1 C2 ih1 ih2 => simp only [to_drop, ih1, ih2]

/-- `applyMut` is absorbed by `to_drop` (every mode is overwritten with `.drop`). -/
@[simp]
theorem to_drop_applyMut {C : CapabilitySet} {m : Mutability} :
    (C.applyMut m).to_drop = C.to_drop := by
  cases m with
  | epsilon => rfl
  | ro =>
    simp only [applyMut]
    induction C with
    | empty => rfl
    | cap m' l => rfl
    | union C1 C2 ih1 ih2 => simp only [applyRO, to_drop, ih1, ih2]

/-- `applyAccess` is absorbed by `to_drop`. -/
@[simp]
theorem to_drop_applyAccess {C : CapabilitySet} {a : Access} :
    (C.applyAccess a).to_drop = C.to_drop := by
  cases a with
  | M m => simp only [applyAccess_M, to_drop_applyMut]
  | drop => simp only [applyAccess_drop, to_drop_to_drop]

/-- Membership lifts through `to_drop` at mode `.drop` (locations preserved,
    every mode becomes `.drop`). -/
theorem hasmem_to_drop_of_hasmem {C : CapabilitySet} :
    hasmem m l C -> hasmem .drop l C.to_drop := by
  intro h
  induction h with
  | here => exact .here
  | left _ ih => exact .left ih
  | right _ ih => exact .right ih

/-- Membership in `C.to_drop` is always at mode `.drop`, and witnesses some
    member of `C` at the same location. -/
theorem hasmem_to_drop_imp {C : CapabilitySet} {mu : CapMode} {l : Nat} :
    hasmem mu l C.to_drop -> mu = .drop ∧ ∃ m', hasmem m' l C := by
  intro h
  induction C with
  | empty => simp only [to_drop] at h; cases h
  | cap m' l' => simp only [to_drop] at h; cases h; exact ⟨rfl, m', .here⟩
  | union C1 C2 ih1 ih2 =>
    simp only [to_drop] at h
    cases h with
    | left h => obtain ⟨he, m', hm'⟩ := ih1 h; exact ⟨he, m', .left hm'⟩
    | right h => obtain ⟨he, m', hm'⟩ := ih2 h; exact ⟨he, m', .right hm'⟩

/-- Coverage lifts through `to_drop`: any cover of `l` in `Y` gives a `.drop`
    cover of `l` in `Y.to_drop`. -/
theorem covers_to_drop_of_covers {Y : CapabilitySet} {mu : CapMode} {l : Nat} :
    covers mu l Y -> covers .drop l Y.to_drop := by
  intro h
  induction h with
  | here _ => exact .here CapMode.Le.drop
  | left _ ih => exact .left ih
  | right _ ih => exact .right ih

/-- Applying mutability m to an epsilon singleton gives an m singleton. -/
@[simp]
theorem applyMut_singleton_epsilon {m : Mutability} {l : Nat} :
    (singleton .epsilon l).applyMut m = singleton m l := by
  cases m <;> rfl

/-- Applying mutability m to an epsilon access cap gives an m access cap. -/
@[simp]
theorem applyMut_cap_epsilon {m : Mutability} {l : Nat} :
    (cap (.access .epsilon) l).applyMut m = cap (.access m) l := by
  cases m <;> rfl

/-- A singleton (access-mode by construction) never has a `.drop` cap. -/
theorem singleton_no_drop {m : Mutability} {l l' : Nat} :
    ¬ hasmem .drop l (singleton m l') := by
  intro hmem
  simp only [singleton] at hmem
  cases hmem

/-- Membership at location `l` in `C` lifts to membership at `m.applyRO` in `C.applyRO`. -/
theorem hasmem_applyRO_of_hasmem {C : CapabilitySet} :
    hasmem m l C -> hasmem m.applyRO l C.applyRO := by
  intro h
  induction h with
  | here => exact .here
  | left _ ih => exact .left ih
  | right _ ih => exact .right ih

/-- Membership in `C.applyRO` is always at a mode fixed by `applyRO` (i.e.,
    `.access .ro` or `.drop`). -/
theorem hasmem_applyRO_fixed {C : CapabilitySet} :
    hasmem m l C.applyRO -> m = m.applyRO := by
  intro h
  induction C with
  | empty => cases h
  | cap m' l' =>
    simp only [applyRO] at h
    cases h
    cases m' <;> rfl
  | union C1 C2 ih1 ih2 =>
    simp only [applyRO] at h
    cases h with
    | left h => exact ih1 h
    | right h => exact ih2 h

/-- Characterization of membership in `C.applyRO`. -/
theorem hasmem_applyRO_iff {C : CapabilitySet} :
    hasmem m l C.applyRO ↔ ∃ m', m = m'.applyRO ∧ hasmem m' l C := by
  constructor
  · intro h
    induction C with
    | empty => cases h
    | cap m' l' =>
      simp only [applyRO] at h
      cases h
      exact ⟨m', rfl, .here⟩
    | union C1 C2 ih1 ih2 =>
      simp only [applyRO] at h
      cases h with
      | left h =>
        obtain ⟨m', heq, hm'⟩ := ih1 h
        exact ⟨m', heq, .left hm'⟩
      | right h =>
        obtain ⟨m', heq, hm'⟩ := ih2 h
        exact ⟨m', heq, .right hm'⟩
  · intro ⟨m', heq, hm'⟩
    subst heq
    exact hasmem_applyRO_of_hasmem hm'

/-- `applyRO` preserves drop-freeness: `.drop` caps survive, `.access` caps stay
    `.access`, so neither gets introduced where it was absent. -/
theorem applyRO_no_drop {C : CapabilitySet} {l : Nat}
    (h : ¬ hasmem .drop l C) : ¬ hasmem .drop l C.applyRO := by
  intro hmem
  rw [hasmem_applyRO_iff] at hmem
  obtain ⟨m', hmu, hm'⟩ := hmem
  have : m' = .drop := by
    cases m' with
    | access _ => simp only [CapMode.applyRO] at hmu; cases hmu
    | drop => rfl
  subst this
  exact h hm'

/-- `applyMut` preserves drop-freeness. -/
theorem applyMut_no_drop {C : CapabilitySet} {m : Mutability} {l : Nat}
    (h : ¬ hasmem .drop l C) : ¬ hasmem .drop l (C.applyMut m) := by
  cases m with
  | epsilon => exact h
  | ro => exact applyRO_no_drop h

/-- applyRO commutes with applyAccess (reading off the read-only image of the mode). -/
theorem applyAccess_applyRO {C : CapabilitySet} {a : Access} :
    (C.applyAccess a).applyRO = C.applyAccess a.applyRO := by
  cases a with
  | M m =>
    cases m with
    | epsilon => simp only [applyAccess_M, applyMut, Access.applyRO]
    | ro => simp only [applyAccess_M, applyMut, Access.applyRO, applyRO_applyRO]
  | drop => simp only [applyAccess_drop, Access.applyRO, to_drop_applyRO]

/-- Membership in `C.applyMut mu_op` implies coverage in `C` at the same mode:
    `applyMut` can only weaken modes (or be identity), so a member of the
    weakened set is covered by some original mode ≥ it. -/
theorem hasmem_applyMut_implies_covers {C : CapabilitySet} {mu_op : Mutability}
    {mu : CapMode} {l : Nat} (h : (C.applyMut mu_op).hasmem mu l) :
    C.covers mu l := by
  cases mu_op with
  | epsilon => exact hasmem_implies_covers h
  | ro =>
    simp only [applyMut] at h
    obtain ⟨m', heq, hm'⟩ := hasmem_applyRO_iff.mp h
    subst heq
    exact covers_of_hasmem_le hm' CapMode.applyRO_le

/-- Coverage in C is preserved by applyRO when the mode is RO-stable (i.e.,
    `.access .ro` or `.drop`). -/
theorem covers_applyRO_of_covers {C : CapabilitySet} {m : CapMode}
    (h : covers m l C) (hfix : m = m.applyRO) : covers m l C.applyRO := by
  induction C generalizing m with
  | empty => cases h
  | cap m' l' =>
    cases h
    rename_i hle
    simp only [applyRO]
    apply covers.here
    cases hle with
    | access hmu =>
      rename_i mu1 mu2
      have : mu1 = .ro := by cases hfix; rfl
      subst this
      cases mu2 with
      | epsilon => exact .access Mutability.Le.refl
      | ro => exact .access Mutability.Le.refl
    | drop => exact .drop
  | union C1 C2 ih1 ih2 =>
    cases h with
    | left h' => exact .left (ih1 h' hfix)
    | right h' => exact .right (ih2 h' hfix)

/-- Specialization: coverage in C at `.access .ro` passes through to `C.applyRO`. -/
theorem covers_applyRO_of_covers_ro {C : CapabilitySet}
    (h : covers (.access .ro) l C) : covers (.access .ro) l C.applyRO :=
  covers_applyRO_of_covers h rfl

/-- Coverage in C.applyRO implies coverage in C (since applyRO only weakens). -/
theorem covers_of_covers_applyRO {C : CapabilitySet}
    (h : covers m l C.applyRO) : covers m l C := by
  induction C with
  | empty => cases h
  | cap m' l' =>
    simp only [applyRO] at h
    cases h
    rename_i hle
    exact .here (CapMode.Le.trans hle CapMode.applyRO_le)
  | union C1 C2 ih1 ih2 =>
    simp only [applyRO] at h
    cases h with
    | left h => exact .left (ih1 h)
    | right h => exact .right (ih2 h)

/-- Sequential composition check on capability sets: running a computation
authorized by `C1` and then one authorized by `C2` is valid when no location
consumed (`.drop`) in `C1` is used again — at any mode — in `C2` (no
use-after-consume). The runtime mirror of `PeakSet.SeqComp`: membership is
exact (`hasmem`, not `covers`), and the check is ∀-quantified over the second
use's mode `mu`. -/
def SeqComp (C1 C2 : CapabilitySet) : Prop :=
  ∀ (mu : CapMode) (l : Nat),
    hasmem .drop l C1 → hasmem mu l C2 → False

/-- Two capability sets are disjoint when they share no capability: no location
is a member of both `C1` and `C2`, at any cap modes. Like `SeqComp`, membership
is exact (`hasmem`); unlike `SeqComp`, the first use's mode is also universally
quantified, so the check is symmetric and location-level. -/
def disjoint (C1 C2 : CapabilitySet) : Prop :=
  ∀ (mu1 mu2 : CapMode) (l : Nat),
    hasmem mu1 l C1 → hasmem mu2 l C2 → False

/-- Disjointness is symmetric. -/
theorem disjoint.symm {C1 C2 : CapabilitySet} (h : disjoint C1 C2) : disjoint C2 C1 :=
  fun mu1 mu2 l h1 h2 => h mu2 mu1 l h2 h1

/-- A capability set is *drop-free* when it holds no `.drop`-mode capability at any
location. This is the runtime image of a capture-parameter instance carrying no
`.drop` authority (`CaptureSet.is_valid_inst`). -/
def drop_free (C : CapabilitySet) : Prop :=
  ∀ l, ¬ hasmem .drop l C

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
| cap_ro :
  Subset (.cap (.access .ro) l) (.cap (.access .epsilon) l)

instance instHasSubset : HasSubset CapabilitySet :=
  ⟨CapabilitySet.Subset⟩

instance instTransSubset : Trans (α := CapabilitySet) (· ⊆ ·) (· ⊆ ·) (· ⊆ ·) where
  trans := CapabilitySet.Subset.trans

/-- `cap mu.applyRO l ⊆ cap mu l`: the read-only image is a subset (the only
    nontrivial case is `mu = .access .ε`, where `cap_ro` applies). -/
private theorem cap_applyRO_subset_cap {mu : CapMode} {l : Nat} :
    (CapabilitySet.cap mu.applyRO l) ⊆ (CapabilitySet.cap mu l) := by
  cases mu with
  | access mu' =>
    cases mu' with
    | epsilon => exact Subset.cap_ro
    | ro => exact Subset.refl
  | drop => exact Subset.refl

/-- The covers-based intersection is a subset of its first argument. -/
theorem intersect_subset_left :
    ∀ {C1 C2 : CapabilitySet}, C1.intersect C2 ⊆ C1
| .empty, _ => Subset.empty
| .cap mu l, C2 => by
    unfold intersect
    split
    · exact Subset.refl
    · split
      · exact cap_applyRO_subset_cap
      · exact Subset.empty
| .union C1a C1b, C2 => by
    unfold intersect
    exact Subset.union_left
      (Subset.trans (intersect_subset_left (C1 := C1a) (C2 := C2))
        Subset.union_right_left)
      (Subset.trans (intersect_subset_left (C1 := C1b) (C2 := C2))
        Subset.union_right_right)

/-- Bool-Prop bridge: `coversCap` reflects `covers`. -/
theorem coversCap_iff_covers :
    ∀ {C : CapabilitySet} {mu : CapMode} {l : Nat},
      C.coversCap mu l = true ↔ C.covers mu l
| .empty, _, _ => by
    constructor
    · intro h; unfold coversCap at h; cases h
    · intro h; cases h
| .cap mu' l', mu, l => by
    unfold coversCap
    constructor
    · intro h
      have hand : mu.leBool mu' = true ∧ decide (l = l') = true := by
        rw [← Bool.and_eq_true]; exact h
      obtain ⟨hmu, hl⟩ := hand
      have hl_eq : l = l' := of_decide_eq_true hl
      subst hl_eq
      exact .here (CapMode.leBool_iff_le.mp hmu)
    · intro h
      cases h with
      | here hle =>
        rw [Bool.and_eq_true]
        exact ⟨CapMode.leBool_iff_le.mpr hle, decide_eq_true rfl⟩
| .union C1 C2, mu, l => by
    unfold coversCap
    constructor
    · intro h
      rw [Bool.or_eq_true] at h
      cases h with
      | inl h1 =>
        exact .left ((@coversCap_iff_covers C1 mu l).mp h1)
      | inr h2 =>
        exact .right ((@coversCap_iff_covers C2 mu l).mp h2)
    · intro h
      rw [Bool.or_eq_true]
      cases h with
      | left h1 =>
        exact Or.inl ((@coversCap_iff_covers C1 mu l).mpr h1)
      | right h2 =>
        exact Or.inr ((@coversCap_iff_covers C2 mu l).mpr h2)

/-- If every cap in `C1` is covered by `C2`, the intersection equals `C1`. -/
theorem intersect_eq_self_when_covered :
    ∀ {C1 C2 : CapabilitySet},
      (∀ mu l, C1.hasmem mu l → C2.covers mu l) →
      C1.intersect C2 = C1
| .empty, _, _ => rfl
| .cap mu l, C2, h => by
    unfold intersect
    have hcov : C2.covers mu l := h mu l hasmem.here
    rw [coversCap_iff_covers.mpr hcov]
    rfl
| .union C1a C1b, C2, h => by
    unfold intersect
    have h_a : ∀ mu l, C1a.hasmem mu l → C2.covers mu l := fun mu l hm =>
      h mu l (hasmem.left hm)
    have h_b : ∀ mu l, C1b.hasmem mu l → C2.covers mu l := fun mu l hm =>
      h mu l (hasmem.right hm)
    rw [intersect_eq_self_when_covered h_a, intersect_eq_self_when_covered h_b]

/-- Distributivity of `intersect` over `union` on the left (definitional). -/
@[simp]
theorem intersect_union_left {C1 C2 C3 : CapabilitySet} :
    (C1 ∪ C2).intersect C3 = C1.intersect C3 ∪ C2.intersect C3 := rfl

/-- Sub-distributivity of `intersect` over `union` on the right: a cap surviving
    the intersection with `B ∪ C` is covered by `B` or by `C`, hence survives one
    of the two pointwise intersections. -/
theorem intersect_union_right_subset :
    ∀ {A B C : CapabilitySet}, A.intersect (B ∪ C) ⊆ A.intersect B ∪ A.intersect C
| .empty, _, _ => Subset.empty
| .cap mu l, B, C => by
    simp only [intersect]
    by_cases hB1 : B.coversCap mu l = true
    · rw [if_pos (show (B ∪ C).coversCap mu l = true by
        simp only [coversCap, hB1, Bool.true_or]), if_pos hB1]
      exact Subset.union_right_left
    · by_cases hC1 : C.coversCap mu l = true
      · rw [if_pos (show (B ∪ C).coversCap mu l = true by
          simp only [coversCap, hC1, Bool.or_true]), if_neg hB1, if_pos hC1]
        exact Subset.union_right_right
      · rw [if_neg (show ¬ (B ∪ C).coversCap mu l = true by
          simp only [coversCap, Bool.or_eq_true, not_or]; exact ⟨hB1, hC1⟩),
          if_neg hB1, if_neg hC1]
        by_cases hB2 : B.coversCap mu.applyRO l = true
        · rw [if_pos (show (B ∪ C).coversCap mu.applyRO l = true by
            simp only [coversCap, hB2, Bool.true_or]), if_pos hB2]
          exact Subset.union_right_left
        · by_cases hC2 : C.coversCap mu.applyRO l = true
          · rw [if_pos (show (B ∪ C).coversCap mu.applyRO l = true by
              simp only [coversCap, hC2, Bool.or_true]), if_neg hB2, if_pos hC2]
            exact Subset.union_right_right
          · rw [if_neg (show ¬ (B ∪ C).coversCap mu.applyRO l = true by
              simp only [coversCap, Bool.or_eq_true, not_or]; exact ⟨hB2, hC2⟩),
              if_neg hB2, if_neg hC2]
            exact Subset.empty
| .union A1 A2, B, C => by
    simp only [intersect]
    apply Subset.union_left
    · exact Subset.trans (intersect_union_right_subset (A := A1) (B := B) (C := C))
        (Subset.union_left
          (Subset.trans Subset.union_right_left Subset.union_right_left)
          (Subset.trans Subset.union_right_left Subset.union_right_right))
    · exact Subset.trans (intersect_union_right_subset (A := A2) (B := B) (C := C))
        (Subset.union_left
          (Subset.trans Subset.union_right_right Subset.union_right_left)
          (Subset.trans Subset.union_right_right Subset.union_right_right))

/-- A weaker mode gives a smaller singleton cap. -/
theorem mode_le_cap_subset {mu mu' : CapMode} {l : Nat} (h : mu ≤ mu') :
    (CapabilitySet.cap mu l) ⊆ (CapabilitySet.cap mu' l) := by
  cases h with
  | drop => exact Subset.refl
  | access hm =>
    cases hm with
    | refl => exact Subset.refl
    | ro_eps => exact Subset.cap_ro

/-- If `C` covers `(mu, l)`, then the singleton `cap mu l` is a subset of `C`. -/
theorem covers_imp_cap_subset {C : CapabilitySet} {mu : CapMode} {l : Nat}
    (h : C.covers mu l) : (CapabilitySet.cap mu l) ⊆ C := by
  induction h with
  | here hle => exact mode_le_cap_subset hle
  | left _ ih => exact Subset.trans ih Subset.union_right_left
  | right _ ih => exact Subset.trans ih Subset.union_right_right

/-- The covers-based intersection is a subset of its second argument: every
    surviving cap is covered by `B`, hence already present (up to mode) in `B`. -/
theorem intersect_subset_right :
    ∀ {A B : CapabilitySet}, A.intersect B ⊆ B
| .empty, _ => Subset.empty
| .cap mu l, B => by
    simp only [intersect]
    by_cases h1 : B.coversCap mu l = true
    · rw [if_pos h1]
      exact covers_imp_cap_subset (coversCap_iff_covers.mp h1)
    · rw [if_neg h1]
      by_cases h2 : B.coversCap mu.applyRO l = true
      · rw [if_pos h2]
        exact covers_imp_cap_subset (coversCap_iff_covers.mp h2)
      · rw [if_neg h2]
        exact Subset.empty
| .union A1 A2, B => by
    simp only [intersect]
    exact Subset.union_left intersect_subset_right intersect_subset_right

/-- `covers` is anti-monotonic in the mode: stronger mode implies weaker. -/
private theorem covers_anti_mu :
    ∀ {C : CapabilitySet} {mu1 mu2 : CapMode} {l : Nat},
      mu1 ≤ mu2 → C.covers mu2 l → C.covers mu1 l := by
  intro C mu1 mu2 l hle hcov
  induction hcov with
  | here hle2 => exact covers.here (CapMode.Le.trans hle hle2)
  | left _ ih => exact covers.left ih
  | right _ ih => exact covers.right ih

/-- `intersect` is monotone in its first argument under `Subset`. With the
    mode-meet semantics of `intersect`, weakening `C1` via `cap_ro` (`.ro → .ε`)
    only weakens the surviving mode, which is still a subset of the larger
    side's surviving cap. -/
theorem intersect_mono_left :
    ∀ {C1 C1' C2 : CapabilitySet}, C1 ⊆ C1' → C1.intersect C2 ⊆ C1'.intersect C2 := by
  intro C1 C1' C2 hsub
  induction hsub with
  | refl => exact Subset.refl
  | empty => exact Subset.empty
  | trans _ _ ih1 ih2 => exact Subset.trans ih1 ih2
  | union_left _ _ ih1 ih2 => exact Subset.union_left ih1 ih2
  | union_right_left => exact Subset.union_right_left
  | union_right_right => exact Subset.union_right_right
  | cap_ro =>
    rename_i l
    -- Key identity: `(access ε).applyRO = (access ro)`, so when C2 covers only
    -- the RO image the RHS fallback yields exactly the surviving LHS cap.
    unfold intersect
    by_cases hro : C2.coversCap (.access .ro) l = true
    · rw [if_pos hro]
      by_cases heps : C2.coversCap (.access .epsilon) l = true
      · rw [if_pos heps]
        exact Subset.cap_ro
      · rw [if_neg heps]
        have h_ro_eq : ((CapMode.access Mutability.epsilon).applyRO) = CapMode.access .ro := rfl
        rw [h_ro_eq, if_pos hro]
        exact Subset.refl
    · rw [if_neg hro]
      have h_ro_eq : ((CapMode.access Mutability.ro).applyRO) = CapMode.access .ro := rfl
      rw [h_ro_eq, if_neg hro]
      exact Subset.empty

/-- `Subset` preserves `covers`: a larger capability set covers everything
    the smaller one does (at the same or stronger modes). -/
theorem covers_mono :
    ∀ {C C' : CapabilitySet}, C ⊆ C' → ∀ {mu l}, C.covers mu l → C'.covers mu l := by
  intro C C' hsub mu l hcov
  induction hsub with
  | refl => exact hcov
  | empty => cases hcov
  | trans _ _ ih1 ih2 => exact ih2 (ih1 hcov)
  | union_left _ _ ih1 ih2 =>
    cases hcov with
    | left h => exact ih1 h
    | right h => exact ih2 h
  | union_right_left => exact covers_union_left hcov
  | union_right_right => exact covers_union_right hcov
  | cap_ro =>
    cases hcov
    rename_i hle
    apply covers.here
    cases hle with
    | access hmu =>
      exact CapMode.Le.access (Mutability.Le.trans hmu Mutability.Le.ro_le)

/-- `intersect` is monotone in its second argument under `Subset`. Since
    `Subset` preserves `covers` (see `covers_mono`), widening the right side
    of intersection can only retain more caps from the left side. -/
theorem intersect_mono_right :
    ∀ {C D D' : CapabilitySet}, D ⊆ D' → C.intersect D ⊆ C.intersect D'
| .empty, _, _, _ => Subset.empty
| .cap mu l, D, D', hsub => by
    unfold intersect
    split
    · rename_i hcov
      have hcov_prop : D.covers mu l := coversCap_iff_covers.mp hcov
      have hcov_prop' : D'.covers mu l := covers_mono hsub hcov_prop
      rw [if_pos (coversCap_iff_covers.mpr hcov_prop')]
      exact Subset.refl
    · split
      · rename_i hcov_low
        have hcov_low_prop : D.covers mu.applyRO l := coversCap_iff_covers.mp hcov_low
        have hcov_low_prop' : D'.covers mu.applyRO l := covers_mono hsub hcov_low_prop
        split
        · exact cap_applyRO_subset_cap
        · rw [if_pos (coversCap_iff_covers.mpr hcov_low_prop')]
          exact Subset.refl
      · exact Subset.empty
| .union Ca Cb, D, D', hsub => by
    unfold intersect
    exact Subset.union_left
      (Subset.trans (intersect_mono_right (C := Ca) hsub) Subset.union_right_left)
      (Subset.trans (intersect_mono_right (C := Cb) hsub) Subset.union_right_right)

/-- A capability set has a certain mutability kind.
    `HasKind C .ro` means every cap in C is either `.access .ro` (immutable
    access) or `.drop` (exclusive — does not grant any read/write authority).
    `HasKind C .epsilon` is always true. -/
inductive HasKind : CapabilitySet -> Mutability -> Prop where
| eps :
  HasKind C .epsilon
| ro_empty :
  HasKind .empty .ro
| ro_cap :
  HasKind (.cap (.access .ro) l) .ro
| ro_drop :
  HasKind (.cap .drop l) .ro
| ro_union :
  HasKind C1 .ro ->
  HasKind C2 .ro ->
  HasKind (C1 ∪ C2) .ro

/-- applyRO always produces a capability set with kind .ro -/
theorem HasKind.applyRO {C : CapabilitySet} : C.applyRO.HasKind .ro := by
  induction C with
  | empty => exact HasKind.ro_empty
  | cap m _ =>
    cases m with
    | access _ => exact HasKind.ro_cap
    | drop => exact HasKind.ro_drop
  | union _ _ ih1 ih2 => exact HasKind.ro_union ih1 ih2

/-- Weakening: if C has kind m1 and m1 ≤ m2, then C has kind m2. -/
theorem HasKind.weaken {C : CapabilitySet} {m1 m2 : Mutability}
    (hkind : C.HasKind m1) (hle : m1 ≤ m2) : C.HasKind m2 := by
  cases hle with
  | refl => exact hkind
  | ro_eps => exact HasKind.eps

/-- Subset preserves HasKind .ro -/
theorem HasKind.subset_ro {C1 C2 : CapabilitySet}
    (hsub : C1 ⊆ C2) (hkind : C2.HasKind .ro) : C1.HasKind .ro := by
  induction hsub with
  | refl => exact hkind
  | empty => exact HasKind.ro_empty
  | trans _ _ ih1 ih2 => exact ih1 (ih2 hkind)
  | union_left _ _ ih1 ih2 => exact HasKind.ro_union (ih1 hkind) (ih2 hkind)
  | union_right_left =>
    cases hkind with
    | ro_union hk1 _ => exact hk1
  | union_right_right =>
    cases hkind with
    | ro_union _ hk2 => exact hk2
  | cap_ro => exact HasKind.ro_cap

/-- applyRO gives a subset: C.applyRO ⊆ C.applyMut m for any m. -/
theorem applyRO_subset_applyMut {C : CapabilitySet} {m : Mutability} :
  C.applyRO ⊆ C.applyMut m := by
  cases m
  case epsilon =>
    simp only [applyMut]
    induction C with
    | empty => exact Subset.refl
    | cap m' l =>
      cases m' with
      | access mu =>
        cases mu with
        | epsilon => exact Subset.cap_ro
        | ro => exact Subset.refl
      | drop => exact Subset.refl
    | union C1 C2 ih1 ih2 =>
      simp only [applyRO]
      exact Subset.union_left (Subset.trans ih1 Subset.union_right_left)
                               (Subset.trans ih2 Subset.union_right_right)
  case ro =>
    simp only [applyMut]
    exact Subset.refl

/-- applyRO is monotonic with respect to subset. -/
theorem applyRO_mono {C1 C2 : CapabilitySet} (hsub : C1 ⊆ C2) :
  C1.applyRO ⊆ C2.applyRO := by
  induction hsub with
  | refl => exact Subset.refl
  | empty => exact Subset.empty
  | trans _ _ ih1 ih2 => exact Subset.trans ih1 ih2
  | union_left _ _ ih1 ih2 =>
    simp only [applyRO]
    exact Subset.union_left ih1 ih2
  | union_right_left =>
    simp only [applyRO]
    exact Subset.union_right_left
  | union_right_right =>
    simp only [applyRO]
    exact Subset.union_right_right
  | cap_ro =>
    simp only [applyRO]
    exact Subset.refl

theorem subset_preserves_covers {C1 C2 : CapabilitySet} {m : CapMode} {x : Nat}
  (hsub : C1 ⊆ C2)
  (hcov : covers m x C1) :
  covers m x C2 := by
  induction hsub generalizing x m
  case refl => exact hcov
  case trans ih1 ih2 => exact ih2 (ih1 hcov)
  case empty => cases hcov
  case union_left ih1 ih2 =>
    cases hcov
    case left h => exact ih1 h
    case right h => exact ih2 h
  case union_right_left => exact covers.left hcov
  case union_right_right => exact covers.right hcov
  case cap_ro =>
    cases hcov
    case here hle =>
      cases hle with
      | access hmu =>
        cases hmu
        exact covers.here (.access Mutability.Le.ro_eps)

/-- If a capability set covers a location via an access cap, then the
    RO singleton is a subset of the set. -/
theorem covers_imp_singleton_subset {C : CapabilitySet} {m : Mutability} {x : Nat}
  (hcov : covers (.access m) x C) :
  {x} ⊆ C := by
  induction C with
  | empty => cases hcov
  | cap m' y =>
    cases hcov
    case here hle =>
      cases hle with
      | access hmu =>
        rename_i mu'
        cases mu' with
        | epsilon => exact Subset.cap_ro
        | ro =>
          cases hmu
          exact Subset.refl
  | union C1 C2 ih1 ih2 =>
    cases hcov with
    | left h =>
      apply Subset.trans (ih1 h)
      apply Subset.union_right_left
    | right h =>
      apply Subset.trans (ih2 h)
      apply Subset.union_right_right

/-- If a capability set covers a location with .epsilon access,
    then the epsilon singleton is a subset of the set. -/
theorem covers_eps_imp_singleton_eps_subset {C : CapabilitySet} {x : Nat}
  (hcov : covers (.access .epsilon) x C) :
  singleton .epsilon x ⊆ C := by
  induction C with
  | empty => cases hcov
  | cap m' y =>
    cases hcov
    case here hle =>
      cases hle with
      | access hmu => cases hmu; exact Subset.refl
  | union C1 C2 ih1 ih2 =>
    cases hcov with
    | left h =>
      apply Subset.trans (ih1 h)
      apply Subset.union_right_left
    | right h =>
      apply Subset.trans (ih2 h)
      apply Subset.union_right_right

/-- Inversion: a covered location must come from some explicit member with a
    weaker-or-equal mode. -/
theorem covers_imp_exists_hasmem
    {C : CapabilitySet} {m : CapMode} {l : Nat}
    (hcov : covers m l C) :
    ∃ m', hasmem m' l C ∧ m ≤ m' := by
  induction hcov with
  | here hle => exact ⟨_, hasmem.here, hle⟩
  | left _ ih =>
    obtain ⟨m', hm, hle⟩ := ih
    exact ⟨m', hasmem.left hm, hle⟩
  | right _ ih =>
    obtain ⟨m', hm, hle⟩ := ih
    exact ⟨m', hasmem.right hm, hle⟩

/-! ## Subset modulo a domain predicate

`SubsetMod P C1 C2` says: every element of `C1` whose location satisfies `P` is
covered by `C2`. Elements failing `P` are unconstrained.

Intended use: `P l := h l ≠ none` for a heap `h` — i.e., "C1 ⊆ C2 modulo what
is already allocated in h". This relaxation excuses freshly-allocated witnesses
that would otherwise break a strict reachability bound.
-/

/-- "C1 is a subset of C2 modulo predicate P". -/
def SubsetMod (P : Nat -> Prop) (C1 C2 : CapabilitySet) : Prop :=
  ∀ mu l, hasmem mu l C1 → P l → covers mu l C2

namespace SubsetMod

/-- Reflexivity. -/
theorem refl {P : Nat -> Prop} {C : CapabilitySet} : SubsetMod P C C := by
  intros mu l hm _
  exact hasmem_implies_covers hm

/-- Transitivity. -/
theorem trans {P : Nat -> Prop} {C1 C2 C3 : CapabilitySet}
    (h12 : SubsetMod P C1 C2) (h23 : SubsetMod P C2 C3) :
    SubsetMod P C1 C3 := by
  intros mu l hm hP
  obtain ⟨mu', hm', hle⟩ := covers_imp_exists_hasmem (h12 mu l hm hP)
  exact covers_weaken (h23 mu' l hm' hP) hle

/-- Strict subset implies subset modulo any predicate. -/
theorem of_subset {P : Nat -> Prop} {C1 C2 : CapabilitySet}
    (hsub : C1 ⊆ C2) : SubsetMod P C1 C2 := by
  intros mu l hm _
  exact subset_preserves_covers hsub (hasmem_implies_covers hm)

/-- Empty is below anything. -/
theorem empty {P : Nat -> Prop} {C : CapabilitySet} :
    SubsetMod P .empty C := by
  intros _ _ hm _
  cases hm

/-- Anti-monotonicity in the predicate: a stronger premise predicate makes the
    relation easier to satisfy. -/
theorem weaken_pred
    {P P' : Nat -> Prop} {C1 C2 : CapabilitySet}
    (himp : ∀ l, P l → P' l)
    (h : SubsetMod P' C1 C2) :
    SubsetMod P C1 C2 := by
  intros mu l hm hP
  exact h mu l hm (himp l hP)

/-- Right-side monotonicity via strict subset. -/
theorem mono_right {P : Nat -> Prop} {C1 C2 C2' : CapabilitySet}
    (h : SubsetMod P C1 C2) (hsub : C2 ⊆ C2') :
    SubsetMod P C1 C2' := by
  intros mu l hm hP
  exact subset_preserves_covers hsub (h mu l hm hP)

/-- Left-side anti-monotonicity via strict subset. -/
theorem mono_left {P : Nat -> Prop} {C1 C1' C2 : CapabilitySet}
    (hsub : C1' ⊆ C1) (h : SubsetMod P C1 C2) :
    SubsetMod P C1' C2 :=
  trans (of_subset hsub) h

/-- Union elimination on the left. -/
theorem union_elim_left {P : Nat -> Prop} {C1 C2 C : CapabilitySet}
    (h : SubsetMod P (C1 ∪ C2) C) : SubsetMod P C1 C := by
  intros mu l hm hP
  exact h mu l (hasmem_union_left hm) hP

/-- Union elimination on the right. -/
theorem union_elim_right {P : Nat -> Prop} {C1 C2 C : CapabilitySet}
    (h : SubsetMod P (C1 ∪ C2) C) : SubsetMod P C2 C := by
  intros mu l hm hP
  exact h mu l (hasmem_union_right hm) hP

/-- Union introduction. -/
theorem union_intro {P : Nat -> Prop} {C1 C2 C : CapabilitySet}
    (h1 : SubsetMod P C1 C) (h2 : SubsetMod P C2 C) :
    SubsetMod P (C1 ∪ C2) C := by
  intros mu l hm hP
  cases hasmem_union_iff.mp hm with
  | inl hm1 => exact h1 mu l hm1 hP
  | inr hm2 => exact h2 mu l hm2 hP

/-- Iff-style union split. -/
theorem union_iff {P : Nat -> Prop} {C1 C2 C : CapabilitySet} :
    SubsetMod P (C1 ∪ C2) C ↔ SubsetMod P C1 C ∧ SubsetMod P C2 C :=
  ⟨fun h => ⟨union_elim_left h, union_elim_right h⟩,
   fun ⟨h1, h2⟩ => union_intro h1 h2⟩

/-- Right-side injection into a union. -/
theorem union_right_left {P : Nat -> Prop} {C1 C2 : CapabilitySet} :
    SubsetMod P C1 (C1 ∪ C2) :=
  of_subset Subset.union_right_left

/-- Right-side injection into a union (other side). -/
theorem union_right_right {P : Nat -> Prop} {C1 C2 : CapabilitySet} :
    SubsetMod P C1 (C2 ∪ C1) :=
  of_subset Subset.union_right_right

/-- Vacuity: if every member of `C1` fails `P`, then `C1 ⊆ C2 mod P` for any
    `C2`. This is the load-bearing lemma — it's how a freshly-allocated witness
    (where `P l = h l ≠ none` and `l` is fresh) trivially fits inside any budget. -/
theorem vacuous {P : Nat -> Prop} {C1 C2 : CapabilitySet}
    (hfresh : ∀ mu l, hasmem mu l C1 → ¬ P l) :
    SubsetMod P C1 C2 := by
  intros mu l hm hP
  exact (hfresh mu l hm hP).elim

/-- Compatibility with `applyRO` on both sides. -/
theorem applyRO {P : Nat -> Prop} {C1 C2 : CapabilitySet}
    (h : SubsetMod P C1 C2) :
    SubsetMod P C1.applyRO C2.applyRO := by
  intros mu l hm hP
  rw [hasmem_applyRO_iff] at hm
  obtain ⟨mu', hmu, hm'⟩ := hm
  subst hmu
  have hcov : covers mu' l C2 := h mu' l hm' hP
  have hcov_ro : covers mu'.applyRO l C2 :=
    covers_weaken hcov CapMode.applyRO_le
  exact covers_applyRO_of_covers hcov_ro CapMode.applyRO_idempotent.symm

end SubsetMod

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
  | .consumer _ _ _, .consumer => .consumer
  | .boxed _ _ _, .boxed => .boxed
  | .reader _, .reader => .reader
  | .unit, .unit => .unit
  | .btrue, .btrue => .btrue
  | .bfalse, .bfalse => .bfalse

inductive Liveness : Type where
| live : Liveness
| dead : Liveness

namespace Liveness

/-- Forward lifecycle order: a cell can transition from live to dead but never
    back.  `Le ℓ_old ℓ_new` means `ℓ_old` may evolve into `ℓ_new` as time
    advances.  This is the liveness component of memory subsumption. -/
inductive Le : Liveness → Liveness → Prop where
| refl {ℓ : Liveness} : Le ℓ ℓ
| live_dead : Le .live .dead

instance instLE : LE Liveness := ⟨Liveness.Le⟩

theorem Le.trans {ℓ1 ℓ2 ℓ3 : Liveness} (h1 : ℓ1 ≤ ℓ2) (h2 : ℓ2 ≤ ℓ3) : ℓ1 ≤ ℓ3 := by
  cases h1 with
  | refl => exact h2
  | live_dead => cases h2; exact .live_dead

end Liveness

/-- Underlying info of a capability. -/
inductive CapabilityInfo : Type where
| basic : CapabilityInfo
| mcell : Nat -> Liveness -> CapabilityInfo

/-- A heap cell. -/
inductive Cell : Type where
| val : HeapVal -> Cell
| capability : CapabilityInfo -> Cell
| masked : Cell

def Heap : Type := Nat -> Option Cell

def Heap.empty : Heap := fun _ => none

instance Heap.instEmptyCollection : EmptyCollection Heap := ⟨Heap.empty⟩

def Heap.extend (h : Heap) (l : Nat) (v : HeapVal) : Heap :=
  fun l' => if l' = l then some (.val v) else h l'

def Heap.extend_cap (h : Heap) (l : Nat) : Heap :=
  fun l' => if l' = l then some (.capability .basic) else h l'

/-- Heap extension with a fresh mutable cell capability.  Fresh cells start `.live`. -/
def Heap.extend_mcell (h : Heap) (l : Nat) (n : Nat) : Heap :=
  fun l' => if l' = l then some (.capability (.mcell n .live)) else h l'

/-- Update a cell in the heap with a new cell value. -/
def Heap.update_cell (h : Heap) (l : Nat) (c : Cell) : Heap :=
  fun l' => if l' = l then some c else h l'

/-- Auxiliary relation: one cell subsumes another.
    For mutable cells, the stored location is irrelevant and liveness is allowed
    to advance forward in time (live → dead) but never to be resurrected
    (dead ↛ live).  Subsumption is the "memory in the future" relation. -/
def Cell.subsumes : Cell -> Cell -> Prop
| .capability (.mcell _ ℓ1), .capability (.mcell _ ℓ2) => ℓ2 ≤ ℓ1
| c1, c2 => c1 = c2

theorem Cell.subsumes_refl (c : Cell) : c.subsumes c := by
  cases c with
  | val _ => rfl
  | capability info =>
    cases info with
    | basic => rfl
    | mcell _ _ => exact Liveness.Le.refl
  | masked => rfl

theorem Cell.subsumes_trans {c1 c2 c3 : Cell}
  (h12 : c1.subsumes c2) (h23 : c2.subsumes c3) : c1.subsumes c3 := by
  cases c1 <;> cases c2 <;> cases c3
  all_goals
    try simp only [Cell.subsumes] at h12 h23 ⊢
  case capability.capability.capability info1 info2 info3 =>
    cases info1 <;> cases info2 <;> cases info3 <;>
      simp only at h12 h23 ⊢
    case basic.basic.mcell _ _ => exact h23
    case basic.mcell.mcell _ _ _ _ => cases h12
    case mcell.basic.basic _ _ => cases h12
    case mcell.basic.mcell _ _ _ _ => cases h12
    case mcell.mcell.basic _ _ _ _ => cases h23
    case mcell.mcell.mcell _ _ _ _ _ _ => exact Liveness.Le.trans h23 h12
  all_goals aesop

def Heap.subsumes (big small : Heap) : Prop :=
  ∀ l v, small l = some v -> ∃ v', big l = some v' ∧ v'.subsumes v

theorem Heap.subsumes_refl (h : Heap) : h.subsumes h := by
  intros l v hlookup
  exists v
  constructor
  · exact hlookup
  · exact Cell.subsumes_refl v

/-- Subsumption preserves "is fresh" backwards: if a location is unallocated
    in the larger heap, it is unallocated in the smaller heap as well. -/
theorem Heap.none_of_subsumes_none {big small : Heap} {l : Nat}
    (hsub : big.subsumes small) (hnone : big l = none) : small l = none := by
  match hopt : small l with
  | none => rfl
  | some v =>
    obtain ⟨_, hv', _⟩ := hsub l v hopt
    rw [hnone] at hv'
    cases hv'

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

/-- Updating an mcell with another mcell creates a heap that subsumes the original.
    Liveness is preserved by the update. -/
theorem Heap.update_mcell_subsumes (h : Heap) (l : Nat) (ℓ : Liveness)
  (hexists : ∃ n0, h l = some (.capability (.mcell n0 ℓ))) (n : Nat) :
  (h.update_cell l (.capability (.mcell n ℓ))).subsumes h := by
  intro l' v hlookup
  unfold Heap.update_cell
  split
  case isTrue heq =>
    subst heq
    obtain ⟨n0, hn0⟩ := hexists
    rw [hn0] at hlookup
    cases hlookup
    exact ⟨.capability (.mcell n ℓ), rfl, Liveness.Le.refl⟩
  case isFalse hneq =>
    exact ⟨v, hlookup, Cell.subsumes_refl v⟩

theorem Heap.extend_lookup_eq
  (h : Heap) (l : Nat) (v : HeapVal) :
  (h.extend l v) l = some (.val v) := by
  simp only [Heap.extend, if_true]

theorem Heap.extend_subsumes {H : Heap} {l : Nat}
  (hfresh : H l = none) :
  (H.extend l v).subsumes H := by
  intro l' v' hlookup
  unfold Heap.extend
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
  CaptureSet.WfInHeap (CaptureSet.var m (.free x)) H
| wf_var_bound :
  CaptureSet.WfInHeap (CaptureSet.var m (.bound x)) H
| wf_cvar :
  CaptureSet.WfInHeap (CaptureSet.cvar m x) H

inductive Var.WfInHeap : Var k s -> Heap -> Prop where
| wf_bound :
  Var.WfInHeap (.bound x) H
| wf_free :
  H n = some val ->
  Var.WfInHeap (.free n) H

inductive SepCtx.WfInHeap : SepCtx s -> Heap -> Prop where
| wf_empty :
  SepCtx.WfInHeap .empty H
| wf_cons :
  SepCtx.WfInHeap Ψ H ->
  CaptureSet.WfInHeap C H ->
  SepCtx.WfInHeap (.cons Ψ C) H

inductive MutabilityCtx.WfInHeap : MutabilityCtx s -> Heap -> Prop where
| wf_empty :
  MutabilityCtx.WfInHeap .empty H
| wf_cons :
  MutabilityCtx.WfInHeap Ψ H ->
  CaptureSet.WfInHeap C H ->
  MutabilityCtx.WfInHeap (.cons Ψ C m) H

structure ModalCtx.WfInHeap (Ψ : ModalCtx s) (H : Heap) : Prop where
  sep : Ψ.sep.WfInHeap H
  mutability : Ψ.mutability.WfInHeap H

inductive CaptureBound.WfInHeap : CaptureBound s -> Heap -> Prop where
| wf_unbound :
  CaptureBound.WfInHeap .unbound H
| wf_bound :
  CaptureSet.WfInHeap cs H ->
  CaptureBound.WfInHeap (.bound cs) H

inductive Ty.WfInHeap : Ty sort s -> Heap -> Prop where
| wf_top :
  Ty.WfInHeap .top H
| wf_tvar :
  Ty.WfInHeap (.tvar x) H
| wf_arrow :
  Ty.WfInHeap T1 H ->
  CaptureSet.WfInHeap cs H ->
  Ty.WfInHeap T2 H ->
  Ty.WfInHeap (.arrow T1 cs T2) H
| wf_poly :
  Ty.WfInHeap T1 H ->
  CaptureSet.WfInHeap cs H ->
  Ty.WfInHeap T2 H ->
  Ty.WfInHeap (.poly T1 cs T2) H
| wf_cpoly :
  CaptureBound.WfInHeap cb H ->
  CaptureSet.WfInHeap cs H ->
  Ty.WfInHeap T H ->
  Ty.WfInHeap (.cpoly cb cs T) H
| wf_consumer :
  Ty.WfInHeap T1 H ->
  CaptureSet.WfInHeap cs H ->
  Ty.WfInHeap T2 H ->
  Ty.WfInHeap (.consumer T1 cs T2) H
| wf_modal :
  CaptureSet.WfInHeap cs H ->
  ModalCtx.WfInHeap Ψ H ->
  Ty.WfInHeap T H ->
  Ty.WfInHeap (.modal cs Ψ T) H
| wf_unit :
  Ty.WfInHeap .unit H
| wf_cap :
  CaptureSet.WfInHeap cs H ->
  Ty.WfInHeap (.cap cs) H
| wf_bool :
  Ty.WfInHeap .bool H
| wf_cell :
  CaptureSet.WfInHeap cs H ->
  Ty.WfInHeap T H ->
  Ty.WfInHeap (.cell cs T) H
| wf_reader :
  CaptureSet.WfInHeap cs H ->
  Ty.WfInHeap T H ->
  Ty.WfInHeap (.reader cs T) H
-- Existential types
| wf_exi {s : Sig} {n : Nat} {T : Ty .capt (s.extendCVars n)} {H : Heap} :
  Ty.WfInHeap T H ->
  Ty.WfInHeap (.exi n T) H
| wf_typ :
  Ty.WfInHeap T H ->
  Ty.WfInHeap (.typ T) H

def PureTy.WfInHeap (T : PureTy s) (H : Heap) : Prop :=
  Ty.WfInHeap T.core H

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
  PureTy.WfInHeap T H ->
  Exp.WfInHeap e H ->
  Exp.WfInHeap (.tabs cs T e) H
| wf_cabs :
  CaptureSet.WfInHeap cs H ->
  CaptureBound.WfInHeap cb H ->
  Exp.WfInHeap e H ->
  Exp.WfInHeap (.cabs cs cb e) H
| wf_consumer :
  CaptureSet.WfInHeap cs H ->
  Ty.WfInHeap T H ->
  Exp.WfInHeap e H ->
  Exp.WfInHeap (.consumer cs T e) H
| wf_boxed :
  CaptureSet.WfInHeap cs H ->
  ModalCtx.WfInHeap Ψ H ->
  Exp.WfInHeap e H ->
  Exp.WfInHeap (.boxed cs Ψ e) H
| wf_reader :
  Var.WfInHeap x H ->
  Exp.WfInHeap (.reader x) H
| wf_alloc :
  Var.WfInHeap x H ->
  Exp.WfInHeap (.alloc x) H
| wf_drop :
  Var.WfInHeap x H ->
  Exp.WfInHeap (.drop x) H
| wf_pack {s : Sig} {n : Nat} {css : List.Vector (CaptureSet s) n} {x : Var .var s} {H : Heap} :
  (∀ cs ∈ css.toList, CaptureSet.WfInHeap cs H) ->
  Var.WfInHeap x H ->
  Exp.WfInHeap (.pack css x) H
| wf_app :
  Var.WfInHeap x H ->
  Var.WfInHeap y H ->
  Exp.WfInHeap (.app x y) H
| wf_tapp :
  Var.WfInHeap x H ->
  PureTy.WfInHeap T H ->
  Exp.WfInHeap (.tapp x T) H
| wf_capp :
  Var.WfInHeap x H ->
  CaptureSet.WfInHeap cs H ->
  Exp.WfInHeap (.capp x cs) H
| wf_consumer_app :
  Var.WfInHeap x H ->
  Exp.WfInHeap e H ->
  Exp.WfInHeap (.consumer_app x e) H
| wf_unwrap :
  Var.WfInHeap x H ->
  Exp.WfInHeap (.unwrap x) H
| wf_letin :
  Exp.WfInHeap e1 H ->
  Exp.WfInHeap e2 H ->
  Exp.WfInHeap (.letin e1 e2) H
| wf_unpack {s : Sig} {n : Nat} {e1 : Exp s} {e2 : Exp ((s.extendCVars n),x)} {H : Heap} :
  Exp.WfInHeap e1 H ->
  Exp.WfInHeap e2 H ->
  Exp.WfInHeap (.unpack n e1 e2) H
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
| wf_par :
  CaptureSet.WfInHeap C1 H ->
  CaptureSet.WfInHeap C2 H ->
  Exp.WfInHeap e1 H ->
  Exp.WfInHeap e2 H ->
  Exp.WfInHeap (.par C1 C2 e1 e2) H

-- Closedness implies well-formedness in any heap

/-- Closedness implies well-formedness for variables. -/
theorem Var.wf_of_closed {x : Var k s} {H : Heap}
  (hclosed : x.IsClosed) :
  Var.WfInHeap x H := by
  cases hclosed
  exact Var.WfInHeap.wf_bound

/-- Closedness implies well-formedness for capture sets. -/
theorem CaptureSet.wf_of_closed {cs : CaptureSet s} {H : Heap}
  (hclosed : cs.IsClosed) :
  CaptureSet.WfInHeap cs H := by
  induction hclosed with
  | empty => exact CaptureSet.WfInHeap.wf_empty
  | union _ _ ih1 ih2 => exact CaptureSet.WfInHeap.wf_union ih1 ih2
  | cvar => exact CaptureSet.WfInHeap.wf_cvar
  | var_bound => exact CaptureSet.WfInHeap.wf_var_bound

theorem SepCtx.wf_of_closed {Ψ : SepCtx s} {H : Heap}
  (hclosed : Ψ.IsClosed) :
  SepCtx.WfInHeap Ψ H := by
  induction hclosed with
  | empty => exact SepCtx.WfInHeap.wf_empty
  | cons hΨ hC ih => exact SepCtx.WfInHeap.wf_cons ih (CaptureSet.wf_of_closed hC)

theorem MutabilityCtx.wf_of_closed {Ψ : MutabilityCtx s} {H : Heap}
  (hclosed : Ψ.IsClosed) :
  MutabilityCtx.WfInHeap Ψ H := by
  induction hclosed with
  | empty => exact MutabilityCtx.WfInHeap.wf_empty
  | cons hΨ hC ih => exact MutabilityCtx.WfInHeap.wf_cons ih (CaptureSet.wf_of_closed hC)

theorem ModalCtx.wf_of_closed {Ψ : ModalCtx s} {H : Heap}
  (hclosed : Ψ.IsClosed) :
  ModalCtx.WfInHeap Ψ H :=
  ⟨SepCtx.wf_of_closed hclosed.sep, MutabilityCtx.wf_of_closed hclosed.mutability⟩

theorem CaptureBound.wf_of_closed {cb : CaptureBound s} {H : Heap}
  (hclosed : cb.IsClosed) :
  CaptureBound.WfInHeap cb H := by
  cases hclosed with
  | unbound => exact CaptureBound.WfInHeap.wf_unbound
  | bound hcs => exact CaptureBound.WfInHeap.wf_bound (CaptureSet.wf_of_closed hcs)

/-- Closedness implies well-formedness for types. -/
theorem Ty.wf_of_closed {T : Ty sort s} {H : Heap}
  (hclosed : T.IsClosed) :
  Ty.WfInHeap T H := by
  induction hclosed with
  | top => exact Ty.WfInHeap.wf_top
  | tvar => exact Ty.WfInHeap.wf_tvar
  | unit => exact Ty.WfInHeap.wf_unit
  | bool => exact Ty.WfInHeap.wf_bool
  | arrow _ hcs _ ih1 ih2 =>
    exact Ty.WfInHeap.wf_arrow ih1 (CaptureSet.wf_of_closed hcs) ih2
  | poly _ hcs _ ih1 ih2 =>
    exact Ty.WfInHeap.wf_poly ih1 (CaptureSet.wf_of_closed hcs) ih2
  | cpoly hcb hcs _ ih =>
    exact Ty.WfInHeap.wf_cpoly (CaptureBound.wf_of_closed hcb)
      (CaptureSet.wf_of_closed hcs) ih
  | consumer _ hcs _ ih1 ih2 =>
    exact Ty.WfInHeap.wf_consumer ih1 (CaptureSet.wf_of_closed hcs) ih2
  | modal hcs hΨ _ ih =>
    exact Ty.WfInHeap.wf_modal (CaptureSet.wf_of_closed hcs)
      (ModalCtx.wf_of_closed hΨ) ih
  | cap hcs => exact Ty.WfInHeap.wf_cap (CaptureSet.wf_of_closed hcs)
  | cell hcs _ ih => exact Ty.WfInHeap.wf_cell (CaptureSet.wf_of_closed hcs) ih
  | reader hcs _ ih => exact Ty.WfInHeap.wf_reader (CaptureSet.wf_of_closed hcs) ih
  | exi _ ih => exact Ty.WfInHeap.wf_exi ih
  | typ _ ih => exact Ty.WfInHeap.wf_typ ih

/-- Closedness implies well-formedness for expressions. -/
theorem Exp.wf_of_closed {e : Exp s} {H : Heap}
  (hclosed : e.IsClosed) :
  Exp.WfInHeap e H := by
  induction hclosed with
  | unit => exact Exp.WfInHeap.wf_unit
  | btrue => exact Exp.WfInHeap.wf_btrue
  | bfalse => exact Exp.WfInHeap.wf_bfalse
  | var hx => exact Exp.WfInHeap.wf_var (Var.wf_of_closed hx)
  | reader hx => exact Exp.WfInHeap.wf_reader (Var.wf_of_closed hx)
  | alloc hx => exact Exp.WfInHeap.wf_alloc (Var.wf_of_closed hx)
  | drop hx => exact Exp.WfInHeap.wf_drop (Var.wf_of_closed hx)
  | unwrap hx => exact Exp.WfInHeap.wf_unwrap (Var.wf_of_closed hx)
  | read hx => exact Exp.WfInHeap.wf_read (Var.wf_of_closed hx)
  | abs hcs hT _ ih =>
    exact Exp.WfInHeap.wf_abs (CaptureSet.wf_of_closed hcs) (Ty.wf_of_closed hT) ih
  | tabs hcs hT _ ih =>
    exact Exp.WfInHeap.wf_tabs (CaptureSet.wf_of_closed hcs) (Ty.wf_of_closed hT) ih
  | cabs hcs hcb _ ih =>
    exact Exp.WfInHeap.wf_cabs
      (CaptureSet.wf_of_closed hcs) (CaptureBound.wf_of_closed hcb) ih
  | consumer hcs hT _ ih =>
    exact Exp.WfInHeap.wf_consumer
      (CaptureSet.wf_of_closed hcs) (Ty.wf_of_closed hT) ih
  | boxed hcs hΨ _ ih =>
    exact Exp.WfInHeap.wf_boxed (CaptureSet.wf_of_closed hcs) (ModalCtx.wf_of_closed hΨ) ih
  | pack hcs hx =>
    exact Exp.WfInHeap.wf_pack
      (fun cs hmem => CaptureSet.wf_of_closed (hcs cs hmem)) (Var.wf_of_closed hx)
  | app hx hy =>
    exact Exp.WfInHeap.wf_app (Var.wf_of_closed hx) (Var.wf_of_closed hy)
  | tapp hx hT =>
    exact Exp.WfInHeap.wf_tapp (Var.wf_of_closed hx) (Ty.wf_of_closed hT)
  | capp hx hcs =>
    exact Exp.WfInHeap.wf_capp (Var.wf_of_closed hx) (CaptureSet.wf_of_closed hcs)
  | consumer_app hx _ ih =>
    exact Exp.WfInHeap.wf_consumer_app (Var.wf_of_closed hx) ih
  | write hx hy =>
    exact Exp.WfInHeap.wf_write (Var.wf_of_closed hx) (Var.wf_of_closed hy)
  | letin _ _ ih1 ih2 => exact Exp.WfInHeap.wf_letin ih1 ih2
  | unpack _ _ ih1 ih2 => exact Exp.WfInHeap.wf_unpack ih1 ih2
  | par hc1 hc2 _ _ ih1 ih2 =>
    exact Exp.WfInHeap.wf_par (CaptureSet.wf_of_closed hc1) (CaptureSet.wf_of_closed hc2) ih1 ih2
  | cond hx _ _ ih2 ih3 =>
    exact Exp.WfInHeap.wf_cond (Var.wf_of_closed hx) ih2 ih3

-- Monotonicity theorems: WfInHeap is preserved under heap subsumption

theorem Var.wf_monotonic
  {h1 h2 : Heap}
  (hsub : h2.subsumes h1)
  (hwf : Var.WfInHeap x h1) :
  Var.WfInHeap x h2 := by
  cases hwf with
  | wf_bound => exact Var.WfInHeap.wf_bound
  | wf_free hex =>
    obtain ⟨v', hv', _⟩ := hsub _ _ hex
    exact Var.WfInHeap.wf_free hv'

theorem CaptureSet.wf_monotonic
  {h1 h2 : Heap}
  (hsub : h2.subsumes h1)
  (hwf : CaptureSet.WfInHeap cs h1) :
  CaptureSet.WfInHeap cs h2 := by
  induction hwf with
  | wf_empty => exact CaptureSet.WfInHeap.wf_empty
  | wf_var_bound => exact CaptureSet.WfInHeap.wf_var_bound
  | wf_cvar => exact CaptureSet.WfInHeap.wf_cvar
  | wf_union _ _ ih1 ih2 => exact CaptureSet.WfInHeap.wf_union (ih1 hsub) (ih2 hsub)
  | wf_var_free hex =>
    obtain ⟨v', hv', _⟩ := hsub _ _ hex
    exact CaptureSet.WfInHeap.wf_var_free hv'

theorem SepCtx.wf_monotonic
  {h1 h2 : Heap}
  (hsub : h2.subsumes h1)
  (hwf : SepCtx.WfInHeap Ψ h1) :
  SepCtx.WfInHeap Ψ h2 := by
  induction hwf with
  | wf_empty => exact SepCtx.WfInHeap.wf_empty
  | wf_cons hwf_Ψ hwf_C ih =>
    exact SepCtx.WfInHeap.wf_cons (ih hsub) (CaptureSet.wf_monotonic hsub hwf_C)

theorem MutabilityCtx.wf_monotonic
  {h1 h2 : Heap}
  (hsub : h2.subsumes h1)
  (hwf : MutabilityCtx.WfInHeap Ψ h1) :
  MutabilityCtx.WfInHeap Ψ h2 := by
  induction hwf with
  | wf_empty => exact MutabilityCtx.WfInHeap.wf_empty
  | wf_cons hwf_Ψ hwf_C ih =>
    exact MutabilityCtx.WfInHeap.wf_cons (ih hsub) (CaptureSet.wf_monotonic hsub hwf_C)

theorem ModalCtx.wf_monotonic
  {h1 h2 : Heap}
  (hsub : h2.subsumes h1)
  (hwf : ModalCtx.WfInHeap Ψ h1) :
  ModalCtx.WfInHeap Ψ h2 :=
  ⟨SepCtx.wf_monotonic hsub hwf.sep, MutabilityCtx.wf_monotonic hsub hwf.mutability⟩

theorem CaptureBound.wf_monotonic
  {h1 h2 : Heap}
  (hsub : h2.subsumes h1)
  (hwf : CaptureBound.WfInHeap cb h1) :
  CaptureBound.WfInHeap cb h2 := by
  cases hwf with
  | wf_unbound => exact CaptureBound.WfInHeap.wf_unbound
  | wf_bound hwf_cs => exact CaptureBound.WfInHeap.wf_bound (CaptureSet.wf_monotonic hsub hwf_cs)

theorem Ty.wf_monotonic
  {h1 h2 : Heap}
  (hsub : h2.subsumes h1)
  (hwf : Ty.WfInHeap T h1) :
  Ty.WfInHeap T h2 := by
  induction hwf generalizing h2 with
  | wf_top => exact Ty.WfInHeap.wf_top
  | wf_tvar => exact Ty.WfInHeap.wf_tvar
  | wf_unit => exact Ty.WfInHeap.wf_unit
  | wf_bool => exact Ty.WfInHeap.wf_bool
  | wf_arrow _ hwf_cs _ ih1 ih2 =>
    exact Ty.WfInHeap.wf_arrow (ih1 hsub)
      (CaptureSet.wf_monotonic hsub hwf_cs) (ih2 hsub)
  | wf_poly _ hwf_cs _ ih1 ih2 =>
    exact Ty.WfInHeap.wf_poly (ih1 hsub)
      (CaptureSet.wf_monotonic hsub hwf_cs) (ih2 hsub)
  | wf_cpoly hwf_cb hwf_cs _ ih_T =>
    exact Ty.WfInHeap.wf_cpoly
      (CaptureBound.wf_monotonic hsub hwf_cb)
      (CaptureSet.wf_monotonic hsub hwf_cs) (ih_T hsub)
  | wf_consumer _ hwf_cs _ ih1 ih2 =>
    exact Ty.WfInHeap.wf_consumer
      (ih1 hsub) (CaptureSet.wf_monotonic hsub hwf_cs) (ih2 hsub)
  | wf_modal hwf_cs hwf_Ψ _ ih_T =>
    exact Ty.WfInHeap.wf_modal
      (CaptureSet.wf_monotonic hsub hwf_cs)
      (ModalCtx.wf_monotonic hsub hwf_Ψ) (ih_T hsub)
  | wf_cap hwf_cs => exact Ty.WfInHeap.wf_cap (CaptureSet.wf_monotonic hsub hwf_cs)
  | wf_cell hwf_cs _ ih_T =>
    exact Ty.WfInHeap.wf_cell (CaptureSet.wf_monotonic hsub hwf_cs) (ih_T hsub)
  | wf_reader hwf_cs _ ih_T =>
    exact Ty.WfInHeap.wf_reader (CaptureSet.wf_monotonic hsub hwf_cs) (ih_T hsub)
  | wf_exi _ ih => exact Ty.WfInHeap.wf_exi (ih hsub)
  | wf_typ _ ih => exact Ty.WfInHeap.wf_typ (ih hsub)

theorem Exp.wf_monotonic
  {h1 h2 : Heap}
  (hsub : h2.subsumes h1)
  (hwf : Exp.WfInHeap e h1) :
  Exp.WfInHeap e h2 := by
  induction hwf generalizing h2 with
  | wf_unit => exact Exp.WfInHeap.wf_unit
  | wf_btrue => exact Exp.WfInHeap.wf_btrue
  | wf_bfalse => exact Exp.WfInHeap.wf_bfalse
  | wf_var hwf_x => exact Exp.WfInHeap.wf_var (Var.wf_monotonic hsub hwf_x)
  | wf_reader hwf_x => exact Exp.WfInHeap.wf_reader (Var.wf_monotonic hsub hwf_x)
  | wf_alloc hwf_x => exact Exp.WfInHeap.wf_alloc (Var.wf_monotonic hsub hwf_x)
  | wf_drop hwf_x => exact Exp.WfInHeap.wf_drop (Var.wf_monotonic hsub hwf_x)
  | wf_unwrap hwf_x => exact Exp.WfInHeap.wf_unwrap (Var.wf_monotonic hsub hwf_x)
  | wf_read hwf_x => exact Exp.WfInHeap.wf_read (Var.wf_monotonic hsub hwf_x)
  | wf_abs hwf_cs hwf_T _ ih_e =>
    exact Exp.WfInHeap.wf_abs
      (CaptureSet.wf_monotonic hsub hwf_cs) (Ty.wf_monotonic hsub hwf_T) (ih_e hsub)
  | wf_tabs hwf_cs hwf_T _ ih_e =>
    exact Exp.WfInHeap.wf_tabs
      (CaptureSet.wf_monotonic hsub hwf_cs) (Ty.wf_monotonic hsub hwf_T) (ih_e hsub)
  | wf_cabs hwf_cs hwf_cb _ ih_e =>
    exact Exp.WfInHeap.wf_cabs
      (CaptureSet.wf_monotonic hsub hwf_cs) (CaptureBound.wf_monotonic hsub hwf_cb) (ih_e hsub)
  | wf_consumer hwf_cs hwf_T _ ih_e =>
    exact Exp.WfInHeap.wf_consumer
      (CaptureSet.wf_monotonic hsub hwf_cs) (Ty.wf_monotonic hsub hwf_T) (ih_e hsub)
  | wf_boxed hwf_cs hwf_Ψ _ ih_e =>
    exact Exp.WfInHeap.wf_boxed
      (CaptureSet.wf_monotonic hsub hwf_cs) (ModalCtx.wf_monotonic hsub hwf_Ψ) (ih_e hsub)
  | wf_pack hwf_cs hwf_x =>
    exact Exp.WfInHeap.wf_pack
      (fun cs hmem => CaptureSet.wf_monotonic hsub (hwf_cs cs hmem))
      (Var.wf_monotonic hsub hwf_x)
  | wf_app hwf_x hwf_y =>
    exact Exp.WfInHeap.wf_app (Var.wf_monotonic hsub hwf_x) (Var.wf_monotonic hsub hwf_y)
  | wf_tapp hwf_x hwf_T =>
    exact Exp.WfInHeap.wf_tapp (Var.wf_monotonic hsub hwf_x) (Ty.wf_monotonic hsub hwf_T)
  | wf_capp hwf_x hwf_cs =>
    exact Exp.WfInHeap.wf_capp (Var.wf_monotonic hsub hwf_x) (CaptureSet.wf_monotonic hsub hwf_cs)
  | wf_consumer_app hwf_x _ ih_e =>
    exact Exp.WfInHeap.wf_consumer_app (Var.wf_monotonic hsub hwf_x) (ih_e hsub)
  | wf_write hwf_x hwf_y =>
    exact Exp.WfInHeap.wf_write (Var.wf_monotonic hsub hwf_x) (Var.wf_monotonic hsub hwf_y)
  | wf_letin _ _ ih1 ih2 => exact Exp.WfInHeap.wf_letin (ih1 hsub) (ih2 hsub)
  | wf_unpack _ _ ih1 ih2 => exact Exp.WfInHeap.wf_unpack (ih1 hsub) (ih2 hsub)
  | wf_par hwf_C1 hwf_C2 _ _ ih1 ih2 =>
    exact Exp.WfInHeap.wf_par (CaptureSet.wf_monotonic hsub hwf_C1)
      (CaptureSet.wf_monotonic hsub hwf_C2) (ih1 hsub) (ih2 hsub)
  | wf_cond hwf_x _ _ ih2 ih3 =>
    exact Exp.WfInHeap.wf_cond (Var.wf_monotonic hsub hwf_x) (ih2 hsub) (ih3 hsub)

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
  {n : Nat} {e1 : Exp s} {e2 : Exp ((s.extendCVars n),x)} {H : Heap}
  (hwf : Exp.WfInHeap (.unpack n e1 e2) H) :
  Exp.WfInHeap e1 H ∧ Exp.WfInHeap e2 H := by
  cases hwf with
  | wf_unpack hwf1 hwf2 => exact ⟨hwf1, hwf2⟩

/-- Inversion for parallel composition: if `par e1 e2` is well-formed, so are both. -/
theorem Exp.wf_inv_par
  {C1 C2 : CaptureSet s} {e1 e2 : Exp s} {H : Heap}
  (hwf : Exp.WfInHeap (.par C1 C2 e1 e2) H) :
  Exp.WfInHeap e1 H ∧ Exp.WfInHeap e2 H := by
  cases hwf with
  | wf_par _ _ hwf1 hwf2 => exact ⟨hwf1, hwf2⟩

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
  {cs : CaptureSet s} {T : PureTy s} {e : Exp (s,X)} {H : Heap}
  (hwf : Exp.WfInHeap (.tabs cs T e) H) :
  CaptureSet.WfInHeap cs H ∧ PureTy.WfInHeap T H ∧ Exp.WfInHeap e H := by
  cases hwf with
  | wf_tabs hwf_cs hwf_T hwf_e => exact ⟨hwf_cs, hwf_T, hwf_e⟩

/-- Inversion for capture abstraction. -/
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
    ∀ X, PureTy.WfInHeap (s.tvar X) H

  wf_cvar :
    ∀ C, CaptureSet.WfInHeap (s.cvar C) H

/-! ## Domain-only heap subsumption

`Heap.dom_subsumes big small` asserts that `big`'s domain covers `small`'s,
without constraining the cell contents.  This is strictly weaker than
`Heap.subsumes` and is preserved by `drop_mcell` (which alters cell content
but not the domain).  All `WfInHeap` predicates only inspect heap domains, so
they propagate along `dom_subsumes`. -/

def Heap.dom_subsumes (big small : Heap) : Prop :=
  ∀ l v, small l = some v → ∃ v', big l = some v'

theorem Heap.subsumes.dom_subsumes {big small : Heap}
    (h : big.subsumes small) : big.dom_subsumes small :=
  fun l v hv => let ⟨v', hv', _⟩ := h l v hv; ⟨v', hv'⟩

theorem Var.wf_dom_subsumes {h1 h2 : Heap}
    (hsub : h2.dom_subsumes h1) (hwf : Var.WfInHeap x h1) : Var.WfInHeap x h2 := by
  cases hwf with
  | wf_bound => exact .wf_bound
  | wf_free hex => obtain ⟨_, hv'⟩ := hsub _ _ hex; exact .wf_free hv'

theorem CaptureSet.wf_dom_subsumes {h1 h2 : Heap}
    (hsub : h2.dom_subsumes h1) (hwf : CaptureSet.WfInHeap cs h1) :
    CaptureSet.WfInHeap cs h2 := by
  induction hwf with
  | wf_empty => exact .wf_empty
  | wf_union _ _ ih1 ih2 => exact .wf_union (ih1 hsub) (ih2 hsub)
  | wf_var_free hex => obtain ⟨_, hv'⟩ := hsub _ _ hex; exact .wf_var_free hv'
  | wf_var_bound => exact .wf_var_bound
  | wf_cvar => exact .wf_cvar

theorem SepCtx.wf_dom_subsumes {h1 h2 : Heap}
    (hsub : h2.dom_subsumes h1) (hwf : SepCtx.WfInHeap Ψ h1) :
    SepCtx.WfInHeap Ψ h2 := by
  induction hwf with
  | wf_empty => exact .wf_empty
  | wf_cons _ hwf_C ih => exact .wf_cons (ih hsub) (CaptureSet.wf_dom_subsumes hsub hwf_C)

theorem MutabilityCtx.wf_dom_subsumes {h1 h2 : Heap}
    (hsub : h2.dom_subsumes h1) (hwf : MutabilityCtx.WfInHeap Ψ h1) :
    MutabilityCtx.WfInHeap Ψ h2 := by
  induction hwf with
  | wf_empty => exact .wf_empty
  | wf_cons _ hwf_C ih => exact .wf_cons (ih hsub) (CaptureSet.wf_dom_subsumes hsub hwf_C)

theorem ModalCtx.wf_dom_subsumes {h1 h2 : Heap}
    (hsub : h2.dom_subsumes h1) (hwf : ModalCtx.WfInHeap Ψ h1) :
    ModalCtx.WfInHeap Ψ h2 :=
  ⟨SepCtx.wf_dom_subsumes hsub hwf.sep, MutabilityCtx.wf_dom_subsumes hsub hwf.mutability⟩

theorem CaptureBound.wf_dom_subsumes {h1 h2 : Heap}
    (hsub : h2.dom_subsumes h1) (hwf : CaptureBound.WfInHeap cb h1) :
    CaptureBound.WfInHeap cb h2 := by
  cases hwf with
  | wf_unbound => exact .wf_unbound
  | wf_bound hwf_cs => exact .wf_bound (CaptureSet.wf_dom_subsumes hsub hwf_cs)

theorem Ty.wf_dom_subsumes {h1 h2 : Heap}
    (hsub : h2.dom_subsumes h1) (hwf : Ty.WfInHeap T h1) : Ty.WfInHeap T h2 := by
  induction hwf generalizing h2 with
  | wf_top => exact .wf_top
  | wf_tvar => exact .wf_tvar
  | wf_unit => exact .wf_unit
  | wf_bool => exact .wf_bool
  | wf_arrow _ hwf_cs _ ih1 ih2 =>
    exact .wf_arrow (ih1 hsub)
                    (CaptureSet.wf_dom_subsumes hsub hwf_cs) (ih2 hsub)
  | wf_poly _ hwf_cs _ ih1 ih2 =>
    exact .wf_poly (ih1 hsub)
                   (CaptureSet.wf_dom_subsumes hsub hwf_cs) (ih2 hsub)
  | wf_cpoly hwf_cb hwf_cs _ ih_T =>
    exact .wf_cpoly (CaptureBound.wf_dom_subsumes hsub hwf_cb)
                    (CaptureSet.wf_dom_subsumes hsub hwf_cs) (ih_T hsub)
  | wf_consumer _ hwf_cs _ ih1 ih2 =>
    exact .wf_consumer (ih1 hsub) (CaptureSet.wf_dom_subsumes hsub hwf_cs) (ih2 hsub)
  | wf_modal hwf_cs hwf_Ψ _ ih_T =>
    exact .wf_modal (CaptureSet.wf_dom_subsumes hsub hwf_cs)
                    (ModalCtx.wf_dom_subsumes hsub hwf_Ψ) (ih_T hsub)
  | wf_cap hwf_cs => exact .wf_cap (CaptureSet.wf_dom_subsumes hsub hwf_cs)
  | wf_cell hwf_cs _ ih_T =>
    exact .wf_cell (CaptureSet.wf_dom_subsumes hsub hwf_cs) (ih_T hsub)
  | wf_reader hwf_cs _ ih_T =>
    exact .wf_reader (CaptureSet.wf_dom_subsumes hsub hwf_cs) (ih_T hsub)
  | wf_exi _ ih => exact .wf_exi (ih hsub)
  | wf_typ _ ih => exact .wf_typ (ih hsub)

theorem Exp.wf_dom_subsumes {h1 h2 : Heap}
    (hsub : h2.dom_subsumes h1) (hwf : Exp.WfInHeap e h1) : Exp.WfInHeap e h2 := by
  induction hwf generalizing h2 with
  | wf_var hwf_x => exact .wf_var (Var.wf_dom_subsumes hsub hwf_x)
  | wf_abs hwf_cs hwf_T _ ih_e =>
    exact .wf_abs (CaptureSet.wf_dom_subsumes hsub hwf_cs)
                  (Ty.wf_dom_subsumes hsub hwf_T) (ih_e hsub)
  | wf_tabs hwf_cs hwf_T _ ih_e =>
    exact .wf_tabs (CaptureSet.wf_dom_subsumes hsub hwf_cs)
                   (Ty.wf_dom_subsumes hsub hwf_T) (ih_e hsub)
  | wf_cabs hwf_cs hwf_cb _ ih_e =>
    exact .wf_cabs (CaptureSet.wf_dom_subsumes hsub hwf_cs)
                   (CaptureBound.wf_dom_subsumes hsub hwf_cb) (ih_e hsub)
  | wf_consumer hwf_cs hwf_T _ ih_e =>
    exact .wf_consumer (CaptureSet.wf_dom_subsumes hsub hwf_cs)
                       (Ty.wf_dom_subsumes hsub hwf_T) (ih_e hsub)
  | wf_boxed hwf_cs hwf_Ψ _ ih_e =>
    exact .wf_boxed (CaptureSet.wf_dom_subsumes hsub hwf_cs)
                    (ModalCtx.wf_dom_subsumes hsub hwf_Ψ) (ih_e hsub)
  | wf_reader hwf_x => exact .wf_reader (Var.wf_dom_subsumes hsub hwf_x)
  | wf_alloc hwf_x => exact .wf_alloc (Var.wf_dom_subsumes hsub hwf_x)
  | wf_drop hwf_x => exact .wf_drop (Var.wf_dom_subsumes hsub hwf_x)
  | wf_pack hwf_cs hwf_x =>
    exact .wf_pack (fun cs hmem => CaptureSet.wf_dom_subsumes hsub (hwf_cs cs hmem))
                   (Var.wf_dom_subsumes hsub hwf_x)
  | wf_app hwf_x hwf_y =>
    exact .wf_app (Var.wf_dom_subsumes hsub hwf_x) (Var.wf_dom_subsumes hsub hwf_y)
  | wf_tapp hwf_x hwf_T =>
    exact .wf_tapp (Var.wf_dom_subsumes hsub hwf_x) (Ty.wf_dom_subsumes hsub hwf_T)
  | wf_capp hwf_x hwf_cs =>
    exact .wf_capp (Var.wf_dom_subsumes hsub hwf_x)
                   (CaptureSet.wf_dom_subsumes hsub hwf_cs)
  | wf_consumer_app hwf_x _ ih_e =>
    exact .wf_consumer_app (Var.wf_dom_subsumes hsub hwf_x) (ih_e hsub)
  | wf_unwrap hwf_x => exact .wf_unwrap (Var.wf_dom_subsumes hsub hwf_x)
  | wf_letin _ _ ih1 ih2 => exact .wf_letin (ih1 hsub) (ih2 hsub)
  | wf_unpack _ _ ih1 ih2 => exact .wf_unpack (ih1 hsub) (ih2 hsub)
  | wf_unit => exact .wf_unit
  | wf_btrue => exact .wf_btrue
  | wf_bfalse => exact .wf_bfalse
  | wf_read hwf_x => exact .wf_read (Var.wf_dom_subsumes hsub hwf_x)
  | wf_write hwf_x hwf_y =>
    exact .wf_write (Var.wf_dom_subsumes hsub hwf_x) (Var.wf_dom_subsumes hsub hwf_y)
  | wf_cond hwf_x _ _ ih2 ih3 =>
    exact .wf_cond (Var.wf_dom_subsumes hsub hwf_x) (ih2 hsub) (ih3 hsub)
  | wf_par hwf_C1 hwf_C2 _ _ ih1 ih2 =>
    exact .wf_par (CaptureSet.wf_dom_subsumes hsub hwf_C1)
      (CaptureSet.wf_dom_subsumes hsub hwf_C2) (ih1 hsub) (ih2 hsub)

/-- Lookup the reachability set of a location. -/
def reachability_of_loc
  (h : Heap)
  (l : Nat) :
  CapabilitySet :=
  match h l with
  | some (.capability _) => CapabilitySet.singleton .epsilon l
  | some (.val ⟨_, _, R⟩) => R
  | some .masked => CapabilitySet.singleton .epsilon l
  | none => {}

/-- Resolve reachability of each element of the capture set.
    Applies the access mode from each captured variable to the result. -/
def expand_captures
  (h : Heap)
  (cs : CaptureSet {}) :
  CapabilitySet :=
  match cs with
  | .empty => {}
  | .var m (.free loc) => (reachability_of_loc h loc).applyAccess m
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
  | .consumer cs _ _ => expand_captures h cs
  | .boxed cs _ _ => expand_captures h cs
  | .reader (.free loc) => .cap (.access .ro) loc
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
  | .consumer cs _ _ => expand_captures H cs
  | .boxed cs _ _ => expand_captures H cs
  | .reader (.free x) => .singleton .ro x
  | _ => {}

theorem resolve_monotonic {H1 H2 : Heap}
  (hsub : H2.subsumes H1)
  (hres : resolve H1 e = some v) :
  resolve H2 e = some v := by
  cases e
  case var x =>
    cases x
    case bound bv =>
      cases bv
    case free fx =>
      simp only [resolve] at hres ⊢
      cases hfx : H1 fx
      · simp [hfx] at hres
      · rename_i cell
        rw [hfx] at hres
        cases cell
        case val heapval =>
          cases hres
          obtain ⟨v', hv', hsub_v⟩ := hsub fx (.val heapval) hfx
          have hsub_v' : v' = .val heapval := by
            simpa only [Cell.subsumes] using hsub_v
          subst hsub_v'
          simp only [hv']
        case capability =>
          simp at hres
        case masked =>
          simp at hres
  all_goals
    simp only [resolve] at hres
    simp only [resolve, hres]

theorem reachability_of_loc_monotonic
  {h1 h2 : Heap}
  (hsub : h2.subsumes h1)
  (l : Nat)
  (hex : h1 l = some v) :
  reachability_of_loc h2 l = reachability_of_loc h1 l := by
  obtain ⟨v', h2_eq, hsub_v⟩ := hsub l v hex
  simp only [reachability_of_loc, hex, h2_eq]
  cases v with
  | val hv =>
    cases v' with
    | val hv' =>
      have hEq : Cell.val hv' = Cell.val hv := by
        simpa only [Cell.subsumes] using hsub_v
      cases hEq
      rfl
    | capability info =>
      have hEq : Cell.capability info = Cell.val hv := by
        simpa only [Cell.subsumes] using hsub_v
      cases hEq
    | masked =>
      have hEq : Cell.masked = Cell.val hv := by
        simpa only [Cell.subsumes] using hsub_v
      cases hEq
  | capability info =>
    cases v' with
    | val hv =>
      have hEq : Cell.val hv = Cell.capability info := by
        simpa only [Cell.subsumes] using hsub_v
      cases hEq
    | capability info' =>
      rfl
    | masked =>
      have hEq : Cell.masked = Cell.capability info := by
        simpa only [Cell.subsumes] using hsub_v
      cases hEq
  | masked =>
    cases v' with
    | val hv =>
      have hEq : Cell.val hv = Cell.masked := by
        simpa only [Cell.subsumes] using hsub_v
      cases hEq
    | capability info =>
      have hEq : Cell.capability info = Cell.masked := by
        simpa only [Cell.subsumes] using hsub_v
      cases hEq
    | masked =>
      rfl

/-- Expanding a capture set in a bigger heap yields the same result, provided
    all free locations in `cs` are allocated in the smaller heap. -/
theorem expand_captures_monotonic
  {h1 h2 : Heap}
  (hsub : h2.subsumes h1)
  (cs : CaptureSet {})
  (hwf : CaptureSet.WfInHeap cs h1) :
  expand_captures h2 cs = expand_captures h1 cs := by
  induction cs with
  | empty =>
    rfl
  | var m x =>
    cases x with
    | bound x =>
      cases x
    | free loc =>
      cases hwf with
      | wf_var_free hex =>
        simpa only [expand_captures] using
          congrArg (CapabilitySet.applyAccess m) (reachability_of_loc_monotonic hsub loc hex)
  | cvar m C =>
    cases C
  | union cs1 cs2 ih1 ih2 =>
    cases hwf with
    | wf_union hwf1 hwf2 =>
      simp only [expand_captures, ih1 hwf1, ih2 hwf2]

theorem resolve_reachability_monotonic
  {H1 H2 : Heap}
  (hsub : H2.subsumes H1)
  (e : Exp {})
  (hwf : e.WfInHeap H1) :
  resolve_reachability H2 e = resolve_reachability H1 e := by
  cases hwf with
  | wf_var hwf_x =>
    cases hwf_x with
    | wf_bound =>
      rename_i x
      cases x
    | wf_free hex =>
      rename_i fx
      change reachability_of_loc H2 fx = reachability_of_loc H1 fx
      exact reachability_of_loc_monotonic hsub fx hex
  | wf_abs hwf_cs _ _ =>
    change expand_captures H2 _ = expand_captures H1 _
    exact expand_captures_monotonic hsub _ hwf_cs
  | wf_tabs hwf_cs _ _ =>
    change expand_captures H2 _ = expand_captures H1 _
    exact expand_captures_monotonic hsub _ hwf_cs
  | wf_cabs hwf_cs _ _ =>
    change expand_captures H2 _ = expand_captures H1 _
    exact expand_captures_monotonic hsub _ hwf_cs
  | wf_consumer hwf_cs _ _ =>
    change expand_captures H2 _ = expand_captures H1 _
    exact expand_captures_monotonic hsub _ hwf_cs
  | wf_boxed hwf_cs _ _ =>
    change expand_captures H2 _ = expand_captures H1 _
    exact expand_captures_monotonic hsub _ hwf_cs
  | wf_reader hwf_x =>
    cases hwf_x with
    | wf_bound =>
      rename_i x
      cases x
    | wf_free =>
      rename_i loc hex
      rfl
  | wf_alloc _ => rfl
  | wf_drop _ => rfl
  | wf_pack _ _ => rfl
  | wf_app _ _ => rfl
  | wf_tapp _ _ => rfl
  | wf_capp _ _ => rfl
  | wf_consumer_app _ _ => rfl
  | wf_unwrap _ => rfl
  | wf_letin _ _ => rfl
  | wf_unpack _ _ => rfl
  | wf_unit => rfl
  | wf_btrue => rfl
  | wf_bfalse => rfl
  | wf_read _ => rfl
  | wf_write _ _ => rfl
  | wf_cond _ _ _ => rfl
  | wf_par _ _ _ _ => rfl

/-- Computing reachability of a value in a bigger heap yields the same result. -/
theorem compute_reachability_monotonic
  {h1 h2 : Heap}
  (hsub : h2.subsumes h1)
  (v : Exp {})
  (hv : v.IsSimpleVal)
  (hwf : Exp.WfInHeap v h1) :
  compute_reachability h2 v hv = compute_reachability h1 v hv := by
  cases hv with
  | abs =>
    change expand_captures h2 _ = expand_captures h1 _
    cases hwf with
    | wf_abs hwf_cs _ _ =>
      exact expand_captures_monotonic hsub _ hwf_cs
  | tabs =>
    change expand_captures h2 _ = expand_captures h1 _
    cases hwf with
    | wf_tabs hwf_cs _ _ =>
      exact expand_captures_monotonic hsub _ hwf_cs
  | cabs =>
    change expand_captures h2 _ = expand_captures h1 _
    cases hwf with
    | wf_cabs hwf_cs _ =>
      exact expand_captures_monotonic hsub _ hwf_cs
  | consumer =>
    change expand_captures h2 _ = expand_captures h1 _
    cases hwf with
    | wf_consumer hwf_cs _ _ =>
      exact expand_captures_monotonic hsub _ hwf_cs
  | boxed =>
    change expand_captures h2 _ = expand_captures h1 _
    cases hwf with
    | wf_boxed hwf_cs _ _ =>
      exact expand_captures_monotonic hsub _ hwf_cs
  | reader =>
    rename_i x
    cases x with
    | free loc => rfl
    | bound bx => cases bx
  | unit =>
    rfl
  | btrue =>
    rfl
  | bfalse =>
    rfl

/-- Updating an mcell preserves reachability_of_loc for all locations. -/
theorem reachability_of_loc_update_mcell (h : Heap) (l : Nat) (ℓ : Liveness)
  (hexists : ∃ n0, h l = some (.capability (.mcell n0 ℓ))) (n : Nat) (l' : Nat) :
  reachability_of_loc (h.update_cell l (.capability (.mcell n ℓ))) l' =
  reachability_of_loc h l' := by
  unfold reachability_of_loc Heap.update_cell
  by_cases heq : l' = l
  · subst heq
    obtain ⟨n0, hn0⟩ := hexists
    simp only [hn0, if_true]
  · simp only [heq, if_false]

/-- Updating an mcell preserves expand_captures. -/
theorem expand_captures_update_mcell (h : Heap) (l : Nat) (ℓ : Liveness)
  (hexists : ∃ n0, h l = some (.capability (.mcell n0 ℓ))) (n : Nat) (cs : CaptureSet {}) :
  expand_captures (h.update_cell l (.capability (.mcell n ℓ))) cs =
  expand_captures h cs := by
  induction cs with
  | empty => rfl
  | var m x =>
    cases x with
    | bound bv => cases bv
    | free loc =>
      simpa only [expand_captures] using
        congrArg (CapabilitySet.applyAccess m)
          (reachability_of_loc_update_mcell h l ℓ hexists n loc)
  | union cs1 cs2 ih1 ih2 =>
    simp only [expand_captures, ih1, ih2]
  | cvar m c => cases c

/-- Updating an mcell preserves compute_reachability. -/
theorem compute_reachability_update_mcell (h : Heap) (l : Nat) (ℓ : Liveness)
  (hexists : ∃ n0, h l = some (.capability (.mcell n0 ℓ))) (n : Nat)
  (v : Exp {}) (hv : v.IsSimpleVal) :
  compute_reachability (h.update_cell l (.capability (.mcell n ℓ))) v hv =
  compute_reachability h v hv := by
  cases hv with
  | abs =>
    simpa only [compute_reachability] using expand_captures_update_mcell h l ℓ hexists n _
  | tabs =>
    simpa only [compute_reachability] using expand_captures_update_mcell h l ℓ hexists n _
  | cabs =>
    simpa only [compute_reachability] using expand_captures_update_mcell h l ℓ hexists n _
  | consumer =>
    simpa only [compute_reachability] using expand_captures_update_mcell h l ℓ hexists n _
  | boxed =>
    simpa only [compute_reachability] using expand_captures_update_mcell h l ℓ hexists n _
  | reader =>
    rename_i x
    cases x with
    | free loc => simp only [compute_reachability]
    | bound bx => cases bx
  | unit | btrue | bfalse => rfl

/-- Dropping a live mcell preserves `reachability_of_loc` for all locations:
    both the live and dead mcell at `l` reduce to the same singleton, and
    other locations are untouched. -/
theorem reachability_of_loc_drop_mcell (h : Heap) (l : Nat)
  (hexists : ∃ b0, h l = some (.capability (.mcell b0 .live))) (l' : Nat) :
  reachability_of_loc (h.update_cell l (.capability (.mcell 0 .dead))) l' =
  reachability_of_loc h l' := by
  unfold reachability_of_loc Heap.update_cell
  by_cases heq : l' = l
  · subst heq
    obtain ⟨b0, hb0⟩ := hexists
    simp only [hb0, if_true]
  · simp only [heq, if_false]

/-- Dropping a live mcell preserves `expand_captures`. -/
theorem expand_captures_drop_mcell (h : Heap) (l : Nat)
  (hexists : ∃ b0, h l = some (.capability (.mcell b0 .live))) (cs : CaptureSet {}) :
  expand_captures (h.update_cell l (.capability (.mcell 0 .dead))) cs =
  expand_captures h cs := by
  induction cs with
  | empty => rfl
  | var m x =>
    cases x with
    | bound bv => cases bv
    | free loc =>
      simpa only [expand_captures] using
        congrArg (CapabilitySet.applyAccess m)
          (reachability_of_loc_drop_mcell h l hexists loc)
  | union cs1 cs2 ih1 ih2 =>
    simp only [expand_captures, ih1, ih2]
  | cvar m c => cases c

/-- Dropping a live mcell preserves `compute_reachability`. -/
theorem compute_reachability_drop_mcell (h : Heap) (l : Nat)
  (hexists : ∃ b0, h l = some (.capability (.mcell b0 .live)))
  (v : Exp {}) (hv : v.IsSimpleVal) :
  compute_reachability (h.update_cell l (.capability (.mcell 0 .dead))) v hv =
  compute_reachability h v hv := by
  cases hv with
  | abs =>
    simpa only [compute_reachability] using expand_captures_drop_mcell h l hexists _
  | tabs =>
    simpa only [compute_reachability] using expand_captures_drop_mcell h l hexists _
  | cabs =>
    simpa only [compute_reachability] using expand_captures_drop_mcell h l hexists _
  | consumer =>
    simpa only [compute_reachability] using expand_captures_drop_mcell h l hexists _
  | boxed =>
    simpa only [compute_reachability] using expand_captures_drop_mcell h l hexists _
  | reader =>
    rename_i x
    cases x with
    | free loc => simp only [compute_reachability]
    | bound bx => cases bx
  | unit | btrue | bfalse => rfl

/-- Membership unwrapping through `applyAccess` (any access mode). -/
theorem CapabilitySet.hasmem_of_applyAccess' {C : CapabilitySet} {a : Access}
    {mu : CapMode} {l : Nat}
    (h : (C.applyAccess a).hasmem mu l) : ∃ mu', C.hasmem mu' l := by
  cases a with
  | M m =>
    cases m with
    | epsilon => exact ⟨mu, h⟩
    | ro =>
      simp only [applyAccess_M, applyMut] at h
      clear * - h
      induction C with
      | empty => exact absurd h CapabilitySet.not_hasmem_empty
      | cap m' l' =>
        cases h
        exact ⟨m', .here⟩
      | union C1 C2 ih1 ih2 =>
        cases h with
        | left h => obtain ⟨mu', h'⟩ := ih1 h; exact ⟨mu', .left h'⟩
        | right h => obtain ⟨mu', h'⟩ := ih2 h; exact ⟨mu', .right h'⟩
  | drop =>
    simp only [applyAccess_drop] at h
    obtain ⟨_, mu', h'⟩ := CapabilitySet.hasmem_to_drop_imp h
    exact ⟨mu', h'⟩

/-- A heap is well-formed if all values stored in it contain well-formed
expressions, stored reachability sets are computed faithfully, and stored
reachability sets only mention allocated locations. -/
structure Heap.WfHeap (H : Heap) : Prop where
  wf_val :
    ∀ l hv, H l = some (.val hv) -> Exp.WfInHeap hv.unwrap H
  wf_reach :
    ∀ l v hv R,
      H l = some (.val ⟨v, hv, R⟩) ->
        R = compute_reachability H v hv
  wf_reach_dom :
    ∀ l v hv R,
      H l = some (.val ⟨v, hv, R⟩) ->
        ∀ mu l', R.hasmem mu l' -> H l' ≠ none

/-- Members of a location's reachability are allocated, given the heap-wide
domain-closure of stored reachability sets. -/
theorem reachability_of_loc_dom {H : Heap}
    (hdom : ∀ l v hv R, H l = some (.val ⟨v, hv, R⟩) ->
      ∀ mu l', R.hasmem mu l' -> H l' ≠ none)
    {l l' : Nat} {mu : CapMode}
    (h : (reachability_of_loc H l).hasmem mu l') : H l' ≠ none := by
  unfold reachability_of_loc at h
  cases hcell : H l with
  | none =>
    rw [hcell] at h
    exact absurd h CapabilitySet.not_hasmem_empty
  | some cell =>
    rw [hcell] at h
    cases cell with
    | capability _ =>
      cases h
      rw [hcell]
      intro hcontra
      cases hcontra
    | masked =>
      cases h
      rw [hcell]
      intro hcontra
      cases hcontra
    | val v =>
      obtain ⟨unwrap, isVal, R⟩ := v
      exact hdom l unwrap isVal R hcell mu l' h

/-- Members of an expanded ground capture set are allocated. -/
theorem expand_captures_dom {H : Heap}
    (hdom : ∀ l v hv R, H l = some (.val ⟨v, hv, R⟩) ->
      ∀ mu l', R.hasmem mu l' -> H l' ≠ none)
    {cs : CaptureSet {}} {l : Nat} {mu : CapMode}
    (h : (expand_captures H cs).hasmem mu l) : H l ≠ none := by
  induction cs with
  | empty => exact absurd h CapabilitySet.not_hasmem_empty
  | union cs1 cs2 ih1 ih2 =>
    cases h with
    | left h => exact ih1 h
    | right h => exact ih2 h
  | var m x =>
    cases x with
    | bound bx => cases bx
    | free n =>
      obtain ⟨mu0, h0⟩ := CapabilitySet.hasmem_of_applyAccess' h
      exact reachability_of_loc_dom hdom h0
  | cvar _ c => cases c

/-- Members of a (well-formed) simple value's computed reachability are
allocated. -/
theorem compute_reachability_dom {H : Heap}
    (hdom : ∀ l v hv R, H l = some (.val ⟨v, hv, R⟩) ->
      ∀ mu l', R.hasmem mu l' -> H l' ≠ none)
    {v : Exp {}} {hv : v.IsSimpleVal}
    (hwf : Exp.WfInHeap v H)
    {mu : CapMode} {l : Nat}
    (h : (compute_reachability H v hv).hasmem mu l) : H l ≠ none := by
  cases v with
  | abs cs _ _ => exact expand_captures_dom hdom h
  | tabs cs _ _ => exact expand_captures_dom hdom h
  | cabs cs _ _ => exact expand_captures_dom hdom h
  | consumer cs _ _ => exact expand_captures_dom hdom h
  | boxed cs _ _ => exact expand_captures_dom hdom h
  | reader x =>
    cases x with
    | bound bx => cases bx
    | free loc =>
      cases h
      cases hwf with
      | wf_reader hwfv =>
        cases hwfv with
        | wf_free hsome =>
          rw [hsome]
          intro hcontra
          cases hcontra
  | unit => exact absurd h CapabilitySet.not_hasmem_empty
  | btrue => exact absurd h CapabilitySet.not_hasmem_empty
  | bfalse => exact absurd h CapabilitySet.not_hasmem_empty
  | _ => cases hv


/-- The empty heap is well-formed. -/
theorem Heap.wf_empty : Heap.WfHeap ∅ := by
  constructor
  · intro l hv hlookup; cases hlookup
  · intros _ _ _ _ hlookup; cases hlookup
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
  · intro l' hv' hlookup
    unfold Heap.extend at hlookup
    split at hlookup
    case isTrue heq =>
      cases hlookup
      exact Exp.wf_monotonic (Heap.extend_subsumes hfresh) hwf_v
    case isFalse hneq =>
      exact Exp.wf_monotonic (Heap.extend_subsumes hfresh) (hwf_H.wf_val l' hv' hlookup)
  · intro l' v' hv' R' hlookup
    unfold Heap.extend at hlookup
    split at hlookup
    case isTrue heq =>
      cases hlookup
      rw [compute_reachability_monotonic (Heap.extend_subsumes hfresh) v' hv' hwf_v]
      exact hreach
    case isFalse hneq =>
      have heq := hwf_H.wf_reach l' v' hv' R' hlookup
      rw [heq]
      exact (compute_reachability_monotonic (Heap.extend_subsumes hfresh) v' hv'
        (hwf_H.wf_val l' _ hlookup)).symm
  · intro l' v' hv' R' hlookup mu l'' hmem
    have hold : H l'' ≠ none := by
      unfold Heap.extend at hlookup
      split at hlookup
      case isTrue heq =>
        cases hlookup
        have hreach' : R' = compute_reachability H v' hv' := hreach
        rw [hreach'] at hmem
        exact compute_reachability_dom hwf_H.wf_reach_dom hwf_v hmem
      case isFalse hneq =>
        exact hwf_H.wf_reach_dom l' v' hv' R' hlookup mu l'' hmem
    unfold Heap.extend
    split
    · intro hcontra; cases hcontra
    · exact hold

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
    change Var.WfInHeap (.bound _) H
    exact Var.WfInHeap.wf_bound
  | wf_free hex =>
    change Var.WfInHeap (.free _) H
    exact Var.WfInHeap.wf_free hex

/-- Renaming preserves well-formedness of capture sets. -/
theorem CaptureSet.wf_rename
  {cs : CaptureSet s1}
  {f : Rename s1 s2}
  {H : Heap}
  (hwf : CaptureSet.WfInHeap cs H) :
  CaptureSet.WfInHeap (cs.rename f) H := by
  induction hwf with
  | wf_empty =>
    simpa only [CaptureSet.rename] using (CaptureSet.WfInHeap.wf_empty)
  | wf_union _ _ ih1 ih2 =>
    simpa only [CaptureSet.rename] using (CaptureSet.WfInHeap.wf_union ih1 ih2)
  | wf_var_free hex =>
    simpa only [CaptureSet.rename, Var.rename] using
      (CaptureSet.WfInHeap.wf_var_free hex)
  | wf_var_bound =>
    simpa only [CaptureSet.rename, Var.rename] using
      (CaptureSet.WfInHeap.wf_var_bound)
  | wf_cvar =>
    simpa only [CaptureSet.rename] using (CaptureSet.WfInHeap.wf_cvar)

theorem SepCtx.wf_rename
  {Ψ : SepCtx s1}
  {f : Rename s1 s2}
  {H : Heap}
  (hwf : SepCtx.WfInHeap Ψ H) :
  SepCtx.WfInHeap (Ψ.rename f) H := by
  induction hwf with
  | wf_empty =>
    simpa only [SepCtx.rename] using (SepCtx.WfInHeap.wf_empty)
  | wf_cons hwf_Ψ hwf_C ih =>
    simpa only [SepCtx.rename] using
      (SepCtx.WfInHeap.wf_cons ih (CaptureSet.wf_rename hwf_C))

theorem MutabilityCtx.wf_rename
  {Ψ : MutabilityCtx s1}
  {f : Rename s1 s2}
  {H : Heap}
  (hwf : MutabilityCtx.WfInHeap Ψ H) :
  MutabilityCtx.WfInHeap (Ψ.rename f) H := by
  induction hwf with
  | wf_empty =>
    simpa only [MutabilityCtx.rename] using (MutabilityCtx.WfInHeap.wf_empty)
  | wf_cons hwf_Ψ hwf_C ih =>
    simpa only [MutabilityCtx.rename] using
      (MutabilityCtx.WfInHeap.wf_cons ih (CaptureSet.wf_rename hwf_C))

theorem ModalCtx.wf_rename
  {Ψ : ModalCtx s1}
  {f : Rename s1 s2}
  {H : Heap}
  (hwf : ModalCtx.WfInHeap Ψ H) :
  ModalCtx.WfInHeap (Ψ.rename f) H :=
  ⟨SepCtx.wf_rename hwf.sep, MutabilityCtx.wf_rename hwf.mutability⟩

theorem CaptureBound.wf_rename
  {cb : CaptureBound s1}
  {f : Rename s1 s2}
  {H : Heap}
  (hwf : CaptureBound.WfInHeap cb H) :
  CaptureBound.WfInHeap (cb.rename f) H := by
  cases hwf with
  | wf_unbound =>
    simpa only [CaptureBound.rename] using (CaptureBound.WfInHeap.wf_unbound)
  | wf_bound hwf_cs =>
    simpa only [CaptureBound.rename] using
      (CaptureBound.WfInHeap.wf_bound (CaptureSet.wf_rename hwf_cs))

/-- Renaming preserves well-formedness of types. -/
theorem Ty.wf_rename
  {T : Ty sort s1}
  {f : Rename s1 s2}
  {H : Heap}
  (hwf : Ty.WfInHeap T H) :
  Ty.WfInHeap (T.rename f) H := by
  induction hwf generalizing s2 with
  | wf_top =>
    simpa only [Ty.rename] using (Ty.WfInHeap.wf_top)
  | wf_tvar =>
    simpa only [Ty.rename] using (Ty.WfInHeap.wf_tvar)
  | wf_arrow _ hwf_cs _ ih1 ih2 =>
    simpa only [Ty.rename] using
      (Ty.WfInHeap.wf_arrow ih1 (CaptureSet.wf_rename hwf_cs) ih2)
  | wf_poly _ hwf_cs _ ih1 ih2 =>
    simpa only [Ty.rename] using
      (Ty.WfInHeap.wf_poly ih1 (CaptureSet.wf_rename hwf_cs) ih2)
  | wf_cpoly hwf_cb hwf_cs _ ih_T =>
    simpa only [Ty.rename] using
      (Ty.WfInHeap.wf_cpoly
        (CaptureBound.wf_rename hwf_cb)
        (CaptureSet.wf_rename hwf_cs)
        ih_T)
  | wf_consumer _ hwf_cs _ ih1 ih2 =>
    simpa only [Ty.rename] using
      (Ty.WfInHeap.wf_consumer ih1 (CaptureSet.wf_rename hwf_cs) ih2)
  | wf_modal hwf_cs hwf_Ψ _ ih_T =>
    simpa only [Ty.rename] using
      (Ty.WfInHeap.wf_modal
        (CaptureSet.wf_rename hwf_cs)
        (ModalCtx.wf_rename hwf_Ψ)
        ih_T)
  | wf_unit =>
    simpa only [Ty.rename] using (Ty.WfInHeap.wf_unit)
  | wf_cap hwf_cs =>
    simpa only [Ty.rename] using
      (Ty.WfInHeap.wf_cap (CaptureSet.wf_rename hwf_cs))
  | wf_bool =>
    simpa only [Ty.rename] using (Ty.WfInHeap.wf_bool)
  | wf_cell hwf_cs _ ih_T =>
    simpa only [Ty.rename] using
      (Ty.WfInHeap.wf_cell (CaptureSet.wf_rename hwf_cs) ih_T)
  | wf_reader hwf_cs _ ih_T =>
    simpa only [Ty.rename] using
      (Ty.WfInHeap.wf_reader (CaptureSet.wf_rename hwf_cs) ih_T)
  | wf_exi _ ih =>
    simpa only [Ty.rename] using (Ty.WfInHeap.wf_exi ih)
  | wf_typ _ ih =>
    simpa only [Ty.rename] using (Ty.WfInHeap.wf_typ ih)

/-- Renaming preserves well-formedness of expressions. -/
theorem Exp.wf_rename
  {e : Exp s1}
  {f : Rename s1 s2}
  {H : Heap}
  (hwf : Exp.WfInHeap e H) :
  Exp.WfInHeap (e.rename f) H := by
  induction hwf generalizing s2 with
  | wf_var hwf_x =>
    simpa only [Exp.rename] using (Exp.WfInHeap.wf_var (Var.wf_rename hwf_x))
  | wf_abs hwf_cs hwf_T _ ih_e =>
    simpa only [Exp.rename] using
      (Exp.WfInHeap.wf_abs
        (CaptureSet.wf_rename hwf_cs)
        (Ty.wf_rename hwf_T)
        ih_e)
  | wf_tabs hwf_cs hwf_T _ ih_e =>
    simpa only [Exp.rename] using
      (Exp.WfInHeap.wf_tabs
        (CaptureSet.wf_rename hwf_cs)
        (by
          simpa only [PureTy.WfInHeap, PureTy.rename] using Ty.wf_rename hwf_T)
        ih_e)
  | wf_cabs hwf_cs hwf_cb _ ih_e =>
    simpa only [Exp.rename] using
      (Exp.WfInHeap.wf_cabs
        (CaptureSet.wf_rename hwf_cs)
        (CaptureBound.wf_rename hwf_cb)
        ih_e)
  | wf_consumer hwf_cs hwf_T _ ih_e =>
    simpa only [Exp.rename] using
      (Exp.WfInHeap.wf_consumer
        (CaptureSet.wf_rename hwf_cs)
        (Ty.wf_rename hwf_T)
        ih_e)
  | wf_boxed hwf_cs hwf_Ψ _ ih_e =>
    simpa only [Exp.rename] using
      (Exp.WfInHeap.wf_boxed
        (CaptureSet.wf_rename hwf_cs)
        (ModalCtx.wf_rename hwf_Ψ)
        ih_e)
  | wf_reader hwf_x =>
    simpa only [Exp.rename] using (Exp.WfInHeap.wf_reader (Var.wf_rename hwf_x))
  | wf_alloc hwf_x =>
    simpa only [Exp.rename] using (Exp.WfInHeap.wf_alloc (Var.wf_rename hwf_x))
  | wf_drop hwf_x =>
    simpa only [Exp.rename] using (Exp.WfInHeap.wf_drop (Var.wf_rename hwf_x))
  | wf_pack hwf_cs hwf_x =>
    simpa only [Exp.rename] using
      (Exp.WfInHeap.wf_pack
        (fun cs hmem => by
          rw [List.Vector.toList_map] at hmem
          obtain ⟨cs', hmem', rfl⟩ := List.mem_map.mp hmem
          exact CaptureSet.wf_rename (hwf_cs cs' hmem'))
        (Var.wf_rename hwf_x))
  | wf_app hwf_x hwf_y =>
    simpa only [Exp.rename] using
      (Exp.WfInHeap.wf_app (Var.wf_rename hwf_x) (Var.wf_rename hwf_y))
  | wf_tapp hwf_x hwf_T =>
    simpa only [Exp.rename] using
      (Exp.WfInHeap.wf_tapp
        (Var.wf_rename hwf_x)
        (by
          simpa only [PureTy.WfInHeap, PureTy.rename] using Ty.wf_rename hwf_T))
  | wf_capp hwf_x hwf_cs =>
    simpa only [Exp.rename] using
      (Exp.WfInHeap.wf_capp (Var.wf_rename hwf_x) (CaptureSet.wf_rename hwf_cs))
  | wf_consumer_app hwf_x _ ih_e =>
    simpa only [Exp.rename] using
      (Exp.WfInHeap.wf_consumer_app (Var.wf_rename hwf_x) ih_e)
  | wf_unwrap hwf_x =>
    simpa only [Exp.rename] using (Exp.WfInHeap.wf_unwrap (Var.wf_rename hwf_x))
  | wf_letin _ _ ih1 ih2 =>
    simpa only [Exp.rename] using (Exp.WfInHeap.wf_letin ih1 ih2)
  | wf_unpack _ _ ih1 ih2 =>
    simpa only [Exp.rename] using (Exp.WfInHeap.wf_unpack ih1 ih2)
  | wf_unit =>
    simpa only [Exp.rename] using (Exp.WfInHeap.wf_unit)
  | wf_btrue =>
    simpa only [Exp.rename] using (Exp.WfInHeap.wf_btrue)
  | wf_bfalse =>
    simpa only [Exp.rename] using (Exp.WfInHeap.wf_bfalse)
  | wf_read hwf_x =>
    simpa only [Exp.rename] using (Exp.WfInHeap.wf_read (Var.wf_rename hwf_x))
  | wf_write hwf_x hwf_y =>
    simpa only [Exp.rename] using
      (Exp.WfInHeap.wf_write (Var.wf_rename hwf_x) (Var.wf_rename hwf_y))
  | wf_cond hwf_x _ _ ih2 ih3 =>
    simpa only [Exp.rename] using
      (Exp.WfInHeap.wf_cond (Var.wf_rename hwf_x) ih2 ih3)
  | wf_par hwf_C1 hwf_C2 _ _ ih1 ih2 =>
    simpa only [Exp.rename] using
      (Exp.WfInHeap.wf_par (CaptureSet.wf_rename hwf_C1) (CaptureSet.wf_rename hwf_C2) ih1 ih2)

-- Substitution well-formedness preservation

/-- A well-formed variable yields a well-formed capture set. -/
theorem CaptureSet.wf_of_var
  {m : Access}
  {x : Var .var s}
  {H : Heap}
  (hwf : Var.WfInHeap x H) :
  CaptureSet.WfInHeap (.var m x) H := by
  cases hwf with
  | wf_bound => exact CaptureSet.WfInHeap.wf_var_bound
  | wf_free hex => exact CaptureSet.WfInHeap.wf_var_free hex

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
      simpa only [Subst.lift] using (Var.WfInHeap.wf_bound)
    | there x =>
      simpa only [Subst.lift] using Var.wf_rename (hwf_σ.wf_var x)
  · intro X
    cases X with
    | here =>
      simpa only [Subst.lift, PureTy.WfInHeap] using (Ty.WfInHeap.wf_tvar)
    | there X =>
      simpa only [Subst.lift, PureTy.WfInHeap, PureTy.rename] using
        Ty.wf_rename (hwf_σ.wf_tvar X)
  · intro C
    cases C with
    | here =>
      simpa only [Subst.lift] using (CaptureSet.WfInHeap.wf_cvar)
    | there C =>
      simpa only [Subst.lift] using CaptureSet.wf_rename (hwf_σ.wf_cvar C)

/-- Lifting a well-formed substitution under `n` capture-variable binders
    preserves well-formedness. -/
theorem Subst.wf_liftCVars
  {σ : Subst s1 s2}
  {H : Heap}
  (hwf_σ : σ.WfInHeap H) :
  {n : Nat} → (σ.liftCVars n).WfInHeap H
  | 0 => hwf_σ
  | _ + 1 => Subst.wf_lift (Subst.wf_liftCVars hwf_σ)

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
    simpa only [Var.subst] using hwf_σ.wf_var x
  | free n =>
    cases hwf_x with
    | wf_free hex =>
      simpa only [Var.subst] using (Var.WfInHeap.wf_free hex)

/-- applyRO preserves well-formedness of capture sets. -/
theorem CaptureSet.wf_applyRO
  {cs : CaptureSet s}
  {H : Heap}
  (hwf : CaptureSet.WfInHeap cs H) :
  CaptureSet.WfInHeap cs.applyRO H := by
  induction hwf with
  | wf_empty => exact WfInHeap.wf_empty
  | wf_union _ _ ih1 ih2 => exact WfInHeap.wf_union ih1 ih2
  | wf_var_free hex => exact WfInHeap.wf_var_free hex
  | wf_var_bound => exact WfInHeap.wf_var_bound
  | wf_cvar => exact WfInHeap.wf_cvar

/-- applyMut preserves well-formedness of capture sets. -/
theorem CaptureSet.wf_applyMut
  {cs : CaptureSet s}
  {H : Heap}
  {m : Mutability}
  (hwf : CaptureSet.WfInHeap cs H) :
  CaptureSet.WfInHeap (cs.applyMut m) H := by
  cases m with
  | epsilon =>
    simpa only [CaptureSet.applyMut] using hwf
  | ro =>
    simpa only [CaptureSet.applyMut] using wf_applyRO hwf

/-- applyDrop preserves well-formedness of capture sets. -/
theorem CaptureSet.wf_applyDrop
  {cs : CaptureSet s}
  {H : Heap}
  (hwf : CaptureSet.WfInHeap cs H) :
  CaptureSet.WfInHeap cs.applyDrop H := by
  induction hwf with
  | wf_empty => exact WfInHeap.wf_empty
  | wf_union _ _ ih1 ih2 => exact WfInHeap.wf_union ih1 ih2
  | wf_var_free hex => exact WfInHeap.wf_var_free hex
  | wf_var_bound => exact WfInHeap.wf_var_bound
  | wf_cvar => exact WfInHeap.wf_cvar

/-- applyAccess preserves well-formedness of capture sets. -/
theorem CaptureSet.wf_applyAccess
  {cs : CaptureSet s}
  {H : Heap}
  {a : Access}
  (hwf : CaptureSet.WfInHeap cs H) :
  CaptureSet.WfInHeap (cs.applyAccess a) H := by
  cases a with
  | M m => exact wf_applyMut hwf
  | drop => exact wf_applyDrop hwf


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
    simpa only [CaptureSet.subst] using (CaptureSet.WfInHeap.wf_empty)
  | wf_union _ _ ih1 ih2 =>
    simpa only [CaptureSet.subst] using
      (CaptureSet.WfInHeap.wf_union (ih1 hwf_σ) (ih2 hwf_σ))
  | wf_var_free hex =>
    simpa only [CaptureSet.subst, Var.subst] using
      (CaptureSet.WfInHeap.wf_var_free hex)
  | wf_var_bound =>
    simpa only [CaptureSet.subst, Var.subst] using
      (CaptureSet.wf_of_var (Var.wf_subst (Var.WfInHeap.wf_bound) hwf_σ))
  | wf_cvar =>
    simpa only [CaptureSet.subst] using CaptureSet.wf_applyAccess (hwf_σ.wf_cvar _)

theorem SepCtx.wf_subst
  {Ψ : SepCtx s1}
  {σ : Subst s1 s2}
  {H : Heap}
  (hwf_Ψ : SepCtx.WfInHeap Ψ H)
  (hwf_σ : σ.WfInHeap H) :
  SepCtx.WfInHeap (Ψ.subst σ) H := by
  induction hwf_Ψ with
  | wf_empty =>
    simpa only [SepCtx.subst] using (SepCtx.WfInHeap.wf_empty)
  | wf_cons hwf_Ψ hwf_C ih =>
    simpa only [SepCtx.subst] using
      (SepCtx.WfInHeap.wf_cons (ih hwf_σ) (CaptureSet.wf_subst hwf_C hwf_σ))

theorem MutabilityCtx.wf_subst
  {Ψ : MutabilityCtx s1}
  {σ : Subst s1 s2}
  {H : Heap}
  (hwf_Ψ : MutabilityCtx.WfInHeap Ψ H)
  (hwf_σ : σ.WfInHeap H) :
  MutabilityCtx.WfInHeap (Ψ.subst σ) H := by
  induction hwf_Ψ with
  | wf_empty =>
    simpa only [MutabilityCtx.subst] using (MutabilityCtx.WfInHeap.wf_empty)
  | wf_cons hwf_Ψ hwf_C ih =>
    simpa only [MutabilityCtx.subst] using
      (MutabilityCtx.WfInHeap.wf_cons (ih hwf_σ) (CaptureSet.wf_subst hwf_C hwf_σ))

theorem ModalCtx.wf_subst
  {Ψ : ModalCtx s1}
  {σ : Subst s1 s2}
  {H : Heap}
  (hwf_Ψ : ModalCtx.WfInHeap Ψ H)
  (hwf_σ : σ.WfInHeap H) :
  ModalCtx.WfInHeap (Ψ.subst σ) H :=
  ⟨SepCtx.wf_subst hwf_Ψ.sep hwf_σ, MutabilityCtx.wf_subst hwf_Ψ.mutability hwf_σ⟩

theorem CaptureBound.wf_subst
  {cb : CaptureBound s1}
  {σ : Subst s1 s2}
  {H : Heap}
  (hwf_cb : CaptureBound.WfInHeap cb H)
  (hwf_σ : σ.WfInHeap H) :
  CaptureBound.WfInHeap (cb.subst σ) H := by
  cases hwf_cb with
  | wf_unbound =>
    simpa only [CaptureBound.subst] using (CaptureBound.WfInHeap.wf_unbound)
  | wf_bound hwf_cs =>
    simpa only [CaptureBound.subst] using
      (CaptureBound.WfInHeap.wf_bound (CaptureSet.wf_subst hwf_cs hwf_σ))

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
    simpa only [Ty.subst] using (Ty.WfInHeap.wf_top)
  | wf_tvar =>
    simpa only [Ty.subst, PureTy.WfInHeap] using hwf_σ.wf_tvar _
  | wf_arrow _ hwf_cs _ ih1 ih2 =>
    simpa only [Ty.subst] using
      (Ty.WfInHeap.wf_arrow
        (ih1 hwf_σ)
        (CaptureSet.wf_subst hwf_cs hwf_σ)
        (ih2 (Subst.wf_lift hwf_σ)))
  | wf_poly _ hwf_cs _ ih1 ih2 =>
    simpa only [Ty.subst] using
      (Ty.WfInHeap.wf_poly
        (ih1 hwf_σ)
        (CaptureSet.wf_subst hwf_cs hwf_σ)
        (ih2 (Subst.wf_lift hwf_σ)))
  | wf_cpoly hwf_cb hwf_cs _ ih_T =>
    simpa only [Ty.subst] using
      (Ty.WfInHeap.wf_cpoly
        (CaptureBound.wf_subst hwf_cb hwf_σ)
        (CaptureSet.wf_subst hwf_cs hwf_σ)
        (ih_T (Subst.wf_lift hwf_σ)))
  | wf_consumer _ hwf_cs _ ih1 ih2 =>
    simpa only [Ty.subst] using
      (Ty.WfInHeap.wf_consumer
        (ih1 hwf_σ)
        (CaptureSet.wf_subst hwf_cs hwf_σ)
        (ih2 hwf_σ))
  | wf_modal hwf_cs hwf_Ψ _ ih_T =>
    simpa only [Ty.subst] using
      (Ty.WfInHeap.wf_modal
        (CaptureSet.wf_subst hwf_cs hwf_σ)
        (ModalCtx.wf_subst hwf_Ψ hwf_σ)
        (ih_T hwf_σ))
  | wf_unit =>
    simpa only [Ty.subst] using (Ty.WfInHeap.wf_unit)
  | wf_cap hwf_cs =>
    simpa only [Ty.subst] using
      (Ty.WfInHeap.wf_cap (CaptureSet.wf_subst hwf_cs hwf_σ))
  | wf_bool =>
    simpa only [Ty.subst] using (Ty.WfInHeap.wf_bool)
  | wf_cell hwf_cs _ ih_T =>
    simpa only [Ty.subst] using
      (Ty.WfInHeap.wf_cell (CaptureSet.wf_subst hwf_cs hwf_σ) (ih_T hwf_σ))
  | wf_reader hwf_cs _ ih_T =>
    simpa only [Ty.subst] using
      (Ty.WfInHeap.wf_reader (CaptureSet.wf_subst hwf_cs hwf_σ) (ih_T hwf_σ))
  | wf_exi _ ih =>
    simpa only [Ty.subst] using
      (Ty.WfInHeap.wf_exi (ih (Subst.wf_liftCVars hwf_σ)))
  | wf_typ _ ih =>
    simpa only [Ty.subst] using (Ty.WfInHeap.wf_typ (ih hwf_σ))

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
    simpa only [Exp.subst] using (Exp.WfInHeap.wf_var (Var.wf_subst hwf_x hwf_σ))
  | wf_abs hwf_cs hwf_T _ ih_e =>
    simpa only [Exp.subst] using
      (Exp.WfInHeap.wf_abs
        (CaptureSet.wf_subst hwf_cs hwf_σ)
        (Ty.wf_subst hwf_T hwf_σ)
        (ih_e (Subst.wf_lift hwf_σ)))
  | wf_tabs hwf_cs hwf_T _ ih_e =>
    simpa only [Exp.subst] using
      (Exp.WfInHeap.wf_tabs
        (CaptureSet.wf_subst hwf_cs hwf_σ)
        (by
          simpa only [PureTy.WfInHeap, PureTy.subst] using Ty.wf_subst hwf_T hwf_σ)
        (ih_e (Subst.wf_lift hwf_σ)))
  | wf_cabs hwf_cs hwf_cb _ ih_e =>
    simpa only [Exp.subst] using
      (Exp.WfInHeap.wf_cabs
        (CaptureSet.wf_subst hwf_cs hwf_σ)
        (CaptureBound.wf_subst hwf_cb hwf_σ)
        (ih_e (Subst.wf_lift hwf_σ)))
  | wf_consumer hwf_cs hwf_T _ ih_e =>
    simpa only [Exp.subst] using
      (Exp.WfInHeap.wf_consumer
        (CaptureSet.wf_subst hwf_cs hwf_σ)
        (Ty.wf_subst hwf_T hwf_σ)
        (ih_e (Subst.wf_lift (Subst.wf_lift hwf_σ))))
  | wf_boxed hwf_cs hwf_Ψ _ ih_e =>
    simpa only [Exp.subst] using
      (Exp.WfInHeap.wf_boxed
        (CaptureSet.wf_subst hwf_cs hwf_σ)
        (ModalCtx.wf_subst hwf_Ψ hwf_σ)
        (ih_e hwf_σ))
  | wf_reader hwf_x =>
    simpa only [Exp.subst] using (Exp.WfInHeap.wf_reader (Var.wf_subst hwf_x hwf_σ))
  | wf_alloc hwf_x =>
    simpa only [Exp.subst] using (Exp.WfInHeap.wf_alloc (Var.wf_subst hwf_x hwf_σ))
  | wf_drop hwf_x =>
    simpa only [Exp.subst] using (Exp.WfInHeap.wf_drop (Var.wf_subst hwf_x hwf_σ))
  | wf_pack hwf_cs hwf_x =>
    simpa only [Exp.subst] using
      (Exp.WfInHeap.wf_pack
        (fun cs hmem => by
          rw [List.Vector.toList_map] at hmem
          obtain ⟨cs', hmem', rfl⟩ := List.mem_map.mp hmem
          exact CaptureSet.wf_subst (hwf_cs cs' hmem') hwf_σ)
        (Var.wf_subst hwf_x hwf_σ))
  | wf_app hwf_x hwf_y =>
    simpa only [Exp.subst] using
      (Exp.WfInHeap.wf_app (Var.wf_subst hwf_x hwf_σ) (Var.wf_subst hwf_y hwf_σ))
  | wf_tapp hwf_x hwf_T =>
    simpa only [Exp.subst] using
      (Exp.WfInHeap.wf_tapp
        (Var.wf_subst hwf_x hwf_σ)
        (by
          simpa only [PureTy.WfInHeap, PureTy.subst] using Ty.wf_subst hwf_T hwf_σ))
  | wf_capp hwf_x hwf_cs =>
    simpa only [Exp.subst] using
      (Exp.WfInHeap.wf_capp (Var.wf_subst hwf_x hwf_σ) (CaptureSet.wf_subst hwf_cs hwf_σ))
  | wf_consumer_app hwf_x _ ih_e =>
    simpa only [Exp.subst] using
      (Exp.WfInHeap.wf_consumer_app (Var.wf_subst hwf_x hwf_σ) (ih_e hwf_σ))
  | wf_unwrap hwf_x =>
    simpa only [Exp.subst] using (Exp.WfInHeap.wf_unwrap (Var.wf_subst hwf_x hwf_σ))
  | wf_letin _ _ ih1 ih2 =>
    simpa only [Exp.subst] using
      (Exp.WfInHeap.wf_letin (ih1 hwf_σ) (ih2 (Subst.wf_lift hwf_σ)))
  | wf_unpack _ _ ih1 ih2 =>
    simpa only [Exp.subst] using
      (Exp.WfInHeap.wf_unpack
        (ih1 hwf_σ)
        (ih2 (Subst.wf_lift (Subst.wf_liftCVars hwf_σ))))
  | wf_unit =>
    simpa only [Exp.subst] using (Exp.WfInHeap.wf_unit)
  | wf_btrue =>
    simpa only [Exp.subst] using (Exp.WfInHeap.wf_btrue)
  | wf_bfalse =>
    simpa only [Exp.subst] using (Exp.WfInHeap.wf_bfalse)
  | wf_read hwf_x =>
    simpa only [Exp.subst] using (Exp.WfInHeap.wf_read (Var.wf_subst hwf_x hwf_σ))
  | wf_write hwf_x hwf_y =>
    simpa only [Exp.subst] using
      (Exp.WfInHeap.wf_write (Var.wf_subst hwf_x hwf_σ) (Var.wf_subst hwf_y hwf_σ))
  | wf_cond hwf_x hwf2 hwf3 ih2 ih3 =>
    simpa only [Exp.subst] using
      (Exp.WfInHeap.wf_cond (Var.wf_subst hwf_x hwf_σ) (ih2 hwf_σ) (ih3 hwf_σ))
  | wf_par hwf_C1 hwf_C2 _ _ ih1 ih2 =>
    simpa only [Exp.subst] using
      (Exp.WfInHeap.wf_par (CaptureSet.wf_subst hwf_C1 hwf_σ) (CaptureSet.wf_subst hwf_C2 hwf_σ)
        (ih1 hwf_σ) (ih2 hwf_σ))

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
      simpa only [Subst.openVar] using hwf_x
    | there y0 =>
      simpa only [Subst.openVar] using (Var.WfInHeap.wf_bound)
  · intro X
    cases X with
    | there X0 =>
      simpa only [Subst.openVar, PureTy.WfInHeap] using (Ty.WfInHeap.wf_tvar)
  · intro C
    cases C with
    | there C0 =>
      simpa only [Subst.openVar] using (CaptureSet.WfInHeap.wf_cvar)

/-- Opening substitution for type variables is well-formed if the type is well-formed. -/
theorem Subst.wf_openTVar
  {U : PureTy s}
  {H : Heap}
  (hwf_U : PureTy.WfInHeap U H) :
  (Subst.openTVar U).WfInHeap H := by
  constructor
  · intro x
    cases x with
    | there x0 =>
      simpa only [Subst.openTVar] using (Var.WfInHeap.wf_bound)
  · intro X
    cases X with
    | here =>
      simpa only [Subst.openTVar] using hwf_U
    | there X0 =>
      simpa only [Subst.openTVar, PureTy.WfInHeap] using (Ty.WfInHeap.wf_tvar)
  · intro C
    cases C with
    | there C0 =>
      simpa only [Subst.openTVar] using (CaptureSet.WfInHeap.wf_cvar)

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
      simpa only [Subst.openCVar] using (Var.WfInHeap.wf_bound)
  · intro X
    cases X with
    | there X0 =>
      simpa only [Subst.openCVar, PureTy.WfInHeap] using (Ty.WfInHeap.wf_tvar)
  · intro C_var
    cases C_var with
    | here =>
      simpa only [Subst.openCVar] using hwf_C
    | there C0 =>
      simpa only [Subst.openCVar] using (CaptureSet.WfInHeap.wf_cvar)

/-- The parallel opening substitution for `n` capture variables is well-formed if
    every evidence in the vector is well-formed. -/
theorem Subst.wf_openCVars {H : Heap} :
  {n : Nat} → {Cs : List.Vector (CaptureSet s) n} →
  (∀ C ∈ Cs.toList, CaptureSet.WfInHeap C H) →
  (Subst.openCVars Cs).WfInHeap H
  | 0, _, _ => by
    constructor
    · intro y
      simpa only [Subst.openCVars, Subst.id] using (Var.WfInHeap.wf_bound)
    · intro X
      simpa only [Subst.openCVars, Subst.id, PureTy.WfInHeap] using (Ty.WfInHeap.wf_tvar)
    · intro C
      simpa only [Subst.openCVars, Subst.id] using (CaptureSet.WfInHeap.wf_cvar)
  | _ + 1, Cs, hwf => by
    obtain ⟨l, hl⟩ := Cs
    cases l with
    | nil => cases hl
    | cons c l' =>
      have ih := Subst.wf_openCVars (Cs := ⟨l', by simpa using hl⟩)
        (fun C hmem => hwf C (List.mem_cons_of_mem c hmem))
      constructor
      · intro y
        cases y with
        | there y0 => exact ih.wf_var y0
      · intro X
        cases X with
        | there X0 => exact ih.wf_tvar X0
      · intro C_var
        cases C_var with
        | here => exact hwf c List.mem_cons_self
        | there C0 => exact ih.wf_cvar C0

/-- The unpack substitution is well-formed if every evidence and the variable
    are well-formed. -/
theorem Subst.wf_unpack
  {n : Nat} {Cs : List.Vector (CaptureSet s) n}
  {x : Var .var s}
  {H : Heap}
  (hwf_Cs : ∀ C ∈ Cs.toList, CaptureSet.WfInHeap C H)
  (hwf_x : Var.WfInHeap x H) :
  (Subst.unpack Cs x).WfInHeap H := by
  have hopen := Subst.wf_openCVars hwf_Cs
  constructor
  · intro y
    cases y with
    | here => simpa only [Subst.unpack] using hwf_x
    | there y0 => simpa only [Subst.unpack] using hopen.wf_var y0
  · intro X
    cases X with
    | there X0 => simpa only [Subst.unpack] using hopen.wf_tvar X0
  · intro C_var
    cases C_var with
    | there C0 => simpa only [Subst.unpack] using hopen.wf_cvar C0

def Heap.HasFinDom (H : Heap) (L : Finset Nat) : Prop :=
  ∀ l, H l ≠ none <-> l ∈ L

def Heap.empty_has_fin_dom : Heap.HasFinDom ∅ ∅ := by
  intro l; aesop

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
      rw [Finset.mem_union, Finset.mem_singleton] at h
      rcases h with h | h
      · exact (hdom l').mpr h
      · contradiction

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
      rw [Finset.mem_union, Finset.mem_singleton] at h
      rcases h with h | h
      · exact (hdom l').mpr h
      · contradiction

/-- Memory is a well-formed heap. -/
structure Memory where
  heap : Heap
  wf : heap.WfHeap
  findom : ∃ dom, heap.HasFinDom dom
  /-- **Content-closure for mutable cells.**  Every *live* mutable cell stores the heap
    location of a *present* cell.  This is the operational content-validity invariant for
    generic (reference-valued) cells: it holds because `alloc`/`write` only ever store
    locations of *present* cells (the env binds every variable — of any type — to a present
    location), and it is what makes a faithful `read` return a well-formed reference
    (`mcell_content_val`).  It also gives the confluence frame lemmas the disequality
    "an mcell's content differs from any cell absent in the smaller heap".

    NB the content is *present* (a value or another capability), not necessarily a value:
    a generic cell may store a reference-valued (`cell`/`reader`) content. -/
  mcell_wf : ∀ l n, heap l = some (.capability (.mcell n .live)) →
    heap n ≠ none

namespace Memory

/-- Create an empty memory. -/
def empty : Memory where
  heap := ∅
  wf := Heap.wf_empty
  findom := ⟨∅, Heap.empty_has_fin_dom⟩
  mcell_wf := by intro l n hlk; cases hlk

/-- A value location differs from any location holding a capability cell. -/
theorem val_ne_cap_loc {H : Heap} {n l : Nat} {w c}
    (hn : H n = some (.val w)) (hl : H l = some (.capability c)) : n ≠ l := by
  rintro rfl; rw [hn] at hl; cases hl

/-- A present value location differs from a fresh (absent) location. -/
theorem val_present_ne_fresh {H : Heap} {n l : Nat} {w}
    (hn : H n = some (.val w)) (hl : H l = none) : n ≠ l := by
  rintro rfl; rw [hn] at hl; cases hl

/-- Any present location differs from a fresh (absent) location. -/
theorem present_ne_fresh {H : Heap} {n l : Nat}
    (hn : H n ≠ none) (hl : H l = none) : n ≠ l := fun h => hn (h ▸ hl)

/-- Lookup a value in memory. -/
def lookup (m : Memory) (l : Nat) : Option Cell :=
  m.heap l

/-- A successful lookup witnesses content presence. -/
theorem heap_ne_none_of_lookup {m : Memory} {n : Nat} {c : Cell}
    (h : m.lookup n = some c) : m.heap n ≠ none := by
  simp only [Memory.lookup] at h; rw [h]; exact Option.some_ne_none c

/-- Content presence transfers across memories that agree off a cell `c`. -/
theorem heap_ne_none_of_agree {m ma : Memory} {c y : Nat}
    (hag : ∀ l, l ≠ c → m.lookup l = ma.lookup l) (hyc : y ≠ c)
    (hy : m.heap y ≠ none) : ma.heap y ≠ none := by
  intro hn; apply hy
  change m.lookup y = none; rw [hag y hyc]; exact hn

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
  mcell_wf := by
    intro l' n' hlk
    have hl'l : l' ≠ l := by rintro rfl; simp [Heap.extend] at hlk
    rw [show (m.heap.extend l v) l' = m.heap l' from by simp [Heap.extend, hl'l]] at hlk
    have hpres := m.mcell_wf l' n' hlk
    rw [show (m.heap.extend l v) n' = m.heap n' from by
      simp [Heap.extend, present_ne_fresh hpres hfresh]]
    exact hpres

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
    · intro l' hv' hlookup
      unfold Heap.extend_cap at hlookup
      split at hlookup
      case isTrue heq =>
        cases hlookup
      case isFalse hneq =>
        exact Exp.wf_monotonic (Heap.extend_cap_subsumes hfresh) (m.wf.wf_val l' hv' hlookup)
    · intro l' v' hv' R' hlookup
      unfold Heap.extend_cap at hlookup
      split at hlookup
      case isTrue heq =>
        cases hlookup
      case isFalse hneq =>
        have heq := m.wf.wf_reach l' v' hv' R' hlookup
        rw [heq]
        exact (compute_reachability_monotonic (Heap.extend_cap_subsumes hfresh) v' hv'
          (m.wf.wf_val l' _ hlookup)).symm
    · intro l' v' hv' R' hlookup mu l'' hmem
      have hold : m.heap l'' ≠ none := by
        unfold Heap.extend_cap at hlookup
        split at hlookup
        case isTrue heq => cases hlookup
        case isFalse hneq =>
          exact m.wf.wf_reach_dom l' v' hv' R' hlookup mu l'' hmem
      unfold Heap.extend_cap
      split
      · intro hcontra; cases hcontra
      · exact hold
  findom :=
    let ⟨dom, hdom⟩ := m.findom
    ⟨dom ∪ {l}, Heap.extend_cap_has_fin_dom hdom hfresh⟩
  mcell_wf := by
    intro l' n' hlk
    have hl'l : l' ≠ l := by rintro rfl; simp [Heap.extend_cap] at hlk
    rw [show (m.heap.extend_cap l) l' = m.heap l' from by simp [Heap.extend_cap, hl'l]] at hlk
    have hpres := m.mcell_wf l' n' hlk
    rw [show (m.heap.extend_cap l) n' = m.heap n' from by
      simp [Heap.extend_cap, present_ne_fresh hpres hfresh]]
    exact hpres

/-- Heap extension with mcell subsumes original heap. -/
theorem Heap.extend_mcell_subsumes {H : Heap} {l : Nat} {n : Nat}
  (hfresh : H l = none) :
  (H.extend_mcell l n).subsumes H := by
  intro l' v' hlookup
  unfold Heap.extend_mcell
  split
  case isTrue heq =>
    subst heq
    rw [hfresh] at hlookup
    contradiction
  case isFalse =>
    exists v'
    exact ⟨hlookup, Cell.subsumes_refl v'⟩

theorem Heap.extend_mcell_has_fin_dom {H : Heap} {dom : Finset Nat} {l : Nat} {n : Nat}
  (hdom : H.HasFinDom dom) (hfresh : H l = none) :
  (H.extend_mcell l n).HasFinDom (dom ∪ {l}) := by
  intro l'
  unfold Heap.extend_mcell
  split
  case isTrue heq =>
    subst heq
    constructor
    · intro _; simp
    · intro _; simp
  case isFalse hneq =>
    constructor
    · intro h
      have : l' ∈ dom := (hdom l').mp h
      simp only [Finset.mem_union, Finset.mem_singleton, this, true_or]
    · intro h
      rw [Finset.mem_union, Finset.mem_singleton] at h
      rcases h with h | h
      · exact (hdom l').mpr h
      · contradiction

/-- Extend memory with a fresh mutable cell capability storing location `n`.
    The fresh cell is live, so its content `n` must already hold a value
    (`hcontent`) to preserve the content-closure invariant `mcell_wf`. -/
def extend_mcell (m : Memory) (l : Nat) (n : Nat)
  (hfresh : m.heap l = none)
  (hcontent : m.heap n ≠ none) : Memory where
  heap := m.heap.extend_mcell l n
  wf := by
    constructor
    · intro l' hv' hlookup
      unfold Heap.extend_mcell at hlookup
      split at hlookup
      case isTrue _ =>
        cases hlookup
      case isFalse _ =>
        exact Exp.wf_monotonic (Heap.extend_mcell_subsumes hfresh)
          (m.wf.wf_val l' hv' hlookup)
    · intro l' v' hv' R' hlookup
      unfold Heap.extend_mcell at hlookup
      split at hlookup
      case isTrue _ =>
        cases hlookup
      case isFalse _ =>
        have heq := m.wf.wf_reach l' v' hv' R' hlookup
        rw [heq]
        exact (compute_reachability_monotonic (Heap.extend_mcell_subsumes hfresh) v' hv'
          (m.wf.wf_val l' _ hlookup)).symm
    · intro l' v' hv' R' hlookup mu l'' hmem
      have hold : m.heap l'' ≠ none := by
        unfold Heap.extend_mcell at hlookup
        split at hlookup
        case isTrue _ => cases hlookup
        case isFalse _ =>
          exact m.wf.wf_reach_dom l' v' hv' R' hlookup mu l'' hmem
      unfold Heap.extend_mcell
      split
      · intro hcontra; cases hcontra
      · exact hold
  findom :=
    let ⟨dom, hdom⟩ := m.findom
    ⟨dom ∪ {l}, Heap.extend_mcell_has_fin_dom hdom hfresh⟩
  mcell_wf := by
    intro l' n' hlk
    by_cases hl'l : l' = l
    · simp only [Heap.extend_mcell] at hlk
      rw [if_pos hl'l] at hlk
      injection hlk with h; injection h with h2; injection h2 with hn _
      subst hn
      rw [show (m.heap.extend_mcell l n) n = m.heap n from by
        simp only [Heap.extend_mcell, if_neg (present_ne_fresh hcontent hfresh)]]
      exact hcontent
    · rw [show (m.heap.extend_mcell l n) l' = m.heap l' from by
        simp [Heap.extend_mcell, hl'l]] at hlk
      have hpres := m.mcell_wf l' n' hlk
      rw [show (m.heap.extend_mcell l n) n' = m.heap n' from by
        simp only [Heap.extend_mcell, if_neg (present_ne_fresh hpres hfresh)]]
      exact hpres

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
  mcell_wf := by
    intro l' n' hlk
    have hl'l : l' ≠ l := by rintro rfl; simp [Heap.extend] at hlk
    rw [show (m.heap.extend l v) l' = m.heap l' from by simp [Heap.extend, hl'l]] at hlk
    have hpres := m.mcell_wf l' n' hlk
    rw [show (m.heap.extend l v) n' = m.heap n' from by
      simp [Heap.extend, present_ne_fresh hpres hfresh]]
    exact hpres

/-- After updating the cell at `l`, location `k` is present whenever it is the updated
    location or was already present. -/
theorem Heap.update_cell_present {H : Heap} {l : Nat} {c : Cell} {k : Nat}
    (h : k = l ∨ H k ≠ none) : (H.update_cell l c) k ≠ none := by
  unfold Heap.update_cell
  rcases h with h | h
  · rw [if_pos h]; exact fun hc => by cases hc
  · split
    · exact fun hc => by cases hc
    · exact h

/-- Update a mutable cell in memory with a new stored heap location.
    Requires proof that the location contains a mutable cell with liveness `ℓ`.
    The update preserves the cell's liveness. -/
def update_mcell (m : Memory) (l : Nat) (n : Nat) (ℓ : Liveness)
  (hexists : ∃ n0, m.heap l = some (.capability (.mcell n0 ℓ)))
  (hcontent : ℓ = .live → m.heap n ≠ none) : Memory where
  heap := m.heap.update_cell l (.capability (.mcell n ℓ))
  wf := by
    constructor
    · intro l' hv' hlookup
      unfold Heap.update_cell at hlookup
      split at hlookup
      case isTrue heq =>
        cases hlookup
      case isFalse hneq =>
        have hwf_orig : hv'.unwrap.WfInHeap m.heap := m.wf.wf_val l' hv' hlookup
        have hsub : (m.heap.update_cell l (.capability (.mcell n ℓ))).subsumes m.heap :=
          Heap.update_mcell_subsumes m.heap l ℓ hexists n
        exact Exp.wf_monotonic hsub hwf_orig
    · intro l' v' hv' R' hlookup
      unfold Heap.update_cell at hlookup
      split at hlookup
      case isTrue heq =>
        cases hlookup
      case isFalse hneq =>
        have hreach_orig : R' = compute_reachability m.heap v' hv' :=
          m.wf.wf_reach l' v' hv' R' hlookup
        rw [hreach_orig]
        exact (compute_reachability_update_mcell m.heap l ℓ hexists n v' hv').symm
    · intro l' v' hv' R' hlookup mu l'' hmem
      have hold : m.heap l'' ≠ none := by
        unfold Heap.update_cell at hlookup
        split at hlookup
        case isTrue heq => cases hlookup
        case isFalse hneq =>
          exact m.wf.wf_reach_dom l' v' hv' R' hlookup mu l'' hmem
      unfold Heap.update_cell
      split
      · intro hcontra; cases hcontra
      · exact hold
  findom := by
    obtain ⟨dom, hdom⟩ := m.findom
    exists dom
    intro l'
    constructor
    · intro hne_none
      unfold Heap.update_cell at hne_none
      split at hne_none
      case isTrue heq =>
        obtain ⟨b0, hb0⟩ := hexists
        rw [←heq] at hb0
        apply (hdom l').mp
        intro hcontra
        rw [hb0] at hcontra
        cases hcontra
      case isFalse hneq =>
        exact (hdom l').mp hne_none
    · intro hin_dom
      unfold Heap.update_cell
      split
      case isTrue => simp
      case isFalse => exact (hdom l').mpr hin_dom
  mcell_wf := by
    intro l' n' hlk
    refine Heap.update_cell_present ?_
    by_cases hn'l : n' = l
    · exact Or.inl hn'l
    · refine Or.inr ?_
      by_cases hl'l : l' = l
      · simp only [Heap.update_cell] at hlk
        rw [if_pos hl'l] at hlk
        injection hlk with h; injection h with h2; injection h2 with hn hℓ
        subst hℓ
        rw [← hn]; exact hcontent rfl
      · rw [show (m.heap.update_cell l (.capability (.mcell n ℓ))) l' = m.heap l' from by
          simp [Heap.update_cell, hl'l]] at hlk
        exact m.mcell_wf l' n' hlk

/-- Mark a live mutable cell as dead.  This is the operational counterpart of
    the `drop` form: the cell remains in the heap (so locations referring to
    it stay well-formed) but is flagged `.dead`, ruling out future reads/writes
    by the live-only premises of `eval_read` / `eval_write_*`.

    Subsumption is *not* preserved by this operation: the dropped memory does
    not subsume the original (live ≠ dead), reflecting that drop is a
    destructive transition. -/
def drop_mcell (m : Memory) (l : Nat)
  (hexists : ∃ b0, m.heap l = some (.capability (.mcell b0 .live))) : Memory where
  heap := m.heap.update_cell l (.capability (.mcell 0 .dead))
  wf := by
    have hdom_sub :
        (m.heap.update_cell l (.capability (.mcell 0 .dead))).dom_subsumes m.heap := by
      intro l' v hlookup
      unfold Heap.update_cell
      by_cases hl : l' = l
      · subst hl; exact ⟨_, by rw [if_pos rfl]⟩
      · exact ⟨v, by rw [if_neg hl]; exact hlookup⟩
    constructor
    · intro l' hv' hlookup
      unfold Heap.update_cell at hlookup
      split at hlookup
      case isTrue _ => cases hlookup
      case isFalse _ =>
        exact Exp.wf_dom_subsumes hdom_sub (m.wf.wf_val l' hv' hlookup)
    · intro l' v' hv' R' hlookup
      unfold Heap.update_cell at hlookup
      split at hlookup
      case isTrue _ => cases hlookup
      case isFalse _ =>
        have heq := m.wf.wf_reach l' v' hv' R' hlookup
        rw [heq]
        exact (compute_reachability_drop_mcell m.heap l hexists v' hv').symm
    · intro l' v' hv' R' hlookup mu l'' hmem
      have hold : m.heap l'' ≠ none := by
        unfold Heap.update_cell at hlookup
        split at hlookup
        case isTrue _ => cases hlookup
        case isFalse _ =>
          exact m.wf.wf_reach_dom l' v' hv' R' hlookup mu l'' hmem
      unfold Heap.update_cell
      split
      · intro hcontra; cases hcontra
      · exact hold
  findom := by
    -- Domain unchanged: dropping replaces a `some` cell with another `some` cell.
    obtain ⟨dom, hdom⟩ := m.findom
    exists dom
    intro l'
    constructor
    · intro hne_none
      unfold Heap.update_cell at hne_none
      split at hne_none
      case isTrue heq =>
        obtain ⟨b0, hb0⟩ := hexists
        rw [←heq] at hb0
        apply (hdom l').mp
        intro hcontra
        rw [hb0] at hcontra
        cases hcontra
      case isFalse hneq =>
        exact (hdom l').mp hne_none
    · intro hin_dom
      unfold Heap.update_cell
      split
      case isTrue => simp
      case isFalse => exact (hdom l').mpr hin_dom
  mcell_wf := by
    intro l' n' hlk
    by_cases hl'l : l' = l
    · subst hl'l
      simp [Heap.update_cell] at hlk
    · rw [show (m.heap.update_cell l (.capability (.mcell 0 .dead))) l' = m.heap l' from by
        simp [Heap.update_cell, hl'l]] at hlk
      exact Heap.update_cell_present (Or.inr (m.mcell_wf l' n' hlk))

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
theorem update_mcell_subsumes (m : Memory) (l : Nat) (n : Nat) (ℓ : Liveness)
  (hexists : ∃ n0, m.heap l = some (.capability (.mcell n0 ℓ)))
  (hcontent : ℓ = .live → m.heap n ≠ none) :
  (m.update_mcell l n ℓ hexists hcontent).subsumes m := by
  change (m.heap.update_cell l (.capability (.mcell n ℓ))).subsumes m.heap
  exact Heap.update_mcell_subsumes m.heap l ℓ hexists n

/-- Extending two subsuming memories with the same mcell at the same location
preserves subsumption. -/
theorem extend_mcell_subsumes_compat {m1 m2 : Memory} (l : Nat) (n : Nat)
  (hfresh1 : m1.heap l = none) (hfresh2 : m2.heap l = none)
  (hcontent1 : m1.heap n ≠ none)
  (hcontent2 : m2.heap n ≠ none)
  (hsub : m2.subsumes m1) :
  (m2.extend_mcell l n hfresh2 hcontent2).subsumes (m1.extend_mcell l n hfresh1 hcontent1) := by
  change (m2.heap.extend_mcell l n).subsumes (m1.heap.extend_mcell l n)
  intro l' v hlookup
  unfold Heap.extend_mcell at hlookup ⊢
  by_cases hneq : l' = l
  · subst hneq
    rw [if_pos rfl] at hlookup
    cases hlookup
    exact ⟨_, by rw [if_pos rfl], Cell.subsumes_refl _⟩
  · rw [if_neg hneq] at hlookup
    obtain ⟨v', hlookup', hsub_v⟩ := hsub l' v hlookup
    exact ⟨v', by rw [if_neg hneq]; exact hlookup', hsub_v⟩

/-- Updating mcells in subsuming memories preserves subsumption.  Both memories
    must carry the same liveness for the cell, which is automatic for any pair
    related by `subsumes`. -/
theorem update_mcell_subsumes_compat {m1 m2 : Memory} (l : Nat) (n : Nat)
  (ℓ : Liveness)
  (hexists1 : ∃ n0, m1.heap l = some (.capability (.mcell n0 ℓ)))
  (hexists2 : ∃ n0, m2.heap l = some (.capability (.mcell n0 ℓ)))
  (hcontent1 : ℓ = .live → m1.heap n ≠ none)
  (hcontent2 : ℓ = .live → m2.heap n ≠ none)
  (hsub : m2.subsumes m1) :
  (m2.update_mcell l n ℓ hexists2 hcontent2).subsumes
    (m1.update_mcell l n ℓ hexists1 hcontent1) := by
  change (m2.heap.update_cell l (.capability (.mcell n ℓ))).subsumes
    (m1.heap.update_cell l (.capability (.mcell n ℓ)))
  unfold Heap.subsumes
  intro l' v hlookup
  unfold Heap.update_cell at hlookup ⊢
  by_cases hneq : l' = l
  · subst hneq
    rw [if_pos rfl] at hlookup
    cases hlookup
    refine ⟨.capability (.mcell n ℓ), ?_, ?_⟩
    · rw [if_pos rfl]
    · simp only [Cell.subsumes]; exact Liveness.Le.refl
  · rw [if_neg hneq] at hlookup
    exact ⟨_, by rw [if_neg hneq]; exact (hsub l' v hlookup).choose_spec.1,
           (hsub l' v hlookup).choose_spec.2⟩

/-- Dropping a live mutable cell yields a memory that subsumes the original:
    the cell transitions `live → dead`, allowed by `Liveness.Le.live_dead`. -/
theorem drop_mcell_subsumes (m : Memory) (l : Nat)
  (hexists : ∃ b0, m.heap l = some (.capability (.mcell b0 .live))) :
  (m.drop_mcell l hexists).subsumes m := by
  change (m.heap.update_cell l (.capability (.mcell 0 .dead))).subsumes m.heap
  intro l' v hlookup
  unfold Heap.update_cell
  by_cases hneq : l' = l
  · subst hneq
    obtain ⟨b0, hb0⟩ := hexists
    rw [hb0] at hlookup
    cases hlookup
    refine ⟨.capability (.mcell 0 .dead), ?_, ?_⟩
    · rw [if_pos rfl]
    · simp only [Cell.subsumes]; exact Liveness.Le.live_dead
  · refine ⟨v, ?_, Cell.subsumes_refl v⟩
    rw [if_neg hneq]; exact hlookup

/-- Dropping mcells in subsuming memories preserves subsumption.  The cell at
    `l` becomes `(.mcell 0 .dead)` in both heaps (so they agree exactly
    there); other cells are unchanged and the subsumption hypothesis carries
    them across. -/
theorem drop_mcell_subsumes_compat {m1 m2 : Memory} (l : Nat)
  (hexists1 : ∃ b0, m1.heap l = some (.capability (.mcell b0 .live)))
  (hexists2 : ∃ b0, m2.heap l = some (.capability (.mcell b0 .live)))
  (hsub : m2.subsumes m1) :
  (m2.drop_mcell l hexists2).subsumes (m1.drop_mcell l hexists1) := by
  change (m2.heap.update_cell l (.capability (.mcell 0 .dead))).subsumes
    (m1.heap.update_cell l (.capability (.mcell 0 .dead)))
  unfold Heap.subsumes
  intro l' v hlookup
  unfold Heap.update_cell at hlookup ⊢
  by_cases hneq : l' = l
  · subst hneq
    rw [if_pos rfl] at hlookup
    cases hlookup
    refine ⟨.capability (.mcell 0 .dead), ?_, ?_⟩
    · rw [if_pos rfl]
    · simp only [Cell.subsumes]; exact Liveness.Le.refl
  · rw [if_neg hneq] at hlookup
    exact ⟨_, by rw [if_neg hneq]; exact (hsub l' v hlookup).choose_spec.1,
           (hsub l' v hlookup).choose_spec.2⟩

/-- Looking up from a memory after extension at the same location returns the value. -/
theorem extend_lookup_eq (m : Memory) (l : Nat) (v : HeapVal)
  (hwf_v : Exp.WfInHeap v.unwrap m.heap)
  (hreach : v.reachability = compute_reachability m.heap v.unwrap v.isVal)
  (hfresh : m.heap l = none) :
  (m.extend l v hwf_v hreach hfresh).lookup l = some (.val v) := by
  simp only [lookup, extend, Heap.extend, if_true]

/-- Extension subsumes the original memory. -/
theorem extend_subsumes (m : Memory) (l : Nat) (v : HeapVal)
  (hwf_v : Exp.WfInHeap v.unwrap m.heap)
  (hreach : v.reachability = compute_reachability m.heap v.unwrap v.isVal)
  (hfresh : m.heap l = none) :
  (m.extend l v hwf_v hreach hfresh).subsumes m := by
  change (m.heap.extend l v).subsumes m.heap
  exact Heap.extend_subsumes hfresh

/-- Extension with extend_val subsumes the original memory. -/
theorem extend_val_subsumes (m : Memory) (l : Nat) (v : HeapVal)
  (hwf_v : Exp.WfInHeap v.unwrap m.heap)
  (hreach : v.reachability = compute_reachability m.heap v.unwrap v.isVal)
  (hfresh : m.heap l = none) :
  (m.extend_val l v hwf_v hreach hfresh).subsumes m := by
  change (m.heap.extend l v).subsumes m.heap
  exact Heap.extend_subsumes hfresh

/-- Capability extension subsumes the original memory. -/
theorem extend_cap_subsumes (m : Memory) (l : Nat)
  (hfresh : m.heap l = none) :
  (m.extend_cap l hfresh).subsumes m := by
  change (m.heap.extend_cap l).subsumes m.heap
  exact Heap.extend_cap_subsumes hfresh

/-- Mutable cell extension subsumes the original memory. -/
theorem extend_mcell_subsumes (m : Memory) (l : Nat) (n : Nat)
  (hfresh : m.heap l = none)
  (hcontent : m.heap n ≠ none) :
  (m.extend_mcell l n hfresh hcontent).subsumes m := by
  change (m.heap.extend_mcell l n).subsumes m.heap
  exact Heap.extend_mcell_subsumes hfresh

theorem extend_mcell_lookup {m : Memory} {l : Nat} {n : Nat}
  (hfresh : m.heap l = none)
  (hcontent : m.heap n ≠ none) :
  (m.extend_mcell l n hfresh hcontent).lookup l = some (.capability (.mcell n .live)) := by
  simp only [lookup, extend_mcell, Heap.extend_mcell, if_true]

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

/-- A memory is *compatible* with a capability set when every capability in the
    set whose location is realised as a mutable cell in the memory is currently
    `.live`.  Capabilities pointing at non-mcell locations (basic capabilities,
    values, masked, or absent) impose no liveness constraint. -/
def is_compatible (m : Memory) (C : CapabilitySet) : Prop :=
  ∀ mu l b ℓ,
    CapabilitySet.hasmem mu l C →
    m.heap l = some (.capability (.mcell b ℓ)) →
    ℓ = .live

theorem is_compatible_empty (m : Memory) : m.is_compatible .empty := by
  intro mu l b ℓ hmem _
  exact (CapabilitySet.not_hasmem_empty hmem).elim

theorem is_compatible_union_left {m : Memory} {C1 C2 : CapabilitySet}
  (hcompat : m.is_compatible (C1 ∪ C2)) : m.is_compatible C1 := by
  intro mu l b ℓ hmem hheap
  exact hcompat mu l b ℓ (CapabilitySet.hasmem.left hmem) hheap

theorem is_compatible_union_right {m : Memory} {C1 C2 : CapabilitySet}
  (hcompat : m.is_compatible (C1 ∪ C2)) : m.is_compatible C2 := by
  intro mu l b ℓ hmem hheap
  exact hcompat mu l b ℓ (CapabilitySet.hasmem.right hmem) hheap

/-- `Subset` preserves location membership (modulo mutability). -/
private theorem hasmem_of_subset {C1 C2 : CapabilitySet} (hsub : C1 ⊆ C2) :
    ∀ mu l, CapabilitySet.hasmem mu l C1 → ∃ mu', CapabilitySet.hasmem mu' l C2 := by
  induction hsub with
  | refl => intro mu l hmem; exact ⟨mu, hmem⟩
  | empty => intro _ _ hmem; exact (CapabilitySet.not_hasmem_empty hmem).elim
  | trans _ _ ih1 ih2 =>
    intro mu l hmem
    obtain ⟨mu', hmem'⟩ := ih1 mu l hmem
    exact ih2 mu' l hmem'
  | union_left _ _ ih1 ih2 =>
    intro mu l hmem
    cases hmem with
    | left hmem' => exact ih1 mu l hmem'
    | right hmem' => exact ih2 mu l hmem'
  | union_right_left =>
    intro mu l hmem; exact ⟨mu, CapabilitySet.hasmem.left hmem⟩
  | union_right_right =>
    intro mu l hmem; exact ⟨mu, CapabilitySet.hasmem.right hmem⟩
  | cap_ro =>
    intro mu l hmem; cases hmem
    exact ⟨.access .epsilon, CapabilitySet.hasmem.here⟩

/-- Disjointness is preserved when the left operand shrinks (`⊆`): any shared
location of `C1`/`C` is a shared location of the superset `C2`/`C`. -/
theorem _root_.CoreCapybara.CapabilitySet.disjoint.subset_left {C1 C2 C : CapabilitySet}
    (hsub : C1 ⊆ C2) (hdisj : CapabilitySet.disjoint C2 C) :
    CapabilitySet.disjoint C1 C := by
  intro mu1 mu2 l h1 h2
  obtain ⟨mu1', h1'⟩ := hasmem_of_subset hsub mu1 l h1
  exact hdisj mu1' mu2 l h1' h2

/-- `is_compatible` is anti-monotonic in the capability set: if `C1 ⊆ C2` and `m`
    is compatible with `C2`, then it is compatible with `C1`. The mutability shift
    in `Subset.cap_ro` is harmless because compatibility only checks the
    underlying location, not the mutability. -/
theorem is_compatible_subset {m : Memory} {C1 C2 : CapabilitySet}
    (hsub : C1 ⊆ C2) (hcompat : m.is_compatible C2) : m.is_compatible C1 := by
  intro mu l b ℓ hmem hheap
  obtain ⟨mu', hmem'⟩ := hasmem_of_subset hsub mu l hmem
  exact hcompat mu' l b ℓ hmem' hheap

/-- `is_compatible` is preserved by extending memory with a fresh value cell:
    the new cell holds a value, not a mutable cell, so it cannot break the
    liveness condition that `is_compatible` checks. -/
theorem is_compatible_extend_val (m : Memory) (l : Nat) (v : HeapVal)
    (hwf_v : Exp.WfInHeap v.unwrap m.heap)
    (hreach : v.reachability = compute_reachability m.heap v.unwrap v.isVal)
    (hfresh : m.heap l = none) {C : CapabilitySet}
    (hcompat : m.is_compatible C) :
    (m.extend_val l v hwf_v hreach hfresh).is_compatible C := by
  intro mu l' b ℓ hmem hheap
  change (m.heap.extend l v) l' = some (.capability (.mcell b ℓ)) at hheap
  unfold Heap.extend at hheap
  split at hheap
  · cases hheap
  · exact hcompat mu l' b ℓ hmem hheap

/-- `is_compatible` is preserved by extending memory with a fresh *live* mutable
    cell: the new cell is live, so it cannot violate the liveness condition. -/
theorem is_compatible_extend_mcell (m : Memory) (l : Nat) (n : Nat)
    (hfresh : m.heap l = none)
    (hcontent : m.heap n ≠ none) {C : CapabilitySet}
    (hcompat : m.is_compatible C) :
    (m.extend_mcell l n hfresh hcontent).is_compatible C := by
  intro mu l' b' ℓ hmem hheap
  change (m.heap.extend_mcell l n) l' = some (.capability (.mcell b' ℓ)) at hheap
  unfold Heap.extend_mcell at hheap
  split at hheap
  · injection hheap with hc; injection hc with hmc; injection hmc with _ hℓ; exact hℓ.symm
  · exact hcompat mu l' b' ℓ hmem hheap

/-- `is_compatible` is preserved by updating a mutable cell to a *live* value:
    the cell stays live, so the liveness condition is maintained. -/
theorem is_compatible_update_mcell (m : Memory) (l : Nat) (n : Nat)
    (hexists : ∃ n0, m.heap l = some (.capability (.mcell n0 .live)))
    (hcontent : m.heap n ≠ none) {C : CapabilitySet}
    (hcompat : m.is_compatible C) :
    (m.update_mcell l n .live hexists (fun _ => hcontent)).is_compatible C := by
  intro mu l' b' ℓ hmem hheap
  change (m.heap.update_cell l (.capability (.mcell n .live))) l' = some (.capability (.mcell b' ℓ))
    at hheap
  unfold Heap.update_cell at hheap
  split at hheap
  · injection hheap with hc; injection hc with hmc; injection hmc with _ hℓ; exact hℓ.symm
  · exact hcompat mu l' b' ℓ hmem hheap

/-- `is_compatible` is preserved by `drop_mcell` *provided the dropped location is
    not a member of the capability set*. Dropping marks the cell `.dead`, which
    would break liveness for that location — so we require it absent from `C`. -/
theorem is_compatible_drop_mcell (m : Memory) (l : Nat)
    (hexists : ∃ b0, m.heap l = some (.capability (.mcell b0 .live))) {C : CapabilitySet}
    (hnotin : ∀ mu, ¬ CapabilitySet.hasmem mu l C)
    (hcompat : m.is_compatible C) :
    (m.drop_mcell l hexists).is_compatible C := by
  intro mu l' b' ℓ hmem hheap
  change (m.heap.update_cell l (.capability (.mcell 0 .dead))) l'
    = some (.capability (.mcell b' ℓ)) at hheap
  unfold Heap.update_cell at hheap
  split at hheap
  · rename_i hl'eq; subst hl'eq; exact absurd hmem (hnotin mu)
  · exact hcompat mu l' b' ℓ hmem hheap

end Memory

/-- A single heap event.  `access` carries the `Mutability` that authorizes it
  (`.epsilon` = write, `.ro` = read), `alloc` records a fresh allocation, and
  `dealloc` records a drop. -/
inductive TraceItem : Type where
| access  : Mutability -> Nat -> TraceItem
| alloc   : Nat -> TraceItem
| dealloc : Nat -> TraceItem

/-- A trace records the heap accesses performed during evaluation, in order. -/
abbrev Trace : Type := List TraceItem

/-- `TraceOkFrom C A t` holds when every access/dealloc in `t` is either covered
  by the capability set `C`, or targets a location already allocated — recorded
  in `A`, the locations the trace has allocated so far.  Each `alloc` extends `A`
  for the remainder of the trace; an `alloc` itself needs no authority. -/
inductive TraceOkFrom (C : CapabilitySet) : List Nat -> Trace -> Prop where
| nil : TraceOkFrom C A []
| alloc :
  TraceOkFrom C (l :: A) t ->
  TraceOkFrom C A (.alloc l :: t)
| access :
  (C.covers (.access mu) l ∨ l ∈ A) ->
  TraceOkFrom C A t ->
  TraceOkFrom C A (.access mu l :: t)
| dealloc :
  (C.covers .drop l ∨ l ∈ A) ->
  TraceOkFrom C A t ->
  TraceOkFrom C A (.dealloc l :: t)

/-- A trace `t` is OK for a capability set `C` when every access/dealloc it
  performs is either covered by `C`, or targets a location it allocated earlier
  in `t` (hence freshly created during evaluation, and not governed by `C`). -/
def TraceOk (t : Trace) (C : CapabilitySet) : Prop := TraceOkFrom C [] t

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
  obtain ⟨dom, hdom⟩ := m.findom
  use dom.sup id + 1
  unfold Memory.lookup
  by_contra h
  have : dom.sup id + 1 ∈ dom := (hdom (dom.sup id + 1)).mp h
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
| .cap _ x => {x}

def Heap.not_mutated (init after : Heap) : Prop :=
  ∀ l b ℓ,
    init l = some (.capability (.mcell b ℓ)) ->
    after l = some (.capability (.mcell b ℓ))

def Memory.not_mutated (init after : Memory) : Prop :=
  init.heap.not_mutated after.heap

/-- `drops_authorized m1 m2 C` says that every memory cell which slips from
    `.live` in `m1` to `.dead` in `m2` is accounted for by `C` at `.drop`
    mode.  In other words, `C` authorizes every live-to-dead transition
    between `m1` and `m2`. -/
def Memory.drops_authorized (m1 m2 : Memory) (C : CapabilitySet) : Prop :=
  ∀ l b1 b2,
    m1.heap l = some (.capability (.mcell b1 .live)) →
    m2.heap l = some (.capability (.mcell b2 .dead)) →
    C.hasmem .drop l

/-- A memory is always `drops_authorized` with respect to itself, since no
    live-to-dead transitions can occur in a comparison of `m` against itself. -/
theorem Memory.drops_authorized_refl (m : Memory) (C : CapabilitySet) :
    m.drops_authorized m C := by
  intro l b1 b2 hlive hdead
  rw [hlive] at hdead
  cases hdead

/-- If the underlying heaps are equal, no live cell can have slipped to dead. -/
theorem Memory.drops_authorized_of_heap_eq
    {m1 m2 : Memory} {C : CapabilitySet} (h : m1.heap = m2.heap) :
    m1.drops_authorized m2 C := by
  intro l b1 b2 hlive hdead
  rw [h] at hlive
  rw [hlive] at hdead
  cases hdead

/-- If `m2` is not mutated with respect to `m1`, all `live` mcells stay
    `live`, so any `C` (including `∅`) authorizes the transition. -/
theorem Memory.drops_authorized_of_not_mutated
    {m1 m2 : Memory} {C : CapabilitySet} (h : m1.not_mutated m2) :
    m1.drops_authorized m2 C := by
  intro l b1 b2 hlive hdead
  have hpres := h l b1 .live hlive
  rw [hpres] at hdead
  cases hdead

/-- `.drop`-membership is preserved under `Subset`: the only `Subset` rule
    that changes mutability is `cap_ro`, which only affects `.access` modes,
    not `.drop`. -/
private theorem CapabilitySet.hasmem_drop_of_subset
    {C1 C2 : CapabilitySet} (hsub : C1 ⊆ C2)
    {l : Nat} (h : C1.hasmem .drop l) : C2.hasmem .drop l := by
  induction hsub with
  | refl => exact h
  | empty => exact (not_hasmem_empty h).elim
  | trans _ _ ih1 ih2 => exact ih2 (ih1 h)
  | union_left _ _ ih1 ih2 =>
    cases h with
    | left h' => exact ih1 h'
    | right h' => exact ih2 h'
  | union_right_left => exact hasmem.left h
  | union_right_right => exact hasmem.right h
  | cap_ro => cases h

/-- `drops_authorized` is monotonic in the capability set: enlarging `C`
    only weakens the obligation. -/
theorem Memory.drops_authorized_subset
    {m1 m2 : Memory} {C1 C2 : CapabilitySet}
    (h : m1.drops_authorized m2 C1) (hsub : C1 ⊆ C2) :
    m1.drops_authorized m2 C2 := by
  intro l b1 b2 hlive hdead
  exact CapabilitySet.hasmem_drop_of_subset hsub (h l b1 b2 hlive hdead)

/-- Drop authority can be widened to a union on the left. -/
theorem Memory.drops_authorized_union_left
    {m1 m2 : Memory} {C1 C2 : CapabilitySet}
    (h : m1.drops_authorized m2 C1) :
    m1.drops_authorized m2 (C1 ∪ C2) :=
  drops_authorized_subset h CapabilitySet.Subset.union_right_left

/-- Drop authority can be widened to a union on the right. -/
theorem Memory.drops_authorized_union_right
    {m1 m2 : Memory} {C1 C2 : CapabilitySet}
    (h : m1.drops_authorized m2 C2) :
    m1.drops_authorized m2 (C1 ∪ C2) :=
  drops_authorized_subset h CapabilitySet.Subset.union_right_right

/-- Composition: if `m2.subsumes m1`, the `C1`-authorized `m1 → m2` and the
    `C2`-authorized `m2 → m3` compose to a `(C1 ∪ C2)`-authorized `m1 → m3`.
    Every live cell in `m1` that ends up dead in `m3` either dropped during
    the first step (covered by `C1`) or during the second step (covered by
    `C2`). -/
theorem Memory.drops_authorized_trans
    {m1 m2 m3 : Memory} {C1 C2 : CapabilitySet}
    (hsub : m2.subsumes m1)
    (h12 : m1.drops_authorized m2 C1)
    (h23 : m2.drops_authorized m3 C2) :
    m1.drops_authorized m3 (C1 ∪ C2) := by
  intro l b1 b3 hlive hdead
  obtain ⟨c2, hm2_l, hsub_c⟩ := hsub l (.capability (.mcell b1 .live)) hlive
  cases c2 with
  | val _ =>
    simp only [Cell.subsumes] at hsub_c
    cases hsub_c
  | capability info =>
    cases info with
    | basic =>
      simp only [Cell.subsumes] at hsub_c
      cases hsub_c
    | mcell b2 ℓ2 =>
      simp only [Cell.subsumes] at hsub_c
      cases hsub_c with
      | refl =>
        exact CapabilitySet.hasmem.right (h23 l b2 b3 hm2_l hdead)
      | live_dead =>
        exact CapabilitySet.hasmem.left (h12 l b1 b2 hlive hm2_l)
  | masked =>
    simp only [Cell.subsumes] at hsub_c
    cases hsub_c

/-- Extending memory with a fresh value cell introduces no live-to-dead
    transitions, so any `C` authorizes it. -/
theorem Memory.extend_drops_authorized
    (m : Memory) (l : Nat) (v : HeapVal)
    (hwf_v : Exp.WfInHeap v.unwrap m.heap)
    (hreach : v.reachability = compute_reachability m.heap v.unwrap v.isVal)
    (hfresh : m.heap l = none) (C : CapabilitySet) :
    m.drops_authorized (m.extend l v hwf_v hreach hfresh) C := by
  intro l' b1 b2 hlive hdead
  unfold Memory.extend Heap.extend at hdead
  simp only at hdead
  by_cases hl : l' = l
  · subst hl
    rw [hfresh] at hlive
    cases hlive
  · rw [if_neg hl] at hdead
    rw [hlive] at hdead
    cases hdead

/-- Extending memory with a fresh mutable cell (starting `.live`) introduces
    no live-to-dead transitions, so any `C` authorizes it. -/
theorem Memory.extend_mcell_drops_authorized
    (m : Memory) (l : Nat) (n : Nat) (hfresh : m.heap l = none)
    (hcontent : m.heap n ≠ none)
    (C : CapabilitySet) :
    m.drops_authorized (m.extend_mcell l n hfresh hcontent) C := by
  intro l' b1 b2 hlive hdead
  unfold Memory.extend_mcell Heap.extend_mcell at hdead
  simp only at hdead
  by_cases hl : l' = l
  · subst hl
    rw [if_pos rfl] at hdead
    cases hdead
  · rw [if_neg hl] at hdead
    rw [hlive] at hdead
    cases hdead

/-- Extending memory with a fresh basic capability introduces no live-to-dead
    transitions, so any `C` authorizes it. -/
theorem Memory.extend_cap_drops_authorized
    (m : Memory) (l : Nat) (hfresh : m.heap l = none) (C : CapabilitySet) :
    m.drops_authorized (m.extend_cap l hfresh) C := by
  intro l' b1 b2 hlive hdead
  unfold Memory.extend_cap Heap.extend_cap at hdead
  simp only at hdead
  by_cases hl : l' = l
  · subst hl
    rw [if_pos rfl] at hdead
    cases hdead
  · rw [if_neg hl] at hdead
    rw [hlive] at hdead
    cases hdead

/-- Updating a mutable cell preserves its liveness, so any `C` authorizes
    the resulting transition. -/
theorem Memory.update_mcell_drops_authorized
    (m : Memory) (l : Nat) (n : Nat) (ℓ : Liveness)
    (hexists : ∃ n0, m.heap l = some (.capability (.mcell n0 ℓ)))
    (hcontent : ℓ = .live → m.heap n ≠ none)
    (C : CapabilitySet) :
    m.drops_authorized (m.update_mcell l n ℓ hexists hcontent) C := by
  intro l' b1 b2 hlive hdead
  unfold Memory.update_mcell Heap.update_cell at hdead
  simp only at hdead
  by_cases hl : l' = l
  · subst hl
    rw [if_pos rfl] at hdead
    cases hdead
    obtain ⟨b0, hb0⟩ := hexists
    rw [hb0] at hlive
    cases hlive
  · rw [if_neg hl] at hdead
    rw [hlive] at hdead
    cases hdead

/-- Dropping a live mutable cell requires the corresponding `.drop`
    capability in `C`. -/
theorem Memory.drop_mcell_drops_authorized
    (m : Memory) (l : Nat)
    (hexists : ∃ b0, m.heap l = some (.capability (.mcell b0 .live)))
    {C : CapabilitySet} (hmem : C.hasmem .drop l) :
    m.drops_authorized (m.drop_mcell l hexists) C := by
  intro l' b1 b2 hlive hdead
  unfold Memory.drop_mcell Heap.update_cell at hdead
  simp only at hdead
  by_cases hl : l' = l
  · subst hl; exact hmem
  · rw [if_neg hl] at hdead
    rw [hlive] at hdead
    cases hdead

/-- Non-interference checking for capability sets. -/
inductive CapabilitySet.Noninterference : CapabilitySet -> CapabilitySet -> Prop
| ni_symm :
  Noninterference cs1 cs2 ->
  Noninterference cs2 cs1
| ni_empty :
  Noninterference {} cs
| ni_union :
  Noninterference cs1 C ->
  Noninterference cs2 C ->
  Noninterference (cs1 ∪ cs2) C
| ni_ro :
  Noninterference (.cap (.access .ro) l1) (.cap (.access .ro) l2)
| ni_disj {m1 m2 : CapMode} :
  (l1 ≠ l2) ->
  Noninterference (.cap m1 l1) (.cap m2 l2)

namespace CapabilitySet.Noninterference

theorem split_union
  (hni : Noninterference R1 R2) :
  (∀ cs1 cs2,
    R1 = cs1 ∪ cs2 ->
    Noninterference cs1 R2 ∧ Noninterference cs2 R2) ∧
  (∀ cs1 cs2,
    R2 = cs1 ∪ cs2 ->
    Noninterference R1 cs1 ∧ Noninterference R1 cs2) := by
  induction hni with
  | ni_symm _ ih =>
    constructor
    · intro cs1 cs2 heq
      have ⟨_, h⟩ := ih
      have ⟨h1, h2⟩ := h cs1 cs2 heq
      exact ⟨ni_symm h1, ni_symm h2⟩
    · intro cs1 cs2 heq
      have ⟨h, _⟩ := ih
      have ⟨h1, h2⟩ := h cs1 cs2 heq
      exact ⟨ni_symm h1, ni_symm h2⟩
  | ni_empty =>
    constructor
    · intro cs1 cs2 heq
      cases heq
    · intro cs1 cs2 heq
      exact ⟨ni_empty, ni_empty⟩
  | ni_union hni1 hni2 ih1 ih2 =>
    constructor
    · intro cs1 cs2 heq
      cases heq
      exact ⟨hni1, hni2⟩
    · intro cs1 cs2 heq
      have ⟨_, h1⟩ := ih1
      have ⟨_, h2⟩ := ih2
      have ⟨h1a, h1b⟩ := h1 cs1 cs2 heq
      have ⟨h2a, h2b⟩ := h2 cs1 cs2 heq
      exact ⟨ni_union h1a h2a, ni_union h1b h2b⟩
  | ni_ro =>
    constructor <;> (intro cs1 cs2 heq; cases heq)
  | ni_disj hne =>
    constructor <;> (intro cs1 cs2 heq; cases heq)

theorem split_union_left
  (hni : Noninterference (cs1 ∪ cs2) R) :
  Noninterference cs1 R ∧ Noninterference cs2 R :=
  (split_union hni).left cs1 cs2 rfl

theorem split_union_right
  (hni : Noninterference R (cs1 ∪ cs2)) :
  Noninterference R cs1 ∧ Noninterference R cs2 :=
  (split_union hni).right cs1 cs2 rfl

theorem subset_left
  (hni : Noninterference cs1 cs2)
  (hsub : cs0 ⊆ cs1) :
  Noninterference cs0 cs2 := by
  induction hsub with
  | refl =>
    exact hni
  | empty =>
    exact ni_empty
  | trans _ _ ih1 ih2 =>
    exact ih1 (ih2 hni)
  | union_left _ _ ih1 ih2 =>
    exact ni_union (ih1 hni) (ih2 hni)
  | union_right_left =>
    exact (split_union_left hni).left
  | union_right_right =>
    exact (split_union_left hni).right
  | @cap_ro l =>
    exact weaken_epsilon_ro hni
where
  weaken_epsilon_ro_aux {l : Nat} {cs1 cs2 : CapabilitySet}
    (hni : Noninterference cs1 cs2) :
    (cs1 = .cap (.access .epsilon) l → Noninterference (.cap (.access .ro) l) cs2) ∧
    (cs2 = .cap (.access .epsilon) l → Noninterference cs1 (.cap (.access .ro) l)) := by
    induction hni with
    | ni_symm _ ih =>
      exact ⟨fun h => ni_symm (ih.2 h), fun h => ni_symm (ih.1 h)⟩
    | ni_empty =>
      constructor
      · intro h; cases h
      · intro _; exact ni_empty
    | ni_union _ _ ih1 ih2 =>
      constructor
      · intro h; cases h
      · intro h
        exact ni_union (ih1.2 h) (ih2.2 h)
    | ni_ro =>
      constructor <;> (intro h; cases h)
    | ni_disj hne =>
      constructor
      · intro h
        cases h
        exact ni_disj hne
      · intro h
        cases h
        exact ni_disj hne
  weaken_epsilon_ro {l : Nat} {cs : CapabilitySet}
    (hni : Noninterference (.cap (.access .epsilon) l) cs) :
    Noninterference (.cap (.access .ro) l) cs :=
    (weaken_epsilon_ro_aux hni).1 rfl

theorem subset_right
  (hni : Noninterference cs1 cs2)
  (hsub : cs2' ⊆ cs2) :
  Noninterference cs1 cs2' :=
  ni_symm (subset_left (ni_symm hni) hsub)

/-- At any shared location, two non-interfering sets agree that neither side is a
`.drop`: the only `Noninterference` constructor admitting a shared location is
`ni_ro`, where both modes are read-only. -/
theorem no_drop_share
  (hni : Noninterference C1 C2) :
  ∀ mu1 mu2 l, hasmem mu1 l C1 → hasmem mu2 l C2 → mu1 ≠ .drop ∧ mu2 ≠ .drop := by
  induction hni with
  | ni_symm _ ih =>
    intro mu1 mu2 l h1 h2
    exact (ih mu2 mu1 l h2 h1).symm
  | ni_empty =>
    intro mu1 mu2 l h1 _
    exact absurd h1 not_hasmem_empty
  | ni_union _ _ ih1 ih2 =>
    intro mu1 mu2 l h1 h2
    rw [hasmem_union_iff] at h1
    cases h1 with
    | inl h => exact ih1 mu1 mu2 l h h2
    | inr h => exact ih2 mu1 mu2 l h h2
  | ni_ro =>
    intro mu1 mu2 l h1 h2
    rw [hasmem_cap_iff] at h1 h2
    obtain ⟨rfl, _⟩ := h1
    obtain ⟨rfl, _⟩ := h2
    exact ⟨by nofun, by nofun⟩
  | ni_disj hne =>
    intro mu1 mu2 l h1 h2
    rw [hasmem_cap_iff] at h1 h2
    obtain ⟨_, rfl⟩ := h1
    obtain ⟨_, rfl⟩ := h2
    exact absurd rfl hne

/-- `Noninterference` implies the (asymmetric) runtime sequential-composition
obligation: nothing consumed (`.drop`) on the left is touched on the right. -/
theorem seqComp (hni : Noninterference C1 C2) : CapabilitySet.SeqComp C1 C2 := by
  intro mu l h1 h2
  exact (no_drop_share hni .drop mu l h1 h2).1 rfl

end CapabilitySet.Noninterference

/-- Compute the reachability of a capture set in a given memory. -/
def CaptureSet.reachability : CaptureSet {} -> Memory -> CapabilitySet
| .empty => fun _ => {}
| .union cs1 cs2 => fun m =>
  (cs1.reachability m) ∪ (cs2.reachability m)
| .var m' (.free x) => fun m => (reachability_of_loc m.heap x).applyAccess m'

/-- Members of a well-formed ground capture set's reachability are allocated:
stored reachability sets are domain-closed (`wf_reach_dom`), and syntactic
locations resolve through allocated cells. -/
theorem CaptureSet.reachability_dom {m : Memory} {cs : CaptureSet {}}
    {mu : CapMode} {l : Nat}
    (h : (cs.reachability m).hasmem mu l) : m.heap l ≠ none := by
  induction cs with
  | empty => exact absurd h CapabilitySet.not_hasmem_empty
  | union cs1 cs2 ih1 ih2 =>
    cases h with
    | left h => exact ih1 h
    | right h => exact ih2 h
  | var m0 x =>
    cases x with
    | bound bx => cases bx
    | free n =>
      obtain ⟨mu0, h0⟩ := CapabilitySet.hasmem_of_applyAccess' h
      exact reachability_of_loc_dom m.wf.wf_reach_dom h0
  | cvar _ c => cases c

/-- Reachability is preserved under memory subsumption when cs is well-formed. -/
theorem CaptureSet.reachability_monotonic
  {m1 m2 : Memory}
  (hsub : m2.subsumes m1)
  (cs : CaptureSet {})
  (hwf : CaptureSet.WfInHeap cs m1.heap) :
  cs.reachability m2 = cs.reachability m1 := by
  induction cs with
  | empty => rfl
  | var m x =>
    cases x with
    | bound x => cases x
    | free loc =>
      cases hwf with
      | wf_var_free hex =>
        simpa only [CaptureSet.reachability] using
          congrArg (CapabilitySet.applyAccess m) (reachability_of_loc_monotonic hsub loc hex)
  | cvar m C =>
    cases C
  | union cs1 cs2 ih1 ih2 =>
    cases hwf with
    | wf_union hwf1 hwf2 =>
      simp only [CaptureSet.reachability, ih1 hwf1, ih2 hwf2]

end CoreCapybara
