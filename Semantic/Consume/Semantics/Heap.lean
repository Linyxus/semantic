import Semantic.Consume.Syntax
import Semantic.Consume.Substitution
import Mathlib.Data.Finset.Basic

namespace Consume

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

/-- applyRO is idempotent. -/
@[simp]
theorem applyRO_applyRO {C : CapabilitySet} : C.applyRO.applyRO = C.applyRO := by
  induction C with
  | empty => rfl
  | cap m l => simp only [applyRO, CapMode.applyRO_idempotent]
  | union C1 C2 ih1 ih2 => simp only [applyRO, ih1, ih2]

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

/-- Coverage in C is preserved by applyRO when the mode is RO-stable (i.e.,
    `.access .ro` or `.drop`). -/
theorem covers_applyRO_of_covers {C : CapabilitySet} {m : CapMode}
    (h : covers m l C) (hfix : m = m.applyRO) : covers m l C.applyRO := by
  induction C generalizing m with
  | empty => cases h
  | cap m' l' =>
    cases h
    rename_i hle
    -- Goal: covers m l (cap m'.applyRO l')
    simp only [applyRO]
    apply covers.here
    cases hle with
    | access hmu =>
      rename_i mu1 mu2
      -- hfix : .access mu1 = (.access mu1).applyRO = .access .ro, so mu1 = .ro
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
    -- C.applyRO ⊆ C
    simp only [applyMut]
    induction C with
    | empty => exact Subset.refl
    | cap m' l =>
      -- Need: .cap m'.applyRO l ⊆ .cap m' l
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
      -- hle : m ≤ .access .ro, so m = .access .ro.
      cases hle with
      | access hmu =>
        cases hmu
        -- Goal: covers (.access .ro) x (cap (.access .epsilon) x)
        exact covers.here (.access Mutability.Le.ro_eps)

/-- If a capability set covers a location via an access cap, then the
    RO singleton is a subset of the set. -/
theorem covers_imp_singleton_subset {C : CapabilitySet} {m : Mutability} {x : Nat}
  (hcov : covers (.access m) x C) :
  {x} ⊆ C := by
  -- {x} = cap (.access .ro) x, so we need cap (.access .ro) x ⊆ C
  induction C with
  | empty => cases hcov
  | cap m' y =>
    cases hcov
    case here hle =>
      -- covers (.access m) x (cap m' x) with .access m ≤ m'
      cases hle with
      | access hmu =>
        -- m' = .access mu' with m ≤ mu'
        rename_i mu'
        cases mu' with
        | epsilon => exact Subset.cap_ro
        | ro =>
          -- m ≤ .ro means m = .ro
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
  -- singleton .epsilon x = cap (.access .epsilon) x
  induction C with
  | empty => cases hcov
  | cap m' y =>
    cases hcov
    case here hle =>
      -- covers (.access .epsilon) x (cap m' x) with .access .epsilon ≤ m'
      -- This means m' = .access .epsilon.
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
  -- Coverage at mu' passes through to applyRO at mu'.applyRO via
  -- `covers_applyRO_of_covers` after weakening to the RO image.
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
| mcell : Bool -> Liveness -> CapabilityInfo

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

/-- Heap extension with a fresh mutable cell capability.  Fresh cells start `.live`. -/
def Heap.extend_mcell (h : Heap) (l : Nat) (b : Bool) : Heap :=
  fun l' => if l' = l then some (.capability (.mcell b .live)) else h l'

/-- Update a cell in the heap with a new cell value. -/
def Heap.update_cell (h : Heap) (l : Nat) (c : Cell) : Heap :=
  fun l' => if l' = l then some c else h l'

/-- Auxiliary relation: one cell subsumes another.
    For mutable cells, the boolean value is irrelevant and liveness is allowed
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
  (hexists : ∃ b0, h l = some (.capability (.mcell b0 ℓ))) (b : Bool) :
  (h.update_cell l (.capability (.mcell b ℓ))).subsumes h := by
  intro l' v hlookup
  unfold Heap.update_cell
  split
  case isTrue heq =>
    subst heq
    obtain ⟨b0, hb0⟩ := hexists
    rw [hb0] at hlookup
    cases hlookup
    exact ⟨.capability (.mcell b ℓ), rfl, Liveness.Le.refl⟩
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
| wf_unit :
  Ty.WfInHeap .unit H
| wf_cap :
  CaptureSet.WfInHeap cs H ->
  Ty.WfInHeap (.cap cs) H
| wf_bool :
  Ty.WfInHeap .bool H
| wf_cell :
  CaptureSet.WfInHeap cs H ->
  Ty.WfInHeap (.cell cs) H
| wf_reader :
  CaptureSet.WfInHeap cs H ->
  Ty.WfInHeap (.reader cs) H
-- Existential types
| wf_exi :
  Ty.WfInHeap T H ->
  Ty.WfInHeap (.exi T) H
| wf_typ :
  Ty.WfInHeap T H ->
  Ty.WfInHeap (.typ T) H

def PureTy.WfInHeap (T : PureTy s) (H : Heap) : Prop :=
  Ty.WfInHeap T.core H

inductive Exp.WfInHeap : Exp s -> Heap -> Prop where
| wf_var :
  Var.WfInHeap x H ->
  Exp.WfInHeap (.var x) H
| wf_alloc :
  Var.WfInHeap x H ->
  Exp.WfInHeap (.alloc x) H
| wf_drop :
  Var.WfInHeap x H ->
  Exp.WfInHeap (.drop x) H
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
| wf_reader :
  Var.WfInHeap x H ->
  Exp.WfInHeap (.reader x) H
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
  PureTy.WfInHeap T H ->
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
  | arrow _ hcs _ ih1 ih2 =>
    exact Ty.WfInHeap.wf_arrow ih1 (CaptureSet.wf_of_closed hcs) ih2
  | poly _ hcs _ ih1 ih2 =>
    exact Ty.WfInHeap.wf_poly ih1 (CaptureSet.wf_of_closed hcs) ih2
  | cpoly hcb hcs _ ih =>
    exact Ty.WfInHeap.wf_cpoly (CaptureBound.wf_of_closed hcb)
                                (CaptureSet.wf_of_closed hcs) ih
  | unit => exact Ty.WfInHeap.wf_unit
  | cap hcs => exact Ty.WfInHeap.wf_cap (CaptureSet.wf_of_closed hcs)
  | bool => exact Ty.WfInHeap.wf_bool
  | cell hcs => exact Ty.WfInHeap.wf_cell (CaptureSet.wf_of_closed hcs)
  | reader hcs => exact Ty.WfInHeap.wf_reader (CaptureSet.wf_of_closed hcs)
  | exi _ ih => exact Ty.WfInHeap.wf_exi ih
  | typ _ ih => exact Ty.WfInHeap.wf_typ ih

/-- Closedness implies well-formedness for expressions. -/
theorem Exp.wf_of_closed {e : Exp s} {H : Heap}
  (hclosed : e.IsClosed) :
  Exp.WfInHeap e H := by
  induction hclosed with
  | var hx => exact Exp.WfInHeap.wf_var (Var.wf_of_closed hx)
  | abs hcs hT _ ih =>
    exact Exp.WfInHeap.wf_abs (CaptureSet.wf_of_closed hcs) (Ty.wf_of_closed hT) ih
  | tabs hcs hT _ ih =>
    exact Exp.WfInHeap.wf_tabs (CaptureSet.wf_of_closed hcs) (Ty.wf_of_closed hT) ih
  | cabs hcs hcb _ ih =>
    exact Exp.WfInHeap.wf_cabs (CaptureSet.wf_of_closed hcs) (CaptureBound.wf_of_closed hcb) ih
  | reader hx => exact Exp.WfInHeap.wf_reader (Var.wf_of_closed hx)
  | alloc hx => exact Exp.WfInHeap.wf_alloc (Var.wf_of_closed hx)
  | drop hx => exact Exp.WfInHeap.wf_drop (Var.wf_of_closed hx)
  | pack hcs hx =>
    exact Exp.WfInHeap.wf_pack (CaptureSet.wf_of_closed hcs) (Var.wf_of_closed hx)
  | app hx hy => exact Exp.WfInHeap.wf_app (Var.wf_of_closed hx) (Var.wf_of_closed hy)
  | tapp hx hT => exact Exp.WfInHeap.wf_tapp (Var.wf_of_closed hx) (Ty.wf_of_closed hT)
  | capp hx hcs => exact Exp.WfInHeap.wf_capp (Var.wf_of_closed hx) (CaptureSet.wf_of_closed hcs)
  | letin _ _ ih1 ih2 => exact Exp.WfInHeap.wf_letin ih1 ih2
  | unpack _ _ ih1 ih2 => exact Exp.WfInHeap.wf_unpack ih1 ih2
  | unit => exact Exp.WfInHeap.wf_unit
  | btrue => exact Exp.WfInHeap.wf_btrue
  | bfalse => exact Exp.WfInHeap.wf_bfalse
  | read hx => exact Exp.WfInHeap.wf_read (Var.wf_of_closed hx)
  | write hx hy => exact Exp.WfInHeap.wf_write (Var.wf_of_closed hx) (Var.wf_of_closed hy)
  | cond hx _ _ ih2 ih3 => exact Exp.WfInHeap.wf_cond (Var.wf_of_closed hx) ih2 ih3

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
  | wf_union _ _ ih1 ih2 =>
    exact CaptureSet.WfInHeap.wf_union (ih1 hsub) (ih2 hsub)
  | wf_var_free hex =>
    obtain ⟨v', hv', _⟩ := hsub _ _ hex
    exact CaptureSet.WfInHeap.wf_var_free hv'
  | wf_var_bound => exact CaptureSet.WfInHeap.wf_var_bound
  | wf_cvar => exact CaptureSet.WfInHeap.wf_cvar

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
  | wf_arrow _ hwf_cs _ ih1 ih2 =>
    exact Ty.WfInHeap.wf_arrow (ih1 hsub) (CaptureSet.wf_monotonic hsub hwf_cs) (ih2 hsub)
  | wf_poly _ hwf_cs _ ih1 ih2 =>
    exact Ty.WfInHeap.wf_poly (ih1 hsub) (CaptureSet.wf_monotonic hsub hwf_cs) (ih2 hsub)
  | wf_cpoly hwf_cb hwf_cs _ ih_T =>
    exact Ty.WfInHeap.wf_cpoly (CaptureBound.wf_monotonic hsub hwf_cb)
                                (CaptureSet.wf_monotonic hsub hwf_cs) (ih_T hsub)
  | wf_unit => exact Ty.WfInHeap.wf_unit
  | wf_cap hwf_cs => exact Ty.WfInHeap.wf_cap (CaptureSet.wf_monotonic hsub hwf_cs)
  | wf_bool => exact Ty.WfInHeap.wf_bool
  | wf_cell hwf_cs => exact Ty.WfInHeap.wf_cell (CaptureSet.wf_monotonic hsub hwf_cs)
  | wf_reader hwf_cs => exact Ty.WfInHeap.wf_reader (CaptureSet.wf_monotonic hsub hwf_cs)
  | wf_exi hwf ih => exact Ty.WfInHeap.wf_exi (ih hsub)
  | wf_typ hwf ih => exact Ty.WfInHeap.wf_typ (ih hsub)

theorem Exp.wf_monotonic
  {h1 h2 : Heap}
  (hsub : h2.subsumes h1)
  (hwf : Exp.WfInHeap e h1) :
  Exp.WfInHeap e h2 := by
  induction hwf generalizing h2 with
  | wf_var hwf_x => exact Exp.WfInHeap.wf_var (Var.wf_monotonic hsub hwf_x)
  | wf_abs hwf_cs hwf_T hwf_e ih_e =>
    exact Exp.WfInHeap.wf_abs (CaptureSet.wf_monotonic hsub hwf_cs)
                               (Ty.wf_monotonic hsub hwf_T) (ih_e hsub)
  | wf_tabs hwf_cs hwf_T hwf_e ih_e =>
    exact Exp.WfInHeap.wf_tabs (CaptureSet.wf_monotonic hsub hwf_cs)
                                (Ty.wf_monotonic hsub hwf_T) (ih_e hsub)
  | wf_cabs hwf_cs hwf_cb hwf_e ih_e =>
    exact Exp.WfInHeap.wf_cabs (CaptureSet.wf_monotonic hsub hwf_cs)
                                (CaptureBound.wf_monotonic hsub hwf_cb) (ih_e hsub)
  | wf_reader hwf_x => exact Exp.WfInHeap.wf_reader (Var.wf_monotonic hsub hwf_x)
  | wf_alloc hwf_x => exact Exp.WfInHeap.wf_alloc (Var.wf_monotonic hsub hwf_x)
  | wf_drop hwf_x => exact Exp.WfInHeap.wf_drop (Var.wf_monotonic hsub hwf_x)
  | wf_pack hwf_cs hwf_x =>
    exact Exp.WfInHeap.wf_pack (CaptureSet.wf_monotonic hsub hwf_cs)
                                (Var.wf_monotonic hsub hwf_x)
  | wf_app hwf_x hwf_y =>
    exact Exp.WfInHeap.wf_app (Var.wf_monotonic hsub hwf_x) (Var.wf_monotonic hsub hwf_y)
  | wf_tapp hwf_x hwf_T =>
    exact Exp.WfInHeap.wf_tapp (Var.wf_monotonic hsub hwf_x) (Ty.wf_monotonic hsub hwf_T)
  | wf_capp hwf_x hwf_cs =>
    exact Exp.WfInHeap.wf_capp (Var.wf_monotonic hsub hwf_x) (CaptureSet.wf_monotonic hsub hwf_cs)
  | wf_letin hwf1 hwf2 ih1 ih2 => exact Exp.WfInHeap.wf_letin (ih1 hsub) (ih2 hsub)
  | wf_unpack hwf1 hwf2 ih1 ih2 => exact Exp.WfInHeap.wf_unpack (ih1 hsub) (ih2 hsub)
  | wf_unit => exact Exp.WfInHeap.wf_unit
  | wf_btrue => exact Exp.WfInHeap.wf_btrue
  | wf_bfalse => exact Exp.WfInHeap.wf_bfalse
  | wf_read hwf_x => exact Exp.WfInHeap.wf_read (Var.wf_monotonic hsub hwf_x)
  | wf_write hwf_x hwf_y =>
    exact Exp.WfInHeap.wf_write (Var.wf_monotonic hsub hwf_x) (Var.wf_monotonic hsub hwf_y)
  | wf_cond hwf_x hwf2 hwf3 ih2 ih3 =>
    exact Exp.WfInHeap.wf_cond (Var.wf_monotonic hsub hwf_x) (ih2 hsub) (ih3 hsub)

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
    exact .wf_arrow (ih1 hsub) (CaptureSet.wf_dom_subsumes hsub hwf_cs) (ih2 hsub)
  | wf_poly _ hwf_cs _ ih1 ih2 =>
    exact .wf_poly (ih1 hsub) (CaptureSet.wf_dom_subsumes hsub hwf_cs) (ih2 hsub)
  | wf_cpoly hwf_cb hwf_cs _ ih_T =>
    exact .wf_cpoly (CaptureBound.wf_dom_subsumes hsub hwf_cb)
                    (CaptureSet.wf_dom_subsumes hsub hwf_cs) (ih_T hsub)
  | wf_cap hwf_cs => exact .wf_cap (CaptureSet.wf_dom_subsumes hsub hwf_cs)
  | wf_cell hwf_cs => exact .wf_cell (CaptureSet.wf_dom_subsumes hsub hwf_cs)
  | wf_reader hwf_cs => exact .wf_reader (CaptureSet.wf_dom_subsumes hsub hwf_cs)
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
  | wf_reader hwf_x => exact .wf_reader (Var.wf_dom_subsumes hsub hwf_x)
  | wf_alloc hwf_x => exact .wf_alloc (Var.wf_dom_subsumes hsub hwf_x)
  | wf_drop hwf_x => exact .wf_drop (Var.wf_dom_subsumes hsub hwf_x)
  | wf_pack hwf_cs hwf_x =>
    exact .wf_pack (CaptureSet.wf_dom_subsumes hsub hwf_cs)
                   (Var.wf_dom_subsumes hsub hwf_x)
  | wf_app hwf_x hwf_y =>
    exact .wf_app (Var.wf_dom_subsumes hsub hwf_x) (Var.wf_dom_subsumes hsub hwf_y)
  | wf_tapp hwf_x hwf_T =>
    exact .wf_tapp (Var.wf_dom_subsumes hsub hwf_x) (Ty.wf_dom_subsumes hsub hwf_T)
  | wf_capp hwf_x hwf_cs =>
    exact .wf_capp (Var.wf_dom_subsumes hsub hwf_x)
                   (CaptureSet.wf_dom_subsumes hsub hwf_cs)
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
    Applies the mutability from each captured variable to the result. -/
def expand_captures
  (h : Heap)
  (cs : CaptureSet {}) :
  CapabilitySet :=
  match cs with
  | .empty => {}
  | .var m (.free loc) => (reachability_of_loc h loc).applyMut m
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
  | .reader (.free x) => .singleton .ro x
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
        rw [hfx] at hres
        cases cell
        case val heapval =>
          cases hres
          -- hres now says: heapval.unwrap = v
          -- Need to show resolve m2.heap (.var (.free fx)) = some v
          -- We know hsub : H2.subsumes H1
          obtain ⟨v', hv', hsub_v⟩ := hsub fx (.val heapval) hfx
          -- For val cells, subsumes requires equality
          have hsub_v' : v' = .val heapval := by
            simpa only [Cell.subsumes] using hsub_v
          subst hsub_v'
          simp only [hv']
        case capability =>
          -- resolve yields none on capabilities; contradiction with hres
          simp at hres
        case masked =>
          -- resolve yields none on masked cells; contradiction
          simp at hres
    -- For .var (.bound _), already contradicted; done
  -- For other expressions, resolve returns them unchanged
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
  | var m x =>
    cases x with
    | bound x =>
      -- Impossible: no bound variables in empty signature
      cases x
    | free loc =>
      -- Variable case: use reachability_of_loc_monotonic
      -- Extract existence proof from well-formedness
      cases hwf with
      | wf_var_free hex =>
        -- We have hex : h1 loc = some cell_val
        simpa only [expand_captures] using
          congrArg (CapabilitySet.applyMut m) (reachability_of_loc_monotonic hsub loc hex)
  | cvar m C =>
    -- Impossible: no capability variables in empty signature
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
      simpa only [resolve_reachability] using
        reachability_of_loc_monotonic hsub fx hex
  | wf_abs hwf_cs _ _ =>
    simpa only [resolve_reachability] using
      expand_captures_monotonic hsub _ hwf_cs
  | wf_tabs hwf_cs _ _ =>
    simpa only [resolve_reachability] using
      expand_captures_monotonic hsub _ hwf_cs
  | wf_cabs hwf_cs _ =>
    simpa only [resolve_reachability] using
      expand_captures_monotonic hsub _ hwf_cs
  | wf_reader hwf_x =>
    cases hwf_x with
    | wf_bound => rename_i x; cases x
    | wf_free => simp only [resolve_reachability]
  | wf_alloc hwf_x =>
    cases hwf_x with
    | wf_bound => rename_i x; cases x
    | wf_free => simp only [resolve_reachability]
  | wf_drop _ | wf_pack _ _ | wf_app _ _ | wf_tapp _ _ | wf_capp _ _
  | wf_letin _ _ | wf_unpack _ _ | wf_unit | wf_btrue | wf_bfalse
  | wf_read _ | wf_write _ _ | wf_cond _ _ _ => simp only [resolve_reachability]

/-- Computing reachability of a value in a bigger heap yields the same result.
Proof by cases on hv, using expand_captures_monotonic. -/
theorem compute_reachability_monotonic
  {h1 h2 : Heap}
  (hsub : h2.subsumes h1)
  (v : Exp {})
  (hv : v.IsSimpleVal)
  (hwf : Exp.WfInHeap v h1) :
  compute_reachability h2 v hv = compute_reachability h1 v hv := by
  cases hv with
  | abs =>
    cases hwf with
    | wf_abs hwf_cs _ _ =>
      simpa only [compute_reachability] using
        expand_captures_monotonic hsub _ hwf_cs
  | tabs =>
    cases hwf with
    | wf_tabs hwf_cs _ _ =>
      simpa only [compute_reachability] using
        expand_captures_monotonic hsub _ hwf_cs
  | cabs =>
    cases hwf with
    | wf_cabs hwf_cs _ =>
      simpa only [compute_reachability] using
        expand_captures_monotonic hsub _ hwf_cs
  | reader =>
    rename_i x
    cases x with
    | free loc => simp only [compute_reachability]
    | bound bx => cases bx
  | unit | btrue | bfalse => rfl

/-- Updating an mcell preserves reachability_of_loc for all locations. -/
theorem reachability_of_loc_update_mcell (h : Heap) (l : Nat) (ℓ : Liveness)
  (hexists : ∃ b0, h l = some (.capability (.mcell b0 ℓ))) (b : Bool) (l' : Nat) :
  reachability_of_loc (h.update_cell l (.capability (.mcell b ℓ))) l' =
  reachability_of_loc h l' := by
  unfold reachability_of_loc Heap.update_cell
  by_cases heq : l' = l
  · -- l' = l case
    subst heq
    obtain ⟨b0, hb0⟩ := hexists
    simp only [hb0, if_true]
  · -- l' ≠ l case
    simp only [heq, if_false]

/-- Updating an mcell preserves expand_captures. -/
theorem expand_captures_update_mcell (h : Heap) (l : Nat) (ℓ : Liveness)
  (hexists : ∃ b0, h l = some (.capability (.mcell b0 ℓ))) (b : Bool) (cs : CaptureSet {}) :
  expand_captures (h.update_cell l (.capability (.mcell b ℓ))) cs =
  expand_captures h cs := by
  induction cs with
  | empty => rfl
  | var m x =>
    cases x with
    | bound bv => cases bv
    | free loc =>
      simpa only [expand_captures] using
        congrArg (CapabilitySet.applyMut m)
          (reachability_of_loc_update_mcell h l ℓ hexists b loc)
  | union cs1 cs2 ih1 ih2 =>
    simp only [expand_captures, ih1, ih2]
  | cvar m c => cases c

/-- Updating an mcell preserves compute_reachability. -/
theorem compute_reachability_update_mcell (h : Heap) (l : Nat) (ℓ : Liveness)
  (hexists : ∃ b0, h l = some (.capability (.mcell b0 ℓ))) (b : Bool)
  (v : Exp {}) (hv : v.IsSimpleVal) :
  compute_reachability (h.update_cell l (.capability (.mcell b ℓ))) v hv =
  compute_reachability h v hv := by
  cases hv with
  | abs =>
    simpa only [compute_reachability] using expand_captures_update_mcell h l ℓ hexists b _
  | tabs =>
    simpa only [compute_reachability] using expand_captures_update_mcell h l ℓ hexists b _
  | cabs =>
    simpa only [compute_reachability] using expand_captures_update_mcell h l ℓ hexists b _
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
  reachability_of_loc (h.update_cell l (.capability (.mcell false .dead))) l' =
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
  expand_captures (h.update_cell l (.capability (.mcell false .dead))) cs =
  expand_captures h cs := by
  induction cs with
  | empty => rfl
  | var m x =>
    cases x with
    | bound bv => cases bv
    | free loc =>
      simpa only [expand_captures] using
        congrArg (CapabilitySet.applyMut m)
          (reachability_of_loc_drop_mcell h l hexists loc)
  | union cs1 cs2 ih1 ih2 =>
    simp only [expand_captures, ih1, ih2]
  | cvar m c => cases c

/-- Dropping a live mcell preserves `compute_reachability`. -/
theorem compute_reachability_drop_mcell (h : Heap) (l : Nat)
  (hexists : ∃ b0, h l = some (.capability (.mcell b0 .live)))
  (v : Exp {}) (hv : v.IsSimpleVal) :
  compute_reachability (h.update_cell l (.capability (.mcell false .dead))) v hv =
  compute_reachability h v hv := by
  cases hv with
  | abs =>
    simpa only [compute_reachability] using expand_captures_drop_mcell h l hexists _
  | tabs =>
    simpa only [compute_reachability] using expand_captures_drop_mcell h l hexists _
  | cabs =>
    simpa only [compute_reachability] using expand_captures_drop_mcell h l hexists _
  | reader =>
    rename_i x
    cases x with
    | free loc => simp only [compute_reachability]
    | bound bx => cases bx
  | unit | btrue | bfalse => rfl

/-- A heap is well-formed if all values stored in it contain well-formed expressions. -/
structure Heap.WfHeap (H : Heap) : Prop where
  wf_val :
    ∀ l hv, H l = some (.val hv) -> Exp.WfInHeap hv.unwrap H
  wf_reach :
    ∀ l v hv R,
      H l = some (.val ⟨v, hv, R⟩) ->
        R = compute_reachability H v hv
  wf_reach_no_drop :
    ∀ l v hv R l',
      H l = some (.val ⟨v, hv, R⟩) ->
        ¬ CapabilitySet.hasmem .drop l' R

/-- The empty heap is well-formed. -/
theorem Heap.wf_empty : Heap.WfHeap ∅ := by
  constructor
  · intro l hv hlookup; cases hlookup
  · intros _ _ _ _ hlookup; cases hlookup
  · intros _ _ _ _ _ hlookup; cases hlookup

/-- `reachability_of_loc` is drop-free under any well-formed heap: capability,
    masked, and absent lookups produce singletons / empty, and stored
    `.val` reachabilities inherit drop-freeness from `wf_reach_no_drop`. -/
theorem reachability_of_loc_no_drop {H : Heap} {l l' : Nat}
    (hwf_H : H.WfHeap) :
    ¬ CapabilitySet.hasmem .drop l' (reachability_of_loc H l) := by
  intro hmem
  rcases hH : H l with _ | c
  · -- H l = none
    have : reachability_of_loc H l = {} := by
      simp only [reachability_of_loc, hH]
    rw [this] at hmem
    cases hmem
  · cases c with
    | val hv =>
      obtain ⟨v_u, v_iv, v_R⟩ := hv
      have hexpand : reachability_of_loc H l = v_R := by
        simp only [reachability_of_loc, hH]
      rw [hexpand] at hmem
      exact hwf_H.wf_reach_no_drop l v_u v_iv v_R l' hH hmem
    | capability _ =>
      have hexpand : reachability_of_loc H l = CapabilitySet.singleton .epsilon l := by
        simp only [reachability_of_loc, hH]
      rw [hexpand] at hmem
      exact CapabilitySet.singleton_no_drop hmem
    | masked =>
      have hexpand : reachability_of_loc H l = CapabilitySet.singleton .epsilon l := by
        simp only [reachability_of_loc, hH]
      rw [hexpand] at hmem
      exact CapabilitySet.singleton_no_drop hmem

/-- `expand_captures` is drop-free: source capture sets only carry `.access`
    modes via `Mutability`, and `applyMut`/`reachability_of_loc` both preserve
    drop-freeness. -/
theorem expand_captures_no_drop {H : Heap} {cs : CaptureSet {}} {l : Nat}
    (hwf_H : H.WfHeap) :
    ¬ CapabilitySet.hasmem .drop l (expand_captures H cs) := by
  induction cs with
  | empty =>
    intro hmem; simp only [expand_captures] at hmem; cases hmem
  | union cs1 cs2 ih1 ih2 =>
    intro hmem
    simp only [expand_captures] at hmem
    cases hmem with
    | left h' => exact ih1 h'
    | right h' => exact ih2 h'
  | var m x =>
    cases x with
    | bound bx => cases bx
    | free loc =>
      simp only [expand_captures]
      exact CapabilitySet.applyMut_no_drop (reachability_of_loc_no_drop hwf_H)
  | cvar m c => cases c

/-- `compute_reachability` is drop-free: each value form expands either to
    `expand_captures` (no drop) or to an explicit access singleton / empty. -/
theorem compute_reachability_no_drop {H : Heap} {v : Exp {}} {hv : v.IsSimpleVal}
    {l : Nat} (hwf_H : H.WfHeap) :
    ¬ CapabilitySet.hasmem .drop l (compute_reachability H v hv) := by
  cases hv with
  | abs =>
    simp only [compute_reachability]
    exact expand_captures_no_drop hwf_H
  | tabs =>
    simp only [compute_reachability]
    exact expand_captures_no_drop hwf_H
  | cabs =>
    simp only [compute_reachability]
    exact expand_captures_no_drop hwf_H
  | reader =>
    rename_i x
    cases x with
    | bound bx => cases bx
    | free _ =>
      intro hmem
      simp only [compute_reachability] at hmem
      cases hmem
  | unit =>
    intro hmem; simp only [compute_reachability] at hmem; cases hmem
  | btrue =>
    intro hmem; simp only [compute_reachability] at hmem; cases hmem
  | bfalse =>
    intro hmem; simp only [compute_reachability] at hmem; cases hmem

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
      exact Exp.wf_monotonic (Heap.extend_subsumes hfresh) hwf_v
    case isFalse hneq =>
      exact Exp.wf_monotonic (Heap.extend_subsumes hfresh) (hwf_H.wf_val l' hv' hlookup)
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
  · -- wf_reach_no_drop case
    intro l' v' hv' R' l_loc hlookup
    unfold Heap.extend at hlookup
    split at hlookup
    case isTrue heq =>
      cases hlookup
      -- New val cell: R' = v.reachability = compute_reachability H v.unwrap v.isVal.
      have heq_R : R' = compute_reachability H v' hv' := hreach
      rw [heq_R]
      exact compute_reachability_no_drop hwf_H
    case isFalse hneq =>
      exact hwf_H.wf_reach_no_drop l' v' hv' R' l_loc hlookup

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
    simp only [Var.rename]
    exact Var.WfInHeap.wf_bound
  | wf_free hex =>
    simp only [Var.rename]
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
    simp only [CaptureSet.rename]; exact CaptureSet.WfInHeap.wf_empty
  | wf_union _ _ ih1 ih2 =>
    simp only [CaptureSet.rename]; exact CaptureSet.WfInHeap.wf_union ih1 ih2
  | wf_var_free hex =>
    simp only [CaptureSet.rename]; exact CaptureSet.WfInHeap.wf_var_free hex
  | wf_var_bound =>
    simp only [CaptureSet.rename]; exact CaptureSet.WfInHeap.wf_var_bound
  | wf_cvar =>
    simp only [CaptureSet.rename]; exact CaptureSet.WfInHeap.wf_cvar

theorem CaptureBound.wf_rename
  {cb : CaptureBound s1}
  {f : Rename s1 s2}
  {H : Heap}
  (hwf : CaptureBound.WfInHeap cb H) :
  CaptureBound.WfInHeap (cb.rename f) H := by
  cases hwf with
  | wf_unbound =>
    simp only [CaptureBound.rename]
    exact CaptureBound.WfInHeap.wf_unbound
  | wf_bound hwf_cs =>
    simp only [CaptureBound.rename]
    exact CaptureBound.WfInHeap.wf_bound (CaptureSet.wf_rename hwf_cs)

/-- Renaming preserves well-formedness of types. -/
theorem Ty.wf_rename
  {T : Ty sort s1}
  {f : Rename s1 s2}
  {H : Heap}
  (hwf : Ty.WfInHeap T H) :
  Ty.WfInHeap (T.rename f) H := by
  induction hwf generalizing s2 with
  | wf_top => simp only [Ty.rename]; exact Ty.WfInHeap.wf_top
  | wf_tvar => simp only [Ty.rename]; exact Ty.WfInHeap.wf_tvar
  | wf_arrow _ hwf_cs _ ih1 ih2 =>
    simp only [Ty.rename]
    exact Ty.WfInHeap.wf_arrow ih1 (CaptureSet.wf_rename hwf_cs) ih2
  | wf_poly _ hwf_cs _ ih1 ih2 =>
    simp only [Ty.rename]
    exact Ty.WfInHeap.wf_poly ih1 (CaptureSet.wf_rename hwf_cs) ih2
  | wf_cpoly hwf_cb hwf_cs _ ih_T =>
    simp only [Ty.rename]
    exact Ty.WfInHeap.wf_cpoly (CaptureBound.wf_rename hwf_cb) (CaptureSet.wf_rename hwf_cs) ih_T
  | wf_unit => simp only [Ty.rename]; exact Ty.WfInHeap.wf_unit
  | wf_cap hwf_cs =>
    simp only [Ty.rename]; exact Ty.WfInHeap.wf_cap (CaptureSet.wf_rename hwf_cs)
  | wf_bool => simp only [Ty.rename]; exact Ty.WfInHeap.wf_bool
  | wf_cell hwf_cs =>
    simp only [Ty.rename]; exact Ty.WfInHeap.wf_cell (CaptureSet.wf_rename hwf_cs)
  | wf_reader hwf_cs =>
    simp only [Ty.rename]; exact Ty.WfInHeap.wf_reader (CaptureSet.wf_rename hwf_cs)
  | wf_exi _ ih => simp only [Ty.rename]; exact Ty.WfInHeap.wf_exi ih
  | wf_typ _ ih => simp only [Ty.rename]; exact Ty.WfInHeap.wf_typ ih

/-- Renaming preserves well-formedness of expressions. -/
theorem Exp.wf_rename
  {e : Exp s1}
  {f : Rename s1 s2}
  {H : Heap}
  (hwf : Exp.WfInHeap e H) :
  Exp.WfInHeap (e.rename f) H := by
  induction hwf generalizing s2 with
  | wf_var hwf_x =>
    simp only [Exp.rename]; exact Exp.WfInHeap.wf_var (Var.wf_rename hwf_x)
  | wf_abs hwf_cs hwf_T _ ih_e =>
    simp only [Exp.rename]
    exact Exp.WfInHeap.wf_abs (CaptureSet.wf_rename hwf_cs) (Ty.wf_rename hwf_T) ih_e
  | wf_tabs hwf_cs hwf_T _ ih_e =>
    simp only [Exp.rename]
    exact Exp.WfInHeap.wf_tabs (CaptureSet.wf_rename hwf_cs) (Ty.wf_rename hwf_T) ih_e
  | wf_cabs hwf_cs hwf_cb _ ih_e =>
    simp only [Exp.rename]
    exact Exp.WfInHeap.wf_cabs (CaptureSet.wf_rename hwf_cs) (CaptureBound.wf_rename hwf_cb) ih_e
  | wf_reader hwf_x =>
    simp only [Exp.rename]; exact Exp.WfInHeap.wf_reader (Var.wf_rename hwf_x)
  | wf_alloc hwf_x =>
    simp only [Exp.rename]; exact Exp.WfInHeap.wf_alloc (Var.wf_rename hwf_x)
  | wf_drop hwf_x =>
    simp only [Exp.rename]; exact Exp.WfInHeap.wf_drop (Var.wf_rename hwf_x)
  | wf_pack hwf_cs hwf_x =>
    simp only [Exp.rename]
    exact Exp.WfInHeap.wf_pack (CaptureSet.wf_rename hwf_cs) (Var.wf_rename hwf_x)
  | wf_app hwf_x hwf_y =>
    simp only [Exp.rename]; exact Exp.WfInHeap.wf_app (Var.wf_rename hwf_x) (Var.wf_rename hwf_y)
  | wf_tapp hwf_x hwf_T =>
    simp only [Exp.rename]; exact Exp.WfInHeap.wf_tapp (Var.wf_rename hwf_x) (Ty.wf_rename hwf_T)
  | wf_capp hwf_x hwf_cs =>
    simp only [Exp.rename]
    exact Exp.WfInHeap.wf_capp (Var.wf_rename hwf_x) (CaptureSet.wf_rename hwf_cs)
  | wf_letin _ _ ih1 ih2 =>
    simp only [Exp.rename]; exact Exp.WfInHeap.wf_letin ih1 ih2
  | wf_unpack _ _ ih1 ih2 =>
    simp only [Exp.rename]; exact Exp.WfInHeap.wf_unpack ih1 ih2
  | wf_unit => simp only [Exp.rename]; exact Exp.WfInHeap.wf_unit
  | wf_btrue => simp only [Exp.rename]; exact Exp.WfInHeap.wf_btrue
  | wf_bfalse => simp only [Exp.rename]; exact Exp.WfInHeap.wf_bfalse
  | wf_read hwf_x =>
    simp only [Exp.rename]; exact Exp.WfInHeap.wf_read (Var.wf_rename hwf_x)
  | wf_write hwf_x hwf_y =>
    simp only [Exp.rename]
    exact Exp.WfInHeap.wf_write (Var.wf_rename hwf_x) (Var.wf_rename hwf_y)
  | wf_cond hwf_x _ _ ih2 ih3 =>
    simp only [Exp.rename]; exact Exp.WfInHeap.wf_cond (Var.wf_rename hwf_x) ih2 ih3

-- Substitution well-formedness preservation

/-- A well-formed variable yields a well-formed capture set. -/
theorem CaptureSet.wf_of_var
  {m : Mutability}
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
      simp only [Subst.lift]; exact Var.WfInHeap.wf_bound
    | there x =>
      simp only [Subst.lift]; exact Var.wf_rename (hwf_σ.wf_var x)
  · intro X
    cases X with
    | here =>
      simp only [Subst.lift]; exact Ty.WfInHeap.wf_tvar
    | there X =>
      simp only [Subst.lift]; exact Ty.wf_rename (hwf_σ.wf_tvar X)
  · intro C
    cases C with
    | here =>
      simp only [Subst.lift]; exact CaptureSet.WfInHeap.wf_cvar
    | there C =>
      simp only [Subst.lift]; exact CaptureSet.wf_rename (hwf_σ.wf_cvar C)

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
    simp only [Var.subst]
    exact hwf_σ.wf_var x
  | free n =>
    simp only [Var.subst]
    cases hwf_x with
    | wf_free hex =>
      exact Var.WfInHeap.wf_free hex

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
  cases m
  · exact hwf
  · exact wf_applyRO hwf

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
    simp only [CaptureSet.subst]; exact CaptureSet.WfInHeap.wf_empty
  | wf_union _ _ ih1 ih2 =>
    simp only [CaptureSet.subst]; exact CaptureSet.WfInHeap.wf_union (ih1 hwf_σ) (ih2 hwf_σ)
  | wf_var_free hex =>
    simp only [CaptureSet.subst]; exact CaptureSet.WfInHeap.wf_var_free hex
  | wf_var_bound =>
    rename_i x H_wf
    simp only [CaptureSet.subst]
    exact CaptureSet.wf_of_var (Var.wf_subst Var.WfInHeap.wf_bound hwf_σ)
  | wf_cvar =>
    simp only [CaptureSet.subst]; exact CaptureSet.wf_applyMut (hwf_σ.wf_cvar _)

theorem CaptureBound.wf_subst
  {cb : CaptureBound s1}
  {σ : Subst s1 s2}
  {H : Heap}
  (hwf_cb : CaptureBound.WfInHeap cb H)
  (hwf_σ : σ.WfInHeap H) :
  CaptureBound.WfInHeap (cb.subst σ) H := by
  cases hwf_cb with
  | wf_unbound =>
    simp only [CaptureBound.subst]
    exact CaptureBound.WfInHeap.wf_unbound
  | wf_bound hwf_cs =>
    simp only [CaptureBound.subst]
    exact CaptureBound.WfInHeap.wf_bound (CaptureSet.wf_subst hwf_cs hwf_σ)

/-- Well-formed substitutions preserve well-formedness of types. -/
theorem Ty.wf_subst
  {T : Ty sort s1}
  {σ : Subst s1 s2}
  {H : Heap}
  (hwf_T : Ty.WfInHeap T H)
  (hwf_σ : σ.WfInHeap H) :
  Ty.WfInHeap (T.subst σ) H := by
  induction hwf_T generalizing s2 with
  | wf_top => simp only [Ty.subst]; exact Ty.WfInHeap.wf_top
  | wf_tvar => simp only [Ty.subst]; exact hwf_σ.wf_tvar _
  | wf_arrow _ hwf_cs _ ih1 ih2 =>
    simp only [Ty.subst]
    exact Ty.WfInHeap.wf_arrow (ih1 hwf_σ) (CaptureSet.wf_subst hwf_cs hwf_σ)
                                (ih2 (Subst.wf_lift hwf_σ))
  | wf_poly _ hwf_cs _ ih1 ih2 =>
    simp only [Ty.subst]
    exact Ty.WfInHeap.wf_poly (ih1 hwf_σ) (CaptureSet.wf_subst hwf_cs hwf_σ)
                               (ih2 (Subst.wf_lift hwf_σ))
  | wf_cpoly hwf_cb hwf_cs _ ih_T =>
    simp only [Ty.subst]
    exact Ty.WfInHeap.wf_cpoly (CaptureBound.wf_subst hwf_cb hwf_σ)
                                (CaptureSet.wf_subst hwf_cs hwf_σ)
                                (ih_T (Subst.wf_lift hwf_σ))
  | wf_unit => simp only [Ty.subst]; exact Ty.WfInHeap.wf_unit
  | wf_cap hwf_cs =>
    simp only [Ty.subst]; exact Ty.WfInHeap.wf_cap (CaptureSet.wf_subst hwf_cs hwf_σ)
  | wf_bool => simp only [Ty.subst]; exact Ty.WfInHeap.wf_bool
  | wf_cell hwf_cs =>
    simp only [Ty.subst]; exact Ty.WfInHeap.wf_cell (CaptureSet.wf_subst hwf_cs hwf_σ)
  | wf_reader hwf_cs =>
    simp only [Ty.subst]; exact Ty.WfInHeap.wf_reader (CaptureSet.wf_subst hwf_cs hwf_σ)
  | wf_exi _ ih =>
    simp only [Ty.subst]; exact Ty.WfInHeap.wf_exi (ih (Subst.wf_lift hwf_σ))
  | wf_typ _ ih =>
    simp only [Ty.subst]; exact Ty.WfInHeap.wf_typ (ih hwf_σ)

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
    simp only [Exp.subst]; exact Exp.WfInHeap.wf_var (Var.wf_subst hwf_x hwf_σ)
  | wf_abs hwf_cs hwf_T _ ih_e =>
    simp only [Exp.subst]
    exact Exp.WfInHeap.wf_abs (CaptureSet.wf_subst hwf_cs hwf_σ) (Ty.wf_subst hwf_T hwf_σ)
                               (ih_e (Subst.wf_lift hwf_σ))
  | wf_tabs hwf_cs hwf_T _ ih_e =>
    simp only [Exp.subst]
    exact Exp.WfInHeap.wf_tabs (CaptureSet.wf_subst hwf_cs hwf_σ) (Ty.wf_subst hwf_T hwf_σ)
                                (ih_e (Subst.wf_lift hwf_σ))
  | wf_cabs hwf_cs hwf_cb _ ih_e =>
    simp only [Exp.subst]
    exact Exp.WfInHeap.wf_cabs (CaptureSet.wf_subst hwf_cs hwf_σ)
                                (CaptureBound.wf_subst hwf_cb hwf_σ)
                                (ih_e (Subst.wf_lift hwf_σ))
  | wf_reader hwf_x =>
    simp only [Exp.subst]; exact Exp.WfInHeap.wf_reader (Var.wf_subst hwf_x hwf_σ)
  | wf_alloc hwf_x =>
    simp only [Exp.subst]; exact Exp.WfInHeap.wf_alloc (Var.wf_subst hwf_x hwf_σ)
  | wf_drop hwf_x =>
    simp only [Exp.subst]; exact Exp.WfInHeap.wf_drop (Var.wf_subst hwf_x hwf_σ)
  | wf_pack hwf_cs hwf_x =>
    simp only [Exp.subst]
    exact Exp.WfInHeap.wf_pack (CaptureSet.wf_subst hwf_cs hwf_σ) (Var.wf_subst hwf_x hwf_σ)
  | wf_app hwf_x hwf_y =>
    simp only [Exp.subst]
    exact Exp.WfInHeap.wf_app (Var.wf_subst hwf_x hwf_σ) (Var.wf_subst hwf_y hwf_σ)
  | wf_tapp hwf_x hwf_T =>
    simp only [Exp.subst]
    exact Exp.WfInHeap.wf_tapp (Var.wf_subst hwf_x hwf_σ) (Ty.wf_subst hwf_T hwf_σ)
  | wf_capp hwf_x hwf_cs =>
    simp only [Exp.subst]
    exact Exp.WfInHeap.wf_capp (Var.wf_subst hwf_x hwf_σ) (CaptureSet.wf_subst hwf_cs hwf_σ)
  | wf_letin _ _ ih1 ih2 =>
    simp only [Exp.subst]
    exact Exp.WfInHeap.wf_letin (ih1 hwf_σ) (ih2 (Subst.wf_lift hwf_σ))
  | wf_unpack _ _ ih1 ih2 =>
    simp only [Exp.subst]
    exact Exp.WfInHeap.wf_unpack (ih1 hwf_σ) (ih2 (Subst.wf_lift (Subst.wf_lift hwf_σ)))
  | wf_unit => simp only [Exp.subst]; exact Exp.WfInHeap.wf_unit
  | wf_btrue => simp only [Exp.subst]; exact Exp.WfInHeap.wf_btrue
  | wf_bfalse => simp only [Exp.subst]; exact Exp.WfInHeap.wf_bfalse
  | wf_read hwf_x =>
    simp only [Exp.subst]; exact Exp.WfInHeap.wf_read (Var.wf_subst hwf_x hwf_σ)
  | wf_write hwf_x hwf_y =>
    simp only [Exp.subst]
    exact Exp.WfInHeap.wf_write (Var.wf_subst hwf_x hwf_σ) (Var.wf_subst hwf_y hwf_σ)
  | wf_cond hwf_x hwf2 hwf3 ih2 ih3 =>
    simp only [Exp.subst]
    exact Exp.WfInHeap.wf_cond (Var.wf_subst hwf_x hwf_σ) (ih2 hwf_σ) (ih3 hwf_σ)

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
      simp only [Subst.openVar]
      exact hwf_x
    | there y0 =>
      simp only [Subst.openVar]
      exact Var.WfInHeap.wf_bound
  · intro X
    cases X with
    | there X0 =>
      simp only [Subst.openVar]
      exact Ty.WfInHeap.wf_tvar
  · intro C
    cases C with
    | there C0 =>
      simp only [Subst.openVar]
      exact CaptureSet.WfInHeap.wf_cvar

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
      simp only [Subst.openTVar]; exact Var.WfInHeap.wf_bound
  · intro X
    cases X with
    | here =>
      simp only [Subst.openTVar]; exact hwf_U
    | there X0 =>
      simp only [Subst.openTVar]
      unfold PureTy.WfInHeap
      exact Ty.WfInHeap.wf_tvar
  · intro C
    cases C with
    | there C0 =>
      simp only [Subst.openTVar]; exact CaptureSet.WfInHeap.wf_cvar

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
      simp only [Subst.openCVar]; exact Var.WfInHeap.wf_bound
  · intro X
    cases X with
    | there X0 =>
      simp only [Subst.openCVar]; exact Ty.WfInHeap.wf_tvar
  · intro C_var
    cases C_var with
    | here =>
      simp only [Subst.openCVar]; exact hwf_C
    | there C0 =>
      simp only [Subst.openCVar]; exact CaptureSet.WfInHeap.wf_cvar

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
      simp only [Subst.unpack]
      exact hwf_x
    | there y' =>
      cases y' with
      | there y0 =>
        -- .there (.there y0) maps to .bound y0
        simp only [Subst.unpack]; exact Var.WfInHeap.wf_bound
  · intro X
    cases X with
    | there X' =>
      cases X' with
      | there X0 =>
        -- .there (.there X0) maps to .tvar X0
        simp only [Subst.unpack]; exact Ty.WfInHeap.wf_tvar
  · intro C_var
    cases C_var with
    | there C' =>
      cases C' with
      | here =>
        -- .there .here maps to C
        simp only [Subst.unpack]; exact hwf_C
      | there C0 =>
        -- .there (.there C0) maps to .cvar C0
        simp only [Subst.unpack]; exact CaptureSet.WfInHeap.wf_cvar

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
      simp only [Finset.mem_union, Finset.mem_singleton, this, true_or]
    · intro h
      rw [Finset.mem_union, Finset.mem_singleton] at h
      rcases h with h | h
      · -- h : l' ∈ dom
        exact (hdom l').mpr h
      · -- h : l' = l, but we have hneq : ¬l' = l
        contradiction

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
      simp only [Finset.mem_union, Finset.mem_singleton, this, true_or]
    · intro h
      rw [Finset.mem_union, Finset.mem_singleton] at h
      rcases h with h | h
      · -- h : l' ∈ dom
        exact (hdom l').mpr h
      · -- h : l' = l, but we have hneq : ¬l' = l
        contradiction

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
        exact Exp.wf_monotonic (Heap.extend_cap_subsumes hfresh) (m.wf.wf_val l' hv' hlookup)
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
    · -- wf_reach_no_drop case
      intro l' v' hv' R' l_loc hlookup
      unfold Heap.extend_cap at hlookup
      split at hlookup
      case isTrue _ => cases hlookup
      case isFalse _ =>
        exact m.wf.wf_reach_no_drop l' v' hv' R' l_loc hlookup
  findom :=
    let ⟨dom, hdom⟩ := m.findom
    ⟨dom ∪ {l}, Heap.extend_cap_has_fin_dom hdom hfresh⟩

/-- Heap extension with mcell subsumes original heap. -/
theorem Heap.extend_mcell_subsumes {H : Heap} {l : Nat} {b : Bool}
  (hfresh : H l = none) :
  (H.extend_mcell l b).subsumes H := by
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

theorem Heap.extend_mcell_has_fin_dom {H : Heap} {dom : Finset Nat} {l : Nat} {b : Bool}
  (hdom : H.HasFinDom dom) (hfresh : H l = none) :
  (H.extend_mcell l b).HasFinDom (dom ∪ {l}) := by
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

/-- Extend memory with a fresh mutable cell capability. -/
def extend_mcell (m : Memory) (l : Nat) (b : Bool)
  (hfresh : m.heap l = none) : Memory where
  heap := m.heap.extend_mcell l b
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
    · -- wf_reach_no_drop case
      intro l' v' hv' R' l_loc hlookup
      unfold Heap.extend_mcell at hlookup
      split at hlookup
      case isTrue _ => cases hlookup
      case isFalse _ =>
        exact m.wf.wf_reach_no_drop l' v' hv' R' l_loc hlookup
  findom :=
    let ⟨dom, hdom⟩ := m.findom
    ⟨dom ∪ {l}, Heap.extend_mcell_has_fin_dom hdom hfresh⟩

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

/-- Update a mutable cell in memory with a new boolean value.
    Requires proof that the location contains a mutable cell with liveness `ℓ`.
    The update preserves the cell's liveness. -/
def update_mcell (m : Memory) (l : Nat) (b : Bool) (ℓ : Liveness)
  (hexists : ∃ b0, m.heap l = some (.capability (.mcell b0 ℓ))) : Memory where
  heap := m.heap.update_cell l (.capability (.mcell b ℓ))
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
        have hsub : (m.heap.update_cell l (.capability (.mcell b ℓ))).subsumes m.heap :=
          Heap.update_mcell_subsumes m.heap l ℓ hexists b
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
        exact (compute_reachability_update_mcell m.heap l ℓ hexists b v' hv').symm
    · -- wf_reach_no_drop case
      intro l' v' hv' R' l_loc hlookup
      unfold Heap.update_cell at hlookup
      split at hlookup
      case isTrue _ => cases hlookup
      case isFalse _ =>
        exact m.wf.wf_reach_no_drop l' v' hv' R' l_loc hlookup
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

/-- Mark a live mutable cell as dead.  This is the operational counterpart of
    the `drop` form: the cell remains in the heap (so locations referring to
    it stay well-formed) but is flagged `.dead`, ruling out future reads/writes
    by the live-only premises of `eval_read` / `eval_write_*`.

    Subsumption is *not* preserved by this operation: the dropped memory does
    not subsume the original (live ≠ dead), reflecting that drop is a
    destructive transition. -/
def drop_mcell (m : Memory) (l : Nat)
  (hexists : ∃ b0, m.heap l = some (.capability (.mcell b0 .live))) : Memory where
  heap := m.heap.update_cell l (.capability (.mcell false .dead))
  wf := by
    -- The new heap dominates the old domain: only the cell at `l` changes,
    -- and it remains `some _`.
    have hdom_sub :
        (m.heap.update_cell l (.capability (.mcell false .dead))).dom_subsumes m.heap := by
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
    · -- wf_reach_no_drop case
      intro l' v' hv' R' l_loc hlookup
      unfold Heap.update_cell at hlookup
      split at hlookup
      case isTrue _ => cases hlookup
      case isFalse _ =>
        exact m.wf.wf_reach_no_drop l' v' hv' R' l_loc hlookup
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
theorem update_mcell_subsumes (m : Memory) (l : Nat) (b : Bool) (ℓ : Liveness)
  (hexists : ∃ b0, m.heap l = some (.capability (.mcell b0 ℓ))) :
  (m.update_mcell l b ℓ hexists).subsumes m := by
  change (m.heap.update_cell l (.capability (.mcell b ℓ))).subsumes m.heap
  exact Heap.update_mcell_subsumes m.heap l ℓ hexists b

/-- Extending two subsuming memories with the same mcell at the same location
preserves subsumption. -/
theorem extend_mcell_subsumes_compat {m1 m2 : Memory} (l : Nat) (b : Bool)
  (hfresh1 : m1.heap l = none) (hfresh2 : m2.heap l = none)
  (hsub : m2.subsumes m1) :
  (m2.extend_mcell l b hfresh2).subsumes (m1.extend_mcell l b hfresh1) := by
  change (m2.heap.extend_mcell l b).subsumes (m1.heap.extend_mcell l b)
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
theorem update_mcell_subsumes_compat {m1 m2 : Memory} (l : Nat) (b : Bool)
  (ℓ : Liveness)
  (hexists1 : ∃ b0, m1.heap l = some (.capability (.mcell b0 ℓ)))
  (hexists2 : ∃ b0, m2.heap l = some (.capability (.mcell b0 ℓ)))
  (hsub : m2.subsumes m1) :
  (m2.update_mcell l b ℓ hexists2).subsumes (m1.update_mcell l b ℓ hexists1) := by
  change (m2.heap.update_cell l (.capability (.mcell b ℓ))).subsumes
    (m1.heap.update_cell l (.capability (.mcell b ℓ)))
  unfold Heap.subsumes
  intro l' v hlookup
  unfold Heap.update_cell at hlookup ⊢
  by_cases hneq : l' = l
  · subst hneq
    rw [if_pos rfl] at hlookup
    cases hlookup
    refine ⟨.capability (.mcell b ℓ), ?_, ?_⟩
    · rw [if_pos rfl]
    · simp only [Cell.subsumes]; exact Liveness.Le.refl
  · rw [if_neg hneq] at hlookup
    exact ⟨_, by rw [if_neg hneq]; exact (hsub l' v hlookup).choose_spec.1,
           (hsub l' v hlookup).choose_spec.2⟩

/-- Dropping a live mutable cell yields a memory that subsumes the original.
    With the relaxed `Cell.subsumes`, this is now sound: the cell transitions
    `live → dead`, which is allowed by `Liveness.Le.live_dead`. -/
theorem drop_mcell_subsumes (m : Memory) (l : Nat)
  (hexists : ∃ b0, m.heap l = some (.capability (.mcell b0 .live))) :
  (m.drop_mcell l hexists).subsumes m := by
  change (m.heap.update_cell l (.capability (.mcell false .dead))).subsumes m.heap
  intro l' v hlookup
  unfold Heap.update_cell
  by_cases hneq : l' = l
  · subst hneq
    obtain ⟨b0, hb0⟩ := hexists
    rw [hb0] at hlookup
    cases hlookup
    refine ⟨.capability (.mcell false .dead), ?_, ?_⟩
    · rw [if_pos rfl]
    · simp only [Cell.subsumes]; exact Liveness.Le.live_dead
  · refine ⟨v, ?_, Cell.subsumes_refl v⟩
    rw [if_neg hneq]; exact hlookup

/-- Dropping mcells in subsuming memories preserves subsumption.  The cell at
    `l` becomes `(.mcell false .dead)` in both heaps (so they agree exactly
    there); other cells are unchanged and the subsumption hypothesis carries
    them across. -/
theorem drop_mcell_subsumes_compat {m1 m2 : Memory} (l : Nat)
  (hexists1 : ∃ b0, m1.heap l = some (.capability (.mcell b0 .live)))
  (hexists2 : ∃ b0, m2.heap l = some (.capability (.mcell b0 .live)))
  (hsub : m2.subsumes m1) :
  (m2.drop_mcell l hexists2).subsumes (m1.drop_mcell l hexists1) := by
  change (m2.heap.update_cell l (.capability (.mcell false .dead))).subsumes
    (m1.heap.update_cell l (.capability (.mcell false .dead)))
  unfold Heap.subsumes
  intro l' v hlookup
  unfold Heap.update_cell at hlookup ⊢
  by_cases hneq : l' = l
  · subst hneq
    rw [if_pos rfl] at hlookup
    cases hlookup
    refine ⟨.capability (.mcell false .dead), ?_, ?_⟩
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
theorem extend_mcell_subsumes (m : Memory) (l : Nat) (b : Bool)
  (hfresh : m.heap l = none) :
  (m.extend_mcell l b hfresh).subsumes m := by
  change (m.heap.extend_mcell l b).subsumes m.heap
  exact Heap.extend_mcell_subsumes hfresh

theorem extend_mcell_lookup {m : Memory} {l : Nat} {b : Bool}
  (hfresh : m.heap l = none) :
  (m.extend_mcell l b hfresh).lookup l = some (.capability (.mcell b .live)) := by
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

/-- `is_compatible` is anti-monotonic in the capability set: if `C1 ⊆ C2` and `m`
    is compatible with `C2`, then it is compatible with `C1`. The mutability shift
    in `Subset.cap_ro` is harmless because compatibility only checks the
    underlying location, not the mutability. -/
theorem is_compatible_subset {m : Memory} {C1 C2 : CapabilitySet}
    (hsub : C1 ⊆ C2) (hcompat : m.is_compatible C2) : m.is_compatible C1 := by
  intro mu l b ℓ hmem hheap
  obtain ⟨mu', hmem'⟩ := hasmem_of_subset hsub mu l hmem
  exact hcompat mu' l b ℓ hmem' hheap

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
| .cap _ x => {x}

def Heap.not_mutated (init after : Heap) : Prop :=
  ∀ l b ℓ,
    init l = some (.capability (.mcell b ℓ)) ->
    after l = some (.capability (.mcell b ℓ))

def Memory.not_mutated (init after : Memory) : Prop :=
  init.heap.not_mutated after.heap

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

end CapabilitySet.Noninterference

/-- Compute the reachability of a capture set in a given memory. -/
def CaptureSet.reachability : CaptureSet {} -> Memory -> CapabilitySet
| .empty => fun _ => {}
| .union cs1 cs2 => fun m =>
  (cs1.reachability m) ∪ (cs2.reachability m)
| .var m' (.free x) => fun m => (reachability_of_loc m.heap x).applyMut m'

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
          congrArg (CapabilitySet.applyMut m) (reachability_of_loc_monotonic hsub loc hex)
  | cvar m C =>
    cases C
  | union cs1 cs2 ih1 ih2 =>
    cases hwf with
    | wf_union hwf1 hwf2 =>
      simp only [CaptureSet.reachability, ih1 hwf1, ih2 hwf2]


end Consume
